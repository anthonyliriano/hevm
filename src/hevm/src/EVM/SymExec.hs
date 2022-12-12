{-# Language DataKinds #-}

module EVM.SymExec where

import Prelude hiding (Word)

import Control.Lens hiding (pre)
import EVM hiding (Query, Revert, push)
import qualified EVM
import EVM.Exec
import qualified EVM.Fetch as Fetch
import EVM.ABI
import EVM.SMT
import qualified EVM.Expr as Expr
import EVM.Stepper (Stepper)
import qualified EVM.Stepper as Stepper
import qualified Control.Monad.Operational as Operational
import Control.Monad.State.Strict hiding (state)
import EVM.Types
import EVM.Traversals
import EVM.Concrete (createAddress)
import qualified EVM.FeeSchedule as FeeSchedule
import Data.DoubleWord (Word256)
import Control.Concurrent.Async
import Data.Maybe
import Data.List (foldl', find)
import Data.Vector (fromList)
import Data.Map (lookup)
import Data.ByteString (ByteString, null, pack)
import qualified Control.Monad.State.Class as State
import Data.Bifunctor (second)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
import EVM.Format (formatExpr)

data ProofResult a b c = Qed a | Cex b | Timeout c
  deriving (Show, Eq)
type VerifyResult = ProofResult (Expr End) (Expr End, SMTCex) (Expr End)

isQed :: ProofResult a b c -> Bool
isQed (Qed _) = True
isQed _ = False

containsA :: Eq a => Eq b => Eq c => ProofResult a b c -> [(d , e, ProofResult a b c)] -> Bool
containsA a lst = isJust $ Data.List.find (\(_, _, c) -> c == a) lst

data VeriOpts = VeriOpts
  { simp :: Bool
  , debug :: Bool
  , maxIter :: Maybe Integer
  , askSmtIters :: Maybe Integer
  }
  deriving (Eq, Show)

defaultVeriOpts :: VeriOpts
defaultVeriOpts = VeriOpts { simp = True, debug = False, maxIter = Nothing, askSmtIters = Nothing }

debugVeriOpts :: VeriOpts
debugVeriOpts = VeriOpts { simp = True, debug = True, maxIter = Nothing, askSmtIters = Nothing }

extractCex :: VerifyResult -> Maybe (Expr End, SMTCex)
extractCex (Cex c) = Just c
extractCex _ = Nothing

inRange :: Int -> Expr EWord -> Prop
inRange sz e = PAnd (PGEq e (Lit 0)) (PLEq e (Lit $ 2 ^ sz - 1))

bool :: Expr EWord -> Prop
bool e = POr (PEq e (Lit 1)) (PEq e (Lit 0))

-- | Abstract calldata argument generation
symAbiArg :: Text -> AbiType -> CalldataFragment
symAbiArg name = \case
  AbiUIntType n ->
    if n `mod` 8 == 0 && n <= 256
    then let v = Var name in St [inRange n v] v
    else error "bad type"
  AbiIntType n ->
    if n `mod` 8 == 0 && n <= 256
    -- TODO: is this correct?
    then let v = Var name in St [inRange n v] v
    else error "bad type"
  AbiBoolType -> let v = Var name in St [bool v] v
  AbiAddressType -> let v = Var name in St [inRange 160 v] v
  AbiBytesType n
    -> if n > 0 && n <= 32
       then let v = Var name in St [inRange (n * 8) v] v
       else error "bad type"
  AbiArrayType sz tp -> Comp $ fmap (\n -> symAbiArg (name <> n) tp) [T.pack (show n) | n <- [0..sz-1]]
  t -> error $ "TODO: symbolic abi encoding for " <> show t

data CalldataFragment
  = St [Prop] (Expr EWord)
  | Dy [Prop] (Expr EWord) (Expr Buf)
  | Comp [CalldataFragment]
  deriving (Show, Eq)

-- | Generates calldata matching given type signature, optionally specialized
-- with concrete arguments.
-- Any argument given as "<symbolic>" or omitted at the tail of the list are
-- kept symbolic.
symCalldata :: Text -> [AbiType] -> [String] -> Expr Buf -> (Expr Buf, [Prop])
symCalldata sig typesignature concreteArgs base =
  let args = concreteArgs <> replicate (length typesignature - length concreteArgs)  "<symbolic>"
      mkArg :: AbiType -> String -> Int -> CalldataFragment
      mkArg typ "<symbolic>" n = symAbiArg (T.pack $ "arg" <> show n) typ
      mkArg typ arg _ = let v = makeAbiValue typ arg
                        in case v of
                             AbiUInt _ w -> St [] . Lit . num $ w
                             AbiInt _ w -> St [] . Lit . num $ w
                             AbiAddress w -> St [] . Lit . num $ w
                             AbiBool w -> St [] . Lit $ if w then 1 else 0
                             _ -> error "TODO"
      calldatas = zipWith3 mkArg typesignature args [1..]
      (cdBuf, props) = combineFragments calldatas base
      withSelector = writeSelector cdBuf sig
      sizeConstraints
        = (Expr.bufLength withSelector .>= cdLen calldatas)
        .&& (Expr.bufLength withSelector .< (Lit (2 ^ (64 :: Integer))))
  in (withSelector, sizeConstraints : props)

cdLen :: [CalldataFragment] -> Expr EWord
cdLen = go (Lit 4)
  where
    go acc = \case
      [] -> acc
      (hd:tl) -> case hd of
                   St _ _ -> go (Expr.add acc (Lit 32)) tl
                   _ -> error "unsupported"

writeSelector :: Expr Buf -> Text -> Expr Buf
writeSelector buf sig = writeSel (Lit 0) $ writeSel (Lit 1) $ writeSel (Lit 2) $ writeSel (Lit 3) buf
  where
    sel = ConcreteBuf $ selector sig
    writeSel idx = Expr.writeByte idx (Expr.readByte idx sel)

combineFragments :: [CalldataFragment] -> Expr Buf -> (Expr Buf, [Prop])
combineFragments fragments base = go (Lit 4) fragments (base, [])
  where
    go :: Expr EWord -> [CalldataFragment] -> (Expr Buf, [Prop]) -> (Expr Buf, [Prop])
    go _ [] acc = acc
    go idx (f:rest) (buf, ps) = case f of
                             St p w -> go (Expr.add idx (Lit 32)) rest (Expr.writeWord idx w buf, p <> ps)
                             s -> error $ "unsupported cd fragment: " <> show s


abstractVM :: Maybe (Text, [AbiType]) -> [String] -> ByteString -> Maybe Precondition -> StorageModel -> VM
abstractVM typesignature concreteArgs contractCode maybepre storagemodel = finalVm
  where
    (calldata', calldataProps) = case typesignature of
                 Nothing -> (AbstractBuf "txdata", [])
                 Just (name, typs) -> symCalldata name typs concreteArgs (AbstractBuf "txdata")
    store = case storagemodel of
              SymbolicS -> AbstractStore
              InitialS -> EmptyStore
              ConcreteS -> ConcreteStore mempty
    caller' = Caller 0
    value' = CallValue 0
    code' = RuntimeCode $ fromJust $ Expr.toList (ConcreteBuf contractCode)
    vm' = loadSymVM code' store caller' value' calldata'
    precond = case maybepre of
                Nothing -> []
                Just p -> [p vm']
    finalVm = vm' & set constraints (precond <> calldataProps)

loadSymVM :: ContractCode -> Expr Storage -> Expr EWord -> Expr EWord -> Expr Buf -> VM
loadSymVM x initStore addr callvalue' calldata' =
  (makeVm $ VMOpts
    { vmoptContract = initialContract x
    , vmoptCalldata = calldata'
    , vmoptValue = callvalue'
    , vmoptStorageBase = Symbolic
    , vmoptAddress = createAddress ethrunAddress 1
    , vmoptCaller = addr
    , vmoptOrigin = ethrunAddress --todo: generalize
    , vmoptCoinbase = 0
    , vmoptNumber = 0
    , vmoptTimestamp = (Lit 0)
    , vmoptBlockGaslimit = 0
    , vmoptGasprice = 0
    , vmoptDifficulty = 0
    , vmoptGas = 0xffffffffffffffff
    , vmoptGaslimit = 0xffffffffffffffff
    , vmoptBaseFee = 0
    , vmoptPriorityFee = 0
    , vmoptMaxCodeSize = 0xffffffff
    , vmoptSchedule = FeeSchedule.berlin
    , vmoptChainId = 1
    , vmoptCreate = False
    , vmoptTxAccessList = mempty
    , vmoptAllowFFI = False
    }) & set (env . contracts . at (createAddress ethrunAddress 1))
             (Just (initialContract x))
       & set (env . EVM.storage) initStore

-- Interpreter which explores all paths at branching points.
-- returns an Expr representing the possible executions
interpret
  :: Fetch.Fetcher
  -> Maybe Integer -- max iterations
  -> Maybe Integer -- ask smt iterations
  -> Stepper (Expr End)
  -> StateT VM IO (Expr End)
interpret fetcher maxIter askSmtIters =
  eval . Operational.view

  where
    eval
      :: Operational.ProgramView Stepper.Action (Expr End)
      -> StateT VM IO (Expr End)

    eval (Operational.Return x) = pure x

    eval (action Operational.:>>= k) =
      case action of
        Stepper.Exec ->
          exec >>= interpret fetcher maxIter askSmtIters . k
        Stepper.Run ->
          run >>= interpret fetcher maxIter askSmtIters . k
        Stepper.IOAct q ->
          mapStateT liftIO q >>= interpret fetcher maxIter askSmtIters . k
        Stepper.Ask (EVM.PleaseChoosePath cond continue) -> do
          assign result Nothing
          vm <- get
          case maxIterationsReached vm maxIter of
            -- TODO: parallelise
            Nothing -> do
              a <- interpret fetcher maxIter askSmtIters (Stepper.evm (continue True) >>= k)
              put vm
              b <- interpret fetcher maxIter askSmtIters (Stepper.evm (continue False) >>= k)
              return $ ITE cond a b
            Just n ->
              -- Let's escape the loop. We give no guarantees at this point
              interpret fetcher maxIter askSmtIters (Stepper.evm (continue (not n)) >>= k)
        Stepper.Wait q -> do
          let performQuery = do
                m <- liftIO (fetcher q)
                interpret fetcher maxIter askSmtIters (Stepper.evm m >>= k)

          case q of
            PleaseAskSMT _ _ continue -> do
              codelocation <- getCodeLocation <$> get
              iteration <- num . fromMaybe 0 <$> use (iterations . at codelocation)

              -- if this is the first time we are branching at this point,
              -- explore both branches without consulting SMT.
              -- Exploring too many branches is a lot cheaper than
              -- consulting our SMT solver.
              if iteration < (fromMaybe 5 askSmtIters)
              then interpret fetcher maxIter askSmtIters (Stepper.evm (continue EVM.Unknown) >>= k)
              else performQuery

            _ -> performQuery

        Stepper.EVM m ->
          State.state (runState m) >>= interpret fetcher maxIter askSmtIters . k

maxIterationsReached :: VM -> Maybe Integer -> Maybe Bool
maxIterationsReached _ Nothing = Nothing
maxIterationsReached vm (Just maxIter) =
  let codelocation = getCodeLocation vm
      iters = view (iterations . at codelocation . non 0) vm
  in if num maxIter <= iters
     then view (cache . path . at (codelocation, iters - 1)) vm
     else Nothing


type Precondition = VM -> Prop
type Postcondition = VM -> Expr End -> Prop


checkAssert :: SolverGroup -> [Word256] -> ByteString -> Maybe (Text, [AbiType]) -> [String] -> VeriOpts -> IO [VerifyResult]
checkAssert solvers errs c signature' concreteArgs opts = verifyContract solvers c signature' concreteArgs opts SymbolicS Nothing (Just $ checkAssertions errs)

{- |Checks if an assertion violation has been encountered

  hevm recognises the following as an assertion violation:

  1. the invalid opcode (0xfe) (solc < 0.8)
  2. a revert with a reason of the form `abi.encodeWithSelector("Panic(uint256)", code)`, where code is one of the following (solc >= 0.8):
    - 0x00: Used for generic compiler inserted panics.
    - 0x01: If you call assert with an argument that evaluates to false.
    - 0x11: If an arithmetic operation results in underflow or overflow outside of an unchecked { ... } block.
    - 0x12; If you divide or modulo by zero (e.g. 5 / 0 or 23 % 0).
    - 0x21: If you convert a value that is too big or negative into an enum type.
    - 0x22: If you access a storage byte array that is incorrectly encoded.
    - 0x31: If you call .pop() on an empty array.
    - 0x32: If you access an array, bytesN or an array slice at an out-of-bounds or negative index (i.e. x[i] where i >= x.length or i < 0).
    - 0x41: If you allocate too much memory or create an array that is too large.
    - 0x51: If you call a zero-initialized variable of internal function type.

  see: https://docs.soliditylang.org/en/v0.8.6/control-structures.html?highlight=Panic#panic-via-assert-and-error-via-require
-}
checkAssertions :: [Word256] -> Postcondition
checkAssertions errs _ = \case
  Revert _ (ConcreteBuf msg) -> PBool $ msg `notElem` (fmap panicMsg errs)
  Revert _ b -> foldl' PAnd (PBool True) (fmap (PNeg . PEq b . ConcreteBuf . panicMsg) errs)
  _ -> PBool True

-- |By default hevm checks for all assertions except those which result from arithmetic overflow
defaultPanicCodes :: [Word256]
defaultPanicCodes = [ 0x00, 0x01, 0x12, 0x21, 0x22, 0x31, 0x32, 0x41, 0x51 ]

allPanicCodes :: [Word256]
allPanicCodes = [ 0x00, 0x01, 0x11, 0x12, 0x21, 0x22, 0x31, 0x32, 0x41, 0x51 ]

-- |Produces the revert message for solc >=0.8 assertion violations
panicMsg :: Word256 -> ByteString
panicMsg err = (selector "Panic(uint256)") <> (encodeAbiValue $ AbiUInt 256 err)

verifyContract :: SolverGroup -> ByteString -> Maybe (Text, [AbiType]) -> [String] -> VeriOpts -> StorageModel -> Maybe Precondition -> Maybe Postcondition -> IO [VerifyResult]
verifyContract solvers theCode signature' concreteArgs opts storagemodel maybepre maybepost = do
  let preState = abstractVM signature' concreteArgs theCode maybepre storagemodel
  verify solvers opts preState Nothing maybepost

pruneDeadPaths :: [VM] -> [VM]
pruneDeadPaths =
  filter $ \vm -> case view result vm of
    Just (VMFailure DeadPath) -> False
    _ -> True

-- | Stepper that parses the result of Stepper.runFully into an Expr End
runExpr :: Stepper.Stepper (Expr End)
runExpr = do
  vm <- Stepper.runFully
  let asserts = view keccakEqs vm
  pure $ case view result vm of
    Nothing -> error "Internal Error: vm in intermediate state after call to runFully"
    Just (VMSuccess buf) -> Return asserts buf (view (env . EVM.storage) vm)
    Just (VMFailure e) -> case e of
      UnrecognizedOpcode _ -> Invalid asserts
      SelfDestruction -> SelfDestruct asserts
      EVM.StackLimitExceeded -> EVM.Types.StackLimitExceeded asserts
      EVM.IllegalOverflow -> EVM.Types.IllegalOverflow asserts
      EVM.Revert buf -> EVM.Types.Revert asserts buf
      EVM.InvalidMemoryAccess -> EVM.Types.InvalidMemoryAccess asserts
      EVM.BadJumpDestination -> EVM.Types.BadJumpDestination asserts
      e' -> EVM.Types.TmpErr asserts $ show e'

-- | Converts a given top level expr into a list of final states and the associated path conditions for each state
flattenExpr :: Expr End -> [([Prop], Expr End)]
flattenExpr = go []
  where
    go :: [Prop] -> Expr End -> [([Prop], Expr End)]
    go pcs = \case
      ITE c t f -> go (PNeg ((PEq c (Lit 0))) : pcs) t <> go (PEq c (Lit 0) : pcs) f
      e@(Invalid _)  -> [(pcs, e)]
      e@(SelfDestruct _) -> [(pcs, e)]
      e@(Revert _ _) -> [(pcs, e)]
      e@(Return _ _ _) -> [(pcs, e)]
      e@(EVM.Types.IllegalOverflow _) -> [(pcs, e)]
      e@(EVM.Types.StackLimitExceeded _ ) -> [(pcs, e)]
      e@(EVM.Types.InvalidMemoryAccess _) -> [(pcs, e)]
      e@(EVM.Types.BadJumpDestination _) -> [(pcs, e)]
      TmpErr _ s -> error s
      GVar _ -> error "cannot flatten an Expr containing a GVar"

reachableQueries :: Expr End -> IO [SMT2]
reachableQueries = go []
  where
    go :: [Prop] -> Expr End -> IO [SMT2]
    go pcs = \case
      ITE c t f -> do
        (tres, fres) <- concurrently
          (go (PEq (Lit 1) c : pcs) t)
          (go (PEq (Lit 0) c : pcs) f)
        pure (tres <> fres)
      _ -> pure [assertProps pcs]

-- | Strips unreachable branches from a given expr
-- Returns a list of executed SMT queries alongside the reduced expression for debugging purposes
-- Note that the reduced expression loses information relative to the original
-- one if jump conditions are removed. This restriction can be removed once
-- Expr supports attaching knowledge to AST nodes.
-- Although this algorithm currently parallelizes nicely, it does not exploit
-- the incremental nature of the task at hand. Introducing support for
-- incremental queries might let us go even faster here.
-- TODO: handle errors properly
reachable2 :: SolverGroup -> Expr End -> IO ([SMT2], Expr End)
reachable2 solvers e = do
    res <- go [] e
    pure $ second (fromMaybe (error "Internal Error: no reachable paths found")) res
  where
    {-
       Walk down the tree and collect pcs.
       Dispatch a reachability query at each leaf.
       If reachable return the expr wrapped in a Just. If not return Nothing.
       When walking back up the tree drop unreachable subbranches.
    -}
    go :: [Prop] -> Expr End -> IO ([SMT2], Maybe (Expr End))
    go pcs = \case
      ITE c t f -> do
        (tres, fres) <- concurrently
          (go (PEq (Lit 1) c : pcs) t)
          (go (PEq (Lit 0) c : pcs) f)
        let subexpr = case (snd tres, snd fres) of
              (Just t', Just f') -> Just $ ITE c t' f'
              (Just t', Nothing) -> Just t'
              (Nothing, Just f') -> Just f'
              (Nothing, Nothing) -> Nothing
        pure (fst tres <> fst fres, subexpr)
      leaf -> do
        let query = assertProps pcs
        res <- checkSat solvers query
        case res of
          Sat _ -> pure ([query], Just leaf)
          Unsat -> pure ([query], Nothing)
          r -> error $ "Invalid solver result: " <> show r

-- | Strips unreachable branches from a given expr
-- Returns a list of executed SMT queries alongside the reduced expression for debugging purposes
-- Note that the reduced expression loses information relative to the original
-- one if jump conditions are removed. This restriction can be removed once
-- Expr supports attaching knowledge to AST nodes.
-- Although this algorithm currently parallelizes nicely, it does not exploit
-- the incremental nature of the task at hand. Introducing support for
-- incremental queries might let us go even faster here.
-- TODO: handle errors properly
reachable :: SolverGroup -> Expr End -> IO ([SMT2], Expr End)
reachable solvers = go []
  where
    go :: [Prop] -> Expr End -> IO ([SMT2], Expr End)
    go pcs = \case
      ITE c t f -> do
        let
          tquery = assertProps (PEq c (Lit 1) : pcs)
          fquery = assertProps (PEq c (Lit 0) : pcs)
        tres <- (checkSat solvers tquery)
        fres <- (checkSat solvers fquery)
        print (tres, fres)
        case (tres, fres) of
          (Error tm, Error fm) -> do
            TL.writeFile "tquery.smt2" (formatSMT2 tquery)
            TL.writeFile "fquery.smt2" (formatSMT2 fquery)
            error $ "Solver Errors: " <> (T.unpack . T.unlines $ [tm, fm])
          (Error tm, _) -> do
            TL.putStrLn $ formatSMT2 tquery
            error $ "Solver Error: " <> T.unpack tm
          (_ , Error fm) -> error $ "Solver Error: " <> T.unpack fm
          (EVM.SMT.Unknown, _) -> error "Solver timeout, unable to analyze reachability"
          (_, EVM.SMT.Unknown) -> error "Solver timeout, unable to analyze reachability"
          (Unsat, Sat _) -> go (PEq c (Lit 0) : pcs) f
          (Sat _, Unsat) -> go (PEq c (Lit 1) : pcs) t
          (Sat _, Sat _) -> do
            ((tqs, texp), (fqs, fexp)) <- concurrently
              (go (PEq c (Lit 1) : pcs) t)
              (go (PEq c (Lit 0) : pcs) f)
            pure ([tquery, fquery] <> tqs <> fqs, ITE c texp fexp)
          (Unsat, Unsat) -> do
            putStrLn $ "pcs: " <> show pcs
            TL.putStrLn $ "tquery:\n " <> (formatSMT2 tquery)
            TL.putStrLn $ "fquery:\n " <> (formatSMT2 fquery)
            error "Internal Error: two unsat branches found"
      Invalid asserts -> pure ([], Invalid asserts)
      SelfDestruct asserts -> pure ([], SelfDestruct asserts)
      Revert asserts msg -> pure ([], Revert asserts msg)
      Return asserts msg store -> pure ([], Return asserts msg store)
      EVM.Types.IllegalOverflow asserts -> pure ([], EVM.Types.IllegalOverflow asserts)
      TmpErr _ e -> error $ "TmpErr: " <> show e
      GVar _ -> error "Internal Error: unexpected GVar"

-- | Evaluate the provided proposition down to its most concrete result
evalProp :: Prop -> Prop
evalProp = \case
  o@(PBool _) -> o
  o@(PNeg p)  -> case p of
              (PBool b) -> PBool (not b)
              _ -> o
  o@(PEq l r) -> if l == r
                 then PBool True
                 else o
  o@(PLT (Lit l) (Lit r)) -> if l < r
                             then PBool True
                             else o
  o@(PGT (Lit l) (Lit r)) -> if l > r
                             then PBool True
                             else o
  o@(PGEq (Lit l) (Lit r)) -> if l >= r
                              then PBool True
                              else o
  o@(PLEq (Lit l) (Lit r)) -> if l <= r
                              then PBool True
                              else o
  o@(PAnd l r) -> case (evalProp l, evalProp r) of
                    (PBool True, PBool True) -> PBool True
                    (PBool _, PBool _) -> PBool False
                    _ -> o
  o@(POr l r) -> case (evalProp l, evalProp r) of
                   (PBool False, PBool False) -> PBool False
                   (PBool _, PBool _) -> PBool True
                   _ -> o
  o -> o


-- | Extract contraints stored in  Expr End nodes
extractProps :: Expr End -> [Prop]
extractProps = \case
  ITE _ _ _ -> []
  Invalid asserts -> asserts
  SelfDestruct asserts -> asserts
  Revert asserts _ -> asserts
  Return asserts _ _ -> asserts
  EVM.Types.IllegalOverflow asserts -> asserts
  TmpErr asserts _ -> asserts
  GVar _ -> error "cannot extract props from a GVar"


-- | Symbolically execute the VM and check all endstates against the postcondition, if available.
verify :: SolverGroup -> VeriOpts -> VM -> Maybe (Fetch.BlockNumber, Text) -> Maybe Postcondition -> IO [VerifyResult]
verify solvers opts preState rpcinfo maybepost = do
  putStrLn "Exploring contract"

  exprInter <- evalStateT (interpret (Fetch.oracle solvers rpcinfo) (maxIter opts) (askSmtIters opts) runExpr) preState
  when (debug opts) $ T.writeFile "unsimplified.expr" (formatExpr exprInter)

  expr <- if (simp opts) then (pure $ Expr.simplify exprInter) else pure exprInter
  when (debug opts) $ T.writeFile "simplified.expr" (formatExpr expr)

  putStrLn $ "Explored contract (" <> show (Expr.numBranches expr) <> " branches)"

  case maybepost of
    Nothing -> pure [Qed expr]
    Just post -> do
      let
        -- Filter out any leaves that can be statically shown to be safe
        canViolate = flip filter (flattenExpr expr) $
          \(_, leaf) -> case evalProp (post preState leaf) of
            PBool True -> False
            _ -> True
        assumes = view constraints preState
        withQueries = fmap (\(pcs, leaf) -> (assertProps (PNeg (post preState leaf) : assumes <> extractProps leaf <> pcs), leaf)) canViolate
      putStrLn $ "Checking for reachability of " <> show (length withQueries) <> "\n potential property violations"

      when (debug opts) $ forM_ (zip [(1 :: Int)..] withQueries) $ \(idx, (q, leaf)) -> do
        TL.writeFile
          ("query-" <> show idx <> ".smt2")
          ("; " <> (TL.pack $ show leaf) <> "\n\n" <> formatSMT2 q <> "\n\n(check-sat)")

      -- Dispatch the remaining branches to the solver to check for violations
      results <- flip mapConcurrently withQueries $ \(query, leaf) -> do
        res <- checkSat solvers query
        pure (res, leaf)
      let cexs = filter (\(res, _) -> not . isUnsat $ res) results
      pure $ if Prelude.null cexs then [Qed expr] else fmap toVRes cexs
  where
    toVRes :: (CheckSatResult, Expr End) -> VerifyResult
    toVRes (res, leaf) = case res of
      Sat model -> Cex (leaf, model)
      EVM.SMT.Unknown -> Timeout leaf
      Unsat -> Qed leaf
      Error e -> error $ "Internal Error: solver responded with error: " <> show e

-- | Compares two contract runtimes for trace equivalence by running two VMs and comparing the end states.
equivalenceCheck :: SolverGroup -> ByteString -> ByteString -> VeriOpts -> Maybe (Text, [AbiType]) -> IO [(Maybe SMTCex, Prop, ProofResult () () ())]
equivalenceCheck solvers bytecodeA bytecodeB opts signature' = do
  let
    bytecodeA' = if Data.ByteString.null bytecodeA then Data.ByteString.pack [0] else bytecodeA
    bytecodeB' = if Data.ByteString.null bytecodeB then Data.ByteString.pack [0] else bytecodeB
    preStateA = abstractVM signature' [] bytecodeA' Nothing SymbolicS
    preStateB = abstractVM signature' [] bytecodeB' Nothing SymbolicS

  aExpr <- evalStateT (interpret (Fetch.oracle solvers Nothing) (maxIter opts) (askSmtIters opts) runExpr) preStateA
  bExpr <- evalStateT (interpret (Fetch.oracle solvers Nothing) (maxIter opts) (askSmtIters opts) runExpr) preStateB
  aExprSimp <- if (simp opts) then (pure $ Expr.simplify aExpr) else pure aExpr
  bExprSimp <- if (simp opts) then (pure $ Expr.simplify bExpr) else pure bExpr
  when (debug opts) $ putStrLn $ "num of aExprSimp endstates:" <> (show $ length $ flattenExpr aExprSimp) <> "\nnum of bExprSimp endstates:" <> (show $ length $ flattenExpr bExprSimp)

  -- Check each pair of end states for equality:
  let
      differingEndStates = uncurry distinct <$> [(a,b) | a <- flattenExpr aExprSimp, b <- flattenExpr bExprSimp]
      distinct :: ([Prop], Expr End) -> ([Prop], Expr End) -> Prop
      distinct (aProps, aEnd) (bProps, bEnd) =
        let
          differingResults = case (aEnd, bEnd) of
            (Return _ aOut aStore, Return _ bOut bStore) ->
              if aOut == bOut && aStore == bStore then PBool False
                                                  else aStore ./= bStore  .|| aOut ./= bOut
            (Return {}, _) -> PBool True
            (_, Return {}) -> PBool True
            (Revert _ a, Revert _ b) -> if a==b then PBool False else a ./= b
            (Revert _ _, _) -> PBool True
            (_, Revert _ _) -> PBool True
            (Invalid _, Invalid _) -> PBool False
            (Invalid _, _ ) -> PBool True
            (_, Invalid _) -> PBool True
            (EVM.Types.StackLimitExceeded _, EVM.Types.StackLimitExceeded _ ) -> PBool False
            (EVM.Types.StackLimitExceeded _, _) -> PBool True
            (_, EVM.Types.StackLimitExceeded _) -> PBool True
            (a, b) -> if a == b then PBool False
                                else error $ "Unimplemented, see TODO about EVM failures and TmpExpr. Left: " <> show a <> " Right: " <> show b

        -- if the SMT solver can find a common input that satisfies BOTH sets of path conditions
        -- AND the output differs, then we are in trouble. We do this for _every_ pair of paths, which
        -- makes this exhaustive
        in
        if differingResults == PBool False
           then PBool False
           else (foldl PAnd (PBool True) aProps) .&& (foldl PAnd (PBool True) bProps)  .&& differingResults
  -- If there exists a pair of end states where this is not the case,
  -- the following constraint is satisfiable

  let diffEndStFilt = filter (/= PBool False) differingEndStates
  putStrLn $ "Equivalence checking " <> (show $ length diffEndStFilt) <> " combinations"
  when (debug opts) $ forM_ (zip diffEndStFilt [1..]) (\(x, i) -> T.writeFile ("prop-checked-" <> show i) (T.pack $ show x))
  results <- flip mapConcurrently (zip diffEndStFilt [1..]) $ \(prop, i) -> do
    let assertedProps = assertProps [prop]
    let filename = "eq-check-" <> show i <> ".smt2"
    when (debug opts) $ T.writeFile (filename) $ (TL.toStrict $ formatSMT2 assertedProps) <> "\n(check-sat)"
    res <- case prop of
      PBool False -> pure Unsat
      _ -> checkSat solvers assertedProps
    case res of
     Sat a -> return (Just a, prop, Cex ())
     Unsat -> return (Nothing, prop, Qed ())
     EVM.SMT.Unknown -> return (Nothing, prop, Timeout ())
     Error txt -> error $ "Error while running solver: `" <> T.unpack txt <> "` SMT file was: `" <> filename <> "`"
  return $ filter (\(_, _, res) -> res /= Qed ()) results

both' :: (a -> b) -> (a, a) -> (b, b)
both' f (x, y) = (f x, f y)

showCounterexample :: VM -> Maybe (Text, [AbiType]) -> ()
showCounterexample vm maybesig = undefined
  --let (calldata', S _ cdlen) = view (EVM.state . EVM.calldata) vm
      --S _ cvalue = view (EVM.state . EVM.callvalue) vm
      --SAddr caller' = view (EVM.state . EVM.caller) vm
  --cdlen' <- num <$> getValue cdlen
  --calldatainput <- case calldata' of
    --SymbolicBuffer cd -> mapM (getValue.fromSized) (take cdlen' cd) >>= return . pack
    --ConcreteBuffer cd -> return $ BS.take cdlen' cd
  --callvalue' <- getValue cvalue
  --caller'' <- num <$> getValue caller'
  --io $ do
    --putStrLn "Calldata:"
    --print $ ByteStringS calldatainput

    ---- pretty print calldata input if signature is available
    --case maybesig of
      --Just (name, types) -> putStrLn $ unpack (head (splitOn "(" name)) ++
        --show (decodeAbiValue (AbiTupleType (fromList types)) $ Lazy.fromStrict (BS.drop 4 calldatainput))
      --Nothing -> return ()

    --putStrLn "Caller:"
    --print (Addr caller'')
    --putStrLn "Callvalue:"
    --print callvalue'
