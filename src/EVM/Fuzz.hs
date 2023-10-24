{-# LANGUAGE ScopedTypeVariables #-}

{- |
    Module: EVM.Fuzz
    Description: Concrete Fuzzer of Exprs
-}

module EVM.Fuzz where

import Prelude hiding (LT, GT, lookup)
import Control.Monad.State
import Data.Map.Strict as Map (Map, (!), (!?), insert)
import EVM.Expr qualified as Expr
import EVM.Expr (bytesToW256)
import Data.Set as Set (insert, Set, empty, toList)
import EVM.Traversals
import Data.ByteString qualified as BS
import Data.Word (Word8)
import Control.Monad.Random.Strict qualified as CMR

import EVM.Types (Prop(..), W256, Expr(..), EType(..), internalError)
import EVM.SMT (BufModel(..), SMTCex(..))

tryCexFuzz :: [Prop] -> Integer -> Maybe (SMTCex)
tryCexFuzz ps tries = CMR.evalRand (testVals tries) (CMR.mkStdGen 1337)
  where
    vars = extractVars ps
    bufs = extractBufs ps
    testVals :: CMR.MonadRandom m => Integer -> m (Maybe SMTCex)
    testVals 0 = pure Nothing
    testVals todo = do
      varVals <- getVals vars
      bufVals <- getBufs bufs
      let
        ret =  map (substituteEWord varVals . substituteBuf bufVals) ps
        retSimp =  Expr.simplifyProps ret
      if null retSimp then pure $ Just (SMTCex {
                                    vars = varVals
                                    , addrs = mempty
                                    , buffers = bufVals
                                    , store = mempty
                                    , blockContext = mempty
                                    , txContext = mempty
                                    })
                                    else testVals (todo-1)


substituteEWord :: Map (Expr EWord) W256 -> Prop -> Prop
substituteEWord valMap p = mapProp go p
  where
    go :: Expr a -> Expr a
    go orig@(Var _) = Lit (valMap ! orig)
    go orig@(TxValue) = Lit (valMap ! orig)
    go a = a


substituteBuf :: Map (Expr Buf) BufModel -> Prop -> Prop
substituteBuf valMap p = mapProp go p
  where
    go :: Expr a -> Expr a
    go orig@(AbstractBuf _) = case (valMap !? orig) of
                                Just (Flat x) -> ConcreteBuf x
                                Just (Comp _) -> internalError "No compressed allowed in fuzz"
                                Nothing -> orig
    go a = a


-- Var extraction
newtype CollectVars = CollectVars { vs :: Set.Set (Expr EWord) }
  deriving (Show)

initVarsState :: CollectVars
initVarsState = CollectVars { vs = Set.empty }

findVarProp :: Prop -> State CollectVars Prop
findVarProp p = mapPropM go p
  where
    go :: forall a. Expr a -> State CollectVars (Expr a)
    go = \case
      e@(Var a) -> do
        s <- get
        put $ s{vs=Set.insert (Var a) s.vs}
        pure e
      e -> pure e


extractVars :: [Prop] -> [Expr EWord]
extractVars ps = Set.toList vars
 where
  CollectVars vars = execState (mapM_ findVarProp ps) initVarsState


--- Buf extraction
newtype CollectBufs = CollectBufs { bufs :: Set.Set (Expr Buf) }
  deriving (Show)

initBufsState :: CollectBufs
initBufsState = CollectBufs { bufs = Set.empty }

extractBufs :: [Prop] -> [Expr Buf]
extractBufs ps = Set.toList bufs
 where
  CollectBufs bufs = execState (mapM_ findBufProp ps) initBufsState


findBufProp :: Prop -> State CollectBufs Prop
findBufProp p = mapPropM go p
  where
    go :: forall a. Expr a -> State CollectBufs (Expr a)
    go = \case
      e@(AbstractBuf a) -> do
        s <- get
        put $ s{bufs=Set.insert (AbstractBuf a) s.bufs}
        pure e
      e -> pure e


-- Var value generation
getVals :: CMR.MonadRandom m => [Expr EWord] -> m (Map (Expr EWord) W256)
getVals vars = do
    bufs <- go vars mempty
    addTxStuff bufs
  where
    addTxStuff :: CMR.MonadRandom m => Map (Expr EWord) W256 -> m (Map (Expr EWord) W256)
    addTxStuff a = pure $ Map.insert TxValue 0 a -- TODO change from 0 sometimes
    go :: CMR.MonadRandom m => [Expr EWord] -> Map (Expr EWord) W256 -> m (Map (Expr EWord) W256)
    go [] valMap = pure valMap
    go (a:ax) valMap = do
      val <- getRndW8s 32
      go ax (Map.insert a (bytesToW256 val) valMap)


-- Buf value generation
getBufs :: CMR.MonadRandom m => [Expr Buf] -> m (Map (Expr Buf) BufModel)
getBufs bufs = go bufs mempty
  where
    go :: CMR.MonadRandom m => [Expr Buf] -> Map (Expr Buf) BufModel -> m (Map (Expr Buf) BufModel)
    go [] valMap = pure valMap
    go (a:ax) valMap = do
      emptySize :: Bool <- CMR.getRandom
      size <- if emptySize then (pure 0)
                           else getRndW8
      bytes <- getRndW8s (fromIntegral size)
      go ax (Map.insert a (Flat $ BS.pack bytes) valMap)


getRndW8 :: CMR.MonadRandom m => m Word8
getRndW8 = do CMR.getRandom

getRndW8s :: CMR.MonadRandom m => Int -> m [Word8]
getRndW8s n = replicateM n getRndW8
