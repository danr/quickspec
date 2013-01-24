-- | The testing loop and term generation of QuickSpec.

{-# LANGUAGE Rank2Types, TypeOperators, ScopedTypeVariables #-}
module Test.QuickSpec.Generate where

import Test.QuickSpec.Signature hiding (con)
import qualified Test.QuickSpec.TestTree as T
import Test.QuickSpec.TestTree(TestResults, reps, classes, numTests, cutOff, discrete)
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.Utils.TypeRel(TypeRel)
import qualified Test.QuickSpec.Utils.TypeRel as TypeRel
import Test.QuickSpec.Utils.TypeMap(TypeMap)
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap
import Test.QuickSpec.Term
import Test.QuickSpec.Family
import Text.Printf
import Test.QuickSpec.Utils.Typeable
import Test.QuickSpec.Utils
import Test.QuickCheck.Gen
import System.Random
import Control.Spoon
import Test.QuickSpec.Utils.MemoValuation
import Data.List
import Data.Ord

terms :: Sig -> TypeRel Family -> TypeRel Family
terms sig base =
  TypeMap.fromList
    [ Some (O (terms' sig base w))
    | Some (Witness w) <- usort (saturatedTypes sig ++ variableTypes sig) ]

terms' :: Typeable a => Sig -> TypeRel Family -> a -> [Family a]
terms' sig base w =
  [ var vs | let vs = TypeRel.lookup w (variables sig), not (null vs) ] ++
  map con (TypeRel.lookup w (constants sig)) ++
  [ app f x
  | Some (Witness w') <- lhsWitnesses sig w,
    x <- TypeRel.lookup w' base,
    not (isUndefined (term x)),
    f <- terms' sig base (const w),
    arity f > 0,
    not (isUndefined (term f)) ]

test :: [(StdGen, Int)] -> Sig ->
        TypeMap (List `O` Family) -> TypeMap (TestResults `O` Family)
test seeds sig ts = fmap (mapSome2 (test' seeds sig)) ts

test' :: forall a. Typeable a => [(StdGen, Int)] -> Sig -> [Family a] -> TestResults (Family a)
test' seeds sig ts
  | not (testable sig (undefined :: a)) = discrete ts
  | otherwise =
    case observe undefined sig of
      Observer obs ->
        let testCase (g, n) =
              let (g1, g2) = split g
                  val = memoValuation sig (unGen valuation g1 n) in
              \x -> teaspoon . force . unGen obs g2 n $ eval x val
            force x = x == x `seq` x
        in cutOff base increment (T.test (map testCase seeds) ts)
  where
    base = minTests sig `div` 2
    increment = minTests sig - base

genSeeds :: IO [(StdGen, Int)]
genSeeds = do
  rnd <- newStdGen
  let rnds rnd = rnd1 : rnds rnd2 where (rnd1, rnd2) = split rnd
  return (zip (rnds rnd) (concat (repeat [0,2..20])))

generate :: Sig -> [(StdGen, Int)] -> IO (TypeMap (TestResults `O` Family))
generate sig seeds | maxDepth sig < 0 =
  error "Test.QuickSpec.Generate.generate: maxDepth must be positive"
generate sig seeds | maxDepth sig == 0 = return TypeMap.empty
generate sig seeds = unbuffered $ do
  let d = maxDepth sig
  rs <- fmap (TypeMap.mapValues2 reps) (generate (updateDepth (d-1) sig) seeds)
  printf "Depth %d: " d
  let count :: ([a] -> a) -> (forall b. f (g b) -> a) ->
               TypeMap (f `O` g) -> a
      count op f = op . map (some2 f) . TypeMap.toList
      ts = terms sig rs
  printf "%d terms, " (count sum length ts)
  let cs = test seeds sig ts
  printf "%d tests, %d classes, %d raw equations.\n"
      (count (maximum . (0:)) numTests cs)
      (count sum (length . classes) cs)
      (count sum (sum . map (subtract 1 . length) . classes) cs)
  return cs

universe :: Sig -> [(StdGen, Int)] -> IO [Tagged Term]
universe sig seeds = do
  cs <- generate (updateDepth (maxDepth sig - 1) sig) seeds
  return $
    sortBy (comparing erase) .
    filter (not . isUndefined . erase) .
    concatMap (some (map (tagged term) . instances)) .
    TypeRel.toList .
    terms sig .
    TypeMap.mapValues2 reps $ cs

eraseClasses :: TypeMap (TestResults `O` Family) -> [[Tagged Term]]
eraseClasses = concatMap (some (map (map (tagged term)) . classes . unO)) . TypeMap.toList
