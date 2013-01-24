-- | The main implementation of QuickSpec.

{-# LANGUAGE TypeOperators, TupleSections, ScopedTypeVariables #-}
module Test.QuickSpec.Main where

import Test.QuickSpec.Generate
import Test.QuickSpec.Reasoning.NaiveEquationalReasoning hiding (universe, maxDepth)
import Test.QuickSpec.Utils.Typed
import qualified Test.QuickSpec.Utils.TypeMap as TypeMap
import qualified Test.QuickSpec.Utils.TypeRel as TypeRel
import Test.QuickSpec.Signature hiding (vars)
import Test.QuickSpec.Term
import Test.QuickSpec.Family
import Control.Monad
import Text.Printf
import Data.Monoid
import Test.QuickSpec.TestTree(TestResults, classes, reps)
import Data.List
import System.Random
import Data.Monoid
import Data.Maybe
import Test.QuickSpec.Utils
import Test.QuickSpec.Equation
import Data.Ord
import Data.Function
import Test.QuickSpec.Utils.Typeable

undefinedsSig :: Sig -> Sig
undefinedsSig sig =
  background
    [ undefinedSig "undefined" (undefined `asTypeOf` witness x)
    | Some x <- saturatedTypes sig ]

limitVars :: Int -> Sig -> Sig
limitVars n sig = sig { variables = TypeMap.mapValues (O . take n . unO) (variables sig) }

data SkeletalEq a
  = RepRenaming (Family a)
  | Normal (Family a) (Family a) -- non-representative first

skeletalBound :: SkeletalEq a -> Term
skeletalBound (RepRenaming t) = term t
skeletalBound (Normal t u) = term t

skeletal :: [Family a] -> [SkeletalEq a]
skeletal (t:ts) = RepRenaming t:[Normal u t | u <- ts]

prune :: Sig -> [(StdGen, Int)] -> [Tagged Term] -> [Some SkeletalEq] -> [Equation]
prune sig seeds univ skels =
  concat (evalEQ (initial (maxDepth sig) univ) (mapM (some prune1) skels))
  where
    prune1 skel =
      filterM (fmap not . unify) =<<
      (fmap retest . weedOut . instantiate $ skel)
    
    retest es =
      equations (map (map (tagged term)) (classes (test' seeds sig es)))
    
    weedOut = fmap (map (fst . head) . groupBy ((==) `on` snd) . sortBy (comparing snd)) . mapM withRep . sort
      where
        withRep t = fmap (t,) (rep (term t))
    
    instantiate (RepRenaming t) = instances t
    instantiate (Normal t u) = instances t ++ instances u
    
defines :: Equation -> Maybe Symbol
defines (t :=: u) = do
  let isVar Var{} = True
      isVar _ = False

      acyclic t =
        all acyclic (args t) &&
        case functor t == functor u of
          True -> usort (map Var (vars t)) `isProperSubsetOf` args u
          False -> True
      xs `isProperSubsetOf` ys = xs `isSubsetOf` ys && sort xs /= sort ys
      xs `isSubsetOf` ys = sort xs `isSublistOf` sort ys
      [] `isSublistOf` _ = True
      (x:xs) `isSublistOf` [] = False
      (x:xs) `isSublistOf` (y:ys)
        | x == y = xs `isSublistOf` ys
        | otherwise = (x:xs) `isSublistOf` ys

  guard (all isVar (args u) && usort (args u) == args u &&
         acyclic t && vars t `isSubsetOf` vars u)

  return (functor u)

definitions :: [Equation] -> [Equation]
definitions es = [ e | e <- es, defines e /= Nothing ]

runTool :: Signature a => (Sig -> IO ()) -> a -> IO ()
runTool tool sig_ = do
  putStrLn "== API =="
  putStr (show (signature sig_))
  let sig = signature sig_ `mappend` undefinedsSig (signature sig_)

  tool sig

quickSpec :: Signature a => a -> IO ()
quickSpec = runTool $ \sig -> do
  seeds <- genSeeds

  putStrLn "== Generating universe =="
  univ <- universe sig seeds
  printf "%d terms in universe.\n\n" (length univ)
  
  putStrLn "== Testing skeletons =="
  r <- generate sig seeds
  let clss = concatMap (some2 (map (Some . O) . classes)) (TypeMap.toList r)
      skel = sortBy (comparing (some skeletalBound)) (concatMap (some2 (map Some . skeletal)) clss)
      pruned = filter (not . all silent . eqnFuns)
                 (prune sig seeds univ skel)
      eqnFuns (t :=: u) = funs t ++ funs u
      isGround (t :=: u) = null (vars t) && null (vars u)
      (ground, nonground) = partition isGround pruned

  putStrLn "== Ground equations =="
  forM_ (zip [1 :: Int ..] ground) $ \(i, eq) ->
    printf "%3d: %s\n" i (showEquation sig eq)
  putStrLn ""

  putStrLn "== Non-ground equations =="
  forM_ (zip [length ground + 1 ..] nonground) $ \(i, eq) ->
    printf "%3d: %s\n" i (showEquation sig eq)
  putStrLn ""

sampleList :: StdGen -> Int -> [a] -> [a]
sampleList g n xs | n >= length xs = xs
                  | otherwise = aux g n (length xs) xs
  where
    aux g 0 _ _ = []
    aux g _ _ [] =
      error "Test.QuickSpec.Main.sampleList: bug in sampling"
    aux g size len (x:xs)
      | i <= size = x:aux g' (size-1) (len-1) xs
      | otherwise = aux g' size (len-1) xs
      where (i, g') = randomR (1, len) g

sampleTerms :: Signature a => a -> IO ()
sampleTerms = runTool $ \sig -> do
  putStrLn "== Testing =="
  seeds <- genSeeds
  univ <- fmap (map erase) (universe sig seeds)
  printf "Universe contains %d terms.\n\n" (length univ)

  let numTerms = 100

  printf "== Here are %d terms out of a total of %d ==\n" numTerms (length univ)
  g <- newStdGen
  forM_ (zip [1 :: Int ..] (sampleList g numTerms univ)) $ \(i, t) ->
    printf "%d: %s\n" i (show (disambiguate sig (vars t) t))

  putStrLn ""
