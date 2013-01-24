{-# LANGUAGE RankNTypes, ExistentialQuantification, DeriveFunctor #-}
module Test.QuickSpec.Expr where

import Test.QuickSpec.Term
import Data.Ord
import Data.Function

data Expr a = Expr {
  term :: Term,
  arity :: {-# UNPACK #-} !Int,
  eval :: (forall b. Variable b -> b) -> a }

instance Eq (Expr a) where
  (==) = (==) `on` term

instance Ord (Expr a) where
  compare = comparing term

instance Show (Expr a) where
  show = show . term

var :: Variable a -> Expr a
var v@(Variable (Atom x _)) = Expr (Var x) 0 (\env -> env v)

con :: Constant a -> Expr a
con (Constant (Atom x v)) = Expr (Const x) (symbolArity x) (const v)

app :: Expr (a -> b) -> Expr a -> Expr b
app (Expr t a f) (Expr u _ x)
  | a == 0 = error "Test.QuickSpec.Term.app: oversaturated function"
  | otherwise = Expr (App t u) (a - 1) (\env -> f env (x env))