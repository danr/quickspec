{-# LANGUAGE Rank2Types #-}
module Test.QuickSpec.Family where

import qualified Test.QuickSpec.Expr as Expr
import Test.QuickSpec.Expr(Expr)
import Test.QuickSpec.Term
import qualified Test.QuickSpec.Utils.TypeRel as TypeRel
import Data.Ord
import Data.Function
import Control.Monad

data Family a = Family {
  skeleton :: Expr a,
  instances_ :: [Expr a]
  }

instance Eq (Family a) where
  (==) = (==) `on` skeleton

instance Ord (Family a) where
  compare = comparing skeleton

instances :: Family a -> [Family a]
instances f = [ Family e [] | e <- instances_ f ]

var :: [Variable a] -> Family a
var vs@(v:_) = Family (Expr.var v) (map Expr.var vs)

con :: Constant a -> Family a
con c = Family (Expr.con c) [Expr.con c]

app :: Family (a -> b) -> Family a -> Family b
app (Family f fs) (Family x xs) =
  Family (Expr.app f x) (liftM2 Expr.app fs xs)

term :: Family a -> Term
term = Expr.term . skeleton

arity :: Family a -> Int
arity = Expr.arity . skeleton

eval :: Family a -> (forall b. Variable b -> b) -> a
eval = Expr.eval . skeleton