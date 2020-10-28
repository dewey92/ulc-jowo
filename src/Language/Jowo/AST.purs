module Language.Jowo.AST where

import Prelude

data Expr
  = EBoolean Boolean
  | EInt Int
  | EString String
  | EVar String
  -- | `let x = 10 in true` is equivalent to `ELet "x" (EInt 10) (EBoolean true)`
  | ELet String Expr Expr
  -- | `\x -> 10` is equivalent to `ELambda "x" (EInt 10)`. Any Additional
  -- | arguments will be curried.
  | ELambda String Expr
  | EFuncAppl Expr Expr
  | EIf Expr Expr Expr

data Monotype
  = TBoolean
  | TInt
  | TString
  | TVar String -- `a` as in `a -> Int`
  -- | `fun :: argType -> returnType`. Any additional arguments should be curried.
  -- | So a function of `String -> Int -> String` is equivalent to `TFunction TString (TFunction TInt TString)`
  | TFunction Monotype Monotype

derive instance eqMonotype :: Eq Monotype
instance showMonotype :: Show Monotype where
  show TBoolean = "Boolean"
  show TInt = "Int"
  show TString = "String"
  show (TVar var) = var
  show (TFunction arg ret) = (case arg of
    TFunction _ _ -> "(" <> show arg <> ")"
    _             -> show arg
  ) <> " -> " <> show ret

-- | Or called "type scheme" in some literatures
-- |
-- | ```purs
-- | ∀ a b. a -> b -> a`
-- | ```
-- |
-- | would be equivalent to
-- |
-- | ```purs
-- | Polytype ["a", "b"] (TFunction (TVar "a") (TFunction (TVar "b") (TVar "a")))
-- | ```
data Polytype = Polytype (Array String) Monotype

poly :: Monotype -> Polytype
poly = Polytype []
