module Language.Jowo.TypeChecker where

import Prelude

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State (State, evalState, modify)
import Data.Array (zip)
import Data.Either (Either)
import Data.HashMap as HM
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Data.String (joinWith)
import Data.Traversable (foldr, traverse)
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\), (/\))
import Language.Jowo.AST (Expr(..), Monotype(..), Polytype(..), poly)


-- | A dictionary that maps **unknown types (TVar)** to their **monotypes** if any
-- |
-- | S = [a |-> Int, b |-> String, c |-> a];
-- | S (Int) = Int;
-- | S (a) = Int;
-- | S (a -> b) = Int -> String;
-- | S (a -> b) = S (a) -> S(b);
-- | S (c) = Int; not `a`. It should keep looking up until a monotype is found
type SubstitutionDict = HM.HashMap String Monotype

emptySubstDict :: SubstitutionDict
emptySubstDict = HM.empty

updateSubstDict :: String -> Monotype -> SubstitutionDict -> SubstitutionDict
updateSubstDict = HM.insert

-- | Composing two dictionaries means merging them together after one dict "learns" from
-- | the other. In this case, `s1` will learn from `s2` (through `substituteMono`). The result
-- | will be merged with `s2` in a way that it favors the learning result in the case of overlapped keys
-- | (`HM.union` is left biased)
-- |
-- | It might be confusing that `s2` sits in the first arg while `s1` in the second. This is to
-- | depict the real usage where you should pass a dict with richer information in the first arg so that
-- | `s1` can "properly learn" from it
composeSubstDict :: SubstitutionDict -> SubstitutionDict -> SubstitutionDict
composeSubstDict s2 s1 = HM.union (HM.mapMaybe (\mono -> Just (substituteMono mono s2)) s1) s2

-- | The function can only be applied to those monotypes containing type variables.
-- | Literal types such as Boolean, Int, and String will not be affected cause they are
-- | concrete types already
-- |
-- | Applying a substitution means replacing all type variables with monotypes.
-- | For instance `[a |-> Int](a -> a -> String)` should be `Int -> Int -> String`
substituteMono :: Monotype -> SubstitutionDict -> Monotype
substituteMono ty subsDict = case ty of
  TVar var -> fromMaybe (TVar var) $ HM.lookup var subsDict
  TFunction arg ret -> TFunction (substituteMono arg subsDict) (substituteMono ret subsDict)
  _ -> ty

-- | When applying a substitution to a polytype, we only substitute all occurences of
-- | _free variables_ in that polytype! Not the quantified ones. So be aware of
-- | type variable naming clashes
-- |
-- | For instance:
-- | ```
-- | [a |-> Int, b |-> Boolean](∀ b. a -> b -> String)
-- | ```
-- |
-- | Type variable `a` here is a free var (comes from somewhere outside its scope)
-- | whereas type variable `b` **belongs to** the polytype thus should not be substituted.
-- | The final result is going to be
-- |
-- | `∀ b. Int -> b -> String`
substitutePoly :: Polytype -> SubstitutionDict -> Polytype
substitutePoly (Polytype vars monoTy) subsDict =
  -- To get free vars only, we can "temporarily" delete all type variables in
  -- the substitution dict that happen to appear in the polytype quantifier
  let dictWithFreeVarsOnly = foldr HM.delete subsDict vars in
  -- Then use the free-vars-only dict to apply substitutions to the polytype
  Polytype vars (substituteMono monoTy dictWithFreeVarsOnly)

-- | This is a dictionary that maps **variable names** in scope to their **types**.
-- | Think of it as a variable scoping mechanism. When a variable is encountered,
-- | we need to look up the variable name in the scope (a.k.a context)
type Context = HM.HashMap String Polytype

extendCtx :: String -> Polytype -> Context -> Context
extendCtx = HM.insert

substituteCtx :: Context -> SubstitutionDict -> Context
substituteCtx ctx subsDict = HM.mapMaybe (\poly -> Just $ substitutePoly poly subsDict) ctx

data TypeError
  = TypeMismatch Monotype Monotype
  | UnknownVariable String
  | OccursCheck

derive instance eqTypeError :: Eq TypeError
instance showTypeError :: Show TypeError where
  show (TypeMismatch tyA tyB) = joinWith " " $ ["Could not match type", show tyA, "with type", show tyB]
  show (UnknownVariable name) = "Unknown variable " <> show name
  show OccursCheck = "Occurs check failed"

type Unique = Int

-- | Our Infer monad. It allows us to throw `TypeError`s while providing the ability
-- | to produce unique values (through `State Unique`) for unknown types
type Infer a = ExceptT TypeError (State Unique) a

-- | Generates an auto-increment Int to make a unique `TVar`
freshTyVar :: Infer Monotype
freshTyVar = do
  n <- modify (_ + 1)
  pure $ TVar ("t" <> show n)

-- | Instantiation means replacing all bound variables in the quantifier with monotypes.
-- | The intention is to make sure polymorphic functions stay polymorphic and
-- | not being narrowed down by a call. For instance if we have an identity function:
-- |
-- | id :: ∀ x. x -> x
-- |
-- | and we later call it with an `Int`, the type checker should not permanently assume
-- | that `id` has the type `Int -> Int`. It should stay polymorphic in a way that
-- | I can still call `id` the next time with, let's say, a `String` to produce
-- | a `String`.
-- |
-- | That's why we don't leak any substitution dict out of this function to make sure
-- | outsiders cannot learn the inferred monotypes inside.
instantiate :: Polytype -> Infer Monotype
instantiate (Polytype vars mono) = do
  -- As a first step, replace all `vars` with fresh `TVar`s
  newVars <- traverse (\_ -> freshTyVar) vars
  -- | Then make a new substitution dict out of it by mapping `vars` with `newVars`.
  -- | In the case of an `id` function, we want to make a subs dict as such:
  -- |
  -- | [x |-> TVar t1]
  let subsDict = HM.fromArray $ zip vars newVars
  -- This way we can safely apply substitutions to its underlying monotype!
  pure $ substituteMono mono subsDict

-- | Basically gathers all `TVar`s within an expression
freeTypeVars :: Monotype -> Set.Set String
freeTypeVars (TVar var) = Set.singleton var
freeTypeVars (TFunction arg ret) = Set.union (freeTypeVars arg) (freeTypeVars ret)
freeTypeVars _ = Set.empty

-- | Bind a type variable to a monotype. See `unify` to know where it's being used
varBind :: String -> Monotype -> Infer SubstitutionDict
varBind var ty
  -- We don't learn anything, return empty dict
  | ty == TVar var = pure emptySubstDict
  -- `unify x (x -> x)` must throw an error, due to the recursive definition of "x"
  | Set.member var (freeTypeVars ty) = throwError OccursCheck
  -- `unify x y = [x |-> y]`
  | otherwise = pure $ HM.singleton var ty

-- | Infer a given expression
runInfer :: Expr -> Context -> Either TypeError Monotype
runInfer expr ctx =
  let inferResult = infer expr ctx in
  fst <$> evalState (runExceptT inferResult) 0

infer :: Expr -> Context -> Infer (Monotype /\ SubstitutionDict)
infer (EBoolean _) _ = pure $ TBoolean /\ emptySubstDict
infer (EInt _) _ = pure $ TInt /\ emptySubstDict
infer (EString _) _ = pure $ TString /\ emptySubstDict
infer (EVar name) ctx = case HM.lookup name ctx of
  Just poly -> do
    ty <- instantiate poly
    pure $ ty /\ emptySubstDict
  Nothing -> throwError $ UnknownVariable name
infer (ELet binder expr body) ctx = do
  tyExpr /\ s1 <- infer expr ctx
  -- | `body` might use some information from `tyExpr` that we happen to know
  -- | just now. To use this new information, we have to put it into the current `ctx`
  -- | by extending it then pass the newly extended `ctx` to infer the body type.
  let newCtx = extendCtx binder (poly tyExpr) ctx
  tyBody /\ s2 <- infer body (substituteCtx newCtx s1)
  pure $ tyBody /\ s2 `composeSubstDict` s1
infer (ELambda arg body) ctx = do
  tyArg <- freshTyVar
  -- | Here we extend `ctx` as `body` might use some information from `tyArg`
  let newEnv = extendCtx arg (poly tyArg) ctx
  tyBody /\ s1 <- infer body newEnv
  pure $ TFunction (substituteMono tyArg s1) tyBody /\ s1
infer (EFuncAppl func arg) ctx = do
    tyArg /\ s1 <- infer arg ctx
    tyFunc /\ s2 <- infer func (substituteCtx ctx s1)
    let s3 = s2 `composeSubstDict` s1
    tyRes <- freshTyVar
    s4 <- unify (substituteMono tyFunc s3) (TFunction tyArg tyRes)
    let s5 = s4 `composeSubstDict` s3
    pure $ substituteMono tyRes s5 /\ s5
infer (EIf pred thenE elseE) ctx = do
  tyPred /\ s1 <- infer pred ctx
  tyThen /\ s2 <- infer thenE (substituteCtx ctx s1)
  tyElse /\ s3 <- infer elseE (substituteCtx ctx s2)
  let s4 = s3 `composeSubstDict` s2 `composeSubstDict` s1
  s5 <- unify TBoolean (substituteMono tyPred s4)
  s6 <- unify (substituteMono tyThen s5) (substituteMono tyElse s5)
  let s7 = s6 `composeSubstDict` s5
  pure $ tyThen /\ s7

-- | Unification is pretty much like an assertion, "please assert that
-- | these two monotypes are identical". It may learn something along the way,
-- | hence `SubstitutionDict` being the return type
-- |
-- | Unification should be commutative, means `unify x y == unify y x`
-- |
-- | Example:
-- | ```
-- | (a -> Bool) `unify` (Int -> Bool) = [a |-> Int]
-- | ```
unify :: Monotype -> Monotype -> Infer SubstitutionDict
unify TInt TInt = pure emptySubstDict  -- we don't learn anything, return empty dict
unify TBoolean TBoolean = pure emptySubstDict
unify TString TString = pure emptySubstDict
unify (TFunction arg1 ret1) (TFunction arg2 ret2) = do
  s1 <- unify arg1 arg2
  s2 <- unify (substituteMono ret1 s1) (substituteMono ret2 s1)
  pure $ s2 `composeSubstDict` s1
unify (TVar var) ty = varBind var ty
unify ty (TVar var) = varBind var ty
unify ty1 ty2 = throwError $ TypeMismatch ty1 ty2
