module Test.Main where

import Prelude

import Data.Either (Either(..))
import Data.HashMap (empty, singleton)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Language.Jowo.AST (Expr(..), Monotype(..), poly)
import Language.Jowo.TypeChecker (TypeError(..), runInfer)
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter] do
  describe "type-checker" do

    describe "infers primitives" do
      it "booleans" do
        runInfer (EBoolean true) empty `shouldEqual` Right TBoolean
        runInfer (EBoolean false) empty `shouldEqual` Right TBoolean
      it "integers" do
        runInfer (EInt 0) empty `shouldEqual` Right TInt
        runInfer (EInt 99) empty `shouldEqual` Right TInt
        runInfer (EInt $ negate 99) empty `shouldEqual` Right TInt
      it "strings" do
        runInfer (EString "") empty `shouldEqual` Right TString
        runInfer (EString "something") empty `shouldEqual` Right TString

    describe "infers var expressions" do
      it "var" do
        runInfer (EVar "x") empty `shouldEqual` Left (UnknownVariable "x")
        runInfer (EVar "x") (singleton "x" $ poly TString) `shouldEqual` Right TString

    describe "infers let expressions" do
      it "ignoring the binder type, returning something else" do
        -- let x = 10 in true
        runInfer (ELet "x" (EInt 10) (EBoolean true)) empty `shouldEqual` Right TBoolean
      it "returning the binder type" do
        -- let x = 10 in x
        runInfer (ELet "x" (EInt 10) (EVar "x")) empty `shouldEqual` Right TInt

    describe "infers simple lambda functions" do
      it "identity function returns Tvar -> TVar" do
        -- \x -> x
        runInfer (ELambda "x" (EVar "x")) empty `shouldEqual` Right (TFunction (TVar "t1") (TVar "t1"))
      it "returns an integer" do
        -- \x -> 5
        runInfer (ELambda "x" (EInt 5)) empty `shouldEqual` Right (TFunction (TVar "t1") TInt)

    describe "infers function applications" do
      it "simple application" do
        -- (\x -> x) 5
        let lambdaId = ELambda "x" (EVar "x")
        runInfer (EFuncAppl lambdaId (EInt 5)) empty `shouldEqual` Right TInt
      it "currying, inferring the return type" do
        -- let const = (\x -> \y -> x) in const 5
        let expr = ELambda "x" $ ELambda "y" (EVar "x")
        let curry = ELet "const" expr (EFuncAppl (EVar "const") (EInt 5))
        runInfer curry empty `shouldEqual` Right (TFunction (TVar "t2") TInt)

    describe "infers if-then-else statements" do
      it "normal if" do
        -- if true then 1 else 0
        runInfer (EIf (EBoolean true) (EInt 1) (EInt 0)) empty `shouldEqual` Right TInt
      it "type mismatch when not passing a predicate" do
        -- if 1 then 1 else 0
        runInfer (EIf (EInt 1) (EInt 1) (EInt 0)) empty `shouldEqual` Left (TypeMismatch TBoolean TInt)
      it "type mismatch when `then` and `else` has different type" do
        -- if true then 1 else "yoo"
        runInfer (EIf (EBoolean true) (EInt 1) (EString "")) empty `shouldEqual` Left (TypeMismatch TInt TString)
