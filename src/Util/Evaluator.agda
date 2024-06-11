module Util.Evaluator where

open import Data.String

-- Evaluation errors are strings.
--
EvalError = String

open import Data.Sum.Base
open import Data.Sum.Effectful.Left EvalError public
open import Effect.Monad

-- An Evaluator results in either a result of type a or an EvalError.
--
Evaluator : Set → Set
Evaluator a = EvalError ⊎ a

evalError : {a : Set} → EvalError → Evaluator a
evalError = inj₁

evalOk : {a : Set} → a → Evaluator a
evalOk = inj₂

instance
  -- Evaluator is a monad.
  --
  iRawMonadEvaluator : RawMonad Evaluator
  iRawMonadEvaluator = monad _

data Check {a : Set} : (String ⊎ a) → Set where
  fail : (msg : String) → Check (inj₁ msg)
  pass : {x : a} → Check (inj₂ x)

