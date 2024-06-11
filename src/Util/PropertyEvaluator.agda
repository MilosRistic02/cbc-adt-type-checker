module Util.PropertyEvaluator where

open import Prelude

open import Util.Evaluator
open import Util.Relations
open import Util.Scope
open import Util.Context

private variable
  α : Scope
  A : Set

-- | Evaluator for whether a boolean is true
evalIsTrue : (b : Bool) → String → Evaluator (IsTrue b)
evalIsTrue true _ = return isTrue
evalIsTrue false s = evalError s

-- | Evaluator for whether a variable is in a list
evalElem : (x : String) -> (xs : List String) -> Evaluator (x ∈ xs)
evalElem x [] = evalError ("not found: " s++ x)
evalElem x₁ (x₂ ∷ xs) with x₁ s≟ x₂
...               | yes refl = return here
...               | no _ = do
                      p <- evalElem x₁ xs
                      return (there p)

-- | Evaluator for whether set is a subset of another set
evalSubset : (xs ys : List String) -> Evaluator (xs ⊆ ys)
evalSubset [] ys = return ⊆empty
evalSubset (x ∷ xs) ys = do
  evalElem' <- evalElem x ys
  evalSubset' <- evalSubset xs ys
  return (⊆there evalElem' evalSubset')

-- | Evaluator for whether two sets are equivalent (ignoring duplicates)
evalSetEquiv : (xs ys : List String) -> Evaluator (xs ↭ ys)
evalSetEquiv xs ys = do
  subset1 <- evalSubset xs ys
  subset2 <- evalSubset ys xs
  return (pequiv subset1 subset2)

evalEquiv : (a b : A) → ((x y : A) → Dec (x ≡ y)) → String → Evaluator (a ≡ b)
evalEquiv a b f err with f a b
... | yes refl = return refl
... | no _ = evalError err

-- | Evaluator for whether a variable is not in a list
evalNotElem : (x : String) -> (xs : List String) → String -> Evaluator (x ∉ xs)
evalNotElem x [] err = return ∉empty
evalNotElem x₁ (x₂ ∷ xs) err with x₁ s≟ x₂
... | yes refl = evalError err
... | no p = do
  rest <- evalNotElem x₁ xs err
  return (∉there p rest)

-- | Evaluator for whether a list is unique
evalUniqueList : (xs : List String) → String -> Evaluator (UniqueList xs)
evalUniqueList [] err = return uniqueEmpty
evalUniqueList (x ∷ xs) err = do
  notElem <- evalNotElem x xs err
  rest <- evalUniqueList xs err
  return (uniqueCons notElem rest)


-- | Evaluator for finding the index of a variable in a context
findContextIndex : (Γ : Context α) → (x : String) → Evaluator (x ∈ α)
findContextIndex ∅ x = evalError ("Variable \"" s++ x s++ "\" not found in scope.")
findContextIndex {a} _ x = evalElem x a

-- | Evaluator for the All relation
evalAll : {p : A → Set} → (xs : List A) → ((x : A) → Evaluator (p x)) → Evaluator (All p xs)
evalAll [] _ = return []
evalAll (x ∷ xs) e = do
  px <- e x
  rest <- evalAll xs e
  return (px ∷ rest)  

-- | Evaluator for whether a number is smaller than another number
evalSmaller : (a b : ℕ) → String → Evaluator (a < b)
evalSmaller zero (suc b) err = return <z
evalSmaller (suc a) (suc b) err = do
  p <- evalSmaller a b err
  return (<s p)
evalSmaller _ _ err = evalError err