module Util.Convert where

open import Prelude

open import Program.TypeDeclaration
open import Program.Type
open import Program.Term
open import Util.Context
open import Util.Relations
open import Util.Scope

private variable
  α : Scope

typeVariablesToList : ℕ → List Type
typeVariablesToList zero = []
typeVariablesToList (suc n) = TVar n ∷ typeVariablesToList n

-- | Converts a list of type declarations to a context
declarationsToContext : (tds : List TypeDeclaration) → Context (constructors tds)
declarationsToContext [] = ∅
declarationsToContext ((`data TC t tvs `where cs) ∷ tds) = 
  mergeContext (constructorsToContext cs) (declarationsToContext tds)
  where
    argsToFun : List Type → Type
    argsToFun = foldr _⇒_ (T t (typeVariablesToList tvs))

    typeAbstractions : Type → ℕ → Type
    typeAbstractions t zero = t
    typeAbstractions t (suc n) = `∀ (typeAbstractions t n)
    
    constructorsToContext : (cs : List DataConstructor) → Context (map constructorName cs)
    constructorsToContext [] = ∅
    constructorsToContext (DC n args ∷ cs) = constructorsToContext cs , n ∶ typeAbstractions (argsToFun args) tvs 

-- | Converts a context to a list of constructors of the given type
contextToConstructors : Context α → String → List String
contextToConstructors ctx s = filter isCapitalized (helper ctx s)
  where
  helper : Context α → String → List String
  helper ∅ s = []
  helper (ctx , x ∶ T n _) s with s s≟ n 
  ... | yes refl = x ∷ helper ctx s
  ... | no _ = helper ctx s
  helper (ctx , x ∶ (_ ⇒ to)) s with (target to)
  ... | (T s₁ _) with s s≟ s₁
  ...             | yes refl = x ∷ (helper ctx s)
  ...             | no _ = helper ctx s
  helper (ctx , x ∶ (_ ⇒ to)) s                | _ = helper ctx s  
  helper (ctx , x ∶ (`∀ to)) s = helper (ctx , x ∶ to) s
  helper (ctx , _ ∶ _) s = helper ctx s

-- | Converts a list of patterns to the constructors they match
patternsToConstructors : List (Pattern α) → List String
patternsToConstructors [] = []
patternsToConstructors ((` c # _ ∶ _ ⟶ _ ) ∷ ps) = c ∷ (patternsToConstructors ps)