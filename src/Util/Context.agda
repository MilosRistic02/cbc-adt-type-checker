module Util.Context where

open import Prelude

open import Program.Type
open import Util.Evaluator
open import Util.Relations
open import Util.Scope

private variable
  α β : Scope
  n m : ℕ

data Context : Scope → Set where
  ∅ : Context Φ
  _,_∶_ : Context α → (x : String) → Type → Context (x ∷ α)

data TyContext : ℕ → Set where
  ∅ : TyContext 0
  _,_ : TyContext n → Type → TyContext n
  _,∙ : TyContext n → TyContext (suc n)

-- | Converting a list of types to a TyContext (used for declarations)
countTVar : List Type → ℕ
countTVar [] = 0
countTVar (TVar x ∷ xs) = 1 + countTVar xs
countTVar (_ ∷ xs) = countTVar xs

typesToContext : (xs : List Type) → TyContext (countTVar xs)
typesToContext [] = ∅
typesToContext (TVar x ∷ xs) = typesToContext xs ,∙
typesToContext (`ℕ ∷ xs) = typesToContext xs , `ℕ
typesToContext (`Bool ∷ xs) = typesToContext xs , `Bool
typesToContext (t@(_ ⇒ _) ∷ xs) = typesToContext xs , t
typesToContext (t@(T _ _) ∷ xs) = typesToContext xs , t
typesToContext (t@(`∀ _) ∷ xs) = typesToContext xs , t

infix 4 _,_∶_

-- | Lookup a variable in the context given the index
lookupVar : (Γ : Context α) (x : String) (p : x ∈ α) → Type
lookupVar (_ , _ ∶ v   ) x here = v
lookupVar (ctx , _ ∶ _) x (there p) = lookupVar ctx x p

-- | Merge two contexts
mergeContext : Context α → Context β → Context (α ++ β)
mergeContext ∅ ctx = ctx
mergeContext  (ctx , x ∶ t) ctx₁ = mergeContext ctx ctx₁ , x ∶ t    

-- | Shift every binding in a context
shiftContext : ℕ → Context α → Context α
shiftContext n ∅ = ∅
shiftContext n (ctx , x ∶ t) = shiftContext n ctx , x ∶ shift n t

↑Γ : Context α → Context α
↑Γ = shiftContext 0

-- | Function for extending the context with a list of bindings
extendContext : Context α → (ns : List String) → (ts : List Type) → (length ns) ≡ (length ts) → Context (ns ++ α)
extendContext ctx [] [] _ = ctx
extendContext ctx (n ∷ ns) (t ∷ ts) p  = (extendContext ctx ns ts (cong pred p)) , n ∶ t
 
-- | Extendending the TyContext with a specific number of type variables
addVarsToTyContext : {n : ℕ} (m : ℕ) → TyContext n → TyContext (m + n)
addVarsToTyContext 0 ctx = ctx
addVarsToTyContext (suc m) ctx = addVarsToTyContext m ctx ,∙
