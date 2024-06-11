module TypeChecker.ProgramCheck where

open import Prelude

open import Program.Program
open import Program.TypeDeclaration 
open import Program.Type
open import Util.Context
open import Program.Term
open import TypeChecker.TypingRules
open import Util.Scope
open import Util.Convert
open import Util.Relations

private variable
  n : ℕ

-- checks that all arguments of a constructor are well-kinded
data DataConstructorCheck (types : TyContext n) : DataConstructor → Set where
  dataConstrCheck : {dataConstructor : String} {args : List Type}
    → IsTrue (isCapitalized dataConstructor)
    → types ⊢ᵏˢ args
    → DataConstructorCheck types (DC dataConstructor args)

-- checks that all constructors are valid
data DeclarationCheck (types : TyContext n) : TypeDeclaration → Set where
  decsCheck : {typeConstructor : String} {typeVariables : ℕ} {dataConstructors : List DataConstructor}
    → IsTrue (isCapitalized typeConstructor)
    → All (DataConstructorCheck (addVarsToTyContext typeVariables types)) dataConstructors
    → DeclarationCheck types (`data TC typeConstructor typeVariables `where dataConstructors)
    
data ProgramCheck : Set where
 progCheck : {declarations : List TypeDeclaration} {term : Term (constructors declarations)} {t : Type}
    → All (DeclarationCheck (typesToContext (types declarations))) declarations
    → UniqueList (constructors declarations ++ typeNames declarations)
    → (declarationsToContext declarations) ⨾ (typesToContext (types declarations)) ⊢ term ∶ t
    → ProgramCheck
   