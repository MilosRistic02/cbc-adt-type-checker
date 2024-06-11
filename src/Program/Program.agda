module Program.Program where

open import Prelude

open import Program.Term
open import Program.TypeDeclaration
open import Util.Scope

private variable
  α : Scope
 
data Program : Set where
  prog : (tds : List TypeDeclaration) → Term (constructors tds) → Program

declarations : Program → List TypeDeclaration
declarations (prog ds _) = ds

term : (p : Program) → Term (constructors (declarations p))
term (prog _ t) = t