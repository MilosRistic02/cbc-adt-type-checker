module Program.TypeDeclaration where

open import Prelude

open import Program.Type

data DataConstructor : Set where
  DC : String → List Type → DataConstructor

constructorName : DataConstructor → String
constructorName (DC x _) = x

data TypeConstructor : Set where
  TC : String → ℕ → TypeConstructor

typeConstructorName : TypeConstructor → String
typeConstructorName (TC x _) = x
 
data TypeDeclaration : Set where
  `data_`where_ : TypeConstructor → List DataConstructor → TypeDeclaration

types : List TypeDeclaration → List Type
types tcs = map (λ { (`data TC t tv `where _) → T t (helper tv) }) tcs
  where
  helper : ℕ → List Type
  helper zero = []
  helper (suc n) = TVar n ∷ helper n

typeNames : List TypeDeclaration → List String
typeNames tcs = map (λ { (`data TC t _ `where _) → t }) tcs

constructors : List TypeDeclaration → List String
constructors tcs = concat (map (λ { (`data _ `where cs) → map constructorName cs  }) tcs)

infix 5 `data_`where_
infix 9 TC
infix 9 DC 