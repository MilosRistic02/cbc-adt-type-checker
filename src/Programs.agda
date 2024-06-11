module Programs where

open import Prelude

open import Program.Term  
open import Program.Program
open import TypeChecker.ProgramCheck
open import Program.TypeDeclaration
open import TypeChecker.TypeChecker
open import Program.Type
open import TypeChecker.TypingRules
open import Util.Context 
open import Util.Evaluator
open import Util.Scope
open import Util.Relations

private
  open import Agda.Builtin.Equality

  open import Effect.Monad
  open RawMonad ⦃ ... ⦄

  program0 : Program
  program0 = prog
    ((`data TC "List" 1 `where 
      ((DC "Cons" (TVar 0 ∷ T "List" (TVar 0 ∷ []) ∷ [])) ∷ 
       (DC "Nil" []) ∷ [])) ∷ [])
    (((Λ (Λ (Λ (ƛ "x" ∶ T "List" (((`∀ (TVar 2 ⇒ TVar 1)) ⇒ TVar 0) ∷ []) ⇒ (` "x" # here) ))) ◦ TVar 0)) ◦ `Bool ◦ `ℕ)

  evaluator0 : Evaluator ProgramCheck
  evaluator0 = checkProgram program0 
    ((T "List" (((`∀ (`Bool ⇒ `ℕ)) ⇒ `ℕ) ∷ []) ⇒ T "List" (((`∀ (`Bool ⇒ `ℕ)) ⇒ `ℕ) ∷ [])))

  check0 : Check evaluator0
  check0 = pass

  -- Correct programs
  {-
    program1 :: List a -> Maybe a
    program1 = \(x :: List a) -> case x of
      Cons v t -> Just v
      Nil -> Nothing  
  -}  
  program : Program
  program = prog 
    ((`data TC "Maybe" 1 `where 
        DC "Just" (TVar 0 ∷ []) ∷ 
        DC "Nothing" [] ∷ []) ∷ 
    (`data TC "List" 1 `where 
      ((DC "Cons" (TVar 0 ∷ T "List" (TVar 0 ∷ []) ∷ [])) ∷ 
       (DC "Nil" []) ∷ [])) ∷ [])
       
    (Λ (ƛ "x" ∶ T "List" (TVar 0 ∷ []) ⇒ 
      `case ` "x" # here of⟦ 
        ((` "Cons" # there (there (there here))  ∶ ("v" ∷ "t" ∷  []) ⟶ ((` "Just" # there (there (there here)) ◦ TVar 0) · ` "v" # there here)) ∷
        ((` "Nil" # there (there (there (there here)))  ∶ [] ⟶ ` "Nothing" # there (there here) ◦ TVar 0)
        ∷ [])) 
      ⟧))

  evaluator : Evaluator ProgramCheck
  evaluator = checkProgram program (`∀ ((T "List" (TVar 0 ∷ [])) ⇒ (T "Maybe" (TVar 0 ∷ []))))

  check : Check evaluator
  check = pass

  {-
    program2 :: Either Bool Int -> Pair Bool Int
    program2 = \(x :: Either Bool Int) -> case x of
      Left a -> P a 0
      Right b -> P False b
   -}
  program2 : Program
  program2 = prog 
    ((`data TC "Either" 2 `where (DC "Left" (TVar 1 ∷ [])) ∷ (DC "Right" (TVar 0 ∷ []) ∷ [])) ∷
    (`data TC "Pair" 2 `where (DC "P" (TVar 1 ∷ TVar 0 ∷ []) ∷ [])) ∷ [])
    
    (ƛ "x" ∶ T "Either" (`Bool ∷ `ℕ ∷ []) ⇒ 
      `case ` "x" # here of⟦ 
        ((` "Left" # there here  ∶ ("v" ∷  []) ⟶ (((` "P" # there (there (there (there here)))  ◦ `Bool) ◦ `ℕ) · ` "v" # here · `zero)) ∷
        ((` "Right" # there (there here) ∶ ("v" ∷  []) ⟶ (((` "P" # there (there (there (there here)))  ◦ `Bool) ◦ `ℕ) · `false · ` "v" # here))
        ∷ [])) 
      ⟧)

  evaluator2 : Evaluator ProgramCheck
  evaluator2 = checkProgram program2 (T "Either" (`Bool ∷ `ℕ ∷ []) ⇒ T "Pair" (`Bool ∷ `ℕ ∷ []))

  check2 : Check evaluator2
  check2 = pass

  {-
    program3 :: Int
    program3 = case program2 (Left True) of
      P a b -> if a then b else 0
  -}

  program3 : Program
  program3 = prog
    (declarations program2)
    (`case (term program2) · ((((` "Left" # here ◦ `Bool) ◦ `ℕ) · `false)) of⟦
      ((` "P" # there (there here)  ∶ ("a" ∷ "b" ∷  []) ⟶ (`if ` "a" # there here then ` "b" # here else `zero ))  ∷ [])
    ⟧)


  evaluator3 : Evaluator ProgramCheck
  evaluator3 = checkProgram program3 `ℕ

  check3 : Check evaluator3
  check3 = pass

  {-
    program29 :: List (List (List A)) -> Int
    program29 = \(x :: List (List (List A)) -> Int) -> case x of
      Nil -> 0
      Cons v t -> 
        case v of
          Nil -> 0
          Cons v t ->
            case v of
              Cons v t -> v
              Nil -> 0
  -}
  program29 : Program
  program29 = prog
    (declarations program)
    (Λ ƛ "x" ∶ T "List" (T "List" (T "List" (TVar 0 ∷ []) ∷ []) ∷ []) ⇒ 
      `case ` "x" # here of⟦ 
        ((` "Nil" # there (there (there (there here)))  ∶ [] ⟶ ` "Nothing" # there (there here) ◦ TVar 0) ∷
        ((` "Cons" # there (there (there here))  ∶ ("v" ∷ "t" ∷  []) ⟶ 
          `case ` "v" # there here of⟦ 
            ((` "Nil" # there (there (there (there (there (there here)))))  ∶ [] ⟶ ` "Nothing" # there (there (there (there here))) ◦ TVar 0) ∷
            ((` "Cons" # there (there (there (there (there here)))) ∶ ("v" ∷ "t" ∷  []) ⟶ 
              `case ` "v" # there here of⟦ 
                ((` "Cons" # there (there (there (there (there (there (there here))))))  ∶ ("v" ∷ "t" ∷  []) ⟶ ` "Just" # there (there (there (there (there (there (there here)))))) ◦ TVar 0 · ` "v" # there here) ∷
                ((` "Nil" # there (there (there (there (there (there (there (there here)))))))  ∶ [] ⟶ ` "Nothing" # there (there (there (there (there (there here))))) ◦ TVar 0) ∷ [])) 
              ⟧) ∷ [])) 
          ⟧) ∷ [])) 
      ⟧)


  evaluator29 : Evaluator ProgramCheck
  evaluator29 = checkProgram program29 (`∀ (T "List" (T "List" (T "List" (TVar 0 ∷ []) ∷ []) ∷ []) ⇒ T "Maybe" (TVar 0 ∷ [])))

  check29 : Check evaluator29
  check29 = pass

  {-
    program30 :: List (List (List A)) -> Int
    program30 = program29 Cons (Cons (Cons 1 Nil) Nil) Nil
  -}
  program30 : Program
  program30 = prog
    (declarations program29)
    (term program29 ◦ `ℕ 
    · (` "Cons" # there (there here) ◦ (T "List" (T "List" (`ℕ ∷ []) ∷ [])) 
    · (` "Cons" # there (there here) ◦ (T "List" (`ℕ ∷ [])) 
    · (` "Cons" # there (there here) ◦ `ℕ · `zero · (` "Nil" # there (there (there here)) ◦ `ℕ)) 
    · (` "Nil" # there (there (there here)) ◦ (T "List" (`ℕ ∷ [])))) · (` "Nil" # there (there (there here)) ◦ (T "List" (T "List" (`ℕ ∷ []) ∷ [])))))

  evaluator30 : Evaluator ProgramCheck
  evaluator30 = checkProgram program30 (T "Maybe" (`ℕ ∷ []))

  check30 : Check evaluator30
  check30 = pass

  -- INCORRECT PROGRAMS
  -- application to type abstracted function
  program4 : Program
  program4 = prog
    (declarations program2)
    (` "Left" # here · `zero)

  evaluator4 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator4 = inferProgram program4

  check4 : Check evaluator4
  check4 = fail "application head should have a function type: ∀ ∀ TVar suc zero ⇒ Either [TVar suc zero, TVar zero]"
  
  -- application with wrong type
  program5 : Program
  program5 = prog
    (declarations program2)
    (((` "Left" # here ◦ `Bool) ◦ `ℕ) · `zero)

  evaluator5 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator5 = inferProgram program5

  check5 : Check evaluator5
  check5 = fail "unequal types: ℕ, Bool"

  -- case match with non adt
  program6 : Program
  program6 = prog 
    []
    `case `zero of⟦ [] ⟧

  evaluator6 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator6 = inferProgram program6

  check6 : Check evaluator6
  check6 = fail "can not pattern match on non-adt"
  
  -- case match with constructor for wrong type
  program8 : Program
  program8 = prog
    (declarations program2)
    (ƛ "x" ∶ T "Either" (`Bool ∷ `ℕ ∷ []) ⇒ 
      `case ` "x" # here of⟦ 
        ((` "Left" # there here  ∶ ("v" ∷  []) ⟶ (((` "P" # there (there (there (there here)))  ◦ `Bool) ◦ `ℕ) · ` "v" # here · `zero)) ∷
        ((` "P" # there (there (there here)) ∶ ("v" ∷ "b" ∷  []) ⟶ (((` "P" # there (there (there (there (there here))))  ◦ `Bool) ◦ `ℕ) · ` "v" # there here · ` "b" # here))
        ∷ [])) 
      ⟧)

  evaluator8 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator8 = inferProgram program8 
  
  check8 : Check evaluator8
  check8 = fail "unequal types: Pair [Bool, ℕ], Either [Bool, ℕ]"
  -- case match with incomplete list of constructors
  program9 = prog
    ((`data (TC "ADT" 0) `where ((DC "A" []) ∷ (DC "B" []) ∷ [])) ∷ [])
    (`case ` "A" # here of⟦ (
      (` "A" # here ∶ [] ⟶ `zero) ∷ [])
    ⟧)

  evaluator9 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator9 = inferProgram program9 

  check9 : Check evaluator9
  check9 = fail "not found: B"

  -- case match with incorrect number of variables for constructor
  program10 : Program
  program10 = prog
    ((`data (TC "ADT" 0) `where ((DC "A" (`Bool ∷ [])) ∷ [])) ∷ [])
    (`case (` "A" # here · `false) of⟦
      ((` "A" # here  ∶ ("a" ∷ "b" ∷ []) ⟶ (`zero)) ∷ [])
    ⟧)

  evaluator10 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator10 = inferProgram program10

  check10 : Check evaluator10
  check10 = fail "Incorrect number of arguments in pattern"
  -- case match with different return types of bodies
  program11 : Program
  program11 = prog
    ((`data (TC "ADT" 0) `where ((DC "A" []) ∷ (DC "B" []) ∷ [])) ∷ [])
    (`case ` "A" # here of⟦ (
        (` "A" # here ∶ [] ⟶ `zero) ∷ 
        (` "B" # there here ∶ [] ⟶ `false) ∷ []) 
      ⟧)

  evaluator11 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator11 = inferProgram program11

  check11 : Check evaluator11
  check11 = fail "unequal types: ℕ, Bool"

  -- capitalized pattern variables
  program21 : Program
  program21 = prog
    ((`data (TC "ADT" 0) `where ((DC "A" (`ℕ ∷ [])) ∷ [])) ∷ [])
    (`case ` "A" # here · `zero of⟦ (
        (` "A" # here ∶ ("X" ∷ []) ⟶ `zero) ∷ []) 
      ⟧)

  evaluator21 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator21 = inferProgram program21

  check21 : Check evaluator21
  check21 = fail "variables capitalized in pattern"

  -- capitalized lambda variable
  program22 : Program
  program22 = prog
    []
    (ƛ "X" ∶ `ℕ ⇒ `zero)
  
  evaluator22 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator22 = inferProgram program22

  check22 : Check evaluator22
  check22 = fail "capitalized variable"

  -- inexistant type in lambda
  program23 = prog
    []
    (ƛ "x" ∶ T "List" [] ⇒ `zero)

  evaluator23 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator23 = inferProgram program23

  check23 : Check evaluator23
  check23 = fail "Type List not in scope"

  -- not using right number of args in lambda for ADT
  program24 : Program
  program24 = prog
    ((`data (TC "List" 1) `where 
      ((DC "Cons" (TVar 0 ∷ T "List" (TVar 0 ∷ []) ∷ [])) ∷ 
      (DC "Nil" [] ∷ [])))∷ [])
      
    (ƛ "x" ∶ T "List" [] ⇒ ` "x" # here)

  evaluator24 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator24 = inferProgram program24

  check24 : Check evaluator24
  check24 = fail "Type List not well formed"

  -- DATA CONSTRUCTOR FAILURES
  -- free variables in constructor
  program12 : Program
  program12 = prog
    ((`data (TC "ADT" 1) `where ((DC "A" (TVar 1 ∷ []))∷ [])) ∷ [])
    `zero

  evaluator12 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator12 = inferProgram program12

  check12 : Check evaluator12
  check12 = fail "Free type variable"
  
  -- non capitalized type constructor
  program13 : Program
  program13 = prog
    ((`data (TC "adt" 0) `where ((DC "A" [])∷ [])) ∷ [])
    `zero

  evaluator13 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator13 = inferProgram program13

  check13 : Check evaluator13
  check13 = fail "type constructor not capitalized"

  -- non capitalized data constructor
  program14 : Program
  program14 = prog
    ((`data (TC "ADT" 0) `where ((DC "a" [])∷ [])) ∷ [])
    `zero

  evaluator14 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator14 = inferProgram program14

  check14 : Check evaluator14
  check14 = fail "data constructor not capitalized"
  -- duplicate type/constructor name
  program16 : Program
  program16 = prog
    ((`data (TC "A" 0) `where ((DC "B" [])∷ [])) ∷
     (`data (TC "C" 0) `where ((DC "A" []) ∷ [])) ∷ [])
    `zero

  evaluator16 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator16 = inferProgram program16

  check16 : Check evaluator16
  check16 = fail "duplicate type/data constructors"
  -- nonexistant type as arg
  program18 : Program
  program18 = prog
    ((`data (TC "ADT" 0) `where ((DC "A" (T "NonExistant" [] ∷ [])) ∷ [])) ∷ [])
    `zero

  evaluator18 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator18 = inferProgram program18

  check18 : Check evaluator18
  check18 = fail "Type NonExistant not in scope"
  
  -- wrong number of typevariables for type constructor
  program19 : Program
  program19 = prog
    ((`data (TC "A" 1) `where ((DC "Construclctor1" [])∷ [])) ∷
     (`data (TC "B" 0) `where ((DC "Constructor2" ((T "A" []) ∷ [])) ∷ [])) ∷ [])
    `zero

  evaluator19 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator19 = inferProgram program19

  check19 : Check evaluator19
  check19 = fail "Type A not well formed"
 
 -- KIND CHECK FAILURES
 -- left arrow fail
  program25 : Program
  program25 = prog
    []
    (ƛ "x" ∶ TVar 0 ⇒ `zero)

  evaluator25 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator25 = inferProgram program25

  check25 : Check evaluator25
  check25 = fail "Free type variable"
 -- right arrow fail
  program26 : Program
  program26 = prog
    []
    (ƛ "x" ∶ `ℕ ⇒ (Λ `zero) ◦ TVar 0)

  evaluator26 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator26 = inferProgram program26

  check26 : Check evaluator26
  check26 = fail "Free type variable"
 -- forall fail
  program27 : Program
  program27 = prog
    []
    (Λ (Λ `zero) ◦ TVar 1)

  evaluator27 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator27 = inferProgram program27

  check27 : Check evaluator27
  check27 = fail "Free type variable"
  -- fail in type variable parameter
  program28 : Program
  program28 = prog
    ((`data TC "A" 3 `where ((DC "B" []) ∷ [])) ∷ [])
    (ƛ "x" ∶ T "A" (`ℕ ∷ `ℕ ∷ TVar 1 ∷ []) ⇒ `zero)
    
  evaluator28 : Evaluator (Σ[ t ∈ Type ] ProgramCheck )
  evaluator28 = inferProgram program28

  check28 : Check evaluator28
  check28 = fail "Free type variable" 