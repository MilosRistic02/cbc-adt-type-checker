# Correct-by-Construction Type Checking

This repository contains a correct-by-construction type checker for a toy language involving algebraic data types, pattern matching and polymorphism. The toy language is based on System F, and the ADT syntax is based on the Haskell syntax.

## Setup

To get the code working, follow these steps:

1. Install Agda by following [the instruction on the website](https://agda.readthedocs.io/en/latest/getting-started/installation.html).
2. Install the `standard-library` using the [installation guide](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md). 
3. To test that everything works, compile the `src/Programs.agda` file.

For development, Agda version 2.6.4.1 and standard library version 2.0 were used.

## Overview

The type checker is built up using various components which are documented uses comments.
A set of small example programs can be found in the `Programs` module.

## Syntax
```
Variables         x, y, z
Type variables    α, β
Type constructors T
Data constructors C

Programs    prog ::= d* t
Data types  d ::= data T α* where (C σ*)*
Atoms       v ::= x | C
Terms       t, u ::= v | λ x : σ . t | Λα.t | t u | t σ
              | zero | suc t | true | false
              | case t of ⟦ p* ⟧
Patterns    p ::= C x* → t

Types         σ, φ ::= ∀α.σ | σ → φ | T σ* | α | Bool | N
Type context  Γ, ∆ ::= ∅ | Γ, σ | Γ, v : σ
```
The syntax of the toy language is given above where * indicates a sequence of the element. Using Agda's Unicode support it was translated to one the closely resembles the original syntax, as can be seen in `Program.Type` and `Program.Term`.

## Declaration Conversion
Since the paper focussed on type-checking terms, we did not discuss the implementation of the conversion of declarations in detail. However, it was implemented as it allows for conciser example programs, as seen in the `Programs` module. The relevant data types can be found in `TypeChecker.ProgramCheck`, and the conversion of a set of declarations to a context can be found in `Util.Convert`. 

We first make sure that all data constructors are valid, which is the case if all type variables used as arguments are present in their respective type constructor and if adts are declared. After that, we check that all types and constructors are unique. Finally, we convert these declarations to a `Context` and `TyContext`, and proceed as discussed in the paper. The style of programming is the same as for the type-checker itself, and we trust that using the information from the paper the implementation can be understood. 
