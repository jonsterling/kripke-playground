{-# OPTIONS --type-in-type #-}

module setoid where

open import prelude

record is-equivalence-relation {A : Set} (_R_ : A → A → Set) : Set where
  field
    reflexivity : {m : A} → m R m
    symmetry : {m n : A} → m R n → n R m
    transitivity : {m n o : A} → n R o → m R n → m R o

record Setoid : Set where
  field
    car : Set
    eq : car → car → Set
    equiv : is-equivalence-relation eq
  
∣_∣ : (S : Setoid) → Set
∣_∣ = Setoid.car

_∋_∼_ : (S : Setoid) (let open Setoid S) → car → car → Set
S ∋ M ∼ N = let open Setoid S in eq M N
