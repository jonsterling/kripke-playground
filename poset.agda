{-# OPTIONS --type-in-type #-}

module poset where

open import setoid
open import prelude

record Preposet : Set where
  field
    car : Setoid
    _⊑_ : ∣ car ∣ → ∣ car ∣ → Set

record is-poset (ℙ : Preposet) : Set where
  open Preposet ℙ

  field
    reflexivity : {p : ∣ car ∣} → p ⊑ p
    antisymmetry : {p q : ∣ car ∣} → p ⊑ q → q ⊑ p → car ∋ p ∼ q
    transitivity : {p q r : ∣ car ∣} → q ⊑ r → p ⊑ q → p ⊑ r
    
record Poset : Set where
  field
    preposet : Preposet
    poset-proof : is-poset preposet 
    
  open Preposet preposet public
  open is-poset poset-proof public
  
  hereditary : (φ : ∣ car ∣ → Set) → Set
  hereditary φ = (p q : ∣ car ∣) → φ p → p ⊑ q → φ q
  
_⁺ : Poset → Set
ℙ ⁺ = Σ (∣ car ∣ → Set) hereditary
  where
    open Poset ℙ
  
