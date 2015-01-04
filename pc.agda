{-# OPTIONS --type-in-type #-}

module pc where

open import poset
open import setoid
open import prelude

-- | A propositional language
record Language : Set where
  constructor language⟨_⟩
  field
    Φ₀ : Set -- ^ The atomic propositions

  -- | Sentences in a language
  data Φ : Set where
    ⌞_⌟ : (π : Φ₀) → Φ
    ∼_ : Φ → Φ
    _∧_ : Φ → Φ → Φ
    _∨_ : Φ → Φ → Φ
    _⊃_ : Φ → Φ → Φ
    
  Valuation : (ℙ : Poset) → Set
  Valuation ℙ = Φ₀ → ℙ ⁺
  
  record Model : Set where
    constructor model⟨_,_⟩
    field
      poset : Poset
      ⟦_⟧ : Valuation poset
      
-- | Kripke semantics for propositional calculus
module Semantics {L : Language} where
  open Language L
 
  private
    open Model {{...}} renaming (poset to ℙ)
    module ℙ {{_}} = Poset ℙ
    open ℙ renaming (car to P)

  _⊨[_]_ : (M : Model) (p : ∣ P ∣) (α : Φ) → Set
  M ⊨[ p ] ⌞ π ⌟ = let ⟨ φ , _ ⟩ = ⟦ π ⟧ in φ p
  M ⊨[ p ] ∼ α = (q : ∣ P ∣) → p ⊑ q → M ⊨[ q ] α → Void
  M ⊨[ p ] (α ∧ β) = (M ⊨[ p ] α) × (M ⊨[ p ] β)
  M ⊨[ p ] (α ∨ β) = (M ⊨[ p ] α) + (M ⊨[ p ] β)
  M ⊨[ p ] (α ⊃ β) = (q : ∣ P ∣) → p ⊑ q → M ⊨[ q ] α → M ⊨[ q ] β

