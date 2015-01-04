module prelude where

record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B fst
   

_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

  
data Void : Set where
