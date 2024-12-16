module Collection where

open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; cong; sym)


Collection→ : Set → Set₁
Collection→ A = A → Set

infix 5 _∈_ _∉_ 

_∈_ : {A : Set} → A → Collection→ A → Set
a ∈ c = c a 

_∉_ : {A : Set} → A → Collection→ A → Set
a ∉ c = ¬ (a ∈ c)

⟪_⟫ : {A : Set} → A → Collection→ A
⟪ a ⟫ = λ x → x ≡ a

∅ : {A : Set} → Collection→ A
∅ = λ _ → ⊥

infix 4 _⊂_
_⊂_ : {A : Set} → Collection→ A → Collection→ A → Set
a ⊂ b = ∀ x → x ∈ a → ¬(x ∉ b)

infixl 12 _∪_
_∪_ : {A : Set} → Collection→ A → Collection→ A → Collection→ A
a ∪ b = λ x → x ∉ a → ¬ (x ∉ b)

-- some notations
⟪_,_⟫ : {A : Set} → A → A → Collection→ A
⟪ a , b ⟫ = ⟪ a ⟫ ∪ ⟪ b ⟫ 
⟪_,_,_⟫ : {A : Set} → A → A → A → Collection→ A
⟪ a , b , c ⟫ = ⟪ a ⟫ ∪ ⟪ b ⟫ ∪ ⟪ c ⟫ 

infixl 12 _-_
_-_ : {A : Set} → Collection→ A → A → Collection→ A
c - a = λ x → ¬ (x ≢ a → x ∉ c)
