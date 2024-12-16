module ND where
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; cong; sym; subst; inspect; [_]; cong₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.String using (String; _≟_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Collection

infixl 17 _∧'_
infixl 17 _∨'_
infixr 16 _→'_
infix 18 ¬'_

data Formula : Set where
  V : String → Formula
  ⊥' : Formula
  _∧'_ : Formula → Formula → Formula
  _∨'_ : Formula → Formula → Formula
  _→'_ : Formula → Formula → Formula
  ¬'_ : Formula → Formula

V-inv : ∀ {x y} → V x ≡ V y → x ≡ y
V-inv {x} {.x} refl = refl
∧'-inv : ∀ {a b a₁ b₁} → a ∧' a₁ ≡ b ∧' b₁ → a ≡ b × a₁ ≡ b₁
∧'-inv refl = ⟨ refl , refl ⟩ 
∨'-inv : ∀ {a b a₁ b₁} → a ∨' a₁ ≡ b ∨' b₁ → a ≡ b × a₁ ≡ b₁
∨'-inv refl = ⟨ refl , refl ⟩ 
→'-inv : ∀ {a b a₁ b₁} → a →' a₁ ≡ b →' b₁ → a ≡ b × a₁ ≡ b₁
→'-inv refl = ⟨ refl , refl ⟩ 
¬'-inv : ∀ {x y} → ¬' x ≡ ¬' y → x ≡ y
¬'-inv {x} {.x} refl = refl

_≟'_ : (a b : Formula) → Dec (a ≡ b)
V x ≟' V x₁ with x ≟ x₁
...            | yes y = yes (cong V y)
...            | no n = no λ x₂ → n (V-inv x₂)
V x ≟' ⊥' = no (λ ())
V x ≟' (b ∧' b₁) = no (λ ())
V x ≟' (b ∨' b₁) = no (λ ())
V x ≟' (b →' b₁) = no (λ ())
V x ≟' (¬' b) = no (λ ())
⊥' ≟' V x = no (λ ())
⊥' ≟' ⊥' = yes refl
⊥' ≟' (b ∧' b₁) = no (λ ())
⊥' ≟' (b ∨' b₁) = no (λ ())
⊥' ≟' (b →' b₁) = no (λ ())
⊥' ≟' (¬' b) = no (λ ())
(a ∧' a₁) ≟' V x = no (λ ())
(a ∧' a₁) ≟' ⊥' = no (λ ())
(a ∧' a₁) ≟' (b ∧' b₁) with a ≟' b | a₁ ≟' b₁ 
...                       | yes y1 | yes y2 = yes (cong₂ _∧'_ y1 y2)
...                       | no n   | _ = no λ x → n (proj₁ (∧'-inv x))
...                       | _      | no n = no λ x → n (proj₂ (∧'-inv x))
(a ∧' a₁) ≟' (b ∨' b₁) = no (λ ())
(a ∧' a₁) ≟' (b →' b₁) = no (λ ())
(a ∧' a₁) ≟' (¬' b) = no (λ ())
(a ∨' a₁) ≟' V x = no (λ ())
(a ∨' a₁) ≟' ⊥' = no (λ ())
(a ∨' a₁) ≟' (b ∧' b₁) = no (λ ())
(a ∨' a₁) ≟' (b ∨' b₁) with a ≟' b | a₁ ≟' b₁ 
...                       | yes y1 | yes y2 = yes (cong₂ _∨'_ y1 y2)
...                       | no n   | _ = no λ x → n (proj₁ (∨'-inv x))
...                       | _      | no n = no λ x → n (proj₂ (∨'-inv x))
(a ∨' a₁) ≟' (b →' b₁) = no (λ ())
(a ∨' a₁) ≟' (¬' b) = no (λ ())
(a →' a₁) ≟' V x = no (λ ())
(a →' a₁) ≟' ⊥' = no (λ ())
(a →' a₁) ≟' (b ∧' b₁) = no (λ ())
(a →' a₁) ≟' (b ∨' b₁) = no (λ ())
(a →' a₁) ≟' (b →' b₁) with a ≟' b | a₁ ≟' b₁ 
...                       | yes y1 | yes y2 = yes (cong₂ _→'_ y1 y2)
...                       | no n   | _ = no λ x → n (proj₁ (→'-inv x))
...                       | _      | no n = no λ x → n (proj₂ (→'-inv x))
(a →' a₁) ≟' (¬' b) = no (λ ())
(¬' a) ≟' V x = no (λ ())
(¬' a) ≟' ⊥' = no (λ ())
(¬' a) ≟' (b ∧' b₁) = no (λ ())
(¬' a) ≟' (b ∨' b₁) = no (λ ())
(¬' a) ≟' (b →' b₁) = no (λ ())
(¬' a) ≟' (¬' b) with a ≟' b
...            | yes y = yes (cong (¬'_) y)
...            | no n = no λ x₂ → n (¬'-inv x₂)

-- valuation
Valuation : Set 
Valuation = String → Bool

-- truth value
infix 10 ⟦_⟧_
⟦_⟧_ : Formula → Valuation → Bool
⟦ V x ⟧ v = v x
⟦ ⊥' ⟧ v = false
⟦ x ∧' x₁ ⟧ v = ⟦ x ⟧ v ∧ ⟦ x₁ ⟧ v
⟦ x ∨' x₁ ⟧ v = ⟦ x ⟧ v ∨ ⟦ x₁ ⟧ v
⟦ x →' x₁ ⟧ v = not (⟦ x ⟧ v) ∨ (⟦ x₁ ⟧ v)
⟦ ¬' x ⟧ v = not (⟦ x ⟧ v)

data Tautology : Formula → Set where
  form : ∀ {x} → (∀ (v : Valuation) → ⟦ x ⟧ v ≡ true) → Tautology x

φ ψ σ : Formula
φ = V "φ"
ψ = V "ψ"
σ = V "σ"

_ : Tautology ((φ →' ψ) ∨' (ψ →' φ)) 
_ = form go
  where
    go : ∀ (v : Valuation) → ⟦ (φ →' ψ) ∨' (ψ →' φ) ⟧ v ≡ true
    go v with v "φ" | v "ψ" 
    ...    | true   | true = refl
    ...    | false  | true = refl
    ...    | true   | false = refl
    ...    | false  | false = refl

Context : Set₁
Context = Collection→ Formula

-- rules for natrual deduction
infix 10 _⊢ⁿ_
data _⊢ⁿ_ : Context → Formula → Set₁ where
  form : ∀ f → ⟪ f ⟫ ⊢ⁿ f 

  weaken : ∀ {Γ Δ φ} 
           → Γ ⊂ Δ → Γ ⊢ⁿ φ 
           -----------------
           → Δ ⊢ⁿ φ

  ∧I : ∀ {Γ₁ Γ₂ φ ψ}
       → Γ₁ ⊢ⁿ φ → Γ₂ ⊢ⁿ ψ 
       ---------------------
       → (Γ₁ ∪ Γ₂) ⊢ⁿ φ ∧' ψ

  ∧Eₗ : ∀ {Γ φ ψ}
        → Γ ⊢ⁿ φ ∧' ψ
        -----------------
        → Γ ⊢ⁿ φ

  ∧Eᵣ : ∀ {Γ φ ψ} 
        → Γ ⊢ⁿ φ ∧' ψ
        ---------------
        → Γ ⊢ⁿ ψ

  ∨Iₗ : ∀ {Γ φ ψ} 
        → Γ ⊢ⁿ φ
        --------------
        → Γ ⊢ⁿ φ ∨' ψ

  ∨Iᵣ : ∀ {Γ φ ψ} 
        → Γ ⊢ⁿ ψ
        --------------
        → Γ ⊢ⁿ φ ∨' ψ
  
  ∨E : ∀ {Γ₁ Γ₂ Γ₃ φ ψ σ} 
       → Γ₁ ⊢ⁿ φ ∨' ψ
       → Γ₂ ⊢ⁿ σ
       → Γ₃ ⊢ⁿ σ
       --------------------------------
       → Γ₁ ∪ (Γ₂ - φ) ∪ (Γ₃ - ψ) ⊢ⁿ σ
  
  →I : ∀ {Γ φ ψ}
       → Γ ⊢ⁿ ψ
       ------------------
       → Γ - φ ⊢ⁿ φ →' ψ

  →E : ∀ {Γ₁ Γ₂ φ ψ}
       → Γ₁ ⊢ⁿ φ →' ψ 
       → Γ₂ ⊢ⁿ φ
       --------------- 
       → Γ₁ ∪ Γ₂ ⊢ⁿ ψ

  ¬I : ∀ {Γ φ}
       → Γ ⊢ⁿ ⊥'
       -----------------
       → Γ - φ ⊢ⁿ ¬' φ

  ¬E : ∀ {Γ₁ Γ₂ φ}
       → Γ₁ ⊢ⁿ ¬' φ
       → Γ₂ ⊢ⁿ φ
       ----------------
       → Γ₁ ∪ Γ₂ ⊢ⁿ ⊥'
  
  ⊥E : ∀ {Γ φ}
       → Γ ⊢ⁿ ⊥'
       ----------
       → Γ ⊢ⁿ φ
  
  RAA : ∀ {Γ φ}
        → Γ ⊢ⁿ ⊥'
        ----------------
        → Γ - ¬' φ ⊢ⁿ φ

-- examples
ex1 : ⟪ φ →' ψ →' σ , φ ∧' ψ ⟫ ⊢ⁿ σ
ex1 = weaken lemma (→E (→E (form (φ →' ψ →' σ)) (∧Eₗ (form (φ ∧' ψ)))) (∧Eᵣ (form (φ ∧' ψ))))
  where 
    lemma : ⟪ φ →' ψ →' σ ⟫ ∪ ⟪ φ ∧' ψ ⟫ ∪ ⟪ φ ∧' ψ ⟫ ⊂ ⟪ φ →' ψ →' σ , φ ∧' ψ ⟫
    lemma x x₁ x₂ = x₂ (λ x₃ x₄ → x₁ x₂ x₄)

ex2 : ⟪ φ →' ψ →' σ ⟫ ⊢ⁿ φ ∧' ψ →' σ
ex2 = weaken l (→I ex1)
  where
    l : ⟪ φ →' ψ →' σ , φ ∧' ψ ⟫ - φ ∧' ψ ⊂ ⟪ φ →' ψ →' σ ⟫
    l x x₁ x₂ = x₁ λ x₃ x₄ → x₄ x₂ x₃

ex3 : ∅ ⊢ⁿ (φ →' ψ →' σ) →' φ ∧' ψ →' σ
ex3 = weaken l (→I ex2)
  where
    l : ⟪ φ →' ψ →' σ ⟫ - φ →' ψ →' σ ⊂ ∅
    l x x₁ x₂ = x₁ λ x₃ x₄ → x₃ x₄

-- provable
infix 10 ⊢ⁿ_
data ⊢ⁿ_ : Formula → Set₁ where
  proof : ∀ {φ} → ∅ ⊢ⁿ φ → ⊢ⁿ φ

ex3' : ⊢ⁿ (φ →' ψ →' σ) →' φ ∧' ψ →' σ
ex3' = proof ex3

-- semantical consequence
infix 10 _⊨_
data _⊨_ : Context → Formula → Set₁ where
  ⊨-intro : ∀ {Γ φ}
            → (∀ {v} → (∀ {r} → r ∈ Γ → ⟦ r ⟧ v ≡ true) → ⟦ φ ⟧ v ≡ true)
            → Γ ⊨ φ

soundness : ∀ {Γ φ} → Γ ⊢ⁿ φ → Γ ⊨ φ
soundness (form f) = ⊨-intro (λ x → x refl)
soundness (weaken x x₁) = {!   !}
soundness (∧I x x₁) = {!   !}
soundness (∧Eₗ x) = {!   !}
soundness (∧Eᵣ x) = {!   !}
soundness (∨Iₗ x) = {!   !}
soundness (∨Iᵣ x) = {!   !}
soundness (∨E x x₁ x₂) = {!   !}
soundness (→I {Γ} {φ} {ψ} x) = ⊨-intro go
  where
    go : {v : Valuation} → ({r : Formula} 
       → r ∈ Γ - φ → ⟦ r ⟧ v ≡ true) → not (⟦ φ ⟧ v) ∨ ⟦ ψ ⟧ v ≡ true
    go {v} x' with soundness x | ⟦ φ ⟧ v | inspect (⟦ φ ⟧_) v
    ...            | _         | false   | _                   = refl
    ...            | ⊨-intro k | true    | [ ⟦φ⟧v≡t ]          = k (lemma x' ⟦φ⟧v≡t) 
      where 
        lemma : ∀ {Γ φ} 
          → (∀ {r} → r ∈ Γ - φ → ⟦ r ⟧ v ≡ true)
          → ⟦ φ ⟧ v ≡ true
          → (∀ {r} → r ∈ Γ → ⟦ r ⟧ v ≡ true)
        lemma {Γ} {φ} x x₁ {r} x₂ with r ≟' φ 
        ...                          | no k    = x {r} (λ x₄ → x₄ k x₂)
        ...                          | yes k   = subst (λ x → ⟦ x ⟧ v ≡ true) (sym k) x₁
soundness (→E x x₁) = {!   !}
soundness (¬I x) = {!   !}
soundness (¬E x x₁) = {!   !}
soundness (⊥E x) = {!   !}
soundness (RAA x) = {!   !}