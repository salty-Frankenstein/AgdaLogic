module ND where
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; cong; sym; subst; inspect; [_]; cong₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃; Σ-syntax; ∃-syntax; map-Σ) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.String using (String; _≟_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; T)
open import Data.Bool.Properties using (T-≡; T-∨; T-∧; ∨-zeroʳ; not-¬; not-injective)
open import Function.Bundles using (Func; _⇔_)
open import Function.Base using (_∘_)
open import Function.Properties.Equivalence using (⇔⇒⟶; ⇔⇒⟵)
open import Level
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

⇔⇒→ : ∀ {a b} → _⇔_ {0ℓ} {0ℓ} a b → a → b
⇔⇒→ = Func.to ∘ ⇔⇒⟶
⇔⇒← : ∀ {a b} → _⇔_ {0ℓ} {0ℓ} a b → b → a
⇔⇒← = Func.to ∘ ⇔⇒⟵

-- semantical consequence
infix 10 _⊨_
data _⊨_ : Context → Formula → Set₁ where
  ⊨-intro : ∀ {Γ φ}
            → (∀ {v} → (∀ {r} → r ∈ Γ → ⟦ r ⟧ v ≡ true) → ⟦ φ ⟧ v ≡ true)
            → Γ ⊨ φ

Γ-φ∪φ : ∀ {v Γ φ} → (∀ {r} → r ∈ Γ - φ → ⟦ r ⟧ v ≡ true) → ⟦ φ ⟧ v ≡ true
                  → (∀ {r} → r ∈ Γ → ⟦ r ⟧ v ≡ true)
Γ-φ∪φ {v} {Γ} {φ} x x₁ {r} x₂ with r ≟' φ 
...                          | no k    = x {r} (λ x₄ → x₄ k x₂)
...                          | yes k   = subst (λ x → ⟦ x ⟧ v ≡ true) (sym k) x₁

×→∧' : ∀ a b → a ≡ true × b ≡ true → a ∧ b ≡ true
×→∧' _ _ ⟨ x , x₁ ⟩ = ⇔⇒→ T-≡ (⇔⇒← T-∧ ⟨ ⇔⇒← T-≡ x , ⇔⇒← T-≡ x₁ ⟩)
∧'→× : ∀ a b → a ∧ b ≡ true → a ≡ true × b ≡ true
∧'→× _ _ x using k <- ⇔⇒→ T-∧ (⇔⇒← T-≡ x) = ⟨ ⇔⇒→ T-≡ (proj₁ k) , ⇔⇒→ T-≡ (proj₂ k) ⟩
∨'→⊎ : ∀ a b → a ∨ b ≡ true → a ≡ true ⊎ b ≡ true
∨'→⊎ _ _ t = map (⇔⇒→ T-≡) (⇔⇒→ T-≡) (⇔⇒→ T-∨ (⇔⇒← T-≡ t))
⊎→∨' : ∀ a b → a ≡ true ⊎ b ≡ true → a ∨ b ≡ true 
⊎→∨' a b x with x
... | inj₁ y = cong (_∨ b) ((⇔⇒→ T-≡) (⇔⇒← T-≡ y))
... | inj₂ y = trans (cong (a ∨_) ((⇔⇒→ T-≡) (⇔⇒← T-≡ y))) (∨-zeroʳ a)

soundness : ∀ {Γ φ} → Γ ⊢ⁿ φ → Γ ⊨ φ
soundness (form f) = ⊨-intro (λ x → x refl)
soundness (weaken {Γ} {Δ} {φ} x x₁) with soundness x₁
...                                    | ⊨-intro k = ⊨-intro (λ x' → k (x' ∘ ⊂-perserve-∈ Γ Δ x))
soundness (∧I {Γ₁} {Γ₂} {φ} {ψ} x x₁) with soundness x | soundness x₁ 
...| ⊨-intro k1  | ⊨-intro k2 = ⊨-intro λ {v} x' → ×→∧' (⟦ φ ⟧ v) (⟦ ψ ⟧ v)
                                                    ⟨ k1 (x' ∘ (∪-perserve-∈ᵣ Γ₁ Γ₂)) 
                                                    , k2 (x' ∘ (∪-perserve-∈ₗ Γ₂ Γ₁)) ⟩
soundness (∧Eₗ {Γ} {φ} {ψ} x) with soundness x 
... | ⊨-intro k = ⊨-intro (λ {v} x' → proj₁ (∧'→× (⟦ φ ⟧ v) (⟦ ψ ⟧ v) (k x')))
soundness (∧Eᵣ {Γ} {φ} {ψ} x) with soundness x 
... | ⊨-intro k = ⊨-intro (λ {v} x' → proj₂ (∧'→× (⟦ φ ⟧ v) (⟦ ψ ⟧ v) (k x')))
soundness (∨Iₗ {Γ} {φ} {ψ} x) with soundness x 
... | ⊨-intro k = ⊨-intro (λ {v} x' → ⊎→∨' (⟦ φ ⟧ v) (⟦ ψ ⟧ v) (inj₁ (k x')))
soundness (∨Iᵣ {Γ} {φ} {ψ} x) with soundness x 
... | ⊨-intro k = ⊨-intro (λ {v} x' → ⊎→∨' (⟦ φ ⟧ v) (⟦ ψ ⟧ v) (inj₂ (k x')))
soundness (∨E {Γ₁} {Γ₂} {Γ₃} {φ} {ψ} {σ} x x₁ x₂) = ⊨-intro go
  where
    lemma1 : ∀ {r} → r ∈ Γ₁ → r ∈ Γ₁ ∪ (Γ₂ - φ) ∪ (Γ₃ - ψ)
    lemma1 = ∪-perserve-∈ᵣ (Γ₁ ∪ (Γ₂ - φ)) (Γ₃ - ψ) ∘ ∪-perserve-∈ᵣ Γ₁ (Γ₂ - φ)

    lemma2 : ∀ {r} → r ∈ Γ₂ - φ → r ∈ Γ₁ ∪ (Γ₂ - φ) ∪ (Γ₃ - ψ)
    lemma2 = ∪-perserve-∈ᵣ (Γ₁ ∪ (Γ₂ - φ)) (Γ₃ - ψ) ∘ ∪-perserve-∈ₗ (Γ₂ - φ) Γ₁

    lemma3 : ∀ {r} → r ∈ Γ₃ - ψ → r ∈ Γ₁ ∪ (Γ₂ - φ) ∪ (Γ₃ - ψ)
    lemma3 = ∪-perserve-∈ₗ (Γ₃ - ψ) (Γ₁ ∪ (Γ₂ - φ))

    go : {v : Valuation} → ({r : Formula} 
      → r ∈ Γ₁ ∪ (Γ₂ - φ) ∪ (Γ₃ - ψ) → ⟦ r ⟧ v ≡ true) → ⟦ σ ⟧ v ≡ true
    go {v} x' with soundness x | soundness x₁ | soundness x₂
    ...          | ⊨-intro k1  | ⊨-intro k2   | ⊨-intro k3 with ∨'→⊎ (⟦ φ ⟧ v) (⟦ ψ ⟧ v) (k1 (x' ∘ lemma1)) in eq
    ...                                                       | inj₁ x = k2 (Γ-φ∪φ (x' ∘ lemma2) x)
    ...                                                       | inj₂ y = k3 (Γ-φ∪φ (x' ∘ lemma3) y)
soundness (→I {Γ} {φ} {ψ} x) = ⊨-intro go
  where
    go : {v : Valuation} → ({r : Formula} 
       → r ∈ Γ - φ → ⟦ r ⟧ v ≡ true) → not (⟦ φ ⟧ v) ∨ ⟦ ψ ⟧ v ≡ true
    go {v} x' with soundness x | ⟦ φ ⟧ v in eq
    ...          | _           | false           = refl
    ...          | ⊨-intro k   | true            = k (Γ-φ∪φ x' eq) 
soundness (→E {Γ₁} {Γ₂} {φ} {ψ} x x₁) with soundness x | soundness x₁ 
...                                      | ⊨-intro k1  | ⊨-intro k2 = ⊨-intro go
  where
    go : {v : Valuation} → ({r : Formula} 
       → r ∈ Γ₁ ∪ Γ₂ → ⟦ r ⟧ v ≡ true) → ⟦ ψ ⟧ v ≡ true
    go {v} x' with ∨'→⊎ (not (⟦ φ ⟧ v)) (⟦ ψ ⟧ v) (k1 (x' ∘ ∪-perserve-∈ᵣ Γ₁ Γ₂)) 
    ... | inj₁ y = ⊥-elim (not-¬ (sym (k2 (x' ∘ ∪-perserve-∈ₗ Γ₂ Γ₁))) (sym y))
    ... | inj₂ y = y
soundness (¬I {Γ} {φ} x) with soundness x
...                         | ⊨-intro k = ⊨-intro go
  where
    go : {v : Valuation} → ({r : Formula} → r ∈ Γ - φ → ⟦ r ⟧ v ≡ true) → ⟦ ¬' φ ⟧ v ≡ true
    go {v} x' with ⟦ φ ⟧ v in eq 
    ...          | false = refl
    ...          | true = k (Γ-φ∪φ x' eq)
soundness (¬E {Γ₁} {Γ₂} {φ} x x₁) with soundness x | soundness x₁
...                                  | ⊨-intro k1  | ⊨-intro k2 
    = ⊨-intro λ x' → ⊥-elim (not-¬ (sym (k2 (x' ∘ ∪-perserve-∈ₗ Γ₂ Γ₁))) 
                                   (sym (k1 (x' ∘ ∪-perserve-∈ᵣ Γ₁ Γ₂))))
soundness (⊥E {Γ} {φ} x) with soundness x 
...                         | ⊨-intro k = ⊨-intro λ x' → ⊥-elim ((⇔⇒← T-≡) (k x'))
soundness (RAA {Γ} {φ} x) with soundness x
...                          | ⊨-intro k = ⊨-intro go
  where
    go : {v : Valuation} → ({r : Formula} 
      → r ∈ Γ - (¬' φ) → ⟦ r ⟧ v ≡ true) → ⟦ φ ⟧ v ≡ true
    go {v} x' with ⟦ ¬' φ ⟧ v in eq 
    ...          | false = not-injective eq
    ...          | true  = ⊥-elim (not-¬ (k (Γ-φ∪φ x' eq)) refl)