module plfa-solutions.part1.quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _∸_)
open import Data.Nat.Properties using (m+[n∸m]≡n; +-comm; ≤-trans; ≤-refl; +-suc)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa-solutions.part1.isomorphism using (_≃_; extensionality;
  _≲_; _⇔_)

open import Function using (_∘_)

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
  { to = to
  ; from = from
  ; from∘to = λ a→[Ba×Ca] → refl
  ; to∘from = λ [a→Ba]×[a→Ca] → refl
  }
  where
    to :  ∀ {A : Set} {B C : A → Set} →
         (∀ (x : A) → B x × C x) →
         (∀ (x : A) → B x) × (∀ (x : A) → C x)
    to a→[Ba×Ca] = ⟨ (λ a → proj₁ (a→[Ba×Ca] a)) , (λ a → proj₂ (a→[Ba×Ca] a)) ⟩

    from : ∀ {A : Set} {B C : A → Set} →
         (∀ (x : A) → B x) × (∀ (x : A) → C x) →
         (∀ (x : A) → B x × C x)
    from ⟨ a→[Ba] , a→[Ca] ⟩ = λ a → ⟨ a→[Ba] a , a→[Ca] a ⟩

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ a→Ba) = λ a → inj₁ (a→Ba a)
⊎∀-implies-∀⊎ (inj₂ a→Ca) = λ a → inj₂ (a→Ca a)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri
  
postulate
  extensionality-tri : ∀ {B : Tri → Set}
    → (f g : ∀ (x : Tri) → B x)
    → (∀ (x : Tri) → f x ≡ g x)
      -------------------------
    → f ≡ g

∀-× : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× =
  record
  { to = to
  ; from = from
  ; from∘to = λ t→Bt → extensionality-tri ((from ∘ to) t→Bt) t→Bt λ{ aa → refl; bb → refl; cc → refl}
  ; to∘from = λ { ⟨ Ba , ⟨ Bb , Bc ⟩ ⟩ → refl}
  }
  where
    to : {B : Tri → Set} → (∀ (x : Tri) → B x) → (B aa × B bb × B cc)
    to = λ t→Bt → ⟨ t→Bt aa , ⟨ t→Bt bb , t→Bt cc ⟩ ⟩

    from : {B : Tri → Set} → (B aa × B bb × B cc) → (∀ (x : Tri) → B x)
    from = λ {⟨ Ba , ⟨ Bb , Bc ⟩ ⟩ → λ {aa → Ba ; bb → Bb ;cc → Bc}}

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
  { to = λ { ⟨ a , (inj₁ Ba) ⟩ → inj₁ ⟨ a , Ba ⟩
           ; ⟨ a , (inj₂ Ca) ⟩ → inj₂ ⟨ a , Ca ⟩ }
  ; from = λ { (inj₁ ⟨ a , Ba ⟩) → ⟨ a , inj₁ Ba ⟩
             ; (inj₂ ⟨ a , Ca ⟩) → ⟨ a , inj₂ Ca ⟩ }
  ; from∘to = λ { ⟨ a , inj₁ x ⟩ → refl
                ; ⟨ a , inj₂ y ⟩ → refl }
  ; to∘from = λ { (inj₁ ⟨ a , Ba ⟩ ) → refl
                ; (inj₂ ⟨ a , Ca ⟩ ) → refl }
  }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ Ba , Ca ⟩ ⟩ = ⟨ ⟨ a , Ba ⟩ , ⟨ a , Ca ⟩ ⟩

∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ =
  record
  { to = λ { ⟨ aa , Bt ⟩ → inj₁ Bt
           ; ⟨ bb , Bt ⟩ → inj₂ (inj₁ Bt)
           ; ⟨ cc , Bt ⟩ → inj₂ (inj₂ Bt)
           }
  ; from = λ { (inj₁ Ba)        → ⟨ aa , Ba ⟩
             ; (inj₂ (inj₁ Bb)) → ⟨ bb , Bb ⟩
             ; (inj₂ (inj₂ Bc)) → ⟨ cc , Bc ⟩ }
  ; from∘to = λ { ⟨ aa , Bt ⟩ → refl
                ; ⟨ bb , Bt ⟩ → refl
                ; ⟨ cc , Bt ⟩ → refl }
  ; to∘from = λ { (inj₁ Ba)        → refl
                ; (inj₂ (inj₁ Bb)) → refl
                ; (inj₂ (inj₂ Bc)) → refl }
  }

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)

----------------------------------------------------------

≤→∃+ : ∀ (y z : ℕ) → y ≤ z → Σ ℕ (λ x → x + y ≡ z)
≤→∃+ y z y≤z =
  ⟨ z ∸ y ,
    begin
      (z ∸ y) + y
    ≡⟨ +-comm (z ∸ y) y ⟩
      y + (z ∸ y)
    ≡⟨ m+[n∸m]≡n y≤z ⟩
      z
    ∎
  ⟩

∃+→≤ : ∀ {y z : ℕ} → Σ ℕ (λ x → x + y ≡ z) → y ≤ z
∃+→≤ {zero} {.(x + zero)} ⟨ x , refl ⟩ = _≤_.z≤n
∃+→≤ {suc y} {.(zero + suc y)} ⟨ zero , refl ⟩ =
  _≤_.s≤s (∃+→≤ {y} {y} ⟨ 0 , refl ⟩)
∃+→≤ {suc y} {.(suc x + suc y)} ⟨ suc x , refl ⟩ =
  _≤_.s≤s (∃+→≤ {y} {x + suc y} ⟨ suc x , Eq.sym (+-suc x y) ⟩)

∃-+-≤ : ∀ (y z : ℕ) → (y ≤ z) ⇔ (Σ ℕ (λ x → x + y ≡ z))
∃-+-≤ y z = record { to = ≤→∃+ y z ; from = ∃+→≤ }

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }

∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ {A} {b} ⟨ x , ¬bx ⟩ = λ x₁ → ¬bx (x₁ x)
