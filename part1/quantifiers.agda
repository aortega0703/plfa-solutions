module plfa-solutions.part1.quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa-solutions.part1.isomorphism using (_≃_; extensionality)
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
