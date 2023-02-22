module plfa-solutions.part1.quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
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
