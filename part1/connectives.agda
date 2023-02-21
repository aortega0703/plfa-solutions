module plfa-solutions.part1.connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa-solutions.part1.isomorphism using (_≃_; _≲_;
  extensionality; _⇔_)
open plfa-solutions.part1.isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

⇔≃× : ∀ {A B : Set} → (A ⇔ B) ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to      = λ A⇔B → ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩
    ; from    = λ A→B×B→A →
      record
        { to = proj₁ A→B×B→A
        ; from = proj₂ A→B×B→A
        }
    ; from∘to = λ A⇔B → refl
    ; to∘from = λ A→B×B→A →
      begin
        ⟨ proj₁ A→B×B→A , proj₂ A→B×B→A ⟩
      ≡⟨ η-× A→B×B→A ⟩
        A→B×B→A
      ∎
    }
