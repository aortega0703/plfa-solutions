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

data ⊤ : Set where

  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

⊤-idˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-idˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-idʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-idʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-idˡ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

⊎-swap : ∀ {A B : Set} → A ⊎ B → B ⊎ A
⊎-swap (inj₁ A) = inj₂ A
⊎-swap (inj₂ B) = inj₁ B

⊎-swap-swap : ∀ {A B : Set} (w : A ⊎ B) → ⊎-swap (⊎-swap w) ≡ w
⊎-swap-swap (inj₁ A) = refl
⊎-swap-swap (inj₂ B) = refl

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ A⊎B → ⊎-swap A⊎B
    ; from = λ B⊎A → ⊎-swap B⊎A
    ; from∘to = λ A⊎B → ⊎-swap-swap A⊎B
    ; to∘from = λ B⊎A → ⊎-swap-swap B⊎A
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = to
    ; from = from
    ; from∘to = from∘to
    ; to∘from = to∘from
    }
  where
    to : ∀ {A B C : Set} → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
    to (inj₁ (inj₁ A)) = inj₁ A
    to (inj₁ (inj₂ B)) = inj₂ (inj₁ B)
    to (inj₂ C)        = inj₂ (inj₂ C)

    from : ∀ {A B C : Set} → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
    from (inj₁ A)        = inj₁ (inj₁ A)
    from (inj₂ (inj₁ B)) = inj₁ (inj₂ B)
    from (inj₂ (inj₂ C)) = inj₂ C

    from∘to : ∀ {A B C : Set} (x : (A ⊎ B) ⊎ C) → from (to x) ≡ x
    from∘to (inj₁ (inj₁ x)) = refl
    from∘to (inj₁ (inj₂ x)) = refl
    from∘to (inj₂ x) = refl

    to∘from : ∀ {A B C : Set} (x : A ⊎ (B ⊎ C)) → to (from x) ≡ x
    to∘from (inj₁ x) = refl
    to∘from (inj₂ (inj₁ x)) = refl
    to∘from (inj₂ (inj₂ x)) = refl

data ⊥ : Set where

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

⊥-idˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-idˡ =
  record
    { to = to
    ; from = λ A → inj₂ A
    ; from∘to = from∘to
    ; to∘from = λ y → refl
    }
  where
    to : ∀ {A : Set} → ⊥ ⊎ A → A
    to (inj₂ A) = A

    from∘to : ∀ {A : Set} (x : ⊥ ⊎ A) → inj₂ (to x) ≡ x
    from∘to (inj₂ x) = refl

⊥-idʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-idʳ =
  record
    { to = to
    ; from = λ A → inj₁ A
    ; from∘to = from∘to
    ; to∘from = λ y → refl
    }
  where
    to : ∀ {A : Set} → A ⊎ ⊥ → A
    to (inj₁ A) = A

    from∘to : ∀ {A : Set} (x : A ⊎ ⊥) → inj₁ (to x) ≡ x
    from∘to (inj₁ x) = refl

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from    = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) } }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ A , C ⟩ = inj₁ A
⊎-weak-× ⟨ inj₂ B , C ⟩ = inj₂ ⟨ B , C ⟩

⊎×-⇒-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-⇒-×⊎ (inj₁ ⟨ A , B ⟩) = ⟨ (inj₁ A) , (inj₁ B) ⟩
⊎×-⇒-×⊎ (inj₂ ⟨ C , D ⟩) = ⟨ (inj₂ C) , inj₂ D ⟩
