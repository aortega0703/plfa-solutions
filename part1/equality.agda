module plfa-solutions.part1.equality where

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl  =  refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl  =  refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl  =  refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

data _≤_ : ℕ → ℕ → Set where
  z≤s : ∀ {n : ℕ} → zero ≤ n

  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
infix 4 _≤_
postulate
  ≤-refl  : ∀ {n : ℕ} → n ≤ n
  ≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p

module ≤-Reasoning where
  infix  1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _≤-∎
  ≤-begin_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
  ≤-begin x≤y  =  x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
  x ≤⟨⟩ x≤y  =  x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z  =  ≤-trans x≤y y≤z

  _≤-∎ : ∀ (x : ℕ) → x ≤ x
  x ≤-∎  = ≤-refl

open ≤-Reasoning
+-monoʳ-≤ : ∀ (n p q : ℕ) → (p ≤ q) → ((n + p) ≤ (n + q))
+-monoʳ-≤ zero p q p≤q =
  ≤-begin
    zero + p
  ≤⟨ p≤q ⟩
    zero + q
  ≤-∎
+-monoʳ-≤ (suc n) p q p≤q =
  ≤-begin
    (suc n) + p
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    (suc n) + q
  ≤-∎

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

--{-# BUILTIN EQUALITY _≡_ #-}

-- postulate
--   +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

-- even-comm : ∀ (m n : ℕ)
--   → even (m + n)
--     ------------
--   → even (n + m)
-- even-comm m n emn rewrite +-comm m n = emn

