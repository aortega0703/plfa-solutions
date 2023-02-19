module plfa-solutions.part1.relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)
-- open Data.Nat.Properties.≤-reasoning using (begin_)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ} → zero ≤ n

  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

≤-trans′ : ∀ (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)

≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

data Total′ : ℕ → ℕ → Set where
  forward′ : ∀ {m n : ℕ} → m ≤ n → Total′ m n
  flipped′ : ∀ {m n : ℕ} → n ≤ m → Total′ m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (m n p : ℕ) → m ≤ n → p + m ≤ p + n
+-monoʳ-≤ m n zero    m≤n  =  m≤n
+-monoʳ-≤ m n (suc p) m≤n  =  s≤s (+-monoʳ-≤ m n p m≤n)

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ m n p m≤n

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ p q n p≤q)

*-monoₗ-≤ : ∀ (m n p : ℕ) → m ≤ n → p * m ≤ p * n
*-monoₗ-≤ m n zero m≤n = z≤n
*-monoₗ-≤ m n (suc p) m≤n  = +-mono-≤ m n (p * m) (p * n) m≤n (*-monoₗ-≤ m n p m≤n)

*-monoᵣ-≤ : ∀ (m n p : ℕ) → m ≤ n → m * p ≤ n * p
*-monoᵣ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoₗ-≤ m n p m≤n

*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoᵣ-≤ m n p m≤n) (*-monoₗ-≤ p q n p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s       (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

<-trans' : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans' zero    _       (suc p) _         _         = z<s
<-trans' (suc m) (suc n) (suc p) (s<s m<n) (s<s n<p) = s<s (<-trans' m n p m<n n<p)

data Trichotomy : ℕ → ℕ → Set where
  tri< : ∀ (m n : ℕ) → m < n → Trichotomy m n
  tri> : ∀ (m n : ℕ) → n < m → Trichotomy m n
  tri≡ : ∀ (m n : ℕ) → m ≡ n → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = tri≡ 0 0 refl
<-trichotomy zero (suc n) = tri< 0 (suc n) z<s
<-trichotomy (suc m) zero = tri> (suc m) 0 z<s
<-trichotomy (suc m) (suc n) with
      <-trichotomy m n
... | tri< m n m<n = tri< (suc m) (suc n) (s<s m<n)
... | tri> m n n<m = tri> (suc m) (suc n) (s<s n<m)
... | tri≡ m n m≡n = tri≡ (suc m) (suc n) (cong suc m≡n)

+-monoₗ-< : ∀ (m n p : ℕ) → m < n → p + m < p + n
+-monoₗ-< m n zero m<n = m<n
+-monoₗ-< m n (suc p) m<n = s<s (+-monoₗ-< m n p m<n)

+-monoᵣ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoᵣ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoₗ-< m n p m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoᵣ-< m n p m<n) (+-monoₗ-< p q n p<q)

if-≤-then-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
if-≤-then-< zero    n       (s≤s m≤n) = z<s
if-≤-then-< (suc m) (suc n) (s≤s m≤n) = s<s (if-≤-then-< m n m≤n)

if-<-then-≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
if-<-then-≤ zero    (suc n) _   = s≤s z≤n
if-<-then-≤ (suc m) (suc n) (s<s m<n) = s≤s (if-<-then-≤ m n m<n)

<-+0ₗ : ∀ (m n : ℕ) → m + 0 < n → m < n
<-+0ₗ m n m<n rewrite +-identityʳ m = m<n

<-+ᵣ : ∀ (m n p : ℕ) → m < n → m < n + p
<-+ᵣ m n zero m<n rewrite +-identityʳ n  = m<n
<-+ᵣ m n (suc p) m<n rewrite (sym (+-identityʳ m)) = +-mono-< m n 0 (suc p) (<-+0ₗ m n m<n) z<s

+-suc : ∀ (n : ℕ) → n + 1 ≡ suc n
+-suc n rewrite +-comm n 1 = refl

<-suc : ∀ (m n : ℕ) → m < n → m < suc n
<-suc m n m<n rewrite (sym (+-suc n)) = <-+ᵣ m n 1 m<n

<-trans-revisited : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans-revisited m (suc n) (suc (suc p)) m<n (s<s n<p) =
  if-≤-then-< m (suc (suc p))
    (≤-trans
      (if-<-then-≤ m (suc n) m<n)
      (if-<-then-≤ n (suc (suc p)) (<-suc n (suc p) n<p)))
