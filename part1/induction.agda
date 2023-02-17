module agda-tutorial.part1.induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (0 + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    0 + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+idᵣ : ∀ (m : ℕ) → m + 0 ≡ m
+idᵣ 0 =
  begin
    0 + 0 ≡⟨⟩
    0     ∎
+idᵣ (suc m) =
  begin
    suc m + 0   ≡⟨⟩
    suc (m + 0) ≡⟨ cong suc (+idᵣ m) ⟩
    suc m       ∎

+idₗ : ∀ (m : ℕ) → 0 + m ≡ m
+idₗ 0 =
  begin
    0 + 0 ≡⟨⟩
    0     ∎
+idₗ (suc m) =
  begin
    0 + suc m   ≡⟨⟩
    suc m ∎
    
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc 0 n =
  begin
    0 + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (0 + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m 0 =
  begin
    m + 0
  ≡⟨ +idᵣ m ⟩
    m
  ≡⟨⟩
    0 + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
     m + (n + p) + q
  ∎

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p
  rewrite
    sym (+-assoc m n p)
    | cong (_+ p) (+-comm m n)
    | +-assoc n m p = refl

*nullᵣ : ∀ (m : ℕ) → m * 0 ≡ 0
*nullᵣ zero = refl
*nullᵣ (suc m) rewrite *nullᵣ m = refl

*idₗ : ∀ (m : ℕ) → 1 * m ≡ m
*idₗ zero = refl
*idₗ (suc m) rewrite cong suc (*idₗ m) = refl

*idᵣ : ∀ (m : ℕ) → m * 1 ≡ m
*idᵣ zero = refl
*idᵣ (suc m) rewrite cong suc (*idᵣ m) = refl

*+distribᵣ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*+distribᵣ zero n p = refl
*+distribᵣ (suc m) n p = begin
  (suc m + n) * p     ≡⟨⟩
  suc (m + n) * p     ≡⟨⟩
  p + (m + n) * p     ≡⟨ cong (p +_) (*+distribᵣ m n p) ⟩
  p + (m * p + n * p) ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
  p + m * p + n * p   ≡⟨⟩
  suc m * p + n * p   ∎

*+distribₗ : ∀ (m n p : ℕ) → m * (n + p) ≡ m * n + m * p
*+distribₗ zero n p = refl
*+distribₗ (suc m) n p =
  begin
    suc m * (n + p)
    ≡⟨⟩
      (n + p) + m * (n + p)
    ≡⟨ +-comm (n + p) (m * (n + p)) ⟩
      m * (n + p) + (n + p)
    ≡⟨ cong (λ x → x + (n + p)) (*+distribₗ m n p) ⟩
      m * n + m * p + (n + p)
    ≡⟨ +-assoc (m * n) (m * p) (n + p) ⟩
      m * n + (m * p + (n + p))
    ≡⟨ cong (λ x → m * n + x) (+-comm (m * p) (n + p)) ⟩
      m * n + ((n + p) + m * p)
    ≡⟨ cong (λ x → m * n + x) (+-assoc n p (m * p)) ⟩
      m * n + (n + (p + m * p))
    ≡⟨ sym (+-assoc (m * n) n (p + m * p)) ⟩
      (m * n + n) + (p + m * p)
    ≡⟨ cong (λ x → (m * n + x) + (p + m * p)) (sym (*idₗ n)) ⟩
      (m * n + 1 * n) + (p + m * p)
    ≡⟨ cong (λ x → x + (p + m * p)) (sym (*+distribᵣ m 1 n)) ⟩
      (m + 1) * n + (p + m * p)
    ≡⟨ cong (λ x → (m + 1) * n + (x + m * p)) (sym (*idₗ p)) ⟩
      (m + 1) * n + (1 * p + m * p)
    ≡⟨ cong (λ x → (m + 1) * n + x) (sym (*+distribᵣ 1 m p)) ⟩
      (m + 1) * n + (1 + m) * p
    ≡⟨ cong (λ x → x * n + (1 + m) * p) (+-comm m 1) ⟩
      (1 + m) * n + (1 + m) * p
    ∎

*assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*assoc zero n p = refl
*assoc (suc m) n p
  rewrite
    *+distribᵣ n (m * n) p
    | cong (n * p +_) (*assoc m n p) = refl


*comm : ∀ (m n : ℕ) → m * n ≡ n * m
*comm zero n =
  begin
    0 * n ≡⟨⟩
    0     ≡⟨ sym (*nullᵣ n) ⟩
    n * 0 ∎
*comm (suc m) zero rewrite *nullᵣ m = refl
*comm (suc m) (suc n) = begin
    suc m * suc n                                 -- definition of multiplication
  ≡⟨⟩
    (1 + m) * (1 + n)
  ≡⟨ *+distribᵣ 1 m (1 + n) ⟩
    1 * (1 + n) + m * (1 + n)
  ≡⟨ cong (λ x → x + m * (1 + n)) (*idₗ (1 + n)) ⟩
    (1 + n) + m * (1 + n)
  ≡⟨ cong (λ x → 1 + n + x) (*+distribₗ m 1 n) ⟩
    (1 + n) + (m * 1 + m * n)
  ≡⟨ cong (λ x → (1 + n) + (x + m * n)) (*idᵣ m) ⟩
    (1 + n) + (m + m * n)
  ≡⟨ cong (λ x → (1 + n) + (x + m * n)) (sym (*idₗ m)) ⟩
    (1 + n) + (1 * m + m * n)
  ≡⟨ sym (+-assoc (1 + n) (1 * m) (m * n)) ⟩
    1 + n + 1 * m + m * n
  ≡⟨ cong (λ x → 1 + n + 1 * m + x) (*comm m n) ⟩
    1 + n + 1 * m + n * m
  ≡⟨ +-assoc (1 + n) (1 * m) (n * m) ⟩
    1 + n + (1 * m + n * m)
  ≡⟨ cong (λ x → 1 + n + x) (sym (*+distribᵣ 1 n m)) ⟩
    1 + n + (1 + n) * m
  ≡⟨⟩
    (1 + n) + (1 + n) * m
  ≡⟨ cong (λ x → x + (1 + n) * m) (sym (*idᵣ (1 + n))) ⟩
    (1 + n) * 1 + (1 + n) * m
  ≡⟨ sym (*+distribₗ (1 + n) 1 m) ⟩
    (1 + n) * (1 + m)
  ∎

∸underflow : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸underflow zero = refl
∸underflow (suc n) = refl

∸+assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸+assoc zero n p =
  begin
    0 ∸ n ∸ p
  ≡⟨ cong (_∸ p) (∸underflow n) ⟩
    0 ∸ p
  ≡⟨ ∸underflow p ⟩
    0
  ≡⟨ sym (∸underflow (n + p)) ⟩
    0 ∸ (n + p)
  ∎
∸+assoc (suc m) zero p =
  begin
    (suc m) ∸ 0 ∸ p
  ≡⟨⟩
    (suc m) ∸ p
  ≡⟨ cong ((suc m) ∸_) (sym (+idₗ p)) ⟩
    (suc m) ∸ (0 + p)
  ∎
∸+assoc (suc m) (suc n) p =
  begin
    (suc m) ∸ (suc n) ∸ p
  ≡⟨⟩
    m ∸ n ∸ p
  ≡⟨ ∸+assoc m n p ⟩
    m ∸ (n + p)
  ∎

^nullₗ : ∀ (m : ℕ) → 0 ^ suc m ≡ 0
^nullₗ zero = refl
^nullₗ (suc m) = refl

^nullᵣ : ∀ (m : ℕ) → m ^ 0 ≡ 1
^nullᵣ m = refl

^suc : ∀ (m n : ℕ) → m ^ suc n ≡ m * m ^ n
^suc m n = refl

^+dist : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^+dist m zero p =
  begin
    m ^ (0 + p)
  ≡⟨ cong (m ^_) (+idₗ p) ⟩
    m ^ p
  ≡⟨ sym (*idₗ (m ^ p))⟩
    1 * (m ^ p)
  ≡⟨ cong (_* (m ^ p)) (sym (^nullᵣ m)) ⟩
    (m ^ 0) * (m ^ p)
  ∎
^+dist m (suc n) p =
  begin
    m ^ (suc n + p)
  ≡⟨⟩
    m ^ (suc (n + p))
  ≡⟨⟩
    m * m ^ (n + p)
  ≡⟨ cong (m *_) (^+dist m n p) ⟩
    m * (m ^ n * m ^ p)
  ≡⟨ sym (*assoc m (m ^ n) (m ^ p)) ⟩
    (m * m ^ n) * m ^ p
  ≡⟨ cong (_* m ^ p) (sym (^suc m n)) ⟩
    (m ^ suc n) * m ^ p 
  ∎

^*dist : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^*dist m n zero = refl
^*dist m n (suc p) =
  begin
    (m * n) ^ suc p
  ≡⟨⟩
    (m * n) * (m * n) ^ p
  ≡⟨ cong ((m * n) *_) (^*dist m n p) ⟩
    (m * n) * (m ^ p * n ^ p)
  ≡⟨ sym (*assoc (m * n) (m ^ p) (n ^ p)) ⟩
    (m * n) * m ^ p * n ^ p
  ≡⟨ cong (_* n ^ p) (*comm (m * n) (m ^ p)) ⟩
    m ^ p * (m * n) * n ^ p
  ≡⟨ cong (_* n ^ p) (sym (*assoc (m ^ p) m n)) ⟩
    m ^ p * m * n * n ^ p
  ≡⟨ *assoc (m ^ p * m) n (n ^ p) ⟩
    (m ^ p * m) * (n * n ^ p)
  ≡⟨ cong (_* (n * n ^ p)) (*comm (m ^ p) m) ⟩
    (m * m ^ p) * (n * n ^ p)
  ≡⟨ cong (_* (n * n ^ p)) (sym (^suc m p)) ⟩
    (m ^ suc p) * (n * n ^ p)
  ≡⟨ cong ((m ^ suc p) *_) (sym (^suc n p)) ⟩
    (m ^ suc p) * (n ^ suc p)
  ∎

^*assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^*assoc m n zero =
  begin
    (m ^ n) ^ 0
  ≡⟨⟩
    1
  ≡⟨ sym (^nullᵣ m) ⟩
   m ^ 0
  ≡⟨ cong (m ^_) (sym (*nullᵣ n)) ⟩
   m ^ (n * 0)
  ∎
^*assoc m n (suc p) =
  begin
    (m ^ n) ^ suc p
  ≡⟨⟩
    (m ^ n) * (m ^ n) ^ p
  ≡⟨ cong ((m ^ n) *_) (^*assoc m n p) ⟩
    (m ^ n) * (m ^ (n * p))
  ≡⟨ sym (^+dist m n (n * p)) ⟩
    m ^ (n + n * p)
  ≡⟨ cong (λ x → m ^ (x + n * p)) (sym (*idᵣ n)) ⟩
    m ^ (n * 1 + n * p)
  ≡⟨ cong (m ^_) (sym (*+distribₗ n 1 p)) ⟩
    m ^ (n * (1 + p))
  ∎

double : ∀ (n : ℕ) → n + n ≡ 2 * n
double zero = refl
double (suc n) =
  begin
    suc n + suc n
  ≡⟨⟩
    suc (n + suc n)
  ≡⟨ cong (λ x → suc x) (+-comm n (suc n)) ⟩
    suc (suc n + n)
  ≡⟨⟩
    suc (suc (n + n))
  ≡⟨⟩
    1 + (suc (n + n))
  ≡⟨⟩
    1 + (1 + n + n)
  ≡⟨ cong (λ x → 1 + (1 + x)) (double n) ⟩
    1 + (1 + 2 * n)
  ≡⟨ sym (+-assoc 1 1 (2 * n)) ⟩
    1 + 1 + 2 * n
  ≡⟨⟩
    2 + 2 * n
  ≡⟨ cong (_+ 2 * n) (*idᵣ 2) ⟩
    2 * 1 + 2 * n
  ≡⟨ sym (*+distribₗ 2 1 n) ⟩
    2 * (1 + n)
  ∎

data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = inc n O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

toBin : ℕ → Bin
toBin 0       = ⟨⟩ O
toBin (suc n) = inc (toBin n)

toℕ   : Bin → ℕ
toℕ ⟨⟩ = 0
toℕ (n O) = 2 * toℕ n
toℕ (n I) = 2 * toℕ n + 1

BinSuc : ∀ (b : Bin) → toℕ (inc b) ≡ suc (toℕ b)
BinSuc ⟨⟩ = refl
BinSuc (b O) =
  begin
    toℕ (inc (b O))
  ≡⟨⟩
    toℕ (b I)
  ≡⟨⟩
    2 * toℕ b + 1
  ≡⟨⟩
    toℕ (b O) + 1
  ≡⟨ +-comm (toℕ (b O)) 1 ⟩
    1 + toℕ (b O)
  ∎
BinSuc (b I) =
  begin
    toℕ (inc (b I))
  ≡⟨⟩
    toℕ ((inc b) O)
  ≡⟨⟩
    2 * toℕ (inc b)
  ≡⟨ cong (2 *_) (BinSuc b) ⟩
    2 * suc (toℕ b)
  ≡⟨⟩
     suc (toℕ b) + 1 * suc (toℕ b)
  ≡⟨ cong (suc (toℕ b) +_) (*idₗ (suc (toℕ b))) ⟩
    suc (toℕ b) + suc (toℕ b)
  ≡⟨⟩
    suc (toℕ b + suc (toℕ b))
  ≡⟨ cong (λ x → suc x) (+-comm (toℕ b) (suc (toℕ b))) ⟩
    suc (suc (toℕ b) + toℕ b)
  ≡⟨⟩
    suc (1 + (toℕ b + toℕ b))
  ≡⟨ cong (λ x → suc (1 + x)) (double (toℕ b)) ⟩
    suc (1 + 2 * (toℕ b))
  ≡⟨ cong (λ x → suc x) (+-comm 1 (2 * (toℕ b))) ⟩
    suc (2 * (toℕ b) + 1)
  ≡⟨⟩
    suc (toℕ (b I))
  ∎

-- BinEqℕ : ∀ (b : Bin) → toBin (toℕ b) ≡ b
-- ⟨⟩ O I => suc zero => ⟨⟩ I != ⟨⟩ O I

ℕEqBin : ∀ (n : ℕ) → toℕ (toBin n) ≡ n
ℕEqBin zero = refl
ℕEqBin (suc n) =
  begin
    toℕ (toBin (suc n))
  ≡⟨⟩
    toℕ (inc (toBin n))
  ≡⟨ BinSuc (toBin n) ⟩
    suc (toℕ (toBin n))
  ≡⟨ cong (λ x → suc x) (ℕEqBin n) ⟩
    suc n
  ∎
