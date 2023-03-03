module plfa-solutions.part1.relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat.Properties using (+-comm; +-identityʳ; +-identityˡ; *-comm; +-assoc)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import plfa-solutions.part1.induction using (Bin; ⟨⟩; _O; _I; inc;
  toℕ; toBin; double; BinSuc; *+distribₗ)
--open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)


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

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero

  suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc  : ∀ {n : ℕ} → even n → odd (suc n)

e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)

o+e≡o : ∀ {m n : ℕ} → odd m → even n → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc zero) on = suc on
o+o≡e (suc (suc om)) on = suc (suc (o+o≡e om on))

data Leading1 : Bin → Set where
  one : Leading1 (⟨⟩ I) 
  _O  : ∀ {b : Bin} → Leading1 b → Leading1 (b O) 
  _I  : ∀ {b : Bin} → Leading1 b → Leading1 (b I)

data Canonical : Bin → Set where
  zero    : Canonical (⟨⟩ O)
  leading : ∀ {b : Bin} → Leading1 b → Canonical b

inc-Leading1 : ∀ {b : Bin} → Leading1 b → Leading1 (inc b)
inc-Leading1 one = one O
inc-Leading1 (l O) = l I 
inc-Leading1 (l I) = inc-Leading1 l O

inc-Canonical : ∀ {b : Bin} → Canonical b → Canonical (inc b)
inc-Canonical zero = leading one
inc-Canonical (leading one) = leading (one O)
inc-Canonical (leading (x O)) = leading (x I)
inc-Canonical (leading (x I)) = leading (inc-Leading1 (x I))

toBin-Canonical : ∀ (n : ℕ) → Canonical (toBin n)
toBin-Canonical zero = zero
toBin-Canonical (suc n) = inc-Canonical (toBin-Canonical n)

unsuc : ℕ → ℕ
unsuc zero = zero
unsuc (suc n) = n

prev : Bin → Bin
prev ⟨⟩ = ⟨⟩
prev (⟨⟩ O) = ⟨⟩ O
prev (b O) = prev b I
prev (b I) = b O

record Σ (A : Set) (B : A → Set) : Set where
  field
    proj₁ : A
    proj₂ : B proj₁
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

leading→suc : ∀ {b : Bin} → Leading1 b → Σ (ℕ) (λ n → toℕ b ≡ suc n)
leading→suc {.(⟨⟩ I)} one =
  record
  { proj₁ = zero
  ; proj₂ = refl }
leading→suc {b O} (lb O) =
  record
  { proj₁ = unsuc (2 * toℕ b)
  ; proj₂ = sym (
      let n = Σ.proj₁ (leading→suc lb) in
      let b≡sn = Σ.proj₂ (leading→suc lb) in 
      begin
        suc (unsuc (2 * toℕ b))
      ≡⟨ cong (λ x → suc (unsuc (2 * x))) b≡sn ⟩
        suc (unsuc (2 * (suc n)))
      ≡⟨ cong (λ x → suc (unsuc x)) (sym (double (suc n))) ⟩
        suc (unsuc ((suc n) + (suc n)))
      ≡⟨⟩
        suc n + suc n
      ≡⟨ double (suc n) ⟩
        2 * (suc n)
      ≡⟨ cong (2 *_) (sym b≡sn) ⟩
        2 * toℕ b
      ∎
    )
  }
leading→suc {b I} (lb I) =
  record
  { proj₁ = 2 * toℕ b
  ; proj₂ = sym (
      let n = Σ.proj₁ (leading→suc lb) in
      let b≡sn = Σ.proj₂ (leading→suc lb) in 
      begin
        suc (2 * toℕ b)
      ≡⟨⟩
        1 + 2 * toℕ b
      ≡⟨ +-comm 1 (2 * toℕ b) ⟩
        2 * toℕ b + 1
      ≡⟨⟩
        toℕ (b I)
      ∎
    )
  }


_+´_ : Bin → Bin → Bin
⟨⟩ +´ b = b
(a O) +´ ⟨⟩ = a O
(a O) +´ (b O) = (a +´ b) O
(a O) +´ (b I) = (a +´ b) I
(a I) +´ ⟨⟩ = a I
(a I) +´ (b O) = (a +´ b) I
(a I) +´ (b I) = (inc (a +´ b)) O

+´-comm : ∀ {a b : Bin} → a +´ b ≡ b +´ a
+´-comm {⟨⟩} {⟨⟩} = refl
+´-comm {⟨⟩} {b O} = refl
+´-comm {⟨⟩} {b I} = refl
+´-comm {a O} {⟨⟩} = refl
+´-comm {a O} {b O} =
  begin
    (a +´ b) O
  ≡⟨ cong _O (+´-comm {a} {b}) ⟩
    ((b +´ a) O)
  ≡⟨⟩
    ((b O) +´ (a O))
  ∎
+´-comm {a O} {b I} =
  begin
    (a +´ b) I
  ≡⟨ cong _I (+´-comm {a} {b}) ⟩
    ((b +´ a) I)
  ≡⟨⟩
    (((b I) +´ (a O)))
  ∎
+´-comm {a I} {⟨⟩} = refl
+´-comm {a I} {b O} =
  begin
    (a +´ b) I
  ≡⟨ cong _I (+´-comm {a} {b}) ⟩
    ((b +´ a) I)
  ≡⟨⟩
    (((b O) +´ (a I)))
  ∎
+´-comm {a I} {b I} =
  begin
    inc (a +´ b) O
  ≡⟨ cong (λ x → (inc x) O) (+´-comm {a} {b}) ⟩
    inc (b +´ a) O
  ≡⟨⟩
    (b I) +´ (a I)
  ∎

+´-incₗ : ∀ {a b : Bin} → inc(a +´ b) ≡ inc a +´ b
+´-incₗ {⟨⟩} {⟨⟩} = refl
+´-incₗ {⟨⟩} {b O} = refl
+´-incₗ {⟨⟩} {b I} = refl
+´-incₗ {a O} {⟨⟩} = refl
+´-incₗ {a O} {b O} = refl
+´-incₗ {a O} {b I} = refl
+´-incₗ {a I} {⟨⟩} = refl
+´-incₗ {a I} {b O} =
  begin
    inc ( (a I) +´ (b O)) 
  ≡⟨⟩
    (inc (a +´ b)) O
  ≡⟨ cong _O (+´-incₗ {a} {b}) ⟩
    (inc a +´ b) O
  ≡⟨⟩
    (inc a O) +´ (b O)
  ≡⟨⟩
    (inc (a I)) +´ (b O)
  ∎
+´-incₗ {a I} {b I} =
  begin
    inc (a +´ b) I
  ≡⟨ cong _I (+´-incₗ {a} {b}) ⟩
    ((inc a) +´ b) I
  ≡⟨⟩
    (inc a O) +´ (b I)
  ≡⟨⟩
    (inc (a I) +´ (b I))
  ∎

+´-incᵣ : ∀ {a b : Bin} → inc( a +´ b) ≡ a +´ inc b
+´-incᵣ {a} {b} =
  begin
    inc (a +´ b)
  ≡⟨ cong inc (+´-comm {a} {b}) ⟩
    inc (b +´ a)
  ≡⟨ +´-incₗ {b} {a} ⟩
    (inc b) +´ a
  ≡⟨ +´-comm {inc b} {a} ⟩
    a +´ inc b
  ∎

toBin-split : ∀ {m n : ℕ} → toBin (m + n) ≡ toBin m +´ toBin n
toBin-split {zero} {zero} = refl
toBin-split {zero} {suc n} =
  begin
    toBin (0 + suc n)
  ≡⟨⟩
    inc (toBin n)
  ≡⟨ cong (λ x → inc (toBin x)) (sym (+-identityˡ n)) ⟩
    inc (toBin (0 + n))
  ≡⟨ cong inc (toBin-split {0} {n}) ⟩
    inc (toBin 0 +´ toBin n)
  ≡⟨ +´-incᵣ {toBin 0} {toBin n} ⟩
    toBin 0 +´ inc (toBin n)
  ≡⟨⟩
    toBin 0 +´ toBin (suc n)
  ∎
toBin-split {suc m} {zero} =
  begin
    inc (toBin (m + 0))
  ≡⟨ cong inc (toBin-split {m} {0}) ⟩
    inc ((toBin m) +´ (toBin 0))
  ≡⟨ +´-incₗ {toBin m} {toBin 0} ⟩
    (inc (toBin m)) +´ (toBin 0)
  ≡⟨⟩
    (toBin (suc m) +´ (toBin 0))
  ∎
toBin-split {suc m} {suc n} =
  begin
    (inc (toBin (m + suc n)))
  ≡⟨ cong (λ x → inc (toBin x)) (+-comm m (suc n)) ⟩
    inc (inc (toBin (n + m)))
  ≡⟨ cong (λ x → inc (inc x)) (toBin-split {n} {m}) ⟩
    inc (inc ((toBin n) +´ (toBin m)))
  ≡⟨ cong inc (+´-incₗ {toBin n} {toBin m}) ⟩
    inc (inc (toBin n) +´ (toBin m))
  ≡⟨ +´-incᵣ {inc (toBin n)} {toBin m} ⟩
    (inc (toBin n)) +´ (inc (toBin m))
  ≡⟨⟩
    (toBin (suc n)) +´ (toBin (suc m))
  ≡⟨ +´-comm {toBin (suc n)} {toBin (suc m)} ⟩
    (toBin (suc m)) +´ (toBin (suc n))
  ∎

double-Bin : ∀ {b : Bin} → Leading1 b → b +´ b ≡ b O
double-Bin {(⟨⟩ I)} one = refl
double-Bin {(b O)} (lb O) =
  begin
    (b +´ b) O
  ≡⟨ cong _O (double-Bin {b} lb) ⟩
    ((b O) O)
  ∎
double-Bin {(b I)} (lb I) =
  begin
    (inc (b +´ b) O)
  ≡⟨ cong (λ x → inc x O) (double-Bin {b} lb) ⟩
    ((b I) O)
  ∎

toBin∘toℕ : ∀ {b : Bin} → Canonical b → toBin (toℕ b) ≡ b
toBin∘toℕ zero = refl
toBin∘toℕ (leading one) = refl
toBin∘toℕ {b O} (leading (cb O)) =
  begin
    toBin (toℕ (b O))
  ≡⟨⟩
    toBin (2 * toℕ b)
  ≡⟨ cong (λ x → toBin (toℕ b + x)) (+-identityʳ (toℕ b))⟩
    toBin (toℕ b + toℕ b)
  ≡⟨ toBin-split {toℕ b} {toℕ b} ⟩
    (toBin (toℕ b)) +´ (toBin (toℕ b))
  ≡⟨ cong (λ x → x +´ x) (toBin∘toℕ {b} (leading cb)) ⟩
    (b +´ b)
  ≡⟨ double-Bin {b} cb ⟩
    (b O)
  ∎
toBin∘toℕ {b I} (leading (cb I)) =
  begin
    toBin (toℕ (b I))
  ≡⟨⟩
    toBin (toℕ (inc (b O)))
  ≡⟨ cong toBin (BinSuc (b O)) ⟩
    toBin (suc (toℕ (b O)))
  ≡⟨⟩
    inc (toBin (toℕ (b O)))
  ≡⟨⟩
    inc (toBin (toℕ b + (toℕ b + zero)))
  ≡⟨ cong (λ x → inc (toBin (toℕ b + x))) (+-identityʳ (toℕ b)) ⟩
    inc (toBin (toℕ b + toℕ b))
  ≡⟨ cong inc (toBin-split {toℕ b} {toℕ b}) ⟩
    inc ((toBin (toℕ b)) +´ (toBin (toℕ b)))
  ≡⟨ cong (λ x → inc (x +´ x)) (toBin∘toℕ {b} (leading cb)) ⟩
    (inc (b +´ b))
  ≡⟨ cong inc (double-Bin {b} cb) ⟩
    (b I)
  ∎
