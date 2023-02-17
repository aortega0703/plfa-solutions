{-# OPTIONS --exact-split #-}
module agda-tutorial.part1.peano where 

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATURAL ℕ #-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)

_ : 2 * 3 ≡ 6
_ = 
    begin
        2 * 3
    ≡⟨⟩
        3 + (1 * 3)
    ≡⟨⟩
        3 + (3 + (0 * 3))
    ≡⟨⟩
        3 + (3 + 0)
    ≡⟨⟩
        3 + 3
    ≡⟨⟩
        6
    ∎

_^_ : ℕ → ℕ → ℕ
n ^ 0       = 1
n ^ (suc m) = n * (n ^ m)

_∸_ : ℕ → ℕ → ℕ
n       ∸ 0       = n
0       ∸ (suc n) = 0
(suc n) ∸ (suc m) = n ∸ m 

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}
 
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
