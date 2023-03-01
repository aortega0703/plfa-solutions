module plfa-solutions.part1.lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; *-distribˡ-∸; +-∸-assoc; m+n∸m≡n; m≤m*n; *-suc; +-∸-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa-solutions.part1.isomorphism using (_≃_; _⇔_)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ (xs ++ ys) ++ zs)
  ≡⟨ cong (λ l → x ∷ l) (++-assoc xs ys zs) ⟩
    (x ∷ xs ++ (ys ++ zs))
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    (x ∷ xs)
  ∎

length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys =
  begin
    (suc (length (xs ++ ys)))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    (suc (length xs + length ys))
  ∎

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys =
  begin 
    (reverse ys)
  ≡⟨ sym (++-identityʳ (reverse ys)) ⟩
    reverse ys ++ []
  ≡⟨⟩
    (reverse ys ++ reverse [])
  ∎
reverse-++-distrib (x ∷ xs) ys =
  begin
    (reverse (xs ++ ys) ++ [ x ])
  ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    (reverse ys ++ reverse xs ++ [ x ])
  ∎

reverse-involute : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involute [] = refl
reverse-involute (x ∷ xs) =
  begin
    (reverse (reverse xs ++ [ x ]))
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs)
  ≡⟨ cong (λ t → reverse [ x ] ++ t) (reverse-involute xs) ⟩
    (x ∷ xs)
  ∎

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

lemma : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → (x : List A)
  → map (g ∘ f) x ≡ (map g ∘ map f) x
lemma f g []       = refl
lemma f g (x ∷ xs) =
  begin
    map (g ∘ f) (x ∷ xs)
  ≡⟨⟩
    (g ∘ f) x ∷ map (g ∘ f) xs
  ≡⟨ cong ((g ∘ f) x ∷_) (lemma f g xs) ⟩
    (g ∘ f) x ∷ (map g ∘ map f) xs
  ≡⟨⟩
    (map g ∘ map f) (x ∷ xs)
  ∎

map-compose : ∀ {A B C : Set} → (f : A → B) → (g : B → C)
  → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality (lemma f g)

map-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-distribute f [] ys = refl
map-distribute f (x ∷ xs) ys =
  begin
    (f x ∷ map f (xs ++ ys))
  ≡⟨ cong (λ T → f x ∷ T) (map-distribute f xs ys) ⟩
    (f x ∷ map f xs ++ map f ys)
  ∎

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf a)             = leaf (f a)
map-Tree f g (node treeˡ b treeʳ) =
  node (map-Tree f g treeˡ) (g b) (map-Tree f g treeʳ)

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ foldr _⊗_ e xs

product : ∀ (xs : List ℕ) → ℕ
product = foldr _*_ 1
sum : List ℕ → ℕ
sum = foldr _+_ 0
foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys =
  begin
    (x ⊗ foldr _⊗_ e (xs ++ ys))
  ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
    (x ⊗ foldr _⊗_ (foldr _⊗_ e ys) xs)
  ∎

foldr-∷ : ∀ {A : Set} (xs : List A)
  → foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) =
  begin
    (x ∷ foldr _∷_ [] xs)
  ≡⟨ cong ( x ∷_ ) (foldr-∷ xs) ⟩
    (x ∷ xs)
  ∎

foldr-∷₁ : ∀ {A : Set} (xs ys : List A)
  → xs ++ ys ≡ foldr _∷_ ys xs
foldr-∷₁ [] ys = refl
foldr-∷₁ (x ∷ xs) ys = sym (
  begin
  (x ∷ foldr _∷_ ys xs)
  ≡⟨ cong (x ∷_) (sym (foldr-∷₁ xs ys)) ⟩
    x ∷ xs ++ ys
  ∎)

map-is-foldr´ : ∀ {A B : Set} (f : A → B) (ys : List A)
  → map f ys ≡ foldr (λ x xs → f x ∷ xs) [] ys
map-is-foldr´ f [] = refl
map-is-foldr´ f (x ∷ ys) =
  begin
    (f x ∷ map f ys)
  ≡⟨ cong (f x ∷_) (map-is-foldr´ f ys) ⟩
    (f x ∷ foldr (λ z → _∷_ (f z)) [] ys)
  ∎

map-is-foldr : ∀ {A B : Set} (f : A → B) 
  → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality (λ xs → map-is-foldr´ f xs)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f _ (leaf a)             = f a
fold-Tree f g (node treeˡ b treeʳ) =
  g (fold-Tree f g treeˡ) b (fold-Tree f g treeʳ)

downFrom : ℕ → List ℕ
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

n≤n*n : ∀ (n : ℕ) → n ≤ n * n
n≤n*n zero    = z≤n
n≤n*n (suc n) = m≤m*n (suc n) (suc n)

n≤n*2 : ∀ (n : ℕ) → n ≤ n * 2
n≤n*2 n = m≤m*n n (2)

n*2∸n≡n : ∀ (n : ℕ) → n * 2 ∸ n ≡ n
n*2∸n≡n n =
  begin
    n * 2 ∸ n
  ≡⟨ cong (_∸ n) (*-suc n 1) ⟩
    n + n * 1 ∸ n
  ≡⟨ m+n∸m≡n n (n * 1) ⟩
    n * 1
  ≡⟨ *-identityʳ n ⟩
    n
  ∎

m*[n∸1]≡m*n∸m : ∀ (m n : ℕ) → m * (n ∸ 1) ≡ m * n ∸ m
m*[n∸1]≡m*n∸m m n =
  begin
    m * (n ∸ 1)
  ≡⟨ *-distribˡ-∸ m n 1 ⟩
    m * n ∸ m * 1
  ≡⟨ cong (m * n ∸_) (*-identityʳ m) ⟩
    m * n ∸ m
  ∎

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero =
  begin
    sum (downFrom zero) * 2
  ≡⟨⟩
    sum [] * 2
  ≡⟨⟩
    zero
  ∎
sum-downFrom (suc n) =
  begin
    sum (downFrom (suc n)) * 2
  ≡⟨⟩
    sum (n ∷ downFrom n) * 2
  ≡⟨⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-distribʳ-+ 2 n (sum (downFrom n)) ⟩
    (n * 2) + (sum (downFrom n)) * 2
  ≡⟨ cong (n * 2 +_) (sum-downFrom n) ⟩
    (n * 2) + (n * (n ∸ 1))
  ≡⟨ cong (n * 2 +_) (m*[n∸1]≡m*n∸m n n) ⟩
    (n * 2) + (n * n ∸ n)
  ≡⟨ sym (+-∸-assoc (n * 2) (n≤n*n n)) ⟩
    (n * 2) + n * n ∸ n
  ≡⟨ +-∸-comm (n * n) (n≤n*2 n) ⟩
    (n * 2) ∸ n + n * n
  ≡⟨ cong (_+ n * n) (n*2∸n≡n n) ⟩
    n + n * n
  ∎

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid
