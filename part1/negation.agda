module plfa-solutions.part1.negation where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂) 
open import plfa-solutions.part1.isomorphism using (_≃_; _≲_; extensionality)
¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition A→B = λ ¬B A → ¬B (A→B A)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<-irreflexive :  ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive (s<s n<n) = <-irreflexive n<n

s<s-elim : ∀ {m n : ℕ} → suc m < suc n → m < n
s<s-elim (s<s m<n) = m<n

s≮s : ∀ {m n : ℕ} → ¬(m < n) → ¬(suc m < suc n)
s≮s m≮n = λ sm<sn → m≮n (s<s-elim sm<sn)

s≡s-elim : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
s≡s-elim refl = refl

s≢s : ∀ {m n : ℕ} → ¬(m ≡ n) → ¬(suc m ≡ suc n)
s≢s m≢n = λ sm≡sn → m≢n (s≡s-elim sm≡sn)

s≡s : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
s≡s {zero} {zero} m≡n = refl
s≡s {suc m} {suc .m} refl = refl

<→≯ : ∀ {m n : ℕ} → m < n → ¬ (n < m)
<→≯ z<s = λ ()
<→≯ (s<s m<n) = λ sn<sm → (<→≯ m<n) (s<s-elim sn<sm)

<→≢ : ∀ {m n : ℕ} → m < n → ¬ (m ≡ n)
<→≢ z<s = λ ()
<→≢ (s<s m<n) = λ{sm≡sn → (<→≢ m<n) (s≡s-elim sm≡sn)}

≡→≮ : ∀ {m n : ℕ} → m ≡ n → ¬ (m < n)
≡→≮ {zero} {zero} m≡n = λ ()
≡→≮ {suc m} {suc n} m≡n = λ sm<sn → (≡→≮ (s≡s-elim m≡n)) (s<s-elim sm<sn)

<-trichotomy : ∀ (m n : ℕ) →
    (m < n) × ¬ (n < m) × ¬ (m ≡ n) ⊎
  ¬ (m < n) ×   (n < m) × ¬ (m ≡ n) ⊎
  ¬ (m < n) × ¬ (n < m) ×   (m ≡ n)
<-trichotomy zero zero = inj₂ (inj₂ ((λ ()), ((λ ()) , refl)))
<-trichotomy zero (suc n) = inj₁ (z<s , (λ ()) , (λ ()))
<-trichotomy (suc m) zero = inj₂ (inj₁ ((λ ()) , z<s , (λ ())))
<-trichotomy (suc m) (suc n) with <-trichotomy m n
... | inj₁       ( m<n     , ( n≮m     , m≢n ) )
    = inj₁       ( s<s m<n , ( s≮s n≮m , s≢s m≢n ) )
... | inj₂ (inj₁ ( m≮n     , ( n<m     , m≢n ) ))
    = inj₂ (inj₁ ( s≮s m≮n , ( s<s n<m , s≢s m≢n)))
... | inj₂ (inj₂ ( m≮n     , ( n≮m     , m≡n ) ))
    = inj₂ (inj₂ ( s≮s m≮n , ( s≮s n≮m , s≡s m≡n)))

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
  { to      = to
  ; from    = from
  ; from∘to = from∘to
  ; to∘from = to∘from
  }
  where
    to : ∀ {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
    to ¬A⊎B = (λ A → ¬A⊎B (inj₁ A)) , λ B → ¬A⊎B (inj₂ B)

    from : ∀ {A B : Set} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
    from (¬A , ¬B) = λ A⊎B → case-⊎ ¬A ¬B A⊎B

    from∘to : ∀ {A B : Set} → (x : ¬ (A ⊎ B)) → from (to x) ≡ x
    from∘to ¬A⊎B = refl

    to∘from : ∀ {A B : Set} → (x : (¬ A) × (¬ B)) → to (from x) ≡ x
    to∘from ¬A⊎B = refl

×-dual-⊎ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-dual-⊎ (inj₁ ¬A) = λ (A , B) → ¬A A
×-dual-⊎ (inj₂ ¬B) = λ (A , B) → ¬B B  

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ λ x → k (inj₁ x))

⊥-E : ∀ {A : Set} → ⊥ → A
⊥-E ()

EM→¬¬-E : (∀ {A : Set} → A ⊎ ¬ A) →
          (∀ {A : Set} → ¬ (¬ A) → A)
EM→¬¬-E em with em
... | inj₁ A  = λ ¬¬A → A
... | inj₂ ¬A = λ ¬¬A → ⊥-E (¬¬A ¬A)  

¬¬-E→peirce :
    (∀ {A : Set} → ¬ ¬ A → A)
    -----------------------------------
  → (∀ {A B : Set} → ((A → B) → A) → A)
¬¬-E→peirce ¬¬-E = λ A→B→A → ¬¬-E (λ ¬A → ¬A (A→B→A (λ A → ⊥-E (¬A A))))

peirce→ID : (∀ {A B : Set} → ((A → B) → A) → A)
          → (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
peirce→ID peirce A→B = peirce (λ ¬[¬A⊎B] → inj₁ λ A → ¬[¬A⊎B] (inj₂ (A→B A)))

ID→DeMorgan : (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
            → (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
ID→DeMorgan [a→b]→¬a⊎b {A} {B} ¬[¬a×¬b]
  with [a→b]→¬a⊎b {A} {A} (λ a → a) | [a→b]→¬a⊎b {B} {B} (λ b → b)
... | inj₁ ¬a | inj₁ ¬b = ⊥-E (¬[¬a×¬b] ( ¬a , ¬b ))
... | inj₂ a  | _       = inj₁ a
... | inj₁ ¬a | inj₂ b  = inj₂ b 

DeMorgan→em : (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
            → (∀ {A : Set} → A ⊎ ¬ A)
DeMorgan→em dm = dm (λ ¬A×¬¬A → proj₂ ¬A×¬¬A (proj₁ ¬A×¬¬A))

Stable : Set → Set
Stable A = ¬ ¬ A → A

stable-¬ : ∀ {A : Set} → Stable (¬ A)
stable-¬ = ¬¬¬-elim

stable-× : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
stable-× sA sB = λ ¬¬[A×B] →
  (sA (λ ¬A → ¬¬[A×B] λ A×B → ¬A (proj₁ A×B)) ,
   sB (λ ¬B → ¬¬[A×B] λ A×B → ¬B (proj₂ A×B)))
