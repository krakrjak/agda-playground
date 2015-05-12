module proofs where

open import Relation.Binary.PropositionalEquality 
open ≡-Reasoning

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m    = m
succ n + m  = succ (n + m)
infixl 6 _+_

--Associativity of + on ℕ
+-assoc : ∀ (a b c : ℕ) → a + (b + c) ≡ (a + b) + c
+-assoc zero _ _     = refl
+-assoc (succ a) b c = cong succ (+-assoc a b c)

--lemma for right unit assoc
zero+ : ∀ (a : ℕ) → a + zero ≡ a
zero+ zero     = refl
zero+ (succ a) = cong succ (zero+ a)

--lemma for right succ assoc
+succ : ∀ (a b : ℕ) → a + (succ b) ≡ succ (a + b)
+succ zero _     = refl
+succ (succ a) b = cong succ (+succ a b)

--Commutivity of + on ℕ
+-commut : (a b : ℕ) → a + b ≡ b + a
+-commut zero     b = sym (zero+ b)
+-commut (succ a) b = begin
  succ a + b ≡⟨ refl ⟩
  succ (a + b) ≡⟨ cong succ (+-commut a b) ⟩
  succ (b + a) ≡⟨ sym (+succ b a) ⟩
  b + succ a
  ∎

_*_ : ℕ → ℕ → ℕ
zero * m   = zero
succ n * m = m + n * m
infixl 8 _*_

--Assoc, distrib for *


--Dependent type toys
data Σ {A : Set} (B : A → Set) : Set where
  _,_  : (a : A) → B a → Σ \(x : A) → B x

fst : {A : Set} {B : A → Set} → Σ B → A
fst (x , a) = x

snd : {A : Set} {B : A → Set} → (y : Σ B) → B (fst y)
snd (x , a) = a

∃ : {A : Set} → (B : A → Set) → Set
∃ = Σ

-- Axiom of choice embedded in dependent types
AC : {X Y : Set} {A : X → Y → Set} →
    (∀ (x : X) → ∃ \(y : Y) → A x y) → ∃ \(f : X → Y) → ∀ (x : X) → A x (f x)
AC g = (λ x → fst(g x)) , (λ x → snd(g x))

-- A version of the Π constructor
Π : {X : Set} → (Y : X → Set) → Set
Π {X} Y = (x : X) → Y x
