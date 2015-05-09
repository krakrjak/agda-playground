module example where

-- Implicit way of writing identity
id : {A : Set} → A → A
id x = x

-- Inductive definition of the Natural numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m   = m
succ n + m = succ (n + m)

_*_ : ℕ → ℕ → ℕ
zero * m   = zero
succ n * m = m + n * m

-- multiplication binds strongly and is left associative
-- addition binds weakly and is left associative
infixl 60 _*_
infixl 40 _+_

-- Indexed Vector
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

-- Safe concatenation for indexed vectors
_++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[]      ++ v2 = v2
(h ∷ t) ++ v2 = h ∷ (t ++ v2)
  
-- Safe head using the indexed vector
head : {A : Set}{n : ℕ} → Vec A (succ n) → A
head (x ∷ _) = x

-- Safe tail for the indexed vector
tail : {A : Set}{n : ℕ} → Vec A (succ n) → Vec A n
tail (_ ∷ xs) = xs

-- Naturals based on one for indexing into vectors
data Fin : ℕ → Set where
  one : {n : ℕ} -> Fin (succ n)
  suc : {n : ℕ} -> Fin n -> Fin (succ n)

-- Vector element index operator
_!_ : {A : Set} {n : ℕ } → Vec A n → Fin n → A
[] ! ()
(x ∷ xs) ! one   = x
(x ∷ xs) ! suc i = xs ! i

-- Cartesian Product operator \times
-- Concatenate two elements into a pair
-- Logically equivalent to AND
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

-- Coproduct operator \oplus
-- Project and element into a disjoint sum, with elements pr₁and pr₂
-- Logically equivalent to OR
data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B
  
-- Product binds weakly to the right
-- Coproduct binds strongly to the right
infixr 60 _×_
infixr 50 _⊕_
