module proofs where

-- ∀ a ∈ A, a ≡ a
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

-- Prove ≡ is an equivalence and respects congruence
refl' : ∀ {A} (a : A) → a ≡ a
refl' a = refl
sym : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl
trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl
cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl


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

