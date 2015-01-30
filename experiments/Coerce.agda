{-# OPTIONS --guardedness-preserving-type-constructors #-}

-- Agda specification of `coerce`
--
-- Incomplete: too much work just to make type system happy.
-- Conversions between morally identical types obscure
-- the operational content.

open import Data.Product
open import Data.Maybe
open import Data.Bool
open import Data.Sum
open import Data.Fin hiding (_+_)
open import Data.Vec
import Data.Nat as ℕ
open ℕ using (ℕ ; suc ; zero)
open import Coinduction renaming (Rec to Fix ; fold to roll ; unfold to unroll)

data Data (ℓ : ℕ) : Set where
  base : ℕ → Data ℓ
  pair : Data ℓ → Data ℓ → Data ℓ
  plus : Data ℓ → Data ℓ → Data ℓ
  var  : Fin ℓ → Data ℓ -- de Bruijn index
  fix  : Data (suc ℓ) → Data ℓ

try : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → B → B → A → A
try a b b₂ = b₂

weaken-fin : ∀{n} (m : ℕ) → Fin n → Fin (m ℕ.+ n)
weaken-fin zero x = x
weaken-fin (suc m) x = suc (weaken-fin m x)

-- this terminates for sure
{-# NO_TERMINATION_CHECK #-}
weaken : ∀ {n} → (m : ℕ) → Data n → Data (m ℕ.+ n)
weaken 0 t = t
weaken m (base x) = base x
weaken m (pair S T) = pair (weaken m S) (weaken m T)
weaken m (plus S T) = plus (weaken m S) (weaken m T)
weaken m (var x) = var (weaken-fin m x)
weaken 1 (fix T) = fix (weaken 1 T)
weaken (suc m) (fix T) = weaken 1 (weaken m (fix T))

-- universe construction; always terminating.
{-# NO_TERMINATION_CHECK #-}
uc : ∀ {ℓ} → Data ℓ → Vec Set ℓ → Set
uc (base n) _ = Fin n
uc (pair σ τ) ρ = uc σ ρ × uc τ ρ
uc (plus σ τ) ρ = uc σ ρ ⊎ uc τ ρ
uc (var i) ρ = lookup i ρ
uc (fix τ) ρ = set where set = Fix (♯ (uc τ (set ∷ ρ)))

my-nat-data : Data 0
my-nat-data = fix (plus (base 1) (var zero))

My-nat : Set
My-nat = uc my-nat-data []

my-zero : My-nat
my-zero = roll (inj₁ zero)

my-one : My-nat
my-one = roll (inj₂ (roll (inj₁ zero)))

-- nonterminating stuff
botData : Data 0
botData = fix (var zero)

botType : Set
botType = uc botData []

{-# NON_TERMINATING #-}
⋯ : botType
⋯ = roll (roll (roll (roll (roll (roll ⋯)))))

-- object language: STLC with fix

infixr 3 _⇒_

-- is a coinductive datatype
data Type : Set₁ where
  base : (ι : Set) → Type
  _⇒_  : (σ : Type) → (τ : Type) → Type
  _*_  : ∞ Type → ∞ Type → Type
  _+_  : ∞ Type → ∞ Type → Type

-- is generative on coinductive data
{-# NO_TERMINATION_CHECK #-}
val : Type → Set
val (base ι) = ι
val (σ ⇒ τ) = val σ → val τ
val (σ * τ) = val (♭ σ) × val (♭ τ)
val (σ + τ) = val (♭ σ) ⊎ val (♭ τ)

Context : ℕ → Set₁
Context = Vec Type

data Term {n} (Γ : Context n) : Type → Set₁ where
  var : (i : Fin n) → Term Γ (lookup i Γ)
  app : ∀ {σ τ} → (s : Term Γ (σ ⇒ τ)) → (t : Term Γ σ) → Term Γ τ
  abs : ∀ {σ τ} → (t : Term (σ ∷ Γ) τ) → Term Γ (σ ⇒ τ)
  fix : ∀ {τ} → Term Γ (τ ⇒ τ) → Term Γ τ

  -- intro/elim products
  pair : ∀ {σ τ} → Term Γ σ → Term Γ τ → Term Γ (♯ σ * ♯ τ)
  uncr : ∀ {σ τ β} → Term Γ (σ ⇒ τ ⇒ β) → Term Γ (♯ σ * ♯ τ) → Term Γ β

  -- intro/elim sums
  left : ∀ {σ τ} → Term Γ σ → Term Γ (♯ σ + ♯ τ)
  rite : ∀ {σ τ} → Term Γ τ → Term Γ (♯ σ + ♯ τ)
  mach : ∀ {σ τ β} →
           Term Γ (σ ⇒ β) → Term Γ (τ ⇒ β) → Term Γ (♯ σ + ♯ τ) → Term Γ β

  -- intro/elim base types
  base : ∀ {S : Set} → S → Term Γ (base S)
  call : ∀ {S T : Set} → Term Γ (base (S → T)) → Term Γ (base S) → Term Γ (base T)

data Env : ∀ {n} (Γ : Context n) → Set₁ where
  [] : Env []
  _∷_ : ∀ {n τ} {Γ : Context n} → val τ → Env Γ → Env (τ ∷ Γ)

seek : ∀ {n} {Γ : Context n} → (i : Fin n) → Env Γ → val (lookup i Γ)
seek zero    (v ∷ _) = v
seek (suc i) (_ ∷ ρ) = seek i ρ

{-# NON_TERMINATING #-}
eval : ∀ {n} {Γ : Context n} {τ} → Term Γ τ → Env Γ → val τ
eval (var x) ρ   = seek x ρ
eval (app s t) ρ = eval s ρ (eval t ρ)
eval (abs t) ρ   = λ v → eval t (v ∷ ρ)
eval (fix f) ρ   = eval (app f (fix f)) ρ

eval (pair s t) ρ = eval s ρ , eval t ρ
eval (uncr f p) ρ = uncurry (eval f ρ) (eval p ρ)

eval (left x) ρ = inj₁ (eval x ρ)
eval (rite y) ρ = inj₂ (eval y ρ)
eval (mach f g t) ρ = [ eval f ρ , eval g ρ ]′ (eval t ρ)

eval (base v) ρ = v
eval (call f x) ρ = eval f ρ (eval x ρ)

nat-eq : ℕ → ℕ → Bool
nat-eq  zero    zero   = true
nat-eq (suc m) (suc n) = nat-eq m n
nat-eq  _       _      = false

fin-eq : ∀ {n} → Fin n → Fin n → Bool
fin-eq m n = nat-eq (toℕ m) (toℕ n)

infix 7 _==_
_==_ : ∀ {n} → Data n → Data n → Bool
base x == base y = nat-eq x y
pair σ₁ τ₁ == pair σ₂ τ₂ = σ₁ == σ₂ ∧ τ₁ == τ₂
plus σ₁ τ₁ == plus σ₂ τ₂ = σ₁ == σ₂ ∧ τ₁ == τ₂
var x == var y = fin-eq x y
fix σ == fix τ = σ == τ
_ == _ = false

-- this is nonterminating for sure (because we use equirecursion)
-- but it's generative (as in coinduction)
-- we want it to expand a couple times during type checking
{-# NO_TERMINATION_CHECK #-}
type-of : ∀ {n} → Context n → Data n → Type
type-of _ (base n)   = base (Fin n)
type-of Γ (pair σ τ) = ♯ (type-of Γ σ) * ♯ (type-of Γ τ)
type-of Γ (plus σ τ) = ♯ (type-of Γ σ) + ♯ (type-of Γ τ)
type-of Γ (var x)    = lookup x Γ
type-of Γ (fix τ)    = type-of (type-of Γ (fix τ) ∷ Γ) τ

inject-fin : ∀ {m n} → m ℕ.≤ n → Fin m → Fin n
inject-fin {zero} {zero} pf ()
inject-fin {zero} {suc n} pf ()
inject-fin {suc m} {zero} () i
inject-fin {suc m} {suc n} pf zero = zero
inject-fin {suc m} {suc n} (ℕ.s≤s pf) (suc i) = suc (inject-fin pf i)

mapMaybe : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
mapMaybe f (just x) = just (f x)
mapMaybe f nothing = nothing

{- have to do weakening properly...
weak : ∀ {n} {Γ : Context n} {σ τ} → Term Γ τ → Term (σ ∷ Γ) τ
weak (var i) = var (suc i)
weak (app t t₁) = app (weak t) (weak t₁)
weak {Γ = []} (abs t) = abs (try t {!!} {!!})
weak {Γ = x ∷ Γ} (abs t) = {!!}
weak (fix t) = fix (weak t)
weak (pair t t₁) = pair (weak t) (weak t₁)
weak (uncr t t₁) = uncr (weak t) (weak t₁)
weak (left t) = left (weak t)
weak (rite t) = rite (weak t)
weak (mach t t₁ t₂) = mach (weak t) (weak t₁) (weak t₂)
weak (base x) = base x
weak (call t t₁) = call (weak t) (weak t₁)
-}

Src : ∀ {n} → Context n → Data n → Data n → Set₁
Src Γ S T = Term Γ (type-of Γ S ⇒ type-of Γ T)

Witness : ∀ {n} → Context n → Set₁
Witness {n} Γ = (S : Data n) → (T : Data n) → Maybe (Src Γ S T)

Result : ∀ {n} → Data n → Data n → Set₁
Result {n} S T =
  Σ ℕ
    (λ m′ → let m = m′ ℕ.+ n in
      Σ (Context m) (λ Γ′ → Witness Γ′ × Src Γ′ (weaken m′ S) (weaken m′ T)))

coerce-src : ∀ {n} {Γ : Context n} →
             Witness Γ → (S : Data n) → (T : Data n) →
             Maybe (Result S T)

coerce-src {n} {Γ} A S T = match (A S T) where
  σ→τ : Type
  σ→τ = type-of Γ S ⇒ type-of Γ T

  A₀ : Witness (σ→τ ∷ Γ)
  A₀ S' T' =
    if S' == weaken 1 S ∧ T' == weaken 1 T then
      {!!} -- just (var zero) -- error due to lack of awareness of equality
    else
      weaken-witness A S' T'
      where
        weaken-witness : Witness Γ → Witness (σ→τ ∷ Γ)
        weaken-witness = {!!} -- some form of fmap'ed weeakening

  inspect : (S : Data n) → (T : Data n) → Maybe (Result S T)

  inspect (base m) (base n) = {!!}
  {-
    inj (m ℕ.≤? n) where
    open import Relation.Nullary.Core
    inj : Dec (m ℕ.≤ n) → Maybe (Witness Γ × Src Γ (base m) (base n))
    inj (yes m≤n) = just ({!!} , abs (call (base (inject-fin m≤n)) (var zero)))
    inj (no _) = nothing
  -}

  inspect (pair S₁ S₂) (pair T₁ T₂) = {!!}
  inspect (plus S₁ S₂) (plus T₁ T₂) = {!!}
  inspect (var x) T = {!!}
  inspect (fix S) T = {!!}
  inspect _ _ = nothing

  match : Maybe (Src Γ S T) → Maybe (Result S T)
  match (just t) = just (0 , Γ , A , t)
  match nothing = inspect S T

