{-# OPTIONS --guardedness-preserving-type-constructors #-}

-- Agda specification of `coerce`
--
-- Incomplete: too much work just to make type system happy.
-- Conversions between morally identical types obscure
-- the operational content.

open import Function
open import Data.Product
open import Data.Maybe
open import Data.Bool hiding (_≟_)
open import Data.Sum
open import Data.Nat
import Data.Fin as Fin
open Fin using (Fin ; zero ; suc)

open import Relation.Nullary using (Dec ; yes ; no)
open import Coinduction renaming (Rec to Fix ; fold to roll ; unfold to unroll)

-- Things fail sometimes
postulate fail : ∀ {ℓ} {A : Set ℓ} → A

-- I know what I'm doing
postulate unsafeCast : ∀ {A B : Set} → A → B

data Data : Set where
  base : ℕ → Data
  pair : Data → Data → Data
  plus : Data → Data → Data
  var  : ℕ → Data
  fix  : Data → Data

-- infinite environments
Env : ∀ {ℓ} → Set ℓ → Set ℓ
Env A = ℕ → A

infixr 0 decide_then_else_

decide_then_else_ : ∀ {p ℓ} {P : Set p} {A : Set ℓ} → Dec P → A → A → A
decide yes p then x else y = x
decide no ¬p then x else y = y

--update : ∀ {ℓ} {A : Set ℓ} → ℕ → A → Env A → Env A
--update n v env = λ m → decide n ≟ m then v else env m

prepend : ∀ {ℓ} {A : Set ℓ} → A → Env A → Env A
prepend v env zero = v
prepend v env (suc m) = env m

-- universe construction; always terminating.
{-# NO_TERMINATION_CHECK #-}
uc : Data → Env Set → Set
uc (base x) ρ = Fin x
uc (pair S T) ρ = uc S ρ × uc T ρ
uc (plus S T) ρ = uc S ρ ⊎ uc T ρ
uc (var x) ρ = ρ x
uc (fix D) ρ = set where set = Fix (♯ (uc D (prepend set ρ)))

∅ : ∀ {ℓ} {A : Set ℓ} → Env A
∅ = fail

my-nat-data : Data
my-nat-data = fix (plus (base 1) (var zero))

My-nat : Set
My-nat = uc my-nat-data ∅

my-zero : My-nat
my-zero = roll (inj₁ zero)

my-one : My-nat
my-one = roll (inj₂ (roll (inj₁ zero)))

-- nonterminating stuff
botData : Data
botData = fix (var zero)

botType : Set
botType = uc botData ∅

{-# NON_TERMINATING #-}
⋯ : botType
⋯ = roll (roll (roll (roll (roll (roll ⋯)))))

shift : ℕ → ℕ → Data → Data
shift c d (base x) = base x
shift c d (pair S T) = pair (shift c d S) (shift c d T)
shift c d (plus S T) = plus (shift c d S) (shift c d T)
shift c d (var k) = decide suc k ≤? c then var k else var (k + d)
shift c d (fix D) = fix (shift c d D)

_[_↦_] : Data → ℕ → Data → Data
base x [ n ↦ S ] = base x
pair T T₁ [ n ↦ S ] = pair (T [ n ↦ S ]) (T₁ [ n ↦ S ])
plus T T₁ [ n ↦ S ] = plus (T [ n ↦ S ]) (T₁ [ n ↦ S ])
var k [ n ↦ S ] = decide k ≟ n then S else var k
fix T [ n ↦ S ] = fix (T [ n + 1 ↦ shift 0 1 S ])


import Level
open import Category.Monad
open RawMonad {Level.zero} monad

{-# NON_TERMINATING #-}
coerce : (S : Data) → (T : Data) → Maybe (uc S ∅ → (uc T ∅))

coerce (base m) (base n) with m ≤? n
... | yes m≤n = just (λ s → Fin.inject≤ s m≤n)
... | no  m>n = nothing

coerce (pair S₁ S₂) (pair T₁ T₂) =
  coerce S₁ T₁ >>= (λ f₁ →
  coerce S₂ T₂ >>= (λ f₂ →
  return (λ s → f₁ (proj₁ s) , f₂ (proj₂ s))))

coerce (plus S₁ S₂) (plus T₁ T₂) =
  coerce S₁ T₁ >>= (λ f₁ →
  coerce S₂ T₂ >>= (λ f₂ →
  return [ inj₁ ∘ f₁ , inj₂ ∘ f₂ ]))

coerce (var j) T =
  nothing -- should not happen

coerce (fix S) T =
  let
    S′ = S [ 0 ↦ fix S ]
  in
    coerce S′ T >>= (λ f →
    return (λ { (roll x) → f (unsafeCast x) }))

coerce S (fix T) =
  let
    T′ = T [ 0 ↦ fix T ]
  in
    coerce S T′ >>= (λ f →
    return (λ x → (roll (unsafeCast (f x)))))

coerce _ _ = nothing
