-- A traversable functor that is not regular.

open import Data.Nat
open import Data.Vec
open import Data.Product

record Applicative : Set₁ where
  constructor
    appl
  field
    Map   : Set → Set
    pure  : ∀ {A} → A → Map A
    call  : ∀ {A B} → Map (A → B) → Map A → Map B




Traversable : (Set → Set) → Set₁
Traversable F = (G : Applicative) →
                ∀ {A B} → (A → Map G B) → F A → Map G (F B)
  where open Applicative


infixr 10 _^_

-- exponents for naturals
_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

-- a regular container
RegCon : Set → Set
RegCon A = Σ ℕ (Vec A)

-- a regular traversal
regTrav : Traversable RegCon

regTrav G f (0 , []) = pure G ((0 , []))
  where open Applicative

regTrav G f (suc n , x ∷ xs) =
  call G (call G
    (pure G (λ y nys → (suc (proj₁ nys) , y ∷ proj₂ nys)))
    (f x)) (regTrav G f (n , xs))
  where open Applicative

-- a nonregular language: 0, 10, 1100, 111000, ....
nonreg : ℕ → ℕ
nonreg n = let 2n = 2 ^ n in 2n * pred 2n

-- a nonregular finitary container
NonregCon : Set → Set
NonregCon A = Σ ℕ (λ n → Vec A (nonreg n))

fmap : ∀ {A B} (G : Applicative) → (A → B) →
       let open Applicative in Map G A → Map G B
fmap G f gx = call G (pure G f) gx
  where open Applicative

-- a nonregular traversable functor
nonregTrav : Traversable NonregCon
nonregTrav G f (n , xs) =
  let
    gnnys = regTrav G f ((nonreg n , xs))
  in
    fmap G (λ{(nn , ys) → (n , {!ys!})}) gnnys
    -- should be well-typed but is not



