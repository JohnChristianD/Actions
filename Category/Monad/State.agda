module Category.Monad.State where

open import Data.Product.Base using (_×_; _,_; uncurry)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Effect.Applicative.Indexed using (IFun)
open import Effect.Monad using (RawMonad)
open import Effect.Monad.Indexed using (RawIMonad)
open import Function.Base using (_∘_)
open import Level using (Level; suc; _⊔_)

private
  variable
    i f : Level
    I : Set i

IStateT : (I → Set f) → (Set f → Set f) → IFun I f
IStateT S M i j A = S i → M (A × S j)

StateTIMonad : ∀ (S : I → Set f) {M} → RawMonad M → RawIMonad (IStateT S M)
StateTIMonad S Mon = record
  { return = λ x s → return (x , s)
  ; _>>=_  = λ m f s → m s >>= uncurry f
  }
  where open RawMonad Mon

record RawIMonadState {I : Set i} (S : I → Set f)
                      (M : IFun I f) : Set (i ⊔ suc f) where
  field
    monad : RawIMonad M
    get   : ∀ {i} → M i i (S i)
    put   : ∀ {i j} → S j → M i j ⊤

  open RawIMonad monad public

  modify : ∀ {i j} → (S i → S j) → M i j ⊤
  modify f = get >>= put ∘ f

StateTIMonadState : ∀ {i f} {I : Set i} (S : I → Set f) {M} →
                    RawMonad M → RawIMonadState S (IStateT S M)
StateTIMonadState S Mon = record
  { monad = StateTIMonad S Mon
  ; get   = λ s   → return (s , s)
  ; put   = λ s _ → return (_ , s)
  }
  where open RawMonad Mon
