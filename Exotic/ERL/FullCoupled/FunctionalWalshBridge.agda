{-# OPTIONS --safe #-}
module Exotic.ERL.FullCoupled.FunctionalWalshBridge where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Fin using (Fin)
open import Data.Product using (_,_)

open import Data.Vec.Functional as VF
  using (Vector; map; updateAt; zipWith; foldr; _∷_; [])
open import Data.Vec.Functional.Properties as VFP
  using (lookup-map; map-id; updateAt-updates)
open import Data.Vec.Functional.Relation.Binary.Pointwise as VFPW
  using (Pointwise)
open import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as VFPWP
  using (zipWith⁺; foldr-cong)

open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C

Walsh4 : Set
Walsh4 = Vector C.Int8 4

attentionPairVector : C.Sparsemax2Pair → Walsh4
attentionPairVector (x , y) =
  x VF.∷ y VF.∷ C.zero8 VF.∷ C.zero8 VF.∷ []

vectorMap-id : ∀ (xs : Walsh4) →
  VFPW.Pointwise _≡_ (map (λ x → x) xs) xs
vectorMap-id xs = VFP.map-id xs

vectorLookup-map :
  ∀ (i : Fin 4) (f : C.Int8 → C.Int8) (xs : Walsh4) →
  map f xs i ≡ f (xs i)
vectorLookup-map = VFP.lookup-map

vectorPointwise-refl :
  ∀ (xs : Walsh4) → VFPW.Pointwise _≡_ xs xs
vectorPointwise-refl xs i = refl

vectorUpdateAt-law :
  ∀ (xs : Walsh4) (i : Fin 4) (f : C.Int8 → C.Int8) →
  updateAt xs i f i ≡ f (xs i)
vectorUpdateAt-law xs i f = VFP.updateAt-updates i xs


vectorZipAdd : Walsh4 → Walsh4 → Walsh4
vectorZipAdd = zipWith C.int8Add

vectorZipAdd-cong :
  ∀ {xs ys us vs : Walsh4} →
  VFPW.Pointwise _≡_ xs ys →
  VFPW.Pointwise _≡_ us vs →
  VFPW.Pointwise _≡_
    (vectorZipAdd xs us)
    (vectorZipAdd ys vs)
vectorZipAdd-cong rs ss =
  VFPWP.zipWith⁺
    (λ {w} {x} {y} {z} p q →
      trans
        (cong (λ t → C.int8Add t y) p)
        (cong (C.int8Add x) q))
    rs
    ss

vectorFoldAdd : C.Int8 → Walsh4 → C.Int8
vectorFoldAdd d = foldr C.int8Add d

vectorFoldAdd-cong :
  ∀ {d e : C.Int8} {xs ys : Walsh4} →
  d ≡ e →
  VFPW.Pointwise _≡_ xs ys →
  vectorFoldAdd d xs ≡ vectorFoldAdd e ys
vectorFoldAdd-cong de rs =
  VFPWP.foldr-cong
    (λ {w} {x} {y} {z} p q →
      trans
        (cong (λ t → C.int8Add t y) p)
        (cong (C.int8Add x) q))
    de
    rs
