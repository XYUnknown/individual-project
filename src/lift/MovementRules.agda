{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
module lift.MovementRules where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Nat.Properties using (*-distribʳ-+)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Function using (_∘_)
  import lift.Primitives as Pm
  open Pm

  {- lemmas -}
  map-fill-empty : {s t : Set} → (m : ℕ) → (f : s → t) →
                   Pm.map (Pm.map f) (Pm.fill m []) ≡ Pm.fill m []
  map-fill-empty zero f = refl
  map-fill-empty (suc m) f =
    begin
      [] ∷ Pm.map (Pm.map f) (Pm.fill m [])
    ≡⟨ cong ([] ∷_) (map-fill-empty m f) ⟩
      refl

  map-head : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s (suc m)) n) →
             Pm.map f (Pm.map Pm.head xss) ≡ Pm.map Pm.head (Pm.map (Pm.map f) xss)
  map-head f [] = refl
  map-head f ((x ∷ xs) ∷ xss) =
    begin
      f x ∷ Pm.map f (Pm.map Pm.head xss)
    ≡⟨ cong (f x ∷_) (map-head f xss) ⟩
      refl

  map-tail : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s (suc m)) n) →
             Pm.map (Pm.map f) (Pm.map Pm.tail xss) ≡ Pm.map Pm.tail (Pm.map (Pm.map f) xss)
  map-tail f [] = refl
  map-tail f ((x ∷ xs) ∷ xss) =
    begin
      Pm.map f xs ∷ Pm.map (Pm.map f) (Pm.map Pm.tail xss)
    ≡⟨ cong (Pm.map f xs ∷_) (map-tail f xss) ⟩
      refl

  {- rules -}
  mapMapFBeforeTranspose : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s m) n) →
                           Pm.map (Pm.map f) (Pm.transpose xss) ≡ Pm.transpose (Pm.map (Pm.map f) xss)
  mapMapFBeforeTranspose {zero} {m} f [] =
    begin
      Pm.map (Pm.map f) (Pm.fill m [])
    ≡⟨ map-fill-empty m f ⟩
      refl
  mapMapFBeforeTranspose {suc n} {zero} f xss = refl
  mapMapFBeforeTranspose {suc n} {suc m} f ((x ∷ xs) ∷ xss) =
    begin
      (f x ∷ Pm.map f (Pm.map Pm.head xss)) ∷
      Pm.map (Pm.map f) (Pm.transpose (xs ∷ Pm.map Pm.tail xss))
    ≡⟨ cong ((f x ∷ Pm.map f (Pm.map Pm.head xss)) ∷_) (mapMapFBeforeTranspose f (xs ∷ Pm.map Pm.tail xss)) ⟩
      (f x ∷ Pm.map f (Pm.map Pm.head xss)) ∷
      Pm.transpose (Pm.map f xs ∷ Pm.map (Pm.map f) (Pm.map tail xss))
    ≡⟨ cong (_∷ Pm.transpose (Pm.map f xs ∷ Pm.map (Pm.map f) (Pm.map tail xss)))
       (cong (f x ∷_) (map-head f xss)) ⟩
      (f x ∷ Pm.map head (Pm.map (Pm.map f) xss)) ∷
      Pm.transpose (Pm.map f xs ∷ Pm.map (Pm.map f) (Pm.map Pm.tail xss))
    ≡⟨ cong (λ yss → (f x ∷ Pm.map head (Pm.map (Pm.map f) xss)) ∷
       Pm.transpose (Pm.map f xs ∷ yss)) (map-tail f xss) ⟩
      refl




