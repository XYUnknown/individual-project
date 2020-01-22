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
  open import lift.Helpers

  {- lemmas -}
  map-fill-empty : {s t : Set} → (m : ℕ) → (f : s → t) →
                   Pm.map (Pm.map f) (Pm.fill m []) ≡ Pm.fill m []
  map-fill-empty zero f = refl
  map-fill-empty (suc m) f =
    begin
      [] ∷ Pm.map (Pm.map f) (Pm.fill m [])
    ≡⟨ cong ([] ∷_) (map-fill-empty m f) ⟩
      refl

  map-join-fill-empty : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t zero) →
                        Pm.fill n xs ≡ Pm.map (Pm.join {m}) (Pm.fill n [])
  map-join-fill-empty zero [] = refl
  map-join-fill-empty (suc n) [] =
    begin
      [] ∷ Pm.fill n []
    ≡⟨ cong ([] ∷_) (map-join-fill-empty n []) ⟩
      refl

  join-[] : {n : ℕ} → {t : Set} → (xs : Vec (Vec t zero) n) → (ys : Vec (Vec t zero) (suc n)) →
            Pm.join xs ≡ Pm.join ys
  join-[] [] ([] ∷ []) = refl
  join-[] ([] ∷ xs) ([] ∷ ys) =
    begin
      Pm.join xs
    ≡⟨ join-[] xs ys ⟩
      refl

  map-join-suc : {n m : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t zero) n) m) → (ysss : Vec (Vec (Vec t zero) (suc n)) m) →
                 Pm.map Pm.join xsss ≡ Pm.map Pm.join ysss
  map-join-suc [] [] = refl
  map-join-suc (xss ∷ xsss) (yss ∷ ysss) =
    begin
      Pm.join xss ∷ Pm.map Pm.join xsss
    ≡⟨ cong (_∷ Pm.map Pm.join xsss) (join-[] xss yss) ⟩
      Pm.join yss ∷ Pm.map Pm.join xsss
    ≡⟨ cong (Pm.join yss ∷_) (map-join-suc xsss ysss) ⟩
      refl

  lem₁ : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t (suc o)) (suc m)) (suc n)) →
         Pm.map (Pm.map Pm.head) xsss ≡ Pm.map Pm.head (Pm.map (λ xss → Pm.map Pm.head xss ∷ Pm.transpose (Pm.map Pm.tail xss)) xsss)
  lem₁ {zero} (xss₁ ∷ []) = refl
  lem₁ {suc n} (xss₁ ∷ xsss) =
    begin
      Pm.map Pm.head xss₁ ∷ Pm.map (Pm.map Pm.head) xsss
    ≡⟨ cong (Pm.map Pm.head xss₁ ∷_) (lem₁ xsss) ⟩
      refl

  lem₂ : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t (suc o)) (suc m)) (suc n)) →
         Pm.map Pm.transpose (Pm.map (Pm.map Pm.tail) xsss) ≡
         Pm.map Pm.tail (Pm.map (λ xss → Pm.map Pm.head xss ∷ Pm.transpose (Pm.map Pm.tail xss)) xsss)
  lem₂ {zero} (xss₁ ∷ []) = refl
  lem₂ {suc n} (xss₁ ∷ xsss) =
    begin
      Pm.transpose (Pm.map Pm.tail xss₁) ∷ Pm.map Pm.transpose (Pm.map (Pm.map Pm.tail) xsss)
    ≡⟨ cong (Pm.transpose (Pm.map Pm.tail xss₁) ∷_) (lem₂ xsss) ⟩
      refl

  {- rules -}
  {- Transpose -}
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

  {- Slide -}
  slideBeforeMapMapF : {n : ℕ} → (sz : ℕ) → (sp : ℕ) → {s t : Set} →
                       (f : s → t) → (xs : Vec s (sz + n * (suc sp))) →
                       Pm.map (Pm.map f) (Pm.slide {n} sz sp xs) ≡ Pm.slide {n} sz sp (Pm.map f xs)
  slideBeforeMapMapF {zero} sz sp f xs = refl
  slideBeforeMapMapF {suc n} sz sp f xs =
    begin
      Pm.map f (take sz xs) ∷
      Pm.map (Pm.map f) (Pm.slide {n} sz sp (Pm.drop (suc sp) xs))
    ≡⟨ cong (_∷ Pm.map (Pm.map f) (Pm.slide {n} sz sp (Pm.drop (suc sp) xs))) (map-take sz f xs) ⟩
      Pm.take sz (Pm.map f xs) ∷
      Pm.map (Pm.map f) (Pm.slide sz sp (Pm.drop (suc sp) xs))
    ≡⟨ cong (Pm.take sz (Pm.map f xs) ∷_) (slideBeforeMapMapF {n} sz sp f (Pm.drop (suc sp) xs))⟩
      Pm.take sz (Pm.map f xs) ∷ Pm.slide sz sp (Pm.map f (Pm.drop (suc sp) xs))
    ≡⟨ cong (λ ys → Pm.take sz (Pm.map f xs) ∷ Pm.slide sz sp ys) (map-drop (suc sp) f xs) ⟩
      refl

  {- Join -}
  joinBeforeMapF : {s : Set} → {t : Set} → {m n : ℕ} →
             (f : s → t) → (xs : Vec (Vec s n) m) →
             Pm.map f (Pm.join xs) ≡ Pm.join (Pm.map (Pm.map f) xs)
  joinBeforeMapF f [] = refl
  joinBeforeMapF f (xs ∷ xs₁) =
    begin
      Pm.map f (xs ++ Pm.join (xs₁))
    ≡⟨ map-++ f xs (Pm.join xs₁) ⟩
      Pm.map f xs ++ Pm.map f (Pm.join xs₁)
    ≡⟨ cong (Pm.map f xs ++_) (joinBeforeMapF f xs₁) ⟩
      refl

  {- Join + Transpose -}
  joinBeforeTranspose : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                        Pm.transpose (Pm.join xsss) ≡ Pm.map Pm.join (Pm.transpose (Pm.map Pm.transpose xsss))
  joinBeforeTranspose {zero} {m} {o} [] =
    begin
      Pm.fill o []
    ≡⟨ map-join-fill-empty o {m} [] ⟩
      refl
  joinBeforeTranspose {.(suc _)} {zero} {o} ([] ∷ xsss) =
    begin
      Pm.transpose (Pm.join xsss)
    ≡⟨ joinBeforeTranspose xsss ⟩
      Pm.map Pm.join (Pm.transpose (Pm.map Pm.transpose xsss))
    ≡⟨ map-join-suc (Pm.transpose (Pm.map Pm.transpose xsss)) (Pm.transpose (Pm.map Pm.transpose ([] ∷ xsss))) ⟩
      refl
  joinBeforeTranspose {.(suc _)} {suc m} {zero} (xss ∷ xsss) = refl
  joinBeforeTranspose {suc n} {suc m} {suc o} xsss =
    begin
      Pm.map Pm.head (Pm.join xsss) ∷ Pm.transpose (Pm.map Pm.tail (Pm.join xsss))
    ≡⟨ cong (_∷ Pm.transpose (Pm.map Pm.tail (Pm.join xsss))) (joinBeforeMapF Pm.head xsss) ⟩
      Pm.join (Pm.map (Pm.map Pm.head) xsss) ∷ Pm.transpose (Pm.map Pm.tail (Pm.join xsss))
    ≡⟨ cong (λ y →  Pm.join (Pm.map (Pm.map Pm.head) xsss) ∷ Pm.transpose y)  (joinBeforeMapF Pm.tail xsss) ⟩
      Pm.join (Pm.map (Pm.map head) xsss) ∷ Pm.transpose (Pm.join (Pm.map (Pm.map Pm.tail) xsss))
    ≡⟨ cong (Pm.join (Pm.map (Pm.map head) xsss) ∷_) (joinBeforeTranspose (Pm.map (Pm.map Pm.tail) xsss)) ⟩
      Pm.join (Pm.map (Pm.map Pm.head) xsss) ∷
      Pm.map Pm.join (Pm.transpose (Pm.map Pm.transpose (Pm.map (Pm.map Pm.tail) xsss)))
    ≡⟨ cong (λ y → join y ∷ Pm.map Pm.join (Pm.transpose (Pm.map Pm.transpose (Pm.map (Pm.map Pm.tail) xsss))))
       (lem₁ xsss) ⟩
      Pm.join (Pm.map Pm.head (Pm.map (λ xss → Pm.map Pm.head xss ∷ Pm.transpose (Pm.map Pm.tail xss)) xsss)) ∷
      Pm.map Pm.join (Pm.transpose (Pm.map Pm.transpose (Pm.map (Pm.map Pm.tail) xsss)))
    ≡⟨ cong (λ y → Pm.join (Pm.map Pm.head (Pm.map (λ xss → Pm.map Pm.head xss ∷ Pm.transpose (Pm.map Pm.tail xss)) xsss)) ∷
       Pm.map Pm.join (Pm.transpose y)) (lem₂ xsss) ⟩
      refl

  {- Join + Join -}
  joinBeforeJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                   Pm.join (Pm.join xsss) ≡ Pm.join (Pm.map Pm.join xsss)
  joinBeforeJoin [] = refl
  joinBeforeJoin (xss ∷ xsss) =
    begin
      Pm.join (xss ++ Pm.join xsss)
    ≡⟨ join-++ xss (Pm.join xsss)⟩
      Pm.join xss ++ Pm.join (Pm.join xsss)
    ≡⟨ cong (Pm.join xss ++_) (joinBeforeJoin xsss) ⟩
      refl
