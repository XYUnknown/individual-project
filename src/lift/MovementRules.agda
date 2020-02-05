{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
module lift.MovementRules where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Nat.Properties using (*-distribʳ-+; *-assoc)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Function using (_∘_)
  import Relation.Binary.HeterogeneousEquality as Heq
  open Heq using (_≅_) renaming (sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
  open Heq.≅-Reasoning using (_≅⟨_⟩_) renaming (begin_ to hbegin_; _≡⟨⟩_ to _h≡⟨⟩_; _≡⟨_⟩_ to _h≡⟨_⟩_; _∎ to _h∎)
  open import lift.Primitives using (map; id; take; drop; split;
    join; fill; head; tail; transpose; slide; reduceSeq; reduce; partRed)
  open import lift.Helpers
  open import lift.AlgorithmicRules using (identity₃)
  open import lift.HeterogeneousHelpers using (hcong′)

  {- lemmas -}
  double-map-transpose : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                         map transpose (map transpose xsss) ≡ xsss
  double-map-transpose [] = refl
  double-map-transpose (xss ∷ xsss) =
    begin
      transpose (transpose xss) ∷ map transpose (map transpose xsss)
    ≡⟨ cong₂ (λ x y → x ∷ y) (identity₃ xss) (double-map-transpose xsss) ⟩
      refl

  map-fill-empty : {s t : Set} → (m : ℕ) → (f : s → t) →
                   map (map f) (fill m []) ≡ fill m []
  map-fill-empty zero f = refl
  map-fill-empty (suc m) f =
    begin
      [] ∷ map (map f) (fill m [])
    ≡⟨ cong ([] ∷_) (map-fill-empty m f) ⟩
      refl

  map-join-fill-empty : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t zero) →
                        fill n xs ≡ map (join {m}) (fill n [])
  map-join-fill-empty zero [] = refl
  map-join-fill-empty (suc n) [] =
    begin
      [] ∷ fill n []
    ≡⟨ cong ([] ∷_) (map-join-fill-empty n []) ⟩
      refl

  join-[] : {n : ℕ} → {t : Set} → (xs : Vec (Vec t zero) n) → (ys : Vec (Vec t zero) (suc n)) →
            join xs ≡ join ys
  join-[] [] ([] ∷ []) = refl
  join-[] ([] ∷ xs) ([] ∷ ys) =
    begin
      join xs
    ≡⟨ join-[] xs ys ⟩
      refl

  map-join-suc : {n m : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t zero) n) m) → (ysss : Vec (Vec (Vec t zero) (suc n)) m) →
                 map join xsss ≡ map join ysss
  map-join-suc [] [] = refl
  map-join-suc (xss ∷ xsss) (yss ∷ ysss) =
    begin
      join xss ∷ map join xsss
    ≡⟨ cong (_∷ map join xsss) (join-[] xss yss) ⟩
      join yss ∷ map join xsss
    ≡⟨ cong (join yss ∷_) (map-join-suc xsss ysss) ⟩
      refl

  map-head-transpose : {n m : ℕ} → {t : Set} → (xs : Vec t m) → (xss : Vec (Vec t (suc m)) n) →
                       map head (transpose (xs ∷ map tail xss)) ≡ xs
  map-head-transpose [] xss = refl
  map-head-transpose (x ∷ xs) xss =
    begin
      x ∷ map head (transpose (xs ∷ map tail (map tail xss)))
    ≡⟨ cong (x ∷_) (map-head-transpose xs (map tail xss)) ⟩
      refl

  map-tail-transpose : {n m : ℕ} → {t : Set} → (xs : Vec t m) → (xss : Vec (Vec t (suc m)) (suc n)) →
                       map tail (transpose (xs ∷ map tail xss)) ≡ transpose (map tail xss)
  map-tail-transpose [] xss = refl
  map-tail-transpose (x ∷ xs) xss =
    begin
      map head (map tail xss) ∷ map tail (transpose (xs ∷ map tail (map tail xss)))
    ≡⟨ cong (map head (map tail xss) ∷_) (map-tail-transpose xs (map tail xss)) ⟩
      refl

  map-head-tail-transpose : {n m : ℕ} → {t : Set} → (xs : Vec t m) → (xss : Vec (Vec t (suc m)) n) →
                            map head xss ∷ map tail (transpose (xs ∷ map tail xss)) ≡ transpose xss
  map-head-tail-transpose {zero} {zero} [] [] = refl
  map-head-tail-transpose {zero} {suc m} xs [] =
    begin
      [] ∷ [] ∷ map tail (transpose (tail xs ∷ []))
    ≡⟨ cong ([] ∷_) (map-head-tail-transpose (tail xs) [])⟩
      refl
  map-head-tail-transpose {suc n} {m} xs xss =
    begin
      map head xss ∷ map tail (transpose (xs ∷ map tail xss))
    ≡⟨ cong (map head xss ∷_) (map-tail-transpose xs xss) ⟩
      refl

  lem₁ : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t (suc o)) (suc m)) (suc n)) →
         map (map head) xsss ≡ map head (map (λ xss → map head xss ∷ transpose (map tail xss)) xsss)
  lem₁ {zero} (xss₁ ∷ []) = refl
  lem₁ {suc n} (xss₁ ∷ xsss) =
    begin
      map head xss₁ ∷ map (map head) xsss
    ≡⟨ cong (map head xss₁ ∷_) (lem₁ xsss) ⟩
      refl

  lem₂ : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t (suc o)) (suc m)) (suc n)) →
         map transpose (map (map tail) xsss) ≡
         map tail (map (λ xss → map head xss ∷ transpose (map tail xss)) xsss)
  lem₂ {zero} (xss₁ ∷ []) = refl
  lem₂ {suc n} (xss₁ ∷ xsss) =
    begin
      transpose (map tail xss₁) ∷ map transpose (map (map tail) xsss)
    ≡⟨ cong (transpose (map tail xss₁) ∷_) (lem₂ xsss) ⟩
      refl

  {- rules -}
  {- Transpose -}
  mapMapFBeforeTranspose : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s m) n) →
                           map (map f) (transpose xss) ≡ transpose (map (map f) xss)
  mapMapFBeforeTranspose {zero} {m} f [] =
    begin
      map (map f) (fill m [])
    ≡⟨ map-fill-empty m f ⟩
      refl
  mapMapFBeforeTranspose {suc n} {zero} f xss = refl
  mapMapFBeforeTranspose {suc n} {suc m} f ((x ∷ xs) ∷ xss) =
    begin
      (f x ∷ map f (map head xss)) ∷
      map (map f) (transpose (xs ∷ map tail xss))
    ≡⟨ cong ((f x ∷ map f (map head xss)) ∷_) (mapMapFBeforeTranspose f (xs ∷ map tail xss)) ⟩
      (f x ∷ map f (map head xss)) ∷
      transpose (map f xs ∷ map (map f) (map tail xss))
    ≡⟨ cong (_∷ transpose (map f xs ∷ map (map f) (map tail xss)))
       (cong (f x ∷_) (map-head f xss)) ⟩
      (f x ∷ map head (map (map f) xss)) ∷
      transpose (map f xs ∷ map (map f) (map tail xss))
    ≡⟨ cong (λ yss → (f x ∷ map head (map (map f) xss)) ∷
       transpose (map f xs ∷ yss)) (map-tail f xss) ⟩
      refl

  transposeBeforeMapMapF : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s m) n) →
                           transpose (map (map f) xss) ≡ map (map f) (transpose xss)
  transposeBeforeMapMapF f xss = sym (mapMapFBeforeTranspose f xss)

  {- Slide -}
  slideBeforeMapMapF : {n : ℕ} → (sz : ℕ) → (sp : ℕ) → {s t : Set} →
                       (f : s → t) → (xs : Vec s (sz + n * (suc sp))) →
                       map (map f) (slide {n} sz sp xs) ≡ slide {n} sz sp (map f xs)
  slideBeforeMapMapF {zero} sz sp f xs = refl
  slideBeforeMapMapF {suc n} sz sp f xs =
    begin
      map f (take sz xs) ∷
      map (map f) (slide {n} sz sp (drop (suc sp) xs))
    ≡⟨ cong (_∷ map (map f) (slide {n} sz sp (drop (suc sp) xs))) (map-take sz f xs) ⟩
      take sz (map f xs) ∷
      map (map f) (slide sz sp (drop (suc sp) xs))
    ≡⟨ cong (take sz (map f xs) ∷_) (slideBeforeMapMapF {n} sz sp f (drop (suc sp) xs))⟩
      take sz (map f xs) ∷ slide sz sp (map f (drop (suc sp) xs))
    ≡⟨ cong (λ ys → take sz (map f xs) ∷ slide sz sp ys) (map-drop (suc sp) f xs) ⟩
      refl

  mapFBeforeSlide : {n : ℕ} → (sz : ℕ) → (sp : ℕ) → {s t : Set} →
                    (f : s → t) → (xs : Vec s (sz + n * (suc sp))) →
                    slide {n} sz sp (map f xs) ≡ map (map f) (slide {n} sz sp xs)
  mapFBeforeSlide sz sp f xs = sym (slideBeforeMapMapF sz sp f xs)

  {- Join -}
  joinBeforeMapF : {s : Set} → {t : Set} → {m n : ℕ} →
                   (f : s → t) → (xs : Vec (Vec s n) m) →
                   map f (join xs) ≡ join (map (map f) xs)
  joinBeforeMapF f [] = refl
  joinBeforeMapF f (xs ∷ xs₁) =
    begin
      map f (xs ++ join (xs₁))
    ≡⟨ map-++ f xs (join xs₁) ⟩
      map f xs ++ map f (join xs₁)
    ≡⟨ cong (map f xs ++_) (joinBeforeMapF f xs₁) ⟩
      refl

  mapMapFBeforeJoin : {s : Set} → {t : Set} → {m n : ℕ} →
                      (f : s → t) → (xs : Vec (Vec s n) m) →
                      join (map (map f) xs) ≡ map f (join xs)
  mapMapFBeforeJoin f xs = sym (joinBeforeMapF f xs)

  {- Join + Transpose -}
  joinBeforeTranspose : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                        transpose (join xsss) ≡ map join (transpose (map transpose xsss))
  joinBeforeTranspose {zero} {m} {o} [] =
    begin
      fill o []
    ≡⟨ map-join-fill-empty o {m} [] ⟩
      refl
  joinBeforeTranspose {.(suc _)} {zero} {o} ([] ∷ xsss) =
    begin
      transpose (join xsss)
    ≡⟨ joinBeforeTranspose xsss ⟩
      map join (transpose (map transpose xsss))
    ≡⟨ map-join-suc (transpose (map transpose xsss)) (transpose (map transpose ([] ∷ xsss))) ⟩
      refl
  joinBeforeTranspose {.(suc _)} {suc m} {zero} (xss ∷ xsss) = refl
  joinBeforeTranspose {suc n} {suc m} {suc o} xsss =
    begin
      map head (join xsss) ∷ transpose (map tail (join xsss))
    ≡⟨ cong (_∷ transpose (map tail (join xsss))) (joinBeforeMapF head xsss) ⟩
      join (map (map head) xsss) ∷ transpose (map tail (join xsss))
    ≡⟨ cong (λ y → join (map (map head) xsss) ∷ transpose y)  (joinBeforeMapF tail xsss) ⟩
      join (map (map head) xsss) ∷ transpose (join (map (map tail) xsss))
    ≡⟨ cong (join (map (map head) xsss) ∷_) (joinBeforeTranspose (map (map tail) xsss)) ⟩
      join (map (map head) xsss) ∷
      map join (transpose (map transpose (map (map tail) xsss)))
    ≡⟨ cong (λ y → join y ∷ map join (transpose (map transpose (map (map tail) xsss))))
       (lem₁ xsss) ⟩
      join (map head (map (λ xss → map head xss ∷ transpose (map tail xss)) xsss)) ∷
      map join (transpose (map transpose (map (map tail) xsss)))
    ≡⟨ cong (λ y → join (map head (map (λ xss → map head xss ∷ transpose (map tail xss)) xsss)) ∷
       map join (transpose y)) (lem₂ xsss) ⟩
      refl

  sym-lem₁ : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
             transpose (join (map transpose xsss)) ≡ map join (transpose xsss)
  sym-lem₁ xsss =
    begin
      transpose (join (map transpose xsss))
    ≡⟨ joinBeforeTranspose (map transpose xsss) ⟩
      map join (transpose (map transpose (map transpose xsss)))
    ≡⟨ cong (λ y → map join (transpose y)) (double-map-transpose xsss) ⟩
      refl

  transposeBeforeMapJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                           map join (transpose xsss) ≡ transpose (join (map transpose xsss))
  transposeBeforeMapJoin xsss = sym (sym-lem₁ xsss)

  sym-lem₂ : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
             transpose (map join (transpose xsss)) ≡ join (map transpose xsss)
  sym-lem₂ xsss =
    begin
      transpose (map join (transpose xsss))
    ≡⟨ cong transpose (transposeBeforeMapJoin xsss) ⟩
      transpose (transpose (join (map transpose xsss)))
    ≡⟨ identity₃ (join (map transpose xsss)) ⟩
      refl

  mapTransposeBeforeJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                           join (map transpose xsss) ≡ transpose (map join (transpose xsss))
  mapTransposeBeforeJoin xsss = sym (sym-lem₂ xsss)

  sym-lem₃ : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
             join (map transpose (transpose xsss)) ≡ transpose (map join xsss)
  sym-lem₃ xsss =
    begin
      join (map transpose (transpose xsss))
    ≡⟨ mapTransposeBeforeJoin (transpose xsss) ⟩
      transpose (map join (transpose (transpose xsss)))
    ≡⟨ cong (λ y → transpose (map join y)) (identity₃ xsss) ⟩
      refl

  mapJoinBeforeTranspose : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                           transpose (map join xsss) ≡ join (map transpose (transpose xsss))
  mapJoinBeforeTranspose xsss = sym (sym-lem₃ xsss)

  {- Transpose + Split -}
  map-head-split : {m q : ℕ} → {t : Set} → (n : ℕ) → (xss : Vec (Vec t (n * (suc m))) q) →
                   transpose (map head (map (split n {suc m}) xss)) ≡ take n {n * m} (transpose xss)
  map-head-split n [] = {!!}
  map-head-split n (xs ∷ xss) = {!!}

  lem₃ :  {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (n + n * m)) q) →
          map transpose (transpose (map (split n {suc m}) xsss)) ≡
          take n {n * m} (transpose xsss) ∷ split n {m} (drop n (transpose xsss))
  lem₃ {m} {p} {zero} n [] = {!!}
  lem₃ {m} {p} {suc q} n xsss =
    begin
      transpose (map head (map (split n) xsss)) ∷
      map transpose (transpose (map tail (map (split n) xsss)))
    ≡⟨⟩
      {!!}

  transposeBeforeSplit : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (n * m)) q) →
                         split n {m} (transpose xsss) ≡
                         map transpose (transpose (map (split n {m}) xsss))
  transposeBeforeSplit {zero} n [] = refl
  transposeBeforeSplit {zero} n (xss ∷ xsss) = refl
  transposeBeforeSplit {suc m} n xsss =
    begin
      take n (transpose xsss) ∷ split n (drop n (transpose xsss))
    ≡⟨⟩
      {!!}

  {- Transpose + Slide -}
  transposeBeforeSlide : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (sz + n * (suc sp))) m) →
                         slide {n} sz sp (transpose xsss) ≡
                         map transpose (transpose (map (slide {n} sz sp) xsss))
  transposeBeforeSlide {n} {m} sz sp xsss = {!!}

  {- Join + Join -}
  joinBeforeJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                   join (join xsss) ≅ join (map join xsss)
  joinBeforeJoin [] = Heq.refl
  joinBeforeJoin {suc n} {m} {o} {t} (xss ∷ xsss) =
    hbegin
     join (xss ++ join xsss)
    ≅⟨ join-++ xss (join xsss) ⟩
     join xss ++ join (join xsss)
    ≅⟨ hcong′ (Vec t) (sym (*-assoc o m n)) (λ y → join xss ++ y) (joinBeforeJoin xsss) ⟩
     join xss ++ join (map join xsss)
    h∎
