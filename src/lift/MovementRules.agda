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

  {- Split -}
  splitBeforeMapMapF : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n * m)) →
                       map (map f) (split n {m} xs) ≡ split n {m} (map f xs)
  splitBeforeMapMapF n {m} f xs = map-split n {m} f xs

  mapFBeforeSplit : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n * m)) →
                    split n {m} (map f xs) ≡ map (map f) (split n {m} xs)
  mapFBeforeSplit n {m} f xs = sym (splitBeforeMapMapF n f xs)

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
  map-head-split : {m q : ℕ} → {t : Set} → (n : ℕ) → (xss : Vec (Vec t (n + n * m)) q) →
                    map head (map (split n {suc m}) xss) ≡ map (take n {n * m}) xss
  map-head-split n [] = refl
  map-head-split n (xs ∷ xss) = cong (take n xs ∷_) (map-head-split n xss)

  map-tail-split : {m q : ℕ} → {t : Set} → (n : ℕ) → (xss : Vec (Vec t (n + n * m)) q) →
                   map tail (map (split n {suc m}) xss) ≡ map (split n) (map (drop n) xss)
  map-tail-split n [] = refl
  map-tail-split n (xs ∷ xss) = cong (split n (drop n xs) ∷_) (map-tail-split n xss)

  lem₃ : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (n + n * m)) q) →
         map transpose (transpose (map (λ xs → take n {n * m} xs ∷ split n {m} (drop n xs)) xsss)) ≡
         transpose (map (take n {n * m}) xsss) ∷ map transpose (transpose (map (split n) (map (drop n) xsss)))
  lem₃ n [] = refl
  lem₃ n (xss ∷ xsss) = cong₂ (λ x y → transpose (take n xss ∷ x) ∷ map transpose (transpose (split n (drop n xss) ∷ y)))
                        (map-head-split n xsss) (map-tail-split n xsss)

  transposeBeforeSplit : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (n * m)) q) →
                         split n {m} (transpose xsss) ≡ map transpose (transpose (map (split n {m}) xsss))
  transposeBeforeSplit {zero} n [] = refl
  transposeBeforeSplit {zero} n (xss ∷ xsss) = refl
  transposeBeforeSplit {suc m} n xsss =
    begin
      take n (transpose xsss) ∷ split n (drop n (transpose xsss))
    ≡⟨ cong (_∷ split n (drop n (transpose xsss))) (take-transpose n xsss) ⟩
      transpose (map (take n) xsss) ∷ split n (drop n (transpose xsss))
    ≡⟨ cong (λ y → transpose (map (take n) xsss) ∷ split n y) (drop-transpose n xsss) ⟩
      transpose (map (take n) xsss) ∷ split n (transpose (map (drop n) xsss))
    ≡⟨ cong (transpose (map (take n) xsss) ∷_) (transposeBeforeSplit n (map (drop n) xsss)) ⟩
      sym (lem₃ n xsss)

  sym-lem₄ : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (n * m)) q) →
             map transpose (split n (transpose xsss)) ≡ transpose (map (split n {m}) xsss)
  sym-lem₄ n xsss =
    begin
      map transpose (split n (transpose xsss))
    ≡⟨ cong (map transpose) (transposeBeforeSplit n xsss) ⟩
      map transpose (map transpose (transpose (map (split n) xsss)))
    ≡⟨ double-map-transpose (transpose (map (split n) xsss)) ⟩
      refl

  mapSplitBeforeTranspose : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (n * m)) q) →
                            transpose (map (split n {m}) xsss) ≡ map transpose (split n (transpose xsss))
  mapSplitBeforeTranspose n xsss = sym (sym-lem₄ n xsss)

  sym-lem₅ : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) q) (n * m)) →
             transpose (map transpose (split n xsss)) ≡  map (split n {m}) (transpose xsss)
  sym-lem₅ n xsss =
    begin
      transpose (map transpose (split n xsss))
    ≡⟨ cong (λ y → transpose (map transpose (split n y))) (sym (identity₃ xsss)) ⟩
      transpose (map transpose (split n (transpose (transpose xsss))))
    ≡⟨ cong transpose (sym-lem₄ n (transpose xsss)) ⟩
      transpose (transpose (map (split n) (transpose xsss)))
    ≡⟨ identity₃ (map (split n) (transpose xsss)) ⟩
      refl

  transposeBeforeMapSplit : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) q) (n * m)) →
                            map (split n {m}) (transpose xsss) ≡ transpose (map transpose (split n xsss))
  transposeBeforeMapSplit n xsss = sym (sym-lem₅ n xsss)

  {- Transpose + Slide -}
  map-head-id : {n m : ℕ} → {t : Set} → (xss : Vec (Vec t m) n) →
                map head (map (λ xs → xs ∷ []) xss) ≡ xss
  map-head-id [] = refl
  map-head-id (xss₁ ∷ xss) = cong (xss₁ ∷_) (map-head-id xss)

  map-head-slide : {n m : ℕ} → {t : Set} → (sz sp : ℕ) → (xss : Vec (Vec t (suc (sp + (sz + (n + n * sp))))) m) →
                   map head (map (slide {suc n} sz sp) xss) ≡ map (take sz {suc (sp + (n + n * sp))}) xss
  map-head-slide sz sp [] = refl
  map-head-slide sz sp (xss₁ ∷ xss) = cong (take sz xss₁ ∷_) (map-head-slide sz sp xss)

  map-tail-slide : {n m : ℕ} → {t : Set} → (sz sp : ℕ) → (xss : Vec (Vec t (suc (sp + (sz + (n + n * sp))))) m) →
                   map tail (map (slide {suc n} sz sp) xss) ≡ map (slide sz sp) (map (drop (suc sp)) xss)
  map-tail-slide sz sp [] = refl
  map-tail-slide sz sp (xss₁ ∷ xss) = cong (slide sz sp (drop (suc sp) xss₁) ∷_) (map-tail-slide sz sp xss)

  lem₄ : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (suc (sp + (sz + (n + n * sp))))) m) →
         map transpose (transpose (map (λ xs → take sz {suc (sp + (n * suc sp))} xs ∷ slide {n} sz sp (drop (suc sp) xs)) xsss)) ≡
         transpose (map (take sz {suc (sp + (n + n * sp))}) xsss) ∷ map transpose (transpose (map (slide sz sp) (map (drop (suc sp)) xsss)))
  lem₄ sz sp [] = refl
  lem₄ {n} sz sp (xss ∷ xsss) =
    begin
      transpose (take sz {suc (sp + n * suc sp)} xss ∷ map head (map (slide sz sp) xsss)) ∷
      transpose (head (slide {n} sz sp (drop (suc sp) xss)) ∷ map head (map tail (map (slide sz sp) xsss))) ∷
      map transpose (transpose (tail (slide sz sp (drop (suc sp) xss)) ∷ map tail (map tail (map (slide sz sp) xsss))))
    ≡⟨ cong (λ y → transpose (take sz {suc (sp + n * suc sp)} xss ∷ y) ∷
       transpose (head (slide {n} sz sp (drop (suc sp) xss)) ∷ map head (map tail (map (slide sz sp) xsss))) ∷
       map transpose (transpose (tail (slide sz sp (drop (suc sp) xss)) ∷ map tail (map tail (map (slide sz sp) xsss)))))
       (map-head-slide sz sp xsss) ⟩
      transpose (take sz xss ∷ map (take sz) xsss) ∷
      transpose (head (slide {n} sz sp (drop (suc sp) xss)) ∷ map head (map tail (map (slide sz sp) xsss))) ∷
      map transpose (transpose (tail (slide sz sp (drop (suc sp) xss)) ∷ map tail (map tail (map (slide sz sp) xsss))))
    ≡⟨ cong₂ (λ x y → transpose (take sz xss ∷ map (take sz) xsss) ∷
       transpose (head (slide {n} sz sp (drop (suc sp) xss)) ∷ map head x) ∷
       map transpose (transpose (tail (slide sz sp (drop (suc sp) xss)) ∷ map tail y)))
       (map-tail-slide sz sp xsss) (map-tail-slide sz sp xsss) ⟩
      refl

  transposeBeforeSlide : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (sz + n * (suc sp))) m) →
                         slide {n} sz sp (transpose xsss) ≡ map transpose (transpose (map (slide {n} sz sp) xsss))
  transposeBeforeSlide {zero} sz sp [] = refl
  transposeBeforeSlide {zero} sz sp (xss ∷ xsss) = cong (λ y → transpose (xss ∷ y) ∷ []) (sym (map-head-id xsss))
  transposeBeforeSlide {suc n} sz sp xsss =
    begin
      take sz (transpose xsss) ∷ slide sz sp (drop (suc sp) (transpose xsss))
    ≡⟨ cong₂ (λ x y → x ∷ slide sz sp y) (take-transpose sz xsss) (drop-transpose (suc sp) xsss) ⟩
      transpose (map (take sz) xsss) ∷ slide sz sp (transpose (map (drop (suc sp)) xsss))
    ≡⟨ cong (transpose (map (take sz) xsss) ∷_) (transposeBeforeSlide sz sp (map (drop (suc sp)) xsss)) ⟩
      transpose (map (take sz) xsss) ∷ map transpose (transpose (map (slide sz sp) (map (drop (suc sp)) xsss)))
    ≡⟨ sym (lem₄ sz sp xsss)⟩
      refl

  sym-lem₆ : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (sz + n * (suc sp))) m) →
             map transpose (slide sz sp (transpose xsss)) ≡ transpose (map (slide {n} sz sp) xsss)
  sym-lem₆ sz sp xsss =
    begin
      map transpose (slide sz sp (transpose xsss))
    ≡⟨ cong (map transpose) (transposeBeforeSlide sz sp xsss) ⟩
      double-map-transpose (transpose (map (slide sz sp) xsss))

  mapSlideBeforeTranspose : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (sz + n * (suc sp))) m) →
                            transpose (map (slide {n} sz sp) xsss) ≡ map transpose (slide sz sp (transpose xsss))
  mapSlideBeforeTranspose sz sp xsss = sym (sym-lem₆ sz sp xsss)

  sym-lem₇ : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) m) (sz + n * (suc sp))) →
             transpose (map transpose (slide sz sp xsss)) ≡ map (slide {n} sz sp) (transpose xsss)
  sym-lem₇ sz sp xsss =
    begin
      transpose (map transpose (slide sz sp xsss))
    ≡⟨ cong (λ y → transpose (map transpose (slide sz sp y))) (sym (identity₃ xsss)) ⟩
      transpose (map transpose (slide sz sp (transpose (transpose xsss))))
    ≡⟨ cong (λ y → transpose y) (sym-lem₆ sz sp (transpose xsss)) ⟩
      identity₃ (map (slide sz sp) (transpose xsss))

  transposeBeforeMapSlide : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) m) (sz + n * (suc sp))) →
                            map (slide {n} sz sp) (transpose xsss) ≡ transpose (map transpose (slide sz sp xsss))
  transposeBeforeMapSlide sz sp xsss = sym (sym-lem₇ sz sp xsss)

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

  mapJoinBeforeJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                      join (map join xsss) ≅ join (join xsss)
  mapJoinBeforeJoin xsss = hsym (joinBeforeJoin xsss)

  {- Split + Slide -}
  -- split k (slide sz sp xs) ≡ map (slide sz sp) (slide (k + sz - sp) k xs)
  -- we choose k = (suc m) * sp
  -- for some reason i'm not able to declare it
  {-
  slideBeforeSplit : (sz sp : ℕ) → {n m : ℕ} → {t : Set} → (xs : Vec t (sz + ((suc m) * sp * n) * (suc sp))) →
                     split ((suc m) * sp) (slide sz sp xs) ≡ map (slide sz sp) (slide (sz + m * sp) ((suc m) * sp) xs)
  slideBeforeSplit = ?
  -}
