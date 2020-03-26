{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop --confluence-check #-}
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
  open import lift.Primitives using (cast; map; id; take; drop; split;
    join; fill; head; tail; transpose; slide-lem; slide; reduceSeq; reduce; partRed)
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

  fill-[]₁ : {s t : Set} → (m : ℕ) → (f : s → t) →
             map (map f) (fill m []) ≡ fill m []
  fill-[]₁ zero f = refl
  fill-[]₁ (suc m) f = cong ([] ∷_) (fill-[]₁ m f)

  fill-[]₂ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t zero) →
             fill n xs ≡ map (join {m}) (fill n [])
  fill-[]₂ zero [] = refl
  fill-[]₂ (suc n) [] = cong ([] ∷_) (fill-[]₂ n [])

  join-[] : {n₁ n₂ : ℕ} → {t : Set} → (xs : Vec (Vec t zero) n₁) → (ys : Vec (Vec t zero) n₂) →
            join xs ≡ join ys
  join-[] [] [] = refl
  join-[] [] ([] ∷ ys₁) = join-[] [] ys₁
  join-[] ([] ∷ xs₁) ys = join-[] xs₁ ys

  map-join-[] : {n₁ n₂ m : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t zero) n₁) m) → (ysss : Vec (Vec (Vec t zero) n₂) m) →
                 map join xsss ≡ map join ysss
  map-join-[] [] [] = refl
  map-join-[] (xss ∷ xsss) (yss ∷ ysss) =
    begin
      join xss ∷ map join xsss
    ≡⟨ cong (_∷ map join xsss) (join-[] xss yss) ⟩
      join yss ∷ map join xsss
    ≡⟨ cong (join yss ∷_) (map-join-[] xsss ysss) ⟩
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

  map-map-head : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t (suc o)) (suc m)) (suc n)) →
                 map (map head) xsss ≡ map head (map transpose xsss)
  map-map-head {zero} (xss₁ ∷ []) = refl
  map-map-head {suc n} (xss₁ ∷ xsss) = cong (map head xss₁ ∷_) (map-map-head xsss)

  map-map-tail : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t (suc o)) (suc m)) (suc n)) →
                 map transpose (map (map tail) xsss) ≡ map tail (map transpose xsss)
  map-map-tail {zero} (xss₁ ∷ []) = refl
  map-map-tail {suc n} (xss₁ ∷ xsss) = cong (transpose (map tail xss₁) ∷_) (map-map-tail xsss)

  {- rules -}
  {- Transpose -}
  mapMapFBeforeTranspose : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s m) n) →
                           map (map f) (transpose xss) ≡ transpose (map (map f) xss)
  mapMapFBeforeTranspose {zero} {m} f [] = fill-[]₁ m f
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
  splitBeforeMapMapF : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (m * n)) →
                       map (map f) (split n {m} xs) ≡ split n {m} (map f xs)
  splitBeforeMapMapF n {m} f xs = map-split n {m} f xs

  mapFBeforeSplit : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (m * n)) →
                    split n {m} (map f xs) ≡ map (map f) (split n {m} xs)
  mapFBeforeSplit n {m} f xs = sym (splitBeforeMapMapF n f xs)

  {- Slide -}
  slideBeforeMapMapF : {n : ℕ} → (sz : ℕ) → (sp : ℕ) → {s t : Set} →
                       (f : s → t) → (xs : Vec s (sz + n * (suc sp))) →
                       map (map f) (slide {n} sz sp xs) ≡ slide {n} sz sp (map f xs)
  slideBeforeMapMapF {zero} sz sp f xs = refl
  slideBeforeMapMapF {suc n} sz sp f xs = let ys = (cast (slide-lem n sz sp) xs) in
    begin
      map f (take sz xs) ∷
      map (map f) (slide {n} sz sp (drop (suc sp) ys))
    ≡⟨ cong (_∷ map (map f) (slide {n} sz sp (drop (suc sp) ys))) (map-take sz f xs) ⟩
      take sz (map f xs) ∷
      map (map f) (slide sz sp (drop (suc sp) ys))
    ≡⟨ cong (take sz (map f xs) ∷_) (slideBeforeMapMapF {n} sz sp f (drop (suc sp) ys))⟩
      take sz (map f xs) ∷ slide sz sp (map f (drop (suc sp) ys))
    ≡⟨ cong (λ ys → take sz (map f xs) ∷ slide sz sp ys) (map-drop (suc sp) f ys) ⟩
      cong (λ y → take sz (map f xs) ∷ slide sz sp (drop (suc sp) y))
      (map-cast {sz + suc (sp + n * suc sp)} {suc (sp + (sz + n * suc sp))} f xs (slide-lem n sz sp))

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
  joinBeforeTranspose {zero} {m} {o} [] = fill-[]₂ o {m} []
  joinBeforeTranspose {suc n} {zero} {o} ([] ∷ xsss) =
    begin
      transpose (join xsss)
    ≡⟨ joinBeforeTranspose xsss ⟩
      map join (transpose (map transpose xsss))
    ≡⟨ map-join-[] (transpose (map transpose xsss)) (transpose (map transpose ([] ∷ xsss))) ⟩
      refl
  joinBeforeTranspose {suc n} {suc m} {zero} (xss ∷ xsss) = refl
  joinBeforeTranspose {suc n} {suc m} {suc o} xsss =
    begin
      map head (join xsss) ∷ transpose (map tail (join xsss))
    ≡⟨ cong₂ (λ x y → x ∷ transpose y) (joinBeforeMapF head xsss) (joinBeforeMapF tail xsss) ⟩
      join (map (map head) xsss) ∷ transpose (join (map (map tail) xsss))
    ≡⟨ cong (join (map (map head) xsss) ∷_) (joinBeforeTranspose (map (map tail) xsss)) ⟩
      join (map (map head) xsss) ∷ map join (transpose (map transpose (map (map tail) xsss)))
    ≡⟨ cong₂ (λ x y → join x ∷ map join (transpose y)) (map-map-head xsss) (map-map-tail xsss) ⟩
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
  map-head-split : {m q : ℕ} → {t : Set} → (n : ℕ) → (xss : Vec (Vec t (suc m * n)) q) →
                    map head (map (split n {suc m}) xss) ≡ map (take n {m * n}) xss
  map-head-split n [] = refl
  map-head-split n (xs ∷ xss) = cong (take n xs ∷_) (map-head-split n xss)

  map-tail-split : {m q : ℕ} → {t : Set} → (n : ℕ) → (xss : Vec (Vec t (suc m * n)) q) →
                   map tail (map (split n {suc m}) xss) ≡ map (split n) (map (drop n) xss)
  map-tail-split n [] = refl
  map-tail-split n (xs ∷ xss) = cong (split n (drop n xs) ∷_) (map-tail-split n xss)

  decompose-lem₁ : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (suc m * n)) q) →
                  map transpose (transpose (map (split n {suc m}) xsss)) ≡
                  transpose (map (take n {m * n}) xsss) ∷ map transpose (transpose (map (split n) (map (drop n) xsss)))
  decompose-lem₁ n [] = refl
  decompose-lem₁ n (xss ∷ xsss) = cong₂ (λ x y → transpose (take n xss ∷ x) ∷
                                 map transpose (transpose (split n (drop n xss) ∷ y)))
                                 (map-head-split n xsss) (map-tail-split n xsss)

  transposeBeforeSplit : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (m * n)) q) →
                         split n {m} (transpose xsss) ≡ map transpose (transpose (map (split n {m}) xsss))
  transposeBeforeSplit {zero} n [] = refl
  transposeBeforeSplit {zero} n (xss ∷ xsss) = refl
  transposeBeforeSplit {suc m} n xsss =
    begin
      take n (transpose xsss) ∷ split n (drop n (transpose xsss))
    ≡⟨ cong₂ (λ x y → x ∷ split n y) (take-transpose n xsss) (drop-transpose n xsss) ⟩
      transpose (map (take n) xsss) ∷ split n (transpose (map (drop n) xsss))
    ≡⟨ cong (transpose (map (take n) xsss) ∷_) (transposeBeforeSplit n (map (drop n) xsss)) ⟩
      transpose (map (take n) xsss) ∷ map transpose (transpose (map (split n) (map (drop n) xsss)))
    ≡⟨ sym (decompose-lem₁ n xsss) ⟩
      refl

  sym-lem₄ : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (m * n)) q) →
             map transpose (split n (transpose xsss)) ≡ transpose (map (split n {m}) xsss)
  sym-lem₄ n xsss =
    begin
      map transpose (split n (transpose xsss))
    ≡⟨ cong (map transpose) (transposeBeforeSplit n xsss) ⟩
      map transpose (map transpose (transpose (map (split n) xsss)))
    ≡⟨ double-map-transpose (transpose (map (split n) xsss)) ⟩
      refl

  mapSplitBeforeTranspose : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (m * n)) q) →
                            transpose (map (split n {m}) xsss) ≡ map transpose (split n (transpose xsss))
  mapSplitBeforeTranspose n xsss = sym (sym-lem₄ n xsss)

  transposeBeforeMapSplit : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) q) (m * n)) →
                            map (split n {m}) (transpose xsss) ≡ transpose (map transpose (split n xsss))
  transposeBeforeMapSplit n xsss =
    begin
      map (split n) (transpose xsss)
    ≡⟨ sym (identity₃ (map (split n) (transpose xsss))) ⟩
      transpose (transpose (map (split n) (transpose xsss)))
    ≡⟨ cong transpose (mapSplitBeforeTranspose n (transpose xsss)) ⟩
      transpose (map transpose (split n (transpose (transpose xsss))))
    ≡⟨ cong (λ y → transpose (map transpose (split n y))) (identity₃ xsss) ⟩
      refl

  {- Transpose + Slide -}
  map-head-id : {n m : ℕ} → {t : Set} → (xss : Vec (Vec t m) n) →
                map head (map (λ xs → xs ∷ []) xss) ≡ xss
  map-head-id [] = refl
  map-head-id (xss₁ ∷ xss) = cong (xss₁ ∷_) (map-head-id xss)

  map-head-slide : {n m : ℕ} → {t : Set} → (sz sp : ℕ) → (xss : Vec (Vec t (suc (sz + (sp + n * suc sp)))) m) →
                   map head (map (slide {suc n} sz sp) xss) ≡ map (take sz {suc (sp + n * suc sp)}) xss
  map-head-slide sz sp [] = refl
  map-head-slide sz sp (xss₁ ∷ xss) = cong (take sz xss₁ ∷_) (map-head-slide sz sp xss)

  map-tail-slide : {n m : ℕ} → {t : Set} → (sz sp : ℕ) → (xss : Vec (Vec t (suc (sz + (sp + n * suc sp)))) m) →
                   map tail (map (slide {suc n} sz sp) xss) ≡ map (slide sz sp) (map (drop (suc sp)) (map (cast (slide-lem n sz sp)) xss))
  map-tail-slide sz sp [] = refl
  map-tail-slide {n} sz sp (xss₁ ∷ xss) = let yss = cast (slide-lem n sz sp) xss₁ in
    cong (slide sz sp (drop (suc sp) yss) ∷_) (map-tail-slide sz sp xss)

  decompose-lem₂ : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (suc (sz + (sp + n * suc sp)))) m) →
                   map transpose (transpose (map (λ xs → take sz {suc (sp + n * suc sp)} xs ∷
                   slide {n} sz sp (drop (suc sp) (cast (slide-lem n sz sp) xs))) xsss)) ≡
                   transpose (map (take sz {suc (sp + n * suc sp)}) xsss) ∷
                   map transpose (transpose (map (slide sz sp) (map (drop (suc sp)) (map (cast (slide-lem n sz sp)) xsss))))
  decompose-lem₂ sz sp [] = refl
  decompose-lem₂ {n} sz sp (xss ∷ xsss) = let yss = cast (slide-lem n sz sp) xss in
    begin
      transpose (take sz {suc (sp + n * suc sp)} xss ∷ map head (map (slide sz sp) xsss)) ∷
      transpose (head (slide {n} sz sp (drop (suc sp) yss)) ∷ map head (map tail (map (slide sz sp) xsss))) ∷
      map transpose (transpose (tail (slide sz sp (drop (suc sp) yss)) ∷ map tail (map tail (map (slide sz sp) xsss))))
    ≡⟨ cong (λ y → transpose (take sz {suc (sp + n * suc sp)} xss ∷ y) ∷
       transpose (head (slide {n} sz sp (drop (suc sp) yss)) ∷ map head (map tail (map (slide sz sp) xsss))) ∷
       map transpose (transpose (tail (slide sz sp (drop (suc sp) yss)) ∷ map tail (map tail (map (slide sz sp) xsss)))))
       (map-head-slide sz sp xsss) ⟩
      transpose (take sz xss ∷ map (take sz) xsss) ∷
      transpose (head (slide {n} sz sp (drop (suc sp) yss)) ∷ map head (map tail (map (slide sz sp) xsss))) ∷
      map transpose (transpose (tail (slide sz sp (drop (suc sp) yss)) ∷ map tail (map tail (map (slide sz sp) xsss))))
    ≡⟨ cong₂ (λ x y → transpose (take sz xss ∷ map (take sz) xsss) ∷
       transpose (head (slide {n} sz sp (drop (suc sp) yss)) ∷ map head x) ∷
       map transpose (transpose (tail (slide sz sp (drop (suc sp) yss)) ∷ map tail y)))
       (map-tail-slide sz sp xsss) (map-tail-slide sz sp xsss) ⟩
      refl

  transposeBeforeSlide : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (sz + n * (suc sp))) m) →
                         slide {n} sz sp (transpose xsss) ≡ map transpose (transpose (map (slide {n} sz sp) xsss))
  transposeBeforeSlide {zero} sz sp [] = refl
  transposeBeforeSlide {zero} sz sp (xss ∷ xsss) = cong (λ y → transpose (xss ∷ y) ∷ []) (sym (map-head-id xsss))
  transposeBeforeSlide {suc n} sz sp xsss = let ys = map (cast (slide-lem n sz sp)) xsss in
    begin
      take sz (transpose xsss) ∷ slide sz sp (drop (suc sp) (cast _ (transpose xsss)))
    ≡⟨ cong (λ y → take sz (transpose xsss) ∷ slide sz sp (drop (suc sp) y)) (transpose-cast (slide-lem n sz sp) xsss)  ⟩
      take sz (transpose xsss) ∷ slide sz sp (drop (suc sp) (transpose ys))
    ≡⟨ cong₂ (λ x y → x ∷ slide sz sp y) (take-transpose sz xsss) (drop-transpose (suc sp) ys) ⟩
      transpose (map (take sz) xsss) ∷ slide sz sp (transpose (map (drop (suc sp)) ys))
    ≡⟨ cong (transpose (map (take sz) xsss) ∷_) (transposeBeforeSlide sz sp (map (drop (suc sp)) ys)) ⟩
      transpose (map (take sz) xsss) ∷ map transpose (transpose (map (slide sz sp) (map (drop (suc sp)) ys)))
    ≡⟨ sym (decompose-lem₂ sz sp xsss) ⟩
      refl

  sym-lem₅ : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (sz + n * (suc sp))) m) →
             map transpose (slide sz sp (transpose xsss)) ≡ transpose (map (slide {n} sz sp) xsss)
  sym-lem₅ sz sp xsss =
    begin
      map transpose (slide sz sp (transpose xsss))
    ≡⟨ cong (map transpose) (transposeBeforeSlide sz sp xsss) ⟩
      map transpose (map transpose (transpose (map (slide sz sp) xsss)))
    ≡⟨ double-map-transpose (transpose (map (slide sz sp) xsss)) ⟩
      refl

  mapSlideBeforeTranspose : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (sz + n * (suc sp))) m) →
                            transpose (map (slide {n} sz sp) xsss) ≡ map transpose (slide sz sp (transpose xsss))
  mapSlideBeforeTranspose sz sp xsss = sym (sym-lem₅ sz sp xsss)

  transposeBeforeMapSlide : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) m) (sz + n * (suc sp))) →
                            map (slide {n} sz sp) (transpose xsss) ≡ transpose (map transpose (slide sz sp xsss))
  transposeBeforeMapSlide sz sp xsss =
    begin
      map (slide sz sp) (transpose xsss)
    ≡⟨ sym (identity₃ (map (slide sz sp) (transpose xsss))) ⟩
      transpose (transpose (map (slide sz sp) (transpose xsss)))
    ≡⟨ cong transpose (mapSlideBeforeTranspose sz sp (transpose xsss)) ⟩
      transpose (map transpose (slide sz sp (transpose (transpose xsss))))
    ≡⟨ cong (λ y → transpose (map transpose (slide sz sp y))) (identity₃ xsss) ⟩
      refl

  {- Join + Join -}
  joinBeforeJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                   join (join xsss) ≅ join (map join xsss)
  joinBeforeJoin [] = Heq.refl
  joinBeforeJoin {suc n} {m} {o} {t} (xss ∷ xsss) =
    hbegin
     join (xss ++ join xsss)
    ≅⟨ join-++ xss (join xsss) ⟩
     join xss ++ join (join xsss)
    ≅⟨ hcong′ (Vec t) (*-assoc n m o) (λ y → join xss ++ y) (joinBeforeJoin xsss) ⟩
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
