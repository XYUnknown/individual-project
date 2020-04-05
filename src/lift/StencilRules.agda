{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop --confluence-check #-}
{-# OPTIONS --with-K #-}
module lift.StencilRules where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.Nat.Properties using (*-distribʳ-+; *-distribˡ-+; +-assoc; *-assoc; +-comm; *-comm)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  import Relation.Binary.HeterogeneousEquality as Heq
  open Heq using (_≅_) renaming (sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
  open Heq.≅-Reasoning using (_≅⟨_⟩_) renaming (begin_ to hbegin_; _≡⟨⟩_ to _h≡⟨⟩_; _≡⟨_⟩_ to _h≡⟨_⟩_; _∎ to _h∎)
  open import lift.HeterogeneousHelpers using (hcong′)
  open import lift.Primitives using (map; id; take; drop; split;
    join; fill; head; tail; transpose; slide-lem; slide; cast)
  open import lift.Helpers
  open import lift.MovementRules using (mapMapFBeforeJoin)

  {- Tiling -}
  -- u = sz + n * (suc sp)
  -- suc v = (suc n) * (suc sp)
  -- sz - suc sp ≡ u - suc v
  lem₁ : (n m sz sp : ℕ) → sz + n * suc sp + m * suc (n + sp + n * sp) ≡ sz + (n + m * suc n) * suc sp
  lem₁ n m sz sp =
    begin
      sz + n * suc sp + m * (suc n + sp + n * sp)
    ≡⟨ cong (λ y → sz + n * suc sp + m * y) (+-assoc (suc n) sp (n * sp)) ⟩
      sz + n * suc sp + m * (suc n + (sp + n * sp))
    ≡⟨ cong (λ y → sz + n * suc sp + m * y) (cong (suc n +_) (sym (*-distribʳ-+ sp 1 n))) ⟩
      sz + n * suc sp + m * (suc n + (1 + n) * sp)
    ≡⟨ cong (λ y →  sz + n * suc sp + m * (suc n + y * sp)) (+-comm 1 n) ⟩
      sz + n * suc sp + m * (suc n + (suc n) * sp)
    ≡⟨ cong (λ y → sz + n * suc sp + m * y) (sym (*-distribˡ-+ (suc n) 1 sp)) ⟩
      sz + n * suc sp + m * (suc n * suc sp)
    ≡⟨ cong (λ y → sz + n * suc sp + y) (sym (*-assoc m (suc n) (suc sp))) ⟩
      sz + n * suc sp + m * suc n * suc sp
    ≡⟨ +-assoc sz (n * suc sp) (m * suc n * suc sp) ⟩
      cong (sz +_) (sym (*-distribʳ-+ (suc sp) n (m * suc n)))

  lem₂ : {n sz sp : ℕ} → {t : Set} → (xs : Vec t (sz + n * suc sp)) → xs ≡ cast (lem₁ n zero sz sp) xs
  lem₂ {zero} {zero} {sp} [] = refl
  lem₂ {zero} {suc sz} {sp} (x ∷ xs) = cong (x ∷_) (lem₂ {zero} {sz} {sp} xs)
  lem₂ {suc n} {zero} {sp} (x ∷ xs) = cong (x ∷_) (lem₂ {n} {sp} {sp} xs)
  lem₂ {suc n} {suc sz} {sp} (x ∷ xs) = cong (x ∷_) (lem₂ {suc n} {sz} {sp} xs)

  lem₃ : (n m sz sp : ℕ) →
         suc (sz + n * suc sp + (n + sp + n * sp + m * suc (n + sp + n * sp))) ≡
         suc (n + sp + n * sp + (sz + n * suc sp + m * suc (n + sp + n * sp)))
  lem₃ n m sz sp = let a = sz + n * suc sp; b = n + sp + n * sp; c = m * suc (n + sp + n * sp) in
    begin
      suc (a + (b + c))
    ≡⟨ cong suc (sym (+-assoc a b c))⟩
      suc (a + b + c)
    ≡⟨ cong suc (cong (_+ c) (+-comm a b))⟩
      cong suc (+-assoc b a c)

  lem₄ : {n m : ℕ} → {t : Set} → (sz sp : ℕ) →
         (xs : Vec t (suc (sz + n * suc sp + (n + sp + n * sp + m * suc (n + sp + n * sp))))) →
         slide {n} sz sp (take (sz + n * suc sp) {suc (n + sp + n * sp + m * suc (n + sp + n * sp))} xs) ++
         slide {n + m * suc n} sz sp (cast (lem₁ n m sz sp) (drop (suc (n + sp + n * sp)) (cast (lem₃ n m sz sp) xs))) ≡
         take sz {suc (sp + (n + (n + m * suc n)) * suc sp)} (cast (lem₁ n (suc m) sz sp) xs) ∷
         slide {n + (n + m * suc n)} sz sp (drop (suc sp) {sz + (n + (n + m * suc n)) * suc sp}
         (cast (slide-lem (n + (n + m * suc n)) sz sp ) (cast (lem₁ n (suc m) sz sp) xs)))
  lem₄ {zero} {m} sz sp xs = {!!}
  lem₄ {suc n} {m} sz sp xs = {!!}

  -- Adapted from paper https://www.lift-project.org/publications/2018/hagedorn18Stencils.pdf
  slideJoin : {n m : ℕ} → {t : Set} → (sz : ℕ) → (sp : ℕ) → (xs : Vec t (sz + n * (suc sp) + m * suc (n + sp + n * sp))) →
              join (map (λ (tile : Vec t (sz + n * (suc sp))) →
              slide {n} sz sp tile) (slide {m} (sz + n * (suc sp)) (n + sp + n * sp) xs)) ≡
              slide {n + m * (suc n)} sz sp (cast (lem₁ n m sz sp) xs)
  slideJoin {n} {zero} sz sp xs =
    begin
      slide sz sp xs ++ []
    ≡⟨ ++-[] (slide sz sp xs) ⟩
      slide sz sp xs
    ≡⟨ cong (slide sz sp) (lem₂ {n} {sz} {sp} xs) ⟩
      refl
  slideJoin {n} {suc m} sz sp xs =
    begin
      slide {n} sz sp (take (sz + n * suc sp) xs) ++
      join (map (slide {n} sz sp)
      (slide {m} (sz + n * suc sp) (n + sp + n * sp) (drop (suc (n + sp + n * sp)) (cast (lem₃ n m sz sp) xs))))
    ≡⟨ cong (slide {n} sz sp (take (sz + n * suc sp) xs) ++_)
      (slideJoin {n} {m} sz sp (drop (suc (n + sp + n * sp)) (cast (lem₃ n m sz sp) xs)) ) ⟩
      slide {n} sz sp (take (sz + n * suc sp) xs) ++
      slide {n + m * suc n} sz sp (cast (lem₁ n m sz sp) (drop (suc (n + sp + n * sp)) (cast (lem₃ n m sz sp) xs)))
    ≡⟨ lem₄ {n} {m} sz sp xs ⟩
      refl

  map-λ : {n m : ℕ} → {s t : Set} → (sz : ℕ) → (sp : ℕ) → (f : Vec s sz → Vec t sz) →
          (xs : Vec s (sz + n * (suc sp) + m * suc (n + sp + n * sp))) →
          map (λ (tile : Vec s (sz + n * (suc sp))) →
          map f (slide {n} sz sp tile)) (slide {m} (sz + n * (suc sp)) (n + sp + n * sp) xs) ≡
          map (map f) ((map (λ (tile : Vec s (sz + n * (suc sp))) →
          slide {n} sz sp tile)) (slide {m} (sz + n * (suc sp)) (n + sp + n * sp) xs))
  map-λ {n} {zero} sz sp f xs = refl
  map-λ {n} {suc m} sz sp f xs =
    begin
      map f (slide sz sp (take (sz + n * suc sp) xs)) ∷
      map (λ tile → map f (slide sz sp tile))
      (slide (sz + n * suc sp) (n + sp + n * sp)
      (drop (suc (n + sp + n * sp)) (cast _ xs)))
    ≡⟨ cong (map f (slide sz sp (take (sz + n * suc sp) xs)) ∷_) (map-λ sz sp f (drop (suc (n + sp + n * sp)) (cast _ xs))) ⟩
      refl

  tiling : {n m : ℕ} → {s t : Set} → (sz sp : ℕ) → (f : Vec s sz → Vec t sz) →
           (xs : Vec s (sz + n * (suc sp) + m * suc (n + sp + n * sp))) →
           join (map (λ (tile : Vec s (sz + n * (suc sp))) →
           map f (slide {n} sz sp tile)) (slide {m} (sz + n * (suc sp)) (n + sp + n * sp) xs)) ≡
           map f (slide {n + m * (suc n)} sz sp (cast (lem₁ n m sz sp) xs))
  tiling {n} {m} {s} {t} sz sp f xs =
    begin
      join (map (λ (tile : Vec s (sz + n * (suc sp))) →
      map f (slide {n} sz sp tile)) (slide {m} (sz + n * (suc sp)) (n + sp + n * sp) xs))
    ≡⟨ cong join (map-λ {n} {m} sz sp f xs) ⟩
      join (map (map f)
      (map (slide {n} sz sp) (slide {m} (sz + n * suc sp) (n + sp + n * sp) xs)))
    ≡⟨ mapMapFBeforeJoin f (map (slide {n} sz sp) (slide {m} (sz + n * suc sp) (n + sp + n * sp) xs)) ⟩
      map f (join (map (slide {n} sz sp) (slide {m} (sz + n * suc sp) (n + sp + n * sp) xs)))
    ≡⟨ cong (map f) (slideJoin {n} {m} sz sp xs) ⟩
      refl

  {- What is u v
  tiling₂ : {n m : ℕ} → {s t : Set} → (sz sp : ℕ) → (f : Vec s sz → Vec t sz) →
            (xs : Vec (Vec s (sz + n * (suc sp))) (sz + m * (suc sp))) →
            map₂ f slide₂ sz sp xs ≡
            map join (join (map transpose
            (map₂ (λ (tile : Vec (Vec s (sz + n * (suc sp))) (sz + m * (suc sp))) → map₂ f (slide₂ sz sp tile))
            (slide₂ u v xs))))
  -}

