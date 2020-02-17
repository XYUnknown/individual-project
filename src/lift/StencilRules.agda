{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
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
    join; fill; head; tail; transpose; slide)
  open import lift.Helpers

  {- Tiling -}
  -- u = sz + n * (suc sp)
  -- suc v = (suc n) * (suc sp)
  -- sz - suc sp ≡ u - suc v
  lem₁ : (n m sz sp : ℕ) →
         sz + n * (suc sp) + m * suc (n + sp + n * sp) ≡ sz + (n + m * (suc n)) * (suc sp)
  lem₁ n m sz sp =
    begin
      sz + (n + n * sp) + (m + m * (n + sp + n * sp))
    ≡⟨ cong (λ y → sz + (n + n * sp) + (m + m * y)) (+-assoc n sp (n * sp)) ⟩
      sz + (n + n * sp) + (m + m * (n + (sp + n * sp)))
    ≡⟨ cong (λ y →  sz + (n + n * sp) + (m + y)) (*-distribˡ-+ m n (sp + n * sp)) ⟩
      sz + (n + n * sp) + (m + (m * n + m * (sp + n * sp)))
    ≡⟨ cong (λ y → sz + (n + n * sp) + y) (sym (+-assoc m (m * n) (m * (sp + n * sp)))) ⟩
      sz + (n + n * sp) + (m + m * n + m * (sp + n * sp))
    ≡⟨ +-assoc sz (n + n * sp) (m + m * n + m * (sp + n * sp)) ⟩
      sz + (n + n * sp + (m + m * n + m * (sp + n * sp)))
    ≡⟨ cong (λ y → sz + (n + n * sp + (m + m * n + y))) (*-distribˡ-+ m sp (n * sp)) ⟩
      sz + (n + n * sp + (m + m * n + (m * sp + m * (n * sp))))
    ≡⟨ cong (λ y → sz + (n + n * sp + (m + m * n + (m * sp + y)))) (sym (*-assoc m n sp)) ⟩
      sz + (n + n * sp + (m + m * n + (m * sp + m * n * sp)))
    ≡⟨ cong (λ y → sz + y) (sym (+-assoc (n + n * sp) (m + m * n) (m * sp + m * n * sp))) ⟩
      sz + (n + n * sp + (m + m * n) + (m * sp + m * n * sp))
    ≡⟨ cong (λ y → sz + (n + n * sp + (m + m * n) + y)) (sym (*-distribʳ-+ sp m (m * n))) ⟩
      sz + (n + n * sp + (m + m * n) + (m + m * n) * sp)
    ≡⟨ cong (λ y → sz + (y + (m + m * n) * sp)) (+-assoc n (n * sp) (m + m * n)) ⟩
      sz + (n + (n * sp + (m + m * n)) + (m + m * n) * sp)
    ≡⟨ cong (λ y → sz + (n + y + (m + m * n) * sp)) (+-comm (n * sp) (m + m * n)) ⟩
      sz + (n + (m + m * n + n * sp) + (m + m * n) * sp)
    ≡⟨ cong (λ y → sz + y) (+-assoc n (m + m * n + n * sp) ((m + m * n) * sp)) ⟩
      sz + (n + (m + m * n + n * sp + (m + m * n) * sp))
    ≡⟨ cong (λ y → sz + (n + y)) (+-assoc (m + m * n) (n * sp) ((m + m * n) * sp)) ⟩
      sz + (n + (m + m * n + (n * sp + (m + m * n) * sp)))
    ≡⟨ cong (λ y → sz + (n + (m + m * n + y))) (sym (*-distribʳ-+ sp n (m + m * n)) ) ⟩
      sz + (n + (m + m * n + (n + (m + m * n)) * sp))
    ≡⟨ cong (λ y → sz + y) (sym (+-assoc n (m + m * n) ((n + (m + m * n)) * sp))) ⟩
      refl

  lem₂ : (n m : ℕ) → suc n * suc m ≡ suc (n + m * suc n)
  lem₂ n m =
    begin
      suc (m + (n + n * m))
    ≡⟨ cong (λ y → suc (m + (n + y))) (*-comm n m) ⟩
      suc (m + (n + m * n))
    ≡⟨ cong suc (sym (+-assoc m n (m * n))) ⟩
      suc (m + n + m * n)
    ≡⟨ cong (λ y → suc (y + m * n)) (+-comm m n) ⟩
      suc (n + m + m * n)
    ≡⟨ cong suc (+-assoc n m (m * n)) ⟩
      refl

  lem₃ : {n sz sp : ℕ} → {t : Set} → (xs : Vec t (sz + n * suc sp)) →
         xs ≡ subst (Vec t) (lem₁ n zero sz sp) xs
  lem₃ {n} {sz} {sp} xs rewrite lem₁ n zero sz sp = refl

  postulate lem₄ : {n m : ℕ} → {t : Set} → (sz : ℕ) → (sp : ℕ) → (xs : Vec t (sz + n * (suc sp) + (suc m) * suc (n + sp + n * sp))) →
                   slide {n} sz sp (take (sz + n * suc sp) {(suc m) * suc (n + sp + n * sp)} xs) ++
                   slide {n + m * (suc n)} sz sp (subst (Vec t) (lem₁ n m sz sp) (drop (suc (n + sp + n * sp)) xs)) ≅
                   slide {n + (suc m) * (suc n)} sz sp (subst (Vec t) (lem₁ n (suc m) sz sp) xs)

  -- Adapted from paper https://www.lift-project.org/publications/2018/hagedorn18Stencils.pdf
  slideJoin : {n m : ℕ} → {t : Set} → (sz : ℕ) → (sp : ℕ) → (xs : Vec t (sz + n * (suc sp) + m * suc (n + sp + n * sp))) →
              join (map (λ (tile : Vec t (sz + n * (suc sp))) →
              slide {n} sz sp tile) (slide {m} (sz + n * (suc sp)) (n + sp + n * sp) xs)) ≅
              slide {n + m * (suc n)} sz sp (subst (Vec t) (lem₁ n m sz sp) xs)
  slideJoin {n} {zero} {t} sz sp xs =
    hbegin
      slide sz sp xs ++ []
    h≡⟨ ++-[] (slide sz sp xs) ⟩
      slide sz sp xs
    h≡⟨ cong (λ y → slide sz sp y) (lem₃ {n} {sz} {sp} xs) ⟩
      slide sz sp (subst (Vec t) (lem₁ n zero sz sp) xs)
    h∎
  slideJoin {n} {suc m} {t} sz sp xs = {!!}
  {-
    hbegin
      slide {n} sz sp (take (sz + n * suc sp) xs) ++
      join (map (slide {n} sz sp)
      (slide {m} (sz + n * suc sp) (n + sp + n * sp) (drop (suc (n + sp + n * sp)) xs)))
    ≅⟨ hcong′ (Vec (Vec t sz)) (lem₂ n m) (λ y → slide {n} sz sp (take (sz + n * suc sp) xs) ++ y)
       (slideJoin {n} {m} sz sp (drop (suc (n + sp + n * sp)) xs)) ⟩
      slide {n} sz sp (take (sz + n * suc sp) {(suc m) * suc (n + sp + n * sp)} xs) ++
      slide {n + m * (suc n)} sz sp (subst (Vec t) (lem₁ n m sz sp) (drop (suc (n + sp + n * sp)) xs))
    ≅⟨ lem₄ sz sp xs ⟩
      slide {n + (suc m) * (suc n)} sz sp (subst (Vec t) (lem₁ n (suc m) sz sp) xs)
    h∎
  -}

