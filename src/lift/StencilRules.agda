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

  {- Tiling -}
  -- u = sz + n * (suc sp)
  -- suc v = (suc n) * (suc sp)
  -- sz - suc sp ≡ u - suc v
  postulate lem₁ : (n m sz sp : ℕ) → sz + n * suc sp + m * suc (n + sp + n * sp) ≡ sz + (n + m * suc n) * suc sp

  lem₂ : {n sz sp : ℕ} → {t : Set} → (xs : Vec t (sz + n * suc sp)) → xs ≡ cast (lem₁ n zero sz sp) xs
  lem₂ {zero} {zero} {sp} [] = refl
  lem₂ {zero} {suc sz} {sp} (x ∷ xs) = cong (x ∷_) (lem₂ {zero} {sz} {sp} xs)
  lem₂ {suc n} {zero} {sp} (x ∷ xs) = cong (x ∷_) (lem₂ {n} {sp} {sp} xs)
  lem₂ {suc n} {suc sz} {sp} (x ∷ xs) = cong (x ∷_) (lem₂ {suc n} {sz} {sp} xs)

  postulate lem₃ : (n m sz sp : ℕ) →
                   suc (sz + n * suc sp + (n + sp + n * sp + m * suc (n + sp + n * sp))) ≡
                   suc (n + sp + n * sp + (sz + n * suc sp + m * suc (n + sp + n * sp)))

  lem₄ : {n m : ℕ} → {t : Set} → (sz sp : ℕ) →
         (xs : Vec t (suc (sz + n * suc sp + (n + sp + n * sp + m * suc (n + sp + n * sp))))) →
         slide {n} sz sp (take (sz + n * suc sp) {suc (n + sp + n * sp + m * suc (n + sp + n * sp))} xs) ++
         slide {n + m * suc n} sz sp (cast (lem₁ n m sz sp) (drop (suc (n + sp + n * sp)) (cast (lem₃ n m sz sp) xs))) ≡
         take sz {suc (sp + (n + (n + m * suc n)) * suc sp)} (cast (lem₁ n (suc m) sz sp) xs) ∷
         slide {n + (n + m * suc n)} sz sp (drop (suc sp) {sz + (n + (n + m * suc n)) * suc sp}
         (cast (slide-lem (n + (n + m * suc n)) sz sp ) (cast (lem₁ n (suc m) sz sp) xs)))
  lem₄ {zero} {m} sz sp xs = ?
  lem₄ {suc n} {m} sz sp xs = ?

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
