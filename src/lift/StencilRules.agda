{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
module lift.StencilRules where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Nat.Properties using (*-distribʳ-+)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  import Relation.Binary.HeterogeneousEquality as Heq
  open Heq using (_≅_) renaming (sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
  open Heq.≅-Reasoning using (_≅⟨_⟩_) renaming (begin_ to hbegin_; _≡⟨⟩_ to _h≡⟨⟩_; _≡⟨_⟩_ to _h≡⟨_⟩_; _∎ to _h∎)
  open import lift.HeterogeneousHelpers using (hcong′)
  open import lift.Primitives using (map; id; take; drop; split;
    join; fill; head; tail; transpose; slide; reduceSeq; reduce; partRed)
  open import lift.Helpers

  {- Tiling -}
  -- u = sz + n * (suc p)
  -- suc v = (suc n) * (suc sp)
  -- sz - suc sp ≡ u - suc v
  postulate lem₁ : (n m sz sp : ℕ) →
                   sz + n * (suc sp) + m * suc (n + sp + n * sp) ≡ sz + (n + m * (suc n)) * (suc sp)
  postulate lem₂ : (n m : ℕ) → suc n * suc m ≡ suc (n + m * suc n)

  postulate lem₃ : {n sz sp : ℕ} → {t : Set} → (xs : Vec t (sz + n * suc sp)) →
                   subst (Vec t) (lem₁ n zero sz sp) xs ≡ xs

  slideJoin : {n m : ℕ} → {t : Set} → (sz : ℕ) → (sp : ℕ) → (xs : Vec t (sz + n * (suc sp) + m * suc (n + sp + n * sp))) →
              join (map (λ (tile : Vec t (sz + n * (suc sp))) →
              slide {n} sz sp tile) (slide {m} (sz + n * (suc sp)) (n + sp + n * sp) xs)) ≅
              slide {n + m * (suc n)} sz sp (subst (Vec t) (lem₁ n m sz sp) xs)
  slideJoin {n} {zero} {t} sz sp xs =
    hbegin
      slide sz sp xs ++ []
    h≡⟨ ++-[] (slide sz sp xs) ⟩
      slide sz sp xs
    h≡⟨ cong (λ y → slide sz sp y) (sym (lem₃ {n} {sz} {sp} xs)) ⟩
      slide sz sp (subst (Vec t) (lem₁ n zero sz sp) xs)
    h∎

  slideJoin {n} {suc m} {t} sz sp xs =
    hbegin
      slide {n} sz sp (take (sz + n * suc sp) xs) ++
      join (map (slide {n} sz sp)
      (slide {m} (sz + n * suc sp) (n + sp + n * sp) (drop (suc (n + sp + n * sp)) xs)))
    h≡⟨⟩
      {!!}

