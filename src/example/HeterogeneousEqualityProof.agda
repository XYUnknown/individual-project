{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
module example.HeterogeneousEqualityProof where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.Nat.Properties using (*-distribˡ-+; +-assoc; *-assoc)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  import Relation.Binary.HeterogeneousEquality as Heq
  open Heq using (_≅_) renaming (sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
  open Heq.≅-Reasoning using (_≅⟨_⟩_) renaming (begin_ to hbegin_; _≡⟨⟩_ to _h≡⟨⟩_; _≡⟨_⟩_ to _h≡⟨_⟩_; _∎ to _h∎)
  open import lift.Primitives using (map; join)
  open import lift.HeterogeneousHelpers using (hcong′)

  -- lemmas
  -- Both of them are difficult to be formed with propositional equality
  -- since the size of resulting vectors on LHS and RHS has sizes provably equal but not identitcal
  -- Agda thinks they are defferent Types
  ++-assoc : {n m o : ℕ} → {t : Set} → (xs : Vec t n) → (ys : Vec t m) → (zs : Vec t o) →
             (xs ++ ys) ++ zs ≅ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = Heq.refl
  ++-assoc {suc n} {m} {o} {t} (x ∷ xs) ys zs = hcong′ (Vec t) (+-assoc n m o) (λ l → x ∷ l) (++-assoc xs ys zs)

  join-++ : {n m o : ℕ} → {t : Set} → (xs₁ : Vec (Vec t o) n) → (xs₂ : Vec (Vec t o) m) →
            join (xs₁ ++ xs₂) ≅ join xs₁ ++ join xs₂
  join-++ [] xs₂ = Heq.refl
  join-++ {suc n} {m} {o} {t} (xs ∷ xs₁) xs₂ =
    hbegin
      xs ++ join (xs₁ ++ xs₂)
    ≅⟨ hcong′ (Vec t) (*-distribˡ-+ o n m) (λ y → xs ++ y) (join-++ xs₁ xs₂) ⟩
      xs ++ join xs₁ ++ join xs₂
    ≅⟨ hsym (++-assoc xs (join xs₁) (join xs₂)) ⟩
      (xs ++ join xs₁) ++ join xs₂
    h∎

  -- We would like to prove join is commutative
  -- But using propositional equality is not about to form the equation
  -- Uncomment to see the error
  {-
  joinJoinP : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
              join (join xsss) ≡ join (map join xsss)
  joinJoinP = ?
  -}
  -- We have the error message:
  {-
  o * m != o of type ℕ
  when checking that the inferred type of an application
  Vec t (o * m * n)
  matches the expected type
  Vec t (o * (m * n))
  -}

  -- So apparently Agda thinks LHS and RHS are different types
  -- thus refuse to form propositional equality between them
  -- In this case we need to form equality between different types
  -- hence we consider using heterogeneous equality

  joinJoinH : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
              join (join xsss) ≅ join (map join xsss)
  joinJoinH [] = Heq.refl
  joinJoinH {suc n} {m} {o} {t} (xss ∷ xsss) =
    hbegin
      join (xss ++ join xsss)
    ≅⟨ join-++ xss (join xsss) ⟩ -- using lemma join-++
      join xss ++ join (join xsss)
    ≅⟨ hcong′ (Vec t) (sym (*-assoc o m n)) (λ y → join xss ++ y) (joinJoinH xsss) ⟩
      join xss ++ join (map join xsss)
    h∎
