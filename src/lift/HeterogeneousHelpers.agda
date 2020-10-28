{-
see discussion in https://lists.chalmers.se/pipermail/agda/2014/007286.html
and https://stackoverflow.com/questions/24139810/stuck-on-proof-with-heterogeneous-equality
-}
module lift.HeterogeneousHelpers where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
  import Relation.Binary.HeterogeneousEquality as Heq
  open Heq using (_≅_) renaming (sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
  open Heq.≅-Reasoning using (_≅⟨_⟩_) renaming (begin_ to hbegin_; _≡⟨⟩_ to _h≡⟨⟩_; _≡⟨_⟩_ to _h≡⟨_⟩_; _∎ to _h∎)
  open import Level hiding (zero; suc)

  hcong′ : {α β γ : Level} {I : Set α} {i j : I}
           → (A : I → Set β) {B : {k : I} → A k → Set γ} {x : A i} {y : A j}
           → i ≡ j
           → (f : {k : I} → (x : A k) → B x)
           → x ≅ y
           → f x ≅ f y
  hcong′ _ refl _ Heq.refl = Heq.refl
