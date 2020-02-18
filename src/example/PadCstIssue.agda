{-# OPTIONS --rewriting --prop #-}
module example.PadCstIssue where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; _≢_; refl; cong; sym; subst)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.Nat.Properties using (*-comm; *-distribˡ-+; *-distribʳ-+; *-identityʳ; +-comm; +-assoc)
  open import Agda.Builtin.Equality.Rewrite

  +zero : {m : ℕ} → m + zero ≡ m
  +zero {zero}  = refl
  +zero {suc m} = cong suc +zero

  +suc : {m n : ℕ} → m + (suc n) ≡ suc (m + n)
  +suc {m} {n} =
    begin
      m + (1 + n)
    ≡⟨ sym (+-assoc m 1 n) ⟩
      m + 1 + n
    ≡⟨ cong (_+ n) (+-comm m 1) ⟩
      refl

  {-# REWRITE +zero +suc #-}

  padCst : {n : ℕ} → (l r : ℕ) → {t : Set} → t → Vec t n → Vec t (l + n + r)
  padCst zero zero x xs = xs
  padCst zero (suc r) x xs = padCst zero r x (xs ++ [ x ])
  padCst (suc l) zero x xs = padCst l zero x ([ x ] ++ xs)
  {- the bug occurs here
     Agda v2.6.1 fixes this issue
  -}
  padCst (suc l) (suc r) x xs = padCst l r x ([ x ] ++ xs ++ [ x ])
