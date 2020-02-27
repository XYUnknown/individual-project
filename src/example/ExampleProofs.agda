{-# OPTIONS --rewriting --prop --confluence-check #-}
module example.ExampleProofs where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; _≢_; refl; cong; sym; subst)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  import Relation.Binary.HeterogeneousEquality as Heq
  open Heq using (_≅_) renaming (sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
  open Heq.≅-Reasoning using (_≅⟨_⟩_) renaming (begin_ to hbegin_; _≡⟨⟩_ to _h≡⟨⟩_; _≡⟨_⟩_ to _h≡⟨_⟩_; _∎ to _h∎)
  open import Level hiding (zero; suc)
  open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Data.Nat.Properties using (*-comm; *-distribˡ-+; *-distribʳ-+; *-identityʳ; +-comm; +-assoc; *-assoc)
  open import Function using (_∘_)
  open import Agda.Builtin.Equality.Rewrite

  {- rewrites -}
  *zero : {m : ℕ} → m * zero ≡ zero
  *zero {zero} = refl
  *zero {suc m} = *zero {m}

  *id : {m : ℕ} → m * 1 ≡ m
  *id {zero} = refl
  *id {suc m} = cong suc *id

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

  {-# REWRITE *zero +zero +suc #-}

  {- Primitives -}
  id : {T : Set} → T → T
  id t = t

  map : {n : ℕ} → {S : Set} → {T : Set} → (S → T) → Vec S n → Vec T n
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  take : (n : ℕ) → {m : ℕ} → {T : Set} → Vec T (n + m) → Vec T n
  take zero xs = []
  take (suc n) {m} (x ∷ xs) = x ∷ (take n {m} xs)

  drop : (n : ℕ) → {m : ℕ} → {T : Set} → Vec T (n + m) → Vec T m
  drop zero xs = xs
  drop (suc n) (x ∷ xs) = drop n xs

  split : (n : ℕ) → {m : ℕ} → {T : Set} → Vec T (m * n) → Vec (Vec T n) m
  split n {zero} xs = []
  split n {suc m} xs = take n {m * n} xs ∷ split n (drop n xs)

  join : {n m : ℕ} → {T : Set} → Vec (Vec T n) m → Vec T (m * n)
  join [] = []
  join (xs ∷ xs₁) = xs ++ join xs₁

  {- Rewrite Rules -}
  {- mapFusion -}
  mapFusion : {n : ℕ} → {S T R : Set} → (f : T → R) → (g : S → T) → (xs : Vec S n) →
              (map f ∘ map g) xs ≡ map (f ∘ g) xs
  mapFusion f g [] = refl
  mapFusion f g (x ∷ xs) =
    begin
      (f ∘ g) x ∷ (map f ∘ map g) xs
    ≡⟨ cong ((f ∘ g) x ∷_) (mapFusion f g xs) ⟩
      refl

  {- splitJoin -}
  -- lemmas
  map-take : (n : ℕ) → {m : ℕ} → {S T : Set} → (f : S → T) → (xs : Vec S (n + m)) →
             map f (take n {m} xs) ≡ (take n {m} (map f xs))
  map-take zero f xs = refl
  map-take (suc n) {m} f (x ∷ xs) =
    begin
      f x ∷ map f (take n {m} xs)
    ≡⟨ cong (f x ∷_) (map-take n {m} f xs) ⟩
      refl

  map-drop : (n : ℕ) → {m : ℕ} → {S T : Set} → (f : S → T) → (xs : Vec S (n + m)) →
             map f (drop n {m} xs) ≡ (drop n {m} (map f xs))
  map-drop zero f xs = refl
  map-drop (suc n) f (x ∷ xs) = map-drop n f xs

  map-split : (n : ℕ) → {m : ℕ} → {S T : Set} → (f : S → T) → (xs : Vec S (m * n)) →
              map (map f) (split n {m} xs) ≡ split n {m} (map f xs)
  map-split n {zero} f xs = refl
  map-split n {suc m} f xs =
    begin
      map f (take n xs) ∷ map (map f) (split n (drop n xs))
    ≡⟨ cong (map f (take n xs) ∷_) (map-split n f (drop n xs)) ⟩
      map f (take n xs) ∷ split n (map f (drop n xs))
    ≡⟨ cong (_∷ split n (map f (drop n xs))) (map-take n f xs) ⟩
      take n (map f xs) ∷ split n (map f (drop n xs))
    ≡⟨ cong (take n (map f xs) ∷_) (cong (split n) (map-drop n f xs)) ⟩
      take n (map f xs) ∷ split n (drop n (map f xs))
    ∎

  take-drop : (n : ℕ) → {m : ℕ} → {T : Set} → (xs : Vec T (n + m)) →
              take n {m} xs ++ drop n {m} xs ≡ xs
  take-drop zero xs = refl
  take-drop (suc n) (x ∷ xs) =
    begin
      x ∷ take n xs ++ drop n xs
    ≡⟨ cong (x ∷_) (take-drop n xs) ⟩
      refl

  simplification : (n : ℕ) → {m : ℕ} → {T : Set} → (xs : Vec T (m * n)) →
                   (join ∘ split n {m}) xs ≡ xs
  simplification n {zero} [] = refl
  simplification n {suc m} xs =
    begin
      take n xs ++ join (split n {m} (drop n xs))
    ≡⟨ cong (take n xs ++_) (simplification n {m} (drop n xs)) ⟩
      take n xs ++ drop n xs
    ≡⟨ take-drop n xs ⟩
      refl

  splitJoin : {m : ℕ} → {S T : Set} →
              (n : ℕ) → (f : S → T) → (xs : Vec S (m * n)) →
              (join ∘ map (map f) ∘ split n {m}) xs ≡ map f xs
  splitJoin {m} n f xs =
    begin
      join (map (map f) (split n {m} xs))
    ≡⟨ cong join (map-split n {m} f xs) ⟩
      join (split n {m} (map f xs))
    ≡⟨ simplification n {m} (map f xs) ⟩
      map f xs
    ∎

  {- Tiling -}
  -- update later, refer to StencilRules.agda

  {- Heterogeneous equality : join + join -}
  -- helper
  hcong′ : {α β γ : Level} {I : Set α} {i j : I}
           → (A : I → Set β) {B : {k : I} → A k → Set γ} {x : A i} {y : A j}
           → i ≡ j
           → (f : {k : I} → (x : A k) → B x)
           → x ≅ y
         → f x ≅ f y
  hcong′ _ refl _ Heq.refl = Heq.refl

  -- lemmas
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
    ≅⟨ hcong′ (Vec t) (*-distribʳ-+ o n m) (λ y → xs ++ y) (join-++ xs₁ xs₂) ⟩
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
    ≅⟨ hcong′ (Vec t) (*-assoc n m o) (λ y → join xss ++ y) (joinJoinH xsss) ⟩
      join xss ++ join (map join xsss)
    h∎
