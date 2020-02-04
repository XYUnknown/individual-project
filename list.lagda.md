# Defined Primitives and Proven Rewrite Rules

## Primitives
### Module
Source: `/individual-project/src/lift/Primitives.adga`
```agda
module lift.Primitives where
  ...
```
### definied primitives
* id
  ```agda
  id : {T : Set} → T → T
  ```
* map
  ```agda
  map : {n : ℕ} → {s : Set} → {t : Set} → (s → t) → Vec s n → Vec t n
  ```
* take
  ```agda
  take : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t n
  ```
* drop
  ```agda
  drop : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t m
  ```
* split
  ```agda
  split : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n * m) → Vec (Vec t n) m
  ```
* join
  ```agda
  join : {n m : ℕ} → {t : Set} → Vec (Vec t n) m → Vec t (n * m)
  ```
* slide
  ```agda
  slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {t : Set} → Vec t (sz + n * (suc sp)) → Vec (Vec t sz) (suc n)
  ```
* reduceSeq
  ```agda
  reduceSeq : {n : ℕ} → {s t : Set} → (s → t → t) → t → Vec s n → t
  ```
* reduce
  ```agda
  reduce : {n : ℕ} → {t : Set} → (M : CommAssocMonoid t) → Vec t n → t
  ```
* partRed
  ```agda
  partRed : (n : ℕ) → {m : ℕ} → {t : Set} → (M : CommAssocMonoid t) → Vec t (suc m * n) → Vec t (suc m)
  ```
* zip
  ```agda
  zip : {n : ℕ} → {s : Set} → {t : Set} → Vec s n → Vec t n → Vec (s × t) n
  ```
* unzip
  ```agda
  unzip : ((x , y) ∷ xs) = Prod.zip _∷_ _∷_ (x , y) (unzip xs)
  ```
* transpose
  ```agda
  transpose : {n m : ℕ} → {t : Set} → Vec (Vec t m) n → Vec (Vec t n) m
  ```
* padCst
  ```agda
  padCst : {n : ℕ} → (l r : ℕ) → {t : Set} → t → Vec t n → Vec t (l + n + r)
  ```
* map₂
  ```agda
  map₂ : {n m : ℕ} → {s t : Set} → (s → t) → Vec (Vec s n) m → Vec (Vec t n) m
  ```
* slide₂
  ```agda
  slide₂ : {n m : ℕ} → (sz : ℕ) → (sp : ℕ)→ {t : Set} → Vec (Vec t (sz + n * (suc sp))) (sz + m * (suc sp)) →
           Vec (Vec (Vec (Vec t sz) sz) (suc n)) (suc m)
  ```

## Algorithmic Rewrite Rules
### Module
Source: `/individual-project/src/lift/AlgorithmicRules.adga`
```agda
module lift.AlgorithmicRules where
  ...
```
### Proven Rewrite Rules
* Identity Rules
  ```adga
  identity₁ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n → Vec t n) → (xs : Vec s n) →
              (f ∘ Pm.map Pm.id) xs ≡ f xs
  ```
  ```agda
  identity₂ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n → Vec t n) → (xs : Vec s n) →
              (Pm.map Pm.id ∘ f) xs ≡ f xs
  ```
  ```agda
  identity₃ : {n m : ℕ} → {t : Set} → (xss : Vec (Vec t m) n) →
              Pm.transpose (Pm.transpose xss) ≡ xss
  ```

* Fusion Rules
  ```adga
  fusion₁ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} → (f : t → r) → (g : s → t) → (xs : Vec s n) →
            (Pm.map f ∘ Pm.map g) xs ≡ Pm.map (f ∘ g) xs
  ```
  ```agda
  fusion₂ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} →
            (f : s → t) → (bf : t → r → r) → (init : r) → (xs : Vec s n) →
            Pm.reduceSeq (λ (a : s) (b : r) → (bf (f a) b)) init xs ≡ (Pm.reduceSeq bf init ∘ Pm.map f) xs
  ```

* Simplification Rules
  ```adga
  simplification₁ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (n * m)) →
                    (Pm.join ∘ Pm.split n {m}) xs ≡ xs
  ```
  ```agda
  simplification₂ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec (Vec t n) m) →
                    (Pm.split n ∘ Pm.join) xs ≡ xs
  ```

* Split-join Rule
  ```agda
  splitJoin : {m : ℕ} → {s : Set} → {t : Set} →
              (n : ℕ) → (f : s → t) → (xs : Vec s (n * m)) →
              (Pm.join ∘ Pm.map (Pm.map f) ∘ Pm.split n {m}) xs ≡ Pm.map f xs
  ```

* Reduction Rule
  ```agda
  reduction : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (suc m * n)) →
              (Pm.reduce M ∘ Pm.partRed n {m} M) xs ≡ Pm.reduce M xs
  ```

* Partial Reduction Rules
  ```adga
  partialReduction₁ : {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t n)  →
                      Pm.partRed n M xs ≡ [ Pm.reduce M xs ]
  ```
  ```agda
  partialReduction₂ : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (n * suc m)) →
                      (Pm.join ∘ Pm.map (Pm.partRed n {zero} M) ∘ Pm.split n {suc m}) xs ≡ Pm.partRed n {m} M xs
  ```
## Movement Rewrite Rules
### Module
Source: `/individual-project/src/lift/MovementRules.adga`
```agda
module lift.MovementRules where
```

### Proven Rewrite Rules
* Transpose
  ```agda
  mapMapFBeforeTranspose : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s m) n) →
                           Pm.map (Pm.map f) (Pm.transpose xss) ≡ Pm.transpose (Pm.map (Pm.map f) xss)
  ```
  ```agda
  transposeBeforeMapMapF : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s m) n) →
                           Pm.transpose (Pm.map (Pm.map f) xss) ≡ Pm.map (Pm.map f) (Pm.transpose xss)
  ```

* Slide
  ```agda
  slideBeforeMapMapF : {n : ℕ} → (sz : ℕ) → (sp : ℕ) → {s t : Set} →
                       (f : s → t) → (xs : Vec s (sz + n * (suc sp))) →
                       Pm.map (Pm.map f) (Pm.slide {n} sz sp xs) ≡ Pm.slide {n} sz sp (Pm.map f xs)
  ```

  ```agda
  mapFBeforeSlide : {n : ℕ} → (sz : ℕ) → (sp : ℕ) → {s t : Set} →
                    (f : s → t) → (xs : Vec s (sz + n * (suc sp))) →
                    Pm.slide {n} sz sp (Pm.map f xs) ≡ Pm.map (Pm.map f) (Pm.slide {n} sz sp xs)
  ```

* Join
  ```agda
  joinBeforeMapF : {s : Set} → {t : Set} → {m n : ℕ} →
                   (f : s → t) → (xs : Vec (Vec s n) m) →
                   Pm.map f (Pm.join xs) ≡ Pm.join (Pm.map (Pm.map f) xs)
  ```

  ```agda
  mapMapFBeforeJoin : {s : Set} → {t : Set} → {m n : ℕ} →
                      (f : s → t) → (xs : Vec (Vec s n) m) →
                      Pm.join (Pm.map (Pm.map f) xs) ≡ Pm.map f (Pm.join xs)
  ```

* Join + Transpose
  ```agda
  joinBeforeTranspose : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                        Pm.transpose (Pm.join xsss) ≡ Pm.map Pm.join (Pm.transpose (Pm.map Pm.transpose xsss))
  ```

  ```agda
  transposeBeforeMapJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                           Pm.map Pm.join (Pm.transpose xsss) ≡ Pm.transpose (Pm.join (Pm.map Pm.transpose xsss))
  ```

  ```agda
  mapTransposeBeforeJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                           Pm.join (Pm.map Pm.transpose xsss) ≡ Pm.transpose (Pm.map Pm.join (Pm.transpose xsss))
  ```

  ```agda
  mapJoinBeforeTranspose : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                           Pm.transpose (Pm.map Pm.join xsss) ≡ Pm.join (Pm.map Pm.transpose (Pm.transpose xsss))
  ```

* Join + Join (Proven using heterogeneous equality)
  ```agda
  joinBeforeJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                   Pm.join (Pm.join xsss) ≅ Pm.join (Pm.map Pm.join xsss)
  ```

* Transpose + Split (_WIP_)
  ```agda
  transposeBeforeSplit : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (n * m)) q) →
                       Pm.split n {m} (Pm.transpose xsss) ≡
                       Pm.map Pm.transpose (Pm.transpose (Pm.map (Pm.split n {m}) xsss))
  ```

* Transpose + Slide (_WIP_)
  ```agda
  transposeBeforeSlide : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (sz + n * (suc sp))) m) →
                         Pm.slide {n} sz sp (Pm.transpose xsss) ≡
                         Pm.map Pm.transpose (Pm.transpose (Pm.map (Pm.slide {n} sz sp) xsss))
  ```

## Stencil Rewrite Rules
### Module
Source: `/individual-project/src/lift/StencilRules.adga`
```agda
module lift.StencilRules where
```

### Proven Rewrite Rules
* Tiling (_WIP_)
  ```agda
  slideJoin : {n m : ℕ} → {t : Set} → (sz : ℕ) → (sp : ℕ) → (xs : Vec t (sz + n * (suc sp) + m * suc (n + sp + n * sp))) →
              Pm.join (Pm.map (λ (tile : Vec t (sz + n * (suc sp))) →
              Pm.slide {n} sz sp tile) (Pm.slide {m} (sz + n * (suc sp)) (n + sp + n * sp) xs)) ≅
              Pm.slide {n + m * (suc n)} sz sp (subst (Vec t) (lem₁ n m sz sp) xs)
  ```