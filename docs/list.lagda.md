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
* padCst₂
  ```agda
  padCst₂ : {n m : ℕ} → (l r : ℕ) → {t : Set} → t → Vec t n → Vec (Vec t n) m → Vec (Vec t (l + n + r)) (l + m + r)
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
              (f ∘ map id) xs ≡ f xs
  ```
  ```agda
  identity₂ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n → Vec t n) → (xs : Vec s n) →
              (map id ∘ f) xs ≡ f xs
  ```
  ```agda
  identity₃ : {n m : ℕ} → {t : Set} → (xss : Vec (Vec t m) n) →
              transpose (transpose xss) ≡ xss
  ```

* Fusion Rules
  ```adga
  fusion₁ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} → (f : t → r) → (g : s → t) → (xs : Vec s n) →
            (map f ∘ map g) xs ≡ map (f ∘ g) xs
  ```
  ```agda
  fusion₂ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} →
            (f : s → t) → (bf : t → r → r) → (init : r) → (xs : Vec s n) →
            reduceSeq (λ (a : s) (b : r) → (bf (f a) b)) init xs ≡ (reduceSeq bf init ∘ map f) xs
  ```

* Simplification Rules
  ```adga
  simplification₁ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (n * m)) →
                    (join ∘ split n {m}) xs ≡ xs
  ```
  ```agda
  simplification₂ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec (Vec t n) m) →
                    (split n ∘ join) xs ≡ xs
  ```

* Split-join Rule
  ```agda
  splitJoin : {m : ℕ} → {s : Set} → {t : Set} →
              (n : ℕ) → (f : s → t) → (xs : Vec s (n * m)) →
              (join ∘ map (map f) ∘ split n {m}) xs ≡ map f xs
  ```

* Reduction Rule
  ```agda
  reduction : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (suc m * n)) →
              (reduce M ∘ partRed n {m} M) xs ≡ reduce M xs
  ```

* Partial Reduction Rules
  ```adga
  partialReduction₁ : {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t n)  →
                      partRed n M xs ≡ [ reduce M xs ]
  ```
  ```agda
  partialReduction₂ : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (n * suc m)) →
                      (join ∘ map (partRed n {zero} M) ∘ split n {suc m}) xs ≡ partRed n {m} M xs
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
                           map (map f) (transpose xss) ≡ transpose (map (map f) xss)
  ```
  ```agda
  transposeBeforeMapMapF : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s m) n) →
                           transpose (map (map f) xss) ≡ map (map f) (transpose xss)
  ```

* Split
  ```agda
  splitBeforeMapMapF : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n * m)) →
                       map (map f) (split n {m} xs) ≡ split n {m} (map f xs)
  ```
  
  ```agda
  mapFBeforeSplit : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n * m)) →
                    split n {m} (map f xs) ≡ map (map f) (split n {m} xs)
  ```

* Slide
  ```agda
  slideBeforeMapMapF : {n : ℕ} → (sz : ℕ) → (sp : ℕ) → {s t : Set} →
                       (f : s → t) → (xs : Vec s (sz + n * (suc sp))) →
                       map (map f) (slide {n} sz sp xs) ≡ slide {n} sz sp (map f xs)
  ```

  ```agda
  mapFBeforeSlide : {n : ℕ} → (sz : ℕ) → (sp : ℕ) → {s t : Set} →
                    (f : s → t) → (xs : Vec s (sz + n * (suc sp))) →
                    slide {n} sz sp (map f xs) ≡ map (map f) (slide {n} sz sp xs)
  ```

* Join
  ```agda
  joinBeforeMapF : {s : Set} → {t : Set} → {m n : ℕ} →
                   (f : s → t) → (xs : Vec (Vec s n) m) →
                   map f (join xs) ≡ join (map (map f) xs)
  ```

  ```agda
  mapMapFBeforeJoin : {s : Set} → {t : Set} → {m n : ℕ} →
                      (f : s → t) → (xs : Vec (Vec s n) m) →
                      join (map (map f) xs) ≡ map f (join xs)
  ```

* Join + Transpose
  ```agda
  joinBeforeTranspose : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                        transpose (join xsss) ≡ map join (transpose (map transpose xsss))
  ```

  ```agda
  transposeBeforeMapJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                           map join (transpose xsss) ≡ transpose (join (map transpose xsss))
  ```

  ```agda
  mapTransposeBeforeJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                           join (map transpose xsss) ≡ transpose (map join (transpose xsss))
  ```

  ```agda
  mapJoinBeforeTranspose : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                           transpose (map join xsss) ≡ join (map transpose (transpose xsss))
  ```

* Join + Join (Proven using heterogeneous equality)
  ```agda
  joinBeforeJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                   join (join xsss) ≅ join (map join xsss)
  ```
  ```agda
  mapJoinBeforeJoin : {n m o : ℕ} → {t : Set} → (xsss : Vec (Vec (Vec t o) m) n) →
                      join (map join xsss) ≅ join (join xsss)
  ```

* Transpose + Split
  ```agda
  transposeBeforeSplit : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (n * m)) q) →
                         split n {m} (transpose xsss) ≡
                         map transpose (transpose (map (split n {m}) xsss))
  ```
  ```agda
  mapSplitBeforeTranspose : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) (n * m)) q) →
                            transpose (map (split n {m}) xsss) ≡ map transpose (split n (transpose xsss))
  ```
  ```agda
  transposeBeforeMapSplit : {m p q : ℕ} → {t : Set} → (n : ℕ) → (xsss : Vec (Vec (Vec t p) q) (n * m)) →
                            map (split n {m}) (transpose xsss) ≡ transpose (map transpose (split n xsss))
  ```

* Transpose + Slide
  ```agda
  transposeBeforeSlide : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (sz + n * (suc sp))) m) →
                         slide {n} sz sp (transpose xsss) ≡
                         map transpose (transpose (map (slide {n} sz sp) xsss))
  ```
  ```agda
  mapSlideBeforeTranspose : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) (sz + n * (suc sp))) m) →
                            transpose (map (slide {n} sz sp) xsss) ≡ map transpose (slide sz sp (transpose xsss))
  ```
  ```agda
  transposeBeforeMapSlide : {n m o : ℕ} → {t : Set} → (sz sp : ℕ) → (xsss : Vec (Vec (Vec t o) m) (sz + n * (suc sp))) →
                            map (slide {n} sz sp) (transpose xsss) ≡ transpose (map transpose (slide sz sp xsss))
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
              join (map (λ (tile : Vec t (sz + n * (suc sp))) →
              slide {n} sz sp tile) (slide {m} (sz + n * (suc sp)) (n + sp + n * sp) xs)) ≅
              slide {n + m * (suc n)} sz sp (subst (Vec t) (lem₁ n m sz sp) xs)
  ```
