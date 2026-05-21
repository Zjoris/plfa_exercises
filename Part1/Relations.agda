module Part1.Relations where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

data _≤_ : ℕ → ℕ → Set where 
    0≤n : {n : ℕ} → zero ≤ n 
    s≤s : {n m : ℕ} → n ≤ m → (suc n) ≤ (suc m)

_ : 2 ≤ 3 
_ = s≤s (s≤s 0≤n)

_ : 2 ≤ 3 
_ = s≤s {1} {2} (s≤s {n = 0} {m = 1} (0≤n {n = 1}))

+-idᴿ' : {m : ℕ} → m + zero ≡ m 
+-idᴿ' = +-identityʳ _ 

infix 4 _≤_ 

s≤s-inv : {n m : ℕ} → suc n ≤ suc m → n ≤ m 
s≤s-inv (s≤s n≤m) = n≤m

z≤n-inv : {n : ℕ} → n ≤ zero → n ≡ zero 
z≤n-inv 0≤n = refl

---- Properties ----- 

≤-rflx : {n : ℕ} → n ≤ n 
≤-rflx {zero} = 0≤n
≤-rflx {suc n} = s≤s ≤-rflx

≤-trans : {n m k : ℕ} → n ≤ m → m ≤ k → n ≤ k
≤-trans 0≤n _ = 0≤n
≤-trans (s≤s n≤m) (s≤s m≤k) = s≤s (≤-trans n≤m m≤k) 

≤-antisym : {n m : ℕ} → n ≤ m → m ≤ n → m ≡ n 
≤-antisym 0≤n m≤n = z≤n-inv m≤n
≤-antisym (s≤s n≤m) (s≤s m≤n) = cong suc (≤-antisym n≤m m≤n)

data _U_ (A : Set) (B : Set) : Set where 
    inl : A → A U B
    inr : B → A U B 

≤-total : {n m : ℕ} → (n ≤ m) U (m ≤ n) 
≤-total {zero} = inl 0≤n
≤-total {suc n} {zero} = inr 0≤n
≤-total {suc n} {suc m} with ≤-total {n} {m}
...                        | inl n≤m = inl (s≤s n≤m)
...                        | inr m≤n = inr (s≤s m≤n)

≤-total' : {n m : ℕ} → (n ≤ m) U (m ≤ n) 
≤-total' {zero} = inl 0≤n
≤-total' {suc n} {zero} = inr 0≤n
≤-total' {suc n} {suc m} = total-helper (≤-total {n} {m})
    where 
    total-helper : {n m : ℕ} → (m ≤ n) U (n ≤ m) → (suc m ≤ suc n) U (suc n ≤ suc m)
    total-helper (inl x) = inl (s≤s x)
    total-helper (inr x) = inr (s≤s x)

pred : ℕ → ℕ 
pred zero = zero 
pred (suc n) = n

-- -- _∸_ : ℕ → ℕ → ℕ
-- -- zero ∸ n = zero 
-- -- m ∸ zero = m 
-- -- suc m ∸ suc n = m ∸ n 

=→≤ : {n m : ℕ} → n ≡ m → n ≤ m 
=→≤ {zero} n=m = 0≤n
=→≤ {suc n} {suc m} n=m = s≤s (=→≤ (cong (pred) n=m))

-- +-suc : ∀ (n m : ℕ) → suc (n + m) ≡ m + suc n
-- +-suc n zero = cong suc (+-identityʳ n) 
-- +-suc n (suc m) = {!   !}
-- -- +-suc zero m = refl
-- -- +-suc (suc n) m =  cong suc (+-suc n m)

-- _ : {n m : ℕ} → suc n ≤ suc (n + m) → suc n ≤ suc n + m 
-- _ = λ x → ≤-trans x (=→≤ (refl))

m≤m+n : ∀ {n m : ℕ} → n ≤ (n + m) 
m≤m+n {zero} = 0≤n
m≤m+n {suc n} {m} = ≤-trans (s≤s m≤m+n) (≤-rflx)

+-≤-mono : {n m k l : ℕ} → n ≤ m → k ≤ l → (n + k) ≤ (m + l) 
+-≤-mono {m = m} {l = l} 0≤n k≤l = ≤-trans k≤l (≤-trans m≤m+n (=→≤ (+-comm l m)))
+-≤-mono (s≤s n≤m) k≤l = s≤s (+-≤-mono n≤m k≤l)

*-≤-monoᴿ : {n m k : ℕ} → n ≤ m → k * n ≤ k * m 
*-≤-monoᴿ {k = zero} n≤m = 0≤n
*-≤-monoᴿ {k = suc k} n≤m = +-≤-mono n≤m (*-≤-monoᴿ {k = k} n≤m)

n*0=0 : {n : ℕ} → n * zero ≤ zero 
n*0=0 {zero} = 0≤n
n*0=0 {suc n} = n*0=0 {n}

*-suc : {n m : ℕ} → n * suc m ≡ n + n * m 
*-suc {zero} = refl
*-suc {suc n} = cong suc {!   !} 

*-≤-monoᴸ : {n m k : ℕ} → n ≤ m → n * k ≤ m * k 
*-≤-monoᴸ {k = zero} n≤m = ≤-trans n*0=0 0≤n 
*-≤-monoᴸ {k = suc k} n≤m = {!   !} 


*-≤-mono : {n m k l : ℕ} → n ≤ m → k ≤ l → (n * k) ≤ (m * l)
*-≤-mono {m = m} n≤m k≤l = ≤-trans ({!   !}) (*-≤-monoᴿ {k = m} k≤l)