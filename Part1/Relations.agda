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

=→≤ : {n m : ℕ} → n ≡ m → n ≤ m 
=→≤ {zero} n=m = 0≤n
=→≤ {suc n} {suc m} n=m = s≤s (=→≤ (cong (pred) n=m))

m≤m+n : ∀ {n m : ℕ} → n ≤ (n + m) 
m≤m+n {zero} = 0≤n
m≤m+n {suc n} {m} = ≤-trans (s≤s m≤m+n) (≤-rflx)

+-≤-mono : {n m k l : ℕ} → n ≤ m → k ≤ l → (n + k) ≤ (m + l) 
+-≤-mono {m = m} {l = l} 0≤n k≤l = ≤-trans k≤l (≤-trans m≤m+n (=→≤ (+-comm l m)))
+-≤-mono (s≤s n≤m) k≤l = s≤s (+-≤-mono n≤m k≤l)

+-≤-monoᴿ : {n m k : ℕ} → n ≤ m → k + n ≤ k + m 
+-≤-monoᴿ {k = zero} n≤m = n≤m
+-≤-monoᴿ {k = suc k} n≤m = s≤s (+-≤-monoᴿ n≤m) 

+-≤-monoᴸ : {n m k : ℕ} → n ≤ m → n + k ≤ m + k 
+-≤-monoᴸ {n} {m} {k} n≤m rewrite (+-comm n k) | (+-comm m k) = +-≤-monoᴿ n≤m

+-≤-mono' : {n m k l : ℕ} → n ≤ m → k ≤ l → n + k ≤ m + l 
+-≤-mono' n≤m k≤l = ≤-trans (+-≤-monoᴿ k≤l) (+-≤-monoᴸ n≤m)

*-≤-monoᴿ : {n m k : ℕ} → n ≤ m → k * n ≤ k * m 
*-≤-monoᴿ {k = zero} n≤m = 0≤n
*-≤-monoᴿ {k = suc k} n≤m = +-≤-mono n≤m (*-≤-monoᴿ {k = k} n≤m)

*-≤-monoᴸ : {n m k : ℕ} → n ≤ m → n * k ≤ m * k 
*-≤-monoᴸ {n} {m} {k} n≤m rewrite (*-comm n k) | (*-comm m k) = *-≤-monoᴿ {k = k} n≤m

*-≤-mono : {n m k l : ℕ} → n ≤ m → k ≤ l → (n * k) ≤ (m * l)
*-≤-mono {m = m} n≤m k≤l = ≤-trans (*-≤-monoᴸ n≤m) (*-≤-monoᴿ {k = m} k≤l)

-- STRICT INEQUALITY

infix 4 _<_

data _<_ : ℕ → ℕ → Set where 
    0<sn : {n : ℕ} → zero < (suc n)
    s<s  : {n m : ℕ} → n < m → suc n < suc m

<-trans : {n m k : ℕ} → n < m → m < k → n < k 
<-trans 0<sn (s<s m<k) = 0<sn
<-trans (s<s n<m) (s<s m<k) = s<s (<-trans n<m m<k)

_>_ : ℕ → ℕ → Set 
n > m = m < n

-- pattern _>_ n m = n < m

<-trichotomy-weak : {n m : ℕ} → (n < m) U ((n ≡ m) U (n > m)) 
<-trichotomy-weak {zero} {zero} = inr (inl refl)
<-trichotomy-weak {zero} {suc m} = inl 0<sn
<-trichotomy-weak {suc n} {zero} = inr (inr 0<sn)
<-trichotomy-weak {suc n} {suc m} with <-trichotomy-weak {n} {m}
...                                    | inl n<m = inl (s<s n<m) 
...                                    | inr (inl n=m) = inr (inl (cong suc n=m))
...                                    | inr (inr n>m) = inr (inr (s<s n>m))

+-<-mono : {n m k l : ℕ} → n < m → k < l → n + k < m + l 
+-<-mono  n<m k<l = <-trans (+-<-monoᴸ n<m) (+-<-monoᴿ k<l)
    where 
    +-<-monoᴿ : {n m k : ℕ} → n < m → k + n < k + m 
    +-<-monoᴿ {k = zero} n<m = n<m
    +-<-monoᴿ {k = suc k} n<m = s<s (+-<-monoᴿ n<m) 
    +-<-monoᴸ : {n m k : ℕ} → n < m → n + k < m + k 
    +-<-monoᴸ {n} {m} {k} rewrite (+-comm n k) | (+-comm m k) = +-<-monoᴿ


≤→< : {n m : ℕ} → suc n ≤ m → n < m 
≤→< {zero} (s≤s sn≤m) = 0<sn
≤→< {suc n} (s≤s sn≤m) = s<s (≤→< sn≤m)

<→≤ : {n m : ℕ} → n < m → suc n ≤ m 
<→≤ {zero} 0<sn = s≤s 0≤n
<→≤ {suc n} (s<s n<m) = s≤s (<→≤ n<m)

<→≤' : {n m : ℕ} → n < m → n ≤ m 
<→≤' {zero} 0<sn = 0≤n
<→≤' {suc n} (s<s n<m) = s≤s (<→≤' n<m)

<-trans' : {n m k : ℕ} → n < m → m < k → n < k 
<-trans' {m = m} n<m m<k = ≤→< (≤-trans (<→≤ n<m) (<→≤' m<k) )

data even : ℕ → Set 
data odd  : ℕ → Set

data even where 
    zero : even zero 
    suc : {n : ℕ} → odd n → even (suc n) 

data odd where 
    suc : {n : ℕ} → even n → odd (suc n)

ev+ev=ev : {n m : ℕ} → even n → even m → even (n + m)
ev+ev=ev zero ev-m = ev-m
ev+ev=ev (suc (suc x)) ev-m = suc (suc (ev+ev=ev x ev-m))

od+ev=od : {n m : ℕ} → odd n → even m → odd (n + m)
od+ev=od (suc zero) ev-m = suc ev-m
od+ev=od (suc (suc x)) ev-m = suc (suc (od+ev=od x ev-m))

od+od=ev : {n m : ℕ} → odd n → odd m → even (n + m)
od+od=ev (suc zero) od-m = suc od-m
od+od=ev (suc (suc x)) od-m = suc (suc (od+od=ev x od-m))

data Bin : Set where 
    ⟨⟩ : Bin 
    _O : Bin → Bin 
    _I : Bin → Bin 

data lead1 : Bin → Set where
    ⟨⟩I  : lead1 (⟨⟩ I)
    _O : {b : Bin} → (lead1 b) → (lead1 (b O))
    _I : {b : Bin} → (lead1 b) → (lead1 (b I))

data BinCan : Bin → Set where 
    ⟨⟩O : BinCan (⟨⟩ O)
    L1 : {b : Bin} → (lead1 b) → (BinCan b)

-- _ : BinCan b → BinCan (inc B)
