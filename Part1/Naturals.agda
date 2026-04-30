module Part1.Naturals where

data ℕ : Set where
    zero : ℕ 
    suc  : ℕ → ℕ

one : ℕ
one = suc zero

two : ℕ
two = suc one 

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

_+_ : ℕ → ℕ → ℕ 
zero + n    = n 
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5 
_ = refl

{- Have to figure out how this chain of equations works in Agda 2.8.0 -}
    -- begin
    --   2 + 3 
    -- ≡⟨⟩
    --   (suc (suc zero)) + (suc (suc (suc zero)))
    -- ≡〈〉
    --     ?
    -- ∎
-- _ : 1 + 1 ≡ 2
-- _ = 
--     begin
--         1 + 1 
--         ≡〈 refl 〉
--         2 
--         ∎

-- +-assoc : (m + n) + k ≡ m + (n + k)
-- +-assoc = ?

_*_ : ℕ → ℕ → ℕ
zero * n = zero 
(suc m) * n = n + (m * n)

_ : 5 * 10 ≡ 50
_ = refl

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81 
_ = refl

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ n = n 
(suc m) ∸ (suc n) = m ∸ n 

infixl 6 _+_ _∸_ 
infixl 7 _*_ 
infixl 8 _^_ 

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
-- {-# BUILTIN NATMINUS _∸_ #-}
-- {-# BUILTIN NATEXP _^_ #-}

{- EXERCISE Binary numbers -}

data Bin : Set where 
    # : Bin
    _O : Bin → Bin
    _I : Bin → Bin 

Binsuc : Bin → Bin 
Binsuc # = # I
Binsuc (bits O) = bits I
Binsuc (bits I) = (Binsuc bits) O

-- Conversions

-- Natural number to Binary repr.
Num2Bin : ℕ → Bin 
Num2Bin 0 = # O
Num2Bin (suc n) = Binsuc (Num2Bin n)

-- Binary number to natural (n = Sum_i (x_i * 2^i))
Bin2NumHelper : Bin → ℕ → ℕ
Bin2NumHelper # n = 0
Bin2NumHelper (bits O) n = Bin2NumHelper bits (n + 1)
Bin2NumHelper (bits I) n = (2 ^ n) + (Bin2NumHelper bits (n + 1))

-- Omitting helper function
Bin2Num : Bin → ℕ
Bin2Num = λ (b : Bin) → Bin2NumHelper b 0

-- Proofs 

_ : { n : ℕ } →  Bin2Num (Num2Bin n) ≡ n
_ = {!   !} 

