import Mathlib

open Finset
open scoped BigOperators

namespace ExpectedAp

/-- Indicator of a Boolean as a natural number (1 for `true`, 0 for `false`). -/
def indicator (b : Bool) : ℕ := if b then 1 else 0

/-- Indicator of a Boolean as a real number (1 for `true`, 0 for `false`). -/
noncomputable def indicatorR (b : Bool) : ℝ := if b then (1 : ℝ) else 0

variable {L : ℕ}

/-- Total number of relevant items in a length-`L` relevance vector. -/
def numRelevant (y : Fin L → Bool) : ℕ :=
  Finset.univ.sum (fun i : Fin L => indicator (y i))

/-- The indices `{ i : Fin L | i < k }` as a finite set, for accumulating counts up to rank `k` (1-indexed externally). -/
def indicesLT (L k : ℕ) : Finset (Fin L) :=
  (univ.filter (fun i : Fin L => i.1 < k))

/-- 1-indexed rank for a 0-indexed `Fin` index. -/
def rank1 (i : Fin L) : ℕ := i.1 + 1

/-- Cumulative number of relevant items among the first `k` ranks (treating ranks as 1..L), as a natural number. -/
def cumRelevant (y : Fin L → Bool) (k : ℕ) : ℕ :=
  (indicesLT L k).sum (fun i => indicator (y i))

/-- Precision at rank `k` (with `k = 1, 2, ..., L`). Defined as 0 when `k = 0` for convenience. -/
noncomputable def precAt (y : Fin L → Bool) (k : ℕ) : ℝ :=
  if 0 < k then (cumRelevant y k : ℝ) / (k : ℝ) else 0

/-- Average Precision (AP): average of `precAt` over relevant ranks. Uses `(i.val + 1)` as the 1-indexed rank of `i`. -/
noncomputable def ap (y : Fin L → Bool) : ℝ :=
  let M := numRelevant y
  if M = 0 then 0
  else (∑ i : Fin L, (if y i then precAt y (rank1 i) else 0)) / (M : ℝ)

/-- Harmonic number `H_L = ∑_{k=1}^L 1/k` as a real number. -/
noncomputable def harmonic (L : ℕ) : ℝ :=
  (Finset.range (L + 1)).sum (fun k => if 0 < k then (1 : ℝ) / (k : ℝ) else 0)

/-- Uniform average over ranks `1..L` (implemented via `Fin L` with 1-indexed conversion).
Defined as 0 when `L = 0`. -/
noncomputable def uniformAvgPrecAt (y : Fin L → Bool) : ℝ :=
  if _h : 0 < L then (∑ i : Fin L, precAt y (rank1 i)) / (L : ℝ) else 0

/-- Cumulative number of relevant items among the first `k` ranks under a permutation `π`.
`π` is interpreted as mapping a rank index to the item at that rank. -/
def cumRelevantPerm (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) (k : ℕ) : ℕ :=
  (indicesLT L k).sum (fun j => indicator (y (π j)))

/-- Precision at rank `k` under permutation `π`. Defined as 0 for `k = 0`. -/
noncomputable def precAtPerm (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) (k : ℕ) : ℝ :=
  if 0 < k then (cumRelevantPerm y π k : ℝ) / (k : ℝ) else 0

/-- Average Precision computed along the order given by permutation `π`.
This matches the usual `∑_{k=1}^L Prec@k · rel@k / M` formula. -/
noncomputable def apUnderPerm (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) : ℝ :=
  let M := numRelevant y
  if M = 0 then 0
  else (∑ i : Fin L, (if y (π i) then precAtPerm y π (rank1 i) else 0)) / (M : ℝ)

/-- Uniform average over all permutations of `Fin L`. -/
noncomputable def uniformAvgOverPerms (f : Equiv.Perm (Fin L) → ℝ) : ℝ :=
  (Finset.univ.sum (fun π : Equiv.Perm (Fin L) => f π)) / (Fintype.card (Equiv.Perm (Fin L)) : ℝ)

/-- Uniform average of `AP` over all permutations (random ranking model). -/
noncomputable def uniformAvgAP (y : Fin L → Bool) : ℝ :=
  uniformAvgOverPerms (fun π => apUnderPerm (L:=L) y π)

/-- Prevalence as a real. -/
noncomputable def prevalence (y : Fin L → Bool) : ℝ :=
  (numRelevant (L:=L) y : ℝ) / (L : ℝ)

/-- Sum of quotients equals quotient of sum (finite, over `univ`). -/
lemma sum_div_const_univ {α} [Fintype α] (g : α → ℝ) (c : ℝ) :
  (∑ x : α, g x / c) = (∑ x : α, g x) / c := by
  classical
  calc
    (∑ x : α, g x / c) = (∑ x : α, g x * c⁻¹) := by simp [div_eq_mul_inv]
    _ = (∑ x : α, g x) * c⁻¹ := by simp [Finset.sum_mul]
    _ = (∑ x : α, g x) / c := by simp [div_eq_mul_inv]

/-- Simple commutation of nested divisions. -/
lemma div_div_comm' (a c d : ℝ) : (a / c) / d = (a / d) / c := by
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Swap double sums and commute the two divisions. -/
lemma double_sum_div_comm_univ
  {α β} [Fintype α] [Fintype β]
  (f : α → β → ℝ) (M H : ℝ) :
  ((∑ a : α, (∑ b : β, f a b) / M) / H)
    = ((∑ b : β, (∑ a : α, f a b) / H) / M) := by
  classical
  have L1 : (∑ a : α, (∑ b : β, f a b) / M)
      = (∑ a : α, ∑ b : β, f a b) / M := by
    simpa using sum_div_const_univ (fun a : α => (∑ b : β, f a b)) M
  have R1 : (∑ b : β, (∑ a : α, f a b) / H)
      = (∑ b : β, ∑ a : α, f a b) / H := by
    simpa using sum_div_const_univ (fun b : β => (∑ a : α, f a b)) H
  have swap : (∑ a : α, ∑ b : β, f a b) = (∑ b : β, ∑ a : α, f a b) := by
    simpa using (Finset.sum_comm (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β)) (f := fun a b => f a b))
  calc
    ((∑ a, (∑ b, f a b) / M) / H)
        = (((∑ a, ∑ b, f a b) / M) / H) := by simp [L1]
    _   = (((∑ b, ∑ a, f a b) / H) / M) := by simp [swap, div_div_comm']
    _   = ((∑ b, (∑ a, f a b) / H) / M) := by simp [R1]

/-- Uniform expectation of `Prec@k` at a fixed rank `k` over permutations. -/
noncomputable def uniformAvgPrecAtAtRank (y : Fin L → Bool) (k : ℕ) : ℝ :=
  uniformAvgOverPerms (fun π => precAtPerm (L:=L) y π k)

/-- Uniform average of `Prec@k` over ranks `1..L`, where each rank uses the
uniform expectation over permutations. Defined as 0 when `L = 0`. -/
noncomputable def uniformAvgPrecAt_allRanks (y : Fin L → Bool) : ℝ :=
  if _h : 0 < L then (∑ i : Fin L, uniformAvgPrecAtAtRank (L:=L) y (rank1 i)) / (L : ℝ) else 0

-- (Removed placeholder exchangeability lemma to focus the development on
-- prevalence/counting and summation lemmas used in the closed form.)

/-- For a fixed rank `i`, the relevance-weighted precision averaged over permutations. -/
noncomputable def rankWeightedPrecAvg (y : Fin L → Bool) (i : Fin L) : ℝ :=
  uniformAvgOverPerms (fun π => if y (π i) then precAtPerm (L:=L) y π (rank1 i) else 0)

/-- Algebraic decomposition: average AP over permutations equals the average,
over ranks, of the relevance-weighted precision, scaled by `1 / M`. -/
theorem uniformAvgAP_rank_decompose (y : Fin L → Bool) :
  uniformAvgAP (L:=L) y =
    (if _hM : numRelevant (L:=L) y = 0 then 0
     else (∑ i : Fin L, rankWeightedPrecAvg (L:=L) y i) / (numRelevant (L:=L) y : ℝ)) := by
  classical
  by_cases hM : numRelevant (L:=L) y = 0
  · -- both sides are 0 by definition
    simp [uniformAvgAP, uniformAvgOverPerms, apUnderPerm, hM]
  · -- M > 0 branch left as a structured proof to fill.
    classical
    -- Set up notation
    let M : ℝ := (numRelevant (L:=L) y : ℝ)
    let H : ℝ := (Fintype.card (Equiv.Perm (Fin L)) : ℝ)
    let f : Equiv.Perm (Fin L) → Fin L → ℝ :=
      fun π i => (if y (π i) then precAtPerm (L:=L) y π (rank1 i) else 0)
    -- Rewrite both sides into the double-sum forms that match `double_sum_div_comm_univ`
    have lhs_eq :
      uniformAvgAP (L:=L) y = ((∑ π : Equiv.Perm (Fin L), (∑ i : Fin L, f π i) / M) / H) := by
      calc
        uniformAvgAP (L:=L) y
            = ((∑ π : Equiv.Perm (Fin L), (∑ i : Fin L, f π i) / (numRelevant (L:=L) y : ℝ)) /
                (Fintype.card (Equiv.Perm (Fin L)) : ℝ)) := by
                  simp [uniformAvgAP, uniformAvgOverPerms, apUnderPerm, hM, f]
        _   = ((∑ π : Equiv.Perm (Fin L), (∑ i : Fin L, f π i) / M) / H) := by
                  simp [M, H]
    have rhs_eq :
      (∑ i : Fin L, rankWeightedPrecAvg (L:=L) y i) / M
        = ((∑ i : Fin L, (∑ π : Equiv.Perm (Fin L), f π i) / H) / M) := by
      calc
        (∑ i : Fin L, rankWeightedPrecAvg (L:=L) y i) / M
            = ((∑ i : Fin L, (∑ π : Equiv.Perm (Fin L), f π i) /
                  (Fintype.card (Equiv.Perm (Fin L)) : ℝ)) / M) := by
                  simp [rankWeightedPrecAvg, uniformAvgOverPerms, f]
        _   = ((∑ i : Fin L, (∑ π : Equiv.Perm (Fin L), f π i) / H) / M) := by
                  simp [H]
    -- Use the algebraic double-sum lemma and finish
    have step := double_sum_div_comm_univ f M H
    calc
      uniformAvgAP (L:=L) y
          = ((∑ π, (∑ i, f π i) / M) / H) := lhs_eq
      _   = ((∑ i, (∑ π, f π i) / H) / M) := by
              simpa using step
      _   = (∑ i : Fin L, rankWeightedPrecAvg (L:=L) y i) / M := by
              simpa using rhs_eq.symm
      _   = if hM : numRelevant (L:=L) y = 0 then 0 else (∑ i : Fin L, rankWeightedPrecAvg (L:=L) y i) / (numRelevant (L:=L) y : ℝ) := by
              simp [hM, M]

/-- Probability a random permutation places a relevant item at a fixed rank `i`. -/
lemma prob_relevant_at_rank (y : Fin L → Bool) (i : Fin L) (hL : 0 < L) :
  uniformAvgOverPerms (fun π => indicatorR (y (π i))) = prevalence (L:=L) y := by
  -- Each rank is equally likely to contain any item under a uniform permutation.
  -- Thus the expected indicator equals M/L.
  classical
  -- Expand the uniform average as a sum divided by |S_L|.
  simp [uniformAvgOverPerms, prevalence, indicatorR, div_eq_mul_inv]
  -- Reduce to: (∑π if y (π i) then 1 else 0) = (numRelevant y) * (Fintype.card (Equiv.Perm (Fin L)) / L)
  -- Counting argument: for each relevant item `j` with y j = true, the number of permutations with π i = j is (L-1)!.
  -- Hence the sum equals M · (L-1)!, and dividing by L! yields M/L.
  -- A full proof would map permutations by fixing the image at `i` and counting the remaining (L-1)! bijections.
  sorry

/-- Probability that two distinct ranks `i ≠ j` are both relevant under a random permutation. -/
lemma prob_both_relevant (y : Fin L → Bool) (i j : Fin L) (hij : i ≠ j) (hL : 1 < L) :
  uniformAvgOverPerms (fun π => indicatorR (y (π i)) * indicatorR (y (π j)))
    = (numRelevant (L:=L) y : ℝ) / (L : ℝ) * ((numRelevant (L:=L) y - 1 : ℝ) / (L - 1 : ℝ)) := by
  -- Sampling without replacement: P(both relevant) = (M/L) * ((M-1)/(L-1)).
  classical
  -- Expand the uniform average over permutations.
  simp [uniformAvgOverPerms, indicatorR, div_eq_mul_inv]
  -- Reduce to counting permutations with π i = a and π j = b for relevant a ≠ b.
  -- For each ordered pair of distinct relevant items (a,b), the number of permutations
  -- mapping i ↦ a and j ↦ b is (L-2)!; summing over such pairs gives M·(M-1)·(L-2)!
  -- Divide by L! = L·(L-1)·(L-2)! to obtain (M/L)·((M-1)/(L-1)).
  -- The remaining formal step establishes the counting identity.
  sorry

/-- Closed form for the relevance-weighted average precision contribution of rank `i`. -/
theorem rankWeightedPrecAvg_closed_form (y : Fin L → Bool) (i : Fin L) (hL : 1 < L) :
  rankWeightedPrecAvg (L:=L) y i
    = ((i.1 : ℝ) / (i.1 + 1)) * prevalence (L:=L) y * (((numRelevant (L:=L) y - 1 : ℝ) / (L - 1 : ℝ)))
      + ((1 : ℝ) / (i.1 + 1)) * prevalence (L:=L) y := by
  -- Expand definition, use prob_both_relevant for the (k-1) earlier ranks
  -- and prob_relevant_at_rank for the rank-`i` term.
  -- Here `i.1 + 1` is the 1-indexed rank k, and `i.1` counts prior positions.
  classical
  -- Unfold the relevance-weighted precision at rank i
  simp [rankWeightedPrecAvg, uniformAvgOverPerms, precAtPerm, div_eq_mul_inv]
  -- Split the precision (X+1)/k into X/k + 1/k and pull 1/k outside the uniform average
  -- X is the count of relevant items among previous positions {j | j.1 < i.1 + 1}
  -- Replace expectations with the probability lemmas specialized to i
  -- P(y at rank i) = prevalence; E[X | y at rank i] = (i.1)*(M-1)/(L-1)
  have h1 := prob_relevant_at_rank (L:=L) y i (by exact Nat.lt_of_le_of_lt (Nat.zero_le 0) (lt_trans (Nat.zero_lt_one) hL))
  -- Two-rank probability reduces to the conditional expectation of X given rank i relevant
  -- Algebra: E[ (X+1)/k 1{y_i} ] = (1/k) P(y_i) + (1/k) ∑_{j< i} P(y_j ∧ y_i)
  -- Use prob_both_relevant for each j< i and sum them to (i.1) * (M/L)*((M-1)/(L-1))
  -- Finish with linearity
  sorry

/-- Sum over ranks of the closed form reduces to the harmonic-number expression. -/
lemma sum_rankWeightedPrecAvg_closed_form (y : Fin L → Bool) (hL : 1 < L) :
  ∑ i : Fin L, rankWeightedPrecAvg (L:=L) y i
    = (prevalence (L:=L) y) * ((numRelevant (L:=L) y - 1 : ℝ) / (L - 1 : ℝ)) * ((L : ℝ) - harmonic L)
      + (prevalence (L:=L) y) * (harmonic L) := by
  -- Use ∑ (i:Fin L) (i/(i+1)) = L - H_L and ∑ (i:Fin L) (1/(i+1)) = H_L.
  classical
  -- First, sum the closed form rank-by-rank
  have hsum :=
    (Finset.univ.sum_congr rfl (fun i _ => rankWeightedPrecAvg_closed_form (L:=L) y i hL))
  -- Rearrange sums and pull constants
  -- Reduce to two sums over `i : Fin L`: ∑ i i/(i+1) and ∑ i 1/(i+1)
  -- Then apply the harmonic-number identities
  sorry

/-- Finite identity: ∑_{i=0}^{L-1} 1/(i+1) = H_L. -/
lemma sum_fin_one_over (hL : 0 < L) :
  (∑ i : Fin L, (1 : ℝ) / (i.1 + 1)) = harmonic L := by
  -- Convert `Fin L` sum to `range (L+1)` with an offset; use the definition of `harmonic`.
  sorry

/-- Finite identity: ∑_{i=0}^{L-1} i/(i+1) = L - H_L. -/
lemma sum_fin_prev_over (hL : 0 < L) :
  (∑ i : Fin L, (i.1 : ℝ) / (i.1 + 1)) = (L : ℝ) - harmonic L := by
  -- Use 1 - 1/(i+1) and the previous lemma.
  sorry

/-- Main closed form for expected AP under uniform random ranking. -/
theorem expected_ap_closed_form (y : Fin L → Bool) (hL : 1 < L) :
  uniformAvgAP (L:=L) y
    = (1 / (L : ℝ)) * (((numRelevant (L:=L) y - 1 : ℝ) / (L - 1 : ℝ)) * ((L : ℝ) - harmonic L) + harmonic L) := by
  -- Will follow from `uniformAvgAP_rank_decompose` and `sum_rankWeightedPrecAvg_closed_form`.
  sorry

-- (Removed second placeholder exchangeability lemma.)

/-- Skeleton statement for the expected AP under uniformly random ranking.
This is a placeholder theorem to anchor the development. -/
theorem expected_ap_uniform_skeleton
  (_y : Fin L → Bool) (_hL : 0 < L) : True := by
  trivial

end ExpectedAp
