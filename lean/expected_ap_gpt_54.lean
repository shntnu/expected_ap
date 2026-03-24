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

/-- The indices `{ i : Fin L | i < k }` as a finite set. -/
def indicesLT (L k : ℕ) : Finset (Fin L) :=
  univ.filter (fun i : Fin L => i.1 < k)

/-- 1-indexed rank for a 0-indexed `Fin` index. -/
def rank1 (i : Fin L) : ℕ := i.1 + 1

/-- Harmonic number `H_L = ∑_{k=1}^L 1/k` as a real number. -/
noncomputable def harmonic (L : ℕ) : ℝ :=
  (Finset.range (L + 1)).sum (fun k => if 0 < k then (1 : ℝ) / (k : ℝ) else 0)

/-- Cumulative number of relevant items among the first `k` ranks under a permutation `π`. -/
def cumRelevantPerm (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) (k : ℕ) : ℕ :=
  (indicesLT L k).sum (fun j => indicator (y (π j)))

/-- Precision at rank `k` under permutation `π`. Defined as 0 for `k = 0`. -/
noncomputable def precAtPerm (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) (k : ℕ) : ℝ :=
  if 0 < k then (cumRelevantPerm y π k : ℝ) / (k : ℝ) else 0

/-- Average Precision computed along the order given by permutation `π`. -/
noncomputable def apUnderPerm (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) : ℝ :=
  let M := numRelevant y
  if M = 0 then 0
  else (∑ i : Fin L, (if y (π i) then precAtPerm y π (rank1 i) else 0)) / (M : ℝ)

/-- Uniform average over all permutations of `Fin L`. -/
noncomputable def uniformAvgOverPerms (f : Equiv.Perm (Fin L) → ℝ) : ℝ :=
  (Finset.univ.sum (fun π : Equiv.Perm (Fin L) => f π)) / (Fintype.card (Equiv.Perm (Fin L)) : ℝ)

/-- Uniform average of `AP` over all permutations. -/
noncomputable def uniformAvgAP (y : Fin L → Bool) : ℝ :=
  uniformAvgOverPerms (fun π => apUnderPerm (L := L) y π)

/-- Prevalence as a real. -/
noncomputable def prevalence (y : Fin L → Bool) : ℝ :=
  (numRelevant (L := L) y : ℝ) / (L : ℝ)

/-- For a fixed rank `i`, the relevance-weighted precision averaged over permutations. -/
noncomputable def rankWeightedPrecAvg (y : Fin L → Bool) (i : Fin L) : ℝ :=
  uniformAvgOverPerms (fun π => if y (π i) then precAtPerm (L := L) y π (rank1 i) else 0)

private lemma sum_perm_apply_swap_gpt {L : ℕ} (f : Fin L → ℝ) (i j : Fin L) :
    ∑ σ : Equiv.Perm (Fin L), f (σ i) = ∑ σ : Equiv.Perm (Fin L), f (σ j) :=
  Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j)) _ _ (fun σ => by
    simp [Equiv.Perm.mul_apply])

private lemma sum_perm_apply_eq_gpt {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ∑ σ : Equiv.Perm (Fin (n + 1)), f (σ i) = ↑n.factorial * ∑ j, f j := by
  conv_lhs => rw [sum_perm_apply_swap_gpt f i 0]
  have : ∑ σ : Equiv.Perm (Fin (n + 1)), f (σ 0) =
      ∑ pe : Fin (n + 1) × Equiv.Perm (Fin n), f pe.1 :=
    Fintype.sum_equiv Equiv.Perm.decomposeFin _ _ (fun σ => by
      simp [Equiv.Perm.decomposeFin])
  rw [this, Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin]
  simp [nsmul_eq_mul, mul_sum]

private lemma sum_indicatorR_eq_gpt {L : ℕ} (y : Fin L → Bool) :
    ∑ j : Fin L, indicatorR (y j) = (numRelevant (L := L) y : ℝ) := by
  simp [numRelevant, indicator, indicatorR]

lemma sum_div_const_univ {α} [Fintype α] (g : α → ℝ) (c : ℝ) :
    (∑ x : α, g x / c) = (∑ x : α, g x) / c := by
  classical
  calc
    (∑ x : α, g x / c) = (∑ x : α, g x * c⁻¹) := by simp [div_eq_mul_inv]
    _ = (∑ x : α, g x) * c⁻¹ := by simp [Finset.sum_mul]
    _ = (∑ x : α, g x) / c := by simp [div_eq_mul_inv]

lemma div_div_comm' (a c d : ℝ) : (a / c) / d = (a / d) / c := by
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

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
    simpa using
      (Finset.sum_comm (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β)) (f := fun a b => f a b))
  calc
    ((∑ a, (∑ b, f a b) / M) / H)
        = (((∑ a, ∑ b, f a b) / M) / H) := by simp [L1]
    _ = (((∑ b, ∑ a, f a b) / H) / M) := by simp [swap, div_div_comm']
    _ = ((∑ b, (∑ a, f a b) / H) / M) := by simp [R1]

theorem uniformAvgAP_rank_decompose (y : Fin L → Bool) :
    uniformAvgAP (L := L) y =
      (if _hM : numRelevant (L := L) y = 0 then 0
       else (∑ i : Fin L, rankWeightedPrecAvg (L := L) y i) / (numRelevant (L := L) y : ℝ)) := by
  classical
  by_cases hM : numRelevant (L := L) y = 0
  · simp [uniformAvgAP, uniformAvgOverPerms, apUnderPerm, hM]
  · let M : ℝ := (numRelevant (L := L) y : ℝ)
    let H : ℝ := (Fintype.card (Equiv.Perm (Fin L)) : ℝ)
    let f : Equiv.Perm (Fin L) → Fin L → ℝ :=
      fun π i => if y (π i) then precAtPerm (L := L) y π (rank1 i) else 0
    have lhs_eq :
        uniformAvgAP (L := L) y = ((∑ π : Equiv.Perm (Fin L), (∑ i : Fin L, f π i) / M) / H) := by
      calc
        uniformAvgAP (L := L) y
            = ((∑ π : Equiv.Perm (Fin L), (∑ i : Fin L, f π i) / (numRelevant (L := L) y : ℝ)) /
                (Fintype.card (Equiv.Perm (Fin L)) : ℝ)) := by
                  simp [uniformAvgAP, uniformAvgOverPerms, apUnderPerm, hM, f]
        _ = ((∑ π : Equiv.Perm (Fin L), (∑ i : Fin L, f π i) / M) / H) := by
              simp [M, H]
    have rhs_eq :
        (∑ i : Fin L, rankWeightedPrecAvg (L := L) y i) / M
          = ((∑ i : Fin L, (∑ π : Equiv.Perm (Fin L), f π i) / H) / M) := by
      calc
        (∑ i : Fin L, rankWeightedPrecAvg (L := L) y i) / M
            = ((∑ i : Fin L, (∑ π : Equiv.Perm (Fin L), f π i) /
                  (Fintype.card (Equiv.Perm (Fin L)) : ℝ)) / M) := by
                    simp [rankWeightedPrecAvg, uniformAvgOverPerms, f]
        _ = ((∑ i : Fin L, (∑ π : Equiv.Perm (Fin L), f π i) / H) / M) := by
              simp [H]
    have step := double_sum_div_comm_univ f M H
    calc
      uniformAvgAP (L := L) y
          = ((∑ π, (∑ i, f π i) / M) / H) := lhs_eq
      _ = ((∑ i, (∑ π, f π i) / H) / M) := by simpa using step
      _ = (∑ i : Fin L, rankWeightedPrecAvg (L := L) y i) / M := by
            simpa using rhs_eq.symm
      _ = if hM : numRelevant (L := L) y = 0 then 0
          else (∑ i : Fin L, rankWeightedPrecAvg (L := L) y i) / (numRelevant (L := L) y : ℝ) := by
            simp [hM, M]

/-!
The next block proves the permutation-counting facts used in the proof:

1. Reindex any ordered pair of distinct ranks to `(0, 1)`.
2. Decompose permutations of `Fin (n+2)` by their value at `0`.
3. Count the two-rank relevance probability from that decomposition.

This is the main combinatorial input. After this point, the proof returns to the
original exchangeability-based outline: analyze one fixed rank, then sum over ranks.
-/
lemma prob_relevant_at_rank (y : Fin L → Bool) (i : Fin L) (hL : 0 < L) :
    uniformAvgOverPerms (fun π => indicatorR (y (π i))) = prevalence (L := L) y := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  simp only [uniformAvgOverPerms, prevalence]
  rw [sum_perm_apply_eq_gpt (fun j => indicatorR (y j)) i, sum_indicatorR_eq_gpt,
    Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]
  push_cast
  field_simp

lemma sum_fin_one_over (_hL : 0 < L) :
    (∑ i : Fin L, (1 : ℝ) / (i.1 + 1)) = harmonic L := by
  unfold harmonic
  rw [Finset.sum_range_succ']
  simp only [Nat.lt_irrefl, ↓reduceIte, add_zero, Nat.succ_pos', Nat.cast_add, Nat.cast_one]
  exact Fin.sum_univ_eq_sum_range (fun n => 1 / ((n : ℝ) + 1)) L

lemma sum_fin_prev_over (hL : 0 < L) :
    (∑ i : Fin L, (i.1 : ℝ) / (i.1 + 1)) = (L : ℝ) - harmonic L := by
  have h1 : ∀ i : Fin L, (i.1 : ℝ) / (i.1 + 1) = 1 - 1 / (i.1 + 1) := by
    intro i
    field_simp
    ring
  simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul, mul_one, sum_fin_one_over hL]

private lemma pair_to_zero_one {n : ℕ} (f : Fin (n + 2) → Fin (n + 2) → ℝ)
    (i j : Fin (n + 2)) (hij : i ≠ j) :
    ∑ σ : Equiv.Perm (Fin (n + 2)), f (σ i) (σ j)
      = ∑ σ : Equiv.Perm (Fin (n + 2)), f (σ 0) (σ 1) := by
  classical
  let τ₁ : Equiv.Perm (Fin (n + 2)) := Equiv.swap i 0
  let j₁ : Fin (n + 2) := τ₁ j
  let τ₂ : Equiv.Perm (Fin (n + 2)) := Equiv.swap j₁ 1
  let τ : Equiv.Perm (Fin (n + 2)) := τ₂ * τ₁
  have hj₁_ne_zero : j₁ ≠ 0 := by
    intro hj₁_zero
    have : j = i := by
      apply τ₁.injective
      simpa [j₁, τ₁] using hj₁_zero
    exact hij this.symm
  have hτi : τ i = 0 := by
    dsimp [τ, τ₁, τ₂, j₁]
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (by simpa using hj₁_ne_zero.symm) Fin.zero_ne_one
  have hτj : τ j = 1 := by
    simp [τ, τ₁, τ₂, j₁]
  calc
    ∑ σ : Equiv.Perm (Fin (n + 2)), f (σ i) (σ j)
      = ∑ σ : Equiv.Perm (Fin (n + 2)), f ((σ * τ) i) ((σ * τ) j) := by
          refine (Fintype.sum_equiv (Equiv.mulRight τ) _ _ ?_).symm
          intro σ
          simp [Equiv.Perm.mul_apply]
    _ = ∑ σ : Equiv.Perm (Fin (n + 2)), f (σ 0) (σ 1) := by
          simp [hτi, hτj]

private lemma sum_swap_zero_succ_eq_sum_succAbove
    {n : ℕ} (p : Fin (n + 2)) (f : Fin (n + 2) → ℝ) :
    (∑ q : Fin (n + 1), f (Equiv.swap 0 p q.succ)) = ∑ r : Fin (n + 1), f (p.succAbove r) := by
  classical
  cases p using Fin.cases with
  | zero =>
      simp
  | succ p =>
      calc
        (∑ q : Fin (n + 1), f (Equiv.swap 0 p.succ q.succ))
            = ∑ q : Fin (n + 1), f (p.succ.succAbove (p.cycleRange q)) := by
                congr with q
                rw [← Fin.succAbove_cycleRange]
        _ = ∑ r : Fin (n + 1), f (p.succ.succAbove r) := by
              simpa using
                (Fintype.sum_equiv p.cycleRange
                  (fun q : Fin (n + 1) => f (p.succ.succAbove (p.cycleRange q)))
                  (fun r : Fin (n + 1) => f (p.succ.succAbove r))
                  (fun q => by simp))

private lemma sum_indicatorR_succAbove
    {n : ℕ} (y : Fin (n + 2) → Bool) (p : Fin (n + 2)) :
    ∑ q : Fin (n + 1), indicatorR (y (p.succAbove q))
      = (numRelevant (L := n + 2) y : ℝ) - indicatorR (y p) := by
  rw [← sum_indicatorR_eq_gpt (L := n + 2) y,
    Fin.sum_univ_succAbove (fun x : Fin (n + 2) => indicatorR (y x)) p]
  ring

private lemma sum_perm_indicator_pair_zero_one
    {n : ℕ} (y : Fin (n + 2) → Bool) :
    ∑ σ : Equiv.Perm (Fin (n + 2)), indicatorR (y (σ 0)) * indicatorR (y (σ 1))
      = (n.factorial : ℝ) *
          ∑ p : Fin (n + 2), indicatorR (y p) *
            ((numRelevant (L := n + 2) y : ℝ) - indicatorR (y p)) := by
  classical
  calc
    ∑ σ : Equiv.Perm (Fin (n + 2)), indicatorR (y (σ 0)) * indicatorR (y (σ 1))
      = ∑ pe : Fin (n + 2) × Equiv.Perm (Fin (n + 1)),
          indicatorR (y pe.1) * indicatorR (y ((Equiv.Perm.decomposeFin.symm pe) 1)) := by
            refine Fintype.sum_equiv Equiv.Perm.decomposeFin _ _ ?_
            intro σ
            simp [Equiv.Perm.decomposeFin]
    _ = ∑ p : Fin (n + 2),
          ∑ e : Equiv.Perm (Fin (n + 1)),
            indicatorR (y p) * indicatorR (y ((Equiv.Perm.decomposeFin.symm (p, e)) 1)) := by
            rw [Fintype.sum_prod_type]
    _ = ∑ p : Fin (n + 2),
          ∑ e : Equiv.Perm (Fin (n + 1)),
            indicatorR (y p) * indicatorR (y (Equiv.swap 0 p (e 0).succ)) := by
            congr with p
            congr with e
            simp [Equiv.Perm.decomposeFin_symm_apply_one]
    _ = ∑ p : Fin (n + 2),
          indicatorR (y p) *
            ∑ e : Equiv.Perm (Fin (n + 1)), indicatorR (y (Equiv.swap 0 p (e 0).succ)) := by
            congr with p
            rw [Finset.mul_sum]
    _ = ∑ p : Fin (n + 2),
          indicatorR (y p) *
            ((n.factorial : ℝ) * ∑ q : Fin (n + 1), indicatorR (y (Equiv.swap 0 p q.succ))) := by
            congr with p
            rw [sum_perm_apply_eq_gpt
              (f := fun q : Fin (n + 1) => indicatorR (y (Equiv.swap 0 p q.succ)))
              (i := 0)]
    _ = ∑ p : Fin (n + 2),
          indicatorR (y p) *
            ((n.factorial : ℝ) * ∑ q : Fin (n + 1), indicatorR (y (p.succAbove q))) := by
            congr with p
            rw [sum_swap_zero_succ_eq_sum_succAbove (p := p) (f := fun x => indicatorR (y x))]
    _ = ∑ p : Fin (n + 2),
          indicatorR (y p) * ((n.factorial : ℝ) * ((numRelevant (L := n + 2) y : ℝ) - indicatorR (y p))) := by
            congr with p
            rw [sum_indicatorR_succAbove (y := y) (p := p)]
    _ = (n.factorial : ℝ) *
          ∑ p : Fin (n + 2), indicatorR (y p) * ((numRelevant (L := n + 2) y : ℝ) - indicatorR (y p)) := by
            calc
              _ = ∑ p : Fin (n + 2), (n.factorial : ℝ) *
                    (indicatorR (y p) * ((numRelevant (L := n + 2) y : ℝ) - indicatorR (y p))) := by
                      congr with p
                      ring
              _ = (n.factorial : ℝ) *
                    ∑ p : Fin (n + 2), indicatorR (y p) * ((numRelevant (L := n + 2) y : ℝ) - indicatorR (y p)) := by
                      rw [← Finset.mul_sum]

private lemma indicatorR_sq (b : Bool) : indicatorR b * indicatorR b = indicatorR b := by
  by_cases h : b <;> simp [indicatorR, h]

lemma prob_both_relevant_nplus2 {n : ℕ} (y : Fin (n + 2) → Bool) (i j : Fin (n + 2)) (hij : i ≠ j) :
    uniformAvgOverPerms (fun π => indicatorR (y (π i)) * indicatorR (y (π j)))
      = (numRelevant (L := n + 2) y : ℝ) / (n + 2 : ℝ) *
          ((numRelevant (L := n + 2) y - 1 : ℝ) / (n + 1 : ℝ)) := by
  classical
  simp only [uniformAvgOverPerms]
  rw [pair_to_zero_one (f := fun a b : Fin (n + 2) => indicatorR (y a) * indicatorR (y b)) i j hij,
    sum_perm_indicator_pair_zero_one]
  have hsquare :
      ∑ p : Fin (n + 2), indicatorR (y p) * ((numRelevant (L := n + 2) y : ℝ) - indicatorR (y p))
        = (numRelevant (L := n + 2) y : ℝ) * ((numRelevant (L := n + 2) y : ℝ) - 1) := by
    calc
      ∑ p : Fin (n + 2), indicatorR (y p) * ((numRelevant (L := n + 2) y : ℝ) - indicatorR (y p))
        = (∑ p : Fin (n + 2), indicatorR (y p) * (numRelevant (L := n + 2) y : ℝ))
            - ∑ p : Fin (n + 2), indicatorR (y p) * indicatorR (y p) := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib]
      _ = (∑ p : Fin (n + 2), indicatorR (y p)) * (numRelevant (L := n + 2) y : ℝ)
            - ∑ p : Fin (n + 2), indicatorR (y p) := by
              simp_rw [indicatorR_sq]
              rw [Finset.sum_mul]
      _ = (numRelevant (L := n + 2) y : ℝ) * (numRelevant (L := n + 2) y : ℝ)
            - (numRelevant (L := n + 2) y : ℝ) := by
              rw [sum_indicatorR_eq_gpt]
      _ = (numRelevant (L := n + 2) y : ℝ) * ((numRelevant (L := n + 2) y : ℝ) - 1) := by
              ring
  rw [hsquare, Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Generic wrapper around the `Fin (n+2)` two-rank formula. -/
lemma prob_both_relevant_gpt54 (y : Fin L → Bool) (i j : Fin L) (hij : i ≠ j) (hL : 1 < L) :
    uniformAvgOverPerms (fun π => indicatorR (y (π i)) * indicatorR (y (π j)))
      = (numRelevant (L := L) y : ℝ) / (L : ℝ) *
          ((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ)) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := ⟨L - 2, by omega⟩
  convert prob_both_relevant_nplus2 (y := y) (i := i) (j := j) hij using 1
  push_cast [Nat.cast_add, Nat.cast_one]
  ring_nf

private def finLTEmb (i : Fin L) : Fin i.1 ↪ Fin L where
  toFun j := ⟨j.1, Nat.lt_trans j.2 i.2⟩
  inj' := by
    intro a b h
    exact Fin.ext <| by simpa using congrArg Fin.val h

private lemma indicesLT_eq_map (i : Fin L) :
    indicesLT L i.1 = (Finset.univ.map (finLTEmb i)) := by
  ext j
  constructor
  · intro hj
    simp [indicesLT] at hj
    simp [finLTEmb]
    exact ⟨⟨j.1, hj⟩, Fin.ext rfl⟩
  · intro hj
    simp [finLTEmb] at hj
    rcases hj with ⟨a, rfl⟩
    simp [indicesLT]
    exact Fin.lt_iff_val_lt_val.mpr a.2

private lemma sum_indicesLT_const (i : Fin L) (c : ℝ) :
    (∑ _j ∈ indicesLT L i.1, c) = (i.1 : ℝ) * c := by
  rw [indicesLT_eq_map i]
  simp [finLTEmb]

/-- The cumulative count through rank `i+1` splits into the previous ranks plus rank `i` itself. -/
private lemma cumRelevantPerm_split (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) (i : Fin L) :
    (cumRelevantPerm (L := L) y π (i.1 + 1) : ℝ) =
      (∑ j ∈ indicesLT L i.1, indicatorR (y (π j))) + indicatorR (y (π i)) := by
  have hins : indicesLT L (i.1 + 1) = insert i (indicesLT L i.1) := by
    ext j
    simp [indicesLT]
    constructor
    · intro h
      by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr (by
          have hjv : j.1 ≠ i.1 := by
            intro hv
            apply hji
            exact Fin.ext hv
          omega)
    · intro h
      rcases h with rfl | h
      · omega
      · omega
  have hprev :
      (cumRelevantPerm (L := L) y π i.1 : ℝ) =
        ∑ j ∈ indicesLT L i.1, indicatorR (y (π j)) := by
    unfold cumRelevantPerm
    simp [indicatorR, indicator]
  unfold cumRelevantPerm
  rw [hins, Finset.sum_insert]
  · push_cast
    simp [indicatorR, indicator, add_comm]
  · simp [indicesLT]

private lemma indicesLT_ne_of_mem (i : Fin L) {j : Fin L} (hj : j ∈ indicesLT L i.1) : j ≠ i := by
  simp [indicesLT] at hj
  exact Fin.ne_of_lt (by omega : j.1 < i.1)

/--
Fixed-rank contribution formula.

At rank `i`, write the relevance-weighted precision as:

`1{relevant at i} * (number of relevant items up to i) / (i+1)`.

Split the numerator into:
- relevant items strictly before `i`
- the indicator that rank `i` itself is relevant

Then evaluate the two resulting expectations using `prob_both_relevant_gpt54`
and `prob_relevant_at_rank`.
-/
theorem rankWeightedPrecAvg_closed_form_gpt54 (y : Fin L → Bool) (i : Fin L) (hL : 1 < L) :
    rankWeightedPrecAvg (L := L) y i
      = ((i.1 : ℝ) / (i.1 + 1)) * prevalence (L := L) y *
          (((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ)))
        + ((1 : ℝ) / (i.1 + 1)) * prevalence (L := L) y := by
  classical
  have hL0 : 0 < L := by omega
  have hk : 0 < i.1 + 1 := Nat.succ_pos _
  set H : ℝ := (Fintype.card (Equiv.Perm (Fin L)) : ℝ)
  set A : Equiv.Perm (Fin L) → ℝ :=
    fun π => indicatorR (y (π i)) * (∑ j ∈ indicesLT L i.1, indicatorR (y (π j))) / (i.1 + 1 : ℝ)
  set B : Equiv.Perm (Fin L) → ℝ :=
    fun π => indicatorR (y (π i)) / (i.1 + 1 : ℝ)
  have key : rankWeightedPrecAvg (L := L) y i = ((∑ π : Equiv.Perm (Fin L), A π) + (∑ π : Equiv.Perm (Fin L), B π)) / H := by
    simp only [rankWeightedPrecAvg, uniformAvgOverPerms, H, A, B]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro π _
    simp only [precAtPerm, rank1, hk, ↓reduceIte]
    split
    · rename_i hrel
      rw [cumRelevantPerm_split]
      simp [indicatorR, hrel]
      ring
    · rename_i hrel
      simp [indicatorR, hrel]
  rw [key]
  have hsplit :
      ((∑ π : Equiv.Perm (Fin L), A π) + (∑ π : Equiv.Perm (Fin L), B π)) / H
        = (∑ π : Equiv.Perm (Fin L), A π) / H + (∑ π : Equiv.Perm (Fin L), B π) / H := by
    simp [div_eq_mul_inv, add_mul]
  rw [hsplit]
  have term2 :
      (∑ π : Equiv.Perm (Fin L), B π) / H
        = ((1 : ℝ) / (i.1 + 1)) * prevalence (L := L) y := by
    rw [show ((∑ π : Equiv.Perm (Fin L), B π) / H)
      = (((∑ π : Equiv.Perm (Fin L), indicatorR (y (π i))) / H) / (i.1 + 1 : ℝ)) by
        simp [B, Finset.sum_div, div_div_comm']]
    have h1 := prob_relevant_at_rank (L := L) y i hL0
    rw [show ((∑ π : Equiv.Perm (Fin L), indicatorR (y (π i))) / H) = prevalence (L := L) y by
      simpa [uniformAvgOverPerms, H] using h1]
    ring
  have term1 :
      (∑ π : Equiv.Perm (Fin L), A π) / H
        = ((i.1 : ℝ) / (i.1 + 1)) * prevalence (L := L) y *
            (((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ))) := by
    rw [show (∑ π : Equiv.Perm (Fin L), A π)
      = (∑ π : Equiv.Perm (Fin L),
          indicatorR (y (π i)) * (∑ j ∈ indicesLT L i.1, indicatorR (y (π j)))) / (i.1 + 1 : ℝ) by
        simp [A, Finset.sum_div]]
    rw [div_div_comm']
    rw [show ∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) * (∑ j ∈ indicesLT L i.1, indicatorR (y (π j))) =
      ∑ j ∈ indicesLT L i.1, ∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) * indicatorR (y (π j)) by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]]
    rw [show ((∑ j ∈ indicesLT L i.1, ∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) * indicatorR (y (π j))) / H)
      = ∑ j ∈ indicesLT L i.1,
          ((∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) * indicatorR (y (π j))) / H) by
        simp [Finset.sum_div]]
    have hpair : ∀ j ∈ indicesLT L i.1,
        ((∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) * indicatorR (y (π j))) / H)
          = (numRelevant (L := L) y : ℝ) / (L : ℝ) *
              ((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ)) := by
      intro j hj
      have := prob_both_relevant_gpt54 (L := L) y i j ((indicesLT_ne_of_mem i hj).symm) hL
      simpa [uniformAvgOverPerms, H] using this
    rw [show ∑ j ∈ indicesLT L i.1,
      ((∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) * indicatorR (y (π j))) / H)
      = ∑ j ∈ indicesLT L i.1,
          ((numRelevant (L := L) y : ℝ) / (L : ℝ) *
            ((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ))) by
        exact Finset.sum_congr rfl hpair]
    rw [sum_indicesLT_const]
    simp [prevalence]
    ring
  rw [term1, term2]

lemma sum_rankWeightedPrecAvg_closed_form_gpt54 (y : Fin L → Bool) (hL : 1 < L) :
    ∑ i : Fin L, rankWeightedPrecAvg (L := L) y i
      = (prevalence (L := L) y) * ((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ)) *
          ((L : ℝ) - harmonic L)
        + (prevalence (L := L) y) * harmonic L := by
  have hL0 : 0 < L := by omega
  rw [show (∑ i : Fin L, rankWeightedPrecAvg (L := L) y i)
    = ∑ i : Fin L,
        (((i.1 : ℝ) / (i.1 + 1)) * prevalence (L := L) y *
          (((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ)))
        + ((1 : ℝ) / (i.1 + 1)) * prevalence (L := L) y) by
      apply Finset.sum_congr rfl
      intro i _
      exact rankWeightedPrecAvg_closed_form_gpt54 (L := L) y i hL]
  rw [Finset.sum_add_distrib]
  have h1 :
      (∑ i : Fin L,
          ((i.1 : ℝ) / (i.1 + 1)) * prevalence (L := L) y *
            (((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ))))
        = (prevalence (L := L) y) * ((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ)) *
            (∑ i : Fin L, (i.1 : ℝ) / (i.1 + 1)) := by
    calc
      _ = ∑ i : Fin L,
            ((prevalence (L := L) y) * ((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ))) *
              ((i.1 : ℝ) / (i.1 + 1)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (prevalence (L := L) y) * ((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ)) *
            (∑ i : Fin L, (i.1 : ℝ) / (i.1 + 1)) := by
              rw [← Finset.mul_sum]
  have h2 :
      (∑ i : Fin L, ((1 : ℝ) / (i.1 + 1)) * prevalence (L := L) y)
        = (prevalence (L := L) y) * (∑ i : Fin L, (1 : ℝ) / (i.1 + 1)) := by
    calc
      _ = ∑ i : Fin L, (prevalence (L := L) y) * ((1 : ℝ) / (i.1 + 1)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (prevalence (L := L) y) * (∑ i : Fin L, (1 : ℝ) / (i.1 + 1)) := by
            rw [← Finset.mul_sum]
  rw [h1, h2, sum_fin_prev_over hL0, sum_fin_one_over hL0]

/-- Closed form for expected AP when there is at least one relevant item. -/
theorem expected_ap_closed_form_gpt54 (y : Fin L → Bool) (hL : 1 < L)
    (hM : numRelevant (L := L) y ≠ 0) :
    uniformAvgAP (L := L) y
      = (1 / (L : ℝ)) *
          ((((numRelevant (L := L) y - 1 : ℝ) / (L - 1 : ℝ)) * ((L : ℝ) - harmonic L))
            + harmonic L) := by
  -- Combine the decomposition of `uniformAvgAP` with the summed fixed-rank formula,
  -- then divide by the nonzero number of relevant items.
  have hL0 : 0 < L := by omega
  rw [uniformAvgAP_rank_decompose]
  simp [hM, sum_rankWeightedPrecAvg_closed_form_gpt54 (L := L) y hL]
  simp [prevalence]
  have hM' : ((numRelevant (L := L) y : ℝ)) ≠ 0 := by
    exact_mod_cast hM
  field_simp [hM']

end ExpectedAp
