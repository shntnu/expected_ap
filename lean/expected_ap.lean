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

/-! ### Proof strategy

The closed-form proof proceeds in four layers:

1. **Permutation counting** (`sum_perm_apply_eq`, `sum_perm_pair`).
   The single-position formula `∑_σ f(σ(i)) = (L-1)! · ∑ f` is proved by
   swapping position `i` to position `0` via `Equiv.mulRight`, then decomposing
   `Perm(Fin(n+1)) ≃ Fin(n+1) × Perm(Fin n)` via `decomposeFin`.
   The two-position formula `∑_σ f(σ(i))·g(σ(j)) = (L-2)!·((∑f)(∑g) - ∑fg)`
   reuses the single-position result on the inner sub-permutation, with
   `sum_swap_succ` bridging the swap-and-successor arithmetic.

2. **Probability lemmas** (`prob_relevant_at_rank`, `prob_both_relevant`).
   Direct corollaries of layer 1, dividing by `L!` and specialising
   `f = g = indicatorR ∘ y`.

3. **Per-rank closed form** (`rankWeightedPrecAvg_closed_form`).
   Splits the precision at rank `k` into the self-term (layer 2, single) and
   the cross-terms (layer 2, pair), then sums over the `i` prior positions.

4. **Global closed form** (`expected_ap_closed_form`).
   Sums layer 3 over all ranks using the harmonic identities
   `∑ 1/(i+1) = H_L` and `∑ i/(i+1) = L − H_L`, then applies the
   already-proved `uniformAvgAP_rank_decompose` to connect `E[AP]` to
   the rank-sum.  Requires `M ≥ 1` (AP is 0 by convention when `M = 0`,
   but the harmonic formula is nonzero for `L > 1`).
-/

/-- The sum `∑ σ, f(σ(i))` is the same for any two positions `i, j`. -/
private lemma sum_perm_apply_swap (f : Fin L → ℝ) (i j : Fin L) :
    ∑ σ : Equiv.Perm (Fin L), f (σ i) = ∑ σ : Equiv.Perm (Fin L), f (σ j) :=
  Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j)) _ _ (fun σ => by
    simp [Equiv.Perm.mul_apply])

/-- Summing `f(σ(i))` over all permutations `σ` of `Fin (n+1)` gives `n! * ∑ j, f j`. -/
private lemma sum_perm_apply_eq {n : ℕ} (f : Fin (n+1) → ℝ) (i : Fin (n+1)) :
    ∑ σ : Equiv.Perm (Fin (n+1)), f (σ i) = ↑n.factorial * ∑ j, f j := by
  conv_lhs => rw [sum_perm_apply_swap f i 0]
  have : ∑ σ : Equiv.Perm (Fin (n + 1)), f (σ 0) =
      ∑ pe : Fin (n + 1) × Equiv.Perm (Fin n), f pe.1 :=
    Fintype.sum_equiv Equiv.Perm.decomposeFin _ _ (fun σ => by
      simp [Equiv.Perm.decomposeFin])
  rw [this, Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin]
  simp [nsmul_eq_mul, mul_sum]

/-- The real-valued indicator sum equals the natural-number count `numRelevant`. -/
private lemma sum_indicatorR_eq (y : Fin L → Bool) :
    ∑ j : Fin L, indicatorR (y j) = (numRelevant (L := L) y : ℝ) := by
  simp [numRelevant, indicator, indicatorR]

/-- Bijection sum over `Fin (n+1)` excluding `0`: `∑_q g(swap(0,p)(q.succ)) = (∑ g) - g(p)`. -/
private lemma sum_swap_succ {n : ℕ} (g : Fin (n+2) → ℝ) (p : Fin (n+2)) :
    ∑ q : Fin (n+1), g ((Equiv.swap (0 : Fin (n+2)) p) q.succ) = (∑ k, g k) - g p := by
  have hbij := Fintype.sum_equiv (Equiv.swap (0 : Fin (n+2)) p) _ g (fun _ => rfl)
  rw [Fin.sum_univ_succ] at hbij; simp only [Equiv.swap_apply_left] at hbij; linarith

/-- Inner sum in the two-position formula: uses `sum_perm_apply_eq` + `sum_swap_succ`. -/
private lemma inner_sum_eq {n : ℕ} (g : Fin (n+2) → ℝ) (p : Fin (n+2)) (m : Fin (n+1)) :
    ∑ τ : Equiv.Perm (Fin (n+1)), g ((Equiv.swap (0 : Fin (n+2)) p) ((τ m).succ))
    = ↑n.factorial * ((∑ b, g b) - g p) := by
  simp_rw [show ∀ τ : Equiv.Perm (Fin (n+1)),
    g ((Equiv.swap (0 : Fin (n+2)) p) ((τ m).succ)) =
    (g ∘ (Equiv.swap (0 : Fin (n+2)) p) ∘ Fin.succ) (τ m) from fun _ => rfl,
    sum_perm_apply_eq _ m]
  congr 1; exact sum_swap_succ g p

/-- Two-position formula: `∑_σ f(σ i) * g(σ j) = n! * ((∑f)(∑g) - ∑fg)` for `i ≠ j` in `Fin(n+2)`. -/
private lemma sum_perm_pair {n : ℕ} (f g : Fin (n+2) → ℝ) (i j : Fin (n+2)) (hij : i ≠ j) :
    ∑ σ : Equiv.Perm (Fin (n+2)), f (σ i) * g (σ j)
    = ↑n.factorial * ((∑ a, f a) * (∑ b, g b) - ∑ a, f a * g a) := by
  rw [show ∑ σ, f (σ i) * g (σ j) = ∑ σ, f (σ 0) * g (σ ((Equiv.swap i 0) j)) from
    Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i 0)) _ _ (fun σ => by simp [Equiv.Perm.mul_apply])]
  set j' := (Equiv.swap i 0) j
  have hj'ne0 : j' ≠ (0 : Fin (n+2)) := by
    simp only [j']; intro heq
    exact hij ((Equiv.swap i 0).injective ((Equiv.swap_apply_left i 0).symm ▸ heq.symm))
  set m := j'.pred hj'ne0
  rw [show j' = m.succ from (Fin.succ_pred j' hj'ne0).symm,
    show ∑ σ : Equiv.Perm (Fin (n+2)), f (σ 0) * g (σ m.succ) =
      ∑ pe : Fin (n+2) × Equiv.Perm (Fin (n+1)),
        f pe.1 * g ((Equiv.swap 0 pe.1) (pe.2 m).succ) from by
      apply Fintype.sum_equiv Equiv.Perm.decomposeFin; intro σ; dsimp only
      have h0 : (Equiv.Perm.decomposeFin σ).1 = σ 0 := by simp [Equiv.Perm.decomposeFin]
      have hm : σ m.succ = (Equiv.swap 0 ((Equiv.Perm.decomposeFin σ).1))
          ((Equiv.Perm.decomposeFin σ).2 m).succ := by
        conv_lhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply σ]
        exact Equiv.Perm.decomposeFin_symm_apply_succ _ _ m
      rw [← h0, hm],
    Fintype.sum_prod_type]
  simp_rw [← mul_sum, inner_sum_eq]
  simp_rw [show ∀ x : Fin (n+2), f x * (↑n.factorial * ((∑ b, g b) - g x)) =
    ↑n.factorial * (f x * (∑ b, g b) - f x * g x) from fun _ => by ring,
    ← mul_sum, Finset.sum_sub_distrib]
  congr 1
  rw [show ∑ x : Fin (n+2), f x * ∑ b, g b = (∑ a, f a) * ∑ b, g b from by rw [sum_mul]]

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
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  simp only [uniformAvgOverPerms, prevalence]
  rw [sum_perm_apply_eq (fun j => indicatorR (y j)) i, sum_indicatorR_eq,
      Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]
  push_cast; field_simp

/-- Probability that two distinct ranks `i ≠ j` are both relevant under a random permutation. -/
lemma prob_both_relevant (y : Fin L → Bool) (i j : Fin L) (hij : i ≠ j) (hL : 1 < L) :
  uniformAvgOverPerms (fun π => indicatorR (y (π i)) * indicatorR (y (π j)))
    = (numRelevant (L:=L) y : ℝ) / (L : ℝ) * ((numRelevant (L:=L) y - 1 : ℝ) / (L - 1 : ℝ)) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := ⟨L - 2, by omega⟩
  simp only [uniformAvgOverPerms]
  rw [sum_perm_pair (fun a => indicatorR (y a)) (fun a => indicatorR (y a)) i j hij,
    sum_indicatorR_eq, show ∑ a : Fin (n+2), indicatorR (y a) * indicatorR (y a) =
      (numRelevant (L := n + 2) y : ℝ) from by
      simp_rw [show ∀ b : Bool, indicatorR b * indicatorR b = indicatorR b from
        fun b => by cases b <;> simp [indicatorR]]
      exact sum_indicatorR_eq y,
    Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ, Nat.factorial_succ]
  set M := (numRelevant (L := n + 2) y : ℝ)
  push_cast [Nat.succ_eq_add_one]
  have hnf : (↑n.factorial : ℝ) > 0 := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [div_mul_div_comm, div_eq_div_iff
    (mul_ne_zero (by linarith) (mul_ne_zero (by linarith) (ne_of_gt hnf)))
    (mul_ne_zero (by linarith) (by linarith))]
  ring

/-- The cumulative count `cumRelevantPerm y π (i+1)` equals
    `(∑ j ∈ indicesLT L i, indicator (y (π j))) + indicator (y (π i))`. -/
private lemma cumRelevantPerm_split (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) (i : Fin L) :
    (cumRelevantPerm (L:=L) y π (i.1 + 1) : ℝ) =
    (∑ j ∈ indicesLT L i.1, indicatorR (y (π j))) + indicatorR (y (π i)) := by
  simp only [cumRelevantPerm, indicesLT]
  rw [show univ.filter (fun j : Fin L => j.1 < i.1 + 1) =
    (univ.filter (fun j : Fin L => j.1 < i.1)) ∪ {i} from by
    ext x; simp only [mem_filter, mem_union, mem_singleton, mem_univ, true_and]
    constructor
    · intro h; by_cases hx : x = i
      · exact Or.inr hx
      · exact Or.inl (by omega)
    · rintro (h | rfl) <;> omega]
  rw [Finset.sum_union (by simp [Finset.disjoint_left]; intro x hx hxi; subst hxi; omega)]
  simp only [Finset.sum_singleton]
  push_cast
  have ind_cast : ∀ b : Bool, (indicator b : ℝ) = indicatorR b := by
    intro b; cases b <;> simp [indicator, indicatorR]
  simp_rw [ind_cast]

/-- Indicator squared is indicator for Boolean indicators. -/
private lemma indicatorR_sq (b : Bool) : indicatorR b * indicatorR b = indicatorR b := by
  cases b <;> simp [indicatorR]

/-- `indicatorR b * indicatorR b = indicatorR b` for composition. -/
private lemma indicatorR_mul_self_comm (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) (i : Fin L) :
    indicatorR (y (π i)) * indicatorR (y (π i)) = indicatorR (y (π i)) := indicatorR_sq _

/-- All elements in `indicesLT L i.1` are different from `i`. -/
private lemma indicesLT_ne_of_mem (i : Fin L) {j : Fin L} (hj : j ∈ indicesLT L i.1) : j ≠ i := by
  simp [indicesLT] at hj; exact Fin.ne_of_lt (by omega : j.1 < i.1)

theorem rankWeightedPrecAvg_closed_form (y : Fin L → Bool) (i : Fin L) (hL : 1 < L) :
  rankWeightedPrecAvg (L:=L) y i
    = ((i.1 : ℝ) / (i.1 + 1)) * prevalence (L:=L) y * (((numRelevant (L:=L) y - 1 : ℝ) / (L - 1 : ℝ)))
      + ((1 : ℝ) / (i.1 + 1)) * prevalence (L:=L) y := by
  classical
  have hL0 : 0 < L := by omega
  -- Step 1: Unfold definition and use rank1 = i.1 + 1 > 0
  have hk : 0 < i.1 + 1 := Nat.succ_pos _
  -- rankWeightedPrecAvg = E_π[1{y(π i)} * cumRelevantPerm(y,π,i+1) / (i+1)]
  -- Split cumRelevantPerm into sum over j < i and the i-th term
  have key : rankWeightedPrecAvg (L:=L) y i =
      uniformAvgOverPerms (fun π =>
        indicatorR (y (π i)) * (∑ j ∈ indicesLT L i.1, indicatorR (y (π j))) / (i.1 + 1 : ℝ)
        + indicatorR (y (π i)) / (i.1 + 1 : ℝ)) := by
    simp only [rankWeightedPrecAvg, uniformAvgOverPerms]
    congr 1
    apply Finset.sum_congr rfl; intro π _
    simp only [precAtPerm, rank1, hk, ↓reduceIte]
    split
    · rename_i hrel
      rw [cumRelevantPerm_split]
      have := indicatorR_sq (y (π i))
      simp [indicatorR, hrel]
      ring
    · rename_i hrel
      simp [indicatorR, hrel]
  rw [key]
  -- Step 2: Expand uniformAvgOverPerms and split into two terms
  simp only [uniformAvgOverPerms]
  -- Split the sum of (a+b) into sum of a + sum of b
  rw [show (∑ π : Equiv.Perm (Fin L),
      ((indicatorR (y (π i)) * (∑ j ∈ indicesLT L i.1, indicatorR (y (π j))) / (↑i.1 + 1) +
        indicatorR (y (π i)) / (↑i.1 + 1)))) =
    (∑ π : Equiv.Perm (Fin L),
      indicatorR (y (π i)) * (∑ j ∈ indicesLT L i.1, indicatorR (y (π j))) / (↑i.1 + 1)) +
    (∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) / (↑i.1 + 1)) from
    Finset.sum_add_distrib]
  set S1 := (∑ π : Equiv.Perm (Fin L),
    indicatorR (y (π i)) * (∑ j ∈ indicesLT L i.1, indicatorR (y (π j))) / (↑i.1 + 1))
  set S2 := (∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) / (↑i.1 + 1))
  set C := (Fintype.card (Equiv.Perm (Fin L)) : ℝ)
  -- Goal: (S1 + S2) / C = target. Split into S1/C + S2/C
  rw [add_div]
  -- Step 3: Handle S2/C (single-rank probability)
  have sum_div_pull : S2 =
      (∑ π : Equiv.Perm (Fin L), indicatorR (y (π i))) / (↑i.1 + 1 : ℝ) := by
    simp only [S2]; rw [Finset.sum_div]
  have term2 : S2 / C = (1 / (↑i.1 + 1)) * prevalence (L:=L) y := by
    rw [sum_div_pull]; simp only [C]; rw [div_div_comm']
    have h1 := prob_relevant_at_rank (L:=L) y i hL0
    simp only [uniformAvgOverPerms] at h1
    rw [h1]
    ring
  -- Step 4: Handle the first sum (two-rank probability)
  -- ∑_π indicator(y(π i)) * (∑_{j < i} indicator(y(π j))) = ∑_{j < i} ∑_π indicator(y(π i)) * indicator(y(π j))
  have term1 : S1 / C =
    (↑i.1 / (↑i.1 + 1)) * prevalence (L:=L) y * ((↑(numRelevant (L:=L) y) - 1) / (↑L - 1)) := by
    simp only [S1, C]
    -- Pull the constant 1/(i+1) out
    have pull_div : (∑ π : Equiv.Perm (Fin L),
        indicatorR (y (π i)) * (∑ j ∈ indicesLT L i.1, indicatorR (y (π j))) / (↑i.1 + 1)) =
      (∑ π : Equiv.Perm (Fin L),
        indicatorR (y (π i)) * (∑ j ∈ indicesLT L i.1, indicatorR (y (π j)))) / (↑i.1 + 1) := by
      rw [Finset.sum_div]
    rw [pull_div]
    -- Swap sums: ∑_π ∑_j = ∑_j ∑_π
    rw [show (∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) *
        ∑ j ∈ indicesLT L i.1, indicatorR (y (π j))) =
      ∑ j ∈ indicesLT L i.1, ∑ π : Equiv.Perm (Fin L),
        indicatorR (y (π i)) * indicatorR (y (π j)) from by
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]]
    -- Each inner sum is the two-rank probability
    -- ∑_j (prob_both_relevant) / (i+1) / card = ∑_j (M/L * (M-1)/(L-1)) / (i+1)
    -- = i * (M/L * (M-1)/(L-1)) / (i+1)
    rw [div_div_comm']
    -- Apply prob_both_relevant to each j
    have hpair : ∀ j ∈ indicesLT L i.1,
        (∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) * indicatorR (y (π j))) /
          (Fintype.card (Equiv.Perm (Fin L)) : ℝ) =
        (numRelevant (L:=L) y : ℝ) / (L : ℝ) * ((numRelevant (L:=L) y - 1 : ℝ) / (L - 1 : ℝ)) := by
      intro j hj
      exact prob_both_relevant (L:=L) y i j ((indicesLT_ne_of_mem i hj).symm) hL
    -- Sum of constants = card * constant
    rw [show (∑ j ∈ indicesLT L i.1,
        ∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) * indicatorR (y (π j))) /
        (Fintype.card (Equiv.Perm (Fin L)) : ℝ) =
      ∑ j ∈ indicesLT L i.1,
        (∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) * indicatorR (y (π j))) /
          (Fintype.card (Equiv.Perm (Fin L)) : ℝ) from
      by rw [Finset.sum_div]]
    rw [show ∑ j ∈ indicesLT L i.1,
        (∑ π : Equiv.Perm (Fin L), indicatorR (y (π i)) * indicatorR (y (π j))) /
          (Fintype.card (Equiv.Perm (Fin L)) : ℝ) =
      ∑ j ∈ indicesLT L i.1,
        ((numRelevant (L:=L) y : ℝ) / (L : ℝ) * ((numRelevant (L:=L) y - 1 : ℝ) / (L - 1 : ℝ))) from
      Finset.sum_congr rfl hpair]
    rw [Finset.sum_const]
    have hcard : (indicesLT L i.1).card = i.1 := by
      simp only [indicesLT]
      have : univ.filter (fun j : Fin L => j.1 < i.1) = Finset.Iio i := by
        ext x; simp only [mem_filter, mem_univ, true_and, Finset.mem_Iio]
        exact Fin.lt_iff_val_lt_val
      rw [this, Fin.card_Iio]
    rw [hcard]
    simp [nsmul_eq_mul, prevalence]
    ring
  rw [term1, term2]

/-- Finite identity: ∑_{i=0}^{L-1} 1/(i+1) = H_L. -/
lemma sum_fin_one_over (_hL : 0 < L) :
  (∑ i : Fin L, (1 : ℝ) / (i.1 + 1)) = harmonic L := by
  unfold harmonic
  rw [Finset.sum_range_succ']
  simp only [Nat.lt_irrefl, ↓reduceIte, add_zero, Nat.succ_pos', Nat.cast_add, Nat.cast_one]
  exact Fin.sum_univ_eq_sum_range (fun n => 1 / ((n : ℝ) + 1)) L

/-- Finite identity: ∑_{i=0}^{L-1} i/(i+1) = L - H_L. -/
lemma sum_fin_prev_over (hL : 0 < L) :
  (∑ i : Fin L, (i.1 : ℝ) / (i.1 + 1)) = (L : ℝ) - harmonic L := by
  have h1 : ∀ i : Fin L, (i.1 : ℝ) / (i.1 + 1) = 1 - 1 / (i.1 + 1) := by
    intro i; field_simp; ring
  simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul, mul_one, sum_fin_one_over hL]

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
  rw [hsum]
  -- Factor out constants from the sums
  have hL0 : (0 : ℕ) < L := by omega
  set p := prevalence (L:=L) y
  set q := ((numRelevant (L:=L) y - 1 : ℝ) / (L - 1 : ℝ))
  -- Split the sum of (a + b) into sum a + sum b
  rw [Finset.sum_add_distrib]
  -- Factor constants out of each sum
  have eq1 : ∑ i : Fin L, ((i.1 : ℝ) / ((i.1 : ℝ) + 1)) * p * q =
      p * q * ∑ i : Fin L, ((i.1 : ℝ) / ((i.1 : ℝ) + 1)) := by
    simp_rw [mul_comm ((_ : ℝ) / _ * p) q, mul_comm ((_ : ℝ) / _) p, ← Finset.mul_sum]; ring
  have eq2 : ∑ i : Fin L, (1 : ℝ) / ((i.1 : ℝ) + 1) * p =
      p * ∑ i : Fin L, (1 : ℝ) / ((i.1 : ℝ) + 1) := by
    simp_rw [mul_comm ((1 : ℝ) / _) p, ← Finset.mul_sum]
  rw [eq1, eq2, sum_fin_prev_over hL0, sum_fin_one_over hL0]

/-- Main closed form for expected AP under uniform random ranking.
The hypothesis `hM` is necessary: when `M = 0`, the AP is 0 by convention,
but the harmonic-number formula gives a nonzero value for `L > 1`. -/
theorem expected_ap_closed_form (y : Fin L → Bool) (hL : 1 < L)
    (hM : numRelevant (L:=L) y ≠ 0) :
  uniformAvgAP (L:=L) y
    = (1 / (L : ℝ)) * (((numRelevant (L:=L) y - 1 : ℝ) / (L - 1 : ℝ)) * ((L : ℝ) - harmonic L) + harmonic L) := by
  classical
  rw [uniformAvgAP_rank_decompose, dif_neg hM,
      sum_rankWeightedPrecAvg_closed_form (L:=L) y hL]
  simp only [prevalence]
  have hLne : (L : ℝ) ≠ 0 := by positivity
  have hMne : (numRelevant (L:=L) y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  field_simp

-- (Removed second placeholder exchangeability lemma.)

/-- Skeleton statement for the expected AP under uniformly random ranking.
This is a placeholder theorem to anchor the development. -/
theorem expected_ap_uniform_skeleton
  (_y : Fin L → Bool) (_hL : 0 < L) : True := by
  trivial

end ExpectedAp
