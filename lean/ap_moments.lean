import ap_distribution

/-!
# Moments of Average Precision under a uniformly random ranking

`expected_ap.lean` proves the closed form for `E[AP]`; `ap_distribution.lean`
identifies the whole law of `AP` with the uniform law on `M`-subsets of the
ranks.  This file adds the second moment.

The organising object is `W = M * AP = ∑_{i ≤ k} Z_i Z_k / k`, where `Z_k`
indicates that rank `k` is relevant, together with the "all `r` fixed ranks are
relevant" probabilities

  `m_r = C(M,r)/C(L,r) = (M)_r / (L)_r`   (`rankMoment` below, `0` when `r > M`).

In that language

  `E[W]   = m₁ H + m₂ (L - H)`
  `E[W²]  = m₁ H⁽²⁾ + m₂ (2H² + 3H - 5H⁽²⁾)
            + m₃ (2LH + 5L - 5H² - 9H + 7H⁽²⁾)
            + m₄ (L² - 2LH - 5L + 3H² + 6H - 3H⁽²⁾)`
  `Var(AP) = (E[W²] - E[W]²) / M²`

with `H = H_L` and `H⁽²⁾ = ∑_{k ≤ L} 1/k²`.

What is proved here:

* `numRelevant_le`, `eq_true_of_numRelevant_eq` — elementary counting facts.
* `sum_apPMF_numRelevant_eq_one` — normalisation of the PMF with no side goal.
* `uniformAPMass_eq_zero_of_not_rat` — the AP law is supported on `ℚ`.
* `uniformAvgOverPerms_comp_relevantRanks` — a general transfer lemma taking any
  statistic of the relevant-rank set from the permutation model to the uniform
  model on `M`-subsets, which is what makes the moments finite sums over
  `powersetCard`.
* `secondMomentAP_eq_sum_over_rankSets`, `varianceAP_eq_rat` — the second moment
  and variance as explicit finite rational expressions.
* `uniformAvgAP_eq_expectedW_div` — the *first* moment in the `m_r` language,
  i.e. `E[AP] = E[W]/M`, checked against `expected_ap_closed_form`.
* Edge cases `M = 0`, `M = L`, `M = 1` of the variance, all fully proved.

What is not proved: the general `E[W²]` identity itself.  See the final section.
-/

open Finset
open scoped BigOperators

namespace ExpectedAp

/-! ### Elementary facts about `numRelevant` -/

/-- At most every item can be relevant. -/
theorem numRelevant_le {L : ℕ} (y : Fin L → Bool) : numRelevant y ≤ L := by
  classical
  have h : ∑ i : Fin L, indicator (y i) ≤ ∑ _i : Fin L, 1 :=
    Finset.sum_le_sum (fun i _ => by cases y i <;> simp [indicator])
  simpa [numRelevant] using h

/-- `numRelevant` counts the relevant indices. -/
theorem numRelevant_eq_card_filter {L : ℕ} (y : Fin L → Bool) :
    numRelevant y = (Finset.univ.filter (fun i : Fin L => y i)).card := by
  classical
  simp [numRelevant, indicator, Finset.sum_boole]

/-- If every item is relevant then every entry of `y` is `true`. -/
theorem eq_true_of_numRelevant_eq {L : ℕ} (y : Fin L → Bool) (h : numRelevant y = L)
    (i : Fin L) : y i = true := by
  classical
  have hcard : (Finset.univ.filter (fun j : Fin L => y j)).card = Fintype.card (Fin L) := by
    simpa [← numRelevant_eq_card_filter] using h
  have huniv : (Finset.univ.filter (fun j : Fin L => y j)) = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  have hi : i ∈ Finset.univ.filter (fun j : Fin L => y j) := by
    rw [huniv]; exact Finset.mem_univ i
  simpa using hi

/-! ### Two gaps left open by `ap_distribution.lean` -/

/-- Normalisation of the AP law, instantiated at the number of relevant items of
an actual relevance vector, so no `M ≤ L` side condition survives. -/
theorem sum_apPMF_numRelevant_eq_one {L : ℕ} (y : Fin L → Bool) :
    ∑ a ∈ apSupport L (numRelevant y), apPMF L (numRelevant y) a = 1 :=
  sum_apPMF_eq_one (numRelevant_le y)

/-- AP is always rational, so the law puts no mass on an irrational point. -/
theorem uniformAPMass_eq_zero_of_not_rat {L : ℕ} (y : Fin L → Bool) (x : ℝ)
    (hx : ∀ a : ℚ, (a : ℝ) ≠ x) : uniformAPMass y x = 0 := by
  classical
  have hzero : ∀ π : Equiv.Perm (Fin L),
      (if apUnderPerm y π = x then (1 : ℝ) else 0) = 0 := by
    intro π
    rw [if_neg]
    rw [apUnderPerm_eq_averagePrecisionOfRanks]
    exact hx _
  simp [uniformAPMass, uniformAvgOverPerms, hzero]

/-- Packaged as a range statement. -/
theorem uniformAPMass_eq_zero_of_not_mem_range {L : ℕ} (y : Fin L → Bool) (x : ℝ)
    (hx : x ∉ Set.range ((↑) : ℚ → ℝ)) : uniformAPMass y x = 0 :=
  uniformAPMass_eq_zero_of_not_rat y x (fun a h => hx ⟨a, h⟩)

/-! ### From permutations to rank sets

`ap_distribution.lean` transfers the *distribution*; the moments need the same
transfer for an arbitrary statistic of the relevant-rank set. -/

/-- All fibres of `relevantRanks y` over equinumerous rank sets have equal size.
(Copied from `ap_distribution.lean`, where it is `private`.) -/
private theorem card_fiber_relevantRanks_eq {L : ℕ} (y : Fin L → Bool)
    {s t : Finset (Fin L)} (hst : s.card = t.card) :
    ((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
        (fun π => relevantRanks y π = s)).card =
      (Finset.univ.filter (fun π => relevantRanks y π = t)).card := by
  classical
  let e : (↥t) ≃ (↥s) := Finset.equivOfCardEq hst.symm
  let ρ : Equiv.Perm (Fin L) := e.extendSubtype
  have hρ (i : Fin L) : i ∈ t ↔ ρ i ∈ s := by
    constructor
    · exact fun hi => e.extendSubtype_mem i hi
    · intro hi
      by_contra hit
      exact e.extendSubtype_not_mem i hit hi
  have hpred (π : Equiv.Perm (Fin L)) :
      relevantRanks y π = s ↔
        relevantRanks y ((Equiv.mulRight ρ) π) = t := by
    constructor
    · intro hπ
      ext i
      simp only [relevantRanks, Finset.mem_filter, Finset.mem_univ, true_and]
      calc
        _ ↔ ρ i ∈ relevantRanks y π := by simp [relevantRanks]
        _ ↔ ρ i ∈ s := by rw [hπ]
        _ ↔ i ∈ t := (hρ i).symm
    · intro hπ
      ext i
      have hi := Finset.ext_iff.mp hπ (ρ.symm i)
      simpa [relevantRanks, Equiv.Perm.mul_apply, hρ] using hi
  let fiberEquiv : {π // relevantRanks y π = s} ≃
      {π // relevantRanks y π = t} :=
    (Equiv.mulRight ρ).subtypeEquiv hpred
  have hcard := Fintype.card_congr fiberEquiv
  calc
    _ = Fintype.card {π // relevantRanks y π = s} :=
      (Fintype.card_of_subtype _ (by simp)).symm
    _ = Fintype.card {π // relevantRanks y π = t} := hcard
    _ = _ := Fintype.card_of_subtype _ (by simp)

/-- **Transfer lemma.** Any statistic of the relevant-rank set has the same
uniform average over permutations as over the `C(L,M)` rank sets of size
`M = numRelevant y`. -/
theorem uniformAvgOverPerms_comp_relevantRanks {L : ℕ} (y : Fin L → Bool)
    (f : Finset (Fin L) → ℝ) :
    uniformAvgOverPerms (fun π => f (relevantRanks y π))
      = (∑ s ∈ (Finset.univ : Finset (Fin L)).powersetCard (numRelevant y), f s) /
          (Nat.choose L (numRelevant y) : ℝ) := by
  classical
  set ranks := (Finset.univ : Finset (Fin L)).powersetCard (numRelevant y) with hranks
  set s0 := relevantRanks y (Equiv.refl (Fin L)) with hs0
  set K := ((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
      (fun π => relevantRanks y π = s0)).card with hK
  have hfmem : ∀ π : Equiv.Perm (Fin L), relevantRanks y π ∈ ranks := by
    intro π
    simp [hranks, Finset.mem_powersetCard, card_relevantRanks]
  have hKpos : 0 < K := by
    rw [hK]
    exact Finset.card_pos.mpr ⟨Equiv.refl (Fin L), by simp [hs0]⟩
  have hfiber : ∀ s ∈ ranks, ((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
      (fun π => relevantRanks y π = s)).card = K := by
    intro s hs
    have hscard : s.card = numRelevant y := by
      simpa [hranks] using (Finset.mem_powersetCard.mp hs).2
    have hs0card : s0.card = numRelevant y := by simp [hs0, card_relevantRanks]
    rw [hK]
    exact card_fiber_relevantRanks_eq y (hscard.trans hs0card.symm)
  have hsum : ∑ π : Equiv.Perm (Fin L), f (relevantRanks y π)
      = (K : ℝ) * ∑ s ∈ ranks, f s := by
    rw [← Finset.sum_fiberwise_of_maps_to' (fun π _ => hfmem π) f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.sum_const, hfiber s hs, nsmul_eq_mul]
  have htotal : Fintype.card (Equiv.Perm (Fin L)) = ranks.card * K := by
    calc
      Fintype.card (Equiv.Perm (Fin L)) =
          (Finset.univ : Finset (Equiv.Perm (Fin L))).card := by simp
      _ = ∑ s ∈ ranks,
          ((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
            (fun π => relevantRanks y π = s)).card :=
        Finset.card_eq_sum_card_fiberwise (fun π _ => hfmem π)
      _ = ∑ _s ∈ ranks, K := Finset.sum_congr rfl hfiber
      _ = ranks.card * K := by simp
  have hrc : ranks.card = Nat.choose L (numRelevant y) := by simp [hranks]
  have hKne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hKpos.ne'
  simp only [uniformAvgOverPerms]
  rw [hsum, htotal]
  push_cast
  rw [mul_comm (ranks.card : ℝ) (K : ℝ), mul_div_mul_left _ _ hKne, hrc]

/-! ### The moments -/

/-- Second moment of AP under the uniform permutation model. -/
noncomputable def secondMomentAP {L : ℕ} (y : Fin L → Bool) : ℝ :=
  uniformAvgOverPerms (fun π => (apUnderPerm y π) ^ 2)

/-- Variance of AP under the uniform permutation model. -/
noncomputable def varianceAP {L : ℕ} (y : Fin L → Bool) : ℝ :=
  secondMomentAP y - (uniformAvgAP y) ^ 2

/-- `E[AP]` as a sum over rank sets. -/
theorem uniformAvgAP_eq_sum_over_rankSets {L : ℕ} (y : Fin L → Bool) :
    uniformAvgAP y =
      (∑ s ∈ (Finset.univ : Finset (Fin L)).powersetCard (numRelevant y),
          (averagePrecisionOfRanks s : ℝ)) / (Nat.choose L (numRelevant y) : ℝ) := by
  have h : uniformAvgAP y =
      uniformAvgOverPerms (fun π => ((averagePrecisionOfRanks (relevantRanks y π) : ℚ) : ℝ)) := by
    simp only [uniformAvgAP]
    exact congrArg uniformAvgOverPerms
      (funext fun π => apUnderPerm_eq_averagePrecisionOfRanks y π)
  rw [h]
  exact uniformAvgOverPerms_comp_relevantRanks y (fun s => (averagePrecisionOfRanks s : ℝ))

/-- `E[AP²]` as a sum over rank sets. -/
theorem secondMomentAP_eq_sum_over_rankSets {L : ℕ} (y : Fin L → Bool) :
    secondMomentAP y =
      (∑ s ∈ (Finset.univ : Finset (Fin L)).powersetCard (numRelevant y),
          (averagePrecisionOfRanks s : ℝ) ^ 2) / (Nat.choose L (numRelevant y) : ℝ) := by
  have h : secondMomentAP y =
      uniformAvgOverPerms
        (fun π => ((averagePrecisionOfRanks (relevantRanks y π) : ℚ) : ℝ) ^ 2) := by
    simp only [secondMomentAP]
    exact congrArg uniformAvgOverPerms
      (funext fun π => by rw [apUnderPerm_eq_averagePrecisionOfRanks])
  rw [h]
  exact uniformAvgOverPerms_comp_relevantRanks y (fun s => (averagePrecisionOfRanks s : ℝ) ^ 2)

/-- The variance is nonnegative (Cauchy-Schwarz on the uniform measure). -/
theorem varianceAP_nonneg {L : ℕ} (y : Fin L → Bool) : 0 ≤ varianceAP y := by
  have h := sum_div_card_sq_le_sum_sq_div_card
    (s := (Finset.univ : Finset (Equiv.Perm (Fin L)))) (f := fun π => apUnderPerm y π)
  rw [Finset.card_univ] at h
  simp only [varianceAP, secondMomentAP, uniformAvgAP, uniformAvgOverPerms]
  linarith

/-! ### Rational (computable) versions

The permutation model is noncomputable, but the rank-set model is a finite
rational computation, so the moments are decidable numbers. -/

/-- `E[AP]` over the `C(L,M)` rank sets, in `ℚ`. -/
def apMeanRat (L M : ℕ) : ℚ :=
  (∑ s ∈ (Finset.univ : Finset (Fin L)).powersetCard M, averagePrecisionOfRanks s) /
    (Nat.choose L M : ℚ)

/-- `E[AP²]` over the `C(L,M)` rank sets, in `ℚ`. -/
def apSecondMomentRat (L M : ℕ) : ℚ :=
  (∑ s ∈ (Finset.univ : Finset (Fin L)).powersetCard M, (averagePrecisionOfRanks s) ^ 2) /
    (Nat.choose L M : ℚ)

/-- `Var(AP)` over the `C(L,M)` rank sets, in `ℚ`. -/
def apVarianceRat (L M : ℕ) : ℚ := apSecondMomentRat L M - (apMeanRat L M) ^ 2

theorem uniformAvgAP_eq_rat {L : ℕ} (y : Fin L → Bool) :
    uniformAvgAP y = ((apMeanRat L (numRelevant y) : ℚ) : ℝ) := by
  rw [uniformAvgAP_eq_sum_over_rankSets, apMeanRat]
  push_cast
  ring

theorem secondMomentAP_eq_rat {L : ℕ} (y : Fin L → Bool) :
    secondMomentAP y = ((apSecondMomentRat L (numRelevant y) : ℚ) : ℝ) := by
  rw [secondMomentAP_eq_sum_over_rankSets, apSecondMomentRat]
  push_cast
  ring

theorem varianceAP_eq_rat {L : ℕ} (y : Fin L → Bool) :
    varianceAP y = ((apVarianceRat L (numRelevant y) : ℚ) : ℝ) := by
  rw [varianceAP, secondMomentAP_eq_rat, uniformAvgAP_eq_rat, apVarianceRat]
  push_cast
  ring

/-! ### The closed form -/

/-- `H⁽²⁾_L = ∑_{k=1}^L 1/k²`. -/
noncomputable def harmonic2 (L : ℕ) : ℝ :=
  (Finset.range (L + 1)).sum (fun k => if 0 < k then (1 : ℝ) / ((k : ℝ) ^ 2) else 0)

/-- `m_r = C(M,r)/C(L,r)`: the probability that `r` prescribed distinct ranks are
all relevant.  Equals the falling-factorial ratio `(M)_r/(L)_r` for `r ≤ M ≤ L`,
and is `0` for `r > M` because `Nat.choose M r = 0`. -/
noncomputable def rankMoment (L M r : ℕ) : ℝ :=
  (Nat.choose M r : ℝ) / (Nat.choose L r : ℝ)

/-- `E[W]` for `W = M · AP`. -/
noncomputable def expectedW (L M : ℕ) : ℝ :=
  rankMoment L M 1 * harmonic L + rankMoment L M 2 * ((L : ℝ) - harmonic L)

/-- `E[W²]` for `W = M · AP`. -/
noncomputable def expectedWSq (L M : ℕ) : ℝ :=
  rankMoment L M 1 * harmonic2 L
    + rankMoment L M 2 * (2 * harmonic L ^ 2 + 3 * harmonic L - 5 * harmonic2 L)
    + rankMoment L M 3 * (2 * (L : ℝ) * harmonic L + 5 * (L : ℝ) - 5 * harmonic L ^ 2
        - 9 * harmonic L + 7 * harmonic2 L)
    + rankMoment L M 4 * ((L : ℝ) ^ 2 - 2 * (L : ℝ) * harmonic L - 5 * (L : ℝ)
        + 3 * harmonic L ^ 2 + 6 * harmonic L - 3 * harmonic2 L)

/-- The claimed closed form `Var(AP) = (E[W²] - E[W]²)/M²`. -/
noncomputable def varianceAPClosedForm (L M : ℕ) : ℝ :=
  (expectedWSq L M - expectedW L M ^ 2) / (M : ℝ) ^ 2

/-- The first moment in the `m_r` language: `E[AP] = E[W]/M`.  This is the
already-proved `expected_ap_closed_form`, restated so that the `E[W]` half of
the moment package is verified rather than assumed. -/
theorem uniformAvgAP_eq_expectedW_div {L : ℕ} (y : Fin L → Bool) (hL : 1 < L)
    (hM : numRelevant y ≠ 0) :
    uniformAvgAP y = expectedW L (numRelevant y) / (numRelevant y : ℝ) := by
  rw [expected_ap_closed_form y hL hM]
  simp only [expectedW, rankMoment, Nat.choose_one_right, Nat.cast_choose_two]
  have hLne : (L : ℝ) ≠ 0 := by positivity
  have hL1 : (L : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    linarith
  have hMne : ((numRelevant y : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  field_simp
  ring

/-! ### Edge cases of the variance, fully proved -/

/-- No relevant items: AP is `0` by convention, so the variance is `0`. -/
theorem varianceAP_eq_zero_of_numRelevant_eq_zero {L : ℕ} (y : Fin L → Bool)
    (h : numRelevant y = 0) : varianceAP y = 0 := by
  simp [varianceAP, secondMomentAP, uniformAvgAP, uniformAvgOverPerms, apUnderPerm, h]

/-- Every item relevant: AP is identically `1`. -/
theorem apUnderPerm_eq_one_of_numRelevant_eq {L : ℕ} (y : Fin L → Bool) (hL : 0 < L)
    (h : numRelevant y = L) (π : Equiv.Perm (Fin L)) : apUnderPerm y π = 1 := by
  classical
  have hy : ∀ i : Fin L, y i = true := eq_true_of_numRelevant_eq y h
  have hcard : ∀ i : Fin L, (indicesLT L (i.1 + 1)).card = i.1 + 1 := by
    intro i
    have hset : indicesLT L (i.1 + 1) = Finset.Iic i := by
      apply Finset.ext
      intro x
      simp only [indicesLT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic,
        Fin.le_def, Nat.lt_succ_iff]
    rw [hset, Fin.card_Iic]
  have hprec : ∀ i : Fin L, precAtPerm y π (rank1 i) = 1 := by
    intro i
    have hcum : cumRelevantPerm y π (i.1 + 1) = i.1 + 1 := by
      simp only [cumRelevantPerm, hy, indicator, if_true, Finset.sum_const,
        smul_eq_mul, mul_one]
      exact hcard i
    have hne : ((i.1 : ℝ) + 1) ≠ 0 := by positivity
    simp only [precAtPerm, rank1, Nat.succ_pos, if_true, hcum]
    push_cast
    exact div_self hne
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  simp only [apUnderPerm, h, hL.ne', if_false, hy, if_true, hprec]
  simp [hLne]

/-- Every item relevant: the variance is `0`. -/
theorem varianceAP_eq_zero_of_numRelevant_eq {L : ℕ} (y : Fin L → Bool) (hL : 0 < L)
    (h : numRelevant y = L) : varianceAP y = 0 := by
  have hcard : (Fintype.card (Equiv.Perm (Fin L)) : ℝ) ≠ 0 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_pos L).ne'
  have h1 : uniformAvgAP y = 1 := by
    simp only [uniformAvgAP, uniformAvgOverPerms,
      apUnderPerm_eq_one_of_numRelevant_eq y hL h]
    simp [hcard]
  have h2 : secondMomentAP y = 1 := by
    simp only [secondMomentAP, uniformAvgOverPerms,
      apUnderPerm_eq_one_of_numRelevant_eq y hL h, one_pow]
    simp [hcard]
  simp [varianceAP, h1, h2]

/-- `∑_{i<L} 1/(i+1)² = H⁽²⁾_L`. -/
lemma sum_fin_one_over_sq (L : ℕ) :
    (∑ i : Fin L, (1 : ℝ) / ((i.1 : ℝ) + 1) ^ 2) = harmonic2 L := by
  unfold harmonic2
  rw [Finset.sum_range_succ']
  simp only [Nat.lt_irrefl, ↓reduceIte, add_zero, Nat.succ_pos', Nat.cast_add, Nat.cast_one]
  exact Fin.sum_univ_eq_sum_range (fun n => 1 / (((n : ℝ) + 1) ^ 2)) L

/-- AP of a single relevant rank `i` (0-indexed) is `1/(i+1)`. -/
lemma averagePrecisionOfRanks_singleton {L : ℕ} (i : Fin L) :
    averagePrecisionOfRanks ({i} : Finset (Fin L)) = 1 / ((i.1 : ℚ) + 1) := by
  classical
  simp [averagePrecisionOfRanks, Finset.filter_singleton]

/-- Sums over singletons. -/
lemma sum_powersetCard_one {L : ℕ} (f : Finset (Fin L) → ℝ) :
    ∑ s ∈ (Finset.univ : Finset (Fin L)).powersetCard 1, f s = ∑ i : Fin L, f {i} := by
  rw [Finset.powersetCard_one, Finset.sum_map]
  rfl

/-- Exactly one relevant item: `E[AP] = H_L / L`. -/
theorem uniformAvgAP_of_numRelevant_eq_one {L : ℕ} (y : Fin L → Bool)
    (h : numRelevant y = 1) : uniformAvgAP y = harmonic L / (L : ℝ) := by
  have hL : 0 < L := lt_of_lt_of_le Nat.zero_lt_one (h ▸ numRelevant_le y)
  rw [uniformAvgAP_eq_sum_over_rankSets, h, Nat.choose_one_right, sum_powersetCard_one]
  congr 1
  rw [← sum_fin_one_over hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [averagePrecisionOfRanks_singleton]
  push_cast
  ring

/-- Exactly one relevant item: `E[AP²] = H⁽²⁾_L / L`. -/
theorem secondMomentAP_of_numRelevant_eq_one {L : ℕ} (y : Fin L → Bool)
    (h : numRelevant y = 1) : secondMomentAP y = harmonic2 L / (L : ℝ) := by
  rw [secondMomentAP_eq_sum_over_rankSets, h, Nat.choose_one_right, sum_powersetCard_one]
  congr 1
  rw [← sum_fin_one_over_sq L]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [averagePrecisionOfRanks_singleton]
  push_cast
  rw [div_pow, one_pow]

/-- Exactly one relevant item: `Var(AP) = H⁽²⁾_L/L - (H_L/L)²`, matching the
`M = 1` edge case of the closed form. -/
theorem varianceAP_of_numRelevant_eq_one {L : ℕ} (y : Fin L → Bool)
    (h : numRelevant y = 1) :
    varianceAP y = harmonic2 L / (L : ℝ) - (harmonic L / (L : ℝ)) ^ 2 := by
  rw [varianceAP, secondMomentAP_of_numRelevant_eq_one y h,
    uniformAvgAP_of_numRelevant_eq_one y h]

/-! ### The closed form is correct at the edge cases

The cases `M = 0`, `M = 1` and `M = L` are proved directly here by evaluating `varianceAPClosedForm` symbolically.
These proofs include `M = 0` and `L = 1`, which lie outside the hypotheses of `varianceAP_closed_form` at the end of the file. -/

/-- At `M = 0` the closed form degenerates to `0` (division by `M² = 0`). -/
theorem varianceAPClosedForm_zero (L : ℕ) : varianceAPClosedForm L 0 = 0 := by
  simp [varianceAPClosedForm]

/-- At `M = 1` the closed form is `H⁽²⁾_L/L - (H_L/L)²`. -/
theorem varianceAPClosedForm_one (L : ℕ) :
    varianceAPClosedForm L 1 = harmonic2 L / (L : ℝ) - (harmonic L / (L : ℝ)) ^ 2 := by
  have c1 : Nat.choose 1 1 = 1 := rfl
  have c2 : Nat.choose 1 2 = 0 := rfl
  have c3 : Nat.choose 1 3 = 0 := rfl
  have c4 : Nat.choose 1 4 = 0 := rfl
  simp only [varianceAPClosedForm, expectedW, expectedWSq, rankMoment, c1, c2, c3, c4,
    Nat.choose_one_right, Nat.cast_zero, Nat.cast_one, zero_div, zero_mul, add_zero,
    one_pow, div_one]
  ring

/-- At `M = L` the closed form is `0`: `E[W] = L` and `E[W²] = L²`. -/
theorem varianceAPClosedForm_self (L : ℕ) : varianceAPClosedForm L L = 0 := by
  rcases lt_or_ge L 4 with hlt | hge
  · interval_cases L <;>
      norm_num [varianceAPClosedForm, expectedW, expectedWSq, rankMoment, harmonic, harmonic2,
        Finset.sum_range_succ]
  · have hne : ∀ r, r ≤ L → (Nat.choose L r : ℝ) ≠ 0 := fun r hr =>
      Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne'
    have m1 : rankMoment L L 1 = 1 := div_self (hne 1 (by omega))
    have m2 : rankMoment L L 2 = 1 := div_self (hne 2 (by omega))
    have m3 : rankMoment L L 3 = 1 := div_self (hne 3 (by omega))
    have m4 : rankMoment L L 4 = 1 := div_self (hne 4 (by omega))
    have hnum : expectedWSq L L - expectedW L L ^ 2 = 0 := by
      simp only [expectedW, expectedWSq, m1, m2, m3, m4, one_mul]
      ring
    rw [varianceAPClosedForm, hnum, zero_div]

/-- The general closed form, proved for `M = 0`. -/
theorem varianceAP_closed_form_of_numRelevant_eq_zero {L : ℕ} (y : Fin L → Bool)
    (h : numRelevant y = 0) : varianceAP y = varianceAPClosedForm L (numRelevant y) := by
  rw [h, varianceAPClosedForm_zero, varianceAP_eq_zero_of_numRelevant_eq_zero y h]

/-- The general closed form, proved for `M = 1`. -/
theorem varianceAP_closed_form_of_numRelevant_eq_one {L : ℕ} (y : Fin L → Bool)
    (h : numRelevant y = 1) : varianceAP y = varianceAPClosedForm L (numRelevant y) := by
  rw [h, varianceAPClosedForm_one, varianceAP_of_numRelevant_eq_one y h]

/-- The general closed form, proved for `M = L`. -/
theorem varianceAP_closed_form_of_numRelevant_eq_card {L : ℕ} (y : Fin L → Bool) (hL : 0 < L)
    (h : numRelevant y = L) : varianceAP y = varianceAPClosedForm L (numRelevant y) := by
  rw [h, varianceAPClosedForm_self, varianceAP_eq_zero_of_numRelevant_eq y hL h]

/-! ### Numerical checks of the closed form

`native_decide`, so these carry `Lean.ofReduceBool`; they are stated as
anonymous `example`s so no named theorem in this file depends on that axiom.
They compare the closed form against exhaustive enumeration of all `C(L,M)`
rank sets, in exact rational arithmetic. -/

/-- Rational mirror of `harmonic`. -/
def harmonicRat (L : ℕ) : ℚ :=
  (Finset.range (L + 1)).sum (fun k => if 0 < k then (1 : ℚ) / (k : ℚ) else 0)

/-- Rational mirror of `harmonic2`. -/
def harmonic2Rat (L : ℕ) : ℚ :=
  (Finset.range (L + 1)).sum (fun k => if 0 < k then (1 : ℚ) / ((k : ℚ) ^ 2) else 0)

/-- Rational mirror of `rankMoment`. -/
def rankMomentRat (L M r : ℕ) : ℚ := (Nat.choose M r : ℚ) / (Nat.choose L r : ℚ)

/-- Rational mirror of `varianceAPClosedForm`. -/
def varianceAPClosedFormRat (L M : ℕ) : ℚ :=
  let H := harmonicRat L
  let H2 := harmonic2Rat L
  let m := fun r => rankMomentRat L M r
  let eW := m 1 * H + m 2 * ((L : ℚ) - H)
  let eW2 := m 1 * H2
    + m 2 * (2 * H ^ 2 + 3 * H - 5 * H2)
    + m 3 * (2 * (L : ℚ) * H + 5 * (L : ℚ) - 5 * H ^ 2 - 9 * H + 7 * H2)
    + m 4 * ((L : ℚ) ^ 2 - 2 * (L : ℚ) * H - 5 * (L : ℚ) + 3 * H ^ 2 + 6 * H - 3 * H2)
  (eW2 - eW ^ 2) / ((M : ℚ) ^ 2)

example : apVarianceRat 1 1 = varianceAPClosedFormRat 1 1 := by native_decide
example : apVarianceRat 2 1 = varianceAPClosedFormRat 2 1 := by native_decide
example : apVarianceRat 2 2 = varianceAPClosedFormRat 2 2 := by native_decide
example : apVarianceRat 3 2 = varianceAPClosedFormRat 3 2 := by native_decide
example : apVarianceRat 4 2 = varianceAPClosedFormRat 4 2 := by native_decide
example : apVarianceRat 5 3 = varianceAPClosedFormRat 5 3 := by native_decide
example : apVarianceRat 6 3 = varianceAPClosedFormRat 6 3 := by native_decide
example : apVarianceRat 7 4 = varianceAPClosedFormRat 7 4 := by native_decide
example : apVarianceRat 8 5 = varianceAPClosedFormRat 8 5 := by native_decide
example : apVarianceRat 9 1 = varianceAPClosedFormRat 9 1 := by native_decide
example : apVarianceRat 10 6 = varianceAPClosedFormRat 10 6 := by native_decide
example : apVarianceRat 10 10 = varianceAPClosedFormRat 10 10 := by native_decide

/-- Concrete value: `Var(AP)` for `L = 6`, `M = 3`. -/
example : apVarianceRat 6 3 = 32393 / 1080000 := by native_decide

/-- End to end: the permutation-model variance of a concrete relevance vector is
a concrete rational number. -/
example (y : Fin 6 → Bool) (h : numRelevant y = 3) :
    varianceAP y = ((32393 / 1080000 : ℚ) : ℝ) := by
  have hval : apVarianceRat 6 3 = 32393 / 1080000 := by native_decide
  rw [varianceAP_eq_rat, h, hval]


/-! ### V1: harmonic-number bridge lemmas -/

lemma harmonic_succ (L : ℕ) : harmonic (L + 1) = harmonic L + 1 / ((L : ℝ) + 1) := by
  unfold harmonic
  rw [Finset.sum_range_succ]
  simp

lemma harmonic2_succ (L : ℕ) :
    harmonic2 (L + 1) = harmonic2 L + 1 / ((L : ℝ) + 1) ^ 2 := by
  unfold harmonic2
  rw [Finset.sum_range_succ]
  simp

lemma sum_range_one_div (L : ℕ) :
    ∑ t ∈ Finset.range L, (1 : ℝ) / ((t : ℝ) + 1) = harmonic L := by
  unfold harmonic
  rw [Finset.sum_range_succ']
  simp

lemma sum_range_one_div_sq (L : ℕ) :
    ∑ t ∈ Finset.range L, (1 : ℝ) / ((t : ℝ) + 1) ^ 2 = harmonic2 L := by
  unfold harmonic2
  rw [Finset.sum_range_succ']
  simp

lemma sum_range_self_div (L : ℕ) :
    ∑ t ∈ Finset.range L, (t : ℝ) / ((t : ℝ) + 1) = (L : ℝ) - harmonic L := by
  have h : ∀ t : ℕ, (t : ℝ) / ((t : ℝ) + 1) = 1 - 1 / ((t : ℝ) + 1) := by
    intro t
    have : ((t : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, sum_range_one_div]

lemma sum_range_self_div_sq (L : ℕ) :
    ∑ t ∈ Finset.range L, (t : ℝ) / ((t : ℝ) + 1) ^ 2 = harmonic L - harmonic2 L := by
  have h : ∀ t : ℕ, (t : ℝ) / ((t : ℝ) + 1) ^ 2
      = 1 / ((t : ℝ) + 1) - 1 / ((t : ℝ) + 1) ^ 2 := by
    intro t
    have : ((t : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [h, Finset.sum_sub_distrib, sum_range_one_div, sum_range_one_div_sq]

lemma sum_range_mul_sub_one_div_sq (L : ℕ) :
    ∑ t ∈ Finset.range L, (t : ℝ) * ((t : ℝ) - 1) / ((t : ℝ) + 1) ^ 2
      = (L : ℝ) - 3 * harmonic L + 2 * harmonic2 L := by
  have h : ∀ t : ℕ, (t : ℝ) * ((t : ℝ) - 1) / ((t : ℝ) + 1) ^ 2
      = 1 - 3 * (1 / ((t : ℝ) + 1)) + 2 * (1 / ((t : ℝ) + 1) ^ 2) := by
    intro t
    have : ((t : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    sum_range_one_div, sum_range_one_div_sq]

/-! ### V2: the inductive double-sum identity -/

lemma sum_range_harmonic_div (L : ℕ) :
    ∑ t ∈ Finset.range L, harmonic t / ((t : ℝ) + 1)
      = (harmonic L ^ 2 - harmonic2 L) / 2 := by
  induction L with
  | zero => simp [harmonic, harmonic2]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ, harmonic2_succ]
      have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring

/-! ### V3: superset counting -/

/-- The number of `M`-subsets of `Fin L` containing a fixed set `T` of size at
most `M` is `C(L - |T|, M - |T|)`. -/
lemma card_powersetCard_filter_superset {L M : ℕ} (T : Finset (Fin L)) (hTM : T.card ≤ M) :
    (((Finset.univ : Finset (Fin L)).powersetCard M).filter (fun s => T ⊆ s)).card
      = Nat.choose (L - T.card) (M - T.card) := by
  classical
  rw [show Nat.choose (L - T.card) (M - T.card)
      = (((Finset.univ : Finset (Fin L)) \ T).powersetCard (M - T.card)).card by
    rw [Finset.card_powersetCard, Finset.card_sdiff (Finset.subset_univ T),
      Finset.card_univ, Fintype.card_fin]]
  apply Finset.card_bij' (fun s _ => s \ T) (fun u _ => u ∪ T)
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨_, hcard⟩, hTs⟩ := hs
    simp only [Finset.mem_powersetCard]
    exact ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ s) (Finset.Subset.refl T),
      by rw [Finset.card_sdiff hTs, hcard]⟩
  · intro u hu
    simp only [Finset.mem_powersetCard] at hu
    obtain ⟨huT, hucard⟩ := hu
    have hdisj : Disjoint u T := by
      refine Finset.disjoint_left.mpr fun x hxu hxT => ?_
      exact (Finset.mem_sdiff.mp (huT hxu)).2 hxT
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_union_right⟩
    rw [Finset.card_union_of_disjoint hdisj, hucard]
    omega
  · intro s hs
    simp only [Finset.mem_filter] at hs
    exact Finset.sdiff_union_of_subset hs.2
  · intro u hu
    simp only [Finset.mem_powersetCard] at hu
    have hdisj : Disjoint u T := by
      refine Finset.disjoint_left.mpr fun x hxu hxT => ?_
      exact (Finset.mem_sdiff.mp (hu.1 hxu)).2 hxT
    exact Finset.union_sdiff_cancel_right hdisj

/-! ### V4: inclusion probability -/

/-- `P(T ⊆ s)` for a uniformly random `M`-subset `s` of `Fin L` equals
`rankMoment L M |T|`; both sides vanish when `|T| > M`. -/
lemma sum_ite_subset_powersetCard_div_choose {L M : ℕ} (hML : M ≤ L) (T : Finset (Fin L)) :
    (∑ s ∈ (Finset.univ : Finset (Fin L)).powersetCard M, if T ⊆ s then (1 : ℝ) else 0)
        / (Nat.choose L M : ℝ)
      = rankMoment L M T.card := by
  classical
  rw [Finset.sum_boole]
  by_cases hTM : T.card ≤ M
  · rw [card_powersetCard_filter_superset T hTM, rankMoment]
    have hTL : T.card ≤ L := le_trans hTM hML
    have hLM : (Nat.choose L M : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos hML).ne'
    have hLT : (Nat.choose L T.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos hTL).ne'
    rw [div_eq_div_iff hLM hLT]
    have hnat : (L - T.card).choose (M - T.card) * L.choose T.card
        = M.choose T.card * L.choose M := by
      calc (L - T.card).choose (M - T.card) * L.choose T.card
          = L.choose T.card * (L - T.card).choose (M - T.card) := Nat.mul_comm _ _
        _ = L.choose M * M.choose T.card := (Nat.choose_mul hML hTM).symm
        _ = M.choose T.card * L.choose M := Nat.mul_comm _ _
    exact_mod_cast hnat
  · push_neg at hTM
    have hempty : ((Finset.univ : Finset (Fin L)).powersetCard M).filter
        (fun s => T ⊆ s) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun s hs => ?_
      intro hTs
      have := Finset.card_le_card hTs
      rw [(Finset.mem_powersetCard.mp hs).2] at this
      omega
    rw [hempty, rankMoment, Nat.choose_eq_zero_of_lt hTM]
    simp

/-! ### V5: `M · AP` as a pair sum over ranks -/

lemma mul_averagePrecisionOfRanks_eq_sum_Iic {L M : ℕ} (s : Finset (Fin L))
    (hs : s.card = M) (hM : M ≠ 0) :
    (M : ℝ) * (averagePrecisionOfRanks s : ℝ)
      = ∑ i : Fin L, ∑ j ∈ Finset.Iic i,
          (if j ∈ s ∧ i ∈ s then (1 : ℝ) else 0) / ((i.1 : ℝ) + 1) := by
  have hcard : ¬ s.card = 0 := by rw [hs]; exact hM
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hinner : ∀ i : Fin L,
      (∑ j ∈ Finset.Iic i, (if j ∈ s ∧ i ∈ s then (1 : ℝ) else 0) / ((i.1 : ℝ) + 1))
        = (if i ∈ s then ((s.filter (fun j => j ≤ i)).card : ℝ) / ((i.1 : ℝ) + 1) else 0) := by
    intro i
    by_cases hi : i ∈ s
    · rw [if_pos hi, ← Finset.sum_div]
      congr 1
      simp only [hi, and_true]
      rw [Finset.sum_boole]
      norm_cast
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_Iic]
      tauto
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => hinner i), Fintype.sum_ite_mem]
  unfold averagePrecisionOfRanks
  rw [if_neg hcard]
  push_cast
  rw [hs, ← mul_div_assoc, mul_div_cancel_left₀ _ hMne]

/-! ### V6: second moment as a quadruple `rankMoment` sum -/

lemma sum_apSq_div_choose_eq_quad {L M : ℕ} (hM : M ≠ 0) (hML : M ≤ L) :
    (M : ℝ) ^ 2 * ((∑ s ∈ (Finset.univ : Finset (Fin L)).powersetCard M,
          (averagePrecisionOfRanks s : ℝ) ^ 2) / (Nat.choose L M : ℝ))
      = ∑ i : Fin L, ∑ j ∈ Finset.Iic i, ∑ i' : Fin L, ∑ j' ∈ Finset.Iic i',
          rankMoment L M ({j, i, j', i'} : Finset (Fin L)).card
            / (((i.1 : ℝ) + 1) * ((i'.1 : ℝ) + 1)) := by
  classical
  -- Step 1: per rank set, expand `(M * AP)²` into the quadruple indicator sum.
  have hstep2 : ∀ s ∈ (Finset.univ : Finset (Fin L)).powersetCard M,
      ((M : ℝ) * (averagePrecisionOfRanks s : ℝ)) ^ 2
        = ∑ i : Fin L, ∑ j ∈ Finset.Iic i, ∑ i' : Fin L, ∑ j' ∈ Finset.Iic i',
            (if ({j, i, j', i'} : Finset (Fin L)) ⊆ s then (1 : ℝ) else 0)
              / (((i.1 : ℝ) + 1) * ((i'.1 : ℝ) + 1)) := by
    intro s hsP
    have hscard : s.card = M := (Finset.mem_powersetCard.mp hsP).2
    have hfuse : ∀ a b c d : Fin L,
        (if a ∈ s ∧ b ∈ s then (1 : ℝ) else 0) * (if c ∈ s ∧ d ∈ s then (1 : ℝ) else 0)
          = if ({a, b, c, d} : Finset (Fin L)) ⊆ s then (1 : ℝ) else 0 := by
      intro a b c d
      have hiff : (({a, b, c, d} : Finset (Fin L)) ⊆ s)
          ↔ ((a ∈ s ∧ b ∈ s) ∧ (c ∈ s ∧ d ∈ s)) := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        tauto
      by_cases h1 : a ∈ s ∧ b ∈ s <;> by_cases h2 : c ∈ s ∧ d ∈ s <;>
        simp [h1, h2, hiff]
    rw [mul_averagePrecisionOfRanks_eq_sum_Iic s hscard hM, pow_two]
    simp_rw [Finset.sum_mul_sum, div_mul_div_comm, hfuse]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  -- Step 2: assemble, moving the rank-set average to the innermost position.
  rw [← mul_div_assoc, Finset.mul_sum]
  simp_rw [← mul_pow]
  rw [Finset.sum_congr rfl hstep2]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [← Finset.sum_div, div_right_comm,
    sum_ite_subset_powersetCard_div_choose hML ({j, i, j', i'} : Finset (Fin L))]

/-! ### V7: `sigSum` and the coincidence-class split -/

/-- `Sig_k`: the sum of `1/((i+1)(i'+1))` over 0-indexed rank quadruples
`(i, j ≤ i, i', j' ≤ i')` whose index set `{j, i, j', i'}` has exactly `k`
distinct elements. -/
noncomputable def sigSum (L k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range (i + 1),
    ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range (i' + 1),
      if ({j, i, j', i'} : Finset ℕ).card = k then
        (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0

/-- Cardinality of a four-element insert chain transports along `Fin.val`. -/
lemma card_quad_val {L : ℕ} (a b c d : Fin L) :
    ({a, b, c, d} : Finset (Fin L)).card = ({a.1, b.1, c.1, d.1} : Finset ℕ).card := by
  have h : ({a.1, b.1, c.1, d.1} : Finset ℕ)
      = ({a, b, c, d} : Finset (Fin L)).image Fin.val := by
    simp [Finset.image_insert]
  rw [h, Finset.card_image_of_injective _ Fin.val_injective]

/-- Reindex a sum over `Finset.Iic i` in `Fin L` as a sum over
`Finset.range (i.1 + 1)` in `ℕ`. -/
private lemma sum_Iic_fin {L : ℕ} (i : Fin L) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.Iic i, f j.1) = ∑ t ∈ Finset.range (i.1 + 1), f t := by
  have h1 : (Finset.Iic i) = Finset.univ.filter (fun j : Fin L => j.1 < i.1 + 1) := by
    refine Finset.ext fun j => ?_
    simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.le_def, Nat.lt_succ_iff]
  have h2 : (Finset.range L).filter (fun t => t < i.1 + 1) = Finset.range (i.1 + 1) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun ht => ht.2
    · intro ht
      exact ⟨lt_of_lt_of_le ht (Nat.succ_le_of_lt i.isLt), ht⟩
  rw [h1, Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun t => if t < i.1 + 1 then f t else 0) L,
    ← Finset.sum_filter, h2]

/-- Reindex the paired sum `∑ i : Fin L, ∑ j ≤ i` as nested `range` sums. -/
private lemma sum_fin_Iic_eq {L : ℕ} (g : ℕ → ℕ → ℝ) :
    (∑ i : Fin L, ∑ j ∈ Finset.Iic i, g j.1 i.1)
      = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range (i + 1), g j i := by
  calc (∑ i : Fin L, ∑ j ∈ Finset.Iic i, g j.1 i.1)
      = ∑ i : Fin L, ∑ t ∈ Finset.range (i.1 + 1), g t i.1 :=
        Finset.sum_congr rfl (fun i _ => sum_Iic_fin i (fun t => g t i.1))
    _ = ∑ i ∈ Finset.range L, ∑ t ∈ Finset.range (i + 1), g t i :=
        Fin.sum_univ_eq_sum_range (fun u => ∑ t ∈ Finset.range (u + 1), g t u) L

/-- Reindex the full quadruple `Fin`/`Iic` sum as nested `range` sums. -/
private lemma quad_reindex {L : ℕ} (g : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ i : Fin L, ∑ j ∈ Finset.Iic i, ∑ i' : Fin L, ∑ j' ∈ Finset.Iic i',
        g j.1 i.1 j'.1 i'.1)
      = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range (i + 1),
          ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range (i' + 1), g j i j' i' := by
  calc (∑ i : Fin L, ∑ j ∈ Finset.Iic i, ∑ i' : Fin L, ∑ j' ∈ Finset.Iic i',
        g j.1 i.1 j'.1 i'.1)
      = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range (i + 1),
          ∑ i' : Fin L, ∑ j' ∈ Finset.Iic i', g j i j'.1 i'.1 :=
        sum_fin_Iic_eq (fun a b => ∑ i' : Fin L, ∑ j' ∈ Finset.Iic i', g a b j'.1 i'.1)
    _ = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range (i + 1),
          ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range (i' + 1), g j i j' i' := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        exact sum_fin_Iic_eq (fun a b => g j i a b)

private lemma quad_card_pos (a b c d : ℕ) : 1 ≤ ({a, b, c, d} : Finset ℕ).card := by
  have ha : a ∈ ({a, b, c, d} : Finset ℕ) := by simp
  exact Finset.card_pos.mpr ⟨a, ha⟩

private lemma quad_card_le (a b c d : ℕ) : ({a, b, c, d} : Finset ℕ).card ≤ 4 := by
  have h1 := Finset.card_insert_le a ({b, c, d} : Finset ℕ)
  have h2 := Finset.card_insert_le b ({c, d} : Finset ℕ)
  have h3 := Finset.card_insert_le c ({d} : Finset ℕ)
  simp only [Finset.card_singleton] at h3
  omega

/-- Pointwise split of `rankMoment L M c / d` by the value of `c ∈ {1,2,3,4}`. -/
private lemma rankMoment_div_split (L M c : ℕ) (h1 : 1 ≤ c) (h4 : c ≤ 4) (d : ℝ) :
    rankMoment L M c / d
      = rankMoment L M 1 * (if c = 1 then (1 : ℝ) / d else 0)
        + rankMoment L M 2 * (if c = 2 then (1 : ℝ) / d else 0)
        + rankMoment L M 3 * (if c = 3 then (1 : ℝ) / d else 0)
        + rankMoment L M 4 * (if c = 4 then (1 : ℝ) / d else 0) := by
  interval_cases c <;> simp [div_eq_mul_inv]

/-- The quadruple sum of `rankMoment` at the coincidence-class cardinality,
weighted by `1/((i+1)(i'+1))`, splits into the four `sigSum` blocks. -/
lemma quad_rankMoment_eq_sigSum_comb (L M : ℕ) :
    (∑ i : Fin L, ∑ j ∈ Finset.Iic i, ∑ i' : Fin L, ∑ j' ∈ Finset.Iic i',
        rankMoment L M ({j, i, j', i'} : Finset (Fin L)).card
          / (((i.1 : ℝ) + 1) * ((i'.1 : ℝ) + 1)))
      = rankMoment L M 1 * sigSum L 1 + rankMoment L M 2 * sigSum L 2
          + rankMoment L M 3 * sigSum L 3 + rankMoment L M 4 * sigSum L 4 := by
  have hA : (∑ i : Fin L, ∑ j ∈ Finset.Iic i, ∑ i' : Fin L, ∑ j' ∈ Finset.Iic i',
        rankMoment L M ({j, i, j', i'} : Finset (Fin L)).card
          / (((i.1 : ℝ) + 1) * ((i'.1 : ℝ) + 1)))
      = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range (i + 1),
          ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range (i' + 1),
            rankMoment L M ({j, i, j', i'} : Finset ℕ).card
              / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) := by
    have hcard : (∑ i : Fin L, ∑ j ∈ Finset.Iic i, ∑ i' : Fin L, ∑ j' ∈ Finset.Iic i',
          rankMoment L M ({j, i, j', i'} : Finset (Fin L)).card
            / (((i.1 : ℝ) + 1) * ((i'.1 : ℝ) + 1)))
        = ∑ i : Fin L, ∑ j ∈ Finset.Iic i, ∑ i' : Fin L, ∑ j' ∈ Finset.Iic i',
            rankMoment L M ({j.1, i.1, j'.1, i'.1} : Finset ℕ).card
              / (((i.1 : ℝ) + 1) * ((i'.1 : ℝ) + 1)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
      rw [card_quad_val]
    rw [hcard]
    exact quad_reindex (fun a b c d =>
      rankMoment L M ({a, b, c, d} : Finset ℕ).card / (((b : ℝ) + 1) * ((d : ℝ) + 1)))
  rw [hA]
  have hB : (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range (i + 1),
        ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range (i' + 1),
          rankMoment L M ({j, i, j', i'} : Finset ℕ).card
            / (((i : ℝ) + 1) * ((i' : ℝ) + 1)))
      = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range (i + 1),
          ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range (i' + 1),
            (rankMoment L M 1 * (if ({j, i, j', i'} : Finset ℕ).card = 1 then
                (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
              + rankMoment L M 2 * (if ({j, i, j', i'} : Finset ℕ).card = 2 then
                (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
              + rankMoment L M 3 * (if ({j, i, j', i'} : Finset ℕ).card = 3 then
                (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
              + rankMoment L M 4 * (if ({j, i, j', i'} : Finset ℕ).card = 4 then
                (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
    exact rankMoment_div_split L M _ (quad_card_pos j i j' i') (quad_card_le j i j' i') _
  rw [hB]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [sigSum]

/-! ### V8: `Sig_1 = H⁽²⁾_L` -/

lemma sigSum_one (L : ℕ) : sigSum L 1 = harmonic2 L := by
  unfold sigSum
  rw [← sum_range_one_div_sq L]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_range_succ]
  -- The strict block j < i vanishes: {j, i} ⊆ {j, i, j', i'} has card 2.
  have hstrict :
      (∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range (i' + 1),
        if ({j, i, j', i'} : Finset ℕ).card = 1 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hji : j < i := Finset.mem_range.mp hj
    refine Finset.sum_eq_zero fun i' _ => ?_
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [if_neg]
    intro hc
    have hsub : ({j, i} : Finset ℕ) ⊆ ({j, i, j', i'} : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      omega
    have h2 : ({j, i} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
    have := Finset.card_le_card hsub
    omega
  rw [hstrict, zero_add]
  -- Now j = i; the summand set is {i, i, j', i'}.
  have hinner : ∀ i' ∈ Finset.range L,
      (∑ j' ∈ Finset.range (i' + 1),
        if ({i, i, j', i'} : Finset ℕ).card = 1 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) := by
    intro i' _
    rw [Finset.sum_range_succ]
    -- The strict block j' < i' vanishes: {j', i'} ⊆ {i, i, j', i'} has card 2.
    have hstrict' :
        (∑ j' ∈ Finset.range i',
          if ({i, i, j', i'} : Finset ℕ).card = 1 then
            (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j' hj' => ?_
      have hj'i' : j' < i' := Finset.mem_range.mp hj'
      rw [if_neg]
      intro hc
      have hsub : ({j', i'} : Finset ℕ) ⊆ ({i, i, j', i'} : Finset ℕ) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        omega
      have h2 : ({j', i'} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
      have := Finset.card_le_card hsub
      omega
    rw [hstrict', zero_add]
    -- j' = i': the set is {i, i, i', i'} = {i, i'}, card 1 iff i' = i.
    by_cases h : i' = i
    · subst h
      simp
    · rw [if_neg h, if_neg]
      intro hc
      have hii' : i ≠ i' := fun hh => h hh.symm
      have hset : ({i, i, i', i'} : Finset ℕ) = ({i, i'} : Finset ℕ) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have h2 : ({i, i'} : Finset ℕ).card = 2 := Finset.card_pair hii'
      rw [hset, h2] at hc
      omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.range L) i, if_pos hi]
  ring

/-! ### V9: `Sig_2` -/

lemma sum_full_pair (L : ℕ) :
    ∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L,
        (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))
      = harmonic L * harmonic L := by
  have e : ∀ i i' : ℕ, (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))
      = ((1 : ℝ) / ((i : ℝ) + 1)) * ((1 : ℝ) / ((i' : ℝ) + 1)) := by
    intro i i'
    rw [div_mul_div_comm, one_mul]
  simp_rw [e, ← Finset.mul_sum, ← Finset.sum_mul, sum_range_one_div]

lemma sum_strict_pair (L : ℕ) :
    ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
        (1 : ℝ) / (((j' : ℝ) + 1) * ((i' : ℝ) + 1))
      = (harmonic L ^ 2 - harmonic2 L) / 2 := by
  have h : ∀ i' ∈ Finset.range L,
      (∑ j' ∈ Finset.range i', (1 : ℝ) / (((j' : ℝ) + 1) * ((i' : ℝ) + 1)))
      = harmonic i' / ((i' : ℝ) + 1) := by
    intro i' _
    have e : ∀ j' : ℕ, (1 : ℝ) / (((j' : ℝ) + 1) * ((i' : ℝ) + 1))
        = ((1 : ℝ) / ((j' : ℝ) + 1)) * ((1 : ℝ) / ((i' : ℝ) + 1)) := by
      intro j'
      rw [div_mul_div_comm, one_mul]
    simp_rw [e]
    rw [← Finset.sum_mul, sum_range_one_div, mul_one_div]
  rw [Finset.sum_congr rfl h]
  exact sum_range_harmonic_div L

lemma sum_strict_pair' (L : ℕ) :
    ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i,
        (1 : ℝ) / (((i : ℝ) + 1) * ((j : ℝ) + 1))
      = (harmonic L ^ 2 - harmonic2 L) / 2 := by
  rw [← sum_strict_pair L]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma sum_diag_weight (L : ℕ) :
    ∑ i ∈ Finset.range L, (i : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1)))
      = harmonic L - harmonic2 L := by
  have e : ∀ t : ℕ, (t : ℝ) * ((1 : ℝ) / (((t : ℝ) + 1) * ((t : ℝ) + 1)))
      = (t : ℝ) / ((t : ℝ) + 1) ^ 2 := by
    intro t; ring
  simp_rw [e]
  exact sum_range_self_div_sq L

/-- The key card-2 characterization for the fully strict block. -/
lemma quad_card_two_iff (i j i' j' : ℕ) (hj : j < i) (hj' : j' < i') :
    ({j, i, j', i'} : Finset ℕ).card = 2 ↔ (j' = j ∧ i' = i) := by
  constructor
  · intro h2
    have hsub : ({j, i} : Finset ℕ) ⊆ ({j, i, j', i'} : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      tauto
    have hpair : ({j, i} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
    have heq : ({j, i} : Finset ℕ) = ({j, i, j', i'} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hj'm : j' ∈ ({j, i} : Finset ℕ) := by
      rw [heq]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hi'm : i' ∈ ({j, i} : Finset ℕ) := by
      rw [heq]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj'm hi'm
    omega
  · rintro ⟨h1, h2⟩
    have hset : ({j, i, j', i'} : Finset ℕ) = {j, i} := by
      rw [h1, h2]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hset, Finset.card_pair (by omega : j ≠ i)]

/-- Block DD of `Sig_2`: both pairs diagonal (`j = i`, `j' = i'`). -/
lemma blockDD (L : ℕ) :
    ∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L,
        (if ({i, i, i', i'} : Finset ℕ).card = 2 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = harmonic L * harmonic L - harmonic2 L := by
  have point : ∀ i i' : ℕ,
      (if ({i, i, i', i'} : Finset ℕ).card = 2 then
        (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))
        - (if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) := by
    intro i i'
    rcases eq_or_ne i' i with h | h
    · have hset : ({i, i, i', i'} : Finset ℕ) = {i} := by
        rw [h]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hset, Finset.card_singleton]
      split_ifs <;> first | ring1 | (exfalso; omega)
    · have hset : ({i, i, i', i'} : Finset ℕ) = {i, i'} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hset, Finset.card_pair (show i ≠ i' by omega)]
      split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [point, Finset.sum_sub_distrib]
  rw [sum_full_pair]
  have hdiag : ∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L,
      (if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = harmonic2 L := by
    have h1 : ∀ i ∈ Finset.range L,
        (∑ i' ∈ Finset.range L,
          if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = (1 : ℝ) / ((i : ℝ) + 1) ^ 2 := by
      intro i hi
      rw [Finset.sum_ite_eq' (Finset.range L) i
        (fun i' => (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))), if_pos hi]
      ring
    rw [Finset.sum_congr rfl h1, sum_range_one_div_sq]
  rw [hdiag]

/-- Block DS of `Sig_2`: outer pair diagonal (`j = i`), inner strict (`j' < i'`). -/
lemma blockDS (L : ℕ) :
    ∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
        (if ({i, i, j', i'} : Finset ℕ).card = 2 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (harmonic L ^ 2 - harmonic2 L) / 2 + (harmonic L - harmonic2 L) := by
  have point : ∀ i i' j' : ℕ, j' < i' →
      (if ({i, i, j', i'} : Finset ℕ).card = 2 then
        (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (if i = j' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        + (if i = i' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) := by
    intro i i' j' hlt
    rcases eq_or_ne i j' with h1 | h1
    · have hset : ({i, i, j', i'} : Finset ℕ) = {i, i'} := by
        rw [← h1]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hset, Finset.card_pair (show i ≠ i' by omega)]
      split_ifs <;> first | ring1 | (exfalso; omega)
    · rcases eq_or_ne i i' with h2 | h2
      · have hset : ({i, i, j', i'} : Finset ℕ) = {i, j'} := by
          rw [← h2]
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hset, Finset.card_pair h1]
        split_ifs <;> first | ring1 | (exfalso; omega)
      · have hset : ({i, i, j', i'} : Finset ℕ) = {i, j', i'} := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        have hcard : ({i, j', i'} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              push_neg
              omega),
            Finset.card_pair (show j' ≠ i' by omega)]
        rw [hset, hcard]
        split_ifs <;> first | ring1 | (exfalso; omega)
  have step1 : ∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
      (if ({i, i, j', i'} : Finset ℕ).card = 2 then
        (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = ∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
        ((if i = j' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
          + (if i = i' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
      Finset.sum_congr rfl fun j' hj' => ?_
    exact point i i' j' (Finset.mem_range.mp hj')
  rw [step1]
  simp only [Finset.sum_add_distrib]
  have hP1 : ∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
      (if i = j' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (harmonic L ^ 2 - harmonic2 L) / 2 := by
    rw [Finset.sum_comm]
    have inner : ∀ i' ∈ Finset.range L,
        (∑ i ∈ Finset.range L, ∑ j' ∈ Finset.range i',
          if i = j' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = harmonic i' / ((i' : ℝ) + 1) := by
      intro i' hi'
      rw [Finset.sum_comm]
      have h3 : ∀ j' ∈ Finset.range i',
          (∑ i ∈ Finset.range L,
            if i = j' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
          = (1 : ℝ) / (((j' : ℝ) + 1) * ((i' : ℝ) + 1)) := by
        intro j' hj'
        have hj'L : j' ∈ Finset.range L := Finset.mem_range.mpr
          (lt_trans (Finset.mem_range.mp hj') (Finset.mem_range.mp hi'))
        simp only [Finset.sum_ite_eq', hj'L, if_true]
      rw [Finset.sum_congr rfl h3]
      have e : ∀ j' : ℕ, (1 : ℝ) / (((j' : ℝ) + 1) * ((i' : ℝ) + 1))
          = ((1 : ℝ) / ((j' : ℝ) + 1)) * ((1 : ℝ) / ((i' : ℝ) + 1)) := by
        intro j'
        rw [div_mul_div_comm, one_mul]
      simp_rw [e]
      rw [← Finset.sum_mul, sum_range_one_div, mul_one_div]
    rw [Finset.sum_congr rfl inner]
    exact sum_range_harmonic_div L
  have hP2 : ∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
      (if i = i' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = harmonic L - harmonic2 L := by
    rw [Finset.sum_comm]
    have inner : ∀ i' ∈ Finset.range L,
        (∑ i ∈ Finset.range L, ∑ j' ∈ Finset.range i',
          if i = i' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = (i' : ℝ) * ((1 : ℝ) / (((i' : ℝ) + 1) * ((i' : ℝ) + 1))) := by
      intro i' hi'
      have h4 : ∀ i ∈ Finset.range L,
          (∑ j' ∈ Finset.range i',
            if i = i' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
          = (i' : ℝ) * (if i = i' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) := by
        intro i _
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.sum_congr rfl h4, ← Finset.mul_sum]
      simp only [Finset.sum_ite_eq', hi', if_true]
    rw [Finset.sum_congr rfl inner]
    exact sum_diag_weight L
  rw [hP1, hP2]

/-- Block SD of `Sig_2`: outer pair strict (`j < i`), inner diagonal (`j' = i'`). -/
lemma blockSD (L : ℕ) :
    ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        (if ({j, i, i', i'} : Finset ℕ).card = 2 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (harmonic L ^ 2 - harmonic2 L) / 2 + (harmonic L - harmonic2 L) := by
  have point : ∀ i j i' : ℕ, j < i →
      (if ({j, i, i', i'} : Finset ℕ).card = 2 then
        (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (if i' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        + (if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) := by
    intro i j i' hlt
    rcases eq_or_ne i' j with h1 | h1
    · have hset : ({j, i, i', i'} : Finset ℕ) = {j, i} := by
        rw [h1]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hset, Finset.card_pair (show j ≠ i by omega)]
      split_ifs <;> first | ring1 | (exfalso; omega)
    · rcases eq_or_ne i' i with h2 | h2
      · have hset : ({j, i, i', i'} : Finset ℕ) = {j, i} := by
          rw [h2]
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [hset, Finset.card_pair (show j ≠ i by omega)]
        split_ifs <;> first | ring1 | (exfalso; omega)
      · have hset : ({j, i, i', i'} : Finset ℕ) = {j, i, i'} := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        have hcard : ({j, i, i'} : Finset ℕ).card = 3 := by
          rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              push_neg
              omega),
            Finset.card_pair (show i ≠ i' by omega)]
        rw [hset, hcard]
        split_ifs <;> first | ring1 | (exfalso; omega)
  have step1 : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
      (if ({j, i, i', i'} : Finset ℕ).card = 2 then
        (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        ((if i' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
          + (if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      Finset.sum_congr rfl fun i' _ => ?_
    exact point i j i' (Finset.mem_range.mp hj)
  rw [step1]
  simp only [Finset.sum_add_distrib]
  have hQ1 : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
      (if i' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (harmonic L ^ 2 - harmonic2 L) / 2 := by
    have h1 : ∀ i ∈ Finset.range L,
        (∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
          if i' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = ∑ j ∈ Finset.range i, (1 : ℝ) / (((i : ℝ) + 1) * ((j : ℝ) + 1)) := by
      intro i hi
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjL : j ∈ Finset.range L := Finset.mem_range.mpr
        (lt_trans (Finset.mem_range.mp hj) (Finset.mem_range.mp hi))
      simp only [Finset.sum_ite_eq', hjL, if_true]
    rw [Finset.sum_congr rfl h1]
    exact sum_strict_pair' L
  have hQ2 : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
      (if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = harmonic L - harmonic2 L := by
    have h1 : ∀ i ∈ Finset.range L,
        (∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
          if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = (i : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1))) := by
      intro i hi
      have h2 : ∀ j ∈ Finset.range i,
          (∑ i' ∈ Finset.range L,
            if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
          = (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1)) := by
        intro j _
        simp only [Finset.sum_ite_eq', hi, if_true]
      rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_congr rfl h1]
    exact sum_diag_weight L
  rw [hQ1, hQ2]

/-- Block SS of `Sig_2`: both pairs strict (`j < i`, `j' < i'`). -/
lemma blockSS (L : ℕ) :
    ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        ∑ j' ∈ Finset.range i',
        (if ({j, i, j', i'} : Finset ℕ).card = 2 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = harmonic L - harmonic2 L := by
  have main : ∀ i ∈ Finset.range L,
      (∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
        (if ({j, i, j', i'} : Finset ℕ).card = 2 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0))
      = ∑ j ∈ Finset.range i, (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1)) := by
    intro i hi
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have e1 : ∀ i' ∈ Finset.range L,
        (∑ j' ∈ Finset.range i',
          if ({j, i, j', i'} : Finset ℕ).card = 2 then
            (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = (if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) := by
      intro i' _
      rcases eq_or_ne i' i with h | h
      · rw [if_pos h]
        have e2 : ∀ j' ∈ Finset.range i',
            (if ({j, i, j', i'} : Finset ℕ).card = 2 then
              (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
            = (if j' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) := by
          intro j' hj'
          rw [if_congr (quad_card_two_iff i j i' j' hjlt (Finset.mem_range.mp hj')) rfl rfl]
          simp [h]
        rw [Finset.sum_congr rfl e2,
          Finset.sum_ite_eq' (Finset.range i') j
            (fun _ => (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))),
          if_pos (Finset.mem_range.mpr (by omega : j < i'))]
      · rw [if_neg h]
        apply Finset.sum_eq_zero
        intro j' hj'
        rw [if_congr (quad_card_two_iff i j i' j' hjlt (Finset.mem_range.mp hj')) rfl rfl,
          if_neg (fun hc => h hc.2)]
    rw [Finset.sum_congr rfl e1,
      Finset.sum_ite_eq' (Finset.range L) i
        (fun i' => (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))),
      if_pos hi]
  rw [Finset.sum_congr rfl main]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact sum_diag_weight L

lemma sigSum_two (L : ℕ) :
    sigSum L 2 = 2 * harmonic L ^ 2 + 3 * harmonic L - 5 * harmonic2 L := by
  have split : sigSum L 2
      = (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
          ∑ j' ∈ Finset.range i',
          (if ({j, i, j', i'} : Finset ℕ).card = 2 then
            (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0))
      + (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
          (if ({j, i, i', i'} : Finset ℕ).card = 2 then
            (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0))
      + (∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
          (if ({i, i, j', i'} : Finset ℕ).card = 2 then
            (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0))
      + (∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L,
          (if ({i, i, i', i'} : Finset ℕ).card = 2 then
            (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)) := by
    unfold sigSum
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    ring
  rw [split, blockSS L, blockSD L, blockDS L, blockDD L]
  ring

/-! ### V10: `Sig_3`

Split each `j ≤ i` sum into diagonal (`j = i`) and strict (`j < i`) parts,
giving four blocks DD/DS/SD/SS.  DD vanishes (card ≤ 2).  DS and SD evaluate
via a "whole sum minus collapsed terms" pointwise identity.  SS splits
pointwise into the four single-coincidence patterns, each of which collapses.
-/

/-- `ring` cannot factor inverses of non-atomic products, so these small
algebra facts are proved once with opaque atoms and instantiated. -/
private lemma sig3_div_mul (a b : ℝ) : (1 : ℝ) / (a * b) = 1 / a * (1 / b) := by
  ring

private lemma sig3_mul_div (t a b : ℝ) : t * ((1 : ℝ) / (a * b)) = 1 / a * (t / b) := by
  ring

private lemma sig3_mul_div' (t a b : ℝ) : t * ((1 : ℝ) / (b * a)) = 1 / a * (t / b) := by
  ring

private lemma sig3_div_mul' (a b : ℝ) : (1 : ℝ) / (b * a) = 1 / a * (1 / b) := by
  ring

private lemma sig3_self_sq (t a : ℝ) : t * ((1 : ℝ) / (a * a)) = t / a ^ 2 := by
  ring

private lemma sig3_card_DD (i i' : ℕ) (w : ℝ) :
    (if ({i, i, i', i'} : Finset ℕ).card = 3 then w else 0) = 0 := by
  have h : ({i, i, i', i'} : Finset ℕ).card ≠ 3 := by
    simp [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton,
      Finset.card_singleton]
    split_ifs <;> omega
  rw [if_neg h]

private lemma sig3_split_DS {j' i' : ℕ} (h : j' < i') (i : ℕ) (w : ℝ) :
    (if ({i, i, j', i'} : Finset ℕ).card = 3 then w else 0)
      = w - ((if i = j' then w else 0) + (if i = i' then w else 0)) := by
  have h3 : (({i, i, j', i'} : Finset ℕ).card = 3) ↔ ¬(i = j' ∨ i = i') := by
    simp [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton,
      Finset.card_singleton]
    split_ifs <;> omega
  simp only [h3]
  split_ifs <;> first | ring1 | (exfalso; omega)

private lemma sig3_split_SD {j i : ℕ} (h : j < i) (i' : ℕ) (w : ℝ) :
    (if ({j, i, i', i'} : Finset ℕ).card = 3 then w else 0)
      = w - ((if i' = j then w else 0) + (if i' = i then w else 0)) := by
  have h3 : (({j, i, i', i'} : Finset ℕ).card = 3) ↔ ¬(i' = j ∨ i' = i) := by
    simp [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton,
      Finset.card_singleton]
    split_ifs <;> omega
  simp only [h3]
  split_ifs <;> first | ring1 | (exfalso; omega)

private lemma sig3_split_SS {j i j' i' : ℕ} (hji : j < i) (hj'i' : j' < i') (w : ℝ) :
    (if ({j, i, j', i'} : Finset ℕ).card = 3 then w else 0)
      = (if j' = j ∧ i' ≠ i then w else 0) + (if i' = i ∧ j' ≠ j then w else 0)
        + (if j' = i then w else 0) + (if i' = j then w else 0) := by
  have h3 : (({j, i, j', i'} : Finset ℕ).card = 3)
      ↔ ((j' = j ∧ i' ≠ i) ∨ (i' = i ∧ j' ≠ j) ∨ j' = i ∨ i' = j) := by
    simp [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton,
      Finset.card_singleton]
    split_ifs <;> omega
  simp only [h3]
  split_ifs <;> first | ring1 | (exfalso; omega)

private lemma sig3_sum_ite_lt (n m : ℕ) (f : ℕ → ℝ) :
    ∑ x ∈ Finset.range n, (if x < m then f x else 0)
      = ∑ x ∈ Finset.range (min n m), f x := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun x _ => rfl
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private lemma sig3_ite_ne (a b : ℕ) (w : ℝ) :
    (if a ≠ b then w else 0) = w - (if a = b then w else 0) := by
  split_ifs <;> first | ring1 | (exfalso; omega)

private lemma sig3_ne_split (i i' : ℕ) (a : ℝ) :
    (if i' ≠ i then a else 0) = (if i' < i then a else 0) + (if i < i' then a else 0) := by
  split_ifs <;> first | ring1 | (exfalso; omega)

/-- The recurring value `X = ∑_{i<L} (1/(i+1)) (i - H_i) = (L - H) - (H² - H⁽²⁾)/2`. -/
private lemma sig3_X (L : ℕ) :
    ∑ i ∈ Finset.range L, 1 / ((i : ℝ) + 1) * ((i : ℝ) - harmonic i)
      = (L : ℝ) - harmonic L - (harmonic L ^ 2 - harmonic2 L) / 2 := by
  have hpt : ∀ i ∈ Finset.range L,
      1 / ((i : ℝ) + 1) * ((i : ℝ) - harmonic i)
        = (i : ℝ) / ((i : ℝ) + 1) - harmonic i / ((i : ℝ) + 1) := fun i _ => by ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, sum_range_self_div,
    sum_range_harmonic_div]

/-- Shared top-level evaluation for the DS and SD blocks. -/
private lemma sig3_top (L : ℕ) :
    ∑ i ∈ Finset.range L,
        ((i : ℝ) * (1 / ((i : ℝ) + 1) * harmonic L)
          - (1 / ((i : ℝ) + 1) * harmonic i
            + (i : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1)))))
      = harmonic L * ((L : ℝ) - harmonic L)
        - (harmonic L ^ 2 - harmonic2 L) / 2 - (harmonic L - harmonic2 L) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : ∀ i ∈ Finset.range L,
      (i : ℝ) * (1 / ((i : ℝ) + 1) * harmonic L)
        = harmonic L * ((i : ℝ) / ((i : ℝ) + 1)) := fun i _ => by ring
  have h2 : ∀ i ∈ Finset.range L,
      1 / ((i : ℝ) + 1) * harmonic i = harmonic i / ((i : ℝ) + 1) := fun i _ => by ring
  have h3 : ∀ i ∈ Finset.range L,
      (i : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1)))
        = (i : ℝ) / ((i : ℝ) + 1) ^ 2 := fun i _ => sig3_self_sq _ _
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_congr rfl h3,
    ← Finset.mul_sum, sum_range_self_div, sum_range_harmonic_div, sum_range_self_div_sq]
  ring

private lemma sig3_DD (L : ℕ) :
    (∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L,
        if ({i, i, i', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) = 0 :=
  Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => sig3_card_DD i i' _

private lemma sig3_DS (L : ℕ) :
    (∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
        if ({i, i, j', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = harmonic L * ((L : ℝ) - harmonic L)
        - (harmonic L ^ 2 - harmonic2 L) / 2 - (harmonic L - harmonic2 L) := by
  rw [Finset.sum_comm]
  have hswap : ∀ i' ∈ Finset.range L,
      (∑ i ∈ Finset.range L, ∑ j' ∈ Finset.range i',
        if ({i, i, j', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = ∑ j' ∈ Finset.range i', ∑ i ∈ Finset.range L,
          if ({i, i, j', i'} : Finset ℕ).card = 3 then
            (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0 :=
    fun i' _ => Finset.sum_comm
  rw [Finset.sum_congr rfl hswap]
  have hinner : ∀ i' ∈ Finset.range L, ∀ j' ∈ Finset.range i',
      (∑ i ∈ Finset.range L,
        if ({i, i, j', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = 1 / ((i' : ℝ) + 1) * harmonic L
        - ((1 : ℝ) / (((j' : ℝ) + 1) * ((i' : ℝ) + 1))
          + (1 : ℝ) / (((i' : ℝ) + 1) * ((i' : ℝ) + 1))) := by
    intro i' hi' j' hj'
    have hj'i' : j' < i' := Finset.mem_range.mp hj'
    have hi'L : i' < L := Finset.mem_range.mp hi'
    have hpt : ∀ i ∈ Finset.range L,
        (if ({i, i, j', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))
          - ((if i = j' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
            + (if i = i' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)) :=
      fun i _ => sig3_split_DS hj'i' i _
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' (Finset.range L) j'
        (fun i => (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))),
      Finset.sum_ite_eq' (Finset.range L) i'
        (fun i => (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))),
      if_pos (Finset.mem_range.mpr (lt_trans hj'i' hi'L)),
      if_pos (Finset.mem_range.mpr hi'L)]
    have hw : ∀ i ∈ Finset.range L,
        (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))
          = 1 / ((i' : ℝ) + 1) * ((1 : ℝ) / ((i : ℝ) + 1)) :=
      fun i _ => sig3_div_mul' _ _
    rw [Finset.sum_congr rfl hw, ← Finset.mul_sum, sum_range_one_div]
  have hmid : ∀ i' ∈ Finset.range L,
      (∑ j' ∈ Finset.range i', ∑ i ∈ Finset.range L,
        if ({i, i, j', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (i' : ℝ) * (1 / ((i' : ℝ) + 1) * harmonic L)
        - (1 / ((i' : ℝ) + 1) * harmonic i'
          + (i' : ℝ) * ((1 : ℝ) / (((i' : ℝ) + 1) * ((i' : ℝ) + 1)))) := by
    intro i' hi'
    rw [Finset.sum_congr rfl (hinner i' hi'), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hb : ∀ j' ∈ Finset.range i',
        (1 : ℝ) / (((j' : ℝ) + 1) * ((i' : ℝ) + 1))
          = 1 / ((i' : ℝ) + 1) * ((1 : ℝ) / ((j' : ℝ) + 1)) :=
      fun j' _ => sig3_div_mul' _ _
    rw [Finset.sum_congr rfl hb, ← Finset.mul_sum, sum_range_one_div]
  rw [Finset.sum_congr rfl hmid, sig3_top]

private lemma sig3_SD (L : ℕ) :
    (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        if ({j, i, i', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = harmonic L * ((L : ℝ) - harmonic L)
        - (harmonic L ^ 2 - harmonic2 L) / 2 - (harmonic L - harmonic2 L) := by
  have hinner : ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range i,
      (∑ i' ∈ Finset.range L,
        if ({j, i, i', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = 1 / ((i : ℝ) + 1) * harmonic L
        - ((1 : ℝ) / (((i : ℝ) + 1) * ((j : ℝ) + 1))
          + (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1))) := by
    intro i hi j hj
    have hji : j < i := Finset.mem_range.mp hj
    have hiL : i < L := Finset.mem_range.mp hi
    have hpt : ∀ i' ∈ Finset.range L,
        (if ({j, i, i', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))
          - ((if i' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
            + (if i' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)) :=
      fun i' _ => sig3_split_SD hji i' _
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' (Finset.range L) j
        (fun i' => (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))),
      Finset.sum_ite_eq' (Finset.range L) i
        (fun i' => (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))),
      if_pos (Finset.mem_range.mpr (lt_trans hji hiL)),
      if_pos (Finset.mem_range.mpr hiL)]
    have hw : ∀ i' ∈ Finset.range L,
        (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))
          = 1 / ((i : ℝ) + 1) * ((1 : ℝ) / ((i' : ℝ) + 1)) :=
      fun i' _ => sig3_div_mul _ _
    rw [Finset.sum_congr rfl hw, ← Finset.mul_sum, sum_range_one_div]
  have hmid : ∀ i ∈ Finset.range L,
      (∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        if ({j, i, i', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (i : ℝ) * (1 / ((i : ℝ) + 1) * harmonic L)
        - (1 / ((i : ℝ) + 1) * harmonic i
          + (i : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1)))) := by
    intro i hi
    rw [Finset.sum_congr rfl (hinner i hi), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hb : ∀ j ∈ Finset.range i,
        (1 : ℝ) / (((i : ℝ) + 1) * ((j : ℝ) + 1))
          = 1 / ((i : ℝ) + 1) * ((1 : ℝ) / ((j : ℝ) + 1)) :=
      fun j _ => sig3_div_mul _ _
    rw [Finset.sum_congr rfl hb, ← Finset.mul_sum, sum_range_one_div]
  rw [Finset.sum_congr rfl hmid, sig3_top]

private lemma sig3_SS_A (L : ℕ) :
    (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        ∑ j' ∈ Finset.range i',
        if j' = j ∧ i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = 2 * ((L : ℝ) - harmonic L - (harmonic L ^ 2 - harmonic2 L) / 2) := by
  -- collapse j'
  have h1 : ∀ (i j : ℕ), ∀ i' ∈ Finset.range L,
      (∑ j' ∈ Finset.range i',
        if j' = j ∧ i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (if j < i' then
          (if i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) else 0) := by
    intro i j i' _
    have hpt : ∀ j' ∈ Finset.range i',
        (if j' = j ∧ i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = (if j' = j then
            (if i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) else 0) :=
      fun j' _ => by rw [ite_and]
    rw [Finset.sum_congr rfl hpt,
      Finset.sum_ite_eq' (Finset.range i') j
        (fun _ => if i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)]
    simp only [Finset.mem_range]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
    (fun j _ => Finset.sum_congr rfl (h1 i j)))]
  -- swap j and i'
  have h2 : ∀ i ∈ Finset.range L,
      (∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        if j < i' then
          (if i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) else 0)
      = ∑ i' ∈ Finset.range L, ∑ j ∈ Finset.range i,
          if j < i' then
            (if i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) else 0 :=
    fun i _ => Finset.sum_comm
  rw [Finset.sum_congr rfl h2]
  -- evaluate the j-sum: min i i' copies
  have h3 : ∀ i ∈ Finset.range L, ∀ i' ∈ Finset.range L,
      (∑ j ∈ Finset.range i,
        if j < i' then
          (if i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) else 0)
      = (if i' < i then
            ((min i i' : ℕ) : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))) else 0)
        + (if i < i' then
            ((min i i' : ℕ) : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))) else 0) := by
    intro i _ i' _
    rw [sig3_sum_ite_lt i i'
        (fun _ => if i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_ite, mul_zero, sig3_ne_split]
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (h3 i hi))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
  -- the two halves are equal by i <-> i' symmetry
  have hT2 : (∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L,
        if i < i' then
          ((min i i' : ℕ) : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))) else 0)
      = ∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L,
          if i' < i then
            ((min i i' : ℕ) : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))) else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hba
    · rw [min_comm b a, mul_comm ((b : ℝ) + 1) ((a : ℝ) + 1)]
    · rfl
  -- evaluate T1
  have hT1 : (∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L,
        if i' < i then
          ((min i i' : ℕ) : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))) else 0)
      = (L : ℝ) - harmonic L - (harmonic L ^ 2 - harmonic2 L) / 2 := by
    have h5 : ∀ i ∈ Finset.range L,
        (∑ i' ∈ Finset.range L,
          if i' < i then
            ((min i i' : ℕ) : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))) else 0)
        = 1 / ((i : ℝ) + 1) * ((i : ℝ) - harmonic i) := by
      intro i hi
      rw [sig3_sum_ite_lt L i
          (fun i' => ((min i i' : ℕ) : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)))),
        min_eq_right (le_of_lt (Finset.mem_range.mp hi))]
      have hpt : ∀ i' ∈ Finset.range i,
          ((min i i' : ℕ) : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)))
            = 1 / ((i : ℝ) + 1) * ((i' : ℝ) / ((i' : ℝ) + 1)) := by
        intro i' hi'
        rw [min_eq_right (le_of_lt (Finset.mem_range.mp hi'))]
        exact sig3_mul_div _ _ _
      rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, sum_range_self_div]
    rw [Finset.sum_congr rfl h5]
    exact sig3_X L
  rw [hT2, hT1]
  ring

private lemma sig3_SS_B (L : ℕ) :
    (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        ∑ j' ∈ Finset.range i',
        if i' = i ∧ j' ≠ j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (L : ℝ) - 3 * harmonic L + 2 * harmonic2 L := by
  have hinner : ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range i,
      (∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
        if i' = i ∧ j' ≠ j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (i : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1)))
        - (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1)) := by
    intro i hi j hj
    have hji : j < i := Finset.mem_range.mp hj
    have hstep : ∀ i' ∈ Finset.range L,
        (∑ j' ∈ Finset.range i',
          if i' = i ∧ j' ≠ j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = (if i' = i then
            (∑ j' ∈ Finset.range i',
              if j' ≠ j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) else 0) := by
      intro i' _
      by_cases h : i' = i
      · rw [if_pos h]
        exact Finset.sum_congr rfl fun j' _ => if_congr (by simp [h]) rfl rfl
      · rw [if_neg h]
        exact Finset.sum_eq_zero fun j' _ => if_neg (fun hc => h hc.1)
    rw [Finset.sum_congr rfl hstep,
      Finset.sum_ite_eq' (Finset.range L)
        i (fun i' => ∑ j' ∈ Finset.range i',
          if j' ≠ j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0),
      if_pos (Finset.mem_range.mpr (Finset.mem_range.mp hi))]
    have hpt : ∀ j' ∈ Finset.range i,
        (if j' ≠ j then (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1)) else 0)
        = (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1))
          - (if j' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1)) else 0) :=
      fun j' _ => sig3_ite_ne j' j _
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul,
      Finset.sum_ite_eq' (Finset.range i) j
        (fun _ => (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 1))),
      if_pos (Finset.mem_range.mpr hji)]
  have hmid : ∀ i ∈ Finset.range L,
      (∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
        if i' = i ∧ j' ≠ j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (i : ℝ) * ((i : ℝ) - 1) / ((i : ℝ) + 1) ^ 2 := by
    intro i hi
    rw [Finset.sum_congr rfl (hinner i hi), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hne : ((i : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl hmid, sum_range_mul_sub_one_div_sq]

private lemma sig3_SS_C (L : ℕ) :
    (∑ i ∈ Finset.range L, ∑ _j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        ∑ j' ∈ Finset.range i',
        if j' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (L : ℝ) - harmonic L - (harmonic L ^ 2 - harmonic2 L) / 2 := by
  have h1 : ∀ (i j : ℕ), ∀ i' ∈ Finset.range L,
      (∑ j' ∈ Finset.range i',
        if j' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (if i < i' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) := by
    intro i j i' _
    rw [Finset.sum_ite_eq' (Finset.range i') i
      (fun _ => (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)))]
    simp only [Finset.mem_range]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
    (fun j _ => Finset.sum_congr rfl (h1 i j)))]
  have h2 : ∀ i ∈ Finset.range L,
      (∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        if i < i' then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = ∑ i' ∈ Finset.range L,
          if i < i' then (i : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))) else 0 := by
    intro i _
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by rw [mul_ite, mul_zero]
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  have h4 : ∀ i' ∈ Finset.range L,
      (∑ i ∈ Finset.range L,
        if i < i' then (i : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))) else 0)
      = 1 / ((i' : ℝ) + 1) * ((i' : ℝ) - harmonic i') := by
    intro i' hi'
    rw [sig3_sum_ite_lt L i'
        (fun i => (i : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)))),
      min_eq_right (le_of_lt (Finset.mem_range.mp hi'))]
    have hpt : ∀ i ∈ Finset.range i',
        (i : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)))
          = 1 / ((i' : ℝ) + 1) * ((i : ℝ) / ((i : ℝ) + 1)) :=
      fun i _ => sig3_mul_div' _ _ _
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, sum_range_self_div]
  rw [Finset.sum_congr rfl h4]
  exact sig3_X L

private lemma sig3_SS_D (L : ℕ) :
    (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        ∑ _j' ∈ Finset.range i',
        if i' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (L : ℝ) - harmonic L - (harmonic L ^ 2 - harmonic2 L) / 2 := by
  have h1 : ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range i,
      (∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
        if i' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (j : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((j : ℝ) + 1))) := by
    intro i hi j hj
    have hji : j < i := Finset.mem_range.mp hj
    have hiL : i < L := Finset.mem_range.mp hi
    have hj'sum : ∀ i' ∈ Finset.range L,
        (∑ j' ∈ Finset.range i',
          if i' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        = (if i' = j then
            (i' : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1))) else 0) := by
      intro i' _
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_congr rfl hj'sum,
      Finset.sum_ite_eq' (Finset.range L) j
        (fun i' => (i' : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)))),
      if_pos (Finset.mem_range.mpr (lt_trans hji hiL))]
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (h1 i hi))]
  have h2 : ∀ i ∈ Finset.range L,
      (∑ j ∈ Finset.range i, (j : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((j : ℝ) + 1))))
      = 1 / ((i : ℝ) + 1) * ((i : ℝ) - harmonic i) := by
    intro i _
    have hpt : ∀ j ∈ Finset.range i,
        (j : ℝ) * ((1 : ℝ) / (((i : ℝ) + 1) * ((j : ℝ) + 1)))
          = 1 / ((i : ℝ) + 1) * ((j : ℝ) / ((j : ℝ) + 1)) :=
      fun j _ => sig3_mul_div _ _ _
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, sum_range_self_div]
  rw [Finset.sum_congr rfl h2]
  exact sig3_X L

private lemma sig3_SS (L : ℕ) :
    (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
        ∑ j' ∈ Finset.range i',
        if ({j, i, j', i'} : Finset ℕ).card = 3 then
          (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = 2 * ((L : ℝ) - harmonic L - (harmonic L ^ 2 - harmonic2 L) / 2)
        + ((L : ℝ) - 3 * harmonic L + 2 * harmonic2 L)
        + ((L : ℝ) - harmonic L - (harmonic L ^ 2 - harmonic2 L) / 2)
        + ((L : ℝ) - harmonic L - (harmonic L ^ 2 - harmonic2 L) / 2) := by
  have hpt : ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range i, ∀ i' ∈ Finset.range L,
      ∀ j' ∈ Finset.range i',
      (if ({j, i, j', i'} : Finset ℕ).card = 3 then
        (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
      = (if j' = j ∧ i' ≠ i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        + (if i' = i ∧ j' ≠ j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        + (if j' = i then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
        + (if i' = j then (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0) :=
    fun i _ j hj i' _ j' hj' =>
      sig3_split_SS (Finset.mem_range.mp hj) (Finset.mem_range.mp hj') _
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj =>
    Finset.sum_congr rfl (fun i' hi' => Finset.sum_congr rfl
      (fun j' hj' => hpt i hi j hj i' hi' j' hj'))))]
  simp only [Finset.sum_add_distrib]
  rw [sig3_SS_A, sig3_SS_B, sig3_SS_C, sig3_SS_D]

lemma sigSum_three (L : ℕ) :
    sigSum L 3 = 2 * (L : ℝ) * harmonic L + 5 * (L : ℝ) - 5 * harmonic L ^ 2
      - 9 * harmonic L + 7 * harmonic2 L := by
  have hsplit : sigSum L 3
      = ((∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
            ∑ j' ∈ Finset.range i',
            if ({j, i, j', i'} : Finset ℕ).card = 3 then
              (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
          + (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range i, ∑ i' ∈ Finset.range L,
              if ({j, i, i', i'} : Finset ℕ).card = 3 then
                (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0))
        + ((∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range i',
              if ({i, i, j', i'} : Finset ℕ).card = 3 then
                (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)
          + (∑ i ∈ Finset.range L, ∑ i' ∈ Finset.range L,
              if ({i, i, i', i'} : Finset ℕ).card = 3 then
                (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) else 0)) := by
    unfold sigSum
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    ring
  rw [hsplit, sig3_SS, sig3_SD, sig3_DS, sig3_DD]
  ring

/-! ### V11: the total and `Sig_4` by subtraction -/

/-- The four coincidence classes partition the unconditional quadruple sum. -/
lemma sigSum_add_eq_total (L : ℕ) :
    sigSum L 1 + sigSum L 2 + sigSum L 3 + sigSum L 4 = (L : ℝ) ^ 2 := by
  have key : ∀ (j i j' i' : ℕ) (w : ℝ),
      (if ({j, i, j', i'} : Finset ℕ).card = 1 then w else 0)
        + (if ({j, i, j', i'} : Finset ℕ).card = 2 then w else 0)
        + (if ({j, i, j', i'} : Finset ℕ).card = 3 then w else 0)
        + (if ({j, i, j', i'} : Finset ℕ).card = 4 then w else 0) = w := by
    intro j i j' i' w
    have h1 : 0 < ({j, i, j', i'} : Finset ℕ).card :=
      Finset.card_pos.mpr (Finset.insert_nonempty _ _)
    have hA := Finset.card_insert_le j ({i, j', i'} : Finset ℕ)
    have hB := Finset.card_insert_le i ({j', i'} : Finset ℕ)
    have hC := Finset.card_insert_le j' ({i'} : Finset ℕ)
    have hD : ({i'} : Finset ℕ).card = 1 := Finset.card_singleton i'
    have hcases : ({j, i, j', i'} : Finset ℕ).card = 1
        ∨ ({j, i, j', i'} : Finset ℕ).card = 2
        ∨ ({j, i, j', i'} : Finset ℕ).card = 3
        ∨ ({j, i, j', i'} : Finset ℕ).card = 4 := by omega
    rcases hcases with h | h | h | h <;> rw [h] <;> norm_num
  have merged : sigSum L 1 + sigSum L 2 + sigSum L 3 + sigSum L 4
      = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range (i + 1),
          ∑ i' ∈ Finset.range L, ∑ j' ∈ Finset.range (i' + 1),
            (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) := by
    unfold sigSum
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun i' _ => ?_
    refine Finset.sum_congr rfl fun j' _ => ?_
    exact key j i j' i' _
  rw [merged]
  have hw : ∀ i i' : ℕ, ∑ j' ∈ Finset.range (i' + 1),
      (1 : ℝ) / (((i : ℝ) + 1) * ((i' : ℝ) + 1)) = 1 / ((i : ℝ) + 1) := by
    intro i i'
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
    have hi' : ((i' : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  simp_rw [hw]
  have hs : ∀ i : ℕ, ∑ _i' ∈ Finset.range L, (1 : ℝ) / ((i : ℝ) + 1)
      = (L : ℝ) / ((i : ℝ) + 1) := by
    intro i
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  simp_rw [hs]
  have hj : ∀ i : ℕ, ∑ _j ∈ Finset.range (i + 1), (L : ℝ) / ((i : ℝ) + 1) = (L : ℝ) := by
    intro i
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hi : ((i : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  simp_rw [hj]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

lemma sigSum_four (L : ℕ) :
    sigSum L 4 = (L : ℝ) ^ 2 - 2 * (L : ℝ) * harmonic L - 5 * (L : ℝ)
      + 3 * harmonic L ^ 2 + 6 * harmonic L - 3 * harmonic2 L := by
  linarith [sigSum_add_eq_total L, sigSum_one L, sigSum_two L, sigSum_three L]

/-! ### V12: assembly -/

/-- `E[AP²] = expectedWSq L M / M²` for `M = numRelevant y ≠ 0`. -/
theorem secondMomentAP_eq_expectedWSq_div {L : ℕ} (y : Fin L → Bool)
    (hM : numRelevant y ≠ 0) :
    secondMomentAP y = expectedWSq L (numRelevant y) / ((numRelevant y : ℝ)) ^ 2 := by
  have hML := numRelevant_le y
  have h6 := sum_apSq_div_choose_eq_quad hM hML
  rw [quad_rankMoment_eq_sigSum_comb, sigSum_one, sigSum_two, sigSum_three,
    sigSum_four] at h6
  have hM2 : ((numRelevant y : ℝ)) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hM)
  rw [secondMomentAP_eq_sum_over_rankSets, eq_div_iff hM2, expectedWSq]
  rw [mul_comm] at h6
  rw [h6]


/-! ### The general second moment and variance, proved

`W = sum_{i <= k} Z_i Z_k / k` squares into a sum over pairs of pairs whose expectation depends only on the coincidence pattern of the indices.
The `V1`-`V12` lemmas above reduce the four pattern sums (`sigSum`) to the harmonic polynomials of `expectedWSq` and assemble the result.
The same identity is independently checked by exact rational enumeration in the `native_decide` examples above.
The supplement's `demo.py` checks the mean and variance by exhaustive enumeration for `1 <= L <= 10` and `0 <= M <= L`. -/

/-- **The general variance closed form.**
`Var(AP) = (E[W²] - E[W]²)/M²` under a uniformly random ranking. -/
theorem varianceAP_closed_form {L : ℕ} (y : Fin L → Bool) (hL : 1 < L)
    (hM : numRelevant y ≠ 0) :
    varianceAP y = varianceAPClosedForm L (numRelevant y) := by
  rw [varianceAP, secondMomentAP_eq_expectedWSq_div y hM,
    uniformAvgAP_eq_expectedW_div y hL hM, varianceAPClosedForm]
  rw [div_pow, div_sub_div_same]

end ExpectedAp
