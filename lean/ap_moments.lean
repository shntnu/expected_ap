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

These check the *definition* `varianceAPClosedForm` symbolically, not just
numerically: at `M = 0`, `M = 1` and `M = L` the general statement below is a
theorem, not a `sorry`. -/

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

/-! ### Open: the general second moment

Everything above is `sorry`-free.  The one statement below is not proved.

What is missing is the `E[W²]` identity.  Writing `W = ∑_{i ≤ k} Z_i Z_k / k`,
`W²` expands into a sum over pairs `((i,k),(j,l))` with `i ≤ k`, `j ≤ l`, whose
expectation depends only on `|{i,k,j,l}|`, giving the four terms `m₁ … m₄`.
Collapsing the index bookkeeping into the polynomial coefficients above needs
the double-sum harmonic identities

  `∑_{k ≤ L} H_k/k = (H_L² + H⁽²⁾_L)/2`,   `∑_{k ≤ L} H_{k-1}/k = (H_L² - H⁽²⁾_L)/2`,
  `∑_{k ≤ L} (k-1)(k-2)/k`,  `∑_{k ≤ L} (k-1) H_{k-1}/k`, …

of which only the first-moment ones (`sum_fin_one_over`, `sum_fin_prev_over` in
`expected_ap.lean`) exist here, plus a four-way case split on the coincidence
pattern of the indices.  That is the whole content of the theorem;
the transfer machinery (`uniformAvgOverPerms_comp_relevantRanks`) and the
statement are in place, and the formula is checked inside Lean above (by exact
rational enumeration of every rank set, for `L ≤ 10`) and outside Lean against
exhaustive enumeration for all `1 ≤ M ≤ L ≤ 12` (`test_ap_moments.py`).

The `M = 0`, `M = 1` and `M = L` instances of this very statement are proved
above without `sorry`. -/
section Unproved

/-- **Not proved.** `Var(AP) = (E[W²] - E[W]²)/M²` under uniform random ranking. -/
theorem varianceAP_closed_form {L : ℕ} (y : Fin L → Bool) (hL : 1 < L)
    (hM : numRelevant y ≠ 0) :
    varianceAP y = varianceAPClosedForm L (numRelevant y) := by
  sorry

end Unproved

end ExpectedAp
