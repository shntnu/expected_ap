import expected_ap

open Finset
open scoped BigOperators

namespace ExpectedAp

/-- Ranks occupied by relevant items under a permutation. -/
def relevantRanks {L : ℕ} (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) :
    Finset (Fin L) :=
  Finset.univ.filter (fun i => y (π i))

@[simp]
theorem card_relevantRanks {L : ℕ} (y : Fin L → Bool) (π : Equiv.Perm (Fin L)) :
    (relevantRanks y π).card = numRelevant y := by
  classical
  have hmap : (relevantRanks y π).map π.toEmbedding =
      Finset.univ.filter (fun i => y i) := by
    ext i
    simp [relevantRanks]
  rw [← Finset.card_map π.toEmbedding, hmap]
  simp [numRelevant, indicator, Finset.sum_boole]

/-- Average Precision determined only by the set of 0-indexed relevant ranks.
If the relevant ranks are `r_1 < ... < r_M` in 1-indexed notation, this is
`(1 / M) * sum j / r_j`. -/
def averagePrecisionOfRanks {L : ℕ} (s : Finset (Fin L)) : ℚ :=
  if s.card = 0 then 0
  else
    (∑ i ∈ s, ((s.filter (fun j => j ≤ i)).card : ℚ) / (i.1 + 1 : ℚ)) /
      (s.card : ℚ)

private theorem cumRelevantPerm_eq_card_filter {L : ℕ} (y : Fin L → Bool)
    (π : Equiv.Perm (Fin L)) (i : Fin L) :
    cumRelevantPerm y π (rank1 i) =
      ((relevantRanks y π).filter (fun j => j ≤ i)).card := by
  classical
  simp only [cumRelevantPerm, indicator, Finset.sum_boole]
  apply congrArg Finset.card
  ext j
  simp [indicesLT, rank1, relevantRanks, Nat.lt_succ_iff, and_comm]

/-- The permutation definition of AP is the rank-set formula above. -/
theorem apUnderPerm_eq_averagePrecisionOfRanks {L : ℕ} (y : Fin L → Bool)
    (π : Equiv.Perm (Fin L)) :
    apUnderPerm y π = (averagePrecisionOfRanks (relevantRanks y π) : ℝ) := by
  classical
  by_cases hM : numRelevant y = 0
  · simp [apUnderPerm, averagePrecisionOfRanks, hM, card_relevantRanks]
  · simp [apUnderPerm, averagePrecisionOfRanks, hM, card_relevantRanks,
      precAtPerm, rank1]
    simp_rw [show ∀ i : Fin L, cumRelevantPerm y π (i.1 + 1) =
        ((relevantRanks y π).filter (fun j => j ≤ i)).card from fun i => by
      simpa [rank1] using cumRelevantPerm_eq_card_filter y π i]
    simp [relevantRanks]
    rw [Finset.sum_filter]

private theorem card_relevantRanks_fiber_eq {L : ℕ} (y : Fin L → Bool)
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

/-- AP mass obtained by enumerating the original permutation sample space. -/
def permutationAPPMF {L : ℕ} (y : Fin L → Bool) (a : ℚ) : ℚ :=
  (((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
      (fun π => averagePrecisionOfRanks (relevantRanks y π) = a)).card : ℚ) /
    Fintype.card (Equiv.Perm (Fin L))

/-- Probability mass of a real AP value in the existing uniform-permutation
model. -/
noncomputable def uniformAPMass {L : ℕ} (y : Fin L → Bool) (x : ℝ) : ℝ :=
  uniformAvgOverPerms (fun π => if apUnderPerm y π = x then 1 else 0)

/-- The finite support of AP for `M` relevant items in `L` ranks. -/
def apSupport (L M : ℕ) : Finset ℚ :=
  ((Finset.univ : Finset (Fin L)).powersetCard M).image averagePrecisionOfRanks

/-- Exact AP probability mass function under a uniformly random ranking.
The numerator counts relevant-rank sets giving `a`; the denominator counts all
`M`-subsets of the `L` ranks. -/
def apPMF (L M : ℕ) (a : ℚ) : ℚ :=
  ((((Finset.univ : Finset (Fin L)).powersetCard M).filter
      (fun s => averagePrecisionOfRanks s = a)).card : ℚ) /
    Nat.choose L M

/-- The rank-set PMF is exactly the pushforward of the repository's uniform
permutation model. -/
theorem permutationAPPMF_eq_apPMF {L : ℕ} (y : Fin L → Bool) (a : ℚ) :
    permutationAPPMF y a = apPMF L (numRelevant y) a := by
  classical
  let f : Equiv.Perm (Fin L) → Finset (Fin L) := relevantRanks y
  let ranks := (Finset.univ : Finset (Fin L)).powersetCard (numRelevant y)
  let event := ranks.filter (fun s => averagePrecisionOfRanks s = a)
  let s0 := f (Equiv.refl (Fin L))
  let K := ((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
    (fun π => f π = s0)).card
  have hfmem (π : Equiv.Perm (Fin L)) : f π ∈ ranks := by
    simp [f, ranks, card_relevantRanks]
  have hs0card : s0.card = numRelevant y := by
    simp [s0, f, card_relevantRanks]
  have hKpos : 0 < K := by
    apply Finset.card_pos.mpr
    exact ⟨Equiv.refl (Fin L), by simp [s0]⟩
  have hfiber (s : Finset (Fin L)) (hs : s ∈ ranks) :
      ((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
        (fun π => f π = s)).card = K := by
    have hscard : s.card = numRelevant y := by
      simpa [ranks] using (Finset.mem_powersetCard.mp hs).2
    simpa [f, K] using card_relevantRanks_fiber_eq y
      (s := s) (t := s0) (hscard.trans hs0card.symm)
  have htotal : Fintype.card (Equiv.Perm (Fin L)) = ranks.card * K := by
    calc
      Fintype.card (Equiv.Perm (Fin L)) =
          (Finset.univ : Finset (Equiv.Perm (Fin L))).card := by simp
      _ = ∑ s ∈ ranks,
          ((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
            (fun π => f π = s)).card :=
        Finset.card_eq_sum_card_fiberwise (fun π _ => hfmem π)
      _ = ∑ _ ∈ ranks, K :=
        Finset.sum_congr rfl (fun s hs => hfiber s hs)
      _ = ranks.card * K := by simp
  have hevent :
      ((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
        (fun π => averagePrecisionOfRanks (f π) = a)).card = event.card * K := by
    calc
      _ = (Finset.univ.filter (fun π : Equiv.Perm (Fin L) => f π ∈ event)).card := by
        congr 1
        ext π
        simp [event, hfmem]
      _ = ∑ s ∈ event,
          ((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
            (fun π => f π = s)).card :=
        (Finset.sum_card_fiberwise_eq_card_filter Finset.univ event f).symm
      _ = ∑ _ ∈ event, K := by
        apply Finset.sum_congr rfl
        intro s hs
        apply hfiber s
        have hs' : s ∈ ranks ∧ averagePrecisionOfRanks s = a := by
          simpa [event] using hs
        exact hs'.1
      _ = event.card * K := by simp
  have hranks : ranks.card = Nat.choose L (numRelevant y) := by simp [ranks]
  unfold permutationAPPMF apPMF
  rw [show ((Finset.univ : Finset (Equiv.Perm (Fin L))).filter
      (fun π => averagePrecisionOfRanks (relevantRanks y π) = a)).card =
      event.card * K by simpa [f] using hevent, htotal, ← hranks]
  change ((event.card * K : ℕ) : ℚ) / ((ranks.card * K : ℕ) : ℚ) =
    (event.card : ℚ) / (ranks.card : ℚ)
  push_cast
  field_simp [Nat.ne_of_gt hKpos]

/-- Closed form for every atom of the AP distribution in the original model. -/
theorem uniformAPMass_closed_form {L : ℕ} (y : Fin L → Bool) (a : ℚ) :
    uniformAPMass y (a : ℝ) = (apPMF L (numRelevant y) a : ℝ) := by
  rw [← permutationAPPMF_eq_apPMF]
  simp [uniformAPMass, uniformAvgOverPerms, permutationAPPMF,
    apUnderPerm_eq_averagePrecisionOfRanks, Finset.sum_boole]

theorem uniformAPMass_closed_form_explicit {L : ℕ} (y : Fin L → Bool) (a : ℚ) :
    uniformAPMass y (a : ℝ) =
      ((((Finset.univ : Finset (Fin L)).powersetCard (numRelevant y)).filter
        (fun s => averagePrecisionOfRanks s = a)).card : ℝ) /
        Nat.choose L (numRelevant y) := by
  rw [uniformAPMass_closed_form]
  simp [apPMF]

/-- Distinct rank sets can collide: `(2, 6)` and `(3, 4)` both give `5/12`. -/
example : apPMF 6 2 (5 / 12) = 2 / 15 := by native_decide

/-- The closed finite formula is a probability distribution. -/
theorem sum_apPMF_eq_one {L M : ℕ} (hML : M ≤ L) :
    ∑ a ∈ apSupport L M, apPMF L M a = 1 := by
  classical
  let ranks := (Finset.univ : Finset (Fin L)).powersetCard M
  have hcount : ranks.card = Nat.choose L M := by simp [ranks]
  have hchoose : (Nat.choose L M : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hML))
  rw [show apSupport L M = ranks.image averagePrecisionOfRanks by rfl]
  simp only [apPMF, ranks]
  rw [← Finset.sum_div]
  rw [div_eq_iff hchoose, one_mul]
  exact_mod_cast
    (Finset.card_eq_sum_card_image averagePrecisionOfRanks ranks).symm.trans hcount

end ExpectedAp
