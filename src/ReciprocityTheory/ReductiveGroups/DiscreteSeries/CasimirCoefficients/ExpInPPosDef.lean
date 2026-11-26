module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.MomentMatch
public import Lemmata.GeneralBFact.Imports

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool}

open PolarDecomposition

private lemma Jm_mul_self_eq_one' : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private lemma Jm_conjTranspose_eq_self' : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  change star (if ε a = true then (1 : ℂ) else -1) = _
  split_ifs <;> simp

lemma isHermitian_of_mem_noncompactPart' {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Xᴴ = X := by
  obtain ⟨hG, hXJ⟩ := hX
  have hJ := Jm_mul_self_eq_one' (ε := ε)
  have h1 : Xᴴ * Jm ε = X * Jm ε := by
    rw [hXJ]
    unfold inG at hG
    exact eq_neg_of_add_eq_zero_left hG
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = X * Jm ε * Jm ε := by rw [h1]
    _ = X := by rw [mul_assoc, hJ, mul_one]

lemma inP_JXJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Jm ε * X * Jm ε = -X := by
  rw [mul_assoc, hX.2, mul_neg, ← mul_assoc, Jm_mul_self_eq_one', one_mul]

lemma toMK_facts (k : KG ε) : (toMK k)ᴴ * toMK k = 1 ∧ toMK k * (toMK k)ᴴ = 1 ∧
    toMK k * Jm ε = Jm ε * toMK k := by
  have hk : toMK k ∈ Kset ε := k.2
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_, hc⟩
  · have h := Matrix.mem_unitaryGroup_iff'.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  · have h := Matrix.mem_unitaryGroup_iff.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h

lemma toMK_inv (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h1 : toMK k⁻¹ * toMK k = 1 := by
    unfold toMK toM
    simp
  have h2 := (toMK_facts k).2.1
  calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * (toMK k)ᴴ) := by rw [h2, mul_one]
    _ = (toMK k)ᴴ := by rw [← mul_assoc, h1, one_mul]

lemma exists_toMK {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : ∃ u : KG ε, toMK u = k := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k * kᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  have h2 : kᴴ * k = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUJ : inUJ ε k := by
    unfold inUJ
    rw [mul_assoc, ← hc, ← mul_assoc, h2, one_mul]
  refine ⟨⟨⟨⟨k, kᴴ, h1, h2⟩, ?_⟩, ?_⟩, rfl⟩
  · exact hUJ
  · exact (⟨hu, hc⟩ : k ∈ Kset ε)

lemma kexp_sq (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hH : Xᴴ = X) :
    (toMK k * NormedSpace.exp X)ᴴ * (toMK k * NormedSpace.exp X) = NormedSpace.exp (X + X) := by
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, hH, mul_assoc, ← mul_assoc (toMK k)ᴴ,
    (toMK_facts k).1, one_mul, ← Matrix.exp_add_of_commute _ _ (Commute.refl _)]

theorem polar_exists {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X ∧ g = toMK k * NormedSpace.exp X := by
  obtain ⟨k, hk, Y, hY, hgk⟩ := polar_UJ (ε := ε) (g := g) hg
  obtain ⟨u, hu⟩ := exists_toMK hk
  exact ⟨u, Y, hY, by rw [hu]; exact hgk⟩

theorem polar_unique {k k' : KG ε} {X X' : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (hX' : inP ε X')
    (h : toMK k * NormedSpace.exp X = toMK k' * NormedSpace.exp X') : k = k' ∧ X = X' := by
  have hH := isHermitian_of_mem_noncompactPart' hX
  have hH' := isHermitian_of_mem_noncompactPart' hX'
  have hXX : X + X = X' + X' := by
    refine polar_exp_inj (by rw [conjTranspose_add, hH]) (by rw [conjTranspose_add, hH']) ?_
    rw [← kexp_sq k hH, ← kexp_sq k' hH', h]
  have hXe : X = X' := polar_half hXX
  subst hXe
  refine ⟨?_, rfl⟩
  have hm : toMK k = toMK k' := by
    have := congrArg (· * NormedSpace.exp (-X)) h
    simp only [Matrix.mul_assoc, polar_exp_mul_neg, Matrix.mul_one] at this
    exact this
  exact Subtype.ext (Subtype.ext (Units.ext hm))

theorem inUJ_kexp (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : inUJ ε (toMK k * NormedSpace.exp X) := by
  have hJ := Jm_mul_self_eq_one' (ε := ε)
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJ, hJ⟩, rfl⟩
  have hconj : Jm ε * NormedSpace.exp X * Jm ε = NormedSpace.exp (-X) := by
    have h := Matrix.exp_conj (Jm ε) X hJu
    rw [hJinv, inP_JXJ hX] at h
    exact h.symm
  have hf := toMK_facts k
  unfold inUJ
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, isHermitian_of_mem_noncompactPart' hX]
  calc NormedSpace.exp X * (toMK k)ᴴ * Jm ε * (toMK k * NormedSpace.exp X)
      = NormedSpace.exp X * ((toMK k)ᴴ * (Jm ε * toMK k)) * NormedSpace.exp X := by
        simp only [mul_assoc]
    _ = NormedSpace.exp X * ((toMK k)ᴴ * (toMK k * Jm ε)) * NormedSpace.exp X := by
        rw [← hf.2.2]
    _ = NormedSpace.exp X * Jm ε * NormedSpace.exp X := by
        rw [← mul_assoc (toMK k)ᴴ, hf.1, one_mul]
    _ = Jm ε * (Jm ε * NormedSpace.exp X * Jm ε) * NormedSpace.exp X := by
        simp only [← mul_assoc, hJ, one_mul]
    _ = Jm ε * NormedSpace.exp (-X) * NormedSpace.exp X := by rw [hconj]
    _ = Jm ε := by
        rw [mul_assoc, ← Matrix.exp_add_of_commute _ _ ((Commute.refl X).neg_left), neg_add_cancel,
          NormedSpace.exp_zero, mul_one]

theorem inP_conj (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    inP ε (toMK k * X * toMK k⁻¹) ∧
      NormedSpace.exp (toMK k * X * toMK k⁻¹) = toMK k * NormedSpace.exp X * toMK k⁻¹ := by
  have hf := toMK_facts k
  have hinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_right_inv hf.2.1
  have hu : IsUnit (toMK k) := ⟨⟨toMK k, (toMK k)ᴴ, hf.2.1, hf.1⟩, rfl⟩
  have hcJ : (toMK k)ᴴ * Jm ε = Jm ε * (toMK k)ᴴ := by
    have h := congrArg Matrix.conjTranspose hf.2.2
    simp only [Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self'] at h
    exact h.symm
  have h2 : toMK k * X * (toMK k)ᴴ * Jm ε = -(Jm ε * (toMK k * X * (toMK k)ᴴ)) := by
    calc toMK k * X * (toMK k)ᴴ * Jm ε = toMK k * (X * Jm ε) * (toMK k)ᴴ := by
          rw [mul_assoc _ (toMK k)ᴴ, hcJ]
          simp only [mul_assoc]
      _ = toMK k * (-(Jm ε * X)) * (toMK k)ᴴ := by rw [hX.2]
      _ = -(Jm ε * (toMK k * X * (toMK k)ᴴ)) := by
          rw [mul_neg, neg_mul, ← mul_assoc (toMK k) (Jm ε) X, hf.2.2]
          simp only [mul_assoc]
  rw [toMK_inv]
  refine ⟨⟨?_, h2⟩, ?_⟩
  · unfold inG
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      isHermitian_of_mem_noncompactPart' hX, ← mul_assoc (toMK k) X, h2, neg_add_cancel]
  · have h := Matrix.exp_conj (toMK k) X hu
    rwa [hinv] at h

theorem exp_noncompactPart_posDef {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : (NormedSpace.exp X).PosDef := by
  have hH : Xᴴ = X := isHermitian_of_mem_noncompactPart' hX
  have hYH : ((1 / 2 : ℂ) • X)ᴴ = (1 / 2 : ℂ) • X := by
    rw [Matrix.conjTranspose_smul, hH]
    norm_num
  have hsplit : NormedSpace.exp X =
      (NormedSpace.exp ((1 / 2 : ℂ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℂ) • X) := by
    rw [← Matrix.exp_conjTranspose, hYH, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
    norm_num
  rw [hsplit]
  apply Matrix.PosDef.conjTranspose_mul_self
  exact Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_exp _)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFactsA
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma kfa_mul_Jm_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Y * Jm ε) a b = Y a b * (if ε b then 1 else -1) := by
  unfold Jm
  rw [Matrix.mul_diagonal]

lemma kfa_Jm_mul_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * Y) a b = (if ε a then 1 else -1) * Y a b := by
  unfold Jm
  rw [Matrix.diagonal_mul]

lemma kfa_comm_iff_block (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y * Jm ε = Jm ε * Y ↔ IsBlock ε Y := by
  constructor
  · intro h a b hab
    have h1 := congrFun (congrFun h a) b
    rw [kfa_mul_Jm_apply, kfa_Jm_mul_apply] at h1
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
      simp [ha, hb] at h1 hab <;>
      first
      | exact h1
      | linear_combination h1
      | linear_combination (-1 / 2 : ℂ) * h1
      | linear_combination (1 / 2 : ℂ) * h1
  · intro h
    ext a b
    rw [kfa_mul_Jm_apply, kfa_Jm_mul_apply]
    by_cases hab : ε a = ε b
    · rw [hab]
      ring
    · rw [h a b hab]
      ring

lemma kfa_inK_iff (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inK ε Y ↔ Yᴴ = -Y ∧ IsBlock ε Y := by
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  unfold inK inG
  rw [← kfa_comm_iff_block]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 : (Yᴴ + Y) * Jm ε = 0 := by
      rw [Matrix.add_mul, h2]
      exact h1
    have h4 := congrArg (· * Jm ε) h3
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, Matrix.zero_mul] at h4
    exact eq_neg_of_add_eq_zero_left h4
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, Matrix.neg_mul, h2, neg_add_cancel]

section ExpL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma kfa_exp_cont (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  first
  | exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)
  | fun_prop

lemma kfa_exp_comm {J X : Matrix (Fin n) (Fin n) ℂ} (h : X * J = J * X) :
    NormedSpace.exp X * J = J * NormedSpace.exp X := Commute.exp_left h

end ExpL

lemma kfa_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]

lemma kfa_exp_mul_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_right, add_neg_cancel, NormedSpace.exp_zero]

lemma kfa_exp_conjTranspose {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = -Y) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Y))ᴴ = NormedSpace.exp (-((t : ℂ) • Y)) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hY, smul_neg]
  simp only [Complex.star_def, Complex.conj_ofReal]

def kfaUnit (Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  ⟨NormedSpace.exp ((t : ℂ) • Y), NormedSpace.exp (-((t : ℂ) • Y)), kfa_exp_mul_neg _, kfa_exp_neg_mul _⟩

lemma kfa_mem_Kset (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) ∈ Kset ε := by
  have hYJ : Y * Jm ε = Jm ε * Y := hY.2
  have hsk : Yᴴ = -Y := ((kfa_inK_iff ε Y).1 hY).1
  unfold Kset
  rw [Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, kfa_exp_conjTranspose hsk,
      kfa_exp_mul_neg]
  · exact kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])

lemma kfa_inUJ (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • Y)) := by
  have hYJ : Y * Jm ε = Jm ε * Y := hY.2
  have hsk : Yᴴ = -Y := ((kfa_inK_iff ε Y).1 hY).1
  have hc : NormedSpace.exp ((t : ℂ) • Y) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • Y) :=
    kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])
  unfold inUJ
  rw [kfa_exp_conjTranspose hsk, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, kfa_exp_neg_mul,
    Matrix.one_mul]

def kfaUJ (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) : UJ ε :=
  ⟨kfaUnit Y t, kfa_inUJ ε hY t⟩

def kfaKG (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) : KG ε :=
  ⟨kfaUJ ε hY t, kfa_mem_Kset ε hY t⟩

lemma kfa_toMK (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    toMK (kfaKG ε hY t) = NormedSpace.exp ((t : ℂ) • Y) := rfl

lemma kfa_continuous (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    Continuous (kfaKG ε hY) := by
  have hu : Continuous (kfaUnit Y) := by
    refine Units.continuous_iff.2 ⟨kfa_exp_cont Y, ?_⟩
    show Continuous fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y))
    simpa only [smul_neg] using kfa_exp_cont (-Y)
  exact (hu.subtype_mk _).subtype_mk _

lemma kfa_add (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (s t : ℝ) :
    kfaKG ε hY (s + t) = kfaKG ε hY s * kfaKG ε hY t := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) =
    NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y)
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

instance kf_isHaar (ε : Fin n → Bool) : (muK ε).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

theorem compactSpace_KG (ε : Fin n → Bool) : CompactSpace (KG ε) := by
  have hc : IsCompact (Kset ε) := by
    have hsub : Kset ε ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
        (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) := by
      intro g hg i _ j _
      simpa [Metric.mem_closedBall, dist_zero_right] using entry_norm_bound_of_unitary hg.1 i j
    exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_Kset ε) hsub
  have hK : IsCompact ((KG ε : Set (UJ ε))) :=
    (isClosedEmbedding_toM ε).isCompact_preimage hc
  exact isCompact_iff_compactSpace.mp hK

theorem muK_univ_pos (ε : Fin n → Bool) : 0 < (muK ε Set.univ).toReal := by
  have := compactSpace_KG ε
  exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero (muK ε) Set.univ_nonempty)
    (isCompact_univ.measure_lt_top (μ := muK ε)).ne

theorem muK_rightInvariant (ε : Fin n → Bool) : (muK ε).IsMulRightInvariant := by
  have := compactSpace_KG ε
  refine ⟨fun k => ?_⟩
  set ν := Measure.map (fun x => x * k) (muK ε) with hν
  have : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace ν (muK ε)
  have hu : ν Set.univ = muK ε Set.univ := by
    rw [hν, Measure.map_apply (measurable_mul_const k) MeasurableSet.univ, Set.preimage_univ]
  have hpos : muK ε Set.univ ≠ 0 := (isOpen_univ.measure_pos (muK ε) Set.univ_nonempty).ne'
  have htop : muK ε Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  rw [h, smul_apply, ENNReal.smul_def, smul_eq_mul] at hu
  have hc : (Measure.haarScalarFactor ν (muK ε) : ℝ≥0∞) = 1 := by
    have := (ENNReal.mul_eq_right hpos htop).mp hu
    exact this
  rw [h, ENNReal.coe_eq_one.mp hc, one_smul]

theorem exists_oneParam (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    ∃ γ : ℝ → KG ε, Continuous γ ∧ (∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) ∧
      ∀ s t, γ (s + t) = γ s * γ t := by
  exact ⟨kfaKG ε hY, kfa_continuous ε hY, kfa_toMK ε hY, kfa_add ε hY⟩

theorem inK_iff (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : inK ε Y ↔ Yᴴ = -Y ∧ IsBlock ε Y := by
  unfold inK IsBlock inG
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hcomm : Y * Jm ε = Jm ε * Y ↔ ∀ a b, ε a ≠ ε b → Y a b = 0 := by
    constructor
    · intro h a b hab
      have h1 := congrFun (congrFun h a) b
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
      have hdb : (if ε b then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
      have hda : (if ε a then (1 : ℂ) else -1) = -(if ε b then (1 : ℂ) else -1) := by
        cases ha : ε a <;> cases hb : ε b <;> simp_all
      rw [hda] at h1
      have h5 : 2 * (Y a b * (if ε b then (1 : ℂ) else -1)) = 0 := by linear_combination h1
      exact (mul_eq_zero.mp ((mul_eq_zero.mp h5).resolve_left two_ne_zero)).resolve_right hdb
    · intro h
      ext a b
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hab : ε a = ε b
      · rw [hab]
        ring
      · rw [h a b hab]
        ring
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, hcomm.mp h2⟩
    have h3 : Yᴴ * Jm ε = -(Y * Jm ε) := by
      rw [h2]
      exact eq_neg_of_add_eq_zero_left h1
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(Y * Jm ε) * Jm ε := by rw [h3]
      _ = -Y := by rw [Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  · rintro ⟨h1, h2⟩
    have h4 := hcomm.mpr h2
    refine ⟨?_, h4⟩
    rw [h1, Matrix.neg_mul, h4, neg_add_cancel]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem exists_mu {lam : Fin n → ℝ} (hlam : IsHCParam lam) : ∃ μ : Fin n → ℤ, IsMu lam μ := by
  choose m hm using hlam.2
  refine ⟨fun a => m a + (n : ℤ) - 1 - ((a : ℕ) : ℤ), ?_⟩
  unfold IsMu
  intro a
  have h := hm a
  simp only [rho]
  push_cast
  linarith

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsOfFormula
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def PsiFormulaStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ)) ∧
      (∀ μ : Fin n → ℤ, IsMu lam μ → ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
        Ψ (NormedSpace.exp X) =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))

section Gelfand

variable {F : Type*} [AddCommGroup F] [Module ℂ F]

def opPow (A : Fin n → Fin n → F → F) : ℕ → Fin n → Fin n → F → F
  | 0, a, b, f => if a = b then f else 0
  | k + 1, a, b, f => ∑ c, A a c (opPow A k c b f)

def opGelfand (A : Fin n → Fin n → F → F) (k : ℕ) (f : F) : F := ∑ a, opPow A k a a f

end Gelfand

section Right

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def rightE (ε : Fin n → Bool) : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E) :=
  fun a b f => EabV ε a b f

def rightEanti (ε : Fin n → Bool) : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E) :=
  fun a b f => -EabV ε (Fin.rev b) (Fin.rev a) f

end Right

def PsiAllStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ)) ∧
      (∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        opGelfand (rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
        opGelfand (rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g) ∧
      (∀ μ : Fin n → ℤ, IsMu lam μ → ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
        Ψ (NormedSpace.exp X) =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DerivGA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section PathL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma dga_exp (W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • W)) W 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) W (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • W)) = fun u : ℝ => NormedSpace.exp (u • W) := by
    funext t
    rw [Complex.coe_smul]
  rw [e]
  exact h

lemma dga_path (Y z : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y)) * z * NormedSpace.exp ((t : ℂ) • Y))
      (z * Y - Y * z) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y))) (-Y) 0 := by
    have h := dga_exp (-Y)
    simpa [smul_neg] using h
  have h2 := dga_exp Y
  have e0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  have e1 : NormedSpace.exp (-(((0 : ℝ) : ℂ) • Y)) = 1 := by simp
  have h3 := (h1.mul_const z).mul h2
  simp only [e0, e1, mul_one, one_mul] at h3
  have e2 : -Y * z + z * Y = z * Y - Y * z := by noncomm_ring
  rw [e2] at h3
  exact h3

end PathL

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCasA
noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_entry (a b : Fin n) {m : ℕ∞ω} :
    ContDiff ℂ m (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
  exact (contDiff_apply ℂ (fun _ => ℂ) b).comp (contDiff_apply ℂ (fun _ => (Fin n → ℂ)) a)

theorem contDiff_lead (i : ℕ) {m : ℕ∞ω} : ContDiff ℂ m (lead (n := n) i) := by
  unfold lead
  by_cases h : i ≤ n
  · simp only [h, dif_pos]
    simp only [Matrix.det_apply, Units.smul_def]
    refine ContDiff.sum fun σ _ => ?_
    refine ContDiff.const_smul _ ?_
    refine contDiff_prod fun k _ => ?_
    simp only [Matrix.submatrix_apply]
    exact contDiff_entry _ _
  · simp only [h, dif_neg, not_false_eq_true]
    exact contDiff_const

theorem contDiffAt_zpow_lead (i : ℕ) (k : ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : lead i z ≠ 0)
    {m : ℕ∞ω} : ContDiffAt ℂ m (fun w => lead i w ^ k) z := by
  have hl : ContDiffAt ℂ m (lead (n := n) i) z := (contDiff_lead i).contDiffAt
  rcases k with k | k
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact hl.pow k
  · simp only [zpow_negSucc]
    exact (hl.pow (k + 1)).inv (pow_ne_zero _ hz)

theorem contDiffAt_phiM (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    {m : ℕ∞ω} : ContDiffAt ℂ m (PhiM μ) z := by
  unfold PhiM
  exact contDiffAt_prod fun i _ => contDiffAt_zpow_lead _ _ (hz i)

theorem differentiableAt_phiM (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ (PhiM μ) z := by
  exact (contDiffAt_phiM μ hz (m := 1)).differentiableAt (by norm_num)

theorem hasDerivAt_line {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : DifferentiableAt ℂ F z) (v : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℂ => F (z + t • v)) (fderiv ℂ F z v) 0 := by
  have hl : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
    rw [one_smul] at h
    exact h
  have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • v) := by
    simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℂ) hl

def mulLeftCLM (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)

theorem lhol_lhol_eq {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (Lhol Y F) z = fderiv ℂ F z (Y * (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) := by
  unfold Lhol
  have hc : DifferentiableAt ℂ (fderiv ℂ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hu : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => Y * y) (mulLeftCLM Y) z :=
    (mulLeftCLM Y).hasFDerivAt
  have h := hc.hasFDerivAt.clm_apply hu
  erw [h.fderiv]
  rfl

theorem lhol_comm {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (Lhol Y F) z = Lhol Y (Lhol X F) z + fderiv ℂ F z ((Y * X - X * Y) * z) := by
  rw [lhol_lhol_eq hF, lhol_lhol_eq hF]
  have hs := hF.isSymmSndFDerivAt (by simp)
  have h1 : fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z) = fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) :=
    hs _ _
  have h2 : fderiv ℂ F z ((Y * X - X * Y) * z) =
      fderiv ℂ F z (Y * (X * z)) - fderiv ℂ F z (X * (Y * z)) := by
    rw [Matrix.sub_mul, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  linear_combination -h1 - h2

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CBinet
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private lemma cb_det_mul_fun {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  have hrow : A * B = Matrix.of (fun a => ∑ j, A a j • B j) := by
    ext a b
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrow]
  have h1 := (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap.map_sum
    (fun a j => A a j • B j)
  have h2 : ∀ f : Fin i → Fin N,
      (Matrix.detRowAlternating (R := R) (n := Fin i)).toMultilinearMap (fun a => A a (f a) • B (f a)) =
        (∏ a, A a (f a)) * (B.submatrix f id).det := by
    intro f
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    rfl
  exact h1.trans (Finset.sum_congr rfl fun f _ => h2 f)

private def cbPar {i N : ℕ} (p : (Σ _ : {S : Finset (Fin N) // S.card = i}, Equiv.Perm (Fin i))) :
    Fin i ↪ Fin N :=
  p.2.toEmbedding.trans (p.1.1.orderEmbOfFin p.1.2).toEmbedding

private lemma cbPar_image {i N : ℕ} (S : Finset (Fin N)) (hS : S.card = i) (σ : Equiv.Perm (Fin i)) :
    univ.map (cbPar ⟨⟨S, hS⟩, σ⟩) = S := by
  simp only [cbPar]
  rw [← Finset.map_map, Finset.map_univ_equiv]
  exact Finset.map_orderEmbOfFin_univ S hS

private lemma cbPar_bij {i N : ℕ} : Function.Bijective (cbPar (i := i) (N := N)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨S, hS⟩, σ⟩ ⟨⟨S', hS'⟩, σ'⟩ h
    have hSS : S = S' := by
      rw [← cbPar_image S hS σ, ← cbPar_image S' hS' σ', h]
    subst hSS
    have hσ : σ = σ' := by
      ext a
      have h2 := DFunLike.congr_fun h a
      exact congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)
    subst hσ
    rfl
  · intro g
    have hcard : (univ.map g).card = i := by simp
    have hmem : ∀ a, g a ∈ univ.map g := fun a => Finset.mem_map_of_mem g (Finset.mem_univ a)
    let g' : Fin i ≃ (univ.map g) := Equiv.ofBijective (fun a => ⟨g a, hmem a⟩)
      ⟨fun a b h => g.injective (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
        obtain ⟨a, _, rfl⟩ := Finset.mem_map.1 hx
        exact ⟨a, rfl⟩⟩
    refine ⟨⟨⟨univ.map g, hcard⟩, g'.trans ((univ.map g).orderIsoOfFin hcard).symm.toEquiv⟩, ?_⟩
    refine DFunLike.ext _ _ fun a => ?_
    change ((univ.map g).orderEmbOfFin hcard) (((univ.map g).orderIsoOfFin hcard).symm (g' a)) = g a
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    rfl

theorem det_mul_eq_sum_submatrix {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ S : {S : Finset (Fin N) // S.card = i},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  have hz : ∀ f : Fin i → Fin N, ¬ Function.Injective f →
      (∏ a, A a (f a)) * (B.submatrix f id).det = 0 := by
    intro f hf
    simp only [Function.Injective, not_forall] at hf
    obtain ⟨a, b, hab, hne⟩ := hf
    rw [Matrix.det_zero_of_row_eq hne (by funext c; simp [hab]), mul_zero]
  have hS : ∀ S : {S : Finset (Fin N) // S.card = i},
      ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det =
        (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
    intro S
    have hA : (A.submatrix id (S.1.orderEmbOfFin S.2)).det =
        ∑ σ : Equiv.Perm (Fin i), ((Equiv.Perm.sign σ : ℤ) : R) *
          ∏ a, A a (S.1.orderEmbOfFin S.2 (σ a)) := by
      rw [← Matrix.det_transpose, Matrix.det_apply']
      rfl
    rw [hA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hB : B.submatrix (cbPar ⟨S, σ⟩) id = (B.submatrix (S.1.orderEmbOfFin S.2) id).submatrix σ id := rfl
    rw [hB, Matrix.det_permute]
    change (∏ a, A a (S.1.orderEmbOfFin S.2 (σ a))) * _ = _
    ring
  calc (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det :=
        cb_det_mul_fun A B
    _ = ∑ f ∈ univ.filter Function.Injective, (∏ a, A a (f a)) * (B.submatrix f id).det :=
        (Finset.sum_filter_of_ne fun f _ hf => by
          by_contra hni
          exact hf (hz f hni)).symm
    _ = ∑ x : {f : Fin i → Fin N // Function.Injective f},
          (∏ a, A a (x.1 a)) * (B.submatrix x.1 id).det :=
        Finset.sum_subtype _ (fun f => by simp) _
    _ = ∑ g : Fin i ↪ Fin N, (∏ a, A a (g a)) * (B.submatrix g id).det :=
        Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding _ _) _ _ (fun _ => rfl)
    _ = ∑ p, (∏ a, A a (cbPar p a)) * (B.submatrix (cbPar p) id).det :=
        (cbPar_bij.sum_comp (fun g : Fin i ↪ Fin N => (∏ a, A a (g a)) * (B.submatrix g id).det)).symm
    _ = ∑ S, ∑ σ : Equiv.Perm (Fin i), (∏ a, A a (cbPar ⟨S, σ⟩ a)) * (B.submatrix (cbPar ⟨S, σ⟩) id).det :=
        Fintype.sum_sigma _
    _ = _ := Finset.sum_congr rfl fun S _ => hS S

theorem lead_unitary_diag {U : Matrix (Fin n) (Fin n) ℂ} (d : Fin n → ℂ) (i : ℕ) (hi : i ≤ n) :
    lead i (U * Matrix.diagonal d * Uᴴ) =
      ∑ J : {J : Finset (Fin n) // J.card = i},
        ((‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 : ℝ) : ℂ) * ∏ j ∈ J.1, d j := by
  unfold lead
  rw [dite_eq_left hi]
  have hsub : (U * Matrix.diagonal d * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      (U.submatrix (Fin.castLE hi) id * Matrix.diagonal d) * (U.submatrix (Fin.castLE hi) id)ᴴ := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hsub, det_mul_eq_sum_submatrix]
  refine Finset.sum_congr rfl fun J _ => ?_
  have h1 : (U.submatrix (Fin.castLE hi) id * Matrix.diagonal d).submatrix id (J.1.orderEmbOfFin J.2) =
      U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2) *
        Matrix.diagonal (fun a => d (J.1.orderEmbOfFin J.2 a)) := by
    ext a b
    simp [Matrix.mul_diagonal]
  have h2 : (U.submatrix (Fin.castLE hi) id)ᴴ.submatrix (J.1.orderEmbOfFin J.2) id =
      (U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2))ᴴ := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  have hp : ∏ a, d (J.1.orderEmbOfFin J.2 a) = ∏ j ∈ J.1, d j := by
    calc ∏ a, d (J.1.orderEmbOfFin J.2 a)
        = ∏ j ∈ univ.map (J.1.orderEmbOfFin J.2).toEmbedding, d j := (Finset.prod_map _ _ _).symm
      _ = ∏ j ∈ J.1, d j := by rw [Finset.map_orderEmbOfFin_univ]
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1, h2, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose, hp, hn]
  ring

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
