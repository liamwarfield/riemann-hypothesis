module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.KdMeasImageProd
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarPol
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQ
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.BridgeA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.JacobianNearOneOfSmall
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.ContinuousMatrixExpCompact
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem compactMatrix_off_block {ε : Fin n → Bool} (w : KCo ε) {a b : Fin n} (h : ε a ≠ ε b) :
    kMat w a b = 0 := by
  have hab : a ≠ b := fun e => h (e ▸ rfl)
  unfold kMat
  rw [if_neg hab, dif_neg (fun h' => h h'.2), dif_neg (fun h' => h h'.2.symm)]

theorem compactMatrix_conjTranspose {ε : Fin n → Bool} (w : KCo ε) : (kMat w)ᴴ = -kMat w := by
  ext a b
  change star (kMat w b a) = -(kMat w a b)
  by_cases hab : a = b
  · subst hab
    simp only [kMat, if_true]
    simp [Complex.ext_iff]
  · have hba : b ≠ a := Ne.symm hab
    by_cases h1 : b < a ∧ ε a = ε b
    · have h2 : ¬ (a < b ∧ ε b = ε a) := fun h => lt_asymm h.1 h1.1
      simp only [kMat, if_neg hab, if_neg hba, dif_pos h1, dif_neg h2, star_neg, star_star]
    · by_cases h2 : a < b ∧ ε b = ε a
      · simp only [kMat, if_neg hab, if_neg hba, dif_pos h2, dif_neg h1, neg_neg]
      · simp only [kMat, if_neg hab, if_neg hba, dif_neg h2, dif_neg h1, star_zero, neg_zero]

theorem compactMatrix_comm_signature {ε : Fin n → Bool} (w : KCo ε) : kMat w * Jm ε = Jm ε * kMat w := by
  ext a b
  simp only [Jm, mul_diagonal, diagonal_mul]
  by_cases h : ε a = ε b
  · rw [h, mul_comm]
  · rw [compactMatrix_off_block w h]; simp

theorem compactMatrix_inK {ε : Fin n → Bool} (w : KCo ε) : inK ε (kMat w) := by
  refine ⟨?_, compactMatrix_comm_signature w⟩
  unfold inG
  rw [compactMatrix_conjTranspose, Matrix.neg_mul, compactMatrix_comm_signature, neg_add_cancel]

theorem exists_compact_exp {ε : Fin n → Bool} (w : KCo ε) :
    ∃ k : KG ε, toMK k = NormedSpace.exp (kMat w) :=
  exists_toMK (exp_mem_Kset (compactMatrix_inK w))

theorem compactMatrix_injective (ε : Fin n → Bool) : Function.Injective (kMat (ε := ε)) := by
  intro w w' h
  have h1 : ∀ a b, kMat w a b = kMat w' a b := fun a b => by rw [h]
  refine Prod.ext (funext fun a => ?_) (funext fun ab => ?_)
  · have h2 := congrArg Complex.im (h1 a a)
    simpa [kMat] using h2
  · have h2 := h1 ab.1.1 ab.1.2
    have hne : ab.1.1 ≠ ab.1.2 := ne_of_gt ab.2.1
    simp only [kMat, if_neg hne, dif_pos ab.2] at h2
    exact h2

theorem compactMatrix_continuous (ε : Fin n → Bool) :
    Continuous (fun w : KCo ε => (kMat w : Matrix (Fin n) (Fin n) ℂ)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold kMat
  by_cases h0 : a = b
  · simp only [h0, if_true]; fun_prop
  · simp only [if_neg h0]
    by_cases h1 : b < a ∧ ε a = ε b
    · simp only [dif_pos h1]; fun_prop
    · simp only [dif_neg h1]
      by_cases h2 : a < b ∧ ε b = ε a
      · simp only [dif_pos h2]; fun_prop
      · simp only [dif_neg h2]; fun_prop

theorem compactMatrix_zero (ε : Fin n → Bool) : kMat (0 : KCo ε) = 0 := by
  ext a b
  simp only [kMat]
  split_ifs <;> simp

theorem continuous_matrix_exp_compact : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt

theorem exists_exp_injOn_nhds_zero : ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (0 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧
    Set.InjOn (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) U := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] _)) 0 := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  exact ⟨_, (h.toOpenPartialHomeomorph _).open_source, h.mem_toOpenPartialHomeomorph_source,
    (h.toOpenPartialHomeomorph _).injOn⟩

def expCompactMatrix {ε : Fin n → Bool} (w : KCo ε) : Fin n → Fin n → ℂ :=
  (NormedSpace.exp (kMat w) : Matrix (Fin n) (Fin n) ℂ)

theorem continuous_exp_compactMatrix (ε : Fin n → Bool) : Continuous (expCompactMatrix (ε := ε)) :=
  continuous_matrix_exp_compact.comp (compactMatrix_continuous ε)

theorem exp_compact_injOn (ε : Fin n → Bool) : ∃ δ > 0, Set.InjOn (expCompactMatrix (ε := ε)) {w | ‖w‖ < δ} := by
  obtain ⟨U, hU, h0, hinj⟩ := (exists_exp_injOn_nhds_zero (n := n))
  have hV : IsOpen ((fun w : KCo ε => (kMat w : Matrix (Fin n) (Fin n) ℂ)) ⁻¹' U) :=
    hU.preimage (compactMatrix_continuous ε)
  have h0V : (0 : KCo ε) ∈ (fun w : KCo ε => (kMat w : Matrix (Fin n) (Fin n) ℂ)) ⁻¹' U := by
    show kMat (0 : KCo ε) ∈ U
    rw [compactMatrix_zero]; exact h0
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hV 0 h0V
  refine ⟨δ, hδ, fun w hw w' hw' h => compactMatrix_injective ε (hinj ?_ ?_ h)⟩
  · exact hball (by simpa using hw)
  · exact hball (by simpa using hw')

def expImageOfCompact {ε : Fin n → Bool} (B : Set (KCo ε)) : Set (KG ε) :=
  {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)}

def compactToMatrixEntries (ε : Fin n → Bool) : KG ε → (Fin n → Fin n → ℂ) := fun k => toMK k

theorem measurableSet_exp_image {ε : Fin n → Bool} {B : Set (KCo ε)} (hB : MeasurableSet B)
    (hinj : Set.InjOn (expCompactMatrix (ε := ε)) B) : MeasurableSet (expImageOfCompact B) := by
  have hI : MeasurableSet (expCompactMatrix (ε := ε) '' B) :=
    hB.image_of_continuousOn_injOn (continuous_exp_compactMatrix ε).continuousOn hinj
  have hc : Continuous (compactToMatrixEntries ε) := (continuous_toM ε).comp continuous_subtype_val
  have hm : Measurable (compactToMatrixEntries ε) := hc.measurable
  have e : expImageOfCompact B = compactToMatrixEntries ε ⁻¹' (expCompactMatrix (ε := ε) '' B) := by
    ext k
    constructor
    · rintro ⟨w, hw, h⟩
      exact ⟨w, hw, h.symm⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨w, hw, h.symm⟩
  rw [e]
  exact hm hI

theorem polarSet_product_eq {ε : Fin n → Bool} (B : Set (KCo ε)) (C : Set (PCoord ε → ℂ)) :
    polSet (B ×ˢ C) =
      (intMuCD_eM ε) ⁻¹' (intMuCD_pM ε '' (expImageOfCompact B ×ˢ C)) := by
  ext g
  constructor
  · rintro ⟨s, hs, hg⟩
    obtain ⟨k, hk⟩ := exists_compact_exp s.1
    refine ⟨(k, s.2), ⟨⟨s.1, hs.1, hk⟩, hs.2⟩, ?_⟩
    show toMK k * NormedSpace.exp (pmat s.2) = toM g
    rw [hk, hg]
  · rintro ⟨⟨k, z⟩, ⟨⟨w, hw, hk⟩, hz⟩, hg⟩
    refine ⟨(w, z), ⟨hw, hz⟩, ?_⟩
    have hg' : toMK k * NormedSpace.exp (pmat z) = toM g := hg
    rw [← hg', hk]

theorem polar_measure_product_eq {ε : Fin n → Bool} {B : Set (KCo ε)} {C : Set (PCoord ε → ℂ)}
    (hA : MeasurableSet (expImageOfCompact B)) (hC : MeasurableSet C) :
    muPolar ε (polSet (B ×ˢ C)) = (∫⁻ z in C, ENNReal.ofReal (Jac z)) * dk ε (expImageOfCompact B) := by
  let R := expImageOfCompact B ×ˢ C
  have hpolar : MeasurableEmbedding (intMuCD_pM ε) :=
    (show Topology.IsClosedEmbedding (intMuCD_pM ε) from polarM_isClosedEmbedding ε).measurableEmbedding
  have htoM : MeasurableEmbedding (intMuCD_eM ε) :=
    (show Topology.IsClosedEmbedding (intMuCD_eM ε) from isClosedEmbedding_toM ε).measurableEmbedding
  have hT : MeasurableSet (intMuCD_pM ε '' R) := hpolar.measurableSet_image.2 (hA.prod hC)
  have hrange : intMuCD_pM ε '' R ⊆ Set.range (intMuCD_eM ε) := by
    rintro _ ⟨kz, _, rfl⟩
    change polarM kz ∈ Set.range (fun g : UJ ε => toM g)
    rw [range_toM]
    exact polarM_inUJ kz
  rw [polarSet_product_eq]
  change Measure.comap (β := Fin n → Fin n → ℂ) (intMuCD_eM ε) (muPolarMat ε)
    ((intMuCD_eM ε) ⁻¹' (intMuCD_pM ε '' R)) = _
  rw [htoM.comap_apply, Set.image_preimage_eq_of_subset hrange]
  change (Measure.map (β := Fin n → Fin n → ℂ) (intMuCD_pM ε) ((dk ε).prod
    (volume.withDensity fun z => ENNReal.ofReal (Jac z)))) (intMuCD_pM ε '' R) = _
  rw [Measure.map_apply hpolar.measurable hT, Set.preimage_image_eq _ hpolar.injective,
    show R = expImageOfCompact B ×ˢ C from rfl, Measure.prod_prod, withDensity_apply _ hC, mul_comm]

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem eigenvalues_zero (ε : Fin n → Bool) : pev (0 : PCoord ε → ℂ) = 0 := by
  have h0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp only [pmat]
    split_ifs <;> simp
  exact (pmat_isHermitian (0 : PCoord ε → ℂ)).eigenvalues_eq_zero_iff.2 h0

theorem jacobian_zero (ε : Fin n → Bool) : Jac (0 : PCoord ε → ℂ) = 1 := by
  unfold Jac
  rw [eigenvalues_zero]
  simp [shc]

theorem unitary_volume_pos (M : ℕ) : 0 < volU M := by
  unfold volU
  exact Finset.prod_pos fun i _ => by positivity

theorem jacobian_near_one_of_small (ε : Fin n → Bool) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ C : Set (PCoord ε → ℂ), MeasurableSet C → (∀ z ∈ C, ‖z‖ < δ) →
      (∫⁻ z in C, ENNReal.ofReal (Jac z)) ≤ ENNReal.ofReal (1 + η) * volume C ∧
        ENNReal.ofReal (1 - η) * volume C ≤ ∫⁻ z in C, ENNReal.ofReal (Jac z) := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 (jac_continuous ε) 0 η hη
  have hpt : ∀ z : PCoord ε → ℂ, ‖z‖ < δ → |Jac z - 1| < η := fun z hz => by
    have := h z (by simpa [dist_zero_right] using hz)
    rwa [jacobian_zero, Real.dist_eq] at this
  refine ⟨δ, hδ, fun C hC hCδ => ⟨?_, ?_⟩⟩
  · rw [← setLIntegral_const]
    refine lintegral_mono_ae ((ae_restrict_iff' hC).2 (Filter.Eventually.of_forall fun z hz => ?_))
    have := abs_lt.1 (hpt z (hCδ z hz))
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [← setLIntegral_const]
    refine lintegral_mono_ae ((ae_restrict_iff' hC).2 (Filter.Eventually.of_forall fun z hz => ?_))
    have := abs_lt.1 (hpt z (hCδ z hz))
    exact ENNReal.ofReal_le_ofReal (by linarith)

theorem muPolar_near_one (ε : Fin n → Bool) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ (B : Set (KCo ε)) (C : Set (PCoord ε → ℂ)), MeasurableSet B → MeasurableSet C →
      (∀ w ∈ B, ‖w‖ < δ) → (∀ z ∈ C, ‖z‖ < δ) →
      muPolar ε (polSet (B ×ˢ C)) ≤
          ENNReal.ofReal ((1 + η) / (volU (pOf ε) * volU (qOf ε))) * (volume B * volume C) ∧
        ENNReal.ofReal ((1 - η) / (volU (pOf ε) * volU (qOf ε))) * (volume B * volume C) ≤
          muPolar ε (polSet (B ×ˢ C)) := by
  have hm0 : 0 < min η 1 := lt_min hη one_pos
  set t : ℝ := min η 1 / 3 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 3 := by
    have := min_le_right η 1
    rw [ht]; linarith
  have ht2 : 3 * t ≤ η := by
    have := min_le_left η 1
    rw [ht]; linarith
  obtain ⟨δ1, hδ1, hdk⟩ := dk_density ε t ht0
  obtain ⟨δ2, hδ2, hJ⟩ := jacobian_near_one_of_small ε t ht0
  obtain ⟨δ3, hδ3, hinj⟩ := exp_compact_injOn ε
  refine ⟨min δ1 (min δ2 δ3), lt_min hδ1 (lt_min hδ2 hδ3), fun B C hB hC hBδ hCδ => ?_⟩
  have hB1 : ∀ w ∈ B, ‖w‖ < δ1 := fun w hw => lt_of_lt_of_le (hBδ w hw) (min_le_left _ _)
  have hB3 : ∀ w ∈ B, ‖w‖ < δ3 := fun w hw =>
    lt_of_lt_of_le (hBδ w hw) ((min_le_right _ _).trans (min_le_right _ _))
  have hC2 : ∀ z ∈ C, ‖z‖ < δ2 := fun z hz =>
    lt_of_lt_of_le (hCδ z hz) ((min_le_right _ _).trans (min_le_left _ _))
  have hA := measurableSet_exp_image hB (hinj.mono fun w hw => hB3 w hw)
  rw [polar_measure_product_eq hA hC]
  obtain ⟨hd1, hd2⟩ := hdk B hB hB1
  obtain ⟨hj1, hj2⟩ := hJ C hC hC2
  have hV : 0 < volU (pOf ε) * volU (qOf ε) := mul_pos (unitary_volume_pos _) (unitary_volume_pos _)
  set V := volU (pOf ε) * volU (qOf ε) with hVdef
  have hA' : expImageOfCompact B = {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} := rfl
  rw [hA']
  constructor
  · calc (∫⁻ z in C, ENNReal.ofReal (Jac z)) * dk ε {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)}
        ≤ (ENNReal.ofReal (1 + t) * volume C) * (ENNReal.ofReal ((1 + t) / V) * volume B) :=
          mul_le_mul' hj1 hd1
      _ = ENNReal.ofReal ((1 + t) * ((1 + t) / V)) * (volume B * volume C) := by
          rw [ENNReal.ofReal_mul (by linarith)]; ring
      _ ≤ ENNReal.ofReal ((1 + η) / V) * (volume B * volume C) := by
          gcongr
          rw [← mul_div_assoc]
          apply div_le_div_of_nonneg_right _ hV.le
          nlinarith
  · calc ENNReal.ofReal ((1 - η) / V) * (volume B * volume C)
        ≤ ENNReal.ofReal ((1 - t) * ((1 - t) / V)) * (volume B * volume C) := by
          gcongr
          rw [← mul_div_assoc]
          apply div_le_div_of_nonneg_right _ hV.le
          nlinarith
      _ = (ENNReal.ofReal (1 - t) * volume C) * (ENNReal.ofReal ((1 - t) / V) * volume B) := by
          rw [ENNReal.ofReal_mul (by linarith)]; ring
      _ ≤ (∫⁻ z in C, ENNReal.ofReal (Jac z)) * dk ε {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)} :=
          mul_le_mul' hj2 hd2

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bridge
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def cOmega (N : ℕ) : ℝ := 1 / (2 ^ (N * (N - 1) / 2) * volU N)

theorem cOmega_pos (N : ℕ) : 0 < cOmega N := by
  have hv : 0 < volU N := by
    unfold volU
    apply Finset.prod_pos
    intro i _
    have hf : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hp : (0 : ℝ) < Real.pi ^ (i + 1) := pow_pos Real.pi_pos _
    exact div_pos (mul_pos two_pos hp) hf
  unfold cOmega
  exact div_pos one_pos (mul_pos (pow_pos two_pos _) hv)

theorem omegaDensity_haarProb (μ : Measure (Formalism.BasicNotions.UpqT N 0)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    Formalism.BasicNotions.OmegaDensity μ (ENNReal.ofReal (cOmega N)) :=
  PolarCoordinateComparison.omegaDensity_main μ

theorem omegaDensity_cd (cd : Formalism.BasicNotions.CDHaar) (N : ℕ) :
    Formalism.BasicNotions.OmegaDensity (cd.cd N 0) (ENNReal.ofReal (cOmega N)) := by
  haveI := cd.haar N 0
  haveI := cd.prob N
  exact omegaDensity_haarProb (cd.cd N 0)

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.MeasurableEmbeddingUpqMat
noncomputable section

open Finset Matrix MeasureTheory Topology Filter

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ} {P Q : ℕ}

def gMatL (ε : Fin n → Bool) : GCo ε →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := gMat
  map_add' s t := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp [star_add] <;> ring
  map_smul' c s := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul] <;> ring

theorem norm_le_sum_gMat {ε : Fin n → Bool} (s : GCo ε) : ‖s‖ ≤ ∑ a, ∑ b, ‖gMat s a b‖ := by
  have hS : ∀ a b, ‖gMat s a b‖ ≤ ∑ a, ∑ b, ‖gMat s a b‖ := fun a b =>
    (Finset.single_le_sum (f := fun b => ‖gMat s a b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, ‖gMat s a b‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))
  have h0 : 0 ≤ ∑ a, ∑ b, ‖gMat s a b‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun a => (le_of_eq ?_).trans (hS a a)
    simp [gMat, kMat, pmat]
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun ab => (le_of_eq ?_).trans (hS ab.1.1 ab.1.2)
    obtain ⟨⟨a, b⟩, h⟩ := ab
    have h1 : ¬ (b < a ∧ ε a ≠ ε b) := fun h' => h'.2 h.2
    have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h' => lt_asymm h'.1 h.1
    have h3 : a ≠ b := h.1.ne'
    simp [gMat, kMat, pmat, h3, h, h1, h2]
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun ab => (le_of_eq ?_).trans (hS ab.1.1 ab.1.2)
    obtain ⟨⟨a, b⟩, h⟩ := ab
    have h1 : ¬ (b < a ∧ ε a = ε b) := fun h' => h.2 h'.2
    have h2 : ¬ (a < b ∧ ε b = ε a) := fun h' => lt_asymm h'.1 h.1
    have h3 : a ≠ b := h.1.ne'
    simp [gMat, kMat, pmat, h3, h, h1, h2]

theorem gco_haar (ε : Fin n → Bool) :
    (volume : Measure (KCo ε)).IsAddHaarMeasure ∧ (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure ∧
      (volume : Measure (GCo ε)).IsAddHaarMeasure := by
  have h1 : (volume : Measure (Fin n → ℝ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => (volume : Measure ℝ)).IsAddHaarMeasure; infer_instance
  have h2 : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => (volume : Measure ℂ)).IsAddHaarMeasure; infer_instance
  have h3 : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure := by
    show (Measure.pi fun _ => (volume : Measure ℂ)).IsAddHaarMeasure; infer_instance
  have h4 : (volume : Measure (KCo ε)).IsAddHaarMeasure := by
    show ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (KPair ε → ℂ))).IsAddHaarMeasure
    infer_instance
  refine ⟨h4, h3, ?_⟩
  show ((volume : Measure (KCo ε)).prod (volume : Measure (PCoord ε → ℂ))).IsAddHaarMeasure
  exact MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _

theorem upqT_borel (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.UpqT P Q) := ⟨rfl⟩

theorem lieU_borel (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩

theorem Jpq_eq_diag (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.UG.Jpq P Q = Matrix.diagonal (fun i => if ε (e i) = true then (1 : ℂ) else -1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.diagonal_apply, he1, he2, Matrix.one_apply] <;>
    split_ifs <;> simp

theorem Jm_eq_reindex (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Jm ε = Matrix.reindex e e (Formalism.UG.Jpq P Q) := by
  rw [Jpq_eq_diag e he1 he2]
  ext a b
  simp [Jm, Matrix.diagonal_apply]

def yE (e : Fin P ⊕ Fin Q ≃ Fin n) (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) : ℂ :=
  (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (e.symm a) (e.symm b)

theorem lie_rel (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) :
    star (yE e X b a) * (if ε b = true then (1 : ℂ) else -1) +
      (if ε a = true then (1 : ℂ) else -1) * yE e X a b = 0 := by
  have h : (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 := X.2
  rw [Jpq_eq_diag e he1 he2] at h
  have h' := congrFun (congrFun h (e.symm a)) (e.symm b)
  simpa [yE, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h'

theorem lie_rel_c (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) (h : ε a = ε b) : yE e X a b = -star (yE e X b a) := by
  have R := lie_rel e he1 he2 X a b
  rw [← h] at R
  simp only [Complex.star_def] at R ⊢
  cases ha : ε a <;> simp [ha] at R <;> first | linear_combination R | linear_combination -R

theorem lie_rel_nc (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) (h : ε a ≠ ε b) : yE e X a b = star (yE e X b a) := by
  have R := lie_rel e he1 he2 X a b
  simp only [Complex.star_def] at R ⊢
  cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at R h ⊢ <;>
    first | linear_combination R | linear_combination -R

theorem lie_rel_d (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a : Fin n) : (yE e X a a).re = 0 := by
  have R := congrArg Complex.re (lie_rel e he1 he2 X a a)
  cases ha : ε a <;> simp [ha] at R <;> linarith

def sOfLie (e : Fin P ⊕ Fin Q ≃ Fin n) (ε : Fin n → Bool) (X : Formalism.BasicNotions.lieU P Q) : GCo ε :=
  (((fun a => (yE e X a a).im), fun ab => yE e X ab.1.1 ab.1.2), fun ab => yE e X ab.1.1 ab.1.2)

theorem gMat_sOfLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) (a b : Fin n) : gMat (sOfLie e ε X) a b = yE e X a b := by
  simp only [gMat, kMat, pmat, sOfLie, Matrix.add_apply]
  rcases lt_trichotomy a b with hab | rfl | hab
  · have n1 : a ≠ b := hab.ne
    have n2 : ¬ (b < a) := not_lt.2 hab.le
    by_cases hε : ε a = ε b
    · simp [n1, n2, hab, hε]
      exact (lie_rel_c e he1 he2 X a b hε).symm
    · have hε' : ε b ≠ ε a := Ne.symm hε
      simp [n1, n2, hab, hε, hε']
      exact (lie_rel_nc e he1 he2 X a b hε).symm
  · have hre := lie_rel_d e he1 he2 X a
    simp
    apply Complex.ext <;> simp [hre]
  · have n1 : a ≠ b := hab.ne'
    have n2 : ¬ (a < b) := not_lt.2 hab.le
    by_cases hε : ε a = ε b
    · simp [n1, n2, hab, hε]
    · simp [n1, n2, hab, hε]

theorem gToLie_surj (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (X : Formalism.BasicNotions.lieU P Q) : gToLie e he1 he2 (sOfLie e ε X) = X := by
  apply Subtype.ext
  ext i j
  show Matrix.reindex e.symm e.symm (gMat (sOfLie e ε X)) i j = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [gMat_sOfLie e he1 he2 X]
  simp [yE]

theorem exp_reindex (e : Fin P ⊕ Fin Q ≃ Fin n) (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    Matrix.reindex e e (NormedSpace.exp X) = NormedSpace.exp (Matrix.reindex e e X) := by
  have hc : Continuous (fun M : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ => Matrix.reindex e e M) :=
    continuous_id.matrix_submatrix _ _
  have hc' : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm M) :=
    continuous_id.matrix_submatrix _ _
  simp only [NormedSpace.exp_eq_tsum_rat]
  show (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom (∑' k : ℕ, ((k.factorial : ℚ)⁻¹ : ℚ) • X ^ k) = _
  rw [Function.LeftInverse.map_tsum (g := (Matrix.reindexAlgEquiv ℂ ℂ e).toRingHom) _ (by exact hc) (by exact hc')
    (fun M => by ext i j; simp)]
  simp only [map_rat_smul, map_pow]
  rfl

theorem cT_eq (A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : Formalism.UG.cT (starRingEnd ℂ) A = Aᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

theorem Jpq_mul_self : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem reindex_form (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (A : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    (Matrix.reindex e e A)ᴴ * Jm ε * Matrix.reindex e e A = Matrix.reindex e e (Aᴴ * Formalism.UG.Jpq P Q * A) := by
  rw [Jm_eq_reindex e he1 he2]
  simp [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

def upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) (g : Formalism.BasicNotions.UpqT P Q) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)

theorem mem_Upq_iff (g : GL (Fin P ⊕ Fin Q) ℂ) :
    g ∈ Formalism.UG.Upq P Q ↔
      (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q * g = Formalism.UG.Jpq P Q := by
  rw [← cT_eq]; exact Iff.rfl

theorem mat_mem (g : Formalism.BasicNotions.UpqT P Q) :
    (Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * Formalism.BasicNotions.UpqT.mat g = Formalism.UG.Jpq P Q :=
  (mem_Upq_iff _).1 (show Formalism.UG.Upq P Q from g).2

theorem mat_inv (g : Formalism.BasicNotions.UpqT P Q) :
    ((((show Formalism.UG.Upq P Q from g) : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) :
      Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      Formalism.UG.Jpq P Q * (Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q := by
  apply Units.inv_eq_of_mul_eq_one_left
  have h := mat_mem g
  calc Formalism.UG.Jpq P Q * (Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * Formalism.BasicNotions.UpqT.mat g
      = Formalism.UG.Jpq P Q * ((Formalism.BasicNotions.UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * Formalism.BasicNotions.UpqT.mat g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Jpq_mul_self]

theorem upqMat_inUJ (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false)
    (g : Formalism.BasicNotions.UpqT P Q) : inUJ ε (upqMat e g) := by
  unfold inUJ upqMat
  rw [reindex_form e he1 he2, mat_mem, ← Jm_eq_reindex e he1 he2]

theorem range_upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Set.range (upqMat e) = {M | inUJ ε M} := by
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    exact upqMat_inUJ e he1 he2 g
  · intro hM
    set A := Matrix.reindex e.symm e.symm M with hA
    have hAM : Matrix.reindex e e A = M := by rw [hA]; ext a b; simp
    have hform : Aᴴ * Formalism.UG.Jpq P Q * A = Formalism.UG.Jpq P Q := by
      apply (Matrix.reindex e e).injective
      rw [← reindex_form e he1 he2, hAM, ← Jm_eq_reindex e he1 he2]
      exact hM
    have h2 : (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) * A = 1 := by
      calc (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) * A = Formalism.UG.Jpq P Q * (Aᴴ * Formalism.UG.Jpq P Q * A) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hform, Jpq_mul_self]
    have h1 : A * (Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q) = 1 := mul_eq_one_comm.mp h2
    let u : GL (Fin P ⊕ Fin Q) ℂ := ⟨A, Formalism.UG.Jpq P Q * Aᴴ * Formalism.UG.Jpq P Q, h1, h2⟩
    have hu : u ∈ Formalism.UG.Upq P Q := (mem_Upq_iff u).2 hform
    refine ⟨(⟨u, hu⟩ : Formalism.UG.Upq P Q), ?_⟩
    exact hAM

theorem upqMat_cont (e : Fin P ⊕ Fin Q ≃ Fin n) : Continuous (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
  have h : Continuous fun g : Formalism.BasicNotions.UpqT P Q => Formalism.BasicNotions.UpqT.mat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact h.matrix_submatrix _ _

theorem isClosedEmbedding_upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    IsClosedEmbedding (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
  let f : Matrix (Fin n) (Fin n) ℂ →
      Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ × (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᵐᵒᵖ :=
    fun M => (Matrix.reindex e.symm e.symm M,
      MulOpposite.op (Formalism.UG.Jpq P Q * (Matrix.reindex e.symm e.symm M)ᴴ * Formalism.UG.Jpq P Q))
  have hr : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm M :=
    continuous_id.matrix_submatrix _ _
  have hf : Continuous f :=
    hr.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul hr.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : f ∘ (upqMat e : Formalism.BasicNotions.UpqT P Q → _) =
      Units.embedProduct _ ∘ (fun g : Formalism.BasicNotions.UpqT P Q => ((show Formalism.UG.Upq P Q from g) : GL (Fin P ⊕ Fin Q) ℂ)) := by
    funext g
    simp only [Function.comp_apply, f, Units.embedProduct_apply, upqMat]
    rw [mat_inv]
    simp
    rfl
  have hI : IsInducing (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
    refine IsInducing.of_comp (upqMat_cont e) hf ?_
    rw [hcomp]
    exact Units.isEmbedding_embedProduct.isInducing.comp IsInducing.subtypeVal
  have hE : IsEmbedding (upqMat e : Formalism.BasicNotions.UpqT P Q → _) := by
    refine ⟨hI, fun a b h => ?_⟩
    have h' : Formalism.BasicNotions.UpqT.mat a = Formalism.BasicNotions.UpqT.mat b := (Matrix.reindex e e).injective h
    exact Subtype.ext (Units.ext h')
  refine ⟨hE, ?_⟩
  rw [range_upqMat e he1 he2]
  exact isClosed_inUJ ε

theorem measurableEmbedding_upqMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    @MeasurableEmbedding (Formalism.BasicNotions.UpqT P Q) (Fin n → Fin n → ℂ) _ _ (fun g => upqMat e g) := by
  haveI := upqT_borel P Q
  exact Topology.IsClosedEmbedding.measurableEmbedding (β := Fin n → Fin n → ℂ)
    (isClosedEmbedding_upqMat e he1 he2)

theorem measurableEmbedding_toM (ε : Fin n → Bool) :
    @MeasurableEmbedding (UJ ε) (Fin n → Fin n → ℂ) _ _ (fun g : UJ ε => toM g) :=
  Topology.IsClosedEmbedding.measurableEmbedding (β := Fin n → Fin n → ℂ) (isClosedEmbedding_toM ε)

theorem gToLie_val (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    Matrix.reindex e e ((gToLie e he1 he2 s : Formalism.BasicNotions.lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      gMat s := by
  show Matrix.reindex e e (Matrix.reindex e.symm e.symm (gMat s)) = gMat s
  ext a b; simp

theorem image_expBall (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (r : ℝ) :
    upqMat e '' {g : Formalism.BasicNotions.UpqT P Q | ∃ X ∈ Formalism.BasicNotions.ballU P Q r, Formalism.BasicNotions.UpqT.mat g =
        NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} =
      (fun g : UJ ε => toM g) '' expSet {s : GCo ε | gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r} := by
  ext M
  constructor
  · rintro ⟨g, ⟨X, hX, hgX⟩, rfl⟩
    have hin : upqMat e g ∈ Set.range (fun u : UJ ε => toM u) := by
      rw [range_toM]; exact upqMat_inUJ e he1 he2 g
    obtain ⟨u, hu⟩ := hin
    refine ⟨u, ⟨sOfLie e ε X, ?_, ?_⟩, hu⟩
    · show gToLie e he1 he2 (sOfLie e ε X) ∈ Formalism.BasicNotions.ballU P Q r
      rw [gToLie_surj]; exact hX
    · have hu' : toM u = upqMat e g := hu
      rw [hu', upqMat, hgX, exp_reindex, ← gToLie_val e he1 he2, gToLie_surj]
  · rintro ⟨u, ⟨s, hs, hus⟩, rfl⟩
    have hin : toM u ∈ Set.range (upqMat e) := by
      rw [range_upqMat e he1 he2]; exact u.2
    obtain ⟨g, hg⟩ := hin
    refine ⟨g, ⟨gToLie e he1 he2 s, hs, ?_⟩, hg⟩
    apply (Matrix.reindex e e).injective
    rw [exp_reindex, gToLie_val e he1 he2]
    show upqMat e g = _
    rw [hg, hus]

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

open Topology Filter

variable {n : ℕ}

def muCDtr {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) (ε : Fin n → Bool) : Measure (Formalism.BasicNotions.UpqT P Q) :=
  Measure.comap (β := Fin n → Fin n → ℂ)
    (fun g : Formalism.BasicNotions.UpqT P Q => Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g))
    (ENNReal.ofReal (cPQ ε) • muPolarMat ε)

theorem tie_volU_pos (N : ℕ) : 0 < volU N :=
  Finset.prod_pos fun i _ => by positivity

theorem tie_tendsto {f : ℝ → ENNReal} {x : ℝ} (hx : 0 < x)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal ((1 - η) * x) ≤ f r ∧ f r ≤ ENNReal.ofReal ((1 + η) * x)) :
    Tendsto f (𝓝[>] 0) (𝓝 (ENNReal.ofReal x)) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hat : a ≠ ⊤ := ne_top_of_lt ha
    have ht : a.toReal < x := by
      have := (ENNReal.toReal_lt_toReal hat ENNReal.ofReal_ne_top).2 ha
      rwa [ENNReal.toReal_ofReal hx.le] at this
    have ht0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
    have hη : 0 < (x - a.toReal) / (2 * x) := div_pos (by linarith) (by linarith)
    filter_upwards [h _ hη] with r hr
    have e1 : (1 - (x - a.toReal) / (2 * x)) * x = (x + a.toReal) / 2 := by field_simp; ring
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal hat).symm
      _ < ENNReal.ofReal ((1 - (x - a.toReal) / (2 * x)) * x) := by
          rw [e1]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      _ ≤ f r := hr.1
  · by_cases hat : a = ⊤
    · filter_upwards [h 1 one_pos] with r hr
      exact lt_of_le_of_lt hr.2 (hat ▸ ENNReal.ofReal_lt_top)
    · have ht : x < a.toReal := by
        have := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hat).2 ha
        rwa [ENNReal.toReal_ofReal hx.le] at this
      have hη : 0 < (a.toReal - x) / (2 * x) := div_pos (by linarith) (by linarith)
      filter_upwards [h _ hη] with r hr
      have e1 : (1 + (a.toReal - x) / (2 * x)) * x = (x + a.toReal) / 2 := by field_simp; ring
      calc f r ≤ _ := hr.2
        _ < ENNReal.ofReal a.toReal := by
          rw [e1]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
        _ = a := ENNReal.ofReal_toReal hat

theorem tie_cancel {p q : ℝ} {v : ENNReal} (hv0 : v ≠ 0) (hvt : v ≠ ⊤) (hq : 0 ≤ q)
    (h : ENNReal.ofReal p * v ≤ ENNReal.ofReal q * v) : p ≤ q := by
  have := (ENNReal.mul_le_mul_iff_left hv0 hvt).1 h
  have h2 := (ENNReal.ofReal_le_ofReal_iff hq).1 this
  exact h2

theorem tie_d_eq (ε : Fin n → Bool) (d : ℝ) (hd0 : 0 < d)
    (hd : DensOn (fun S => muPolar ε (expSet S)) d) : d = 1 / (volU (pOf ε) * volU (qOf ε)) := by
  haveI := muPolar_isHaar ε
  obtain ⟨hK, hP, hG⟩ := gco_haar ε
  have hpol := haar_pol_density (muPolar ε) d hd
  set x := volU (pOf ε) * volU (qOf ε) with hx
  have hx0 : 0 < x := mul_pos (tie_volU_pos _) (tie_volU_pos _)
  set D := 1 / x with hD
  have hD0 : 0 < D := by positivity
  have key : ∀ η : ℝ, 0 < η → η < 1 → (1 - η) * d ≤ (1 + η) * D ∧ (1 - η) * D ≤ (1 + η) * d := by
    intro η hη hη1
    obtain ⟨δ1, hδ1, h1⟩ := hpol η hη
    obtain ⟨δ2, hδ2, h2⟩ := muPolar_near_one ε η hη
    set δ := min δ1 δ2
    have hδ : 0 < δ := lt_min hδ1 hδ2
    set B := Metric.ball (0 : KCo ε) (δ / 2)
    set C := Metric.ball (0 : PCoord ε → ℂ) (δ / 2)
    have hB0 : volume B ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
    have hC0 : volume C ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
    have hBt : volume B ≠ ⊤ := measure_ball_lt_top.ne
    have hCt : volume C ≠ ⊤ := measure_ball_lt_top.ne
    have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
    have hCm : MeasurableSet C := Metric.isOpen_ball.measurableSet
    have hSm : MeasurableSet (B ×ˢ C) := hBm.prod hCm
    have hvS : volume (B ×ˢ C) = volume B * volume C := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
    have hv0 : volume B * volume C ≠ 0 := mul_ne_zero hB0 hC0
    have hvt : volume B * volume C ≠ ⊤ := ENNReal.mul_ne_top hBt hCt
    have hsm : ∀ s ∈ B ×ˢ C, ‖s‖ < δ1 := by
      intro s hs
      have h1' : ‖s.1‖ < δ / 2 := by simpa [B] using hs.1
      have h2' : ‖s.2‖ < δ / 2 := by simpa [C] using hs.2
      have : ‖s‖ ≤ δ / 2 := norm_prod_le_iff.2 ⟨h1'.le, h2'.le⟩
      linarith [min_le_left δ1 δ2]
    have hB : ∀ w ∈ B, ‖w‖ < δ2 := by
      intro w hw
      have : ‖w‖ < δ / 2 := by simpa [B] using hw
      linarith [min_le_right δ1 δ2]
    have hC : ∀ z ∈ C, ‖z‖ < δ2 := by
      intro z hz
      have : ‖z‖ < δ / 2 := by simpa [C] using hz
      linarith [min_le_right δ1 δ2]
    obtain ⟨u1, l1⟩ := h1 (B ×ˢ C) hSm hsm
    obtain ⟨u2, l2⟩ := h2 B C hBm hCm hB hC
    rw [hvS] at u1 l1
    have e1 : (1 + η) / x = (1 + η) * D := by rw [hD]; ring
    have e2 : (1 - η) / x = (1 - η) * D := by rw [hD]; ring
    rw [e1] at u2
    rw [e2] at l2
    constructor
    · exact tie_cancel hv0 hvt (by positivity) (l1.trans u2)
    · exact tie_cancel hv0 hvt (by positivity) (l2.trans u1)
  rcases lt_trichotomy d D with hlt | heq | hgt
  · exfalso
    set η := (D - d) / (2 * (D + d))
    have hη : 0 < η := div_pos (by linarith) (by linarith)
    have hη1 : η < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    have e : η * (2 * (D + d)) = D - d := div_mul_cancel₀ _ (by linarith)
    have := (key η hη hη1).2
    nlinarith
  · exact heq
  · exfalso
    set η := (d - D) / (2 * (D + d))
    have hη : 0 < η := div_pos (by linarith) (by linarith)
    have hη1 : η < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    have e : η * (2 * (D + d)) = d - D := div_mul_cancel₀ _ (by linarith)
    have := (key η hη hη1).1
    nlinarith

section

variable {P Q : ℕ}

theorem tie_sum_reindex (e : Fin P ⊕ Fin Q ≃ Fin n) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖Matrix.reindex e.symm e.symm M i j‖ = ∑ a, ∑ b, ‖M a b‖ := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [← Equiv.sum_comp e (fun a => ∑ b, ‖M a b‖)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp e (fun b => ‖M (e i) b‖)

theorem tie_mem_ball (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (r : ℝ) (s : GCo ε) :
    gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r ↔ ∑ a, ∑ b, ‖gMat s a b‖ < r := by
  show ∑ i, ∑ j, ‖Matrix.reindex e.symm e.symm (gMat s) i j‖ < r ↔ _
  rw [tie_sum_reindex]

theorem tie_gToLie_cont (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Continuous (gToLie e he1 he2 : GCo ε → Formalism.BasicNotions.lieU P Q) := by
  have h1 : Continuous fun s : GCo ε => gToLieMat e s :=
    (LinearMap.continuous_of_finiteDimensional (gMatL ε)).matrix_submatrix _ _
  exact h1.subtype_mk _

theorem tie_ball_open (P Q : ℕ) (r : ℝ) : IsOpen (Formalism.BasicNotions.ballU P Q r) :=
  isOpen_lt (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_norm.comp (continuous_subtype_val.matrix_elem i j)) continuous_const

end

theorem omegaDensity_muCDtr {P Q : ℕ} (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.OmegaDensity (muCDtr e ε) (ENNReal.ofReal (cOmega n)) := by
  haveI := muPolar_isHaar ε
  haveI := lieU_borel P Q
  obtain ⟨hK, hP, hG⟩ := gco_haar ε
  obtain ⟨d, hd0, hd⟩ := haar_exp_density (muPolar ε)
  have hdD := tie_d_eq ε d hd0 hd
  refine ⟨_, isOmegaLeb_gToLie e he1 he2, ?_⟩
  set κ : ℝ := 2 ^ (n * (n - 1) / 2) with hκ
  have hκ0 : 0 < κ := by positivity
  have hσc : Continuous fun s : GCo ε => ∑ a, ∑ b, ‖gMat s a b‖ :=
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_norm.comp ((LinearMap.continuous_of_finiteDimensional (gMatL ε)).matrix_elem a b)
  have hnum : ∀ r, muCDtr e ε {g | ∃ X ∈ Formalism.BasicNotions.ballU P Q r, Formalism.BasicNotions.UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} =
      ENNReal.ofReal (cPQ ε) * muPolar ε (expSet {s : GCo ε | gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r}) := by
    intro r
    have hE := measurableEmbedding_upqMat e he1 he2
    show Measure.comap (β := Fin n → Fin n → ℂ) (fun g => upqMat e g) (ENNReal.ofReal (cPQ ε) • muPolarMat ε) _ =
      _ * Measure.comap (β := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) (muPolarMat ε) _
    rw [hE.comap_apply, (measurableEmbedding_toM ε).comap_apply, Measure.smul_apply, smul_eq_mul]
    congr 2
    exact image_expBall e he1 he2 r
  have hden : ∀ r, (ENNReal.ofReal κ • Measure.map (gToLie e he1 he2) volume) (Formalism.BasicNotions.ballU P Q r) =
      ENNReal.ofReal κ * volume {s : GCo ε | gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r} := by
    intro r
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (tie_gToLie_cont e he1 he2).measurable (tie_ball_open P Q r).measurableSet]
    rfl
  have hvn := tie_volU_pos n
  have hvp := tie_volU_pos (pOf ε)
  have hvq := tie_volU_pos (qOf ε)
  have hc : cOmega n * κ = cPQ ε * d := by
    rw [hdD, cPQ_eq_volU, cOmega, ← hκ]
    field_simp
  have hc0 : 0 < cOmega n := cOmega_pos n
  have hcP : 0 ≤ cPQ ε := (cPQ_pos ε).le
  refine tie_tendsto hc0 (fun η hη => ?_)
  obtain ⟨δ, hδ, hdδ⟩ := hd η hη
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [hnum r, hden r]
  set S := {s : GCo ε | gToLie e he1 he2 s ∈ Formalism.BasicNotions.ballU P Q r} with hS
  have hSe : S = {s | ∑ a, ∑ b, ‖gMat s a b‖ < r} := Set.ext fun s => tie_mem_ball e he1 he2 r s
  have hSo : IsOpen S := by rw [hSe]; exact isOpen_lt hσc continuous_const
  have h0S : (0 : GCo ε) ∈ S := by
    rw [hSe, Set.mem_ofPred_eq, show gMat (0 : GCo ε) = 0 from (gMatL ε).map_zero]
    simpa using hr.1
  have hSb : ∀ s ∈ S, ‖s‖ < δ := fun s hs => by
    rw [hSe] at hs
    exact lt_of_le_of_lt (norm_le_sum_gMat s) (lt_trans hs hr.2)
  have hSball : S ⊆ Metric.ball 0 r := fun s hs => by
    rw [hSe] at hs
    rw [mem_ball_zero_iff]; exact lt_of_le_of_lt (norm_le_sum_gMat s) hs
  have hV0 : volume S ≠ 0 := (hSo.measure_pos volume ⟨0, h0S⟩).ne'
  have hVt : volume S ≠ ⊤ := ((measure_mono hSball).trans_lt measure_ball_lt_top).ne
  obtain ⟨hu, hl⟩ := hdδ S hSo.measurableSet hSb
  have hden0 : ENNReal.ofReal κ * volume S ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 hκ0).ne' hV0
  have hdent : ENNReal.ofReal κ * volume S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVt
  have eq1 : (1 - η) * cOmega n * κ = cPQ ε * ((1 - η) * d) := by linear_combination (1 - η) * hc
  have eq2 : (1 + η) * cOmega n * κ = cPQ ε * ((1 + η) * d) := by linear_combination (1 + η) * hc
  constructor
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)]
    calc ENNReal.ofReal ((1 - η) * cOmega n) * (ENNReal.ofReal κ * volume S)
        = ENNReal.ofReal (cPQ ε) * (ENNReal.ofReal ((1 - η) * d) * volume S) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul' hκ0.le, eq1, ENNReal.ofReal_mul hcP, mul_assoc]
      _ ≤ _ := by gcongr
  · apply ENNReal.div_le_of_le_mul
    calc ENNReal.ofReal (cPQ ε) * muPolar ε (expSet S)
        ≤ ENNReal.ofReal (cPQ ε) * (ENNReal.ofReal ((1 + η) * d) * volume S) := by gcongr
      _ = ENNReal.ofReal ((1 + η) * cOmega n) * (ENNReal.ofReal κ * volume S) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hcP, ← eq2, ENNReal.ofReal_mul' hκ0.le, mul_assoc]

end ReciprocityTheory.ChartRestriction.DS
