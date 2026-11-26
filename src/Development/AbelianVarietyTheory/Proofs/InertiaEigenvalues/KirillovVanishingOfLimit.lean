module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHeightSqLintegralLtTop
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentDecompositionOfIntegrality
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentDecompositionOfIntegrality
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

open Polynomial

namespace GlobalTheory.JR.Et.Idem

theorem isIntegral_of_forall {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

theorem isIntegral_single {O : Type} [CommRing O] {ι : Type} [Finite ι] [DecidableEq ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (i : ι) (z : R i) (hz : IsIntegral O z) :
    IsIntegral O (Pi.single i z : ∀ j, R j) := by
  refine isIntegral_of_forall _ fun j => ?_
  by_cases h : j = i
  · subst h; simpa using hz
  · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero

theorem single_mul_single_of_ne {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ i, MulZeroClass (R i)] {i j : ι}
    (h : i ≠ j) (a : R i) (b : R j) : (Pi.single i a : ∀ k, R k) * Pi.single j b = 0 := by
  funext k
  rw [Pi.mul_apply, Pi.zero_apply]
  by_cases hk : k = i
  · subst hk; rw [Pi.single_eq_of_ne h, mul_zero]
  · rw [Pi.single_eq_of_ne hk, zero_mul]

theorem single_one_mul {ι : Type} [DecidableEq ι] {R : ι → Type} [∀ i, MulZeroOneClass (R i)] (i : ι)
    (x : ∀ j, R j) : (Pi.single i 1 : ∀ j, R j) * x = Pi.single i (x i) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [Pi.single_eq_of_ne hk]

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] [IsUltrametricDist F] (A : Et F E),
    (∀ (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 →
      IsIntegral (NormedField.valuation (K := F)).integer y ∨
        IsIntegral (NormedField.valuation (K := F)).integer y⁻¹) →
    ∃ (m : ℕ) (f : Fin m → A.K), (∀ i, f i * f i = f i) ∧ (∀ i j, i ≠ j → f i * f j = 0) ∧ ∑ i, f i = 1 ∧
      (∀ i (c : F), 1 < ‖c‖ → algebraMap F A.K c * f i ∉ A.OK) ∧
      ∀ i (y : A.K), f i * y ∉ A.OK → ∃ w ∈ A.OK, w * (f i * y) = f i := by
  intro F E _ _ _ _ _ _ A hval
  classical
  haveI : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  let ψ : A.K ≃ₐ[F] (∀ I : MaximalSpectrum A.K, A.K ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A.K).restrictScalars F
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin (MaximalSpectrum A.K)
  let f : Fin m → A.K := fun i => ψ.symm (Pi.single (e.symm i) 1)
  have hf : ∀ i, ψ (f i) = Pi.single (e.symm i) 1 := fun i => ψ.apply_symm_apply _
  haveI : Fintype (MaximalSpectrum A.K) := Fintype.ofFinite _
  have hOK : ∀ x : (∀ I : MaximalSpectrum A.K, A.K ⧸ I.asIdeal),
      IsIntegral (NormedField.valuation (K := F)).integer x → ψ.symm x ∈ A.OK := fun x hx =>
    (mem_OK_iff_isIntegral A _).2 (hx.map (ψ.symm.restrictScalars (NormedField.valuation (K := F)).integer))
  refine ⟨m, f, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply ψ.injective
    rw [map_mul, hf, ← Pi.single_mul, mul_one]
  · intro i j hij
    apply ψ.injective
    rw [map_mul, hf, hf, map_zero]
    exact single_mul_single_of_ne (e.symm.injective.ne hij) _ _
  · apply ψ.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp_rw [hf]
    rw [Equiv.sum_comp e.symm (fun I => (Pi.single I 1 : ∀ J : MaximalSpectrum A.K, A.K ⧸ J.asIdeal))]
    exact Finset.univ_sum_single 1
  · intro i c hc h
    rw [mem_OK_iff_isIntegral] at h
    haveI := (e.symm i).isMaximal
    letI : Field (A.K ⧸ (e.symm i).asIdeal) := Ideal.Quotient.field _
    have h1 := h.map (((Pi.evalAlgHom F (fun J : MaximalSpectrum A.K => A.K ⧸ J.asIdeal) (e.symm i)).comp
      ψ.toAlgHom).restrictScalars (NormedField.valuation (K := F)).integer)
    have h2 : (((Pi.evalAlgHom F (fun J : MaximalSpectrum A.K => A.K ⧸ J.asIdeal) (e.symm i)).comp
      ψ.toAlgHom).restrictScalars (NormedField.valuation (K := F)).integer) (algebraMap F A.K c * f i) =
        algebraMap F (A.K ⧸ (e.symm i).asIdeal) c := by
      change ψ (algebraMap F A.K c * f i) (e.symm i) = _
      rw [map_mul, AlgEquiv.commutes, hf, Pi.mul_apply, Pi.single_eq_same, mul_one, Pi.algebraMap_apply]
    rw [h2] at h1
    have h3 := (isIntegral_algebraMap_iff ).1 h1
    have h4 := (Valuation.integer.integers (NormedField.valuation (K := F))).mem_of_integral h3
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h4
    have h5 : ‖c‖ ≤ 1 := by exact_mod_cast h4
    linarith
  · intro i y hy
    haveI := (e.symm i).isMaximal
    letI : Field (A.K ⧸ (e.symm i).asIdeal) := Ideal.Quotient.field _
    haveI : FiniteDimensional F (A.K ⧸ (e.symm i).asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ F (e.symm i).asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have hfy : ψ (f i * y) = Pi.single (e.symm i) (ψ y (e.symm i)) := by
      rw [map_mul, hf, single_one_mul]
    have hfy' : f i * y = ψ.symm (Pi.single (e.symm i) (ψ y (e.symm i))) := by
      rw [← hfy, ψ.symm_apply_apply]
    by_cases hz : ψ y (e.symm i) = 0
    · exact absurd (by rw [hfy', hz, Pi.single_zero, map_zero]; exact (mem_OK_iff_isIntegral A 0).2 isIntegral_zero) hy
    rcases hval (A.K ⧸ (e.symm i).asIdeal) (ψ y (e.symm i)) hz with h | h
    · exact absurd (by rw [hfy']; exact hOK _ (isIntegral_single _ _ h)) hy
    · refine ⟨ψ.symm (Pi.single (e.symm i) (ψ y (e.symm i))⁻¹), hOK _ (isIntegral_single _ _ h), ?_⟩
      apply ψ.injective
      rw [map_mul, ψ.apply_symm_apply, hfy, hf, ← Pi.single_mul, inv_mul_cancel₀ hz]

end GlobalTheory.JR.Et.Idem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentDecompositionOfIntegralityStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_decomposition_of_integrality : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] [IsUltrametricDist F] (A : Et F E), (∀ (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹) → ∃ (m : ℕ) (f : Fin m → A.K), (∀ i, f i * f i = f i) ∧ (∀ i j, i ≠ j → f i * f j = 0) ∧ ∑ i, f i = 1 ∧ (∀ i (c : F), 1 < ‖c‖ → algebraMap F A.K c * f i ∉ A.OK) ∧ ∀ i (y : A.K), f i * y ∉ A.OK → ∃ w ∈ A.OK, w * (f i * y) = f i := by
  first | exact @GlobalTheory.JR.Et.Idem.main | exact GlobalTheory.JR.Et.Idem.main | (intros; apply GlobalTheory.JR.Et.Idem.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrInvIsIntegralFiniteExtUltrametric
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrInvIsIntegralFiniteExtUltrametric
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Polynomial

noncomputable section

namespace GlobalTheory.JR.Spec

variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
  {k : Type} [Field k] [Algebra F k]

theorem isIntegral_integer_of_spectralNorm_le_one [FiniteDimensional F k] {y : k}
    (h : spectralNorm F k y ≤ 1) : IsIntegral (NormedField.valuation (K := F)).integer y := by
  have hyF : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyF)] at h
  have hl : minpoly F y ∈ lifts (algebraMap (NormedField.valuation (K := F)).integer F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast h n
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyF)
  refine ⟨q, hqm, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap F, hq, minpoly.aeval]

theorem isIntegral_or_isIntegral_inv : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 →
    IsIntegral (NormedField.valuation (K := F)).integer y ∨
      IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by
  intro F _ _ _ k _ _ _ y hy0
  have hmul : spectralNorm F k y * spectralNorm F k y⁻¹ = 1 := by
    have := spectralAlgNorm_mul (K := F) (L := k) y y⁻¹
    rw [spectralAlgNorm_def, spectralAlgNorm_def, spectralAlgNorm_def, mul_inv_cancel₀ hy0,
      spectralNorm_one] at this
    exact this.symm
  by_cases h : spectralNorm F k y ≤ 1
  · exact Or.inl (isIntegral_integer_of_spectralNorm_le_one h)
  · right
    apply isIntegral_integer_of_spectralNorm_le_one
    have h1 : 1 < spectralNorm F k y := lt_of_not_ge h
    by_contra h2
    have h2 : 1 < spectralNorm F k y⁻¹ := lt_of_not_ge h2
    have : 1 < spectralNorm F k y * spectralNorm F k y⁻¹ := one_lt_mul_of_lt_of_le h1 h2.le
    linarith

end GlobalTheory.JR.Spec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by
  first | exact @GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv | exact GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv | (intros; apply GlobalTheory.JR.Spec.isIntegral_or_isIntegral_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHeightSqLintegralLtTop
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace GlobalTheory.JR.HeightSquareIntegrable

theorem tsum_pi_prod_le' {ι : Type} [Fintype ι] {α : ι → Type} (f : ∀ i, α i → ℝ≥0∞) :
    ∑' t : ∀ i, α i, ∏ i, f i (t i) ≤ ∏ i, ∑' x, f i x := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ t ∈ s, ∏ i, f i (t i)
      ≤ ∑ t ∈ Fintype.piFinset (fun i => s.image (fun t => t i)), ∏ i, f i (t i) := by
        refine Finset.sum_le_sum_of_subset fun t ht => ?_
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
    _ = ∏ i, ∑ x ∈ s.image (fun t => t i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod' fun i _ => ENNReal.sum_le_tsum _

section Idem
variable {K : Type} [CommRing K] {m : ℕ} {f : Fin m → K}

theorem eq_of_mul_eq (hsum : ∑ i, f i = 1) {x y : K} (h : ∀ j, f j * x = f j * y) : x = y := by
  have hx : x = ∑ j, f j * x := by rw [← Finset.sum_mul, hsum, one_mul]
  have hy : y = ∑ j, f j * y := by rw [← Finset.sum_mul, hsum, one_mul]
  rw [hx, hy]; exact Finset.sum_congr rfl fun j _ => h j

theorem mul_sum_eq (hid : ∀ i, f i * f i = f i) (hor : ∀ i j, i ≠ j → f i * f j = 0)
    (a : Fin m → K) (j : Fin m) : f j * ∑ i, f i * a i = f j * a j := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [← mul_assoc, hid]
  · intro i _ hij; rw [← mul_assoc, hor j i (Ne.symm hij), zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem mul_eq_iff_mk (hid : ∀ i, f i * f i = f i) (j : Fin m) (x y : K) :
    f j * x = f j * y ↔
      Ideal.Quotient.mk (Ideal.span {1 - f j}) x = Ideal.Quotient.mk (Ideal.span {1 - f j}) y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  constructor
  · intro h; exact ⟨x - y, by linear_combination (-1 : K) * h⟩
  · rintro ⟨a, ha⟩; linear_combination (-f j) * ha - a * hid j

theorem mul_prod_eq (hid : ∀ i, f i * f i = f i) (hor : ∀ i j, i ≠ j → f i * f j = 0)
    (g : Fin m → K) (k : Fin m → ℕ) (j : Fin m) :
    f j * ∏ i, (f i * g i + (1 - f i)) ^ k i = f j * g j ^ k j := by
  rw [mul_eq_iff_mk hid]; simp only [map_prod, map_pow]
  rw [Finset.prod_eq_single j]
  · congr 1
    rw [← mul_eq_iff_mk hid]; linear_combination (g j - 1) * hid j
  · intro i _ hij
    have h1 : Ideal.Quotient.mk (Ideal.span {1 - f j}) (f i * g i + (1 - f i)) = 1 := by
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - f j})), ← mul_eq_iff_mk hid]
      linear_combination (g i - 1) * hor j i (Ne.symm hij)
    rw [h1, one_pow]
  · intro h; exact absurd (Finset.mem_univ j) h

end Idem

theorem height_sq_lintegral_lt_top : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.K), μ.IsAddHaarMeasure → ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ < ⊤ := by
  intro F E _ _ _ _ hU A μ hμ
  classical
  haveI := hU.ultraF; haveI := hU.lcF; haveI := hU.charZero
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : IsTopologicalAddGroup A.K := IsModuleTopology.topologicalAddGroup F A.K
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  let b := Module.finBasis F A.K
  haveI : T2Space A.K := .of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  haveI : SecondCountableTopology A.K := b.equivFunL.toHomeomorph.secondCountableTopology
  obtain ⟨-, -, -, -, -, -, -, -, -, hOo, hOc, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨m, f, hid, hor, hsum, hsc, hvp⟩ :=
    GlobalTheory.T.idempotent_decomposition_of_integrality F E A (fun k _ _ _ y hy => GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric F k y hy)
  have hOR : ∀ x, x ∈ A.OK ↔ x ∈ R := fun x => by rw [← hR, SetLike.mem_coe]
  have hfR : ∀ i, f i ∈ R := fun i => by
    rw [← hOR, Et.mem_OK_iff_isIntegral]
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩
    simp [sq, hid i]
  obtain ⟨π, hπ0, hπ1⟩ := NormedField.exists_norm_lt_one F
  have hπ : π ≠ 0 := norm_pos_iff.1 hπ0
  have hpp : algebraMap F A.K π * algebraMap F A.K π⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hπ, map_one]
  have hpR : algebraMap F A.K π ∈ R := by
    rw [← hOR, Et.mem_OK_iff_isIntegral]
    have hmem : π ∈ (NormedField.valuation (K := F)).integer := by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply]; exact_mod_cast hπ1.le
    exact (isIntegral_algebraMap (R := (NormedField.valuation (K := F)).integer) (A := A.K) (x := ⟨π, hmem⟩) : _)
  set p := algebraMap F A.K π with hp
  set p' := algebraMap F A.K π⁻¹ with hp'
  let u : Fin m → A.Kˣ := fun i => ⟨f i * p + (1 - f i), f i * p' + (1 - f i),
    by linear_combination (f i * f i) * hpp + (2 - p - p') * hid i,
    by linear_combination (f i * f i) * hpp + (2 - p - p') * hid i⟩
  have hu : ∀ i, ((u i : A.Kˣ) : A.K) = f i * p + (1 - f i) := fun i => rfl
  have huR : ∀ i, ((u i : A.Kˣ) : A.K) ∈ R := fun i => by
    rw [hu]; exact R.add_mem (R.mul_mem (hfR i) hpR) (R.sub_mem R.one_mem (hfR i))
  haveI : μ.IsAddHaarMeasure := hμ
  have hμO0 : μ A.OK ≠ 0 := hOo.measure_ne_zero μ ⟨0, (hOR 0).2 R.zero_mem⟩
  have hμOt : μ A.OK ≠ ⊤ := hOc.measure_lt_top.ne
  have hsmulO : ∀ v : A.Kˣ, (v : A.K) ∈ R → v • A.OK ⊆ A.OK := by
    rintro v hv _ ⟨y, hy, rfl⟩
    rw [hOR] at hy ⊢
    exact R.mul_mem hv hy
  have hle1 : ∀ v : A.Kˣ, (v : A.K) ∈ R → distribHaarChar A.K v ≤ 1 := by
    intro v hv
    have h2 : μ (v • A.OK) ≤ μ A.OK := measure_mono (hsmulO v hv)
    rw [← distribHaarChar_mul μ] at h2
    have h3 : (distribHaarChar A.K v : ℝ≥0∞) ≤ 1 := by
      rwa [← ENNReal.mul_le_mul_iff_left hμO0 hμOt, one_mul]
    exact_mod_cast h3
  have hlt1 : ∀ i, distribHaarChar A.K (u i) < 1 := by
    intro i
    have hsub := hsmulO (u i) (huR i)
    have hcl : IsClosed ((u i) • A.OK) := (hOc.smul (u i)).isClosed
    have hfi : f i ∉ (u i) • A.OK := by
      rintro ⟨y, hy, hyf⟩
      have hyf' : ((u i : A.Kˣ) : A.K) * y = f i := hyf
      have hy' : y = p' * f i := by
        have h1 : y = (((u i)⁻¹ : A.Kˣ) : A.K) * f i := by rw [← hyf', Units.inv_mul_cancel_left]
        rw [h1]
        show (f i * p' + (1 - f i)) * f i = p' * f i
        linear_combination (p' - 1) * hid i
      have hn : 1 < ‖π⁻¹‖ := by rw [norm_inv]; exact (one_lt_inv₀ hπ0).2 hπ1
      exact hsc i π⁻¹ hn (hy' ▸ hy)
    have hopen : IsOpen (A.OK \ (u i) • A.OK) := hOo.sdiff hcl
    have hpos : μ (A.OK \ (u i) • A.OK) ≠ 0 := hopen.measure_ne_zero μ ⟨f i, (hOR _).2 (hfR i), hfi⟩
    have hadd : μ ((u i) • A.OK) + μ (A.OK \ (u i) • A.OK) = μ A.OK := by
      rw [measure_add_sdiff hcl.measurableSet.nullMeasurableSet, Set.union_eq_right.2 hsub]
    have hlt : μ ((u i) • A.OK) < μ A.OK := by
      rw [← hadd]; exact ENNReal.lt_add_right (ne_top_of_le_ne_top hμOt (measure_mono hsub)) hpos
    rw [← distribHaarChar_mul μ] at hlt
    have h4 : (distribHaarChar A.K (u i) : ℝ≥0∞) < 1 := by
      by_contra hc
      have hc' : 1 ≤ (distribHaarChar A.K (u i) : ℝ≥0∞) := not_lt.1 hc
      have h5 : 1 * μ A.OK ≤ (distribHaarChar A.K (u i) : ℝ≥0∞) * μ A.OK := by gcongr
      rw [one_mul] at h5; exact absurd hlt (not_lt.2 h5)
    exact_mod_cast h4
  have hex : ∀ z : A.K, ∀ i, ∃ n : ℕ, π ^ n • (f i * z) ∈ A.OK := by
    intro z i
    have ht : Tendsto (fun n : ℕ => π ^ n • (f i * z)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπ1).smul_const (f i * z)
      simpa using this
    exact (ht.eventually (hOo.mem_nhds ((hOR 0).2 R.zero_mem))).exists

  let N : A.K → Fin m → ℕ := fun z i => Nat.find (hex z i)
  have hNspec : ∀ z i, π ^ N z i • (f i * z) ∈ A.OK := fun z i => Nat.find_spec (hex z i)
  have hNmin : ∀ z i, N z i ≠ 0 → π ^ (N z i - 1) • (f i * z) ∉ A.OK := fun z i hi =>
    Nat.find_min (hex z i) (Nat.sub_lt (Nat.pos_of_ne_zero hi) one_pos)
  have hsmul : ∀ (k : ℕ) (x : A.K), π ^ k • x = p ^ k * x := fun k x => by
    rw [Algebra.smul_def, map_pow]
  have hrep : ∀ x : A.K, x = ∑ j, f j * x := fun x => by rw [← Finset.sum_mul, hsum, one_mul]
  have hkey : ∀ z : A.K, ∃ s : A.Kˣ, ((s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
      ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1) ∧
      distribHaarChar A.K s ≤ ∏ i, distribHaarChar A.K (u i) ^ (N z i - 1) := by
    intro z
    set n := N z with hn
    have hn0 : ∀ i, π ^ n i • (f i * z) ∈ A.OK := fun i => hNspec z i
    have hnmin : ∀ i, n i ≠ 0 → f i * (π ^ (n i - 1) • z) ∉ A.OK := fun i hi => by
      rw [mul_smul_comm]; exact hNmin z i hi
    have hw : ∀ i, ∃ w ∈ R, n i ≠ 0 → w * (f i * (π ^ (n i - 1) • z)) = f i := by
      intro i
      by_cases hi : n i = 0
      · exact ⟨0, R.zero_mem, fun h => absurd hi h⟩
      · obtain ⟨w, hwO, hw⟩ := hvp i _ (hnmin i hi)
        exact ⟨w, (hOR w).1 hwO, fun _ => hw⟩
    choose w hwR hwf using hw
    obtain ⟨a, ha⟩ : ∃ a : Fin m → A.K, ∀ i, a i = if n i = 0 then 1 else w i := ⟨_, fun i => rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : Fin m → A.K, ∀ i, c i = if n i = 0 then 1 else π ^ (n i - 1) • z :=
      ⟨_, fun i => rfl⟩
    have haR : ∀ i, a i ∈ R := fun i => by
      rw [ha]; split_ifs
      · exact R.one_mem
      · exact hwR i
    have hac : ∀ i, f i * (a i * c i) = f i := fun i => by
      rw [ha, hc]; split_ifs with hi
      · ring
      · linear_combination hwf i hi
    obtain ⟨σ, hσ⟩ : ∃ σ : A.K, σ = ∑ i, f i * a i := ⟨_, rfl⟩
    obtain ⟨σ', hσ'⟩ : ∃ σ' : A.K, σ' = ∑ i, f i * c i := ⟨_, rfl⟩
    have hfσ : ∀ j, f j * σ = f j * a j := fun j => by rw [hσ]; exact mul_sum_eq hid hor a j
    have hfσ' : ∀ j, f j * σ' = f j * c j := fun j => by rw [hσ']; exact mul_sum_eq hid hor c j
    have hσσ : σ * σ' = 1 := by
      refine eq_of_mul_eq hsum fun j => ?_
      calc f j * (σ * σ') = (f j * σ) * σ' := by ring
        _ = a j * (f j * σ') := by rw [hfσ]; ring
        _ = f j * (a j * c j) := by rw [hfσ']; ring
        _ = f j * 1 := by rw [hac, mul_one]
    let σU : A.Kˣ := ⟨σ, σ', hσσ, by rw [mul_comm]; exact hσσ⟩
    have hσR : σ ∈ R := by rw [hσ]; exact R.sum_mem fun i _ => R.mul_mem (hfR i) (haR i)
    let q : A.Kˣ := ∏ i, u i ^ (n i - 1)
    have hfq : ∀ j, f j * (q : A.K) = f j * p ^ (n j - 1) := fun j => by
      rw [Units.coe_prod]; simp only [Units.val_pow_eq_pow_val]
      exact mul_prod_eq hid hor (fun _ => p) (fun i => n i - 1) j
    have hqR : (q : A.K) ∈ R := by
      rw [Units.coe_prod]
      exact R.prod_mem fun i _ => by rw [Units.val_pow_eq_pow_val]; exact R.pow_mem (huR i) _
    have hsval : ((σU * q : A.Kˣ) : A.K) = σ * q := rfl
    have hfs : ∀ j, f j * ((σU * q : A.Kˣ) : A.K) = a j * (f j * p ^ (n j - 1)) := fun j => by
      rw [hsval, ← hfq]
      calc f j * (σ * q) = (f j * σ) * q := by ring
        _ = _ := by rw [hfσ]; ring
    have hfs0 : ∀ j, n j = 0 → f j * ((σU * q : A.Kˣ) : A.K) = f j := fun j hj => by
      rw [hfs, ha, if_pos hj, hj]; simp
    have hfsz : ∀ j, f j * (((σU * q : A.Kˣ) : A.K) * z) = if n j = 0 then f j * z else f j := by
      intro j
      rw [← mul_assoc, hfs]
      split_ifs with hj
      · rw [ha, if_pos hj, hj]; simp
      · have h1 := hwf j hj
        rw [hsmul] at h1
        rw [ha, if_neg hj]; linear_combination h1
    refine ⟨σU * q, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hOR, hsval]; exact R.mul_mem hσR hqR
    · rw [hOR, hrep (((σU * q : A.Kˣ) : A.K) * z)]
      refine R.sum_mem fun j _ => ?_
      rw [hfsz]; split_ifs with hj
      · have h1 := hn0 j; rw [hj, pow_zero, one_smul, hOR] at h1; exact h1
      · exact hfR j
    · refine ⟨∑ i, f i * (if n i = 0 then 1 else 0), ?_, ∑ i, f i * (if n i = 0 then 0 else 1), ?_,
        eq_of_mul_eq hsum fun j => ?_⟩
      · rw [hOR]; refine R.sum_mem fun i _ => R.mul_mem (hfR i) ?_
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      · rw [hOR]; refine R.sum_mem fun i _ => R.mul_mem (hfR i) ?_
        split_ifs
        · exact R.zero_mem
        · exact R.one_mem
      · have e1 : ∀ (x y X Y : A.K), f j * (x * X + y * Y) = (f j * x) * X + (f j * y) * Y :=
          fun x y X Y => by ring
        rw [e1, mul_sum_eq hid hor, mul_sum_eq hid hor]
        split_ifs with hj
        · rw [mul_one, mul_zero, zero_mul, add_zero, hfs0 j hj]
        · rw [mul_zero, zero_mul, zero_add, mul_one, hfsz, if_neg hj]
    · rw [map_mul, map_prod]; simp only [map_pow]
      exact mul_le_of_le_one_left zero_le (hle1 σU hσR)

  set C : Fin m → ℝ≥0∞ := fun i => (distribHaarChar A.K (u i) : ℝ≥0∞) with hCdef
  set D : Fin m → ℝ≥0∞ := fun i => (distribHaarChar A.K (u i)⁻¹ : ℝ≥0∞) with hDdef
  have hCD : ∀ i, C i * D i = 1 := fun i => by
    simp only [hCdef, hDdef]
    rw [← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one]
  have hC1 : ∀ i, C i < 1 := fun i => ENNReal.coe_lt_one_iff.2 (hlt1 i)
  have hD1 : ∀ i, 1 ≤ D i := fun i => by
    calc (1 : ℝ≥0∞) = C i * D i := (hCD i).symm
      _ ≤ 1 * D i := by gcongr; exact (hC1 i).le
      _ = D i := one_mul _
  have hpow : ∀ i (k : ℕ), C i ^ (k - 1) ≤ D i * C i ^ k := fun i k => by
    cases k with
    | zero => simpa using hD1 i
    | succ k =>
      rw [Nat.add_sub_cancel, pow_succ, show D i * (C i ^ k * C i) = C i ^ k * (C i * D i) by ring,
        hCD, mul_one]
  let Q : (Fin m → ℕ) → A.Kˣ := fun k => ∏ i, u i ^ k i
  have hfQ : ∀ k j, f j * (Q k : A.K) = f j * p ^ k j := fun k j => by
    simp only [Q]; rw [Units.coe_prod]; simp only [Units.val_pow_eq_pow_val]
    exact mul_prod_eq hid hor (fun _ => p) k j
  let S : (Fin m → ℕ) → Set A.K := fun k => {z | (Q k : A.K) * z ∈ A.OK}
  have hzS : ∀ z, z ∈ S (N z) := fun z => by
    show (Q (N z) : A.K) * z ∈ A.OK
    rw [hOR, hrep ((Q (N z) : A.K) * z)]
    refine R.sum_mem fun j _ => ?_
    have h1 := hNspec z j
    rw [hsmul, hOR] at h1
    have e : f j * ((Q (N z) : A.K) * z) = p ^ N z j * (f j * z) := by
      rw [← mul_assoc, hfQ]; ring
    rw [e]; exact h1
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    (hOo.preimage (continuous_const_mul _)).measurableSet
  have hμS : ∀ k, μ (S k) = (∏ i, D i ^ k i) * μ A.OK := fun k => by
    have hset : S k = (Q k)⁻¹ • A.OK := by
      ext z; rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def]; rfl
    have hinv : (Q k)⁻¹ = ∏ i, (u i)⁻¹ ^ k i := by
      simp only [Q, ← Finset.prod_inv_distrib, inv_pow]
    rw [hset, ← distribHaarChar_mul μ, hinv]
    simp only [hDdef, map_prod, map_pow, ENNReal.ofNNReal_finsetProd, ENNReal.coe_pow]
  refine lt_of_le_of_lt (lintegral_mono (g := fun z => ∑' k : Fin m → ℕ,
    (S k).indicator (fun _ => (∏ i, D i) ^ 2 * ∏ i, (C i ^ k i) ^ 2) z) fun z => ?_) ?_
  · obtain ⟨s, hs, hsle⟩ := hkey z
    have h1 : (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK,
        α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ≤ ∏ i, C i ^ (N z i - 1) := by
      refine (iInf₂_le s hs).trans ?_
      have e : A.absK (s : A.K) = distribHaarChar A.K s := by simp [Et.absK]
      rw [e, ENNReal.ofReal_coe_nnreal]
      simp only [hCdef]
      exact_mod_cast hsle
    have h2 : ∏ i, C i ^ (N z i - 1) ≤ (∏ i, D i) * ∏ i, C i ^ N z i := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_le_prod' fun i _ => hpow i _
    refine le_trans ?_ (ENNReal.le_tsum (N z))
    rw [Set.indicator_of_mem (hzS z), Finset.prod_pow, ← mul_pow]
    exact pow_le_pow_left₀ zero_le (h1.trans h2) 2
  · rw [lintegral_tsum (fun k => (measurable_const.indicator (hSm k)).aemeasurable)]
    have hterm : ∀ k : Fin m → ℕ, ∫⁻ z, (S k).indicator (fun _ => (∏ i, D i) ^ 2 * ∏ i, (C i ^ k i) ^ 2) z ∂μ
        = ((∏ i, D i) ^ 2 * μ A.OK) * ∏ i, C i ^ k i := by
      intro k
      rw [lintegral_indicator_const (hSm k), hμS]
      have e : (∏ i, (C i ^ k i) ^ 2) * ∏ i, D i ^ k i = ∏ i, C i ^ k i := by
        rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun i _ => ?_
        rw [sq, mul_assoc, ← mul_pow, hCD, one_pow, mul_one]
      calc _ = (∏ i, D i) ^ 2 * μ A.OK * ((∏ i, (C i ^ k i) ^ 2) * ∏ i, D i ^ k i) := by ring
        _ = _ := by rw [e]
    rw [tsum_congr hterm, ENNReal.tsum_mul_left]
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top
      (ENNReal.prod_lt_top fun i _ => ENNReal.coe_lt_top)) hμOt.lt_top) ?_
    refine lt_of_le_of_lt (tsum_pi_prod_le' (fun i (x : ℕ) => C i ^ x)) ?_
    refine ENNReal.prod_lt_top fun i _ => ?_
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt (hC1 i))

end GlobalTheory.JR.HeightSquareIntegrable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHeightSqLintegralLtTopStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.K), μ.IsAddHaarMeasure → ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ < ⊤ := by
  first | exact @GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top | exact GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top | (intros; apply GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerBoundBigCell
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerBoundBigCell
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LamBound

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem norm_etaK (A : Et F E) (t : A.K) : ‖A.etaK t‖ = 1 := by
  unfold Et.etaK eta
  split_ifs <;> simp

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK
  split_ifs <;> simp

theorem bdd_of_loc_const (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (O : Set K) (hO : IsCompact O) (Ψ : SpecialLinearGroup (Fin 2) K → ℂ) (U : Set K) (hU : U ∈ 𝓝 (0 : K))
    (hΨ : ∀ g k : SpecialLinearGroup (Fin 2) K, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) K) - 1) i j ∈ U) →
      Ψ (g * k) = Ψ g) :
    ∃ C : ℝ, ∀ k : SpecialLinearGroup (Fin 2) K, (∀ i j, (k : Matrix (Fin 2) (Fin 2) K) i j ∈ O) → ‖Ψ k‖ ≤ C := by
  classical
  let T : Set (Matrix (Fin 2) (Fin 2) K) := {M | ∀ i j, M i j ∈ O} ∩ {M | M.det = 1}
  have hT : IsCompact T := by
    have h1 : IsCompact {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} := by
      have := isCompact_univ_pi (fun _ : Fin 2 => isCompact_univ_pi (fun _ : Fin 2 => hO))
      have he : {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} =
          Set.univ.pi (fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => O) := by
        ext M
        exact ⟨fun h => Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => h i j,
          fun h i j => Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h i) j⟩
      rw [he]; exact this
    exact h1.inter_right (isClosed_eq (continuous_id.matrix_det) continuous_const)
  let N : Matrix (Fin 2) (Fin 2) K → Set (Matrix (Fin 2) (Fin 2) K) := fun M =>
    {M' | ∀ i j, (M.adjugate * M' - 1) i j ∈ U}
  have hN : ∀ M ∈ T, N M ∈ 𝓝 M := by
    intro M hM
    have hc : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => M.adjugate * M' - 1) :=
      (continuous_const.matrix_mul continuous_id).sub continuous_const
    have h0 : M.adjugate * M - 1 = 0 := by
      rw [Matrix.adjugate_mul, hM.2]; simp
    have hij : ∀ i j, ∀ᶠ M' in 𝓝 M, (M.adjugate * M' - 1) i j ∈ U := by
      intro i j
      have hcij : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => (M.adjugate * M' - 1) i j) :=
        hc.matrix_elem i j
      have := hcij.tendsto M
      simp only [h0, Matrix.zero_apply] at this
      exact this hU
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  obtain ⟨t, htT, hcov⟩ := hT.elim_nhds_subcover N hN
  let g : Matrix (Fin 2) (Fin 2) K → ℝ := fun M => if h : M.det = 1 then ‖Ψ ⟨M, h⟩‖ else 0
  refine ⟨∑ M ∈ t, g M, fun k hk => ?_⟩
  have hkT : (k : Matrix (Fin 2) (Fin 2) K) ∈ T := ⟨hk, k.2⟩
  obtain ⟨M, hMt, hkM⟩ := Set.mem_iUnion₂.1 (hcov hkT)
  have hdet : M.det = 1 := (htT M hMt).2
  let k₀ : SpecialLinearGroup (Fin 2) K := ⟨M, hdet⟩
  have he : Ψ k = Ψ k₀ := by
    have := hΨ k₀ (k₀⁻¹ * k) (by
      intro i j
      have := hkM i j
      exact this)
    simpa using this
  have hg : g M = ‖Ψ k₀‖ := by simp only [g, dif_pos hdet]; rfl
  rw [he, ← hg]
  exact Finset.single_le_sum (f := g) (fun M _ => by simp only [g]; split_ifs <;> positivity) hMt

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ), A.InI Ψ → ∃ C : ℝ, ∀ (z : A.K) (s : A.Kˣ) (α β : A.K), α ∈ A.OK → β ∈ A.OK → (s : A.K) ∈ A.OK → (s : A.K) * z ∈ A.OK → α * s + β * (s * z) = 1 → ‖Ψ (wS A.K * nS z)‖ ≤ C * A.absK s := by
  intro F E _ _ _ _ U A Ψ hΨ
  have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let b := Module.finBasis F A.K
  have : T2Space A.K := .of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcpt, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨V, hV, hloc⟩ := hΨ.1
  obtain ⟨C, hC⟩ := bdd_of_loc_const A.K A.OK hcpt Ψ V hV hloc
  refine ⟨C, fun z s α β hα hβ hs hsz h => ?_⟩
  have hu : (s : A.K) * ((s⁻¹ : A.Kˣ) : A.K) = 1 := Units.mul_inv s
  let k : SpecialLinearGroup (Fin 2) A.K := ⟨!![-β, α; -(s : A.K), -((s : A.K) * z)], by
    simp [Matrix.det_fin_two]; linear_combination h⟩
  have hk : wS A.K * nS z = nS (-((s : A.K) * β)) * mS s * k := by
    apply Subtype.ext
    show !![(0 : A.K), 1; -1, 0] * !![1, z; 0, 1] =
      !![1, -((s : A.K) * β); 0, 1] * !![(s : A.K), 0; 0, ((s⁻¹ : A.Kˣ) : A.K)] * !![-β, α; -(s : A.K), -((s : A.K) * z)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination (-1 : A.K) * h - (β * (s : A.K) * z) * hu
  have hkO : ∀ i j, (k : Matrix (Fin 2) (Fin 2) A.K) i j ∈ A.OK := by
    rw [← hR]
    have hα' : α ∈ R := by rw [← SetLike.mem_coe, hR]; exact hα
    have hβ' : β ∈ R := by rw [← SetLike.mem_coe, hR]; exact hβ
    have hs' : (s : A.K) ∈ R := by rw [← SetLike.mem_coe, hR]; exact hs
    have hsz' : (s : A.K) * z ∈ R := by rw [← SetLike.mem_coe, hR]; exact hsz
    intro i j; fin_cases i <;> fin_cases j <;> simp [k, R.neg_mem, hα', hβ', hs', hsz']
  rw [hk, hΨ.2, norm_mul, norm_mul, norm_etaK, Complex.norm_real, Real.norm_of_nonneg (absK_nonneg A _), one_mul,
    mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC k hkO) (absK_nonneg A _)

end GlobalTheory.JR.LamBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerBoundBigCellStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_bound_big_cell : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ), A.InI Ψ → ∃ C : ℝ, ∀ (z : A.K) (s : A.Kˣ) (α β : A.K), α ∈ A.OK → β ∈ A.OK → (s : A.K) ∈ A.OK → (s : A.K) * z ∈ A.OK → α * s + β * (s * z) = 1 → ‖Ψ (wS A.K * nS z)‖ ≤ C * A.absK s := by
  first | exact @GlobalTheory.JR.LamBound.main | exact GlobalTheory.JR.LamBound.main | (intros; apply GlobalTheory.JR.LamBound.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerFunctionalWeylVanishOfWeylUnipotentZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerFunctionalWeylVanishOfWeylUnipotentZero
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem wS_nS_wS_eq_unit {k : Type} [CommRing k] (z : kˣ) :
    wS k * nS (z : k) * wS k = nS ((-z⁻¹ : kˣ) : k) * mS (-z⁻¹) * (wS k * nS ((-z⁻¹ : kˣ) : k)) := by
  have h1 : (z : k) * ((z⁻¹ : kˣ) : k) = 1 := z.mul_inv
  have cw : ((wS k : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  have cn : ∀ t : k, ((nS t : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![1, t; 0, 1] :=
    fun _ => rfl
  have cm : ∀ s : kˣ, ((mS s : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(s : k), 0; 0, ((s⁻¹ : kˣ) : k)] := fun _ => rfl
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, cw, cn, cm]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two] <;> ring_nf <;> simp [h1]

theorem lam_flip_eq_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ μK hμ Ψ hΨ h0 a c
  have hnull : μK {t | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hμ
  have hae : ∀ᵐ z ∂μK, IsUnit z := ae_iff.2 hnull
  unfold Et.abelian₂
  apply integral_eq_zero_of_ae
  apply ae_restrict_of_ae
  filter_upwards [hae] with z hz
  obtain ⟨u, rfl⟩ := hz
  simp only [Pi.zero_apply]
  rw [wS_nS_wS_eq_unit u, hΨ.2, h0, mul_zero, zero_mul]

end GlobalTheory.JR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerFunctionalWeylVanishOfWeylUnipotentZeroStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.lam_flip_eq_zero | exact GlobalTheory.JR.lam_flip_eq_zero | (intros; apply GlobalTheory.JR.lam_flip_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KirillovVanishingOfLimit
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LTwoLemma
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem u_locallyConstant (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    IsLocallyConstant (fun z => Ψ (wS A.K * nS z)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  obtain ⟨U, hU, hinv⟩ := h.1
  have h0 : (0 : A.K) ∈ U := mem_of_mem_nhds hU
  have ht : Tendsto (fun y : A.K => y - z) (𝓝 z) (𝓝 0) :=
    (continuous_sub_right z).tendsto' z 0 (sub_self z)
  filter_upwards [ht hU] with y hy
  simp only [Set.mem_preimage] at hy
  have he : wS A.K * nS y = (wS A.K * nS z) * nS (y - z) := by
    rw [mul_assoc]; congr 1; apply Subtype.ext
    show !![(1 : A.K), y; 0, 1] = !![1, z; 0, 1] * !![1, y - z; 0, 1]
    rw [Matrix.mul_fin_two]; simp
  rw [he]
  apply hinv
  intro i j
  fin_cases i <;> fin_cases j <;> simp [nS, h0, hy]

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK; split_ifs <;> simp

theorem weyl_unipotent_l2_finite [Unram F E] (hB1 : type_of% GlobalTheory.T.whittaker_bound_big_cell) (hB2 : type_of% GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top) (A : Et F E) (μ : Measure A.K) (hμ : μ.IsAddHaarMeasure)
    (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ) (h : A.InI Ψ) :
    ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ < ⊤ := by
  obtain ⟨C, hC⟩ := hB1 F E A Ψ h
  have hB := hB2 F E A μ hμ
  have h0 : ENNReal.ofReal C + 1 ≠ 0 := by simp
  have hT : ENNReal.ofReal C + 1 ≠ ⊤ := by simp
  have hle : ∀ z, ‖Ψ (wS A.K * nS z)‖ₑ ≤ (ENNReal.ofReal C + 1) *
      ⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK,
        α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s) := by
    intro z
    simp only [ENNReal.mul_iInf_of_ne h0 hT]
    refine le_iInf₂ fun s hs => ?_
    obtain ⟨hs1, hs2, α, hα, β, hβ, he⟩ := hs
    have hb := hC z s α β hα hβ hs1 hs2 he
    calc ‖Ψ (wS A.K * nS z)‖ₑ = ENNReal.ofReal ‖Ψ (wS A.K * nS z)‖ := (ofReal_norm_eq_enorm _).symm
      _ ≤ ENNReal.ofReal (C * A.absK s) := ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal C * ENNReal.ofReal (A.absK s) := ENNReal.ofReal_mul' (absK_nonneg A _)
      _ ≤ _ := by gcongr; exact le_self_add
  calc ∫⁻ z, ‖Ψ (wS A.K * nS z)‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ z, ((ENNReal.ofReal C + 1) * ⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
          ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ :=
        lintegral_mono fun z => pow_le_pow_left' (hle z) 2
    _ = (ENNReal.ofReal C + 1) ^ 2 * ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
          ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ := by
        simp_rw [mul_pow]
        exact lintegral_const_mul' _ _ (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hB

end GlobalTheory.JR.LTwoLemma

open GlobalTheory.JR.LTwoLemma in
theorem GlobalTheory.JR.kirillov_vanishing_l2 : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd Ψ hI hlim
  have hμ : μK.IsAddHaarMeasure := hsd.1
  have hu : (fun z => Ψ (wS A.K * nS z)) = 0 :=
    GlobalTheory.T.eq_zero_of_truncatedFourier_tendsto_zero_etale F E A ψ hψ μK hsd _ (u_locallyConstant A Ψ hI) (weyl_unipotent_l2_finite GlobalTheory.T.whittaker_bound_big_cell GlobalTheory.T.unimodularHeight_sq_lintegral_lt_top A μK hμ Ψ hI) hlim
  have h1 : ∀ z, Ψ (wS A.K * nS z) = 0 := fun z => congrFun hu z
  exact ⟨h1, GlobalTheory.T.whittakerFunctional_weyl_vanish_of_weylUnipotent_zero F E A ψ μK hμ Ψ hI h1⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KirillovVanishingOfLimitStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_vanishing_of_limit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ Ψ, A.InI Ψ → (∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0)) → (∀ z, Ψ (wS A.K * nS z) = 0) ∧ ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  first | exact @GlobalTheory.JR.kirillov_vanishing_l2 | exact GlobalTheory.JR.kirillov_vanishing_l2 | (intros; apply GlobalTheory.JR.kirillov_vanishing_l2 <;> assumption)
end
