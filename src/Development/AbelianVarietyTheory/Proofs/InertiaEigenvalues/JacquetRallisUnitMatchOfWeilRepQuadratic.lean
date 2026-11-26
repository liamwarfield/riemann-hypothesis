module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KirillovVanishingOfLimit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypMemInducedFourierWeyl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerJHypEqOrbitalIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerWeilRepEventually
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSucc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchingOfWeilField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformKProdLocallyConstantCompactSuppo
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformKProdLocallyConstantCompactSuppo
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.FourKTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def betaK (A : Et F E) : LinearMap.BilinForm F (A.K × A.K) :=
  (Algebra.traceForm F A.K).compl₁₂ (LinearMap.fst F A.K A.K) (LinearMap.snd F A.K A.K) +
    (Algebra.traceForm F A.K).compl₁₂ (LinearMap.snd F A.K A.K) (LinearMap.fst F A.K A.K)

theorem betaK_apply (A : Et F E) (x y : A.K × A.K) :
    betaK A x y = Algebra.trace F A.K (x.1 * y.2) + Algebra.trace F A.K (x.2 * y.1) := by
  simp [betaK, Algebra.traceForm_apply]

theorem betaK_isSymm (A : Et F E) : (betaK A).IsSymm :=
  ⟨fun x y => by rw [betaK_apply, betaK_apply, mul_comm x.1, mul_comm x.2, add_comm]⟩

theorem betaK_nondeg (A : Et F E) (h : (Algebra.traceForm F A.K).Nondegenerate) : (betaK A).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (betaK A) := by
    intro x hx
    have h1 : x.1 = 0 := h.1 x.1 fun z => by
      have := hx (0, z); rw [betaK_apply] at this; simpa [Algebra.traceForm_apply] using this
    have h2 : x.2 = 0 := h.1 x.2 fun z => by
      have := hx (z, 0); rw [betaK_apply] at this; simpa [Algebra.traceForm_apply] using this
    exact Prod.ext h1 h2
  refine ⟨hl, fun y hy => hl y fun x => ?_⟩
  rw [(betaK_isSymm A).eq]; exact hy x

theorem secondCountable [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).secondCountableTopology

theorem psi_continuous (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : ψ y = ψ x * ψ (y - x) := by rw [← AddChar.map_add_eq_mul]; congr 1; abel
  rw [this, hψ.1 (y - x) (by rwa [Metric.mem_closedBall, dist_eq_norm] at hy), mul_one]

theorem fourK_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (A.fourK μK ψ φ') := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  haveI := secondCountable A
  haveI : μK.IsAddHaarMeasure := hsd.1
  haveI : (μK.prod μK).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have key := (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ (A.K × A.K) (betaK A) (betaK_isSymm A) (betaK_nondeg A hnd)).2
    (μK.prod μK) inferInstance φ' hφ
  have hψc := psi_continuous ψ hψ
  have heq : A.fourK μK ψ φ' = fourB (μK.prod μK) (fun x y => ψ (betaK A x y)) φ' := by
    funext p
    simp only [fourB, Et.fourK]
    rw [integral_prod]
    · refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
      refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
      simp only [Et.psiK, betaK_apply, map_add (f := _)]
      congr 1
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, mul_comm p.1, mul_comm c' p.1]
      ring
    · apply Continuous.integrable_of_hasCompactSupport
      · exact hφ.1.continuous.mul (hψc.comp (IsModuleTopology.continuous_of_linearMap ((betaK A).flip p)))
      · exact hφ.2.mul_right
  rw [heq]; exact key

end GlobalTheory.FourKTest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformKProdLocallyConstantCompactSuppoStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTransformKProd_locallyConstantCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (A.fourK μK ψ φ') := by
  first | exact @GlobalTheory.FourKTest.fourK_isTest | exact GlobalTheory.FourKTest.fourK_isTest | (intros; apply GlobalTheory.FourKTest.fourK_isTest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepEvalZeroMemInduced
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousEtaleHermitianPairNormAndMapZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousEtaleHermitianPairNormAndMapZero
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem etale_norm_continuous_and_zero (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) : Continuous A.NL ∧ A.NL 0 = 0 := by
  classical
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hb : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  let b0 := Module.finBasisOfFinrankEq F E h2
  let b : Module.Basis (Fin 2) A.K A.L := hb.basis b0
  have hN : ∀ y, A.NL y = (Algebra.leftMulMatrix b y).det := fun y => Algebra.norm_eq_matrix_det b y
  refine ⟨?_, ?_⟩
  · have : A.NL = fun y => (Algebra.leftMulMatrix b y).det := funext hN
    rw [this]
    refine Continuous.matrix_det ?_
    refine continuous_pi fun i => continuous_pi fun j => ?_
    let f : A.L →ₗ[F] A.K := ((b.coord i).comp (LinearMap.mulRight A.K (b j))).restrictScalars F
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    refine hf.congr fun y => ?_
    simp [f, Algebra.leftMulMatrix_eq_repr_mul]
  · rw [hN, map_zero]
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousEtaleHermitianPairNormAndMapZeroStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_etaleHermitianPair_norm_and_map_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Continuous A.NL ∧ A.NL 0 = 0 := by
  first | exact @GlobalTheory.etale_norm_continuous_and_zero | exact GlobalTheory.etale_norm_continuous_and_zero | (intros; apply GlobalTheory.etale_norm_continuous_and_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairEventuallyIsUnitContinuousAtIn
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairEventuallyIsUnitContinuousAtIn
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem units_near_one_inverse_continuousAt (F K : Type) [NontriviallyNormedField F] [CommRing K] [Algebra F K]
    [Module.Finite F K] [TopologicalSpace K] [IsModuleTopology F K] [IsTopologicalRing K] :
    (∀ᶠ a in 𝓝 (1 : K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : K) := by
  classical
  let b := Module.finBasis F K
  let ι : K →ₐ[F] Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F := Algebra.leftMulMatrix b
  have hι : Continuous ι := IsModuleTopology.continuous_of_linearMap ι.toLinearMap
  have hdet : Continuous fun a : K => (ι a).det := (continuous_id.matrix_det).comp hι
  have h1 : (ι 1).det ≠ 0 := by simp
  have hev : ∀ᶠ a in 𝓝 (1 : K), (ι a).det ≠ 0 :=
    hdet.continuousAt.eventually_ne h1
  have hunit : ∀ a : K, (ι a).det ≠ 0 → IsUnit a := by
    intro a ha
    have hn : Algebra.norm F a ≠ 0 := by rw [Algebra.norm_eq_matrix_det b]; exact ha
    rw [Algebra.norm_apply] at hn
    have hu : IsUnit (Algebra.lmul F K a) := by
      rw [LinearMap.isUnit_iff_isUnit_det]; exact hn.isUnit
    obtain ⟨c, hc⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
    exact IsUnit.of_mul_eq_one c (by simpa using hc)
  have hev' : ∀ᶠ a in 𝓝 (1 : K), IsUnit a := hev.mono hunit
  refine ⟨hev', ?_⟩
  let g : K → K := fun a => b.equivFun.symm ((ι a)⁻¹ *ᵥ b.equivFun 1)
  have hinv : ∀ a : K, IsUnit a → (ι a)⁻¹ = ι (Ring.inverse a) := by
    intro a ha
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
  have heq : g =ᶠ[𝓝 (1 : K)] Ring.inverse := by
    filter_upwards [hev'] with a ha
    simp only [g, hinv a ha, Module.Basis.equivFun_apply, ι, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]
  refine ContinuousAt.congr ?_ heq
  have hsymm : Continuous b.equivFun.symm := LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hdet1 : ContinuousAt Ring.inverse (ι 1).det := by
    have : (ι 1).det = 1 := by simp
    rw [this]
    have : (Ring.inverse : F → F) = Inv.inv := funext Ring.inverse_eq_inv
    rw [this]
    exact continuousAt_inv₀ one_ne_zero
  have hmi : ContinuousAt (fun a : K => (ι a)⁻¹) 1 :=
    (continuousAt_matrix_inv (ι 1) hdet1).comp hι.continuousAt
  have hmv : Continuous fun M : Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F => M *ᵥ b.equivFun 1 :=
    continuous_id.matrix_mulVec continuous_const
  exact hsymm.continuousAt.comp (hmv.continuousAt.comp hmi)

theorem et_units_near_one_inverse_continuousAt :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) :=
  fun F _ _ _ _ _ A => units_near_one_inverse_continuousAt F A.K

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairEventuallyIsUnitContinuousAtInStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHermitianPair_eventually_isUnit_continuousAt_inverse : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) := by
  first | exact @GlobalTheory.et_units_near_one_inverse_continuousAt | exact GlobalTheory.et_units_near_one_inverse_continuousAt | (intros; apply GlobalTheory.et_units_near_one_inverse_continuousAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepEvalZeroMemInduced
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.WeilSmooth

def lS {k : Type} [CommRing k] (u : k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; u, 1], by simp [Matrix.det_fin_two]⟩

theorem sl_ext {k : Type} [CommRing k] {A B : SpecialLinearGroup (Fin 2) k}
    (h : (A : Matrix (Fin 2) (Fin 2) k) = B) : A = B := Subtype.ext h

theorem lS_eq {k : Type} [CommRing k] (u : k) : lS u = (wS k)⁻¹ * nS (-u) * wS k := by
  apply sl_ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lS, nS, wS, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem mid_eq {k : Type} [CommRing k] (a a' t t' : k) (ha : a * a' = 1) (ht : t * t' = 1) :
    ((nS ((a - 1) * t') * lS t * nS ((a' - 1) * t') * lS (-(t * a)) : SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) = !![a, 0; 0, a'] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lS, nS, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (a-1)*ht - t*a*((a-1)*(a'-1)*t'*ht + t'*ha)
  · linear_combination (a-1)*(a'-1)*t' * ht + t' * ha
  · linear_combination (-t*a*(a'-1))*ht - t*ha
  · linear_combination (a'-1)*ht

theorem decomp {k : Type} [CommRing k] (g : SpecialLinearGroup (Fin 2) k) (a' t t' : k)
    (ha : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * a' = 1) (ht : t * t' = 1) :
    g = lS ((g : Matrix (Fin 2) (Fin 2) k) 1 0 * a') * (nS (((g : Matrix (Fin 2) (Fin 2) k) 0 0 - 1) * t') * lS t *
      nS ((a' - 1) * t') * lS (-(t * (g : Matrix (Fin 2) (Fin 2) k) 0 0))) *
      nS ((g : Matrix (Fin 2) (Fin 2) k) 0 1 * a') := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) k) 0 1 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; exact this
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mid_eq _ _ _ _ ha ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lS, nS, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 0 1) * ha
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 1 0) * ha
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 1 0 * (g : Matrix (Fin 2) (Fin 2) k) 0 1 * a' +
      (g : Matrix (Fin 2) (Fin 2) k) 1 1) * ha + a' * hdet

end GlobalTheory.WeilSmooth

noncomputable section
namespace GlobalTheory.WeilSmooth
open GlobalTheory.JR

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem nl_cont [Unram F E] (A : Et F E) : Continuous A.NL ∧ A.NL 0 = 0 := GlobalTheory.T.continuous_etaleHermitianPair_norm_and_map_zero F E A
theorem inv_cont (A : Et F E) : (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) :=
  GlobalTheory.T.etaleHermitianPair_eventually_isUnit_continuousAt_inverse F E A

theorem fix_n [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) (ω : A.K → ℂ)
    (μ : Measure A.L) (γ : ℂ) (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ)
    (hW : A.IsWeil ψ x ω μ γ W) (f : A.L → ℂ) (hf : IsTest f) :
    ∀ᶠ z in 𝓝 (0 : A.K), W (nS z) f = f := by
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun p : A.K × A.L => ‖Algebra.trace F A.K (p.1 * x * A.NL p.2)‖ :=
    (htr.comp ((continuous_fst.mul continuous_const).mul ((nl_cont A).1.comp continuous_snd))).norm
  have hK : IsCompact (tsupport f) := hf.2
  have hev : ∀ᶠ z in 𝓝 (0 : A.K), ∀ y ∈ tsupport f, ‖Algebra.trace F A.K (z * x * A.NL y)‖ < 1 := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h0 : ‖Algebra.trace F A.K ((0 : A.K) * x * A.NL y)‖ < 1 := by simp
    exact hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds h0)
  filter_upwards [hev] with z hz
  funext y
  rw [(hW.2 f hf).1 z y]
  by_cases hy : y ∈ tsupport f
  · rw [Et.psiK, hψ.1 _ (hz y hy).le, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

theorem fix_l [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) (ω : A.K → ℂ)
    (μ : Measure A.L) (γ : ℂ) (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ)
    (hW : A.IsWeil ψ x ω μ γ W) (f : A.L → ℂ) (hf : IsTest f) :
    ∀ᶠ u in 𝓝 (0 : A.K), W (lS u) f = f := by
  have h1 := fix_n A ψ hψ x ω μ γ W hW (W (wS A.K) f) (hW.1.1 _ _ hf)
  have h2 : Tendsto (fun u : A.K => -u) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.tendsto (0 : A.K))
  filter_upwards [h2.eventually h1] with u hu
  have hwf := hW.1.1 (wS A.K) f hf
  calc W (lS u) f = W ((wS A.K)⁻¹ * nS (-u) * wS A.K) f := by rw [lS_eq]
    _ = W (wS A.K)⁻¹ (W (nS (-u)) (W (wS A.K) f)) := by
        rw [hW.1.2.2.1 _ _ _ hf, hW.1.2.2.1 _ _ _ hwf]
    _ = W ((wS A.K)⁻¹ * wS A.K) f := by rw [hu, hW.1.2.2.1 _ _ _ hf]
    _ = f := by rw [inv_mul_cancel, hW.1.2.1 _ hf]

theorem jx_mem_induced : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L) (γ : ℂ) W, A.IsWeil ψ x A.etaK μ γ W → ∀ φ, IsTest φ → A.InI (fun g => W g φ 0) ∧ (φ ≠ 0 → γ ≠ 0) := by
  intro F E _ _ _ _ _ A ψ hψ x μ γ W hW φ hφ
  obtain ⟨⟨htest, hone, hmul, hlin⟩, hact⟩ := id hW
  have ht0 : IsTest (0 : A.L → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  have h0 : ∀ g, W g 0 = 0 := by
    intro g
    have := hlin g (-1) 0 0 ht0 ht0
    simpa using this
  have hfix : ∀ g h, W h φ = φ → W (g * h) φ = W g φ := fun g h hh => by rw [hmul _ _ _ hφ, hh]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hn := fix_n A ψ hψ x A.etaK μ γ W hW φ hφ
    have hl := fix_l A ψ hψ x A.etaK μ γ W hW φ hφ
    obtain ⟨hunit, hinv⟩ := inv_cont A
    have hQ : ∀ᶠ u in 𝓝 (0 : A.K), ∀ᶠ v in 𝓝 u, W (lS v) φ = φ := hl.eventually_nhds
    haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
    have hcm : Continuous (algebraMap F A.K) := continuous_algebraMap F A.K
    have hQ2 : ∀ᶠ c in 𝓝 (0 : F), (∀ᶠ v in 𝓝 (algebraMap F A.K c), W (lS v) φ = φ) ∧
        ∀ᶠ v in 𝓝 (-algebraMap F A.K c), W (lS v) φ = φ := by
      have e1 : Tendsto (algebraMap F A.K) (𝓝 0) (𝓝 0) := by simpa using hcm.tendsto 0
      have e2 : Tendsto (fun c => -algebraMap F A.K c) (𝓝 0) (𝓝 0) := by simpa using (hcm.tendsto 0).neg
      exact (e1.eventually hQ).and (e2.eventually hQ)
    haveI := NormedField.nhdsNE_neBot (0 : F)
    obtain ⟨c, ⟨hc1, hc2⟩, hc0⟩ := ((hQ2.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {y : F | y ≠ 0} ∈ 𝓝[≠] (0 : F))).exists
    set t := algebraMap F A.K c with ht_def
    set t' := algebraMap F A.K c⁻¹ with ht'_def
    have htt : t * t' = 1 := by rw [ht_def, ht'_def, ← map_mul, mul_inv_cancel₀ hc0, map_one]
    have hq1 : Tendsto (fun q : A.K × A.K × A.K => q.1) (𝓝 (0, 0, 0)) (𝓝 0) :=
      continuous_fst.tendsto ((0 : A.K), (0 : A.K), (0 : A.K))
    have ha : Tendsto (fun q : A.K × A.K × A.K => 1 + q.1) (𝓝 (0, 0, 0)) (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : A.K))).add hq1
    have hi : Tendsto (fun q : A.K × A.K × A.K => Ring.inverse (1 + q.1)) (𝓝 (0, 0, 0)) (𝓝 1) := by
      have := hinv.tendsto.comp ha
      rw [Ring.inverse_one] at this
      exact this
    have hq2 : Tendsto (fun q : A.K × A.K × A.K => q.2.1) (𝓝 (0, 0, 0)) (𝓝 0) :=
      (continuous_fst.comp continuous_snd).tendsto ((0 : A.K), (0 : A.K), (0 : A.K))
    have hq3 : Tendsto (fun q : A.K × A.K × A.K => q.2.2) (𝓝 (0, 0, 0)) (𝓝 0) :=
      (continuous_snd.comp continuous_snd).tendsto ((0 : A.K), (0 : A.K), (0 : A.K))
    have key : ∀ᶠ q : A.K × A.K × A.K in 𝓝 (0, 0, 0), IsUnit (1 + q.1) ∧
        W (lS (q.2.2 * Ring.inverse (1 + q.1))) φ = φ ∧ W (nS (q.1 * t')) φ = φ ∧
        W (nS ((Ring.inverse (1 + q.1) - 1) * t')) φ = φ ∧ W (lS (-(t * (1 + q.1)))) φ = φ ∧
        W (nS (q.2.1 * Ring.inverse (1 + q.1))) φ = φ := by
      have f1 : Tendsto (fun q : A.K × A.K × A.K => q.2.2 * Ring.inverse (1 + q.1)) (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using hq3.mul hi
      have f2 : Tendsto (fun q : A.K × A.K × A.K => q.1 * t') (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using hq1.mul_const t'
      have f3 : Tendsto (fun q : A.K × A.K × A.K => (Ring.inverse (1 + q.1) - 1) * t') (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using (hi.sub_const 1).mul_const t'
      have f4 : Tendsto (fun q : A.K × A.K × A.K => -(t * (1 + q.1))) (𝓝 (0, 0, 0)) (𝓝 (-t)) := by
        simpa using (ha.const_mul t).neg
      have f5 : Tendsto (fun q : A.K × A.K × A.K => q.2.1 * Ring.inverse (1 + q.1)) (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using hq2.mul hi
      exact (ha.eventually hunit).and ((f1.eventually hl).and ((f2.eventually hn).and ((f3.eventually hn).and
        ((f4.eventually hc2).and (f5.eventually hn)))))
    rw [nhds_prod_eq, nhds_prod_eq] at key
    obtain ⟨p1, hp1, p2, hp2, h12⟩ := eventually_prod_iff.1 key
    obtain ⟨p3, hp3, p4, hp4, h34⟩ := eventually_prod_iff.1 hp2
    refine ⟨{e | p1 e ∧ p3 e ∧ p4 e}, hp1.and (hp3.and hp4), ?_⟩
    intro g k hk
    have e00 : ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) 0 0 = (k : Matrix (Fin 2) (Fin 2) A.K) 0 0 - 1 := by simp
    have e01 : ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) 0 1 = (k : Matrix (Fin 2) (Fin 2) A.K) 0 1 := by simp
    have e10 : ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) 1 0 = (k : Matrix (Fin 2) (Fin 2) A.K) 1 0 := by simp
    have k1 := (hk 0 0).1
    have k2 := (hk 0 1).2.1
    have k3 := (hk 1 0).2.2
    rw [e00] at k1
    rw [e01] at k2
    rw [e10] at k3
    obtain ⟨hu, hP1, hP2, hP3, hP4, hP5⟩ := h12 k1 (h34 k2 k3)
    have h1a : (1 : A.K) + ((k : Matrix (Fin 2) (Fin 2) A.K) 0 0 - 1) = (k : Matrix (Fin 2) (Fin 2) A.K) 0 0 := by ring
    simp only [h1a] at hu hP1 hP2 hP3 hP4 hP5
    have hdec := decomp k (Ring.inverse ((k : Matrix (Fin 2) (Fin 2) A.K) 0 0)) t t'
      (Ring.mul_inverse_cancel _ hu) htt
    have hk : W k φ = φ := by
      rw [hdec, hfix _ _ hP5, hfix _ _ ?_, hP1]
      rw [hfix _ _ hP4, hfix _ _ hP3, hfix _ _ hc1.self_of_nhds, hP2]
    show W (g * k) φ 0 = W g φ 0
    rw [hfix _ _ hk]
  · intro z s g
    have hg := htest g φ hφ
    show W (nS z * mS s * g) φ 0 = A.etaK s * (A.absK s : ℂ) * W g φ 0
    rw [hmul _ _ _ hφ, hmul _ _ _ hg, (hact _ (htest _ _ hg)).1 z 0, (hact _ hg).2.1 s 0, smul_zero,
      (nl_cont A).2]
    simp [Et.psiK]
  · intro hne hγ
    apply hne
    have hw : W (wS A.K) φ = 0 := funext fun y => by rw [(hact φ hφ).2.2 y, hγ, zero_mul]; rfl
    calc φ = W 1 φ := (hone φ hφ).symm
      _ = W ((wS A.K)⁻¹ * wS A.K) φ := by rw [inv_mul_cancel]
      _ = 0 := by rw [hmul _ _ _ hφ, hw, h0]

end GlobalTheory.WeilSmooth
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepEvalZeroMemInducedStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_evalZero_mem_induced : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L) (γ : ℂ) W, A.IsWeil ψ x A.etaK μ γ W → ∀ φ, IsTest φ → A.InI (fun g => W g φ 0) ∧ (φ ≠ 0 → γ ≠ 0) := by
  first | exact @GlobalTheory.WeilSmooth.jx_mem_induced | exact GlobalTheory.WeilSmooth.jx_mem_induced | (intros; apply GlobalTheory.WeilSmooth.jx_mem_induced <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransfer
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.RankOneTransfer

theorem inI_comb : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (Φ₁ Φ₂ : SpecialLinearGroup (Fin 2) A.K → ℂ) (r : ℂ), A.InI Φ₁ → A.InI Φ₂ →
    A.InI (fun g => Φ₁ g + r * Φ₂ g) := by
  intro F E _ _ _ _ A Φ₁ Φ₂ r h₁ h₂
  obtain ⟨⟨U₁, hU₁, i₁⟩, e₁⟩ := h₁
  obtain ⟨⟨U₂, hU₂, i₂⟩, e₂⟩ := h₂
  refine ⟨⟨U₁ ∩ U₂, Filter.inter_mem hU₁ hU₂, fun g k hk => ?_⟩, fun z s g => ?_⟩
  · simp only
    rw [i₁ g k (fun i j => (hk i j).1), i₂ g k (fun i j => (hk i j).2)]
  · simp only
    rw [e₁, e₂]
    ring

theorem inI_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E), A.InI (fun _ => 0) := by
  intro F E _ _ _ _ A
  exact ⟨⟨Set.univ, Filter.univ_mem, fun _ _ _ => rfl⟩, fun _ _ _ => by simp⟩

theorem nS_add {k : Type} [CommRing k] (a b : k) : nS (a + b) = nS a * nS b := by
  apply Subtype.ext
  show !![1, a + b; 0, 1] = !![1, a; 0, 1] * !![1, b; 0, 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]

theorem psi_cont {F : Type} [NormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have : ∀ᶠ x in 𝓝 x₀, ψ x₀ = ψ x := by
    filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    have h1 : ψ (x - x₀) = 1 := hψ.1 _ (by rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx.le)
    calc ψ x₀ = ψ x₀ * ψ (x - x₀) := by rw [h1, mul_one]
      _ = ψ (x₀ + (x - x₀)) := (AddChar.map_add_eq_mul ψ _ _).symm
      _ = ψ x := by congr 1; abel
  exact continuousAt_const.congr this

theorem lam_integrand_cont {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (a : A.K)
    (Φ : SpecialLinearGroup (Fin 2) A.K → ℂ) (hΦ : A.InI Φ) :
    Continuous fun z => Φ (wS A.K * nS z) * A.psiK ψ (-(a * z)) := by
  refine Continuous.mul ?_ ?_
  · obtain ⟨⟨U, hU, hinv⟩, -⟩ := hΦ
    refine continuous_iff_continuousAt.2 fun z₀ => ?_
    have hpre : {z : A.K | z - z₀ ∈ U} ∈ 𝓝 z₀ := by
      have ht : Tendsto (fun z : A.K => z - z₀) (𝓝 z₀) (𝓝 0) := by
        simpa using (continuous_id.sub continuous_const).tendsto z₀ (f := fun z : A.K => z - z₀)
      exact ht hU
    have h0 : (0 : A.K) ∈ U := mem_of_mem_nhds hU
    have : ∀ᶠ z in 𝓝 z₀, Φ (wS A.K * nS z₀) = Φ (wS A.K * nS z) := by
      filter_upwards [hpre] with z hz
      have hz' : z = z₀ + (z - z₀) := by abel
      rw [hz', nS_add, ← mul_assoc]
      symm
      apply hinv
      intro i j
      fin_cases i <;> fin_cases j <;> simp [nS, h0, hz]
    exact continuousAt_const.congr this
  · have htr : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact (psi_cont ψ hψ).comp (htr.comp (continuous_const.mul continuous_id).neg)

end GlobalTheory.JR.RankOneTransfer

namespace GlobalTheory.JR.RankOneTransfer

theorem lam_comb : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K),
    μK.IsAddHaarMeasure → ∀ (a : A.K) (Φ₁ Φ₂ : SpecialLinearGroup (Fin 2) A.K → ℂ) (r : ℂ), A.InI Φ₁ → A.InI Φ₂ →
    ∀ c : F, c ≠ 0 → A.abelian₂ μK ψ a (fun g => Φ₁ g + r * Φ₂ g) c = A.abelian₂ μK ψ a Φ₁ c + r * A.abelian₂ μK ψ a Φ₂ c := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ a Φ₁ Φ₂ r h₁ h₂ c hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hOKo, hOKc, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hsm : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hKc : IsCompact {z : A.K | c • z ∈ A.OK} := by
    have := (Homeomorph.smulOfNeZero c hc (α := A.K)).isCompact_preimage.2 hOKc
    exact this
  have hKm : MeasurableSet {z : A.K | c • z ∈ A.OK} := (hOKo.preimage hsm).measurableSet
  have i₁ : IntegrableOn (fun z => Φ₁ (wS A.K * nS z) * A.psiK ψ (-(a * z))) {z : A.K | c • z ∈ A.OK} μK :=
    (lam_integrand_cont A ψ hψ a Φ₁ h₁).continuousOn.integrableOn_compact' hKc hKm
  have i₂ : IntegrableOn (fun z => Φ₂ (wS A.K * nS z) * A.psiK ψ (-(a * z))) {z : A.K | c • z ∈ A.OK} μK :=
    (lam_integrand_cont A ψ hψ a Φ₂ h₂).continuousOn.integrableOn_compact' hKc hKm
  simp only [Et.abelian₂]
  rw [← integral_const_mul, ← integral_add i₁ (i₂.const_mul r)]
  congr 1
  funext z
  ring

end GlobalTheory.JR.RankOneTransfer

namespace GlobalTheory.JR.RankOneTransfer

theorem lam_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (μK : Measure A.K) (ψ : AddChar F ℂ) (a : A.K) (c : F),
    A.abelian₂ μK ψ a (fun _ => 0) c = 0 := by
  intro F E _ _ _ _ A μK ψ a c
  simp [Et.abelian₂]

end GlobalTheory.JR.RankOneTransfer

namespace GlobalTheory.JR.RankOneTransfer

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem inI_sum (A : Et F E) {ι : Type} (s : Finset ι) (r : ι → ℂ) (Φ : ι → SpecialLinearGroup (Fin 2) A.K → ℂ)
    (h : ∀ i ∈ s, A.InI (Φ i)) : A.InI (fun g => ∑ i ∈ s, r i * Φ i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inI_zero F E A
  | insert i s hi ih =>
    have := inI_comb F E A (fun g => ∑ j ∈ s, r j * Φ j g) (Φ i) (r i)
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) (h i (Finset.mem_insert_self i s))
    simpa [Finset.sum_insert hi, add_comm] using this

theorem lam_sum [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hμ : μK.IsAddHaarMeasure) (a : A.K) {ι : Type} (s : Finset ι) (r : ι → ℂ)
    (Φ : ι → SpecialLinearGroup (Fin 2) A.K → ℂ) (h : ∀ i ∈ s, A.InI (Φ i)) (c : F) (hc : c ≠ 0) :
    A.abelian₂ μK ψ a (fun g => ∑ i ∈ s, r i * Φ i g) c = ∑ i ∈ s, r i * A.abelian₂ μK ψ a (Φ i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lam_zero F E A μK ψ a c
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, A.InI (Φ j) := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have := lam_comb F E A ψ hψ μK hμ a (fun g => ∑ j ∈ s, r j * Φ j g) (Φ i) (r i)
      (inI_sum A s r Φ hs) (h i (Finset.mem_insert_self i s)) c hc
    rw [Finset.sum_insert hi, ← ih hs, add_comm, ← this]
    congr 1
    funext g
    rw [Finset.sum_insert hi, add_comm]

end GlobalTheory.JR.RankOneTransfer

namespace GlobalTheory.JR.RankOneTransfer

theorem rankOne : RankOne := by
  intro F E _ _ _ _ _ A ψ hψ m S hS γ W hW φ' φ κ hφ' hφ hmatch x hx y hy
  classical
  obtain ⟨-, -, -, -, -, -, -, hfin, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hSf := hfin S hS
  set Sf := hSf.toFinset with hSfdef
  have hmem : ∀ x', x' ∈ Sf ↔ x' ∈ S := fun x' => hSf.mem_toFinset
  have hμ : m.μK.IsAddHaarMeasure := m.sdK.1

  have huniq : ∀ (x₀ x₁ : A.Kˣ) (y₀ y₁ : A.L), x₀ ∈ S → x₁ ∈ S → IsUnit y₀ → IsUnit y₁ →
      (x₀ : A.K) * A.NL y₀ = x₁ * A.NL y₁ → x₀ = x₁ := by
    intro x₀ x₁ y₀ y₁ h₀ h₁ u₀ u₁ he
    have hu : IsUnit ((x₀ : A.K) * A.NL y₀) := x₀.isUnit.mul (u₀.map (Algebra.norm A.K))
    obtain ⟨z, -, hz⟩ := hS hu.unit
    have e0 := hz x₀ ⟨h₀, y₀, u₀, by simp⟩
    have e1 := hz x₁ ⟨h₁, y₁, u₁, by simp [he]⟩
    rw [e0, e1]
  let jx : A.Kˣ → SpecialLinearGroup (Fin 2) A.K → ℂ := fun x' g => W x' g (φ x') 0
  let φw : A.Kˣ → A.L → ℂ := fun x' => W x' (wS A.K) (φ x')
  let jw : A.Kˣ → SpecialLinearGroup (Fin 2) A.K → ℂ := fun x' g => W x' g (φw x') 0
  let r : A.Kˣ → ℂ := fun x' => -(γ x')⁻¹
  let Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ := fun g =>
    (∑ x' ∈ Sf, r x' * jx x' g) + κ * A.jHyp m.μK ψ φ' g
  have hφw : ∀ x' ∈ S, IsTest (φw x') := fun x' hx' => (hW x' hx').1.1 _ _ (hφ x' hx')
  have hjx : ∀ x' ∈ Sf, A.InI (jx x') := fun x' hx' =>
    (GlobalTheory.T.weilRep_evalZero_mem_induced F E A ψ hψ x' _ _ _ (hW x' ((hmem x').1 hx')) _ (hφ x' ((hmem x').1 hx'))).1
  have hjw : ∀ x' ∈ Sf, A.InI (jw x') := fun x' hx' =>
    (GlobalTheory.T.weilRep_evalZero_mem_induced F E A ψ hψ x' _ _ _ (hW x' ((hmem x').1 hx')) _ (hφw x' ((hmem x').1 hx'))).1
  have h14 := GlobalTheory.T.jHyp_mem_induced_fourier_weyl F E A ψ hψ m.μK m.sdK φ' hφ'
  have hF' : IsTest (A.fourK m.μK ψ φ') := GlobalTheory.T.fourierTransformKProd_locallyConstantCompactSupport F E A ψ hψ m.μK m.sdK φ' hφ'
  have h14F := GlobalTheory.T.jHyp_mem_induced_fourier_weyl F E A ψ hψ m.μK m.sdK _ hF'
  have hΨ : A.InI Ψ := inI_comb F E A _ _ κ (inI_sum A Sf r jx hjx) h14.1

  have hlim : ∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ m.μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0) := by
    intro a ha
    obtain ⟨x₀, ⟨hx₀, y₀, hy₀, ha₀⟩, -⟩ := hS ha.unit
    have ha₀' : a = x₀ * A.NL y₀ := by simpa using ha₀
    have hne : ∀ᶠ c in 𝓝[≠] (0 : F), c ≠ 0 := self_mem_nhdsWithin
    have h14b := GlobalTheory.T.truncatedWhittaker_jHyp_eq_orbitalIntegral F E A ψ hψ m.μK m.sdK φ' hφ' a ha
    have h15 : ∀ᶠ c in 𝓝[≠] (0 : F), ∀ x' ∈ Sf,
        A.abelian₂ m.μK ψ a (jx x') c = if x' = x₀ then γ x₀ * A.orbL m.ν (φ x₀) y₀ else 0 := by
      rw [Finset.eventually_all]
      intro x' hx'
      have hx'S := (hmem x').1 hx'
      have := GlobalTheory.T.truncatedWhittaker_weilRep_eventually F E A ψ hψ m x' _ _ (hW x' hx'S) _ (hφ x' hx'S) a ha
      by_cases hxx : x' = x₀
      · subst hxx
        simpa using this.1 y₀ hy₀ ha₀'
      · have hno : ¬ ∃ y' : A.L, IsUnit y' ∧ a = x' * A.NL y' := by
          rintro ⟨y', hy', he⟩
          exact hxx (huniq x' x₀ y' y₀ hx'S hx₀ hy' hy₀ (he.symm.trans ha₀'))
        simpa [hxx] using this.2 hno
    have hev : ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a Ψ c = 0 := by
      filter_upwards [hne, h14b, h15] with c hc e14 e15
      have hl := lam_comb F E A ψ hψ m.μK hμ a _ _ κ (inI_sum A Sf r jx hjx) h14.1 c hc
      rw [hl, lam_sum A ψ hψ m.μK hμ a Sf r jx hjx c hc, e14]
      rw [Finset.sum_congr rfl (fun x' hx' => by rw [e15 x' hx'])]
      have hx₀f : x₀ ∈ Sf := (hmem x₀).2 hx₀
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', hx₀f, if_true]
      have hm := hmatch x₀ hx₀ y₀ hy₀
      rw [← ha₀'] at hm
      rw [hm]
      by_cases hg : γ x₀ = 0
      · have h0 : φ x₀ = 0 := by
          by_contra hne0
          exact (GlobalTheory.T.weilRep_evalZero_mem_induced F E A ψ hψ x₀ _ _ _ (hW x₀ hx₀) _ (hφ x₀ hx₀)).2 hne0 hg
        simp [h0, Et.orbL]
      · simp only [r]
        field_simp
        ring
    exact tendsto_const_nhds.congr' (hev.mono fun c hc => hc.symm)
  have h13 := (GlobalTheory.T.kirillov_vanishing_of_limit F E A ψ hψ m.μK m.sdK Ψ hΨ hlim).2

  have hΨw : (fun h => Ψ (h * wS A.K)) = fun g => (∑ x' ∈ Sf, r x' * jw x' g) +
      κ * A.jHyp m.μK ψ (A.fourK m.μK ψ φ') g := by
    funext g
    simp only [Ψ]
    rw [h14.2 g]
    congr 1
    refine Finset.sum_congr rfl fun x' hx' => ?_
    have hx'S := (hmem x').1 hx'
    simp only [jx, jw, φw]
    rw [(hW x' hx'S).1.2.2.1 g (wS A.K) (φ x') (hφ x' hx'S)]
  set a := (x : A.K) * A.NL y with hadef
  have ha : IsUnit a := x.isUnit.mul (hy.map (Algebra.norm A.K))
  have hne : ∀ᶠ c in 𝓝[≠] (0 : F), c ≠ 0 := self_mem_nhdsWithin
  have h14b := GlobalTheory.T.truncatedWhittaker_jHyp_eq_orbitalIntegral F E A ψ hψ m.μK m.sdK _ hF' a ha
  have h15 : ∀ᶠ c in 𝓝[≠] (0 : F), ∀ x' ∈ Sf,
      A.abelian₂ m.μK ψ a (jw x') c = if x' = x then γ x * A.orbL m.ν (φw x) y else 0 := by
    rw [Finset.eventually_all]
    intro x' hx'
    have hx'S := (hmem x').1 hx'
    have := GlobalTheory.T.truncatedWhittaker_weilRep_eventually F E A ψ hψ m x' _ _ (hW x' hx'S) _ (hφw x' hx'S) a ha
    by_cases hxx : x' = x
    · subst hxx
      simpa using this.1 y hy rfl
    · have hno : ¬ ∃ y' : A.L, IsUnit y' ∧ a = x' * A.NL y' := by
        rintro ⟨y', hy', he⟩
        exact hxx (huniq x' x y' y hx'S hx hy' hy he.symm)
      simpa [hxx] using this.2 hno
  obtain ⟨c, hc, e14, e15⟩ := (hne.and (h14b.and h15)).exists
  have hz := h13 a c
  rw [hΨw, lam_comb F E A ψ hψ m.μK hμ a _ _ κ (inI_sum A Sf r jw hjw) h14F.1 c hc,
    lam_sum A ψ hψ m.μK hμ a Sf r jw hjw c hc, e14,
    Finset.sum_congr rfl (fun x' hx' => by rw [e15 x' hx'])] at hz
  have hxf : x ∈ Sf := (hmem x).2 hx
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', hxf, if_true] at hz
  have horb : A.orbL m.ν (φw x) y = γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y := by
    simp only [Et.orbL, φw]
    rw [← integral_const_mul]
    congr 1
    funext t
    exact ((hW x hx).2 (φ x) (hφ x hx)).2.2 _
  rw [horb] at hz
  simp only [r] at hz
  by_cases hg : γ x = 0
  · simp [hg] at hz
    simp [hg, hz]
  · field_simp at hz
    linear_combination hz

end GlobalTheory.JR.RankOneTransfer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransferStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer : RankOne := by
  first | exact @GlobalTheory.JR.RankOneTransfer.rankOne | exact GlobalTheory.JR.RankOneTransfer.rankOne | (intros; apply GlobalTheory.JR.RankOneTransfer.rankOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchingOfWeilField
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatch_of_weilField : WeilField → ∀ r, FourierMatch r := fun h =>
  GlobalTheory.T.jacquetRallisFourierMatch_of_weilRepresentation (GlobalTheory.T.weilRepresentationEtale_of_quadraticField h) GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer GlobalTheory.T.weilConstantStandardHermitian_eq_one

end GlobalTheory.JR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchingOfWeilFieldStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field : WeilField → ∀ r, FourierMatch r := by
  first | exact @GlobalTheory.JR.fourierMatch_of_weilField | exact GlobalTheory.JR.fourierMatch_of_weilField | (intros; apply GlobalTheory.JR.fourierMatch_of_weilField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SizeOne

theorem eta_one' {F : Type} [NormedField F] : eta (1 : F) = 1 := by
  unfold eta
  rw [if_pos ⟨1, by simp⟩]

theorem unitMatch_zero : UnitMatch 0 := by
  intro F E _ _ _ _ _ M a _
  letI := M.mG; letI := M.mU
  have hG : M.μG Set.univ = 1 := by
    rw [← M.volG]; congr 1; ext g; simp [glO]
  have hU : M.μU Set.univ = 1 := by
    rw [← M.volU]; congr 1; ext g; simp [uO]
  have hw : ∀ Y : Gl 0 F, omega Y = 1 := by
    intro Y
    have : lastDet Y = 1 := by simp [lastDet, Fin.last]
    rw [omega, this, eta_one']
  refine ⟨fun X hX => ?_, fun hn => (hn ⟨(0, 0, a.2.2), ?_⟩).elim⟩
  · have hl : X.2.2 = a.2.2 := (algebraMap F E).injective (congrArg (fun t => t.2.2) hX)
    by_cases hb : ‖a.2.2‖ ≤ 1 <;>
      simp [orbG, orbU, hw, unitG, unitU, act, actU, sec, Set.indicator, hl, hb, Measure.real, hG, hU]
  · exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)

end GlobalTheory.JR.SizeOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOneStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_sizeOne : UnitMatch 0 := by
  first | exact @GlobalTheory.JR.SizeOne.unitMatch_zero | exact GlobalTheory.JR.SizeOne.unitMatch_zero | (intros; apply GlobalTheory.JR.SizeOne.unitMatch_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadratic
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_of_weilField : WeilField → ∀ r, UnitMatch r := by
  intro hW r
  induction r with
  | zero => exact GlobalTheory.T.jacquetRallisUnitMatch_sizeOne
  | succ r ih => exact GlobalTheory.T.jacquetRallisUnitMatch_succ (GlobalTheory.T.weilRepresentationEtale_of_quadraticField hW) GlobalTheory.T.weilConstantStandardHermitian_eq_one r (GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field hW (r + 1)) ih

end GlobalTheory.JR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadraticStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic : WeilField → ∀ r, UnitMatch r := by
  first | exact @GlobalTheory.JR.unitMatch_of_weilField | exact GlobalTheory.JR.unitMatch_of_weilField | (intros; apply GlobalTheory.JR.unitMatch_of_weilField <;> assumption)
end
