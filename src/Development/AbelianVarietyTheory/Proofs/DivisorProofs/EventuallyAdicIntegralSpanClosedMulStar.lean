module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarSectionLift
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicCoeffDenominatorBoundOfBoundedRoots

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem rat_mem_adicCompletionIntegers_eventually (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite,
      algebraMap ℚ (v.adicCompletion ℚ) x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal ℤ) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_le ?_
  have h1 : w.valuation ℚ (algebraMap ℤ ℚ b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

section

variable {C : Type} [Ring C] [Algebra ℚ C] {κ : Type} (b : Module.Basis κ ℚ C) (v : HeightOneSpectrum ℤ)

theorem repr_tmul_apply (a : v.adicCompletion ℚ) (x : C) (k : κ) :
    (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr (a ⊗ₜ[ℚ] x) k =
      a * algebraMap ℚ (v.adicCompletion ℚ) (b.repr x k) := by
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]

theorem eq_sum_tmul [Fintype κ] (y : v.adicCompletion ℚ ⊗[ℚ] C) :
    y = ∑ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ⊗ₜ[ℚ] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end

theorem isIntB_mul_star_eventually : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (σ : C →+* Cᵐᵒᵖ) (κ : Type)
    (b : Module.Basis κ ℚ C), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) ∧
      (∀ y, IsIntB v b y → IsIntB v b (starT σ (v.adicCompletion ℚ) y).unop) := by
  intro C _ _ _ σ κ b
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (σ (b t.1)).unop t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (hc.and hs)
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨hcv, hsv⟩ := hv
  refine ⟨fun y z hy hz k => ?_, fun y hy k => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · have hu : ∀ (f : κ → (v.adicCompletion ℚ ⊗[ℚ] C)ᵐᵒᵖ), (∑ i, f i).unop = ∑ i, (f i).unop :=
      fun f => map_sum (MulOpposite.opAddEquiv : v.adicCompletion ℚ ⊗[ℚ] C ≃+ _).symm f Finset.univ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul b v y, map_sum, hu, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    rw [starT_tmul, repr_tmul_apply]
    exact mul_mem (hy i) (hsv (i, k))

end GlobalTheory.AdicSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStarStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_adic_integral_span_closed_mul_star : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (σ : C →+* Cᵐᵒᵖ) (κ : Type)
    (b : Module.Basis κ ℚ C), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) ∧
      (∀ y, IsIntB v b y → IsIntB v b (starT σ (v.adicCompletion ℚ) y).unop) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_mul_star_eventually) | (exact GlobalTheory.AdicSpan.isIntB_mul_star_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_mul_star_eventually  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapBridge

theorem heckeChoiceClauses_of_weakCharacterisation_at_face : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ R.toRealDat.tup_mu_off ∧ R.toRealDat.tup_mu_used := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hC hE
  have h := RealDat3.characterisation_of_weak hC hE
  exact ⟨⟨h.lev, h.grp, h.fam, h.models, h.chain, h.thP⟩, h.tup.mu_off, h.tup.mu_used⟩

end GlobalTheory.OneMapBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAlStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hk3Core_and_tup_mu_of_weakCharacterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ R.toRealDat.tup_mu_off ∧ R.toRealDat.tup_mu_used := by
  first | exact @GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face | exact GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face | (intros; apply GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunction
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory.ThetaBox

theorem thetaSum_boxFun : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  intro F _ _ κ κ' _ _ φ₁ h₁ φ₂ h₂
  have s₁ := (thetaSum_summable_linear F κ).2.1 φ₁ h₁
  have s₂ := (thetaSum_summable_linear F κ').2.1 φ₂ h₂
  unfold thetaSum
  rw [tsum_mul_tsum_of_summable_norm s₁ s₂]
  rw [← (Equiv.sumArrowEquivProdArrow κ κ' F).symm.tsum_eq]
  rfl

end GlobalTheory.ThetaBox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunctionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicThetaDistributionSum_productFunction : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  first | exact @GlobalTheory.ThetaBox.thetaSum_boxFun | exact GlobalTheory.ThetaBox.thetaSum_boxFun | (intros; apply GlobalTheory.ThetaBox.thetaSum_boxFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHaarMeasureScaling
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

theorem herm_laws : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ), sh G β = β →
    (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → (herm G v β).IsHermitian ∧ (herm G v β).det ≠ 0 ∧
      ∃ Z : GL (Fin G.n) ℂ, herm G v β =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  intro p _ G v β _ hR
  obtain ⟨z, hz⟩ := hR
  have hc : ∃ Z : GL (Fin G.n) ℂ, herm G v β =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
    set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
    change G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
    have hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C) := by
      change G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _
      rw [psiR_tmul, one_smul]
    have h1 := congrArg (G.psiR v) hz
    rw [map_mul, map_mul, psiR_starT, hb] at h1
    simp only [Units.val_one, map_one] at h1
    rw [← hZm] at h1
    have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
    set M := G.psi v ((β⁻¹ : G.Cˣ) : G.C)
    have hMb : M * G.psi v (β : G.C) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
      have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
        Zm * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
      simpa [Matrix.mul_assoc] using this
    have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
      calc M = M * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
    rw [h3]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
  obtain ⟨Z, hZ⟩ := hc
  refine ⟨?_, ?_, Z, hZ⟩
  · rw [hZ]
    exact isHermitian_conjTranspose_mul_mul _ (G.gram_herm v)
  · rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    have hZd : (Z : Matrix (Fin G.n) (Fin G.n) ℂ).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse
      (show ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) * Z = 1 by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one])).ne_zero
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hZd) (G.gram_det v)) hZd

end GlobalTheory.LKCx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairsSameSimilitude
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem grp_factor_eq_of_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y y₀ : grp G β) (c : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    (y : G.Cˣ × ℚˣ).2 = (y₀ : G.Cˣ × ℚˣ).2 := by
  intro p _ G β y y₀ c hyc
  haveI : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C
  haveI : Nontrivial G.C := inferInstance
  set d : G.C → ℚ := fun a => LinearMap.det (LinearMap.mulLeft ℚ a) with hd
  have dmul : ∀ a b, d (a * b) = d a * d b := by
    intro a b; simp only [hd, LinearMap.mulLeft_mul, LinearMap.det_comp]
  have done : d 1 = 1 := by simp [hd, LinearMap.mulLeft_one]
  have dsc : ∀ s : ℚ, d (algebraMap ℚ G.C s) = s ^ Module.finrank ℚ G.C := by
    intro s
    have : LinearMap.mulLeft ℚ (algebraMap ℚ G.C s) = s • LinearMap.id := by
      ext x; simp [Algebra.smul_def]
    simp only [hd, this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have dunit : ∀ u : G.Cˣ, d (u : G.C) * d ((u⁻¹ : G.Cˣ) : G.C) = 1 := by
    intro u; rw [← dmul, Units.mul_inv, done]
  have shmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have shone : sh G 1 = 1 := by simp [sh]
  have dsh_conj : d (sh G (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C))) =
      d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
    have e : d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C)) = 1 := by
      rw [← dmul, ← shmul, Units.mul_inv, shone, done]
    rw [shmul, shmul, dmul, dmul]
    calc d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * (d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * d (sh G (c : G.C)))
        = d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
          (d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C))) := by ring
      _ = _ := by rw [e, mul_one]
  have d_conj : d (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C)) =
      d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
    rw [dmul, dmul]
    calc d (c : G.C) * d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * d ((c⁻¹ : G.Cˣ) : G.C)
        = d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * (d (c : G.C) * d ((c⁻¹ : G.Cˣ) : G.C)) := by ring
      _ = _ := by rw [dunit, mul_one]
  obtain ⟨hy, hs⟩ := y.2
  obtain ⟨hy₀, hs₀⟩ := y₀.2
  have ey := congrArg d hy
  have ey₀ := congrArg d hy₀
  rw [dmul, dmul, dmul, dsc] at ey ey₀
  rw [hyc, d_conj, dsh_conj, ey₀] at ey
  have hβ : d (β : G.C) ≠ 0 := by
    intro h; have := dunit β; rw [h, zero_mul] at this; exact zero_ne_one this
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  have hpow : ((y : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C = ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C :=
    (mul_right_cancel₀ hβ ey).symm
  exact Units.ext ((pow_left_inj₀ hs.le hs₀.le hN).1 hpow)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistedUnitCommutes
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem unit_conj_form_props {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β Y c : G.Cˣ) (s : ℚ) (hβ : sh G β = β)
    (h0 : (Y : G.C) * β * sh G Y = algebraMap ℚ G.C s * β)
    (h1 : ((c : G.C) * Y * ((c⁻¹ : G.Cˣ) : G.C)) * β * sh G ((c : G.C) * Y * ((c⁻¹ : G.Cˣ) : G.C)) =
      algebraMap ℚ G.C s * β) :
    IsUnit (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) ∧
    Commute (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) (Y : G.C) ∧
    (β : G.C) * sh G (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
      ((β⁻¹ : G.Cˣ) : G.C) = ((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := by
  have shm : ∀ x z : G.C, sh G (x * z) = sh G z * sh G x := fun x z => by simp [sh]
  have shs : ∀ x : G.C, sh G (sh G x) = x := G.star_star
  have sh1 : sh G 1 = 1 := sh_one_eq G
  set u : G.C := ((c⁻¹ : G.Cˣ) : G.C) with hu
  set bi : G.C := ((β⁻¹ : G.Cˣ) : G.C) with hbi_def
  set S : G.C := algebraMap ℚ G.C s with hS
  have hA : ∀ r : G.C, u * ((c : G.C) * r) = r := fun r => by rw [← mul_assoc, hu, Units.inv_mul, one_mul]
  have hB : sh G (c : G.C) * sh G u = 1 := by rw [← shm, hu, Units.inv_mul, sh1]
  have hB' : ∀ r : G.C, sh G (c : G.C) * (sh G u * r) = r := fun r => by rw [← mul_assoc, hB, one_mul]
  have hC : ∀ r : G.C, (β : G.C) * (bi * r) = r := fun r => by rw [← mul_assoc, hbi_def, Units.mul_inv, one_mul]
  have hC' : ∀ r : G.C, bi * ((β : G.C) * r) = r := fun r => by rw [← mul_assoc, hbi_def, Units.inv_mul, one_mul]
  have hD : (β : G.C) * bi = 1 := by rw [hbi_def, Units.mul_inv]
  set shYi : G.C := sh G ((Y⁻¹ : G.Cˣ) : G.C) with hshYi
  have hE : ∀ r : G.C, sh G (Y : G.C) * (shYi * r) = r := fun r => by
    rw [← mul_assoc, hshYi, ← shm, Units.inv_mul, sh1, one_mul]
  have hE1 : sh G (Y : G.C) * shYi = 1 := by rw [hshYi, ← shm, Units.inv_mul, sh1]
  refine ⟨?_, ?_, ?_⟩
  · have hshu : IsUnit (sh G u) := ⟨⟨sh G u, sh G (c : G.C), by rw [← shm, hu, Units.mul_inv, sh1], hB⟩, rfl⟩
    exact (((Units.isUnit _).mul (Units.isUnit β)).mul hshu).mul (Units.isUnit _)
  · have h2 : (Y : G.C) * (u * β * sh G u) * sh G Y = S * (u * β * sh G u) := by
      calc (Y : G.C) * (u * β * sh G u) * sh G Y
          = u * (((c : G.C) * Y * u) * β * sh G ((c : G.C) * Y * u)) * sh G u := by
            simp only [shm, mul_assoc, hA, hB, hB', mul_one]
        _ = S * (u * β * sh G u) := by
            rw [h1, hS, ← mul_assoc, ← Algebra.commutes s u]; simp only [mul_assoc]
    have e1 : (Y : G.C) * (u * β * sh G u * bi) = S * ((u * β * sh G u) * (shYi * bi)) := by
      calc (Y : G.C) * (u * β * sh G u * bi) = ((Y : G.C) * (u * β * sh G u) * sh G Y) * (shYi * bi) := by
            simp only [mul_assoc, hE]
        _ = _ := by rw [h2, mul_assoc]
    have eY : (Y : G.C) = S * ((β : G.C) * (shYi * bi)) := by
      calc (Y : G.C) = ((Y : G.C) * β * sh G Y) * (shYi * bi) := by
            simp only [mul_assoc, hE, hD, mul_one]
        _ = _ := by rw [h0, mul_assoc]
    have e2 : (u * β * sh G u * bi) * (Y : G.C) = S * ((u * β * sh G u) * (shYi * bi)) := by
      rw [eY]
      calc u * β * sh G u * bi * (S * ((β : G.C) * (shYi * bi)))
          = (u * β * sh G u) * (bi * S * ((β : G.C) * (shYi * bi))) := by simp only [mul_assoc]
        _ = (u * β * sh G u) * (S * (bi * ((β : G.C) * (shYi * bi)))) := by
            rw [hS, ← Algebra.commutes s bi]; simp only [mul_assoc]
        _ = _ := by rw [hC', ← mul_assoc, ← mul_assoc, ← Algebra.commutes s, hS]; simp only [mul_assoc]
    exact e2.trans e1.symm
  · have hbi : sh G bi = bi := by
      have h3 : sh G (β : G.C) * sh G bi = 1 := by rw [← shm, hbi_def, Units.inv_mul, sh1]
      rw [hβ] at h3
      calc sh G bi = (bi * β) * sh G bi := by rw [hbi_def, Units.inv_mul, one_mul]
        _ = bi := by rw [mul_assoc, h3, mul_one]
    simp only [shm, shs, hβ, hbi, mul_assoc, hC]

theorem grp_conj_unit_props : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y y₀ : grp G β) (c : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    (y : G.Cˣ × ℚˣ).2 = (y₀ : G.Cˣ × ℚˣ).2 →
    IsUnit (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ Commute (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧
    (β : G.C) * sh G (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * ((β⁻¹ : G.Cˣ) : G.C) = (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β hβ y y₀ c hy hs
  have h0 : (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) * β := y₀.2.1
  have h1 : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C ((y : G.Cˣ × ℚˣ).2 : ℚ) * β := y.2.1
  rw [hy, hs] at h1
  exact unit_conj_form_props G β _ c _ hβ h0 h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegral
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic TopologicalSpace

theorem res_res_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom x) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem mul_compat {X : Scheme.{0}} {A₁ A₂ B₁ B₂ : X.Opens} (s₁ : Γ(X, A₁)) (s₂ : Γ(X, A₂))
    (t₁ : Γ(X, B₁)) (t₂ : Γ(X, B₂)) (gA : Γ(X, A₁ ⊓ A₂)ˣ) (gB : Γ(X, B₁ ⊓ B₂)ˣ)
    (hs : (X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ A₂ ≤ A₁)).op).hom s₁ =
      (gA : Γ(X, A₁ ⊓ A₂)) * (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ A₂ ≤ A₂)).op).hom s₂)
    (ht : (X.presheaf.map (homOfLE (inf_le_left : B₁ ⊓ B₂ ≤ B₁)).op).hom t₁ =
      (gB : Γ(X, B₁ ⊓ B₂)) * (X.presheaf.map (homOfLE (inf_le_right : B₁ ⊓ B₂ ≤ B₂)).op).hom t₂) :
    (X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ B₁)).op).hom
        ((X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ B₁ ≤ A₁)).op).hom s₁ *
          (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ B₁ ≤ B₁)).op).hom t₁) =
      ((res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ A₂) gA *
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ B₁ ⊓ B₂) gB : Γ(X, A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂))ˣ) : Γ(X, A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂))) *
      (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₂ ⊓ B₂)).op).hom
        ((X.presheaf.map (homOfLE (inf_le_left : A₂ ⊓ B₂ ≤ A₂)).op).hom s₂ *
          (X.presheaf.map (homOfLE (inf_le_right : A₂ ⊓ B₂ ≤ B₂)).op).hom t₂) := by
  have hσ := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans inf_le_left) : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ A₂)).op).hom hs
  have hτ := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
    (inf_le_right.trans inf_le_right) : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ B₁ ⊓ B₂)).op).hom ht
  rw [res_res_apply, map_mul, res_res_apply] at hσ hτ
  simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul, res_res_apply]
  rw [hσ, hτ]
  ring

def tensSec {X : Scheme.{0}} {A B : LB X} (σ : LB.Sec A) (τ : LB.Sec B) : LB.Sec (tens A B) where
  f p := (X.presheaf.map (homOfLE (inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ A.U p.1)).op).hom (σ.f p.1) *
    (X.presheaf.map (homOfLE (inf_le_right : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2)).op).hom (τ.f p.2)
  compat p q := mul_compat _ _ _ _ _ _ (σ.compat p.1 q.1) (τ.compat p.2 q.2)

theorem germ_sec_ne_zero {X : Scheme.{0}} [IsIntegral X] {N : LB X} (σ : LB.Sec N) {j : N.ι}
    (hj : σ.f j ≠ 0) (i : N.ι) (y : X) (hy : y ∈ N.U i) : X.presheaf.germ (N.U i) y hy (σ.f i) ≠ 0 := by
  intro h0
  have hi0 : σ.f i = 0 := germ_injective_of_isIntegral X y hy (by rw [h0, map_zero])
  apply hj
  by_cases hne : (N.U j : Set X).Nonempty
  · obtain ⟨z, hz⟩ := hne
    obtain ⟨w, hwi, hwj⟩ :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen ⟨y, hy⟩ ⟨z, hz⟩
    apply germ_injective_of_isIntegral X w hwj
    rw [map_zero]
    have hw : w ∈ N.U i ⊓ N.U j := ⟨hwi, hwj⟩
    have e := congrArg (X.presheaf.germ (N.U i ⊓ N.U j) w hw) (σ.compat i j)
    rw [X.presheaf.germ_res_apply, hi0, map_zero, map_mul, X.presheaf.germ_res_apply] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact absurd h (((N.g i j).isUnit.map (X.presheaf.germ (N.U i ⊓ N.U j) w hw).hom).ne_zero)
    · exact h
  · have hT : N.U j = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨x, hx⟩
    haveI : Subsingleton Γ(X, N.U j) := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hT)
    exact Subsingleton.elim _ _

theorem eff_add {X : Scheme.{0}} [IsIntegral X] (a b : Pic X) (ha : Eff a) (hb : Eff b) : Eff (a + b) := by
  obtain ⟨A, hA, rfl, σ, j, hσ⟩ := ha
  obtain ⟨B, hB, rfl, τ, k, hτ⟩ := hb
  obtain ⟨y⟩ := (inferInstance : Nonempty X)
  have hyA : y ∈ ⨆ i, A.U i := hA.cover ▸ trivial
  have hyB : y ∈ ⨆ i, B.U i := hB.cover ▸ trivial
  obtain ⟨p, hp⟩ := Opens.mem_iSup.1 hyA
  obtain ⟨q, hq⟩ := Opens.mem_iSup.1 hyB
  refine ⟨tens A B, isLB_tens hA hB, cls_tens hA hB _, tensSec σ τ, (p, q), ?_⟩
  have hy : y ∈ A.U p ⊓ B.U q := ⟨hp, hq⟩
  intro h0
  have h0' : (X.presheaf.map (homOfLE (inf_le_left : A.U p ⊓ B.U q ≤ A.U p)).op).hom (σ.f p) *
      (X.presheaf.map (homOfLE (inf_le_right : A.U p ⊓ B.U q ≤ B.U q)).op).hom (τ.f q) = 0 := h0
  have e' := congrArg (X.presheaf.germ (A.U p ⊓ B.U q) y hy) h0'
  rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, map_zero] at e'
  rcases mul_eq_zero.mp e' with h | h
  · exact germ_sec_ne_zero σ hσ p y hp h
  · exact germ_sec_ne_zero τ hτ q y hq h

end GlobalTheory.EffBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegralStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEffectivePicClass_add_integral : ∀ {X : Scheme.{0}} [IsIntegral X] (a b : GlobalTheory.CechPic.Pic X), GlobalTheory.EffBound.Eff a → GlobalTheory.EffBound.Eff b → GlobalTheory.EffBound.Eff (a + b) := by
  first | exact @GlobalTheory.EffBound.eff_add | exact GlobalTheory.EffBound.eff_add | (intros; apply GlobalTheory.EffBound.eff_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinWeilO

open GlobalTheory.SplitScalar GlobalTheory.FinWeil GlobalTheory.WeilParts

theorem relIndex_ne_zero_of_finite {G Y : Type} [AddCommGroup G] (H K : AddSubgroup G) {R : Set Y} (hR : R.Finite)
    (rel : G → Y → Prop) (h1 : ∀ k ∈ K, ∃ r ∈ R, rel k r) (h2 : ∀ k k' r, rel k r → rel k' r → k - k' ∈ H) :
    H.relIndex K ≠ 0 := by
  haveI := hR.to_subtype
  choose f hf hf' using h1
  haveI : Finite (K ⧸ H.addSubgroupOf K) := by
    refine Finite.of_injective (fun q => (⟨f _ (Quotient.out q : K).2, hf _ _⟩ : R)) fun q q' h => ?_
    have h3 : f _ (Quotient.out q : K).2 = f _ (Quotient.out q' : K).2 := congrArg Subtype.val h
    have h4 := h2 _ _ _ (hf' _ (Quotient.out q : K).2) (h3 ▸ hf' _ (Quotient.out q' : K).2)
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_iff_sub_mem]
    exact h4
  exact AddSubgroup.index_ne_zero_of_finite

theorem exists_extend {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (Om : Γ →* Module.End ℂ M) : ∃ om : Γ →* Module.End ℂ V, ∀ p (m : M), om p m = Om p m := by
  obtain ⟨C, hC⟩ := M.exists_isCompl
  let e := M.prodEquivOfIsCompl C hC
  refine ⟨{ toFun := fun p => e.conj ((Om p).prodMap LinearMap.id), map_one' := ?_, map_mul' := fun p q => ?_ }, ?_⟩
  · rw [map_one]
    exact (congrArg e.conj LinearMap.prodMap_id).trans e.conj_id
  · rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← e.conj_comp, LinearMap.prodMap_comp,
      LinearMap.id_comp]
  · intro p m
    show e (((Om p).prodMap LinearMap.id) (e.symm m)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp [e]

section Abstract

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
  {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

theorem normOp_of_le (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B) (hle : B ≤ A)
    {e : M} (he : Fixes W A e) : normOp lam W A B e = e := by
  obtain ⟨h1, h2⟩ := (sumOp_transversal h A B hB).2.2 hle
  rw [normOp, h1, h2 e he, map_one, inv_one, one_smul]

theorem normOp_comm (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B) (hi : idx A B ≠ 0)
    (L : M →ₗ[ℂ] M) (hL : ∀ x v, L (W x v) = W x (L v)) {e : M} (he : Fixes W A e) :
    normOp lam W A B (L e) = L (normOp lam W A B e) := by
  obtain ⟨n, f, hf, hu⟩ := ((sumOp_transversal h A B hB).2.1 hi).1
  have he' : Fixes W A (L e) := fun a ha => by rw [← hL, he a ha]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [normOp, normOp, ((sumOp_transversal h A B hB).1 _ he' _ f hf hu).1,
    ((sumOp_transversal h A B hB).1 _ he _ f hf hu).1, map_smul, map_sum]
  simp only [hL]

end Abstract

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
  {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idx_latF_ne_zero {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (B : Submodule (𝓞 D.host.E) (XF S T)) {N : ℕ} (hN : 0 < N) (hB : ∀ b ∈ B, N • b ∈ latF S T ΛS ΛT) :
    idx (latF S T ΛS ΛT) B ≠ 0 := by
  obtain ⟨R, hR, h⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True) N hN
  refine relIndex_ne_zero_of_finite _ _ hR
    (fun b r => ∃ u ∈ latO S T ΛS ΛT fun _ => True, N • (b : WO S T) = r + N • u) (fun b hb => h _ (hB b hb)) ?_
  rintro b b' r ⟨u, hu, h1⟩ ⟨u', hu', h2⟩
  have h3 : N • ((b : WO S T) - b') = N • (u - u') := by
    rw [nsmul_sub, nsmul_sub, h1, h2, add_sub_add_left_eq_sub]
  have h4 : (b : WO S T) - b' = u - u' := by
    rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hN ((b : WO S T) - b'), h3, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN]
  show (b : WO S T) - b' ∈ latO S T ΛS ΛT fun _ => True
  rw [h4]
  exact sub_mem hu hu'

theorem idx_latF_eq (B : Submodule (𝓞 D.host.E) (XF S T)) :
    idx (latF S T LS LT) B = (latO S T LS LT fun _ => True).relIndex (B.toAddSubgroup.map (XF.incl S T)) :=
  AddSubgroup.relIndex_comap (latO S T LS LT fun _ => True) (XF.incl S T) B.toAddSubgroup

theorem phase_two (hA : SelfDual (gamF ψ S T) (latF S T LS LT)) (w : 𝓞 D.host.E) {u : XF S T}
    (hu : u ∈ latF S T LS LT) : phase ψ w (2 • u) = 1 := by
  have h : ψ (symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u) = 1 :=
    (hA _).1 ((latF S T LS LT).smul_mem w (nsmul_mem hu 2)) u hu
  have h2 := AddChar.map_add_eq_mul ψ (-symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u)
    (symplO S T (intA D w • ((2 • u : XF S T) : WO S T)) u)
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at h2
  rw [phase, h2]
  congr 2
  rw [← symplOH_add_self, ← symplOH_add_right, XF.coe_nsmul, two_nsmul]

theorem phase_half {e : AE D} (he : IsSplitIdem D e) (w : 𝓞 D.host.E) {u : XF S T} (hu : IsHalf e (u : WO S T)) :
    phase ψ w u = 1 := by
  have h : IsHalf e (intA D w • (u : WO S T)) := by
    rw [isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  rw [phase, symplOH, half_orth he h hu, mul_zero, neg_zero, AddChar.map_zero_eq_one]

theorem real_smul_mt {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) :
    realIdem D • mt V g = realIdem D • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : (mt V g).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub]
  refine Matrix.ext fun i j => realIdem_mul_of_fin ?_
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (infPart D) (infPart D).map_zero (infPart D).map_one]
  rfl

theorem fin_smul_mt {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) :
    (1 - realIdem D) • mt V g = (1 - realIdem D) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : (mt V g).map (finPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero]
  refine Matrix.ext fun i j => (realIdem_mul_of_real ?_).symm
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (finPart D) (finPart D).map_zero (finPart D).map_one]
  rfl

theorem rhoF_real {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) (x : XF S T) :
    rhoF S T (g, h) x = x := by
  have h1 : ∀ y : XF S T, (1 - realIdem D) • (y : WO S T) = y := fun y => by
    rw [sub_smul, one_smul, mem_finSub_iff.1 y.fin, sub_zero]
  apply XF.ext
  rw [← h1 (rhoF S T (g, h) x), coe_rhoF, smul_actO (fin_smul_mt hg) (fin_smul_mt hh), h1]

theorem real_smul_real (u : WO S T) : (realIdem D • u).map (finPart D) = 0 := by
  funext i j
  show finPart D (realIdem D * u i j) = 0
  rw [RingHom.map_mul, finPart_realIdem, zero_mul]

theorem fin_smul_fin (u : WO S T) : ((1 - realIdem D) • u).map (infPart D) = 0 := by
  funext i j
  show infPart D ((1 - realIdem D) * u i j) = 0
  rw [RingHom.map_mul, RingHom.map_sub, infPart_realIdem, RingHom.map_one, sub_self, zero_mul]

theorem off_smul_mt_place {V : HSp D} {η : AF D.host.F} {g : GA D V} (hg : SuppPl η V g) :
    (1 - algebraMap (AF D.host.F) (AE D) η) • mt V g =
      (1 - algebraMap (AF D.host.F) (AE D) η) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have h : algebraMap (AF D.host.F) (AE D) η • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, h, sub_self]

theorem cA_algebraMap (η : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) η) = algebraMap (AF D.host.F) (AE D) η := by
  show η ⊗ₜ[D.host.F] D.sp.cm.sig (1 : D.host.E) = _
  rw [map_one]; rfl

theorem exists_half_of_nonSplit {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : NonSplitAt D v η) :
    ∃ a : AE D, finPart D a ∈ intAE D ∧ 2 * a = algebraMap (AF D.host.F) (AE D) η := by
  obtain ⟨⟨α, rfl, h1, h0⟩, hn⟩ := h
  have hα : α = singleV D.host.F v 1 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h1, GlobalTheory.SplitIdem.evalV_singleV_same]
    · rw [h0 w hw, GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw]
  have h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal := fun h2 => by
    obtain ⟨e, e1, e2, e3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    rw [← hα] at e3
    exact hn ⟨e, ⟨e1, e2, v, _, ⟨α, rfl, h1, h0⟩, e3⟩, e3⟩
  obtain ⟨y, hy⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v 2).2 h2).exists_right_inv
  rw [map_ofNat] at hy
  have hy' : (2 : Fv D.host.F v) * y = 1 := congrArg Subtype.val hy
  refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v y), ?_, ?_⟩
  · exact AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v y, 1, rfl⟩
  · rw [two_mul, ← map_add (f := _), ← map_add (f := _), ← two_mul, hy', hα]
    rfl

theorem finPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : IsPlaceIdem D v η) :
    finPart D (algebraMap (AF D.host.F) (AE D) η) ∈ intAE D := by
  obtain ⟨β, rfl, h1, h0⟩ := h
  refine AddSubgroup.subset_closure ⟨β, fun w => ?_, 1, rfl⟩
  by_cases hw : w = v
  · subst hw; rw [h1]; exact one_mem _
  · rw [h0 w hw]; exact zero_mem _

theorem smooth_theta (hψ : IsCharAF D.host.F ψ) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {w : 𝓞 D.host.E} (hw : w + sgO D w = 1) (hA : SelfDual (gamF ψ S T) (latF S T ΛS ΛT))
    (hlev : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧
      ∀ u ∈ latO S T ΛS ΛT fun _ => True, N • u ∈ U) (f : thetaSub ψ S T) :
    ∃ B : Submodule (𝓞 D.host.E) (XF S T), idx (latF S T ΛS ΛT) B ≠ 0 ∧
      ∀ a ∈ latF S T ΛS ΛT, (∀ t ∈ B, gamF ψ S T a t = 1) → opF hψ S T w a f = f := by
  have H := isHeis_opF hψ S T hw
  obtain ⟨U, hU, hf⟩ := f.2.level
  obtain ⟨N, hN, hNU⟩ := hlev U hU
  have hN2 : 0 < 2 * N := by omega
  have hdiv : ∀ x : XF S T, (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • x) = x := fun x => by
    apply XF.ext
    show (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • (x : WO S T)) = x
    rw [smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN2]
  refine ⟨(latF S T ΛS ΛT).comap ((2 * N) • LinearMap.id), idx_latF_ne_zero hS hT _ hN2 fun b hb => hb,
    fun a _ ha => ?_⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = (2 * N) • a' := ⟨_, (hdiv a).symm⟩
  have ha' : a' ∈ latF S T ΛS ΛT := (hA a').2 fun t ht => by
    rw [← hdiv t, H.nsmul_right, ← H.nsmul_left]
    refine ha _ ?_
    show (2 * N) • (incA D ((2 * N : ℕ) : D.host.E)⁻¹ • t) ∈ latF S T ΛS ΛT
    rw [hdiv]
    exact ht
  apply Subtype.ext
  rw [coe_opF, hf _ (by rw [XF.coe_nsmul, mul_comm, mul_smul]; exact hNU _ (nsmul_mem ha' 2)) (XF.fin _),
    mul_smul, phase_two hA w (nsmul_mem ha' N), one_smul]

end GlobalTheory.FinWeilO

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSideOfModels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSideOfModels
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicSide

theorem adForms_eq_of_reps {Gr Γ : Type} [Group Gr] [Group Γ] (ι : Γ →* Gr) {Wc : Type} [NormedAddCommGroup Wc]
    [InnerProductSpace ℂ Wc] (ρ : Γ →* Module.End ℂ Wc) {J J' : Subgroup Gr} (χ : J →* ℂˣ) (hle : J' ≤ J) {I : Type}
    {y : I → Gr} (hy : Bridge.IsReps ι J' y) {f f' : Gr → Wc} (h1 : f ∈ Bridge.AdForms ι ρ J χ)
    (h2 : f' ∈ Bridge.AdForms ι ρ J χ) (h : ∀ k, f (y k) = f' (y k)) : f = f' := by
  funext g
  obtain ⟨k, ⟨γ, u, rfl⟩, -⟩ := hy g
  have m1 := h1 γ (y k) ⟨u, hle u.2⟩
  have m2 := h2 γ (y k) ⟨u, hle u.2⟩
  rw [h k] at m1
  exact m1.trans m2.symm


set_option maxHeartbeats 1000000 in
theorem exists_thAd_of_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), J' ≤ levJ R i t → Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => FWT.fin _ (h k)) → ∀ v₀ : (R.MW i (sg0 D A)).Vec, ∃ thAd, ThAdIs R i t h c0' v₀ thAd := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i t K' _ σ' c0' Cl h J' hle hr v₀
  classical
  obtain ⟨hinj, hrange, -⟩ := hR.HV i t
  have huniq : ∀ y y' x, Place R i t h c0' y x → Place R i t h c0' y' x → y = y' := fun y y' x h1 h2 =>
    hinj (adForms_eq_of_reps _ _ _ hle hr (hrange.le (LinearMap.mem_range_self _ y))
      (hrange.le (LinearMap.mem_range_self _ y')) fun k => (h1 k).trans (h2 k).symm)
  refine ⟨fun x => if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0, fun y x hy => ?_⟩
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  simp only [dif_pos hx]
  rw [huniq _ _ _ hx.choose_spec hy]

end GlobalTheory.AdelicSide
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSideOfModelsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicSide_of_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), J' ≤ levJ R i t → Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => FWT.fin _ (h k)) → ∀ v₀ : (R.MW i (sg0 D A)).Vec, ∃ thAd, ThAdIs R i t h c0' v₀ thAd := by
  first | exact @GlobalTheory.AdelicSide.exists_thAd_of_models | exact GlobalTheory.AdelicSide.exists_thAd_of_models | (intros; apply GlobalTheory.AdelicSide.exists_thAd_of_models <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RatUDiscrete

theorem discreteTopology_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), DiscreteTopology (ratU σ J) := by
  intro F E _ _ _ _ _ σ n J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  obtain ⟨U, hU, h⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let f : ratU σ J → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
    fun g => ((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1
  have hf : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hf1 : f 1 = 0 := sub_self _
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs))
    (pure_le_nhds _)
  have hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : ratU σ J) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j =>
      (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by
        show U ∈ 𝓝 (f 1 i j)
        rw [hf1]; exact hU)
  refine Filter.mem_of_superset hW fun g hg => ?_
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hfg : ∀ i j, f g i j =
      inclR (F := F) (AF F) (((γ : Matrix (Fin n) (Fin n) E) - 1 : Matrix (Fin n) (Fin n) E) i j) := by
    intro i j
    show (((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1) i j = _
    rw [← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply,
      apply_ite (inclR (F := F) (AF F)), map_one, map_zero]
    rfl
  have hγ1 : γ = 1 := by
    refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))
    rw [Units.val_one, ← hfg]
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j
  refine Subtype.ext (Subtype.ext ?_)
  rw [← hγ, hγ1, map_one]
  rfl

end GlobalTheory.RatUDiscrete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicScalarBase
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseScalar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem Q_base (h : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro PP hPP
  refine (h.Q_ram A.μ0 PP).2 (Or.inl hPP) ?_
  rw [h.xi_base]
  intro x _
  rfl

theorem exists_factor {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (e : Y →ₗ[ℂ] Z) (f : X →ₗ[ℂ] Z) (V : Submodule ℂ Z) (hinj : Function.Injective e) (hr : LinearMap.range e = V)
    (hm : ∀ x, f x ∈ V) : ∃ th : X →ₗ[ℂ] Y, ∀ x, e (th x) = f x := by
  subst hr
  refine ⟨(LinearEquiv.ofInjective _ hinj).symm.toLinearMap ∘ₗ f.codRestrict _ hm, fun x => ?_⟩
  have := congrArg Subtype.val ((LinearEquiv.ofInjective _ hinj).apply_symm_apply ⟨f x, hm x⟩)
  rwa [LinearEquiv.ofInjective_apply] at this

theorem integrableOn_of_isThetaLift {G' H' S' Sinf TK Tau X : Type} [MeasurableSpace H'] [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK]
    [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau] [AddCommGroup X] [Module ℂ X] {ν : Measure H'} {𝓕 : Set H'}
    {th : G' → H' → S' → ℂ} {pt : Sinf → S'} {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf} {φ : X →ₗ[ℂ] (H' → Tau)}
    {thP : LinearMap.range φ →ₗ[ℂ] TK →ₗ[ℂ] G' → ℂ} (h : Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range φ) thP)
    (x : X) (e : TK) (g : G') :
    IntegrableOn (fun a => th g a (pt (io e (φ x a)))) 𝓕 ν ∧
      thP (φ.rangeRestrict x) e g = Lift.thetaPInt ν 𝓕 th pt io (φ x) e g :=
  ⟨h.integ (φ.rangeRestrict x) e g, h.eq (φ.rangeRestrict x) e g⟩

theorem adjLev_triv {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (th : X →ₗ[ℂ] Y) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.adjLev (D := D) R.triv th = LinearMap.adjoint th := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.adjLev
  have : Nat.card (R.triv).H = 1 := Subgroup.card_bot
  rw [this]; simp

end GlobalTheory.BaseScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormConjNormalizeAndDegreeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormConjNormalizeAndDegreeOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem nrm_exact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), (∀ (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r →
    IsNrm G r γ δ z → IsNrm G r γ (z * δ * (sigG G r z)⁻¹) 1) ∧ ∀ γ : Gp G, IsNrm G 1 γ (inclG G 1 γ) 1 := by
  intro p _ G
  refine ⟨fun r γ δ z hr h => ?_, fun γ => ?_⟩
  · unfold IsNrm at h ⊢
    have e := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ z⁻¹).1
    have hit := (GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points p G r hr).1 z⁻¹
    rw [inv_inv] at e
    rw [← map_inv, e, h, hit]
    group
  · unfold IsNrm nrmG
    simp
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormConjNormalizeAndDegreeOneStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedNormConj_normalize_and_degree_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), (∀ (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r → IsNrm G r γ δ z → IsNrm G r γ (z * δ * (sigG G r z)⁻¹) 1) ∧ ∀ γ : Gp G, IsNrm G 1 γ (inclG G 1 γ) 1 := by
  first | (exact @GlobalTheory.nrm_exact) | (exact GlobalTheory.nrm_exact) | (intros; apply GlobalTheory.nrm_exact  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MkEqIffRelAndOutRel
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem GlobalTheory.LKMid.Pair.mk_eq_iff_rel_and_out_rel :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G),
      (Quot.mk Pair.Rel P = Quot.mk Pair.Rel Q ↔ P.Rel Q) ∧
        (Quot.out (Quot.mk Pair.Rel P : Cls G)).Rel P := by
  intro p _ G P Q
  have e : Equivalence (Pair.Rel (G := G)) := GlobalTheory.T.kottwitzPairScalarIsomorphic_equivalence p G
  have key : ∀ A B : Pair G, (Quot.mk Pair.Rel A = Quot.mk Pair.Rel B ↔ A.Rel B) := by
    intro A B
    rw [Quot.eq, e.eqvGen_iff]
  refine ⟨key P Q, ?_⟩
  exact (key _ _).1 (Quot.out_eq _)
end
