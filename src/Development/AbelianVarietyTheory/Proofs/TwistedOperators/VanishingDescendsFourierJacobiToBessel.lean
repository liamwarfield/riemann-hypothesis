module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralStripEqZeroOfRealModulationVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaIntegrandIsUnfoldingTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedFunctionConvergesContinuous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointJacobiFunctionUnfolded
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedBaseTermEqFlatMapLineContraction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelBasePointMulMemRationalMatrices
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.HeisL

variable {D : D7}

theorem mixedModelBasePointWithLast_mul {σ : ℕ} (B : BesL D σ) (S : HSp D) (b : Mx D (σ + 1) S.rank) :
    xLast B.d (vecB B.o B.ζ) ⬝ b = B.d.incX S (Matrix.of fun i j => b (Fin.castSucc i) j) +
      B.d.inc0 S ((B.o.resT S).symm (0, zEll B.L (σ + 1) B.ζ ⬝ b)) := by
  rw [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, GlobalTheory.Unf.FB.zEll_mul_eq,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, OrthDec.jB, ← ratV_mulVec]
  ext k j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, xLast, vecMulVec_apply, vecB]

theorem symplOH_x0L {σ : ℕ} (B : BesL D σ) (S : HSp D) (b b' : Mx D (σ + 1) S.rank) :
    symplOH S B.V (xLast B.d (vecB B.o B.ζ) ⬝ b) (xLast B.d (vecB B.o B.ζ) ⬝ b') =
      symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ b) (zEll B.L (σ + 1) B.ζ ⬝ b') := by
  rw [mixedModelBasePointWithLast_mul, mixedModelBasePointWithLast_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX,
    HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, HypDec.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, zero_add]
  rw [symplOH_skew S B.V (B.d.incX S _) (B.d.inc0 S _), HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero, zero_add,
    OrthDec.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem zlL_mem_ratMx {σ : ℕ} (B : BesL D σ) : zEll B.L (σ + 1) B.ζ ∈ ratMx D B.L.rank (σ + 1) := by
  refine ⟨vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  refine Matrix.ext fun k i => ?_
  change incA D (B.ζ k * (if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0)) =
    incA D (B.ζ k) * (if i.1 + 1 = σ + 1 then (1 : AE D) else 0)
  split_ifs
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, map_zero]

theorem mixedModelBasePoint_mul_mem_rationalMatrices {σ : ℕ} (B : BesL D σ) (S : HSp D) {γ : Mx D (σ + 1) S.rank} (hγ : γ ∈ ratMx D (σ + 1) S.rank) :
    xLast B.d (vecB B.o B.ζ) ⬝ γ ∈ ratMx D B.V.rank S.rank := by
  rw [mixedModelBasePointWithLast_mul]
  obtain ⟨g, rfl⟩ := hγ
  refine add_mem (ratMx_mul (rat_mem _) ⟨Matrix.of fun i j => g (Fin.castSucc i) j, rfl⟩)
    (ratMx_mul (rat_mem _) ?_)
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  exact ratMx_mul (rat_mem _) (ratMx_mul (zlL_mem_ratMx B) (rat_mem _))

end GlobalTheory.Asc.HeisL

namespace GlobalTheory.Asc

open GlobalTheory.Asc.HeisL GlobalTheory.Unf.FB


set_option maxHeartbeats 2000000 in
theorem heis_baseL : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : HSp D) (B : BesL D σ) (vB : VolM D (σ + 1) S.rank) (vT : VolM D σ S.rank) (vL : VolM D B.L.rank S.rank) (f : WO S B.V → ℂ) (y : WO S B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ S B.V f → GlobalTheory.Unf.FB.Quasi ψ S B.L y → (∫ b in vB.𝓕, f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) ∂vB.μ = contractT B.o S vL.μ vL.𝓕 (B.d.mixT S ψ vT.μ vT.𝓕 f 0) y 0) ∧ ∫⁻ v in vL.𝓕, ‖B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v))‖ₑ ∂vL.μ ≤ ∫⁻ b in vB.𝓕, ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vB.μ := by
  intro D ψ hψ σ S B vB vT vL f y hf hy
  have hψn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have hL1 : B.L.rank = 1 := B.line.1
  let i₀ : Fin B.L.rank := ⟨0, by omega⟩
  have h1 : ∀ i : Fin B.L.rank, i = i₀ := fun i => Fin.ext (by have := i.2; simp only [i₀]; omega)
  have h0 : B.ζ i₀ ≠ 0 := by
    intro h
    apply B.line.2
    have : B.ζ = 0 := funext fun i => by rw [h1 i, h]; rfl
    rw [this]; simp
  set e := splitLine (σ := σ) (n := S.rank) B.L B.ζ i₀ h1 h0 with he_def
  obtain ⟨he, hes⟩ := continuous_splitLine (σ := σ) (n := S.rank) B.L B.ζ i₀ h1 h0
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D (σ + 1) S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D σ S.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D B.L.rank S.rank
  haveI : BorelSpace (Mx D (σ + 1) S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D σ S.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D B.L.rank S.rank) := ⟨rfl⟩
  haveI : Countable (ratMx D (σ + 1) S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := vT.covol.1
  haveI := vL.covol.1
  haveI := vB.covol.1

  have hx : ∀ b : Mx D (σ + 1) S.rank, xLast B.d (vecB B.o B.ζ) ⬝ b = B.d.incX S (e b).1 + B.d.inc0 S ((B.o.resT S).symm (0, (e b).2)) := fun b => mixedModelBasePointWithLast_mul B S b

  set P := vT.μ.prod vL.μ with hP
  let me : Mx D (σ + 1) S.rank ≃ᵐ Mx D σ S.rank × Mx D B.L.rank S.rank :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving me (P.map e.symm) P := MeasurePreserving.symm me.symm ⟨me.symm.measurable, rfl⟩
  have hmp' : MeasurePreserving e (P.map e.symm) P := hmp
  have hν : (P.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map P e.symm hes (by simpa using he)
  have hPF : IsAddFundamentalDomain ((ratMx D σ S.rank).prod (ratMx D B.L.rank S.rank)) (vT.𝓕 ×ˢ vL.𝓕) P :=
    GlobalTheory.CoordUnfold.isAddFundamentalDomain_prod vT.covol.2.1 vL.covol.2.1
  have hF' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) (P.map e.symm) := by
    let g : (ratMx D σ S.rank).prod (ratMx D B.L.rank S.rank) → ratMx D (σ + 1) S.rank :=
      fun p => ⟨e.symm p, splitLine_symm_mem B.L B.ζ i₀ h1 h0 p.2⟩
    have hg : Function.Bijective g := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, splitLine_mem B.L B.ζ i₀ h1 h0 x.2⟩, Subtype.ext (by simp [g])⟩
    refine hPF.preimage_of_equiv hmp'.quasiMeasurePreserving hg ?_
    intro p x
    simp [g, AddSubgroup.vadd_def]
  have hv : (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) = 1 := by
    refine (hmp.measure_preimage_equiv _).trans ?_
    rw [Measure.prod_prod, vT.covol.2.2, vL.covol.2.2, one_mul]
  have hcov : IsCovolOne (ratMx D (σ + 1) S.rank) (P.map e.symm) (e ⁻¹' (vT.𝓕 ×ˢ vL.𝓕)) := ⟨hν, hF', hv⟩
  have hμeq : P.map e.symm = vB.μ := covolOne_measure_eq vB.covol hcov

  have hfx : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b,
      f (xLast B.d (vecB B.o B.ζ) ⬝ (γ + b)) = ψ (-(symplOH S B.V (xLast B.d (vecB B.o B.ζ) ⬝ γ) (xLast B.d (vecB B.o B.ζ) ⬝ b))) * f (xLast B.d (vecB B.o B.ζ) ⬝ b) := by
    intro γ hγ b
    obtain ⟨δ, hδ⟩ := mixedModelBasePoint_mul_mem_rationalMatrices B S hγ
    have e1 := hf.1 δ (xLast B.d (vecB B.o B.ζ) ⬝ b)
    rw [show ratW B.V S δ = xLast B.d (vecB B.o B.ζ) ⬝ γ from hδ] at e1
    rw [Matrix.mul_add, e1]
  have hyz : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b,
      y (zEll B.L (σ + 1) B.ζ ⬝ (γ + b)) = ψ (-(symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b))) * y (zEll B.L (σ + 1) B.ζ ⬝ b) := by
    intro γ hγ b
    obtain ⟨δ, hδ⟩ := ratMx_mul (zlL_mem_ratMx B) hγ
    have e1 := hy.1 δ (zEll B.L (σ + 1) B.ζ ⬝ b)
    rw [show ratW B.L S δ = zEll B.L (σ + 1) B.ζ ⬝ γ from hδ] at e1
    rw [Matrix.mul_add, e1]
  have hunit : ∀ a, ψ a * star (ψ a) = 1 := fun a => by
    rw [← starRingEnd_apply, RCLike.mul_conj, hψn]; simp
  set s := vT.𝓕 ×ˢ vL.𝓕 with hs
  set G : Mx D (σ + 1) S.rank → ℂ := fun b => f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) with hG
  have hGper : ∀ γ ∈ ratMx D (σ + 1) S.rank, ∀ b, G (γ + b) = G b := by
    intro γ hγ b
    simp only [hG]
    rw [hfx γ hγ b, hyz γ hγ b, symplOH_x0L, star_mul]
    calc ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b)) * f (xLast B.d (vecB B.o B.ζ) ⬝ b) *
          (star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) * star (ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b))))
        = (ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b)) * star (ψ (-symplOH S B.L (zEll B.L (σ + 1) B.ζ ⬝ γ) (zEll B.L (σ + 1) B.ζ ⬝ b)))) *
          (f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b))) := by ring
      _ = _ := by rw [hunit, one_mul]
  have hx0c : Continuous fun b : Mx D (σ + 1) S.rank => xLast B.d (vecB B.o B.ζ) ⬝ b := continuous_const.matrix_mul continuous_id
  have hzlc : Continuous fun b : Mx D (σ + 1) S.rank => zEll B.L (σ + 1) B.ζ ⬝ b := continuous_const.matrix_mul continuous_id
  have hGc : Continuous G := (hf.2.comp hx0c).mul (continuous_star.comp (hy.2.comp hzlc))
  set H : Mx D σ S.rank × Mx D B.L.rank S.rank → ℂ :=
    fun p => f (B.d.incX S p.1 + B.d.inc0 S ((B.o.resT S).symm (0, p.2))) * star (y p.2) with hH
  have hGH : ∀ p, G (e.symm p) = H p := by
    intro p
    simp only [hG, hH]
    rw [hx (e.symm p), AddEquiv.apply_symm_apply]
    congr 3
    exact congrArg Prod.snd (e.apply_symm_apply p)
  have hmix : ∀ w₀, B.d.mixT S ψ vT.μ vT.𝓕 f 0 w₀ = ∫ ξ in vT.𝓕, f (B.d.incX S ξ + B.d.inc0 S w₀) ∂vT.μ := by
    intro w₀
    change ∫ ξ in vT.𝓕, heisO ψ S B.V (B.d.incX S ξ) (heisO ψ S B.V (B.d.incAdj S 0)
      (heisO ψ S B.V (B.d.inc0 S w₀) f)) 0 ∂vT.μ = _
    congr 1
    funext ξ
    rw [HypDec.integrandT_eq, map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  have hGi : IntegrableOn G (e ⁻¹' s) (P.map e.symm) := covolOne_integrableOn hcov G hGc hGper
  have hHi : Integrable H ((vT.μ.restrict vT.𝓕).prod (vL.μ.restrict vL.𝓕)) := by
    rw [Measure.prod_restrict]
    have h2 := (hmp.integrableOn_comp_preimage me.measurableEmbedding (f := H) (s := s)).1 (by
      have : H ∘ me = G := funext fun b => by
        rw [Function.comp_apply, ← hGH]
        exact congrArg G (e.symm_apply_apply b)
      rw [this]; exact hGi)
    exact h2
  refine ⟨?_, ?_⟩
  · calc ∫ b in vB.𝓕, f (xLast B.d (vecB B.o B.ζ) ⬝ b) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) ∂vB.μ = ∫ b in vB.𝓕, G b ∂vB.μ := rfl
      _ = ∫ b in e ⁻¹' s, G b ∂(P.map e.symm) := (covolOne_integral_eq vB.covol hcov G hGper).symm
      _ = ∫ p in s, H p ∂P := by
        have h3 := hmp.setIntegral_preimage_emb me.measurableEmbedding H s
        rw [← h3]
        refine congrArg (fun F : Mx D (σ + 1) S.rank → ℂ => ∫ b in e ⁻¹' s, F b ∂(P.map e.symm)) (funext fun b => ?_)
        rw [← hGH]
        exact (congrArg G (e.symm_apply_apply b)).symm
      _ = ∫ v in vL.𝓕, ∫ ξ in vT.𝓕, H (ξ, v) ∂vT.μ ∂vL.μ := by
        rw [hP, ← Measure.prod_restrict]
        exact integral_prod_symm H hHi
      _ = _ := by
        change _ = ∫ v in vL.𝓕, B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v)) * star (y v) ∂vL.μ
        congr 1
        funext v
        rw [hmix, ← integral_mul_const]
  · have hψe : ∀ a, ‖ψ a‖ₑ = 1 := fun a => by rw [← ofReal_norm_eq_enorm, hψn, ENNReal.ofReal_one]
    set K : Mx D σ S.rank × Mx D B.L.rank S.rank → ENNReal :=
      fun p => ‖f (B.d.incX S p.1 + B.d.inc0 S ((B.o.resT S).symm (0, p.2)))‖ₑ with hK
    have hKc : Continuous K := by
      refine (hf.2.comp ?_).enorm
      simp only [HypDec.incX_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, OrthDec.resT_symm_apply]
      exact (continuous_const.matrix_mul continuous_fst).add (continuous_const.matrix_mul
        (continuous_const.add (continuous_const.matrix_mul continuous_snd)))
    have hKe : ∀ b, K (e b) = ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ := fun b => by rw [hK, hx b]
    have hper' : ∀ (γ : ratMx D (σ + 1) S.rank) (b : Mx D (σ + 1) S.rank),
        ‖f (xLast B.d (vecB B.o B.ζ) ⬝ (γ +ᵥ b))‖ₑ = ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ := by
      intro γ b
      rw [AddSubgroup.vadd_def, vadd_eq_add, hfx γ γ.2 b, enorm_mul, hψe, one_mul]
    have hF'' : IsAddFundamentalDomain (ratMx D (σ + 1) S.rank) (e ⁻¹' s) vB.μ := hμeq ▸ hF'
    calc ∫⁻ v in vL.𝓕, ‖B.d.mixT S ψ vT.μ vT.𝓕 f 0 ((B.o.resT S).symm (0, v))‖ₑ ∂vL.μ
        ≤ ∫⁻ v in vL.𝓕, ∫⁻ ξ in vT.𝓕, K (ξ, v) ∂vT.μ ∂vL.μ := by
          refine lintegral_mono fun v => ?_
          rw [hmix]
          exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p in s, K p ∂P := by
        rw [hP, ← Measure.prod_restrict, lintegral_prod_symm _ hKc.measurable.aemeasurable]
      _ = ∫⁻ b in e ⁻¹' s, K (e b) ∂(P.map e.symm) :=
        (hmp'.setLIntegral_comp_preimage_emb me.measurableEmbedding K s).symm
      _ = ∫⁻ b in e ⁻¹' s, ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vB.μ := by
        rw [hμeq]; congr 1; funext b; exact hKe b
      _ = ∫⁻ b in vB.𝓕, ‖f (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vB.μ := hF''.setLIntegral_eq vB.covol.2.1 _ hper'

end GlobalTheory.Asc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedBaseTermEqFlatMapLineContraction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

open GlobalTheory.Unf.FB GlobalTheory.FlatBase

namespace GlobalTheory.Asc.FlatBaseL

theorem fl_base_eq_contract : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  intro D ψ σ J B s vb vL y Ψ hy hΨ
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hchar := hstd.1
  obtain ⟨-, ⟨My, hMy, -⟩, -, -, -, hlaw0⟩ := GlobalTheory.Unf.FB.ThLawsL.th_laws D ψ hstd σ J B y hy
  have hlaw : ∀ b, ∀ u ∈ UX D (σ + 1), star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.nB b * J.d.levi u) y 0) * star (psiFlag ψ J.d (J.d.nB b * J.d.levi u)) = star (psiUni ψ u) * star (y (zEll B.L (σ + 1) B.ζ ⬝ b)) := hlaw0
  have hnorm : ∀ u : UX D (σ + 1), ‖psiUni ψ u.1‖ = 1 := fun u => hchar.2.1 _
  have hfl : ∀ u : UX D (σ + 1), (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ) =
      star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ := by
    intro u
    have hf : Quasi ψ J.W₀ B.V (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1)) := by
      have h := (GlobalTheory.MixValues.mixed_values D ψ hstd).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1)
      exact ⟨h.quasi, h.cont⟩
    have hh := (GlobalTheory.Asc.heis_baseL D ψ hstd σ J.W₀ B vb s.vT vL _ y hf hy).1
    calc (∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ)
        = ∫ b in vb.𝓕, star (psiUni ψ u.1) * (J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b) *
            star (y (zEll B.L (σ + 1) B.ζ ⬝ b))) ∂vb.μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
          simp only [flFun]
          rw [hlaw b u.1 u.2]
          simp only [I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source, HypDec.mixS,
            HypDec.extX, HypDec.extY, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          ring
      _ = _ := by
          rw [integral_const_mul]
          exact congrArg (star (psiUni ψ u.1) * ·) hh
  have hLeft : fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = ∫ u, star (psiUni ψ u.1) *
      ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) 0
        ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν := by
    unfold fl
    exact integral_congr_ae (Filter.Eventually.of_forall hfl)
  obtain ⟨x, hxo, hx⟩ := GlobalTheory.Asc.FBx.exists_rat_eq_xLast D σ B
  obtain ⟨M, hMi, hMb⟩ := GlobalTheory.Unf.flatFun_majorant D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x
    hxo.1 Ψ hΨ {1} isCompact_singleton
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl
  have hbound : ∀ (u : UX D (σ + 1)) (v : WO J.W₀ B.L),
      ‖flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)‖ ≤
        M u * My := by
    intro u v
    have h := hMb 1 (Set.mem_singleton 1) 0 ((B.o.resT J.W₀).symm (0, v)) u
    rw [hx, hom1] at h
    rw [norm_mul, norm_star]
    exact mul_le_mul h (hMy v) (norm_nonneg _) ((norm_nonneg _).trans h)
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  have : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  have : SecondCountableTopology (WO J.W₀ B.L) := (lattice_Mx D B.L.rank J.W₀.rank).2.2.1
  have hE : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ p.1.1.1) 0 ((B.o.resT J.W₀).symm (0, p.2)) := by
    have hmc := (GlobalTheory.MixCont.mixed_coords_continuous D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ).2
    have hc : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L => (p.1.1.1 : Mx D (σ + 1) (σ + 1)) :=
      (Units.continuous_val.comp continuous_subtype_val).comp continuous_fst
    have hin : Continuous fun p : UX D (σ + 1) × WO J.W₀ B.L =>
        ((1 : GA D J.W × GA D B.V), xLast B.d (vecB B.o B.ζ) ⬝ p.1.1.1, (0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, p.2)) :=
      continuous_const.prodMk ((continuous_const.matrix_mul hc).prodMk (continuous_const.prodMk
        ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_snd))))
    have h := hmc.comp hin
    simpa only [Function.comp_def, hom1] using h
  have hK : Continuous (Function.uncurry fun (u : UX D (σ + 1)) (v : WO J.W₀ B.L) =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v)) :=
    ((continuous_star.comp ((continuous_psiUni hchar.1 (σ + 1)).comp continuous_fst)).mul hE).mul
      (continuous_star.comp (hy.2.comp continuous_snd))
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; simp)
  have hswap := integral_swap_of_majorant s.vU.ν (vL.μ.restrict vL.𝓕) (fun u v =>
      flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u * star (y v))
    hK.stronglyMeasurable M hMi My hbound
  have h1 : fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 := by
    rw [hLeft]
    calc (∫ u, star (psiUni ψ u.1) * ∫ v in vL.𝓕, evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) 0
            ((B.o.resT J.W₀).symm (0, v)) * star (y v) ∂vL.μ ∂s.vU.ν)
        = ∫ u, ∫ v in vL.𝓕, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂vL.μ ∂s.vU.ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          simp only [flatFun]
          ring
      _ = ∫ v in vL.𝓕, ∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u *
            star (y v) ∂s.vU.ν ∂vL.μ := hswap
      _ = ∫ v in vL.𝓕, (∫ u, flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xLast B.d (vecB B.o B.ζ)) 0 Ψ ((B.o.resT J.W₀).symm (0, v)) u
            ∂s.vU.ν) * star (y v) ∂vL.μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun v => integral_mul_const _ _)
      _ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 := rfl
  refine ⟨h1, fun Mb hMb' => ?_⟩
  rw [← h1]
  unfold fl
  calc ‖∫ u, ∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ ∂s.vU.ν‖ₑ
      ≤ ∫⁻ u, ‖∫ b in vb.𝓕, flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b ∂vb.μ‖ₑ ∂s.vU.ν :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ‖flFun ψ J.d B.V s.vS (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ u b‖ₑ ∂vb.μ ∂s.vU.ν :=
        lintegral_mono fun u => enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ u, ∫⁻ b in vb.𝓕, ENNReal.ofReal Mb *
          ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
        refine lintegral_mono fun u => lintegral_mono fun b => ?_
        simp only [flFun]
        rw [enorm_mul]
        gcongr
        · rw [hlaw b u.1 u.2, ← ofReal_norm, norm_mul, norm_star, norm_star, hnorm u, one_mul]
          exact ENNReal.ofReal_le_ofReal (hMb' _)
        · simp only [I195MixedCoordinates_f1b992d3c44b213cc9f27f15.source, HypDec.mixS,
            HypDec.extX, HypDec.extY, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, le_refl]
    _ = _ := (lintegral_congr fun u => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

end GlobalTheory.Asc.FlatBaseL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedBaseTermEqFlatMapLineContractionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedBaseTerm_eq_flatMap_lineContraction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (xLast B.d (vecB B.o B.ζ)) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (xLast B.d (vecB B.o B.ζ) ⬝ u.1.1) (xLast B.d (vecB B.o B.ζ) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  first | exact @GlobalTheory.Asc.FlatBaseL.fl_base_eq_contract | exact GlobalTheory.Asc.FlatBaseL.fl_base_eq_contract | (intros; apply GlobalTheory.Asc.FlatBaseL.fl_base_eq_contract <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionFunctionIsUnfoldingNoCompactCore
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionFunctionIsUnfoldingNoCompactCore
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
open GlobalTheory.Unf.FB

noncomputable section


open GlobalTheory.ThLaws in
theorem GlobalTheory.th_isTh_lev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) := by
  intro D ψ hψ σ J B y hy x₀ hx₀
  obtain ⟨hcont, -, hleft, hcen, -, -⟩ := GlobalTheory.T.jacobiActionUnipotent_laws D ψ hψ σ J B y hy
  beta_reduce at hcen hleft
  obtain ⟨x₁, hx₁, -, -, hlast, hq⟩ := GlobalTheory.T.besselBasePoint_isUnfoldingBasePoint_spec D σ B
  have e : x₁ = x₀ := rat_injective (hx₁.trans hx₀.symm)
  refine ⟨hcont.comp continuous_subtype_val, fun γ hγQ hγN n hn => hleft γ hγN hγQ n hn, fun c n hn => ?_, ?_⟩
  · rw [hcen c n hn, hx₀, hq]
  intro j a ha1 ha0 hg
  have hl : a (Fin.last σ) = 0 := hlast a (by rw [e]; exact hg)
  have hj : j.1 < σ := by
    by_contra hc
    have : j = Fin.last σ := Fin.ext (by have := j.2; simp only [Fin.val_last]; omega)
    rw [this, hl] at ha1
    exact zero_ne_one ha1
  let j' : Fin (σ + 1) := ⟨j.1 + 1, by omega⟩
  have hjj : j < j' := by rw [Fin.lt_def]; simp [j']
  obtain ⟨t, ht⟩ := exists_psiE_ne_one hψ
  let A : Fin (σ + 1) → AE D := GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a
  let Bv : Fin (σ + 1) → AE D := fun k => if k = j' then cA D t else 0
  have hB0 : ∀ k, k ≠ j' → Bv k = 0 := fun k hk => if_neg hk
  have hA0 : ∀ i, j < i → A i = 0 := fun i hi => by
    show incA D (a i) = 0
    rw [ha0 i hi, map_zero]
  have hN : ∀ i k, ¬(i ≤ j ∧ k = j') → A i * cA D (Bv k) = 0 := by
    intro i k hik
    by_cases hk : k = j'
    · rw [hA0 i (not_le.1 fun hi => hik ⟨hi, hk⟩), zero_mul]
    · rw [hB0 k hk, map_zero, mul_zero]
  have hAB : (fun k => cA D (Bv k)) ⬝ᵥ A = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_comm]
    exact hN k k fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj)
  have hupper : tvGL A Bv hAB ∈ upperUni (σ + 1) (AE D) := fun i k => by
    refine ⟨fun hki => ?_, ?_⟩
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hki), tvN_apply,
        hN i k fun h => absurd (h.2 ▸ hki) (not_lt.2 (le_of_lt (lt_of_le_of_lt h.1 hjj))), zero_add]
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_eq, tvN_apply,
        hN i i fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj), add_zero]
  have hUX : tvGL A Bv hAB ∈ UX D (σ + 1) := mem_UX.2 hupper
  have hu : J.d.levi (tvGL A Bv hAB) ∈ flagN J.d := J.d.levi_mem_NFlag hupper
  have hup : upSum (tvN A Bv) = t := by
    unfold upSum
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j']
    · rw [if_pos (by simp [j']), tvN_apply, show Bv j' = cA D t from if_pos rfl, cA_cA']
      show incA D (a j) * t = t
      rw [ha1, map_one, one_mul]
    · intro k _ hk
      rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = j'
      · rw [if_neg]
        intro h
        apply hi
        rw [hk] at h
        exact Fin.ext (by simp [j'] at h; omega)
      · rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨J.d.jY *ᵥ Bv, J.d.levi (tvGL A Bv hAB), star (psiE ψ t), ?_, levi_isTransv J.d A Bv hAB,
    Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_iInf.2 fun i => ?_⟩, ?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form J.W (J.d.jX *ᵥ A) (J.d.jY *ᵥ Bv) = 0
    rw [form_mulVec, ← J.d.pX_eq, Matrix.mulVec_mulVec, J.d.pX_jX, Matrix.one_mulVec, hAB]
  · rw [mem_fixer]
    have hcol : ∀ m, (tvGL A Bv hAB).1 m i.1 = (1 : Mx D (σ + 1) (σ + 1)) m i.1 := fun m => by
      rw [tvGL_val, Matrix.add_apply, tvN_apply,
        hN m i.1 fun h => absurd (h.2 ▸ i.2) (not_le.2 hjj), add_zero]
    ext k l
    have h1 := congrFun (congrFun (J.d.levi_jX (tvGL A Bv hAB)) k) i.1
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id] at h1 ⊢
    rw [h1]
    simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro h1
    apply ht
    rw [← star_star (psiE ψ t), h1, star_one]
  · intro n hn n' hn'
    have hx : ∀ u ∈ UX D (σ + 1), zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := fun u hu => zEll_mul B.L B.ζ hu
    have hJu : jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.levi (tvGL A Bv hAB)) = id := by
      have := jacS_levi_mul ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (hx _ hUX) 1
      rwa [mul_one, jacS_one] at this
    have hpu : psiFlag ψ J.d (J.d.levi (tvGL A Bv hAB)) = psiE ψ t := by
      rw [psiFlag, blockX_levi, tvGL_val, upSum_add, upSum_one, zero_add, hup]
    beta_reduce
    rw [GlobalTheory.JacHom.jacS_mul J.d hx ψ (mul_mem hn hu) hn', GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hu, hJu,
      GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hn', psiFlag_mul J.d ψ (mul_mem hn hu) hn', psiFlag_mul J.d ψ hn hu,
      psiFlag_mul J.d ψ hn hn', hpu]
    simp only [id, star_mul']
    ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionFunctionIsUnfoldingNoCompactCoreStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiActionFunction_isUnfolding_noCompactCore : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) := by
  first | exact @GlobalTheory.th_isTh_lev | exact GlobalTheory.th_isTh_lev | (intros; apply GlobalTheory.th_isTh_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointJacobiFunctionUnfolded
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem fb_base_th_fl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ ∀ y : WO J.W₀ B.L → ℂ, GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) ∧ ∀ (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) Ψ, IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (rat x₀) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 := by
  intro D ψ σ J B s
  obtain ⟨x₀, hx, hbase, hR, -, -⟩ := GlobalTheory.T.besselBasePoint_isUnfoldingBasePoint_spec D σ B
  refine ⟨x₀, hx, hbase, hR, fun y hy => ⟨GlobalTheory.T.jacobiActionFunction_isUnfolding_noCompactCore D ψ s.weil.std σ J B y hy x₀ hx, fun vb vL Ψ hΨ => ?_⟩⟩
  rw [hx]
  exact (GlobalTheory.T.unfoldedBaseTerm_eq_flatMap_lineContraction D ψ σ J B s vb vL y Ψ hy hΨ).1

end GlobalTheory.Asc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointJacobiFunctionUnfoldedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiStep_basePoint_jacobiFunction_unfolded : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ ∀ y : WO J.W₀ B.L → ℂ, GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) ∧ ∀ (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) Ψ, IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) (rat x₀) Ψ = contractT B.o J.W₀ vL.μ vL.𝓕 (flFB s Ψ) y 0 := by
  first | exact @GlobalTheory.Asc.fb_base_th_fl | exact GlobalTheory.Asc.fb_base_th_fl | (intros; apply GlobalTheory.Asc.fb_base_th_fl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsFourierJacobiToBessel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.VanJac

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem isTh_const_mul {V V₀ W : HSp D} {ρ : ℕ} {d : HypDec V V₀ ρ} {x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E}
    {Th : GA D V → ℂ} (h : IsTh ψ d W x₀ Th) (c : ℂ) : IsTh ψ d W x₀ fun n => c * Th n := by
  refine ⟨continuous_const.mul h.cont, fun γ hγ hγ' n hn => by rw [h.left γ hγ hγ' n hn],
    fun a n hn => by rw [h.cen a n hn]; ring, fun j a h1 h2 h3 => ?_⟩
  obtain ⟨v, u, t, e1, e2, e3, e4, e5⟩ := h.dep j a h1 h2 h3
  exact ⟨v, u, t, e1, e2, e3, e4, fun n hn n' hn' => by rw [e5 n hn n' hn']; ring⟩

theorem fl_const_mul {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (v : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank)
    (vU : VolU D ρ) (Th : GA D V → ℂ) (c : ℂ) (x : Mx D W.rank ρ) (Ψ : WO V W → ℂ) :
    fl ψ d W v vb vU (fun n => c * Th n) x Ψ = c * fl ψ d W v vb vU Th x Ψ := by
  simp only [fl, flFun, mul_assoc, integral_const_mul]

theorem integrable_rapid {V : HSp D} (v : GlobalTheory.Unf.Vol V) {φ : GA D V → ℂ} (hφ : RapidDec V φ) (N : ℕ) :
    Integrable (fun y => ‖φ y‖ * quotHeight V y ^ N) (v.μ.restrict v.𝓕) := by
  have hfin : v.μ v.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V v.μ _ v.haar v.fund
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  obtain ⟨C, hC⟩ := hφ.decay N
  refine Integrable.of_bound (hφ.continuous.norm.mul ((continuous_quotHeight V).pow N)).aestronglyMeasurable C
    (.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (quotHeight_pos V y).le N))]
  exact hC y

variable {σ : ℕ} {J : JacL D (σ + 1)} {B : BesL D σ}

def thJ (ψ : AddChar (AF D.host.F) ℂ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ) (n : GA D J.W) : ℂ :=
  star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)

def gen (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) (x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E)
    (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) : Gen ψ J.W J.W₀ B.V (σ + 1) (GA D J.W₀) where
  d := J.d
  χV := s.χV
  χW := s.χW
  om := s.om
  vS := s.vS
  vN := J.vN
  vb := vb
  vU := s.vU
  vW := s.vW
  x₀ := x₀
  m := J.v0.μ.restrict J.v0.𝓕
  g := id
  Th := fun h n => φ h * thJ ψ J B (omz (h, 1) Φ₀) n

theorem quasi_om {S L : HSp D} {χ χz : (AE D)ˣ →* Circle} {omz : Om S L} (hz : IsWeilDatumO ψ S L χ χz omz)
    {Φ₀ : WO S L → ℂ} (h₀ : IsThetaFunO ψ S L Φ₀) (h : GA D S) : GlobalTheory.Unf.FB.Quasi ψ S L (omz (h, 1) Φ₀) :=
  ⟨(hz.om_pres _ _ h₀).quasi, (GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ S L χ χz omz hz Φ₀ h₀).comp (Continuous.prodMk_right (h, 1))⟩

theorem gen_is (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) {x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E}
    (hb : IsBase B.V x₀) (hth : ∀ y, GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsTh ψ J.d B.V x₀ (thJ ψ J B y))
    {χ χz : (AE D)ˣ →* Circle} {omz : Om J.W₀ B.L} (hz : IsWeilDatumO ψ J.W₀ B.L χ χz omz) {φ : GA D J.W₀ → ℂ}
    (hφ : RapidDec J.W₀ φ) {Φ₀ : WO J.W₀ B.L → ℂ} (h₀ : IsThetaFunO ψ J.W₀ B.L Φ₀) : (gen s vb x₀ omz φ Φ₀).Is := by
  have hψ : IsCharAF D.host.F ψ := s.weil.std.1
  have hval : ∀ y n, thJ ψ J B y n = star (ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) n) *
      y (ptS J.d B.L (zEll B.L (σ + 1) B.ζ) n)) * star (psiFlag ψ J.d n) := fun y n => by
    rw [thJ, GlobalTheory.Unf.FB.ThLaws.jacS_zero_apply]
  obtain ⟨b1, b2, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  haveI := J.v0.haar
  refine ⟨s.weil, hb, (inferInstance : SFinite (J.v0.μ.restrict J.v0.𝓕)), continuous_id,
    fun y => isTh_const_mul (hth _ (quasi_om hz h₀ y)) _, ?_, ?_⟩
  · change Continuous fun p : GA D J.W₀ × flagN J.d => φ p.1 * thJ ψ J B (omz (p.1, 1) Φ₀) p.2.1
    simp only [hval]
    have hn : Continuous fun p : GA D J.W₀ × flagN J.d => p.2.1 := continuous_subtype_val.comp continuous_snd
    have hj := (GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ χ χz omz hz Φ₀ h₀).comp
      ((continuous_fst.prodMk (continuous_const (y := (1 : GA D B.L)))).prodMk
        ((GlobalTheory.Unf.FB.ThLaws.continuous_ptS J.d B.L (zEll B.L (σ + 1) B.ζ)).comp hn))
    exact (hφ.continuous.comp continuous_fst).mul
      ((((hψ.1.comp ((GlobalTheory.Unf.FB.ThLaws.continuous_cenS _ _ _).comp hn)).mul hj).star).mul
        ((GlobalTheory.Unf.FB.ThLaws.continuous_psiFlag hψ.1 _).comp hn).star)
  · obtain ⟨C, A, hC⟩ := GlobalTheory.T.weilRepresentation_thetaFunction_sup_le_quotientHeight D ψ _ _ χ χz omz hz Φ₀ h₀
    refine ⟨fun y => ‖φ y‖ * (C * quotHeight J.W₀ y ^ A),
      (hφ.continuous.norm.mul (continuous_const.mul ((continuous_quotHeight _).pow A))).measurable, fun y n _ => ?_,
      fun k => ?_⟩
    · change ‖φ y * thJ ψ J B (omz (y, 1) Φ₀) n‖ ≤ _
      have h1 : ‖psiFlag ψ J.d n‖ = 1 := hψ.2.1 _
      rw [hval, norm_mul, norm_mul, norm_star, norm_star, norm_mul, hψ.2.1, h1, one_mul, mul_one]
      have h2 := hC y 1 (ptS J.d B.L (zEll B.L (σ + 1) B.ζ) n)
      rw [quotHeight_of_mem B.L (one_mem _), mul_one] at h2
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    · refine ((integrable_rapid J.v0 hφ (A + k)).const_mul C).congr (.of_forall fun y => ?_)
      change C * (‖φ y‖ * quotHeight J.W₀ y ^ (A + k)) = ‖φ y‖ * (C * quotHeight J.W₀ y ^ A) * quotHeight J.W₀ y ^ k
      ring

theorem gen_lhs (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) (x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E)
    (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ) :
    (gen s vb x₀ omz φ Φ₀).lhs G Φ = J.per ψ B.ζ omz φ (s.lift G Φ) Φ₀ := by
  unfold Gen.lhs JacL.per fjSrc
  refine integral_congr_ae (.of_forall fun y => integral_congr_ae (.of_forall fun n => ?_))
  change φ y * thJ ψ J B (omz (y, 1) Φ₀) n.1 * s.lift G Φ (n.1 * J.d.emb0 y) = _
  simp only [fjSrcFun, thJ, thetaJS]
  ring

theorem handP_smul_om (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ)
    (Φ₀ : WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ) (c : ℂ) (h₁ : GA D B.A) :
    handP s vL omz φ Φ₀ (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) 1 = c * handP s vL omz φ Φ₀ Ξ h₁ := by
  unfold handP
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have e : s.om₀ (h₀, B.o.emb (1, 1)) (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) = c • s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ := by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
      one_mul]
  rw [e]
  simp only [contractT, thPair, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  ring

theorem handP_zero (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ)
    (Φ₀ : WO J.W₀ B.L → ℂ) (h₁ : GA D B.A) : handP s vL omz φ Φ₀ 0 h₁ = 0 := by
  simp [handP, contractT, thPair]

theorem handP_rat (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ)
    (Φ₀ : WO J.W₀ B.L → ℂ) {Ξ : WO J.W₀ B.V₀ → ℂ} (hΞ : IsThetaFunO ψ J.W₀ B.V₀ Ξ) {γ : GA D B.A} (hγ : γ ∈ GQ B.A) :
    handP s vL omz φ Φ₀ Ξ γ = handP s vL omz φ Φ₀ Ξ 1 := by
  unfold handP
  congr 1
  funext h₀
  have e := fun w => GlobalTheory.PairKer.om_emb s.weil₀ hΞ B.o hγ h₀ 1 w
  simp only [mul_one] at e
  simp only [contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, e]

def unf (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ)
    (Φ₀ : WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ) (h : GA D B.V) : ℂ :=
  G h * handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) 1

theorem om_mul_apply {S T : HSp D} (om : Om S T) (a a' : GA D S) (b b' : GA D T) (f : WO S T → ℂ) :
    om (a * a', b * b') f = om (a, b) (om (a', b') f) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem unf_bes (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ)
    (Φ₀ : WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) {Φ : WO J.W B.V → ℂ} (hΦ : IsThetaFunO ψ J.W B.V Φ) (h : GA D B.V)
    (h₁ : GA D B.A) (n : flagN B.d) : unf s vL omz φ Φ₀ G Φ (n.1 * embA B.d B.o h₁ * h) =
      besFun ψ 1 B.d B.o B.ζ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G) h₁ n := by
  have c := GlobalTheory.T.jacobiToBesselFlatMap_equivariant D ψ σ J B s _ (s.weil.om_pres (1, h) _ hΦ) 1 n.1 n.2 h₁
  rw [← om_mul_apply, map_one, one_mul] at c
  unfold unf besFun rTrans
  rw [c, handP_smul_om]
  ring

theorem jacobiToBesselFlatMap_core_translate (s : StFB ψ J B) {Φ : WO J.W B.V → ℂ} (hΦ : IsThetaFunO ψ J.W B.V Φ) (h₀ : GA D J.W₀) (h : GA D B.V) :
    flFB s (s.om (J.d.emb0 h₀, h) Φ) = s.om₀ (h₀, B.o.emb (1, 1)) (flFB s (s.om (1, h) Φ)) := by
  have c := GlobalTheory.T.jacobiToBesselFlatMap_equivariant D ψ σ J B s _ (s.weil.om_pres (1, h) _ hΦ) h₀ 1 (one_mem _) 1
  rw [← om_mul_apply, map_one, mul_one, mul_one, one_mul,
    (GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1).2.1 _ 1 (one_mem _), star_one, one_smul] at c
  exact c


set_option maxHeartbeats 1000000 in
theorem unf_measurable (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank)
    {x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E} (hx : (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ))
    (hli : LinearIndependent D.host.E x₀.transpose)
    {χ χz : (AE D)ˣ →* Circle} {omz : Om J.W₀ B.L} (hz : IsWeilDatumO ψ J.W₀ B.L χ χz omz) {φ : GA D J.W₀ → ℂ}
    (hφ : Continuous φ) {Φ₀ : WO J.W₀ B.L → ℂ} (h₀ : IsThetaFunO ψ J.W₀ B.L Φ₀) {G : GA D B.V → ℂ} (hG : Continuous G)
    {Φ : WO J.W B.V → ℂ} (hΦ : IsThetaFunO ψ J.W B.V Φ) : Measurable (unf s vL omz φ Φ₀ G Φ) := by
  obtain ⟨b1, b2, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨vU⟩ := (GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D).2.2.2 B.L.rank
  obtain ⟨sL, -⟩ := GlobalTheory.Unf.sFinite_vol D B.L.rank J.W₀.rank vL vU
  haveI := J.v0.haar
  haveI : BorelSpace (Mx D B.L.rank J.W₀.rank) := ⟨rfl⟩
  have hfl := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x₀ hli Φ hΦ
  rw [hx] at hfl
  let f : (GA D B.V × GA D J.W₀) × Mx D B.L.rank J.W₀.rank →
      (GA D J.W × GA D B.V) × Mx D J.W₀.rank σ × WO J.W₀ B.V₀ :=
    fun q => ((J.d.emb0 q.1.2, q.1.1), ((0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, q.2)))
  have hf : Continuous f :=
    ((J.d.continuous_embed.comp (continuous_snd.comp continuous_fst)).prodMk
      (continuous_fst.comp continuous_fst)).prodMk (continuous_const.prodMk
        ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_snd)))
  have h1 := hfl.comp hf
  have h2 : Continuous fun q : (GA D B.V × GA D J.W₀) × Mx D B.L.rank J.W₀.rank => star (omz (q.1.2, 1) Φ₀ q.2) :=
    continuous_star.comp ((GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ χ χz omz hz Φ₀ h₀).comp
      (((continuous_snd.comp continuous_fst).prodMk continuous_const).prodMk continuous_snd))
  let K : (GA D B.V × GA D J.W₀) × Mx D B.L.rank J.W₀.rank → ℂ := fun q =>
    flFB s (s.om (J.d.emb0 q.1.2, q.1.1) Φ) ((B.o.resT J.W₀).symm (0, q.2)) * star (omz (q.1.2, 1) Φ₀ q.2)
  have hK : Continuous K := h1.mul h2
  haveI : SecondCountableTopology (GA D B.V × GA D J.W₀) := inferInstance
  haveI : OpensMeasurableSpace (GA D B.V × GA D J.W₀) := Prod.opensMeasurableSpace
  haveI : SecondCountableTopologyEither (GA D B.V × GA D J.W₀) (Mx D B.L.rank J.W₀.rank) :=
    secondCountableTopologyEither_of_left _ _
  haveI : OpensMeasurableSpace ((GA D B.V × GA D J.W₀) × Mx D B.L.rank J.W₀.rank) := Prod.opensMeasurableSpace
  have m1 : StronglyMeasurable fun p : GA D B.V × GA D J.W₀ => ∫ v in vL.𝓕, K (p, v) ∂vL.μ :=
    hK.measurable.stronglyMeasurable.integral_prod_right'
  have m2 : StronglyMeasurable fun p : GA D B.V × GA D J.W₀ => φ p.2 * ∫ v in vL.𝓕, K (p, v) ∂vL.μ :=
    (hφ.comp continuous_snd).measurable.stronglyMeasurable.mul m1
  have m3 : StronglyMeasurable fun h : GA D B.V => ∫ y in J.v0.𝓕, φ y * ∫ v in vL.𝓕, K ((h, y), v) ∂vL.μ ∂J.v0.μ :=
    m2.integral_prod_right' (ν := J.v0.μ.restrict J.v0.𝓕)
  have e : unf s vL omz φ Φ₀ G Φ =
      fun h => G h * ∫ y in J.v0.𝓕, φ y * ∫ v in vL.𝓕, K ((h, y), v) ∂vL.μ ∂J.v0.μ := by
    funext h
    simp only [unf, handP, K, jacobiToBesselFlatMap_core_translate s hΦ]
    rfl
  rw [e]
  exact hG.measurable.mul m3.measurable


set_option maxHeartbeats 1000000 in
theorem vanFB : ∀ D : D7, VanFB D := by
  intro D ψ σ J B s 𝒮 Γ₀ K hL vL χ χz omz hz φ G Φ₀ hφ hG h₀ hGK hvan Φ hΦ𝒮
  have hΦ := hL.theta Φ hΦ𝒮
  obtain ⟨x₀, hx, hb, hR, hy⟩ := GlobalTheory.T.fourierJacobiStep_basePoint_jacobiFunction_unfolded D ψ σ J B s
  obtain ⟨vb⟩ := (GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D).2.2.1 (σ + 1) J.W₀.rank
  have ha : (gen s vb x₀ omz φ Φ₀).Is := gen_is s vb hb (fun y h => (hy y h).1) hz hφ h₀
  have hker : (gen s vb x₀ omz φ Φ₀).ker G Φ = unf s vL omz φ Φ₀ G Φ := by
    funext h
    change G h * ∫ y in J.v0.𝓕, fl ψ J.d B.V s.vS vb s.vU (fun n => φ y * thJ ψ J B (omz (y, 1) Φ₀) n) (rat x₀)
      (s.om (J.d.emb0 y, h) Φ) ∂J.v0.μ = _
    unfold unf handP
    congr 2
    funext y
    rw [fl_const_mul, ← jacobiToBesselFlatMap_core_translate s hΦ]
    exact congrArg (φ y * ·) ((hy _ (quasi_om hz h₀ y)).2 vb vL _ (s.weil.om_pres _ _ hΦ))
  obtain ⟨b1, b2, b3, b4, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨b1', b2', b3', b4', -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨-, -, hfd⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D B.V (GQ B.V ⊓ besGrp B.d B.o) inf_le_left
  obtain ⟨𝓑, h𝓑⟩ := hfd s.vW.μ s.vW.haar
  have h𝓑' : IsFundamentalDomain (GQ B.V ⊓ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) : Subgroup (GA D B.V)) 𝓑 s.vW.μ := by
    rw [hR]; exact h𝓑
  have hU := B.vN.unit
  have hHR : (semiMeas (flagN B.d) (embA B.d B.o) B.vA.μ B.vN.ν).IsHaarMeasure :=
    (GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L σ B.d B.o B.vN.ν B.vN.𝓝 hU).2.2 B.vA.μ B.vA.haar
  obtain ⟨𝓡, h𝓡, hint⟩ := GlobalTheory.T.semidirect_haar_measure_fundamental_domain D B.V B.A (flagN B.d) (embA B.d B.o) (BesSemi.continuous_embA B.d B.o)
    (GlobalTheory.Mem.TrueRecord.isClosed_NFlag B.V (isIsoSub_e B.d))
    (fun n hn h => by rw [embA_apply]; exact GlobalTheory.MixPer.Decomp.conj_mem B.d hn _)
    (fun n hn n' hn' h h' e => BesSemi.unique B.d B.o hn hn' e) (fun n hn h => BesSemi.rat_iff B.d B.o hn h)
    B.vA B.vN.ν B.vN.𝓝 hU.1 hU.2.1 hHR
  obtain ⟨hsplit, hinv, -⟩ := ((GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D B.V).2.2.2.2.2 B.V₀ σ B.d).2 B.A B.L B.o
  obtain ⟨-, hone, -, -, hdec, -⟩ := GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1
  obtain ⟨habs, hcont⟩ := GlobalTheory.T.besselPeriod_handedFunction_converges_continuous D ψ σ J B s vL χ χz omz hz φ G Φ₀ Φ hφ hG h₀ hΦ
  have hmeas := unf_measurable s vL hx hb.1 hz hφ.continuous h₀ hG.continuous hΦ
  have hm : ∀ h : GA D B.V, Measurable fun g : GA D B.V => unf s vL omz φ Φ₀ G Φ (g * h) :=
    fun h => hmeas.comp (continuous_mul_const h).measurable
  have habs' : ∀ h : GA D B.V, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝
      fun h₁ n => unf s vL omz φ Φ₀ G Φ (n.1 * embA B.d B.o h₁ * h) := fun h => by
    simp only [unf_bes s vL omz φ Φ₀ G hΦ]
    exact habs h
  have hmean : ∀ h : GA D B.V, (∫ r : besGrp B.d B.o in 𝓡, unf s vL omz φ Φ₀ G Φ (r * h)
      ∂(semiMeas (flagN B.d) (embA B.d B.o) B.vA.μ B.vN.ν)) =
        B.per ψ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G) := fun h => by
    refine ((hint _ (hm h)).2 (habs' h)).trans ?_
    simp only [unf_bes s vL omz φ Φ₀ G hΦ]
    rfl
  have key := GlobalTheory.T.continuousMean_vanishing_on_strips_at_one D B.V s.vW (besGrp B.d B.o) K (GlobalTheory.BesClosed.besGrp_isClosed D B.V B.V₀ B.A B.L σ B.d B.o)
    hsplit hL.fin hL.cpt hL.opn _ hHR (hinv _ hHR) 𝓡 𝓑 h𝓡 h𝓑 (unf s vL omz φ Φ₀ G Φ) hmeas ?_ ?_
    (fun h => (hint _ (hm h)).1.2 (habs' h)) ?_ ?_ ?_ ?_
  · have e := hmean 1
    have e1 : s.om ((1 : GA D J.W), (1 : GA D B.V)) Φ = Φ := by rw [Prod.mk_one_one, map_one, Module.End.one_apply]
    have e2 : rTrans (1 : GA D B.V) G = G := funext fun g => by rw [rTrans, mul_one]
    rw [e1, e2] at e
    simp only [mul_one] at e
    exact e.symm.trans key
  · intro γ hγ h
    obtain ⟨hq, hbes⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨n, hn, h₁, rfl⟩ := (hdec γ).1 hbes
    obtain ⟨hnq, hhq⟩ := (BesSemi.rat_iff B.d B.o hn h₁).1 hq
    have hth : IsThetaFunO ψ J.W₀ B.V₀ (flFB s (s.om (1, h) Φ)) := by
      have t := (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU x₀ hb.1 0 _
        (s.weil.om_pres (1, h) _ hΦ)).2
      rw [hx] at t
      exact t
    refine (unf_bes s vL omz φ Φ₀ G hΦ h h₁ ⟨n, hn⟩).trans ?_
    simp only [besFun, rTrans, unf]
    rw [handP_rat s vL omz φ Φ₀ hth hhq, hone _ n hnq, hG.1 _ hq h, star_one, mul_one, mul_comm]
  · rw [← hker]
    exact (GlobalTheory.T.thetaLift_unfolding_integrated_over_family D ψ J.W J.W₀ B.V (σ + 1) (GA D J.W₀) _ ha G Φ hG hΦ 𝓑 h𝓑').2.1
  · exact hcont.congr fun h => (hmean h).symm
  · intro k hk g
    have e : s.om (1, g * k) Φ = s.om (1, g) Φ := by
      have := om_mul_apply s.om 1 1 g k Φ
      rwa [one_mul, hL.fix Φ hΦ𝒮 k hk] at this
    rw [unf, unf, e, hGK k hk]
  · intro h hh
    have hne : flFB s (s.om (1, h) Φ) ≠ 0 := fun h0 => hh (by rw [unf, h0, handP_zero, mul_zero])
    have t := hL.supp Φ hΦ𝒮 h hne
    rwa [← hx, hR] at t
  · intro C hC hCi
    have t1 := (GlobalTheory.T.adelicStripSet_measurable_read_on_realPart D B.V (σ + 1) x₀ hb C hC hCi).1
    have t2 := GlobalTheory.T.integral_strip_eq_zero_of_real_modulation_vanishing D ψ J.W J.W₀ B.V (σ + 1) (GA D J.W₀) _ ha G hG Φ hΦ (fun c hc => ?_) 𝓑 h𝓑' C hC hCi
    · rw [hker] at t2
      rw [← hR]
      exact ⟨t1, t2⟩
    · rw [gen_lhs]
      refine hvan _ (hL.real Φ hΦ𝒮 _ ?_)
      change (c ⬝ J.d.pY).map (finPart D) = 0
      rw [Matrix.map_mul, hc, Matrix.zero_mul]

end GlobalTheory.Asc.VanJac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsFourierJacobiToBesselStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_descends_fourierJacobi_to_bessel : ∀ D : D7, VanFB D := by
  first | exact @GlobalTheory.Asc.VanJac.vanFB | exact GlobalTheory.Asc.VanJac.vanFB | (intros; apply GlobalTheory.Asc.VanJac.vanFB <;> assumption)
end
