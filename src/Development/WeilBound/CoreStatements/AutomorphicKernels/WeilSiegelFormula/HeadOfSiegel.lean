module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviAdjointOnChains
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinUnfoldingSecondTerm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanGramFibreMeasureExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonHermMain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEisensteinSiegelConvergence
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec)

namespace GlobalTheory.WeilEisConv

theorem weilEisensteinSiegelConvergence : GlobalTheory.Published.WeilEisensteinSiegelConvergence := by
  intro D n V hn hV ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.StdUnn.SchDatum.exists_datum D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 0 = swSec A V omh μ 𝓕 f (κ.symm g) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    have e : κ (κ.symm g) = g := κ.apply_symm_apply g
    rw [e] at h
    exact (congrFun h 0).trans (mixS_dblDec_zero A V ψ₀ μ 𝓕 _ 0)
  obtain ⟨a, ha⟩ := exists_isMaj A
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  obtain ⟨C, hC, h₁⟩ := GlobalTheory.SWAbsGrowth.norm_swSec_le hW hμ hf a ha
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hs : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hc.2.2.2, hc.2.2.2, star_star])
  have hP := GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ' hsk κ hκ
  have hG := GlobalTheory.StdUnn.chart_mem_GF_iff D A μ' hsk κ hκ
  have hb : (A.rank : ℝ) < (V.rank : ℝ) / 2 := by
    have : (2 * n : ℝ) < V.rank := by exact_mod_cast hV
    change (n : ℝ) < _
    linarith
  have hsum : Summable fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) =>
      (hgt A a (κ.symm (Subtype.val (q.out : GF D n))) : ℝ) ^ ((V.rank : ℝ) / 2) := by
    refine GlobalTheory.Eis.Conv.summable_hgt hc hs (GlobalTheory.Doubling.gram_hdbl A) (GlobalTheory.Doubling.isHermND_gram A)
      (GlobalTheory.Doubling.isCompact_Khat A a) hI (γ := fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) => κ.symm (Subtype.val (q.out : GF D n)))
      (fun q => (hG _).2 (by rw [MulEquiv.apply_symm_apply]; exact q.out.2)) (fun q q' h => ?_) hb
    have h' := (hP _).1 h
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    rw [← q.out_eq, ← q'.out_eq]
    exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, h'⟩, inv_mul_cancel_right _ _⟩
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hsum.mul_left C)
  simp only [GlobalTheory.Eis.term, mul_one]
  rw [key]
  exact h₁ _

end GlobalTheory.WeilEisConv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisCells
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCellsChapter

theorem eisCells : PositivityTheory.GramSchwartzFunctions.EisCells :=
  GlobalTheory.T.eisenstein_cells_decomposition GlobalTheory.T.eisenstein_bruhat_decomposition GlobalTheory.T.eisenstein_rational_points GlobalTheory.T.eisenstein_siegel_parabolic_invariance
    (GlobalTheory.T.eisenstein_second_term_from_parts GlobalTheory.T.eisenstein_heisenberg_schwartz GlobalTheory.T.eisenstein_covariance GlobalTheory.T.eisenstein_vanishing GlobalTheory.T.eisenstein_unfolding_second_term GlobalTheory.T.eisenstein_theta_invariance)

end GlobalTheory.CompanionTheory.EisCellsChapter
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.SiegelND
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.UntupTupOf
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Hand.TupleUntupling

variable {D : D7}

def untup {m r : ℕ} (y : Mx D m r) : Fin r → Fin m → AE D := fun a i => y i a

theorem tupOf_untup {m r : ℕ} (y : Mx D m r) : tupOf (untup y) = y := rfl

theorem untup_tupOf {m r : ℕ} (X : Fin r → Fin m → AE D) : untup (tupOf X) = X := rfl

def hermE (D : D7) (r : ℕ) (b : hermA D r) : HermR (AF D.host.F) D.sp.cm.sig r :=
  ⟨b.1, fun i j => by
    have h := congrFun (congrFun b.2 i) j
    simp only [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] at h
    exact h⟩

end PositivityTheory.PfWsf.Hand.TupleUntupling
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.HermitianIntegration
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.ExistsSchwartzOfIsSchwartzArch
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Hand.TupleUntupling

variable {D : D7}

theorem exists_schwartz_of_isSchwartzArch {θ : InfFam D} (hθ : IsInfFam θ) {m r : ℕ}
    {a : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (ha : GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (F := D.host.F) (E := D.host.E) a) :
    ∃ f : SchwartzMap (D.what₂.Tau → Fin m → Fin r → ℂ) ℂ, ∀ Y, a Y = f fun τ i j => θ τ (Y j i) := by
  obtain ⟨N, e, he, he', f, hf⟩ := ha
  obtain ⟨P, hP⟩ := GlobalTheory.CompanionTheory.SiegelND.SchGlue.exists_infHomeo hθ
  let Q : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → Fin m → Fin r → ℂ) :=
    { toFun := fun Y τ i j => P (Y j i) τ
      invFun := fun c j i => P.symm fun τ => c τ i j
      left_inv := fun Y => by simp
      right_inv := fun c => by simp
      continuous_toFun := continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply τ).comp (P.continuous.comp ((continuous_apply i).comp (continuous_apply j)))
      continuous_invFun := continuous_pi fun j => continuous_pi fun i => P.symm.continuous.comp
        (continuous_pi fun τ => (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))) }
  have hQ : ∀ Y τ i j, Q Y τ i j = θ τ (Y j i) := fun Y τ i j => hP _ _
  have hadd : ∀ X Y, Q (X + Y) = Q X + Q Y := fun X Y => by
    funext τ i j
    simp only [hQ, Pi.add_apply, map_add (f := _)]
  let A : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃+ (Fin N → ℝ) := (AddEquiv.mk' Q.toEquiv hadd).symm.trans e
  have hA : Continuous A := he.comp Q.symm.continuous
  have hA' : Continuous A.symm := Q.continuous.comp he'
  let L : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃L[ℝ] (Fin N → ℝ) := A.toRealLinearEquiv hA hA'
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, fun Y => ?_⟩
  have hY : (fun τ i j => θ τ (Y j i)) = Q Y := funext fun τ => funext fun i => funext fun j => (hQ Y τ i j).symm
  rw [hf, hY]
  show f (e Y) = f (e (Q.symm (Q Y)))
  rw [Homeomorph.symm_apply_apply]

theorem mem_schwartzA_of_sb (θ : InfFam D) (hθ : IsInfFam θ) {m r : ℕ} (Φ : (Fin r → Fin m → AE D) → ℂ)
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    (fun y : Mx D m r => Φ (untup y)) ∈ schwartzA θ m r := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  choose f hf using fun i => exists_schwartz_of_isSchwartzArch hθ (ha i)
  have hg : ∀ i, (fun Z : Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => b i fun j l => Z l j) ∈
      GlobalTheory.WeilM.SB (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) := fun i => by
    have h := GlobalTheory.CompanionTheory.SiegelND.SchGlue.isSB_swap (D := D) (m := r) (r := m) (g := b i) ⟨(hb i).1, (hb i).2⟩
    exact ⟨h.1, h.2⟩
  have hsum : (fun y : Mx D m r => Φ (untup y)) = ∑ i : Fin k, fun x : Mx D m r =>
      f i (fun τ l j => compAt θ τ x l j) *
        (fun Z : Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => b i fun j l => Z l j)
          (fun l j => finPart D (x l j)) := by
    funext y
    rw [hs, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf]
    rfl
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, _, hg i, rfl⟩

end PositivityTheory.PfWsf.Hand.TupleUntupling
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.IntegrableOfAddEquiv
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Jab.WsInteg

variable {D : D7}

def hermE (D : D7) (r : ℕ) (b : hermA D r) : HermR (AF D.host.F) D.sp.cm.sig r :=
  ⟨b.1, fun i j => by
    have h := congrFun (congrFun b.2 i) j
    simp only [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] at h
    exact h⟩

theorem integrable_of_addEquiv {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V']
    (g : V → V') (k : V' → V) (h1 : Function.LeftInverse k g) (h2 : Function.RightInverse k g)
    (hadd : ∀ x y, g (x + y) = g x + g y) (hc : Continuous g) (hc' : Continuous k)
    (μ : Measure V) (hμ : μ.IsAddHaarMeasure) (ν : Measure V') (hν : ν.IsAddHaarMeasure)
    (f : V' → ℂ) (hf : Integrable (fun b => f (g b)) μ) : Integrable f ν := by
  let e : V ≃+ V' := { toFun := g, invFun := k, left_inv := h1, right_inv := h2, map_add' := hadd }
  let h : V ≃ₜ V' := { toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ hc hc'
  have hi : Integrable f (μ.map e) := (integrable_map_equiv h.toMeasurableEquiv f).2 hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (μ.map e)]
  exact hi.smul_measure_nnreal


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_of_hermE {r : ℕ} (lam : Measure (hermA D r)) (hlam : lam.IsAddHaarMeasure)
    (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)) (hdb : db.IsAddHaarMeasure)
    (f : HermR (AF D.host.F) D.sp.cm.sig r → ℂ) (hf : Integrable (fun b => f (hermE D r b)) lam) :
    Integrable f db := by
  haveI : IsTopologicalAddGroup (Mx D r r) := inferInstanceAs (IsTopologicalAddGroup (Fin r → Fin r → AE D))
  haveI i3 : SecondCountableTopology (Mx D r r) := inferInstanceAs (SecondCountableTopology (Fin r → Fin r → AE D))
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  haveI : SecondCountableTopology (HermR (AF D.host.F) D.sp.cm.sig r) :=
    @Topology.IsInducing.secondCountableTopology _ _ _ _ _ i3 Topology.IsInducing.subtypeVal
  exact integrable_of_addEquiv (hermE D r) (fun S => ⟨S.1, Matrix.ext fun a c => S.2 a c⟩) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (continuous_subtype_val.subtype_mk _) (continuous_subtype_val.subtype_mk _)
    lam hlam db hdb f hf

end PositivityTheory.PfWsf.Jab.WsInteg
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.ExistsIntegralEqMul
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Hand.TupleUntupling

variable {D : D7}

theorem exists_integral_eq_mul {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V']
    (f : V → V') (g : V' → V) (h1 : Function.LeftInverse g f) (h2 : Function.RightInverse g f)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hc : Continuous f) (hc' : Continuous g)
    (ν : Measure V) (hν : ν.IsAddHaarMeasure) (μ : Measure V') (hμ : μ.IsAddHaarMeasure) :
    ∃ c : ℂ, ∀ u : V' → ℂ, ∫ x, u (f x) ∂ν = c * ∫ y, u y ∂μ := by
  let e : V ≃+ V' := { toFun := f, invFun := g, left_inv := h1, right_inv := h2, map_add' := hadd }
  haveI : (ν.map f).IsAddHaarMeasure := e.isAddHaarMeasure_map ν hc hc'
  refine ⟨((Measure.addHaarScalarFactor (ν.map f) μ : ℝ) : ℂ), fun u => ?_⟩
  have h : ∫ y, u y ∂(ν.map f) = ∫ x, u (f x) ∂ν :=
    integral_map_equiv
      ({ toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' } : V ≃ₜ V').toMeasurableEquiv u
  rw [← h]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (ν.map f) μ]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem gramR_untup (V : HSp D) {r : ℕ} (y : Mx D V.rank r) :
    gramR (AF D.host.F) D.sp.cm.sig V.gram (untup y) = GlobalTheory.StdUnn.inner V y y := by
  ext a b
  simp only [gramR, untup, hR, Formalism.UG.hform, JR, GlobalTheory.StdUnn.inner, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change _ = (cA D (y i a)) * (incA D (V.gram i j) * y j b)
  rw [mul_assoc]
  rfl


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem starN_hermE (V : HSp D) {r : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank r))
    (hμ : μ.IsAddHaarMeasure) (dx : Measure (Fin r → Fin V.rank → AE D)) (hdx : dx.IsAddHaarMeasure) :
    ∃ c : ℂ, ∀ (Φ : (Fin r → Fin V.rank → AE D) → ℂ) (b : hermA D r),
      starN D.sp.cm.sig V.gram ψ dx Φ (hermE D r b) = c * Jt ψ V μ (fun y => Φ (untup y)) b := by
  obtain ⟨k1, k2, k3, -, -, -⟩ := lattice_Mx D V.rank r
  haveI : IsTopologicalAddGroup (Mx D V.rank r) := k1
  haveI : LocallyCompactSpace (Mx D V.rank r) := k2
  haveI : SecondCountableTopology (Mx D V.rank r) := k3
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  obtain ⟨j1, -, -, i4, i5⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI : BorelSpace (Fin V.rank → AE D) := Pi.borelSpace
  haveI : BorelSpace (Fin r → Fin V.rank → AE D) := Pi.borelSpace
  obtain ⟨c, hc⟩ := exists_integral_eq_mul (tupOf (D := D) (m := V.rank) (r := r)) untup untup_tupOf tupOf_untup
    (fun _ _ => rfl) (continuous_matrix fun i a => (continuous_apply i).comp (continuous_apply a))
    (continuous_pi fun a => continuous_pi fun i => continuous_id.matrix_elem i a) dx hdx μ hμ
  refine ⟨c, fun Φ b => ?_⟩
  unfold starN Jt
  rw [← hc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have hg := gramR_untup V (tupOf X)
  change Φ X * ψ (_ * Algebra.trace _ _
    (Matrix.trace (b.1 * gramR (AF D.host.F) D.sp.cm.sig V.gram (untup (tupOf X))))) = _
  rw [hg]
  rfl

end PositivityTheory.PfWsf.Hand.TupleUntupling
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Hand.TupleUntupling

variable {D : D7}

theorem integrable_of_hermE {r : ℕ} (lam : Measure (hermA D r)) (hlam : lam.IsAddHaarMeasure)
    (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)) (hdb : db.IsAddHaarMeasure)
    (f : HermR (AF D.host.F) D.sp.cm.sig r → ℂ) (hf : Integrable (fun b => f (hermE D r b)) lam) :
    Integrable f db :=
  PositivityTheory.PfWsf.Jab.WsInteg.integrable_of_hermE lam hlam db hdb f hf

theorem hermitian_unfolding_integral (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (θ : InfFam D)
    (hθ : IsInfFam θ) (μ : Measure (Mx D V.rank r)) (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕)
    (lam : Measure (hermA D r)) (hlam : ∃ 𝓖, IsCovolOneH lam 𝓖) (hr : 2 * r < V.rank)
    (dx : Measure (Fin r → Fin V.rank → AE D)) (hdx : dx.IsAddHaarMeasure)
    (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)) (hdb : db.IsAddHaarMeasure)
    (Φ : (Fin r → Fin V.rank → AE D) → ℂ)
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    Integrable (starN D.sp.cm.sig V.gram ψ dx Φ) db := by
  have hφ := mem_schwartzA_of_sb θ hθ Φ hΦ
  obtain ⟨𝓖, h𝓖⟩ := hlam
  have hJ : Integrable (Jt ψ V μ fun y => Φ (untup y)) lam :=
    (GlobalTheory.T.poisson_summation_hermitian_lattice D r ψ hψ lam 𝓖 h𝓖 _ (GlobalTheory.T.theta_integral_continuous D r V ψ θ μ _ hψ hθ hμ hφ)
      (GlobalTheory.T.theta_integral_locally_summable_bound D r V ψ θ μ _ hr hψ hθ hμ hφ)).1
  obtain ⟨c, hc⟩ := starN_hermE V (r := r) ψ μ hμ.choose_spec.1 dx hdx
  refine integrable_of_hermE lam h𝓖.1 db hdb _ ?_
  simp only [hc]
  exact hJ.const_mul c

end PositivityTheory.PfWsf.Hand.TupleUntupling
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.PureIdentity
noncomputable section

section Body
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace PositivityTheory.PfWsf.Hand.CoreH

section Pure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem coefS_pure (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (h2n : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (hInt : ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Integrable (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ) db)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf)
    (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (hdet : T.det ≠ 0) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S →
      ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, IsSchwartzArch φ →
      ∀ A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E),
        (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) →
        coefSN σ b J ψ dx db (pureN φ A) T S =
          (∫ X, φ X ∂(minf (hermOf (Ainf F) σ T hT))) *
            ∏ v ∈ S, ((m v (hermOf (Fv F v) σ T hT) (A v)).toReal : ℂ) := by
  classical
  obtain ⟨hEu, hlat⟩ := GlobalTheory.T.adelic_measure_euler_product_decomposition F E σ hCM M J hJ n h2n ψ hψ dx hdx d b laminf lam hinf hlam
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.euler_product_measure_eventually_standard F E M n d b dx 1 _ _ hEu
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.hermitian_measure_euler_product F E σ hCM M J hJ n h2n ψ hψ db hdb d b laminf lam hinf hlam
  have hq := GlobalTheory.T.gram_matrix_integral_almost_all_places F E σ hCM M J hJ n h2n d b T hT
  have hqf := Filter.eventually_cofinite.1 hq
  refine ⟨S₀ ∪ S₁ ∪ hqf.toFinset, fun S hS φ hφ A hA hAl => ?_⟩
  have hS0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : ∀ v, v ∉ S → ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)),
      hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ latH σ b v n := by
    intro v hv
    by_contra hc
    exact hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inr hc))
  obtain ⟨ρ, U, hρ, hρs, hU, hUs, hI, hc, hbd, hlim⟩ := hS₁ S hS1
  have hΦSB : IsSchwartzBruhat (pureN φ A) := GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n d b S φ A hφ hA hAl
  have hΦdx : Integrable (pureN φ A) dx := GlobalTheory.T.schwartz_bruhat_integrable_adelic F E σ hCM M J hJ n h2n ψ hψ dx hdx _ hΦSB
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    hInt _ hΦSB
  have hu : ∀ (R : Type) [CommRing R] [Algebra F R],
      IsUnit (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
    intro R _ _
    have h : (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det = inclR R T.det :=
      ((inclR R).map_det T).symm
    rw [h]
    exact (IsUnit.mk0 _ hdet).map (inclR R)
  set cI : HermR (Ainf F) σ n := hermOf (Ainf F) σ T hT with hcI
  have hInf := GlobalTheory.T.archimedean_gram_fibre_measure_exists F E σ hCM M J hJ n h2n d b laminf hinf minf hminf cI (hu _) φ hφ ρ hρ hρs
  have hV := fun v => GlobalTheory.T.local_gram_fibre_measure_unramified F E σ hCM M J hJ n h2n d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (hu _) (A v) (hA v).1 (hA v).2 (fun k => U k v)
    (fun k => ⟨(hU k v).1, (hU k v).2.1, (hU k v).2.2.1⟩) (hUs v)
  have hUpos : ∀ k v, 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal :=
    fun k v => (hU k v).2.2.2
  have hρpos : ∀ k, 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) := fun k => (hρ k).2.2.2
  have hck : ∀ k, (∫ y, testH σ b (ρ k) S (U k) y ∂db) ≠ 0 := by
    intro k
    rw [hc k]
    refine mul_ne_zero (by exact_mod_cast (hρpos k).ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    exact_mod_cast (hUpos k v).ne'
  have a1 : ∀ {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R'),
      hermMap f σ (hermOf R σ T hT) = hermOf R' σ T hT := fun f => hermMap_hermOf f σ T hT
  have h3 : ∀ (x : Fin n → Fin M → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      hermV σ v (hermFin σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x)) =
        hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) (projV v (projFin x)) := by
    intro x v
    simp only [hermV, hermFin, hermMap_sub, a1, hermMap_gramH]
    rfl
  have h0 : ∀ x : Fin n → Fin M → AF F ⊗[F] E,
      hermInf σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) = cI - gramH hCM hJ (Ainf F) (projInf x) := by
    intro x
    simp only [hermInf, hermMap_sub, a1, hermMap_gramH]
    rfl
  have key : ∀ k, ∫ bb, (fouH σ ψ db (testH σ b (ρ k) S (U k)) bb / ∫ y, testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db =
      ((∫ X, φ X * (ρ k (cI - gramH hCM hJ (Ainf F) X) : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) /
          ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) *
        ∏ v ∈ S, (((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M
          (A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v})).toReal /
            (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℝ) : ℂ) := by
    intro k
    have hf := GlobalTheory.T.siegel_weil_integral_normalised F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb _ hΦdx
      (testH σ b (ρ k) S (U k)) (hI k).1 (hI k).2 T hT
    let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) := fun v =>
      if v ∈ S then A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v} else A v
    have hA'S : ∀ v ∈ S, A' v = A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v} :=
      fun v hv => if_pos hv
    have hA'n : ∀ v, v ∉ S → A' v = latV b v := fun v hv => (if_neg hv).trans (hAl v hv)
    have hmem : ∀ x : Fin n → Fin M → AF F ⊗[F] E,
        (projFin x ∈ boxFN A ∧ hermFin σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∈ boxH σ b n S (U k)) ↔
          projFin x ∈ boxFN A' := by
      intro x
      constructor
      · rintro ⟨h, h'⟩ v
        by_cases hv : v ∈ S
        · rw [hA'S v hv]
          refine ⟨h v, ?_⟩
          show _ ∈ U k v
          rw [← h3 x v]
          exact h'.1 v hv
        · rw [show A' v = A v from if_neg hv]
          exact h v
      · intro h
        refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
        · by_cases hv : v ∈ S
          · have := h v
            rw [hA'S v hv] at this
            exact this.1
          · have := h v
            rwa [show A' v = A v from if_neg hv] at this
        · have := h v
          rw [hA'S v hv] at this
          rw [h3 x v]
          exact this.2
        · have := h v
          rw [hA'n v hv] at this
          rw [h3 x v]
          exact hS2 v hv _ this
    have hpt : ∀ x, pureN φ A x * testH σ b (ρ k) S (U k) (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) =
        pureN (fun X => φ X * (ρ k (cI - gramH hCM hJ (Ainf F) X) : ℂ)) A' x := by
      intro x
      unfold pureN testH
      rw [h0 x]
      by_cases h : projFin x ∈ boxFN A'
      · obtain ⟨ha, hb⟩ := (hmem x).2 h
        rw [Set.indicator_of_mem ha, Set.indicator_of_mem hb, Set.indicator_of_mem h]
        ring
      · rw [Set.indicator_of_notMem h, mul_zero]
        by_cases ha : projFin x ∈ boxFN A
        · have hb : hermFin σ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∉ boxH σ b n S (U k) :=
            fun hb => h ((hmem x).1 ⟨ha, hb⟩)
          rw [Set.indicator_of_notMem hb]
          simp
        · rw [Set.indicator_of_notMem ha]
          simp
    have hmeasA' : ∀ v, MeasurableSet (A' v) := by
      intro v
      by_cases hv : v ∈ S
      · rw [hA'S v hv]; exact ((hV v).1 k).1
      · rw [show A' v = A v from if_neg hv]
        exact (GlobalTheory.T.local_gram_fibre_measure_standard_volume F E σ hCM M J hJ n h2n d b v (lam v) (hlam v) (m v) (hm v) _ (hu _) (A v) (hA v).1 (hA v).2).1
    have hfinA' : ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v) ≠ ⊤ := by
      intro v
      by_cases hv : v ∈ S
      · rw [hA'S v hv]; exact ((hV v).1 k).2
      · rw [hA'n v hv, hlat v]; exact ENNReal.one_ne_top
    have he := (hS₀ S hS0 _ (hInf.1 k).1 (hInf.1 k).2 A' hmeasA' hfinA' hA'n).2
    have htail : (∏' v : {v // v ∉ S}, (GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) b (lam v.1) n M (latV b v.1)).toReal) = 1 := by
      simp [hlat]
    rw [htail] at he
    have hprod : (∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v)).toReal : ℂ)) =
        ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M
          (A v ∩ {X | hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ U k v})).toReal : ℂ) :=
      Finset.prod_congr rfl fun v hv => by rw [hA'S v hv]
    have e1 : ∫ bb, (fouH σ ψ db (testH σ b (ρ k) S (U k)) bb / ∫ y, testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db =
        (∫ bb, fouH σ ψ db (testH σ b (ρ k) S (U k)) bb *
          (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db) /
          ∫ y, testH σ b (ρ k) S (U k) y ∂db := by
      rw [← integral_div]
      exact integral_congr_ae (Filter.Eventually.of_forall fun bb => by simp only []; ring)
    rw [e1, hf, integral_congr_ae (Filter.Eventually.of_forall hpt), he, hprod, hc k]
    push_cast
    rw [Finset.prod_div_distrib]
    simp only [NNReal.coe_one, Complex.ofReal_one, one_mul, mul_one]
    rw [div_mul_div_comm]
  have lim1 : Filter.Tendsto (fun k => ∫ bb, (fouH σ ψ db (testH σ b (ρ k) S (U k)) bb /
        ∫ y, testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) bb * chiT σ ψ T bb) ∂db) Filter.atTop
      (nhds (coefSN σ b J ψ dx db (pureN φ A) T S)) := by
    have hχ : Continuous (chiT σ ψ T) := GlobalTheory.T.continuous_fourier_character_of_matrix F E σ hCM M J hJ n h2n ψ hψ T
    refine tendsto_integral_of_dominated_convergence (fun bb => ‖starN σ J ψ dx (pureN φ A) bb‖) ?_ hstar.norm ?_ ?_
    · intro k
      exact ((hI k).1.div_const _).aestronglyMeasurable.mul (hstar.aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    · intro k
      refine Filter.Eventually.of_forall fun bb => ?_
      rw [norm_mul, norm_mul, show ‖chiT σ ψ T bb‖ = 1 from hψ.2.1 _, mul_one, norm_div]
      exact mul_le_of_le_one_left (norm_nonneg _)
        ((div_le_one (norm_pos_iff.2 (hck k))).2 (hbd k bb))
    · refine Filter.Eventually.of_forall fun bb => ?_
      exact (hlim bb).mul_const _
  have lim2 := hInf.2.mul (tendsto_finsetProd S fun v _ =>
    (Complex.continuous_ofReal.tendsto _).comp (hV v).2)
  exact tendsto_nhds_unique lim1 (lim2.congr fun k => by simpa using (key k).symm)

theorem pure_identity (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (h2n : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (hInt : ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Integrable (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ) db)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf)
    (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (hdet : T.det ≠ 0)
    (hEu : GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hφ : IsSchwartzArch φ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v)) (hAl : ∀ v, v ∉ S₀ → A v = latV b v) :
    Integrable (pureN φ A) I ∧ coefN σ J ψ dx db (pureN φ A) T = ∫ X, pureN φ A X ∂I := by
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.euler_product_measure_eventually_standard F E M n d b _ 1 _ _ hEu
  obtain ⟨S₂, hS₂⟩ := coefS_pure σ hCM J hJ h2n ψ hψ dx hdx db hdb hInt d b laminf lam hinf hlam minf hminf m hm T hT hdet
  have hu : ∀ (R : Type) [CommRing R] [Algebra F R],
      IsUnit (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
    intro R _ _
    have h : (hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det = inclR R T.det :=
      ((inclR R).map_det T).symm
    rw [h]
    exact (IsUnit.mk0 _ hdet).map (inclR R)
  obtain ⟨hφm, hφi, -⟩ := GlobalTheory.T.archimedean_gram_fibre_measure_formula F E σ hCM M J hJ n h2n d b laminf hinf minf hminf _ (hu _) φ hφ
  have hφi' := hφi.self_of_nhds
  have hΦSB : IsSchwartzBruhat (pureN φ A) := GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n d b S₀ φ A hφ hA hAl
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    hInt _ hΦSB
  have hlimC := GlobalTheory.T.siegel_eisenstein_unfolding_identity F E σ hCM M J hJ n h2n ψ hψ dx db _ hstar d b T
  have hsum := hEu.2.1
  have htail := GlobalTheory.T.tendsto_tail_infinite_product_one _ hsum
  have hfin := fun v => GlobalTheory.T.local_gram_fibre_measure_standard_volume F E σ hCM M J hJ n h2n d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (hu _) (A v) (hA v).1 (hA v).2
  refine ⟨?_, ?_⟩
  · have hs : S₁ ⊆ S₀ ∪ S₁ := Finset.subset_union_right
    exact (hS₁ (S₀ ∪ S₁) hs φ hφm hφi' A (fun v => (hfin v).1) (fun v => (hfin v).2)
      (fun v hv => hAl v fun h => hv (Finset.mem_union_left _ h))).1
  have hev : ∀ᶠ S in Filter.atTop, S₀ ∪ S₁ ∪ S₂ ⊆ S := Filter.eventually_ge_atTop _
  have hlim2 : Filter.Tendsto (fun S => coefSN σ b J ψ dx db (pureN φ A) T S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ))
      Filter.atTop (nhds (coefN σ J ψ dx db (pureN φ A) T * ((1 : ℝ) : ℂ))) :=
    hlimC.mul ((Complex.continuous_ofReal.tendsto _).comp htail)
  have hconst : ∀ᶠ S in Filter.atTop, coefSN σ b J ψ dx db (pureN φ A) T S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ) =
      ∫ X, pureN φ A X ∂I := by
    filter_upwards [hev] with S hS
    have hs0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
    have hs1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
    have hs2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
    have hAS : ∀ v, v ∉ S → A v = latV b v := fun v hv => hAl v fun h => hv (hs0 h)
    rw [hS₂ S hs2 φ hφ A hA hAS, (hS₁ S hs1 φ hφm hφi' A (fun v => (hfin v).1) (fun v => (hfin v).2) hAS).2]
    simp
  have := tendsto_nhds_unique (hlim2.congr' hconst) tendsto_const_nhds
  simpa using this

theorem coefN_sum (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (h2n : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (hInt : ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Integrable (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ) db)
    (T : Matrix (Fin n) (Fin n) E) (N : ℕ) (Φ : Fin N → (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (hΦ : ∀ i, IsSchwartzBruhat (Φ i)) :
    GlobalTheory.CompanionTheory.SiegelND.coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, GlobalTheory.CompanionTheory.SiegelND.coefN σ J ψ dx db (Φ i) T := by
  have hstar : ∀ y, GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx (fun X => ∑ i, Φ i X) y =
      ∑ i, GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx (Φ i) y := by
    intro y
    unfold GlobalTheory.CompanionTheory.SiegelND.starN
    simp only [Finset.sum_mul]
    exact integral_finsetSum _ fun i _ => GlobalTheory.T.twisted_schwartz_function_integrable F E σ hCM M J n ψ hψ dx hdx.1 (Φ i) (hΦ i) y
  have hχ : Continuous (chiT σ ψ T) := GlobalTheory.T.continuous_fourier_character_of_matrix F E σ hCM M J hJ n h2n ψ hψ T
  have hi : ∀ i, Integrable (fun y => GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx (Φ i) y * chiT σ ψ T y) db := fun i =>
    (hInt _ (hΦ i)).mul_bdd (c := 1) hχ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => le_of_eq (hψ.2.1 _))
  show ∫ y, GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx (fun X => ∑ i, Φ i X) y * chiT σ ψ T y ∂db =
    ∑ i, ∫ y, GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx (Φ i) y * chiT σ ψ T y ∂db
  simp only [hstar, Finset.sum_mul]
  exact integral_finsetSum _ fun i _ => hi i

end Pure

end PositivityTheory.PfWsf.Hand.CoreH

end Body

section Final

open GlobalTheory.CompanionTheory.SiegelND.Coef

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem PositivityTheory.PfWsf.Hand.CoreH.coreH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  (∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → Integrable (starN σ J ψ dx Φ) db) →
  ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)),
    μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ T : Matrix (Fin n) (Fin n) E, (∀ a b, σ (T b a) = T a b) → T.det ≠ 0 →
    coefN σ J ψ dx db Φ T = ∫ X, Φ X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n h2n ψ hψ dx hdx db hdb hInt μ 𝓕 hμ h𝓕 Φ hΦ T hT hdet
  classical
  let b := Module.finBasis F E
  obtain ⟨laminf, hinf⟩ := GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdInf F
  choose lam hlam using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV F
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  obtain ⟨minf, hminf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM J hJ (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1) b laminf hinf.1 n
  choose m hm using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) b (lam v) (hlam v).1 n
  have hEu : GlobalTheory.CompanionTheory.SW.IsEulerProd b (GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) 1
      (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) :=
    GlobalTheory.T.siegel_weil_measure_of_rank_small_or_zero F E σ hCM n M J hJ (by omega) T hT hdet _ b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  obtain ⟨N, φ, A, S, hφ, hA, hAl, hsum⟩ := GlobalTheory.T.schwartz_bruhat_finite_sum_of_products F E σ hCM M J hJ n h2n _ b Φ hΦ
  have hSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Coef.pureN (φ i) (A i)) := fun i =>
    GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n _ b S (φ i) (A i) (hφ i) (hA i) (hAl i)
  have hΦe : Φ = fun X => ∑ i, Coef.pureN (φ i) (A i) X := funext hsum
  have hP := fun i => PositivityTheory.PfWsf.Hand.CoreH.pure_identity σ hCM J hJ h2n ψ hψ dx hdx db hdb hInt _ _ b laminf lam hinf hlam minf hminf m hm
    T hT hdet hEu S (φ i) (hφ i) (A i) (hA i) (hAl i)
  have e1 : ∫ X, Φ X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) =
      ∑ i, ∫ X, Coef.pureN (φ i) (A i) X ∂(GlobalTheory.CompanionTheory.SW.thetaMeas σ J μ 𝓕 {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T}) := by
    simp only [hsum]
    exact integral_finsetSum _ fun i _ => (hP i).1
  rw [e1, hΦe, PositivityTheory.PfWsf.Hand.CoreH.coefN_sum σ hCM J hJ h2n ψ hψ dx hdx db hdb hInt T N _ hSB]
  exact Finset.sum_congr rfl fun i _ => (hP i).2

end Final
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfWsf.Hand.Merge

theorem siegelND : PositivityTheory.GramSchwartzFunctions.BC.SiegelND := by
  intro D r V ψ θ μ lam ν φ hyp β hβ
  obtain ⟨hr, hψ, hθ, hμ, hlam, hν, hφ, habs⟩ := hyp
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  obtain ⟨μH, 𝓕, hμH, h𝓕, -⟩ := GlobalTheory.Published.SiegelOneVector.exists_normalised D.sp.cm.sig V.gram hCM hJ
  obtain ⟨dx, db, hdx, hdb, hW⟩ := GlobalTheory.T.exists_self_dual_siegel_weil_measures D r V ψ hψ μ hμ lam hlam
  have hT : ∀ a b, D.sp.cm.sig (β.1 b a) = β.1 a b := fun a b => by
    have := congrFun (congrFun β.2 a) b
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  have hInt := fun Φ hΦ => PositivityTheory.PfWsf.Hand.TupleUntupling.hermitian_unfolding_integral r V ψ hψ θ hθ μ hμ lam hlam hr dx hdx.1 db hdb.1 Φ hΦ
  have hc := PositivityTheory.PfWsf.Hand.CoreH.coreH D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr ψ hψ dx hdx db hdb
    hInt μH 𝓕 hμH h𝓕 _ (GlobalTheory.T.schwartz_function_schwartz_bruhat D θ hθ V.rank r φ hφ) β.1 hT hβ
  rw [GlobalTheory.T.frame_integral_eq_theta_part_nondegenerate D r V θ hθ ν hν φ hφ habs μH 𝓕 hμH h𝓕 β hβ, hW φ β, hc]
  rfl

end PositivityTheory.PfWsf.Hand.Merge
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellOfPoissonSiegel
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel

theorem bigCell_of_poisson_siegel :
    (∀ (D : Formalism.BasicNotions.D7) (r : ℕ), ∃ (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)) (𝓖 : Set (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)), PositivityTheory.GramSchwartzFunctions.BC.IsCovolOneH lam 𝓖) → PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm → (∀ (D : Formalism.BasicNotions.D7) (r : ℕ) (V : Formalism.BasicNotions.TH.HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → HasSum (fun β : PositivityTheory.GramSchwartzFunctions.HermE D r => PositivityTheory.GramSchwartzFunctions.BC.IfrB V ν φ β) (PositivityTheory.GramSchwartzFunctions.Ifr V ν φ)) → PositivityTheory.GramSchwartzFunctions.BC.SiegelND → PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg → PositivityTheory.GramSchwartzFunctions.BigCell := by
  intro hlam hP hG hND hDeg D r V h2r ψ hψ θ hθ μ 𝓕 h𝓕 ν hν φ hφ habs hsum
  obtain ⟨lam, 𝓖, hlg⟩ := hlam D r
  have hyp : Hyp D r V ψ θ μ lam ν φ :=
    ⟨h2r, hψ, hθ, ⟨𝓕, h𝓕⟩, ⟨𝓖, hlg⟩, hν, hφ, habs⟩
  have h1 := hP D r V ψ θ μ lam ν φ hyp hsum
  have h2 := hG D r V θ hθ ν hν φ hφ habs
  have h3 : (fun β : HermE D r => IfrB V ν φ β) = fun β : HermE D r => W ψ V μ lam φ β := by
    funext β
    by_cases hβ : β.1.det = 0
    · exact hDeg D r V ψ θ μ lam ν φ hyp β hβ
    · exact hND D r V ψ θ μ lam ν φ hyp β hβ
  rw [h3] at h2
  have h4 := h1.unique h2
  have h5 := hsum.hasSum
  rwa [h4] at h5

end GlobalTheory.CompanionTheory.WeilSiegel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSiegelFormulaOfChaptersLI
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsThetaIntLtTopOfEqZero
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelAssembly

theorem two_mul_finrank_isotropic_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E)
    (W : Submodule E B.V) (hW : ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0) : 2 * Module.finrank E W ≤ B.rank := by
  let b := Module.finBasis E W
  have hl : LinearIndependent E fun i => B.hT (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h1 : B.hT ((∑ i, star (c i) • b i : W) : B.V) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc]; simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]
    have h2 : (∑ i, star (c i) • b i : W) = 0 := Subtype.ext (B.nondeg.1 _ fun y => by rw [h1]; rfl)
    simpa using Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i
  have h3 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range fun i => B.hT (b i)))
  rw [finrank_span_eq_card hl, Fintype.card_fin, B.rank_eq] at h3
  have h4 : W ≤ (Submodule.span E (Set.range fun i => B.hT (b i))).dualCoannihilator := fun y hy => by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact hW _ (b i).2 _ hy
    | zero => rfl
    | add _ _ _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]
    | smul _ _ _ h => rw [LinearMap.smul_apply, h, smul_zero]
  have := Submodule.finrank_mono h4
  omega

theorem bddAbove_isotropic_dims {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    BddAbove {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0} :=
  ⟨B.rank, by rintro _ ⟨W, rfl, hW⟩; have := two_mul_finrank_isotropic_le B W hW; omega⟩

theorem two_mul_wittIdx_le_rank {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    2 * Formalism.MainNotions.SchurIrreducible.wittIdx B ≤ B.rank := by
  obtain ⟨W, h, hW⟩ := Nat.sSup_mem (s := {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧
    ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0}) ⟨_, ⊥, rfl, by simp⟩ (bddAbove_isotropic_dims B)
  rw [Formalism.MainNotions.SchurIrreducible.wittIdx, ← h]
  exact two_mul_finrank_isotropic_le B W hW

theorem exists_isRowBasis {D : D7} {n : ℕ} (U : Submodule D.host.E (Fin n → D.host.E)) :
    ∃ c, IsRowBasis U c := by
  refine ⟨fun i => ((Module.finBasis D.host.E U i : U) : Fin n → D.host.E), ?_, ?_⟩
  · exact (Module.finBasis D.host.E U).linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · have : Set.range (fun i => ((Module.finBasis D.host.E U i : U) : Fin n → D.host.E)) =
        U.subtype '' Set.range (Module.finBasis D.host.E U) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, (Module.finBasis D.host.E U).span_eq, Submodule.map_subtype_top]

theorem absThetaInt_lt_top_of_eq_zero {D : D7} (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {r : ℕ}
    (hr : r = 0) (φ : Mx D V.rank r → ℂ) : GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ := by
  subst hr
  have hc : ∀ h, GlobalTheory.SiegelFormula.absTheta V φ h = ‖φ 0‖ₑ := by
    intro h
    unfold GlobalTheory.SiegelFormula.absTheta
    haveI : Unique (Matrix (Fin V.rank) (Fin 0) D.host.E) :=
      inferInstanceAs (Unique (Fin V.rank → Fin 0 → D.host.E))
    rw [tsum_eq_single default (fun b hb => absurd (Subsingleton.elim b default) hb)]
    have h0 : GlobalTheory.SiegelFormula.invPt V h (default : Matrix (Fin V.rank) (Fin 0) D.host.E) = 0 := by
      funext i j; exact j.elim0
    rw [h0]
  unfold GlobalTheory.SiegelFormula.absThetaInt
  have hq : ∀ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q = ‖φ 0‖ₑ := fun q => hc _
  simp_rw [hq, lintegral_const]
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

end GlobalTheory.CompanionTheory.SiegelAssembly

namespace GlobalTheory.CompanionTheory.SiegelAssembly

end GlobalTheory.CompanionTheory.SiegelAssembly
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelAssemblyLI

open GlobalTheory.CompanionTheory.SiegelAssembly

theorem weilSiegelFormula_of_chapters_LI : GlobalTheory.Published.WeilThetaConvergence → GlobalTheory.Published.WeilEisensteinSiegelConvergence →
    PullSchLI → EisCells → ThetaOrbits → BigCell → GlobalTheory.Published.WeilSiegelFormula := by
  intro hTh hES hP hE hT hB D n V hn h2n ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω ν hν Φ
  haveI := hν
  have hw : 2 * Formalism.MainNotions.SchurIrreducible.wittIdx V ≤ V.rank := two_mul_wittIdx_le_rank V
  have hSet : HidaSetting D n V ψ χ θ μ ω := ⟨hn, h2n, hψ, hχ, hη, hθ, ⟨𝓕, hμ⟩, hω⟩
  have hconv := hES D n V hn h2n ψ hψ χ hχ hη θ hθ μ 𝓕 hμ ω hω Φ
  choose μr 𝓕r hμr using fun r => GlobalTheory.MixModel.exists_isCovolOne D V.rank r
  choose c hc using fun U : Submodule D.host.E (Fin n → D.host.E) => exists_isRowBasis U
  have hEis := hE D n V ψ χ θ μ ω hSet Φ hconv μr (fun r => ⟨𝓕r r, hμr r⟩) c hc
  have hfib : ∀ U : Submodule D.host.E (Fin n → D.host.E),
      HasSum (fun b : HermE D (Module.finrank D.host.E U) => J ψ V (μr _) (pull (c U) Φ.1) b)
        (Ifr V ν (pull (c U) Φ.1)) := by
    intro U
    have hr : Module.finrank D.host.E U ≤ n := by
      have := Submodule.finrank_le U
      simpa using this
    have hpull := hP D θ hθ V.rank _ n (c U) (hc U).1 Φ.1 Φ.2
    have habs : GlobalTheory.SiegelFormula.absThetaInt V ν (pull (c U) Φ.1) < ⊤ := by
      rcases Nat.eq_zero_or_pos (Module.finrank D.host.E U) with h0 | hpos
      · exact absThetaInt_lt_top_of_eq_zero V ν h0 _
      · exact hTh D _ V hpos (Or.inr (by omega)) θ hθ ν hν ⟨_, hpull⟩
    exact hB D _ V (by omega) ψ hψ θ hθ (μr _) (𝓕r _) (hμr _) ν hν _ hpull habs
      (hEis.summable.sigma_factor U)
  exact (hEis.sigma hfib).unique
    (hT D n V θ hθ ν hν Φ (hTh D n V hn (Or.inr (by omega)) θ hθ ν hν Φ) c hc)

end GlobalTheory.CompanionTheory.SiegelAssemblyLI
end
end

namespace PositivityTheory.PfWsf.Top

theorem pull : PositivityTheory.GramSchwartzFunctions.PullSchLI := GlobalTheory.CompanionTheory.PullSch.pullSchLI
theorem orb : PositivityTheory.GramSchwartzFunctions.ThetaOrbits := GlobalTheory.CompanionTheory.ThetaOrbit.thetaOrbits

theorem head_of_two (hE : PositivityTheory.GramSchwartzFunctions.EisCells) (hB : PositivityTheory.GramSchwartzFunctions.BigCell) : GlobalTheory.Published.WeilSiegelFormula :=
  GlobalTheory.CompanionTheory.SiegelAssemblyLI.weilSiegelFormula_of_chapters_LI
    (GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary)
    GlobalTheory.WeilEisConv.weilEisensteinSiegelConvergence pull hE orb hB

theorem big_of_three (h1 : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm) (h2 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND) (h3 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) :
    PositivityTheory.GramSchwartzFunctions.BigCell :=
  GlobalTheory.CompanionTheory.WeilSiegel.bigCell_of_poisson_siegel GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH h1 GlobalTheory.CompanionTheory.SplitGram.hasSum_IfrB h2 h3

end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_three (h4 : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm) (h5 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND)
    (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_two GlobalTheory.CompanionTheory.EisCellsChapter.eisCells (big_of_three h4 h5 h6)
end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_siegel (h5 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND) (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_three GlobalTheory.CompanionTheory.HermPoisson.poissonHerm_main h5 h6
end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_deg (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_siegel PositivityTheory.PfWsf.Hand.Merge.siegelND h6
end PositivityTheory.PfWsf.Top
