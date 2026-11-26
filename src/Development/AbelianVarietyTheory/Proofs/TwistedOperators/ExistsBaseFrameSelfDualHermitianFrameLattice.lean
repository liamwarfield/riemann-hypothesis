module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseFrameSelfDualHermitianFrameLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseFrameSelfDualHermitianFrameLattice
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.SelfDualBaseFrame

theorem exists_baseFrame_frameLat : ∀ (D : D7) (V : HSp D), ∃ β₀ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D), IsSDFrame V β₀ (frameLat V) 1 ∧ IsBaseFrame V β₀ (frameLat V) 1 := by
  intro D V
  have hl : frameLat V = GlobalTheory.Member.latC V :=
    SetLike.coe_injective ((GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice V).symm.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  have hd : Formalism.L2.Herm.dualL D.sp.cm V (frameLat V) = frameLat V := by
    rw [hl]; exact Formalism.L2.Herm.coordinate_lattice_self_dual D.sp.cm V
  obtain ⟨β, c, hc⟩ := GlobalTheory.AdelicFrame.exists_isSDFrame D V (frameLat V) (GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice V).symm hd
  rw [one_pow] at hc
  exact ⟨β, ⟨0, by rwa [pow_zero]⟩, hc⟩

end GlobalTheory.SelfDualBaseFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseFrameSelfDualHermitianFrameLatticeStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice : ∀ (D : D7) (V : HSp D), ∃ β₀ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D), IsSDFrame V β₀ (frameLat V) 1 ∧ IsBaseFrame V β₀ (frameLat V) 1 := by
  first | exact @GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat | exact GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat | (intros; apply GlobalTheory.SelfDualBaseFrame.exists_baseFrame_frameLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesMultiplicity
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesMultiplicity
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TestFnCusp

theorem hypH_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (h : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ := by
  intro a ha har
  obtain ⟨v, hv⟩ := h.2 a ha har
  refine ⟨v, fun y hy => hv y fun g hg => hy g ?_⟩
  intro i j hij
  by_contra hc
  exact hij (hg i j hc)

theorem isCuspidalOp_tensor : (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ (tensor D.sp.cm.sig V.gram fa ff) := by
  intro hCO hPC D V lam S M T U μa μf μ _ _ fa ff hTD
  obtain ⟨hodd, -, -, hnf, hμ, ha, hb⟩ := hTD
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hμ.haar_loc
  have hT : IsTestFnG M T U μa μf (tensor D.sp.cm.sig V.gram fa ff) := ⟨fa, ff, ha, hb, rfl⟩
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V := hT.isPureTensor.2
  have hU := hPC.2 D V hodd S M T (hypH_of_noFixed T hnf) U μa μf _ hT
  refine hCO D V μ _ hf ?_ ?_
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).1 ν x y).2
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).2 ν x y).2

end GlobalTheory.TestFnCusp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesMultiplicityStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_multiplicity : (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ (tensor D.sp.cm.sig V.gram fa ff) := by
  first | exact @GlobalTheory.TestFnCusp.isCuspidalOp_tensor | exact GlobalTheory.TestFnCusp.isCuspidalOp_tensor | (intros; apply GlobalTheory.TestFnCusp.isCuspidalOp_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorConvolutionAndLeftTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorConvolutionAndLeftTranslate
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

open scoped Pointwise

namespace GlobalTheory.OpConv

theorem isIntegralOp_conv_and_translate : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth σ → ∀ f ∈ GlobalTheory.SplitWeil.SB G, ∀ f' ∈ GlobalTheory.SplitWeil.SB G, ∀ A B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f A → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f' B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (conv μ f f') (A ∘ₗ B) ∧ ∀ g : G, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (fun x => f' (g⁻¹ * x)) (σ g ∘ₗ B) := by
  intro G _ _ _ _ _ _ μ _ W _ _ σ hσ f hf f' hf' A B hA hB
  have hfc : Continuous f := hf.1.continuous
  have hf'c : Continuous f' := hf'.1.continuous
  have horb : ∀ (l : Module.Dual ℂ W) (v : W), Continuous fun y => l (σ y v) := fun l v =>
    ((hσ.isLocallyConstant_orbit v).comp l).continuous
  refine ⟨fun v l => ?_, fun g v l => ?_⟩
  ·
    have h0 : ∀ x y : G, (x, y) ∉ tsupport f ×ˢ (tsupport f * tsupport f') →
        f x * f' (x⁻¹ * y) = 0 := by
      intro x y h
      by_contra hne
      have h1 := subset_tsupport f (left_ne_zero_of_mul hne)
      have h2 := subset_tsupport f' (right_ne_zero_of_mul hne)
      exact h ⟨h1, x, h1, _, h2, by simp⟩
    have hK : IsCompact (tsupport f ×ˢ (tsupport f * tsupport f')) := hf.2.prod (hf.2.mul hf'.2)
    have hcont : Continuous fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ := by
      refine continuousOn_univ.1 (continuousOn_integral_of_compact_support
        (f := fun y x => f x * f' (x⁻¹ * y)) (s := Set.univ) hf.2 ?_ fun y x _ hx => ?_)
      · exact ((hfc.comp continuous_snd).mul
          (hf'c.comp (continuous_snd.inv.mul continuous_fst))).continuousOn
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have hcs : HasCompactSupport fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ :=
      HasCompactSupport.intro (hf.2.mul hf'.2) fun y hy => by
        simp [fun x => h0 x y fun h => hy h.2]
    have hF : Continuous (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * l (σ y v)) :=
      ((hfc.comp continuous_fst).mul (hf'c.comp (continuous_fst.inv.mul continuous_snd))).mul
        ((horb l v).comp continuous_snd)
    have hFc : HasCompactSupport (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * l (σ y v)) :=
      HasCompactSupport.intro hK fun p hp => by simp [Function.uncurry, h0 p.1 p.2 hp]
    have hconv : conv μ f f' = fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ := rfl
    rw [hconv]
    refine ⟨(hcont.mul (horb l v)).integrable_of_hasCompactSupport (hcs.mul_right), ?_⟩
    have hx : ∀ x, l (σ x (B v)) = ∫ y, f' (x⁻¹ * y) * l (σ y v) ∂μ := by
      intro x
      have := (hB v (l ∘ₗ σ x)).2
      simp only [LinearMap.comp_apply] at this
      rw [this, ← integral_mul_left_eq_self (fun y => f' (x⁻¹ * y) * l (σ y v)) x]
      refine integral_congr_ae (.of_forall fun y => ?_)
      simp [map_mul, Module.End.mul_apply]
    rw [LinearMap.comp_apply, (hA (B v) l).2]
    simp_rw [hx, ← integral_const_mul, ← mul_assoc]
    rw [integral_integral_swap_of_hasCompactSupport hF hFc]
    simp_rw [integral_mul_const]
  ·
    have hx : ∀ y, f' y * l (σ g (σ y v)) = (fun x => f' (g⁻¹ * x) * l (σ x v)) (g * y) := by
      intro y
      simp [map_mul, Module.End.mul_apply]
    have hc : Continuous fun x => f' (g⁻¹ * x) * l (σ x v) :=
      (hf'c.comp (continuous_const.mul continuous_id)).mul (horb l v)
    have hs : HasCompactSupport fun x => f' (g⁻¹ * x) * l (σ x v) :=
      ((hf'.2.comp_homeomorph (Homeomorph.mulLeft g⁻¹))).mul_right
    refine ⟨hc.integrable_of_hasCompactSupport hs, ?_⟩
    have := (hB v (l ∘ₗ σ g)).2
    simp only [LinearMap.comp_apply] at this
    rw [LinearMap.comp_apply, this,
      ← integral_mul_left_eq_self (fun x => f' (g⁻¹ * x) * l (σ x v)) g]
    exact integral_congr_ae (.of_forall fun y => hx y)

end GlobalTheory.OpConv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorConvolutionAndLeftTranslateStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_convolution_and_leftTranslate : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth σ → ∀ f ∈ GlobalTheory.SplitWeil.SB G, ∀ f' ∈ GlobalTheory.SplitWeil.SB G, ∀ A B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f A → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f' B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (conv μ f f') (A ∘ₗ B) ∧ ∀ g : G, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (fun x => f' (g⁻¹ * x)) (σ g ∘ₗ B) := by
  first | exact @GlobalTheory.OpConv.isIntegralOp_conv_and_translate | exact GlobalTheory.OpConv.isIntegralOp_conv_and_translate | (intros; apply GlobalTheory.OpConv.isIntegralOp_conv_and_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRegularSemisimpleOfTestFunctionNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRegularSemisimpleOfTestFunctionNeZero
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer

open GlobalTheory.Orb

namespace GlobalTheory.RegSupp

theorem mem_iwahori_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    {g : GL (Fin n) (Fv F v)} :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    g ∈ GlobalTheory.SmGL.iwahori (Fv F v) (Fin n) → g ∈ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.iwahori (Fv F v) n := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  intro hg
  haveI hc : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he : (ValuativeRel.valuation (Fv F v)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  have hle : (ValuativeRel.valuation (Fv F v)).integer ≤ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.Int (Fv F v) :=
    fun x hx => he.le_one_iff_le_one.1 hx
  refine Subgroup.mem_map.2 ⟨Matrix.GeneralLinearGroup.map (Subring.inclusion hle) h, ?_, ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.mem_iwahoriInt_iff]
    intro i j hij
    have hb := (Subgroup.mem_comap.1 hh) (i := i) (j := j) (by
      rw [show i = (GlobalTheory.SmGL.points (Fin n)) ⟨i, ()⟩ from rfl, show j = (GlobalTheory.SmGL.points (Fin n)) ⟨j, ()⟩ from rfl,
        GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
      exact hij)
    change IsLocalRing.residue _ (h.1 i j) = 0 at hb
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers _).isUnit_iff_valuation_eq_one] at hb
    have h1 : ValuativeRel.valuation (Fv F v) ((h.1 i j : _) : Fv F v) < 1 :=
      lt_of_le_of_ne (h.1 i j).2 hb
    exact he.lt_one_iff_lt_one.1 h1
  · ext i j
    rfl

end GlobalTheory.RegSupp

namespace GlobalTheory.RegSupp

theorem isRegSS_of_tensor_ne_zero : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (δ : GF V) (x : GA D V), tensor D.sp.cm.sig V.gram fa ff (x⁻¹ * rat V δ * x) ≠ 0 → IsRegSS δ.1.1 := by
  intro hI D V T U μf ff hT fa δ x h
  obtain ⟨-, -, ⟨t, ht, hfu⟩, -, hcof⟩ := hT
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  have hfin : (Function.mulSupport fun v =>
      ff v (proj D.sp.cm.sig V.gram v (x⁻¹ * rat V δ * x))).Finite :=
    Filter.eventually_cofinite.1 ((hcof.and (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V)
      (x⁻¹ * rat V δ * x))).mono fun v hv => by
        show ff v _ = 1
        rw [hv.1, unitLoc, Set.indicator_of_mem hv.2, Pi.one_apply])
  have hne : ff U.u (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x)) ≠ 0 := by
    intro h0
    apply h
    show (∏ w, fa w (projArch D.sp.cm.sig V.gram w _)) * ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v _) = 0
    rw [finprod_eq_zero _ U.u h0 hfin, mul_zero]
  rw [hfu] at hne
  have hmem := Set.mem_of_indicator_ne_zero hne
  obtain ⟨A, hA, rfl⟩ := ht
  obtain ⟨a, ha, b, hb, e⟩ := U.frame.mem_iwahoriCoset.1 hmem
  have key := (hI _ (U.ϖ : Fv _ U.u) U.unif _ A hA
    (U.frame.equiv (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x))).1
    ⟨a, mem_iwahori_valued U.u ha, b, mem_iwahori_valued U.u hb, by
      rw [e, Units.val_mul, Units.val_mul, GlobalTheory.SmGL.val_diagT]
      congr 2
      unfold GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.diagPow
      congr 1
      funext i
      exact Units.val_zpow_eq_zpow_val _ _⟩).2
  have e1 : U.frame.equiv (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x)) =
      (U.frame.equiv (proj D.sp.cm.sig V.gram U.u x))⁻¹ * U.frame.equiv (proj D.sp.cm.sig V.gram U.u (rat V δ)) *
        U.frame.equiv (proj D.sp.cm.sig V.gram U.u x) := by
    simp only [map_mul, map_inv]
  rw [e1, charpoly_conj_GL] at key
  change (splitEquivIn _ _ U.frame.emb U.frame.basis _).1.charpoly.Separable at key
  rw [splitEquivIn_apply, charpoly_conj_GL, splitHom_val, rat, proj_ratEmb,
    show (matHom _ D.sp.cm.sig V.gram (ratLoc D.sp.cm.sig V.gram U.u δ)).1 = δ.1.1.map (inclR _) from rfl,
    Matrix.map_map, show (splitProj U.frame.emb) ∘ (inclR (Fv _ U.u)) = (U.frame.emb : _ →+* Fv _ U.u) from
      funext (splitProj_inclR _), Matrix.charpoly_map] at key
  exact (Polynomial.separable_map _).1 key

end GlobalTheory.RegSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRegularSemisimpleOfTestFunctionNeZeroStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularSemisimple_of_testFunction_ne_zero : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (δ : GF V) (x : GA D V), tensor D.sp.cm.sig V.gram fa ff (x⁻¹ * rat V δ * x) ≠ 0 → IsRegSS δ.1.1 := by
  first | exact @GlobalTheory.RegSupp.isRegSS_of_tensor_ne_zero | exact GlobalTheory.RegSupp.isRegSS_of_tensor_ne_zero | (intros; apply GlobalTheory.RegSupp.isRegSS_of_tensor_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalUnitaryGroupIsoConjIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalUnitaryGroupIsoConjIsometry
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocIsoConj

open Formalism.UG

theorem conj_unitary {R : Type} [CommRing R] (σ : R →+* R) {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1)
    (J : Matrix n n R) (J' : Matrix m m R) (hJ : cT σ a * J' * a = J) (g : Matrix n n R)
    (hg : cT σ g * J * g = J) : cT σ (a * g * b) * J' * (a * g * b) = J' := by
  calc cT σ (a * g * b) * J' * (a * g * b) = cT σ b * (cT σ g * (cT σ a * J' * a) * g) * b := by
        rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT σ b * (cT σ a * J' * a) * b := by rw [hJ, hg]
    _ = cT σ (a * b) * J' * (a * b) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]

def conjHom {R : Type} [CommRing R] {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1) (hba : b * a = 1) :
    Matrix n n R →* Matrix m m R where
  toFun g := a * g * b
  map_one' := by rw [Matrix.mul_one, hab]
  map_mul' g h := by
    calc a * (g * h) * b = a * g * (b * a) * h * b := by rw [hba, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_equiv {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (σ : R →+* R)
    {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1) (hba : b * a = 1)
    (J : Matrix n n R) (J' : Matrix m m R) (hJ : cT σ a * J' * a = J) :
    ∃ φ : UJ σ J ≃ₜ* UJ σ J', ∀ g, ((φ g).1 : Matrix m m R) = a * (g.1 : Matrix n n R) * b := by
  have hJ' : cT σ b * J * b = J' := by
    rw [← hJ]
    calc cT σ b * (cT σ a * J' * a) * b = cT σ (a * b) * J' * (a * b) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hc : ∀ {k l : Type} [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l] (x : Matrix l k R)
      (y : Matrix k l R), Continuous fun g : Matrix k k R => x * g * y := by
    intro k l _ _ _ _ x y
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let φ₀ : UJ σ J →* GL m R := (Units.map (conjHom a b hab hba)).comp (UJ σ J).subtype
  let ψ₀ : UJ σ J' →* GL n R := (Units.map (conjHom b a hba hab)).comp (UJ σ J').subtype
  have hφU : ∀ g, φ₀ g ∈ UJ σ J' := fun g => conj_unitary σ a b hab J J' hJ _ g.2
  have hψU : ∀ g, ψ₀ g ∈ UJ σ J := fun g => conj_unitary σ b a hba J' J hJ' _ g.2
  let φ : UJ σ J →* UJ σ J' := φ₀.codRestrict _ hφU
  let ψ : UJ σ J' →* UJ σ J := ψ₀.codRestrict _ hψU
  have hφc : Continuous φ :=
    ((Continuous.units_map _ (hc a b)).comp continuous_subtype_val).subtype_mk _
  have hψc : Continuous ψ :=
    ((Continuous.units_map _ (hc b a)).comp continuous_subtype_val).subtype_mk _
  have l : ∀ g, ψ (φ g) = g := by
    intro g
    apply Subtype.ext; apply Units.ext
    show b * (a * (g.1 : Matrix n n R) * b) * a = g.1
    calc b * (a * (g.1 : Matrix n n R) * b) * a = (b * a) * (g.1 : Matrix n n R) * (b * a) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hba, Matrix.one_mul, Matrix.mul_one]
  have r : ∀ g, φ (ψ g) = g := by
    intro g
    apply Subtype.ext; apply Units.ext
    show a * (b * (g.1 : Matrix m m R) * a) * b = g.1
    calc a * (b * (g.1 : Matrix m m R) * a) * b = (a * b) * (g.1 : Matrix m m R) * (a * b) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hab, Matrix.one_mul, Matrix.mul_one]
  exact ⟨{ toFun := φ, invFun := ψ, left_inv := l, right_inv := r, map_mul' := map_mul φ,
            continuous_toFun := hφc, continuous_invFun := hψc }, fun g => rfl⟩

theorem exists_locIso : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E) (v : HeightOneSpectrum (𝓞 F)) (a : Matrix (Fin r') (Fin r) (Fv F v ⊗[F] E)) (b : Matrix (Fin r) (Fin r') (Fv F v ⊗[F] E)), a * b = 1 → b * a = 1 → Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a * JR (F := F) (Fv F v) J' * a = JR (F := F) (Fv F v) J → ∃ φ : GLoc σ J v ≃ₜ* GLoc σ J' v, ∀ g, (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val = a * (GlobalTheory.AdelicU.matHom _ σ J g).val * b := by
  intro F E _ _ _ _ _ σ r r' J J' v a b hab hba hJ
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨φ, hφ⟩ := exists_equiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a b hab hba _ _ hJ
  exact ⟨φ, hφ⟩

end GlobalTheory.LocIsoConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalUnitaryGroupIsoConjIsometryStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localUnitaryGroupIso_conj_isometry : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E) (v : HeightOneSpectrum (𝓞 F)) (a : Matrix (Fin r') (Fin r) (Fv F v ⊗[F] E)) (b : Matrix (Fin r) (Fin r') (Fv F v ⊗[F] E)), a * b = 1 → b * a = 1 → Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a * JR (F := F) (Fv F v) J' * a = JR (F := F) (Fv F v) J → ∃ φ : GLoc σ J v ≃ₜ* GLoc σ J' v, ∀ g, (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val = a * (GlobalTheory.AdelicU.matHom _ σ J g).val * b := by
  first | exact @GlobalTheory.LocIsoConj.exists_locIso | exact GlobalTheory.LocIsoConj.exists_locIso | (intros; apply GlobalTheory.LocIsoConj.exists_locIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleAdmissibleLocalComponentFiniteA
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleAdmissibleLocalComponentFiniteA
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.LocCompFin

open GlobalTheory.CuspRep.LocEx GlobalTheory.AutMult

section Groups

variable {D : D7} (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F))

theorem finLoc_locFin (x : Gv V u) : finLoc V u (locFin V u x) = x :=
  GlobalTheory.AdelicU.proj_emb_self _ _ u x

theorem commute_locFin (x : Gv V u) {g : GfC V} (hg : finLoc V u g = 1) : Commute (locFin V u x) g :=
  Subtype.ext (GlobalTheory.AdelicU.commute_emb _ _ x hg).eq

theorem continuous_locFin : Continuous (locFin V u) :=
  (GlobalTheory.AdelicU.continuous_emb _ _ u).subtype_mk _

theorem continuous_finLoc : Continuous (finLoc V u) :=
  (GlobalTheory.AdelicU.continuous_proj _ _ u).comp continuous_subtype_val

theorem finLoc_inv_mul (g : GfC V) : finLoc V u ((locFin V u (finLoc V u g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, finLoc_locFin, inv_mul_cancel]

end Groups

theorem exists_locComp : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (π : Representation ℂ (Gv V u) N),
      π.IsIrreducible ∧ IsAdmissible π ∧ FinHasLocComp V u π σ := by
  intro D V u W _ _ σ hirr hadm
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  obtain ⟨hnt, hinv⟩ := (GlobalTheory.CuspRep.isIrreducible_iff σ).1 hirr
  obtain ⟨x, hx0⟩ := exists_ne (0 : W)
  have hsplit : ∀ g (y : W), σ g y = σ (locFin V u (finLoc V u g)) (σ ((locFin V u (finLoc V u g))⁻¹ * g) y) :=
    fun g y => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hcomm : ∀ g : GfC V, finLoc V u g = 1 → ∀ h (y : W),
      σ g (σ (locFin V u h) y) = σ (locFin V u h) (σ g y) := by
    intro g hg h y
    rw [← Module.End.mul_apply, ← map_mul, ← (commute_locFin V u h hg).eq, map_mul, Module.End.mul_apply]
  have hρ : GlobalTheory.PRep.IsSmooth (σ.comp (locFin V u)) := fun v => (hadm.1 v).preimage (continuous_locFin V u)
  let K₀ : Subgroup (GfC V) := stab σ x
  have hK₀ : IsOpen (K₀ : Set (GfC V)) := hadm.1 x
  let Kc : Subgroup (Gv V u) := K₀.comap (locFin V u) ⊓ Kv V u
  have hKco : IsOpen (Kc : Set (Gv V u)) :=
    (hK₀.preimage (continuous_locFin V u)).inter (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ u)
  have hKcc : IsCompact (Kc : Set (Gv V u)) :=
    (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ u).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKco) fun k hk => hk.2
  have hKcK₀ : ∀ k ∈ Kc, locFin V u k ∈ K₀ := fun k hk => hk.1
  have hxKc : x ∈ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) Kc := mem_fix.2 fun k hk => hKcK₀ k hk
  have hnull : nullPart (σ.comp (locFin V u)) Kc = ⊥ := by
    rcases hinv (nullPart (σ.comp (locFin V u)) Kc) (fun g y hy => by
      rw [hsplit g y]
      exact nullPart_act _ Kc (finLoc V u g) (nullPart_comm _ Kc (σ _)
        (fun h z => hcomm _ (finLoc_inv_mul V u g) h z) hy)) with h | h
    · exact h
    · exact absurd (eq_zero_of_mem_nullPart hρ hKcc hxKc (h ▸ Submodule.mem_top)) hx0
  have h2 : ∀ Y : Submodule ℂ W, (∀ g, ∀ v ∈ Y, σ.comp (locFin V u) g v ∈ Y) →
      Y ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) Kc = ⊥ → Y = ⊥ :=
    fun Y hY h => le_bot_iff.1 (hnull ▸ le_nullPart hρ hKcc Y hY h)
  let L' : Subgroup (GfC V) := K₀ ⊓ (finLoc V u).ker
  let U : Submodule ℂ W := GlobalTheory.PRep.fixed σ L'
  have hU : ∀ g, ∀ v ∈ U, σ.comp (locFin V u) g v ∈ U := fun g v hv => mem_fix.2 fun k hk => by
    change σ k (σ (locFin V u g) v) = σ (locFin V u g) v
    rw [hcomm k hk.2 g v, mem_fix.1 hv k hk]
  have hU0 : U ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨x, mem_fix.2 fun k hk => hk.1, hx0⟩
  obtain ⟨C, hCo, hCc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  have hfin : ∀ K' : Subgroup (Gv V u), IsOpen (K' : Set (Gv V u)) →
      FiniteDimensional ℂ ↥(U ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) K') := by
    intro K' hK'
    let M : Subgroup (GfC V) := (K₀ ⊓ (Kc ⊓ K').comap (finLoc V u)) ⊓ C
    have hMo : IsOpen (M : Set (GfC V)) :=
      (hK₀.inter ((hKco.inter hK').preimage (continuous_finLoc V u))).inter hCo
    have hMc : IsCompact (M : Set (GfC V)) :=
      hCc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hMo) fun k hk => hk.2
    have := hadm.2 M hMo hMc
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.PRep.fixed σ M) fun v hv => mem_fix.2 fun k hk => ?_
    have hk1 : (locFin V u (finLoc V u k))⁻¹ * k ∈ L' :=
      ⟨K₀.mul_mem (K₀.inv_mem (hKcK₀ _ hk.1.2.1)) hk.1.1, finLoc_inv_mul V u k⟩
    rw [hsplit k v, mem_fix.1 hv.1 _ hk1]
    exact mem_fix.1 hv.2 _ hk.1.2.2
  obtain ⟨π, ⟨f, hf0, hf⟩, hπ⟩ := exists_irred hρ hKco h2 U hU hU0 hfin
  refine ⟨π.V, inferInstance, inferInstance, π.ρ, π.irred, hπ, ?_⟩
  let F : π.ρ.IntertwiningMap (σ.comp (locFin V u)) :=
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext (hf g) }
  have hI : ∀ g, ∀ y ∈ isoPartAlg π.ρ (σ.comp (locFin V u)), σ g y ∈ isoPartAlg π.ρ (σ.comp (locFin V u)) := by
    intro g y hy
    refine Submodule.iSup_induction _ (motive := fun y => σ g y ∈ isoPartAlg π.ρ (σ.comp (locFin V u))) hy ?_ ?_ ?_
    · rintro T _ ⟨z, rfl⟩
      let T' : π.ρ.IntertwiningMap (σ.comp (locFin V u)) :=
        { toLinearMap := σ ((locFin V u (finLoc V u g))⁻¹ * g) ∘ₗ T.toLinearMap
          isIntertwining' := fun h => LinearMap.ext fun w => by
            change σ _ (T (π.ρ h w)) = σ (locFin V u h) (σ _ (T w))
            rw [T.isIntertwining]
            exact hcomm _ (finLoc_inv_mul V u g) h _ }
      refine Submodule.mem_iSup_of_mem T' ⟨π.ρ (finLoc V u g) z, ?_⟩
      change T' (π.ρ (finLoc V u g) z) = σ g (T z)
      rw [T'.isIntertwining, hsplit g (T z)]
      rfl
    · simp only [map_zero]; exact zero_mem _
    · intro a b ha hb; simp only [map_add (f := _)]; exact add_mem ha hb
  rcases hinv _ hI with h | h
  · refine absurd ?_ hf0
    have hr : LinearMap.range F.toLinearMap ≤ ⊥ :=
      h ▸ le_iSup (fun T : π.ρ.IntertwiningMap (σ.comp (locFin V u)) => LinearMap.range T.toLinearMap) F
    exact LinearMap.range_eq_bot.1 (le_bot_iff.1 hr)
  · exact h

end GlobalTheory.LocCompFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleAdmissibleLocalComponentFiniteAStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_admissible_localComponent_finiteAdelic : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (π : Representation ℂ (Gv V u) N), π.IsIrreducible ∧ IsAdmissible π ∧ FinHasLocComp V u π σ := by
  first | exact @GlobalTheory.LocCompFin.exists_locComp | exact GlobalTheory.LocCompFin.exists_locComp | (intros; apply GlobalTheory.LocCompFin.exists_locComp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPart
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorFaceLevelEqPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorFaceLevelEqPrincipalLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevOpFace

theorem heckeOp_face_to_principal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (b : Bool) (i : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (B : Finset (GA D (Wc D i))), Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) SF P d B → Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF b i P d B hB
  have hS : OffS D SF P := by
    obtain ⟨_, _, _, _, hS, -⟩ := hB
    exact hS
  have hG : GlobalTheory.Hk3.Good R A.μ0 P := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.2.1 SF hSF P).1 hS
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hPP : ∀ L : LevelP R.Pg D.R.r ℂ, ∀ PP, PP ∈ (R.datWp i L).Pg ∨ PP ∈ (R.datWp i L).Q →
      PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := fun L PP h =>
    hG PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))
  have h1 := ((GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n)
    (R.datWp i (R.levL F b (sg0 D A))) hβ P hN (hPP _)).2.1 SF d B).1 hB
  exact ((GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P hN (hPP _)).2.1 SF d B).2 h1

end GlobalTheory.LevOpFace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorFaceLevelEqPrincipalLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_faceLevel_eq_principalLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (b : Bool) (i : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (B : Finset (GA D (Wc D i))), Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) SF P d B → Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B := by
  first | exact @GlobalTheory.LevOpFace.heckeOp_face_to_principal | exact GlobalTheory.LevOpFace.heckeOp_face_to_principal | (intros; apply GlobalTheory.LevOpFace.heckeOp_face_to_principal <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsNeProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 1000000 in
theorem exists_part (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hs : A.fam.Ok s) (hC : GlobalTheory.Hk3.Core R F)
    (hS : GlobalTheory.Hk3.SchurAll R) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hSF : GlobalTheory.Hk3.IsSF R SF) (b : Bool)
    (i : Fin D.R.m) (hi : R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥) :
    ∃ c, ∃ z ∈ GlobalTheory.Hk3.Wcc R SF i c, z ≠ 0 ∧ (R.HW i (sg0 D A)).e z ∈ R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) := by
  classical
  have irr : ∀ χ ∈ A.X, IsAbsIrrChar χ := hs.irr
  obtain ⟨y, hy, hy0⟩ := Submodule.ne_bot_iff _ |>.1 hi
  have hWall : R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≤ R.Wall i (sg0 D A) :=
    (GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _).trans inf_le_left
  have hR : LinearMap.range (R.HW i (sg0 D A)).e = R.Wall i (sg0 D A) := (hC.models.HW i (sg0 D A)).2.1
  obtain ⟨x, rfl⟩ : y ∈ LinearMap.range (R.HW i (sg0 D A)).e := hR ▸ hWall hy
  have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (map_zero _)
  obtain ⟨hxe, hxt⟩ := (GlobalTheory.WatType.wat_iff_type R F hs hC b i x).1 hy
  obtain ⟨h, -, -, -, hsup, hstab, -, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS irr SF hSF i
  obtain ⟨hidem, -, -, -⟩ := GlobalTheory.Hk3.eH_laws R F hC irr i
  obtain ⟨lam, hlam⟩ : ∃ lam : (F.lvl b).P → ℂ, ∀ p, lam p = sg0 D A ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) :=
    ⟨_, fun _ => rfl⟩
  have lam_mul : ∀ p q, lam (p * q) = lam p * lam q := fun p q => by
    simp only [hlam, map_mul, Units.val_mul]
  have lam_ne : ∀ p, lam p ≠ 0 := fun p => by rw [hlam]; exact (map_ne_zero _).2 (Units.ne_zero _)
  have hxt' : ∀ p : (F.lvl b).P, R.gW i (sg0 D A) (p : G) x = lam p • x := fun p => by rw [hlam]; exact hxt p
  obtain ⟨π, hπ⟩ : ∃ π : Module.End ℂ (R.HW i (sg0 D A)).H,
      ∀ w, π w = ∑ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G) w :=
    ⟨∑ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G), fun w => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]⟩
  have htype : ∀ w (q : (F.lvl b).P), R.gW i (sg0 D A) (q : G) (π w) = lam q • π w := by
    intro w q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hπ, map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun p => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, smul_smul, Equiv.coe_mulLeft]
    show (lam p)⁻¹ • R.gW i (sg0 D A) ((q : G) * p) w =
      (lam q * (lam (q * p))⁻¹) • R.gW i (sg0 D A) ((q * p : (F.lvl b).P) : G) w
    rw [lam_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (lam_ne q), one_mul]
    exact congrArg (fun g => (lam p)⁻¹ • R.gW i (sg0 D A) g w) (Subgroup.coe_mul _ q p).symm
  have hπmem : ∀ c w, w ∈ GlobalTheory.Hk3.Wcc R SF i c → π w ∈ GlobalTheory.Hk3.Wcc R SF i c := by
    intro c w hw
    rw [hπ]
    refine Submodule.sum_mem _ fun p _ => ?_
    refine Submodule.smul_mem _ _ ?_
    have h2 : R.gW i (sg0 D A) (p : G) w ∈ (GlobalTheory.Hk3.Wcc R SF i c).map (R.gW i (sg0 D A) (p : G)) :=
      Submodule.mem_map_of_mem hw
    exact hstab c (p : G) h2
  have hfix : π x = (Fintype.card (F.lvl b).P : ℂ) • x := by
    have h1 : ∀ p : (F.lvl b).P, (lam p)⁻¹ • R.gW i (sg0 D A) (p : G) x = x := fun p => by
      rw [hxt' p, smul_smul, inv_mul_cancel₀ (lam_ne p), one_smul]
    rw [hπ, Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hπx : π x ≠ 0 := by
    intro h0
    apply hx0
    have hc : (Fintype.card (F.lvl b).P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have h3 := congrArg (fun z => (Fintype.card (F.lvl b).P : ℂ)⁻¹ • z) (hfix.symm.trans h0)
    rwa [smul_zero, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
  have hxR := hsup.ge (LinearMap.mem_range.2 ⟨x, hxe⟩)
  have hmem := (Submodule.map_iSup π (fun c => GlobalTheory.Hk3.Wcc R SF i c)).le (Submodule.mem_map_of_mem (f := π) hxR)
  by_contra hall
  push_neg at hall
  have hbot : ∀ c, (GlobalTheory.Hk3.Wcc R SF i c).map π = ⊥ := by
    intro c
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    have hz : π w ∈ GlobalTheory.Hk3.Wcc R SF i c := hπmem c w hw
    have he : GlobalTheory.Hk3.eH R i (π w) = π w := by
      obtain ⟨u, hu⟩ := LinearMap.mem_range.1 (hsup.le (Submodule.mem_iSup_of_mem c hz))
      rw [← hu, ← Module.End.mul_apply, hidem]
    by_contra h0
    exact hall c (π w) hz h0
      ((GlobalTheory.WatType.wat_iff_type R F hs hC b i _).2 ⟨he, fun p => by rw [htype w p, hlam]⟩)
  simp only [hbot, iSup_bot, Submodule.mem_bot] at hmem
  exact hπx hmem

theorem rowsNe : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF → (∀ b, ∃ i, R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥) → RowsNe R F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hs hC hS SF hSF hTR hW b
  obtain ⟨i, hi⟩ := hW b
  obtain ⟨c, z, hzc, hz0, hzW⟩ := exists_part R F hs hC hS SF hSF b i hi
  have hinj := (hC.models.HW i (sg0 D A)).1
  have hez : (R.HW i (sg0 D A)).e z ≠ 0 := fun h => hz0 (hinj (h.trans (map_zero _).symm))
  have hzc' := (Submodule.mem_inf.1 (Submodule.mem_comap.1 hzc)).2
  have hpart : (R.HW i (sg0 D A)).e z ∈ GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A))
      (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (R.eWf i (sg0 D A)) SF c := by
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hzW).1, ?_⟩, hzW⟩
    have h1 := (Submodule.mem_inf.1 hzc').2
    simp only [Submodule.mem_iInf] at h1 ⊢
    exact fun P d B hB => h1 P d B (GlobalTheory.T.heckeOperator_faceLevel_eq_principalLevel R F hC SF hSF b i P d B hB)
  have hne : GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A))
      (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (R.eWf i (sg0 D A)) SF c ≠ ⊥ := fun h => hez ((Submodule.mem_bot ℂ).1 (h ▸ hpart))
  have hr := (hTR i).2 b c
  intro hE
  apply hne
  rw [← Submodule.rank_eq_zero, ← hr, Submodule.rank_eq_zero]
  exact eq_bot_iff.2 (inf_le_right.trans hE.le)

end GlobalTheory.RowsNeProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrep
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrep
noncomputable section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.TrFinDense

theorem span_values_dense : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ hU : IsSubrep π ⊤, ∀ N : Subrepresentation (finPartDSSm M hU), N ≠ ⊥ → (Submodule.span ℂ {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}).topologicalClosure = ⊤ := by
  intro D V S M H _ _ _ π hπ hU N hN
  classical
  set Sv : Set H := {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}
    with hSv
  set W : Submodule ℂ H := Submodule.span ℂ Sv with hW

  let Mon : Submonoid (GA D V) :=
    { carrier := {g | Sv ⊆ W.comap (π g : H →ₗ[ℂ] H)}
      mul_mem' := by
        intro a b ha hb z hz
        have hbz : π b z ∈ W := hb hz
        have : W ≤ W.comap (π a : H →ₗ[ℂ] H) := Submodule.span_le.2 ha
        show π (a * b) z ∈ W
        rw [map_mul]
        exact this hbz
      one_mem' := by
        intro z hz
        show π 1 z ∈ W
        rw [map_one]
        exact Submodule.subset_span hz }
  have hfin : ∀ g : GfC V, (g : GA D V) ∈ Mon := by
    rintro g _ ⟨Φ, hΦ, y, rfl⟩
    refine Submodule.subset_span ⟨finPartDSSm M hU g Φ, N.apply_mem_toSubmodule g hΦ, y, rfl⟩
  have hinf : ∀ w x, embW V w x ∈ Mon := by
    intro w x
    obtain ⟨τ, rfl⟩ := (placeOf_bijective D).2 w
    rintro _ ⟨Φ, hΦ, y, rfl⟩
    refine Submodule.subset_span ⟨Φ, hΦ, Function.update y τ (dsRep M τ x (y τ)), ?_⟩
    exact (((Φ : homDS M π ⊤).2).2 τ x y).symm
  haveI : Submodule.IsFullLattice D.host.E (stdLattice D.host.E V.rank) := isLattice_stdLattice
  have htop : Mon = ⊤ := GlobalTheory.PlaceGen.eq_top_of_local D.sp.cm.sig V.gram (stdLattice D.host.E V.rank) Mon ∅
    (fun v x => hfin (locFin V v x)) hinf (fun k hk => hfin ⟨k, (mem_levelOff.1 hk).1⟩)
  have hinvW : ∀ g, ∀ v ∈ W, π g v ∈ W := fun g v hv =>
    (Submodule.span_le.2 (show g ∈ Mon from htop ▸ trivial)) hv
  have hsub := isSubrep_topologicalClosure (π := π) hinvW
  rcases hπ.irred.2 _ hsub with h | h
  · exfalso
    obtain ⟨Φ, hΦ, hΦ0⟩ : ∃ Φ ∈ N.toSubmodule, Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hN (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun Φ hΦ => (Submodule.mem_bot ℂ).2 (hc Φ hΦ)))
    have : ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) ≠ 0 := by
      intro e
      exact hΦ0 (Subtype.ext (Subtype.ext e))
    obtain ⟨y, hy⟩ : ∃ y, ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact this (ContinuousMultilinearMap.ext hc)
    have hmem : ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y ∈ W.topologicalClosure :=
      W.le_topologicalClosure (Submodule.subset_span ⟨Φ, hΦ, y, rfl⟩)
    rw [h] at hmem
    exact hy ((Submodule.mem_bot ℂ).1 hmem)
  · exact h

end GlobalTheory.TrFinDense
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrepStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_values_dense_finitePartSubrep : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ hU : IsSubrep π ⊤, ∀ N : Subrepresentation (finPartDSSm M hU), N ≠ ⊥ → (Submodule.span ℂ {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}).topologicalClosure = ⊤ := by
  first | exact @GlobalTheory.TrFinDense.span_values_dense | exact GlobalTheory.TrFinDense.span_values_dense | (intros; apply GlobalTheory.TrFinDense.span_values_dense <;> assumption)
end
end
