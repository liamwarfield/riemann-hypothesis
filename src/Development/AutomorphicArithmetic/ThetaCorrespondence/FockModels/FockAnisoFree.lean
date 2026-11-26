module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.CoefND
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.WeilSiegelFormula
public import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilTheta

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SiegelFormulaSchwartz.SiegelFormulaThetaOfSchwartz
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

theorem PositivityTheory.SiegelWeilFormulaUnitary.siegelFormula_theta_of_schwartz' : GlobalTheory.Published.WeilSiegelFormula →
    ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ (dblSp A) B 1 χ ω → ∀ f, IsThetaFunO ψ (dblSp A) B f → 2 * A.rank < B.rank →
    ∀ ν 𝓖, IsCovolOne (ratL B A) ν 𝓖 → LeftInv (siegelQ A) (swSection A B ν 𝓖 ω f) ∧
      ∀ g, CosetConv (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g ∧
        cosetSum (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g =
          ⨍ q, descend (GQ B) (fun h => thetaKO ω g h f) q ∂autMeasure B m := by
  intro hSieg D A B m hm hA ψ χ ω hW f hf hB ν 𝓖 hcov
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨μ, hμ, -⟩ := GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ hμ
  obtain ⟨lam, hlam, hψ', -⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ hW.std θ hθ μ hμ
  obtain ⟨omS, hT⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ A B χ ω hW ν 𝓖 hcov θ hθ κ
  have hχ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ B.rank hW.hecT hW.resT
  have hWS : IsWeilSch (shift ψ lam) χ⁻¹ θ B ν omS :=
    ⟨GlobalTheory.StdUnn.transport_levi D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam,
     GlobalTheory.StdUnn.Unip.transport_unip D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam,
     GlobalTheory.StdUnn.WeylStd.main D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam⟩
  let Φ : schwartzA θ B.rank A.rank :=
    ⟨sch ψ A B ν 𝓖 f, ((GlobalTheory.SchSchwartzAll.schSchwartz D) ψ hW.std θ hθ A B ν 𝓖 hcov).1 f hf⟩
  have hΦ : Φ.1 = sch ψ A B ν 𝓖 (ω (((1 : siegel A) : GA D (dblSp A))⁻¹, 1) f) := by
    simp only [OneMemClass.coe_one, inv_one, Prod.mk_one_one, map_one, Module.End.one_apply]; rfl
  obtain ⟨-, -, hact⟩ := GlobalTheory.StdUnn.flat_swSec_eq_sect D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam 1 1 f hf Φ hΦ
  have hact' : ∀ g, (omS (κ g) Φ).1 = sch ψ A B ν 𝓖 (ω (g, 1) f) := fun g => by
    have := hact g; rwa [OneMemClass.coe_one, mul_one] at this
  have hval : ∀ g, swSection A B ν 𝓖 ω f g = 1 * (fun γ => (omS γ Φ).1 0) (κ (g * 1)) := fun g => by
    simp only [one_mul, mul_one]
    rw [hact' g, GlobalTheory.Core.Rk.IP.swSection_eq_swSec]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec, sch, mixS_dblDec_zero]
  obtain ⟨H, hH⟩ := GlobalTheory.StdUnn.exists_height D A.rank
  have hL : LeftInv (P D A.rank ⊓ GF D A.rank) (fun γ => (omS γ Φ).1 0) := by
    have hs := LeftInvSect.leftInv_sect D A.rank (Iwasawa.exists_mul D A.rank) B (shift ψ lam) χ⁻¹ θ ν omS hχ.1 hWS H hH Φ
      (s0 B A.rank)
    intro γ hγ g
    have h := hs γ hγ g
    simpa only [sect, sub_self, npow, Complex.cpow_zero, one_mul] using h
  obtain ⟨hleft, hg⟩ := GlobalTheory.StdUnn.cosetSum_along_mulEquiv _ _ κ (siegel A) (GQ (dblSp A)) (P D A.rank) (GF D A.rank)
    (GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ hμ κ hκ) (GlobalTheory.StdUnn.chart_mem_GF_iff D A μ hμ κ hκ) (fun γ => (omS γ Φ).1 0) 1 1 _ hval hL
  have hterm : ∀ g, term (P D A.rank) (GF D A.rank) (fun γ => (omS γ (omS (κ g) Φ)).1 0) 1 =
      term (P D A.rank) (GF D A.rank) (fun γ => (omS γ Φ).1 0) (κ (g * 1)) := fun g => by
    funext q
    simp only [term, mul_one, map_mul, Module.End.mul_apply]
  refine ⟨hleft, fun g => ⟨(hg g).1 ?_, ?_⟩⟩
  · have hcφ : Continuous (fun γ => (omS γ Φ).1 0) := by
      have e : (fun γ => (omS γ Φ).1 0) = swSection A B ν 𝓖 ω f ∘ κ.symm := by
        funext γ
        have := hval (κ.symm γ)
        simp only [mul_one, one_mul, MulEquiv.apply_symm_apply] at this
        simp only [Function.comp_apply, this]
      rw [e]
      exact (GlobalTheory.T.theta_section_continuous D ψ A B χ ω hW f hf ν 𝓖 hcov).comp
        (GlobalTheory.T.continuous_symm_unitary_chart D A μ hμ κ hκ)
    have hs : (A.rank : ℝ) / 2 < (s0 B A.rank).re := by
      have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast hB
      simp only [s0, Complex.sub_re, Complex.div_ofNat_re, Complex.natCast_re]
      linarith
    exact GlobalTheory.T.siegel_eisenstein_convergent D A.rank χ⁻¹ (s0 B A.rank) _ hcφ
      (GlobalTheory.T.weil_schwartz_parabolic_equivariant D A.rank (shift ψ lam) χ⁻¹ θ B ν omS hWS Φ) hs (κ (g * 1))
  · rw [(hg g).2, one_mul]
    have h := hSieg D A.rank B hA hB (shift ψ lam) hψ' χ⁻¹ hχ.1 hχ.2 θ hθ ν 𝓖 hcov omS hWS m hm (omS (κ g) Φ)
    unfold cosetSum at h ⊢
    rw [hterm g] at h
    rw [h]
    congr 1
    funext q
    congr 1
    funext h'
    rw [GlobalTheory.StdUnn.thetaKO_eq_tsum_sch D ψ A B χ ω hW ν 𝓖 hcov f hf g h', hact' g]
    rfl

theorem PositivityTheory.SiegelWeilFormulaUnitary.weilSiegelFormulaUnitary_of_two :
    GlobalTheory.Published.WeilThetaConvergence → GlobalTheory.Published.WeilSiegelFormula → GlobalTheory.Published.WeilSiegelFormulaUnitary := by
  intro hT hS D A B m hm hA hW
  refine ⟨GlobalTheory.T.absoluteThetaIntegral_le_continuousSeminorm hT D A B m hm hA hW, fun ψ χ ω hω f hf => ⟨GlobalTheory.T.integrable_thetaKernel_weilRange hT D A B m hm hA hW ψ χ ω hω f hf, ?_⟩⟩
  intro hab ν 𝓖 hν
  exact PositivityTheory.SiegelWeilFormulaUnitary.siegelFormula_theta_of_schwartz' hS D A B m hm hA ψ χ ω hω f hf hab ν 𝓖 hν
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.FockAnisoOfRanges
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace UpperTheory.Lit.Sw47

open GlobalTheory.BottomRallis

def FockAnisoLe (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank → B.rank ≤ 2 * A.rank → wittIndex B = 0 →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    GlobalTheory.Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (GlobalTheory.ThetaMean.thetaMean omh mH φ)

def FockAnisoGt (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → 2 * A.rank < B.rank → wittIndex B = 0 →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    GlobalTheory.Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (GlobalTheory.ThetaMean.thetaMean omh mH φ)

theorem fockAniso_of_ranges (D : D7) (h1 : FockAnisoLe D) (h2 : FockAnisoGt D) : SiegelWeilFockAniso D := by
  intro ψ A B hA hAB hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  rcases le_or_gt B.rank (2 * A.rank) with h | h
  · exact h1 ψ A B hA hAB h hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  · exact h2 ψ A B hA h hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF

theorem fockAniso_le (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent) : ∀ D, FockAnisoLe D := by
  intro D ψ A B _hA hab hle hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj
  have hw : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 := by rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]; exact hB
  exact hSW D ψ A B hab hle (by omega) χB omh homh a hmaj hI θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF

theorem re_sZero_gt {D : D7} (A B : HSp D) (h : 2 * A.rank < B.rank) : (A.rank : ℝ) / 2 < (sZero A B).re := by
  have e : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
    simp [sZero]
  rw [e]
  have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast h
  linarith

theorem fockAniso_gt : GlobalTheory.Published.WeilSiegelFormulaUnitary → ∀ D, FockAnisoGt D := by
  intro hWeil D ψ A B ha hab hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  have hφ := hF.1
  have hK := GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp A) B 1 χB omh sS sB homh hθ hS hBc (Khat A a) (isCompact_Khat A a) hKc φ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj
  have hwitt : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]; exact Or.inl hB
  obtain ⟨-, hW2⟩ := hWeil D A B mH hmH ha hwitt
  obtain ⟨hint, hser⟩ := hW2 ψ χB omh homh φ hφ
  refine ⟨hint, ?_⟩
  have hsum : ∀ g, GlobalTheory.Eis.eis A (GlobalTheory.SiegelFormula.swSection A B ν 𝓕 omh φ) g =
      ⨍ q, descend (GQ B) (fun h => thetaKO omh g h φ) q ∂autMeasure B mH := fun g =>
    ((hser hab ν 𝓕 hcov).2 g).2
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries GlobalTheory.weilRepresentationUnitaryPair D ψ A B χB omh homh ν 𝓕 hcov φ hφ a hK
  have hv := GlobalTheory.Eis.SphConv.eisValueAt_flat hI hmem (GlobalTheory.Eis.sphConv D A a hI) (isHeckeCharacter_inv_of_isHeckeCharacter homh.hecT)
    (re_sZero_gt A B hab)
  have he : GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 φ) = GlobalTheory.ThetaMean.thetaMean omh mH φ := by
    funext g
    rw [← swSection_eq_swSec]
    exact hsum g
  rw [he] at hv
  exact hv

def FA : Prop := ∀ D : D7, GlobalTheory.BottomRallis.SiegelWeilFockAniso D

theorem fa_of (hC : GlobalTheory.Published.SiegelWeilUnitaryConvergent) (hW : GlobalTheory.Published.WeilSiegelFormulaUnitary) : FA :=
  fun D => fockAniso_of_ranges D (fockAniso_le hC D) (fockAniso_gt hW D)

end UpperTheory.Lit.Sw47
end
end

namespace UpperTheory.Lit.Sw47

theorem convergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent := GlobalTheory.StdUnn.sw_doubled_of_std PositivityTheory.SiegelWeilCoefficients.field

theorem weilUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary :=
  PositivityTheory.SiegelWeilFormulaUnitary.weilSiegelFormulaUnitary_of_two UpperTheory.Lit.weilThetaConvergence PositivityTheory.Rg.Wsf.weilSiegelFormula

theorem fa : FA := fa_of convergent weilUnitary

theorem fockAniso_free (_ : GlobalTheory.Published.SiegelWeilAnisotropicUnitary) (D : Formalism.BasicNotions.D7) :
    GlobalTheory.BottomRallis.SiegelWeilFockAniso D := fa D

end UpperTheory.Lit.Sw47
