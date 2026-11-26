module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonzeroScalarsRootsOfUnity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesLiftData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesUnitEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.Stage1
theorem stage1_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → ((∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)) ∧ R.PGUnit F ∧ R.PGEquiv F ∧ (R.toCx3 F).zs.InBlock ∧ R.PThmA ∧ R.PThmB := by
  intro P D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hM
  obtain ⟨_hGiven, _hGS, _hCD, hLI, hTR, _hUI, _hUIW⟩ := _root_.GlobalTheory.T.lift_data_of_multiplicity_one P R F hT hM
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := _root_.ResidueKilled.sec_of_dm P.q9
  have hOk := GlobalTheory.InertOkH.heckeOperators_rows_lifts_rational_adjointClosed R F hT.char hT.junk
  have hGU : R.PGUnit F := GlobalTheory.gUnit_of_models R F hT.char.base.models
  have hGE : R.PGEquiv F := GlobalTheory.GEquivCx.pGEquiv_of_baseW P.q2 R F hT.char.base hT.ex
  have hBlk : (R.toCx3 F).zs.InBlock := GlobalTheory.Hk3.inBlock_of_cuspRapidDecay P.q2 R F hLI hT.ok hT.char hT.ex hGE
  have hA : R.PThmA := GlobalTheory.T.thetaLift_theoremA_publishedHypotheses P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q11 R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hJ
  have hB : R.PThmB := GlobalTheory.T.thetaLift_theoremB_publishedHypotheses P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q11 R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hTR hJ
  exact ⟨hOk, hGU, hGE, hBlk, hA, hB⟩
end GlobalTheory.Stage1
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pgUnit_and_pgEquiv_of_multEq : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → ((∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint)) ∧ R.PGUnit F ∧ R.PGEquiv F ∧ (R.toCx3 F).zs.InBlock ∧ R.PThmA ∧ R.PThmB := by
  first | exact @_root_.GlobalTheory.Stage1.stage1_alt | exact _root_.GlobalTheory.Stage1.stage1_alt | (intros; apply _root_.GlobalTheory.Stage1.stage1_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsCuspidal
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxThetaLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspFormApprox
theorem cuspForm_approx_of_thetaLift (hU : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → ∀ b : ℕ, IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → (G.V i (j + 1)).Maps) (vs : Fin n → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) ∧ IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂(G.meas t i (j + 1)).ν ≤ ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj φ hφ b
  obtain ⟨hμ, h𝓕⟩ := GlobalTheory.PairLift.haar_vert hR hG t hi (j := j + 1) hj
  exact ⟨integrableOn_quotHeight_pow_mul_norm hP.cuspRapidDecay hR.inf hμ h𝓕 hφ b,
    weighted_uniform_approx_cusp_forms hμ h𝓕 hφ.1.cont b (hU D R.θ hR.inf hP _ φ hφ b)⟩
theorem cuspForm_approx_thetaLift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → ∀ b : ℕ, IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → (G.V i (j + 1)).Maps) (vs : Fin n → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) ∧ IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂(G.meas t i (j + 1)).ν ≤ ε :=
  _root_.GlobalTheory.CuspFormApprox.cuspForm_approx_of_thetaLift _root_.GlobalTheory.T.twist_cusp_form_approx_weighted
end GlobalTheory.CuspFormApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_cuspForm_approx_thetaLift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → ∀ b : ℕ, IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → (G.V i (j + 1)).Maps) (vs : Fin n → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) ∧ IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂(G.meas t i (j + 1)).ν ≤ ε := by
  first | exact @_root_.GlobalTheory.CuspFormApprox.cuspForm_approx_thetaLift | exact _root_.GlobalTheory.CuspFormApprox.cuspForm_approx_thetaLift | (intros; apply _root_.GlobalTheory.CuspFormApprox.cuspForm_approx_thetaLift <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistThetaLiftLeQuotientHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaArrowGrowth
theorem thetaLift_le_quotientHeight : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  intro _ _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨K, n, hK, hb⟩ := GlobalTheory.ChainOnto.ThetaSwap.thetaKO_le_quotHeight hRB.inf hω hΦ
  refine ⟨n, n, K, hK, fun h g => ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact hb h g
end GlobalTheory.ThetaArrowGrowth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_thetaLift_le_quotientHeight : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  first | exact @_root_.GlobalTheory.ThetaArrowGrowth.thetaLift_le_quotientHeight | exact _root_.GlobalTheory.ThetaArrowGrowth.thetaLift_le_quotientHeight | (intros; apply _root_.GlobalTheory.ThetaArrowGrowth.thetaLift_le_quotientHeight <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistThetaLiftApproxFockSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaArrowApprox
private theorem thetaKO_sub_local {D : D7} {S T : HSp D}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (g : GA D S) (h : GA D T) (f f' : WO S T → ℂ) :
    thetaKO om g h f - thetaKO om g h f' = thetaKO om g h (f - f') := by
  simp only [thetaKO, map_sub, Pi.sub_apply]

private theorem exists_kernel_approx_local {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om) (P : (WO S T → ℂ) → Prop)
    {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ)
    (hden : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → Φ ∈ GlobalTheory.Size.thetaLevel ψ S T U →
      ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε →
        ∃ X, P X ∧ X ∈ GlobalTheory.Size.thetaLevel ψ S T U ∧ GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ) < ENNReal.ofReal ε) :
    ∃ a : ℕ, ∀ ε : ℝ, 0 < ε → ∃ X, P X ∧ ∀ g h,
      ‖thetaKO om g h X - thetaKO om g h Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a := by
  obtain ⟨a, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D S.rank T.rank
  obtain ⟨U, hU, hΦU⟩ := GlobalTheory.Size.isTheta_iff_level.1 hΦ
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne S T
  obtain ⟨C, hC0, hC⟩ := (H _ _ rfl rfl).real ψ hθ hU
  refine ⟨a, fun ε hε => ?_⟩
  have hK : 0 < (C + 1) * 4 ^ a := by positivity
  obtain ⟨X, hPX, hXU, hsob⟩ := hden U hU hΦU μ 𝓕 hμ d (ε / ((C + 1) * 4 ^ a)) (div_pos hε hK)
  refine ⟨X, hPX, fun g h => ?_⟩
  have hΨ : X - Φ ∈ GlobalTheory.Size.thetaLevel ψ S T U := Submodule.sub_mem _ hXU hΦU
  rw [thetaKO_sub_local]
  obtain ⟨-, hb⟩ := hC _ _ _ hω μ 𝓕 hμ (X - Φ) hΨ
  have hsr : (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal ≤ ε / ((C + 1) * 4 ^ a) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsob.le
    rwa [ENNReal.toReal_ofReal (div_pos hε hK).le] at this
  obtain ⟨γ, hγ, h1⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight T h
  rw [← GlobalTheory.ChainOnto.ThetaSwap.thetaKO_left_fst hω hΨ.1 γ hγ g h,
    ← GlobalTheory.Chain.LiftConv.thetaKO_left hω hΨ.1 (γ * g) γ' hγ' h]
  have hq1 := GlobalTheory.Grow.quotHeight_pos S g
  have hq2 := GlobalTheory.Grow.quotHeight_pos T h
  have hh1 := GlobalTheory.Grow.height_pos S (γ * g)
  have hh2 := GlobalTheory.Grow.height_pos T (γ' * h)
  have hs0 : 0 ≤ (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal := ENNReal.toReal_nonneg
  have hpow : (GlobalTheory.Grow.height S (γ * g) * GlobalTheory.Grow.height T (γ' * h)) ^ a ≤
      4 ^ a * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a) := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) a
  have hne : (C + 1) * 4 ^ a ≠ 0 := hK.ne'
  calc ‖thetaKO om (γ * g) (γ' * h) (X - Φ)‖
      ≤ C * (GlobalTheory.Size.sobO ψ θ μ 𝓕 d (X - Φ)).toReal *
          (GlobalTheory.Grow.height S (γ * g) * GlobalTheory.Grow.height T (γ' * h)) ^ a := hb _ _
    _ ≤ (C + 1) * (ε / ((C + 1) * 4 ^ a)) * (4 ^ a * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a)) :=
        mul_le_mul (mul_le_mul (by linarith) hsr hs0 (by linarith)) hpow (pow_nonneg (mul_pos hh1 hh2).le a)
          (mul_nonneg (by linarith) (div_pos hε hK).le)
    _ = ((C + 1) * 4 ^ a) * (ε / ((C + 1) * 4 ^ a)) * (GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a) := by
        ring
    _ = ε * GlobalTheory.Grow.quotHeight S g ^ a * GlobalTheory.Grow.quotHeight T h ^ a := by
        rw [mul_div_cancel₀ _ hne]; ring

theorem thetaLift_approx_fockSpace : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - thetaKO (G.th t i j).ω h g Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  intro _ _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨a, ha⟩ := exists_kernel_approx_local hRB.inf hω
    (fun X => ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank),
      (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧
        X = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) hΦ
    (fun U hU hΦU μ 𝓕 hμ d ε hε => by
      obtain ⟨n, fs, ps, h1, h2, h3⟩ := GlobalTheory.T.gridDownArrow_thetaFunction_fock_dense_of_level D G₀ Pl0 T A Ks R G hRB hG t i j hi hj U hU Φ hΦU μ 𝓕 hμ d ε hε
      exact ⟨_, ⟨n, fs, ps, h1, rfl⟩, h2, h3⟩)
  refine ⟨a, a, fun ε hε => ?_⟩
  obtain ⟨X, ⟨n, fs, ps, hfs, rfl⟩, hX⟩ := ha ε hε
  exact ⟨n, fs, ps, hfs, fun h g => hX h g⟩
end GlobalTheory.ThetaArrowApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_thetaLift_approx_fockSpace : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - thetaKO (G.th t i j).ω h g Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  first | exact @_root_.GlobalTheory.ThetaArrowApprox.thetaLift_approx_fockSpace | exact _root_.GlobalTheory.ThetaArrowApprox.thetaLift_approx_fockSpace | (intros; apply _root_.GlobalTheory.ThetaArrowApprox.thetaLift_approx_fockSpace <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFiniteLevelLiftOfTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FinLift
theorem exists_finite_level_lift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) → ∀ (n' : ℕ) (Fs : Fin n' → (G.V i (j + 1)).Maps) (vs : Fin n' → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) ∧ IsAutFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) ∧ IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) := by
  intro LC _ D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj n fs ps hfs n' Fs vs hFs
  have hC := LC D hS G₀ Pl0 T A Ks R G hRB hG
  simp only [thetaKO_sum]
  exact lift_finSum (fun l p h g => thetaKO (G.th t i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) p))
    (fun p v => (G.th t i j).It p v) (fun l => hC.th t i j hi hj (fs l) (hfs l)) ps Fs vs hFs
end GlobalTheory.FinLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_level_lift_of_twist : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) → ∀ (n' : ℕ) (Fs : Fin n' → (G.V i (j + 1)).Maps) (vs : Fin n' → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g)) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) ∧ IsAutFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) ∧ IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) * (∑ k, Fs k (vs k) g) ∂(G.meas t i (j + 1)).ν) := by
  first | exact @_root_.GlobalTheory.FinLift.exists_finite_level_lift | exact _root_.GlobalTheory.FinLift.exists_finite_level_lift | (intros; apply _root_.GlobalTheory.FinLift.exists_finite_level_lift <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
theorem GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj Φ hΦ φ hφ hint
  have haut := _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint
  obtain ⟨a1, b1, C, hC0, hK1⟩ := _root_.GlobalTheory.T.twist_thetaLift_le_quotientHeight hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ
  obtain ⟨a2, b2, happ2⟩ := _root_.GlobalTheory.T.twist_thetaLift_approx_fockSpace hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ
  set a := max a1 a2
  set b := max b1 b2
  have hqB : ∀ h, ∀ c, c ≤ a → GlobalTheory.Grow.quotHeight (G.V i j).V h ^ c ≤ GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a :=
    fun h c hc => pow_le_pow_right₀ (GlobalTheory.Grow.one_le_quotHeight _ h) hc
  have hqA : ∀ g, ∀ c, c ≤ b → GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ c ≤ GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b :=
    fun g c hc => pow_le_pow_right₀ (GlobalTheory.Grow.one_le_quotHeight _ g) hc
  have hK : ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤
      C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := fun h g =>
    (hK1 h g).trans (mul_le_mul (mul_le_mul_of_nonneg_left (hqB h a1 (le_max_left _ _)) hC0)
      (hqA g b1 (le_max_left _ _)) (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _)
      (mul_nonneg hC0 (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ h).le _)))
  have happ : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ))
      (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank),
      (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ ∀ h g,
        ‖thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - thetaKO (G.th t i j).ω h g Φ‖ ≤
          ε * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
    intro ε hε
    obtain ⟨n, fs, ps, hfs, hb⟩ := happ2 ε hε
    exact ⟨n, fs, ps, hfs, fun h g => (hb h g).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (hqB h a2 (le_max_right _ _)) hε.le) (hqA g b2 (le_max_right _ _))
      (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _)
      (mul_nonneg hε.le (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ h).le _)))⟩
  obtain ⟨hI1, hform⟩ := _root_.GlobalTheory.T.twist_cuspForm_approx_thetaLift hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj φ hφ b
  refine GlobalTheory.ThLiftCusp.isCuspFun_of_approx _ _ haut.cont haut.left a fun η hη => ?_
  set I1 := ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖ ∂(G.meas t i (j + 1)).ν
    with hI1def
  have hI1nn : 0 ≤ I1 := setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun g =>
    mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le _) (norm_nonneg _))
  have hden : 0 < I1 + 1 + C := by linarith
  set e := min 1 (η / (I1 + 1 + C)) with hedef
  have he : 0 < e := lt_min one_pos (div_pos hη hden)
  obtain ⟨n, fs, ps, hfs, hKK⟩ := happ e he
  obtain ⟨n', Fs, vs, hFs, hI2, hδ⟩ := hform e he
  obtain ⟨hint', haut', hcusp'⟩ := _root_.GlobalTheory.T.exists_finite_level_lift_of_twist hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj n fs ps hfs n' Fs vs hFs
  refine ⟨_, haut'.cont, haut'.left, hcusp', fun h => ?_⟩
  have key := GlobalTheory.ThLiftCusp.norm_lift_sub_le ((G.meas t i (j + 1)).ν.restrict (G.meas t i (j + 1)).fd)
    (fun h g => thetaKO (G.th t i j).ω h g Φ)
    (fun h g => thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)))
    φ (fun g => ∑ k, Fs k (vs k) g) (fun h => GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a)
    (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b) C e e hC0 he.le
    (fun h => pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ h).le _) hK hKK hI1 hI2 hδ hint' hint h
  refine key.trans ?_
  have hq : GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a ≤ GlobalTheory.Grow.height (G.V i j).V h ^ a :=
    pow_le_pow_left₀ (GlobalTheory.Grow.quotHeight_pos _ h).le (GlobalTheory.Grow.quotHeight_le_height _ h) a
  have he1 : e ≤ 1 := min_le_left _ _
  have he2 : e ≤ η / (I1 + 1 + C) := min_le_right _ _
  have hb : e * I1 + (e + C) * e ≤ η := by
    have : e * (I1 + 1 + C) ≤ η := (le_div_iff₀ hden).1 he2
    nlinarith
  have h0 : 0 ≤ e * I1 + (e + C) * e := by positivity
  calc GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * (e * I1 + (e + C) * e)
      ≤ GlobalTheory.Grow.height (G.V i j).V h ^ a * η :=
        mul_le_mul hq hb h0 (pow_nonneg ((GlobalTheory.Grow.quotHeight_pos _ h).le.trans (GlobalTheory.Grow.quotHeight_le_height _ h)) _)
    _ = η * GlobalTheory.Grow.height (G.V i j).V h ^ a := mul_comm _ _
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → IsCuspFun (G.V i j).V (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  first | exact @_root_.GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal | exact _root_.GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal | (intros; apply _root_.GlobalTheory.ThLiftCusp.theta_lift_of_cusp_form_isCuspidal <;> assumption)
end
end
