module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageRealDataConjValueMemCuspForms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilCoefficientFockVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilCoefficientFockVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftCoefCont

theorem continuous_l2_weil_action_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ Q₁ Q₂, Continuous fun g : GA D (Wc D i) => l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hc Q₁ Q₂
  obtain ⟨-, -, -, -, -, hom, -, -, hpt, -, -⟩ := h
  have e : ∀ g : GA D (Wc D i), l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) =
      GlobalTheory.RawLift.thetaIP μ 𝓧 (ptAt R i σ BW f Q₂) (ω (1, g) (ptAt R i σ BW f Q₁)) := fun g => by
    rw [← GlobalTheory.RawLift.FockCoef.thetaInner_star, GlobalTheory.RawLift.GoodModulus.thetaInner_eq_star_l2, star_star]
  simp only [e]
  exact GlobalTheory.RawLift.FockCoef.continuous_coef hom hc (hpt Q₂) (hpt Q₁)

end GlobalTheory.LiftCoefCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilCoefficientFockVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_weilCoefficient_fockVectors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ Q₁ Q₂, Continuous fun g : GA D (Wc D i) => l2 μ 𝓧 (ω (1, g) (ptAt R i σ BW f Q₁)) (ptAt R i σ BW f Q₂) := by
  first | exact @GlobalTheory.LiftCoefCont.continuous_l2_weil_action_ptAt | exact GlobalTheory.LiftCoefCont.continuous_l2_weil_action_ptAt | (intros; apply GlobalTheory.LiftCoefCont.continuous_l2_weil_action_ptAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDatumFockVectorsAreFockVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDatumFockVectorsAreFockVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftFockVec

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis

theorem ptAt_isFockVec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (ptAt R i σ BW f Q) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h Q
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, hlv, hpt, -, -⟩ := h'
  obtain ⟨⟨hψ, hv⟩, -⟩ := hlv
  have hθ : IsInfFam R.θ := hv.inf
  obtain ⟨⟨p, hp⟩, -⟩ := hv.norm
  obtain ⟨-, hθf, hS, hvac⟩ := GlobalTheory.LiftFockVac.levVec_fockVac R F i t σ s P cμ cη m ω BW f₀ f c io h p.1 p.2 hp
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i σ) τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i σ)
  set Ap := aPlusAll (heisO R.ψ (Vc D i) (Wc D i)) R.θ (fun τ => cplxO ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) τ) (cart (R.MW i σ) τ)) (R.BV i) BW with hAdef
  have hadd : ∀ g g', IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) g' →
      IsThetaFunO R.ψ (Vc D i) (Wc D i) (g + g') := fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) (a • g) :=
    fun a _ => theta_smul a
  have hA : ∀ k g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) (Ap k g) :=
    fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i' j g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → Ap i' (Ap j g) = Ap j (Ap i' g) :=
    fun i' j _ h => aPlus_comm' hψ hθ i'.1 _ hS hT j.1 _ h
  have Aadd : ∀ i' g g', IsThetaFunO R.ψ (Vc D i) (Wc D i) g → IsThetaFunO R.ψ (Vc D i) (Wc D i) g' →
      Ap i' (g + g') = Ap i' g + Ap i' g' :=
    fun i' _ _ h h' => aPlus_add hψ hθ i'.1 _ _ h h'
  have Asm : ∀ i' (a : ℂ) g, IsThetaFunO R.ψ (Vc D i) (Wc D i) g → Ap i' (a • g) = a • Ap i' g :=
    fun i' a _ h => aPlus_smul hψ hθ i'.1 _ _ a h
  have hpt' : ∀ Q', ptAt R i σ BW f Q' = pureTensorL Ap f Q' := fun _ => rfl
  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) ℂ),
      ∃ c' : FVar D (Wc D i).rank (Vc D i).rank → ℂ, ∀ Q',
      annih (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) z (pureTensorL Ap f Q') =
        pureTensorL Ap f (∑ k, c' k • MvPolynomial.pderiv k Q') := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir (Vc D i) (Wc D i) τ z k.1 (unitMap (R.BV i k.1) (BW k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir (Vc D i) (Wc D i) τ (cplxO 1 (cart (R.MW i σ) τ) z) k.1
          (unitMap (R.BV i k.1) (BW k.1) k.2.1 k.2.2) : ℝ))), fun Q' => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hθf (hvac τ z) Q'
  refine ⟨hpt Q, Q.totalDegree + 1, fun l hl => ?_⟩
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) ℂ),
      ∃ Q' : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ,
      l.foldr (fun p g => annih (heisO R.ψ (Vc D i) (Wc D i)) R.θ p.1 (cplxO 1 (cart (R.MW i σ) p.1)) p.2 g)
          (pureTensorL Ap f Q) = pureTensorL Ap f Q' ∧
        ∀ n : FVar D (Wc D i).rank (Vc D i).rank →₀ ℕ, Q.totalDegree < n.degree + l.length → Q'.coeff n = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨Q, rfl, fun n hn => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h2 : Q.totalDegree < n.degree := by simpa using hn
      exact h2
    | cons q l ih =>
      obtain ⟨Q', hQ', hQc⟩ := ih
      obtain ⟨c', hc'⟩ := hder q.1 q.2
      refine ⟨∑ k, c' k • MvPolynomial.pderiv k Q', ?_, fun n hn => ?_⟩
      · rw [List.foldr_cons, hQ', hc']
      · refine GlobalTheory.FockVecOfVac.coeff_sum_pderiv_eq_zero c' Q' (Q.totalDegree - l.length)
          (fun n' hn' => hQc n' (by omega)) n ?_
        simp only [List.length_cons] at hn
        omega
  obtain ⟨Q', hQ', hQc⟩ := key l
  have hQ0 : Q' = 0 := MvPolynomial.ext _ _ fun n => by
    simpa using hQc n (by rw [hl]; omega)
  show l.foldr _ (ptAt R i σ BW f Q) = 0
  rw [hpt', hQ', hQ0, map_zero]

end GlobalTheory.LiftFockVec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDatumFockVectorsAreFockVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDatum_fockVectors_areFockVectors : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (ptAt R i σ BW f Q) := by
  first | exact @GlobalTheory.LiftFockVec.ptAt_isFockVec | exact GlobalTheory.LiftFockVec.ptAt_isFockVec | (intros; apply GlobalTheory.LiftFockVec.ptAt_isFockVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftPairPositiveDefiniteWittIndexZeroCartan
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapValueKFiniteMemCuspForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapValueKFiniteMemCuspForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D), V.SigOK → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ cA : GlobalTheory.Mem.Th.CptF V, GlobalTheory.Cusp.IsCartanFrame V cA ∧ (∀ τ, IsCartanInv (gramAt D V τ) (cart M τ)) ∧ (∀ τ, cA τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * cA τ) ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) → U v ∈ GlobalTheory.Cusp.A0 θ V cA := by
  intro D θ hθ V hV S M
  refine ⟨GlobalTheory.ChainOnto.RealData.sortedFrame M hV, GlobalTheory.ChainOnto.RealData.isCartanFrame_sortedFrame M hV,
    fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M τ, fun τ => GlobalTheory.ChainOnto.RealData.sortedFrame_cart M hV τ, ?_⟩
  intro J χ U hU v hv
  induction hU using Submodule.span_induction with
  | mem T hT =>
    exact GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨hT.aut v, hT.cusp v⟩,
      GlobalTheory.ChainOnto.RealData.isKFinite_value θ hθ M hV hT v hv⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact (GlobalTheory.Cusp.A0 θ V _).smul_mem a hx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapValueKFiniteMemCuspFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_map_apply_mem_A0_of_kfin : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D), V.SigOK → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ cA : GlobalTheory.Mem.Th.CptF V, GlobalTheory.Cusp.IsCartanFrame V cA ∧ (∀ τ, IsCartanInv (gramAt D V τ) (cart M τ)) ∧ (∀ τ, cA τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * cA τ) ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) → U v ∈ GlobalTheory.Cusp.A0 θ V cA := by
  first | exact @GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms | exact GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms | (intros; apply GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowestKTypeMemDiscreteSeriesKFiniteVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowestKTypeMemDiscreteSeriesKFiniteVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowKFin

theorem lowT_mem_kfin (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (v : lowT M τ) : ((v : M.sm τ) : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ := by
  have hv : ((v : M.sm τ) : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := v.2
  refine (sSup_le ?_ : lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) hv
  rintro T hT x hx
  exact Submodule.subset_span ⟨T, hT.1, hx, hT.2.1⟩

end GlobalTheory.LowKFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowestKTypeMemDiscreteSeriesKFiniteVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_mem_discreteSeriesKFiniteVectors : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (v : lowT M τ), ((v : M.sm τ) : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ := by
  first | exact @GlobalTheory.LowKFin.lowT_mem_kfin | exact GlobalTheory.LowKFin.lowT_mem_kfin | (intros; apply GlobalTheory.LowKFin.lowT_mem_kfin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftPairPositiveDefiniteWittIndexZeroCartan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.PairSetting

theorem main : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GlobalTheory.Cusp.wittIndex (Vc D i) = 0 ∧ (Wc D i).rank < D.R.t ∧ ∃ cA : GlobalTheory.Mem.Th.CptF (Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.HidaSetting R.θ (Wc D i) (Vc D i) (cart (R.MW i σ)) (fun _ => 1) D.R.t cA ∧ ∀ U ∈ R.Wall i σ, ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, U (fun ρ => v ρ) ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := by
  intro D G _ _ Pl0 T' A Ks _ _ _ R F hC _ i σ
  have hi1 : 1 ≤ (i : ℕ) + 1 := Nat.le_add_left 1 _
  have hi2 : (i : ℕ) + 1 ≤ D.R.m := i.isLt
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ hi1 hi2
  have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ hi1 hi2
  have hk := D.R.rank_add_five_le
  have hm := D.R.two_le_m
  obtain ⟨cA, hF, hcart, hJ, hA0⟩ := GlobalTheory.T.multiplicity_map_apply_mem_A0_of_kfin D R.θ hC.models.inf (Wc D i) (D.sp.W_sig _) _ (R.MW i σ)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig (↑i + 1) (tauE D τ)
    rw [hC.models.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  refine ⟨GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Per.isAniso_of_posDef (D.sp.V_sig _) (hC.models.vpos i)), ?_, cA, ⟨?_, ?_, ?_, hC.models.inf, D.sp.W_sig _, hF, hcart, fun τ => ⟨by simp, by simp, by simpa using hpos τ⟩, hJ⟩, ?_⟩
  · rw [hW]; simp only [Ranks.r] at *; omega
  · rw [hW]; simp only [Ranks.r] at *; omega
  · simp only [Ranks.r] at *; omega
  · rw [hV, hW]; rfl
  · intro U hU v
    exact hA0 _ _ U hU (fun ρ => v ρ) (fun τ => GlobalTheory.T.lowestKType_mem_discreteSeriesKFiniteVectors D (Wc D i) _ (R.MW i σ) τ (v τ))

end GlobalTheory.PairSetting
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftPairPositiveDefiniteWittIndexZeroCartanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftPair_positiveDefinite_wittIndexZero_cartan : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GlobalTheory.Cusp.wittIndex (Vc D i) = 0 ∧ (Wc D i).rank < D.R.t ∧ ∃ cA : GlobalTheory.Mem.Th.CptF (Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.HidaSetting R.θ (Wc D i) (Vc D i) (cart (R.MW i σ)) (fun _ => 1) D.R.t cA ∧ ∀ U ∈ R.Wall i σ, ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, U (fun ρ => v ρ) ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := by
  first | exact @GlobalTheory.PairSetting.main | exact GlobalTheory.PairSetting.main | (intros; apply GlobalTheory.PairSetting.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnitaryAdelicEqSumFiniteCosetsRealIntegr
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnitaryAdelicEqSumFiniteCosetsRealIntegr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetDisint

theorem integral_eq_of_lintegral_eq {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (m : Measure Y)
    (f : X → ℂ) (g : Y → ℂ) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ c : ℂ → ENNReal, Measurable c → ∫⁻ x, c (f x) ∂μ = ∫⁻ y, c (g y) ∂m) (hi : Integrable f μ) :
    Integrable g m ∧ ∫ x, f x ∂μ = ∫ y, g y ∂m := by
  have e : μ.map f = m.map g := by
    ext S hS
    rw [Measure.map_apply hf hS, Measure.map_apply hg hS]
    have h1 := h (S.indicator 1) (measurable_one.indicator hS)
    have e1 : ∀ x, S.indicator (1 : ℂ → ENNReal) (f x) = (f ⁻¹' S).indicator 1 x := fun x => by
      by_cases hx : f x ∈ S <;> simp [Set.indicator, hx]
    have e2 : ∀ y, S.indicator (1 : ℂ → ENNReal) (g y) = (g ⁻¹' S).indicator 1 y := fun y => by
      by_cases hy : g y ∈ S <;> simp [Set.indicator, hy]
    simp only [e1, e2] at h1
    rwa [lintegral_indicator_one (hf hS), lintegral_indicator_one (hg hS)] at h1
  refine ⟨?_, ?_⟩
  · have h1 : Integrable (fun z : ℂ => z) (μ.map f) :=
      (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).2 hi
    rw [e] at h1
    exact (integrable_map_measure aestronglyMeasurable_id hg.aemeasurable).1 h1
  · have a1 := integral_map (μ := μ) hf.aemeasurable (f := fun z : ℂ => z) aestronglyMeasurable_id
    have a2 := integral_map (μ := m) hg.aemeasurable (f := fun z : ℂ => z) aestronglyMeasurable_id
    rw [← a1, ← a2, e]

variable {D : D7}

theorem continuous_realPt {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} (hW : W.SigOK) {Fr : Frames W}
    (hFr : IsFrames W Fr) : Continuous fun b : (∀ ρ, Upq W ρ) => realElt θ W fun ρ => realMat W Fr ρ (b ρ) := by
  obtain ⟨h1, h2, h3⟩ := Formalism.IndefR.Eqv.G5.af_facts D.host.F
  obtain ⟨h1, -, -, -, -⟩ := Formalism.IndefR.Eqv.G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig W.gram
  unfold realElt
  refine continuous_list_prod _ fun ρ _ => ?_
  have hm : Continuous fun b : (∀ ρ, Upq W ρ) => UpqT.mat (b ρ) :=
    (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply ρ)
  refine (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ W ρ).comp_continuous
    (continuous_const.matrix_mul ((continuous_const.matrix_mul hm).matrix_mul continuous_const)) fun b => ?_
  refine conjFrame_mem_UH _ _ _ (sig_sum W hW (tauE D ρ)) _ _ (hFr ρ) ?_ (b ρ)
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ((map_ne_zero _).2 (GlobalTheory.DefiniteQuotient.gram_hermND W).2).isUnit

theorem finE_toFin (W : HSp D) (h : GA D W) : finE W h = finE W (GlobalTheory.AutMult.toFin W h : GA D W) := by
  conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin h]
  rw [map_mul]
  have : finE W (GlobalTheory.AutMult.toInf W h : GA D W) = 1 := by
    show Formalism.UG.bc (swapAE D) (finHom W _) = 1
    rw [MonoidHom.mem_ker.1 (GlobalTheory.AutMult.toInf W h).2, map_one]
  rw [this, one_mul]

end GlobalTheory.CosetDisint

end

namespace GlobalTheory.CosetDisint

theorem integral_eq_cosetSum : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → IsOpen {h : GA D W | finE W h ∈ K} → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ℂ, Continuous Z → Integrable Z ν → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ))‖ₑ ∂(Measure.pi mR) < ⊤ ∧ ∫ g, Z g ∂ν = ∫ b, ∑' x : FinCos W (levA W K), Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  intro D θ hθ W hW K ν hν hO Fr hFr mR hmR Z hZc hZi hZinv
  obtain ⟨h1, h2, h3⟩ := Formalism.IndefR.Eqv.G5.af_facts D.host.F
  obtain ⟨i0, -, -, i3, i4⟩ := Formalism.IndefR.Eqv.G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig W.gram
  haveI := i0; haveI := i3; haveI := i4
  haveI : ν.IsHaarMeasure := hν.1
  haveI : SecondCountableTopology (GfC W) := Topology.IsInducing.subtypeVal.secondCountableTopology
  set O : Set (GA D W) := {h | finE W h ∈ K} with hOdef
  have hOm : MeasurableSet O := hO.measurableSet
  set φ : (∀ ρ, Upq W ρ) → GA D W := fun b => realElt θ W fun ρ => realMat W Fr ρ (b ρ) with hφdef
  have hφ : Continuous φ := continuous_realPt hθ hW hFr
  have hZm : Measurable Z := hZc.measurable
  set L' := (levA W K).subgroupOf (GfC W) with hL'
  have hmemL : ∀ y : GfC W, y ∈ L' ↔ finE W (y : GA D W) ∈ K := fun y => by
    rw [hL', Subgroup.mem_subgroupOf, mem_levA]
    exact and_iff_right y.2
  have hL'o : IsOpen (L' : Set (GfC W)) := by
    have : (L' : Set (GfC W)) = Subtype.val ⁻¹' O := Set.ext fun y => hmemL y
    rw [this]; exact hO.preimage continuous_subtype_val

  haveI : Countable (GfC W ⧸ L') := by
    have hpd : (Set.univ : Set (GfC W ⧸ L')).PairwiseDisjoint
        (fun q => (fun x => (Quotient.out q : GfC W)⁻¹ * x) ⁻¹' (L' : Set (GfC W))) := by
      intro q _ q' _ hne
      refine Set.disjoint_left.2 fun x h1 h2 => hne ?_
      have e1 : QuotientGroup.mk (Quotient.out q) = (QuotientGroup.mk x : GfC W ⧸ L') := QuotientGroup.eq.2 h1
      have e2 : QuotientGroup.mk (Quotient.out q') = (QuotientGroup.mk x : GfC W ⧸ L') := QuotientGroup.eq.2 h2
      rw [QuotientGroup.out_eq'] at e1 e2
      exact e1.trans e2.symm
    exact Set.countable_univ_iff.1 (hpd.countable_of_isOpen
      (fun q _ => hL'o.preimage (continuous_const.mul continuous_id))
      (fun q _ => ⟨Quotient.out q, by simp [L'.one_mem]⟩))

  let s : GfC W ⧸ L' → Set (GA D W) := fun q => (fun g => (FinCos.rep q)⁻¹ * g) ⁻¹' O
  have hmem : ∀ q g, g ∈ s q ↔ q = QuotientGroup.mk (GlobalTheory.AutMult.toFin W g) := by
    intro q g
    show finE W ((FinCos.rep q)⁻¹ * g) ∈ K ↔ _
    rw [finE_toFin, map_mul, map_inv, FinCos.rep, GlobalTheory.AutMult.toFin_coe, ← hmemL]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq]
  have hsm : ∀ q, MeasurableSet (s q) := fun q => (measurable_const_mul _) hOm
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro q q' hne
    exact Set.disjoint_left.2 fun g h1 h2 => hne (((hmem q g).1 h1).trans ((hmem q' g).1 h2).symm)
  have hU : (⋃ q, s q) = Set.univ := Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, (hmem _ g).2 rfl⟩

  have key : ∀ q : GfC W ⧸ L', ∀ G : GA D W → ENNReal, Measurable G → (∀ g, ∀ k ∈ levA W K, G (g * k) = G g) →
      ∫⁻ g in s q, G g ∂ν = ∫⁻ b, G (FinCos.rep q * φ b) ∂(Measure.pi mR) := by
    intro q G hG hGi
    have hpre : (fun h => FinCos.rep q * h) ⁻¹' s q = O := by
      ext h; simp [s]
    rw [← (measurePreserving_mul_left ν (FinCos.rep q)).setLIntegral_comp_preimage_emb
      (measurableEmbedding_mulLeft _) G (s q), hpre]
    exact GlobalTheory.T.level_measure_pushforward_eq_product_real_measures D θ hθ W hW K ν hν Fr hFr mR hmR (fun h => G (FinCos.rep q * h)) (hG.comp (measurable_const_mul _))
      (fun g k hk => by simp only [← mul_assoc]; exact hGi _ k hk) hOm
  have hcm : ∀ q : GfC W ⧸ L', Continuous fun b => Z (FinCos.rep q * φ b) := fun q =>
    hZc.comp (continuous_const.mul hφ)

  have hlin : ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * φ b)‖ₑ ∂(Measure.pi mR) = ∫⁻ g, ‖Z g‖ₑ ∂ν := by
    rw [lintegral_tsum fun q => (hcm q).measurable.enorm.aemeasurable]
    rw [← Measure.restrict_univ (μ := ν), ← hU, lintegral_iUnion hsm hd]
    refine tsum_congr fun q => (key q (fun g => ‖Z g‖ₑ) hZm.enorm fun g k hk => by rw [hZinv g k hk]).symm
  have hfin : ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * φ b)‖ₑ ∂(Measure.pi mR) < ⊤ := by
    rw [hlin]; exact hZi.2
  refine ⟨hfin, ?_⟩

  have hint : ∀ q : GfC W ⧸ L', ∫ g in s q, Z g ∂ν = ∫ b, Z (FinCos.rep q * φ b) ∂(Measure.pi mR) := fun q =>
    (integral_eq_of_lintegral_eq (ν.restrict (s q)) (Measure.pi mR) Z _ hZm (hcm q).measurable
      (fun c hc => key q (fun g => c (Z g)) (hc.comp hZm) fun g k hk => by simp only [hZinv g k hk])
      hZi.integrableOn).2
  have hsum := hasSum_integral_iUnion hsm hd (by rw [hU]; exact hZi.integrableOn)
  rw [hU, Measure.restrict_univ] at hsum
  rw [← hsum.tsum_eq, integral_tsum (fun q => (hcm q).aestronglyMeasurable)
    (by rw [← lintegral_tsum fun q => (hcm q).measurable.enorm.aemeasurable]; exact hfin.ne)]
  exact tsum_congr hint

end GlobalTheory.CosetDisint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnitaryAdelicEqSumFiniteCosetsRealIntegrStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unitaryAdelic_eq_sum_finiteCosets_realIntegrals : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → IsOpen {h : GA D W | finE W h ∈ K} → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ℂ, Continuous Z → Integrable Z ν → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ))‖ₑ ∂(Measure.pi mR) < ⊤ ∧ ∫ g, Z g ∂ν = ∫ b, ∑' x : FinCos W (levA W K), Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  first | exact @GlobalTheory.CosetDisint.integral_eq_cosetSum | exact GlobalTheory.CosetDisint.integral_eq_cosetSum | (intros; apply GlobalTheory.CosetDisint.integral_eq_cosetSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonPrincipalLevelContinuousRightInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonPrincipalLevelContinuousRightInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrincPet

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem value_laws (hP : GlobalTheory.Published.CuspRapidDecay) {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    (hθ : IsInfFam θ) {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} (hχ : ∀ k ∈ J, χ k = 1)
    {U : MMap M} (hU : U ∈ Mult θ M J χ) :
    ∀ v, Continuous (U v) ∧ (∃ C : ℝ, ∀ g, ‖U v g‖ ≤ C) ∧ ∀ k ∈ J, ∀ g, U v (g * k) = U v g := by
  unfold Mult at hU
  induction hU using Submodule.span_induction with
  | mem T hT =>
    intro v
    refine ⟨(hT.aut v).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut v) (hT.cusp v), fun k hk g => ?_⟩
    rw [hT.lev v k hk g, hχ k hk, one_mul]
  | zero =>
    intro v
    exact ⟨continuous_const, ⟨0, fun g => by simp⟩, fun k _ g => by simp⟩
  | add U U' _ _ h h' =>
    intro v
    obtain ⟨c1, ⟨C1, b1⟩, i1⟩ := h v
    obtain ⟨c2, ⟨C2, b2⟩, i2⟩ := h' v
    refine ⟨by simpa using c1.add c2, ⟨C1 + C2, fun g => ?_⟩, fun k hk g => ?_⟩
    · simp only [MultilinearMap.add_apply, Pi.add_apply]
      exact (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g))
    · simp only [MultilinearMap.add_apply, Pi.add_apply, i1 k hk g, i2 k hk g]
  | smul a U _ h =>
    intro v
    obtain ⟨c1, ⟨C1, b1⟩, i1⟩ := h v
    refine ⟨by simpa using c1.const_smul a, ⟨‖a‖ * C1, fun g => ?_⟩, fun k hk g => ?_⟩
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (b1 g) (norm_nonneg _)
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, i1 k hk g]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_triv (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
  have hP : (R.datWp i R.triv).P = LevelP.triv R.Pg D.R.r ℂ := rfl
  have hs : (R.datWp i R.triv).s = 0 := rfl
  have hQ : (R.datWp i R.triv).Q = ∅ := rfl
  have hchi : ∀ (Q : LevelP R.Pg D.R.r ℂ), Q = LevelP.triv R.Pg D.R.r ℂ → ∀ y : Q.H, Q.chi y = 1 := by
    rintro _ rfl y; rfl
  have h1 : ∀ x, ext1 (R.datWp i R.triv).P.H (⇑(R.datWp i R.triv).P.chi) x = 1 := by
    intro x
    unfold ext1
    split
    · exact hchi _ hP _
    · rfl
  simp only [levChi, levFn, h1, hs, hQ, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one,
    Units.val_one]

end GlobalTheory.PrincPet

namespace GlobalTheory.PrincPet

theorem petW_continuous_rightInv : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i σ, IsOpen {h : GA D (Wc D i) | finE (Wc D i) h ∈ lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv)} ∧ ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec, (Continuous fun g => petW R i (rTr (Wc D i) g (U₁ v₁)) (U₂ v₂)) ∧ ∀ g, ∀ k ∈ levW R i, petW R i (rTr (Wc D i) (g * k) (U₁ v₁)) (U₂ v₂) = petW R i (rTr (Wc D i) g (U₁ v₁)) (U₂ v₂) := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hC i σ
  refine ⟨GlobalTheory.AdelicScalar.isOpen_level (Wc D i) (R.βW i) (R.datWp i R.triv), ?_⟩
  intro U₁ hU₁ U₂ hU₂ v₁ v₂
  have hθ : IsInfFam R.θ := hC.models.inf
  have hχ : ∀ k ∈ levS (Wc D i) (R.βW i) (R.datWp i R.triv),
      levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := fun k _ => levChi_triv R i k
  obtain ⟨c₁, ⟨C₁, b₁⟩, inv₁⟩ := value_laws hP hθ hχ hU₁ v₁
  obtain ⟨c₂, ⟨C₂, b₂⟩, -⟩ := value_laws hP hθ hχ hU₂ v₂
  refine ⟨?_, fun g k hk => ?_⟩
  · have : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    have hμ := (hC.models.νW i).1.1
    have hfin : R.νW i (R.fdW i) < ⊤ :=
      GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol (Wc D i) (R.νW i) (R.fdW i) hμ (hC.models.νW i).2
    haveI : IsFiniteMeasure ((R.νW i).restrict (R.fdW i)) := isFiniteMeasure_restrict.2 hfin.ne
    have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (b₁ 1)
    show Continuous fun g => ∫ x in R.fdW i, rTr (Wc D i) g (U₁ v₁) x * starRingEnd ℂ (U₂ v₂ x) ∂(R.νW i)
    refine continuous_of_dominated (bound := fun _ => C₁ * C₂) (fun g => ?_) (fun g => ?_) (integrable_const _) ?_
    · exact ((c₁.comp (continuous_id.mul continuous_const)).mul
        (Complex.continuous_conj.comp c₂)).aestronglyMeasurable
    · refine .of_forall fun x => ?_
      simp only [rTr, norm_mul, Complex.norm_conj]
      exact mul_le_mul (b₁ _) (b₂ _) (norm_nonneg _) hC₁
    · exact .of_forall fun x => (c₁.comp (continuous_const.mul continuous_id)).mul continuous_const
  · have e : rTr (Wc D i) (g * k) (U₁ v₁) = rTr (Wc D i) g (U₁ v₁) := by
      funext x
      simp only [rTr]
      rw [← mul_assoc]
      exact inv₁ k hk (x * g)
    rw [e]

end GlobalTheory.PrincPet

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonPrincipalLevelContinuousRightInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_principal_level_continuous_right_invariant : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i σ, IsOpen {h : GA D (Wc D i) | finE (Wc D i) h ∈ lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i R.triv)} ∧ ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec, (Continuous fun g => petW R i (rTr (Wc D i) g (U₁ v₁)) (U₂ v₂)) ∧ ∀ g, ∀ k ∈ levW R i, petW R i (rTr (Wc D i) (g * k) (U₁ v₁)) (U₂ v₂) = petW R i (rTr (Wc D i) g (U₁ v₁)) (U₂ v₂) := by
  exact @GlobalTheory.PrincPet.petW_continuous_rightInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductFormulaDefiniteOfRallisConverge
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IPFConv

theorem integrableOn_of_quot {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsMulLeftInvariant]
    {𝓕 : Set (GA D V)} (hFD : IsFundamentalDomain (GQ V) 𝓕 μ) {φ : GA D V → ℂ}
    (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ)
    (h : Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ)) : IntegrableOn φ 𝓕 μ := by
  have h1 := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hFD).1 (memLp_one_iff_integrable.2 h)
  rw [hφ.lift_descend] at h1
  exact memLp_one_iff_integrable.1 h1

theorem thetaKO_left_snd {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χV χW ω)
    {φ : WO V W → ℂ} (hf : IsThetaFunO ψ V W φ) (h : GA D V) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ W) (fun g => thetaKO ω h g φ) := fun γ hγ g => by
  have e : ((h, γ * g) : GA D V × GA D W) = (1, γ) * (h, g) := by simp
  show thetaKO ω h (γ * g) φ = thetaKO ω h g φ
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ φ hf)

theorem innerProductFormulaC_of_convergent : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hConv hpar
  intro i t σ s P cμ cη m ω BW f₀ f c io hL
  intro ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR U₁ hU₁ U₂ hU₂ v₁ v₂ Q₁ Q₂
  intro φ₁ φ₂ F₁ F₂ Z pt
  have hCore : GlobalTheory.Hk3.Core R F := hL.1
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω := hL.2.2.2.2.2.1
  obtain ⟨hwitt, hrank, cA, hSet, hA0⟩ := GlobalTheory.T.liftPair_positiveDefinite_wittIndexZero_cartan R F hCore hpar i σ
  have hFo₁ := GlobalTheory.T.thetaDatum_fockVectors_areFockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₁
  have hFo₂ := GlobalTheory.T.thetaDatum_fockVectors_areFockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₂
  have hW := hCore.models.νW i
  haveI : (R.νW i).IsHaarMeasure := hW.1.1
  have hFDW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := hW.2
  haveI : ν.IsHaarMeasure := hν.1.1
  have hFDV : IsFundamentalDomain (GQ (Vc D i)) 𝓕 ν := hν.2
  have hF₁ : F₁ ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := hA0 U₁ hU₁ v₁
  have hF₂ : F₂ ∈ GlobalTheory.Cusp.A0 R.θ (Wc D i) cA := hA0 U₂ hU₂ v₂
  have hL₁ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) F₁ := (Submodule.mem_inf.1 hF₁).2.2.1
  have hL₂ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) F₂ := (Submodule.mem_inf.1 hF₂).2.2.1
  have hKP : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair R.ψ R.θ (Wc D i) (Vc D i) (cμ * cη⁻¹) cμ (cart (R.MW i σ)) (fun _ => 1)
      true (fun _ => True) (fun _ => True) (fun g h => thetaKO ω h g φ₁) (fun g h => thetaKO ω h g φ₂)
      (fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂) :=
    ⟨ω, φ₁, φ₂, hω, hFo₁, hFo₂, trivial, trivial, fun _ _ => rfl, fun _ _ => rfl, μ, 𝓧, hμ, fun _ => rfl⟩
  obtain ⟨hC₁, hC₂, hInt, hEq⟩ := hConv R.ψ R.θ (Wc D i) (Vc D i) (cμ * cη⁻¹) cμ (cart (R.MW i σ)) (fun _ => 1) D.R.t
    cA true (fun g h => thetaKO ω h g φ₁) (fun g h => thetaKO ω h g φ₂) (fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂)
    (R.νW i) ν F₁ F₂ hSet (Or.inl hwitt) hrank hKP inferInstance inferInstance hF₁ hF₂
  have hpetW : ∀ u₁ u₂ : GA D (Wc D i) → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) u₁ →
      GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) u₂ → GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) u₁ u₂ = petW R i u₁ u₂ :=
    fun u₁ u₂ h₁ h₂ => GlobalTheory.AutomorphicL2Unitary.pet_eq hFDW h₁ h₂
  have hlift₁ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift (R.νW i) (fun g h => thetaKO ω h g φ₁) F₁ = upLift R i ω φ₁ F₁ :=
    funext fun h => hpetW _ _ (thetaKO_left_snd hω hFo₁.1 h) hL₁
  have hlift₂ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift (R.νW i) (fun g h => thetaKO ω h g φ₂) F₂ = upLift R i ω φ₂ F₂ :=
    funext fun h => hpetW _ _ (thetaKO_left_snd hω hFo₂.1 h) hL₂
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv at hC₁ hC₂
  rw [hlift₁] at hC₁ hEq
  rw [hlift₂] at hC₂ hEq
  have hZeq : ∀ g, l2 μ 𝓧 (ω (1, g) φ₁) φ₂ *
      conj (GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) (rTr (Wc D i) g F₁) F₂) = Z g := fun g => by
    rw [hpetW (rTr (Wc D i) g F₁) F₂ (hL₁.mul_right g) hL₂]
  have hpc := GlobalTheory.T.petersson_principal_level_continuous_right_invariant hP R F hCore i σ
  have hZc : Continuous Z :=
    (GlobalTheory.T.continuous_weilCoefficient_fockVectors R F i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hμ Q₁ Q₂).mul
      (Complex.continuous_conj.comp (hpc.2 U₁ hU₁ U₂ hU₂ _ _).1)
  have hZi : Integrable Z (R.νW i) := hInt.congr (ae_of_all _ hZeq)
  have hZr : ∀ g, ∀ k ∈ levW R i, Z (g * k) = Z g := fun g k hk => by
    have hk1 := GlobalTheory.T.principalLevel_fixes_fockVectors_finiteDatum R F i t σ s P cμ cη m ω BW f₀ f c io hL Q₁ k hk
    have e : (((1 : GA D (Vc D i)), g * k) : GA D (Vc D i) × GA D (Wc D i)) = (1, g) * (1, k) := by simp
    show l2 μ 𝓧 (ω (1, g * k) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) (g * k) F₁) F₂) =
      l2 μ 𝓧 (ω (1, g) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) g F₁) F₂)
    rw [e, map_mul, Module.End.mul_apply, hk1, (hpc.2 U₁ hU₁ U₂ hU₂ _ _).2 g k hk]
  obtain ⟨hfin, hdis⟩ := GlobalTheory.T.integral_unitaryAdelic_eq_sum_finiteCosets_realIntegrals D R.θ hSet.2.2.2.1 (Wc D i) hSet.2.2.2.2.1 _ (R.νW i) hW.1 hpc.1 Fr hFr mR
    hmR Z hZc hZi hZr
  refine ⟨fun h => ?_, ?_, hfin, ?_⟩
  · have hLp : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Wc D i)) (fun g => thetaKO ω h g φ₁ * starRingEnd ℂ (F₁ g)) :=
      fun γ hγ g => by
        have e1 : thetaKO ω h (γ * g) φ₁ = thetaKO ω h g φ₁ := thetaKO_left_snd hω hFo₁.1 h γ hγ g
        have e2 : F₁ (γ * g) = F₁ g := hL₁ γ hγ g
        show thetaKO ω h (γ * g) φ₁ * starRingEnd ℂ (F₁ (γ * g)) = _
        rw [e1, e2]
    exact integrableOn_of_quot hFDW hLp (hC₁.1 h)
  · have hLp : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (Vc D i))
        (fun h => upLift R i ω φ₁ F₁ h * starRingEnd ℂ (upLift R i ω φ₂ F₂ h)) := fun γ hγ g => by
      have e1 : upLift R i ω φ₁ F₁ (γ * g) = upLift R i ω φ₁ F₁ g := hC₁.2.1 γ hγ g
      have e2 : upLift R i ω φ₂ F₂ (γ * g) = upLift R i ω φ₂ F₂ g := hC₂.2.1 γ hγ g
      show upLift R i ω φ₁ F₁ (γ * g) * starRingEnd ℂ (upLift R i ω φ₂ F₂ (γ * g)) = _
      rw [e1, e2]
    exact integrableOn_of_quot hFDV hLp (hC₁.2.integrable_mul_conj hC₂.2)
  · have hvol : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Vc D i) ν = (ν 𝓕).toReal := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, GlobalTheory.AutomorphicL2Unitary.autMeasure, Measure.real, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hFDV]
    have hpV : GlobalTheory.Cusp.petersson (Vc D i) ν (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) =
        l2 ν 𝓕 (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) := GlobalTheory.AutomorphicL2Unitary.pet_eq hFDV hC₁.2.1 hC₂.2.1
    have hI : ∫ g, l2 μ 𝓧 (ω (1, g) φ₁) φ₂ *
        conj (GlobalTheory.Cusp.petersson (Wc D i) (R.νW i) (rTr (Wc D i) g F₁) F₂) ∂(R.νW i) = ∫ g, Z g ∂(R.νW i) :=
      integral_congr_ae (ae_of_all _ hZeq)
    rw [hpV, hvol, hI, hdis] at hEq
    exact hEq

end GlobalTheory.IPFConv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductFormulaDefiniteOfRallisConvergeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaInnerProductFormulaDefinite_of_rallisConvergent : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  first | exact @GlobalTheory.IPFConv.innerProductFormulaC_of_convergent | exact GlobalTheory.IPFConv.innerProductFormulaC_of_convergent | (intros; apply GlobalTheory.IPFConv.innerProductFormulaC_of_convergent <;> assumption)
end
