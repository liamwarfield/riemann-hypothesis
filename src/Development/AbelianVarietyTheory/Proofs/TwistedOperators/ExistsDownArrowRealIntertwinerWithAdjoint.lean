module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeSpanProjectionPreservesFiniteDimInvariantSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridColumnParametersNegatedDataARPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerDownArrowTransportAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNonzeroFockVacuumConjUnitVacuumNegSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNonzeroFockVacuumConjUnitVacuumNegSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.VacCjNeg

variable {D : D7}


open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem dRho_cj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (θ : InfFam D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ S T) θ τ z (cj id f) = cj id (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ z f) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id f) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) 0)
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id f) x) =
      fun t => star (heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) f x) := by
    funext t
    rw [GlobalTheory.CjNeg.heis_negS' hψ]
    rfl
  rw [e, deriv.star]
  rfl

theorem isVacVec_cj_of_isVac_neg : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (f : WO S.V T.V → ℂ), GlobalTheory.Grid.IsVac ψ θ true S T f →
      GlobalTheory.Chain.IsVacVec ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := by
  intro D S T ψ θ f h
  obtain ⟨hψ, hv⟩ := h
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f := hv.theta
  refine ⟨GlobalTheory.CjNeg.theta_negS' hψ (show IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S.V) T.V f from hth), ?_, fun τ => ?_⟩
  · intro h0
    have hf0 : f = 0 := by
      rw [← GlobalTheory.CjNeg.cj_id_cj_id f, h0]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    obtain ⟨⟨p, hp⟩, hall⟩ := hv.norm
    have h1 := hall p hp
    rw [hf0] at h1
    simp [nrm2] at h1
  · intro z
    have h0 : annih (heisO ψ (GlobalTheory.Grid.neg S.V) T.V) θ τ (cplxO (-(cart S.M τ)) (cart T.M τ)) z f = 0 :=
      hv.fock τ z
    have hJ : cplxO (-(cart S.M τ)) (cart T.M τ) z = -cplxO (cart S.M τ) (cart T.M τ) z := by
      simp [cplxO]
    unfold annih at h0 ⊢
    rw [hJ, GlobalTheory.FockAdjoint.dRho_neg' hψ hv.inf hth] at h0
    rw [dRho_cj hψ, dRho_cj hψ]
    funext x
    have h2 := congrFun h0 x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply] at h2 ⊢
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq]
    have e := congrArg (starRingEnd ℂ) h2
    simp only [map_add (f := _), map_mul, map_neg, Complex.conj_I, map_zero] at e
    linear_combination e

end GlobalTheory.VacCjNeg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNonzeroFockVacuumConjUnitVacuumNegSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNonzeroFockVacuum_conj_unitVacuum_negSpace : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), GlobalTheory.Grid.IsVac ψ θ true S T f → GlobalTheory.Chain.IsVacVec ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := by
  first | exact @GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg | exact GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg | (intros; apply GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerDownArrowTransportAdjoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.AdjTr

variable {D : D7}

theorem isIntw_transport {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X Y P P' : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P'] [Module ℂ P'] (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ω : GA D V × GA D W →* Module.End ℂ (X → ℂ)) (ω₀ : GA D V × GA D W →* Module.End ℂ (Y → ℂ))
    (pt : P → (X → ℂ)) (pt₀ : P' → (Y → ℂ)) (e : P ≃ₗ[ℂ] P') (b : Y → X) (It : P' →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (hpt : ∀ φ, pt₀ (e φ) = pt φ ∘ b) (hω : ∀ p F, ω₀ p (F ∘ b) = ω p F ∘ b) (h : IsIntw θ M M' ω₀ pt₀ It) :
    IsIntw θ M M' ω pt (It ∘ₗ e.toLinearMap) := by
  refine { ne := ?_, bdd := ?_, eqK := ?_, eqg := ?_, invK := ?_, invg := ?_ }
  · intro h0
    apply h.ne
    apply LinearMap.ext
    intro φ
    have hφ := congrArg (fun L => L (e.symm φ)) h0
    simpa using hφ
  · intro φ w
    exact h.bdd (e φ) w
  · intro τ g hg φ φ' hφ v
    exact h.eqK τ g hg (e φ) (e φ') (by rw [hpt, hpt, hφ, hω]) v
  · intro τ Y hY φ φ' hd v
    exact h.eqg τ Y hY (e φ) (e φ') (fun z => by
      simpa only [hpt, hω, Function.comp_apply] using hd (b z)) v
  · intro τ k hk φ φ' v v' hφ hv
    exact h.invK τ k hk (e φ) (e φ') v v' (by rw [hpt, hpt, hφ, hω]) hv
  · intro τ Y hY φ φ' v v' hd hv
    exact h.invg τ Y hY (e φ) (e φ') v v' (fun z => by
      simpa only [hpt, hω, Function.comp_apply] using hd (b z)) hv


open GlobalTheory.FockAdjoint in
theorem ptOf_dag {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {V W : HSp D} {SV SW : D.what₂.Tau → SPar} (M : DSModel V SV) (M' : DSModel W SW) {g : WO V W → ℂ}
    (hg : IsThetaFunO ψ V W g) (Q : PolF D W.rank V.rank) :
    ptOf ψ θ M' M (dag V W g) (jHom (Fr.ofModel M) (Fr.ofModel M') Q) = dag V W (ptOf ψ θ M M' g Q) := by
  set A := Fr.ofModel M
  set B := Fr.ofModel M'
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hψ V W
  have cA := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A
  have cB := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B
  have hd := L.theta g hg
  show ptF ψ θ B A (dag V W g) (jHom A B Q) = dag V W (ptF ψ θ A B g Q)
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [jHom_C, ← mul_one (MvPolynomial.C _), ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one,
      dag_smul']
  | add p q hp hq => rw [map_add (f := _), ptF_add, ptF_add, hp, hq, dag_add]
  | mul_X p v hp =>
    obtain ⟨τ, i, j⟩ := v
    rw [map_mul, jHom_X, mul_comm (jHom A B p), mul_assoc, ptF_C, ptF_X_mul hψ hθ B A hd, hp, mul_comm p,
      ptF_X_mul hψ hθ A B hg]
    dsimp only
    rw [aPlus_dag hψ hθ L τ (cA τ) (cB τ) _ (ptF_theta hψ hθ A B hg p), cdag_unitMap,
      aPlus_real_smul hψ hθ (ptF_theta hψ hθ A B hg p), dag_smul', Complex.conj_ofReal, smul_smul]
    rw [show ((sg (B.ε τ i) * sg (A.ε τ j) : ℝ) : ℂ) = sgv A B τ i j from rfl, sgv_mul_self, one_smul]

open GlobalTheory.FockAdjoint in
theorem jHom_map_conj {S T : HSp D} (A : Fr S) (B : Fr T) (P : PolF D T.rank S.rank) :
    jHom A B (MvPolynomial.map (starRingEnd ℂ) P) = swapHom A B P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [jHom_C, swapHom]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, MvPolynomial.map_X, jHom_X, map_mul, swapHom_X]

theorem dag_cj {S T : HSp D} (F : WO S T → ℂ) : dag S T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F) = F ∘ adjO S T := by
  funext y; simp [dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

end GlobalTheory.AdjTr


open GlobalTheory.AdjTr in
theorem GlobalTheory.AdjTr.downArrow_transport : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χ : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S.V T.V) (f : WO S.V T.V → ℂ), IsInfFam θ → GlobalTheory.Grid.IsWeil ψ true S.V T.V χ χ ω →
    GlobalTheory.Grid.IsVac ψ θ true S T f →
    ∃ (ω₀ : GlobalTheory.Grid.WRep T.V S.V) (f₀ : WO T.V S.V → ℂ) (χ₀ : (AE D)ˣ →* Circle)
      (e : GlobalTheory.Grid.Pol S T ≃ₗ[ℂ] PolF D S.V.rank T.V.rank),
      IsWeilDatumO ψ T.V S.V χ₀ χ₀ ω₀ ∧ (∀ τ a, HasInfExp D χ τ a → HasInfExp D χ₀ τ (-a)) ∧
      IsVacVec ψ θ T.M S.M f₀ ∧
      ∀ It : PolF D S.V.rank T.V.rank →ₗ[ℂ] SmT S.M →ₗ[ℂ] SmT T.M, IsItW θ T.M S.M ω₀ (ptOf ψ θ T.M S.M f₀) It →
        GlobalTheory.Grid.IsIntw θ T.M S.M ω.swap (GlobalTheory.Grid.fock ψ θ true S T f) (It ∘ₗ e.toLinearMap) := by
  intro D S T ψ θ χ ω f hθ hW hV
  set A := Fr.ofModel S.M
  set B := Fr.ofModel T.M
  have hstd : IsStdChar D ψ (-1) := hV.1
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hstd S.V T.V
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f := hV.2.theta
  have hvv := GlobalTheory.T.isNonzeroFockVacuum_conj_unitVacuum_negSpace S T ψ θ f hV
  refine ⟨adjRep ω, dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f), χ⁻¹, (swapEquiv A B).toLinearEquiv, ?_,
    fun τ a h => GlobalTheory.Mem.HeckeExp.hasInfExp_inv h, ⟨L.theta _ hvv.theta, ?_, fun τ => GlobalTheory.FockAdjoint.vac_dag hstd hθ L τ
      (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ) hvv.theta (hvv.vac τ)⟩,
    fun It hIt => ?_⟩
  · exact GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ S.V T.V χ⁻¹ χ⁻¹ (conjRep ω) (GlobalTheory.T.isWeilDatum_complexConjugate_of_negHermitianSpace ψ S.V T.V χ χ ω hW)
  · intro h0
    apply hvv.ne
    funext x
    have := congrFun h0 (adjO T.V S.V x)
    simp only [dag, GlobalTheory.AdjLawPf.adj_invol, Pi.zero_apply, map_eq_zero] at this
    exact this
  · refine isIntw_transport θ T.M S.M ω.swap (adjRep ω) (GlobalTheory.Grid.fock ψ θ true S T f)
      (ptOf ψ θ T.M S.M (dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f))) (swapEquiv A B).toLinearEquiv (adjO S.V T.V) It
      (fun φ => ?_) (fun p F => ?_) ((GlobalTheory.Grid.isIntw_iff θ T.M S.M _ _ It).2 hIt)
    · show ptOf ψ θ T.M S.M (dag S.V T.V (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)) (swapHom A B φ) = _
      rw [← jHom_map_conj, ptOf_dag hstd hθ S.M T.M hvv.theta, ← GlobalTheory.T.conj_fockPureTensorMap_negFormSpace_eq S T ψ θ f hstd hθ hth, dag_cj]
    · obtain ⟨h, g⟩ := p
      rw [adjRep_apply, WRep.swap_apply]
      funext y
      simp only [Function.comp_apply, GlobalTheory.AdjLawPf.adj_invol]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerDownArrowTransportAdjointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realIntertwiner_downArrow_transport_adjoint : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χ : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S.V T.V) (f : WO S.V T.V → ℂ), IsInfFam θ → GlobalTheory.Grid.IsWeil ψ true S.V T.V χ χ ω →
    GlobalTheory.Grid.IsVac ψ θ true S T f →
    ∃ (ω₀ : GlobalTheory.Grid.WRep T.V S.V) (f₀ : WO T.V S.V → ℂ) (χ₀ : (AE D)ˣ →* Circle)
      (e : GlobalTheory.Grid.Pol S T ≃ₗ[ℂ] PolF D S.V.rank T.V.rank),
      IsWeilDatumO ψ T.V S.V χ₀ χ₀ ω₀ ∧ (∀ τ a, HasInfExp D χ τ a → HasInfExp D χ₀ τ (-a)) ∧
      IsVacVec ψ θ T.M S.M f₀ ∧
      ∀ It : PolF D S.V.rank T.V.rank →ₗ[ℂ] SmT S.M →ₗ[ℂ] SmT T.M, IsItW θ T.M S.M ω₀ (ptOf ψ θ T.M S.M f₀) It →
        GlobalTheory.Grid.IsIntw θ T.M S.M ω.swap (GlobalTheory.Grid.fock ψ θ true S T f) (It ∘ₗ e.toLinearMap) := by
  first | exact @GlobalTheory.AdjTr.downArrow_transport | exact GlobalTheory.AdjTr.downArrow_transport | (intros; apply GlobalTheory.AdjTr.downArrow_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerAdjointSmoothValues
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerAdjointSmoothValues
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.AdjSmooth

variable {D : D7}

theorem eq_zero_of_ellT_smooth {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (u : SmT M')
    (hu : ∀ v : M'.Vec, ellT M' (fun τ => (v τ : M'.H τ)) (inclT M' u) = 0) : u = 0 := by
  classical
  obtain ⟨F, hF, h⟩ := exists_finite_support u
  obtain ⟨y, rfl⟩ := h F fun _ => le_rfl
  let o := fun τ => stdOrthonormalBasis ℂ (F τ)
  let b := Basis.piTensorProduct fun τ => (o τ).toBasis
  have key : ∀ i, b.coord i = ellT M' (fun τ => (((o τ (i τ) : F τ) : M'.sm τ) : M'.H τ)) ∘ₗ inclT M' ∘ₗ
      PiTensorProduct.map fun τ => (F τ).subtype := by
    intro i
    refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod, inclT, ellT_pure,
      Module.Basis.coord_apply, b]
    rw [Basis.piTensorProduct_repr_tprod_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [OrthonormalBasis.repr_apply_apply]
  have hy : y = 0 := by
    refine b.ext_elem fun i => ?_
    have h1 : b.coord i y = 0 := by
      rw [key]
      exact hu fun τ => (o τ (i τ) : M'.sm τ)
    change b.repr y i = b.repr 0 i
    rw [map_zero b.repr, Finsupp.zero_apply]
    exact h1
  rw [hy, map_zero]

end GlobalTheory.AdjSmooth

namespace GlobalTheory.AdjSmooth

open GlobalTheory.Chain.RealLine

variable {D : D7}

theorem exists_adj_glue {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : GlobalTheory.Grid.WRep V W)
    (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hC : GlobalTheory.Published.DiscreteSeriesCover)
    (hH : GlobalTheory.Published.HarishChandraModules) (hθ : IsInfFam θ)
    (hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (aS τ)))
    (hω : IsWeilExp ψ V W aS aT ω) (hf : IsVacVec ψ θ M M' f) (hI : IsItW θ M M' ω (ptOf ψ θ M M' f) It)
    (Ps : D.what₂.Tau → LPol W.rank V.rank) (w : M.Vec) :
    ∃ u : SmT M', ∀ v : M'.Vec,
      ellT M (fun τ => (w τ : M.H τ)) (inclT M (It (glue Ps) (PiTensorProduct.tprod ℂ v))) =
        conj (ellT M' (fun τ => (v τ : M'.H τ)) (inclT M' u)) := by
  classical
  obtain ⟨X, hX, -, -, -, -, h3, -⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hC hH
  have hB := GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hC hH D
  obtain ⟨χS, χT, hωd, he⟩ := hω
  have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_realPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hωd (he τ).1 (he τ).2 hf
  have key : ∀ τ, ∃ A₀ : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ,
      ∀ A, LocW M M' τ (aS τ) (aT τ) A → ∃ c : ℂ, A = c • A₀ := fun τ => by
    obtain ⟨t, al, be, ga, de, hd, e1, e2⟩ := hP τ
    exact loc_line hX h3 hH hB M M' τ hd e1 e2
  choose A₀ hA₀ using key
  let Fn : (∀ τ, LPol W.rank V.rank × M'.sm τ × M.H τ) → ℂ := fun a => ellT M (fun τ => (a τ).2.2)
    (inclT M (It (glue fun τ => (a τ).1) (PiTensorProduct.tprod ℂ fun τ => (a τ).2.1)))
  have part : ∀ τ a, ∃ B : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ, LocW M M' τ (aS τ) (aT τ) B ∧
      ∀ x, Fn (Function.update a τ x) = ⟪x.2.2, B x.1 x.2.1⟫_ℂ := by
    intro τ a
    obtain ⟨A, hA, hA'⟩ := GlobalTheory.T.exists_realIntertwiner_contraction_one_place D V W _ _ M M' θ ψ ω f τ _ _ It hθ (hv τ).2.1 (hv τ).2.2 hI
      (fun ρ => (a ρ).2.1) (fun ρ => (a ρ).2.2)
    obtain ⟨j, hj⟩ := exists_ins (fun ρ => (a ρ).1) τ
    refine ⟨A ∘ₗ j, locW_of_semiW hA hj, fun x => ?_⟩
    rw [LinearMap.comp_apply, hA' (j x.1) x.2.1 x.2.2, hj]
    have h1 : (fun ρ => (Function.update a τ x ρ).2.2) = Function.update (fun ρ => (a ρ).2.2) τ x.2.2 :=
      funext fun ρ => Function.apply_update (fun ρ (z : LPol W.rank V.rank × M'.sm ρ × M.H ρ) => z.2.2) a τ x ρ
    have h2 : (fun ρ => (Function.update a τ x ρ).1) = Function.update (fun ρ => (a ρ).1) τ x.1 :=
      funext fun ρ => Function.apply_update (fun ρ (z : LPol W.rank V.rank × M'.sm ρ × M.H ρ) => z.1) a τ x ρ
    have h3 : (fun ρ => (Function.update a τ x ρ).2.1) = Function.update (fun ρ => (a ρ).2.1) τ x.2.1 :=
      funext fun ρ => Function.apply_update (fun ρ (z : LPol W.rank V.rank × M'.sm ρ × M.H ρ) => z.2.1) a τ x ρ
    show ellT M (fun ρ => (Function.update a τ x ρ).2.2) (inclT M (It (glue fun ρ => (Function.update a τ x ρ).1)
      (PiTensorProduct.tprod ℂ fun ρ => (Function.update a τ x ρ).2.1))) = _
    rw [h1, h2, h3]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ a, Fn a = c * ∏ τ, ⟪(a τ).2.2, A₀ τ (a τ).1 (a τ).2.1⟫_ℂ := by
    refine eq_mul_prod_of_partial (fun τ x => ⟪x.2.2, A₀ τ x.1 x.2.1⟫_ℂ) Fn fun τ a => ?_
    obtain ⟨B, hB, hB'⟩ := part τ a
    obtain ⟨d, hd⟩ := hA₀ τ B hB
    exact ⟨d, fun x => by rw [hB', hd, LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_right]⟩
  by_cases h0 : ∀ a, Fn a = 0
  · refine ⟨0, fun v => ?_⟩
    rw [map_zero, map_zero, map_zero]
    exact h0 fun τ => (Ps τ, v τ, (w τ : M.H τ))
  push_neg at h0
  obtain ⟨a₀, ha₀⟩ := h0
  have loc : ∀ τ, ∃ (K : ℂ) (B : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), K ≠ 0 ∧
      LocW M M' τ (aS τ) (aT τ) B ∧
      ∀ x : LPol W.rank V.rank × M'.sm τ × M.H τ, K * ⟪x.2.2, A₀ τ x.1 x.2.1⟫_ℂ = ⟪x.2.2, B x.1 x.2.1⟫_ℂ := by
    intro τ
    obtain ⟨B, hB, hB'⟩ := part τ a₀
    have hpr : ∀ x, ∏ ρ ∈ Finset.univ.erase τ,
        ⟪(Function.update a₀ τ x ρ).2.2, A₀ ρ (Function.update a₀ τ x ρ).1 (Function.update a₀ τ x ρ).2.1⟫_ℂ =
        ∏ ρ ∈ Finset.univ.erase τ, ⟪(a₀ ρ).2.2, A₀ ρ (a₀ ρ).1 (a₀ ρ).2.1⟫_ℂ := fun x =>
      Finset.prod_congr rfl fun ρ hρ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]
    refine ⟨c * ∏ ρ ∈ Finset.univ.erase τ, ⟪(a₀ ρ).2.2, A₀ ρ (a₀ ρ).1 (a₀ ρ).2.1⟫_ℂ, B, ?_, hB, fun x => ?_⟩
    · intro hK
      apply ha₀
      rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), mul_left_comm, hK, mul_zero]
    · rw [← hB', hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hpr, Function.update_self]
      ring
  choose K B hK hB hKB using loc
  have adj : ∀ τ, ∃ b : M'.sm τ, ∀ y : M'.sm τ,
      ⟪(w τ : M.H τ), B τ (Ps τ) y⟫_ℂ = ⟪(b : M'.H τ), (y : M'.H τ)⟫_ℂ := by
    intro τ
    obtain ⟨b, hbK, hb⟩ := (hB τ).kT (Ps τ) (w τ)
    exact ⟨⟨b, (GlobalTheory.KFinLoc.kFin_smooth_absIrr hH D W S' M' τ).1 hbK⟩, hb⟩
  choose b hb using adj
  refine ⟨conj (c * ∏ τ, (K τ)⁻¹) • PiTensorProduct.tprod ℂ b, fun v => ?_⟩
  have e1 := hc fun τ => (Ps τ, v τ, (w τ : M.H τ))
  have e2 : ∀ τ, ⟪(w τ : M.H τ), A₀ τ (Ps τ) (v τ)⟫_ℂ = (K τ)⁻¹ * ⟪(b τ : M'.H τ), (v τ : M'.H τ)⟫_ℂ := fun τ => by
    rw [← hb, ← hKB τ (Ps τ, v τ, (w τ : M.H τ)), inv_mul_cancel_left₀ (hK τ)]
  have e3 : ellT M (fun τ => (w τ : M.H τ)) (inclT M (It (glue Ps) (PiTensorProduct.tprod ℂ v))) =
      c * ∏ τ, ((K τ)⁻¹ * ⟪(b τ : M'.H τ), (v τ : M'.H τ)⟫_ℂ) := by
    rw [← Finset.prod_congr rfl fun τ _ => e2 τ]
    exact e1
  rw [e3, map_smul, map_smul, inclT, PiTensorProduct.map_tprod, ellT_pure]
  simp [Finset.prod_mul_distrib, map_prod, inner_conj_symm, mul_assoc]

end GlobalTheory.AdjSmooth

namespace GlobalTheory.AdjSmooth

variable {D : D7}

theorem ellT_update_add {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : ∀ ρ, M.H ρ) (τ : D.what₂.Tau)
    (x y : M.H τ) (z : ⨂[ℂ] ρ, M.H ρ) [DecidableEq D.what₂.Tau] :
    ellT M (Function.update w τ (x + y)) z = ellT M (Function.update w τ x) z + ellT M (Function.update w τ y) z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    have e : ∀ u : M.H τ, (fun ρ => ⟪Function.update w τ u ρ, v ρ⟫_ℂ) =
        Function.update (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ ⟪u, v τ⟫_ℂ := fun u =>
      funext fun ρ => Function.apply_update (fun ρ (a : M.H ρ) => ⟪a, v ρ⟫_ℂ) w τ u ρ
    have h := (MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).map_update_add (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ ⟪x, v τ⟫_ℂ ⟪y, v τ⟫_ℂ
    simp only [map_smul, ellT_pure, smul_eq_mul]
    rw [← mul_add]
    congr 1
    have e2 : ∀ u : M.H τ, ∏ ρ, ⟪Function.update w τ u ρ, v ρ⟫_ℂ =
        MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ (Function.update (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ ⟪u, v τ⟫_ℂ) := fun u => by
      rw [MultilinearMap.mkPiAlgebra_apply, ← e u]
    rw [e2, e2, e2, inner_add_left, h]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    ring

theorem ellT_update_smul {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : ∀ ρ, M.H ρ) (τ : D.what₂.Tau)
    (c : ℂ) (x : M.H τ) (z : ⨂[ℂ] ρ, M.H ρ) [DecidableEq D.what₂.Tau] :
    ellT M (Function.update w τ (c • x)) z = conj c * ellT M (Function.update w τ x) z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    have e : ∀ u : M.H τ, (fun ρ => ⟪Function.update w τ u ρ, v ρ⟫_ℂ) =
        Function.update (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ ⟪u, v τ⟫_ℂ := fun u =>
      funext fun ρ => Function.apply_update (fun ρ (a : M.H ρ) => ⟪a, v ρ⟫_ℂ) w τ u ρ
    have h := (MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).map_update_smul (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ (conj c) ⟪x, v τ⟫_ℂ
    simp only [map_smul, ellT_pure, smul_eq_mul]
    have e2 : ∀ u : M.H τ, ∏ ρ, ⟪Function.update w τ u ρ, v ρ⟫_ℂ =
        MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ (Function.update (fun ρ => ⟪w ρ, v ρ⟫_ℂ) τ ⟪u, v τ⟫_ℂ) := fun u => by
      rw [MultilinearMap.mkPiAlgebra_apply, ← e u]
    rw [smul_eq_mul, smul_eq_mul] at h
    rw [e2, e2, inner_smul_left, h]
    simp only [RingHom.id_apply]
    ring
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), ha, hb]
    ring

theorem coe_update {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (w : M.Vec) (τ : D.what₂.Tau) (x : M.sm τ)
    [DecidableEq D.what₂.Tau] :
    (fun ρ => ((Function.update w τ x ρ : M.sm ρ) : M.H ρ)) = Function.update (fun ρ => (w ρ : M.H ρ)) τ (x : M.H τ) :=
  funext fun ρ => Function.apply_update (fun ρ (a : M.sm ρ) => (a : M.H ρ)) w τ x ρ

theorem adjoint_smooth : ∀ {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : GlobalTheory.Grid.WRep V W) (f : WO V W → ℂ)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    IsInfFam θ →
    (∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (aS τ))) →
    IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It →
    ∃ Tp : PolF D W.rank V.rank →ₗ⋆[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ (P : PolF D W.rank V.rank) (v : M'.Vec) (w : M.Vec),
      ellT M (fun τ => w τ) (inclT M (It P (PiTensorProduct.tprod ℂ v))) =
        starRingEnd ℂ (ellT M' (fun τ => v τ) (inclT M' (Tp P (PiTensorProduct.tprod ℂ w)))) := by
  intro D V W S S' M M' θ ψ aS aT ω f It hC hH hθ hP hω hf hI
  classical
  have hE : ∀ (P : PolF D W.rank V.rank) (w : M.Vec), ∃ u : SmT M', ∀ v : M'.Vec,
      ellT M (fun τ => (w τ : M.H τ)) (inclT M (It P (PiTensorProduct.tprod ℂ v))) =
        conj (ellT M' (fun τ => (v τ : M'.H τ)) (inclT M' u)) := by
    intro P w
    have hP' : P ∈ Submodule.span ℂ
        (Set.range (glue : (D.what₂.Tau → LPol W.rank V.rank) → PolF D W.rank V.rank)) := by
      rw [(GlobalTheory.T.gluing_law_holds D V.rank W.rank).1]
      trivial
    induction hP' using Submodule.span_induction with
    | mem P hP' =>
      obtain ⟨Ps, rfl⟩ := hP'
      exact exists_adj_glue M M' θ ψ aS aT ω f It hC hH hθ hP hω hf hI Ps w
    | zero => exact ⟨0, fun v => by simp⟩
    | add P Q _ _ h1 h2 =>
      obtain ⟨u1, h1⟩ := h1
      obtain ⟨u2, h2⟩ := h2
      exact ⟨u1 + u2, fun v => by simp only [map_add (f := _), LinearMap.add_apply, h1, h2]⟩
    | smul c P _ h1 =>
      obtain ⟨u, hu⟩ := h1
      exact ⟨conj c • u, fun v => by
        simp only [map_smul, LinearMap.smul_apply, hu, smul_eq_mul, map_mul, Complex.conj_conj]⟩
  choose U hU using hE
  have char : ∀ P w u, (∀ v : M'.Vec,
      ellT M (fun τ => (w τ : M.H τ)) (inclT M (It P (PiTensorProduct.tprod ℂ v))) =
        conj (ellT M' (fun τ => (v τ : M'.H τ)) (inclT M' u))) → U P w = u := by
    intro P w u h
    refine sub_eq_zero.1 (eq_zero_of_ellT_smooth M' _ fun v => ?_)
    have e := (hU P w v).symm.trans (h v)
    rw [(starRingEnd ℂ).injective.eq_iff] at e
    rw [map_sub, map_sub, e, sub_self]
  let mm : PolF D W.rank V.rank → MultilinearMap (RingHom.id ℂ) (fun τ => M.sm τ) (SmT M') := fun P =>
    { toFun := U P
      map_update_add' := fun w τ x y => by
        refine char P _ _ fun v => ?_
        rw [coe_update, Submodule.coe_add, ellT_update_add, ← coe_update, ← coe_update, hU, hU, map_add (f := _), map_add (f := _),
          map_add]
      map_update_smul' := fun w τ c x => by
        refine char P _ _ fun v => ?_
        rw [coe_update, Submodule.coe_smul, ellT_update_smul, ← coe_update, hU, map_smul, map_smul, smul_eq_mul,
          map_mul]
        rfl }
  have hmm : ∀ P w, mm P w = U P w := fun _ _ => rfl
  refine ⟨{ toFun := fun P => PiTensorProduct.lift (mm P)
            map_add' := fun P Q => PiTensorProduct.ext (MultilinearMap.ext fun w => ?_)
            map_smul' := fun c P => PiTensorProduct.ext (MultilinearMap.ext fun w => ?_) }, fun P v w => ?_⟩
  · simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, LinearMap.add_apply, hmm]
    refine char _ _ _ fun v => ?_
    rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), map_add (f := _), hU, hU, map_add (f := _), map_add (f := _), map_add (f := _)]
  · simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, LinearMap.smul_apply, hmm,
      RingHom.id_apply]
    refine char _ _ _ fun v => ?_
    rw [map_smul, LinearMap.smul_apply, map_smul, map_smul, hU, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul,
      Complex.conj_conj]
  · show _ = conj (ellT M' _ (inclT M' (PiTensorProduct.lift (mm P) (PiTensorProduct.tprod ℂ w))))
    rw [PiTensorProduct.lift.tprod, hmm]
    exact hU P w v

end GlobalTheory.AdjSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerAdjointSmoothValuesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realIntertwiner_adjoint_smoothValues : ∀ {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : GlobalTheory.Grid.WRep V W) (f : WO V W → ℂ)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    IsInfFam θ →
    (∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (aS τ))) →
    IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It →
    ∃ Tp : PolF D W.rank V.rank →ₗ⋆[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ (P : PolF D W.rank V.rank) (v : M'.Vec) (w : M.Vec),
      ellT M (fun τ => w τ) (inclT M (It P (PiTensorProduct.tprod ℂ v))) =
        starRingEnd ℂ (ellT M' (fun τ => v τ) (inclT M' (Tp P (PiTensorProduct.tprod ℂ w)))) := by
  first | exact @GlobalTheory.AdjSmooth.adjoint_smooth | exact GlobalTheory.AdjSmooth.adjoint_smooth | (intros; apply GlobalTheory.AdjSmooth.adjoint_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDownArrowRealIntertwinerWithAdjoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

namespace GlobalTheory.DownArrow

theorem itPair_gen (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
    (aS aT : D.what₂.Tau → ℚ) (hθ : IsInfFam θ)
    (hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (aS τ))) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, It ≠ 0 ∧
      ∀ ω f, IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨t, al, be, ga, de, hd, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 (GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D) M M' τ hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  refine ⟨It, hI.ne, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
    fun τ => (hv τ).2.2

theorem down_intertwiner_adj : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V) (f : WO (G.P (i + 1)).V (G.P i).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f → ∃ (It : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ[ℂ] SmT (G.P (i + 1)).M →ₗ[ℂ] SmT (G.P i).M) (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), GlobalTheory.Grid.IsIntw R.θ (G.P i).M (G.P (i + 1)).M ω.swap (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f) It ∧ (⟨ω, f, It⟩ : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i)).IsAdj U := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH F hC hgap G' W hW G hsp hch hag hcos i hi ω f hω hf
  have hθ : IsInfFam R.θ := hC.models.inf
  obtain ⟨ω₀, f₀, χ₀, e, hω₀, hχ₀, hf₀, htr⟩ :=
    GlobalTheory.T.realIntertwiner_downArrow_transport_adjoint (G.P (i + 1)) (G.P i) R.ψ R.θ (G.chi (D.R.m - i)) ω f hθ hω hf
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have hexp : ∀ τ, HasInfExp D (G.chi (D.R.m - i)) τ (GlobalTheory.Grid.cen D τ (D.R.m - i)) :=
    (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ (fun τ => (GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))
      (hch.tie _ hm1 hm2)).2 (hch.aux _ hm1 hm2).inf
  have hS : (G.P i).S = GlobalTheory.Grid.parP D i := (hsp.P i (by omega)).par
  have hS' : (G.P (i + 1)).S = GlobalTheory.Grid.parP D (i + 1) := (hsp.P (i + 1) (by omega)).par
  have hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      (G.P i).S τ = dualPar (signed (al ++ be) (ga ++ de) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) ∧
      (G.P (i + 1)).S τ = dualPar (signed (al ++ block t ++ de) (ga ++ be) (-(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))) :=
    fun τ => by
      obtain ⟨al, be, ga, de, hd, e1, e2⟩ := GlobalTheory.T.gridColumnParameters_negated_dataAR_pair D i hi τ
      exact ⟨_, al, be, ga, de, hd, by rw [hS]; exact e1, by rw [hS']; exact e2⟩
  obtain ⟨It, -, hIt⟩ := itPair_gen hDC hHC (G.P i).M (G.P (i + 1)).M R.θ R.ψ
    (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ)) (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ)) hθ hP
  have hωe : IsWeilExp R.ψ (G.P i).V (G.P (i + 1)).V (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))
      (fun τ => -(GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ)) ω₀ :=
    ⟨χ₀, χ₀, hω₀, fun τ => ⟨hχ₀ τ _ (hexp τ), hχ₀ τ _ (hexp τ)⟩⟩
  have hI := hIt ω₀ f₀ hωe hf₀
  obtain ⟨Tp, hTp⟩ := GlobalTheory.T.realIntertwiner_adjoint_smoothValues (G.P i).M (G.P (i + 1)).M R.θ R.ψ _ _ ω₀ f₀ It hDC hHC hθ hP hωe hf₀ hI
  refine ⟨It ∘ₗ e.toLinearMap, Tp.comp e.toLinearMap, htr It hI, fun P v w => ?_⟩
  exact hTp (e P) v w

end GlobalTheory.DownArrow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDownArrowRealIntertwinerWithAdjointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_downArrow_realIntertwiner_with_adjoint : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V) (f : WO (G.P (i + 1)).V (G.P i).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f → ∃ (It : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ[ℂ] SmT (G.P (i + 1)).M →ₗ[ℂ] SmT (G.P i).M) (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), GlobalTheory.Grid.IsIntw R.θ (G.P i).M (G.P (i + 1)).M ω.swap (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) f) It ∧ (⟨ω, f, It⟩ : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i)).IsAdj U := by
  first | exact @GlobalTheory.DownArrow.down_intertwiner_adj | exact GlobalTheory.DownArrow.down_intertwiner_adj | (intros; apply GlobalTheory.DownArrow.down_intertwiner_adj <;> assumption)
end
