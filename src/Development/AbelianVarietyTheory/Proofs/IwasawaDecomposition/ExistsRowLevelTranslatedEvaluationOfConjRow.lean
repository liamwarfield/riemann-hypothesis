module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ChoiceFinal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesSmoothAutomorphic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdempotentIntertwinerImagesCuspidalOfLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMemMultT
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEquivariantRealPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIntertwinerValuesSobolevContinuous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIntertwinerMapSobolevContinuousEachSlotStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIntertwinerMapSobolevSeparatelyContinuous
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem GlobalTheory.ConjRowCont.conjMap_sobCont_ofIdE : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : (MP R).Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : (MP R).H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) ((MP R).rep τ) ℓ ∧ ∀ w : (MP R).sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) x := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hιE _ _ hinf _ _ c hc Φ hΦ _ τ v x
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h R.θ hinf hιE
  exact GlobalTheory.ConjRowCont.sobCont_conjMap X h R.θ (MP R) t c hinf (fun k hk => (hf k).1 hk)
    (fun τ g hg => ⟨(hat τ g hg).1, (hat τ g hg).2.1⟩) hc Φ hΦ τ v x
end

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjIntertwinerMap_sobolevContinuous_separately : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : (MP R).Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : (MP R).H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) ((MP R).rep τ) ℓ ∧ ∀ w : (MP R).sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) x := by
  first | exact @GlobalTheory.ConjRowCont.conjMap_sobCont_ofIdE | exact GlobalTheory.ConjRowCont.conjMap_sobCont_ofIdE | (intros; apply GlobalTheory.ConjRowCont.conjMap_sobCont_ofIdE <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationMapSmoothAutomorphicValues
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationMapSmoothAutomorphicValues
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

section Gen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct
open GlobalTheory.ConjRowMult Formalism.L2.SG.EvalTOntoRep

namespace GlobalTheory.ConjEvalAut

theorem equiv_gen {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (t : GA D (D.sp.Y 0))
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (hθ : IsInfFam θ) (hιE : ∀ x : X.B.I.E, HEq (X.ιE x) x)
    (ht : t ∈ GfC (D.sp.Y 0))
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w))
    (Φ : X.B.Hs →L[ℂ] L2X X) (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re)
    (hrep : ∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) :
    ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t v) := by
  intro τ g hg v w hw
  obtain ⟨hfin, -, hreal, -⟩ := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hιE
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  set a := iotaX X h (atTau θ (D.sp.Y 0) τ g) with ha
  have hvec : vecC X M c (Function.update v τ w) =
      fun p => X.B.σ p (uMat (a.1 p)) (vecC X M c v p) := by
    refine vecC_eq X M c _ _ fun τ' => ?_
    have e1 : vecC X M c v (X.pl.symm τ') = c τ' (v τ' : M.H τ') := by
      unfold vecC
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    rw [e1]
    by_cases ht' : τ' = τ
    · subst ht'
      rw [Function.update_self, hw, hc τ' g hg]
    · rw [Function.update_of_ne ht', ha1 (X.pl.symm τ') (fun e => ht' (X.pl.symm.injective e))]
      have h1 : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds (X.pl.symm τ')).2.2.1.1.1
      have h2 : uMat (1 : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ'))) = 1 := rfl
      rw [h2, h1]
      rfl
  have htens : X.B.tens (vecC X M c (Function.update v τ w)) = X.B.σs a.1 (X.B.tens (vecC X M c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have haeq : ((a.1, 1) : X.B.I.GA) = a := Prod.ext rfl ha2.symm
  obtain ⟨T, hT, hTΦ⟩ := Submodule.mem_map.1 hΦ
  have hΦx : ∀ x, Φ x = X.B.Re (T x) := fun x => by rw [← hTΦ]; rfl
  have hcomm := (GlobalTheory.IdemProj.re_orth_proj X.B).2.1 a.1
  have key : ∀ x, Φ (X.B.σs a.1 x) = X.B.R a (Φ x) := by
    intro x
    rw [hΦx, hΦx, ← haeq]
    have e1 := congrArg (fun L => L x) (hT a.1)
    simp only [ContinuousLinearMap.comp_apply] at e1
    rw [e1]
    exact congrArg (fun L => L (T x)) hcomm
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' : IsContRep X (Φ (X.B.tens (vecC X M c (Function.update v τ w)))) (fun x => ψ (x * a)) := by
    rw [htens, key]
    exact contRep_reg X hψ a
  funext y
  rw [conjMap_apply, contRepL_spec X hψ']
  show _ = conjMap X M c Φ h t v (y * atTau θ (D.sp.Y 0) τ g)
  rw [conjMap_apply, contRepL_spec X hψ]
  congr 1
  have hti : (iotaX X h t⁻¹).1 = 1 := by rw [map_inv, Prod.fst_inv, (hfin t).1 ht, inv_one]
  rw [map_mul, map_mul, map_mul, ← ha, mul_assoc]
  beta_reduce
  rw [mul_assoc]
  congr 2
  exact Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, hti, one_mul, mul_one])
    (by rw [Prod.snd_mul, Prod.snd_mul, ha2, one_mul, mul_one])


set_option maxHeartbeats 1000000 in
theorem cont_gen {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (t : GA D (D.sp.Y 0))
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (hθ : IsInfFam θ) (hE : ∀ x : X.B.I.E, HEq (X.ιE x) x)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w))
    (Φ : X.B.Hs →L[ℂ] L2X X) (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re)
    (hrep : ∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) :
    ∀ (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  intro τ₀ v₀ x₀
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.ConjRowCont.exists_conj_multilinear X M c Φ
  obtain ⟨N, hN1, hN2, hN3⟩ := GlobalTheory.TensRep.exists_mmap (ι := fun v x => X.B.I.ext v (T x)) hθ M h1 h2 h5 h6 h7 h8 h9
    (fun γ hγ v => h10 γ ((GlobalTheory.ConjRowCont.iotaX_rat_iff X h γ).1 hγ) v) hU Ψ
    (fun τ a ha y => by
      obtain ⟨q1, q2, -⟩ := hat τ a ha
      rw [h3, hΨ, hΨ, GlobalTheory.ConjRowCont.reg_star]
      congr 1
      refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
      obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
      rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
      by_cases e : τ' = τ
      · subst e
        rw [Function.update_self]
        exact hc _ a ha _
      · rw [Function.update_of_ne e]
        have q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
        rw [q]
        have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
        show _ = X.B.σ (X.pl.symm τ') 1 _
        rw [this]
        rfl)
    (fun y k hk hk' => by
      rw [h3, hΨ, GlobalTheory.ConjRowCont.reg_star]
      have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
      rw [e, hlev _ (hUg k hk)])
  have key : ∀ (u : M.Vec) y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = N u (y * t⁻¹) := by
    intro u y
    have r1 : GlobalTheory.Dec.IsContRep X.B (Ψ fun τ => (u τ : M.H τ)) (fun z => N u (T.symm z)) := by
      refine GlobalTheory.RepSmooth.isContRep_of_ae X.B ((hN2 u).3.comp hT') (fun γ hγ z => ?_) ?_
      · rw [map_mul]
        refine (hN2 u).1 _ ((GlobalTheory.ConjRowCont.iotaX_rat_iff X h _).2 ?_) _
        have : iotaX X h (T.symm γ) = γ := T.apply_symm_apply γ
        rwa [this]
      · filter_upwards [h4 _ (hN1 u)] with z hz
        rw [← hz, T.apply_symm_apply]
    have r2 : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))
        (fun z => star (N u (T.symm z))) := by
      refine ⟨r1.1.star, fun γ hγ z => congrArg star (r1.2.1 γ hγ z), ?_⟩
      have r3 := r1.2.2
      rw [hΨ] at r3
      filter_upwards [r3, Lp.coeFn_star (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))] with z a1 a2
      rw [← a1]
      exact (star_star _).symm.trans (congrArg star a2.symm)
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X r2, star_star]
    exact congrArg (N u) (T.symm_apply_apply _)
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := hN3 τ₀ v₀ (x₀ * t⁻¹)
  exact ⟨ℓ, hℓ1, fun w => (hℓ2 w).trans (key _ _).symm⟩


set_option maxHeartbeats 800000 in
theorem conjMap_isAutFunSm_gen {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (t : GA D (D.sp.Y 0))
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (hθ : IsInfFam θ) (hid : ∀ x : X.B.I.E, HEq (X.ιE x) x)
    (ht : t ∈ GfC (D.sp.Y 0))
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w))
    (Φ : X.B.Hs →L[ℂ] L2X X) (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re)
    (hrep : ∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) :
    ∀ u : M.Vec, IsAutFunSm θ (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  have he : GlobalTheory.RepSmooth.IsEquiv θ (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) :=
    equiv_gen X h θ M t c hθ hid ht hc Φ hΦ hrep
  have hs : GlobalTheory.RepSmooth.IsSob (GlobalTheory.ConjRowMult.conjMap X M c Φ h t) :=
    cont_gen X h θ M t c hθ hid hc Φ hΦ hrep
  obtain ⟨hrat, hfst, hsnd, hone, hgr⟩ := GlobalTheory.ConjRowAut.iota_data θ hθ
    (fun τ Y hY s => GlobalTheory.SmVec.exp_mem_UH (GlobalTheory.SmVec.gram_unit (M.fr_unit τ) (M.fr_gram τ)) hY s) X.B.I h
  change ∀ k ∈ _, iotaX X h k ∈ _ at hrat
  change ∀ k ∈ _, (iotaX X h k).1 = 1 at hfst
  change ∀ k ∈ _, (iotaX X h k).2 = 1 at hsnd
  choose f hf using hrep
  have hval : ∀ u y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = star (f u (iotaX X h (y * t⁻¹))) := fun u y => by
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X (hf u)]
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hlev : ∀ u, ∀ k ∈ X.B.I.Kg X.B.g, ∀ y, f u (y * (1, k)) = f u y := by
    intro u k hk y
    obtain ⟨A, -, hA⟩ := hΦ
    have hA' : Φ = X.B.Re.comp A := hA.symm
    have h1 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X (hf u) (1, k)
    have h2 : X.B.R (1, k) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) =
        Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)) := by
      rw [hA']
      exact congrArg (fun L : L2X X →L[ℂ] L2X X => L (A (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))))
        (GlobalTheory.Dec.CuspFrame.re_fixed X.B k hk)
    rw [h2] at h1
    exact congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 (hf u)) y
  have hcomm : ∀ a b : X.B.I.GA, a.1 = 1 → b.2 = 1 → a * b = b * a := fun a b ha hb =>
    Prod.ext (by simp [ha]) (by simp [hb])
  have hcont : ∀ u, Continuous (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := fun u => by
    have : GlobalTheory.ConjRowMult.conjMap X M c Φ h t u = fun y => star (f u (iotaX X h (y * t⁻¹))) := funext (hval u)
    rw [this]
    exact ((hf u).1.comp ((iotaX X h).continuous.comp (continuous_mul_const _))).star
  have haut : ∀ u, IsAutFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
    intro u
    refine ⟨fun γ hγ y => ?_, ?_, hcont u⟩
    · rw [hval, hval, mul_assoc, map_mul, (hf u).2.1 _ (hrat γ hγ)]
    · obtain ⟨hKo, ⟨K, hK⟩, -⟩ := (GlobalTheory.CongTop.adelic_topology X.B.I).2.2.2.2.2.2 X.B.g hg
      refine ⟨K.comap ((MonoidHom.snd _ _).comp ((iotaX X h).toMulEquiv.toMonoidHom.comp
        (MulAut.conj t).toMonoidHom)), ?_, fun k hk hkf y => ?_⟩
      · rw [← hK] at hKo
        exact hKo.preimage (f := fun k => (iotaX X h (t * k * t⁻¹)).2)
          (continuous_snd.comp ((iotaX X h).continuous.comp
            ((continuous_mul_const _).comp (continuous_const_mul _))))
      · have hk' : (iotaX X h (t * k * t⁻¹)).2 ∈ X.B.I.Kg X.B.g := by rw [← hK]; exact hk
        have h1 : (iotaX X h (t * k * t⁻¹)).1 = 1 :=
          hfst _ ((GfC _).mul_mem ((GfC _).mul_mem ht hkf) ((GfC _).inv_mem ht))
        have e : y * k * t⁻¹ = y * t⁻¹ * (t * k * t⁻¹) := by group
        have e2 : iotaX X h (t * k * t⁻¹) = (1, (iotaX X h (t * k * t⁻¹)).2) := Prod.ext h1 rfl
        rw [hval, hval, e, map_mul, e2, hlev u _ hk']
  intro u
  refine ⟨haut u, GlobalTheory.RepSmooth.smooth hθ he hs hcont u, GlobalTheory.RepSmooth.zfin he hs u, ?_⟩
  have key : ∃ N : ℕ, ∀ v x, ∃ C : ℝ, ∀ a ∈ GinfC (D.sp.Y 0),
      ‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v (x * a)‖ ≤ C * normInf θ (D.sp.Y 0) a ^ N := by
    rcases Nat.eq_zero_or_pos (D.sp.Y 0).rank with hn | hn
    · refine ⟨0, fun v x => ⟨‖GlobalTheory.ConjRowMult.conjMap X M c Φ h t v x‖, fun a _ => ?_⟩⟩
      have : a = 1 := Subtype.ext (Units.ext (Matrix.ext fun i => (Fin.cast hn i).elim0))
      rw [this, mul_one, pow_zero, mul_one]
    have hn' : 1 ≤ X.B.I.n := by rw [← rank_eq X h]; exact hn
    have hti : (iotaX X h t⁻¹).1 = 1 := hfst _ ((GfC _).inv_mem ht)
    obtain ⟨m, hm⟩ := GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize X.B hn' hg
    refine ⟨m, fun v x => ?_⟩
    obtain ⟨C, hC⟩ := hm (Set.range f) (by
      rintro _ ⟨u, rfl⟩
      refine ⟨⟨_, hf u⟩, hlev u, fun w E => ?_⟩
      obtain ⟨τ, Y, hY, hι⟩ := hone w E.1 E.2
      refine ⟨_, ⟨Function.update u τ (GlobalTheory.RepSmooth.der u τ hY), rfl⟩, fun y => ?_⟩
      have h1 := (GlobalTheory.RepSmooth.hasDerivAt_apply he hs τ u hY ((iotaX X h).symm y * t)).star
      simp only [hval, star_star, mul_inv_cancel_right, ContinuousMulEquiv.apply_symm_apply] at h1
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      have e1 : iotaX X h (oneP θ (D.sp.Y 0) τ Y s) =
          GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B w E) s :=
        GlobalTheory.RepSmooth.eq_onePar X.B w E s (hι s).1 (hι s).2.1 (hι s).2.2
      have e2 : iotaX X h ((iotaX X h).symm y * t * oneP θ (D.sp.Y 0) τ Y s * t⁻¹) =
          y * iotaX X h (oneP θ (D.sp.Y 0) τ Y s) := by
        have h3 : (iotaX X h (oneP θ (D.sp.Y 0) τ Y s)).2 = 1 := (hι s).1
        rw [map_mul, map_mul, mul_assoc, ← hcomm _ _ hti h3, ← mul_assoc, ← map_mul, mul_inv_cancel_right,
          ContinuousMulEquiv.apply_symm_apply]
      show f u _ = f u _
      rw [e2, e1]) _ ⟨v, rfl⟩
    choose b hb0 hb using hgr hn'
    have hp := (GlobalTheory.TauLipschitz.tauLip X.B.I hn').1
    have hB : 0 ≤ ∑ w, b w := Finset.sum_nonneg fun w _ => hb0 w
    refine ⟨|C| * ((GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹)))⁻¹ * ∑ w, b w) ^ m, fun a ha => ?_⟩
    have hN : 0 ≤ normInf θ (D.sp.Y 0) a := by unfold normInf; positivity
    have e : iotaX X h (x * a * t⁻¹) = iotaX X h (x * t⁻¹) * iotaX X h a := by
      rw [map_mul, map_mul, map_mul, mul_assoc, ← hcomm _ _ hti (hsnd a ha), mul_assoc]
    have h2 := GlobalTheory.TauNorm.inv_tau_mul_le X.B.I hn' (iotaX X h (x * t⁻¹)) (iotaX X h a) (hsnd a ha)
      ((∑ w, b w) * normInf θ (D.sp.Y 0) a) fun w => (hb w a).trans
        (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun w _ => hb0 w) (Finset.mem_univ w)) hN)
    rw [hval, norm_star, e]
    refine (hC _).trans ?_
    have h0 := inv_nonneg.2 (hp (iotaX X h (x * t⁻¹) * iotaX X h a)).le
    rw [mul_assoc, ← mul_pow, mul_assoc]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ h0 h2 m) (pow_nonneg h0 m) (abs_nonneg _)
  obtain ⟨N, hN⟩ := key
  refine ⟨N, fun l hl x => ?_⟩
  obtain ⟨v, hv⟩ := GlobalTheory.RepSmooth.foldr_rder he hs u l hl
  rw [hv]
  exact hN v x

end GlobalTheory.ConjEvalAut
end Gen

theorem GlobalTheory.ConjEvalAut.conjMap_isAutFunSm_see : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hid _ _ hinf _ hsee c hc Φ hΦ hrep u
  exact GlobalTheory.ConjEvalAut.conjMap_isAutFunSm_gen X h R.θ (MP R) t c hinf hid hsee.fin hc Φ hΦ hrep u

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationMapSmoothAutomorphicValuesStatement
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateEvaluationMap_smooth_automorphic_values : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  exact @GlobalTheory.ConjEvalAut.conjMap_isAutFunSm_see
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationIntertwinerCuspidalValues
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationIntertwinerCuspidalValues
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.ConjRowCuspGap

theorem gap_of_sign {D : D7} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (τ : D.what₂.Tau) (a b : Fin D.R.r)
    (hab : a < b) (hne : epsS D.R a ≠ epsS D.R b) :
    100 * (D.R.r : ℝ) ^ 4 ≤ lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b := by
  obtain ⟨hr, hgp⟩ := hG
  have hkb := GlobalTheory.Core.Rk.HdNc.node_of_sign D.R a b hab hne
  have hbr : b.1 < D.R.r := b.2
  have hm2 := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr' : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hstep : ∀ (i : Fin D.R.r) (hi : i.1 + 1 < D.R.r),
      lamS D.R (D.hc τ) ⟨i.1 + 1, hi⟩ < lamS D.R (D.hc τ) i := fun i hi =>
    (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc τ)).1 (show i < ⟨i.1 + 1, hi⟩ by rw [Fin.lt_def]; simp)
  set j := b.1 - D.R.k with hj
  have hj1 : j + 1 < D.R.m := by omega
  have e1 : b = ⟨D.R.k - 1 + (j + 1), by omega⟩ := by ext; simp only []; omega
  have hac : a ≤ (⟨D.R.k - 1 + j, by omega⟩ : Fin D.R.r) := by
    rw [Fin.le_def]; simp only []; have : a.1 < b.1 := hab; omega
  have h1 := GlobalTheory.Core.Rk.HdNc.anti_of_step _ hstep _ _ hac
  have hg := hgp τ ⟨j, by omega⟩ hj1
  have hgR : (16 : ℝ) * (D.R.r : ℝ) ^ 19 ≤
      (((D.hc τ).b ⟨j + 1, hj1⟩ : ℚ) : ℝ) - (((D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
    exact_mod_cast hg
  rw [GlobalTheory.Core.Rk.HdNc.lamS_node D.R (D.hc τ) j (by omega) (by omega)] at h1
  rw [e1, GlobalTheory.Core.Rk.HdNc.lamS_node D.R (D.hc τ) (j + 1) hj1 (by omega)]
  have hr7 : (7 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 7 ≤ D.R.r)
  have h5 : (D.R.r : ℝ) ^ 5 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h4 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 4 := by positivity
  have h6 : 7 * (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 5 := by
    rw [pow_succ]; nlinarith
  linarith

theorem gapGe_of_gapHyp {D : D7} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (X : HidaSetting D) :
    GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  have key : ∀ (τ : D.what₂.Tau) (a b : Fin D.R.r), epsS D.R a ≠ epsS D.R b →
      100 * (D.R.r : ℝ) ^ 4 ≤ |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) b| := by
    intro τ a b hne
    have hp : (0 : ℝ) ≤ 100 * (D.R.r : ℝ) ^ 4 := by positivity
    rcases lt_trichotomy a b with h | h | h
    · have := gap_of_sign hG τ a b h hne
      rw [abs_of_nonneg (by linarith)]
      linarith
    · exact absurd (by rw [h]) hne
    · have := gap_of_sign hG τ b a h (Ne.symm hne)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  intro v a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq]
  exact key _ _ _ hab

theorem conjMap_isCuspFun : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsCuspFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t _ hG _ _ _ _ c _ Φ hΦ hcont u
  obtain ⟨ψ, hψ⟩ := hcont u
  have hgap := gapGe_of_gapHyp hG X
  obtain ⟨hd, hl, hH, hb, -⟩ := GlobalTheory.Core.Mi.seeData_of_gap D X hgap
  have hK : ∀ v, Formalism.MainNotions.S.IsKTypeOf (X.B.I.ε v) (X.B.σ v) (Formalism.QuantumDeterminants.lowK (X.B.I.ε v) (X.B.lam v))
      (Formalism.MainNotions.S.lowKSub (X.B.I.ε v) (X.B.lam v) (X.B.σ v)) := fun v =>
    GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub _ _ _ _ _ (hd v).1 (hd v).2.1 fun a b hab =>
      (GlobalTheory.Dec.ProjCuspGap.two_mul_lt _ _ (hb v) (GlobalTheory.Dec.ProjCuspGap.rank_pos_of_ne _ hab)).trans_le (hgap v a b hab)
  have hL2 := ((GlobalTheory.Dec.CuspAllKType.cusp_all X.B X.dv _ hd hK (GlobalTheory.PinScale.one_le_g X) hb hl hH Φ hΦ).2
    (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))).1
  have hψc := GlobalTheory.ConjRowMultCusp.isCuspFn_of_contRep X hψ hL2
  have hY := GlobalTheory.ConjRowMultCusp.isCuspFun_of_isCuspFn_iota D X.B.I h X.B.μf ψ hψ.1 hψ.2.1 hψc
  have e : GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u = fun y => star (ψ (iotaX X h (y * t⁻¹))) := by
    funext y
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  rw [e]
  intro r C hC μ 𝓕 hμ h𝓕 g
  have hz : ∫ n in 𝓕, ψ (iotaX X h ((n : GA D (D.sp.Y 0)) * (g * t⁻¹))) ∂μ = 0 := hY r C hC μ 𝓕 hμ h𝓕 (g * t⁻¹)
  show ∫ n in 𝓕, star (ψ (iotaX X h ((n : GA D (D.sp.Y 0)) * g * t⁻¹))) ∂μ = 0
  simp only [mul_assoc]
  have := congrArg (starRingEnd ℂ) hz
  rw [← integral_conj, map_zero] at this
  exact this

end GlobalTheory.ConjRowCuspGap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationIntertwinerCuspidalValuesStatement
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_evaluation_intertwiner_cuspidal_values : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsCuspFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  exact @GlobalTheory.ConjRowCuspGap.conjMap_isCuspFun
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRepIntertwinerImageModels
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRepIntertwinerImageModels
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct ContDiff

noncomputable section

namespace GlobalTheory.ConjRowRepModels


set_option maxHeartbeats 1000000 in
theorem exists_contRep_models : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hE _ _ hθ _ _ c hc Φ hΦ u
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h R.θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨m, hm, -⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  let C : (∀ τ, (MP R).H τ) → ∀ v, X.B.H v := fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))
  have hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ) := fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hCd : ContDiff ℝ ∞ C := by
    refine contDiff_pi.2 fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [hC]
    exact (GlobalTheory.ConjRowRep.contDiff_anti (c τ)).comp (contDiff_pi.1 contDiff_id τ)
  let F : (∀ τ, (MP R).H τ) → L2X X := fun y => Φ (X.B.tens (C y))
  have hF : ContDiff ℝ ∞ F := by
    have e : F = fun y => (Φ.compContinuousMultilinearMap m) (C y) := by
      funext y
      show Φ (X.B.tens (C y)) = Φ (m (C y))
      rw [hm]
    rw [e]
    exact (((Φ.compContinuousMultilinearMap m).contDiff (n := ∞)).restrict_scalars ℝ).comp hCd
  have hsm := GlobalTheory.ConjRowRep.smooth_of_contDiff R.θ (MP R) ρ F hF (fun τ a ha y => by
    obtain ⟨q1, q2, -⟩ := hat τ a ha
    rw [h3]
    refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
    obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
    rw [hC, hC]
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact hc _ a ha _
    · rw [Function.update_of_ne e]
      have q : (iotaX X h (atTau R.θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
      rw [q]
      have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
      show _ = X.B.σ (X.pl.symm τ') 1 _
      rw [this]
      rfl) u
  obtain ⟨R', L, -, hR, -⟩ := GlobalTheory.TensRep.exists_adelic_rep (ι := fun v x => X.B.I.ext v (T x)) hθ h1 h2 h5 h6 h7
    h8 h9 hU
  obtain ⟨p1, p2⟩ := hR _ hsm (fun k hk hk' => by
    rw [h3]
    have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
    rw [e]
    exact hlev _ (hUg k hk) _)
  refine ⟨fun x => R' (F fun τ => (u τ : (MP R).H τ)) (T.symm x),
    GlobalTheory.RepSmooth.isContRep_of_ae X.B (p1.comp hT') (fun γ hγ x => ?_) ?_⟩
  · have e : (fun x => R' (F fun τ => (u τ : (MP R).H τ)) (T.symm γ * x)) = R' (F fun τ => (u τ : (MP R).H τ)) :=
      ((p1.comp (continuous_const_mul _)).ae_eq_iff_eq μ p1).1
        (Filter.EventuallyEq.trans
          (((measurePreserving_mul_left μ _).quasiMeasurePreserving.ae p2).mono fun _ hy => hy.symm)
          ((h10 (T.symm γ) (by rw [T.apply_symm_apply]; exact hγ) _).trans p2))
    rw [map_mul]
    exact congrFun e _
  · filter_upwards [h4 _ p2] with x hx
    rw [← hx, T.apply_symm_apply]
    rfl

end GlobalTheory.ConjRowRepModels

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRepIntertwinerImageModelsStatement
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousRep_intertwinerImage_models : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ :=
  @GlobalTheory.ConjRowRepModels.exists_contRep_models
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEvaluationHasRowLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEvaluationHasRowLevel
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
noncomputable section

namespace GlobalTheory.ConjRowLevelSee

theorem conjMap_level_of_seeAt : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ JR R F, ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = chiR R F k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t _ _ _ _ _ hsee c _ Φ hΦ hrep u (k : GA D (D.sp.Y 0)) hk (g : GA D (D.sp.Y 0))
  obtain ⟨ψ, hψ⟩ := hrep u
  show star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)))
      (iotaX X h ((g * k * t⁻¹ : GA D (D.sp.Y 0))))) = _ *
    star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)))
      (iotaX X h ((g * t⁻¹ : GA D (D.sp.Y 0)))))
  rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  obtain ⟨hJ, hχ⟩ := hsee.conj k
  have hmem := hJ.1 hk
  have hval := hχ hk
  set x := iotaX X h ((t⁻¹)⁻¹ * k * t⁻¹ : GA D (D.sp.Y 0)) with hxdef
  have hx : x.1 = 1 ∧ x.2 ∈ X.K2 := hmem
  have hxeq : x = (1, x.2) := Prod.ext hx.1 rfl
  have hΦk : X.B.R (1, x.2) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) =
      X.chi2 x.2 • Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)) := by
    obtain ⟨T', -, hT'⟩ := hΦ
    rw [← hT']
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (T' _)) (GlobalTheory.ConjRowLevel.reg_comp_Re X x.2 hx.2)
  have hrep2 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (1, x.2)
  rw [hΦk] at hrep2
  have key := Formalism.L2.SG.EvalTOntoRep.contRep_unique X hrep2 (Formalism.L2.SG.EvalTOntoRep.contRep_smul X _ hψ)
  have e1 : (g * k * t⁻¹ : GA D (D.sp.Y 0)) = g * t⁻¹ * ((t⁻¹)⁻¹ * k * t⁻¹) := by group
  have hkey : ∀ z, ψ (z * x) = X.chi2 x.2 * ψ z := by
    intro z
    conv_lhs => rw [hxeq]
    exact congrFun key z
  have hm : iotaX X h ((g * k * t⁻¹ : GA D (D.sp.Y 0))) = iotaX X h ((g * t⁻¹ : GA D (D.sp.Y 0))) * x := by
    rw [e1, hxdef]
    exact map_mul (iotaX X h) _ _
  rw [hm, hkey, star_mul']
  exact congrArg (· * _) hval

end GlobalTheory.ConjRowLevelSee
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEvaluationHasRowLevelStatement
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedIntertwinerEvaluation_has_row_level : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ JR R F, ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = chiR R F k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  first | exact @GlobalTheory.ConjRowLevelSee.conjMap_level_of_seeAt | exact GlobalTheory.ConjRowLevelSee.conjMap_level_of_seeAt | (intros; apply GlobalTheory.ConjRowLevelSee.conjMap_level_of_seeAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLevelTranslatedEvaluationOfConjRow
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem exists_multR_eval_of_star_mem : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ φ : L2X X, star φ ∈ HHX X → ∃ S ∈ MultR R F, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) := by
  intro hIC hCD hDU hFD D G' _ _ Pl0 T A Ks _ _ _ R F X h t hιE hgap hlev hinf hν0 hsee c v₀ hc hv₀ φ hφ
  obtain ⟨Φ, hΦ, hΦw⟩ := Formalism.L2.SG.EvalTOnto.rows_eq_hom X (fun v => Formalism.L2.SG.EvalTPh.phLoc_int_of_gap X hgap v) (star φ) hφ
  have hrep := GlobalTheory.T.exists_continuousRep_intertwinerImage_models hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ
  have hmm : IsMultMap R.θ (MP R) (JR R F) (chiR R F) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t) :=
    { aut := GlobalTheory.T.conjugateEvaluationMap_smooth_automorphic_values hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep
      cusp := GlobalTheory.T.conjugate_evaluation_intertwiner_cuspidal_values hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep
      lev := GlobalTheory.T.conjugatedIntertwinerEvaluation_has_row_level hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep
      equiv := fun τ g hg v w hw => GlobalTheory.T.conjugated_intertwiner_equivariant_real_place hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep τ g hg v w hw
      cont := fun τ v x => GlobalTheory.T.conjIntertwinerMap_sobolevContinuous_separately hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep τ v x }
  have hmem : GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t ∈ MultR R F := (Submodule.span_le (p := MultR R F)).1 le_rfl hmm
  refine ⟨GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t, hmem, ?_⟩
  · have hw : GlobalTheory.ConjRowMult.vecC X (MP R) c v₀ = X.B.w := GlobalTheory.ConjRowMult.vecC_eq X (MP R) c v₀ X.B.w hv₀
    obtain ⟨ψ, hψ⟩ := hrep v₀
    rw [hw, hΦw] at hψ
    have key : ∀ x, ev (MP R) v₀ (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t) ((iotaX X h).symm x * t) = star (ψ x) := by
      intro x
      rw [ev_apply]
      refine (GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t v₀ _).trans ?_
      rw [hw, hΦw, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
      simp only [mul_inv_cancel_right, ContinuousMulEquiv.apply_symm_apply]
    filter_upwards [hψ.2.2, Lp.coeFn_star φ] with x h1 h2
    rw [key x, ← h1, h2, Pi.star_apply, star_star]

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLevelTranslatedEvaluationOfConjRowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowLevel_translatedEvaluation_of_conj_row : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ φ : L2X X, star φ ∈ HHX X → ∃ S ∈ MultR R F, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) :=
  @GlobalTheory.Mem.SRe.exists_multR_eval_of_star_mem
end
