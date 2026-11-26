module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEvaluationTranslateMemRowSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIntertwinerValuesSobolevContinuous
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesSmoothAutomorphic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjIntertwinerMapValuesIsCuspFunStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerEquivariantRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerEquivariantRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.ConjEquivReal


set_option maxHeartbeats 1000000 in
theorem conjMap_update_real : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Yc D 0) τ), ∀ (v : (MP R).Vec) (w : (MP R).sm τ), (w : (MP R).H τ) = (MP R).rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) = rTr (Yc D 0) (atTau R.θ (Yc D 0) τ g) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hlev hgrp hmod hhost hιE t c ht hconj hc Φ hΦ hrep τ g hg v w hw
  classical
  obtain ⟨hfin, hreal, -⟩ := GlobalTheory.IotaReal.iotaX_real_finite R F X h hlev hgrp hmod hιE
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  obtain ⟨-, Rm, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  have hint : ∀ (x : X.B.I.Ginf) (z : X.B.Hs), Φ (X.B.σs x z) = X.B.R (x, 1) (Φ z) := by
    obtain ⟨B, hB, rfl⟩ := hΦ
    intro x z
    have hb : B (X.B.σs x z) = X.B.R (x, 1) (B z) := DFunLike.congr_fun (hB x) z
    show X.B.Re (B (X.B.σs x z)) = X.B.R (x, 1) (X.B.Re (B z))
    rw [hb]
    obtain ⟨-, hT⟩ := X.B.Re_spec
    apply ext_inner_left ℂ
    intro u
    rw [← ContinuousLinearMap.adjoint_inner_left (X.B.R (x, 1)), hT, hT]
    congr 1
    funext k
    rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← Rm, ← ContinuousLinearMap.comp_apply (X.B.R (x, 1)), ← Rm]
    simp
  have hσ1 : ∀ v', X.B.σ v' 1 = 1 := fun v' => (X.ds v').2.2.1.1.1
  have hvec : GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w) = fun v' =>
      X.B.σ v' (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v')) (GlobalTheory.ConjRowMult.vecC X (MP R) c v v') := by
    rw [GlobalTheory.ConjRowMult.vecC_update]
    funext v'
    by_cases hv : v' = X.pl.symm τ
    · subst hv
      rw [Function.update_self, hw, hc τ g hg]
      unfold GlobalTheory.ConjRowMult.vecC
      rw [Equiv.piCongrLeft_apply_apply]
    · rw [Function.update_of_ne hv, ha1 v' hv,
        show uMat (1 : Formalism.REAL.UJ (X.B.I.ε v')) = 1 from rfl, hσ1]
      rfl
  have hsig : X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w)) =
      X.B.σs ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1) (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have ea : iotaX X h (atTau R.θ (D.sp.Y 0) τ g) = ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1, 1) :=
    Prod.ext rfl ha2
  have hcomm : iotaX X h t⁻¹ * iotaX X h (atTau R.θ (D.sp.Y 0) τ g) =
      iotaX X h (atTau R.θ (D.sp.Y 0) τ g) * iotaX X h t⁻¹ := by
    have h1 : (iotaX X h t).1 = 1 := (hfin t).1 ht
    erw [map_inv]
    refine Prod.ext ?_ ?_
    · simp [h1]
    · simp [ha2]
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (iotaX X h (atTau R.θ (D.sp.Y 0) τ g))
  funext y
  show _ = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v (y * atTau R.θ (D.sp.Y 0) τ g)
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [hsig, hint, ← ea,
    GlobalTheory.ConjRowMult.contRepL_spec X hψ', GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  simp only [map_mul]
  rw [mul_assoc, hcomm, mul_assoc]

end GlobalTheory.ConjEquivReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerEquivariantRealPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedIntertwiner_equivariant_realPlace : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Yc D 0) τ), ∀ (v : (MP R).Vec) (w : (MP R).sm τ), (w : (MP R).H τ) = (MP R).rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) = rTr (Yc D 0) (atTau R.θ (Yc D 0) τ g) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v) := by
  first | exact @GlobalTheory.ConjEquivReal.conjMap_update_real | exact GlobalTheory.ConjEquivReal.conjMap_update_real | (intros; apply GlobalTheory.ConjEquivReal.conjMap_update_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEqTranslatedEvaluationCuspFormMap
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerValuesSmoothAutomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerContinuousRepresentativePowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerContinuousRepresentativePowerBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRepBound


set_option maxHeartbeats 1000000 in
theorem contRep_bound : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → 1 ≤ (D.sp.Y 0).rank → ∃ m : ℕ, ∀ u : (MP R).Vec, ∃ C : ℝ, ∀ y : X.B.I.GA, ‖GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) y‖ ≤ C * (GlobalTheory.Count.tau1 X.B.I y)⁻¹ ^ m := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep hrank
  classical
  have hn : 1 ≤ X.B.I.n := by
    rw [← GlobalTheory.Core.Mi.rank_eq X h]
    exact hrank
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hexp : ∀ τ, ∀ Y ∈ lieAt (D.sp.Y 0) τ, ∀ s : ℝ,
      NormedSpace.exp (s • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ) := fun τ Y hY s =>
    GlobalTheory.SmoothAutCheck.exp_mem_UH (Formalism.IndefR.Eqv.gramAt_isUnit D (D.sp.Y 0) τ) hY s
  obtain ⟨-, hfin, -, hpl, -⟩ := GlobalTheory.ConjRowAut.iota_data R.θ h3.inf hexp X.B.I h
  have hιt : (iotaX X h t).1 = 1 := hfin t ht
  have hcomm : ∀ z : X.B.I.GA, z.2 = 1 → iotaX X h t * z = z * iotaX X h t := by
    intro z hz
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_mul, hιt]
    · simp [Prod.snd_mul, hz]
  have hsymm : ∀ z, iotaX X h ((iotaX X h).toMulEquiv.symm z) = z := fun z =>
    (iotaX X h).toMulEquiv.apply_symm_apply z
  obtain ⟨f, hfdef⟩ : ∃ f : (MP R).Vec → X.B.I.GA → ℂ, ∀ u,
      f u = GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) :=
    ⟨_, fun _ => rfl⟩
  have hf : ∀ u, Formalism.L2.SG.EvalTOntoRep.IsContRep X
      (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) (f u) := by
    intro u
    obtain ⟨ψ, hψ⟩ := hrep u
    rw [hfdef, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    exact hψ
  have hK : ∀ u, ∀ k ∈ X.B.I.Kg X.B.g, ∀ y, f u (y * (1, k)) = f u y := by
    intro u k hk y
    obtain ⟨S, -, hS⟩ := Submodule.mem_map.mp hΦ
    have hΦz : ∀ z, Φ z = X.B.Re (S z) := fun z => by rw [← hS]; rfl
    have hR : X.B.R (1, k) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) =
        Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)) := by
      rw [hΦz]
      exact ContinuousLinearMap.ext_iff.mp (GlobalTheory.Dec.CuspFrame.re_fixed X.B k hk) _
    have hr := Formalism.L2.SG.EvalTOntoRep.contRep_reg X (hf u) ((1, k) : X.B.I.GA)
    rw [hR] at hr
    exact congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X hr (hf u)) y
  have he := GlobalTheory.T.conjugatedIntertwiner_equivariant_realPlace hDS R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep
  have hs := GlobalTheory.T.conjugateIntertwinerValues_sobolevContinuous hDS R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep
  obtain ⟨m, hm⟩ := GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize X.B hn hg
  have hW : ∀ g ∈ Set.range f, (∃ G, GlobalTheory.Dec.IsContRep X.B G g) ∧
      (∀ k ∈ X.B.I.Kg X.B.g, ∀ y, g (y * (1, k)) = g y) ∧
      ∀ (v : NumberField.InfinitePlace X.B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (X.B.I.ε v)), ∃ g' ∈ Set.range f,
        ∀ y, HasDerivAt (fun s : ℝ => g (y * GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s))
          (g' y) 0 := by
    rintro _ ⟨u, rfl⟩
    refine ⟨⟨_, hf u⟩, hK u, fun v E => ?_⟩
    obtain ⟨τ, Y, hY, hYt⟩ := hpl v E.1 E.2
    have h2s : ∀ s : ℝ, (iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)).2 = 1 := fun s => (hYt s).1
    have hone : ∀ s : ℝ, iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s) =
        GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s := fun s =>
      GlobalTheory.RepSmooth.eq_onePar X.B v E s (hYt s).1 (hYt s).2.1 (hYt s).2.2
    refine ⟨f (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY)), ⟨_, rfl⟩, fun y => ?_⟩
    have key := (GlobalTheory.RepSmooth.hasDerivAt_switch he hs τ u hY (iotaX X h).toMulEquiv
      (fun s => iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)) (fun _ => rfl) (y * iotaX X h t)).star
    have hfun : (fun s : ℝ => f u (y * GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s)) =
        fun s => star (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u ((iotaX X h).toMulEquiv.symm
          (y * iotaX X h t * iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)))) := by
      funext s
      erw [GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t]
      rw [star_star, ← hone s, hfdef]
      congr 1
      erw [map_mul, map_inv, hsymm]
      rw [mul_assoc y, hcomm _ (h2s s), ← mul_assoc, mul_inv_cancel_right]
    have hval : f (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY)) y =
        star (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY))
          ((iotaX X h).toMulEquiv.symm (y * iotaX X h t))) := by
      erw [GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t]
      rw [star_star]
      erw [map_mul, map_inv, hsymm]
      rw [mul_inv_cancel_right, hfdef]
    rw [hfun, hval]
    exact key
  refine ⟨m, fun u => ?_⟩
  have hb := hm (Set.range f) hW (f u) ⟨u, rfl⟩
  rw [hfdef] at hb
  exact hb

end GlobalTheory.ConjRepBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerContinuousRepresentativePowerBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_continuous_representative_power_bound : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → 1 ≤ (D.sp.Y 0).rank → ∃ m : ℕ, ∀ u : (MP R).Vec, ∃ C : ℝ, ∀ y : X.B.I.GA, ‖GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) y‖ ≤ C * (GlobalTheory.Count.tau1 X.B.I y)⁻¹ ^ m := by
  first | exact @GlobalTheory.ConjRepBound.contRep_bound | exact GlobalTheory.ConjRepBound.contRep_bound | (intros; apply GlobalTheory.ConjRepBound.contRep_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointIdentificationLeastSizeLinearGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointIdentificationLeastSizeLinearGrowth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IotaNorm

theorem iota_norm_of_eq {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) :
    (∀ g ∈ GinfC (D.sp.Y 0), ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm) g).2 = 1) ∧
    (1 ≤ (D.sp.Y 0).rank → ∀ x : I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0),
      (GlobalTheory.Count.tau1 I (x * (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm) g))⁻¹ ≤
        C * normInf θ (D.sp.Y 0) g) := by
  subst h
  set ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm) with hιdef
  have key : ∀ k, (∀ v, Formalism.MainNotions.S.uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧ (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, Formalism.MainNotions.S.uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J (θ ((Formalism.L2.Host.tauPl D).symm v)) k *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M * (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (GlobalTheory.IotaReal.map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hfin : ∀ g ∈ GinfC (D.sp.Y 0), (ι g).2 = 1 := by
    intro g hg
    apply Subtype.ext
    apply Units.ext
    refine (key g).2.trans (GlobalTheory.IotaReal.ofHAFin_eq_one _ _ ?_)
    have e3 : (finHom (D.sp.Y 0) g).val = 1 := by
      rw [show finHom (D.sp.Y 0) g = 1 from hg]; rfl
    ext i j
    exact congrFun (congrFun e3 i) j
  refine ⟨hfin, fun hn x => ?_⟩
  choose c hc0 hc using fun v => GlobalTheory.TauNorm.exp_dOp_le ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ ((Formalism.L2.SG.InstExistsPf.instOf D).P v)
  have hC : 0 ≤ ∑ v, c v := Finset.sum_nonneg fun v _ => hc0 v
  have hn' : 1 ≤ (Formalism.L2.SG.InstExistsPf.instOf D).n := hn
  have hp : 0 ≤ (GlobalTheory.Count.tau1 (Formalism.L2.SG.InstExistsPf.instOf D) x)⁻¹ :=
    inv_nonneg.2 ((GlobalTheory.TauLipschitz.tauLip (Formalism.L2.SG.InstExistsPf.instOf D) hn').1 _).le
  refine ⟨(GlobalTheory.Count.tau1 (Formalism.L2.SG.InstExistsPf.instOf D) x)⁻¹ * ∑ v, c v, mul_nonneg hp hC, fun g hg => ?_⟩
  have hv : ∀ v, Real.exp (GlobalTheory.Count.dOp (Formalism.MainNotions.S.uMat ((ι g).1 v))) ≤ (∑ v, c v) * normInf θ (D.sp.Y 0) g := by
    intro v
    have h0 := GlobalTheory.TauNorm.uMat_ne_zero (Formalism.L2.SG.InstExistsPf.instOf D) hn' (ι g) v
    rw [hinf g v] at h0 ⊢
    have h2 := hc v _ h0
    have h3 : c v ≤ ∑ v, c v := Finset.single_le_sum (fun v _ => hc0 v) (Finset.mem_univ _)
    exact h2.trans (mul_le_mul h3 (GlobalTheory.TauNorm.sum_le_normInf θ g ((Formalism.L2.Host.tauPl D).symm v))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hC)
  have hh := GlobalTheory.TauNorm.inv_tau_mul_le (Formalism.L2.SG.InstExistsPf.instOf D) hn' x (ι g) (hfin g hg) _ hv
  rw [← mul_assoc] at hh
  exact hh

theorem iotaX_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ g ∈ GinfC (D.sp.Y 0), (iotaX X h g).2 = 1) ∧ (1 ≤ (D.sp.Y 0).rank → ∀ x : X.B.I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0), (GlobalTheory.Count.tau1 X.B.I (x * iotaX X h g))⁻¹ ≤ C * normInf R.θ (D.sp.Y 0) g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hMod _
  exact iota_norm_of_eq R.θ hMod.inf X.B.I h

end GlobalTheory.IotaNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointIdentificationLeastSizeLinearGrowthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPointIdentification_leastSize_linear_growth : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ g ∈ GinfC (D.sp.Y 0), (iotaX X h g).2 = 1) ∧ (1 ≤ (D.sp.Y 0).rank → ∀ x : X.B.I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0), (GlobalTheory.Count.tau1 X.B.I (x * iotaX X h g))⁻¹ ≤ C * normInf R.θ (D.sp.Y 0) g) := by
  first | exact @GlobalTheory.IotaNorm.iotaX_norm | exact GlobalTheory.IotaNorm.iotaX_norm | (intros; apply GlobalTheory.IotaNorm.iotaX_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerValuesSmoothAutomorphic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjAutSmooth

theorem castGA_mem {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) : castGA e x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst e; rfl

theorem iotaX_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {γ : GA D (D.sp.Y 0)} (hγ : γ ∈ GQ (D.sp.Y 0)) : iotaX X h γ ∈ X.B.I.GFset := by
  show castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D γ) ∈ X.B.I.GFset
  rw [castGA_mem]
  exact (Formalism.IndefR.RationalEmbedding.iota_rat D γ).1 hγ


set_option maxHeartbeats 1000000 in
theorem conjMap_isAutFunSm : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep u
  set Ψ := GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t with hΨ
  have hθ : IsInfFam R.θ := hMod.inf
  have he : GlobalTheory.RepSmooth.IsEquiv R.θ Ψ := fun τ g hg v w hw =>
    GlobalTheory.T.conjugatedIntertwiner_equivariant_realPlace hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep τ g hg v w hw
  have hs : GlobalTheory.RepSmooth.IsSob Ψ := fun τ v x =>
    GlobalTheory.T.conjugateIntertwinerValues_sobolevContinuous hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep τ v x
  have hval : ∀ v (y : GA D (Yc D 0)), Ψ v y = star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c v)))
      (iotaX X h (y * t⁻¹))) := fun v y => GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t v y
  have hcont : ∀ v, Continuous (Ψ v) := by
    intro v
    obtain ⟨ψ, hψ⟩ := hrep v
    have e : Ψ v = fun y : GA D (Yc D 0) => star (ψ (iotaX X h (y * t⁻¹))) := by
      funext y; exact (hval v y).trans (by rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ])
    rw [e]
    exact continuous_star.comp (hψ.1.comp ((iotaX X h).continuous.comp (continuous_mul_const t⁻¹)))
  refine ⟨⟨?_, ?_, hcont u⟩, fun k τs Xs hX g => GlobalTheory.RepSmooth.smooth hθ he hs hcont u k τs Xs hX g,
    GlobalTheory.RepSmooth.zfin he hs u, ?_⟩
  · intro γ hγ g
    obtain ⟨ψ, hψ⟩ := hrep u
    rw [hval, hval, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    congr 1
    have e2 : iotaX X h (γ * g * t⁻¹) = iotaX X h γ * iotaX X h (g * t⁻¹) := by
      exact (congrArg (iotaX X h) (mul_assoc γ g t⁻¹)).trans (map_mul (iotaX X h) γ (g * t⁻¹))
    rw [e2]; exact hψ.2.1 _ (iotaX_rat X h hγ) _
  · obtain ⟨U, hU, hUk⟩ := GlobalTheory.GoodFiniteDim.exists_open_subgroup (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))
    refine ⟨U, hU, fun k hk hkf g => ?_⟩
    obtain ⟨h1, h2⟩ := hUk k hk hkf
    rw [GlobalTheory.T.conjugatedIntertwiner_hasColumnLevel hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep u k h1 g, h2, one_mul]
  · have key : ∃ N : ℕ, ∀ v (x : GA D (Yc D 0)), ∃ C : ℝ, ∀ g ∈ GinfC (Yc D 0),
        ‖Ψ v (x * g)‖ ≤ C * normInf R.θ (Yc D 0) g ^ N := by
      rcases Nat.eq_zero_or_pos (D.sp.Y 0).rank with hn | hn
      · refine ⟨0, fun v x => ⟨‖Ψ v x‖, fun a _ => ?_⟩⟩
        have : a = 1 := Subtype.ext (Units.ext (Matrix.ext fun i => (Fin.cast hn i).elim0))
        simp [this]
      obtain ⟨hfin, hnorm⟩ := GlobalTheory.T.realPointIdentification_leastSize_linear_growth R F X h hRI hGrp hMod hιE
      obtain ⟨m, hm⟩ := GlobalTheory.T.intertwiner_continuous_representative_power_bound hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep hn
      refine ⟨m, fun v x => ?_⟩
      obtain ⟨C, hC⟩ := hm v
      obtain ⟨C', hC0, hC'⟩ := hnorm hn (iotaX X h (x * t⁻¹))
      refine ⟨|C| * C' ^ m, fun a ha => ?_⟩
      have hi2 : (iotaX X h t⁻¹).1 = 1 :=
        ((GlobalTheory.IotaReal.iotaX_real_finite R F X h hRI hGrp hMod hιE).1 t⁻¹).1 (inv_mem ht)
      have hi1 : (iotaX X h a).2 = 1 := hfin a ha
      have hc : iotaX X h a * iotaX X h t⁻¹ = iotaX X h t⁻¹ * iotaX X h a :=
        Prod.ext (by simp [Prod.fst_mul, hi2]) (by simp [Prod.snd_mul, hi1])
      have hcomm : iotaX X h (x * a * t⁻¹) = iotaX X h (x * t⁻¹) * iotaX X h a := by
        have e1 : iotaX X h (x * a * t⁻¹) = iotaX X h x * iotaX X h a * iotaX X h t⁻¹ := by
          exact (map_mul (iotaX X h) (x * a) t⁻¹).trans (congrArg (· * iotaX X h t⁻¹) (map_mul (iotaX X h) x a))
        have e2 : iotaX X h (x * t⁻¹) = iotaX X h x * iotaX X h t⁻¹ := by
          exact map_mul (iotaX X h) x t⁻¹
        rw [e1, e2, mul_assoc, hc, ← mul_assoc]
      have hp : 0 ≤ (GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹) * iotaX X h a))⁻¹ :=
        inv_nonneg.2 ((GlobalTheory.TauLipschitz.tauLip X.B.I (by rw [h]; exact hn)).1 _).le
      have h1 := hC (iotaX X h (x * a * t⁻¹))
      rw [hcomm] at h1
      rw [hval, norm_star, hcomm]
      refine h1.trans ?_
      calc C * (GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹) * iotaX X h a))⁻¹ ^ m
          ≤ |C| * (C' * normInf R.θ (Yc D 0) a) ^ m :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ hp (hC' a ha) m) (pow_nonneg hp m) (abs_nonneg _)
        _ = |C| * C' ^ m * normInf R.θ (Yc D 0) a ^ m := by rw [mul_pow, mul_assoc]
    obtain ⟨N, hN⟩ := key
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨v, hv⟩ := GlobalTheory.RepSmooth.foldr_rder he hs u l hl
    obtain ⟨C, hC⟩ := hN v x
    exact ⟨C, fun g hg => (congrArg norm (congrFun hv (x * g))).le.trans (hC g hg)⟩

end GlobalTheory.ConjAutSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerValuesSmoothAutomorphicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedIntertwiner_values_smoothAutomorphic : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  first | exact @GlobalTheory.ConjAutSmooth.conjMap_isAutFunSm | exact GlobalTheory.ConjAutSmooth.conjMap_isAutFunSm | (intros; apply GlobalTheory.ConjAutSmooth.conjMap_isAutFunSm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepIntertwinerImageRows
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepIntertwinerImageRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowRepR

private theorem lamS_eq_lamAt (R : Ranks) (P : HCParam R) (i : Fin R.r) :
    Formalism.MainNotions.S.lamS R P i = ((Formalism.L2.NTheta.lamAt P i.val : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.S.lamS Formalism.L2.NTheta.lamAt
  by_cases h1 : i.val < R.k - 1
  · simp [h1]
  · by_cases h2 : i.val - (R.k - 1) < R.m
    · simp [h1, h2]
    · simp [h1, h2]

private theorem lamAt_gap_of_lt {D : D7} (hH : HostHyp D) (τ : D.what₂.Tau)
    {i j : ℕ} (hij : i < j) (hj : j < D.R.r) :
    100 * (D.R.r : ℚ) ^ 4 ≤
      Formalism.L2.NTheta.lamAt (D.hc τ) i - Formalism.L2.NTheta.lamAt (D.hc τ) j := by
  induction j, hij using Nat.le_induction with
  | base => exact hH.gapR τ i hj
  | succ j _ ih =>
    exact (ih (Nat.lt_of_succ_lt hj)).trans
      (sub_le_sub_left (Formalism.L2.NTheta.lamAt_lt (D.hc τ) j hj).le _)

private theorem gapGe_hundred_mul_r_pow_four {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hH : HostHyp D) :
    GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  intro v
  unfold Formalism.QuantumDeterminants.GapAtLeast
  intro a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq, lamS_eq_lamAt, lamS_eq_lamAt]
  have key : ∀ i j : Fin D.R.r, i.val < j.val →
      100 * (D.R.r : ℝ) ^ 4 ≤ |((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) i.val : ℚ) : ℝ) -
        ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) j.val : ℚ) : ℝ)| := by
    intro i j hij
    have hq := lamAt_gap_of_lt hH (X.pl v) hij j.isLt
    have hr : 100 * (D.R.r : ℝ) ^ 4 ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) i.val : ℚ) : ℝ) -
        ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) j.val : ℚ) : ℝ) := by exact_mod_cast hq
    exact hr.trans (le_abs_self _)
  have hne : (Fin.cast X.n_eq a).val ≠ (Fin.cast X.n_eq b).val := fun hv => hab (congrArg _ (Fin.ext hv))
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact key _ _ hlt
  · rw [abs_sub_comm]
    exact key _ _ hgt

theorem exists_contRep_rows : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM hH hE t c ht hconj hc Φ hΦ u
  exact GlobalTheory.ConjRowRep.exists_contRep hDS D X h R.θ _ (MP R) _ _ t c rfl hM.inf (gapGe_hundred_mul_r_pow_four X hH) hE
    ⟨ht, hconj⟩ hc Φ hΦ u

end GlobalTheory.ConjRowRepR

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepIntertwinerImageRowsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousRep_intertwinerImage_rows : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ := by
  exact @GlobalTheory.ConjRowRepR.exists_contRep_rows
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEqTranslatedEvaluationCuspFormMap
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowMult

theorem conj_row_eq_eval_mult : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ φ : L2X X, star φ ∈ HHX X → ∃ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hH hιE t c v₀ ht hCL hc hv₀ φ hφ
  have hL := (GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hH).2.2.2.2.2
  obtain ⟨Φ, hΦ, hΦw⟩ := Formalism.L2.SG.EvalTOnto.rows_eq_hom X hL (star φ) hφ
  have hrep := GlobalTheory.T.exists_continuousRep_intertwinerImage_rows hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ
  refine ⟨GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t, Submodule.subset_span
    ⟨GlobalTheory.T.conjugatedIntertwiner_values_smoothAutomorphic hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep,
     GlobalTheory.T.conjIntertwinerMap_values_isCuspFun hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep,
     GlobalTheory.T.conjugatedIntertwiner_hasColumnLevel hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep, ?_, ?_⟩, ?_⟩
  · intro τ g hg v w hw
    exact GlobalTheory.T.conjugatedIntertwiner_equivariant_realPlace hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep τ g hg v w hw
  · intro τ v x
    exact GlobalTheory.T.conjugateIntertwinerValues_sobolevContinuous hDS R F X h hLev hGrp hMod hH hιE t c ht hCL hc Φ hΦ hrep τ v x
  · have hw : GlobalTheory.ConjRowMult.vecC X (MP R) c v₀ = X.B.w := GlobalTheory.ConjRowMult.vecC_eq X (MP R) c v₀ X.B.w hv₀
    obtain ⟨ψ, hψ⟩ := hrep v₀
    rw [hw, hΦw] at hψ
    have key : ∀ x, ev (MP R) v₀ (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t) (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) = star (ψ x) := by
      intro x
      rw [ev_apply]
      apply (GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t v₀ _).trans
      rw [hw, hΦw, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
      have e : ∀ a b : GA D (D.sp.Y 0), a * b * b⁻¹ = a := fun a b => mul_inv_cancel_right a b
      erw [e, ContinuousMulEquiv.apply_symm_apply]
    filter_upwards [hψ.2.2, Lp.coeFn_star φ] with x h1 h2
    rw [key x, ← h1, h2, Pi.star_apply, star_star]

end GlobalTheory.ConjRowMult

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEqTranslatedEvaluationCuspFormMapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjRow_eq_translatedEvaluation_cuspFormMap : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ φ : L2X X, star φ ∈ HHX X → ∃ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  exact GlobalTheory.ConjRowMult.conj_row_eq_eval_mult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodOpStarTranslatedEvalEqGoodProjector
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodOpStarTranslatedEvalEqGoodProjector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GoodProjEval

open GlobalTheory.Mem.SRe Formalism.L2.SG.Pf.unitaryCongruence

theorem multR_left_inv {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (v₀ : (MP R).Vec) (S : MMap (MP R)) (hS : S ∈ MultR R F) :
    ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g := by
  intro γ hγ g
  induction hS using Submodule.span_induction with
  | mem x hx => exact (hx.aut v₀).left γ hγ g
  | zero => rfl
  | add x y _ _ hx hy =>
    show x v₀ (γ * g) + y v₀ (γ * g) = x v₀ g + y v₀ g
    rw [hx, hy]
  | smul c x _ hx =>
    show c • x v₀ (γ * g) = c • x v₀ g
    rw [hx]

theorem goodOp_star_ev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), RowLevelMatchAt R F X h t → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → (star (Gd.Rg (star φ)) : L2X X) =ᵐ[muX X] (fun x => ev (MP R) v₀ (postOn (MP R) R.e0 S) (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ Gd t v₀ hM S hS φ hφ
  obtain ⟨σ, red, -, hB, hC⟩ := hM
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G σ.symm.toEquiv
  obtain ⟨hgood, hmul, hsurj, hker⟩ := hB.1
  choose s hsK hsred using hsurj
  have hinv := multR_left_inv R F v₀ S hS
  have hEv := evalAct_intertwines D G Pl0 T A Ks R F X h t v₀ σ red hB S hS φ hφ hinv

  have hF1 : ∀ k ∈ X.B.I.Kset, X.B.R (1, k) (star φ) = X.B.R (1, s (red k)) (star φ) := by
    intro k hk
    classical
    let a : G0g D.nd → ℂ := fun γ => if γ = red k then 1 else 0
    let s' : G0g D.nd → X.B.I.Gf := Function.update s (red k) k
    have hs' : ∀ γ, s' γ ∈ X.B.I.Kset ∧ red (s' γ) = γ := by
      intro γ
      by_cases hγ : γ = red k
      · subst hγ
        simp only [s', Function.update_self]
        exact ⟨hk, trivial⟩
      · simp only [s', Function.update_of_ne hγ]
        exact ⟨hsK γ, hsred γ⟩
    have e1 := hEv a s' hs'
    have e2 := hEv a s (fun γ => ⟨hsK γ, hsred γ⟩)
    have hsum : ∀ u : G0g D.nd → X.B.I.Gf,
        (∑ γ, star (a γ) • star (X.B.R (1, u γ) (star φ)) : L2X X) = star (X.B.R (1, u (red k)) (star φ)) := by
      intro u
      rw [Finset.sum_eq_single (red k)]
      · simp [a]
      · intro γ _ hγ
        simp [a, hγ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    rw [hsum] at e1 e2
    have e3 : star (X.B.R (1, k) (star φ)) = (star (X.B.R (1, s (red k)) (star φ)) : L2X X) := by
      apply Lp.ext
      have : s' (red k) = k := by simp [s']
      rw [this] at e1
      exact e1.trans e2.symm
    exact star_injective e3

  have hKgK : X.B.I.Kg X.B.g ⊆ X.B.I.Kset := fun x hx => hx.1
  have hKgO : IsOpen (X.B.I.Kg X.B.g) :=
    X.B.I.topf_open X.B.g (Nat.one_le_iff_ne_zero.2 (Formalism.L2.SG.Pf.RowDictPf.level_ne_zero X))
  have h1Kg : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
    rw [← hker 1 (K_one _)]
    have := hmul 1 (K_one _) 1 (K_one _)
    rw [mul_one] at this
    exact left_eq_mul.mp this
  have hvol_pos : 0 < X.B.μf (X.B.I.Kg X.B.g) := hKgO.measure_pos X.B.μf ⟨1, h1Kg⟩
  have hvol_fin : X.B.μf (X.B.I.Kg X.B.g) < ⊤ :=
    lt_of_le_of_lt (measure_mono hKgK) ((Formalism.L2.SG.Closed.AutKCompact_holds X.B.I).measure_lt_top)
  set C : G0g D.nd → Set X.B.I.Gf := fun γ => (fun y => (s γ)⁻¹ * y) ⁻¹' X.B.I.Kg X.B.g with hCdef
  have hCmem : ∀ γ k, k ∈ C γ ↔ k ∈ X.B.I.Kset ∧ red k = γ := by
    intro γ k
    show (s γ)⁻¹ * k ∈ X.B.I.Kg X.B.g ↔ _
    constructor
    · intro hk'
      have hk2 : k = s γ * ((s γ)⁻¹ * k) := by group
      have hKk : k ∈ X.B.I.Kset := by rw [hk2]; exact K_mul _ (hsK γ) (hKgK hk')
      refine ⟨hKk, ?_⟩
      rw [hk2, hmul _ (hsK γ) _ (hKgK hk'), (hker _ (hKgK hk')).2 hk', mul_one, hsred]
    · rintro ⟨hKk, hrk⟩
      have hK' : (s γ)⁻¹ * k ∈ X.B.I.Kset := K_mul _ (K_inv _ (hsK γ)) hKk
      refine (hker _ hK').1 ?_
      have := hmul (s γ) (hsK γ) _ hK'
      rw [mul_inv_cancel_left, hrk, hsred] at this
      exact (left_eq_mul.mp this)
  have hCmeas : ∀ γ, MeasurableSet (C γ) := fun γ =>
    (hKgO.preimage (continuous_const.mul continuous_id)).measurableSet
  have hCvol : ∀ γ, X.B.μf (C γ) = X.B.μf (X.B.I.Kg X.B.g) := fun γ =>
    measure_preimage_mul X.B.μf _ _

  set vol : ℝ := (X.B.μf (X.B.I.Kg X.B.g)).toReal with hvol
  have hvol0 : (vol : ℂ) ≠ 0 := by
    rw [hvol]
    exact_mod_cast (ENNReal.toReal_pos hvol_pos.ne' hvol_fin.ne).ne'
  have hRg : Gd.Rg (star φ) = ∑ γ, D.ntypes.e0.coeff γ • X.B.R (1, s γ) (star φ) := by
    apply ext_inner_left ℂ
    intro x
    rw [Gd.Rg_spec.2 x (star φ), inner_sum]
    simp_rw [inner_smul_right]
    have hpt : ∀ k, eg X k * ⟪x, X.B.R (1, k) (star φ)⟫_ℂ =
        ∑ γ, (C γ).indicator (fun _ => D.ntypes.e0.coeff γ / (vol : ℂ) * ⟪x, X.B.R (1, s γ) (star φ)⟫_ℂ) k := by
      intro k
      by_cases hk : k ∈ X.B.I.Kset
      · have hgk := hgood k hk
        have heg : eg X k = D.ntypes.e0.coeff (red k) / (vol : ℂ) := by
          unfold eg
          rw [dite_eq_left ⟨hk, ⟨red k, hgk⟩⟩]
          congr 1
          exact Formalism.L2.SG.Pf.rowDictEgWellDef_holds X k _ _ (Classical.choose_spec _) hgk
        rw [Finset.sum_eq_single (red k)]
        · rw [Set.indicator_of_mem ((hCmem _ k).2 ⟨hk, rfl⟩), heg, hF1 k hk]
        · intro γ _ hγ
          exact Set.indicator_of_notMem (fun hm => hγ ((hCmem γ k).1 hm).2.symm) _
        · intro hn
          exact absurd (Finset.mem_univ _) hn
      · have heg : eg X k = 0 := by
          unfold eg
          rw [dite_eq_right (fun h' => hk h'.1)]
        rw [heg, zero_mul]
        symm
        refine Finset.sum_eq_zero fun γ _ => Set.indicator_of_notMem (fun hm => hk ((hCmem γ k).1 hm).1) _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_finsetSum _ (fun γ _ => (integrable_indicator_iff (hCmeas γ)).2
      (integrableOn_const (by rw [hCvol]; exact hvol_fin.ne)))]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [integral_indicator_const _ (hCmeas γ), Measure.real, hCvol, ← hvol, Complex.real_smul]
    field_simp

  have hstar : (star (Gd.Rg (star φ)) : L2X X) =
      ∑ γ, star (D.ntypes.e0.coeff γ) • star (X.B.R (1, s γ) (star φ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← conjL_apply (muX X), hRg, map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply]
    rfl
  rw [hstar]
  refine (hEv (fun γ => D.ntypes.e0.coeff γ) s (fun γ => ⟨hsK γ, hsred γ⟩)).trans
    (Filter.Eventually.of_forall fun x => ?_)
  have hc : (fun g => star (D.ntypes.e0.coeff (σ.symm g))) = RealDat.eC (A := A) D.what₂.embLL := by
    funext g
    rw [hC (σ.symm g), MulEquiv.apply_symm_apply]
  show gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (fun g => star (D.ntypes.e0.coeff (σ.symm g))) (S v₀) _ =
    R.e0 (S v₀) _
  rw [hc]
  rfl

end GlobalTheory.GoodProjEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodOpStarTranslatedEvalEqGoodProjectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), RowLevelMatchAt R F X h t → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → (star (Gd.Rg (star φ)) : L2X X) =ᵐ[muX X] (fun x => ev (MP R) v₀ (postOn (MP R) R.e0 S) (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  first | exact @GlobalTheory.GoodProjEval.goodOp_star_ev | exact GlobalTheory.GoodProjEval.goodOp_star_ev | (intros; apply GlobalTheory.GoodProjEval.goodOp_star_ev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsCompareByLevelMatchingEvaluation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeEval
section SlopeTestRemainingChoices
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem postOn_eq_of_mem (R : RealDat D A Ks) (F : Face D A) {S : MMap (MP R)} (hS : S ∈ EP R F) :
    postOn (MP R) R.e0 S = S :=
  sub_eq_zero.mp (LinearMap.mem_ker.mp hS.2)

theorem rg_fix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (φ : L2X X) (h2 : star (Gd.Rg (star φ)) = φ) :
    Gd.Rg (star φ) = star φ :=
  calc Gd.Rg (star φ) = star (star (Gd.Rg (star φ))) := (star_star _).symm
    _ = star φ := by rw [h2]

theorem ev_sub (R : RealDat D A Ks) (v₀ : (MP R).Vec) (S S' : MMap (MP R)) (y : GA D (Yc D 0)) :
    ev (MP R) v₀ (S - S') y = ev (MP R) v₀ S y - ev (MP R) v₀ S' y := by
  simp [ev_apply]
  rfl

end SlopeTestRemainingChoices

theorem evalTieT_of_levelMatch : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → RowLevelMatchAt R F X h t → ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd (iotaX X h).toMulEquiv t c' := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hE Gd t ht hConj hRow
  obtain ⟨c, hc, hsm⟩ := GlobalTheory.T.exists_linearIsometryEquiv_intertwining_modelRep hDS R F X h hLev hGrp hMod hHost hE
  let v₀ : (MP R).Vec := fun τ => ⟨(c τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by
    simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(c τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  have hne : ∀ τ, (v₀ τ : (MP R).H τ) ≠ 0 := fun τ h0 => by
    have := hnorm τ
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨σ, red, hA, -, -⟩ := id hRow
  obtain ⟨c0, hc0, hN⟩ := GlobalTheory.T.translatedRowEvaluation_squareIntegrable_norm R F X h hLev hGrp hMod t ht
  refine ⟨c0, Formalism.IndefR.AutomorphicEvaluation.evalTieT_of _ _ _ _ X Gd _ t c0 v₀ hnorm ?_ ?_ ?_⟩
  · intro S hS
    obtain ⟨hmem, hint, -⟩ := hN v₀ hnorm S hS
    have hHH := GlobalTheory.T.conj_rowEvaluation_translate_mem_rowSpace R F X h hLev hGrp hMod hHost hE t c v₀ ht hA hc hv₀ S hS _ hmem.coeFn_toLp
    have h1 := GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector R F X h hLev hGrp hMod Gd t v₀ hRow S hS.1 _ hmem.coeFn_toLp
    rw [postOn_eq_of_mem R F hS] at h1
    have hfix : Gd.Rg (star (hmem.toLp _)) = star (hmem.toLp _) :=
      rg_fix X Gd _ (Lp.ext (h1.trans hmem.coeFn_toLp.symm))
    refine ⟨⟨hmem.toLp _, Submodule.mem_inf.mpr ⟨hHH, LinearMap.mem_ker.mpr (sub_eq_zero.mpr hfix)⟩⟩,
      hmem.coeFn_toLp, ?_⟩
    show ‖(hmem.toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hmem]
    exact hint
  · intro Φ
    have hF : star (Φ : L2X X) ∈ goodSub X Gd := Φ.2
    have hfix : Gd.Rg (star (Φ : L2X X)) = star (Φ : L2X X) :=
      sub_eq_zero.mp (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hF).2)
    obtain ⟨S, hSM, hSF⟩ := GlobalTheory.T.conjRow_eq_translatedEvaluation_cuspFormMap hDS R F X h hLev hGrp hMod hHost hE t c v₀ ht hConj hc hv₀ (Φ : L2X X)
      (Submodule.mem_inf.mp hF).1
    have h1 := GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector R F X h hLev hGrp hMod Gd t v₀ hRow S hSM _ hSF
    rw [hfix, star_star] at h1
    have hz := GlobalTheory.T.multiplicityMap_eq_zero_of_translated_evaluation_ae_zero R F X h hLev hGrp hMod t v₀ hne S hSM _ rfl (by
      filter_upwards [h1, hSF] with x h1x h2x
      refine (ev_sub R v₀ _ _ _).trans ?_
      exact sub_eq_zero.mpr (h1x.symm.trans h2x))
    exact ⟨S, ⟨hSM, LinearMap.mem_ker.mpr hz⟩, hSF⟩
  · intro S hS h0
    obtain ⟨-, hint, hzero⟩ := hN v₀ hnorm S hS
    have hI : ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = 0 := by
      refine (integral_congr_ae ?_).trans (integral_zero _ _)
      filter_upwards [h0] with x hx
      have : ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) = 0 := hx
      simp [this]
    rw [hI] at hint
    have hre : (ipM (MP R) R.ν0 R.fd0 S S).re = 0 := by
      rcases mul_eq_zero.mp hint.symm with h' | h'
      · exact absurd h' hc0.ne'
      · exact h'
    exact hzero hre

end GlobalTheory.SeeEval
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsCompareByLevelMatchingEvaluationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodRows_compare_by_levelMatching_evaluation : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → RowLevelMatchAt R F X h t → ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd (iotaX X h).toMulEquiv t c' := by
  exact @GlobalTheory.SeeEval.evalTieT_of_levelMatch
end
