module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvari

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepsKernelEqSumCouplingCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeCombinationMovesLastStepDatumToChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeCombinationMovesLastStepDatumToChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QPl

theorem exchange_posOne_last : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m) (s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h)), s₁.χW = χ Q.s → ∀ α (Tm : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) →ₗ[ℂ] (WO (c.V Q.s) (c.V (Q.s + 1)) → ℂ)), (ofSplit Q.q).IsModel c.ψ (Q.FY Q.s (0 + 1) (by omega)) (Q.FY (Q.s + 1) 0 (by omega)) Tm → ∀ Φ Φα : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k), Φ.1 = Q.T.Phi Q.s 0 rfl → Φα.1 = om (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (Q.T.Phi Q.s 0 rfl) → ∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (Tm Φ) = Tm Φα := by
  intro D c v χ Q _ h s₁ hχ α Tm hTm Φ Φα hΦ hΦα
  obtain ⟨⟨ρ', hρ'⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep Q.k (Q.X Q.s ⊕ Fin (0 + 1)) (Q.X (Q.s + 1) ⊕ Fin 0)
    (Q.T.mu (Q.s + 1)) (Q.mu Q.s (by omega)).2
  have hsmooth := hsm ρ' hρ'
  obtain ⟨e, he, heL⟩ := Q.εL_at Q.s 0 h 0 rfl α
  obtain ⟨μS, hμS⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit Q.q) s₁.χV
  have hμT : (ofSplit Q.q).IsComp s₁.χW (Q.T.mu (Q.s + 1))⁻¹ := by
    intro x a hxa
    have := (Q.mu Q.s (by omega)).1 x a hxa
    rw [hχ, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, this]
    simp
  have hloc1 : (ofSplit Q.q).IsLoc (Q.FY (Q.s + 1) 0 (by omega)) 1 1 := by
    have := Q.gl_loc (Q.s + 1) 0 (by omega) 1
    rwa [map_one] at this
  have key : ∀ g, s₁.om (Q.gl Q.s (0 + 1) (by omega) g, 1) (Tm Φ) = Tm (ρ' g Φ) := by
    intro g
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) c.ψ _ _ s₁.χV s₁.χW s₁.om s₁.weil μS _ hμS hμT _ _ _ _ Tm hTm
      _ g 1 1 (Q.gl_loc Q.s (0 + 1) (by omega) g) hloc1 Φ (ρ' g Φ) ?_
    rw [hρ']
    funext x
    have hu : (((μS * Q.T.mu (Q.s + 1)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((μS⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
        = ((Q.T.mu (Q.s + 1) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
      rw [← Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_comm (μS _), mul_assoc, mul_inv_cancel, mul_one]
    simp only [om, Pi.smul_apply, smul_eq_mul, map_one, inv_one, Units.val_one, inv_inv]
    rw [← hu]
    ring
  have hN : ∀ g ∈ N Q.k (Q.X Q.s) (0 + 1) (0 + 1), g = 1 := by
    intro g hg
    have hle : N Q.k (Q.X Q.s) (0 + 1) (0 + 1) ≤ ⊥ := by
      refine (Subgroup.closure_le _).2 fun g' hg' => ?_
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      ext r s
      refine hg' r s ?_
      rcases r with r | r <;> rcases s with s | s <;> simp [GlobalTheory.RootEx.lev, Fin.val_eq_zero]
    exact Subgroup.mem_bot.1 (hle hg)
  let lx : Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k →
      (SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) →ₗ[ℂ] ℂ) :=
    fun x => (LinearMap.proj x).comp (SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k)).subtype
  have hsum : Φα = e.sum (fun g a => a • ρ' g Φ) := by
    apply Subtype.ext
    funext x
    have h1 := he _ ρ' hsmooth (lx x) (fun g hg w => by
        rw [hN g hg]
        simp [GlobalTheory.RootEx.simpleSum]) Φ (fun j => by
        apply Subtype.ext
        rw [hρ', Submodule.coe_smul, hΦ, (Q.laws.1 Q.s 0 rfl).1 j])
    have h2 : (Φα : Matrix _ _ _ → ℂ) x = lx x (ρ' (Q.rep Q.s 0 rfl α) Φ) := by
      simp only [lx, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply, hΦα]
      rw [hρ', hΦ]
    have h3 : ((e.sum fun g a => a • ρ' g Φ : SB _) : Matrix _ _ _ → ℂ) x = lx x (e.sum fun g a => a • ρ' g Φ) := rfl
    rw [h2, h3, map_finsuppSum]
    refine h1.trans ?_
    simp [GlobalTheory.PosOne.comb, map_smul]
  rw [heL]
  show (Finsupp.mapDomain _ e).sum (fun g a => a • s₁.om (g, 1) (Tm Φ)) = Tm Φα
  rw [Finsupp.sum_mapDomain_index (h := fun g (a : ℂ) => a • s₁.om (g, 1) (Tm Φ)) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rw [hsum, map_finsuppSum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [map_smul, key]

end GlobalTheory.QPl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeCombinationMovesLastStepDatumToChartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exchangeCombination_moves_lastStepDatum_to_chart : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m) (s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h)), s₁.χW = χ Q.s → ∀ α (Tm : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) →ₗ[ℂ] (WO (c.V Q.s) (c.V (Q.s + 1)) → ℂ)), (ofSplit Q.q).IsModel c.ψ (Q.FY Q.s (0 + 1) (by omega)) (Q.FY (Q.s + 1) 0 (by omega)) Tm → ∀ Φ Φα : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k), Φ.1 = Q.T.Phi Q.s 0 rfl → Φα.1 = om (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (Q.T.Phi Q.s 0 rfl) → ∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (Tm Φ) = Tm Φα := by
  first | exact @GlobalTheory.QPl.exchange_posOne_last | exact GlobalTheory.QPl.exchange_posOne_last | (intros; apply GlobalTheory.QPl.exchange_posOne_last <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiEqSumCoupIdx
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.Couple

theorem psi_eq_sum_coupIdx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (s : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z] (T : Chain k s X Z) (A : RepFam k s X) (c₁ c₂ : kˣ) (_ : T.Adapted A (box _ c₁) (box _ c₂)) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (ε : k) (S : Finset ((X (s + 1) → k) ⧸ box (X (s + 1)) c₂)) (_ : T.coupIdx A (box _ c₁) (box _ c₂) ⊆ S), ∀ g ∈ A s 0 rfl, ∀ x₀, (∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y) ∧ ∀ η, GlobalTheory.StepData.hat ψ ν ε (T.Psi g x₀) η = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * GlobalTheory.StepData.hat ψ ν ε (cosetInd (box _ c₂) yb) η := by
  intro k _ _ _ _ _ _ s X _ _ Z _ _ T A c₁ c₂ hA ψ hψ ν _ ε S hS g hg x₀
  classical
  have key : ∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y := by
    intro y
    have hc : ∀ yb, cosetInd (box _ c₂) yb y = if Submodule.Quotient.mk y = yb then 1 else 0 := by
      intro yb; simp [cosetInd, Set.indicator_apply]
    simp_rw [hc, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · exact (T.xiPen_mk hA hg y x₀).symm
    · by_contra hne
      exact hm (Finset.mem_coe.1 (hS ⟨y, (hA g hg x₀ y).1 hne, rfl, g, hg, x₀, hne⟩))
  refine ⟨key, fun η => ?_⟩
  have hfun : T.Psi g x₀ = fun y => ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y := funext key
  rw [hfun]
  simp only [GlobalTheory.StepData.hat, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun yb _ => ?_
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  · intro yb _
    simp_rw [mul_assoc]
    exact (integrable_hat ψ ν ε hψ (cosetInd_mem_SB c₂ yb) η).const_mul _

end GlobalTheory.Couple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepsKernelEqSumCouplingCosets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LastPt


set_option maxHeartbeats 4000000 in
theorem kernel_eq_sum : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ α (S : Finset ((Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂)), Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S → ∀ (d₁ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) (d₁ yb) (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb)) → (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM (d₂ yb) (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb)) → c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂) = ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
  intro D c v χ Q hc hv h hr hτ s₁ hχ X₁ X₂ h₁ h₂ α S hS d₁ d₂ hd₁ hd₂
  classical
  have hs := Q.hs
  have hsc : Q.sc Q.s ≠ 0 := Q.sc_ne Q.s
  obtain ⟨T₁, hT₁, hX₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Q.k Q.q Q.unit _ _ _ _ (Q.FY Q.s (0 + 1) (by omega)) (Q.FY (Q.s + 1) 0 rfl) c.ψ Q.ψk
    hc.std Q.char Q.cond _ _ (hv.sd Q.s (by omega)) (hv.sd (Q.s + 1) (by omega)) (Q.latY _ _ _) (Q.latY _ _ _)).2 X₁ h₁
  obtain ⟨T₂, hT₂, hX₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Q.k Q.q Q.unit _ _ _ _ (Q.FY (Q.s + 1) 0 rfl) Q.FT c.ψ Q.ψk
    hc.std Q.char Q.cond _ _ (hv.sd (Q.s + 1) (by omega)) hv.sdT (Q.latY _ _ _) Q.latT).2 X₂ h₂
  obtain ⟨F₀, hF₀⟩ := ((GlobalTheory.LocMod.normalFrames_exist D Q.k (ofSplit Q.q) _ 0 (Q.sc Q.s) hsc).1 (c.B Q.s 0 h)
    (Q.FX Q.s (by omega))).1
  have hjac := Q.jac Q.s 0 h 0 (by omega)
  obtain ⟨U₁, hU₁, hfl⟩ := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D) Q.k (ofSplit Q.q) Q.ν Q.unitVol.1
    c.ψ Q.ψk Q.char 0 (c.B Q.s 0 h) (c.J Q.s 0 h) s₁ (Q.sc Q.s) hsc _ _ 0 (Q.FX Q.s (by omega)) F₀
    (Q.FY Q.s (0 + 1) (by omega)) (Q.FX (Q.s + 1) le_rfl) (Q.FY (Q.s + 1) 0 rfl) hF₀ (Q.bes Q.s 0 h (0 + 1) (by omega)) hjac T₁ hT₁
  obtain ⟨U₂, hU₂, hres, hext⟩ := GlobalTheory.LevelLast.splitLocalPlace_isModel_wittExtendByZero_rankZero (ofSplit Q.q) c.ψ (c.jac Q.s 0 h).d (Q.FX (Q.s + 1) le_rfl)
    (Q.FY (Q.s + 1) 0 rfl) Q.FT hjac.2.1 T₂ hT₂
  let Φ₁ : SB _ := ⟨_, Q.reg.1 Q.s 0 rfl⟩
  let Φα : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) :=
    ⟨om (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (Q.T.Phi Q.s 0 rfl), om_mem_SB _ _ _ (Q.reg.1 Q.s 0 rfl)⟩
  let Φ₂ : SB _ := ⟨_, Q.reg.2.1⟩
  let O₁ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1))⟩
  let O₂ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Q.Z (Q.X (Q.s + 1) ⊕ Fin 0)⟩
  let O₁' : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1)) (Q.X Q.s ⊕ Unit)⟩
  let O₂' : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Q.Z (Q.X (Q.s + 1))⟩
  let Ψα : SB _ := ⟨_, ((GlobalTheory.LocFlat.flat_SB_onto Q.k Q.ψk Q.ν Q.cond.continuous Q.unitVol.1 _ _ 0 (0 + 1) le_rfl).1
    le_rfl).1 _ Φα.2⟩
  obtain ⟨Y₂, hY₂⟩ := hres Φ₂
  have a₁ : comb c.ψ _ _ (Q.eL Q.s) X₁ = T₁ Φ₁ := by
    rw [← hX₁ O₁ rfl]
    exact ((Q.eL_at Q.s 0 rfl).2 T₁ hT₁ O₁ Φ₁ rfl rfl).symm
  have a₂ : comb c.ψ _ _ Q.eLT X₂ = T₂ Φ₂ := by
    rw [← hX₂ O₂ rfl]
    exact (Q.eLT_at.2 T₂ hT₂ O₂ Φ₂ rfl rfl).symm
  have a₃ := GlobalTheory.T.exchangeCombination_moves_lastStepDatum_to_chart D c v χ Q hc h s₁ hχ α T₁ hT₁ Φ₁ Φα rfl rfl
  have b₁ : flatBF s₁ (T₁ Φα) = U₁ Ψα := hfl Φα Ψα rfl
  have b₁' : flatBF s₁ (T₁ O₁) = U₁ O₁' := hfl O₁ O₁' (by
    have := (GlobalTheory.LocFlat.flat_contr_intIndicator Q.k Q.ψk Q.ν Q.cond Q.unitVol (Q.X (Q.s + 1)) (Q.X Q.s) Unit 0 (0 + 1)).1
    rw [if_neg (by omega)] at this
    exact this.symm)
  have b₂ := hext Φ₂ Y₂ hY₂
  have b₂' := hext O₂ O₂' fun x => by
    have hx : (∀ r q, x r q ∈ 𝒪[Q.k]) ↔
        ∀ r (q : Q.X (Q.s + 1) ⊕ Fin 0), (fromCols x 0) r q ∈ 𝒪[Q.k] := by
      refine ⟨fun hx r q => ?_, fun hx r q => hx r (Sum.inl q)⟩
      rcases q with q | q
      · exact hx r q
      · exact q.elim0
    simp only [O₂, O₂', Set.indicator_apply, Set.mem_setOf_eq, hx]
  rw [a₁, a₂, a₃, ← hX₁ O₁ rfl, ← hX₂ O₂ rfl]
  unfold Comm.lst
  rw [b₁, b₁', b₂, b₂']
  obtain ⟨Λ, hΛ, hK⟩ := GlobalTheory.T.splitPlace_doubleStep_kernel_localModels D Q.k (ofSplit Q.q) Q.ν Q.unitVol.1 c.ψ hc.std Q.ψk Q.char 0 (c.B Q.s 0 h) (c.X (Q.s + 1))
    (c.X (Q.s + 1 + 1)) c.T c.Lz (c.oT (Q.s + 1 + 1) h) (v.τ Q.s h) hr hτ (Q.sc Q.s) Q.z₀ hsc (Q.tau h) _ _ _
    (Q.FX Q.s (by omega)) F₀ (Q.FX (Q.s + 1) le_rfl) Q.FT Q.FM hF₀ Q.last U₁ U₂ hU₁ hU₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Ψα Y₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁' O₂'
  have hv1 : valuation Q.k (-1 : Q.k) = 1 := by simp
  haveI := Q.unitVol.1
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.X (Q.s + 1)) (n' := Q.X Q.s)
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.Z ⊕ Unit) (n' := Q.X (Q.s + 1))
  let P₁ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1)) (Q.X Q.s)⟩
  let P₂ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.Z ⊕ Unit) (Q.X (Q.s + 1))⟩
  let E₁ := fun yb => (⟨_, (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).1⟩ : SB _)
  let E₂ := fun yb => (⟨_, (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).2⟩ : SB _)
  let E := fun yb => (⟨fun q => (E₁ yb).1 q.1 * (E₂ yb).1 q.2, GlobalTheory.FinPl.Comm.prod_mem_SB (E₁ yb).2 (E₂ yb).2 (s := id)
    continuous_fst continuous_snd continuous_id fun _ => rfl⟩ :
      SB (Matrix (Q.X (Q.s + 1)) (Q.X Q.s) Q.k × Matrix (Q.Z ⊕ Unit) (Q.X (Q.s + 1)) Q.k))
  have hsum : Ξ = ∑ yb ∈ S, E yb := Subtype.ext (funext fun q => by
    have e : (fun y => Ψα.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = Q.T.Psi (Q.rep Q.s 0 rfl α) q.1 :=
      funext fun y => GlobalTheory.LevelLast.flCol_one _ _ _ _
    rw [hΞ q, hY₂, e, (GlobalTheory.Couple.psi_eq_sum_coupIdx Q.k Q.s Q.X Q.Z Q.T Q.A Q.c₁ Q.c₂ Q.adapt Q.ψk Q.cond.continuous Q.ν (-1) S hS
      _ ((Q.rep_bij Q.s 0 rfl).mapsTo (Set.mem_univ α)) q.1).2, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun yb _ => mul_left_comm _ _ _)
  have hone : ∀ q, Ξ'.1 q = P₁.1 q.1 * P₂.1 q.2 := fun q => by
    have e : (fun y => O₁'.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        P₁.1 q.1 * cosetInd (box _ (1 : Q.kˣ)) (Submodule.Quotient.mk 0) y :=
      funext fun y => GlobalTheory.LastTwoSteps.intInd_fromCols q.1 y
    rw [hΞ' q, e, GlobalTheory.LastTwoSteps.hat_const_mul, GlobalTheory.LastTwoSteps.hat_int Q.cond Q.unitVol hv1]
    simp only [P₂, O₂']
    rw [GlobalTheory.LastTwoSteps.intInd_rows q.2]
    ring
  refine Eq.trans (funext hΞK) ?_
  show Λ Ξ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun yb _ => ?_
  refine ((GlobalTheory.T.heisenbergCombination_twoVariableModel_and_lineExtension D Q.k (ofSplit Q.q) c.ψ _ _ _).1 _ _ _ _ _ _ Λ (d₁ yb) (d₂ yb) (E₁ yb) P₁ (E₂ yb) P₂ (E yb) Ξ' hΛ
    (hd₁ yb) (hd₂ yb) rfl rfl (fun _ => rfl) hone).trans ?_
  exact congrArg _ (funext hΞ'K).symm

end GlobalTheory.QPl.LastPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepsKernelEqSumCouplingCosetsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ α (S : Finset ((Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂)), Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S → ∀ (d₁ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) (d₁ yb) (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb)) → (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM (d₂ yb) (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb)) → c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂) = ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
  first | exact @GlobalTheory.QPl.LastPt.kernel_eq_sum | exact GlobalTheory.QPl.LastPt.kernel_eq_sum | (intros; apply GlobalTheory.QPl.LastPt.kernel_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftAdditive
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastOneLin

variable {D : D7}

theorem sum_fin {G M : Type*} [AddCommMonoid M] (s : Finset G) (F : G → M) :
    ∑ g ∈ s, F g = ∑ i : Fin s.card, F (s.equivFin.symm i) := by
  rw [← Finset.sum_coe_sort s F]
  exact (Equiv.sum_comp s.equivFin.symm (fun x => F x)).symm

section Theta

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem biTheta_left (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO A S →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ A S c (fun u' => C u' v) u) := by
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  rw [GlobalTheory.BiTransfer.isBiTheta_iff_join d] at hC ⊢
  have e : GlobalTheory.BiTransfer.join d S (fun u v => comb ψ A S c (fun u' => C u' v) u) =
      fun w => ∑ x ∈ c.support, c x * heisO ψ _ S (GlobalTheory.BiTransfer.inlH d S x) (GlobalTheory.BiTransfer.join d S C) w := by
    funext w
    simp only [GlobalTheory.BiTransfer.join_apply, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [GlobalTheory.BiTransfer.symplOH_split d, map_add (GlobalTheory.BiTransfer.fstH d S), map_add (GlobalTheory.BiTransfer.sndH d S),
      GlobalTheory.BiTransfer.fst_inl, GlobalTheory.BiTransfer.snd_inl, add_zero, GlobalTheory.FinTranslate.symplOH_zero_right]
  rw [e]
  exact GlobalTheory.SeeSawFold.theta_sum' c.support _ fun x _ =>
    GlobalTheory.SeeSawFold.theta_const_mul' (c x) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hC _)

theorem biTheta_right (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (fun u v => comb ψ S A' c (C u) v) := by
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  rw [GlobalTheory.BiTransfer.isBiTheta_iff_join d] at hC ⊢
  have e : GlobalTheory.BiTransfer.join d S (fun u v => comb ψ S A' c (C u) v) =
      fun w => ∑ y ∈ c.support, c y * heisO ψ _ S (GlobalTheory.BiTransfer.inrH d S y) (GlobalTheory.BiTransfer.join d S C) w := by
    funext w
    simp only [GlobalTheory.BiTransfer.join_apply, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [GlobalTheory.BiTransfer.symplOH_split d, map_add (GlobalTheory.BiTransfer.fstH d S), map_add (GlobalTheory.BiTransfer.sndH d S),
      GlobalTheory.BiTransfer.fst_inr, GlobalTheory.BiTransfer.snd_inr, add_zero, GlobalTheory.FinTranslate.symplOH_zero_right, zero_add]
  rw [e]
  exact GlobalTheory.SeeSawFold.theta_sum' c.support _ fun y _ =>
    GlobalTheory.SeeSawFold.theta_const_mul' (c y) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hC _)

theorem biTheta_biComb_any (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (hC : IsBiTheta ψ A S A' C) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) :
    IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) :=
  biTheta_left hψ hθ (biTheta_right hψ hθ hC c') c

end Theta

theorem aconv_one {G : Type} [AddMonoid G] (d : G →₀ ℂ) : aconv [d] = d := by
  apply AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := G)
  rw [GlobalTheory.QValOuter.aconv_cons, GlobalTheory.QValOuter.aconv_nil, mul_one]

theorem comb_aconv_pair (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {E : AE D} (hE : cA D E = E) (hEE : E * E = E)
    (c d : WO S T →₀ ℂ) (hc : ∀ u ∈ c.support, IsHalf (1 - E) u) (hd : ∀ u ∈ d.support, IsHalf E u)
    (f : WO S T → ℂ) : comb ψ S T (aconv [c, d]) f = comb ψ S T c (comb ψ S T d f) := by
  have h := GlobalTheory.QFinLaw.comb_aconv_cons ψ S T c [d] (fun x hx y hy => by
    rw [aconv_one] at hy
    exact GlobalTheory.HeisComb.symplO_half S T (1 - E) E x y (by rw [map_sub, map_one, hE])
      (by rw [sub_mul, one_mul, hEE, sub_self]) (hc x hx) (hd y hy)) f
  rwa [aconv_one] at h

theorem place_idem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : cA D (q.e + cA D q.e) = q.e + cA D q.e ∧
      (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  have h3 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  refine ⟨by rw [map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm], ?_⟩
  linear_combination h1 + 2 * h2 + h3

theorem lin : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ (ι : Type) (S : Finset ι) (d₁ : ι → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : ι → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ i, ∀ u ∈ (d₁ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → (∀ i, ∀ u ∈ (d₂ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))) = ∑ i ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  intro D c v χ Q hc hv h hr hτ s₁ hs₁ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ ι S d₁ d₂ hd₁ hd₂
  obtain ⟨hE, hEE⟩ := place_idem (D := D) Q.q
  have hL : IsBiTheta c.ψ _ _ _ (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
    obtain ⟨-, -, hthS, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D c.ψ (c.V (Q.s + 1)) (c.X (Q.s + 1)) c.T (c.jac Q.s 0 h).d hc.std
    have hY' : IsThetaFunO c.ψ (c.X (Q.s + 1)) c.T (fun w => Ψ₂ ((c.jac Q.s 0 h).d.ext0 c.T w)) := (hthS Ψ₂).2 hΨ₂
    have hZ' : IsThetaFunO c.ψ (c.B Q.s 0 h).V (c.J Q.s 0 h).W Ψ₁ := hΨ₁
    obtain ⟨hΞ, -⟩ := GlobalTheory.LastRed.val_zero s₁ hZ'
    exact GlobalTheory.LastRed.lastBi_biTheta D c.ψ (c.bes Q.s 0 h).V₀ (c.X Q.s) (c.bes Q.s 0 h).L (c.X (Q.s + 1))
      (c.X (Q.s + 1 + 1)) c.T c.Lz (c.bes Q.s 0 h).o (c.oT (Q.s + 1 + 1) h) (v.τ Q.s h) hτ (flatBF s₁ Ψ₁) _ hΞ hY'
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hA : CoCpt (c.X Q.s) := (hc.x Q.s (by omega)).cpt
  have hS : CoCpt (c.X (Q.s + 1)) := (hc.x (Q.s + 1) (by omega)).cpt
  have step : biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) =
      ∑ i ∈ S, biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
    show (GlobalTheory.BiCombStable.biCombL c.ψ _ _ _ c₁ c₂) (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact GlobalTheory.ProdLocInv.biComb_comp c.ψ _ _ _ c₁ (d₁ i) (aconv [c₁, d₁ i]) c₂ (d₂ i) (aconv [c₂, d₂ i])
      (comb_aconv_pair c.ψ _ _ hE hEE c₁ (d₁ i) hc₁ (hd₁ i)) (comb_aconv_pair c.ψ _ _ hE hEE c₂ (d₂ i) hc₂ (hd₂ i)) _
  rw [step]
  funext h₂
  rw [Finset.sum_apply, sum_fin S (fun i => biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)),
    sum_fin S (fun i => c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) h₂)]
  exact GlobalTheory.SeeSmallPf.biLift_sum hB hoa hob hA hS _ _ hφ
    (fun j => biComb c.ψ _ _ _ (aconv [c₁, d₁ (S.equivFin.symm j)]) (aconv [c₂, d₂ (S.equivFin.symm j)])
      (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))
    (fun j => biTheta_biComb_any hc.std hc.inf hL _ _) h₂

end GlobalTheory.LastOneLin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftAdditiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawLastTwoSteps_doubleLift_additive : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ (ι : Type) (S : Finset ι) (d₁ : ι → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : ι → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ i, ∀ u ∈ (d₁ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → (∀ i, ∀ u ∈ (d₂ i).support, IsHalf (Q.q.e + cA D Q.q.e) u) → c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (∑ i ∈ S, biComb c.ψ _ _ _ (d₁ i) (d₂ i) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂))) = ∑ i ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ i]) (aconv [c₂, d₂ i]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.LastOneLin.lin | exact GlobalTheory.LastOneLin.lin | (intros; apply GlobalTheory.LastOneLin.lin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLastTwoSteps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QLastOne


set_option maxHeartbeats 1000000 in
theorem lastOne : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ α u, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂))) = ∑ y, (Nat.card {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} : ℂ) • c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by

  intro D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u
  classical
  obtain ⟨hfin, -, hsymm, htrans, hstab⟩ := GlobalTheory.T.twistPlace_couplingIndex_finite_level_stable D c v χ Q

  have hcomb : ∀ {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
      (FS : GlobalTheory.LocMod.Frame Q.k S.rank Y') (FT : GlobalTheory.LocMod.Frame Q.k T.rank Y) (Ξ : Matrix Y Y' Q.k → ℂ),
      Ξ ∈ SB _ → ∃ d, (ofSplit Q.q).IsCombAt c.ψ FS FT d Ξ := by
    intro S T Y Y' _ _ _ _ FS FT Ξ hΞ
    let O : SB (Matrix Y Y' Q.k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Y Y'⟩
    have hO : O ≠ 0 := by
      intro h0
      have := congrFun (congrArg Subtype.val h0) 0
      simp [O, Set.indicator_apply] at this
    obtain ⟨d, hd, hT⟩ := GlobalTheory.T.exists_heisenberg_combination_split_place_datum D Q.k (ofSplit Q.q) Y Y' S T FS FT c.ψ hc.std O ⟨Ξ, hΞ⟩ hO
    refine ⟨d, hd, fun Tm hTm Φ₀ Φ h0 h1 => ?_⟩
    have e0 : Φ₀ = O := Subtype.ext h0
    have e1 : Φ = ⟨Ξ, hΞ⟩ := Subtype.ext h1
    rw [e0, e1]
    exact hT Tm hTm
  choose d₁ hd₁ using fun yb => hcomb (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) _ (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).1
  choose d₂ hd₂ using fun yb => hcomb (Q.FX (Q.s + 1) le_rfl) Q.FM _ (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).2
  set S := hfin.toFinset with hS
  have hSc : Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S := by simp [S]
  have hmemS : ∀ yb, yb ∈ S ↔ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := fun yb => by simp [S]
  set C := c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂ with hC
  have hpt := GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets D c v χ Q hc hv h hr hτ s₁ hχ Ψ₁ Ψ₂ hΨ₁ hΨ₂ α S hSc d₁ d₂ hd₁ hd₂
  have hlin := GlobalTheory.T.seeSawLastTwoSteps_doubleLift_additive D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1 φ hφ
  rw [hpt, hlin _ S d₁ d₂ (fun i => (hd₁ i).1) (fun i => (hd₂ i).1)]

  set B : Q.Ch (Q.s + 1) → GA D (c.X (Q.s + 1 + 1)) → ℂ := fun y =>
    c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) C) with hB

  have hterm : ∀ yb ∈ S, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, d₁ yb]) (aconv [c₂, d₂ yb]) C) =
      ∑ y, if SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb then B y else 0 := by
    intro yb hyb
    obtain ⟨y₀, hy₀⟩ := Q.cos_cov yb ((hmemS yb).1 hyb)
    rw [Finset.sum_eq_single y₀]
    · rw [if_pos hy₀]
      exact GlobalTheory.T.doubleThetaLift_lastSteps_couplingCoset_orbit_invariant D c v χ Q hc hv h hr hτ s₁ hχ oma omb hoa hob c₁ c₂ hc₁ hc₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α u y₀ yb hy₀
        (d₁ yb) (d₂ yb) (hd₁ yb) (hd₂ yb)
    · intro y _ hy
      rw [if_neg]
      intro h'
      exact hy (Q.cos_inj y y₀ (htrans _ _ _ h' (hsymm _ _ hy₀)))
    · intro h'; exact absurd (Finset.mem_univ _) h'
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  by_cases hy : Q.cos y ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)
  · have hset : {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} =
        ↑(S.filter fun yb => SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb) := by
      ext yb
      simp only [Set.mem_setOf_eq, Finset.coe_filter]
      exact ⟨fun h' => ⟨(hmemS yb).2 (hstab _ hy yb h'), h'⟩, fun h' => h'.2⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.cast_smul_eq_nsmul]
  · have hempty : (S.filter fun yb => SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro yb hyb h'
      exact hy (hstab yb ((hmemS yb).1 hyb) _ (hsymm _ _ h'))
    have hnot : Q.cos y ∉ S := fun h' => hy ((hmemS _).1 h')

    have hz : biComb c.ψ _ _ _ (Q.dL Q.s α y) (Q.dL (Q.s + 1) y u) C = 0 := by
      have h2 := GlobalTheory.T.lastStepsKernel_eq_sum_couplingCosets D c v χ Q hc hv h hr hτ s₁ hχ Ψ₁ Ψ₂ hΨ₁ hΨ₂ α (insert (Q.cos y) S)
        (hSc.trans (by simp)) (Function.update d₁ (Q.cos y) (Q.dL Q.s α y))
        (Function.update d₂ (Q.cos y) (Q.dL (Q.s + 1) y u))
        (fun yb => by
          by_cases e : yb = Q.cos y
          · subst e; rw [Function.update_self]; exact Q.dL_pen α y
          · rw [Function.update_of_ne e]; exact hd₁ yb)
        (fun yb => by
          by_cases e : yb = Q.cos y
          · subst e; rw [Function.update_self]; exact Q.dL_top y u
          · rw [Function.update_of_ne e]; exact hd₂ yb)
      rw [hpt, Finset.sum_insert hnot, Function.update_self, Function.update_self] at h2
      have h3 : ∑ yb ∈ S, biComb c.ψ _ _ _ (Function.update d₁ (Q.cos y) (Q.dL Q.s α y) yb)
          (Function.update d₂ (Q.cos y) (Q.dL (Q.s + 1) y u) yb) C =
          ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) C := by
        refine Finset.sum_congr rfl fun yb hyb => ?_
        have e : yb ≠ Q.cos y := fun e => hnot (e ▸ hyb)
        rw [Function.update_of_ne e, Function.update_of_ne e]
      rw [h3] at h2
      rw [← hC] at h2
      have h4 := congrArg (fun F => F - ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) C) h2
      simp only [sub_self, add_sub_cancel_right] at h4
      exact h4.symm
    have hB0 : c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) C) = 0 := by
      have e1 := hlin Unit (Finset.univ : Finset Unit) (fun _ => Q.dL Q.s α y) (fun _ => Q.dL (Q.s + 1) y u)
        (fun _ => (Q.dL_pen α y).1) (fun _ => (Q.dL_top y u).1)
      have e2 := hlin Unit (∅ : Finset Unit) (fun _ => Q.dL Q.s α y) (fun _ => Q.dL (Q.s + 1) y u)
        (fun _ => (Q.dL_pen α y).1) (fun _ => (Q.dL_top y u).1)
      simp only [Finset.univ_unique, Finset.sum_singleton, Finset.sum_empty] at e1 e2
      rw [hz] at e1
      rw [← e1, e2]
    rw [hempty, Finset.card_empty, zero_smul, hB0, smul_zero]

end GlobalTheory.QLastOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLastTwoStepsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_twistPlace_last_two_steps : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ oma omb, IsWeilDatumO c.ψ _ _ (χ Q.s) (χ Q.s) oma → IsWeilDatumO c.ψ _ _ (χ (Q.s + 1)) (χ (Q.s + 1)) omb → ∀ c₁ c₂, (∀ u ∈ c₁.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → (∀ u ∈ c₂.support, IsHalf (1 - (Q.q.e + cA D Q.q.e)) u) → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ φ, IsContAut (c.X Q.s) φ → ∀ α u, c.bl Q.s oma omb φ (biComb c.ψ _ _ _ c₁ c₂ (c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂))) = ∑ y, (Nat.card {yb | SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) (Q.cos y) yb} : ℂ) • c.bl Q.s oma omb φ (biComb c.ψ _ _ _ (aconv [c₁, Q.dL Q.s α y]) (aconv [c₂, Q.dL (Q.s + 1) y u]) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.QLastOne.lastOne | exact GlobalTheory.QLastOne.lastOne | (intros; apply GlobalTheory.QLastOne.lastOne <;> assumption)
end
