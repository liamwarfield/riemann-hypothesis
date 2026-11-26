module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeRatioPosOfPublished
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColon

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainMeasureEq
open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst)

namespace GlobalTheory.AdelicVol

theorem exists_fundamentalDomain_measure_eq (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund) :
    ∃ (μ : Measure (HA (AF I.F) I.cm.sig I.J)) (S : Set (HA (AF I.F) I.cm.sig I.J)), μ.IsHaarMeasure ∧
      IsFundamentalDomain (HFinIn (AF I.F) I.cm.sig I.J) S μ ∧ μ S = I.muA μf fund := by
  obtain ⟨-, -, T, hT, -, -⟩ := GlobalTheory.AdelicModels.exists_adelic_equiv I
  obtain ⟨Γ, hΓ, -, -, hdom⟩ := GlobalTheory.RatDiscrete.rational_points I
  have hF : IsFundamentalDomain Γ fund (I.muA μf) := hdom μf fund hfund
  haveI : BorelSpace (HA (AF I.F) I.cm.sig I.J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : IsTopologicalGroup (HA (AF I.F) I.cm.sig I.J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : SecondCountableTopology I.Gf := (GlobalTheory.CongTop.adelic_topology I).2.2.1
  haveI : BorelSpace I.GA := inferInstance
  haveI hG1 : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => inferInstance
  haveI hG2 : ∀ v, SigmaFinite (Formalism.REAL.muG (I.ε v)) := fun v => inferInstance
  haveI hP : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := inferInstance
  haveI hPs : SigmaFinite (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) := inferInstance
  haveI : (I.muA μf).IsHaarMeasure := by unfold AutInst.muA; infer_instance
  have hTm : Measurable T := T.continuous.measurable
  have hTsm : Measurable T.symm := T.symm.continuous.measurable
  let μ : Measure (HA (AF I.F) I.cm.sig I.J) := Measure.map T.symm (I.muA μf)
  haveI hμ : μ.IsHaarMeasure :=
    T.symm.toMulEquiv.isHaarMeasure_map (I.muA μf) T.symm.continuous T.continuous
  let e : Γ → HFinIn (AF I.F) I.cm.sig I.J := fun g =>
    ⟨T.symm g, (hT (T.symm g)).2 (by
      rw [ContinuousMulEquiv.apply_symm_apply, ← hΓ]
      exact g.2)⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply T.symm.injective
      exact congrArg Subtype.val hab
    · intro h
      have hm : T h.1 ∈ I.GFset := (hT h.1).1 h.2
      rw [← hΓ] at hm
      refine ⟨⟨T h.1, hm⟩, Subtype.ext ?_⟩
      exact T.symm_apply_apply _
  have hsc : ∀ g : Γ, Function.Semiconj T (fun x : HA (AF I.F) I.cm.sig I.J => e g • x) (fun y : I.GA => (g : I.GA) * y) := by
    intro g x
    show T ((T.symm (g : I.GA)) * x) = (g : I.GA) * T x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have hmp : MeasurePreserving T μ (I.muA μf) := by
    refine ⟨hTm, ?_⟩
    rw [Measure.map_map hTm hTsm]
    have : (T ∘ T.symm) = id := funext fun y => T.apply_symm_apply y
    rw [this, Measure.map_id]
  refine ⟨μ, T ⁻¹' fund, hμ, hF.preimage_of_equiv hmp.quasiMeasurePreserving he hsc, ?_⟩
  rw [Measure.map_apply hTsm (hTm hfund.1), ← Set.preimage_comp]
  have : (T ∘ T.symm) = id := funext fun y => T.apply_symm_apply y
  rw [this, Set.preimage_id]

theorem vol_finite_pos : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund → I.muA μf fund < ⊤ ∧ I.muA μf fund ≠ 0 ∧ 0 < I.vol μf fund := by
  intro I μf _ _ fund hfund
  obtain ⟨hcm, hJ, -⟩ := GlobalTheory.AdelicModels.exists_adelic_equiv I
  obtain ⟨μ, S, hμ, hS, hμS⟩ := exists_fundamentalDomain_measure_eq I μf fund hfund
  have hfin : μ S < ⊤ := GlobalTheory.Mem.VolFin.finVol I.F I.E I.cm.sig hcm I.n I.J hJ μ hμ S hS
  have hne : μ S ≠ 0 :=
    ((GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary I.F I.E I.cm.sig I.n I.J μ hμ).2 S S hS hS).2
  rw [← hμS]
  refine ⟨hfin, hne, ?_⟩
  show 0 < ((I.muA μf) fund).toReal
  rw [← hμS]
  exact ENNReal.toReal_pos hne hfin.ne

end GlobalTheory.AdelicVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.TranslatedRow

variable {D : D7}

def Good (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (F : GA D (D.sp.Y 0) → ℂ) : Prop :=
  Continuous F ∧ (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) ∧ (∀ γ ∈ GQ (D.sp.Y 0), ∀ g, F (γ * g) = F g) ∧
    (∀ k ∈ J, ∀ g, F (g * k) = χ k * F g)

theorem good_add {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {F G : GA D (D.sp.Y 0) → ℂ}
    (hF : Good J χ F) (hG : Good J χ G) : Good J χ (F + G) := by
  obtain ⟨c1, ⟨C1, b1⟩, l1, r1⟩ := hF
  obtain ⟨c2, ⟨C2, b2⟩, l2, r2⟩ := hG
  refine ⟨c1.add c2, ⟨C1 + C2, fun g => (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g))⟩,
    fun γ hγ g => by simp [l1 γ hγ g, l2 γ hγ g], fun k hk g => by simp [r1 k hk g, r2 k hk g, mul_add]⟩

theorem good_smul {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {F : GA D (D.sp.Y 0) → ℂ} (c : ℂ)
    (hF : Good J χ F) : Good J χ (c • F) := by
  obtain ⟨c1, ⟨C1, b1⟩, l1, r1⟩ := hF
  refine ⟨continuous_const.mul c1, ⟨‖c‖ * C1, fun g => ?_⟩, fun γ hγ g => by simp [l1 γ hγ g],
    fun k hk g => by simp [r1 k hk g]; ring⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (b1 g) (norm_nonneg _)

theorem good_of_mem (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {S : D.what₂.Tau → SPar}
    {M : DSModel (D.sp.Y 0) S} {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ}
    {T : SmT M →ₗ[ℂ] (GA D (D.sp.Y 0) → ℂ)} (hT : T ∈ MultT θ M J χ) (x : SmT M) : Good J χ (T x) := by
  have h1 := (GlobalTheory.MultMem.mem_mult_iff D θ _ S M J χ _).1 ((mem_multT θ M J χ T).1 hT)
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul]
    refine good_smul c ?_
    have e : T (PiTensorProduct.tprod ℂ v) = (PiTensorProduct.lift.symm T) v := by
      rw [PiTensorProduct.lift_symm]; rfl
    rw [e]
    exact ⟨(h1.aut v).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h1.aut v) (h1.cusp v), (h1.aut v).left,
      fun k hk g => h1.lev v k hk g⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact good_add ha hb

end GlobalTheory.Core.Mi.TranslatedRow

namespace GlobalTheory.Core.Mi.TranslatedRow

variable {D : D7}

theorem castGA_symm_mem' {I I' : Formalism.MainNotions.S.AutInst} (p : I = I') (γ : I'.GA) (hγ : γ ∈ I'.GFset) :
    (castGA p).symm γ ∈ I.GFset := by
  subst p
  exact hγ

theorem rat_of_GF (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ : X.B.I.GA) (hγ : γ ∈ X.B.I.GFset) : (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
  refine (Formalism.IndefR.RationalEmbedding.iota_rat D ((iotaX X h).symm γ)).2 ?_
  show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact castGA_symm_mem' _ γ hγ

theorem rowFun_of_good (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {t : GA D (D.sp.Y 0)} (hm : Matches X h J χ t)
    {F : GA D (D.sp.Y 0) → ℂ} (hF : Good J χ F) : RowFun X (evS X h t F) := by
  obtain ⟨hc, ⟨C, hb⟩, hl, hr⟩ := hF
  refine ⟨hc.comp ((iotaX X h).symm.continuous.mul continuous_const), ⟨C, fun x => hb _⟩, fun γ hγ x => ?_,
    fun k hk x => ?_⟩
  · show F ((iotaX X h).symm (γ * x) * t) = F ((iotaX X h).symm x * t)
    rw [map_mul, mul_assoc]
    exact hl _ (rat_of_GF X h γ hγ) _
  · show F ((iotaX X h).symm (x * (1, k)) * t) = star (X.chi2 k) * F ((iotaX X h).symm x * t)
    set κ := t⁻¹ * (iotaX X h).symm (1, k) * t with hκ
    have hc1 := hm.2 κ
    have e1 : t⁻¹⁻¹ * κ * t⁻¹ = (iotaX X h).symm (1, k) := by simp [hκ, mul_assoc]
    rw [e1] at hc1
    have hrow : (iotaX X h).symm (1, k) ∈ rowJ X h := by
      simp only [rowJ, Set.mem_preimage, ContinuousMulEquiv.apply_symm_apply, Set.mem_setOf_eq]
      exact ⟨trivial, hk⟩
    have hκJ : κ ∈ J := hc1.1.2 hrow
    have hχ := hc1.2 hκJ
    have e2 : (iotaX X h).symm (x * (1, k)) * t = ((iotaX X h).symm x * t) * κ := by
      simp [hκ, map_mul, mul_assoc]
    have e3 : rowChi X h ((iotaX X h).symm (1, k)) = star (X.chi2 k) := by
      simp only [rowChi, ContinuousMulEquiv.apply_symm_apply]
    rw [e2, hr κ hκJ, ← hχ, e3]

theorem muX_finite (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : IsFiniteMeasure (muX X) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact (GlobalTheory.AdelicVol.vol_finite_pos X.B.I X.B.μf X.B.fund X.B.fund_spec).1

end GlobalTheory.Core.Mi.TranslatedRow


open GlobalTheory.Core.Mi.TranslatedRow in
theorem GlobalTheory.Core.Mi.rowFun_evS : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), IsInfFam θ → Matches X h J χ t → ∀ T ∈ MultT θ M J χ, ∀ x : SmT M, RowFun X (evS X h t (T x)) ∧ MemLp (evS X h t (T x)) 2 (muX X) := by
  intro hP D X h θ S M J χ t hθ hm T hT x
  have hg := good_of_mem hP hθ hT x
  have hR := rowFun_of_good X h hm hg
  refine ⟨hR, ?_⟩
  haveI := muX_finite X
  obtain ⟨C, hC⟩ := hR.bdd
  exact MemLp.of_bound hR.cont.aestronglyMeasurable C (.of_forall hC)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), IsInfFam θ → Matches X h J χ t → ∀ T ∈ Formalism.IndefR.Mult.MultT θ M J χ, ∀ x : SmT M, RowFun X (evS X h t (T x)) ∧ MemLp (evS X h t (T x)) 2 (muX X) := by
  first | exact @GlobalTheory.Core.Mi.rowFun_evS | exact GlobalTheory.Core.Mi.rowFun_evS | (intros; apply GlobalTheory.Core.Mi.rowFun_evS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.FrameAct

theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  simp

theorem finE_inv_val' {D : D7} (V : HSp D) (g : GA D V) :
    ((Lev.finE V g)⁻¹).1 = (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) := by
  rw [← map_inv]; rfl

theorem conj_inv_val' {D : D7} {n : ℕ} (β y : GL (Fin n) (Lev.EAf D)) :
    ((β⁻¹ * y * β)⁻¹ : GL (Fin n) (Lev.EAf D)).1 = (β⁻¹).1 * (y⁻¹).1 * β.1 := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]

theorem frMapO_actO_left : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (x : WO S T), frMapO S T βS βT (actO S T g 1 x) = HMul.hMul (frMapO S T βS βT x) ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
  intro D S T βS βT g x
  rw [frMapO, frMapO, actO, mt_one', Matrix.one_mul, Matrix.map_mul, conj_inv_val', finE_inv_val']
  have hb : βS.1 * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1, hb, Matrix.one_mul]

end GlobalTheory.ChainOnto.FrameAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInvStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_weilPairAction_left_inv : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (x : WO S T), frMapO S T βS βT (actO S T g 1 x) = HMul.hMul (frMapO S T βS βT x) ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
  exact @_root_.GlobalTheory.ChainOnto.FrameAct.frMapO_actO_left
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactFiniteAdelicSubgroupIntegralOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactFiniteAdelicSubgroupIntegralOpen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem isCompact_of_integral_open (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) (K : Subgroup (GA D V)) (hKf : K ≤ GfC V)
    (hKi : ∀ k ∈ K, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v)
    (hU : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ K) :
    IsCompact (K : Set (GA D V)) := by
  haveI : Submodule.IsFullLattice D.host.E Λ :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ
  obtain ⟨U, hUo, hUK⟩ := hU
  have hGf : IsClosed ((GfC V : Subgroup (GA D V)) : Set (GA D V)) := by
    rw [GlobalTheory.AdelicU.GfC_eq]; exact GlobalTheory.AdelicU.isClosed_finPts _ _

  have hopen : IsOpen ((K.subgroupOf (GfC V)) : Set (GfC V)) := by
    refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) ?_ ?_
    · intro x hx
      exact Subgroup.mem_subgroupOf.2 (hUK _ (Subgroup.mem_subgroupOf.1 hx) x.2)
    · exact hUo.preimage continuous_subtype_val
  have hcl : IsClosed ((K.subgroupOf (GfC V)) : Set (GfC V)) := Subgroup.isClosed_of_isOpen _ hopen
  have hKcl : IsClosed (K : Set (GA D V)) := by
    have h := hcl.trans hGf
    convert h using 1
    ext g
    constructor
    · intro hg; exact ⟨⟨g, hKf hg⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact Subgroup.mem_subgroupOf.1 hx
  refine (GlobalTheory.AdelicU.isCompact_levelFin D.sp.cm.sig V.gram Λ).of_isClosed_subset hKcl ?_
  intro k hk
  refine GlobalTheory.AdelicU.mem_levelFin.2 ⟨?_, hKi k hk⟩
  have := hKf hk
  rw [GlobalTheory.AdelicU.GfC_eq] at this
  exact this

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactFiniteAdelicSubgroupIntegralOpenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ K : Subgroup (GA D V), K ≤ GfC V → (∀ k ∈ K, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) → (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ K) → IsCompact (K : Set (GA D V)) := by
  first | exact @GlobalTheory.ChainOnto.isCompact_of_integral_open | exact GlobalTheory.ChainOnto.isCompact_of_integral_open | (intros; apply GlobalTheory.ChainOnto.isCompact_of_integral_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensors
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFiniteLevel

theorem mem_multT_of_kfin : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), (∀ κ ∈ J, κ ∈ GfC V) → ∀ F ∈ MultT θ M ∅ 1, (∀ w ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), ∀ κ ∈ J, ∀ g, F w (g * κ) = χ κ * F w g) → F ∈ MultT θ M J χ := by
  intro D V S M θ hθ J χ hJ F hF hk
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff] at hF ⊢
  set T : MMap M := PiTensorProduct.lift.symm F with hTdef
  have hT : ∀ v : M.Vec, T v = F (PiTensorProduct.tprod ℂ v) := fun v => by
    rw [hTdef, PiTensorProduct.lift_symm]; rfl
  refine ⟨hF.aut, hF.cusp, fun v κ hκ g => ?_, hF.equiv, hF.cont⟩
  set U : MMap M := heckeOn M {κ} T - χ κ • T with hUdef
  have hU : U ∈ Mult θ M ∅ 1 :=
    sub_mem ((GlobalTheory.MultMem.mem_mult_iff ..).2 (GlobalTheory.SphericalOps.isMultMap_single hF (hJ κ hκ)))
      (Submodule.smul_mem _ _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hF))
  have hUv : ∀ (u : M.Vec) (x : GA D V), U u x = T u (x * κ) - χ κ * T u x := fun u x => by
    simp [hUdef, heckeOn, postOn_apply, heckeLin_apply]
  have h0 : U = 0 := GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M ∅ 1 U hU fun u hu => by
    funext x
    rw [hUv, hT, Pi.zero_apply, sub_eq_zero]
    exact hk _ (Submodule.subset_span ⟨u, fun τ => Submodule.subset_span (hu τ), rfl⟩) κ hκ x
  have := hUv v g
  rw [h0] at this
  exact (sub_eq_zero.1 this.symm)

end GlobalTheory.KFiniteLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), (∀ κ ∈ J, κ ∈ GfC V) → ∀ F ∈ MultT θ M ∅ 1, (∀ w ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), ∀ κ ∈ J, ∀ g, F w (g * κ) = χ κ * F w g) → F ∈ MultT θ M J χ := by
  exact @_root_.GlobalTheory.KFiniteLevel.mem_multT_of_kfin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlaces
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.ParamInert

open Formalism.UG (IsUnramInv GU KU qV IsInertAt)

theorem paramBoundOn_nonsplit (hUDI : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert) :
    ∀ D : D7, ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro D A L hL v hv par c hc hc1 w hw
  obtain ⟨⟨C, hC⟩, V, iV, iM, ρ, x, ℓ, hpar, hℓ, hcv⟩ := hc
  have hp := hpar w hw
  refine ⟨hp.card, ?_⟩
  rcases hp with ⟨hs, -⟩ | ⟨hin, τ, ϖ, e, α, hU, he, hsat, hB⟩
  · exact absurd hs hv
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have h4 := hU.2.2.2.1
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  set ϖu : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ hϖ0 with hϖu
  have hU' : IsUnramInv ((ϖu : w.adicCompletion D.host.E)) τ (qV D.host.F v) := hU
  set ρ' : Representation ℂ (GU τ A.rank) V := ρ.comp e.symm.toMonoidHom with hρ'
  have hKinv : ∀ k ∈ KU τ A.rank, ∀ g, ℓ (ρ' (k * g) x) = ℓ (ρ' g x) := by
    intro k hk g
    have hk' : e.symm k ∈ stabLoc D.sp.cm.sig A.gram L v := by
      rw [he.2.2, MulEquiv.apply_symm_apply]; exact hk
    simp only [hρ', MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, map_mul]
    rw [← map_mul]
    exact hℓ _ hk' _
  have h1 : ℓ x ≠ 0 := by
    intro h0; apply hc1; rw [hcv, map_one]; exact h0
  have hz := (GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal _ ϖu τ (qV D.host.F v) A.rank hU' V ρ' x α hsat ℓ hKinv).2 h1
  have hbd : ∃ C' : ℝ, ∀ g, ‖ℓ (ρ' g x) / ℓ x‖ ≤ C' := by
    refine ⟨C / ‖ℓ x‖, fun g => ?_⟩
    rw [norm_div]
    have : ‖ℓ (ρ' g x)‖ ≤ C := by
      have := hC (e.symm g); rw [hcv] at this; exact this
    exact div_le_div_of_nonneg_right this (norm_nonneg _)
  have htb := GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary hUDI _ ϖu τ (qV D.host.F v) A.rank hU' α _ hz hbd
  intro β hβ
  rw [hB] at hβ
  have hq2 : 2 ≤ qV D.host.F v := hU.2.2.2.2.2.1
  have hle := GlobalTheory.FinZeta.ParamBound.norm_le_of_mem_bcParam hq2 htb β hβ
  have hnorm : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 :=
    ((GlobalTheory.LFun.exists_isInertChart _ (isCMExt_host D) v).2 w hw hin).2.2.2.1
  have hqv : (qV D.host.F v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := rfl
  rw [hnorm, Nat.cast_pow, ← hqv]
  refine hle.trans (Real.rpow_le_rpow_of_exponent_le ?_ ?_)
  · have : (1 : ℝ) ≤ qV D.host.F v := by exact_mod_cast (by omega : 1 ≤ qV D.host.F v)
    nlinarith
  · linarith

end GlobalTheory.Core.Rk.ParamInert
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlacesStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalParameterBound_nonsplit_places : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.Core.Rk.ParamInert.paramBoundOn_nonsplit | exact GlobalTheory.Core.Rk.ParamInert.paramBoundOn_nonsplit | (intros; apply GlobalTheory.Core.Rk.ParamInert.paramBoundOn_nonsplit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCharQuotientLFunctionEntireNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCharQuotientLFunctionEntireNeZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.QuotL

theorem e_strictMono {R : Ranks} (P : HCParam R) : StrictMono P.e := by
  have ht : (0 : ℚ) ≤ R.t := by positivity
  have step : ∀ (a : ℕ) (h : a + 1 < R.m), P.e ⟨a, by omega⟩ < P.e ⟨a + 1, h⟩ := fun a h => by
    have g1 := P.gap_eb ⟨a, by omega⟩ h
    have g2 := P.gap_be ⟨a + 1, h⟩
    linarith
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
  induction d with
  | zero => exact step a hb
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := step (a + d + 1) (by omega)
    have e1 : (⟨a + (d + 1) + 1, hb⟩ : Fin R.m) = ⟨a + d + 1 + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e1]
    exact h1.trans h2

variable {D : D7}

theorem trivialOnF {c : Com D} (hc : c.Is) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.TrivialOnF (c.μ k) := fun a => by
  obtain ⟨⟨η, hη⟩, h⟩ := (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2
  exact (h η hη a).trans (pow_zero _)

theorem isHecke {c : Com D} (hc : c.Is) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) : IsHeckeChar D (c.μ k) :=
  (hc.chars.2.2.2.2 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).1

theorem quotL_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m →
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
  intro D c hc i j hi hij hj
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.μ (i' + 1)) τ (-e) ∧
      HasInfExp D (c.μ (j' + 1)) τ (-e') ∧ e ≠ e' :=
    ⟨τ, (D.hc τ).e ⟨i', by omega⟩, (D.hc τ).e ⟨j', by omega⟩, hc.exp ⟨i', by omega⟩ τ, hc.exp ⟨j', by omega⟩ τ,
      (e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
        Fin.mk_lt_mk.2 (by omega))).ne⟩
  obtain ⟨Λ, ⟨hd, hp⟩, hpos⟩ := (GlobalTheory.HeckeRatio.heckeRatioPos D (c.μ (i' + 1)) (c.μ (j' + 1))
    (isHecke hc (by omega) (by omega)) (isHecke hc (by omega) hj) (trivialOnF hc (by omega) (by omega))
    (trivialOnF hc (by omega) hj) hexp D.R.t).2 c.S
  refine ⟨Λ, hd, fun z hz => ?_, fun n h1 h2 h0 => ?_⟩
  · have hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
        GlobalTheory.LFun.UnrAt (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w := fun w hw =>
      (hc.unr ⟨i', by omega⟩ w hw).mul (hc.unr ⟨j', by omega⟩ w hw).inv
    have hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) :=
      fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl
    let e := Equiv.subtypeEquivRight hoff
    have k := hp z hz
    rw [GlobalTheory.HeckeRatio.lfac_eq] at k
    have k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
        GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹) w}) w.1 z) (Λ z) := by
      refine (e.hasProd_iff).1 (k.congr_fun fun P => ?_)
      have hu := hunr P.1 ((hoff P.1).1 P.2)
      rw [GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]
      simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL,
        GlobalTheory.LFun.charFam_of_unrAt hu]
    exact k2.tprod_eq.symm
  · have := (hpos n h1 h2).2
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this

end GlobalTheory.ChainOnto.QuotL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCharQuotientLFunctionEntireNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_char_quotient_LFunction_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w}) z) ∧ ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
  first | exact @GlobalTheory.ChainOnto.QuotL.quotL_entire_ne_zero | exact GlobalTheory.ChainOnto.QuotL.quotL_entire_ne_zero | (intros; apply GlobalTheory.ChainOnto.QuotL.quotL_entire_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlace
noncomputable section

namespace GlobalTheory.Core.Rk.BdSplit

section Abstract

open Formalism.UG GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}


open Classical in
def cosetInd (S : Finset (G ⧸ K)) : G → ℂ := fun g => if (g : G ⧸ K) ∈ S then 1 else 0

theorem cosetInd_mem {S : Finset (G ⧸ K)} (hS : ∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) : cosetInd S ∈ Hecke ℂ K := by
  classical
  refine ⟨fun a b g => ?_, S.image Quotient.out, fun g hg => ?_⟩
  · have e : ((a * g * b : G) : G ⧸ K) = (a : G) • (g : G ⧸ K) := QuotientGroup.mk_mul_of_mem _ b.2
    have : (a : G) • (g : G ⧸ K) ∈ S ↔ (g : G ⧸ K) ∈ S :=
      ⟨fun h => by simpa using hS _ (inv_mem a.2) _ h, hS _ a.2 _⟩
    simp only [cosetInd, e, this]
  · have h : (g : G ⧸ K) ∈ S := by
      by_contra h
      exact hg (if_neg h)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨_, Finset.mem_image_of_mem _ h, 1, k⁻¹, by rw [hk]; simp⟩

theorem heckeVec_cosetInd (ρ : Representation ℂ G V) (S : Finset (G ⧸ K)) (x : V) :
    heckeVec ρ K (cosetInd S) x = ∑ c ∈ S, ρ c.out x := by
  rw [heckeVec, finsum_eq_sum_of_support_subset (s := S)]
  · exact Finset.sum_congr rfl fun c hc => by simp [cosetInd, hc]
  · intro c hc
    by_contra h
    exact hc (by simp [cosetInd, show c ∉ S from h])

theorem norm_le_card {ι : Type} (ρ : Representation ℂ G V) {x : V} (l : V →ₗ[ℂ] ℂ) {C : ℝ}
    (hC : ∀ y, ‖l (ρ y x)‖ ≤ C) (h1 : l (ρ 1 x) ≠ 0) (S : Finset ι) (g : ι → G) (a : ℂ)
    (h : ∑ c ∈ S, ρ (g c) x = a • x) : ‖a‖ ≤ S.card := by
  have hb : BddAbove (Set.range fun y => ‖l (ρ y x)‖) := ⟨C, by rintro _ ⟨y, rfl⟩; exact hC y⟩
  set M := ⨆ y, ‖l (ρ y x)‖
  have hM : ∀ y, ‖l (ρ y x)‖ ≤ M := fun y => le_ciSup hb y
  have hM0 : 0 < M := (norm_pos_iff.2 h1).trans_le (hM 1)
  have key : ∀ y, ‖a‖ * ‖l (ρ y x)‖ ≤ S.card * M := fun y => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← norm_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← h, map_sum, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun c _ => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact hM _
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have : M ≤ S.card * M / ‖a‖ := ciSup_le fun y => by rw [le_div_iff₀' h0]; exact key y
    rw [le_div_iff₀' h0] at this
    exact le_of_mul_le_mul_right this hM0

end Abstract

section Linear

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SatakeBound

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem norm_le_of_isSatVecGL {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (l : V →ₗ[ℂ] ℂ) {C : ℝ} (hC : ∀ y, ‖l (ρ y x)‖ ≤ C) (h1 : l (ρ 1 x) ≠ 0) :
    ∀ β ∈ B, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  obtain ⟨α, rfl⟩ : ∃ α : Fin n → ℂˣ, Finset.univ.val.map α = B := by
    obtain ⟨l, rfl⟩ := Quot.exists_rep B
    obtain rfl : l.length = n := hx.2.2.1
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  obtain ⟨φ, hφ, hφ1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at hφ1
  have hy := isSatVecGL_of_isSpherical hφ hφ0
  have hKO : KO (w.adicCompletion E) (Fin n) = KGL w (n := n) := SphCompletion.KO_completion w n
  have hb : HasBoundedSums (w.adicCompletion E) φ := by
    intro S hS
    have H := SatCompare.exists_eigenvalue_GL hx hy
    rw [← hKO] at H
    obtain ⟨c, e1, e2⟩ := H _ (cosetInd_mem hS)
    rw [heckeVec_cosetInd] at e1 e2
    have e3 : ∑ c ∈ S, φ c.out = c := by
      have := congrFun e2 1
      rw [Finset.sum_apply, Pi.smul_apply, hφ1, smul_eq_mul, mul_one] at this
      rw [← this]
      exact Finset.sum_congr rfl fun c _ => congrArg φ (one_mul _).symm
    rw [e3]
    exact norm_le_card ρ l hC h1 S _ c e1
  have hs : IsBorelSph (w.adicCompletion E) (fun i : Fin n => (α i : ℂ) *
      (((resCard (w.adicCompletion E) : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ := by
    refine ⟨fun g k hk => congrFun (GlobalTheory.LGrp.mem_fixed.1 hy.2.1 k (hKO ▸ hk)) g, fun b hb' t ht => ?_⟩
    obtain ⟨y, -, rfl⟩ := (SphCompletion.isSpherical_iff E w n α φ).1 hφ
    have h := GlobalTheory.SatakeBound.Rep.law α y b hb' t ht 1
    rwa [hφ1, mul_one, mul_one] at h
  intro β hβ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hβ
  have hq : (0 : ℝ) < resCard (w.adicCompletion E) := by
    exact_mod_cast (GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard (w.adicCompletion E)).le
  have h2 := norm_le_pow hs hb i
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _), ← Real.rpow_natCast] at h2
  rw [← le_div_iff₀ (Real.rpow_pos_of_pos hq _), ← Real.rpow_sub hq] at h2
  rw [← GlobalTheory.LFun.SatBoundGL.resCard_completion w]
  exact h2.trans_eq (congrArg _ (by ring))

end Linear

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem paramBound_split : ∀ D : D7, ParamBoundOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  rintro D A L - v hv par c ⟨⟨C, hC⟩, V, _, _, ρ, x, l, hx, -, hc⟩ h1 w h
  refine ⟨(hx w h).card, fun β hβ => ?_⟩
  rcases hx w h with ⟨-, e, -, hx⟩ | ⟨hw, -⟩
  · have hb := norm_le_of_isSatVecGL hx l (C := C) (fun y => (hc (e.symm y)) ▸ hC (e.symm y))
      (by rw [hc] at h1; rwa [map_one, ← map_one ρ]) β hβ
    refine hb.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by linarith))
    exact_mod_cast (GlobalTheory.LFun.one_lt_absNorm w).le
  · exact absurd hv (GlobalTheory.LFun.not_isSplit_of_isInertAt hw)

end GlobalTheory.Core.Rk.BdSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundSplitPlaceStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalParameterBound_split_place : ∀ D : D7, ParamBoundOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.Core.Rk.BdSplit.paramBound_split | exact GlobalTheory.Core.Rk.BdSplit.paramBound_split | (intros; apply GlobalTheory.Core.Rk.BdSplit.paramBound_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSlice

variable {D : D7}

theorem symplOH_zero_right' (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem symplOH_zero_left' (S T : HSp D) (x : WO S T) : symplOH S T 0 x = 0 := by
  simp [symplOH, symplO, hO]

def shiftA {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) : WO S T →+ WO S T where
  toFun w := (o.resS T).symm (actO A T g⁻¹ h⁻¹ (o.resS T w).1, (o.resS T w).2)
  map_zero' := by simp [actO_eq]
  map_add' x y := by
    rw [map_add (f := _), Prod.fst_add, Prod.snd_add, ← map_add (f := _)]
    congr 1
    simp [actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem shiftA_apply {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T) :
    shiftA o T g h w = (o.resS T).symm (actO A T g⁻¹ h⁻¹ (o.resS T w).1, (o.resS T w).2) := rfl

theorem actO_shift (A T : HSp D) (g : GA D A) (h : GA D T) (u : WO A T) : actO A T g h (actO A T g⁻¹ h⁻¹ u) = u := by
  simp only [actO_eq, inv_inv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (mt T h), mt_mul_inv, Matrix.one_mul, mt_mul_inv, Matrix.mul_one]

theorem continuous_shiftA {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) :
    Continuous (shiftA o T g h) := by
  have h1 : Continuous fun w : WO S T => (o.resS T w).1 := continuous_fst.comp (o.continuous_resS T)
  have h2 : Continuous fun w : WO S T => (o.resS T w).2 := continuous_snd.comp (o.continuous_resS T)
  refine (o.continuous_resS_symm T).comp (Continuous.prodMk ?_ h2)
  simp only [actO_eq]
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const

theorem shiftA_fin {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T)
    (hw : w.map (finPart D) = 0) : (shiftA o T g h w).map (finPart D) = 0 := by
  rw [shiftA_apply, OrthDec.resS_symm_apply]
  simp only [OrthDec.resS_apply, actO_eq]
  rw [Matrix.map_add _ (map_add (finPart D))]
  simp only [Matrix.map_mul, hw, Matrix.zero_mul, Matrix.mul_zero, zero_add]

theorem shiftA_inf {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T)
    (hw : w.map (infPart D) = 0) : (shiftA o T g h w).map (infPart D) = 0 := by
  rw [shiftA_apply, OrthDec.resS_symm_apply]
  simp only [OrthDec.resS_apply, actO_eq]
  rw [Matrix.map_add _ (map_add (infPart D))]
  simp only [Matrix.map_mul, hw, Matrix.zero_mul, Matrix.mul_zero, zero_add]

theorem half (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (χ χ' : (AE D)ˣ →* Circle) (om : Om A T) (hom : IsWeilDatumO ψ A T χ χ' om)
    (p : GA D A × GA D T) :
    IsThetaFunO ψ S T fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 := by
  obtain ⟨g, h⟩ := p
  have hstd := hom.std
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hslice := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hstd S A B T o).2.2.2
  have hsob := (GlobalTheory.T.weil_operator_orth_summand_slices_sobolev_bounded D ψ θ hθ S A B T o).1 χ χ' om hom (g, h)
  refine GlobalTheory.T.theta_of_heisenberg_intertwiner_bounded_at_zero D ψ hstd θ hθ S T S T (shiftA o T g h) (continuous_shiftA o T g h) (shiftA_fin o T g h)
    (shiftA_inf o T g h) (fun F x => om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1)
    ?_ ?_ ?_ f hf
  · have e : (fun F : WO S T → ℂ => om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T 0).2))) (o.resS T 0).1) =
        fun F => om (g, h) (fun u => F ((o.resS T).symm (u, 0))) 0 := by
      funext F
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    exact e ▸ hsob
  · intro F w hF
    funext x
    have hG := (hslice F hF).1 ((o.resS T x).2 + (o.resS T w).2)
    have hin : (fun u => heisO ψ S T (shiftA o T g h w) F ((o.resS T).symm (u, (o.resS T x).2))) =
        ψ (symplOH B T (o.resS T x).2 (o.resS T w).2) • heisO ψ A T (actO A T g⁻¹ h⁻¹ (o.resS T w).1)
          (fun u => F ((o.resS T).symm (u, (o.resS T x).2 + (o.resS T w).2))) := by
      funext u
      simp only [heisO, shiftA_apply, Pi.smul_apply, smul_eq_mul]
      rw [o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply]
      rw [← map_add (f := _), Prod.mk_add_mk, AddChar.map_add_eq_mul]
      ring
    show om (g, h) (fun u => heisO ψ S T (shiftA o T g h w) F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 = _
    rw [hin, map_smul, hom.om_heis g h _ _ hG, actO_shift]
    simp only [Pi.smul_apply, heisO, smul_eq_mul]
    rw [o.symplOH_resS, map_add (o.resS T) x w, AddChar.map_add_eq_mul]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  · intro F γ hF
    have hr : ratW T S γ ∈ ratL T S := ⟨γ, rfl⟩
    obtain ⟨ha, hb⟩ := (o.mem_ratL_resS T _).1 hr
    have hsl : (fun u => F ((o.resS T).symm (u, (o.resS T (ratW T S γ)).2))) =
        fun u => F ((o.resS T).symm (u, 0)) := by
      funext u
      have hb' : (o.resS T).symm (0, (o.resS T (ratW T S γ)).2) ∈ ratL T S := by
        refine (o.mem_ratL_resS T _).2 ?_
        simp only [AddEquiv.apply_symm_apply]
        exact ⟨zero_mem _, hb⟩
      obtain ⟨δ, hδ⟩ := hb'
      have hδ' : ratW T S δ = (o.resS T).symm (0, (o.resS T (ratW T S γ)).2) := hδ
      have e : (o.resS T).symm (u, (o.resS T (ratW T S γ)).2) = ratW T S δ + (o.resS T).symm (u, 0) := by
        rw [hδ', ← map_add (f := _), Prod.mk_add_mk, zero_add, add_zero]
      rw [e, hF.quasi δ, hδ', o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply, symplOH_zero_left', symplOH_zero_right', add_zero, neg_zero,
        AddChar.map_zero_eq_one, one_mul]
    show om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T (ratW T S γ)).2))) (o.resS T (ratW T S γ)).1 =
      om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T 0).2))) (o.resS T 0).1
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [hsl]
    obtain ⟨γa, hγa⟩ := ha
    have ea : (o.resS T (ratW T S γ)).1 = ratW T A γa + 0 := by rw [add_zero]; exact hγa.symm
    rw [ea, (hom.om_pres (g, h) _ ((hslice F hF).1 0)).quasi γa 0, symplOH_zero_right', neg_zero,
      AddChar.map_zero_eq_one, one_mul]

theorem resS_symm_swap {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (u : WO B T) (v : WO A T) :
    (o.symm.resS T).symm (u, v) = (o.resS T).symm (v, u) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply]; exact add_comm _ _

theorem weilSlice_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2 := by
  intro D ψ S A B T o f hf
  refine ⟨fun χ χ' om hom p => half D ψ S A B T o f hf χ χ' om hom p, fun χ χ' om hom p => ?_⟩
  have h2 := half D ψ S B A T o.symm f hf χ χ' om hom p
  have key : (fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2) =
      fun x => om p (fun u => f ((o.symm.resS T).symm (u, (o.symm.resS T x).2))) (o.symm.resS T x).1 := by
    funext x
    simp only [resS_symm_swap]
    rfl
  exact key ▸ h2

end GlobalTheory.WeilSlice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2 := by
  first | exact @GlobalTheory.WeilSlice.weilSlice_theta | exact GlobalTheory.WeilSlice.weilSlice_theta | (intros; apply GlobalTheory.WeilSlice.weilSlice_theta <;> assumption)
end
end
