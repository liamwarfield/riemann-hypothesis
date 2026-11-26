module

public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunction
public import Development.WeilBound.CoreStatements.TorusUniformisation.SiegelCompactSupport.ExistsRouteDatumTranslationCombinationGoodPlace
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationThetaEquivariance
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaHeisenbergTranslatesSeparate

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ActEEqOfConjRelated
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SvN

open Matrix
open scoped PositivityTheory.Member.ZakTransform
open PositivityTheory.Member.ZakTransform (schr_tens lift lift_tens lift_schr lift_adm lift_lift lift_one lift_mem psv psv_apply evP offP
  offP_eq evalEmbedding_smul evalPoints_add Indep indep_pure ep ep_mul ep_ep ev_ep at_iff schr_zero schr_mem_SB cont_at spM spM_fst spM_snd
  spM_off mat_ext coB ev_symp map_smul_piW map_cA_piW incM_piW ev_dot stdF stdF_mem sub sub_mem hasSig_det schur
  exists_bump rest_zero tens_at pure_update pure_mem good_std Good)
open PositivityTheory.Member.ZakTransform.Z (psi_re re trace_emb)
open GlobalTheory.EmbChart (atPlace evFin_atPlace)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM UA Spc Model Rep mat UAt At Rest Acts tens piW)

theorem isCharAF_of_isStd {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : IsCharAF F ψ := by
  obtain ⟨K, hK, hx⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := F)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn h.1.continuousOn
  have bd : ∀ x, ‖ψ x‖ ≤ C := fun x => by
    obtain ⟨a, ha⟩ := hx x
    have e : ψ x = ψ (x - algebraMap F _ a) := by
      have : x = (x - algebraMap F _ a) + algebraMap F _ a := by ring
      conv_lhs => rw [this, AddChar.map_add_eq_mul, h.2.1 a, mul_one]
    rw [e]
    exact hC _ ha
  have le1 : ∀ x, ‖ψ x‖ ≤ 1 := fun x => by
    by_contra hlt
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (not_le.1 hlt)
    have := bd (m • x)
    rw [AddChar.map_nsmul_eq_pow, norm_pow] at this
    linarith
  have hn : ∀ x, ‖ψ x‖ = 1 := fun x => by
    have e : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by
      rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
    nlinarith [le1 x, le1 (-x), norm_nonneg (ψ x), norm_nonneg (ψ (-x))]
  refine ⟨h.1, hn, h.2.1, ?_⟩
  have hN : ((Module.finrank ℚ F : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have tr1 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) 1 = (Module.finrank ℚ F : ℝ) := by
    have := trace_emb (F := F) 1
    have e1 : Algebra.trace ℚ F 1 = (Module.finrank ℚ F : ℚ) := by
      have := Algebra.trace_algebraMap (S := F) (1 : ℚ)
      simpa using this
    rw [map_one, e1] at this
    simpa using this
  refine ⟨re F (((2 * (Module.finrank ℚ F : ℝ))⁻¹ : ℝ) • (1 : mixedEmbedding.mixedSpace F)), ?_⟩
  rw [psi_re h, map_smul, tr1, smul_eq_mul]
  have : ((2 * (Module.finrank ℚ F : ℝ))⁻¹ * (Module.finrank ℚ F : ℝ)) = (2⁻¹ : ℝ) := by
    field_simp
  rw [this]
  push_cast
  have e : -(2 * (Real.pi : ℂ) * Complex.I) * 2⁻¹ = -(Real.pi * Complex.I) := by ring
  rw [e, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

section Inverse

end Inverse

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ}

variable {I : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
  {J : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ)}

end Local

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem indep_of {κ : Type} [Fintype κ] {r : (κ → AF F) → ℂ}
    (h : ∀ x z, At (evFin F v) z → r (x + z) = r x) : Indep v r := fun x t =>
  h x _ ((at_iff _).2 (funext fun i => by
    show ep v * atPlace v (t i) = _
    rw [ep_mul, evFin_atPlace]))

end Split

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

end Main

end GlobalTheory.CompanionTheory.Ar.SvN
end
end

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open PositivityTheory.Member.ZakTransform GlobalTheory.CompanionTheory.Ar.SvN GlobalTheory.EmbChart

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : Pl F}

theorem schr_inst (ψ : AddChar (Fv F v) ℂ) :
    @schr _ _ (invTwo v) ψ κ _ = @schr _ _ (invTwoV (v := v)) ψ κ _ := by
  rw [Subsingleton.elim (invTwo v) invTwoV]

theorem ad_heis (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (hw : At (evFin F v) w) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (schr ψ w) φ (@schr _ _ (invTwo v) (psiV ψ v) κ _ (locW v w) φ) := by
  intro r hr
  rw [schr_inst, schr_tens ψ _ _ (indep_of hr.1), offP_eq, sub_smul, (at_iff _).1 hw, one_smul, sub_self, schr_zero]
  rfl

theorem ad_rest (r : (κ → AF F) → ℂ) (φ₀ : (κ → Fv F v) → ℂ) (hne : φ₀ ≠ 0) (hr : Rest (evFin F v) φ₀ r)
    (φ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v)) : Rest (evFin F v) φ r := by
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  let S : Module.End ℂ ((κ → Fv F v) → ℂ) := (LinearMap.proj y : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ).smulRight ((φ₀ y)⁻¹ • φ)
  have h := lift_mem (v := v) (S := S) (fun θ _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hφ)) hr.2
  rw [lift_tens _ _ (indep_of hr.1)] at h
  have e : S φ₀ = φ := by
    change φ₀ y • (φ₀ y)⁻¹ • φ = φ
    rw [smul_smul, mul_inv_cancel₀ hy, one_smul]
  exact ⟨hr.1, e ▸ h⟩

theorem ad_act (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (s : (κ → AF F) × (κ → AF F) → (κ → AF F) × (κ → AF F))
    (L L' : Module.End ℂ ((κ → Fv F v) → ℂ)) (sv : (κ → Fv F v) × (κ → Fv F v) → (κ → Fv F v) × (κ → Fv F v))
    (h1 : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (h2 : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (h3 : ∀ w, ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ (s w) (T Φ))
    (h4 : ∀ φ ∈ SB (κ → Fv F v), L φ ∈ SB (κ → Fv F v) ∧ L' φ ∈ SB (κ → Fv F v) ∧ L' (L φ) = φ ∧ L (L' φ) = φ)
    (h5 : ∀ w, ∀ φ ∈ SB (κ → Fv F v), L (@schr _ _ (invTwo v) (psiV ψ v) κ _ w φ) =
      @schr _ _ (invTwo v) (psiV ψ v) κ _ (sv w) (L φ))
    (h6 : ∀ w, locW v (s w) = sv (locW v w) ∧ At (evFin F v) (s w - w)) :
    ∃ c : ℂ, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ (c • L φ) := by
  have hA := isCharAF_of_isStd hψ
  have hc : Continuous (psv v ψ) := hA.1.comp cont_at
  rw [schr_inst] at h5
  have hL' : ∀ φ ∈ SB (κ → Fv F v), L' φ ∈ SB (κ → Fv F v) := fun φ h => (h4 φ h).2.1
  obtain ⟨x₀, hx₀⟩ := hA.2.2.2
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.AdelicSchur.schur F κ ψ hA.1 (fun e => hx₀ (by rw [e]; rfl)) hA.2.2.1 (lift v L' * T)
    (fun Φ hΦ => lift_mem hL' (h1 Φ hΦ)) (fun l hl => h2 _ (lift_adm hL' l hl)) fun w Φ hΦ => by
      rw [Module.End.mul_apply, Module.End.mul_apply, h3 w Φ hΦ]
      refine lift_schr ψ ?_ (fun φ hφ => ?_) (h1 Φ hΦ)
      · rw [offP_eq, offP_eq, ← sub_eq_zero, ← smul_sub, sub_smul, one_smul, (at_iff _).1 (h6 w).2, sub_self]
      · have e := h5 (evP v w) _ (hL' φ hφ)
        rw [(h4 φ hφ).2.2.2] at e
        have e2 : evP v (s w) = sv (evP v w) := (h6 w).1
        rw [e2]
        exact (congrArg L' e).symm.trans (h4 _ (schr_mem_SB hc _ (hL' φ hφ))).2.2.1
  refine ⟨a, fun φ hφ r hr => ?_⟩
  have e := congrArg (lift v L) (ha _ hr.2)
  rw [Module.End.mul_apply, lift_lift (S'' := 1) hL' (fun θ h => (h4 θ h).2.2.2) (h1 _ hr.2), lift_one, map_smul,
    lift_tens _ _ (indep_of hr.1)] at e
  rw [e]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem indep_at {r : (κ → AF F) → ℂ} (h : Indep v r) (x z : κ → AF F) (hz : At (evFin F v) z) : r (x + z) = r x := by
  have e : z = fun i => atPlace v (evFin F v (z i)) := funext fun i => by
    rw [← ep_mul]; exact (congrFun ((at_iff z).1 hz) i).symm
  rw [e]; exact h x _

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

open GlobalTheory.DiagForm Classical in
theorem lDiag_box_ne : ∃ f : SInf F κ, lDiag F κ (boxFun (pure f (stdF κ)) (pure f (stdF κ))) ≠ 0 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (b x : ℂ) := b.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  let f : SInf F κ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨f, ?_⟩
  have hm := pure_mem f (good_std (F := F) (κ := κ))
  have hg := pf_mem (good_std (F := F) (κ := κ))
  set g := pf (stdF (F := F) κ) with hgd
  have g01 : ∀ y, g y = 0 ∨ g y = 1 := fun y => by
    obtain ⟨S, hS⟩ := exists_fin (good_std (F := F) (κ := κ)).2 y
    rw [hgd, pf_eq_prod S y hS]
    refine Finset.prod_induction _ (fun z : ℂ => z = 0 ∨ z = 1) ?_ (Or.inr rfl) fun u _ => ?_
    · rintro a c (rfl | rfl) (rfl | rfl) <;> simp
    · simp only [stdF, Set.indicator_apply]
      split_ifs <;> simp
  have g0 : g 0 = 1 := by
    rw [hgd, pf, finprod_eq_one_of_forall_eq_one]
    intro u
    simp [stdF, Set.indicator_apply]
  have e : resD F κ (boxFun (pure f (stdF κ)) (pure f (stdF κ))) =
      fun p => (((b (eI F κ p.1)) ^ 2 : ℝ) : ℂ) * ((‖g p.2‖ : ℝ) : ℂ) := funext fun p => by
    have e1 : pure f (stdF κ) (glue p) = (b (eI F κ p.1) : ℂ) * g p.2 := by
      change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _)) * g p.2 = _
      simp only [RingEquiv.apply_symm_apply]
      rfl
    change pure f (stdF κ) (glue p) * pure f (stdF κ) (glue p) = _
    rw [e1]
    rcases g01 p.2 with h | h <;> simp [h, sq]
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD (GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hm _ hm)), e, mu,
    integral_prod_mul (fun u => (((b (eI F κ u)) ^ 2 : ℝ) : ℂ)) (fun y => ((‖g y‖ : ℝ) : ℂ)), integral_complex_ofReal,
    integral_complex_ofReal]
  refine mul_ne_zero (Complex.ofReal_ne_zero.2 (ne_of_gt ?_)) (Complex.ofReal_ne_zero.2 (ne_of_gt ?_))
  · refine ((b.continuous.comp (eI F κ).continuous).pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      ?_ (fun u => sq_nonneg _) ?_
    · exact (b.hasCompactSupport.comp_homeomorph (eI F κ).toHomeomorph).comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    · simp only [Function.comp_apply, map_zero]
      rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
      simp
  · exact hg.1.continuous.norm.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) hg.2.norm
      (fun _ => norm_nonneg _) (by simp [g0])

open Classical in
theorem adjoint_statement : AdSt := by
  refine {
    psi := ?_
    Heisenberg₂ := fun F _ _ κ _ ψ v w hw φ => ad_heis ψ w hw φ
    rest := fun F _ _ κ _ v r φ₀ _ hne hr φ hφ => ad_rest r φ₀ hne hr φ hφ
    act := fun F _ _ κ _ ψ hψ v T s L L' sv => ad_act ψ hψ T s L L' sv
    diag := ?_ }
  · intro F _ _ ψ h
    have hA := isCharAF_of_isStd h
    obtain ⟨x₀, hx₀⟩ := hA.2.2.2
    refine ⟨fun e => hx₀ (by rw [e]; rfl), fun v => ⟨hA.1.comp cont_at, fun e => ?_⟩⟩
    obtain ⟨y, hy⟩ := ((GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hA).1 v).2
    exact hy (DFunLike.congr_fun e y)
  · intro F _ _ κ _ ψ v
    obtain ⟨f, hf⟩ := lDiag_box_ne (F := F) (κ := κ)
    have hi := indep_pure (v := v) f (stdF (F := F) κ)
    have e : tens (evFin F v) (stdF κ v) (pure f (Function.update (stdF κ) v 1)) = pure f (stdF κ) := by
      rw [← pure_update f (good_std (F := F) (κ := κ)).2, Function.update_eq_self]
    have hm := pure_mem f (good_std (F := F) (κ := κ))
    refine ⟨_, GlobalTheory.DiagForm.lDiag_adm, fun x y Φ hΦ => GlobalTheory.DiagForm.lDiag_schr ψ x y hΦ, stdF κ v, stdF_mem v,
      pure f (Function.update (stdF κ) v 1), ⟨indep_at hi, e ▸ hm⟩, ⟨fun x z hz => ?_, ?_⟩, e ▸ hf⟩
    · have h1 := indep_at hi (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _
      have h2 := indep_at hi (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _
      exact congrArg₂ (· * ·) h1 h2
    · have := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hm _ hm
      rw [← e] at this
      convert this using 1
      funext x
      exact mul_mul_mul_comm _ _ _ _

end PositivityTheory.KCo
end
end

section -- merged from Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictSec
noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.Member.ZakTransform MeasureTheory Topology
open GlobalTheory.EmbChart (tensAt compFin_tensAt tensAt_mul_right tensAt_tmul)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem modu_eq (u : (AF F)ˣ) : ((distribHaarChar (AF F) u : NNReal) : ℝ) = GroundTheory.Global.IdeleGroup.ideleModule F u := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := inferInstance
  have : (GroundTheory.Global.adeleMeasure F).Regular := by
    obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (AdeleRing (𝓞 F) F)))
    exact Measure.regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty K.isCompact.measure_lt_top.ne
  have h0 := (GroundTheory.Global.IdeleGroup.ideleModule F u).2
  have key : distribHaarChar (AdeleRing (𝓞 F) F) u = NNReal.mk _ h0.le := by
    refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := GroundTheory.Global.adeleMeasure F)
      (s := GroundTheory.Global.fundamentalSet F) ?_ ?_ ?_
    · rw [GroundTheory.Global.adeleMeasure_fundamentalSet]; exact one_ne_zero
    · rw [GroundTheory.Global.adeleMeasure_fundamentalSet]; exact ENNReal.one_ne_top
    · rw [← ENNReal.ofReal_eq_coe_nnreal h0.le]
      exact GroundTheory.Global.adeleMeasure_smul (K := F) u (GroundTheory.Global.fundamentalSet F)
  exact congrArg NNReal.toReal key

theorem modu_single (u : (AF F)ˣ) (x : (Fv F v)ˣ) (h : (u : AF F) = 1 - sgl v 1 + sgl v x) :
    ((distribHaarChar (AF F) u : NNReal) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) x := by
  rw [modu_eq, GroundTheory.Global.IdeleGroup.ideleModule_apply]
  have h1 : ∀ w, (u : AF F).1 w = 1 := fun w => by
    rw [h]
    change (1 : Ainf F) w - (0 : Ainf F) w + (0 : Ainf F) w = 1
    rw [sub_add_cancel]
    rfl
  have h2 : ∀ w, (u : AF F).2 w = 1 - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v 1) + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v x) :=
    fun w => by rw [h]; rfl
  have h3 : GroundTheory.Global.IdeleGroup.infiniteModule u = 1 := Finset.prod_eq_one fun w _ => by
    change ‖(u : AF F).1 w‖ ^ _ = 1
    rw [h1, norm_one, one_pow]
  have h4 : GroundTheory.Global.IdeleGroup.finiteModule u = ‖(x : Fv F v)‖ := by
    change ∏ᶠ w, ‖(u : AF F).2 w‖ = _
    rw [finprod_eq_single _ v fun w hw => by rw [h2, evalV_singleFin_ne hw, evalV_singleFin_ne hw, sub_add_cancel, norm_one],
      h2, evalV_singleFin_self, evalV_singleFin_self, sub_self, zero_add]
  rw [h3, h4, one_mul, GlobalTheory.SplitWeil.nabs]
  have := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v (x : Fv F v) x.ne_zero
  rw [Units.mk0_val] at this
  exact (congrArg NNReal.toReal this).symm

theorem off_of_at {z : AE F E} (h : At (evFin F v) (z - 1)) : (1 - ep v) • z = (1 - ep v) • (1 : AE F E) := by
  have := (at_iff _).1 h
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, this, sub_self]

theorem norm_eq (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {z : AE F E} {x : Fv F v} (hz : At (evFin F v) (z - 1))
    (h1 : piW t z = x) (h2 : piW (t.comp σ) z = 1) : Algebra.norm (AF F) z = 1 - sgl v 1 + sgl v x := by
  have hi : Function.Injective (algebraMap (AF F) (AE F E)) := Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  apply hi
  rw [GlobalTheory.Doubling.algebraMap_norm_eq h]
  change z * cA σ z = _
  have e : ∀ a : AF F, algebraMap (AF F) (AE F E) a = a • (1 : AE F E) := fun a => Algebra.algebraMap_eq_smul_one a
  have es : ∀ a, sgl v a = ep v * sgl v a := fun a => by
    rw [ep_mul]
    exact congrArg (sgl v) (evalV_singleFin_self v a).symm
  have ev : ∀ a, evFin F v (sgl v a) = a := evalV_singleFin_self v
  have o := off_of_at hz
  refine AE_ext h t ?_ ?_ ?_
  · rw [← smul_mul_assoc, o, smul_mul_assoc, one_mul, ← map_smul, o, map_smul, map_one, e, smul_smul]
    congr 1
    change _ = (1 - ep v) * (1 - ep v + sgl v x)
    rw [es x]
    linear_combination (1 - sgl v x) * (-ep_ep (v := v))
  · rw [map_mul, piW_cA, h1, h2, e, piW_smul, map_add (f := _), map_sub, ev, ev, map_one, map_one]
    ring
  · rw [map_mul, piW_cA, comp_conj_conj h, h1, h2, e, piW_smul, map_add (f := _), map_sub, ev, ev, map_one, map_one]
    ring

theorem eq_locIdele (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {z : (AE F E)ˣ} {x : (Fv F v)ˣ} (hz : At (evFin F v) ((z : AE F E) - 1))
    (h1 : piW t z = x) (h2 : piW (t.comp σ) z = 1) :
    z = locIdele F (splitPrime t) (Units.map (complMap (splitPrime_under t)).toMonoidHom x) := by
  classical
  let y : (Fv F v ⊗[F] E)ˣ := Units.map (compFin F E v).toMonoidHom z
  have e1 : z = GlobalTheory.Doubling.ideleAt F E v y := Units.ext (by
    change (z : AE F E) = 1 - tensAt E v 1 + tensAt E v (compFin F E v z)
    have o := off_of_at hz
    rw [← ep_smul, ← map_one (compFin F E v), ← ep_smul]
    rw [sub_smul, sub_smul, one_smul, one_smul] at o
    rw [← o, sub_add_cancel])
  rw [e1, ideleAt_eq_prod_locIdele]
  have hm : splitPrime t ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset :=
    (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.2 (splitPrime_under t)
  rw [Finset.prod_eq_single_of_mem ⟨splitPrime t, hm⟩ (Finset.mem_attach _ _)]
  · congr 1
    exact Units.ext ((ConjPlace.toCompl_eq h _ rfl _).trans (congrArg _ h1))
  · rintro ⟨w, hw⟩ - hb
    have hne : w ≠ splitPrime t := fun e => hb (Subtype.ext e)
    have hw' := (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 hw
    obtain ⟨ρ, hρ, -⟩ := existsUnique_splitPrime_eq h hne hw' (splitPrime_under t)
    obtain rfl : ρ = t.comp σ := (eq_or_eq_comp_conj h t ρ).resolve_left fun k => hne (hρ.symm.trans (k ▸ rfl))
    rw [← map_one (locIdele F w)]
    congr 1
    exact Units.ext ((ConjPlace.toCompl_eq h _ hρ _).trans ((congrArg _ h2).trans (map_one _)))

theorem usm_chrW (t : E →ₐ[F] Fv F v) {χ : Chr F E} (hχ : Continuous χ) : USm (chrW χ t) := by
  let μ : (Fv F v)ˣ →* Circle := (χ.comp (locIdele F (splitPrime t))).comp (Units.map (complMap (splitPrime_under t)).toMonoidHom)
  have hμ : Continuous μ := (hχ.comp (continuous_locIdele _)).comp
    (Continuous.units_map _ (SplitChart.continuous_complMap (splitPrime_under t)))
  refine ⟨fun x => Circle.norm_coe (μ x), Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_⟩
  filter_upwards [eventually_char_eq_one μ hμ] with x hx
  change Circle.toUnits (μ x) = 1
  rw [hx.1, map_one]

theorem section_statement : SecSt := by
  intro F E _ _ _ _ _ σ h v t
  refine ⟨⟨fun x => tensAt E v ((splitAlgEquiv h t).symm x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun χ hχ => usm_chrW t hχ.1⟩
  · intro x
    rw [at_iff, ep_smul, compFin_tensAt]
  · intro x
    change splitProj t (compFin F E v (tensAt E v _)) = _
    rw [compFin_tensAt, splitProj_symm]
  · intro x
    change splitProj (t.comp σ) (compFin F E v (tensAt E v _)) = _
    rw [compFin_tensAt, splitProj_comp_symm]
  · intro z hz h1 h2
    refine AE_ext h t ?_ (h1.trans (map_zero _).symm) (h2.trans (map_zero _).symm)
    rw [sub_smul, one_smul, (at_iff _).1 hz, sub_self, smul_zero]
  · intro z
    exact ⟨piW_cA t z, by rw [piW_cA, comp_conj_conj h]⟩
  · intro z hz u hu
    rw [← map_smul, hz u hu, map_zero]
  · exact fun a z => ⟨piW_smul _ a z, piW_smul _ a z⟩
  · exact fun x => ⟨piW_inc _ x, piW_inc _ x⟩
  · intro z hz
    rw [← ev_trace h t, ← (at_iff _).1 hz, map_smul, smul_eq_mul, ep_mul]
    exact congrArg (sgl v) (evalV_singleFin_self v _).symm
  · intro z x hz h1 h2
    refine ⟨fun χ => ?_, modu_single _ x (norm_eq h t hz h1 h2)⟩
    rw [eq_locIdele h t hz h1 h2]
    rfl

end PositivityTheory.KCo
end
end
