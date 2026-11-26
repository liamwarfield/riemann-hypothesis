module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PetEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.locInt :
    UpperTheory.V.Cj.H.LocInt := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _
  refine ⟨fun F => ?_, fun C hC => ?_⟩
  · rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    exact (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact G Γ μ F K hK).2
  · have hfin := GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
    refine ⟨hfin.toFinset.card, fun g => ?_⟩
    by_cases hne : {γ : Γ | ↑γ * g ∈ C}.Nonempty
    · obtain ⟨γ0, hγ0⟩ := hne
      calc {γ : Γ | ↑γ * g ∈ C}.encard ≤ {δ : Γ | ↑δ ∈ C * C⁻¹}.encard := by
            apply Set.encard_le_encard_of_injOn (f := fun γ => γ * γ0⁻¹)
            · intro γ hγ
              refine ⟨↑γ * g, hγ, (↑γ0 * g)⁻¹, Set.inv_mem_inv.2 hγ0, ?_⟩
              simp [mul_assoc]
            · intro a _ b _ h
              simpa using h
        _ = hfin.toFinset.card := hfin.encard_eq_coe_toFinset_card
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private def stab (ψ : Sm E a) : Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) where
  carrier := {k | rt E a (finGL E a k) ψ = ψ}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_mul, map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

private theorem lev_lie (X : Lie E a) (ψ : Sm E a) (h : HasLev ψ) : HasLev (lie E a X ψ) := by
  have hle : stab ψ ≤ stab (lie E a X ψ) := fun k hk =>
    (LinearMap.congr_fun (lie_rt_fin X k) ψ).symm.trans (congrArg (lie E a X) hk)
  exact Subgroup.isOpen_mono hle h

private theorem lev_rt (g : GA E a) (ψ : Sm E a) (h : HasLev ψ) : HasLev (rt E a g ψ) := by
  obtain ⟨y, l, rfl⟩ : ∃ y l, infGL E a y * finGL E a l = g := ⟨_, _, infGL_mul_finGL g⟩
  have hc : Continuous fun k : GL (Fin a) (GlobalTheory.CuspRep.Af E) => l⁻¹ * k * l := by fun_prop
  have ho : IsOpen ((fun k : GL (Fin a) (GlobalTheory.CuspRep.Af E) => l⁻¹ * k * l) ⁻¹' (stab ψ : Set _)) :=
    IsOpen.preimage hc h
  refine Subgroup.isOpen_of_mem_nhds (stab (rt E a (infGL E a y * finGL E a l) ψ)) (g := 1)
    (mem_of_superset (ho.mem_nhds ?_) fun k hk => ?_)
  · simpa using (stab ψ).one_mem
  · have hk' : rt E a (finGL E a (l⁻¹ * k * l)) ψ = ψ := hk
    change rt E a (finGL E a k) (rt E a (infGL E a y * finGL E a l) ψ) = rt E a (infGL E a y * finGL E a l) ψ
    have e : finGL E a k * (infGL E a y * finGL E a l) = infGL E a y * finGL E a l * finGL E a (l⁻¹ * k * l) := by
      rw [← mul_assoc, ← infGL_comm, mul_assoc, mul_assoc (infGL E a y), ← map_mul, ← map_mul]
      congr 2
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']

private theorem supp_lie (X : Lie E a) (ψ : Sm E a) (h : HasCompactSupport ψ.1) :
    HasCompactSupport (lie E a X ψ).1 := by
  obtain ⟨c, c0, -, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  set_option synthInstance.maxHeartbeats 200000 in
    refine HasCompactSupport.intro h fun g hg => ?_
  have hd := GlobalTheory.CuspRep.hasDerivAt_curve ψ g c X c0 cder
  have hc : Continuous fun t : ℝ => g * infGL E a (c t) := continuous_const.mul ccont
  have ht : Tendsto (fun t : ℝ => g * infGL E a (c t)) (𝓝 0) (𝓝 g) := by
    set_option synthInstance.maxHeartbeats 200000 in
      simpa [c0] using hc.tendsto 0
  have hz : (fun t : ℝ => ψ.1 (g * infGL E a (c t))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) :=
    ht.eventually (notMem_tsupport_iff_eventuallyEq.1 hg)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)

private theorem supp_rt (g : GA E a) (ψ : Sm E a) (h : HasCompactSupport ψ.1) :
    HasCompactSupport (rt E a g ψ).1 :=
  h.comp_homeomorph (Homeomorph.mulRight g)

end

theorem UpperTheory.V.Cj.H.testOps :
    UpperTheory.V.Cj.H.TestOps := by
  intro E _ _ _ a ψ
  exact ⟨fun h => ⟨ContAut.continuous_of_isOpen_stab E a ψ h, fun X => lev_lie X ψ h, fun g => lev_rt g ψ h⟩,
    fun h => ⟨fun X => ⟨supp_lie X ψ h.1, lev_lie X ψ h.2⟩, fun g => ⟨supp_rt g ψ h.1, lev_rt g ψ h.2⟩⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConvolutionL2Class
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.convolution_L2_class :
    UpperTheory.V.Cj.H.ConvolutionL2Class := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψs F
  set f : G → ℂ := fun y => ψ y⁻¹ with hfdef
  have hfi : Integrable f μ :=
    (hψ.comp continuous_inv).integrable_of_hasCompactSupport
      (hψs.comp_homeomorph (Homeomorph.inv G))
  have hconv : cv ψ F = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F) := by
    funext x
    show ∫ y, GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x) ∂μ = ∫ y, f y * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) (x * y) ∂μ
    rw [← MeasureTheory.integral_mul_left_eq_self
      (fun y => GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x)) x]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hfdef, _root_.mul_inv_rev, inv_mul_cancel_right]
    exact mul_comm _ _
  obtain ⟨-, hae⟩ := GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR G Γ μ f hfi F
  rw [hconv]
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv Γ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F)) :=
    (GlobalTheory.AutomorphicL2Unitary.leftInv_lift _).convR f
  have hdesc : GlobalTheory.AutomorphicL2Unitary.descend Γ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F))
      =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ] ↑↑(GlobalTheory.AutomorphicL2Unitary.Rop Γ μ f F) := by
    refine GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.2 ?_
    filter_upwards [hae] with g hg
    have hl := congrFun hinv.lift_descend g
    simp only [GlobalTheory.AutomorphicL2Unitary.lift] at hg hl
    rw [hl, hg]
  have hm : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F)) :=
    ⟨hinv, (MeasureTheory.Lp.memLp _).ae_eq hdesc.symm⟩
  exact ⟨hm, GlobalTheory.AutomorphicL2Unitary.l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (hm.lift_toL2_ae_eq.trans hae.symm)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private def levFnSub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsLevelFn U Ξ φ}
  zero_mem' := ⟨fun _ _ => rfl, fun u _ => map_zero _, fun m _ => by simp⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ g => congrArg₂ (· + ·) (h.1 γ g) (h'.1 γ g),
    fun u hu => by rw [map_add (f := _), h.2.1 u hu, h'.2.1 u hu],
    fun m hm => by rw [map_add (f := _), h.2.2 m hm, h'.2.2 m hm, smul_add]⟩
  smul_mem' := fun c φ h => ⟨fun γ g => congrArg (c • ·) (h.1 γ g),
    fun u hu => by rw [map_smul, h.2.1 u hu],
    fun m hm => by rw [map_smul, h.2.2 m hm, smul_comm]⟩

private theorem cmp_rTensor {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : Module.End ℂ W) (i : Fin d)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor (Fin d → ℂ) m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

theorem UpperTheory.V.Cj.H.levLin :
    UpperTheory.V.Cj.H.LevLin := by
  intro E _ _ _ a U Ξ q
  have ap : ∀ (α β : Co Ξ q) (s t : ℂ) X, (s • α + t • β) X = s • α X + t • β X := fun _ _ _ _ _ => rfl
  refine ⟨fun α β s t hα hβ => ⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, fun α β s t => ?_,
    fun α hα X i => ?_, fun T α X i => ?_⟩
  · rw [ap, ap, hα.equiv k X, hβ.equiv k X, map_add (f := _), map_smul, map_smul]
  · rw [ap, hα.basic X i hi, hβ.basic X i hi, smul_zero, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hα.val X)) (Submodule.smul_mem _ _ (hβ.val X))
  · refine AlternatingMap.ext fun X => ?_
    have e : (s • dCo (smLie Ξ) α + t • dCo (smLie Ξ) β) X = s • dCo (smLie Ξ) α X + t • dCo (smLie Ξ) β X := rfl
    rw [e, dCo_apply, dCo_apply, dCo_apply]
    simp only [ap, map_add (f := _), map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · exact mem_tens.1 (span_le_tens (N := levFnSub U Ξ) (fun φ h => h) (hα.val X)) i
  · rw [app_apply, cmp_rTensor]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvCount
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped ENNReal in
private theorem sq_on_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : MeasurableSet S) (N : ℕ) (hN : ∀ x : G, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (F : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) :
    eLpNorm (GlobalTheory.AutomorphicL2Unitary.lift Γ F) 2 (μ.restrict S) ≤ N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
  have hmeasF : AEStronglyMeasurable (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) μ :=
    GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have key : ∫⁻ x, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S) ≤
      (N : ℝ≥0∞) * ∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
    rw [← lintegral_indicator hS, GlobalTheory.AutomorphicL2Unitary.lintegral_eq_lintegral_tsum (Γ := Γ) ((hmeasF.enorm.pow_const _).indicator hS),
      ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
    refine lintegral_mono (fun q => ?_)
    have hq : ∀ γ : Γ, S.indicator (fun x => ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ))
        ((γ : G) * Quotient.out q) = {γ : Γ | (γ : G) * Quotient.out q ∈ S}.indicator
          (fun _ => ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ)) γ := by
      intro γ
      have hl : GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) ((γ : G) * Quotient.out q) =
          (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q := by
        rw [GlobalTheory.AutomorphicL2Unitary.lift, GlobalTheory.AutomorphicL2Unitary.mk_mul]
        exact congrArg _ (Quotient.out_eq q)
      by_cases h : (γ : G) * Quotient.out q ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show γ ∈ {γ : Γ | (γ : G) * Quotient.out q ∈ S} from h), hl]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show γ ∉ {γ : Γ | (γ : G) * Quotient.out q ∈ S} from h)]
    rw [tsum_congr hq, ← tsum_subtype, ENNReal.tsum_set_const]
    gcongr
    have h1 := ENat.toENNReal_le.mpr (hN (Quotient.out q))
    simpa using h1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have hN2 : (N : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp
    · calc (N : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (N : ℝ≥0∞) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast h0) (by norm_num)
        _ = N := ENNReal.rpow_one _
  calc (∫⁻ x, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) x‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ^ (1 / 2 : ℝ)
      ≤ ((N : ℝ≥0∞) * ∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow key (by norm_num)
    _ = (N : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (∫⁻ q, ‖(F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) q‖ₑ ^ (2 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ _ := by gcongr
  all_goals first | exact Lp.aestronglyMeasurable F | exact hmeasF.restrict

theorem UpperTheory.V.Cj.H.cvCount :
    UpperTheory.V.Cj.H.CvCount := by
  open scoped Pointwise in
    intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψc
    obtain ⟨C0, hC0⟩ := hψ.bounded_above_of_compact_support hψc
    have hC : ∀ z, ‖ψ z‖ ≤ max C0 0 := fun z => (hC0 z).trans (le_max_left _ _)
    have hC' : 0 ≤ max C0 0 := le_max_right _ _
    have hMfin : μ (tsupport ψ)⁻¹ ≠ ⊤ := (hψc.isCompact.inv).measure_lt_top.ne
    refine ⟨max C0 0 * (μ (tsupport ψ)⁻¹).toReal ^ (1 / 2 : ℝ), by positivity, ?_⟩
    intro x N hN F
    have hS : MeasurableSet {y : G | ψ (y⁻¹ * x) ≠ 0} :=
      (isOpen_ne_fun (hψ.comp (continuous_inv.mul continuous_const)) continuous_const).measurableSet
    have hSK : μ {y : G | ψ (y⁻¹ * x) ≠ 0} ≤ μ (tsupport ψ)⁻¹ := by
      calc μ {y : G | ψ (y⁻¹ * x) ≠ 0} ≤ μ ((fun y => x⁻¹ * y) ⁻¹' (tsupport ψ)⁻¹) := by
            refine measure_mono (fun y hy => ?_)
            show (x⁻¹ * y)⁻¹ ∈ tsupport ψ
            rw [_root_.mul_inv_rev, inv_inv]
            exact subset_tsupport _ hy
        _ = μ (tsupport ψ)⁻¹ := measure_preimage_mul μ x⁻¹ _
    have hF := sq_on_le Γ μ hS N hN F
    have hmeas : AEStronglyMeasurable (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) μ :=
      GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
    have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
      (hmeas.restrict (s := {y : G | ψ (y⁻¹ * x) ≠ 0}))
    rw [show (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) by norm_num,
      Measure.restrict_apply_univ] at hH
    have hE : ‖cv ψ F x‖ₑ ≤ (N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal (max C0 0) := by
      calc ‖cv ψ F x‖ₑ ≤ ∫⁻ y, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y * ψ (y⁻¹ * x)‖ₑ ∂μ :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ y, {y : G | ψ (y⁻¹ * x) ≠ 0}.indicator
              (fun y => ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y‖ₑ) y * ENNReal.ofReal (max C0 0) ∂μ := by
            refine lintegral_mono (fun y => ?_)
            by_cases hy : y ∈ {y : G | ψ (y⁻¹ * x) ≠ 0}
            · rw [Set.indicator_of_mem hy, enorm_mul]
              gcongr
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (hC _)
            · have h0 : ψ (y⁻¹ * x) = 0 := not_not.mp hy
              rw [h0, mul_zero, enorm_zero]
              exact bot_le
        _ = (∫⁻ y in {y : G | ψ (y⁻¹ * x) ≠ 0}, ‖GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ) y‖ₑ ∂μ) *
              ENNReal.ofReal (max C0 0) := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hS]
        _ = eLpNorm (GlobalTheory.AutomorphicL2Unitary.lift Γ (F : GlobalTheory.AutomorphicL2Unitary.Quot Γ → ℂ)) 1 (μ.restrict {y : G | ψ (y⁻¹ * x) ≠ 0}) *
              ENNReal.ofReal (max C0 0) := by
            rw [eLpNorm_one_eq_lintegral_enorm]
            exact hmeas.restrict
        _ ≤ _ := by
            gcongr
            calc _ ≤ _ := hH
              _ ≤ _ := by gcongr
    have hRfin : (N * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal (max C0 0) ≠ ⊤ := by
      have h1 : eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ≠ ⊤ := Lp.eLpNorm_ne_top F
      have h2 : μ (tsupport ψ)⁻¹ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hMfin
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) h1) h2)
        ENNReal.ofReal_ne_top
    calc ‖cv ψ F x‖ = ‖cv ψ F x‖ₑ.toReal := (toReal_enorm _).symm
      _ ≤ _ := ENNReal.toReal_mono hRfin hE
      _ = max C0 0 * (μ (tsupport ψ)⁻¹).toReal ^ (1 / 2 : ℝ) * N * ‖F‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC',
          ENNReal.toReal_rpow, ENNReal.toReal_natCast, Lp.norm_def]
        ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PetInv
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem tw_rt (χ : HChar E) (g : GA E a) (φ : Sm E a) :
    mulChi a χ (rt E a g φ) = ((chiDet a χ g : ℂˣ) : ℂ)⁻¹ • rt E a g (mulChi a χ φ) := by
  rw [rt_mulChi, map_smul, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]

private theorem prod_fin (x : GL (Fin a) (Af E)) (φ : Sm E a) (l : List (Lie E a)) :
    (l.map (lie E a)).prod (act (.fin x) φ) = act (.fin x) ((l.map (lie E a)).prod φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, ih]
    exact LinearMap.congr_fun (lie_rt_fin X x) _

private theorem prod_sq {r : ℝ} {φ : Sm E a} (h : IsSq r φ) (l : List (Lie E a)) :
    IsSq r ((l.map (lie E a)).prod φ) := by
  induction l with
  | nil => exact h
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact (sqLie E a r).1 X _ ih

private theorem sqInt_fin (ha : 1 ≤ a) {r : ℝ} {φ : Sm E a} (h : IsSq r φ) (x : GL (Fin a) (Af E)) :
    IsSqIntMod (act (.fin x) φ) := by
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  obtain ⟨s, hs⟩ := hχ.1
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨h1, h2⟩ := sqMem E a ha μ r χ hχ φ (Submodule.subset_span h)
  have h3 := (sqUniq E a ha r χ hχ φ h.one (h.sq [])).1
  have hc : Continuous (mulChi a χ φ).1 := ContAut.continuous_of_isOpen_stab E a _ h1
  refine ⟨s, χ, hs, ?_⟩
  have e : (fun g => ((chiDet a χ g : ℂˣ) : ℂ) * (act (.fin x) φ).1 g) =
      ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ • fun g => (mulChi a χ φ).1 (g * finGL E a x) := by
    funext g
    exact (mul_comm _ _).trans (congrFun (congrArg Subtype.val (tw_rt χ (finGL E a x) φ)) g)
  rw [e]
  have h4 := h2.mul_right (finGL E a x)
  generalize ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ = c
  have hc' : Continuous fun g => (mulChi a χ φ).1 (g * finGL E a x) := hc.comp (continuous_id.mul continuous_const)
  refine (CuspidalL2GL.memL2_iff_isSqInt (μ := μ) (hc'.const_smul c) (fun γ g => ?_)
    (fun t g => ?_)).1 ⟨fun γ hγ g => congrArg (c • ·) (h4.1 γ hγ g), h4.2.const_smul c⟩
  · simp only [Pi.smul_apply, mul_assoc]
    rw [mulChi_apply, mulChi_apply, map_mul (chiDet a χ) (ratGL E a γ), chiDet_ratGL, one_mul, h.left]
  · simp only [Pi.smul_apply, mul_assoc, h3]

private theorem isSq_fin (ha : 1 ≤ a) {r : ℝ} (x : GL (Fin a) (Af E)) (φ : Sm E a) (h : IsSq r φ) :
    IsSq r (act (.fin x) φ) := by
  refine { left := ?_, level := ?_, one := ?_, sq := ?_ }
  · intro γ g
    change φ.1 (ratGL E a γ * g * finGL E a x) = φ.1 (g * finGL E a x)
    rw [mul_assoc, h.left]
  · have e : {k | act (.fin k) (act (.fin x) φ) = act (.fin x) φ} =
        (fun k => x⁻¹ * k * x) ⁻¹' {k | act (.fin k) φ = φ} := by
      ext k
      change finRep E a k (finRep E a x φ) = finRep E a x φ ↔ finRep E a (x⁻¹ * k * x) φ = φ
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      constructor
      · intro hk
        rw [hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro hk
        have := congrArg (finRep E a x) hk
        rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [e]
    exact h.level.preimage (by fun_prop)
  · have e : lie E a (oneL E a) (act (.fin x) φ) = act (.fin x) (lie E a (oneL E a) φ) :=
      LinearMap.congr_fun (lie_rt_fin _ x) φ
    rw [e, h.one, map_smul]
  · intro l
    rw [prod_fin]
    exact sqInt_fin ha (prod_sq h l) x

end

theorem UpperTheory.V.Cj.H.petInv :
    UpperTheory.V.Cj.H.PetInv := by
  intro E _ _ _ a ha r
  refine ⟨isSq_fin ha, ?_⟩
  obtain ⟨χ, hχ⟩ := twEx E a ha r
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hs := sqMem E a ha μ r χ hχ
  have hm : ∀ φ ∈ (sqSub E a r).map (mulChi a χ).toLinearMap, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ φ.1 := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact (hs φ hφ).2
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (sqSub E a r).subtype (Submodule.ker_subtype _)
  obtain ⟨T, hT⟩ : ∃ T : Sm E a →ₗ[ℂ] GlobalTheory.AutomorphicL2Unitary.L2 (latticeGL E a) μ, ∀ φ (hφ : φ ∈ sqSub E a r),
      T φ = (hs φ hφ).2.toL2 := by
    refine ⟨CuspidalL2GL.toL2ₗ μ _ hm ∘ₗ (mulChi a χ).toLinearMap.submoduleMap (sqSub E a r) ∘ₗ p, fun φ hφ => ?_⟩
    have e : p φ = ⟨φ, hφ⟩ := LinearMap.congr_fun hp ⟨φ, hφ⟩
    simp only [LinearMap.comp_apply, e]
    rfl
  refine ⟨((innerₛₗ ℂ) ∘ₛₗ T).compl₂ T, ⟨fun x y => ?_, fun x _ => ?_, fun x hx h0 => ?_⟩, fun x => ?_⟩
  · exact (inner_conj_symm (T y) (T x)).symm
  · exact inner_self_nonneg (𝕜 := ℂ) (x := T x)
  · have h1 : T x = 0 := inner_self_eq_zero.1 (show inner ℂ (T x) (T x) = 0 from h0)
    rw [hT x hx] at h1
    by_contra hne
    refine CuspidalL2GL.toL2_ne_zero (hs x hx).2 (ContAut.continuous_of_isOpen_stab E a _ (hs x hx).1) (fun e => hne ?_) h1
    exact (mulChi a χ).map_eq_zero_iff.1 (Subtype.ext e)
  · set c : ℂ := ((chiDet a χ (finGL E a x) : ℂˣ) : ℂ)⁻¹ with hc
    have hst : sqSub E a r ≤ (sqSub E a r).comap (act (.fin x)) :=
      Submodule.span_le.2 fun ψ hψ => Submodule.subset_span (isSq_fin ha x ψ hψ)
    have key : ∀ φ ∈ sqSub E a r,
        T (act (.fin x) φ) = c • GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T φ) := fun φ hφ => by
      rw [hT _ (hst hφ), hT φ hφ, GlobalTheory.AutomorphicL2Unitary.right_translate_toL2]
      have h4 := (hs φ hφ).2.mul_right (finGL E a x)
      have h5 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ (c • fun g => (mulChi a χ φ).1 (g * finGL E a x)) :=
        ⟨fun γ hγ g => congrArg (c • ·) (h4.1 γ hγ g), h4.2.const_smul c⟩
      refine Eq.trans ?_ (show h5.toL2 = c • h4.toL2 from MemLp.toLp_const_smul c h4.2)
      exact (GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.toL2_eq_iff_ae_eq _ h5).2
        (.of_forall fun g => congrFun (congrArg Subtype.val (tw_rt χ (finGL E a x) φ)) g)
    refine ⟨starRingEnd ℂ c * c, fun φ hφ ψ hψ => ?_⟩
    change inner ℂ (T (act (.fin x) φ)) (T (act (.fin x) ψ)) = _ * inner ℂ (T φ) (T ψ)
    have hi : inner ℂ (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T φ))
        (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x) (T ψ)) = inner ℂ (T φ) (T ψ) :=
      (LinearIsometry.mk (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ (finGL E a x)).toLinearMap
        (GlobalTheory.AutomorphicL2Unitary.norm_R _)).inner_map_map _ _
    rw [key φ hφ, key ψ hψ, inner_smul_left, inner_smul_right, hi, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ContrSingle
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

noncomputable section

namespace UpperTheory.V.Cj.H

private theorem multi_cont {H : Type} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [T2Space H] [FiniteDimensional ℝ H] {q : ℕ} (f : (Fin q → H) →ₘₗ[ℝ] ℂ) :
    Continuous f := by
  classical
  let b := Module.finBasis ℝ H
  have h : (f : (Fin q → H) → ℂ) = fun x => ∑ r : Fin q → Fin (Module.finrank ℝ H),
      (∏ i, b.coord (r i) (x i)) • f fun i => b (r i) := by
    funext x
    have e : x = fun i => ∑ j, b.coord j (x i) • b j := funext fun i => (b.sum_repr (x i)).symm
    conv_lhs => rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [f.map_sum]
    exact Finset.sum_congr rfl fun r _ => f.map_smul_univ _ _
  rw [h]
  refine continuous_finsetSum _ fun r _ => Continuous.fun_smul (continuous_finsetProd _ fun i _ => ?_) continuous_const
  exact (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)

private def contr {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} :
    (Fin d → ℂ) →ₗ[ℂ] S ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] S :=
  ∑ i, (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ).smulRight (Bor.cmp i)

private theorem contr_tmul {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} (v u : Fin d → ℂ) (φ : S) :
    contr v (φ ⊗ₜ[ℂ] u) = (v ⬝ᵥ u) • φ := by
  simp [contr, LinearMap.sum_apply, dotProduct, Finset.sum_smul, smul_smul]

private theorem contr_single {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} (i : Fin d) (m : S ⊗[ℂ] (Fin d → ℂ)) :
    contr (Pi.single i 1) m = Bor.cmp i m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ u => simp [contr_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem abs_type {K H S : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [T2Space H] [FiniteDimensional ℝ H] [AddCommGroup S] [Module ℂ S] [Module ℝ S] [IsScalarTower ℝ ℂ S]
    {d : ℕ} (q : ℕ) (ad : K →* (H →ₗ[ℝ] H)) (had : ∀ X, Continuous fun k => ad k X)
    (M : K →* Matrix (Fin d) (Fin d) ℂ) (hM : Continuous M) (π : Representation ℂ K S) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (ρ : Representation ℂ K W), GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ ω : (Fin q → H) →ₘₗ[ℝ] S ⊗[ℂ] (Fin d → ℂ),
        (∀ k X, ω (fun i => ad k (X i)) = TensorProduct.map (π k) (Matrix.toLin' (M k)) (ω X)) → ∀ X i,
      ∃ (T : W →ₗ[ℂ] S) (w : W), (∀ k v, T (ρ k v) = π k (T v)) ∧ T w = Bor.cmp i (ω X) := by
  classical
  let P := PiTensorProduct ℝ fun _ : Fin q => H
  let A : K → P →ₗ[ℝ] P := fun k => PiTensorProduct.map fun _ => ad k
  let B : K → (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := fun k => Matrix.toLin' (M k⁻¹)ᵀ
  let ρ : Representation ℂ K ((Fin d → ℂ) ⊗[ℝ] P) :=
    { toFun := fun k => TensorProduct.AlgebraTensorModule.map (B k) (A k)
      map_one' := by
        have h1 : A 1 = LinearMap.id := by
          simp only [A, map_one]; exact PiTensorProduct.map_one
        have h2 : B 1 = LinearMap.id := by simp [B]
        rw [h1, h2, TensorProduct.AlgebraTensorModule.map_id]; rfl
      map_mul' := fun k l => by
        have h1 : A (k * l) = A k ∘ₗ A l := by
          simp only [A, map_mul]; exact PiTensorProduct.map_mul _ _
        have h2 : B (k * l) = B k ∘ₗ B l := by simp [B, Matrix.toLin'_mul]
        rw [h1, h2, TensorProduct.AlgebraTensorModule.map_comp]; rfl }
  have hρ : ∀ k v (X : Fin q → H), ρ k (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X) =
      ((M k⁻¹)ᵀ *ᵥ v) ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ fun i => ad k (X i) := fun k v X => by
    change TensorProduct.AlgebraTensorModule.map (B k) (A k) _ = _
    rw [TensorProduct.AlgebraTensorModule.map_tmul]
    exact congrArg₂ _ rfl (PiTensorProduct.map_tprod _ _)
  have ind : ∀ (p : (Fin d → ℂ) ⊗[ℝ] P → Prop) (h0 : p 0) (ha : ∀ x y, p x → p y → p (x + y))
      (ht : ∀ v (X : Fin q → H), p (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X)) (w : (Fin d → ℂ) ⊗[ℝ] P), p w := by
    intro p h0 ha ht w
    induction w using TensorProduct.induction_on with
    | zero => exact h0
    | add x y hx hy => exact ha x y hx hy
    | tmul v t =>
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r X => rw [← TensorProduct.smul_tmul]; exact ht _ _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact ha _ _ hx hy
  refine ⟨(Fin d → ℂ) ⊗[ℝ] P, inferInstance, inferInstance, Module.Finite.of_restrictScalars_finite ℝ ℂ _, ρ,
    fun ℓ w => ?_, fun ω hω X i => ?_⟩
  · induction w using ind with
    | h0 => simpa using continuous_const
    | ha x y hx hy => simpa only [map_add (f := _)] using hx.fun_add hy
    | ht v X =>
      have e : (fun k => ℓ (ρ k (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X))) = fun k => ∑ j, ((M k⁻¹)ᵀ *ᵥ v) j *
          ((ℓ.restrictScalars ℝ ∘ₗ TensorProduct.mk ℝ (Fin d → ℂ) P (Pi.single j 1)).compMultilinearMap
            (PiTensorProduct.tprod ℝ)) fun i => ad k (X i) := by
        funext k
        rw [hρ]
        generalize (M k⁻¹)ᵀ *ᵥ v = u
        conv_lhs => rw [pi_eq_sum_univ' u]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [TensorProduct.sum_tmul, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← TensorProduct.smul_tmul', map_smul]
        rfl
      rw [e]
      refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ ?_
      · exact (continuous_apply j).comp ((hM.comp continuous_inv).matrix_transpose.matrix_mulVec continuous_const)
      · exact (multi_cont _).comp (continuous_pi fun i => had _)
  · let T : (Fin d → ℂ) ⊗[ℝ] P →ₗ[ℂ] S := TensorProduct.AlgebraTensorModule.lift
      { toFun := fun v => (contr v).restrictScalars ℝ ∘ₗ PiTensorProduct.lift ω
        map_add' := fun u v => by ext; simp
        map_smul' := fun c v => by ext; simp }
    have hT : ∀ v (Y : Fin q → H), T (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ Y) = contr v (ω Y) := fun v Y => by
      exact congrArg (contr v) (PiTensorProduct.lift.tprod (φ := ω) Y)
    refine ⟨T, Pi.single i 1 ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X, fun k w => ?_, by rw [hT, contr_single]⟩
    induction w using ind with
    | h0 => simp
    | ha x y hx hy => simp only [map_add (f := _), hx, hy]
    | ht v Y =>
      rw [hρ, hT, hT, hω]
      induction ω Y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul φ u =>
        rw [TensorProduct.map_tmul, contr_tmul, contr_tmul, map_smul, Matrix.toLin'_apply, Matrix.mulVec_transpose,
          ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

end UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.kType :
    UpperTheory.V.Cj.H.KType := by
  intro E _ _ _ a Ξ q
  let ad : Kinf E a →* (Herm E a →ₗ[ℝ] Herm E a) :=
    { toFun := fun k =>
        { toFun := adHerm k
          map_add' := fun X Y => Subtype.ext (by simp [adHerm, mul_add, add_mul])
          map_smul' := fun c X => Subtype.ext (by simp [adHerm]) }
      map_one' := LinearMap.ext fun X => Subtype.ext (by simp [adHerm])
      map_mul' := fun k l => LinearMap.ext fun X => Subtype.ext (by simp [adHerm, mul_assoc]) }
  have had : ∀ X, Continuous fun k => ad k X := fun X =>
    Continuous.subtype_mk ((continuous_subtype_val.mul continuous_const).mul continuous_subtype_val.star) _
  have hM : Continuous (Ξ.mat.comp (Unitary.toUnits : Kinf E a →* _)) := by
    refine continuous_matrix fun i j => continuous_iff_continuousAt.2 fun k => ?_
    have h := (differentiableAt_extGL (Ξ.reg i j) (x := toL (Unitary.toUnits k).val) (Unitary.toUnits k).isUnit).continuousAt
    have h2 : Continuous fun l : Kinf E a => (toL (Unitary.toUnits l).val : Lie E a) := continuous_subtype_val
    have h3 := ContinuousAt.comp (f := fun l : Kinf E a => (toL (Unitary.toUnits l).val : Lie E a)) h h2.continuousAt
    simp only [Function.comp_def, extGL_val] at h3
    exact h3
  obtain ⟨W, i1, i2, i3, ρ, h1, h2⟩ := abs_type q ad had _ hM (cptRep E a)
  exact ⟨W, i1, i2, i3, ρ, h1, fun ω hω => h2 ω.toMultilinearMap hω⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.RopComm
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.ropComm :
    UpperTheory.V.Cj.H.RopComm := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ T hT f hf F
  have hF := GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hf F
  have hTF := GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hf (T F)
  rw [hF.2, hTF.2]
  refine (T.integral_comp_comm hF.1).symm.trans ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show T (f g • (GlobalTheory.AutomorphicL2Unitary.R Γ μ g) F) = f g • (GlobalTheory.AutomorphicL2Unitary.R Γ μ g) (T F)
  rw [map_smul, hT g F]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.UnitCont
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem inf_cont (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

private theorem unit_cont (E : Type) [Field E] [NumberField E] (a : ℕ) {X : Type} [TopologicalSpace X]
    (u : X → GL (Fin a) (Cinf E)) (hu : Continuous fun x => (u x).val) : Continuous u := by
  refine Units.continuous_iff.2 ⟨hu, ?_⟩
  simp only [Matrix.coe_units_inv]
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨d, hd⟩ := (Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit
  refine ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt
  rw [← hd]
  exact NormedRing.inverse_continuousAt d

theorem UpperTheory.V.Cj.H.smDiv :
    UpperTheory.V.Cj.H.SmDiv := by
  intro E _ _ _ a φ u w
  refine ⟨fun g => ?_, fun Z hZ h0 hw g x hx => ?_⟩
  · refine ((φ.2 g).mul (u.2 g)).congr fun x hx => ?_
    have h : IsUnit (Matrix.of x) := hx
    simp only [chart, dif_pos h]
  · have h : IsUnit (Matrix.of x) := hx
    have e : ∀ y ∈ invSet E a, chart (fun g => φ.1 g / w.1 g) g y = chart φ.1 g y * (chart w.1 g y)⁻¹ := by
      intro y hy
      have h' : IsUnit (Matrix.of y) := hy
      simp only [chart, dif_pos h', div_eq_mul_inv]
    by_cases hz : g * infGL E a h.unit ∈ Z
    · have hne : chart w.1 g x ≠ 0 := by
        rw [chart, dif_pos h]
        exact hw _ hz
      exact ((φ.2 g x hx).mul ((w.2 g x hx).inv hne)).congr e (e x hx)
    · let v : invSet E a → GL (Fin a) (Cinf E) := fun y => (show IsUnit (Matrix.of y.1) from y.2).unit
      have hv : Continuous v := unit_cont E a v continuous_subtype_val
      have hc : Continuous fun y : invSet E a => g * infGL E a (v y) :=
        continuous_const.mul ((inf_cont E a).comp hv)
      have ho : IsOpen {y : invSet E a | g * infGL E a (v y) ∉ Z} := hZ.isOpen_compl.preimage hc
      have hn : ∀ᶠ y : invSet E a in 𝓝 ⟨x, hx⟩, g * infGL E a (v y) ∉ Z := ho.mem_nhds hz
      have hv : ∀ᶠ y in 𝓝[invSet E a] x, chart (fun g => φ.1 g / w.1 g) g y = 0 := by
        rw [nhdsWithin_eq_map_subtype_coe hx, eventually_map]
        filter_upwards [hn] with y hy
        have h' : IsUnit (Matrix.of y.1) := y.2
        rw [chart, dif_pos h', h0 _ hy, zero_div]
      exact (contDiffWithinAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hv (hv.self_of_nhdsWithin hx)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SmSepDer
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem sm_sepDer (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) :
    SepDer (smK Ξ) (smLie Ξ) := by
  intro k Z h0 hk m' hm
  have h1 : ∃ j, Bor.cmp j m' ≠ 0 := by
    by_contra h
    push Not at h
    apply hm
    rw [← sum_cmp m']
    simp [h]
  obtain ⟨j, hj⟩ := h1
  have h2 : (Bor.cmp j m').1 ≠ 0 := fun h => hj (Subtype.ext h)
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h2
  let l : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun m => (Bor.cmp j m).1 g
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hl : ∀ (φ : Sm E a) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1 g * v j := fun φ v => by
    change (Bor.cmp j (φ ⊗ₜ v)).1 g = _
    rw [cmp_tmul, mul_comm]
    rfl
  have hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1 := by simp only [h0, map_one]
  refine ⟨l, hg, fun m => ?_⟩
  induction m using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simpa only [map_add (f := _)] using hx.fun_add hy
  | tmul φ v =>
    have h3 := GlobalTheory.CuspRep.hasDerivAt_curve φ g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk
    have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)
    have h5 := h3.fun_mul h4
    simp only [h0, map_one, mul_one] at h5
    have h7 : smLie Ξ (toL Z) (φ ⊗ₜ v) = lie E a (toL Z) φ ⊗ₜ v + φ ⊗ₜ (Ξ.dmat (toL Z) *ᵥ v) := rfl
    simp only [smK, h7, TensorProduct.map_tmul, map_add (f := _), hl, Matrix.toLin'_apply]
    have h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j := congrFun (Matrix.one_mulVec v) j
    rw [h6] at h5
    exact h5

theorem UpperTheory.V.Cj.H.smAB :
    UpperTheory.V.Cj.H.SmAB := by
  intro E _ _ _ a Ξ
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun X Y => ?_, fun k X => ?_, fun k X => ?_,
    infAbs E a _ _ _ (sm_sepDer E a Ξ)⟩
  · simp only [smA_apply]
    rw [← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_sub]
    congr 1
    exact (lie_comm (toL X) (toL Y)).trans (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm
  · simp only [smB_apply]
    rw [← GlobalTheory.AlgInfChar.dmat_bracket, map_sub, LinearMap.lTensor_sub, Matrix.toLin'_mul, Matrix.toLin'_mul,
      LinearMap.lTensor_comp, LinearMap.lTensor_comp]
    rfl
  · rw [smA_apply, smB_apply]
    exact TensorProduct.ext' fun _ _ => rfl
  · refine TensorProduct.ext' fun φ v => ?_
    have h1 : act (.cpt k) (lie E a (toL X) φ) = lie E a (toL (k.1 * X * star k.1)) (act (.cpt k) φ) :=
      LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X) φ
    simp only [Module.End.mul_apply, smK, smA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]
  · refine TensorProduct.ext' fun φ v => ?_
    have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X) =
        Ξ.dmat (toL (k.1 * X * star k.1)) * Ξ.mat (Unitary.toUnits k) :=
      Ξ.mat_mul_dmat (Unitary.toUnits k) X
    simp only [Module.End.mul_apply, smK, smB_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ROpApply
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private noncomputable def rAlg (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)) :=
  (Module.End.lTensorAlgHom ℂ (Fin d → ℂ) V).comp
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

private noncomputable def rOp (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] (Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)))ᵐᵒᵖ where
  toFun N := MulOpposite.op (rAlg V d Nᵀ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.transpose_mul]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.transpose_add]
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

private theorem rOp_apply (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) (N : Matrix (Fin d) (Fin d) ℂ) :
    rOp V d N = MulOpposite.op (rAlg V d Nᵀ) := rfl

private theorem qdet_stab {M : Type} [AddCommGroup M] [Module ℂ M] (N : Submodule ℂ M) {n : ℕ}
    (X : Fin n → Fin n → Module.End ℂ M) (h : ∀ i j, ∀ m ∈ N, X i j m ∈ N) (u : ℂ) :
    ∀ m ∈ N, Formalism.REAL.qdet X u m ∈ N := by
  let S : Subalgebra ℂ (Module.End ℂ M) :=
    { carrier := {z | ∀ m ∈ N, z m ∈ N}
      mul_mem' := fun hx hy m hm => hx _ (hy m hm)
      add_mem' := fun hx hy m hm => N.add_mem (hx m hm) (hy m hm)
      algebraMap_mem' := fun c m hm => N.smul_mem c hm }
  let Z : Fin n → Fin n → S := fun i j => ⟨X i j, h i j⟩
  have e : ((Formalism.REAL.qdet Z u : S) : Module.End ℂ M) = Formalism.REAL.qdet X u := mapQ S.val Z u
  rw [← e]
  exact (Formalism.REAL.qdet Z u).2

theorem UpperTheory.V.Cj.H.capSm :
    UpperTheory.V.Cj.H.CapSm := by
  intro E _ _ _ a Ξ τ u
  have hE : ∀ i j : Fin a, Eop (a := a) τ i j = eL (N := Module.End ℂ (Sm E a)) (lie E a) τ i j := fun _ _ => rfl
  have hc : cap (a := a) τ u = Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) := rfl
  refine ⟨?_, fun m hm => ?_, fun X => ?_, fun N hN => ?_⟩
  · let f : Module.End ℂ (Sm E a) →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
      Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)
    have hf : ∀ X, smA Ξ X = f (lie E a X) := fun _ => rfl
    have e : eL (smA Ξ) τ = fun i j => f (Eop (a := a) τ i j) := by
      funext i j
      simp only [hE, eL, hf, map_smul, map_sub]
    rw [e, ← mapQ, ← hc]
    rfl
  · have hd := (dualIff E a Ξ τ m).1 hm
    have hB : ∀ X, smB Ξ X = rAlg (Sm E a) Ξ.d (Ξ.dmat X) := fun X => smB_apply Ξ X
    have h := (mapQ (rOp (Sm E a) Ξ.d) (GlobalTheory.WignerGL.dualE Ξ τ) (u + ((a : ℂ) - 1) / 2)).symm.trans
      (congrArg (rOp (Sm E a) Ξ.d) (hd.2 u))
    rw [map_smul, map_one] at h
    have e : ∀ i j, rOp (Sm E a) Ξ.d (GlobalTheory.WignerGL.dualE Ξ τ i j) = -MulOpposite.op (eL (smB Ξ) τ i j) := fun i j => by
      rw [dualE_eq, map_neg, rOp_apply, Matrix.transpose_transpose]
      simp only [eL, hB, map_smul, map_sub]
    simp only [e] at h
    rw [h, MulOpposite.unop_smul, MulOpposite.unop_one]
  · rw [← UpperTheory.V.Cm.uC_capC, ← UpperTheory.V.Cm.uC_ιC]
    exact Commute.map (Subalgebra.mem_center_iff.1 (UpperTheory.V.Cm.capC_mem_center τ u) _) (UpperTheory.V.Cm.uC E a)
  · rw [hc]
    refine qdet_stab N _ (fun i j φ hφ => ?_) _
    rw [hE]
    exact N.smul_mem _ (N.sub_mem (hN _ φ hφ) (N.smul_mem _ (hN _ φ hφ)))
end
