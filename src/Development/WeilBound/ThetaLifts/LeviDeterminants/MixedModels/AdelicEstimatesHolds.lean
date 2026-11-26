module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PureSt
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSplit
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PsiUnrOfNotLe

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MCGlue
noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo
  GlobalTheory.CompanionTheory.Ar.RT.Move

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

abbrev stdL (F : Type) [Field F] [NumberField F] (κ : Type) (v : Pl F) : (κ → Fv F v) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def Dat (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : Type :=
  {p : SInf F κ × ∀ v : Pl F, (κ → Fv F v) → ℂ // ∀ᶠ v in cofinite, p.2 v = stdL F κ v}

theorem rel_inf (ei : SInf F κ →ₗ[ℂ] SInf F κ) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → SInf F κ)
    (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ) (h : ∑ j ∈ s, c j • pure (f j) (φ j) = 0) :
    ∑ j ∈ s, c j • pure (ei (f j)) (φ j) = 0 := by
  funext x
  have h1 : ∑ j ∈ s, (c j * ∏ᶠ v, φ j v fun i => evFin F v (x i)) • f j = 0 := by
    refine DFunLike.ext _ _ fun y => ?_
    let z : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), (x i).2)
    have := congrFun h z
    have e : (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), (x i).2) : AF F)) = y :=
      funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
    rw [sum_apply, zero_apply]
    refine Eq.trans ?_ this
    refine Eq.trans ?_ (Finset.sum_apply z s fun j => c j • pure (f j) (φ j)).symm
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_apply, smul_eq_mul, mul_assoc, mul_comm _ (f j y)]
    exact congrArg (fun z => c j * (f j z * ∏ᶠ v, φ j v fun i => evFin F v (x i))) e.symm
  have h2 := DFunLike.congr_fun (congrArg ei h1) fun i => evI F (x i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, sum_apply, zero_apply] at h2
  rw [Finset.sum_apply, Pi.zero_apply, ← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc,
    mul_comm (ei (f j) _)]

theorem rel_fin (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (hev : ∀ᶠ v in cofinite, ev v (stdL F κ v) = stdL F κ v)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → SInf F κ) (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hφ : ∀ j, ∀ᶠ v in cofinite, φ j v = stdL F κ v) (h : ∑ j ∈ s, c j • pure (f j) (φ j) = 0) :
    ∑ j ∈ s, c j • pure (f j) (fun v => ev v (φ j v)) = 0 := by
  classical
  have key : ∀ T : Finset (Pl F), ∑ j ∈ s, c j • pure (f j) (fun v => if v ∈ T then ev v (φ j v) else φ j v) = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using h
    | insert v T hv ih =>
      have h1 := congrArg (opL v (ev v)) ih
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h2 : ∀ᶠ w in cofinite, (fun w => if w ∈ T then ev w (φ j w) else φ j w) w = stdL F κ w := by
        filter_upwards [hφ j, T.eventually_cofinite_notMem] with w e1 e2
        simp only [ite_eq_right e2, e1]
      have hop (g : SInf F κ) {θ : ∀ w : Pl F, (κ → Fv F w) → ℂ}
          (hθ : ∀ᶠ w in cofinite, θ w = stdL F κ w) :
          opL v (ev v) (pure g θ) = pure g (Function.update θ v (ev v (θ v))) := by
        let r := pure g (Function.update θ v 1)
        have hr (x : κ → AF F) (y : κ → Fv F v) : r (repl v x y) = r x := by
          unfold r GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
          congr 1
          refine finprod_congr fun w => ?_
          by_cases e : w = v
          · subst w
            simp
          · rw [Function.update_of_ne e]
            congr 1
            funext i
            change evalV F w ((x i).2 - singleFin v _ + singleFin v _) = _
            rw [map_add (f := _), map_sub, evalV_singleFin_ne e, evalV_singleFin_ne e,
              sub_zero, add_zero]
            rfl
        have hu (η : (κ → Fv F v) → ℂ) :
            pure g (Function.update θ v η) = tens (evFin F v) η r := by
          funext x
          have hθ₁ : ∀ᶠ w in cofinite, Function.update θ v 1 w = stdL F κ w := by
            filter_upwards [hθ, eventually_cofinite_ne v] with w hw e
            rw [Function.update_of_ne e, hw]
          have hsupport := finite_mulSupport (vac := stdL F κ)
            (Eventually.of_forall fun _ => rfl) hθ₁ x
          let t (w : Pl F) := if w = v then η (fun i => evFin F v (x i)) else 1
          have ht : (Function.mulSupport t).Finite :=
            (Set.finite_singleton v).subset fun w hw => by
              by_contra e
              exact hw (ite_eq_right e)
          have hprod (w : Pl F) :
              Function.update θ v η w (fun i => evFin F w (x i)) =
                t w * Function.update θ v 1 w (fun i => evFin F w (x i)) := by
            by_cases e : w = v
            · subst w
              simp [t]
            · simp [t, e]
          unfold tens r GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
          rw [funext hprod, finprod_mul_distrib ht hsupport,
            finprod_eq_single t v (fun w e => ite_eq_right e)]
          simp only [t, if_true]
          ac_rfl
        funext x
        have hs : (fun y => pure g θ (repl v x y)) = r x • θ v := by
          have hself := hu (θ v)
          rw [Function.update_eq_self] at hself
          funext y
          rw [hself, tens, piK_repl, hr, Pi.smul_apply, smul_eq_mul, mul_comm]
        change ev v (fun y => pure g θ (repl v x y)) (piK v (finPart x)) = _
        rw [hs, map_smul, hu, tens, Pi.smul_apply, smul_eq_mul, mul_comm]
        rfl
      rw [map_smul, hop _ h2]
      congr 2
      funext w
      rcases eq_or_ne w v with rfl | e
      · simp [hv]
      · simp [e]
  have hfin : {v | ¬ (ev v (stdL F κ v) = stdL F κ v ∧ ∀ j ∈ s, φ j v = stdL F κ v)}.Finite :=
    eventually_cofinite.1 (hev.and ((eventually_all_finset s).2 fun j _ => hφ j))
  rw [← key hfin.toFinset]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  funext v
  split_ifs with e
  · rfl
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at e
    rw [e.2 j hj, e.1]

theorem exists_glue (ei : SInf F κ →ₗ[ℂ] SInf F κ) (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ))
    (hev : ∀ᶠ v in cofinite, ev v (stdL F κ v) = stdL F κ v) : ∃ e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ),
    ∀ f φ, (∀ᶠ v in cofinite, φ v = stdL F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
  let a : (Dat F κ →₀ ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := Finsupp.linearCombination ℂ fun p => pure p.1.1 p.1.2
  let b : (Dat F κ →₀ ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := Finsupp.linearCombination ℂ fun p => pure (ei p.1.1) fun v => ev v (p.1.2 v)
  have hk : LinearMap.ker a ≤ LinearMap.ker b := fun z hz =>
    rel_fin ev hev z.support z (fun p => ei p.1.1) (fun p => p.1.2) (fun p => p.2) (rel_inf ei z.support z _ _ hz)
  obtain ⟨e, he⟩ := ((LinearMap.ker a).liftQ b hk ∘ₗ a.quotKerEquivRange.symm.toLinearMap).exists_extend
  refine ⟨e, fun f φ hφ => ?_⟩
  have h1 : a (Finsupp.single ⟨(f, φ), hφ⟩ 1) = pure f φ := (Finsupp.linearCombination_single ℂ 1 _).trans (one_smul _ _)
  have h2 := LinearMap.congr_fun he ⟨_, LinearMap.mem_range_self a (Finsupp.single ⟨(f, φ), hφ⟩ 1)⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply] at h2
  rw [← h1, h2]
  exact (Finsupp.linearCombination_single ℂ 1 _).trans (one_smul _ _)

theorem adelSt_of (hP : PureSt) (hF : FinSt) (hI : InfSt) : AdelSt := by
  intro F _ _ ψ hψ κ _ S hS
  obtain ⟨ev, hb, hi, hs⟩ := hF F ψ hψ κ S hS
  obtain ⟨ei, hei⟩ := hI F κ S hS
  obtain ⟨e, he'⟩ := exists_glue (ei : SInf F κ →L[ℂ] SInf F κ).toLinearMap ev hs
  have he : ∀ f φ, (∀ᶠ v in cofinite, φ v = stdL F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v) := he'
  have hstd : ∀ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, (∀ᶠ v in cofinite, φ v = stdL F κ v) →
      ∀ᶠ v in cofinite, ev v (φ v) = stdL F κ v := fun φ h => by
    filter_upwards [h, hs] with v e1 e2
    rw [e1, e2]
  refine ⟨e, ei, ev, fun Φ hΦ => schA_le ((schA F κ).comap e) (fun f φ h1 h2 => ?_) hΦ, fun w Φ hΦ => ?_, hb,
    fun v w hw φ hφ φ₁ h₁ => ?_, hs, fun f φ _ h => he f φ h⟩
  · rw [Submodule.mem_comap, he f φ h2]
    exact pure_mem_schA _ _ (fun v => (hb v).1 (h1 v)) (hstd φ h2)
  · let L : ∀ u : (κ → AF F) × (κ → AF F), ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := fun u =>
      { toFun := schr ψ u
        map_add' := fun _ _ => funext fun _ => by simp [schr, mul_add]
        map_smul' := fun _ _ => funext fun _ => by simp [schr, mul_left_comm] }
    refine schA_le (LinearMap.eqLocus (e ∘ₗ L w) (L (S w) ∘ₗ e)) (fun f φ h1 h2 => ?_) hΦ
    change e (schr ψ w _) = schr ψ (S w) (e _)
    obtain ⟨⟨g, hg⟩, h⟩ := hP F ψ hψ κ w f
    rw [(h φ h2).2 g hg, he _ _ (h φ h2).1, he f φ h2, ((hP F ψ hψ κ (S w) (ei f)).2 _ (hstd φ h2)).2 _ (hei w f g hg)]
    congr 1
    funext v
    exact hi v w _ (h1 v)
  · have hw' : At (evFin F v) (S w) := fun u hu => by rw [← map_smul, hw u hu, map_zero]
    rw [action_uniqueness F κ v _ φ hφ _ _ h₁ (ad_heis ψ w hw φ), hi v w φ hφ]
    exact ad_heis ψ (S w) hw' (ev v φ)

end PositivityTheory.Mix
end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.FiniteAdelicEstimatesHolds
noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo
  GlobalTheory.LatVac

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : Pl F}

def liftW (v : Pl F) (y : (κ → Fv F v) × (κ → Fv F v)) : (κ → AF F) × (κ → AF F) :=
  (fun i => liftV v (y.1 i), fun i => liftV v (y.2 i))

omit [Fintype κ] in
theorem locW_smul (a : AF F) (z : (κ → AF F) × (κ → AF F)) : locW v (a • z) = evFin F v a • locW v z :=
  Prod.ext (funext fun _ => map_mul _ _ _) (funext fun _ => map_mul _ _ _)

omit [Fintype κ] in
theorem locW_add (z z' : (κ → AF F) × (κ → AF F)) : locW v (z + z') = locW v z + locW v z' :=
  Prod.ext (funext fun _ => map_add _ _ _) (funext fun _ => map_add _ _ _)

omit [Fintype κ] in
theorem locW_liftW (y : (κ → Fv F v) × (κ → Fv F v)) : locW v (liftW v y) = y :=
  Prod.ext (funext fun _ => evFin_liftV _ _) (funext fun _ => evFin_liftV _ _)

omit [Fintype κ] in
theorem liftW_locW (z : (κ → AF F) × (κ → AF F)) : liftW v (locW v z) = liftV v 1 • z :=
  Prod.ext (funext fun _ => (GlobalTheory.LatVacArith.liftV_one_mul _ _).symm) (funext fun _ => (GlobalTheory.LatVacArith.liftV_one_mul _ _).symm)

def locT (v : Pl F) (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ((κ → Fv F v) × (κ → Fv F v)) →ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v)) where
  toFun y := locW v (T (liftW v y))
  map_add' y y' := by
    rw [← locW_add, ← map_add (f := _)]
    congr 2
    exact Prod.ext (funext fun _ => map_add _ _ _) (funext fun _ => map_add _ _ _)
  map_smul' c y := by
    have e : liftW v (c • y) = liftV v c • liftW v y := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
        exact ((mul_liftV _ _).trans (by rw [evFin_liftV]; rfl)).symm
    rw [e, map_smul, locW_smul, evFin_liftV]
    rfl

omit [Fintype κ] in
theorem locT_locW (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) (z) : locT v T (locW v z) = locW v (T z) := by
  change locW v (T (liftW v (locW v z))) = _
  rw [liftW_locW, map_smul, locW_smul, evFin_liftV, one_smul]

def locE (v : Pl F) (S : ((κ → AF F) × (κ → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ((κ → Fv F v) × (κ → Fv F v)) ≃ₗ[Fv F v] ((κ → Fv F v) × (κ → Fv F v)) :=
  { locT v S.toLinearMap with
    invFun := locT v S.symm.toLinearMap
    left_inv := fun y => by
      change locT v _ (locW v _) = _
      rw [locT_locW, LinearEquiv.coe_coe, LinearEquiv.coe_coe, S.symm_apply_apply, locW_liftW]
    right_inv := fun y => by
      change locT v _ (locW v _) = _
      rw [locT_locW, LinearEquiv.coe_coe, LinearEquiv.coe_coe, S.apply_symm_apply, locW_liftW] }

def intW (v : Pl F) : Submodule (v.adicCompletionIntegers F) ((κ → Fv F v) × (κ → Fv F v)) where
  carrier := {y | (∀ i, y.1 i ∈ v.adicCompletionIntegers F) ∧ ∀ i, y.2 i ∈ v.adicCompletionIntegers F}
  add_mem' ha hb := ⟨fun i => add_mem (ha.1 i) (hb.1 i), fun i => add_mem (ha.2 i) (hb.2 i)⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ h := ⟨fun i => mul_mem c.2 (h.1 i), fun i => mul_mem c.2 (h.2 i)⟩

theorem locW_int (z : (κ → AF F) × (κ → AF F)) : ∀ᶠ v in cofinite, locW v z ∈ intW v :=
  (eventually_all.2 fun i => (z.1 i).2.2).and (eventually_all.2 fun i => (z.2 i).2.2)

theorem locT_int (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ∀ᶠ v in cofinite, ∀ y ∈ intW v, locT v T y ∈ intW v := by
  classical
  filter_upwards [eventually_all.2 fun i => locW_int (T (Pi.single i 1, 0)), eventually_all.2 fun i => locW_int (T (0, Pi.single i 1))]
    with v h1 h2 y hy
  have e : liftW v y = ∑ i, liftV v (y.1 i) • ((Pi.single i 1, 0) : (κ → AF F) × (κ → AF F)) +
      ∑ i, liftV v (y.2 i) • ((0, Pi.single i 1) : (κ → AF F) × (κ → AF F)) := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      simp [liftW, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hs : ∀ (c : κ → Fv F v) (z : κ → (κ → AF F) × (κ → AF F)), (∀ i, c i ∈ v.adicCompletionIntegers F) →
      (∀ i, locW v (T (z i)) ∈ intW v) → locW v (T (∑ i, liftV v (c i) • z i)) ∈ intW v := fun c z hc hz => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_induction _ (fun t => locW v t ∈ intW v) (fun a b ha hb => locW_add a b ▸ add_mem ha hb) ?_ fun i _ => ?_
    · have z0 : evFin F v 0 ∈ v.adicCompletionIntegers F := by rw [map_zero]; exact zero_mem _
      exact ⟨fun _ => z0, fun _ => z0⟩
    · rw [map_smul, locW_smul, evFin_liftV]
      exact ⟨fun j => mul_mem (hc i) ((hz i).1 j), fun j => mul_mem (hc i) ((hz i).2 j)⟩
  change locW v (T (liftW v y)) ∈ _
  rw [e, map_add (f := _), locW_add]
  exact add_mem (hs _ _ hy.1 h1) (hs _ _ hy.2 h2)

theorem schr_std {ψ : AddChar (AF F) ℂ} (hψ : PsiUnr ψ v) (h2 : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F) {y} (hy : y ∈ intW (κ := κ) v) :
    schr (psiV ψ v) y (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  funext x
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have h : psiV ψ v (x ⬝ᵥ y.2 + ⅟(2 : Fv F v) * (y.1 ⬝ᵥ y.2)) = 1 := by
      have := (hψ _).2 (show x ⬝ᵥ y.2 + ⅟(2 : Fv F v) * (y.1 ⬝ᵥ y.2) ∈ v.adicCompletionIntegers F from
        add_mem (sum_mem fun i _ => mul_mem (hx i) (hy.2 i))
          (mul_mem (by rwa [invOf_eq_inv]) (sum_mem fun i _ => mul_mem (hy.1 i) (hy.2 i)))) 1 (one_mem _)
      rwa [mul_one] at this
    rw [schr, h, one_mul, Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx),
      Set.indicator_of_mem (show x + y.1 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun i => add_mem (hx i) (hy.1 i))]
    rfl
  · rw [schr, Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx),
      Set.indicator_of_notMem (show x + y.1 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun h => hx fun i => by
        simpa using sub_mem (h i) (hy.1 i)), mul_zero]

theorem eq_std {ψ : AddChar (AF F) ℂ} (hψ : PsiUnr ψ v) {Φ : (κ → Fv F v) → ℂ} (h : ∀ y ∈ intW v, schr (psiV ψ v) y Φ = Φ) :
    Φ = Φ 0 • Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  classical
  funext x
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have := congrFun (h (x, 0) ⟨hx, fun _ => zero_mem _⟩) 0
    rw [Pi.smul_apply, Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
    simpa [schr] using this
  · rw [Pi.smul_apply, Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx), smul_zero]
    obtain ⟨i, hi⟩ := not_forall.1 hx
    obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x i * y) ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hi ((hψ _).1 hc)
    have := congrFun (h (0, Pi.single i y) ⟨fun _ => zero_mem _, fun j => by
      by_cases e : j = i
      · subst e; simpa using hy
      · simp [Pi.single_eq_of_ne e]⟩) x
    simp only [schr, dotProduct_single, zero_dotProduct, mul_zero, add_zero, Pi.zero_apply, zero_mul] at this
    exact (mul_left_eq_self₀.1 this).resolve_left hne

theorem finite_adelic_estimates_holds : FinSt := by
  intro F _ _ ψ hψ κ _ S hS
  classical
  have hsy : ∀ (v : Pl F) y y', ((locE v S).symm y).1 ⬝ᵥ ((locE v S).symm y').2 - ((locE v S).symm y').1 ⬝ᵥ ((locE v S).symm y).2 =
      y.1 ⬝ᵥ y'.2 - y'.1 ⬝ᵥ y.2 := fun v y y' => by
    have := congrArg (evFin F v) (hS (S.symm (liftW v y)) (S.symm (liftW v y')))
    rw [S.apply_symm_apply, S.apply_symm_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sub, map_sum, map_mul, liftW, evFin_liftV] at this
    exact this.symm
  choose ι hb hi using fun v : Pl F => Mod.model ((adjoint_statement.psi F ψ hψ).2 v).1 ((adjoint_statement.psi F ψ hψ).2 v).2 (locE v S).symm (hsy v)
  let s : ∀ v : Pl F, (κ → Fv F v) → ℂ := fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let c : Pl F → ℂ := fun v => if ι v (s v) 0 = 0 then 1 else (ι v (s v) 0)⁻¹
  have hc : ∀ v, c v ≠ 0 := fun v => by
    simp only [c]
    split_ifs with e
    exacts [one_ne_zero, inv_ne_zero e]
  refine ⟨fun v => c v • ι v, fun v => ⟨fun φ hφ => Submodule.smul_mem _ _ ((hb v).1 hφ), fun φ hφ φ' hφ' e =>
    (hb v).2.1 hφ hφ' (smul_right_injective _ (hc v) e), fun Φ hΦ => ?_⟩, fun v w φ hφ => ?_, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := (hb v).2.2 (Submodule.smul_mem _ (c v)⁻¹ hΦ)
    exact ⟨φ, hφ, by rw [LinearMap.smul_apply, e, smul_inv_smul₀ (hc v)]⟩
  · have e : locW v w = (locE v S).symm (locW v (S w)) := by
      change _ = locT v _ _
      rw [locT_locW, LinearEquiv.coe_coe, S.symm_apply_apply]
    rw [LinearMap.smul_apply, LinearMap.smul_apply, e, hi v _ φ hφ]
    funext x
    simp [schr, mul_left_comm]
  · have hd : ∀ᶠ v : Pl F in cofinite, ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal :=
      (Ideal.finite_factors differentIdeal_ne_bot).subset fun v hv => Ideal.dvd_iff_le.2 (not_not.1 hv)
    have h2 : ∀ᶠ v : Pl F in cofinite, evFin F v (algebraMap F (AF F) 2⁻¹) ∈ v.adicCompletionIntegers F :=
      (algebraMap F (AF F) 2⁻¹).2.2
    filter_upwards [hd, h2, locT_int S.symm.toLinearMap] with v e1 e2 e3
    have hu : PsiUnr ψ v := psiUnr_of_not_le hψ v e1
    have e2' : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
      rwa [AlgHom.commutes, map_inv₀, map_ofNat] at e2
    have h := eq_std hu (Φ := ι v (s v)) fun y hy => by
      rw [← hi v y _ (std_mem_SB v)]
      exact congrArg (ι v) (schr_std hu e2' (e3 y hy))
    have h0 : ι v (s v) 0 ≠ 0 := fun e => by
      rw [e, zero_smul] at h
      have := congrFun ((hb v).2.1 (std_mem_SB v) (zero_mem (SB _)) (h.trans (map_zero _).symm)) 0
      rw [Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun i => zero_mem _)] at this
      exact one_ne_zero this
    change c v • ι v (s v) = _
    rw [show c v = (ι v (s v) 0)⁻¹ from if_neg h0, inv_smul_eq_iff₀ h0]
    exact h

end PositivityTheory.Mix
end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MCPure
noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo

variable {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ]

theorem exists_triv (hψ : IsStd ψ) : ∃ T : Finset (Pl F), ∀ b : Af F,
    (∀ v ∈ T, evalV F v b = 0) → (∀ v, evalV F v b ∈ v.adicCompletionIntegers F) → ψ ((0 : Ainf F), b) = 1 := by
  have hl := GlobalTheory.CompanionTheory.AdelicHeis.isLocallyConstant_fin (ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F)))
    (hψ.1.comp (continuous_const.prodMk continuous_id)) fun x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _
  obtain ⟨M, hM, h⟩ := GlobalTheory.IdeleCharLevel.exists_level F _ ((hl.isOpen_fiber 1).mem_nhds (AddChar.map_zero_eq_one _))
  have h0 : Ideal.span {(M : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hM
  refine ⟨(Ideal.finite_factors h0).toFinset, fun b h1 h2 => h b fun v => ?_⟩
  by_cases hv : v ∈ (Ideal.finite_factors h0).toFinset
  · have : b v = 0 := h1 v hv
    rw [this, map_zero]; exact zero_le'
  · have e : v.intValuation (M : 𝓞 F) = 1 := by
      by_contra e
      exact hv ((Set.Finite.mem_toFinset _).2
        ((v.intValuation_lt_one_iff_dvd _).1 (lt_of_le_of_ne (v.intValuation_le_one (M : 𝓞 F)) e)))
    rw [e]; exact h2 v

theorem psiV_int (hψ : IsStd ψ) : ∀ᶠ v : Pl F in cofinite, ∀ y ∈ v.adicCompletionIntegers F, psiV ψ v y = 1 := by
  obtain ⟨T, hT⟩ := exists_triv hψ
  filter_upwards [T.eventually_cofinite_notMem] with v hv y hy
  refine hT (singleFin v y) (fun u hu => evalV_singleFin_ne (fun e : u = v => hv (e ▸ hu)) y) fun u => ?_
  rcases eq_or_ne u v with rfl | e
  · rwa [evalV_singleFin_self]
  · rw [evalV_singleFin_ne e]; exact zero_mem _

theorem psiV_ev (hψ : IsStd ψ) (a : AF F) : ∀ᶠ v : Pl F in cofinite, psiV ψ v (evFin F v a) = 1 := by
  filter_upwards [psiV_int hψ, (a.2.2 : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F)] with v h1 h2
  exact h1 _ h2

theorem psi_fin (hψ : IsStd ψ) (a : AF F) : ψ ((0 : Ainf F), a.2) = ∏ᶠ v, psiV ψ v (evFin F v a) := by
  classical
  obtain ⟨T, hT⟩ := exists_triv hψ
  have hfin : {v : Pl F | ¬ (v ∉ T ∧ psiV ψ v (evFin F v a) = 1 ∧ evFin F v a ∈ v.adicCompletionIntegers F)}.Finite :=
    eventually_cofinite.1 (T.eventually_cofinite_notMem.and ((psiV_ev hψ a).and a.2.2))
  set U := hfin.toFinset
  have hU : ∀ v ∉ U, v ∉ T ∧ psiV ψ v (evFin F v a) = 1 ∧ evFin F v a ∈ v.adicCompletionIntegers F := fun v hv =>
    not_not.1 fun e => hv (hfin.mem_toFinset.2 e)
  let s : Af F := ∑ v ∈ U, singleFin v (evFin F v a)
  have hs : ∀ u, evalV F u s = if u ∈ U then evFin F u a else 0 := fun u => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    split_ifs with h
    · rw [Finset.sum_eq_single u (fun v _ e => evalV_singleFin_ne (Ne.symm e) _) (fun e => (e h).elim), evalV_singleFin_self]
    · exact Finset.sum_eq_zero fun v hv => evalV_singleFin_ne (fun e : u = v => h (e ▸ hv)) _
  have h1 : ψ ((0 : Ainf F), a.2 - s) = 1 := hT _ (fun v hv => by
      have : v ∈ U := by by_contra e; exact (hU v e).1 hv
      rw [map_sub, hs, if_pos this]; exact sub_self _) fun v => by
    rw [map_sub, hs]
    split_ifs with h
    · exact (sub_self (evFin F v a)).symm ▸ zero_mem _
    · rw [sub_zero]; exact (hU v h).2.2
  let χ : AddChar (Af F) ℂ := ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F))
  have h2 : χ s = ∏ v ∈ U, psiV ψ v (evFin F v a) := by
    have : ∀ V : Finset (Pl F), χ (∑ v ∈ V, singleFin v (evFin F v a)) = ∏ v ∈ V, psiV ψ v (evFin F v a) := fun V => by
      induction V using Finset.induction_on with
      | empty => simp
      | insert v V hv ih => rw [Finset.sum_insert hv, Finset.prod_insert hv, AddChar.map_add_eq_mul, ih]; rfl
    exact this U
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := U) fun v hv => by
    by_contra e; exact hv (hU v e).2.1, ← h2]
  change χ a.2 = _
  rw [← sub_add_cancel a.2 s, AddChar.map_add_eq_mul]
  exact (congrArg (· * χ s) h1).trans (one_mul _)

theorem psi_prod (hψ : IsStd ψ) (a : AF F) : ψ a = Complex.exp (-(2 * Real.pi * Complex.I) *
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) : ℝ)) * ∏ᶠ v, psiV ψ v (evFin F v a) := by
  have e : a = ((a.1, (0 : Af F)) : AF F) + (((0 : Ainf F), a.2) : AF F) := Prod.ext (add_zero _).symm (zero_add _).symm
  have h := hψ.2.2 ((a.1, (0 : Af F)) : AF F) fun u hu => by
    have : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    exact Prod.ext (show u.1 * a.1 = 0 by rw [this, zero_mul]) (mul_zero u.2)
  rw [← psi_fin hψ]
  exact (congrArg ψ e).trans ((ψ.map_add_eq_mul (pairA F a.1 0) (pairA F 0 a.2)).trans (congrArg (· * _) h))

def evIH (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem map_half {R S : Type} [CommRing R] [CommRing S] [Invertible (2 : R)] [Invertible (2 : S)] (f : R →+* S) :
    f (⅟2) = ⅟2 := by
  refine (invOf_eq_right_inv ?_).symm
  rw [← map_ofNat f 2, ← map_mul, mul_invOf_self, map_one]

open scoped Classical in
theorem exists_isTr (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) : ∃ g, IsTr w f g := by
  let c : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun x =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((beta F κ x (infV w.2) : ℝ) : ℂ))
  have hb : Continuous fun x : κ → mixedEmbedding.mixedSpace F => beta F κ x (infV w.2) :=
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).continuous_of_finiteDimensional.comp (by unfold dotProduct; fun_prop)
  have hT : Function.HasTemperateGrowth c := GlobalTheory.CompanionTheory.AdelicHeis.temperate_char c (by fun_prop)
    (fun t => by simp [c, Complex.norm_exp]) (by simp [c, beta]) fun s t => by
      simp only [c, beta, add_dotProduct, map_add (f := _), Complex.ofReal_add, mul_add, Complex.exp_add]
  refine ⟨Complex.exp (-(2 * Real.pi * Complex.I) * ((beta F κ (infV w.1) (infV w.2) / 2 : ℝ) : ℂ)) •
    SchwartzMap.smulLeftCLM ℂ c (SchwartzMap.compSubConstCLM ℂ (-infV w.1) f), fun x => ?_⟩
  rw [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add,
    Complex.ofReal_add, mul_add, Complex.exp_add]
  simp only [c, smul_eq_mul]
  ring

theorem pure_tensor_estimates_holds : PureSt := by
  intro F _ _ ψ hψ κ _ w f
  refine ⟨exists_isTr w f, fun φ hφ => ⟨?_, fun g hg => funext fun x => ?_⟩⟩
  · have h1 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (w.1 i) ∈ v.adicCompletionIntegers F := eventually_all.2 fun i => (w.1 i).2.2
    have h2 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (w.2 i) ∈ v.adicCompletionIntegers F := eventually_all.2 fun i => (w.2 i).2.2
    have h3 : ∀ᶠ v : Pl F in cofinite, evFin F v (⅟2) ∈ v.adicCompletionIntegers F := (⅟2 : AF F).2.2
    filter_upwards [hφ, h1, h2, h3, psiV_int hψ] with v e e1 e2 e3 e4
    rw [show evFin F v (⅟2) = ⅟2 from map_half (evFin F v).toRingHom] at e3
    funext y
    rw [e, schr]
    by_cases hy : ∀ i, y i ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (show y + (locW v w).1 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun i => add_mem (hy i) (e1 i)), Set.indicator_of_mem (show y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy),
        e4 (y ⬝ᵥ (locW v w).2 + ⅟2 * ((locW v w).1 ⬝ᵥ (locW v w).2)) (add_mem (sum_mem fun i _ => mul_mem (hy i) (e2 i)) (mul_mem e3 (sum_mem fun i _ => mul_mem (e1 i) (e2 i))))]
      simp
    · rw [Set.indicator_of_notMem (show y + (locW v w).1 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun h => hy fun i => by simpa [locW] using sub_mem (h i) (e1 i)),
        Set.indicator_of_notMem (show y ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy), mul_zero]
  · let a : AF F := x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2)
    have e1 : ∀ v, schr (psiV ψ v) (locW v w) (φ v) (fun i => evFin F v (x i)) =
        psiV ψ v (evFin F v a) * φ v fun i => evFin F v ((x + w.1) i) := fun v => by
      have hh : evFin F v (⅟2) = ⅟2 := map_half (evFin F v).toRingHom
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [schr, a, locW, dotProduct, map_add (f := _), map_mul, map_sum, hh, Pi.add_apply]
      rfl
    have e2 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
        beta F κ (fun i => evI F (x i)) (infV w.2) + beta F κ (infV w.1) (infV w.2) / 2 := by
      have h2 : evIH F (⅟2) = algebraMap ℝ _ (1 / 2) := by
        have : evIH F (⅟2) * algebraMap ℝ _ 2 = 1 := by rw [map_ofNat, ← map_ofNat (evIH F) 2, ← map_mul, invOf_mul_self, map_one]
        calc evIH F (⅟2) = evIH F (⅟2) * algebraMap ℝ _ 2 * algebraMap ℝ _ (1 / 2) := by
              rw [mul_assoc, ← map_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, map_one, mul_one]
          _ = _ := by rw [this, one_mul]
      change Algebra.trace ℝ _ (evIH F a) = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [a, map_add (f := _), map_mul, h2, ← Algebra.smul_def, map_smul, dotProduct, map_sum, beta, smul_eq_mul]
      exact congrArg₂ (· + ·) rfl ((one_div_mul_eq_div _ _).trans rfl)
    have e3 : (fun i => evI F ((x + w.1) i)) = (fun i => evI F (x i)) + infV w.1 := funext fun i => map_add (evIH F) _ _
    change ψ a * _ = _
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, e1]
    rw [finprod_mul_distrib (eventually_cofinite.1 (psiV_ev hψ a))
      (GlobalTheory.CompanionTheory.Ar.RT.Move.finite_mulSupport (vac := φ) hφ (Eventually.of_forall fun _ => rfl) (x + w.1)), hg, psi_prod hψ, e2, e3]
    ring

end PositivityTheory.Mix
end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.TraceNondeg
noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open mixedEmbedding
open scoped Classical

namespace Inf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def rho (F : Type) [Field F] [NumberField F] : AF F →+* mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

def li (a : mixedSpace F) : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0)

theorem rho_li (a : mixedSpace F) : rho F (li a) = a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a

theorem li_add (a b : mixedSpace F) : li (a + b) = li a + li b := Prod.ext (map_add _ a b) (add_zero _).symm

theorem li_mul (a b : mixedSpace F) : li (a * b) = li a * li b := Prod.ext (map_mul _ a b) (mul_zero _).symm

theorem li_rho (z : AF F) : li (rho F z) = li 1 * z :=
  Prod.ext (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _).trans (by
    change z.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 1 * z.1
    rw [map_one, one_mul])) (zero_mul _).symm

def pr (w : (κ → AF F) × (κ → AF F)) : (κ → mixedSpace F) × (κ → mixedSpace F) := (fun i => rho F (w.1 i), fun i => rho F (w.2 i))

def lf (y : (κ → mixedSpace F) × (κ → mixedSpace F)) : (κ → AF F) × (κ → AF F) := (fun i => li (y.1 i), fun i => li (y.2 i))

omit [Fintype κ] in
theorem pr_lf (y : (κ → mixedSpace F) × (κ → mixedSpace F)) : pr (lf y) = y :=
  Prod.ext (funext fun _ => rho_li _) (funext fun _ => rho_li _)

omit [Fintype κ] in
theorem pr_smul (c : AF F) (w : (κ → AF F) × (κ → AF F)) : pr (c • w) = rho F c • pr w :=
  Prod.ext (funext fun _ => map_mul _ _ _) (funext fun _ => map_mul _ _ _)

omit [Fintype κ] in
theorem lf_pr (w : (κ → AF F) × (κ → AF F)) : lf (pr w) = li (1 : mixedSpace F) • w :=
  Prod.ext (funext fun _ => li_rho _) (funext fun _ => li_rho _)

def loc (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ((κ → mixedSpace F) × (κ → mixedSpace F)) →ₗ[mixedSpace F] ((κ → mixedSpace F) × (κ → mixedSpace F)) where
  toFun y := pr (T (lf y))
  map_add' y z := by
    have e : lf (y + z) = lf y + lf z := Prod.ext (funext fun _ => li_add _ _) (funext fun _ => li_add _ _)
    rw [e, map_add (f := _)]
    exact Prod.ext (funext fun _ => map_add _ _ _) (funext fun _ => map_add _ _ _)
  map_smul' c y := by
    have e : lf (c • y) = li c • lf y := Prod.ext (funext fun _ => li_mul _ _) (funext fun _ => li_mul _ _)
    rw [e, map_smul, pr_smul, rho_li]
    rfl

omit [Fintype κ] in
theorem loc_pr (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) (w : (κ → AF F) × (κ → AF F)) :
    loc T (pr w) = pr (T w) := by
  change pr (T (lf (pr w))) = _
  rw [lf_pr, map_smul, pr_smul, rho_li, one_smul]

theorem pr_dot (x y : κ → AF F) : (fun i => rho F (x i)) ⬝ᵥ (fun i => rho F (y i)) = rho F (x ⬝ᵥ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, map_sum]

theorem trace_nondeg (a : mixedSpace F) (h : ∀ b, Algebra.trace ℝ (mixedSpace F) (a * b) = 0) : a = 0 := by
  let b : mixedSpace F := (fun w => (a.1 w)⁻¹, fun w => (a.2 w)⁻¹)
  have h1 : a * b * a = a := Prod.ext (funext fun w => mul_inv_mul_cancel (a.1 w)) (funext fun w => mul_inv_mul_cancel (a.2 w))
  have h2 : IsIdempotentElem (Algebra.lmul ℝ (mixedSpace F) (a * b)) := by
    unfold IsIdempotentElem
    rw [← map_mul, ← mul_assoc, h1]
  have h3 := (LinearMap.IsIdempotentElem.isProj_range _ h2).trace
  have h4 : LinearMap.trace ℝ _ (Algebra.lmul ℝ (mixedSpace F) (a * b)) = 0 := h b
  rw [h4] at h3
  have h5 : LinearMap.range (Algebra.lmul ℝ (mixedSpace F) (a * b)) = ⊥ :=
    Submodule.finrank_eq_zero.1 (by exact_mod_cast h3.symm)
  have h6 : a * b * a ∈ LinearMap.range (Algebra.lmul ℝ (mixedSpace F) (a * b)) := ⟨a, rfl⟩
  rwa [h5, h1, Submodule.mem_bot] at h6

def betaL (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : (κ → mixedSpace F) →ₗ[ℝ] (κ → mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (beta F κ) (fun x y z => by simp only [beta, add_dotProduct, map_add (f := _)]) (fun c x y => by simp [beta, smul_dotProduct])
    (fun x y z => by simp only [beta, dotProduct_add, map_add (f := _)]) fun c x y => by simp [beta, dotProduct_smul]

end Inf

open Inf

theorem infSt_of (h : RealSt) : InfSt := by
  intro F _ _ κ _ S hS
  let S₀ : ((κ → mixedSpace F) × (κ → mixedSpace F)) ≃ₗ[mixedSpace F] ((κ → mixedSpace F) × (κ → mixedSpace F)) :=
    LinearEquiv.ofLinear (loc S.toLinearMap) (loc S.symm.toLinearMap)
      (LinearMap.ext fun y => by
        change loc S.toLinearMap (pr (S.symm (lf y))) = y
        rw [loc_pr]; simp [pr_lf])
      (LinearMap.ext fun y => by
        change loc S.symm.toLinearMap (pr (S (lf y))) = y
        rw [loc_pr]; simp [pr_lf])
  have hp : ∀ w, (S₀.restrictScalars ℝ) (pr w) = pr (S w) := fun w => loc_pr S.toLinearMap w
  obtain ⟨T, hT⟩ := h (κ → mixedSpace F) (betaL F κ) (fun x y => congrArg (Algebra.trace ℝ (mixedSpace F)) (dotProduct_comm x y))
    (fun x hx => funext fun i => trace_nondeg _ fun b => by
      have e : beta F κ x (Pi.single i b) = 0 := hx _
      rwa [beta, dotProduct_single] at e)
    (S₀.restrictScalars ℝ) fun y z => by
      rw [← pr_lf y, ← pr_lf z, hp, hp]
      change beta F κ _ _ - beta F κ _ _ = beta F κ _ _ - beta F κ _ _
      simp only [beta, pr, pr_dot, ← map_sub, hS]
  refine ⟨T, fun w f g hg x => ?_⟩
  have := hT (pr w) f g hg x
  rw [hp] at this
  exact this

end PositivityTheory.Mix
end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MCReal
noncomputable section

namespace PositivityTheory.Mix.Real

open SchwartzMap MeasureTheory FourierTransform
open scoped RealInnerProductSpace

def ee (t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ))

theorem ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  rw [ee, ee, ee, ← Complex.exp_add]; congr 1; push_cast; ring

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem ee_temp : ee.HasTemperateGrowth := by
  have hc : Real.cos.HasTemperateGrowth := ⟨Real.contDiff_cos, fun n => ⟨0, 1, fun x => by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; simpa using Real.abs_iteratedDeriv_cos_le_one n x⟩⟩
  have hs : Real.sin.HasTemperateGrowth := ⟨Real.contDiff_sin, fun n => ⟨0, 1, fun x => by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; simpa using Real.abs_iteratedDeriv_sin_le_one n x⟩⟩
  have hl : (fun t : ℝ => -(2 * Real.pi) * t).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul Function.HasTemperateGrowth.id'
  have e : ee = fun t => ((Real.cos (-(2 * Real.pi) * t) : ℝ) : ℂ) + ((Real.sin (-(2 * Real.pi) * t) : ℝ) : ℂ) * Complex.I := by
    funext t
    rw [ee, Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
    congr 1; push_cast; ring
  rw [e]
  exact (Complex.ofRealCLM.hasTemperateGrowth.comp (hc.comp hl)).add
    ((Complex.ofRealCLM.hasTemperateGrowth.comp (hs.comp hl)).mul (Function.HasTemperateGrowth.const _))

section Gen

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def Tr (β : X → X → ℝ) (w : X × X) (f g : 𝓢(X, ℂ)) : Prop := ∀ x, g x = ee (β x w.2 + β w.1 w.2 / 2) * f (x + w.1)

def cmp (A : X ≃L[ℝ] Y) : 𝓢(X, ℂ) ≃L[ℂ] 𝓢(Y, ℂ) :=
  ContinuousLinearEquiv.equivOfInverse (compCLMOfContinuousLinearEquiv ℂ A.symm) (compCLMOfContinuousLinearEquiv ℂ A)
    (fun f => by ext x; simp) (fun f => by ext x; simp)

theorem tr_cmp {β : X → X → ℝ} {β' : Y → Y → ℝ} (A : X ≃L[ℝ] Y) (B : X → Y) (h : ∀ x y, β' (A x) (B y) = β x y) {w : X × X}
    {f g : 𝓢(X, ℂ)} (H : Tr β w f g) : Tr β' (A w.1, B w.2) (cmp A f) (cmp A g) := fun y => by
  obtain ⟨x, rfl⟩ := A.surjective y
  change g (A.symm (A x)) = _ * f (A.symm (A x + A w.1))
  rw [← map_add (f := _), A.symm_apply_apply, A.symm_apply_apply, H x, h, h]

end Gen

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def Impl (S : V × V → V × V) : Prop :=
  ∃ T : 𝓢(V, ℂ) ≃L[ℂ] 𝓢(V, ℂ), ∀ w f g, Tr (inner ℝ) w f g → Tr (inner ℝ) (S w) (T f) (T g)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem Impl.comp {S S' : V × V → V × V} (h : Impl S) (h' : Impl S') : Impl fun w => S (S' w) :=
  let ⟨T, hT⟩ := h
  let ⟨T', hT'⟩ := h'
  ⟨T'.trans T, fun w f g H => hT _ _ _ (hT' w f g H)⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem implM (A : V ≃L[ℝ] V) (B : V → V) (h : ∀ x y, ⟪A x, B y⟫ = ⟪x, y⟫) : Impl fun w : V × V => (A w.1, B w.2) :=
  ⟨cmp A, fun _ _ _ H => tr_cmp A B h H⟩

omit [MeasurableSpace V] [BorelSpace V] in
theorem implN (Q : V →ₗ[ℝ] V) (h : ∀ x y, ⟪x, Q y⟫ = ⟪y, Q x⟫) : Impl fun w : V × V => (w.1, w.2 + Q w.1) := by
  have hq : ∀ c : ℝ, (fun x : V => ee (c * ⟪x, Q x⟫)).HasTemperateGrowth := fun c =>
    ee_temp.comp ((Function.HasTemperateGrowth.const c).mul ((innerSL ℝ).bilinear_hasTemperateGrowth
      Function.HasTemperateGrowth.id' (LinearMap.toContinuousLinearMap Q).hasTemperateGrowth))
  have hi : ∀ c : ℝ, ∀ f : 𝓢(V, ℂ), smulLeftCLM ℂ (fun x : V => ee (-c * ⟪x, Q x⟫))
      (smulLeftCLM ℂ (fun x : V => ee (c * ⟪x, Q x⟫)) f) = f := fun c f => by
    ext x
    rw [smulLeftCLM_apply_apply (hq _), smulLeftCLM_apply_apply (hq _), smul_smul, ← ee_add]
    simp [ee_zero]
  refine ⟨ContinuousLinearEquiv.equivOfInverse (smulLeftCLM ℂ fun x : V => ee (-(1 / 2) * ⟪x, Q x⟫))
    (smulLeftCLM ℂ fun x : V => ee (- -(1 / 2) * ⟪x, Q x⟫)) (hi _) (fun f => by simpa using hi (1 / 2) f), fun w f g H x => ?_⟩
  simp only [ContinuousLinearEquiv.equivOfInverse_apply, smulLeftCLM_apply_apply (hq _), smul_eq_mul]
  rw [H x, ← mul_assoc, ← mul_assoc, ← ee_add, ← ee_add]
  congr 2
  simp only [map_add (f := _), inner_add_left, inner_add_right, h w.1 x]
  ring

theorem implJ : Impl fun w : V × V => (w.2, -w.1) := by
  refine ⟨fourierCLE ℂ 𝓢(V, ℂ), fun w f g H ξ => ?_⟩
  have e : ∀ (φ : 𝓢(V, ℂ)) (η : V), fourierCLE ℂ 𝓢(V, ℂ) φ η = ∫ v, ee ⟪v, η⟫ * φ v := fun φ η => by
    rw [fourierCLE_apply, fourier_coe, Real.fourier_eq']
    congr 1; funext v
    rw [smul_eq_mul, ee]; congr 2; push_cast; ring
  rw [e, e, ← integral_const_mul, ← integral_add_right_eq_self (fun v => _ * (ee ⟪v, ξ + w.2⟫ * f v)) w.1]
  congr 1; funext v
  rw [H v, ← mul_assoc, ← mul_assoc, ← ee_add, ← ee_add]
  congr 2
  simp only [inner_add_left, inner_add_right, inner_neg_right, real_inner_comm w.1 ξ, real_inner_comm w.1 w.2]
  ring

theorem implJ' : Impl fun w : V × V => (-w.2, w.1) := by
  simpa using implJ.comp (implM (ContinuousLinearEquiv.neg ℝ (M := V)) (fun y => -y) fun x y => by simp)

theorem implU (Q : V →ₗ[ℝ] V) (h : ∀ x y, ⟪x, Q y⟫ = ⟪y, Q x⟫) : Impl fun w : V × V => (w.1 + Q w.2, w.2) := by
  have := implJ'.comp ((implN (-Q) fun x y => by simp [inner_neg_right, h x y]).comp implJ)
  simpa [add_comm] using this

def Sp (S : V × V →ₗ[ℝ] V × V) : Prop := ∀ w w', ⟪(S w).1, (S w').2⟫ - ⟪(S w').1, (S w).2⟫ = ⟪w.1, w'.2⟫ - ⟪w'.1, w.2⟫

omit [MeasurableSpace V] [BorelSpace V] in
theorem implP (R : V × V →ₗ[ℝ] V × V) (hR : Sp R) (h0 : ∀ y, (R (0, y)).1 = 0) : Impl R := by
  let a : V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ R ∘ₗ LinearMap.inl ℝ V V
  let c : V →ₗ[ℝ] V := LinearMap.snd ℝ V V ∘ₗ R ∘ₗ LinearMap.inl ℝ V V
  have h1 : ∀ x y, ⟪a x, (R (0, y)).2⟫ = ⟪x, y⟫ := fun x y => by simpa [h0, a] using hR (x, 0) (0, y)
  have hi : Function.Injective a := (injective_iff_map_eq_zero a).2 fun x hx => by
    have := h1 x x
    rw [hx, inner_zero_left] at this
    exact inner_self_eq_zero.1 this.symm
  let A := (LinearEquiv.ofInjectiveEndo a hi).toContinuousLinearEquiv
  have hA : ∀ x, A x = a x := fun _ => rfl
  have := (implN (c ∘ₗ (A.symm : V →L[ℝ] V).toLinearMap) fun x y => by
    obtain ⟨x, rfl⟩ := A.surjective x
    obtain ⟨y, rfl⟩ := A.surjective y
    have := hR (x, 0) (y, 0)
    simp only [inner_zero_right, sub_self, sub_eq_zero] at this
    have key : ⟪A x, c y⟫ = ⟪A y, c x⟫ := this
    simpa using key).comp (implM A (fun y => (R (0, y)).2) h1)
  convert this using 1
  funext w
  have e : R w = R (w.1, 0) + R (0, w.2) := by rw [← map_add (f := _)]; simp
  refine Prod.ext ?_ ?_
  · rw [e, Prod.fst_add, h0, add_zero]; rfl
  · rw [e, Prod.snd_add, add_comm]; simp [c]

theorem implSp (S : V × V →ₗ[ℝ] V × V) (hS : Sp S) : Impl S := by
  let b : V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ S ∘ₗ LinearMap.inr ℝ V V
  let d : V →ₗ[ℝ] V := LinearMap.snd ℝ V V ∘ₗ S ∘ₗ LinearMap.inr ℝ V V
  have hbd : ∀ y z, ⟪b y, d z⟫ = ⟪b z, d y⟫ := fun y z => by
    have := hS (0, y) (0, z)
    simp only [inner_zero_left, sub_self, sub_eq_zero] at this
    exact this
  let P : V →ₗ[ℝ] V := ((LinearMap.range b)ᗮ.starProjection : V →L[ℝ] V).toLinearMap
  have hP : ∀ x y, ⟪x, P y⟫ = ⟪y, P x⟫ := fun x y => by
    change ⟪x, (LinearMap.range b)ᗮ.starProjection y⟫ = ⟪y, (LinearMap.range b)ᗮ.starProjection x⟫
    rw [← Submodule.inner_starProjection_left_eq_right, real_inner_comm]
  have hi : Function.Injective (b + P ∘ₗ d) := (injective_iff_map_eq_zero _).2 fun y hy => by
    have hy' : b y + P (d y) = 0 := hy
    have hm : P (d y) ∈ (LinearMap.range b)ᗮ := Submodule.starProjection_apply_mem _ _
    have hb : b y = 0 := by
      have := Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self b y) hm
      rw [eq_neg_of_add_eq_zero_right hy', inner_neg_right, neg_eq_zero] at this
      exact inner_self_eq_zero.1 this
    have hd : d y ∈ (LinearMap.range b)ᗮ := (Submodule.mem_orthogonal _ _).2 (by
      rintro _ ⟨z, rfl⟩
      rw [hbd, hb, inner_zero_left])
    have hd0 : d y = 0 := by
      rw [hb, zero_add] at hy'
      exact (Submodule.starProjection_eq_self_iff.2 hd).symm.trans hy'
    have := hS (y, 0) (0, y)
    change ⟪_, d y⟫ - ⟪b y, _⟫ = _ at this
    rw [hb, hd0, inner_zero_left, inner_zero_right, sub_self] at this
    simpa using this.symm
  let B := LinearEquiv.ofInjectiveEndo _ hi
  have hB : ∀ y, B y = b y + P (d y) := fun _ => rfl
  let Q : V →ₗ[ℝ] V := d ∘ₗ B.symm.toLinearMap
  have hQ : ∀ x y, ⟪x, Q y⟫ = ⟪y, Q x⟫ := fun x y => by
    obtain ⟨x, rfl⟩ := B.surjective x
    obtain ⟨y, rfl⟩ := B.surjective y
    simp only [Q, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hB, hB, inner_add_left, inner_add_left, hbd, real_inner_comm (d y), real_inner_comm (d x) (P _), hP]
  let u : V × V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ S + P ∘ₗ LinearMap.snd ℝ V V ∘ₗ S
  let R : V × V →ₗ[ℝ] V × V := (LinearMap.snd ℝ V V ∘ₗ S - Q ∘ₗ u).prod (-u)
  have hR : ∀ w, R w = ((S w).2 - Q ((S w).1 + P (S w).2), -((S w).1 + P (S w).2)) := fun _ => rfl
  have hsp : Sp R := fun w w' => by
    rw [← hS w w', hR, hR]
    have e1 := hQ ((S w).1 + P (S w).2) ((S w').1 + P (S w').2)
    have e2 := hP (S w).2 (S w').2
    simp only [inner_neg_right, inner_sub_left, real_inner_comm _ (Q _)]
    simp only [inner_add_right (S w).2, inner_add_right (S w').2, real_inner_comm (S w).1, real_inner_comm (S w').1] at *
    linarith
  have h0 : ∀ y, (R (0, y)).1 = 0 := fun y => by
    change d y - Q (B y) = 0
    simp [Q]
  have := (implU (-P) fun x y => by simp [inner_neg_right, hP x y]).comp ((implN Q hQ).comp (implJ'.comp (implP R hsp h0)))
  convert this using 1
  funext w
  simp [hR]

end PositivityTheory.Mix.Real

namespace PositivityTheory.Mix

open PositivityTheory.Mix.Real
open scoped RealInnerProductSpace

theorem real_estimates_holds : RealSt := by
  intro X _ _ _ β hs hn S hS
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ X))
  let L : X ≃L[ℝ] V := ContinuousLinearEquiv.ofFinrankEq (by simp [V])
  let l : X →ₗ[ℝ] V := (InnerProductSpace.toDual ℝ V).symm.toLinearEquiv.toLinearMap ∘ₗ
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℝ)).toLinearMap ∘ₗ
      (β.compl₂ (L.symm : V →L[ℝ] X).toLinearMap)
  have hl : ∀ x y, ⟪L x, l y⟫ = β x y := fun x y => by
    rw [real_inner_comm]
    simp [l, hs x y]
  have hi : Function.Injective l := (injective_iff_map_eq_zero l).2 fun y hy => hn y fun x => by
    rw [hs, ← hl, hy, inner_zero_right]
  let M : X ≃ₗ[ℝ] V := LinearMap.linearEquivOfInjective l hi (by simp [V])
  have hM : ∀ x y, ⟪L x, M y⟫ = β x y := hl
  have hM' : ∀ x y, β (L.symm x) (M.symm y) = ⟪x, y⟫ := fun x y => by rw [← hM]; simp
  let E : (X × X) ≃ₗ[ℝ] (V × V) := L.toLinearEquiv.prodCongr M
  obtain ⟨T, hT⟩ := implSp (E.toLinearMap ∘ₗ S.toLinearMap ∘ₗ E.symm.toLinearMap) fun w w' => by
    change ⟪L _, M _⟫ - ⟪L _, M _⟫ = _
    rw [hM, hM, ← hM', ← hM']
    exact hS _ _
  refine ⟨((cmp L).trans T).trans (cmp L.symm), fun w f g H => ?_⟩
  have h1 := tr_cmp (β' := fun x y => β x y) L.symm M.symm hM'
    (hT _ _ _ (tr_cmp (β := fun x y => β x y) (β' := inner ℝ) L M hM (w := w) H))
  have e : E.symm (L w.1, M w.2) = w := E.symm_apply_apply w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e] at h1
  have e1 : L.symm (E (S w)).1 = (S w).1 := L.symm_apply_apply _
  have e2 : M.symm (E (S w)).2 = (S w).2 := M.symm_apply_apply _
  rw [e1, e2] at h1
  exact h1

end PositivityTheory.Mix
end
end

theorem PositivityTheory.Mix.adelic_estimates_holds : PositivityTheory.Mix.AdelSt :=
  PositivityTheory.Mix.adelSt_of PositivityTheory.Mix.pure_tensor_estimates_holds PositivityTheory.Mix.finite_adelic_estimates_holds (PositivityTheory.Mix.infSt_of PositivityTheory.Mix.real_estimates_holds)
