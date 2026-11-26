module

public import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairAlg
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoxFunMemSB
noncomputable section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.VacDbl

theorem boxFun_mem_SB {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type} {φ₁ : (κ → R) → ℂ}
    {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) : boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by
  refine ⟨(h₁.1.comp_continuous (f := fun x : κ ⊕ κ' → R => x ∘ Sum.inl) (by fun_prop)).mul
    (h₂.1.comp_continuous (f := fun x : κ ⊕ κ' → R => x ∘ Sum.inr) (by fun_prop)), ?_⟩
  have hK : IsCompact ((fun p : (κ → R) × (κ' → R) => Sum.elim p.1 p.2) '' (tsupport φ₁ ×ˢ tsupport φ₂)) := by
    refine (IsCompact.prod h₁.2 h₂.2).image (continuous_pi ?_)
    rintro (i | i)
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_snd
  refine HasCompactSupport.intro hK fun x hx => ?_
  by_contra hne
  obtain ⟨e₁, e₂⟩ := mul_ne_zero_iff.1 hne
  refine hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ e₁, subset_tsupport _ e₂⟩, ?_⟩
  funext i
  rcases i with i | i <;> rfl

section

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end

end GlobalTheory.CompanionTheory.VacDbl
end
end

section -- merged from Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairRep
noncomputable section

namespace PositivityTheory.ThKH.Locpair

open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK PositivityTheory.ThKH.Locrep
open MeasureTheory
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt tensAt_tmul compFin_tensAt tensAt_mul_right)

theorem exists_ext {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (T : G → Module.End ℂ V)
    (pres : ∀ g, ∀ φ ∈ S, T g φ ∈ S) (one : ∀ φ ∈ S, T 1 φ = φ) (mul : ∀ g g', ∀ φ ∈ S, T (g * g') φ = T g (T g' φ)) :
    ∃ ρ : G →* Module.End ℂ V, ∀ g, ∀ φ ∈ S, ρ g φ = T g φ := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_extend (LinearMap.id : S →ₗ[ℂ] S)
  let P : Module.End ℂ V := S.subtype ∘ₗ π
  have h1 : ∀ φ ∈ S, P φ = φ := fun φ hφ => congrArg Subtype.val (LinearMap.congr_fun hπ ⟨φ, hφ⟩)
  have h2 : ∀ x, P x ∈ S := fun x => (π x).2
  refine ⟨{ toFun := fun g => T g * P + (1 - P), map_one' := ?_, map_mul' := fun g g' => ?_ }, fun g φ hφ => ?_⟩
  · ext x; simp [one _ (h2 x)]
  · ext x
    simp [mul _ _ _ (h2 x), h1 _ (h2 x), h1 _ (pres _ _ (h2 x))]
  · simp [h1 φ hφ]

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

theorem modu_single [LocallyCompactSpace (Fv F v)] (u : (AF F)ˣ) (x : (Fv F v)ˣ)
    (h : (u : AF F) = 1 - atPlace v 1 + atPlace v x) :
    ((distribHaarChar (AF F) u : NNReal) : ℝ) = (distribHaarChar (Fv F v) x : NNReal) := by
  rw [modu_eq, GroundTheory.Global.IdeleGroup.ideleModule_apply]
  have h1 : ∀ w, (u : AF F).1 w = 1 := fun w => by
    rw [h]
    change (1 : Ainf F) w - (0 : Ainf F) w + (0 : Ainf F) w = 1
    rw [sub_add_cancel]
    rfl
  have h2 : ∀ w, (u : AF F).2 w =
      1 - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v 1) + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (singleFin v x) :=
    fun w => by rw [h]; rfl
  have h3 : GroundTheory.Global.IdeleGroup.infiniteModule u = 1 := Finset.prod_eq_one fun w _ => by
    change ‖(u : AF F).1 w‖ ^ _ = 1
    rw [h1, norm_one, one_pow]
  have h4 : GroundTheory.Global.IdeleGroup.finiteModule u = ‖(x : Fv F v)‖ := by
    change ∏ᶠ w, ‖(u : AF F).2 w‖ = _
    rw [finprod_eq_single _ v fun w hw => by rw [h2, evalV_singleFin_ne hw, evalV_singleFin_ne hw, sub_add_cancel, norm_one],
      h2, evalV_singleFin_self, evalV_singleFin_self, sub_self, zero_add]
  rw [h3, h4, one_mul]
  have := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v (x : Fv F v) x.ne_zero
  rw [Units.mk0_val] at this
  exact (congrArg NNReal.toReal this).symm

section Fun

variable {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

theorem std_ne (h : IsStd ψ) (v : Pl F) : ψ ≠ 1 := fun e => GlobalTheory.PsiNontriv.psiV_ne_one ψ h v (by rw [e]; rfl)

theorem acts_schr (ψ : AddChar (AF F) ℂ) {w : (κ → AF F) × (κ → AF F)} (hw : At (evFin F v) w) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (schr ψ w) φ (schr (GlobalTheory.VacAny.psiV ψ v) (locW v w) φ) := fun r hr =>
  GlobalTheory.SchrLoc.schr_tens_of_at ψ v w (fun i a ha => congrFun (congrArg Prod.fst (hw a ha)) i)
    (fun i a ha => congrFun (congrArg Prod.snd (hw a ha)) i) φ r hr.1

omit [Fintype κ] in
theorem tens_inj {r : (κ → AF F) → ℂ} (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h₁ : r x₀ = 1)
    {φ φ' : (κ → Fv F v) → ℂ} (h : tens (evFin F v) φ r = tens (evFin F v) φ' r) : φ = φ' := by
  funext y
  have := congrFun h (putA v x₀ y)
  change φ (evA κ v (putA v x₀ y)) * r (putA v x₀ y) = φ' (evA κ v (putA v x₀ y)) * r (putA v x₀ y) at this
  rwa [ev_put (evA_inA v), inv_putA v hr, h₁, mul_one, mul_one] at this


variable (v) in
def IsLocOm {G : Type} [Monoid G] (om : G →* Module.End ℂ ((κ → AF F) → ℂ))
    (omv : G →* Module.End ℂ ((κ → Fv F v) → ℂ)) : Prop :=
  ∀ g, ∀ φ ∈ SB _, omv g φ ∈ SB _ ∧ Acts (evFin F v) (om g) φ (omv g φ)

theorem exists_locOm (hψ : IsStd ψ) {G : Type} [Monoid G] (om : G →* Module.End ℂ ((κ → AF F) → ℂ))
    (hp : ∀ g, ∀ Φ ∈ schA F κ, om g Φ ∈ schA F κ)
    (ha : ∀ g, ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ om g ∈ (adeleClass F).adm κ)
    (hc : ∀ g, ∀ w : (κ → AF F) × (κ → AF F), atPlace v (1 : Fv F v) • w = 0 →
      ∀ Φ ∈ schA F κ, om g (schr ψ w Φ) = schr ψ w (om g Φ)) : ∃ omv, IsLocOm v om omv := by
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base κ v
  let T : G → Module.End ℂ ((κ → Fv F v) → ℂ) := fun g => res v x₀ ∘ₗ om g ∘ₗ tensL v r₀
  have hT : ∀ g φ, T g φ = res v x₀ (om g (tens (evFin F v) φ r₀)) := fun _ _ => rfl
  have pres : ∀ g, ∀ φ ∈ SB _, T g φ ∈ SB _ := fun g φ hφ => res_mem v x₀ (hp g _ (h₀ φ hφ).2)
  have acts : ∀ g, ∀ φ ∈ SB _, Acts (evFin F v) (om g) φ (T g φ) := fun g φ hφ =>
    acts_res v hψ.1 (std_ne hψ v) hψ.2.1 (hp g) (ha g) (fun w h1 h2 => hc g w (by
      rw [← in_locW, locW, h1, h2, map_zero]; rfl)) h₁ hφ (h₀ φ hφ)
  obtain ⟨ρ, hρ⟩ := exists_ext (SB _) T pres
    (fun φ hφ => (eq_of_acts v h₁ (h₀ φ hφ) (T := om 1) fun r _ => by rw [map_one]; rfl).symm)
    (fun g g' φ hφ => by rw [hT, hT g, ← acts g' φ hφ r₀ (h₀ φ hφ), map_mul]; rfl)
  exact ⟨ρ, fun g φ hφ => by rw [hρ g φ hφ]; exact ⟨pres g φ hφ, acts g φ hφ⟩⟩

omit [Fintype κ] in
theorem putA_zero (x : κ → AF F) : putA v x 0 = (1 - atPlace v (1 : Fv F v)) • x := by
  funext i
  rw [putA_apply, Pi.zero_apply, map_zero, add_zero, Pi.smul_apply, smul_eq_mul, sub_mul, one_mul]

theorem arg_eq (a : κ → Fv F v) (w : (κ → AF F) × (κ → AF F)) :
    inA κ v a ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2 - putA v w.1 0 ⬝ᵥ putA v w.2 0) =
      atPlace v (a ⬝ᵥ (locW v w).2 + ⅟(2 : Fv F v) * ((locW v w).1 ⬝ᵥ (locW v w).2)) := by
  have evFin_invOf_two : evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
    refine (invOf_eq_right_inv ?_).symm
    have h : evFin F v (2 * ⅟(2 : AF F)) = 1 := by rw [mul_invOf_self, map_one]
    rwa [map_mul, map_ofNat] at h
  refine extF v ?_ ?_
  · rw [evFin_atPlace, map_add (f := _), map_mul, map_sub, ev_dot, ev_dot, ev_dot, evA_inA, ev_put (evA_inA v),
      evFin_invOf_two, zero_dotProduct, sub_zero]
    rfl
  · have e : ∀ i, awF v (inA κ v a i) = 0 := fun i => awF_at v _
    simp [awF_at, putA_zero, dotProduct, e]

theorem exists_form (Λ : Set ((κ → AF F) × (κ → AF F))) (hΛ : ∀ w ∈ Λ, (1 - atPlace v (1 : Fv F v)) • w ∈ Λ)
    {L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hL : L ∈ (adeleClass F).adm κ)
    (hi : ∀ w ∈ Λ, ∀ Φ ∈ schA F κ, L (schr ψ w Φ) = L Φ) (h0 : ∃ Φ ∈ schA F κ, L Φ ≠ 0)
    (lv : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (hv : ∀ w ∈ Λ, ∀ φ ∈ SB _, lv (schr (GlobalTheory.VacAny.psiV ψ v) (locW v w) φ) = lv φ) :
    ∃ l ∈ (adeleClass F).adm κ, (∀ w ∈ Λ, ∀ Φ ∈ schA F κ, l (schr ψ w Φ) = l Φ) ∧
      ∃ (r : (κ → AF F) → ℂ) (c : ℂ), c ≠ 0 ∧ (∀ φ ∈ SB _, Rest (evFin F v) φ r) ∧
        ∀ φ, l (tens (evFin F v) φ r) = c * lv φ := by
  obtain ⟨φ₀, hφ₀, y₀, Ψ, hΨ, hne⟩ : ∃ φ₀ ∈ SB (κ → Fv F v), ∃ y₀, ∃ Ψ ∈ schA F κ, L (PA v φ₀ y₀ Ψ) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨Φ, hΦ, hn⟩ := h0
    exact hn (schA_le v (LinearMap.ker L) h hΦ)
  let sl : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := LinearMap.pi fun y => L ∘ₗ PA v φ₀ y
  have hsl : ∀ φ₁ y₁ Φ, sl (PA v φ₁ y₁ Φ) = L (PA v φ₀ y₁ Φ) • φ₁ := fun φ₁ y₁ Φ => by
    funext y
    change L (PA v φ₀ y (PA v φ₁ y₁ Φ)) = _
    rw [Pm_Pm (evA_inA v), map_smul, smul_eq_mul, mul_comm]
    rfl
  have hm : ∀ Φ ∈ schA F κ, sl Φ ∈ SB _ := fun Φ hΦ => schA_le v ((SB _).comap sl) (fun φ hφ y Ψ _ => by
    rw [Submodule.mem_comap, hsl]; exact Submodule.smul_mem _ _ hφ) hΦ
  refine ⟨lv ∘ₗ sl, admissible_of_integral_conj_le v _ fun φ hφ y => ?_, fun w hw Φ hΦ => ?_, fun x => Ψ (putA v x y₀), L (PA v φ₀ y₀ Ψ), hne,
    fun φ hφ => ⟨fun x z hz => by simp only [putA_add v hz], PA_mem v hφ y₀ hΨ⟩, fun φ => ?_⟩
  · rw [show (lv ∘ₗ sl) ∘ₗ PA v φ y = lv φ • (L ∘ₗ PA v φ₀ y) from LinearMap.ext fun Φ => by
      simp only [LinearMap.comp_apply, hsl, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]]
    intro g hg
    obtain ⟨T, hT⟩ := PA_adm v hφ₀ y hL g hg
    exact ⟨lv φ • T, fun f => congrArg (lv φ • ·) (hT f)⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hv w hw _ (hm Φ hΦ)]
    congr 1
    funext a
    change L (PA v φ₀ a (schr ψ w Φ)) = _
    have e : (putA v w.1 0, putA v w.2 0) = (1 - atPlace v (1 : Fv F v)) • w := by rw [putA_zero, putA_zero]; rfl
    rw [PA_schr, map_smul, arg_eq, e, hi _ (hΛ w hw) _ (PA_mem v hφ₀ _ hΦ)]
    rfl
  · change lv (sl (PA v φ y₀ Ψ)) = _
    rw [hsl, map_smul, smul_eq_mul]

end Fun

end PositivityTheory.ThKH.Locpair
end
end

noncomputable section

namespace PositivityTheory.ThKH.Locpair

open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK PositivityTheory.ThKH.Locrep
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt tensAt_tmul compFin_tensAt tensAt_mul_right)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {α β κ ν : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Fintype ν] [DecidableEq ν]
  {ψ : AddChar (AF F) ℂ} {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {JAv : Matrix α α (Ev E v)}
  {JBv : Matrix β β (Ev E v)} {co : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}
  {dv : Darboux (symp (R := Fv F v) (cV σ v) (-1) JAv JBv) κ}

omit [DecidableEq α] [DecidableEq β] in
theorem acts_rho (h : IsLocD co dv) (ψ : AddChar (AF F) ℂ) {u : Matrix α β (AE F E)} (hu : At (evFin F v) u)
    (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (co.rho ψ u) φ (dv.rho (GlobalTheory.VacAny.psiV ψ v) (u.map (compFin F E v)) φ) := by
  rw [Darboux.rho, Darboux.rho, h]
  exact acts_schr ψ (fun a ha => by rw [← map_smul, hu a ha, map_zero]) φ

omit [Fintype α] [DecidableEq α] in
theorem mul_lift_away {u : Matrix α β (AE F E)} (hu : atPlace v (1 : Fv F v) • u = 0) (m : Matrix β β (Ev E v)) :
    u * (liftM E v β m)ᵀ = u :=
  extM v (by rw [Matrix.map_mul, compM_of_away v hu, Matrix.zero_mul])
    (by rw [Matrix.map_mul, Matrix.transpose_map, aw_liftM, Matrix.transpose_one, Matrix.mul_one])

omit [Fintype β] [DecidableEq β] in
theorem lift_mul_away {u : Matrix α β (AE F E)} (hu : atPlace v (1 : Fv F v) • u = 0) (m : Matrix α α (Ev E v)) :
    liftM E v α m * u = u :=
  extM v (by rw [Matrix.map_mul, compM_of_away v hu, Matrix.mul_zero]) (by rw [Matrix.map_mul, aw_liftM, Matrix.one_mul])

omit [DecidableEq α] [DecidableEq β] in
theorem exists_locOm' (hψ : IsStd ψ) {G Gv : Type} [Group G] [Group Gv] {act : G → Matrix α β (AE F E) → Matrix α β (AE F E)}
    {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} (hs : IsSplitting (adeleClass F) ψ co act om) (j : Gv →* G)
    (hj : ∀ g u, atPlace v (1 : Fv F v) • u = 0 → act (j g) u = u) : ∃ omv, IsLocOm v (om.comp j) omv :=
  exists_locOm hψ _ (fun g => hs.pres (j g)) (fun g => hs.adm (j g)) fun g w hw Φ hΦ => by
    obtain ⟨u, rfl⟩ := co.e.surjective w
    rw [← map_smul, LinearEquiv.map_eq_zero_iff] at hw
    have := hs.impl (j g) u Φ hΦ
    rwa [hj g u hw] at this

variable [LocallyCompactSpace (Fv F v)] {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)}
  {omv : UG (cV σ v) JBv →* Module.End ℂ ((κ → Fv F v) → ℂ)}

omit [DecidableEq α] in
theorem split_loc (hψ : IsStd ψ) (hB : JB.map (compFin F E v) = JBv) (h : IsLocD co dv)
    (hs : IsSplitting (adeleClass F) ψ co (actB (cA σ)) om) (ho : IsLocOm v (om.comp (liftU hB)) omv) :
    IsSplitting (sbClass (Fv F v)) (GlobalTheory.VacAny.psiV ψ v) dv (actB (cV σ v)) omv := by
  refine ⟨fun g φ hφ => (ho g φ hφ).1, fun g w φ hφ => ?_, fun _ _ _ => Set.mem_univ _⟩
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base κ v
  have hH := (GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F κ ψ hψ.1 (std_ne hψ v) hψ.2.1).1
  have a1 := acts_rho h ψ (at_up v w) φ r₀ (h₀ φ hφ)
  rw [comp_up] at a1
  have m1 : dv.rho (GlobalTheory.VacAny.psiV ψ v) w φ ∈ SB _ := by
    have e := eq_of_acts v h₁ (h₀ φ hφ) (acts_rho h ψ (at_up v w) φ)
    rw [comp_up] at e
    rw [e]
    exact res_mem v x₀ (hH _ _ (h₀ φ hφ).2)
  have hat : At (evFin F v) (actB (cA σ) (liftU hB g) (w.map (tensAt E v))) := fun a ha => by
    rw [actB, ← Matrix.smul_mul, at_up v w a ha, Matrix.zero_mul]
  have a2 := acts_rho h ψ hat (omv g φ) r₀ (h₀ _ (ho g φ hφ).1)
  rw [show (actB (cA σ) (liftU hB g) (w.map (tensAt E v))).map (compFin F E v) = actB (cV σ v) g w by
    rw [actB, Matrix.map_mul, comp_up, Matrix.transpose_map, liftU_val, comp_liftM, actB]] at a2
  refine tens_inj (h₀ φ hφ).1 h₁ ?_
  rw [← a2, ← (ho g φ hφ).2 r₀ (h₀ φ hφ), ← (ho g _ m1).2 r₀ (h₀ _ m1), ← a1]
  exact hs.impl _ _ _ (h₀ φ hφ).2

omit [DecidableEq α] in
theorem siegel_loc (hB : JB.map (compFin F E v) = JBv) (h : IsLocD co dv) (ho : IsLocOm v (om.comp (liftU hB)) omv)
    {χ : Chr F E} {Cy : Matrix β ν (AE F E)} (hr : SiegelRule (cA σ) (adeleClass F) ψ (-1) JA JB co χ Cy om)
    {L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hL : L ∈ (adeleClass F).adm κ)
    (hi : ∀ z : Matrix α ν (AE F E), ∀ Φ ∈ schA F κ, L (co.rho ψ (z * Cyᵀ) Φ) = L Φ) (h0 : ∃ Φ ∈ schA F κ, L Φ ≠ 0) :
    SiegelRule (cV σ v) (sbClass (Fv F v)) (GlobalTheory.VacAny.psiV ψ v) (-1) JAv JBv dv (locChr v χ)
      (Cy.map (compFin F E v)) omv := by
  intro lv _ hv p t hp φ hφ
  obtain ⟨l, hl, hli, r, c, hc, hR, hlr⟩ := exists_form (v := v) (ψ := ψ)
    (Set.range fun z : Matrix α ν (AE F E) => co.e (z * Cyᵀ))
    (by rintro _ ⟨z, rfl⟩; exact ⟨(1 - atPlace v (1 : Fv F v)) • z, by simp only [Matrix.smul_mul, map_smul]⟩) hL
    (by rintro _ ⟨z, rfl⟩; exact hi z) h0 lv (by
      rintro _ ⟨z, rfl⟩ φ hφ
      have := hv (z.map (compFin F E v)) φ hφ
      rwa [Darboux.rho, ← Matrix.transpose_map, ← Matrix.map_mul, h] at this)
  have key := hr l hl (fun z => hli _ ⟨z, rfl⟩) (liftU hB p) (Units.map (liftM E v ν) t) (extM v
    (by
      change (liftM E v β _ * Cy).map _ = (Cy * liftM E v ν _).map _
      rw [Matrix.map_mul, Matrix.map_mul, comp_liftM, comp_liftM]; exact hp)
    (by
      change (liftM E v β _ * Cy).map _ = (Cy * liftM E v ν _).map _
      rw [Matrix.map_mul, Matrix.map_mul, aw_liftM, aw_liftM, Matrix.one_mul, Matrix.mul_one])) _ (hR φ hφ).2
  have ed : Matrix.GeneralLinearGroup.det (Units.map (liftM E v ν) t) =
      Units.map (liftE E v) (Matrix.GeneralLinearGroup.det t) := Units.ext (det_liftM v _)
  have em : ∀ y : (Ev E v)ˣ,
      (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Units.map (liftE E v) y)) : NNReal) : ℝ) =
      ((sbClass (Fv F v)).modu (Units.map (Algebra.norm (Fv F v) : Ev E v →* Fv F v) y) : NNReal) :=
    fun y => modu_single _ _ (norm_liftE v _)
  have a := (ho p φ hφ).2 r (hR φ hφ)
  rw [MonoidHom.comp_apply] at a
  rw [ed, em, a, hlr, hlr, mul_left_comm] at key
  exact mul_left_cancel₀ hc key

omit [NumberField E] [LocallyCompactSpace (Fv F v)] [Fintype β] [DecidableEq β] in
theorem comp_dbl (hB : JB.map (compFin F E v) = JBv) : (dbl JB).map (compFin F E v) = dbl JBv := by
  rw [dbl, dbl, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), hB]

omit [DecidableEq α] in
theorem dbl_loc (hψ : IsStd ψ) (hA : JA.map (compFin F E v) = JAv) (hB : JB.map (compFin F E v) = JBv) (h : IsLocD co dv)
    (ho : IsLocOm v (om.comp (liftU hB)) omv) {χ : Chr F E}
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)}
    {omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)} (hdd : IsDblCoord (cA σ) (-1) JA JB co dd)
    (hsd : IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (hr : SiegelRule (cA σ) (adeleClass F) ψ (-1) JA (dbl JB) dd χ (diagCols β) omd)
    (hbox : ∀ (g : UG (cA σ) JB) (gd : UG (cA σ) (dbl JB)), gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂) :
    ∃ ddv omdv, IsLocOm v (omd.comp (liftU (comp_dbl hB))) omdv ∧ IsDblCoord (cV σ v) (-1) JAv JBv dv ddv ∧
      IsSplitting (sbClass (Fv F v)) (GlobalTheory.VacAny.psiV ψ v) ddv (actB (cV σ v)) omdv ∧
      SiegelRule (cV σ v) (sbClass (Fv F v)) (GlobalTheory.VacAny.psiV ψ v) (-1) JAv (dbl JBv) ddv (locChr v χ) (diagCols β) omdv ∧
      ∀ (g : UG (cV σ v) JBv) (gd : UG (cV σ v) (dbl JBv)), gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
        ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), omdv gd (boxFun φ₁ φ₂) = boxFun (omv g φ₁) φ₂ := by
  have hD := comp_dbl hB
  obtain ⟨ddv, hd⟩ := exists_locD hA hD dd
  obtain ⟨omdv, hod⟩ := exists_locOm' (v := v) hψ hsd (liftU hD) fun g u hu => mul_lift_away hu _
  refine ⟨ddv, omdv, hod, fun w₁ w₂ => ?_, split_loc hψ hD hd hsd hod, ?_, fun g gd hg φ₁ h₁ φ₂ h₂ => ?_⟩
  · rw [← comp_up v w₁, ← comp_up v w₂, ← Matrix.fromCols_map, hd, h, h, hdd]
    refine Prod.ext (funext ?_) (funext ?_) <;> rintro (i | i)
    · rfl
    · rfl
    · rfl
    · exact map_neg (evFin F v) _
  · obtain ⟨L, hL, hi, φ, -, r, hr1, -, hne⟩ := PositivityTheory.KCo.adjoint_statement.diag F κ ψ v
    have := siegel_loc hD hd hod hr hL (fun z Φ hΦ => by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one, Darboux.rho, hdd]
      exact hi _ _ Φ hΦ) ⟨_, GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hr1.2 _ hr1.2, hne⟩
    rwa [diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)] at this
  · obtain ⟨r₀, x₀, h₀, hx⟩ := exists_base κ v
    have tb : ∀ a b : (κ → Fv F v) → ℂ, tens (evFin F v) (boxFun a b) (boxFun r₀ r₀) =
        boxFun (tens (evFin F v) a r₀) (tens (evFin F v) b r₀) := fun a b => funext fun x => mul_mul_mul_comm _ _ _ _
    have hi : ∀ x z : κ ⊕ κ → AF F, At (evFin F v) z → boxFun r₀ r₀ (x + z) = boxFun r₀ r₀ x := fun x z hz =>
      congrArg₂ (· * ·) ((h₀ φ₁ h₁).1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => funext fun i => congrFun (hz u hu) _)
        ((h₀ φ₁ h₁).1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => funext fun i => congrFun (hz u hu) _)
    refine tens_inj hi (x₀ := Sum.elim x₀ x₀) (by simp [boxFun, hx]) ?_
    rw [← (hod gd _ (GlobalTheory.CompanionTheory.VacDbl.boxFun_mem_SB h₁ h₂)).2 _
      ⟨hi, tb φ₁ φ₂ ▸ GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ (h₀ φ₁ h₁).2 _ (h₀ φ₂ h₂).2⟩, tb, tb,
      ← (ho g φ₁ h₁).2 r₀ (h₀ φ₁ h₁)]
    refine hbox (liftU hB g) (liftU hD gd) (extM v ?_ ?_) _ (h₀ φ₁ h₁).2 _ (h₀ φ₂ h₂).2
    · rw [liftU_val, liftU_val, comp_liftM, Matrix.fromBlocks_map, comp_liftM, Matrix.map_zero _ (map_zero _),
        Matrix.map_one _ (map_zero _) (map_one _), hg]
    · rw [liftU_val, liftU_val, aw_liftM, Matrix.fromBlocks_map, aw_liftM, Matrix.map_zero _ (map_zero _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.fromBlocks_one]

omit [DecidableEq α] in
theorem weilB_loc (hψ : IsStd ψ) (hA : JA.map (compFin F E v) = JAv) (hB : JB.map (compFin F E v) = JBv) (h : IsLocD co dv)
    (ho : IsLocOm v (om.comp (liftU hB)) omv) {χ : Chr F E} (hw : IsWeilB (cA σ) (adeleClass F) ψ (-1) JA JB co χ om) :
    IsWeilB (cV σ v) (sbClass (Fv F v)) (GlobalTheory.VacAny.psiV ψ v) (-1) JAv JBv dv (locChr v χ) omv := by
  obtain ⟨hs, dd, omd, hdd, hsd, hr, hbox⟩ := hw
  obtain ⟨ddv, omdv, -, h1⟩ := dbl_loc hψ hA hB h ho hdd hsd hr hbox
  exact ⟨split_loc hψ hB h hs ho, ddv, omdv, h1⟩

omit [NumberField E] [LocallyCompactSpace (Fv F v)] in
theorem comp_incM {a b : Type} (J : Matrix a b E) : (incM F J).map (compFin F E v) = locM J v :=
  Matrix.ext fun i j => congrArg (· ⊗ₜ[F] J i j) (map_one (evFin F v))

omit [LocallyCompactSpace (Fv F v)] in
theorem IsLocOm.comp {G H : Type} [Monoid G] [Monoid H] {om : G →* Module.End ℂ ((κ → AF F) → ℂ)}
    {omv : G →* Module.End ℂ ((κ → Fv F v) → ℂ)} (ho : IsLocOm v om omv) (f : H →* G)
    {om' : H →* Module.End ℂ ((κ → AF F) → ℂ)} (e : ∀ g, om' g = om (f g)) : IsLocOm v om' (omv.comp f) :=
  fun g φ hφ => e g ▸ ho (f g) φ hφ

theorem locPair_core {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {om : Rep σ X W} {χX χW : Chr F E}
    (hψ : IsStd ψ) (hw : M.IsWeil ψ χX χW om) :
    ∃ dv omv, IsLocD M.co dv ∧ IsLocOm v (om.comp ((liftU (comp_incM X.J)).prodMap (liftU (comp_incM W.J)))) omv ∧
      IsLocOm v ((om.comp (MonoidHom.inr _ _)).comp (liftU (comp_incM W.J))) (omv.comp (MonoidHom.inr _ _)) ∧
      IsLocOm v ((om.comp (MonoidHom.inl _ _)).comp (liftU (comp_incM X.J))) (omv.comp (MonoidHom.inl _ _)) ∧
      IsLocPair M ψ χX χW om v (GlobalTheory.VacAny.psiV ψ v) dv (locChr v χX) (locChr v χW) omv := by
  have hA := comp_incM (F := F) (v := v) X.J
  have hB := comp_incM (F := F) (v := v) W.J
  obtain ⟨dv, hd⟩ := exists_locD hA hB M.co
  obtain ⟨omv, ho⟩ := exists_locOm' (v := v) hψ (IsUWeilPair.isUSplitting hw).toIsSplitting
    ((liftU hA).prodMap (liftU hB)) fun g u hu => by
      change liftM E v _ _ * u * (liftM E v _ _)ᵀ = u
      rw [lift_mul_away hu, mul_lift_away hu]
  obtain ⟨w1, d', hd', w2⟩ := IsUWeilPair.isWeilPair hw
  obtain ⟨dv', hdv'⟩ := exists_locD hB hA d'
  have o1 : IsLocOm v ((om.comp (MonoidHom.inr _ _)).comp (liftU hB)) (omv.comp (MonoidHom.inr _ _)) :=
    ho.comp _ fun g => congrArg om (Prod.ext (map_one (liftU hA)).symm rfl)
  have o2 : IsLocOm v ((om.comp (MonoidHom.inl _ _)).comp (liftU hA)) (omv.comp (MonoidHom.inl _ _)) :=
    ho.comp _ fun g => congrArg om (Prod.ext rfl (map_one (liftU hB)).symm)
  refine ⟨dv, omv, hd, ho, o1, o2, fun _ => rfl, isLocChar v _, isLocChar v _,
    ⟨weilB_loc hψ hA hB hd o1 w1, dv', fun x => ?_, weilB_loc hψ hB hA hdv' o2 w2⟩,
    fun u hu φ _ => acts_rho hd _ hu φ, fun g => ⟨liftU hA g, at_liftM v _, comp_liftM v _⟩,
    fun g => ⟨liftU hB g, at_liftM v _, comp_liftM v _⟩, fun g hg h hh => ?_⟩
  · rw [← comp_up v x, ← Matrix.transpose_map, hdv', hd, hd']
  · obtain ⟨gv, rfl⟩ := exists_liftU hA g hg
    obtain ⟨hv, rfl⟩ := exists_liftU hB h hh
    obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
    refine ⟨gv, hv, comp_liftM v _, comp_liftM v _, fun φ hφ φ₁ => ⟨fun A => ?_, fun e => e ▸ (ho (gv, hv) φ hφ).2⟩⟩
    exact (eq_of_acts v h₁ (h₀ φ hφ) A).trans (eq_of_acts v h₁ (h₀ φ hφ) (ho (gv, hv) φ hφ).2).symm

theorem locPairEx : LocPairEx := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hP hw v _ i2
  obtain rfl : i2 = GlobalTheory.VacAny.invTwoV v := Subsingleton.elim _ _
  obtain ⟨dv, omv, -, -, -, -, h⟩ := locPair_core (v := v) hP.base.std hw
  exact ⟨_, dv, _, _, omv, h⟩

end PositivityTheory.ThKH.Locpair
