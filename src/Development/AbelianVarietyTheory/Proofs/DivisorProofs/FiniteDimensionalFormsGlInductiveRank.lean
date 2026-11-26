module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLTameOfFinitenessAtRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLTameOfFinitenessAtRank
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology GlobalTheory.HCF

namespace GlobalTheory.AutGrowth.RankLocal

open GlobalTheory.AutGrowth.KilledFin GlobalTheory.AutGrowth.SmoothFinite

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem finite_forms (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W)
    (c : (E →+* ℂ) → ℂ → ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L ρ c)) := by
  classical
  haveI hW' : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := GlobalTheory.T.finiteDimensional_matrixCoefficientSpan _ W ρ
  let χ : Module.End ℂ (Sm E a) → ℂ := fun z =>
    if hz : ∃ s : ℂ, ∀ φ : Sm E a, (∀ τ u, cap τ u φ = c τ u • φ) → z φ = s • φ then hz.choose else 0
  have hsub : GlobalTheory.Published.AutFinGL.forms L ρ c ⊆ formsGL E a L (GlobalTheory.Published.AutFin.coeffSpan ρ) {χ} 1 := by
    rintro φ ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, χ, rfl, ?_⟩
    intro zs hlen hzs
    match zs, hlen with
    | [z], _ =>
      have hz : z ∈ Zalg E a := hzs z (List.mem_singleton_self z)
      have hex := GlobalTheory.T.center_acts_by_scalar_on_eigenforms E a c z hz
      have hχ : χ z = hex.choose := dif_pos hex
      simp only [List.foldr_cons, List.foldr_nil]
      rw [hχ, hex.choose_spec φ h4, sub_self]
  have hfin := h L hL (GlobalTheory.Published.AutFin.coeffSpan ρ) hW' {χ} (Set.finite_singleton χ) 1
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

theorem finiteDimensional_capEigen_maps_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (L : Subgroup (GL (Fin a) (Af E))) (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) (hWf : FiniteDimensional ℂ W)
    (c : (E →+* ℂ) → ℂ → ℂ) (N : Submodule ℂ (W →ₗ[ℂ] Sm E a)) (hN : N ≤ maps L W hW)
    (hcap : ∀ T ∈ N, ∀ τ u, cap τ u ∘ₗ T = c τ u • T) : FiniteDimensional ℂ N := by
  haveI := hWf
  have hF := finite_forms h L hL W (GlobalTheory.PRep.sub (cptRep E a) W hW) c
  haveI := hF
  have hmem : ∀ T ∈ N, ∀ w, T w ∈ GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c := by
    intro T hT w
    have hm : (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
        ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧
          ∀ k ∈ L, finRep E a k (T w) = T w := hN hT
    obtain ⟨heq, hall⟩ := hm
    obtain ⟨htame, hleft, hfix⟩ := hall w
    have hZ : ∀ z ∈ Zalg E a, ∃ s : ℂ, z ∘ₗ T = s • T := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact ⟨c τ u, hcap T hT τ u⟩
      | algebraMap r => exact ⟨r, LinearMap.ext fun v => by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨s + t, by rw [LinearMap.add_comp, hs, ht, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨t * s, by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ht, LinearMap.comp_smul, hs, smul_smul]⟩
    refine ⟨⟨hleft, ?_, ?_, ?_, ?_⟩, hfix, GlobalTheory.Published.AutFinGL.type_of_map _ T heq w, fun τ u => ?_⟩
    · exact isOpen_stab_of_mem_nhds (finRep E a) (T w)
        (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
    · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, heq k w⟩
    · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {T w}) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs⟩ := hZ z hz
      have e : z (T w) = s • T w := LinearMap.congr_fun hs w
      show z (T w) ∈ _
      rw [e]
      exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
    · exact growth_of_tame htame
    · exact LinearMap.congr_fun (hcap T hT τ u) w
  let Φ : N →ₗ[ℂ] (W →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c)) :=
    { toFun := fun T => LinearMap.codRestrict _ T.1 fun w => Submodule.subset_span (hmem T.1 T.2 w)
      map_add' := fun T T' => LinearMap.ext fun w => rfl
      map_smul' := fun r T => LinearMap.ext fun w => rfl }
  have hinj : Function.Injective Φ := fun T T' h =>
    Subtype.ext (LinearMap.ext fun w => congrArg Subtype.val (LinearMap.congr_fun h w))
  exact Module.Finite.of_injective Φ hinj

theorem finiteDimensional_mapsJ_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (φ : Sm E a) (hφ : IsAutForm φ) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) : FiniteDimensional ℂ (mapsJ φ L) := by
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := a) τ u ∈ Zalg E a := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let S : Set (Module.End ℂ (mapsJ φ L)) := {s | ∃ τ u, s = postZ φ L (cap τ u) (hcap τ u)}
  refine GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen (mapsJ φ L) S ?_ ?_ ?_
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨τ', u', rfl⟩
    refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
    show cap τ u (cap τ' u' (T.1 w)) = cap τ' u' (cap τ u (T.1 w))
    rw [← Module.End.mul_apply, (Zalg_commute (hcap τ u) (hcap τ' u')).eq, Module.End.mul_apply]
  · let ev : Zalg E a →ₗ[ℂ] Sm E a := (LinearMap.applyₗ φ).comp (Zalg E a).val.toLinearMap
    have hker : LinearMap.ker ev ≤ LinearMap.ker (postZAlg φ L).toLinearMap := by
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.2 z.1 z.2 hz w
    have hev : FiniteDimensional ℂ (LinearMap.range ev) := by
      have h1 : LinearMap.range ev ≤
          Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) := by
        rintro _ ⟨z, rfl⟩
        exact Submodule.subset_span ⟨z.1, z.2, rfl⟩
      haveI := hφ.zfin
      exact Submodule.finiteDimensional_of_le h1
    refine fd_adjoin_of_ker_le (mapsJ φ L) (Zalg E a) (Sm E a) (postZAlg φ L) ev hev hker S ?_
    rintro _ ⟨τ, u, rfl⟩
    exact ⟨⟨cap τ u, hcap τ u⟩, rfl⟩
  · intro c
    let J := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s))
    let N : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) := J.map (mapsJ φ L).subtype
    have hNle : N ≤ maps L (spanK E a φ) (spanK_stable φ) := by
      rintro _ ⟨T, _, rfl⟩
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.1
    have hNe : ∀ T ∈ N, ∀ (τ : E →+* ℂ) (u : ℂ),
        cap τ u ∘ₗ T = c (postZ φ L (cap τ u) (hcap τ u)) • T := by
      rintro _ ⟨T, hT, rfl⟩ τ u
      have hT' : T ∈ ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s)) := hT
      have h₀ := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hT' (postZ φ L (cap τ u) (hcap τ u))) ⟨τ, u, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h₀
      exact congrArg Subtype.val h₀
    have hN : FiniteDimensional ℂ N :=
      finiteDimensional_capEigen_maps_rank h L hL (spanK E a φ) (spanK_stable φ) hφ.kfin
        (fun τ u => c (postZ φ L (cap τ u) (hcap τ u))) N hNle hNe
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective (mapsJ φ L).subtype Subtype.val_injective J).symm

theorem exists_finite_space_rank (h : ∀ (L' : Subgroup (GL (Fin a) (Af E))), IsOpen (L' : Set (GL (Fin a) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E a) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L' W' X' N')))
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a) (hφ : IsAutForm φ) :
    ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α →
      ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  let w0 : spanK E a φ := ⟨φ, self_mem_spanK φ⟩
  haveI := finiteDimensional_mapsJ_rank h φ hφ (stabL φ) hφ.level
  refine ⟨(mapsJ φ (stabL φ)).map (LinearMap.applyₗ w0), inferInstance, ?_, fun α hα hK =>
    ⟨GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα φ.1 φ.2, smoothMap ν hα _, smoothMap_mem ν hα hK hφ, rfl⟩⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (hT.1.2 w0).1

theorem tame_of_autForm_rank : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ),
    (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) →
      ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' →
      ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) →
    ∀ φ : Sm E n, IsAutForm φ → φ ∈ GlobalTheory.AutGrowth.tame E n := by
  intro E _ _ _ a hfin φ hφ
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, hVt, hV⟩ := exists_finite_space_rank hfin ν φ hφ
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨_, hv, rfl⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  obtain ⟨ψ, hψ, e⟩ := hφ'
  have e' : ψ = φ := Subtype.ext e
  exact hVt (e' ▸ hψ)

end GlobalTheory.AutGrowth.RankLocal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLTameOfFinitenessAtRankStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_GL_tame_of_finiteness_at_rank : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ φ : Sm E n, IsAutForm φ → φ ∈ GlobalTheory.AutGrowth.tame E n := by
  first | exact @GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank | exact GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank | (intros; apply GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlInductiveRank
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

noncomputable section

namespace GlobalTheory.CentreInherit

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

def stab (φ : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {k | finRep E n k φ = φ}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem ktype_of_central {ψ : Sm E n} (hk : FiniteDimensional ℂ (spanK E n ψ)) {z : Module.End ℂ (Sm E n)}
    (hz : z ∈ Zalg E n) (W' : Submodule ℂ (Kinf E n → ℂ))
    (hW : ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') (g : GA E n) :
    (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) ∈ W' := by
  let S := spanK E n ψ
  let ev : GA E n → Module.Dual ℂ S := fun h => (LinearMap.proj h).comp ((Sm E n).subtype.comp S.subtype)
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ h, v.1.1 h = 0 := fun h => hv _ (Submodule.subset_span ⟨h, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (Subtype.ext (funext h2))
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  have hmem : ∀ k, cptRep E n k ψ ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have key : ∀ m ∈ Submodule.span ℂ (Set.range ev), (fun k => m ⟨cptRep E n k ψ, hmem k⟩) ∈ W' := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx => obtain ⟨h, rfl⟩ := hx; exact hW h
    | zero => exact W'.zero_mem
    | add x y _ _ hx hy => exact W'.add_mem hx hy
    | smul c x _ hx => exact W'.smul_mem c hx
  let ℓ : Module.Dual ℂ S := (LinearMap.proj g).comp ((Sm E n).subtype.comp (z.comp S.subtype))
  have e : (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) = fun k => ℓ ⟨cptRep E n k ψ, hmem k⟩ := by
    funext k
    have h1 := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E n k z hz) ψ
    simp only [Module.End.mul_apply] at h1
    show _ = (z (cptRep E n k ψ)).1 g
    rw [h1]
  rw [e]
  exact key ℓ (hspan ▸ Submodule.mem_top)

theorem central_of_tame {ψ : Sm E n} (hA : IsAutForm ψ) (htame : ψ ∈ tame E n) {z : Module.End ℂ (Sm E n)}
    (hz : z ∈ Zalg E n) (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ))
    (hL : ∀ k ∈ L', finRep E n k ψ = ψ) (hW : ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') :
    IsAutForm (z ψ) ∧ (∀ k ∈ L', finRep E n k (z ψ) = z ψ) ∧
      ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k (z ψ)).1 g) ∈ W' := by
  have hs : z ψ ∈ fixL E n (stab ψ) :=
    Zalg_stable (V := fixL E n (stab ψ)) (fun X _ h => lie_mem_fixL _ X h) hz ψ (fun k hk => hk)
  refine ⟨⟨Zalg_stable (V := leftInv E n) (fun X _ h => lie_mem_leftInv X h) hz ψ hA.left, ?_, ?_, ?_,
    growth_of_tame (Zalg_stable (V := tame E n) (fun X _ h => lie_mem_tame X h) hz ψ htame)⟩,
    Zalg_stable (V := fixL E n L') (fun X _ h => lie_mem_fixL L' X h) hz ψ hL,
    ktype_of_central hA.kfin hz W' hW⟩
  · exact isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hA.level.mem_nhds (by simp)) fun k hk => hs k hk)
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E n k ψ)).map z)
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    have h1 := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E n k z hz) ψ
    simpa only [Module.End.mul_apply] using h1
  · have := hA.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun y : Module.End ℂ (Sm E n) => y ψ) '' Zalg E n)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z', hz', rfl⟩
    exact Submodule.subset_span ⟨z' * z, mul_mem hz' hz, rfl⟩

end GlobalTheory.CentreInherit

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.CentreInherit

theorem centre_preserves_forms : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ)) (ψ : Sm E n), IsAutForm ψ → (∀ k ∈ L', finRep E n k ψ = ψ) → (∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') → ∀ ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E n) => z ψ) '' Zalg E n), IsAutForm ψ' ∧ (∀ k ∈ L', finRep E n k ψ' = ψ') ∧ ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ').1 g) ∈ W' := by
  intro E _ _ _ n hH L' W' ψ hA hL hW ψ' hψ'
  have htame : ψ ∈ tame E n := GlobalTheory.T.automorphicForm_GL_tame_of_finiteness_at_rank E n hH ψ hA
  induction hψ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact central_of_tame hA htame hz L' W' hL hW
  | zero => exact ⟨GlobalTheory.HCF.FormsSub.isAutForm_zero, fun k _ => map_zero _, fun g => by
      convert W'.zero_mem using 1; funext k; simp⟩
  | add x y _ _ hx hy =>
    refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_add hx.1 hy.1, fun k hk => by rw [map_add (f := _), hx.2.1 k hk, hy.2.1 k hk],
      fun g => ?_⟩
    convert W'.add_mem (hx.2.2 g) (hy.2.2 g) using 1
    funext k; simp [map_add (f := _)]
  | smul c x _ hx =>
    refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_smul c hx.1, fun k hk => by rw [map_smul, hx.2.1 k hk], fun g => ?_⟩
    convert W'.smul_mem c (hx.2.2 g) using 1
    funext k; simp [map_smul]

end GlobalTheory.CentreInherit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlInductiveRankStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_forms_gl_inductive_rank : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ (L' : Subgroup (GL (Fin n) (Af E))) (W' : Submodule ℂ (Kinf E n → ℂ)) (ψ : Sm E n), IsAutForm ψ → (∀ k ∈ L', finRep E n k ψ = ψ) → (∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ).1 g) ∈ W') → ∀ ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E n) => z ψ) '' Zalg E n), IsAutForm ψ' ∧ (∀ k ∈ L', finRep E n k ψ' = ψ') ∧ ∀ g : GA E n, (fun k : Kinf E n => (cptRep E n k ψ').1 g) ∈ W' := by
  first | exact @GlobalTheory.CentreInherit.centre_preserves_forms | exact GlobalTheory.CentreInherit.centre_preserves_forms | (intros; apply GlobalTheory.CentreInherit.centre_preserves_forms <;> assumption)
end
