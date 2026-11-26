module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfPureTensorsOfFactorGenerators

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OperatorStablePiTensorPureKernelSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OperatorStablePiTensorPureKernelSpan
open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem _root_.GlobalTheory.TensHead.stab_piOps_piKer {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i))
    (h : ∀ i, _root_.GlobalTheory.TensHead.Stab (Op i) (K i)) :
    _root_.GlobalTheory.TensHead.Stab (_root_.GlobalTheory.TensHead.piOps Op) (_root_.GlobalTheory.TensHead.piKer K) := by
  unfold _root_.GlobalTheory.TensHead.Stab at h ⊢
  rintro _ ⟨i, g, hg, rfl⟩ x hx
  unfold _root_.GlobalTheory.TensHead.piKer at hx ⊢
  have hle : Submodule.span ℂ {t | ∃ y : ∀ j, M j, (∃ j, y j ∈ K j) ∧ t = PiTensorProduct.tprod ℂ y}
      ≤ (Submodule.span ℂ {t | ∃ y : ∀ j, M j, (∃ j, y j ∈ K j) ∧ t = PiTensorProduct.tprod ℂ y}).comap
        (_root_.GlobalTheory.TensHead.piOp i g) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, ⟨j, hj⟩, rfl⟩
    refine Submodule.subset_span ⟨fun k => Function.update (fun _ => LinearMap.id) i g k (y k), ⟨j, ?_⟩, ?_⟩
    · by_cases hji : j = i
      · subst hji
        simpa using h j g hg _ hj
      · simpa [Function.update_of_ne hji] using hj
    · simp [_root_.GlobalTheory.TensHead.piOp]
  exact hle hx

end GlobalTheory.TensHead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OperatorStablePiTensorPureKernelSpanStatement
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorStable_piTensorPureKernelSpan : ∀ {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  first | exact @GlobalTheory.TensHead.stab_piOps_piKer | exact GlobalTheory.TensHead.stab_piOps_piKer | (intros; apply GlobalTheory.TensHead.stab_piOps_piKer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmodulePiTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmodulePiTensor
open scoped TensorProduct

namespace GlobalTheory.PiSimple

open GlobalTheory.TensHead

theorem simpleOver_of_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (e : V ≃ₗ[ℂ] W) (G : Set (Module.End ℂ V)) (G' : Set (Module.End ℂ W))
    (K : Submodule ℂ V) (K' : Submodule ℂ W) (hK : K.map (e : V →ₗ[ℂ] W) = K')
    (hG : ∀ g' ∈ G', ∃ g ∈ G, ∀ x, g' (e x) = e (g x)) (h : SimpleOver G' K') :
    SimpleOver G K := by
  intro N hN hKN
  have hs : Stab G' (N.map (e : V →ₗ[ℂ] W)) := by
    rintro g' hg' _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg, hc⟩ := hG g' hg'
    exact ⟨g x, hN g hg x hx, by simpa using (hc x).symm⟩
  have hle : K' ≤ N.map (e : V →ₗ[ℂ] W) := hK ▸ Submodule.map_mono hKN
  have key : ∀ P : Submodule ℂ V, (P.map (e : V →ₗ[ℂ] W)).comap (e : V →ₗ[ℂ] W) = P := by
    intro P; ext x; simp
  rcases h _ hs hle with h1 | h1
  · left
    have := congrArg (Submodule.comap (e : V →ₗ[ℂ] W)) h1
    rwa [← hK, key, key] at this
  · right
    have := congrArg (Submodule.comap (e : V →ₗ[ℂ] W)) h1
    rwa [key, Submodule.comap_top] at this

def PP (σ : Type) : Prop :=
  ∀ [DecidableEq σ] (M : σ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, Stab (Op i) (K i)) →
    (∀ i, SimpleOver (Op i) (K i)) → SimpleOver (piOps Op) (piKer K)

theorem pp_empty : PP PEmpty := by
  intro _ M _ _ Op K _ _ _
  refine simpleOver_of_equiv (PiTensorProduct.isEmptyEquiv PEmpty) _ (∅ : Set (Module.End ℂ ℂ))
    _ ⊥ ?_ (by simp) ?_
  · have : piKer K = ⊥ := by
      rw [piKer, Submodule.span_eq_bot]
      rintro _ ⟨y, ⟨i, _⟩, _⟩
      exact i.elim
    rw [this, Submodule.map_bot]
  · intro N _ _
    rcases Ideal.eq_bot_or_top (N : Ideal ℂ) with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem pp_unit : PP PUnit := by
  intro _ M _ _ Op K _ _ hso
  let e := PiTensorProduct.subsingletonEquiv (R := ℂ) (s := M) PUnit.unit
  refine simpleOver_of_equiv e _ (Op PUnit.unit) _ (K PUnit.unit) ?_ ?_ (hso _)
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      cases i
      simpa [e] using hi
    · intro x hx
      refine ⟨e.symm x, Submodule.subset_span ⟨_, ⟨PUnit.unit, by simpa using hx⟩, rfl⟩, by simp⟩
  · intro g hg
    refine ⟨piOp PUnit.unit g, ⟨PUnit.unit, g, hg, rfl⟩, fun x => ?_⟩
    have H : g ∘ₗ (e : _ →ₗ[ℂ] M PUnit.unit) = (e : _ →ₗ[ℂ] M PUnit.unit) ∘ₗ piOp PUnit.unit g := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro y
      simp [e, piOp, PiTensorProduct.map_tprod]
    exact LinearMap.congr_fun H x

theorem pp_of_equiv {σ ι : Type} (f : σ ≃ ι) (hσ : PP σ) : PP ι := by
  intro _ M _ _ Op K hr hs hso
  classical
  have H := hσ (fun s => M (f s)) (fun s => Op (f s)) (fun s => K (f s)) (fun s => hr _)
    (fun s => hs _) (fun s => hso _)
  refine simpleOver_of_equiv (PiTensorProduct.reindex ℂ M f.symm) _ _ _ _ ?_ ?_ H
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      obtain ⟨s, rfl⟩ := f.surjective i
      exact Submodule.subset_span ⟨fun s => y (f s), ⟨s, hi⟩, by simp⟩
    · rw [piKer, Submodule.span_le]
      rintro _ ⟨z, ⟨s, hz⟩, rfl⟩
      refine ⟨PiTensorProduct.tprod ℂ (Equiv.piCongrLeft M f z),
        Submodule.subset_span ⟨_, ⟨f s, by simpa using hz⟩, rfl⟩, ?_⟩
      simp
  · rintro _ ⟨s, g, hg, rfl⟩
    refine ⟨piOp (f s) g, ⟨f s, g, hg, rfl⟩, fun x => ?_⟩
    have hu : (Function.update (fun j => (LinearMap.id : M (f j) →ₗ[ℂ] M (f j))) s g) =
        fun j => Function.update (fun i => (LinearMap.id : M i →ₗ[ℂ] M i)) (f s) g (f.symm.symm j) := by
      funext j
      by_cases h : j = s
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact (Function.update_of_ne (β := fun i => M i →ₗ[ℂ] M i) (a := f j) (a' := f s)
          (fun h' => h (f.injective h')) g (fun i => LinearMap.id)).symm
    simp only [piOp, LinearEquiv.coe_coe]
    rw [hu, PiTensorProduct.map_reindex]

theorem simpleOver_sum {α β : Type} (hα : PP α) (hβ : PP β) [DecidableEq (α ⊕ β)]
    (N : α ⊕ β → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    (Op : ∀ i, Set (Module.End ℂ (N i))) (K : ∀ i, Submodule ℂ (N i))
    (hr : ∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0)
    (hrl : Module.rank ℂ (⨂[ℂ] a, N (.inl a)) ≤ Cardinal.aleph0)
    (hs : ∀ i, Stab (Op i) (K i)) (hso : ∀ i, SimpleOver (Op i) (K i)) :
    SimpleOver (piOps Op) (piKer K) := by
  classical
  have hA := hα (fun a => N (.inl a)) (fun a => Op (.inl a)) (fun a => K (.inl a))
    (fun a => hr _) (fun a => hs _) (fun a => hso _)
  have hB := hβ (fun b => N (.inr b)) (fun b => Op (.inr b)) (fun b => K (.inr b))
    (fun b => hr _) (fun b => hs _) (fun b => hso _)
  have hT := GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan (piOps (fun a => Op (.inl a))) (piOps (fun b => Op (.inr b)))
    (piKer (fun a => K (.inl a))) (piKer (fun b => K (.inr b))) hrl
    (GlobalTheory.T.operatorStable_piTensorPureKernelSpan _ _ (fun a => hs _)) (GlobalTheory.T.operatorStable_piTensorPureKernelSpan _ _ (fun b => hs _)) hA hB
  let e := (PiTensorProduct.tmulEquivDep ℂ N).symm
  refine simpleOver_of_equiv e _ _ _ _ ?_ ?_ hT
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨PiTensorProduct.tprod ℂ (fun a => y (.inl a)),
        PiTensorProduct.tprod ℂ (fun b => y (.inr b)), ?_, by simp [e]⟩
      cases i with
      | inl a => exact Or.inl (Submodule.subset_span ⟨_, ⟨a, hi⟩, rfl⟩)
      | inr b => exact Or.inr (Submodule.subset_span ⟨_, ⟨b, hi⟩, rfl⟩)
    · set Q := (piKer K).map e.toLinearMap with hQ
      have pure : ∀ (y₁ : ∀ a, N (.inl a)) (y₂ : ∀ b, N (.inr b)),
          ((∃ a, y₁ a ∈ K (.inl a)) ∨ (∃ b, y₂ b ∈ K (.inr b))) →
          PiTensorProduct.tprod ℂ y₁ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y₂ ∈ Q := by
        intro y₁ y₂ h
        refine ⟨PiTensorProduct.tprod ℂ (fun i => Sum.rec y₁ y₂ i),
          Submodule.subset_span ⟨_, ?_, rfl⟩, by simp [e]⟩
        rcases h with ⟨a, ha⟩ | ⟨b, hb⟩
        · exact ⟨.inl a, ha⟩
        · exact ⟨.inr b, hb⟩
      have left : ∀ (y₁ : ∀ a, N (.inl a)), (∃ a, y₁ a ∈ K (.inl a)) →
          ∀ z, PiTensorProduct.tprod ℂ y₁ ⊗ₜ[ℂ] z ∈ Q := by
        intro y₁ h z
        have : (⊤ : Submodule ℂ (⨂[ℂ] b, N (.inr b))) ≤
            Q.comap (TensorProduct.mk ℂ _ _ (PiTensorProduct.tprod ℂ y₁)) := by
          rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
          rintro _ ⟨y₂, rfl⟩
          exact pure y₁ y₂ (Or.inl h)
        exact this Submodule.mem_top
      have right : ∀ (y₂ : ∀ b, N (.inr b)), (∃ b, y₂ b ∈ K (.inr b)) →
          ∀ x, x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y₂ ∈ Q := by
        intro y₂ h x
        have : (⊤ : Submodule ℂ (⨂[ℂ] a, N (.inl a))) ≤
            Q.comap ((TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ y₂)) := by
          rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
          rintro _ ⟨y₁, rfl⟩
          exact pure y₁ y₂ (Or.inr h)
        exact this Submodule.mem_top
      rw [tensKer, Submodule.span_le]
      rintro _ ⟨x, z, hxz, rfl⟩
      rcases hxz with hx | hz
      · have : piKer (fun a => K (.inl a)) ≤ Q.comap ((TensorProduct.mk ℂ _ _).flip z) := by
          rw [piKer, Submodule.span_le]
          rintro _ ⟨y₁, h, rfl⟩
          exact left y₁ h z
        exact this hx
      · have : piKer (fun b => K (.inr b)) ≤ Q.comap (TensorProduct.mk ℂ _ _ x) := by
          rw [piKer, Submodule.span_le]
          rintro _ ⟨y₂, h, rfl⟩
          exact right y₂ h x
        exact this hz
  · rintro _ (⟨_, ⟨a, g, hg, rfl⟩, rfl⟩ | ⟨_, ⟨b, g, hg, rfl⟩, rfl⟩)
    · refine ⟨piOp (Sum.inl a) g, ⟨_, g, hg, rfl⟩, fun x => ?_⟩
      have H : (TensorProduct.map (piOp a g) LinearMap.id) ∘ₗ e.toLinearMap =
          e.toLinearMap ∘ₗ piOp (Sum.inl a) g := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro y
        simp only [e, piOp, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, PiTensorProduct.map_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
          TensorProduct.map_tmul, LinearMap.id_apply]
        congr 2
        · funext a'
          by_cases h : a' = a
          · subst h; simp
          · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Sum.inl_injective h'))]
        · funext b'
          rw [Function.update_of_ne (Sum.inr_ne_inl)]
          rfl
      exact LinearMap.congr_fun H x
    · refine ⟨piOp (Sum.inr b) g, ⟨_, g, hg, rfl⟩, fun x => ?_⟩
      have H : (TensorProduct.map LinearMap.id (piOp b g)) ∘ₗ e.toLinearMap =
          e.toLinearMap ∘ₗ piOp (Sum.inr b) g := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro y
        simp only [e, piOp, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, PiTensorProduct.map_tprod, PiTensorProduct.tmulEquivDep_symm_apply,
          TensorProduct.map_tmul, LinearMap.id_apply]
        congr 2
        · funext a'
          rw [Function.update_of_ne (Sum.inl_ne_inr)]
          rfl
        · funext b'
          by_cases h : b' = b
          · subst h; simp
          · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Sum.inr_injective h'))]
      exact LinearMap.congr_fun H x

theorem pp_unit_sum {α : Type} (hα : PP α) : PP (PUnit ⊕ α) := by
  intro _ N _ _ Op K hr hs hso
  refine simpleOver_sum pp_unit hα N Op K hr ?_ hs hso
  rw [(PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun u : PUnit => N (Sum.inl u))
    PUnit.unit).rank_eq]
  exact hr _

theorem pp_option {α : Type} (hα : PP α) : PP (Option α) :=
  pp_of_equiv ((Equiv.optionEquivSumPUnit α).trans (Equiv.sumComm _ _)).symm (pp_unit_sum hα)

theorem pp_finite (σ : Type) [Finite σ] : PP σ :=
  Finite.induction_empty_option (P := PP) (fun f h => pp_of_equiv f h) pp_empty
    (fun h => pp_option h) σ

theorem simpleOver_piKer : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i)))
    (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    (∀ i, GlobalTheory.TensHead.SimpleOver (Op i) (K i)) →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  intro ι _ _ M _ _ Op K hr hs hso
  exact pp_finite ι M Op K hr hs hso

end GlobalTheory.PiSimple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmodulePiTensorStatement
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleOverStableSubmodule_piTensor : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    (∀ i, GlobalTheory.TensHead.SimpleOver (Op i) (K i)) →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  first | exact @GlobalTheory.PiSimple.simpleOver_piKer | exact GlobalTheory.PiSimple.simpleOver_piKer | (intros; apply GlobalTheory.PiSimple.simpleOver_piKer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorMaximalStableContainsSlotKernelStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorMaximalStableContainsFactorKernel
open scoped TensorProduct

namespace GlobalTheory.TensHead

section Quot
variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def quotOp (N : Submodule ℂ V) (f : Module.End ℂ V) : Module.End ℂ (V ⧸ N) := by
  classical
  exact if h : N ≤ N.comap f then N.mapQ N f h else 0

theorem quotOp_mk (N : Submodule ℂ V) (f : Module.End ℂ V) (h : ∀ x ∈ N, f x ∈ N) (x : V) :
    quotOp N f (N.mkQ x) = N.mkQ (f x) := by
  have h' : N ≤ N.comap f := fun x hx => h x hx
  unfold quotOp
  rw [dite_eq_left h']
  simp

theorem quotOp_mul (N : Submodule ℂ V) (f₁ f₂ : Module.End ℂ V) (h₁ : ∀ x ∈ N, f₁ x ∈ N)
    (h₂ : ∀ x ∈ N, f₂ x ∈ N) : quotOp N f₁ * quotOp N f₂ = quotOp N (f₁ * f₂) := by
  have h₁₂ : ∀ x ∈ N, (f₁ * f₂) x ∈ N := fun x hx => h₁ _ (h₂ x hx)
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  rw [quotOp_mk N f₂ h₂, quotOp_mk N f₁ h₁, quotOp_mk N _ h₁₂, Module.End.mul_apply]

end Quot

section Slot
variable {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem piOp_comm (i j : ι) (hij : j ≠ i) (g : Module.End ℂ (M i)) (h : Module.End ℂ (M j)) :
    piOp i g * piOp j h = piOp j h * piOp i g := by
  unfold piOp
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← PiTensorProduct.map_comp,
    ← PiTensorProduct.map_comp]
  congr 1
  funext k
  by_cases hki : k = i
  · subst hki
    simp [Function.update_of_ne hij.symm]
  · by_cases hkj : k = j
    · subst hkj
      simp [Function.update_of_ne hij]
    · simp [Function.update_of_ne hki, Function.update_of_ne hkj]

end Slot

end GlobalTheory.TensHead

namespace GlobalTheory.TensHead

theorem position_mem_of_maximal_stable : ∀ {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i))) (i : ι)
    (Rel K : Submodule ℂ (M i)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ (M i), Rel ≤ N → GlobalTheory.TensHead.Stab (Op i) N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab (Op i) K →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)),
      (∀ x ∈ Rel, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N') →
      GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) U → N' ≤ U →
        U = N' ∨ U = ⊤) →
      ∀ x ∈ K, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N' := by
  intro ι _ M₀ _ _ M _ _ Op₀ Op i Rel K hlen hmax hK hKst N' hRel hN'st hN'max x hx x₀ y
  let φ : M i →ₗ[ℂ] (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) ⧸ N' :=
    N'.mkQ ∘ₗ (TensorProduct.mk ℂ M₀ (⨂[ℂ] j, M j) x₀) ∘ₗ
      ((PiTensorProduct.tprod ℂ : (∀ j, M j) →ₘₗ[ℂ] (⨂[ℂ] j, M j)).toLinearMap y i)
  have hφ : ∀ z, φ z = N'.mkQ (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i z)) := by
    intro z
    simp [φ, MultilinearMap.toLinearMap_apply]
  let act : Module.End ℂ (M i) → Module.End ℂ ((M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) ⧸ N') :=
    fun g => quotOp N' (TensorProduct.map LinearMap.id (piOp i g))
  let B : Set (Module.End ℂ ((M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) ⧸ N')) :=
    quotOp N' '' ({f | ∃ g ∈ Op₀, f = TensorProduct.map g LinearMap.id} ∪
      {f | ∃ j, j ≠ i ∧ ∃ h ∈ Op j, f = TensorProduct.map LinearMap.id (piOp j h)})
  have hst0 : ∀ g ∈ Op₀, ∀ z ∈ N', TensorProduct.map g LinearMap.id z ∈ N' :=
    fun g hg => hN'st _ (Or.inl ⟨g, hg, rfl⟩)
  have hst1 : ∀ j, ∀ h ∈ Op j, ∀ z ∈ N', TensorProduct.map LinearMap.id (piOp j h) z ∈ N' :=
    fun j h hh => hN'st _ (Or.inr ⟨piOp j h, ⟨j, h, hh, rfl⟩, rfl⟩)
  have key := GlobalTheory.T.le_ker_of_local_finite_length_to_simple (Op i) Rel K φ act B hlen hmax hK hKst ?_ ?_ ?_ ?_
  · have h0 := key hx
    rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · intro z hz
    rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hRel z hz x₀ y
  · intro g hg
    ext z
    simp only [LinearMap.comp_apply]
    rw [hφ, hφ, quotOp_mk N' _ (hst1 i g hg), TensorProduct.map_tmul, LinearMap.id_apply,
      piOp_tprod_update]
  · intro g hg b hb
    obtain ⟨f, hf, rfl⟩ := hb
    rcases hf with ⟨g₀, hg₀, rfl⟩ | ⟨j, hji, h, hh, rfl⟩
    · rw [quotOp_mul N' _ _ (hst1 i g hg) (hst0 g₀ hg₀), quotOp_mul N' _ _ (hst0 g₀ hg₀) (hst1 i g hg)]
      congr 1
      simp only [Module.End.mul_eq_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
        LinearMap.comp_id]
    · rw [quotOp_mul N' _ _ (hst1 i g hg) (hst1 j h hh), quotOp_mul N' _ _ (hst1 j h hh) (hst1 i g hg)]
      congr 1
      simp only [Module.End.mul_eq_comp, ← TensorProduct.map_comp, LinearMap.id_comp]
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, piOp_comm i j hji g h]
  · intro U hU
    have hs : U = (U.comap N'.mkQ).map N'.mkQ :=
      (Submodule.map_comap_eq_of_surjective N'.mkQ_surjective U).symm
    have hle : N' ≤ U.comap N'.mkQ := by
      intro z hz
      rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N').mpr hz]
      exact U.zero_mem
    have hstab : Stab (tensOps Op₀ (piOps Op)) (U.comap N'.mkQ) := by
      intro f hf z hz
      rw [Submodule.mem_comap] at hz ⊢
      rw [← quotOp_mk N' f (hN'st f hf)]
      apply hU _ _ _ hz
      rcases hf with ⟨g₀, hg₀, rfl⟩ | ⟨p, ⟨j, h, hh, rfl⟩, rfl⟩
      · exact Or.inr ⟨_, Or.inl ⟨g₀, hg₀, rfl⟩, rfl⟩
      · by_cases hji : j = i
        · subst hji
          exact Or.inl ⟨h, hh, rfl⟩
        · exact Or.inr ⟨_, Or.inr ⟨j, hji, h, hh, rfl⟩, rfl⟩
    rcases hN'max _ hstab hle with h | h
    · left
      rw [hs, h, Submodule.mkQ_map_self]
    · right
      rw [hs, h, Submodule.map_top, Submodule.range_mkQ]

end GlobalTheory.TensHead
end

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensor_maximalStable_contains_positionKernel : ∀ {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i))) (i : ι)
    (Rel K : Submodule ℂ (M i)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ (M i), Rel ≤ N → GlobalTheory.TensHead.Stab (Op i) N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab (Op i) K →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)),
      (∀ x ∈ Rel, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N') →
      GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) U → N' ≤ U →
        U = N' ∨ U = ⊤) →
      ∀ x ∈ K, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N' := by
  first | exact @GlobalTheory.TensHead.position_mem_of_maximal_stable | exact GlobalTheory.TensHead.position_mem_of_maximal_stable | (intros; apply GlobalTheory.TensHead.position_mem_of_maximal_stable <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorMaximalStableContainsLeftKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorMaximalStableContainsLeftKernel
open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem tens_maxStab_contains_left_ker : ∀ {M₀ V : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup V] [Module ℂ V]
    (Op₀ : Set (Module.End ℂ M₀)) (B : Set (Module.End ℂ V)) (Rel₀ K₀ : Submodule ℂ M₀),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → GlobalTheory.TensHead.Stab Op₀ N → N ≠ ⊤ → N ≤ K₀) →
    K₀ ≠ ⊤ → GlobalTheory.TensHead.Stab Op₀ K₀ →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] V),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N') → GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) U → N' ≤ U → U = N' ∨ U = ⊤) →
      ∀ x ∈ K₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N' := by
  classical
  intro M₀ V _ _ _ _ Op₀ B Rel₀ K₀ hlen hmax hK hKs N' hrel hN'st hN'max x hx y

  let act : Module.End ℂ M₀ → Module.End ℂ ((M₀ ⊗[ℂ] V) ⧸ N') := fun g =>
    if hs : N' ≤ N'.comap (TensorProduct.map g LinearMap.id) then
      N'.mapQ N' (TensorProduct.map g LinearMap.id) hs else 0
  let bAct : Module.End ℂ V → Module.End ℂ ((M₀ ⊗[ℂ] V) ⧸ N') := fun h =>
    if hs : N' ≤ N'.comap (TensorProduct.map LinearMap.id h) then
      N'.mapQ N' (TensorProduct.map LinearMap.id h) hs else 0
  have hsg : ∀ g ∈ Op₀, N' ≤ N'.comap (TensorProduct.map g LinearMap.id) := by
    intro g hg z hz
    exact hN'st _ (Or.inl ⟨g, hg, rfl⟩) z hz
  have hsh : ∀ h ∈ B, N' ≤ N'.comap (TensorProduct.map LinearMap.id h) := by
    intro h hh z hz
    exact hN'st _ (Or.inr ⟨h, hh, rfl⟩) z hz
  have hactg : ∀ g ∈ Op₀, ∀ z, act g (N'.mkQ z) = N'.mkQ (TensorProduct.map g LinearMap.id z) := by
    intro g hg z
    simp only [act, dif_pos (hsg g hg), Submodule.mapQ_apply, Submodule.mkQ_apply]
  have hbacth : ∀ h ∈ B, ∀ z, bAct h (N'.mkQ z) = N'.mkQ (TensorProduct.map LinearMap.id h z) := by
    intro h hh z
    simp only [bAct, dif_pos (hsh h hh), Submodule.mapQ_apply, Submodule.mkQ_apply]
  let φ : M₀ →ₗ[ℂ] (M₀ ⊗[ℂ] V) ⧸ N' := N'.mkQ ∘ₗ (TensorProduct.mk ℂ M₀ V).flip y
  have hφ : ∀ x, φ x = N'.mkQ (x ⊗ₜ[ℂ] y) := fun x => rfl
  have key := GlobalTheory.T.le_ker_of_local_finite_length_to_simple Op₀ Rel₀ K₀ φ act (bAct '' B) hlen hmax hK hKs
    (by
      intro z hz
      rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hrel z hz y)
    (by
      intro g hg
      ext z
      simp only [LinearMap.comp_apply, hφ, hactg g hg, TensorProduct.map_tmul, LinearMap.id_apply])
    (by
      rintro g hg b ⟨h, hh, rfl⟩
      apply Submodule.linearMap_qext
      apply TensorProduct.ext'
      intro u v
      simp only [LinearMap.comp_apply, Module.End.mul_apply, hactg g hg, hbacth h hh,
        TensorProduct.map_tmul, LinearMap.id_apply])
    (by
      intro U hU
      have hP : Stab (tensOps Op₀ B) (U.comap N'.mkQ) := by
        rintro f (⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩) z hz
        · rw [Submodule.mem_comap] at hz ⊢
          rw [← hactg g hg]
          exact hU _ (Or.inl ⟨g, hg, rfl⟩) _ hz
        · rw [Submodule.mem_comap] at hz ⊢
          rw [← hbacth h hh]
          exact hU _ (Or.inr ⟨h, hh, rfl⟩) _ hz
      have hle : N' ≤ U.comap N'.mkQ := by
        intro z hz
        rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N').2 hz]
        exact U.zero_mem
      have hsurj : Function.Surjective N'.mkQ := Submodule.mkQ_surjective N'
      rcases hN'max _ hP hle with h1 | h1
      · left
        rw [← Submodule.map_comap_eq_of_surjective hsurj U, h1, Submodule.mkQ_map_self]
      · right
        rw [← Submodule.map_comap_eq_of_surjective hsurj U, h1, Submodule.map_top,
          LinearMap.range_eq_top.2 hsurj])
  have := key hx
  rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  exact this

end GlobalTheory.TensHead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorMaximalStableContainsLeftKernelStatement
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_maximalStable_contains_leftKernel : ∀ {M₀ V : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup V] [Module ℂ V]
    (Op₀ : Set (Module.End ℂ M₀)) (B : Set (Module.End ℂ V)) (Rel₀ K₀ : Submodule ℂ M₀),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → GlobalTheory.TensHead.Stab Op₀ N → N ≠ ⊤ → N ≤ K₀) →
    K₀ ≠ ⊤ → GlobalTheory.TensHead.Stab Op₀ K₀ →
    ∀ N' : Submodule ℂ (M₀ ⊗[ℂ] V),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N') → GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) N' →
      (∀ U, GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ B) U → N' ≤ U → U = N' ∨ U = ⊤) →
      ∀ x ∈ K₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N' := by
  first | exact @GlobalTheory.TensHead.tens_maxStab_contains_left_ker | exact GlobalTheory.TensHead.tens_maxStab_contains_left_ker | (intros; apply GlobalTheory.TensHead.tens_maxStab_contains_left_ker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetGeneratingOperatorStableBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetGeneratingOperatorStableBounded
open scoped TensorProduct

namespace GlobalTheory.StabGen

open GlobalTheory.TensHead

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stabClosure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) : Submodule ℂ M :=
  sInf {N | Rel ≤ N ∧ Stab Op N ∧ S ⊆ N}

theorem rel_le_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Rel ≤ stabClosure Op Rel S :=
  le_sInf fun _ hN => hN.1

theorem subset_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    S ⊆ stabClosure Op Rel S := fun _ hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.2.2 hx

theorem stab_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Stab Op (stabClosure Op Rel S) := by
  intro g hg x hx
  rw [stabClosure, Submodule.mem_sInf] at hx ⊢
  intro N hN
  exact hN.2.1 g hg x (hx N hN)

theorem closure_le {Op : Set (Module.End ℂ M)} {Rel N : Submodule ℂ M} {S : Set M}
    (h1 : Rel ≤ N) (h2 : Stab Op N) (h3 : S ⊆ N) : stabClosure Op Rel S ≤ N :=
  sInf_le ⟨h1, h2, h3⟩

theorem closure_mono {Op : Set (Module.End ℂ M)} {Rel : Submodule ℂ M} {S T : Set M}
    (h : S ⊆ T) : stabClosure Op Rel S ≤ stabClosure Op Rel T :=
  closure_le (rel_le_closure Op Rel T) (stab_closure Op Rel T)
    (h.trans (subset_closure Op Rel T))

noncomputable def chainSet [DecidableEq M] (pick : Finset M → M) : ℕ → Finset M
  | 0 => ∅
  | n + 1 => insert (pick (chainSet pick n)) (chainSet pick n)

theorem exists_finset_generating (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) :
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N →
      (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  classical
  obtain ⟨L, hL⟩ := hL
  by_contra hne
  push_neg at hne
  have hx : ∀ F : Finset M, ∃ x, x ∉ stabClosure Op Rel (F : Set M) := by
    intro F
    obtain ⟨N, h1, h2, h3, h4⟩ := hne F
    by_contra h
    push_neg at h
    exact h4 (eq_top_iff.2 fun x _ => closure_le h1 h2 h3 (h x))
  choose pick hpick using hx
  have hD : StrictMono fun n => stabClosure Op Rel (↑(chainSet pick n) : Set M) := by
    refine strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne ?_ ?_
    · exact closure_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))
    · intro h
      apply hpick (chainSet pick n)
      have hmem : pick (chainSet pick n) ∈ stabClosure Op Rel (↑(chainSet pick (n + 1)) : Set M) :=
        subset_closure Op Rel _ (by simp [chainSet])
      rw [← h] at hmem
      exact hmem
  have := hL (L + 1) (fun j => stabClosure Op Rel (↑(chainSet pick j) : Set M))
    (fun a b hab => hD hab) (fun j => ⟨rel_le_closure _ _ _, stab_closure _ _ _⟩)
  omega

end GlobalTheory.StabGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetGeneratingOperatorStableBoundedStatement
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_generating_operator_stable_bounded : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  first | exact @GlobalTheory.StabGen.exists_finset_generating | exact GlobalTheory.StabGen.exists_finset_generating | (intros; apply GlobalTheory.StabGen.exists_finset_generating <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaximalOperatorStableOfFinsetGenerating
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaximalOperatorStableOfFinsetGenerating
open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem exists_maximal_stab_of_finset {V : Type} [AddCommGroup V] [Module ℂ V]
    (G : Set (Module.End ℂ V)) (R : Submodule ℂ V) (F : Finset V)
    (hF : ∀ N : Submodule ℂ V, R ≤ N → Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) :
    ∀ N : Submodule ℂ V, R ≤ N → Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  intro N hRN hN hNtop
  let s : Set (Submodule ℂ V) := {U | R ≤ U ∧ Stab G U ∧ ¬ (↑F : Set V) ⊆ ↑U}
  have hcomp := (isCompactElement_iff_le_of_directed_sSup_le _).1
    (Submodule.finset_span_isCompactElement (R := ℂ) F)
  have hNs : N ∈ s := ⟨hRN, hN, fun h => hNtop (hF N hRN hN h)⟩
  obtain ⟨M, hNM, hM⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨le_trans (hcs hy).1 (le_sSup hy), ?_, ?_⟩, fun z hz => le_sSup hz⟩
    · intro g hg x hx
      obtain ⟨U, hU, hxU⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨U, hU, (hcs hU).2.1 g hg x hxU⟩
    · intro hFc
      have hspan : Submodule.span ℂ (↑F : Set V) ≤ sSup c := Submodule.span_le.2 hFc
      obtain ⟨U, hU, hle⟩ := hcomp c hne hdir hspan
      exact (hcs hU).2.2 (Submodule.span_le.1 hle)) N hNs
  refine ⟨M, hNM, hM.prop.2.1, fun h => hM.prop.2.2 (by rw [h]; exact fun _ _ => trivial), ?_⟩
  intro U hU hMU
  by_cases hFU : (↑F : Set V) ⊆ ↑U
  · exact Or.inr (hF U (le_trans hM.prop.1 hMU) hU hFU)
  · exact Or.inl (le_antisymm (hM.2 ⟨le_trans hM.prop.1 hMU, hU, hFU⟩ hMU) hMU)

end GlobalTheory.TensHead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMaximalOperatorStableOfFinsetGeneratingStatement
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_operatorStable_of_finset_generating : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V)) (R : Submodule ℂ V)
    (F : Finset V),
    (∀ N : Submodule ℂ V, R ≤ N → GlobalTheory.TensHead.Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ V, R ≤ N → GlobalTheory.TensHead.Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ GlobalTheory.TensHead.Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, GlobalTheory.TensHead.Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  first | exact @GlobalTheory.TensHead.exists_maximal_stab_of_finset | exact GlobalTheory.TensHead.exists_maximal_stab_of_finset | (intros; apply GlobalTheory.TensHead.exists_maximal_stab_of_finset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModules
open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem tensor_eq_top_or_le_ker_map : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ P₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup P₀] [Module ℂ P₀]
    {M P : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (p₀ : M₀ →ₗ[ℂ] P₀) (p : ∀ i, M i →ₗ[ℂ] P i),
    Module.rank ℂ M₀ ≤ Cardinal.aleph0 → (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → (∀ g ∈ Op₀, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker p₀) →
    Rel₀ ≤ LinearMap.ker p₀ → (∀ g ∈ Op₀, ∀ x ∈ LinearMap.ker p₀, g x ∈ LinearMap.ker p₀) →
    (∀ i, ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel i ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → (∀ g ∈ Op i, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (p i)) →
    (∀ i, Rel i ≤ LinearMap.ker (p i)) → (∀ i, ∀ g ∈ Op i, ∀ x ∈ LinearMap.ker (p i), g x ∈ LinearMap.ker (p i)) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      (∀ g ∈ Op₀, ∀ t ∈ N, TensorProduct.map g LinearMap.id t ∈ N) →
      (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) →
      N = ⊤ ∨ N ≤ LinearMap.ker (TensorProduct.map p₀ (PiTensorProduct.map p)) := by
  intro ι _ _ M₀ P₀ _ _ _ _ M P _ _ _ _ Op₀ Op Rel₀ Rel p₀ p hr₀ hr hL₀ hloc₀ hRel₀ hK₀ hL hloc hRel hK
    N hN₀ hNi hS₀ hSi
  classical
  have hS : Stab (tensOps Op₀ (piOps Op)) N := by
    rintro f (⟨g, hg, rfl⟩ | ⟨h, ⟨i, g, hg, rfl⟩, rfl⟩) t ht
    · exact hS₀ g hg t ht
    · exact hSi i g hg t ht
  by_cases h0 : LinearMap.ker p₀ = ⊤
  · right
    intro t _
    have : p₀ = 0 := LinearMap.ker_eq_top.mp h0
    rw [LinearMap.mem_ker, this, TensorProduct.map_zero_left, LinearMap.zero_apply]
  by_cases hi : ∃ i, LinearMap.ker (p i) = ⊤
  · right
    obtain ⟨i, hi⟩ := hi
    have hpi : p i = 0 := LinearMap.ker_eq_top.mp hi
    have hmap : PiTensorProduct.map p = 0 := by
      ext y
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
        LinearMap.zero_apply]
      exact MultilinearMap.map_coord_zero _ i (by simp [hpi])
    intro t _
    rw [LinearMap.mem_ker, hmap, TensorProduct.map_zero_right, LinearMap.zero_apply]
  push_neg at hi
  by_cases hN : N = ⊤
  · exact Or.inl hN
  have hSimple₀ : SimpleOver Op₀ (LinearMap.ker p₀) := fun U hU hKU => by
    by_cases hUt : U = ⊤
    · exact Or.inr hUt
    exact Or.inl (le_antisymm (hloc₀ U (hRel₀.trans hKU) hU hUt) hKU)
  have hSimple : ∀ i, SimpleOver (Op i) (LinearMap.ker (p i)) := fun i U hU hKU => by
    by_cases hUt : U = ⊤
    · exact Or.inr hUt
    exact Or.inl (le_antisymm (hloc i U ((hRel i).trans hKU) hU hUt) hKU)
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.T.exists_finset_generating_operator_stable_bounded Op₀ Rel₀ hL₀
  choose F hF using fun i => GlobalTheory.T.exists_finset_generating_operator_stable_bounded (Op i) (Rel i) (hL i)
  let G : Finset (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :=
    (F₀ ×ˢ Fintype.piFinset F).image (fun q => q.1 ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ q.2)
  have hgen : ∀ U, N ≤ U → Stab (tensOps Op₀ (piOps Op)) U → (↑G : Set (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))) ⊆ (U : Set (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))) → U = ⊤ := by
    intro U hNU hU hGU
    refine GlobalTheory.T.eq_top_of_pure_tensors_of_factor_generators Op₀ Op Rel₀ Rel F₀ F hF₀ hF U (fun x hx y => hNU (hN₀ x hx y))
      (fun i x hx x₀ y => hNU (hNi i x hx x₀ y)) hU ?_
    intro x₀ hx₀ y hy
    apply hGU
    simp only [G, Finset.coe_image]
    exact ⟨(x₀, y), by simp [hx₀, Fintype.mem_piFinset, hy], rfl⟩
  obtain ⟨N', hNN', hS', hN'top, hmax⟩ := GlobalTheory.T.exists_maximal_operatorStable_of_finset_generating _ N G hgen N le_rfl hS hN
  have h0' := GlobalTheory.T.tensor_maximalStable_contains_leftKernel Op₀ (piOps Op) Rel₀ (LinearMap.ker p₀) hL₀ hloc₀ h0 hK₀ N'
    (fun x hx y => hNN' (hN₀ x hx y)) hS' hmax
  have hi' : ∀ i, ∀ x ∈ LinearMap.ker (p i), ∀ (x₀ : M₀) (y : ∀ j, M j),
      x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N' := fun i =>
    GlobalTheory.T.piTensor_maximalStable_contains_positionKernel Op₀ Op i (Rel i) (LinearMap.ker (p i)) (hL i) (hloc i) (hi i) (hK i) N'
      (fun x hx x₀ y => hNN' (hNi i x hx x₀ y)) hS' hmax
  have hKT : tensKer (LinearMap.ker p₀) (piKer fun i => LinearMap.ker (p i)) ≤ N' := by
    rw [tensKer, Submodule.span_le]
    rintro t ⟨x, y, hxy | hxy, rfl⟩
    · exact h0' x hxy y
    · refine Submodule.span_induction (p := fun y _ => x ⊗ₜ[ℂ] y ∈ N') ?_ ?_ ?_ ?_ hxy
      · rintro _ ⟨z, ⟨i, hzi⟩, rfl⟩
        have := hi' i (z i) hzi x z
        rwa [Function.update_eq_self] at this
      · simp
      · intro a b _ _ ha hb
        rw [TensorProduct.tmul_add]
        exact N'.add_mem ha hb
      · intro c a _ ha
        rw [TensorProduct.tmul_smul]
        exact N'.smul_mem c ha
  have hPi := GlobalTheory.T.simpleOverStableSubmodule_piTensor Op (fun i => LinearMap.ker (p i)) hr hK hSimple
  have hT := GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan Op₀ (piOps Op) (LinearMap.ker p₀) (piKer fun i => LinearMap.ker (p i)) hr₀ hK₀
    (GlobalTheory.T.operatorStable_piTensorPureKernelSpan Op _ hK) hSimple₀ hPi
  rcases hT N' hS' hKT with h | h
  · right
    rw [h] at hNN'
    refine hNN'.trans ?_
    have hle : piKer (fun i => LinearMap.ker (p i)) ≤ LinearMap.ker (PiTensorProduct.map p) := by
      rw [piKer, Submodule.span_le]
      rintro _ ⟨z, ⟨i, hzi⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, PiTensorProduct.map_tprod]
      exact MultilinearMap.map_coord_zero _ i (LinearMap.mem_ker.mp hzi)
    rw [tensKer, Submodule.span_le]
    rintro t ⟨x, y, hxy | hxy, rfl⟩
    · simp [TensorProduct.map_tmul, LinearMap.mem_ker.mp hxy]
    · simp [TensorProduct.map_tmul, LinearMap.mem_ker.mp (hle hxy)]
  · exact absurd h hN'top

end GlobalTheory.TensHead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModulesStatement
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_eq_top_or_le_ker_finiteLength_modules : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ P₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup P₀] [Module ℂ P₀]
    {M P : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (p₀ : M₀ →ₗ[ℂ] P₀) (p : ∀ i, M i →ₗ[ℂ] P i),
    Module.rank ℂ M₀ ≤ Cardinal.aleph0 → (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N →
        (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → (∀ g ∈ Op₀, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker p₀) →
    Rel₀ ≤ LinearMap.ker p₀ → (∀ g ∈ Op₀, ∀ x ∈ LinearMap.ker p₀, g x ∈ LinearMap.ker p₀) →
    (∀ i, ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (M i)), StrictMono N →
        (∀ j, Rel i ≤ N j ∧ ∀ g ∈ Op i, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → (∀ g ∈ Op i, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker (p i)) →
    (∀ i, Rel i ≤ LinearMap.ker (p i)) → (∀ i, ∀ g ∈ Op i, ∀ x ∈ LinearMap.ker (p i), g x ∈ LinearMap.ker (p i)) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      (∀ g ∈ Op₀, ∀ t ∈ N, TensorProduct.map g LinearMap.id t ∈ N) →
      (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) →
      N = ⊤ ∨ N ≤ LinearMap.ker (TensorProduct.map p₀ (PiTensorProduct.map p)) := by
  first | exact @GlobalTheory.TensHead.tensor_eq_top_or_le_ker_map | exact GlobalTheory.TensHead.tensor_eq_top_or_le_ker_map | (intros; apply GlobalTheory.TensHead.tensor_eq_top_or_le_ker_map <;> assumption)
end
