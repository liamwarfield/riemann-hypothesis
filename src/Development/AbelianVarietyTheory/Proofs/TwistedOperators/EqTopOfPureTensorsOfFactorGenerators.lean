module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousRealToComplexExponential

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfPureTensorsOfFactorGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfPureTensorsOfFactorGenerators
open scoped TensorProduct

namespace GlobalTheory.TensHead

private lemma piOp_tprod {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ y) =
      PiTensorProduct.tprod ℂ (Function.update y i (g (y i))) := by
  unfold _root_.GlobalTheory.TensHead.piOp
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

lemma _root_.GlobalTheory.TensHead.piOp_tprod_update {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) (x : M i) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ (Function.update y i x)) =
      PiTensorProduct.tprod ℂ (Function.update y i (g x)) := by
  rw [piOp_tprod]
  simp

private lemma apply_tmul_mem_of_stab_left {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀]
    [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    {Op₀ : Set (Module.End ℂ M₀)} {Op : ∀ i, Set (Module.End ℂ (M i))}
    {N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))}
    (hN : _root_.GlobalTheory.TensHead.Stab
      (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N)
    {g : Module.End ℂ M₀} (hg : g ∈ Op₀) {a : M₀} {t : ⨂[ℂ] i, M i} (h : a ⊗ₜ[ℂ] t ∈ N) :
    g a ⊗ₜ[ℂ] t ∈ N := by
  have hmem : TensorProduct.map g LinearMap.id ∈
      _root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op) := by
    unfold _root_.GlobalTheory.TensHead.tensOps
    exact Or.inl ⟨g, hg, rfl⟩
  unfold _root_.GlobalTheory.TensHead.Stab at hN
  simpa using hN _ hmem _ h

private lemma tmul_tprod_update_apply_mem_of_stab {ι : Type} [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀]
    [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    {Op₀ : Set (Module.End ℂ M₀)} {Op : ∀ i, Set (Module.End ℂ (M i))}
    {N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i))}
    (hN : _root_.GlobalTheory.TensHead.Stab
      (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N)
    (i : ι) {g : Module.End ℂ (M i)} (hg : g ∈ Op i) {a : M₀} {y : ∀ j, M j} {x : M i}
    (h : a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) :
    a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i (g x)) ∈ N := by
  have hmem : TensorProduct.map LinearMap.id (_root_.GlobalTheory.TensHead.piOp i g) ∈
      _root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op) := by
    unfold _root_.GlobalTheory.TensHead.tensOps _root_.GlobalTheory.TensHead.piOps
    exact Or.inr ⟨_, ⟨i, g, hg, rfl⟩, rfl⟩
  unfold _root_.GlobalTheory.TensHead.Stab at hN
  have := hN _ hmem _ h
  rwa [TensorProduct.map_tmul, LinearMap.id_apply, _root_.GlobalTheory.TensHead.piOp_tprod_update] at this

theorem _root_.GlobalTheory.TensHead.eq_top_of_pure_generators :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (F₀ : Finset M₀) (F : ∀ i, Finset (M i)),
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → _root_.GlobalTheory.TensHead.Stab Op₀ N → (↑F₀ : Set M₀) ⊆ ↑N → N = ⊤) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → _root_.GlobalTheory.TensHead.Stab (Op i) N →
      (↑(F i) : Set (M i)) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      _root_.GlobalTheory.TensHead.Stab (_root_.GlobalTheory.TensHead.tensOps Op₀ (_root_.GlobalTheory.TensHead.piOps Op)) N →
      (∀ x₀ ∈ F₀, ∀ y : ∀ i, M i, (∀ i, y i ∈ F i) → x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N) →
      N = ⊤ := by
  intro ι _ _ M₀ _ _ M _ _ Op₀ Op Rel₀ Rel F₀ F h₀ hF N hRel₀ hRel hN hgen
  have key : ∀ s : Finset ι, ∀ y : ∀ j, M j, (∀ j, j ∉ s → y j ∈ F j) →
      ∀ a : M₀, a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y hy a
      have hT := h₀ (N.comap ((TensorProduct.mk ℂ M₀ (⨂[ℂ] i, M i)).flip
        (PiTensorProduct.tprod ℂ y))) ?_ ?_ ?_
      · have ha : a ∈ (⊤ : Submodule ℂ M₀) := trivial
        rw [← hT] at ha
        simpa using ha
      · intro x hx
        simpa using hRel₀ x hx _
      · unfold _root_.GlobalTheory.TensHead.Stab
        intro g hg x hx
        simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hx ⊢
        exact apply_tmul_mem_of_stab_left hN hg hx
      · intro x hx
        simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.flip_apply,
          TensorProduct.mk_apply]
        exact hgen x hx y (fun j => hy j (by simp))
    | insert i s hi ih =>
      intro y hy a
      let S : Submodule ℂ (M i) := ⨅ (b : M₀)
        (z : {z : ∀ j, M j // ∀ j, j ∉ s → j ≠ i → z j ∈ F j}),
        N.comap ((TensorProduct.mk ℂ M₀ (⨂[ℂ] j, M j) b) ∘ₗ
          (PiTensorProduct.tprod ℂ).toLinearMap z.1 i)
      have hS : ∀ x, x ∈ S ↔ ∀ (b : M₀) (z : ∀ j, M j), (∀ j, j ∉ s → j ≠ i → z j ∈ F j) →
          b ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update z i x) ∈ N := by
        intro x
        simp only [S, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.comp_apply,
          MultilinearMap.toLinearMap_apply, TensorProduct.mk_apply, Subtype.forall]
      have hT := hF i S ?_ ?_ ?_
      · have hx : y i ∈ S := by
          rw [hT]
          trivial
        have := (hS _).1 hx a y (fun j hj hji => hy j (by simp [hji, hj]))
        simpa using this
      · intro x hx
        rw [hS]
        intro b z _
        exact hRel i x hx b z
      · unfold _root_.GlobalTheory.TensHead.Stab
        intro g hg x hx
        rw [hS] at hx ⊢
        intro b z hz
        exact tmul_tprod_update_apply_mem_of_stab hN i hg (hx b z hz)
      · intro x hx
        rw [SetLike.mem_coe, hS]
        intro b z hz
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst hji
          simpa using hx
        · rw [Function.update_of_ne hji]
          exact hz j hj hji
  have hall : ∀ v, v ∈ N := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => exact N.zero_mem
    | tmul a t =>
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r y =>
        rw [TensorProduct.tmul_smul]
        exact N.smul_mem r (key Finset.univ y (fun j hj => absurd (Finset.mem_univ j) hj) a)
      | add p q hp hq =>
        rw [TensorProduct.tmul_add]
        exact N.add_mem hp hq
    | add p q hp hq => exact N.add_mem hp hq
  exact eq_top_iff.2 fun v _ => hall v

end GlobalTheory.TensHead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfPureTensorsOfFactorGeneratorsStatement
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_top_of_pure_tensors_of_factor_generators : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
    {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i)))
    (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (F₀ : Finset M₀) (F : ∀ i, Finset (M i)),
    (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → GlobalTheory.TensHead.Stab Op₀ N → (↑F₀ : Set M₀) ⊆ ↑N → N = ⊤) →
    (∀ i, ∀ N : Submodule ℂ (M i), Rel i ≤ N → GlobalTheory.TensHead.Stab (Op i) N →
      (↑(F i) : Set (M i)) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)),
      (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) →
      (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j),
        x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) →
      GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps Op₀ (GlobalTheory.TensHead.piOps Op)) N →
      (∀ x₀ ∈ F₀, ∀ y : ∀ i, M i, (∀ i, y i ∈ F i) → x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y ∈ N) →
      N = ⊤ := by
  first | exact @GlobalTheory.TensHead.eq_top_of_pure_generators | exact GlobalTheory.TensHead.eq_top_of_pure_generators | (intros; apply GlobalTheory.TensHead.eq_top_of_pure_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmoduleTensorPureKernelSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleTensorProductOperatorStableCountable
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleTensorProductOperatorStableCountable
open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem exists_adjoin_agree {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (A : Set (Module.End ℂ V)) (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hA : ∀ U : Submodule ℂ V, Stab A U → U = ⊥ ∨ U = ⊤) (p : Module.End ℂ V) (s : Finset V) :
    ∃ r ∈ Algebra.adjoin ℂ A, ∀ m ∈ s, p m = r m := by
  set R := Algebra.adjoin ℂ A with hR
  haveI : IsSimpleModule R V := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun N => ?_ }
    have h := hA (N.restrictScalars ℂ) (fun g hg x hx =>
      N.smul_mem (⟨g, Algebra.subset_adjoin hg⟩ : R) hx)
    rcases h with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff ℂ R V).1 h
    · right; exact (Submodule.restrictScalars_eq_top_iff ℂ R V).1 h
  have hsc : ∀ φ : Module.End R V, ∃ c : ℂ, ∀ x, φ x = c • x := by
    intro φ
    obtain ⟨c, hc⟩ := GlobalTheory.dixmier_schur_of_rank_le_aleph0 V A (fun g => g.1)
      (LinearMap.restrictScalars ℂ φ) inferInstance hrank
      (fun N hN => hA N (fun g hg x hx => hN ⟨g, hg⟩ x hx))
      (fun g => LinearMap.ext fun x =>
        φ.map_smul (⟨g.1, Algebra.subset_adjoin g.2⟩ : R) x)
    exact ⟨c, fun x => LinearMap.congr_fun hc x⟩
  let f : Module.End (Module.End R V) V :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := fun φ x => by
        obtain ⟨c, hc⟩ := hsc φ
        change p (φ x) = φ (p x)
        rw [hc, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f s
  exact ⟨r.1, r.2, hr⟩

theorem simple_tensor :
    ∀ {S₀ S₁ : Type} [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    (A : Set (Module.End ℂ S₀)) (B : Set (Module.End ℂ S₁)),
    Module.rank ℂ S₀ ≤ Cardinal.aleph0 →
    (∀ U : Submodule ℂ S₀, GlobalTheory.TensHead.Stab A U → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ S₁, GlobalTheory.TensHead.Stab B U → U = ⊥ ∨ U = ⊤) →
    ∀ U : Submodule ℂ (S₀ ⊗[ℂ] S₁), GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps A B) U →
      U = ⊥ ∨ U = ⊤ := by
  classical
  intro S₀ S₁ _ _ _ _ A B hrank hA hB U hU
  rcases eq_or_ne U ⊥ with h0 | h0
  · exact Or.inl h0
  right
  obtain ⟨t, htU, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hadj : ∀ r ∈ Algebra.adjoin ℂ A, ∀ z ∈ U, TensorProduct.map r LinearMap.id z ∈ U := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem g hg => exact hU _ (Or.inl ⟨g, hg, rfl⟩)
    | algebraMap c =>
      intro z hz
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.map_smul_left, LinearMap.smul_apply,
        Module.End.one_eq_id, TensorProduct.map_id]
      exact U.smul_mem c hz
    | add f g _ _ hf hg =>
      intro z hz
      rw [TensorProduct.map_add_left]
      exact U.add_mem (hf z hz) (hg z hz)
    | mul f g _ _ hf hg =>
      intro z hz
      have : TensorProduct.map (f * g) (LinearMap.id : S₁ →ₗ[ℂ] S₁) =
          (TensorProduct.map f LinearMap.id) ∘ₗ (TensorProduct.map g LinearMap.id) := by
        rw [← TensorProduct.map_comp]; rfl
      rw [this]
      exact hf _ (hg z hz)
  let b := Module.Basis.ofVectorSpace ℂ S₀
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht : t = c.sum fun i n => b i ⊗ₜ[ℂ] n := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hc0 : c ≠ 0 := by
    intro h
    apply ht0
    rw [ht, h, Finsupp.sum_zero_index]
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hc0
  have hbi : b i ≠ 0 := b.ne_zero i
  haveI : Nontrivial S₀ := ⟨⟨b i, 0, hbi⟩⟩
  obtain ⟨r, hr, hrp⟩ := exists_adjoin_agree A hrank hA ((b.coord i).smulRight (b i))
    (c.support.image b)
  have h1 : b i ⊗ₜ[ℂ] c i ∈ U := by
    have h2 := hadj r hr t htU
    have h3 : TensorProduct.map r LinearMap.id t = b i ⊗ₜ[ℂ] c i := by
      conv_lhs => rw [ht]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finsupp.sum, map_sum, Finset.sum_eq_single i]
      · rw [TensorProduct.map_tmul, ← hrp _ (Finset.mem_image_of_mem b hi)]
        simp
      · intro j hj hji
        rw [TensorProduct.map_tmul, ← hrp _ (Finset.mem_image_of_mem b hj)]
        simp [Finsupp.single_apply, hji]
      · intro h; exact absurd hi h
    rwa [h3] at h2
  have h4 : U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) = ⊤ := by
    refine (hB _ ?_).resolve_left ?_
    · intro g hg y hy
      exact hU _ (Or.inr ⟨g, hg, rfl⟩) _ hy
    · intro h
      have : c i ∈ U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) := h1
      rw [h, Submodule.mem_bot] at this
      exact Finsupp.mem_support_iff.1 hi this
  have h5 : ∀ y, U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) = ⊤ := by
    intro y
    refine (hA _ ?_).resolve_left ?_
    · intro g hg x hx
      exact hU _ (Or.inl ⟨g, hg, rfl⟩) _ hx
    · intro h
      have h6 : y ∈ U.comap (TensorProduct.mk ℂ S₀ S₁ (b i)) := by rw [h4]; trivial
      have : b i ∈ U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) := h6
      rw [h, Submodule.mem_bot] at this
      exact hbi this
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact U.zero_mem
  | tmul x y =>
    have : x ∈ U.comap ((TensorProduct.mk ℂ S₀ S₁).flip y) := by rw [h5]; trivial
    exact this
  | add x y hx hy => exact U.add_mem hx hy

end GlobalTheory.TensHead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleTensorProductOperatorStableCountableStatement
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_tensor_product_operatorStable_countable : ∀ {S₀ S₁ : Type} [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    (A : Set (Module.End ℂ S₀)) (B : Set (Module.End ℂ S₁)),
    Module.rank ℂ S₀ ≤ Cardinal.aleph0 →
    (∀ U : Submodule ℂ S₀, GlobalTheory.TensHead.Stab A U → U = ⊥ ∨ U = ⊤) →
    (∀ U : Submodule ℂ S₁, GlobalTheory.TensHead.Stab B U → U = ⊥ ∨ U = ⊤) →
    ∀ U : Submodule ℂ (S₀ ⊗[ℂ] S₁), GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.tensOps A B) U → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.TensHead.simple_tensor | exact GlobalTheory.TensHead.simple_tensor | (intros; apply GlobalTheory.TensHead.simple_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmoduleTensorPureKernelSpan
open scoped TensorProduct

namespace GlobalTheory.TensHead

def quotOps {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) : Set (Module.End ℂ (V ⧸ K)) :=
  {f | ∃ g ∈ G, f ∘ₗ K.mkQ = K.mkQ ∘ₗ g}

theorem quot_simple {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) (hs : Stab G K) (hK : SimpleOver G K) :
    ∀ U : Submodule ℂ (V ⧸ K), Stab (quotOps G K) U → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  have hst : Stab G (U.comap K.mkQ) := by
    intro g hg x hx
    have hf : (K.mapQ K g (fun y hy => hs g hg y hy)) ∘ₗ K.mkQ = K.mkQ ∘ₗ g := by
      ext y; simp
    have := hU _ ⟨g, hg, hf⟩ _ hx
    simpa using this
  have hle : K ≤ U.comap K.mkQ := by
    intro x hx; simp [(Submodule.Quotient.mk_eq_zero K).2 hx]
  rcases hK _ hst hle with h | h
  · left
    rw [← Submodule.map_comap_eq_of_surjective K.mkQ_surjective U, h, Submodule.mkQ_map_self]
  · right
    rw [← Submodule.map_comap_eq_of_surjective K.mkQ_surjective U, h, Submodule.map_top,
      LinearMap.range_eq_top.2 K.mkQ_surjective]

theorem ker_map_mkQ_le {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁]
    [Module ℂ V₁] (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁) :
    LinearMap.ker (TensorProduct.map K₀.mkQ K₁.mkQ) ≤ tensKer K₀ K₁ := by
  rw [TensorProduct.map_ker (LinearMap.exact_subtype_mkQ K₀) K₀.mkQ_surjective
    (LinearMap.exact_subtype_mkQ K₁) K₁.mkQ_surjective]
  refine sup_le ?_ ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul x k => exact Submodule.subset_span ⟨x, k, Or.inr k.2, by simp⟩
    | add a b ha hb => simpa only [map_add] using add_mem ha hb
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul k y => exact Submodule.subset_span ⟨k, y, Or.inl k.2, by simp⟩
    | add a b ha hb => simpa only [map_add] using add_mem ha hb

theorem simpleOver_tensKer : ∀ {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁),
    Module.rank ℂ V₀ ≤ Cardinal.aleph0 → GlobalTheory.TensHead.Stab A K₀ → GlobalTheory.TensHead.Stab B K₁ →
    GlobalTheory.TensHead.SimpleOver A K₀ → GlobalTheory.TensHead.SimpleOver B K₁ →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.tensOps A B) (GlobalTheory.TensHead.tensKer K₀ K₁) := by
  intro V₀ V₁ _ _ _ _ A B K₀ K₁ hr hA hB hsA hsB N hN hKN
  set φ := TensorProduct.map K₀.mkQ K₁.mkQ with hφ
  have hker : LinearMap.ker φ ≤ N := (ker_map_mkQ_le K₀ K₁).trans hKN
  have hstU : Stab (tensOps (quotOps A K₀) (quotOps B K₁)) (N.map φ) := by
    rintro f hf _ ⟨x, hx, rfl⟩
    rcases hf with ⟨f', ⟨g, hg, hfg⟩, rfl⟩ | ⟨f', ⟨g, hg, hfg⟩, rfl⟩
    · have hc : TensorProduct.map f' LinearMap.id ∘ₗ φ = φ ∘ₗ TensorProduct.map g LinearMap.id := by
        rw [hφ, ← TensorProduct.map_comp, ← TensorProduct.map_comp, hfg]; rfl
      refine ⟨TensorProduct.map g LinearMap.id x, hN _ (Or.inl ⟨g, hg, rfl⟩) x hx, ?_⟩
      exact (LinearMap.congr_fun hc x).symm
    · have hc : TensorProduct.map LinearMap.id f' ∘ₗ φ = φ ∘ₗ TensorProduct.map LinearMap.id g := by
        rw [hφ, ← TensorProduct.map_comp, ← TensorProduct.map_comp, hfg]; rfl
      refine ⟨TensorProduct.map LinearMap.id g x, hN _ (Or.inr ⟨g, hg, rfl⟩) x hx, ?_⟩
      exact (LinearMap.congr_fun hc x).symm
  rcases GlobalTheory.T.simple_tensor_product_operatorStable_countable (quotOps A K₀) (quotOps B K₁) ((rank_quotient_le K₀).trans hr)
    (quot_simple A K₀ hA hsA) (quot_simple B K₁ hB hsB) _ hstU with h | h
  · left
    refine le_antisymm ?_ hKN
    intro x hx
    apply ker_map_mkQ_le K₀ K₁
    rw [LinearMap.mem_ker, ← Submodule.mem_bot ℂ, ← h]
    exact Submodule.mem_map_of_mem hx
  · right
    rw [eq_top_iff]
    intro x _
    have : φ x ∈ N.map φ := h ▸ Submodule.mem_top
    obtain ⟨y, hy, hxy⟩ := this
    have : x - y ∈ LinearMap.ker φ := by simp [hxy]
    simpa using add_mem (hker this) hy

end GlobalTheory.TensHead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOverStableSubmoduleTensorPureKernelSpanStatement
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleOverStableSubmodule_tensorPureKernelSpan : ∀ {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁),
    Module.rank ℂ V₀ ≤ Cardinal.aleph0 → GlobalTheory.TensHead.Stab A K₀ → GlobalTheory.TensHead.Stab B K₁ →
    GlobalTheory.TensHead.SimpleOver A K₀ → GlobalTheory.TensHead.SimpleOver B K₁ →
    GlobalTheory.TensHead.SimpleOver (GlobalTheory.TensHead.tensOps A B) (GlobalTheory.TensHead.tensKer K₀ K₁) := by
  first | exact @GlobalTheory.TensHead.simpleOver_tensKer | exact GlobalTheory.TensHead.simpleOver_tensKer | (intros; apply GlobalTheory.TensHead.simpleOver_tensKer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeKerOfLocalFiniteLengthToSimple
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeKerOfLocalFiniteLengthToSimple
open scoped TensorProduct

namespace GlobalTheory.TensHead

section HeadKill

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def MinStab (A : Set (Module.End ℂ W)) (T : Submodule ℂ W) : Prop :=
  Stab A T ∧ ∀ U : Submodule ℂ W, Stab A U → U ≤ T → U = ⊥ ∨ U = T

theorem MinStab.map {A : Set (Module.End ℂ W)} {T : Submodule ℂ W} (hT : MinStab A T)
    (b : Module.End ℂ W) (hb : ∀ a ∈ A, a * b = b * a) : MinStab A (T.map b) := by
  obtain ⟨hTs, hTmin⟩ := hT
  have hcomm' : ∀ a ∈ A, ∀ x, a (b x) = b (a x) := fun a ha x =>
    LinearMap.congr_fun (hb a ha) x
  refine ⟨?_, ?_⟩
  · intro a ha y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [hcomm' a ha x]
    exact Submodule.mem_map_of_mem (hTs a ha x hx)
  · intro U hU hUle
    have hU' : Stab A (T ⊓ U.comap b) := by
      intro a ha x hx
      refine ⟨hTs a ha x hx.1, ?_⟩
      show b (a x) ∈ U
      rw [← hcomm' a ha x]
      exact hU a ha (b x) hx.2
    rcases hTmin _ hU' inf_le_left with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp (hUle hu)
      have hx' : x ∈ T ⊓ U.comap b := ⟨hx, hu⟩
      rw [h] at hx'
      rw [(Submodule.mem_bot ℂ).mp hx', map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hUle ?_
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      have hx' : x ∈ T ⊓ U.comap b := by rw [h]; exact hx
      exact hx'.2

theorem exists_stab_compl {A : Set (Module.End ℂ W)}
    (htop : sSup {T | MinStab A T} = ⊤) (K : Submodule ℂ W) (hK : Stab A K) :
    ∃ C : Submodule ℂ W, Stab A C ∧ C ⊓ K = ⊥ ∧ C ⊔ K = ⊤ := by
  have hsup : ∀ N N' : Submodule ℂ W, Stab A N → Stab A N' → Stab A (N ⊔ N') := by
    intro N N' hN hN' a ha x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hN a ha y hy) (hN' a ha z hz)
  let S : Set (Submodule ℂ W) := {C | Stab A C ∧ C ⊓ K = ⊥}
  obtain ⟨C, hCmax⟩ : ∃ C, Maximal (· ∈ S) C := by
    refine zorn_le₀ S ?_
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ⟨?_, bot_inf_eq _⟩, by simp⟩
      intro a _ x hx
      rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _
    · refine ⟨sSup c, ⟨?_, ?_⟩, fun z hz => le_sSup hz⟩
      · intro a ha x hx
        rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx ⊢
        obtain ⟨y, hy, hxy⟩ := hx
        exact ⟨y, hy, (hcS hy).1 a ha x hxy⟩
      · rw [eq_bot_iff]
        intro x hx0
        obtain ⟨hx, hxK⟩ := Submodule.mem_inf.mp hx0
        rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx
        obtain ⟨y, hy, hxy⟩ := hx
        have hx' : x ∈ y ⊓ K := ⟨hxy, hxK⟩
        rwa [(hcS hy).2] at hx'
  obtain ⟨⟨hCs, hCK⟩, hCm⟩ := hCmax
  refine ⟨C, hCs, hCK, ?_⟩
  by_contra hne
  have hex : ∃ T, MinStab A T ∧ ¬ T ≤ C ⊔ K := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hne (top_unique (by rw [← htop]; exact sSup_le fun T hT => h T hT))
  obtain ⟨T, ⟨hTs, hTmin⟩, hTn⟩ := hex
  have hI : Stab A (T ⊓ (C ⊔ K)) := fun a ha x hx =>
    ⟨hTs a ha x hx.1, hsup C K hCs hK a ha x hx.2⟩
  rcases hTmin _ hI inf_le_left with h | h
  · have hmem : C ⊔ T ∈ S := by
      refine ⟨hsup C T hCs hTs, ?_⟩
      rw [eq_bot_iff]
      intro x hx0
      obtain ⟨hx, hxK⟩ := Submodule.mem_inf.mp hx0
      obtain ⟨c, hc, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
      have ht' : t ∈ T ⊓ (C ⊔ K) := by
        refine ⟨ht, ?_⟩
        simpa using Submodule.sub_mem _ (Submodule.mem_sup_right hxK : c + t ∈ C ⊔ K)
          (Submodule.mem_sup_left hc : c ∈ C ⊔ K)
      have ht0 : t = 0 := by
        rw [h] at ht'
        exact (Submodule.mem_bot ℂ).mp ht'
      subst ht0
      rw [add_zero] at hxK ⊢
      have hc' : c ∈ C ⊓ K := ⟨hc, hxK⟩
      rwa [hCK] at hc'
    have hle : C ⊔ T ≤ C := hCm hmem le_sup_left
    exact hTn ((le_sup_right.trans hle).trans le_sup_left)
  · exact hTn (inf_eq_left.mp h)

end HeadKill

theorem le_ker_of_simple_commuting {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W]
    [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W))
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L)
    (hmax : ∀ N : Submodule ℂ M, Rel ≤ N → Stab Op N → N ≠ ⊤ → N ≤ K)
    (hKtop : K ≠ ⊤) (hK : Stab Op K) (hRel : Rel ≤ LinearMap.ker φ)
    (hφ : ∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ)
    (hcomm : ∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g)
    (hsimple : ∀ U : Submodule ℂ W, Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) :
    K ≤ LinearMap.ker φ := by
  classical
  have hint : ∀ g ∈ Op, ∀ x, φ (g x) = act g (φ x) := fun g hg x =>
    LinearMap.congr_fun (hφ g hg) x
  by_cases hφ0 : LinearMap.range φ = ⊥
  · intro x _
    have hx : φ x ∈ LinearMap.range φ := LinearMap.mem_range_self φ x
    rw [hφ0] at hx
    exact (Submodule.mem_bot ℂ).mp hx
  have hrange : Stab (act '' Op) (LinearMap.range φ) := by
    intro a ha y hy
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact LinearMap.mem_range.mpr ⟨g x, hint g hg x⟩
  have hcomap : ∀ U : Submodule ℂ W, Stab (act '' Op) U → Stab Op (U.comap φ) := by
    intro U hU g hg x hx
    show φ (g x) ∈ U
    rw [hint g hg x]
    exact hU _ ⟨g, hg, rfl⟩ _ hx
  have hRelc : ∀ U : Submodule ℂ W, Rel ≤ U.comap φ := by
    intro U x hx
    show φ x ∈ U
    rw [LinearMap.mem_ker.mp (hRel hx)]
    exact U.zero_mem
  obtain ⟨L, hL⟩ := hL
  let P : Set (Submodule ℂ W) := {U | U ≤ LinearMap.range φ ∧ Stab (act '' Op) U ∧ U ≠ ⊥}
  have hwf : P.WellFoundedOn (· < ·) := by
    rw [Set.wellFoundedOn_iff_no_descending_seq]
    intro f hf
    have hlt : ∀ m n : ℕ, m < n → f n < f m := fun m n h => f.map_rel_iff.mpr h
    have hmono : StrictMono (fun i : Fin (L + 1) => (f (L - i.val)).comap φ) := by
      intro i j hij
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      have hlt' : f (L - i.val) < f (L - j.val) := hlt _ _ (by omega)
      show (f (L - i.val)).comap φ < (f (L - j.val)).comap φ
      refine lt_of_le_of_ne (Submodule.comap_mono hlt'.le) ?_
      intro heq
      have hmap := congrArg (Submodule.map φ) heq
      rw [Submodule.map_comap_eq_self (hf _).1, Submodule.map_comap_eq_self (hf _).1] at hmap
      exact hlt'.ne hmap
    have hbound := hL (L + 1) _ hmono (fun j => ⟨hRelc _, hcomap _ (hf _).2.1⟩)
    omega
  have hPne : LinearMap.range φ ∈ P := ⟨le_rfl, hrange, hφ0⟩
  obtain ⟨T, hTP, hTmin⟩ := (Set.wellFoundedOn_iff.mp hwf).has_min P ⟨_, hPne⟩
  have hTms : MinStab (act '' Op) T := by
    refine ⟨hTP.2.1, fun U hU hUT => ?_⟩
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    · right
      by_contra hne
      have hUP : U ∈ P := ⟨hUT.trans hTP.1, hU, hU0⟩
      exact hTmin U hUP ⟨lt_of_le_of_ne hUT hne, hUP, hTP⟩
  have hbcomm : ∀ b ∈ B, ∀ a ∈ act '' Op, a * b = b * a := by
    rintro b hb _ ⟨g, hg, rfl⟩
    exact hcomm g hg b hb
  have hstop : sSup {T | MinStab (act '' Op) T} = ⊤ := by
    have hst : Stab (act '' Op ∪ B) (sSup {T | MinStab (act '' Op) T}) := by
      intro a ha
      rcases ha with ha | ha
      · have hle : sSup {T | MinStab (act '' Op) T} ≤ (sSup {T | MinStab (act '' Op) T}).comap a :=
          sSup_le fun T' hT' y hy => (le_sSup hT' : T' ≤ _) (hT'.1 a ha y hy)
        exact fun x hx => hle hx
      · have hle : sSup {T | MinStab (act '' Op) T} ≤ (sSup {T | MinStab (act '' Op) T}).comap a :=
          sSup_le fun T' hT' y hy =>
            (le_sSup (MinStab.map hT' a (hbcomm a ha)) : T'.map a ≤ _) (Submodule.mem_map_of_mem hy)
        exact fun x hx => hle hx
    rcases hsimple _ hst with h | h
    · exact absurd (eq_bot_iff.mpr ((le_sSup (show T ∈ {T | MinStab (act '' Op) T} from hTms)).trans h.le)) hTP.2.2
    · exact h
  have hKs : Stab (act '' Op) (K.map φ) := by
    intro a ha y hy
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    rw [← hint g hg k]
    exact Submodule.mem_map_of_mem (hK g hg k hk)
  obtain ⟨C, hCs, hCK, hCtop⟩ := exists_stab_compl hstop (K.map φ) hKs
  have hNK : C.comap φ ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have hm : φ m ∈ C ⊔ K.map φ := by rw [hCtop]; exact Submodule.mem_top
    obtain ⟨c, hc, y, hy, hcy⟩ := Submodule.mem_sup.mp hm
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    have hmk : m - k ∈ C.comap φ := by
      show φ (m - k) ∈ C
      rw [map_sub, ← hcy, add_sub_cancel_right]
      exact hc
    simpa using Submodule.add_mem_sup hmk hk
  by_cases hN : C.comap φ = ⊤
  · intro k hk
    have h1 : k ∈ C.comap φ := by rw [hN]; exact Submodule.mem_top
    have h2 : φ k ∈ C ⊓ K.map φ := ⟨h1, Submodule.mem_map_of_mem hk⟩
    rw [hCK] at h2
    exact (Submodule.mem_bot ℂ).mp h2
  · exact absurd (top_unique (hNK.symm.le.trans
      (sup_le (hmax _ (hRelc C) (hcomap C hCs) hN) le_rfl))) hKtop

end GlobalTheory.TensHead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeKerOfLocalFiniteLengthToSimpleStatement
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_ker_of_local_finite_length_to_simple : ∀ {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W)),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    (∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → N ≠ ⊤ → N ≤ K) →
    K ≠ ⊤ → GlobalTheory.TensHead.Stab Op K → Rel ≤ LinearMap.ker φ →
    (∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ) →
    (∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g) →
    (∀ U : Submodule ℂ W, GlobalTheory.TensHead.Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) →
    K ≤ LinearMap.ker φ := by
  first | exact @GlobalTheory.TensHead.le_ker_of_simple_commuting | exact GlobalTheory.TensHead.le_ker_of_simple_commuting | (intros; apply GlobalTheory.TensHead.le_ker_of_simple_commuting <;> assumption)
end
end
