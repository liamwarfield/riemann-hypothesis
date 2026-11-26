module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalMemInvariantSubmodule

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.GeneratedSubmoduleStableUnderAction
noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

theorem tensor_dual_action_apply_component (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (g : Fin n → M) (c : Fin n) :
    tensVd E a b g c = E a b (g c) - (if c = b then g a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem euler_tensor_dual_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

theorem euler_tensor_dual_commute_gl_action (hE : IsGlRep E) (a b : Fin n) :
    eeVd E * tensVd E a b = tensVd E a b * eeVd E := by
  refine LinearMap.ext fun f => funext fun d => ?_
  have hc : ∀ c, E d c (E a b (f c)) = E a b (E d c (f c)) + (if c = a then E d b (f c) else 0) -
      (if b = d then E a c (f c) else 0) := by
    intro c
    have := congrArg (fun T : Module.End ℂ M => T (f c)) (hE d c a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    rw [sub_eq_iff_eq_add] at this
    rw [this]
    by_cases h1 : c = a <;> by_cases h2 : b = d <;> simp [h1, h2] <;> abel
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.End.mul_apply, euler_tensor_dual_apply, tensor_dual_action_apply_component, map_sub, map_neg, map_sum,
    sum_sub_distrib, hc, sum_add_distrib]
  by_cases hbd : b = d
  · subst hbd
    simp [apply_ite, Finset.sum_ite_eq']
    abel
  · have hdb : d ≠ b := Ne.symm hbd
    simp [hbd, hdb, apply_ite, Finset.sum_ite_eq']

theorem mem_pi_submodule_iff {S : Submodule ℂ M} {f : Fin n → M} :
    f ∈ Submodule.pi Set.univ (fun _ : Fin n => S) ↔ ∀ c, f c ∈ S := by
  simp [Submodule.mem_pi]

theorem dualTensorAction_mem {S : Submodule ℂ M} (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S) (a b : Fin n)
    {f : Fin n → M} (hf : ∀ c, f c ∈ S) (c : Fin n) : tensVd E a b f c ∈ S := by
  rw [tensor_dual_action_apply_component]
  refine sub_mem (hS a b _ (hf c)) ?_
  split_ifs
  · exact hf a
  · exact zero_mem _

theorem euler_tensor_dual_mem_of_stable {S : Submodule ℂ M} (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S)
    {f : Fin n → M} (hf : ∀ c, f c ∈ S) (d : Fin n) : eeVd E f d ∈ S := by
  rw [euler_tensor_dual_apply]
  exact neg_mem (sum_mem fun c _ => hS d c _ (hf c))

theorem generated_submodule_stable_under_action (V : Submodule ℂ M) (a b : Fin n) {v : M} (hv : v ∈ genSub E V) :
    E a b v ∈ genSub E V := by
  unfold genSub at *
  rw [Submodule.mem_sInf] at *
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem le_generatedSubmodule_dual (V : Submodule ℂ M) : V ≤ genSub E V := le_sInf fun _ hT => hT.1

theorem mem_euler_eigenspace_iff {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs (eeVd E) S θ ↔ (∀ c, f c ∈ S) ∧ eeVd E f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_pi, sub_eq_zero]

theorem euler_eigenspace_stable_under_action (hE : IsGlRep E) {S : Submodule ℂ M} (hS : ∀ a b, ∀ v ∈ S, E a b v ∈ S)
    {θ : ℝ} (a b : Fin n) {f : Fin n → M} (hf : f ∈ Xs (eeVd E) S θ) :
    tensVd E a b f ∈ Xs (eeVd E) S θ := by
  rw [mem_euler_eigenspace_iff] at hf ⊢
  refine ⟨dualTensorAction_mem hS a b hf.1, ?_⟩
  have := congrArg (fun T : Module.End ℂ (Fin n → M) => T f) (euler_tensor_dual_commute_gl_action hE a b)
  simp only [Module.End.mul_apply] at this
  rw [this, hf.2, map_smul]

end Alg

section Poly

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

theorem shifted_product_eq_aeval (A : Module.End ℂ Y) (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C (((θ t : ℝ) : ℂ)))) := by
  unfold prodShift
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext t
  simp [Function.comp, Algebra.algebraMap_eq_smul_one]

theorem aeval_mem_invariant_submodule (A : Module.End ℂ Y) (p : Submodule ℂ Y) (hA : ∀ y ∈ p, A y ∈ p)
    (q : ℂ[X]) : ∀ y ∈ p, aeval A q y ∈ p := by
  first | exact UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule .. | (apply UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj11.aeval_mem_invariant_submodule <;> first | assumption | infer_instance)

theorem aeval_commute_of_commute (A T : Module.End ℂ Y) (h : Commute A T) (q : ℂ[X]) :
    Commute (aeval A q) T := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq
  | monomial k c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left c T).mul_left (h.pow_left k)

end Poly

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ExistsIrreducibleHighestWeightSubmodule
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem tensor_dual_action_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (g : Fin n → M) (c : Fin n) :
    tensVd E a b g c = E a b (g c) - (if c = b then g a else 0) := by
  unfold tensVd
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

section Unit

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

theorem highest_weight_dominant_of_unitary (hA : IsGlRep A) (hU : IsKUnitary ε A) {ν : Fin n → ℝ} {y : X}
    (hy : IsKHWVec ε A ν y) (hy0 : y ≠ 0) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    ν b ≤ ν a := by
  have hc := hA a b b a
  rw [if_pos rfl, if_pos rfl] at hc
  have h1 : A a b (A b a y) = ((ν a - ν b : ℝ) : ℂ) • y := by
    have := congrArg (fun T : Module.End ℂ X => T y) hc
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hy.2 a b hab he, map_zero, sub_zero] at this
    rw [this, hy.1 a, hy.1 b]; push_cast; rw [sub_smul]
  have h2 : inner ℂ (A b a y) (A b a y) = inner ℂ y (A a b (A b a y)) := hU b a he.symm y _
  rw [h1, inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ‖A b a y‖ ^ 2 = (ν a - ν b) * ‖y‖ ^ 2 := by
    have := congrArg Complex.re h2
    simpa [← Complex.ofReal_pow, Complex.mul_re] using this
  have hpos : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.2 hy0) 2
  by_contra hlt
  push Not at hlt
  have : (ν a - ν b) * ‖y‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (by linarith) hpos
  nlinarith [sq_nonneg ‖A b a y‖]

theorem exists_irreducible_highest_weight_submodule (hU : IsKUnitary ε A) {ν : Fin n → ℝ} :
    ∀ (d : ℕ) (T : Submodule ℂ X), Module.finrank ℂ T = d → FiniteDimensional ℂ T →
      IsKStableSub ε A T → ∀ w ∈ T, w ≠ 0 → IsKHWVec ε A ν w →
      ∃ W : Submodule ℂ X, W ≤ T ∧ IsKIrrHW ε A ν W := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro T hd hfd hT w hwT hw0 hw
  by_cases hirr : ∀ S' : Submodule ℂ X, S' ≤ T → IsKStableSub ε A S' → S' = ⊥ ∨ S' = T
  · exact ⟨T, le_rfl, hfd, hT, hirr, w, hwT, hw0, hw⟩
  push Not at hirr
  obtain ⟨S', hS'T, hS', hS'0, hS'ne⟩ := hirr
  have hlt : S' < T := lt_of_le_of_ne hS'T hS'ne
  have hfdS : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'T
  have : CompleteSpace S' := FiniteDimensional.complete ℂ S'
  have hw1 : IsKHWVec ε A ν (S'.starProjection w) := isKHWVec_starProjection hU hS' hw
  by_cases h1 : S'.starProjection w = 0
  · set T2 : Submodule ℂ X := T ⊓ S'ᗮ
    have hT2 : IsKStableSub ε A T2 := fun a b he v hv =>
      ⟨hT a b he v hv.1, orthogonal_kStable hU hS' a b he v hv.2⟩
    have hwT2 : w ∈ T2 := by
      refine ⟨hwT, ?_⟩
      have := Submodule.sub_starProjection_mem_orthogonal (K := S') w
      rwa [h1, sub_zero] at this
    have hlt2 : T2 < T := by
      refine lt_of_le_of_ne inf_le_left (fun heq => ?_)
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS'0
      have hsT2 : s ∈ T2 := heq ▸ hS'T hs
      have h0 : inner ℂ s s = (0 : ℂ) := Submodule.inner_right_of_mem_orthogonal hs hsT2.2
      exact hs0 (inner_self_eq_zero.1 h0)
    have hfd2 : FiniteDimensional ℂ T2 := Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨W, hW, hWi⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt2) T2 rfl hfd2 hT2 w hwT2 hw0 hw
    exact ⟨W, hW.trans inf_le_left, hWi⟩
  · obtain ⟨W, hW, hWi⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) S' rfl hfdS hS'
      _ (S'.starProjection_apply_mem w) h1 hw1
    exact ⟨W, hW.trans hS'T, hWi⟩

end Unit

section Lift

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ D}

def coordinateTensorEndAction (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) : Module.End ℂ (WithLp 2 (Fin n → D)) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → D)).symm.toLinearMap ∘ₗ tensVd E a b ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin n → D)).toLinearMap

theorem k3vdTA_isKUnitary (hU : IsKUnitary ε E) : IsKUnitary ε (coordinateTensorEndAction E) := by
  intro a b he x y
  have key : ∀ g h : Fin n → D, ∑ i, inner ℂ (tensVd E a b g i) (h i) =
      ∑ i, inner ℂ (g i) (tensVd E b a h i) := by
    intro g h
    simp only [tensor_dual_action_apply, inner_sub_left, inner_sub_right, sum_sub_distrib, hU a b he]
    congr 1
    rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (by simp),
      Finset.sum_eq_single a (fun c _ hc => by simp [hc]) (by simp)]
    simp
  simp only [coordinateTensorEndAction, LinearMap.comp_apply, LinearEquiv.coe_coe, PiLp.inner_apply,
    WithLp.linearEquiv_apply, WithLp.linearEquiv_symm_apply, WithLp.ofLp_toLp]
  exact key _ _

theorem k3vdTA_e (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (z : WithLp 2 (Fin n → D)) :
    WithLp.linearEquiv 2 ℂ (Fin n → D) (coordinateTensorEndAction E a b z) =
      tensVd E a b (WithLp.linearEquiv 2 ℂ (Fin n → D) z) := by
  simp only [coordinateTensorEndAction, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem exists_highest_weight_lift_pi (hU : IsKUnitary ε E) {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {B : Fin n → Fin n → Module.End ℂ Y} (f : (Fin n → D) →ₗ[ℂ] Y) {S : Submodule ℂ (Fin n → D)}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε (tensVd E) S)
    (hf : ∀ a b, ε a = ε b → ∀ x ∈ S, f (tensVd E a b x) = B a b (f x)) {x₀ : Fin n → D} (hx₀ : x₀ ∈ S)
    {μ : Fin n → ℝ} (hy : IsKHWVec ε B μ (f x₀)) :
    ∃ x ∈ S, IsKHWVec ε (tensVd E) μ x ∧ f x = f x₀ := by
  classical
  set e := WithLp.linearEquiv 2 ℂ (Fin n → D) with he_def
  set S' : Submodule ℂ (WithLp 2 (Fin n → D)) := S.comap e.toLinearMap with hS'_def
  have hmem : ∀ z, z ∈ S' ↔ e z ∈ S := fun z => Iff.rfl
  have hfd' : FiniteDimensional ℂ S' := by
    have hinj : Function.Injective (e.toLinearMap.domRestrict S') := by
      intro u v huv
      apply Subtype.ext
      exact e.injective (by simpa using huv)
    exact Module.Finite.of_injective
      ((e.toLinearMap.domRestrict S').codRestrict S (fun z => (hmem z).1 z.2)) (by
        intro u v huv; apply hinj; simpa [LinearMap.codRestrict] using congrArg Subtype.val huv)
  haveI : CompleteSpace S' := FiniteDimensional.complete ℂ S'
  have hU' := k3vdTA_isKUnitary (ε := ε) hU
  have hS' : IsKStableSub ε (coordinateTensorEndAction E) S' := by
    intro a b hab z hz
    rw [hmem] at hz ⊢
    rw [he_def, k3vdTA_e, ← he_def]
    exact hS a b hab _ hz
  set P := S'.starProjection with hP
  set f' : WithLp 2 (Fin n → D) →ₗ[ℂ] Y := f ∘ₗ e.toLinearMap ∘ₗ (P : WithLp 2 (Fin n → D) →ₗ[ℂ] _)
  have hPS : ∀ z, e (P z) ∈ S := fun z => (hmem _).1 (S'.starProjection_apply_mem z)
  have hf' : ∀ a b, ε a = ε b → ∀ x, f' (coordinateTensorEndAction E a b x) = B a b (f' x) := by
    intro a b hab x
    have h1 : P (coordinateTensorEndAction E a b x) = coordinateTensorEndAction E a b (P x) := starProjection_comm hU' hS' hab x
    simp only [f', LinearMap.comp_apply, ContinuousLinearMap.coe_coe, h1]
    change f (e (coordinateTensorEndAction E a b (P x))) = B a b (f (e (P x)))
    rw [he_def, k3vdTA_e, ← he_def]
    exact hf a b hab _ (hPS x)
  have hx₀' : e.symm x₀ ∈ S' := by rw [hmem]; simpa using hx₀
  have hPx₀ : P (e.symm x₀) = e.symm x₀ := Submodule.starProjection_eq_self_iff.2 hx₀'
  have hfx₀ : f' (e.symm x₀) = f x₀ := by simp [f', hPx₀]
  obtain ⟨x, hxS, -, hkhw, hfx⟩ := lift_khw hU' f' hf' hfd' hS' hx₀' (μ := μ) (by rwa [hfx₀])
  have hPx : P x = x := Submodule.starProjection_eq_self_iff.2 hxS
  refine ⟨e x, (hmem x).1 hxS, ⟨fun a => ?_, fun a b hab hε => ?_⟩, ?_⟩
  · have := congrArg e (hkhw.1 a)
    rw [he_def, k3vdTA_e, ← he_def, map_smul] at this
    exact this
  · have := congrArg e (hkhw.2 a b hab hε)
    rw [he_def, k3vdTA_e, ← he_def, map_zero] at this
    exact this
  · rw [← hfx₀, ← hfx]; simp [f', hPx]

end Lift

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem pi_submodule_finiteDimensional {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => S) := by
  let g : (Fin n → S) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun c => S.subtype ∘ₗ LinearMap.proj c
  have : Submodule.pi Set.univ (fun _ : Fin n => S) = LinearMap.range g := by
    ext f
    constructor
    · intro hf
      exact ⟨fun c => ⟨f c, mem_pi_submodule_iff.1 hf c⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact mem_pi_submodule_iff.2 fun c => by simp [g]
  rw [this]
  infer_instance

section HidaSetting

variable {ε : Fin n → Bool} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
  {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] {EN : Fin n → Fin n → Module.End ℂ N}
  {φ : (Fin n → M) →ₗ[ℂ] N} {θ : ℝ}

theorem eigenspace_K_finite (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V)
    {x : Fin n → M} (hx : x ∈ Xs (eeVd E) (genSub E V) θ) :
    ∃ S : Submodule ℂ (Fin n → M), S ≤ Xs (eeVd E) (genSub E V) θ ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (tensVd E) S ∧ x ∈ S := by
  classical
  have hxg := (mem_euler_eigenspace_iff.1 hx).1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => generated_submodule_stable_under_action V a b hv
  choose m hm using fun c => exists_layer_of_mem_genSub hE hVk (hxg c)
  set K := Finset.univ.sup m
  have hxK : ∀ c, x c ∈ layer ε E V K := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hfdL : FiniteDimensional ℂ (layer ε E V K) := finiteDimensional_layer hVfd K
  have hLk := layer_kStable hE hVk K
  have := pi_submodule_finiteDimensional (n := n) (layer ε E V K)
  refine ⟨Submodule.pi Set.univ (fun _ => layer ε E V K) ⊓ Xs (eeVd E) (genSub E V) θ, inf_le_right,
    Submodule.finiteDimensional_of_le inf_le_left, ?_, ⟨mem_pi_submodule_iff.2 hxK, hx⟩⟩
  intro a b hab f hf
  refine ⟨mem_pi_submodule_iff.2 fun c => ?_, euler_eigenspace_stable_under_action hE hGs a b hf.2⟩
  rw [tensor_dual_action_apply_component]
  refine sub_mem (hLk a b hab _ (mem_pi_submodule_iff.1 hf.1 c)) ?_
  split_ifs
  · exact mem_pi_submodule_iff.1 hf.1 a
  · exact zero_mem _

theorem image_eigenspace_K_finite (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensVd E a b f) = EN a b (φ f))
    {y : N} (hy : y ∈ (Xs (eeVd E) (genSub E V) θ).map φ) :
    ∃ T : Submodule ℂ N, T ≤ (Xs (eeVd E) (genSub E V) θ).map φ ∧ FiniteDimensional ℂ T ∧
      IsKStableSub ε EN T ∧ y ∈ T := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨S, hSX, hfd, hSk, hxS⟩ := eigenspace_K_finite hE hVfd hVk hx
  refine ⟨S.map φ, Submodule.map_mono hSX, inferInstance, ?_, Submodule.mem_map_of_mem hxS⟩
  intro a b hab v hv
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hv
  rw [← hφ a b f (mem_euler_eigenspace_iff.1 (hSX hf)).1]
  exact Submodule.mem_map_of_mem (hSk a b hab f hf)

theorem image_weights_in_root_cone (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensVd E a b f) = EN a b (φ f))
    {Λ : Fin n → ℝ}
    (hK2 : ∀ (μ : Fin n → ℝ) (f : Fin n → M), f ∈ Xs (eeVd E) (genSub E V) θ → f ≠ 0 →
      IsKHWVec ε (tensVd E) μ f → InRootCone (μ - Λ))
    {μ : Fin n → ℝ} {y : N} (hy : y ∈ (Xs (eeVd E) (genSub E V) θ).map φ) (hy0 : y ≠ 0)
    (hμ : IsKHWVec ε EN μ y) : InRootCone (μ - Λ) := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨S, hSX, hfd, hSk, hxS⟩ := eigenspace_K_finite hE hVfd hVk hx
  obtain ⟨x1, hx1S, hkhw, hfx⟩ := exists_highest_weight_lift_pi (isKUnitary_of_isInfUnitary hU) φ hfd hSk
    (fun a b _ z hz => hφ a b z (mem_euler_eigenspace_iff.1 (hSX hz)).1) hxS hμ
  have hx10 : x1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfx
    exact hy0 hfx.symm
  exact hK2 μ x1 (hSX hx1S) hx10 hkhw

end HidaSetting

section Gen

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
  {N : Type*} [AddCommGroup N] [Module ℂ N] {EN : Fin n → Fin n → Module.End ℂ N}

theorem exists_commuting_projection_image (V : Submodule ℂ M)
    (hGen : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) →
      f ∈ genSub (tensVd E) (Submodule.pi Set.univ fun _ => V))
    (P : Module.End ℂ (Fin n → M)) (hPg : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) → ∀ c, P f c ∈ genSub E V)
    (hPc : ∀ a b, Commute P (tensVd E a b)) (φ : (Fin n → M) →ₗ[ℂ] N)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensVd E a b f) = EN a b (φ f))
    {x : Fin n → M} (hx : ∀ c, x c ∈ genSub E V) (hPx : φ (P x) ≠ 0) :
    ∃ u : Fin n → M, (∀ c, u c ∈ V) ∧ φ (P u) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => generated_submodule_stable_under_action V a b hv
  set T : Submodule ℂ (Fin n → M) :=
    Submodule.pi Set.univ (fun _ => genSub E V) ⊓ LinearMap.ker (φ ∘ₗ P) with hT
  have hle : genSub (tensVd E) (Submodule.pi Set.univ fun _ => V) ≤ T := by
    unfold genSub
    refine sInf_le ⟨fun u hu => ⟨mem_pi_submodule_iff.2 fun c => le_generatedSubmodule_dual V (mem_pi_submodule_iff.1 hu c), ?_⟩,
      fun a b v hv => ⟨mem_pi_submodule_iff.2 (dualTensorAction_mem hGs a b (mem_pi_submodule_iff.1 hv.1)), ?_⟩⟩
    · exact LinearMap.mem_ker.2 (hcon u (mem_pi_submodule_iff.1 hu))
    · have hv2 : φ (P v) = 0 := LinearMap.mem_ker.1 hv.2
      refine LinearMap.mem_ker.2 ?_
      rw [LinearMap.comp_apply]
      have hc := (hPc a b).eq
      have : P (tensVd E a b v) = tensVd E a b (P v) := by
        rw [← Module.End.mul_apply, hc, Module.End.mul_apply]
      rw [this, hφ a b _ (hPg v (mem_pi_submodule_iff.1 hv.1)), hv2, map_zero]
  have hxT := hle (hGen x hx)
  exact hPx (LinearMap.mem_ker.1 hxT.2)

end Gen

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
