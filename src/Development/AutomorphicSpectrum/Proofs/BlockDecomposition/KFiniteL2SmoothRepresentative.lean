module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeafBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionSmoothLieDerivative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JCh

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExponentialPathExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExponentialPathExists
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.KCurve

section
open scoped Matrix.Norms.L2Operator

theorem exists_exp_eq_of_unitary {n : ℕ} (k : Matrix (Fin n) (Fin n) ℂ)
    (hu : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp Y = k := by
  haveI : IsStarNormal k :=
    ⟨(Unitary.star_mul_self_of_mem hu).trans (Unitary.mul_star_self_of_mem hu).symm⟩
  have hfin := Matrix.finite_spectrum k
  have hunit : IsUnit k := (Unitary.toUnits ⟨k, hu⟩).isUnit
  have hne : ∀ x ∈ spectrum ℂ k, x ≠ 0 := fun x hx h0 =>
    (spectrum.zero_notMem_iff ℂ).mpr hunit (h0 ▸ hx)
  refine ⟨cfc Complex.log k, ?_⟩
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) (p := IsStarNormal) (a := cfc Complex.log k),
    ← cfc_comp (R := ℂ) (p := IsStarNormal) NormedSpace.exp Complex.log k
      (hg := (hfin.image _).continuousOn _) (hf := hfin.continuousOn _)]
  have hc : cfc (NormedSpace.exp ∘ Complex.log) k = cfc (id : ℂ → ℂ) k := by
    refine cfc_congr fun x hx => ?_
    simp only [Function.comp, id]
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_log (hne x hx)]
  rw [hc, cfc_id ℂ k]

end

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def atPlace (w : InfinitePlace E) :
    Matrix (Fin a) (Fin a) (Cinf E) →+* Matrix (Fin a) (Fin a) ℂ :=
  (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix

theorem atPlace_apply (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) :
    atPlace w x i j = x i j w := rfl

theorem continuous_atPlace (w : InfinitePlace E) :
    Continuous (atPlace (a := a) w) :=
  continuous_id.matrix_map (continuous_apply w)

theorem atPlace_star (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) (Cinf E)) :
    atPlace w (star x) = star (atPlace w x) := by
  ext i j
  rfl

theorem exists_exp_eq (k : Kinf E a) :
    ∃ M : Matrix (Fin a) (Fin a) (Cinf E), NormedSpace.exp M = k.1 := by
  have hk : ∀ w, atPlace w k.1 ∈ unitary (Matrix (Fin a) (Fin a) ℂ) := fun w =>
    Unitary.mem_iff.mpr
      ⟨by rw [← atPlace_star, ← map_mul, Unitary.star_mul_self_of_mem k.2, map_one],
       by rw [← atPlace_star, ← map_mul, Unitary.mul_star_self_of_mem k.2, map_one]⟩
  choose Y hY using fun w => exists_exp_eq_of_unitary (atPlace w k.1) (hk w)
  refine ⟨Matrix.of fun i j w => Y w i j, Matrix.ext fun i j => ?_⟩
  funext w
  have h1 := congrArg (fun m => m i j)
    (NormedSpace.map_exp (atPlace w) (continuous_atPlace w) (Matrix.of fun i j w => Y w i j))
  have hM : atPlace w (Matrix.of fun i j w => Y w i j) = Y w := by
    ext i' j'
    rfl
  simp only [atPlace_apply, hM] at h1
  exact h1.trans ((congrArg (fun m => m i j) (hY w)).trans (atPlace_apply w k.1 i j))

theorem exists_curve : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (k : Kinf E a), ∃ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 ∧ c 1 = Unitary.toUnits k ∧ (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) ∧ (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) := by
  intro E _ _ _ a k
  obtain ⟨M, hM⟩ := exists_exp_eq k
  have htoL : ∀ N : Matrix (Fin a) (Fin a) (Cinf E), toL N = GlobalTheory.CompanionTheory.LieCurve.toLieL E a N := fun N => by
    rw [GlobalTheory.CompanionTheory.LieCurve.toLieL_apply]
  have hof : Matrix.of (GlobalTheory.CompanionTheory.LieCurve.toLieL E a M) = M := by
    rw [GlobalTheory.CompanionTheory.LieCurve.toLieL_apply]
    rfl
  refine ⟨GlobalTheory.CompanionTheory.LieCurve.expUnit E a M, GlobalTheory.CompanionTheory.LieCurve.toLieL E a M,
    GlobalTheory.CompanionTheory.LieCurve.expUnit_zero E a M, ?_, fun s => ?_, fun s => ?_⟩
  · apply Units.ext
    rw [GlobalTheory.CompanionTheory.LieCurve.expUnit_val, one_smul, hM]
    rfl
  · simp only [GlobalTheory.CompanionTheory.LieCurve.expUnit_val, hof, htoL]
    exact (GlobalTheory.CompanionTheory.LieCurve.toLieL E a).hasFDerivAt.comp_hasDerivAt s
      (GlobalTheory.CompanionTheory.LieCurve.hasDerivAt_exp E a M s)
  · simp only [GlobalTheory.CompanionTheory.LieCurve.expUnit_inv_val, hof, htoL]
    have h1 := GlobalTheory.CompanionTheory.LieCurve.hasDerivAt_exp E a (-M) s
    have e1 : (fun t : ℝ => NormedSpace.exp (t • -M)) = fun t : ℝ => NormedSpace.exp (-t • M) := by
      funext t
      rw [neg_smul, smul_neg]
    have e2 : NormedSpace.exp (s • -M) * -M = -(M * NormedSpace.exp (-s • M)) := by
      rw [smul_neg, ← neg_smul, mul_neg, ((Commute.refl M).smul_right (-s)).exp_right.eq]
    rw [e1, e2] at h1
    exact (GlobalTheory.CompanionTheory.LieCurve.toLieL E a).hasFDerivAt.comp_hasDerivAt s h1

end GlobalTheory.CompanionTheory.SmoothRep.KCurve
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExponentialPathExistsStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_exponential_path_exists : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (k : Kinf E a), ∃ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 ∧ c 1 = Unitary.toUnits k ∧ (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) ∧ (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.KCurve.exists_curve | exact GlobalTheory.CompanionTheory.SmoothRep.KCurve.exists_curve | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.KCurve.exists_curve <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesOneParameterFlow
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesOneParameterFlow
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Flow

section Abstract

variable {A : Type} [Ring A] [Algebra ℂ A]

def HD (f f' : ℝ → A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (p p' : ι → ℝ → ℂ) (C : ι → A),
    (∀ i s, HasDerivAt (p i) (p' i s) s) ∧ (∀ s, f s = ∑ i, p i s • C i) ∧ ∀ s, f' s = ∑ i, p' i s • C i

theorem HD.congr {f f' g g' : ℝ → A} (h : HD f f') (e : ∀ s, g s = f s) (e' : ∀ s, g' s = f' s) : HD g g' := by
  obtain ⟨ι, i, p, p', C, h1, h2, h3⟩ := h
  exact ⟨ι, i, p, p', C, h1, fun s => (e s).trans (h2 s), fun s => (e' s).trans (h3 s)⟩

theorem HD.const (C : A) : HD (fun _ => C) (fun _ => 0) :=
  ⟨Unit, inferInstance, fun _ _ => 1, fun _ _ => 0, fun _ => C, fun _ s => hasDerivAt_const s 1, by simp, by simp⟩

theorem HD.add {f f' g g' : ℝ → A} (h : HD f f') (k : HD g g') :
    HD (fun s => f s + g s) (fun s => f' s + g' s) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  obtain ⟨κ, _, q, q', D, k1, k2, k3⟩ := k
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim p q, Sum.elim p' q', Sum.elim C D, ?_, ?_, ?_⟩
  · rintro (i | j) s
    · exact h1 i s
    · exact k1 j s
  · intro s; simp [h2, k2]
  · intro s; simp [h3, k3]

theorem HD.mul {f f' g g' : ℝ → A} (h : HD f f') (k : HD g g') :
    HD (fun s => f s * g s) (fun s => f' s * g s + f s * g' s) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  obtain ⟨κ, _, q, q', D, k1, k2, k3⟩ := k
  refine ⟨ι × κ, inferInstance, fun x s => p x.1 s * q x.2 s,
    fun x s => p' x.1 s * q x.2 s + p x.1 s * q' x.2 s, fun x => C x.1 * D x.2, ?_, ?_, ?_⟩
  · intro x s; exact (h1 x.1 s).mul (k1 x.2 s)
  · intro s
    simp only [h2, k2, Finset.sum_mul_sum, Fintype.sum_prod_type, smul_mul_smul_comm]
  · intro s
    simp only [h2, h3, k2, k3, Finset.sum_mul_sum, Fintype.sum_prod_type, smul_mul_smul_comm, add_smul,
      Finset.sum_add_distrib]

theorem HD.const_of_zero {f : ℝ → A} (h : HD f (fun _ => 0)) (l : A →ₗ[ℂ] ℂ) (s t : ℝ) : l (f s) = l (f t) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  have hd : ∀ s, HasDerivAt (fun s => l (f s)) 0 s := by
    intro s
    have h4 : HasDerivAt (fun s => ∑ i, p i s * l (C i)) (∑ i, p' i s * l (C i)) s :=
      HasDerivAt.fun_sum fun i _ => (h1 i s).mul_const _
    have e1 : (fun s => l (f s)) = fun s => ∑ i, p i s * l (C i) := by
      funext s; simp [h2, map_sum]
    have e2 : ∑ i, p' i s * l (C i) = 0 := by
      have := congrArg l (h3 s)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum] using this.symm
    rw [e1]
    rwa [e2] at h4
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) s t

theorem hd_adjoin (R Q : ℝ → A) (hRQ : ∀ s, R s * Q s = 1) (hQR : ∀ s, Q s * R s = 1) (L : A) (G : Set A)
    (hG : ∀ B ∈ G, HD (fun s => R s * B * Q s) (fun s => R s * (L * B - B * L) * Q s)) :
    ∀ B ∈ Algebra.adjoin ℂ G, HD (fun s => R s * B * Q s) (fun s => R s * (L * B - B * L) * Q s) := by
  have hmul : ∀ s x y, R s * x * Q s * (R s * y * Q s) = R s * (x * y) * Q s := by
    intro s x y
    calc R s * x * Q s * (R s * y * Q s) = R s * x * (Q s * R s) * y * Q s := by simp only [mul_assoc]
      _ = R s * (x * y) * Q s := by rw [hQR]; simp only [mul_assoc, mul_one]
  intro B hB
  induction hB using Algebra.adjoin_induction with
  | mem x hx => exact hG x hx
  | algebraMap r =>
    refine (HD.const (algebraMap ℂ A r)).congr (fun s => ?_) (fun s => ?_)
    · rw [← Algebra.commutes, mul_assoc, hRQ, mul_one]
    · rw [Algebra.commutes, sub_self]; simp
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr (fun s => ?_) (fun s => ?_)
    · noncomm_ring
    · noncomm_ring
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr (fun s => ?_) (fun s => ?_)
    · rw [hmul]
    · rw [hmul, hmul, ← add_mul, ← mul_add]
      congr 2
      noncomm_ring

end Abstract

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem Zalg_le : Zalg E a ≤ Algebra.adjoin ℂ (Set.range (lie E a)) := by
  set S := Algebra.adjoin ℂ (Set.range (lie E a)) with hSdef
  have hL : ∀ X, lie E a X ∈ S := fun X => Algebra.subset_adjoin ⟨X, rfl⟩
  have hS : ∀ i j x, lieS E a i j x ∈ S := fun i j x => by rw [lieS_apply]; exact hL _
  have hE : ∀ (τ : E →+* ℂ) i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hS _ _ _) (S.smul_mem (hS _ _ _) _)) _
  refine Algebra.adjoin_le ?_
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem hd_lie {F F' : ℝ → Lie E a} (h : ∀ s, HasDerivAt F (F' s) s) :
    HD (fun s => lie E a (F s)) (fun s => lie E a (F' s)) := by
  classical
  let b := Module.finBasis ℝ (Lie E a)
  have hsum : ∀ X : Lie E a, lie E a X = ∑ m, ((b.repr X m : ℝ) : ℂ) • lie E a (b m) := by
    intro X
    conv_lhs => rw [← b.sum_repr X]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul]
    exact (algebraMap_smul ℂ _ _).symm
  refine ⟨_, inferInstance, fun m s => ((b.repr (F s) m : ℝ) : ℂ), fun m s => ((b.repr (F' s) m : ℝ) : ℂ),
    fun m => lie E a (b m), fun m s => ?_, fun s => hsum _, fun s => hsum _⟩
  have hl := (LinearMap.toContinuousLinearMap (b.coord m)).hasFDerivAt.comp_hasDerivAt s (h s)
  exact hl.ofReal_comp

theorem hasDerivAt_matMul {u v : ℝ → Lie E a} {u' v' : Lie E a} {s : ℝ} (hu : HasDerivAt u u' s)
    (hv : HasDerivAt v v' s) :
    HasDerivAt (fun t => toL (Matrix.of (u t) * Matrix.of (v t)))
      (toL (Matrix.of u' * Matrix.of (v s) + Matrix.of (u s) * Matrix.of v')) s := by
  rw [hasDerivAt_pi] at hu hv ⊢
  intro i
  rw [hasDerivAt_pi]
  intro j
  have hu' := fun k => (hasDerivAt_pi.1 (hu i)) k
  have hv' := fun k => (hasDerivAt_pi.1 (hv k)) j
  have := HasDerivAt.fun_sum (u := Finset.univ) fun k (_ : k ∈ Finset.univ) => (hu' k).mul (hv' k)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using this

theorem zalg_comm_rt_curve : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g)) → ∀ z : Module.End ℂ (Sm E a), z ∈ Zalg E a → (∀ X : Lie E a, z * lie E a X = lie E a X * z) → ∀ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 → (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) → (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) → z * rt E a (infGL E a (c 1)) = rt E a (infGL E a (c 1)) * z := by
  intro E _ _ _ a hconj z hz hcomm c Y h0 hc hci
  let R : ℝ → Module.End ℂ (Sm E a) := fun s => rt E a (infGL E a (c s))
  let Q : ℝ → Module.End ℂ (Sm E a) := fun s => rt E a (infGL E a (c s)⁻¹)
  have hRQ : ∀ s, R s * Q s = 1 := fun s => by
    change rt E a _ * rt E a _ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hQR : ∀ s, Q s * R s = 1 := fun s => by
    change rt E a _ * rt E a _ = 1
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have hconj' : ∀ s X, R s * lie E a X * Q s =
      lie E a (toL ((c s).val * Matrix.of X * ((c s)⁻¹).val)) := by
    intro s X
    change rt E a (infGL E a (c s)) * lie E a X * Q s = _
    rw [hconj (c s) X, mul_assoc]
    rw [show rt E a (infGL E a (c s)) * Q s = 1 from hRQ s, mul_one]
  have hG : ∀ B ∈ Set.range (lie E a), HD (fun s => R s * B * Q s)
      (fun s => R s * (lie E a Y * B - B * lie E a Y) * Q s) := by
    rintro _ ⟨X, rfl⟩
    let W : Lie E a := toL (Matrix.of Y * Matrix.of X - Matrix.of X * Matrix.of Y)
    have hW : lie E a Y * lie E a X - lie E a X * lie E a Y = lie E a W := by
      rw [lie_comm]
      exact (map_sub (lie E a) _ _).symm
    refine (hd_lie (F := fun s => toL ((c s).val * Matrix.of X * ((c s)⁻¹).val))
      (F' := fun s => toL ((c s).val * Matrix.of W * ((c s)⁻¹).val)) fun s => ?_).congr
      (fun s => hconj' s X) (fun s => by rw [hW]; exact hconj' s W)
    have h1 := hasDerivAt_matMul (hc s) (hasDerivAt_const s X)
    have h2 := hasDerivAt_matMul h1 (hci s)
    refine HasDerivAt.congr_deriv h2 ?_
    change toL (((c s).val * Matrix.of Y * Matrix.of X + (c s).val * 0) * ((c s)⁻¹).val +
      ((c s).val * Matrix.of X) * (-(Matrix.of Y * ((c s)⁻¹).val))) =
      toL ((c s).val * (Matrix.of Y * Matrix.of X - Matrix.of X * Matrix.of Y) * ((c s)⁻¹).val)
    congr 1
    noncomm_ring
  have h := hd_adjoin R Q hRQ hQR (lie E a Y) _ hG z (Zalg_le hz)
  have h' : HD (fun s => R s * z * Q s) (fun _ => 0) :=
    h.congr (fun _ => rfl) fun s => by rw [hcomm Y, sub_self, mul_zero, zero_mul]
  let l : Sm E a → GA E a → (Module.End ℂ (Sm E a) →ₗ[ℂ] ℂ) := fun φ x =>
    { toFun := fun B => (B φ).1 x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have e1 : R 1 * z * Q 1 = R 0 * z * Q 0 :=
    LinearMap.ext fun φ => Subtype.ext <| funext fun x => h'.const_of_zero (l φ x) 1 0
  have hR0 : R 0 = 1 := by
    change rt E a (infGL E a (c 0)) = 1
    rw [h0, map_one, map_one]
  have hQ0 : Q 0 = 1 := by
    change rt E a (infGL E a (c 0)⁻¹) = 1
    rw [h0, inv_one, map_one, map_one]
  rw [hR0, hQ0, one_mul, mul_one] at e1
  change z * R 1 = R 1 * z
  calc z * R 1 = R 1 * z * Q 1 * R 1 := by rw [e1]
    _ = R 1 * z * (Q 1 * R 1) := by simp only [mul_assoc]
    _ = R 1 * z := by rw [hQR, mul_one]

end GlobalTheory.CompanionTheory.SmoothRep.Flow
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesOneParameterFlowStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_commutes_one_parameter_flow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g)) → ∀ z : Module.End ℂ (Sm E a), z ∈ Zalg E a → (∀ X : Lie E a, z * lie E a X = lie E a X * z) → ∀ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 → (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) → (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) → z * rt E a (infGL E a (c 1)) = rt E a (infGL E a (c 1)) * z := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.Flow.zalg_comm_rt_curve | exact GlobalTheory.CompanionTheory.SmoothRep.Flow.zalg_comm_rt_curve | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.Flow.zalg_comm_rt_curve <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionSplitCentreInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionSplitCentreInvariant
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem convR_lift_splitCentre_mul (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ)
    (F : L2 (latticeGL E a) μ) (hF : F ∈ L2cusp μ) (t : ℝ) (x : GA E a) :
    convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) =
      convR μ f (lift (latticeGL E a) F) x := by
  have hR := R_splitCentre (μ := μ) t hF
  have h1 := GlobalTheory.AutomorphicL2Unitary.lift_R (Γ := latticeGL E a) (μ := μ) (splitCentre E a t) F
  rw [hR] at h1
  have h2 := (measurePreserving_mul_left μ x).quasiMeasurePreserving.ae_eq h1
  unfold convR
  refine integral_congr_ae ?_
  filter_upwards [h2] with y hy
  have e : splitCentre E a t * x * y = x * y * splitCentre E a t := by
    rw [splitCentre_comm t x, mul_assoc, splitCentre_comm t y, ← mul_assoc]
  rw [e]
  exact congrArg (f y * ·) hy.symm

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionSplitCentreInvariantStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_convolution_split_centre_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ) (F : L2 (latticeGL E a) μ), F ∈ L2cusp μ → ∀ (t : ℝ) (x : GA E a), convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) = convR μ f (lift (latticeGL E a) F) x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul | exact GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslationLieConjugate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslationLieConjugate
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem rt_infGL_mul_lie (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (g : GL (Fin a) (Cinf E)) (X : Lie E a) :
    rt E a (infGL E a g) * lie E a X =
      lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g) := by
  refine LinearMap.ext fun ψ => Subtype.ext <| funext fun x => ?_
  have hd : DifferentiableAt ℝ (chart ψ.1 x) (toL g.val) :=
    (contDiffAt_chart ψ.2 x (val_mem_invSet g)).differentiableAt (by simp)
  have e1 : lmul (toL g.val) (oneL E a) = toL g.val := mul_one g.val
  have e2 : rmul (toL g.val) (oneL E a) = toL g.val := one_mul g.val
  have e3 : lmul (toL g.val) X = rmul (toL g.val) (toL (g.val * Matrix.of X * (g⁻¹).val)) := by
    change g.val * Matrix.of X = g.val * Matrix.of X * (g⁻¹).val * g.val
    rw [mul_assoc (g.val * Matrix.of X), ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  change fderiv ℝ (chart ψ.1 (x * infGL E a g)) (oneL E a) X =
    fderiv ℝ (chart (fun y => ψ.1 (y * infGL E a g)) x) (oneL E a)
      (toL (g.val * Matrix.of X * (g⁻¹).val))
  rw [chart_mul, chart_rt_inf,
    fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL g.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL g.val)).differentiableAt,
    e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [e3]

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslationLieConjugateStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translation_lie_conjugate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie | exact GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionDerivativeIsTest
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionDerivativeIsTest
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem contDiff_mulRight {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) :
    ContDiff ℝ ∞ (fun w : Lie E a => toL (Matrix.of w * Matrix.of X)) := by
  let L : Lie E a →ₗ[ℝ] Lie E a :=
    { toFun := fun w => toL (Matrix.of w * Matrix.of X)
      map_add' := fun w v => by
        simp only [toL]
        exact congrArg Matrix.of.symm (Matrix.add_mul (Matrix.of w) (Matrix.of v) (Matrix.of X))
      map_smul' := fun c w => by
        simp only [toL, RingHom.id_apply]
        exact congrArg Matrix.of.symm (Matrix.smul_mul c (Matrix.of w) (Matrix.of X)) }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem tsupport_dTest_subset {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) (β : Lie E a → ℂ) :
    tsupport (dTest X β) ⊆ tsupport β := by
  refine (closure_mono fun w hw => ?_).trans (tsupport_fderiv_subset ℝ (f := β))
  rw [Function.mem_support] at hw ⊢
  intro h
  apply hw
  simp [dTest, h]

theorem isTest_dTest (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ)
    (hβ : IsTest β) (X : Lie E a) : IsTest (dTest X β) := by
  have hfd := (contDiff_infty_iff_fderiv.mp hβ.contDiff).2
  refine IsTest.mk ?_ ?_ ?_
  · exact hfd.clm_apply (contDiff_mulRight X)
  · exact hβ.compact.mono' ((subset_tsupport _).trans (tsupport_dTest_subset X β))
  · exact (tsupport_dTest_subset X β).trans hβ.support

end GlobalTheory.CompanionTheory.SmoothRep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionDerivativeIsTestStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_function_derivative_is_test : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ), IsTest β → ∀ X : Lie E a, IsTest (dTest X β) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest | exact GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterEnvelopingCommutesLie
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterEnvelopingCommutesLie
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem Zalg_comm_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X : Lie E a, z * lie E a X = lie E a X * z :=
  GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie

end GlobalTheory.CompanionTheory.SmoothRep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterEnvelopingCommutesLieStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_enveloping_commutes_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X : Lie E a, z * lie E a X = lie E a X * z := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.Zalg_comm_lie | exact GlobalTheory.CompanionTheory.SmoothRep.Zalg_comm_lie | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.Zalg_comm_lie <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionMaximalCompactEquivariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionMaximalCompactEquivariant
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem tst_conj_Kinf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) {β : Lie E a → ℂ} (hβ : ConjInv β) (k : Kinf E a) (y : GA E a) :
    tst U β ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k))) = tst U β y := by
  have e : ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k)))⁻¹ =
      (infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k) := by group
  have hf : GeneralLinearGroup.map (pFin E) ((infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k)) =
      GeneralLinearGroup.map (pFin E) y⁻¹ := by
    simp only [map_mul, map_inv, pFin_infGL, inv_one, one_mul, mul_one]
  have hi : GeneralLinearGroup.map (pInf E) ((infGL E a (Unitary.toUnits k))⁻¹ * y⁻¹ * infGL E a (Unitary.toUnits k)) =
      (Unitary.toUnits k)⁻¹ * GeneralLinearGroup.map (pInf E) y⁻¹ * Unitary.toUnits k := by
    rw [map_mul, map_mul, map_inv, pInf_infGL]
  have hc := hβ k⁻¹ (toL (GeneralLinearGroup.map (pInf E) y⁻¹).val)
  have hv : toL ((k⁻¹ : Kinf E a).1 * Matrix.of (toL (GeneralLinearGroup.map (pInf E) y⁻¹).val) * star (k⁻¹ : Kinf E a).1) =
      toL ((Unitary.toUnits k)⁻¹ * GeneralLinearGroup.map (pInf E) y⁻¹ * Unitary.toUnits k).val := by
    have h1 : ((Unitary.toUnits k)⁻¹ : GL (Fin a) (Cinf E)).val = (k⁻¹ : Kinf E a).1 := by
      rw [← map_inv]; rfl
    have h2 : star (k⁻¹ : Kinf E a).1 = k.1 := by
      change star (star k.1) = k.1
      exact star_star _
    rw [h2, Units.val_mul, Units.val_mul, h1]
    rfl
  unfold tst ker
  rw [e, hf, hi, ← hv, hc]

theorem convR_tst_cpt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ), ConjInv β → ∀ (F : L2 (latticeGL E a) μ) (k : Kinf E a) (x : GA E a), convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F)) x = convR μ (tst U β) (lift (latticeGL E a) F) (x * infGL E a (Unitary.toUnits k)) := by
  intro E _ _ _ a μ _ _ U β hβ F k x
  have h1 : ∀ᵐ y ∂μ, lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F) (x * y) =
      lift (latticeGL E a) F (x * y * infGL E a (Unitary.toUnits k)) :=
    (measurePreserving_mul_left μ x).quasiMeasurePreserving.ae (lift_R (infGL E a (Unitary.toUnits k)) F)
  simp only [AutomorphicL2Unitary.convR]
  rw [← integral_mul_left_eq_self
      (fun y => tst U β y * lift (latticeGL E a) F (x * infGL E a (Unitary.toUnits k) * y)) (infGL E a (Unitary.toUnits k))⁻¹,
    ← integral_mul_right_eq_self
      (fun y => tst U β ((infGL E a (Unitary.toUnits k))⁻¹ * y) *
        lift (latticeGL E a) F (x * infGL E a (Unitary.toUnits k) * ((infGL E a (Unitary.toUnits k))⁻¹ * y)))
      (infGL E a (Unitary.toUnits k))]
  refine integral_congr_ae (h1.mono fun y hy => ?_)
  have e : x * infGL E a (Unitary.toUnits k) * ((infGL E a (Unitary.toUnits k))⁻¹ * (y * infGL E a (Unitary.toUnits k))) =
      x * y * infGL E a (Unitary.toUnits k) := by group
  simp only [tst_conj_Kinf U hβ k y, e, hy]

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionMaximalCompactEquivariantStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_maximal_compact_equivariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ), ConjInv β → ∀ (F : L2 (latticeGL E a) μ) (k : Kinf E a) (x : GA E a), convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F)) x = convR μ (tst U β) (lift (latticeGL E a) F) (x * infGL E a (Unitary.toUnits k)) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_tst_cpt | exact GlobalTheory.CompanionTheory.SmoothRep.convR_tst_cpt | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_tst_cpt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionRightInvariantOpenCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionRightInvariantOpenCompact
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem tst_finGL_inv_mul {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (u : GL (Fin a) (Af E)) (hu : u ∈ U)
    (y : GA E a) : tst U β ((finGL E a u)⁻¹ * y) = tst U β y := by
  have hinv : ((finGL E a u)⁻¹ * y)⁻¹ = y⁻¹ * finGL E a u := by
    rw [_root_.mul_inv_rev, inv_inv]
  have hfin : GeneralLinearGroup.map (pFin E) (y⁻¹ * finGL E a u)
      = GeneralLinearGroup.map (pFin E) y⁻¹ * u := by
    rw [map_mul, pFin_finGL]
  have hinf : GeneralLinearGroup.map (pInf E) (y⁻¹ * finGL E a u)
      = GeneralLinearGroup.map (pInf E) y⁻¹ := by
    rw [map_mul, pInf_finGL, mul_one]
  unfold tst ker
  rw [hinv, hfin, hinf]
  by_cases hm : GeneralLinearGroup.map (pFin E) y⁻¹ ∈ U
  · rw [if_pos (U.mul_mem hm hu), if_pos hm]
  · rw [if_neg (fun h => hm (by simpa using U.mul_mem h (U.inv_mem hu))), if_neg hm]

theorem convR_tst_mul_finGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ)
    (u : GL (Fin a) (Af E)) (hu : u ∈ U) (x : GA E a) :
    convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  unfold convR
  have h := integral_mul_left_eq_self (μ := μ)
    (fun y => tst U β ((finGL E a u)⁻¹ * y) * Fl (x * y)) (finGL E a u)
  simp only [inv_mul_cancel_left] at h
  simp only [tst_finGL_inv_mul U β u hu] at h
  simpa only [mul_assoc] using h

theorem convR_tst_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (u : GL (Fin a) (Af E)), u ∈ U → ∀ x : GA E a, convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  intro E _ _ _ a μ _ _ U β Fl u hu x
  exact convR_tst_mul_finGL E a μ U β Fl u hu x

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvolutionRightInvariantOpenCompactStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_right_invariant_open_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (u : GL (Fin a) (Af E)), u ∈ U → ∀ x : GA E a, convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_tst_right_invariant | exact GlobalTheory.CompanionTheory.SmoothRep.convR_tst_right_invariant | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_tst_right_invariant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteL2SmoothRepresentative
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Rep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

omit μ in
theorem continuous_tst {U : Subgroup (GL (Fin a) (Af E))} (hUo : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {β : Lie E a → ℂ} (hβ : IsTest β) :
    Continuous (tst U β) ∧ HasCompactSupport (tst U β) := GlobalTheory.T.test_function_continuous_compact_support E a U hUo hUc β hβ

theorem cv_mem_Sm {U : Subgroup (GL (Fin a) (Af E))} (hUo : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ}
    (hFl : LocallyIntegrable Fl μ) : convR μ (tst U β) Fl ∈ Sm E a :=
  (GlobalTheory.T.convolution_smooth_lie_derivative E a μ U hUo hUc β hβ Fl hFl).1

omit μ in
theorem isTest_dTest {β : Lie E a → ℂ} (hβ : IsTest β) (X : Lie E a) : IsTest (dTest X β) := GlobalTheory.T.test_function_derivative_is_test E a β hβ X

theorem lieD_cv {U : Subgroup (GL (Fin a) (Af E))} (hUo : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ}
    (hFl : LocallyIntegrable Fl μ) (X : Lie E a) (g : GA E a) :
    lieD X (convR μ (tst U β) Fl) g = convR μ (tst U (dTest X β)) Fl g :=
  (GlobalTheory.T.convolution_smooth_lie_derivative E a μ U hUo hUc β hβ Fl hFl).2 X g

theorem cv_fin (U : Subgroup (GL (Fin a) (Af E))) (β : Lie E a → ℂ) (Fl : GA E a → ℂ) {u : GL (Fin a) (Af E)} (hu : u ∈ U)
    (x : GA E a) : convR μ (tst U β) Fl (x * finGL E a u) = convR μ (tst U β) Fl x := GlobalTheory.T.convolution_right_invariant_open_compact E a μ U β Fl u hu x

theorem cv_cpt (U : Subgroup (GL (Fin a) (Af E))) {β : Lie E a → ℂ} (hβ : ConjInv β) (F : L2 (latticeGL E a) μ) (k : Kinf E a)
    (x : GA E a) :
    convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) F)) x =
      convR μ (tst U β) (lift (latticeGL E a) F) (x * infGL E a (Unitary.toUnits k)) := GlobalTheory.T.convolution_maximal_compact_equivariant E a μ U β hβ F k x

theorem cv_split (f : GA E a → ℂ) {F : L2 (latticeGL E a) μ} (hF : F ∈ L2cusp μ) (t : ℝ) (x : GA E a) :
    convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) = convR μ f (lift (latticeGL E a) F) x :=
  GlobalTheory.T.cuspidal_convolution_split_centre_invariant E a μ f F hF t x

theorem exists_injective (U : Subgroup (GL (Fin a) (Af E))) (hUo : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) (X : Submodule ℂ (L2 (latticeGL E a) μ)) [hX' : FiniteDimensional ℂ X]
    (hX : ∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) :
    ∃ β : Lie E a → ℂ, IsTest β ∧ ConjInv β ∧ ∀ v ∈ X, Rop (latticeGL E a) μ (tst U β) v = 0 → v = 0 :=
  GlobalTheory.T.exists_test_function_fixed_subspace E a μ U hUo hUc X hX' hX

theorem exists_typeSpace (H : Submodule ℂ (L2 (latticeGL E a) μ)) (hH : H ≤ L2cusp μ)
    (hI : IsIrredSubrep (R (latticeGL E a) μ) H) (F : L2 (latticeGL E a) μ) (hFH : F ∈ H) (hF : IsKFinL2 μ F) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧
      ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧
        (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧
        (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧
        ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ,
          (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) =
            R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) →
          (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) →
            B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) →
          ∀ v ∈ X, B v ∈ X := GlobalTheory.T.k_finite_irreducible_fixed_vectors E a μ H hH hI F hFH hF


omit μ in
theorem Zalg_comm_cptRep {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (k : Kinf E a) :
    z * cptRep E a k = cptRep E a k * z := by
  obtain ⟨c, Y, h0, h1, hd, hi⟩ := GlobalTheory.T.unitary_exponential_path_exists E a k
  have h := GlobalTheory.T.center_commutes_one_parameter_flow E a (GlobalTheory.T.right_translation_lie_conjugate E a) z hz (GlobalTheory.T.center_enveloping_commutes_lie E a z hz) c Y h0 hd hi
  rw [h1] at h
  exact h


omit μ in
theorem Zalg_le (S : Subalgebra ℂ (Module.End ℂ (Sm E a))) (h : ∀ X, lie E a X ∈ S) : Zalg E a ≤ S := by
  have hE : ∀ τ i j, Eop (a := a) τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (h _) (S.smul_mem (h _) _)) _
  refine Algebra.adjoin_le ?_
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem fd_span (X : Submodule ℂ (L2 (latticeGL E a) μ)) [FiniteDimensional ℂ X] (S : Set (Sm E a))
    (hS : ∀ ψ ∈ S, Continuous ψ.1 ∧ LeftInv (latticeGL E a) ψ.1 ∧ ∃ v ∈ X, lift (latticeGL E a) v =ᵐ[μ] ψ.1) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  let V : Submodule ℂ (Sm E a) :=
    { carrier := {ψ | Continuous ψ.1 ∧ LeftInv (latticeGL E a) ψ.1 ∧ ∃ v ∈ X, lift (latticeGL E a) v =ᵐ[μ] ψ.1}
      zero_mem' := ⟨continuous_zero, fun _ _ _ => rfl, 0, zero_mem _, ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)⟩
      add_mem' := fun {φ ψ} ⟨h1, h2, v, hv, e⟩ ⟨h1', h2', v', hv', e'⟩ =>
        ⟨h1.add h1', fun γ hγ g => congrArg₂ (· + ·) (h2 γ hγ g) (h2' γ hγ g), v + v', add_mem hv hv',
          Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add v v')) (e.add e')⟩
      smul_mem' := fun c φ ⟨h1, h2, v, hv, e⟩ =>
        ⟨h1.const_smul c, fun γ hγ g => congrArg (c • ·) (h2 γ hγ g), c • v, Submodule.smul_mem _ c hv,
          Filter.EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c v)) (e.const_smul c)⟩ }
  have hm : ∀ φ ∈ V, MemL2Quotient (latticeGL E a) μ φ.1 := fun φ ⟨_, h2, v, _, e⟩ => memL2_of_ae_eq h2 e
  have hinj := toL2ₗ_injective hm fun φ hφ => hφ.1
  have hr : ∀ φ : V, toL2ₗ μ V hm φ ∈ X := fun φ => by
    obtain ⟨_, _, v, hv, e⟩ := φ.2
    have : toL2ₗ μ V hm φ = v := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ((lift_toL2ₗ hm φ).trans e.symm)
    rwa [this]
  have : FiniteDimensional ℂ V :=
    FiniteDimensional.of_injective ((toL2ₗ μ V hm).codRestrict X hr) fun x y e => hinj (congrArg Subtype.val e)
  exact Submodule.finiteDimensional_of_le (S₂ := V) (Submodule.span_le.2 hS)

variable {μ}
variable {U : Subgroup (GL (Fin a) (Af E))}

theorem locallyIntegrable_mul_left {Fl : GA E a → ℂ} (hFl : LocallyIntegrable Fl μ) (x : GA E a) :
    LocallyIntegrable (fun y => Fl (x * y)) μ := by
  refine locallyIntegrable_iff.2 fun K hK => ?_
  have h1 := locallyIntegrable_iff.1 hFl _ (hK.image (continuous_const_mul x))
  have h2 := ((measurePreserving_mul_left μ x).integrableOn_comp_preimage
    (Homeomorph.mulLeft x).measurableEmbedding).2 h1
  refine h2.mono_set fun y hy => ⟨y, hy, rfl⟩

theorem integrable_tst_mul (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ} (hFl : LocallyIntegrable Fl μ) (x : GA E a) :
    Integrable (fun y => tst U β y * Fl (x * y)) μ := by
  obtain ⟨h1, h2⟩ := continuous_tst hUo hUc hβ
  exact (locallyIntegrable_mul_left hFl x).integrable_smul_left_of_hasCompactSupport h1 h2

theorem tst_add (β β' : Lie E a → ℂ) (y : GA E a) : tst U (β + β') y = tst U β y + tst U β' y := by
  unfold tst ker
  split_ifs <;> simp

theorem tst_smul (c : ℂ) (β : Lie E a → ℂ) (y : GA E a) : tst U (c • β) y = c * tst U β y := by
  unfold tst ker
  split_ifs <;> simp

theorem IsTest.add {β β' : Lie E a → ℂ} (h : IsTest β) (h' : IsTest β') : IsTest (β + β') :=
  ⟨h.contDiff.add h'.contDiff, h.compact.add h'.compact, (closure_mono (Function.support_add β β')).trans (by
    rw [closure_union]; exact Set.union_subset h.support h'.support)⟩

theorem IsTest.smul {β : Lie E a → ℂ} (h : IsTest β) (c : ℂ) : IsTest (c • β) :=
  ⟨h.contDiff.const_smul c, h.compact.mono (Function.support_const_smul_subset c β),
    (closure_mono (Function.support_const_smul_subset c β)).trans h.support⟩

theorem Zalg_cv (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    ∀ (β : Lie E a → ℂ) (hβ : IsTest β), ∃ β', IsTest β' ∧ ∀ (Fl : GA E a → ℂ) (hFl : LocallyIntegrable Fl μ),
      (z ⟨_, cv_mem_Sm μ hUo hUc hβ hFl⟩).1 = convR μ (tst U β') Fl := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ (β : Lie E a → ℂ) (hβ : IsTest β), ∃ β', IsTest β' ∧
        ∀ (Fl : GA E a → ℂ) (hFl : LocallyIntegrable Fl μ),
          (z ⟨_, cv_mem_Sm μ hUo hUc hβ hFl⟩).1 = convR μ (tst U β') Fl}
      mul_mem' := fun {x y} hx hy β hβ => by
        obtain ⟨β₁, h1, e1⟩ := hy β hβ
        obtain ⟨β₂, h2, e2⟩ := hx β₁ h1
        refine ⟨β₂, h2, fun Fl hFl => ?_⟩
        have e : y ⟨_, cv_mem_Sm μ hUo hUc hβ hFl⟩ = ⟨_, cv_mem_Sm μ hUo hUc h1 hFl⟩ := Subtype.ext (e1 Fl hFl)
        change (x (y _)).1 = _
        rw [e]
        exact e2 Fl hFl
      add_mem' := fun {x y} hx hy β hβ => by
        obtain ⟨β₁, h1, e1⟩ := hx β hβ
        obtain ⟨β₂, h2, e2⟩ := hy β hβ
        refine ⟨β₁ + β₂, IsTest.add h1 h2, fun Fl hFl => ?_⟩
        change (x _).1 + (y _).1 = _
        rw [e1 Fl hFl, e2 Fl hFl]
        funext g
        simp only [convR, tst_add, add_mul, Pi.add_apply]
        exact (integral_add (integrable_tst_mul hUo hUc h1 hFl g) (integrable_tst_mul hUo hUc h2 hFl g)).symm
      algebraMap_mem' := fun c β hβ => by
        refine ⟨c • β, IsTest.smul hβ c, fun Fl hFl => ?_⟩
        funext g
        change c * _ = _
        simp only [convR, tst_smul, mul_assoc]
        exact (integral_const_mul _ _).symm }
  refine Zalg_le S (fun X β hβ => ⟨dTest X β, isTest_dTest hβ X, fun Fl hFl => ?_⟩) hz
  funext g
  exact lieD_cv μ hUo hUc hβ hFl X g

theorem lift_Rop_tst (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) (G : L2 (latticeGL E a) μ) :
    lift (latticeGL E a) (Rop (latticeGL E a) μ (tst U β) G) =ᵐ[μ] convR μ (tst U β) (lift (latticeGL E a) G) := by
  obtain ⟨h1, h2⟩ := continuous_tst hUo hUc hβ
  exact (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR (GA E a) (latticeGL E a) μ _ (h1.integrable_of_hasCompactSupport h2) G).2

theorem R_Rop_fin (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) (G : L2 (latticeGL E a) μ) {u : GL (Fin a) (Af E)} (hu : u ∈ U) :
    R (latticeGL E a) μ (finGL E a u) (Rop (latticeGL E a) μ (tst U β) G) = Rop (latticeGL E a) μ (tst U β) G := by
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have h := lift_Rop_tst hUo hUc hβ G
  filter_upwards [lift_R (finGL E a u) (Rop (latticeGL E a) μ (tst U β) G),
    (measurePreserving_mul_right μ (finGL E a u)).quasiMeasurePreserving.ae h, h] with x e1 e2 e3
  rw [e1, e2, cv_fin μ U β _ hu, e3]

theorem Rop_R_comm (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) (g : GA E a)
    (hK : ∀ (G : L2 (latticeGL E a) μ) (x : GA E a),
      convR μ (tst U β) (lift (latticeGL E a) (R (latticeGL E a) μ g G)) x =
        convR μ (tst U β) (lift (latticeGL E a) G) (x * g)) (G : L2 (latticeGL E a) μ) :
    Rop (latticeGL E a) μ (tst U β) (R (latticeGL E a) μ g G) =
      R (latticeGL E a) μ g (Rop (latticeGL E a) μ (tst U β) G) := by
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have h := lift_Rop_tst hUo hUc hβ G
  filter_upwards [lift_R g (Rop (latticeGL E a) μ (tst U β) G),
    (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h,
    lift_Rop_tst hUo hUc hβ (R (latticeGL E a) μ g G)] with x e1 e2 e3
  rw [e1, e2, e3, hK]

variable (μ) in
theorem isOpen_level (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ} (hFl : LocallyIntegrable Fl μ) :
    IsOpen {k | finRep E a k ⟨_, cv_mem_Sm μ hUo hUc hβ hFl⟩ = ⟨_, cv_mem_Sm μ hUo hUc hβ hFl⟩} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hUo.mem_nhds U.one_mem) fun u hu =>
    Subtype.ext (funext fun x => cv_fin μ U β Fl hu x))

theorem smooth_rep (H : Submodule ℂ (L2 (latticeGL E a) μ)) (hH : H ≤ L2cusp μ)
    (hI : IsIrredSubrep (R (latticeGL E a) μ) H) (F : L2 (latticeGL E a) μ) (hFH : F ∈ H) (hF : IsKFinL2 μ F) :
    ∃ φ : Sm E a, lift (latticeGL E a) F =ᵐ[μ] φ.1 ∧ MemL2Quotient (latticeGL E a) μ φ.1 ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧
      (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) ∧
      FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) := by
  obtain ⟨U, hUo, hUc, X, hXf, hFX, hXH, hXk, hXu, hXB⟩ := exists_typeSpace μ H hH hI F hFH hF
  obtain ⟨β, hβ, hβc, hinj⟩ := exists_injective μ U hUo hUc X hXu
  have hloc : ∀ G : L2 (latticeGL E a) μ, LocallyIntegrable (lift (latticeGL E a) G) μ := fun G =>
    GlobalTheory.CuspAE.locallyIntegrable_lift G
  have hint : ∀ β' : Lie E a → ℂ, IsTest β' → Integrable (tst U β') μ := fun β' h =>
    (continuous_tst hUo hUc h).1.integrable_of_hasCompactSupport (continuous_tst hUo hUc h).2
  have hstab : ∀ β' : Lie E a → ℂ, IsTest β' →
      (∀ (k : Kinf E a) (G : L2 (latticeGL E a) μ) (x : GA E a),
        convR μ (tst U β') (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) G)) x =
        convR μ (tst U β') (lift (latticeGL E a) G) (x * infGL E a (Unitary.toUnits k))) →
      ∀ v ∈ X, Rop (latticeGL E a) μ (tst U β') v ∈ X := fun β' h hK =>
    hXB (Rop (latticeGL E a) μ (tst U β')).toLinearMap (fun k v => Rop_R_comm hUo hUc h _ (hK k) v)
      fun v hv _ => ⟨hI.1.Rop_mem (hint β' h) hv, fun u hu => R_Rop_fin hUo hUc h v hu⟩
  have hKβ := fun k G x => cv_cpt μ U hβc G k x
  let A : X →ₗ[ℂ] X := LinearMap.restrict (Rop (latticeGL E a) μ (tst U β)).toLinearMap (hstab β hβ hKβ)
  have hAi : Function.Injective A := (injective_iff_map_eq_zero A).2 fun v hv =>
    Subtype.ext (hinj v.1 v.2 (congrArg Subtype.val hv))
  obtain ⟨G, hG⟩ := LinearMap.injective_iff_surjective.1 hAi ⟨F, hFX⟩
  have hGF : Rop (latticeGL E a) μ (tst U β) G.1 = F := congrArg Subtype.val hG
  have hGc : G.1 ∈ L2cusp μ := hH (hXH G.2)
  have hrep := lift_Rop_tst hUo hUc hβ G.1
  rw [hGF] at hrep
  have hcv : ∀ (β' : Lie E a → ℂ) (h : IsTest β') (v : L2 (latticeGL E a) μ), v ∈ X →
      (∀ (k : Kinf E a) (G : L2 (latticeGL E a) μ) (x : GA E a),
        convR μ (tst U β') (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) G)) x =
        convR μ (tst U β') (lift (latticeGL E a) G) (x * infGL E a (Unitary.toUnits k))) →
      Continuous (convR μ (tst U β') (lift (latticeGL E a) v)) ∧
        LeftInv (latticeGL E a) (convR μ (tst U β') (lift (latticeGL E a) v)) ∧
        ∃ w ∈ X, lift (latticeGL E a) w =ᵐ[μ] convR μ (tst U β') (lift (latticeGL E a) v) := fun β' h v hv hK =>
    ⟨ContAut.continuous_of_isOpen_stab E a ⟨_, cv_mem_Sm μ hUo hUc h (hloc v)⟩ (isOpen_level μ hUo hUc h (hloc v)),
      (leftInv_lift v).convR _, _, hstab β' h hK v hv, lift_Rop_tst hUo hUc h v⟩
  refine ⟨⟨_, cv_mem_Sm μ hUo hUc hβ (hloc G.1)⟩, hrep, memL2_of_ae_eq ((leftInv_lift G.1).convR _) hrep,
    fun γ g => (leftInv_lift G.1).convR _ _ (ratGL_mem_latticeGL γ) g, fun t g => cv_split μ _ hGc t g,
    isOpen_level μ hUo hUc hβ (hloc G.1), ?_, ?_⟩
  · refine fd_span μ X _ ?_
    rintro _ ⟨k, rfl⟩
    have e : cptRep E a k ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc G.1)⟩ =
        ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) G.1))⟩ :=
      Subtype.ext (funext fun x => (hKβ k G.1 x).symm)
    beta_reduce
    rw [e]
    exact hcv β hβ _ (hXk k _ G.2) hKβ
  · refine fd_span μ X _ ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨β', h', e'⟩ := Zalg_cv hUo hUc hz μ β hβ
    have hK' : ∀ (k : Kinf E a) (G : L2 (latticeGL E a) μ) (x : GA E a),
        convR μ (tst U β') (lift (latticeGL E a) (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) G)) x =
        convR μ (tst U β') (lift (latticeGL E a) G) (x * infGL E a (Unitary.toUnits k)) := fun k G x => by
      have e : cptRep E a k ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc G)⟩ =
          ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) G))⟩ :=
        Subtype.ext (funext fun x => (hKβ k G x).symm)
      have h1 := LinearMap.congr_fun (Zalg_comm_cptRep hz k) ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc G)⟩
      simp only [Module.End.mul_apply, e] at h1
      have h2 := congrFun (congrArg Subtype.val h1) x
      rw [e' _ (hloc _)] at h2
      refine h2.trans ?_
      have h3 := congrFun (e' _ (hloc G)) (x * infGL E a (Unitary.toUnits k))
      exact h3
    have e2 : z ⟨_, cv_mem_Sm μ hUo hUc hβ (hloc G.1)⟩ = ⟨_, cv_mem_Sm μ hUo hUc h' (hloc G.1)⟩ :=
      Subtype.ext (e' _ (hloc G.1))
    beta_reduce
    rw [e2]
    exact hcv β' h' _ G.2 hK'

end GlobalTheory.CompanionTheory.SmoothRep.Rep

theorem GlobalTheory.CompanionTheory.SmoothRep.smoothRep : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ φ : Sm E a, lift (latticeGL E a) F =ᵐ[μ] φ.1 ∧ MemL2Quotient (latticeGL E a) μ φ.1 ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) ∧ FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) :=
  fun _ _ _ _ _ _ _ _ H hH hI F hFH hF => GlobalTheory.CompanionTheory.SmoothRep.Rep.smooth_rep H hH hI F hFH hF
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteL2SmoothRepresentativeStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.K_finite_L2_smooth_representative : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ φ : Sm E a, lift (latticeGL E a) F =ᵐ[μ] φ.1 ∧ MemL2Quotient (latticeGL E a) μ φ.1 ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) ∧ FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.smoothRep | exact GlobalTheory.CompanionTheory.SmoothRep.smoothRep | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.smoothRep <;> assumption)
end
