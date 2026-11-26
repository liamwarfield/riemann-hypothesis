module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusOfBasic
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace FunctionalCalculusInner

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}

theorem fc_basis (b : Module.Basis ι ℂ V) (μ : ι → ℝ) (φ : ℝ → ℝ) (i : ι) :
    fc b μ φ (b i) = ((φ (μ i) : ℝ) : ℂ) • b i := by
  unfold fc
  exact b.constr_basis ℂ _ i

theorem repr_fc (b : Module.Basis ι ℂ V) (μ : ι → ℝ) (φ : ℝ → ℝ) (v : V) (i : ι) :
    b.repr (fc b μ φ v) i = ((φ (μ i) : ℝ) : ℂ) * b.repr v i := by
  have key : (b.coord i).comp (fc b μ φ) = ((φ (μ i) : ℝ) : ℂ) • b.coord i := by
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, fc_basis, map_smul,
      LinearMap.smul_apply, Module.Basis.repr_self]
    by_cases hji : j = i
    · subst hji; simp
    · simp [Finsupp.single_apply, hji]
  exact LinearMap.congr_fun key v

theorem inner_basis_left (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (i : ι) (y : V) :
    inner ℂ (b i) y = b.repr y i := by
  classical
  have key : (innerₛₗ ℂ (b i) : V →ₗ[ℂ] ℂ) = b.coord i := by
    refine b.ext fun j => ?_
    show inner ℂ (b i) (b j) = b.repr (b j) i
    rw [Module.Basis.repr_self, orthonormal_iff_ite.mp hb i j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  exact LinearMap.congr_fun key y

theorem inner_eq_sum (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (x y : V) (s : Finset ι)
    (hs : (b.repr x).support ⊆ s) :
    inner ℂ x y = ∑ i ∈ s, starRingEnd ℂ (b.repr x i) * b.repr y i := by
  have hx : x = ∑ i ∈ s, b.repr x i • b i := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hs]
    intro i _
    simp
  conv_lhs => rw [hx]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_basis_left b hb]

theorem fc_id (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (b : Module.Basis ι ℂ V) (μ : ι → ℝ)
    (h : ∀ i, Eig ε E (μ i) (b i)) : fc b μ (fun x => x) = casimirK ε E :=
  b.ext fun i => by rw [fc_basis]; exact (h i).symm

theorem re_conj_mul (z : ℂ) (r : ℝ) : (starRingEnd ℂ z * ((r : ℂ) * z)).re = r * ‖z‖ ^ 2 := by
  rw [mul_left_comm, Complex.conj_mul']
  norm_cast

theorem re_inner_fc (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (μ : ι → ℝ) (φ : ℝ → ℝ) (w : V) :
    (inner ℂ w (fc b μ φ w)).re = ∑ i ∈ (b.repr w).support, φ (μ i) * ‖b.repr w i‖ ^ 2 := by
  rw [inner_eq_sum b hb w _ _ subset_rfl, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_fc, re_conj_mul]

end FunctionalCalculusInner

open FunctionalCalculusInner in
theorem functional_calculus_of_basic : A0 → FunctionalCalculusLaws := by
  intro _ n ε V _ _ E _ ι b μ hb
  have hid := fc_id ε E b μ hb.eig
  refine ⟨fun φ ν v hv => ?_, fun φ x y => ?_, fun φ ψ hφψ w => ?_, fun φ ψ => ?_, fun φ ψ => ?_,
    fun c => ?_, hid⟩
  · refine b.repr.injective (Finsupp.ext fun i => ?_)
    have h1 : b.repr (casimirK ε E v) i = b.repr ((ν : ℂ) • v) i := by rw [show casimirK ε E v = (ν : ℂ) • v from hv]
    rw [← hid, repr_fc] at h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    rw [repr_fc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases h0 : b.repr v i = 0
    · simp [h0]
    · have : μ i = ν := by
        have := mul_right_cancel₀ h0 h1
        exact_mod_cast this
      rw [this]
  · have hs : (b.repr (fc b μ φ x)).support ⊆ (b.repr x).support := by
      intro i hi
      rw [Finsupp.mem_support_iff] at hi ⊢
      rw [repr_fc] at hi
      exact right_ne_zero_of_mul hi
    rw [inner_eq_sum b hb.on _ _ _ hs, inner_eq_sum b hb.on _ _ _ subset_rfl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_fc, repr_fc, map_mul, Complex.conj_ofReal]
    ring
  · rw [re_inner_fc b hb.on, re_inner_fc b hb.on]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hφψ _ (hb.nonneg i)) (sq_nonneg _)
  · refine b.ext fun i => ?_
    simp only [fc_basis, LinearMap.add_apply, Complex.ofReal_add, add_smul]
  · refine b.ext fun i => ?_
    simp only [fc_basis, Module.End.mul_apply, map_smul, smul_smul, Complex.ofReal_mul, mul_comm]
  · refine b.ext fun i => ?_
    simp [fc_basis]

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KFiniteInclusion
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace WeightedEigenSum

theorem pow_eig {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (m : ℝ) (x : V)
    (h : T x = (m : ℂ) • x) (s : ℕ) : ((1 + T) ^ s) x = (((1 + m) ^ s : ℝ) : ℂ) • x := by
  induction s with
  | zero => simp
  | succ k ih =>
    have hx : x + (m : ℂ) • x = (((1 + m : ℝ)) : ℂ) • x := by
      push_cast
      rw [add_smul, one_smul]
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.add_apply, Module.End.one_apply, h, hx,
      smul_smul]
    congr 1
    push_cast
    ring

theorem wsum_le {ι : Type} (μ : ι → ℝ) (hnn : ∀ i, 0 ≤ μ i) (hfin : ∀ R : ℝ, {i | μ i ≤ R}.Finite)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (s : ℕ) (hs : 1 ≤ s) (K : ℝ)
    (hS : ∀ (R : ℝ) (S : Finset ι), (∀ i, i ∈ S ↔ μ i < R) → ∑ i ∈ S, phiR s R (μ i) * a i ≤ K ^ 2)
    (T : Finset ι) : ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i ≤ K ^ 2 := by
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, ∀ i ∈ T, μ i < R0 :=
    ⟨∑ i ∈ T, μ i + 1, fun i hi => by
      have := Finset.single_le_sum (fun j _ => hnn j) hi
      linarith⟩
  have key : ∀ R : ℝ, R0 ≤ R →
      ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i ≤ K ^ 2 := by
    intro R hR
    have hSmem : ∀ i, i ∈ (hfin R).toFinset.filter (fun i => μ i < R) ↔ μ i < R := by
      intro i
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
    have hTS : T ⊆ (hfin R).toFinset.filter (fun i => μ i < R) :=
      fun i hi => (hSmem i).mpr (lt_of_lt_of_le (hR0 i hi) hR)
    have h1 := hS R _ hSmem
    have h2 : ∑ i ∈ T, phiR s R (μ i) * a i ≤
        ∑ i ∈ (hfin R).toFinset.filter (fun i => μ i < R), phiR s R (μ i) * a i :=
      Finset.sum_le_sum_of_subset_of_nonneg hTS (fun i _ _ => mul_nonneg (le_max_right _ _) (ha i))
    have h3 : ∑ i ∈ T, phiR s R (μ i) * a i =
        ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hlt : ((1 + R) ^ s)⁻¹ ≤ ((1 + μ i) ^ s)⁻¹ := by
        apply inv_anti₀ (pow_pos (by linarith [hnn i]) s)
        exact pow_le_pow_left₀ (by linarith [hnn i]) (by linarith [hR0 i hi]) s
      rw [phiR, max_eq_left (by linarith)]
      ring
    linarith
  have hpow : Filter.Tendsto (fun R : ℝ => (1 + R) ^ s) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by omega : s ≠ 0)).comp
      (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
  have ht : Filter.Tendsto
      (fun R : ℝ => ∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - ((1 + R) ^ s)⁻¹ * ∑ i ∈ T, a i) Filter.atTop
      (nhds (∑ i ∈ T, ((1 + μ i) ^ s)⁻¹ * a i - 0 * ∑ i ∈ T, a i)) :=
    tendsto_const_nhds.sub ((tendsto_inv_atTop_zero.comp hpow).mul_const _)
  have hlim := le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨R0, key⟩)
  simpa using hlim

end WeightedEigenSum

theorem eigen_weighted_sum_bound : A0 → FunctionalCalculusLaws → B5 := by
  intro _ _ n ε V _ _ E _ ι b μ hb f s K hK hS hs v
  have hv : v = ∑ i ∈ (b.repr v).support, b.repr v i • b i := by
    conv_lhs => rw [← b.linearCombination_repr v]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hpos : ∀ i, 0 < (1 + μ i) ^ s := fun i => pow_pos (by linarith [hb.nonneg i]) s
  have heig : ∀ i, ((1 + casimirK ε E) ^ s) (b i) = (((1 + μ i) ^ s : ℝ) : ℂ) • b i :=
    fun i => WeightedEigenSum.pow_eig _ (μ i) (b i) (hb.eig i) s
  have hw : ((1 + casimirK ε E) ^ s) v =
      ∑ i ∈ (b.repr v).support, (b.repr v i * (((1 + μ i) ^ s : ℝ) : ℂ)) • b i := by
    conv_lhs => rw [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, heig, smul_smul]
  have hfv : f v = inner ℂ (∑ i ∈ (b.repr v).support,
      (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i) (((1 + casimirK ε E) ^ s) v) := by
    rw [hw, hb.on.inner_sum]
    conv_lhs => rw [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    have h1 : ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ) * (((1 + μ i) ^ s : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hpos i).ne', Complex.ofReal_one]
    linear_combination (-(b.repr v i * f (b i))) * h1
  have hu2 : ‖∑ i ∈ (b.repr v).support,
      (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i‖ ^ 2 ≤ K ^ 2 := by
    have e : ‖∑ i ∈ (b.repr v).support,
        (starRingEnd ℂ (f (b i)) * ((((1 + μ i) ^ s)⁻¹ : ℝ) : ℂ)) • b i‖ ^ 2 =
        ∑ i ∈ (b.repr v).support, ‖f (b i)‖ ^ 2 * (((1 + μ i) ^ s)⁻¹) ^ 2 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [@norm_sq_eq_re_inner ℂ, hb.on.inner_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hr : 0 ≤ ((1 + μ i) ^ s)⁻¹ := (inv_pos.mpr (hpos i)).le
      rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr, Complex.norm_conj, mul_pow]
    have e2 : ∑ i ∈ (b.repr v).support, ‖f (b i)‖ ^ 2 * (((1 + μ i) ^ s)⁻¹) ^ 2 ≤
        ∑ i ∈ (b.repr v).support, ((1 + μ i) ^ s)⁻¹ * ‖f (b i)‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h0 : 0 ≤ ((1 + μ i) ^ s)⁻¹ := (inv_pos.mpr (hpos i)).le
      have h1 : ((1 + μ i) ^ s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hb.nonneg i]))
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ‖f (b i)‖) h0) (sub_nonneg.mpr h1)]
    have e3 : ∑ i ∈ (b.repr v).support, ((1 + μ i) ^ s)⁻¹ * ‖f (b i)‖ ^ 2 ≤ K ^ 2 :=
      WeightedEigenSum.wsum_le μ hb.nonneg hb.fin (fun i => ‖f (b i)‖ ^ 2) (fun i => sq_nonneg _) s hs K hS _
    linarith
  have hu := (pow_le_pow_iff_left₀ (norm_nonneg _) hK two_ne_zero).mp hu2
  rw [hfv]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.WordFiltrationCommute
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenSumRepresentation

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}

lemma inner_basis {b : Module.Basis ι ℂ V} (hb : Orthonormal ℂ b) (i : ι) (y : V) :
    inner ℂ (b i) y = b.repr y i := by
  have h := hb.inner_right_finsupp (b.repr y) i
  rwa [b.linearCombination_repr] at h

lemma repr_sum {b : Module.Basis ι ℂ V} (T : Finset ι) (y : V) (hy : (b.repr y).support ⊆ T) :
    y = ∑ j ∈ T, b.repr y j • b j := by
  conv_lhs => rw [← b.linearCombination_repr y]
  rw [Finsupp.linearCombination_apply]
  exact Finsupp.sum_of_support_subset _ hy _ (fun i _ => zero_smul ℂ (b i))

lemma inner_h {b : Module.Basis ι ℂ V} (hb : Orthonormal ℂ b) (f : V →ₗ[ℂ] ℂ) (T : Finset ι) (y : V)
    (hy : (b.repr y).support ⊆ T) :
    inner ℂ (∑ j ∈ T, starRingEnd ℂ (f (b j)) • b j) y = f y := by
  rw [sum_inner]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [repr_sum (b := b) T y hy, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_basis hb, map_smul, smul_eq_mul, starRingEnd_self_apply, mul_comm]

lemma inner_fc {b : Module.Basis ι ℂ V} (hb : Orthonormal ℂ b) (μ : ι → ℝ) (φ : ℝ → ℝ) (S : Finset ι)
    (hS : ∀ i, i ∉ S → φ (μ i) = 0) (y : V) :
    inner ℂ y (fc b μ φ y) = ∑ i ∈ S, ((φ (μ i) * ‖b.repr y i‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hyU : (b.repr y).support ⊆ (b.repr y).support ∪ S := Finset.subset_union_left
  have hfc : fc b μ φ y = ∑ j ∈ (b.repr y).support ∪ S, b.repr y j • ((φ (μ j) : ℂ) • b j) := by
    conv_lhs => rw [repr_sum (b := b) _ y hyU]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, fc, Module.Basis.constr_basis]
  have key : ∀ j, inner ℂ y (b.repr y j • ((φ (μ j) : ℂ) • b j)) = ((φ (μ j) * ‖b.repr y j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [inner_smul_right, inner_smul_right, ← inner_conj_symm, inner_basis hb]
    push_cast
    rw [← Complex.mul_conj']
    ring
  rw [hfc, inner_sum, Finset.sum_congr rfl (fun j _ => key j)]
  symm
  apply Finset.sum_subset Finset.subset_union_right
  intro j _ hj
  rw [hS j hj]
  simp

lemma beta_sum {E : Fin n → Fin n → Module.End ℂ V} (A : Module.End ℂ V) {κ : Type} (s : Finset κ) (v : κ → V) :
    beta ε E A (∑ k ∈ s, v k) (∑ k ∈ s, v k) = ∑ l ∈ s, ∑ k ∈ s, beta ε E A (v k) (v l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [beta, map_sum, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

lemma eig_sum {E : Fin n → Fin n → Module.End ℂ V} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (heig : ∀ i, Eig ε E (μ i) (b i)) (s : Finset ι) (c : ι → ℂ) (ν : ℝ) (hs : ∀ j ∈ s, μ j = ν) :
    Eig ε E ν (∑ j ∈ s, c j • b j) := by
  unfold Eig
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, smul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [map_smul, show casimirK ε E (b j) = _ from heig j, hs j hj, smul_comm]

lemma mem_nc_swap {p : Fin n × Fin n} (hp : p ∈ nc ε) : p.swap ∈ nc ε := by
  simp only [nc, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact Ne.symm hp

end EigenSumRepresentation

open EigenSumRepresentation in
theorem basis_sum_of_orthogonality : A0 → FunctionalCalculusLaws → EigenspacesOrthogonalAlt → BasisSumAsFormValues := by
  intro _ _ h11c n ε V _ _ E hM ι b μ hB φ S hS
  classical
  set T : Finset ι := S ∪ S.biUnion (fun i => (nc ε).biUnion (fun p => (b.repr (E p.1 p.2 (b i))).support)) with hT
  refine ⟨T, Finset.subset_union_left, fun f => ?_⟩
  have hsupp : ∀ i ∈ S, ∀ p ∈ nc ε, (b.repr (E p.1 p.2 (b i))).support ⊆ T := by
    intro i hi p hp j hj
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_biUnion.2 ⟨p, hp, hj⟩⟩
  set H : V := ∑ j ∈ T, starRingEnd ℂ (f (b j)) • b j with hH
  have hinner : ∀ y, (b.repr y).support ⊆ T → inner ℂ H y = f y := fun y hy => inner_h hB.on f T y hy
  have hfib : ∑ ν ∈ image μ T, (∑ j ∈ T with μ j = ν, starRingEnd ℂ (f (b j)) • b j) = H :=
    Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem μ hj) _
  have heig : ∀ ν, Eig ε E ν (∑ j ∈ T with μ j = ν, starRingEnd ℂ (f (b j)) • b j) := fun ν =>
    eig_sum hB.eig _ (fun j => starRingEnd ℂ (f (b j))) ν (fun j hj => (Finset.mem_filter.1 hj).2)
  have hdiag : ∑ ν ∈ image μ T, beta ε E (fc b μ φ) (∑ j ∈ T with μ j = ν, starRingEnd ℂ (f (b j)) • b j)
      (∑ j ∈ T with μ j = ν, starRingEnd ℂ (f (b j)) • b j) = beta ε E (fc b μ φ) H H := by
    rw [← hfib, beta_sum (v := fun ν => ∑ j ∈ T with μ j = ν, starRingEnd ℂ (f (b j)) • b j)]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.sum_eq_single_of_mem l hl]
    intro k _ hk
    exact h11c n ε V E hM ι b μ hB φ k l _ _ hk (heig k) (heig l)
  rw [← Complex.re_sum, hdiag]
  have hterm : ∀ p ∈ nc ε, ∀ i ∈ S, ‖b.repr (E p.1 p.2 H) i‖ = ‖f (E p.2 p.1 (b i))‖ := by
    intro p hp i hi
    have hsw : (p.2, p.1) ∈ nc ε := mem_nc_swap hp
    have hsign : adjSign ε p.1 p.2 = -1 := by
      simp only [nc, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [adjSign, hp]
    rw [← inner_basis hB.on, ← inner_conj_symm, hM.uni p.1 p.2 H (b i), hinner _ (hsupp i hi _ hsw), hsign]
    simp
  have hbeta : beta ε E (fc b μ φ) H H =
      ∑ p ∈ nc ε, ∑ i ∈ S, ((φ (μ i) * ‖f (E p.2 p.1 (b i))‖ ^ 2 : ℝ) : ℂ) := by
    unfold beta
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [inner_fc hB.on μ φ S hS]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hterm p hp i hi]
  rw [hbeta, Finset.sum_comm]
  simp only [Complex.re_sum, Complex.ofReal_re]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_nbij' Prod.swap Prod.swap (fun p hp => mem_nc_swap hp) (fun p hp => mem_nc_swap hp)
    (fun p _ => rfl) (fun p _ => rfl) (fun p _ => rfl)

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MaximumPrincipleOfFacts
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace MaximumPrincipleOneFunction

variable {n : ℕ}

theorem step (hB3 : B3) (hB3g : UnitaryGroupFacts) (ε : Fin n → Bool) (r : ℕ) (u : Matrix (Fin n) (Fin n) ℂ → ℝ) (A η : ℝ)
    (g0 : Matrix (Fin n) (Fin n) ℂ)
    (hmax : ∀ g ∈ UJset ε, u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1) ≤
      u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1))
    (hg0 : g0 ∈ UJset ε) (p : Fin n × Fin n) (hp : p ∈ nc ε)
    (u' : ℝ → ℝ) (d : ℝ)
    (hu' : ∀ t, HasDerivAt (fun t : ℝ => u (g0 * NormedSpace.exp (t • Xp p.1 p.2))) (u' t) t)
    (hd : HasDerivAt u' d 0)
    (v' : ℝ → ℝ) (v'' : ℝ)
    (hv' : ∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ r) (v' t) t)
    (hv'' : HasDerivAt v' v'' 0)
    (w' : ℝ → ℝ) (w'' : ℝ)
    (hw' : ∀ t, HasDerivAt (fun t : ℝ => (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ (r + 1)) (w' t) t)
    (hw'' : HasDerivAt w' w'' 0) :
    d - A * v'' - η * w'' ≤ 0 := by
  obtain ⟨-, -, hmem, -, -, hX⟩ := hB3g n ε
  have hXp := hX p hp
  refine hB3 (fun t => u (g0 * NormedSpace.exp (t • Xp p.1 p.2)) -
      A * (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ r -
      η * (1 + hs2 (g0 * NormedSpace.exp (t • Xp p.1 p.2))) ^ (r + 1))
    (fun t => u' t - A * v' t - η * w' t) _ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun t => ?_
    have h0 : g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2) = g0 := by simp
    show _ ≤ u (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2)) -
      A * (1 + hs2 (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2))) ^ r -
      η * (1 + hs2 (g0 * NormedSpace.exp ((0 : ℝ) • Xp p.1 p.2))) ^ (r + 1)
    rw [h0]
    exact hmax _ (hmem g0 hg0 _ hXp t)
  · intro t
    exact ((hu' t).sub ((hv' t).const_mul A)).sub ((hw' t).const_mul η)
  · exact (hd.sub (hv''.const_mul A)).sub (hw''.const_mul η)

theorem hilbert_schmidt_nonneg_alt (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

end MaximumPrincipleOneFunction

open MaximumPrincipleOneFunction in
theorem maximum_principle_of_facts : B2 → B3 → UnitaryGroupFacts → MaximumPrincipleVar := by
  intro hB2 hB3 hB3g n ε r
  choose cf hcf0 hcf using hB2
  have hcr0 : 0 ≤ ∑ p ∈ nc ε, cf n (Xp p.1 p.2) r := Finset.sum_nonneg fun p _ => hcf0 _ _ _
  have hcr10 : 0 ≤ ∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1) := Finset.sum_nonneg fun p _ => hcf0 _ _ _
  refine ⟨(∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) + 1, by linarith, ?_⟩
  intro u A hA hcont hgrowth hsub
  obtain ⟨C, hC⟩ := hgrowth
  obtain ⟨hcpt, h1, hmem, -, hhs, hX⟩ := hB3g n ε
  have key : ∀ η : ℝ, 0 < η → u 1 ≤ A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r +
      η * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) := by
    intro η hη
    by_contra hneg
    push Not at hneg
    have hW : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => 1 + hs2 g := continuous_const.add hhs
    have hK := hcpt (|C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ))
    have hKne : ({g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} : Set _).Nonempty :=
      ⟨1, h1, by have := div_nonneg (abs_nonneg C) hη.le; linarith⟩
    have hψc : ContinuousOn (fun g => u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1))
        {g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} := by
      have hu : ContinuousOn u {g | g ∈ UJset ε ∧ hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)} :=
        hcont.mono fun g hg => hg.1
      exact (hu.sub (continuous_const.mul (hW.pow r)).continuousOn).sub
        (continuous_const.mul (hW.pow (r + 1))).continuousOn
    obtain ⟨g0, hg0K, hg0max⟩ := hK.exists_isMaxOn hKne hψc
    have hψ1 : u 1 - A * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ r -
        η * (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) ≤
        u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1) :=
      hg0max ⟨h1, by have := div_nonneg (abs_nonneg C) hη.le; linarith⟩
    have hglob : ∀ g ∈ UJset ε, u g - A * (1 + hs2 g) ^ r - η * (1 + hs2 g) ^ (r + 1) ≤
        u g0 - A * (1 + hs2 g0) ^ r - η * (1 + hs2 g0) ^ (r + 1) := by
      intro g hg
      by_cases hgρ : hs2 g ≤ |C| / η + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)
      · exact hg0max ⟨hg, hgρ⟩
      · push Not at hgρ
        have hs1 := hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)
        have hsg := hilbert_schmidt_nonneg_alt g
        have hlt : |C| / η < 1 + hs2 g := by linarith
        have hCl : C < η * (1 + hs2 g) := by
          have := (div_lt_iff₀ hη).mp hlt
          have := le_abs_self C
          linarith
        have hWr : 0 < (1 + hs2 g) ^ r := pow_pos (by linarith) r
        have hAW : 0 ≤ A * (1 + hs2 g) ^ r := mul_nonneg hA hWr.le
        have hug := hC g hg
        have hprod := mul_pos hWr (sub_pos.mpr hCl)
        rw [pow_succ]
        nlinarith
    have hg0 : g0 ∈ UJset ε := hg0K.1
    obtain ⟨d, hd, hdsum⟩ := hsub g0 hg0
    have hW0 := hilbert_schmidt_nonneg_alt g0
    have hWr : 0 < (1 + hs2 g0) ^ r := pow_pos (by linarith) r
    have hWr1 : 0 < (1 + hs2 g0) ^ (r + 1) := pow_pos (by linarith) (r + 1)
    have hp : ∀ p ∈ nc ε, d p ≤ A * cf n (Xp p.1 p.2) r * (1 + hs2 g0) ^ r +
        η * cf n (Xp p.1 p.2) (r + 1) * (1 + hs2 g0) ^ (r + 1) := by
      intro p hp
      obtain ⟨u', hu', hdp⟩ := hd p hp
      obtain ⟨v', v'', hv', hv'', hvb⟩ := hcf n (Xp p.1 p.2) r g0
      obtain ⟨w', w'', hw', hw'', hwb⟩ := hcf n (Xp p.1 p.2) (r + 1) g0
      have hst := step hB3 hB3g ε r u A η g0 hglob hg0 p hp u' (d p) hu' hdp v' v'' hv' hv'' w' w'' hw' hw''
      have h1 := mul_le_mul_of_nonneg_left hvb hA
      have h2 := mul_le_mul_of_nonneg_left hwb hη.le
      nlinarith
    have hsum : ∑ p ∈ nc ε, d p ≤ A * (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) * (1 + hs2 g0) ^ r +
        η * (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) * (1 + hs2 g0) ^ (r + 1) := by
      refine (Finset.sum_le_sum hp).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
    have hpos : 0 < (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + (∑ p ∈ nc ε, cf n (Xp p.1 p.2) (r + 1)) + 1 := by
      linarith
    have hug0 : A * (1 + hs2 g0) ^ r + η * (1 + hs2 g0) ^ (r + 1) < u g0 := by linarith
    have hm := mul_lt_mul_of_pos_left hug0 hpos
    have e1 := mul_nonneg hcr10 (mul_nonneg hA hWr.le)
    have e2 := mul_pos (by linarith : (0:ℝ) < (∑ p ∈ nc ε, cf n (Xp p.1 p.2) r) + 1) (mul_pos hη hWr1)
    nlinarith
  have hW1 : 0 < (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1) :=
    pow_pos (by linarith [hilbert_schmidt_nonneg_alt (1 : Matrix (Fin n) (Fin n) ℂ)]) (r + 1)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have := key (δ / (1 + hs2 (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (r + 1)) (div_pos hδ hW1)
  rwa [div_mul_cancel₀ _ hW1.ne'] at this

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.OrthonormalEigenbasisOfBasic
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenvectorBasisSetup

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem casK_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (v : V) :
    casimirK ε E v = ∑ a, ∑ b, if ε b = ε a then E a b (E b a v) else 0 := by
  unfold casimirK
  simp only [Finset.sum_filter, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem cas_apply (E : Fin n → Fin n → Module.End ℂ V) (v : V) :
    casimir E v = ∑ a, ∑ b, E a b (E b a v) := by
  unfold casimir
  simp [LinearMap.sum_apply]

theorem nc_sum {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f : Fin n × Fin n → M) :
    ∑ p ∈ nc ε, f p = ∑ a, ∑ b, if ε b = ε a then 0 else f (a, b) := by
  unfold nc
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε b = ε a
  · simp [h]
  · have : ε a ≠ ε b := fun h' => h h'.symm
    simp [h, this]

theorem swap_sum {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f g : Fin n → Fin n → M) :
    (∑ a, ∑ b, if ε b = ε a then f a b else g a b) =
      ∑ a, ∑ b, if ε b = ε a then f b a else g b a := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε b = ε a
  · simp [h]
  · have : ε a ≠ ε b := fun h' => h h'.symm
    simp [h, this]

theorem sq_re (u : V) : ‖u‖ ^ 2 = (inner ℂ u u).re := by
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm

theorem sm_re (r : ℝ) (u : V) : (inner ℂ u ((r : ℂ) • u)).re = r * ‖u‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul, ← sq_re]

end EigenvectorBasisSetup

open EigenvectorBasisSetup in
theorem orthonormal_eigenbasis_of_basic : A0 := by
  intro n ε V _ _ E hM
  have hU := hM.uni
  have hc : ∀ a b, ε b = ε a → ∀ x y, inner ℂ (E a b x) y = inner ℂ x (E b a y) := by
    intro a b h x y
    rw [hU a b x y]
    simp [adjSign, h.symm]
  have hK : ∀ x y, inner ℂ x (casimirK ε E y) =
      ∑ a, ∑ b, if ε b = ε a then inner ℂ (E b a x) (E b a y) else 0 := by
    intro x y
    rw [casK_apply, inner_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rw [hc b a h.symm]
    · simp
  have hKre : ∀ w, (inner ℂ w (casimirK ε E w)).re =
      ∑ a, ∑ b, if ε b = ε a then ‖E b a w‖ ^ 2 else 0 := by
    intro w
    rw [hK, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [sq_re]
    · simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← inner_conj_symm, hK, hK, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  · intro μ v hv h0
    have h1 := hKre v
    rw [hv, sm_re] at h1
    have h2 : 0 ≤ μ * ‖v‖ ^ 2 := by
      rw [h1]
      refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
      split_ifs <;> positivity
    have h3 : 0 < ‖v‖ ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_left h2 h3
  · intro a b h
    unfold Z
    exact sub_eq_zero.mpr (casimirK_comm ε hM.gl a b h)
  · intro κ hκ w
    have h3 : ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = (κ : ℂ) • w - casimirK ε E w := by
      rw [← hκ w, cas_apply, casK_apply, nc_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
    have hnorm : ∀ a b, ‖E a b w‖ ^ 2 = (adjSign ε a b * inner ℂ w (E b a (E a b w))).re := by
      intro a b
      rw [sq_re, hU]
    have h2 : ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 = (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 := by
      have e1 : ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 =
          ∑ a, ∑ b, if ε b = ε a then 0 else -(inner ℂ w (E b a (E a b w))).re := by
        rw [nc_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases h : ε b = ε a
        · simp [h]
        · have : ε a ≠ ε b := fun h' => h h'.symm
          simp [h, hnorm, adjSign, this]
      have e2 : (∑ a, ∑ b, if ε b = ε a then (0 : ℝ) else -(inner ℂ w (E b a (E a b w))).re) =
          -(inner ℂ w (∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w))).re := by
        rw [swap_sum, nc_sum, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      rw [e1, e2, h3, inner_sub_right, Complex.sub_re, sm_re]
      ring
    have h1 : ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 := by
      have e1 : ∑ a, ∑ b, ‖E a b w‖ ^ 2 =
          (∑ a, ∑ b, if ε b = ε a then ‖E a b w‖ ^ 2 else 0) +
            ∑ a, ∑ b, if ε b = ε a then 0 else ‖E a b w‖ ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      have e2 : (∑ a, ∑ b, if ε b = ε a then ‖E a b w‖ ^ 2 else (0 : ℝ)) =
          (inner ℂ w (casimirK ε E w)).re := by
        rw [hKre, swap_sum]
      have e3 : (∑ a, ∑ b, if ε b = ε a then (0 : ℝ) else ‖E a b w‖ ^ 2) =
          ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 := by
        rw [nc_sum]
      rw [e1, e2, e3, h2]
      ring
    exact ⟨h1, h2, h3⟩

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SecondDerivativeHolds
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace HilbertSchmidtNorm

variable {n : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem hasDerivAt_entry (g X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (g * NormedSpace.exp (s • X) * Y) i j)
      ((g * NormedSpace.exp (t • X) * X * Y) i j) t := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).const_mul g).mul_const Y
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t h
  have e : (g * NormedSpace.exp (t • X) * X * Y) i j = L (g * (NormedSpace.exp (t • X) * X) * Y) := by
    show _ = (g * (NormedSpace.exp (t • X) * X) * Y) i j
    rw [mul_assoc g]
  rw [e]
  exact h2

theorem hilbert_schmidt_nonneg_alt (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem hilbert_schmidt_mul_le (g X : Matrix (Fin n) (Fin n) ℂ) : hs2 (g * X) ≤ hs2 g * hs2 X := by
  have key : ∀ i j, ‖(g * X) i j‖ ^ 2 ≤ (∑ k, ‖g i k‖ ^ 2) * (∑ k, ‖X k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(g * X) i j‖ ≤ ∑ k, ‖g i k‖ * ‖X k j‖ := by
      rw [Matrix.mul_apply]
      exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    calc ‖(g * X) i j‖ ^ 2 ≤ (∑ k, ‖g i k‖ * ‖X k j‖) ^ 2 := by gcongr
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  unfold hs2
  calc ∑ i, ∑ j, ‖(g * X) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ k, ‖g i k‖ ^ 2) * (∑ k, ‖X k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖g i k‖ ^ 2) * ∑ j, ∑ k, ‖X k j‖ ^ 2 := by
        rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm (f := fun j k => ‖X k j‖ ^ 2)]

theorem abs_two_inner_le (M N : Matrix (Fin n) (Fin n) ℂ) :
    |∑ i, ∑ j, 2 * inner ℝ (M i j) (N i j)| ≤ hs2 M + hs2 N := by
  unfold hs2
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have := abs_real_inner_le_norm (M i j) (N i j)
  rw [abs_mul, abs_two]
  nlinarith [sq_nonneg (‖M i j‖ - ‖N i j‖)]

theorem hasDerivAt_entry1 (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (g * NormedSpace.exp (s • X)) i j)
      ((g * NormedSpace.exp (t • X) * X) i j) t := by
  simpa using hasDerivAt_entry g X 1 t i j

theorem hd1 (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => hs2 (g * NormedSpace.exp (s • X)))
      (∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (t • X)) i j) ((g * NormedSpace.exp (t • X) * X) i j)) t := by
  unfold hs2
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  exact (hasDerivAt_entry1 g X t i j).norm_sq

theorem hd2 (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (s • X)) i j)
        ((g * NormedSpace.exp (s • X) * X) i j))
      (∑ i, ∑ j, 2 * (inner ℝ ((g * NormedSpace.exp (t • X)) i j) ((g * NormedSpace.exp (t • X) * X * X) i j) +
        inner ℝ ((g * NormedSpace.exp (t • X) * X) i j) ((g * NormedSpace.exp (t • X) * X) i j))) t := by
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  exact ((hasDerivAt_entry1 g X t i j).inner ℝ (hasDerivAt_entry g X X t i j)).const_mul 2

theorem L1 (r : ℕ) (u : ℝ) (hu : 1 ≤ u) :
    ((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * u ^ 2 ≤ r * u ^ r := by
  rcases r with _ | _ | k
  · simp
  · simp; linarith
  · have e1 : k + 1 + 1 - 1 = k + 1 := by omega
    have e2 : u ^ k * u ^ 2 = u ^ (k + 1 + 1) := by rw [← pow_add]
    rw [e1, mul_assoc, show k + 1 - 1 = k by omega, e2]
    have h0 : 0 ≤ u ^ (k + 1 + 1) := by positivity
    push_cast
    nlinarith

theorem L2 (r : ℕ) (u : ℝ) : (r : ℝ) * u ^ (r - 1) * u ≤ r * u ^ r := by
  rcases r with _ | k
  · simp
  · simp [pow_succ, mul_assoc]

end HilbertSchmidtNorm

open HilbertSchmidtNorm in
theorem heightFunctionalStatement_of_pairingProperties : B2 := by
  intro n X r
  set A : ℝ := 1 + hs2 X with hA
  set Bc : ℝ := 1 + hs2 (X * X) + 2 * hs2 X with hBc
  have hXn := hilbert_schmidt_nonneg_alt X
  have hXXn := hilbert_schmidt_nonneg_alt (X * X)
  refine ⟨r * r * A ^ 2 + r * Bc, by positivity, fun g => ?_⟩
  set h : ℝ → ℝ := fun s => hs2 (g * NormedSpace.exp (s • X)) with hh
  set h' : ℝ → ℝ := fun t => ∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (t • X)) i j)
    ((g * NormedSpace.exp (t • X) * X) i j) with hh'
  set H2 : ℝ := ∑ i, ∑ j, 2 * (inner ℝ ((g * NormedSpace.exp ((0:ℝ) • X)) i j)
    ((g * NormedSpace.exp ((0:ℝ) • X) * X * X) i j) + inner ℝ ((g * NormedSpace.exp ((0:ℝ) • X) * X) i j)
      ((g * NormedSpace.exp ((0:ℝ) • X) * X) i j)) with hH2
  have d1 : ∀ t, HasDerivAt h (h' t) t := fun t => hd1 g X t
  have d2 : HasDerivAt h' H2 0 := hd2 g X 0
  refine ⟨fun t => r * (1 + h t) ^ (r - 1) * h' t,
    r * (((r - 1 : ℕ) : ℝ) * (1 + h 0) ^ (r - 1 - 1) * h' 0) * h' 0 + r * (1 + h 0) ^ (r - 1) * H2,
    fun t => ((d1 t).const_add 1).pow r, (((d1 0).const_add 1).pow (r - 1)).const_mul (r : ℝ) |>.mul d2, ?_⟩
  have e0 : NormedSpace.exp ((0:ℝ) • X) = 1 := by simp
  have hg := hilbert_schmidt_nonneg_alt g
  have h0 : h 0 = hs2 g := by simp [hh]
  have hp : |h' 0| ≤ A * hs2 g := by
    have := abs_two_inner_le g (g * X)
    have := hilbert_schmidt_mul_le g X
    simp only [hh', e0, mul_one]
    nlinarith
  have hpp : |H2| ≤ Bc * hs2 g := by
    have k1 := abs_two_inner_le g (g * (X * X))
    have k2 := abs_two_inner_le (g * X) (g * X)
    have k3 := hilbert_schmidt_mul_le g X
    have k4 := hilbert_schmidt_mul_le g (X * X)
    have : H2 = (∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * (X * X)) i j)) +
        ∑ i, ∑ j, 2 * inner ℝ ((g * X) i j) ((g * X) i j) := by
      simp only [hH2, e0, mul_one, mul_add, Finset.sum_add_distrib, mul_assoc]
    rw [this]
    refine (abs_add_le _ _).trans ?_
    nlinarith
  rw [h0]
  set u : ℝ := 1 + hs2 g with hu
  have hu1 : 1 ≤ u := by linarith
  have hP : 0 ≤ ((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) := by positivity
  have hQ : 0 ≤ u ^ (r - 1) := by positivity
  have hr : (0 : ℝ) ≤ r := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hsq : h' 0 ^ 2 ≤ (A * u) ^ 2 := by
    have : |h' 0| ≤ A * u := hp.trans (by nlinarith)
    exact sq_le_sq' (by linarith [neg_abs_le (h' 0)]) (le_trans (le_abs_self _) this)
  have t1 : r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * h' 0) * h' 0 ≤ r * A ^ 2 * (r * u ^ r) := by
    calc r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * h' 0) * h' 0
        = r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1)) * h' 0 ^ 2 := by ring
      _ ≤ r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1)) * (A * u) ^ 2 := by gcongr
      _ = r * A ^ 2 * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * u ^ 2) := by ring
      _ ≤ r * A ^ 2 * (r * u ^ r) := mul_le_mul_of_nonneg_left (L1 r u hu1) (by positivity)
  have t2 : r * u ^ (r - 1) * H2 ≤ Bc * (r * u ^ r) := by
    have hH : H2 ≤ Bc * u := (le_abs_self _).trans (hpp.trans (by nlinarith))
    calc r * u ^ (r - 1) * H2 ≤ r * u ^ (r - 1) * (Bc * u) := by gcongr
      _ = Bc * (r * u ^ (r - 1) * u) := by ring
      _ ≤ Bc * (r * u ^ r) := mul_le_mul_of_nonneg_left (L2 r u) (by rw [hBc]; positivity)
  nlinarith

end PositivityTheory.CW

end
end
