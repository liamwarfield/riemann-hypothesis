module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ReInnerGeOfSpanEigenvectors
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.re_inner_ge_of_span_eigenvectors :
    ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M →ₗ[ℂ] H) (V : Submodule ℂ M) (T : Module.End ℂ M) (c : ℝ) (s : Set M), (∀ x ∈ V, ∀ y ∈ V, inner ℂ (j (T x)) (j y) = inner ℂ (j x) (j (T y))) → (∀ x ∈ s, x ∈ V ∧ ∃ κ : ℂ, -c ≤ κ.re ∧ T x = κ • x) → ∀ v ∈ Submodule.span ℂ s, -c * ‖j v‖ ^ 2 ≤ (inner ℂ (j v) (j (T v))).re := by
  intro M H _ _ _ _ j V T c s hsym hs v hv
  classical
  have hle : Submodule.span ℂ s ≤
      ⨆ κ : {κ : ℂ // -c ≤ κ.re}, (V ⊓ Module.End.eigenspace T (κ : ℂ)) := by
    refine Submodule.span_le.2 fun x hx => ?_
    obtain ⟨hxV, κ, hκ, hT⟩ := hs x hx
    exact Submodule.mem_iSup_of_mem (⟨κ, hκ⟩ : {κ : ℂ // -c ≤ κ.re})
      ⟨hxV, Module.End.mem_eigenspace_iff.2 hT⟩
  obtain ⟨f, hf, hfv⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hle hv)
  have hV : ∀ κ, f κ ∈ V := fun κ => (hf κ).1
  have hT : ∀ κ, T (f κ) = (κ : ℂ) • f κ := fun κ => Module.End.mem_eigenspace_iff.1 (hf κ).2
  have hrel : ∀ a b : {κ : ℂ // -c ≤ κ.re}, (starRingEnd ℂ) (a : ℂ) * inner ℂ (j (f a)) (j (f b))
      = (b : ℂ) * inner ℂ (j (f a)) (j (f b)) := by
    intro a b
    have := hsym _ (hV a) _ (hV b)
    rwa [hT, hT, map_smul, map_smul, inner_smul_left, inner_smul_right] at this
  have horth : ∀ a b, a ≠ b → inner ℂ (j (f a)) (j (f b)) = 0 := by
    intro a b hab
    by_cases h0 : j (f a) = 0
    · rw [h0, inner_zero_left]
    · have h1 : (starRingEnd ℂ) (a : ℂ) = a :=
        mul_right_cancel₀ (fun h => h0 (inner_self_eq_zero.1 h)) (hrel a a)
      have h2 := hrel a b
      rw [h1] at h2
      by_contra h3
      exact hab (Subtype.ext (mul_right_cancel₀ h3 h2))
  have hv' : v = ∑ a ∈ f.support, f a := hfv.symm
  have e1 : inner ℂ (j v) (j v) = ∑ a ∈ f.support, inner ℂ (j (f a)) (j (f a)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv', map_sum, sum_inner]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum, Finset.sum_eq_single_of_mem a ha]
    intro b _ hb
    exact horth a b hb.symm
  have e2 : inner ℂ (j v) (j (T v))
      = ∑ a ∈ f.support, (a : ℂ) * inner ℂ (j (f a)) (j (f a)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv', map_sum T, map_sum, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum, Finset.sum_eq_single_of_mem a ha, hT, map_smul, inner_smul_right]
    intro b _ hb
    rw [hT, map_smul, inner_smul_right, horth a b hb.symm, mul_zero]
  have hn : ∀ x : H, inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have e3 : ‖j v‖ ^ 2 = ∑ a ∈ f.support, ‖j (f a)‖ ^ 2 := by
    simp only [hn] at e1
    exact_mod_cast e1
  rw [e2, e3, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [hn, Complex.re_mul_ofReal]
  exact mul_le_mul_of_nonneg_right a.2 (sq_nonneg _)
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsSignedBasisLieSubalgebraExpCompact
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.TrFormDefiniteOnArchSkewArchHerm
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.TraceMixedSpaceEqMixedTraceLMul
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

private theorem algebra_trace_pi_eq_sum_trace {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]
    [Module.Free R A] [Module.Finite R A] (x : ι → A) :
    Algebra.trace R (ι → A) x = ∑ i, Algebra.trace R A (x i) := by
  classical
  let b := Module.Free.chooseBasis R A
  rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι => b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]

theorem UpperTheory.trace_mixedSpace_eq_mixedTraceL_mul :
    ∀ (K : Type) [Field K] [NumberField K] (x : NumberField.mixedEmbedding.mixedSpace K),
      Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) x =
        mixedTraceL (K := K) (x * ((fun _ => (1 : ℝ)), (fun _ => (2 : ℂ)))) := by
  classical
  intro K _ _ x
  rw [Algebra.trace_prod_apply, algebra_trace_pi_eq_sum_trace, algebra_trace_pi_eq_sum_trace]
  simp [mixedTraceL, Algebra.trace_complex_apply, mul_comm]
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

open scoped Classical in
private theorem trace_mixedSpace_eq {K : Type} [Field K] [NumberField K]
    (x : NumberField.mixedEmbedding.mixedSpace K) :
    Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) x =
      mixedTraceL K x + ∑ v, (x.2 v).re := by
  rw [UpperTheory.trace_mixedSpace_eq_mixedTraceL_mul, mixedTraceL_apply, mixedTraceL_apply]
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, mul_zero, sub_zero, ← Finset.sum_mul]
  ring

open scoped Classical in
private theorem trace_eq_zero_of_star_neg {K : Type} [Field K] [NumberField K]
    (z : NumberField.mixedEmbedding.mixedSpace K) (hz : star z = -z) :
    Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) z = 0 := by
  have h1 : mixedTraceL K (star z) = mixedTraceL K z := mixedTraceL_star z
  rw [hz, map_neg] at h1
  have h2 : ∑ v, (z.2 v).re = 0 := by
    have h3 : ∀ v, (z.2 v).re = 0 := fun v => by
      have h4 : star (z.2 v) = -(z.2 v) := congrFun (congrArg Prod.snd hz) v
      have h5 := congrArg Complex.re h4
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h5
      linarith
    simp [h3]
  rw [trace_mixedSpace_eq, h2]
  linarith

open scoped Classical in
private theorem trace_conjTranspose_mul_pos {K : Type} [Field K] [NumberField K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (NumberField.mixedEmbedding.mixedSpace K)} (hA : A ≠ 0) :
    0 < Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
      (Matrix.trace (A.conjTranspose * A)) := by
  rw [trace_mixedSpace_eq]
  have h1 := mixedTraceL_trace_conjTranspose_mul_self_pos hA
  have h2 : 0 ≤ ∑ v, ((Matrix.trace (A.conjTranspose * A)).2 v).re := by
    refine Finset.sum_nonneg fun v _ => ?_
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Prod.snd_sum, Finset.sum_apply, Complex.re_sum, Prod.snd_mul, Pi.mul_apply, Prod.snd_star,
      Pi.star_apply]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  linarith

theorem UpperTheory.trForm_definite_on_archSkew_archHerm :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), (∀ X ∈ archSkew K n, X ≠ 0 → trForm K n X X < 0) ∧ (∀ X ∈ archHerm K n, X ≠ 0 → 0 < trForm K n X X) ∧ (∀ X ∈ archSkew K n, ∀ Y ∈ archHerm K n, trForm K n X Y = 0) := by
  intro K _ _ n
  refine ⟨fun X hX h0 => ?_, fun X hX h0 => ?_, fun X hX Y hY => ?_⟩
  · rw [mem_archSkew] at hX
    have hX0 : mat (X : ArchMatrix K n) ≠ 0 := fun e => h0 (Subtype.ext (mat_injective e))
    have e : mat (X : ArchMatrix K n) * mat (X : ArchMatrix K n) =
        -((mat (X : ArchMatrix K n)).conjTranspose * mat (X : ArchMatrix K n)) := by
      rw [hX, Matrix.neg_mul, neg_neg]
    have h := trace_conjTranspose_mul_pos hX0
    have h2 : trForm K n X X = Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (X : ArchMatrix K n))) := rfl
    rw [h2, e, Matrix.trace_neg, map_neg]
    linarith
  · rw [mem_archHerm] at hX
    have hX0 : mat (X : ArchMatrix K n) ≠ 0 := fun e => h0 (Subtype.ext (mat_injective e))
    have h := trace_conjTranspose_mul_pos hX0
    rw [hX] at h
    exact h
  · rw [mem_archSkew] at hX
    rw [mem_archHerm] at hY
    have h2 : trForm K n X Y = Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))) := rfl
    rw [h2]
    refine trace_eq_zero_of_star_neg _ ?_
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX, hY, Matrix.mul_neg,
      Matrix.trace_neg, Matrix.trace_mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsSignedOrthonormalBasisOfIsCompl
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_signed_orthonormal_basis_of_isCompl :
    ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (k p : Submodule ℝ V), IsCompl k p → (∀ X Y, B X Y = B Y X) → (∀ X ∈ k, X ≠ 0 → B X X < 0) → (∀ X ∈ p, X ≠ 0 → 0 < B X X) → (∀ X ∈ k, ∀ Y ∈ p, B X Y = 0) → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ V) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ i j, B (b i) (b j) = if i = j then ε i else 0) ∧ ∀ i, ε i = -1 → b i ∈ k := by
  intro V _ _ _ B k p hc hsymm hneg hpos hzero
  classical
  obtain ⟨bk, hbk⟩ := exists_signed_basis (B.restrict k)
    (fun x y => hsymm (x : V) y) (s := -1)
    (by norm_num) (fun v hv => by
      have h0 : (v : V) ≠ 0 := fun e => hv (Subtype.ext e)
      have := hneg v v.2 h0
      change 0 < _ * B (v : V) v
      linarith)
  obtain ⟨bp, hbp⟩ := exists_signed_basis (B.restrict p)
    (fun x y => hsymm (x : V) y) (s := 1)
    (by norm_num) (fun v hv => by
      have h0 : (v : V) ≠ 0 := fun e => hv (Subtype.ext e)
      have := hpos v v.2 h0
      change 0 < _ * B (v : V) v
      linarith)
  set e := Submodule.prodEquivOfIsCompl k p hc
  set b0 := (bk.prod bp).map e
  set f : Fin (Module.finrank ℝ k) ⊕ Fin (Module.finrank ℝ p) → V :=
    Sum.elim (fun i => (bk i : V)) (fun j => (bp j : V))
  have hb0 : ∀ x, b0 x = f x := by
    rintro (i | j)
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
  set ε0 : Fin (Module.finrank ℝ k) ⊕ Fin (Module.finrank ℝ p) → ℝ :=
    Sum.elim (fun _ => -1) (fun _ => 1)
  have horth : ∀ x y, B (b0 x) (b0 y) = if x = y then ε0 x else 0 := by
    intro x y
    rw [hb0, hb0]
    rcases x with i | i <;> rcases y with j | j
    · have := hbk i j
      change B _ _ = _ at this
      simp only [f, ε0, Sum.elim_inl, Sum.inl.injEq]
      exact this
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact hzero _ (bk i).2 _ (bp j).2
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      rw [hsymm]
      exact hzero _ (bk j).2 _ (bp i).2
    · have := hbp i j
      change B _ _ = _ at this
      simp only [f, ε0, Sum.elim_inr, Sum.inr.injEq]
      exact this
  set σ := finSumFinEquiv (m := Module.finrank ℝ k) (n := Module.finrank ℝ p)
  refine ⟨_, b0.reindex σ, ε0 ∘ σ.symm, fun i => ?_, fun i j => ?_, fun i hi => ?_⟩
  · rcases hx : σ.symm i with a | a <;> simp [ε0, hx]
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, horth]
    simp only [Function.comp_apply, σ.symm.injective.eq_iff]
  · rw [Module.Basis.reindex_apply, hb0]
    simp only [Function.comp_apply] at hi
    rcases hx : σ.symm i with a | a
    · simp only [f, Sum.elim_inl]
      exact (bk a).2
    · rw [hx] at hi
      simp [ε0] at hi
      norm_num at hi
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.exists_signed_basis_lieSubalgebra_exp_compact :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ B : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra, (∀ X Y, B X Y = trForm K n X Y) ∧ (∀ X Y, B X Y = B Y X) ∧ ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ i j, B (b i) (b j) = if i = j then ε i else 0) ∧ ∀ i, ε i = -1 → ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n := by
  intro K _ _ n
  have hmk : ∀ X Y : (isExpLieAlgebra K n).lieSubalgebra, trForm K n X Y =
      Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))) := fun _ _ => rfl
  let B : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra :=
    LinearMap.mk₂ ℝ (fun X Y => trForm K n X Y)
      (fun X₁ X₂ Y => by
        simp only [hmk, mat_coe_add, Matrix.add_mul, Matrix.trace_add, map_add (f := _)])
      (fun r X Y => by
        simp only [hmk, mat_coe_smul, Matrix.smul_mul, Matrix.trace_smul, map_smul])
      (fun X Y₁ Y₂ => by
        simp only [hmk, mat_coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _)])
      (fun r X Y => by
        simp only [hmk, mat_coe_smul, Matrix.mul_smul, Matrix.trace_smul, map_smul])
  have hB : ∀ X Y, B X Y = trForm K n X Y := fun _ _ => rfl
  have hsymm : ∀ X Y, B X Y = B Y X := by
    intro X Y
    rw [hB, hB, hmk, hmk, Matrix.trace_mul_comm]
  obtain ⟨h1, h2, h3⟩ := UpperTheory.trForm_definite_on_archSkew_archHerm K n
  haveI : FiniteDimensional ℝ (isExpLieAlgebra K n).lieSubalgebra :=
    FiniteDimensional.finiteDimensional_submodule (isExpLieAlgebra K n).lieSubalgebra.toSubmodule
  obtain ⟨d, b, ε, hε, horth, hk⟩ := UpperTheory.exists_signed_orthonormal_basis_of_isCompl _ B (archSkew K n) (archHerm K n)
    isCompl_archSkew_archHerm hsymm h1 h2 h3
  refine ⟨B, hB, hsymm, d, b, ε, hε, horth, fun i hi t => expG_mem_archCompact_of_skew _ ?_⟩
  have h := hk i hi
  rw [mem_archSkew] at h
  show Matrix.conjTranspose (t • mat (b i : ArchMatrix K n)) = -(t • mat (b i : ArchMatrix K n))
  rw [Matrix.conjTranspose_smul, star_trivial, h, smul_neg]
end
