module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MinkowskiLinearForms
namespace GlobalTheory.MinkowskiLinearForms

open MeasureTheory

theorem minkowski_linear_forms {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : Matrix.det A ≠ (0 : ℝ)) {t : ℝ} (ht : (0 : ℝ) < t)
    (hlt : |Matrix.det A| < t ^ Fintype.card ι) :
    ∃ (z : ι → ℤ), z ≠ (0 : ι → ℤ) ∧ ∀ (j : ι), |∑ i : ι, (↑(z i) : ℝ) * A i j| < t := by
  classical
  have hli : LinearIndependent ℝ (fun i => A i) := Matrix.linearIndependent_rows_of_det_ne_zero hA
  let b : Module.Basis ι ℝ (ι → ℝ) := basisOfPiSpaceOfLinearIndependent hli
  have hb : (⇑b : ι → ι → ℝ) = fun i => A i := coe_basisOfPiSpaceOfLinearIndependent hli
  let L : AddSubgroup (ι → ℝ) := (Submodule.span ℤ (Set.range b)).toAddSubgroup
  have hF := ZSpan.isAddFundamentalDomain' b (volume : Measure (ι → ℝ))
  let s : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ioo (-t) t
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.neg_apply] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    exact ⟨by linarith, by linarith⟩
  have hconv : Convex ℝ s := convex_pi (fun i _ => convex_Ioo (-t) t)
  have hvolF : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal |Matrix.det A| := by
    rw [ZSpan.volume_fundamentalDomain]
    congr 3
  have hvols : volume s = ENNReal.ofReal ((2 * t) ^ Fintype.card ι) := by
    simp only [s, Real.volume_pi_Ioo]
    rw [Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (by linarith)]
    congr 2
    ring
  have hlt' : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (ι → ℝ) < volume s := by
    rw [hvolF, hvols, Module.finrank_fintype_fun_eq_card]
    rw [show (2 : ENNReal) ^ Fintype.card ι = ENNReal.ofReal ((2 : ℝ) ^ Fintype.card ι) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [mul_pow, mul_comm ((2:ℝ) ^ _)]
    exact mul_lt_mul_of_pos_right hlt (by positivity)
  haveI hcount : Countable (Submodule.span ℤ (Set.range b)) := inferInstance
  haveI : Countable L := hcount
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF hsymm hconv hlt'
  have hxmem : (x : ι → ℝ) ∈ Submodule.span ℤ (Set.range b) := x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxmem
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    apply hx0
    ext1
    rw [← hc, hc0]
    simp
  · intro j
    have hxj := hxs j (Set.mem_univ j)
    rw [Set.mem_Ioo] at hxj
    have : (x : ι → ℝ) j = ∑ i, (c i : ℝ) * A i j := by
      rw [← hc, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hb, zsmul_eq_mul]
    rw [← this, abs_lt]
    exact hxj

end GlobalTheory.MinkowskiLinearForms
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsShortOfTraceDet
namespace GlobalTheory.HermClass

open MeasureTheory Module Submodule NumberField Matrix

theorem exists_int_vecMul_lt {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.det ≠ 0) {t : ℝ} (ht : 0 < t) (h : |A.det| < t ^ Fintype.card ι) :
    ∃ z : ι → ℤ, z ≠ 0 ∧ ∀ j, |∑ i, (z i : ℝ) * A i j| < t := by
  first
  | exact @_root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms
  | exact _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms
  | (apply _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> assumption)
  | (intros; apply _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms ..)

theorem det_ne_zero_and_abs_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℚ)
    {M : ℤ} (hM : M ≠ 0)
    (h : ∀ x : ι → ℚ, (∀ j, ∃ m : ℤ, (x ᵥ* T) j = m) → ∀ i, ∃ m : ℤ, M * x i = m) :
    T.det ≠ 0 ∧ |T.det| ≤ |(M : ℚ)| ^ Fintype.card ι := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have h0 : T.det ≠ 0 := by
    intro hd
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    have hi' : x i ≠ 0 := hi
    obtain ⟨m, hm⟩ := h ((2 * M * x i)⁻¹ • x) (fun j => ⟨0, by rw [Matrix.smul_vecMul, hx]; simp⟩) i
    have h2 : (2 * m : ℚ) = 1 := by
      rw [← hm]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega
  refine ⟨h0, ?_⟩
  have hu : IsUnit T.det := isUnit_iff_ne_zero.2 h0
  have hK : ∀ k i, ∃ m : ℤ, M * T⁻¹ k i = m := fun k => h (T⁻¹ k) fun j => by
    have : (T⁻¹ k ᵥ* T) j = (T⁻¹ * T) k j := rfl
    rw [this, Matrix.nonsing_inv_mul T hu, Matrix.one_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  choose K hK using hK
  have hKe : (Int.castRingHom ℚ).mapMatrix (Matrix.of K) = (M : ℚ) • T⁻¹ := by
    ext k i; simp [← hK]
  have hdet : (((Matrix.of K).det : ℤ) : ℚ) * T.det = (M : ℚ) ^ Fintype.card ι := by
    have := (Int.castRingHom ℚ).map_det (Matrix.of K)
    rw [hKe, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at this
    rw [← eq_intCast (Int.castRingHom ℚ), this]; field_simp
  have hK0 : (Matrix.of K).det ≠ 0 := by
    intro hz; rw [hz] at hdet
    exact pow_ne_zero _ hM' (by simpa using hdet.symm)
  have h1 : (1 : ℚ) ≤ |(((Matrix.of K).det : ℤ) : ℚ)| := by exact_mod_cast Int.one_le_abs hK0
  rw [← abs_pow, ← hdet, abs_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) h1

theorem exists_short_of_trace_det {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : LinearMap.BilinForm F V) (hq : LinearMap.IsSymm q) {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : κ → V) (hκ : Fintype.card κ = finrank ℚ F * finrank F V) {t : ℝ} (ht : 0 < t)
    (h0 : (Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det ≠ 0)
    (h1 : |(((Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j))).det : ℚ) : ℝ)| <
      (t ^ Fintype.card κ) ^ 2) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ ∀ φ : F →+* ℂ,
      ‖φ (q (∑ i, z i • b i) (∑ i, z i • b i))‖ ≤ finrank F V * t ^ 2 := by
  classical
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis hq
  set ρ : (F →+* ℂ) → (F →+* ℝ) := fun φ => (IsTotallyReal.complexEmbedding_isReal φ).embedding
    with hρ
  have hρc : ∀ φ x, ((ρ φ x : ℝ) : ℂ) = φ x := fun φ x => by simp [hρ]
  have hqe : ∀ x y, q x y = ∑ k, e.repr x k * e.repr y k * q (e k) (e k) := by
    intro x y
    conv_lhs => rw [← e.sum_repr x, ← e.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · ring
    · intro l _ hl
      have : q (e l) (e k) = 0 := he hl
      rw [this, mul_zero]
    · simp
  have htr : ∀ x : F, ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, ρ φ x := by
    intro x
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x)
    rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ x) _ (fun _ => rfl)] at h
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum, hρc, ← h]
    simp
  let ε : κ ≃ (F →+* ℂ) × Fin (finrank F V) := Fintype.equivOfCardEq (by
    rw [hκ, Fintype.card_prod, Embeddings.card, Fintype.card_fin])
  let a : κ → ℝ := fun j => ρ (ε j).1 (q (e (ε j).2) (e (ε j).2))
  let B : Matrix κ κ ℝ := Matrix.of fun i j => ρ (ε j).1 (e.repr (b i) (ε j).2)
  set T : Matrix κ κ ℚ := Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j)) with hT
  have hTB : (Rat.castHom ℝ).mapMatrix T = B * Matrix.diagonal a * Bᵀ := by
    ext i i'
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply, hT, Matrix.of_apply,
      eq_ratCast, htr, Matrix.transpose_apply, B, a]
    rw [Fintype.sum_equiv ε _ (fun p => ρ p.1 (e.repr (b i) p.2) * ρ p.1 (q (e p.2) (e p.2)) *
      ρ p.1 (e.repr (b i') p.2)) (fun _ => rfl), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun φ _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hqe, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  have hdT : ((T.det : ℚ) : ℝ) = B.det ^ 2 * ∏ j, a j := by
    have := (Rat.castHom ℝ).map_det T
    rw [hTB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at this
    rw [← eq_ratCast (Rat.castHom ℝ), this]; ring
  let A : Matrix κ κ ℝ := B * Matrix.diagonal fun j => Real.sqrt |a j|
  have hdA : A.det ^ 2 = |((T.det : ℚ) : ℝ)| := by
    rw [hdT, Matrix.det_mul, Matrix.det_diagonal, mul_pow, ← Finset.prod_pow, abs_mul,
      Finset.abs_prod, abs_of_nonneg (sq_nonneg B.det)]
    simp only [Real.sq_sqrt (abs_nonneg _)]
  have hA0 : A.det ≠ 0 := by
    intro hz
    rw [hz] at hdA
    apply h0
    have : ((T.det : ℚ) : ℝ) = 0 := by simpa using hdA.symm
    exact_mod_cast this
  have hA1 : |A.det| < t ^ Fintype.card κ := by
    apply abs_lt_of_sq_lt_sq _ (by positivity)
    rwa [hdA]
  obtain ⟨z, hz0, hz⟩ := exists_int_vecMul_lt A hA0 ht hA1
  refine ⟨z, hz0, fun φ => ?_⟩
  set v := ∑ i, z i • b i with hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hρc, Complex.norm_real, hqe, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k, ‖ρ φ (e.repr v k * e.repr v k * q (e k) (e k))‖ ≤ t ^ 2 := by
    intro k
    have h2 := hz (ε.symm (φ, k))
    have h3 : ∑ i, (z i : ℝ) * A i (ε.symm (φ, k)) =
        ρ φ (e.repr v k) * Real.sqrt |ρ φ (q (e k) (e k))| := by
      have hc : e.repr v k = ∑ i, (z i : F) * e.repr (b i) k := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← e.coord_apply, hv, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul, zsmul_eq_mul, e.coord_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hc, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [A, Matrix.mul_diagonal, B, a, Matrix.of_apply, Equiv.apply_symm_apply,
        mul_assoc, map_mul, map_intCast]
    rw [h3] at h2
    have h4 := (sq_lt_sq' (abs_lt.1 h2).1 (abs_lt.1 h2).2).le
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)] at h4
    rw [map_mul, map_mul, Real.norm_eq_abs, abs_mul, abs_mul_self]
    rwa [sq] at h4
  calc _ ≤ ∑ _k : Fin (finrank F V), t ^ 2 := Finset.sum_le_sum fun k _ => this k
    _ = _ := by simp

end GlobalTheory.HermClass
end

namespace GlobalTheory.HermClass

open Module Submodule NumberField

theorem exists_finite_residues {V : Type} [AddCommGroup V] (L : Submodule ℤ V) (hL : L.FG)
    {m : ℤ} (hm : m ≠ 0) :
    ∃ R : Set V, R.Finite ∧ (∀ ρ ∈ R, ρ ∈ L) ∧ ∀ x ∈ L, ∃ ρ ∈ R, ∃ y ∈ L, x = ρ + m • y := by
  have : Module.Finite ℤ L := Module.Finite.iff_fg.2 hL
  let P : Submodule ℤ L := LinearMap.range (m • LinearMap.id)
  have : Finite (L ⧸ P) := Module.finite_of_fg_torsion _ fun q => by
    obtain ⟨x, rfl⟩ := P.mkQ_surjective q
    refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, ?_⟩
    change m • P.mkQ x = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  choose s hs using P.mkQ_surjective
  refine ⟨Set.range fun q => (s q : V), Set.finite_range _, ?_, fun x hx => ?_⟩
  · rintro _ ⟨q, rfl⟩; exact (s q).2
  · have h := hs (P.mkQ ⟨x, hx⟩)
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq] at h
    obtain ⟨y, hy⟩ := h
    refine ⟨_, ⟨P.mkQ ⟨x, hx⟩, rfl⟩, y, y.2, ?_⟩
    have := congrArg Subtype.val hy
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul_of_tower,
      Submodule.coe_sub] at this
    rw [this]; simp

section NumberField

variable (E : Type) [Field E] [NumberField E]

theorem exists_int_mul_isIntegral {S : Set E} (hS : S.Finite) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ a ∈ S, IsIntegral ℤ ((M : E) * a) := by
  obtain ⟨M, hM, h⟩ := exists_integral_multiples ℤ ℚ hS.toFinset
  exact ⟨M, hM, fun a ha => by simpa using h a (by simpa using ha)⟩

theorem exists_int_mul_isIntegral_of_trace :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ a : E, (∀ t : E, IsIntegral ℤ t → ∃ m : ℤ, Algebra.trace ℚ E (a * t) = m) →
      IsIntegral ℤ ((D : E) * a) := by
  classical
  obtain ⟨D, hD, h⟩ := exists_int_mul_isIntegral E (Set.finite_range (integralBasis E).traceDual)
  refine ⟨D, hD, fun a ha => ?_⟩
  rw [← (integralBasis E).traceDual.sum_repr a, Finset.mul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨m, hm⟩ := ha (integralBasis E i) (by
    rw [integralBasis_apply]; exact (RingOfIntegers.basis E i).isIntegral_coe)
  rw [Basis.traceDual_repr_apply, Algebra.traceForm_apply, hm, mul_smul_comm, Int.cast_smul_eq_zsmul]
  exact (h _ ⟨i, rfl⟩).smul m

theorem exists_int_mul_mem_span :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ J : Ideal (𝓞 E), J ≠ ⊥ →
      ∃ j ∈ J, j ≠ 0 ∧ ∀ a ∈ J, j ∣ (M : 𝓞 E) * a := by
  classical
  choose I hI using ClassGroup.mk0_surjective (R := 𝓞 E)
  refine ⟨∏ C, (Ideal.absNorm (I C : Ideal (𝓞 E)) : ℤ), Finset.prod_ne_zero_iff.2 fun C _ => ?_,
    fun J hJ => ?_⟩
  · exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors (I C)
  · let J' : nonZeroDivisors (Ideal (𝓞 E)) := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
    obtain ⟨j, hj0, hj⟩ := ClassGroup.mk0_eq_mk0_inv_iff.1 (hI (ClassGroup.mk0 J')⁻¹)
    refine ⟨j, ?_, hj0, fun a ha => ?_⟩
    · have hjm : j ∈ (I (ClassGroup.mk0 J')⁻¹ : Ideal (𝓞 E)) * J := by
        rw [hj]; exact Ideal.mem_span_singleton_self j
      exact (Ideal.mul_le_inf hjm).2
    · have hj' : (I (ClassGroup.mk0 J')⁻¹ : Ideal (𝓞 E)) * J = Ideal.span {j} := hj
      rw [← Ideal.mem_span_singleton, ← hj']
      refine Ideal.mul_mem_mul ?_ ha
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (ClassGroup.mk0 J')⁻¹), Int.cast_mul]
      refine Ideal.mul_mem_right _ _ ?_
      simpa using Ideal.absNorm_mem _

theorem fg_integers : (Subalgebra.toSubmodule (integralClosure ℤ E)).FG :=
  Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite ℤ (𝓞 E)))

end NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIntegral_star {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (star a) :=
  ha.map (starRingEnd E).toIntAlgHom

theorem trace_star (a : E) : Algebra.trace ℚ E (star a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem exists_bound_short (n : ℕ) (hn : n ≠ 0) {N : ℤ} (hN : N ≠ 0) :
    ∃ C : ℝ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v ∈ Λ, v ≠ 0 ∧ ∀ φ : E →+* ℂ, ‖φ (h v v)‖ ≤ C := by
  classical
  obtain ⟨D, hD, hDa⟩ := exists_int_mul_isIntegral_of_trace E
  set F := maximalRealSubfield E with hF
  have hM0 : N * D * 2 ≠ 0 := by positivity
  refine ⟨(2 * n : ℕ) * (|((N * D * 2 : ℤ) : ℝ)| + 1) ^ 2, ?_⟩
  intro V _ _ _ h Λ hV hs hfg hsp hO hdual
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ E)
  have : IsScalarTower ℚ E V := IsScalarTower.of_compHom ℚ E V
  have : Module.Finite ℤ Λ := Module.Finite.iff_fg.2 hfg
  have : HasUniqueDiv V := .of_module_rat V
  have : Module.Free ℤ Λ := inferInstance
  let β := Module.Free.chooseBasis ℤ Λ
  let κ := Module.Free.ChooseBasisIndex ℤ Λ
  let b : κ → V := fun i => β i
  have hbZ : LinearIndependent ℤ b := β.linearIndependent.map' Λ.subtype (ker_subtype Λ)
  have hbQ : LinearIndependent ℚ b := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hbZ
  have hbΛ : ∀ x ∈ Λ, ∃ c : κ → ℤ, x = ∑ i, c i • b i := fun x hx =>
    ⟨β.repr ⟨x, hx⟩, by
      have := congrArg Λ.subtype (β.sum_repr ⟨x, hx⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      exact this.symm⟩
  have hbs : ⊤ ≤ span ℚ (Set.range b) := by
    have hΛ : ∀ x ∈ Λ, x ∈ span ℚ (Set.range b) := fun x hx => by
      obtain ⟨c, rfl⟩ := hbΛ x hx
      exact sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self i)) _
    have key : ∀ x ∈ span E (Λ : Set V), ∀ a : E, a • x ∈ span ℚ (Set.range b) := by
      intro x hx
      induction hx using span_induction with
      | mem x hx =>
        intro a
        obtain ⟨M, hM, hMa⟩ := exists_int_mul_isIntegral E (Set.finite_singleton a)
        have h1 := smul_mem _ (M : ℚ)⁻¹ (hΛ _ (hO _ (hMa a rfl) x hx))
        rw [← smul_assoc, ← smul_mul_assoc, Algebra.smul_def] at h1
        have hM' : (M : E) ≠ 0 := by exact_mod_cast hM
        simpa [hM'] using h1
      | zero => intro a; simp
      | add x y _ _ hx hy => intro a; rw [smul_add]; exact add_mem (hx a) (hy a)
      | smul c x _ hx => intro a; rw [smul_smul]; exact hx _
    intro x _
    simpa using key x (hsp ▸ mem_top) 1
  have hFV : finrank F V = 2 * n := by
    rw [← finrank_mul_finrank F E V, hV, Algebra.IsQuadraticExtension.finrank_eq_two]
  have : FiniteDimensional F V := Module.Finite.trans E V
  have hκ : Fintype.card κ = finrank ℚ F * finrank F V := by
    rw [← finrank_eq_card_basis (Basis.mk hbQ hbs), ← finrank_mul_finrank ℚ E V,
      ← finrank_mul_finrank F E V, ← finrank_mul_finrank ℚ F E, mul_assoc]
  have hreal : ∀ x y, h x y + h y x ∈ F := fun x y => by
    rw [← IsCMField.complexConj_eq_self_iff]
    change star _ = _
    rw [star_add, ← hs, ← hs, add_comm]
  have hstF : ∀ c : F, starRingEnd E (c : E) = c := fun c => IsCMField.complexConj_apply_eq_self E c
  let q : LinearMap.BilinForm F V := LinearMap.mk₂ F (fun x y => ⟨h x y + h y x, hreal x y⟩)
    (fun x x' y => Subtype.ext (by simp; ring))
    (fun c x y => Subtype.ext (by simp [Subfield.smul_def, hstF]; ring))
    (fun x y y' => Subtype.ext (by simp; ring))
    (fun c x y => Subtype.ext (by simp [Subfield.smul_def, hstF]; ring))
  have hq : ∀ x y, (q x y : E) = h x y + h y x := fun _ _ => rfl
  have hqs : LinearMap.IsSymm q := ⟨fun x y => Subtype.ext (by simp [hq, add_comm])⟩
  have htr : ∀ x y, Algebra.trace ℚ F (q x y) = Algebra.trace ℚ E (h x y) := fun x y => by
    have h1 := Algebra.trace_trace (R := ℚ) (S := F) (T := E) (algebraMap F E (q x y))
    rw [Algebra.trace_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, map_nsmul] at h1
    have h2 : algebraMap F E (q x y) = h x y + star (h x y) := by rw [← hs]; rfl
    rw [h2, map_add (f := _), trace_star, two_nsmul] at h1
    linarith
  set T : Matrix κ κ ℚ := Matrix.of fun i j => Algebra.trace ℚ F (q (b i) (b j)) with hT
  obtain ⟨hT0, hT1⟩ := det_ne_zero_and_abs_le T hM0 (by
    intro x hx i
    set y : V := ∑ i, x i • b i with hy
    have h1 : ∀ j, ∃ m : ℤ, Algebra.trace ℚ E (h y (b j)) = m := fun j => by
      obtain ⟨m, hm⟩ := hx j
      refine ⟨m, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hm, hy, map_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul, map_smul, ← htr]
      rfl
    have h2 : ∀ w ∈ Λ, ∃ m : ℤ, Algebra.trace ℚ E (h y w) = m := fun w hw => by
      obtain ⟨c, rfl⟩ := hbΛ w hw
      choose m hm using h1
      refine ⟨∑ j, c j * m j, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Int.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, map_zsmul, hm, zsmul_eq_mul, Int.cast_mul]
    have h3 : (N : E) • (D : E) • y ∈ Λ := hdual _ fun w hw => by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      refine hDa _ fun t ht => ?_
      obtain ⟨m, hm⟩ := h2 _ (hO _ (isIntegral_star ht) w hw)
      exact ⟨m, by rw [← hm, map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]⟩
    obtain ⟨c, hc⟩ := hbΛ _ h3
    have h4 : ∑ i, ((N : ℚ) * D * x i - c i) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul, ← hc, mul_smul,
        ← Finset.smul_sum, ← hy, sub_self]
    have h5 := Fintype.linearIndependent_iff.1 hbQ _ h4 i
    exact ⟨2 * c i, by push_cast; linarith⟩)
  have hcard : Fintype.card κ ≠ 0 := by
    rw [hκ, hFV]; exact mul_ne_zero finrank_pos.ne' (by omega)
  set M : ℝ := |((N * D * 2 : ℤ) : ℝ)| with hM
  have hM' : 0 ≤ M := abs_nonneg _
  obtain ⟨z, hz0, hz⟩ := exists_short_of_trace_det q hqs b hκ (t := M + 1) (by positivity) hT0 (by
    have h1 : |((T.det : ℚ) : ℝ)| ≤ M ^ Fintype.card κ := by rw [hM]; exact_mod_cast hT1
    have h2 : M ^ Fintype.card κ < (M + 1) ^ Fintype.card κ :=
      pow_lt_pow_left₀ (by linarith) hM' hcard
    have h3 : 1 ≤ (M + 1) ^ Fintype.card κ := one_le_pow₀ (by linarith)
    refine h1.trans_lt (h2.trans_le ?_)
    nlinarith)
  refine ⟨∑ i, z i • b i, sum_mem fun i _ => Λ.smul_mem _ (β i).2, fun h0 => hz0 ?_, fun φ => ?_⟩
  · exact funext (Fintype.linearIndependent_iff.1 hbZ z h0)
  · have h1 := hz (φ.comp (algebraMap F E))
    rw [hFV] at h1
    refine le_trans ?_ h1
    change _ ≤ ‖φ (h _ _ + h _ _)‖
    rw [← two_mul, map_mul, norm_mul, map_ofNat, Complex.norm_ofNat]
    linarith [norm_nonneg (φ (h (∑ i, z i • b i) (∑ i, z i • b i)))]

end GlobalTheory.HermClass
