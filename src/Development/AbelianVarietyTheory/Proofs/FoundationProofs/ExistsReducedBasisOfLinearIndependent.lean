module

public import ReciprocityTheory.ReducedBases.ExistsRedOf
public import ReciprocityTheory.ReducedBases.PrefixProdGeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IntegralModuleBases.NormGsoSqLeTwoPowMulOfValEqAdd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst
public import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReducedBasisOfLinearIndependent
noncomputable section

open Finset Module Matrix
open scoped InnerProductSpace TensorProduct MatrixOrder ComplexOrder

namespace GlobalTheory

open ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2 ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

section Family

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem rpow_half_sq (d : ℕ) : ((2 : ℝ) ^ ((d : ℝ) / 2)) ^ 2 = 2 ^ d := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
  congr 1; push_cast; ring

theorem nu_sq_mul_le_norm_sq (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ)
    (j : Fin d) : nu b c j ^ 2 * ‖gs b j‖ ^ 2 ≤ ‖∑ l, c l • b l‖ ^ 2 := by
  rw [norm_sq_comb b hb c]
  exact single_le_sum (f := fun j => nu b c j ^ 2 * ‖gs b j‖ ^ 2)
    (fun k _ => by positivity) (mem_univ j)

theorem abs_inner_le_of_isRed (b : Fin d → E) (hr : IsRed b) (c : Fin d → ℤ) (i : Fin d) :
    |⟪b i, ∑ l, (c l : ℝ) • b l⟫_ℝ| ≤
      (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * ‖∑ l, (c l : ℝ) • b l‖ ^ 2 := by
  classical
  set x := ∑ l, (c l : ℝ) • b l with hx
  set s := (2 : ℝ) ^ ((d : ℝ) / 2) with hs
  have hs0 : 0 < s := by positivity
  by_cases hc : c = 0
  · simp [hx, hc]
  obtain ⟨t, ht, hmax⟩ := exists_max_image (univ.filter fun l => c l ≠ 0) id
    (by simpa [Finset.Nonempty, funext_iff] using hc)
  have ht0 : c t ≠ 0 := (mem_filter.1 ht).2
  have htop : ∀ l, t < l → (c l : ℝ) = 0 := by
    intro l hl
    by_contra h
    exact absurd (hmax l (mem_filter.2 ⟨mem_univ _, by exact_mod_cast h⟩)) (not_le.2 hl)
  have hgt : ‖gs b t‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have h1 := nu_sq_mul_le_norm_sq b hr.1 (fun l => (c l : ℝ)) t
    rw [nu_top b hr.1 _ t htop] at h1
    have h2 : (1 : ℝ) ≤ (c t : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ c t ^ 2 := by
        have := sq_pos_of_ne_zero ht0
        omega
      exact_mod_cast this
    nlinarith [sq_nonneg ‖gs b t‖]
  have hterm : ∀ j, |⟪mu b i j • gs b j, x⟫_ℝ| ≤ s * ‖x‖ ^ 2 := by
    intro j
    have hmu : |mu b i j| ≤ 1 := by
      rcases lt_trichotomy j i with h | h | h
      · linarith [hr.2.1 i j h]
      · rw [h, mu_self b hr.1, abs_one]
      · rw [mu_of_lt b h, abs_zero]; exact zero_le_one
    rw [real_inner_smul_left, abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) hmu).trans ?_
    rcases le_or_gt j t with h | h
    · have h1 := gs_sq_le_pow b hr t j h
      have h2 : (2 : ℝ) ^ (t.val - j.val) ≤ 2 ^ d :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : ‖gs b j‖ ≤ s * ‖x‖ := by
        refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
        rw [mul_pow, hs, rpow_half_sq]
        exact h1.trans (mul_le_mul h2 hgt (sq_nonneg _) (by positivity))
      calc _ ≤ ‖gs b j‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ ≤ s * ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ = _ := by ring
    · rw [hx, inner_gs_comb b hr.1, nu_eq_zero_of b _ j fun l hl => htop l (h.trans_le hl)]
      rw [zero_mul, abs_zero]; positivity
  conv_lhs => rw [b_eq_sum b hr.1 i, sum_inner]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j _ => hterm j).trans_eq ?_)
  simp [mul_assoc]

theorem abs_nu_le_of_isRed (b : Fin d → E) (hr : IsRed b) (c : Fin d → ℝ) {N : ℝ} (hN : 0 < N)
    (hmin : ∀ w : Fin d → ℤ, ‖∑ l, c l • b l‖ ^ 2 ≤ ‖∑ l, (c l - N * w l) • b l‖ ^ 2)
    (t : Fin d) : |nu b c t| ≤ (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * N := by
  obtain ⟨w, hw0, hw⟩ := babai b hr.1 c hN (t.val + 1) t.isLt
  have h := hmin w
  rw [norm_sq_comb b hr.1, norm_sq_comb b hr.1,
    ← sum_filter_add_sum_filter_not univ (fun j : Fin d => j.val ≤ t.val),
    ← sum_filter_add_sum_filter_not univ (fun j : Fin d => j.val ≤ t.val)] at h
  have e : ∑ j ∈ univ.filter (fun j : Fin d => ¬ j.val ≤ t.val),
      nu b (fun l => c l - N * w l) j ^ 2 * ‖gs b j‖ ^ 2 =
      ∑ j ∈ univ.filter (fun j : Fin d => ¬ j.val ≤ t.val), nu b c j ^ 2 * ‖gs b j‖ ^ 2 := by
    refine sum_congr rfl fun j hj => ?_
    have hj' : ¬ j.val ≤ t.val := (mem_filter.1 hj).2
    rw [nu_sub, nu_eq_zero_of b (fun l => (w l : ℝ)) j fun l hl => by
      rw [hw0 l (by rw [Fin.le_def] at hl; omega), Int.cast_zero]]
    simp
  rw [e, add_le_add_iff_right] at h
  have h1 : nu b c t ^ 2 * ‖gs b t‖ ^ 2 ≤
      ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ t.val), nu b c j ^ 2 * ‖gs b j‖ ^ 2 :=
    single_le_sum (f := fun j => nu b c j ^ 2 * ‖gs b j‖ ^ 2)
      (fun k _ => by positivity) (mem_filter.2 ⟨mem_univ _, le_rfl⟩)
  have h2 : ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ t.val),
      nu b (fun l => c l - N * w l) j ^ 2 * ‖gs b j‖ ^ 2 ≤
      (N / 2) ^ 2 * ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ t.val), ‖gs b j‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hw j (Nat.lt_succ_of_le (mem_filter.1 hj).2)) 2
  have h3 := sum_gs_le b hr.2.2 t.val t.isLt
  have h4 : (2 : ℝ) ^ (t.val + 1) - 1 ≤ 2 ^ d := by
    have : (2 : ℝ) ^ (t.val + 1) ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) t.isLt
    linarith
  have hg : 0 < ‖gs b t‖ ^ 2 := by have := gs_ne_zero b hr.1 t; positivity
  have h5 : nu b c t ^ 2 * ‖gs b t‖ ^ 2 ≤ ((N / 2) ^ 2 * 2 ^ d) * ‖gs b t‖ ^ 2 := by
    rw [mul_assoc]
    exact (h1.trans h).trans (h2.trans (mul_le_mul_of_nonneg_left
      (h3.trans (mul_le_mul_of_nonneg_right h4 hg.le)) (sq_nonneg _)))
  refine abs_le_of_sq_le_sq ((le_of_mul_le_mul_right h5 hg).trans_eq ?_) (by positivity)
  rw [Real.rpow_sub_one (by norm_num), mul_pow, div_pow, div_pow, rpow_half_sq]
  ring

theorem abs_coeff_le_of_isRed (b : Fin d → E) (hr : IsRed b) (c : Fin d → ℝ) {N : ℝ} (hN : 0 < N)
    (hmin : ∀ w : Fin d → ℤ, ‖∑ l, c l • b l‖ ^ 2 ≤ ‖∑ l, (c l - N * w l) • b l‖ ^ 2)
    (i : Fin d) : |c i| ≤ C1 d * N := by
  have h := coeff_bound b hr.1 hr.2.1 c (by positivity) (abs_nu_le_of_isRed b hr c hN hmin) i
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast i.pos
  refine h.trans ?_
  rw [C1, mul_assoc, mul_assoc]
  exact le_mul_of_one_le_left (by positivity) hd

end Family

theorem exists_reduced_basis_matrix : ExistsBoundedBasis := by
  intro d A hA
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin d) (Fin d) ℝ, A = Bᴴ * B := by
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
    exact ⟨B, hB⟩
  obtain ⟨e, hr⟩ :=
    exists_red_of (fB B) (fun e => (li_basis A B hA hB e).2) (hlow_of A B hA hB)
  refine ⟨e, fun i μ => ?_, fun N hN α hα i => ?_⟩
  · have h := abs_inner_le_of_isRed _ hr (fun l => e.repr μ l) i
    rw [← fB_expand B e μ] at h
    rwa [polar_eq A B hB, polar_eq A B hB, real_inner_self_eq_norm_sq]
  · refine abs_coeff_le_of_isRed _ hr (fun l => (e.repr α l : ℝ))
      (by exact_mod_cast hN) (fun w => ?_) i
    have h := hα (-e.equivFun.symm w)
    rw [Q_eq A B hB, Q_eq A B hB, fB_expand B e, fB_expand B e] at h
    have e1 : ∀ l, ((e.repr (α + N • -e.equivFun.symm w) l : ℤ) : ℝ) =
        (e.repr α l : ℝ) - N * w l := by
      intro l
      have : e.repr (e.equivFun.symm w) l = w l := congrFun (e.equivFun.apply_symm_apply w) l
      rw [map_add (f := _), map_smul, map_neg, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.neg_apply, this]
      push_cast [smul_eq_mul]; ring
    simp only [e1] at h
    linarith

section Lattice

variable {X : Type*} [AddCommGroup X] {d : ℕ}

theorem polar_equivFun (q : QuadraticMap ℤ X ℝ) (b : Basis (Fin d) ℤ X) (x y : X) :
    ReciprocityTheory.ReducedBases.polar (Matrix.of fun i j => QuadraticMap.polar q (b i) (b j))
      (b.equivFun x) (b.equivFun y) = QuadraticMap.polar q x y := by
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y, ← QuadraticMap.polarBilin_apply_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    QuadraticMap.polarBilin_apply_apply, ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, mulVec, of_apply,
    mul_sum, Basis.equivFun_apply, zsmul_eq_mul]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem quadratic_equivFun (q : QuadraticMap ℤ X ℝ) (b : Basis (Fin d) ℤ X) (x : X) :
    Q (Matrix.of fun i j => QuadraticMap.polar q (b i) (b j)) (b.equivFun x) = q x := by
  rw [Q, polar_equivFun, QuadraticMap.polar_self, nsmul_eq_mul]; push_cast; ring

theorem exists_reduced_basis_of_posDef_gram (q : QuadraticMap ℤ X ℝ) (b : Basis (Fin d) ℤ X)
    (hq : (Matrix.of fun i j => QuadraticMap.polar q (b i) (b j)).PosDef) :
    ∃ e : Basis (Fin d) ℤ X,
      (∀ (i : Fin d) (μ : X), |QuadraticMap.polar q (e i) μ| ≤
        (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * QuadraticMap.polar q μ μ) ∧
      ∀ N : ℤ, 1 ≤ N → ∀ α : X, (∀ w : X, q α ≤ q (α + N • w)) → ∀ i : Fin d,
        |(e.repr α i : ℝ)| ≤ (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * N := by
  obtain ⟨e, h1, h2⟩ := exists_reduced_basis_matrix d _ hq
  refine ⟨e.map b.equivFun.symm, fun i μ => ?_, fun N hN α hα i => ?_⟩
  · have h := h1 i (b.equivFun μ)
    rw [← polar_equivFun q b, ← polar_equivFun q b]
    simpa only [Basis.map_apply, LinearEquiv.apply_symm_apply] using h
  · refine h2 N hN (b.equivFun α) (fun w => ?_) i
    have h := hα (b.equivFun.symm w)
    rw [← quadratic_equivFun q b, ← quadratic_equivFun q b] at h
    simpa only [map_add (f := _), map_smul, LinearEquiv.apply_symm_apply] using h

theorem exists_reduced_basis_pairing_coord [Module.Free ℤ X] [Module.Finite ℤ X]
    (hd : finrank ℤ X = d) (q : QuadraticMap ℤ X ℝ) (hq : (realExt q).PosDef) :
    ∃ e : Basis (Fin d) ℤ X,
      (∀ (i : Fin d) (μ : X), |QuadraticMap.polar q (e i) μ| ≤
        (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * QuadraticMap.polar q μ μ) ∧
      ∀ N : ℤ, 1 ≤ N → ∀ α : X, (∀ w : X, q α ≤ q (α + N • w)) → ∀ i : Fin d,
        |(e.repr α i : ℝ)| ≤ (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * N :=
  exists_reduced_basis_of_posDef_gram q _
    (posDef_gram_of_posDef_realExt (finBasisOfFinrankEq ℤ X hd) hq)

theorem lt_add_smul_of_abs_polar_le (q : QuadraticMap ℤ X ℝ) {e μ : X} {c : ℝ} {N : ℤ}
    (hc : 0 ≤ c) (hN : 2 * c < N) (hμ : 0 < q μ)
    (h : |QuadraticMap.polar q e μ| ≤ c * QuadraticMap.polar q μ μ) :
    q e < q (e + N • μ) ∧ q (-e) < q (-e + N • μ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  rw [QuadraticMap.polar_self, nsmul_eq_mul, abs_le] at h
  have h1 := mul_pos hN0 (mul_pos (sub_pos.2 hN) hμ)
  have h2 := mul_le_mul_of_nonneg_left h.1 hN0.le
  have h3 := mul_le_mul_of_nonneg_left h.2 hN0.le
  simp only [QuadraticMap.map_add q, QuadraticMap.polar_smul_right, QuadraticMap.polar_neg_left,
    QuadraticMap.map_smul, zsmul_eq_mul]
  push_cast at h2 h3 ⊢
  constructor <;> nlinarith

theorem pairing_const_mono {d g : ℕ} (h : d ≤ g) :
    (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) ≤ (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) := by
  have : (d : ℝ) ≤ g := by exact_mod_cast h
  gcongr; norm_num

theorem coordinate_const_mono {d g : ℕ} (h : d ≤ g) :
    (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1) ≤
      (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by
  have : (d : ℝ) ≤ g := by exact_mod_cast h
  gcongr <;> norm_num

theorem exists_reduced_basis_unique_min_of_le [Module.Free ℤ X] [Module.Finite ℤ X]
    (hd : finrank ℤ X = d) {g : ℕ} (hg : d ≤ g) (q : QuadraticMap ℤ X ℝ)
    (hq : (realExt q).PosDef) :
    ∃ e : Basis (Fin d) ℤ X,
      (∀ (i : Fin d) (μ : X), |QuadraticMap.polar q (e i) μ| ≤
        (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) * QuadraticMap.polar q μ μ) ∧
      (∀ N : ℤ, 1 ≤ N → ∀ α : X, (∀ w : X, q α ≤ q (α + N • w)) → ∀ i : Fin d,
        |(e.repr α i : ℝ)| ≤ (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) * N) ∧
      ∀ N : ℤ, 2 * ((g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2)) < N → ∀ (i : Fin d) (w : X), w ≠ 0 →
        q (e i) < q (e i + N • w) ∧ q (-e i) < q (-e i + N • w) := by
  obtain ⟨e, h1, h2⟩ := exists_reduced_basis_pairing_coord hd q hq
  have hp := posDef_of_posDef_realExt hq
  have h1' : ∀ (i : Fin d) (μ : X), |QuadraticMap.polar q (e i) μ| ≤
      (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) * QuadraticMap.polar q μ μ := fun i μ => by
    refine (h1 i μ).trans (mul_le_mul_of_nonneg_right (pairing_const_mono hg) ?_)
    rw [QuadraticMap.polar_self]
    exact nsmul_nonneg (hp.nonneg μ) 2
  refine ⟨e, h1', fun N hN α hα i => (h2 N hN α hα i).trans ?_, fun N hN i w hw =>
    lt_add_smul_of_abs_polar_le q (by positivity) hN (hp w hw) (h1' i w)⟩
  exact mul_le_mul_of_nonneg_right (coordinate_const_mono hg) (by exact_mod_cast (by omega))

end Lattice

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfJKMem
open scoped MatrixGroups

open Polynomial

namespace GlobalTheory.K4.LevNormal

open GlobalTheory.KZ

theorem normal_of_fixed (F L : Type) [Field F] [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]
    (h : ∀ x : L, (∀ σ : L ≃ₐ[F] L, σ x = x) → x ∈ Set.range (algebraMap F L)) : Normal F L := by
  classical
  rw [normal_iff]
  intro x
  have hx : IsIntegral F x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  refine ⟨hx, ?_⟩
  have hfin : (Set.range fun σ : L ≃ₐ[F] L => σ x).Finite := by
    refine ((minpoly F x).rootSet_finite L).subset ?_
    rintro _ ⟨σ, rfl⟩
    rw [mem_rootSet]
    refine ⟨minpoly.ne_zero hx, ?_⟩
    show aeval (σ x) (minpoly F x) = 0
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  set O := hfin.toFinset with hO
  set P : L[X] := ∏ g ∈ O, (X - C g) with hP
  have hmap : ∀ σ : L ≃ₐ[F] L, P.map (σ : L →+* L) = P := by
    intro σ
    rw [hP, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    refine Finset.prod_bijective σ σ.bijective ?_ (fun _ _ => rfl)
    intro g
    simp only [hO, Set.Finite.mem_toFinset, Set.mem_range]
    constructor
    · rintro ⟨τ, rfl⟩
      exact ⟨σ * τ, rfl⟩
    · rintro ⟨τ, hτ⟩
      refine ⟨σ⁻¹ * τ, ?_⟩
      show σ.symm (τ x) = g
      rw [hτ, σ.symm_apply_apply]
  have hl : P ∈ lifts (algebraMap F L) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    apply h
    intro σ
    have := congrArg (fun Q => Q.coeff n) (hmap σ)
    simpa [coeff_map] using this
  have hmon : P.Monic := monic_prod_of_monic _ _ fun g _ => monic_X_sub_C g
  obtain ⟨Q, hQ⟩ := (mem_lifts P).1 hl
  have h0 : aeval x Q = 0 := by
    rw [aeval_def, ← eval_map, hQ, hP, eval_prod]
    refine Finset.prod_eq_zero (i := x) ?_ (by simp)
    simp only [hO, Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨1, rfl⟩
  have hd : (minpoly F x).map (algebraMap F L) ∣ P := by
    rw [← hQ]
    exact Polynomial.map_dvd _ (minpoly.dvd F x h0)
  have hs : P.Splits := Splits.prod fun g _ => Splits.X_sub_C g
  exact hs.of_dvd hmon.ne_zero hd

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem isAlgebraic_of_jK_mem [Algebra.IsAlgebraic ℚ Ω] (X : Tower Ω ε) (F : Subfield X.K) (hj : X.jK ∈ F) (f : X.K) :
    IsAlgebraic F f := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : CharZero X.K := charZero_of_injective_algebraMap (algebraMap Ω X.K).injective
  let A : IntermediateField F X.K := algebraicClosure F X.K
  have hc : ∀ c : Ω, algebraMap Ω X.K c ∈ A := by
    intro c
    rw [mem_algebraicClosure_iff]
    have h1 : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic c)
    have h2 : IsAlgebraic ℤ (algebraMap Ω X.K c) := h1.algHom (algebraMap Ω X.K).toIntAlgHom
    exact h2.extendScalars (R := ℤ) (S := F) (RingHom.injective_int _)
  let B : IntermediateField Ω X.K := A.toSubfield.toIntermediateField hc
  have hle : IntermediateField.adjoin Ω {X.jK} ≤ B := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact A.algebraMap_mem ⟨X.jK, hj⟩
  have h3 : IsAlgebraic A f := by
    obtain ⟨p, hp, h0⟩ := X.alg_j f
    let φ : IntermediateField.adjoin Ω {X.jK} →+* A :=
      (IntermediateField.adjoin Ω {X.jK}).toSubfield.subtype.codRestrict A fun y => hle y.2
    refine ⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).2 hp, ?_⟩
    rw [aeval_def, eval₂_map]
    exact h0
  exact h3.restrictScalars F

theorem gal_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (m : ℕ) (ζ : Ω) (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m)
    (hΓ : CongruenceSubgroup.Gamma m ≤ Γ') (s : Ω ≃ₐ[ℚ] Ω) (hs : s ζ = ζ) (f : X.K) (hf : f ∈ lev X Γ') :
    X.gal s f ∈ lev X Γ' := by
  rw [mem_lev_iff] at hf ⊢
  intro γ hγ
  have := X.recip m f hm (fun δ hδ => hf δ (hΓ hδ)) ζ hζ s 1 (by simpa using hs) γ γ (by simp)
  rw [← this, hf γ hγ]

theorem normal : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (m : ℕ) (ζ : Ω), 0 < m → IsPrimitiveRoot ζ m → CongruenceSubgroup.Gamma m ≤ Γ' → letI := GlobalTheory.K4.algMdl X Γ' (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup; Normal (GlobalTheory.K4.mdl X Γ' (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup) (GlobalTheory.K4.lev X Γ') := by
  intro Ω _ _ _ ε X Γ' m ζ hm hζ hΓ
  set S := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup with hS
  letI := algMdl X Γ' S
  haveI := isScalarTower_mdl X Γ' S
  haveI : Algebra.IsAlgebraic (mdl X Γ' S) (lev X Γ') := ⟨fun f =>
    (isAlgebraic_algebraMap_iff (A := X.K) (lev X Γ').subtype.injective).1
      (isAlgebraic_of_jK_mem X _ (jK_mem_mdl X Γ' S) (f : X.K))⟩
  apply normal_of_fixed
  intro x hx
  refine ⟨⟨x, (mem_mdl_iff X Γ' S _).2 ⟨x.2, fun s hs => ?_⟩⟩, rfl⟩
  have hsζ : s ζ = ζ := hs ⟨ζ, IntermediateField.subset_adjoin ℚ {ζ} rfl⟩
  let φ : lev X Γ' →ₐ[mdl X Γ' S] lev X Γ' :=
    { ((X.gal s).toRingHom.comp (lev X Γ').subtype).codRestrict (lev X Γ')
        (fun f => gal_mem_lev X Γ' m ζ hm hζ hΓ s hsζ f f.2) with
      commutes' := fun y => Subtype.ext (((mem_mdl_iff X Γ' S _).1 y.2).2 s hs) }
  exact congrArg Subtype.val (hx (AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)))

end GlobalTheory.K4.LevNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstUpperTriangularHahnMulAndOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstUpperTriangularHahnMulAndOne
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.CyclotomicQExpansion

section Character

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)

theorem exp_mem_range_of_isAlgClosed (x : ℚ) :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ Set.range ε := by
  have hMΩ : ((x.den : ℕ) : Ω) ≠ 0 := by
    intro h
    have := congrArg ε h
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at this
    exact x.den_nz this
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨hMΩ⟩
  haveI : NeZero x.den := ⟨x.den_nz⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have hζ' := hζ.map_of_injective ε.injective
  have hw : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [← hx]; ring
    rw [this]; exact Complex.exp_int_mul_two_pi_mul_I _
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hw
  exact ⟨ζ ^ i, by rw [map_pow]; exact hi⟩

theorem eOm_spec (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exp_mem_range_of_isAlgClosed ε x)

theorem eOm_add (x y : ℚ) : eOm ε (x + y) = eOm ε x * eOm ε y := by
  apply ε.injective
  rw [map_mul, eOm_spec, eOm_spec, eOm_spec, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem eOm_zero : eOm ε 0 = 1 := by
  apply ε.injective
  rw [eOm_spec, map_one]; simp

end Character

section Coeff

variable {R : Type*} [CommRing R]

theorem cm_coeff (c : ℚ → R) (φ : HahnSeries ℚ R) (r : ℚ) : (cm c φ).coeff r = c r * φ.coeff r := rfl

theorem cm_mul (c : ℚ → R) (hc : ∀ r s, c (r + s) = c r * c s) (φ ψ : HahnSeries ℚ R) :
    cm c (φ * ψ) = cm c φ * cm c ψ := by
  ext r
  have h1 : (cm c φ).support ⊆ φ.support := fun t ht h => ht (by simp [cm_coeff, h])
  have h2 : (cm c ψ).support ⊆ ψ.support := fun t ht h => ht (by simp [cm_coeff, h])
  rw [cm_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, Finset.mul_sum]
  have e1 : ∀ ij ∈ Finset.antidiagonal φ.isPWO_support ψ.isPWO_support r,
      c r * (φ.coeff ij.1 * ψ.coeff ij.2) = (cm c φ).coeff ij.1 * (cm c ψ).coeff ij.2 := by
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    rw [cm_coeff, cm_coeff, ← hij.2.2, hc]; ring
  rw [Finset.sum_congr rfl e1]
  symm
  apply Finset.sum_subset
  · intro ij hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    exact ⟨h1 hij.1, h2 hij.2.1, hij.2.2⟩
  · intro ij hij hn
    rw [Finset.mem_antidiagonal] at hij hn
    by_contra hne
    exact hn ⟨(HahnSeries.mem_support _ _).2 (ne_zero_and_ne_zero_of_mul hne).1,
      (HahnSeries.mem_support _ _).2 (ne_zero_and_ne_zero_of_mul hne).2, hij.2.2⟩

theorem cm_one (c : ℚ → R) (hc : c 0 = 1) : cm c (1 : HahnSeries ℚ R) = 1 := by
  ext r
  rw [cm_coeff, HahnSeries.coeff_one]
  split_ifs with h
  · subst h; rw [hc, mul_one]
  · rw [mul_zero]

theorem scale_mul {a : ℚ} (ha : 0 < a) (φ ψ : HahnSeries ℚ R) : scale a (φ * ψ) = scale a φ * scale a ψ := by
  simp only [scale, dif_pos ha]
  exact HahnSeries.embDomain_mul _ (fun x y => by simp [mul_add]) φ ψ

theorem scale_one {a : ℚ} (ha : 0 < a) : scale a (1 : HahnSeries ℚ R) = 1 := by
  simp only [scale, dif_pos ha]
  exact HahnSeries.embDomain_one _ (by simp)

end Coeff

theorem sub_mul_and_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d →
    ∀ φ ψ : HahnSeries ℚ Ω,
  sub ε a b d (φ * ψ) = sub ε a b d φ * sub ε a b d ψ ∧ sub ε a b d 1 = 1 := by
  intro Ω _ _ _ ε a b d h φ ψ
  have hc : ∀ r s : ℚ, eOm ε ((r + s) * b / d) = eOm ε (r * b / d) * eOm ε (s * b / d) := by
    intro r s; rw [← eOm_add]; congr 1; ring
  have h0 : eOm ε (0 * b / d) = 1 := by rw [zero_mul, zero_div, eOm_zero]
  refine ⟨?_, ?_⟩
  · simp only [sub]; rw [cm_mul _ hc, scale_mul h]
  · simp only [sub]; rw [cm_one _ h0, scale_one h]

end GlobalTheory.CyclotomicQExpansion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstUpperTriangularHahnMulAndOneStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.substUpperTriangularHahn_mul_and_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d → ∀ φ ψ : HahnSeries ℚ Ω,
  sub ε a b d (φ * ψ) = sub ε a b d φ * sub ε a b d ψ ∧ sub ε a b d 1 = 1 := by
  first | exact @GlobalTheory.CyclotomicQExpansion.sub_mul_and_one | exact GlobalTheory.CyclotomicQExpansion.sub_mul_and_one | (intros; apply GlobalTheory.CyclotomicQExpansion.sub_mul_and_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDivSqrtLeFourExp
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem badBound_tail (eps C : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in Filter.atTop,
      612 * (x ^ C) ^ 3 * Real.exp (-(x ^ (eps / 6))) ≤ Real.exp (-(x ^ (eps / 7))) := by
  have hb : 0 < eps / 7 := by positivity
  have hab : 0 < eps / 6 - eps / 7 := by linarith
  have h612 : 0 ≤ Real.log 612 := Real.log_nonneg (by norm_num)
  set K : ℝ := 1 + Real.log 612 + 3 * |C| / (eps / 7) with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (K ^ (1 / (eps / 6 - eps / 7)))] with x hx1 hxK
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxb : 1 ≤ x ^ (eps / 7) := Real.one_le_rpow hx1 hb.le
  have hl : Real.log x ≤ x ^ (eps / 7) / (eps / 7) := Real.log_le_rpow_div hx0.le hb
  have hd : K ≤ x ^ (eps / 6 - eps / 7) := by
    calc K = (K ^ (1 / (eps / 6 - eps / 7))) ^ (eps / 6 - eps / 7) := by
          rw [← Real.rpow_mul hK0, one_div_mul_cancel hab.ne', Real.rpow_one]
      _ ≤ x ^ (eps / 6 - eps / 7) := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hxK hab.le
  have hsplit : x ^ (eps / 6) = x ^ (eps / 6 - eps / 7) * x ^ (eps / 7) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hpow : (x ^ C) ^ 3 = Real.exp (3 * (Real.log x * C)) := by
    rw [Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]; norm_num
  rw [hpow, show (612 : ℝ) = Real.exp (Real.log 612) from (Real.exp_log (by norm_num)).symm,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hC1 : Real.log x * C ≤ Real.log x * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hlog
  have hC2 : Real.log x * |C| ≤ x ^ (eps / 7) / (eps / 7) * |C| :=
    mul_le_mul_of_nonneg_right hl (abs_nonneg C)
  have hKx : K * x ^ (eps / 7) ≤ x ^ (eps / 6) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hl612 : Real.log 612 ≤ Real.log 612 * x ^ (eps / 7) := le_mul_of_one_le_right h612 hxb
  have h3 : 3 * (Real.log x * C) ≤ 3 * |C| / (eps / 7) * x ^ (eps / 7) := by
    calc 3 * (Real.log x * C) ≤ 3 * (x ^ (eps / 7) / (eps / 7) * |C|) := by linarith
      _ = 3 * |C| / (eps / 7) * x ^ (eps / 7) := by ring
  have h4 : (1 + Real.log 612 + 3 * |C| / (eps / 7)) * x ^ (eps / 7) =
      x ^ (eps / 7) + Real.log 612 * x ^ (eps / 7) + 3 * |C| / (eps / 7) * x ^ (eps / 7) := by ring
  rw [hK, h4] at hKx
  linarith

theorem log_div_sqrt_le_four_exp {g u : ℝ} (hg : Real.exp (4 * u) ≤ g) :
    Real.log g / Real.sqrt g ≤ 4 * Real.exp (-u) := by
  have hg0 : 0 < g := lt_of_lt_of_le (Real.exp_pos _) hg
  set q := g ^ (1 / 4 : ℝ) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hg0 _
  have h1 : Real.log g ≤ g ^ (1 / 4 : ℝ) / (1 / 4) := Real.log_le_rpow_div hg0.le (by norm_num)
  have hs : Real.sqrt g = q * q := by
    rw [hqdef, ← Real.rpow_add hg0, Real.sqrt_eq_rpow]; norm_num
  have hq : Real.exp u ≤ q := by
    have : Real.exp u = (Real.exp (4 * u)) ^ (1 / 4 : ℝ) := by
      rw [← Real.exp_mul]; ring_nf
    rw [this]; exact Real.rpow_le_rpow (Real.exp_pos _).le hg (by norm_num)
  have hone : 1 ≤ Real.exp (-u) * q := by
    calc (1 : ℝ) = Real.exp (-u) * Real.exp u := by rw [← Real.exp_add]; simp
      _ ≤ Real.exp (-u) * q := mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
  rw [hs, div_le_iff₀ (by positivity)]
  have h1' : Real.log g ≤ 4 * q := by rw [← hqdef] at h1; linarith
  nlinarith [hq0, hone]

theorem badBound_numbers : ∀ eps C : ℝ, 0 < eps → eps ≤ 1 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (g f m N q : ℝ), Real.exp (8 * x ^ eps) ≤ g → x ^ (2 : ℝ) ≤ f → f ≤ x ^ C → 0 ≤ m → m ≤ x ^ C → x ^ eps ≤ N → N ≤ x ^ C → Real.exp (x ^ (eps / 6)) ≤ q → 100000 ≤ N ∧ 0 ≤ badBound g f m N q ∧ 6 * badBound g f m N q ≤ Real.exp (-(x ^ (eps / 7))) := by
  intro eps C he he1
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1 (badBound_tail eps C he)
  refine ⟨max (max X1 8) (max (20 * |C| + 1) ((100000 : ℝ) ^ (1 / eps))), ?_⟩
  intro x hx g f m N q hg hf1 hf2 hm1 hm2 hN1 hN2 hq
  have hxX1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx8 : 8 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC : 20 * |C| + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxN : (100000 : ℝ) ^ (1 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx1' : 1 < x := by linarith
  have hNbig : 100000 ≤ N := by
    have e : (100000 : ℝ) = ((100000 : ℝ) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel he.ne', Real.rpow_one]
    have h2 : ((100000 : ℝ) ^ (1 / eps)) ^ eps ≤ x ^ eps := Real.rpow_le_rpow (by positivity) hxN he.le
    linarith
  have hTail := hX1 x hxX1
  have hCe : eps ≤ C := (Real.rpow_le_rpow_left_iff hx1').1 (le_trans hN1 hN2)
  have hC0 : 0 ≤ C := by linarith
  set P := x ^ C with hP
  set E := Real.exp (-(x ^ (eps / 6))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hN0 : 0 < N := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hx1 hC0
  have hx2 : x ^ (2 : ℝ) = x * x := by rw [Real.rpow_two, sq]
  rw [hx2] at hf1
  have hf0 : 0 ≤ f := le_trans (by positivity) hf1
  have he6 : x ^ (eps / 6) ≤ x ^ eps := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have he6h : x ^ (eps / 6) ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by rw [← Real.rpow_add hx0]; norm_num
  have hs0 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
  have hsx : x ^ (1 / 2 : ℝ) ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hxe1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1 he.le
  have hg8 : Real.exp 8 ≤ g := le_trans (Real.exp_le_exp.2 (by linarith)) hg
  have hg2 : 2 ≤ g := by have := Real.add_one_le_exp 8; linarith
  have hg0 : 0 < g := by linarith
  have hEg : 1 ≤ E * g := by
    calc (1 : ℝ) = E * Real.exp (x ^ (eps / 6)) := by rw [hE, ← Real.exp_add]; simp
      _ ≤ E * g := mul_le_mul_of_nonneg_left (le_trans (Real.exp_le_exp.2 (by linarith)) hg) hE0.le
  have hginv : 1 / g ≤ E := by rw [div_le_iff₀ hg0]; linarith
  have hT2 : Real.log g / Real.sqrt g ≤ 4 * E := by
    have h := log_div_sqrt_le_four_exp (u := 2 * x ^ eps) (g := g)
      (by rw [show 4 * (2 * x ^ eps) = 8 * x ^ eps by ring]; exact hg)
    refine h.trans ?_
    rw [hE]
    gcongr
    linarith
  have hLg : 0 ≤ Real.log g / Real.sqrt g :=
    div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hq0 : 0 < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hEq : 1 ≤ E * q := by
    calc (1 : ℝ) = E * Real.exp (x ^ (eps / 6)) := by rw [hE, ← Real.exp_add]; simp
      _ ≤ E * q := mul_le_mul_of_nonneg_left hq hE0.le
  have hqinv : 1 / (4 * q) ≤ E / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hlogN : 1 + Real.log N ≤ N := by linarith [Real.log_le_sub_one_of_pos hN0]
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hT3b : (1 + Real.log N) / (g - 1) ≤ 2 * N * E := by
    rw [div_le_iff₀ (by linarith)]
    have h1 := mul_nonneg (mul_nonneg hN0.le hE0.le) (show 0 ≤ g - 2 by linarith)
    have h2 : N * 1 ≤ N * (E * g) := mul_le_mul_of_nonneg_left hEg hN0.le
    linarith
  have hT4 : (7 / 8 : ℝ) ^ f ≤ E := by
    rw [Real.rpow_def_of_pos (by norm_num), hE, Real.exp_le_exp]
    have hl78 : Real.log (7 / 8) ≤ -(1 / 8) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 8 by norm_num); linarith
    have h1 : Real.log (7 / 8) * f ≤ -(1 / 8) * f := mul_le_mul_of_nonneg_right hl78 hf0
    have h2 : 8 * x ≤ x * x := mul_le_mul_of_nonneg_right hx8 hx0.le
    linarith
  have hT5 : Real.exp (-(f / (10 * Real.log N))) ≤ E := by
    have hlN0 : 0 < Real.log N := Real.log_pos (by linarith)
    rw [hE, Real.exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by linarith)]
    have hlN : Real.log N ≤ C * Real.log x := by
      rw [← Real.log_rpow hx0]; exact Real.log_le_log hN0 hN2
    have hlx : Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hx0.le (by norm_num)
    have h1 : x ^ (eps / 6) * (10 * Real.log N) ≤
        x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) := by
      apply mul_le_mul he6h _ (by linarith) hs0
      have : C * Real.log x ≤ C * (x ^ (1 / 2 : ℝ) / (1 / 2)) := mul_le_mul_of_nonneg_left hlx hC0
      linarith
    have h2 : x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2)))) = 20 * C * x := by
      calc x ^ (1 / 2 : ℝ) * (10 * (C * (x ^ (1 / 2 : ℝ) / (1 / 2))))
          = 20 * C * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
        _ = 20 * C * x := by rw [hsq]
    have h3 : 20 * C * x ≤ x * x := by
      have : 20 * C ≤ x := by have := le_abs_self C; linarith
      exact mul_le_mul_of_nonneg_right this hx0.le
    linarith
  have hgm1 : 0 < g - 1 := by linarith
  unfold badBound
  refine ⟨hNbig, ?_, ?_⟩
  · have t1 : 0 ≤ 3 * f / g := div_nonneg (by linarith) hg0.le
    have t2 : 0 ≤ 23 * f * Real.log g / Real.sqrt g :=
      div_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by linarith))) (Real.sqrt_nonneg _)
    have t3 : 0 ≤ 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) :=
      mul_nonneg (mul_nonneg (by linarith) hm1)
        (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))
    have t4 : 0 ≤ N / 2 * (7 / 8 : ℝ) ^ f := mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
    have t5 : 0 ≤ Real.exp (-(f / (10 * Real.log N))) := (Real.exp_pos _).le
    linarith
  · have b1 : 3 * f / g ≤ 3 * P * E := by
      calc 3 * f / g = 3 * f * (1 / g) := by ring
        _ ≤ 3 * P * E := mul_le_mul (by linarith) hginv (div_nonneg zero_le_one hg0.le) (by linarith)
    have b2 : 23 * f * Real.log g / Real.sqrt g ≤ 92 * P * E := by
      calc 23 * f * Real.log g / Real.sqrt g = 23 * f * (Real.log g / Real.sqrt g) := by ring
        _ ≤ 23 * P * (4 * E) := mul_le_mul (by linarith) hT2 hLg (by linarith)
        _ = 92 * P * E := by ring
    have b3 : 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) ≤ 2 * P * P * (E / 4 + 2 * P * E) := by
      have hfm : 2 * f * m ≤ 2 * P * P := mul_le_mul (by linarith) hm2 hm1 (by linarith)
      have hsum : 1 / (4 * q) + (1 + Real.log N) / (g - 1) ≤ E / 4 + 2 * P * E := by
        have : 2 * N * E ≤ 2 * P * E := mul_le_mul_of_nonneg_right (by linarith) hE0.le
        linarith
      exact mul_le_mul hfm hsum
        (add_nonneg (div_nonneg zero_le_one (by linarith)) (div_nonneg (by linarith) hgm1.le))
        (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    have b4 : N / 2 * (7 / 8 : ℝ) ^ f ≤ P / 2 * E :=
      mul_le_mul (by linarith) hT4 (Real.rpow_nonneg (by norm_num) _) (by linarith)
    have hP0 : 0 ≤ P := by linarith
    have hPP : P ≤ P * P := le_mul_of_one_le_right hP0 hP1
    have hPPP : P * P ≤ P ^ 3 := by
      rw [show P ^ 3 = P * P * P by ring]
      exact le_mul_of_one_le_right (mul_nonneg hP0 hP0) hP1
    have c1 : P * E ≤ P ^ 3 * E := mul_le_mul_of_nonneg_right (hPP.trans hPPP) hE0.le
    have c2 : P * P * E ≤ P ^ 3 * E := mul_le_mul_of_nonneg_right hPPP hE0.le
    have c3 : E ≤ P ^ 3 * E := le_mul_of_one_le_left hE0.le (hP1.trans (hPP.trans hPPP))
    have hnn : 0 ≤ P ^ 3 * E := mul_nonneg (pow_nonneg hP0 3) hE0.le
    linarith

end GlobalTheory.BadShare
end
