module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
public import Formalism.SharpRestriction.CuspSpanNormBounds.MinorCosetSumOfLatticeIndexHypOfTieOK

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.MinorIntegralityTorus
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.MinorIntegralityTorus

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

theorem prod_norm_emb_eq_abs_norm {K : Type*} [Field K] [NumberField K] (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 : ∏ σ : K →+* ℂ, σ x = ∏ σ : K →ₐ[ℚ] ℂ, σ x :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  calc ∏ σ : K →+* ℂ, ‖σ x‖ = ‖∏ σ : K →+* ℂ, σ x‖ := (norm_prod _ _).symm
    _ = ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ := by rw [h2, h]
    _ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by simp

theorem one_le_abs_norm {K : Type*} [Field K] [NumberField K] (x : K) (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    1 ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  set y : 𝓞 K := ⟨x, hx⟩ with hy_def
  have hy : y ≠ 0 := by
    intro h
    apply h0
    first
    | exact congrArg Subtype.val h
    | simpa [y] using congrArg (algebraMap (𝓞 K) K) h
  have hN : Algebra.norm ℤ y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  have hc : ((Algebra.norm ℤ y : ℤ) : ℚ) = Algebra.norm ℚ x := Algebra.coe_norm_int y
  rw [← hc]
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ y| := Int.one_le_abs hN
  exact_mod_cast h1

theorem prod_cm {K : Type*} [Field K] [NumberField K] (Φ : Set (K →+* ℂ))
    (hΦ : ∀ φ : K →+* ℂ, φ ∈ Φ ↔ (starRingEnd ℂ).comp φ ∉ Φ) (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = ∏ σ ∈ Finset.univ.filter (· ∈ Φ), ‖σ x‖ ^ 2 := by
  have cc : ∀ σ : K →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := by
    intro σ
    ext z
    simp
  have hinj : Set.InjOn (fun φ : K →+* ℂ => (starRingEnd ℂ).comp φ)
      ↑(Finset.univ.filter (· ∈ Φ)) := by
    intro a _ c _ hab
    ext z
    have h1 := congrArg (fun ψ : K →+* ℂ => ψ z) hab
    simp only [RingHom.comp_apply] at h1
    exact (starRingEnd ℂ).injective h1
  have hc : (Finset.univ.filter (· ∈ Φ))ᶜ =
      (Finset.univ.filter (· ∈ Φ)).image (fun φ : K →+* ℂ => (starRingEnd ℂ).comp φ) := by
    ext σ
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hσ
      refine ⟨(starRingEnd ℂ).comp σ, ?_, cc σ⟩
      rw [hΦ, cc]
      exact hσ
    · rintro ⟨τ, hτ, rfl⟩
      exact (hΦ τ).1 hτ
  rw [← Finset.prod_mul_prod_compl (Finset.univ.filter (· ∈ Φ)), hc, Finset.prod_image hinj,
    Finset.prod_pow, sq]
  congr 1
  apply Finset.prod_congr rfl
  intro σ _
  simp

theorem NormLB_holds : Formalism.MainNotions.KTwoMinorIntegrality.NormLB := by
  intro D x hx h0
  have hcm := D.host.der.cmType
  have hemb := Formalism.BasicNotions.factEmb D.R D.host
  have hre : ∏ τ : D.what₂.Tau, ‖embS D τ x‖ ^ 2 =
      ∏ σ ∈ Finset.univ.filter (· ∈ D.host.cmType), ‖σ x‖ ^ 2 := by
    refine Finset.prod_bij (fun τ _ => embS D τ) ?_ ?_ ?_ ?_
    · intro τ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hemb.2 _).2 (D.eTau τ).2
    · intro τ₁ _ τ₂ _ h
      have h' := hemb.1.1 h
      exact D.eTau.injective (Subtype.ext h')
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      obtain ⟨g, rfl⟩ := hemb.1.2 σ
      have hg : g ∈ D.R.Psi := (hemb.2 g).1 hσ
      exact ⟨D.eTau.symm ⟨g, hg⟩, Finset.mem_univ _, by simp [embS]⟩
    · intro τ _
      rfl
  rw [hre, ← prod_cm _ hcm.1 x, prod_norm_emb_eq_abs_norm]
  exact one_le_abs_norm x hx h0

theorem one_mem_zpow {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) (hI : I ≠ ⊥) (n : ℕ) :
    (1 : K) ∈ ((I : FractionalIdeal (nonZeroDivisors R) K) ^ (-(n : ℤ))) := by
  rw [zpow_neg, zpow_natCast]
  have hne : ((I : FractionalIdeal (nonZeroDivisors R) K) ^ n) ≠ 0 :=
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
  rw [FractionalIdeal.mem_inv_iff hne]
  intro y hy
  rw [one_mul]
  have hle : ((I : FractionalIdeal (nonZeroDivisors R) K) ^ n) ≤ 1 := by
    rw [← FractionalIdeal.coeIdeal_pow]
    exact FractionalIdeal.coeIdeal_le_one
  exact hle hy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fr

variable (D : D7)

theorem ddS_ideal_ne : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :
    Ideal (𝓞 D.host.E)) ≠ ⊥ := by
  exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem e_mem_XS {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS) : F0.e a ∈ XS D F0 := by
  unfold XS ddS
  apply Submodule.subset_span
  refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
  convert one_mem_zpow _ (ddS_ideal_ne D) (D.R.rS - (a : ℕ))
  have := a.isLt
  omega

theorem e_mem_lam {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (hS D).V) (F : LFlag (D.sp.Y 0) D.R.rS T)
    (hX : XLam Λ F = XS D F.fl) (a : Fin D.R.rS) : F.fl.e a ∈ Λ := by
  unfold XLam at hX
  have h := e_mem_XS D F.fl a
  rw [← hX] at h
  exact (Submodule.mem_inf.mp h).1

theorem pair_int {Λ : Submodule (𝓞 D.host.E) (hS D).V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ)
    {x y : (hS D).V} (hx : x ∈ Λ) (hy : y ∈ Λ) : IsIntegral ℤ ((hS D).hT y x) := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at hU
  rw [← hU] at hx
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hx
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hx
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hx y hy)
  have hr' : ((hS D).hT y) x = algebraMap (𝓞 D.host.E) D.host.E r := hr.symm
  rw [hr']
  first
  | exact r.2
  | exact RingOfIntegers.isIntegral_coe r
  | exact RingOfIntegers.isIntegral r

end Fr

theorem det_isIntegral {E : Type*} [Field E] {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n E)
    (h : ∀ i j, IsIntegral ℤ (M i j)) : IsIntegral ℤ M.det := by
  let M' : Matrix n n (integralClosure ℤ E) := fun i j => ⟨M i j, h i j⟩
  have hM : (integralClosure ℤ E).val.toRingHom.mapMatrix M' = M := by
    ext i j
    rfl
  rw [← hM, ← RingHom.map_det]
  exact (M'.det).2

end Formalism.MainNotions.MinorIntegralityTorus

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.LatticeSumBound
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.WeightedLatticeSum
noncomputable section

namespace Formalism.MainNotions.WeightedLatticeSum

open Finset

def wt (R : ℝ) (m : ℕ) : ℝ := (max 1 (((m : ℝ) - 1) / (2 * R))) ^ (-(3 / 2 : ℝ))

lemma rpow_neg_three_halves {t : ℝ} (ht : 0 < t) : t ^ (-(3 / 2 : ℝ)) = 1 / (t * Real.sqrt t) := by
  rw [Real.rpow_neg ht.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one,
    ← Real.sqrt_eq_rpow, one_div]

lemma wt_nonneg (R : ℝ) (m : ℕ) : 0 ≤ wt R m := by
  unfold wt
  exact Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

lemma wt_le_one (R : ℝ) (m : ℕ) : wt R m ≤ 1 := by
  unfold wt
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by norm_num)

private theorem inv_mul_le_two_mul_inv_sub_inv_of_sq (k a b : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ha2 : a ^ 2 = k)
    (hb2 : b ^ 2 = k - 1) : 1 / (k * a) ≤ 2 * (1 / b - 1 / a) := by
  have hba : b ≤ a := by nlinarith
  have hab : (a - b) * (a + b) = 1 := by linear_combination ha2 - hb2
  have hD : 0 < a * b * (a + b) := mul_pos (mul_pos ha0 hb0) (add_pos ha0 hb0)
  have e : 2 * (1 / b - 1 / a) = 2 / (a * b * (a + b)) := by
    apply eq_div_of_mul_eq hD.ne'
    calc 2 * (1 / b - 1 / a) * (a * b * (a + b))
        = 2 * ((1 / b * b) * a - (1 / a * a) * b) * (a + b) := by ring
      _ = 2 * (a - b) * (a + b) := by
          rw [one_div_mul_cancel hb0.ne', one_div_mul_cancel ha0.ne']; ring
      _ = 2 := by rw [mul_assoc, hab, mul_one]
  have hk0 : 0 < k := by nlinarith
  rw [e, div_le_div_iff₀ (mul_pos hk0 ha0) hD, ← ha2]
  nlinarith [mul_le_mul_of_nonneg_left hba (sq_nonneg a),
    mul_le_mul_of_nonneg_left (mul_le_mul hba hba hb0.le ha0.le) ha0.le]

lemma tele (k : ℝ) (hk : 2 ≤ k) :
    1 / (k * Real.sqrt k) ≤ 2 * (1 / Real.sqrt (k - 1) - 1 / Real.sqrt k) := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  exact inv_mul_le_two_mul_inv_sub_inv_of_sq k _ _ (Real.sqrt_pos.mpr hk0) (Real.sqrt_pos.mpr hk1) (Real.sq_sqrt hk0.le)
    (Real.sq_sqrt hk1.le)

private theorem max_div_rpow_le_two_mul_inv_sqrt_sub (c K : ℝ) (hc : 0 < c) (hK : 2 ≤ K) (hcK : c ≤ K) :
    (max 1 (K / c)) ^ (-(3 / 2 : ℝ)) ≤
      2 * c * Real.sqrt c * (1 / Real.sqrt (K - 1) - 1 / Real.sqrt K) := by
  have hKpos : 0 < K := by linarith
  have hx : 1 ≤ K / c := by rw [le_div_iff₀ hc]; linarith
  rw [max_eq_right hx, rpow_neg_three_halves (lt_of_lt_of_le one_pos hx),
    Real.sqrt_div hKpos.le c]
  have ht := tele K hK
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have e : 1 / (K / c * (Real.sqrt K / Real.sqrt c)) = c * Real.sqrt c * (1 / (K * Real.sqrt K)) := by
    rw [div_mul_div_comm, one_div_div, mul_one_div]
  rw [e]
  calc c * Real.sqrt c * (1 / (K * Real.sqrt K))
      ≤ c * Real.sqrt c * (2 * (1 / Real.sqrt (K - 1) - 1 / Real.sqrt K)) :=
        mul_le_mul_of_nonneg_left ht (mul_pos hc hsc).le
    _ = 2 * c * Real.sqrt c * (1 / Real.sqrt (K - 1) - 1 / Real.sqrt K) := by ring

lemma wt_tail (R : ℝ) (hR : 1 ≤ R) (N : ℕ) (hN : 2 * R ≤ N) (j : ℕ) :
    wt R (N + 2 + j) ≤ 2 * (2 * R) * Real.sqrt (2 * R) *
      (1 / Real.sqrt ((N : ℝ) + (j : ℝ)) - 1 / Real.sqrt ((N : ℝ) + ((j + 1 : ℕ) : ℝ))) := by
  have hc : 0 < 2 * R := by linarith
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have e1 : ((N + 2 + j : ℕ) : ℝ) - 1 = (N : ℝ) + ((j + 1 : ℕ) : ℝ) := by push_cast; ring
  have e2 : (N : ℝ) + (j : ℝ) = (N : ℝ) + ((j + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
  have h := max_div_rpow_le_two_mul_inv_sqrt_sub (2 * R) ((N : ℝ) + ((j + 1 : ℕ) : ℝ)) hc (by push_cast; linarith)
    (by push_cast; linarith)
  unfold wt
  rw [e1, e2]
  exact h

lemma sum_wt_le (R : ℝ) (hR : 1 ≤ R) (T : Finset ℕ) : ∑ m ∈ T, wt R m ≤ 9 * R := by
  obtain ⟨N, hN, hN'⟩ : ∃ N : ℕ, 2 * R ≤ (N : ℝ) ∧ (N : ℝ) < 2 * R + 1 :=
    ⟨⌈2 * R⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by linarith)⟩
  obtain ⟨J, hsub⟩ : ∃ J : ℕ, T ⊆ Finset.range (N + 2 + J) := by
    refine ⟨T.sup id + 1, fun m hm => ?_⟩
    have hm' : m ≤ T.sup id := Finset.le_sup (f := id) hm
    rw [Finset.mem_range]
    omega
  have h1 : ∑ m ∈ T, wt R m ≤ ∑ m ∈ Finset.range (N + 2 + J), wt R m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => wt_nonneg R m)
  rw [Finset.sum_range_add] at h1
  have h2 : ∑ m ∈ Finset.range (N + 2), wt R m ≤ (N : ℝ) + 2 := by
    calc ∑ m ∈ Finset.range (N + 2), wt R m ≤ ∑ m ∈ Finset.range (N + 2), (1 : ℝ) :=
          Finset.sum_le_sum (fun m _ => wt_le_one R m)
      _ = (N : ℝ) + 2 := by simp
  have hc : 0 < 2 * R := by linarith
  have hsc : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr hc
  have hC : 0 ≤ 2 * (2 * R) * Real.sqrt (2 * R) := (mul_pos (mul_pos two_pos hc) hsc).le
  have h3 : ∑ j ∈ Finset.range J, wt R (N + 2 + j) ≤ 4 * R := by
    calc ∑ j ∈ Finset.range J, wt R (N + 2 + j)
        ≤ ∑ j ∈ Finset.range J, 2 * (2 * R) * Real.sqrt (2 * R) *
            (1 / Real.sqrt ((N : ℝ) + (j : ℝ)) - 1 / Real.sqrt ((N : ℝ) + ((j + 1 : ℕ) : ℝ))) :=
          Finset.sum_le_sum (fun j _ => wt_tail R hR N hN j)
      _ = 2 * (2 * R) * Real.sqrt (2 * R) *
            (1 / Real.sqrt ((N : ℝ) + ((0 : ℕ) : ℝ)) - 1 / Real.sqrt ((N : ℝ) + ((J : ℕ) : ℝ))) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_range_sub' (fun j : ℕ => 1 / Real.sqrt ((N : ℝ) + (j : ℝ))) J
      _ ≤ 2 * (2 * R) * Real.sqrt (2 * R) * (1 / Real.sqrt (2 * R)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          have e0 : (N : ℝ) + ((0 : ℕ) : ℝ) = N := by simp
          rw [e0]
          have ha := one_div_le_one_div_of_le hsc (Real.sqrt_le_sqrt hN)
          have hb : 0 ≤ 1 / Real.sqrt ((N : ℝ) + ((J : ℕ) : ℝ)) := by positivity
          linarith
      _ = 4 * R := by
          rw [mul_one_div, mul_div_assoc, div_self hsc.ne', mul_one]; ring
  linarith

private theorem sum_wt_natAbs_le_nine_mul_of_injOn (R : ℝ) (hR : 1 ≤ R) (s : Finset ℤ)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, x.natAbs = y.natAbs → x = y) :
    ∑ a ∈ s, wt R a.natAbs ≤ 9 * R := by
  calc ∑ a ∈ s, wt R a.natAbs = ∑ m ∈ s.image Int.natAbs, wt R m :=
        (Finset.sum_image hinj).symm
    _ ≤ 9 * R := sum_wt_le R hR _

lemma sum_wt_int_le (R : ℝ) (hR : 1 ≤ R) (S : Finset ℤ) : ∑ a ∈ S, wt R a.natAbs ≤ 18 * R := by
  have h1 := sum_wt_natAbs_le_nine_mul_of_injOn R hR (S.filter (fun a : ℤ => 0 ≤ a)) (by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := (Finset.mem_filter.mp hx).2
    have hy0 : 0 ≤ y := (Finset.mem_filter.mp hy).2
    have ex := Int.natAbs_eq x
    have ey := Int.natAbs_eq y
    rw [hxy] at ex
    omega)
  have h2 := sum_wt_natAbs_le_nine_mul_of_injOn R hR (S.filter (fun a : ℤ => ¬ 0 ≤ a)) (by
    intro x hx y hy hxy
    have hx0 : ¬ 0 ≤ x := (Finset.mem_filter.mp hx).2
    have hy0 : ¬ 0 ≤ y := (Finset.mem_filter.mp hy).2
    have ex := Int.natAbs_eq x
    have ey := Int.natAbs_eq y
    rw [hxy] at ex
    omega)
  calc ∑ a ∈ S, wt R a.natAbs
      = ∑ a ∈ S.filter (fun a : ℤ => 0 ≤ a), wt R a.natAbs +
          ∑ a ∈ S.filter (fun a : ℤ => ¬ 0 ≤ a), wt R a.natAbs :=
        (Finset.sum_filter_add_sum_filter_not S _ _).symm
    _ ≤ 9 * R + 9 * R := add_le_add h1 h2
    _ = 18 * R := by ring

private theorem rpow_neg_three_halves_anti_of_one_le {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    t ^ (-(3 / 2 : ℝ)) ≤ s ^ (-(3 / 2 : ℝ)) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  rw [rpow_neg_three_halves hs0, rpow_neg_three_halves ht0]
  apply one_div_le_one_div_of_le (mul_pos hs0 (Real.sqrt_pos.mpr hs0))
  exact mul_le_mul hst (Real.sqrt_le_sqrt hst) (Real.sqrt_nonneg _) ht0.le

private theorem natAbs_floor_sub_one_le_abs (y : ℝ) : ((⌊y⌋.natAbs : ℕ) : ℝ) - 1 ≤ |y| := by
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  rcases Int.natAbs_eq ⌊y⌋ with h | h
  · have e : ((⌊y⌋ : ℤ) : ℝ) = (((⌊y⌋.natAbs : ℕ) : ℤ) : ℝ) := congrArg (fun n : ℤ => (n : ℝ)) h
    rw [Int.cast_natCast] at e
    linarith [le_abs_self y]
  · have e' : ((⌊y⌋ : ℤ) : ℝ) = -((⌊y⌋.natAbs : ℕ) : ℝ) := by exact_mod_cast h
    linarith [neg_abs_le y]

lemma floor_bound (R : ℝ) (hR : 1 ≤ R) (x : ℝ) :
    (max 1 (|x| / R)) ^ (-(3 / 2 : ℝ)) ≤ wt R (⌊2 * x⌋).natAbs := by
  have hR0 : 0 < R := by linarith
  have key : (((⌊2 * x⌋).natAbs : ℕ) : ℝ) - 1 ≤ 2 * |x| := by
    have h := natAbs_floor_sub_one_le_abs (2 * x)
    rwa [abs_mul, abs_two] at h
  unfold wt
  apply rpow_neg_three_halves_anti_of_one_le (le_max_left _ _)
  apply max_le_max le_rfl
  rw [div_le_div_iff₀ (by linarith) hR0]
  nlinarith

private theorem rpow_neg_three_le_mul_rpow_neg_three_halves {A B C : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hAC : A ≤ C) (hBC : B ≤ C) :
    C ^ (-(3 : ℝ)) ≤ A ^ (-(3 / 2 : ℝ)) * B ^ (-(3 / 2 : ℝ)) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hC0 : 0 < C := by linarith
  rw [← Real.mul_rpow hA0.le hB0.le]
  have e : C ^ (-(3 : ℝ)) = (C * C) ^ (-(3 / 2 : ℝ)) := by
    rw [Real.mul_rpow hC0.le hC0.le, ← Real.rpow_add hC0]
    norm_num
  rw [e]
  exact rpow_neg_three_halves_anti_of_one_le (by nlinarith) (mul_le_mul hAC hBC hB0.le hC0.le)

lemma cplx_bound (R : ℝ) (hR : 0 < R) (z : ℂ) :
    (max 1 (‖z‖ / R)) ^ (-(3 : ℝ)) ≤
      (max 1 (|z.re| / R)) ^ (-(3 / 2 : ℝ)) * (max 1 (|z.im| / R)) ^ (-(3 / 2 : ℝ)) := by
  have h1 : |z.re| / R ≤ ‖z‖ / R := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (inv_nonneg.mpr hR.le)
  have h2 : |z.im| / R ≤ ‖z‖ / R := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (inv_nonneg.mpr hR.le)
  exact rpow_neg_three_le_mul_rpow_neg_three_halves (le_max_left _ _) (le_max_left _ _) (max_le_max le_rfl h1)
    (max_le_max le_rfl h2)

lemma norm_lt_one_of_cell (z w : ℂ) (h1 : ⌊2 * z.re⌋ = ⌊2 * w.re⌋) (h2 : ⌊2 * z.im⌋ = ⌊2 * w.im⌋) :
    ‖z - w‖ < 1 := by
  have a1 := Int.floor_le (2 * z.re)
  have a2 := Int.lt_floor_add_one (2 * z.re)
  have b1 := Int.floor_le (2 * w.re)
  have b2 := Int.lt_floor_add_one (2 * w.re)
  have c1 := Int.floor_le (2 * z.im)
  have c2 := Int.lt_floor_add_one (2 * z.im)
  have d1 := Int.floor_le (2 * w.im)
  have d2 := Int.lt_floor_add_one (2 * w.im)
  rw [h1] at a1 a2
  rw [h2] at c1 c2
  have kre : 0 < (1 - (2 * z.re - 2 * w.re)) * (1 + (2 * z.re - 2 * w.re)) :=
    mul_pos (by linarith) (by linarith)
  have im_algebraMap_add_mul : 0 < (1 - (2 * z.im - 2 * w.im)) * (1 + (2 * z.im - 2 * w.im)) :=
    mul_pos (by linarith) (by linarith)
  have hn : ‖z - w‖ ^ 2 < 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith
  nlinarith [norm_nonneg (z - w)]

theorem latSum (ι : Type) [Fintype ι] (P : Finset (ι → ℂ)) (R : ℝ) (hR : 1 ≤ R)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 1 ≤ ∏ i, ‖p i - q i‖) :
    ∑ p ∈ P, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ)) ≤ (64 * R) ^ (2 * Fintype.card ι) := by
  classical
  have hR0 : 0 < R := by linarith
  let cell : (ι → ℂ) → (ι → ℤ × ℤ) := fun p i => (⌊2 * (p i).re⌋, ⌊2 * (p i).im⌋)
  have hf0 : ∀ x : ℤ × ℤ, 0 ≤ wt R x.1.natAbs * wt R x.2.natAbs :=
    fun x => mul_nonneg (wt_nonneg _ _) (wt_nonneg _ _)
  have hpt : ∀ p : ι → ℂ, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ)) ≤
      ∏ i, wt R (cell p i).1.natAbs * wt R (cell p i).2.natAbs := by
    intro p
    apply Finset.prod_le_prod₀
    · intro i _
      exact Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    · intro i _
      calc (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ))
          ≤ (max 1 (|(p i).re| / R)) ^ (-(3 / 2 : ℝ)) * (max 1 (|(p i).im| / R)) ^ (-(3 / 2 : ℝ)) :=
            cplx_bound R hR0 (p i)
        _ ≤ wt R (cell p i).1.natAbs * wt R (cell p i).2.natAbs :=
            mul_le_mul (floor_bound R hR _) (floor_bound R hR _)
              (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (wt_nonneg _ _)
  have hinj : ∀ p ∈ P, ∀ q ∈ P, cell p = cell q → p = q := by
    intro p hp q hq hpq
    by_contra hne
    have hs := hsep p hp q hq hne
    have hlt : ∀ i, ‖p i - q i‖ < 1 := by
      intro i
      have e := congrFun hpq i
      exact norm_lt_one_of_cell (p i) (q i) (congrArg Prod.fst e) (congrArg Prod.snd e)
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact hne (funext fun i => hι.elim i)
    · obtain ⟨i0⟩ := hι
      have hE : ∏ i ∈ Finset.univ.erase i0, ‖p i - q i‖ ≤ 1 :=
        Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => (hlt i).le)
      have hE0 : 0 ≤ ∏ i ∈ Finset.univ.erase i0, ‖p i - q i‖ :=
        Finset.prod_nonneg (fun i _ => norm_nonneg _)
      have hsplit : ‖p i0 - q i0‖ * ∏ i ∈ Finset.univ.erase i0, ‖p i - q i‖ = ∏ i, ‖p i - q i‖ :=
        Finset.mul_prod_erase Finset.univ (fun i => ‖p i - q i‖) (Finset.mem_univ i0)
      nlinarith [hlt i0, norm_nonneg (p i0 - q i0)]
  obtain ⟨S, hS⟩ : ∃ S : Finset (ℤ × ℤ), ∀ c ∈ P.image cell, ∀ i, c i ∈ S :=
    ⟨(P.image cell).biUnion (fun c => Finset.univ.image c), fun c hc i =>
      Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_image_of_mem c (Finset.mem_univ i)⟩⟩
  have hSf : ∑ x ∈ S, wt R x.1.natAbs * wt R x.2.natAbs ≤ (18 * R) * (18 * R) := by
    calc ∑ x ∈ S, wt R x.1.natAbs * wt R x.2.natAbs
        ≤ ∑ x ∈ (S.image Prod.fst) ×ˢ (S.image Prod.snd), wt R x.1.natAbs * wt R x.2.natAbs := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
          · intro x _ _
            exact hf0 x
      _ = (∑ a ∈ S.image Prod.fst, wt R a.natAbs) * (∑ b ∈ S.image Prod.snd, wt R b.natAbs) := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ (18 * R) * (18 * R) :=
          mul_le_mul (sum_wt_int_le R hR _) (sum_wt_int_le R hR _)
            (Finset.sum_nonneg (fun b _ => wt_nonneg _ _)) (by linarith)
  calc ∑ p ∈ P, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ))
      ≤ ∑ p ∈ P, ∏ i, wt R (cell p i).1.natAbs * wt R (cell p i).2.natAbs :=
        Finset.sum_le_sum (fun p _ => hpt p)
    _ = ∑ c ∈ P.image cell, ∏ i, wt R (c i).1.natAbs * wt R (c i).2.natAbs := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ c ∈ Fintype.piFinset (fun _ : ι => S), ∏ i, wt R (c i).1.natAbs * wt R (c i).2.natAbs := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro c hc
          exact Fintype.mem_piFinset.mpr (fun i => hS c hc i)
        · intro c _ _
          exact Finset.prod_nonneg (fun i _ => hf0 _)
    _ = ∏ _i : ι, ∑ x ∈ S, wt R x.1.natAbs * wt R x.2.natAbs :=
        (Finset.prod_univ_sum (fun _ : ι => S)
          (fun _ x => wt R x.1.natAbs * wt R x.2.natAbs)).symm
    _ ≤ ∏ _i : ι, ((18 * R) * (18 * R)) := by
        apply Finset.prod_le_prod₀
        · intro i _
          exact Finset.sum_nonneg (fun x _ => hf0 x)
        · intro i _
          exact hSf
    _ = (18 * R) ^ (2 * Fintype.card ι) := by
        rw [Finset.prod_const, Finset.card_univ, pow_mul, sq]
    _ ≤ (64 * R) ^ (2 * Fintype.card ι) := pow_le_pow_left₀ (by linarith) (by linarith) _

end Formalism.MainNotions.WeightedLatticeSum

end
end

noncomputable section

namespace Formalism.MainNotions.LatticeSumConvergence

theorem LatSum_holds : Formalism.MainNotions.KTwoMinorIntegrality.LatSum :=
  fun ι _ P R hR hsep => Formalism.MainNotions.WeightedLatticeSum.latSum ι P R hR hsep

end Formalism.MainNotions.LatticeSumConvergence

end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.KTwoCosetCount Formalism.MainNotions.MinorIntegralityTorus

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

theorem cosets_sum_gen {D : D7} (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum)
    [Nonempty D.what₂.Tau] (hrd : 0 < D.host.rdE) {H1 : ℝ}
    (hH : 0 < H1) {j : ℕ} (hj : j ≤ D.R.rS) (T : Finset (ℕ → D.host.E))
    (hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1) :
    ∑ δ ∈ T, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
      2 ^ j * ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := by
  classical
  set K : ℝ := ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) with hK
  have hmaps : ∀ δ ∈ T, KappaEndpoints.k2ends D j δ ∈ (Finset.Icc 1 j).powerset := by
    intro δ _
    rw [Finset.mem_powerset]
    unfold KappaEndpoints.k2ends
    exact Finset.filter_subset _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hS : ∀ S ∈ (Finset.Icc 1 j).powerset,
      ∑ δ ∈ T with KappaEndpoints.k2ends D j δ = S, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ K := by
    intro S hSm
    have hSsub := Finset.mem_powerset.1 hSm
    set TS := T.filter (fun δ => KappaEndpoints.k2ends D j δ = S) with hTS
    have step1 : ∑ δ ∈ TS, KappaEndpoints.k2S D H1 j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
        ∑ δ ∈ TS, ∏ l ∈ S, wl (D := D) H1 l (δ l) := by
      apply Finset.sum_le_sum
      intro δ hδ
      have he := (Finset.mem_filter.1 hδ).2
      have := S_rpow_le (D := D) H1 hj δ
      rwa [he] at this
    have hinj : ∀ δ ∈ TS, ∀ δ' ∈ TS, (∀ l ∈ S, δ l = δ' l) → δ = δ' := by
      intro δ hδ δ' hδ' h
      obtain ⟨hδT, he⟩ := Finset.mem_filter.1 hδ
      obtain ⟨hδT', he'⟩ := Finset.mem_filter.1 hδ'
      obtain ⟨-, hz, h0⟩ := hfact δ hδT
      obtain ⟨-, hz', h0'⟩ := hfact δ' hδT'
      funext l
      by_cases hl0 : l = 0
      · rw [hl0, h0, h0']
      by_cases hlj : j < l
      · rw [hz l hlj, hz' l hlj]
      by_cases hlS : l ∈ S
      · exact h l hlS
      have hI : l ∈ Finset.Icc 1 j := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have a1 : δ l = 0 := by
        by_contra hne
        apply hlS
        rw [← he]
        unfold KappaEndpoints.k2ends
        exact Finset.mem_filter.2 ⟨hI, hne⟩
      have a2 : δ' l = 0 := by
        by_contra hne
        apply hlS
        rw [← he']
        unfold KappaEndpoints.k2ends
        exact Finset.mem_filter.2 ⟨hI, hne⟩
      rw [a1, a2]
    have step2 := sum_prod_le S TS (fun l x => wl (D := D) H1 l x) (fun l x => wl_nonneg H1 l x) hinj
    have step3 : ∏ l ∈ S, ∑ x ∈ TS.image (fun δ => δ l), wl (D := D) H1 l x ≤
        ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) := by
      apply Finset.prod_le_prod₀
      · intro l _; exact Finset.sum_nonneg fun x _ => wl_nonneg H1 l x
      · intro l _
        have hint : ∀ x ∈ TS.image (fun δ => δ l), IsIntegral ℤ x := by
          intro x hx
          obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hx
          exact (hfact δ (Finset.mem_filter.1 hδ).1).1 l
        calc ∑ x ∈ TS.image (fun δ => δ l), wl (D := D) H1 l x
            ≤ ∑ x ∈ TS.image (fun δ => δ l), ∏ τ : D.what₂.Tau, (max 1 (‖embS D τ x‖ / Rl (D := D) H1 l)) ^ (-(3 : ℝ)) :=
              Finset.sum_le_sum fun x _ => wl_le hrd hH l x
          _ ≤ _ := sum_one_coord hNT hLS _ hint (one_le_Rl H1 l)
    have step4 : ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤ K := by
      rw [hK, ← Finset.prod_sdiff hSsub]
      have hge : ∀ l, 1 ≤ (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        fun l => one_le_pow₀ (by linarith [one_le_Rl (D := D) H1 l])
      have h1 : 1 ≤ ∏ l ∈ Finset.Icc 1 j \ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
          (fun l _ => hge l)
      have h0 : 0 ≤ ∏ l ∈ S, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) :=
        Finset.prod_nonneg fun l _ => le_trans zero_le_one (hge l)
      nlinarith
    exact step1.trans (step2.trans (step3.trans step4))
  calc _ ≤ ∑ S ∈ (Finset.Icc 1 j).powerset, K := Finset.sum_le_sum hS
    _ = 2 ^ j * K := by
      rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
      simp

theorem kloostermanCosetSum_le {D : D7} (hNT : KTwoMinorIntegrality.NormLB) (hLS : KTwoMinorIntegrality.LatSum) (large₂ : SizeData₂ D)
    {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0) (CH : ℝ)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.rS) (T : Finset (ℕ → D.host.E))
    (hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1) :
    ∑ δ ∈ T, KappaEndpoints.k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤
      Hb large₂.sc.b (ccOf CH Cl) D.R.m D.R.f ^ (ccOf CH Cl * (D.R.rS : ℝ)) := by
  obtain ⟨⟨h0, -, -⟩, -⟩ := hH
  obtain ⟨-, -, hmf, -, -, -, -, -, -, -, hrdL, -, -, -, -, -, -, -, hv, -, -, -, -, -, hCl⟩ := h0
  have hjI := Finset.mem_Icc.1 hj
  have hrd2 : 2 ≤ D.host.rdE := by unfold Formalism.BasicNotions.Host.v at hv; linarith
  have hm2 := D.R.two_le_m
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [D.what₂.card_Tau]; omega)
  have hb2 := KappaEndpoints.two_le_scale_b D large₂
  set H1 : ℝ := large₂.sc.b ^ (CH * (D.R.m : ℝ)) with hH1def
  have hH1 : 0 < H1 := Real.rpow_pos_of_pos (by linarith) _
  have hsum := cosets_sum_gen hNT hLS (by linarith) hH1 hjI.2 T hfact
  set B : ℝ := D.host.rdE ^ (((2 * (D.R.rS * D.R.rS) : ℕ)) : ℝ) * (max 1 (2 * H1)) ^ (2 * D.R.rS) with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) (Nat.cast_nonneg _))
    (one_le_pow₀ (le_max_left _ _))
  have hRl : ∀ l ∈ Finset.Icc 1 j, Rl (D := D) H1 l ≤ B := by
    intro l hl
    have hlr : l ≤ D.R.rS := (Finset.mem_Icc.1 hl).2.trans hjI.2
    have hfe := frameExp_le hlr
    refine max_le hB1 (mul_le_mul ?_ (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _) (by positivity)
      (Real.rpow_nonneg (by linarith) _))
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast (by omega : 2 * frameExp D.R.rS l ≤ 2 * (D.R.rS * D.R.rS)))
  have hprod : ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau) ≤
      ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := by
    calc ∏ l ∈ Finset.Icc 1 j, (64 * Rl (D := D) H1 l) ^ (2 * Fintype.card D.what₂.Tau)
        ≤ ∏ l ∈ Finset.Icc 1 j, (64 * B) ^ (2 * Fintype.card D.what₂.Tau) :=
          Finset.prod_le_prod₀ (fun l _ => pow_nonneg (by linarith [one_le_Rl (D := D) H1 l]) _)
            (fun l hl => pow_le_pow_left₀ (by linarith [one_le_Rl (D := D) H1 l]) (by linarith [hRl l hl]) _)
      _ = ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := by rw [Finset.prod_const]; simp
  have hfin := final_arith (L := large₂.sc.L) (CH := CH) (rd := D.host.rdE) (r := D.R.rS) (m := D.R.m) (f := D.R.f)
    (n := Fintype.card D.what₂.Tau) (j := j) (KappaEndpoints.one_lt_scale_L D large₂) hCl (by linarith) hrdL (by omega)
    (by have := KappaEndpoints.two_rank_add_two_eq_m D; omega) hjI.2 (by rw [D.what₂.card_Tau]) hf1
  unfold Hb
  calc _ ≤ _ := hsum
    _ ≤ 2 ^ j * ((64 * B) ^ (2 * Fintype.card D.what₂.Tau)) ^ j := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ _ := hfin

end Gen

section Conc

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u : D.what₂.Word}

theorem minorInt_conc (t : GTu Y u) (l : ℕ) (hl : l ≤ D.R.rS) :
    IsIntegral ℤ (Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l) := by
  have hRow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hOK : FrameOK D t.lam (frq X t.rep) := t.rep.2.2.2.2.2.2
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT t.lam := hRow.2.1.2.1
  have he : ∀ a, (lf D (X.Fu u)).fl.e a ∈ t.lam := e_mem_lam D t.lam (lf D (X.Fu u)) hRow.2.2
  have he' : ∀ a, (frq X t.rep).fl.e a ∈ t.lam := e_mem_lam D t.lam (frq X t.rep) hOK.2
  have hl' : l ≤ D.R.rS + 1 := by omega
  unfold Dl leadMinorE
  rw [dite_eq_left hl']
  apply det_isIntegral
  intro i j
  have hi : Fin.castLE hl' i = Fin.castSucc ⟨i, by omega⟩ := Fin.ext rfl
  have hj : Fin.castLE hl' j = Fin.castSucc ⟨j, by omega⟩ := Fin.ext rfl
  simp only [Matrix.submatrix_apply, Zhat, brS]
  rw [hi, hj]
  simp only [FlagG.fvec, Fin.snoc_castSucc]
  exact pair_int D hU (he' _) (he _)

theorem labFacts_conc (t : GTu Y u) :
    (∀ l, IsIntegral ℤ (labT t l)) ∧ (∀ l, jT t < l → labT t l = 0) ∧ labT t 0 = 1 := by
  refine ⟨fun l => ?_, fun l hl => ?_, ?_⟩
  · unfold labT
    split_ifs with hl
    · exact minorInt_conc t l (le_trans hl (Nat.sub_le _ _))
    · exact isIntegral_zero
  · unfold labT
    rw [if_neg (not_le.mpr (by unfold jT at hl; exact hl))]
  · unfold labT
    rw [if_pos (Nat.zero_le _)]
    unfold Dl leadMinorE
    first
      | exact Matrix.det_isEmpty
      | simp
      | done

theorem cosetsC_holds : CosetsC := by
  intro Cg cb Cw cT CT C0 CH hCH
  refine ⟨21 + 4 * |CH|, by positivity, 0, 1, fun C' Cl _ hCl1 D large₂ X Y u hH _ j hj T hTm => ?_⟩
  have hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1 := by
    intro δ hδ
    obtain ⟨t, -, rfl, rfl⟩ := hTm δ hδ
    exact labFacts_conc t
  have h := kloostermanCosetSum_le NormLB_holds Formalism.MainNotions.LatticeSumConvergence.LatSum_holds large₂ hH CH j hj T hfact
  unfold H1C
  refine h.trans ?_
  have hb : 1 ≤ large₂.sc.b := by linarith [KappaEndpoints.two_le_scale_b D large₂]
  have hCl0 : 0 < Cl := by linarith
  have hc0 : 0 ≤ ccOf CH Cl := by unfold ccOf; positivity
  have hcle : ccOf CH Cl ≤ 21 + 4 * |CH| := by
    unfold ccOf
    have : 4 / Cl ≤ 4 := by rw [div_le_iff₀ hCl0]; linarith
    linarith
  unfold Hb
  rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hb
  have hx : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS := by positivity
  have e1 : ccOf CH Cl * (D.R.m : ℝ) ^ 2 * D.R.f * (ccOf CH Cl * D.R.rS) =
      ccOf CH Cl * ccOf CH Cl * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  have e2 : (21 + 4 * |CH|) * (D.R.m : ℝ) ^ 2 * D.R.f * ((21 + 4 * |CH|) * D.R.rS) =
      (21 + 4 * |CH|) * (21 + 4 * |CH|) * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hcle hcle hc0 (by positivity)) hx

end Conc

end Formalism.L2.SG.KappaOffDiagonal
