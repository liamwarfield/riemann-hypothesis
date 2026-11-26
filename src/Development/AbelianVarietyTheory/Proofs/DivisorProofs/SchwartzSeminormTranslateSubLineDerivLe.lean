module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe
open scoped SchwartzMap ContDiff

namespace GlobalTheory.SchwartzTranslate

private theorem fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (a : V) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : V → F), ContDiff ℝ ∞ g →
      ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m := by
  induction n with
  | zero =>
    intro F _ _ g hg x m
    simp only [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro F _ _ g hg x m
    have hg1 : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (fderiv ℝ g)) :=
      hg1.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
    have hsym : (fun y => fderiv ℝ (fun z => fderiv ℝ g z a) y)
        = fun y => fderiv ℝ (fderiv ℝ g) y a := by
      funext y
      ext w
      rw [fderiv_clm_apply ((hg1.differentiable (by simp)) y) (differentiableAt_const _)]
      simp
      have h2le : minSmoothness ℝ 2 ≤ ∞ := by simp
      exact (ContDiffAt.isSymmSndFDerivAt (hg.contDiffAt (x := y)) h2le) w a
    simp_rw [iteratedFDeriv_succ_apply_right]
    rw [fderiv_clm_apply ((hdiff x).continuousMultilinear_apply_const _) (differentiableAt_const _)]
    simp
    rw [ih (fderiv ℝ g) hg1 x (Fin.init m), hsym]

theorem fderiv_iteratedFDeriv_apply_comm {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) :
    ∀ (g : V → F), ContDiff ℝ ∞ g → ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m :=
  fun g hg x m => fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv a n g hg x m

theorem hasDerivAt_iteratedFDeriv_line {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) (g : V → F) (hg : ContDiff ℝ ∞ g)
    (x : V) (s : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n g (x + s • a))
      (iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a)) s := by
  have hline : HasDerivAt (fun s : ℝ => x + s • a) a s := by
    simpa using ((hasDerivAt_id s).smul_const a).const_add x
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    hg.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
  have key : fderiv ℝ (iteratedFDeriv ℝ n g) (x + s • a) a
      = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a) := by
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply (hd _)]
    exact fderiv_iteratedFDeriv_apply_comm a n g hg _ m
  rw [← key]
  exact (hd _).hasFDerivAt.comp_hasDerivAt s hline

theorem taylor_two {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (φ φ' φ'' : ℝ → G)
    (h1 : ∀ s, HasDerivAt φ (φ' s) s) (h2 : ∀ s, HasDerivAt φ' (φ'' s) s) (M : ℝ)
    (hM : ∀ s, |s| ≤ 1 → ‖φ'' s‖ ≤ M) (t : ℝ) (ht : |t| ≤ 1) :
    ‖φ t - φ 0 - t • φ' 0‖ ≤ M * t ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hd1 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ' s - φ' 0‖ ≤ M * |s| := by
    intro s hs
    have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ') (f' := φ'')
      (s := Set.Icc (-1) 1) (fun x _ => (h2 x).hasDerivWithinAt)
      (fun x hx => hM x (abs_le.mpr hx)) (convex_Icc _ _) h0 hs
    simpa [Real.norm_eq_abs] using this
  have hψ : ∀ s, HasDerivAt (fun s => φ s - s • φ' 0) (φ' s - φ' 0) s := by
    intro s
    convert (h1 s).sub ((hasDerivAt_id s).smul_const (φ' 0)) using 1 <;> first | rfl | simp
  have ht' : t ∈ Set.Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
  have h0' : (0 : ℝ) ∈ Set.Icc (-|t|) |t| := ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩
  have hbound : ∀ x ∈ Set.Icc (-|t|) |t|, ‖φ' x - φ' 0‖ ≤ M * |t| := by
    intro x hx
    have hx1 : |x| ≤ |t| := abs_le.mpr hx
    exact (hd1 x (abs_le.mp (hx1.trans ht))).trans (mul_le_mul_of_nonneg_left hx1 hM0)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => φ s - s • φ' 0) (f' := fun s => φ' s - φ' 0)
    (fun x _ => (hψ x).hasDerivWithinAt) hbound (convex_Icc _ _) h0' ht'
  have e : φ t - φ 0 - t • φ' 0 = (φ t - t • φ' 0) - (φ 0 - (0 : ℝ) • φ' 0) := by
    rw [zero_smul, sub_zero, sub_right_comm]
  rw [e]
  calc _ ≤ M * |t| * ‖t - 0‖ := key
    _ = M * t ^ 2 := by rw [sub_zero, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self, sq]

theorem seminorm_translate_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V)
    (f : 𝓢(V, ℂ)) (k n : ℕ) : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f
        - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f) ≤ C * t ^ 2 := by
  set f1 := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hf1def
  set f2 := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f1 with hf2def
  have hf1 : (⇑f1 : V → ℂ) = fun y => fderiv ℝ f y a := rfl
  have hf2 : (⇑f2 : V → ℂ) = fun y => fderiv ℝ f1 y a := rfl
  have hsm : ∀ g : 𝓢(V, ℂ), ContDiff ℝ ∞ ⇑g := fun g => g.smooth ⊤
  have hsmn : ∀ g : 𝓢(V, ℂ), ContDiff ℝ n ⇑g := fun g => (g.smooth ⊤).of_le (mod_cast le_top)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f2 :=
    ⟨_, rfl⟩
  have hL : ∀ y, (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ n f2 y‖ ≤ 2 ^ k * S := fun y => by
    rw [hS]; exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) le_rfl le_rfl f2 y
  have hS0 : 0 ≤ 2 ^ k * S := le_trans (by positivity) (hL 0)
  refine ⟨(1 + ‖a‖) ^ k * (2 ^ k * S), fun t ht => ?_⟩
  have hC0 : 0 ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := mul_nonneg (by positivity) hS0
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg hC0 (sq_nonneg t)) fun x => ?_
  have hcoe : (⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1) : V → ℂ)
      = (fun y => f (y + t • a)) - ⇑f - (t : ℂ) • ⇑f1 := by
    funext y; simp [sub_neg_eq_add]
  have hshift : ContDiff ℝ n (fun y => f (y + t • a)) :=
    (hsmn f).comp (contDiff_id.add contDiff_const)
  have hD : iteratedFDeriv ℝ n ((fun y => f (y + t • a)) - ⇑f - (t : ℂ) • ⇑f1) x
      = iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - (t : ℂ) • iteratedFDeriv ℝ n f1 x := by
    rw [iteratedFDeriv_sub_apply, iteratedFDeriv_sub_apply, iteratedFDeriv_const_smul_apply,
      iteratedFDeriv_comp_add_right]
    all_goals first
      | exact hshift.contDiffAt
      | exact (hsmn f).contDiffAt
      | exact (hsmn f1).contDiffAt
      | exact (hshift.sub (hsmn f)).contDiffAt
      | exact ((hsmn f1).const_smul (t : ℂ)).contDiffAt
  have hre : (t : ℂ) • iteratedFDeriv ℝ n f1 x = t • iteratedFDeriv ℝ n f1 x := by
    ext m; simp [Complex.real_smul]
  rw [hcoe, hD, hre]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ‖x‖ ^ k := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hdf : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c • iteratedFDeriv ℝ n f (x + s • a))
      (c • iteratedFDeriv ℝ n f1 (x + s • a)) s := by
    intro s
    have := hasDerivAt_iteratedFDeriv_line a n f (hsm f) x s
    rw [← hf1] at this
    exact this.const_smul c
  have hdf1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c • iteratedFDeriv ℝ n f1 (x + s • a))
      (c • iteratedFDeriv ℝ n f2 (x + s • a)) s := by
    intro s
    have := hasDerivAt_iteratedFDeriv_line a n f1 (hsm f1) x s
    rw [← hf2] at this
    exact this.const_smul c
  have hbd : ∀ s : ℝ, |s| ≤ 1 →
      ‖c • iteratedFDeriv ℝ n f2 (x + s • a)‖ ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := by
    intro s hs
    have h2 : ‖s • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) hs
    have hxy : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖x + s • a‖) := by
      have h3 : ‖x‖ ≤ ‖x + s • a‖ + ‖s • a‖ := by
        have := norm_sub_le (x + s • a) (s • a)
        rwa [add_sub_cancel_right] at this
      nlinarith [norm_nonneg (x + s • a), norm_nonneg a]
    have hpow : c ≤ (1 + ‖a‖) ^ k * (1 + ‖x + s • a‖) ^ k := by
      rw [hc, ← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hxy k
    rw [norm_smul, Real.norm_of_nonneg hc0]
    calc c * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖
        ≤ ((1 + ‖a‖) ^ k * (1 + ‖x + s • a‖) ^ k) * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = (1 + ‖a‖) ^ k * ((1 + ‖x + s • a‖) ^ k * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖) := by ring
      _ ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := mul_le_mul_of_nonneg_left (hL _) (by positivity)
  have hT := taylor_two (fun s : ℝ => c • iteratedFDeriv ℝ n f (x + s • a))
    (fun s : ℝ => c • iteratedFDeriv ℝ n f1 (x + s • a))
    (fun s : ℝ => c • iteratedFDeriv ℝ n f2 (x + s • a)) hdf hdf1 _ hbd t ht
  simp only [zero_smul, add_zero] at hT
  have e : c • iteratedFDeriv ℝ n f (x + t • a) - c • iteratedFDeriv ℝ n f x
      - t • c • iteratedFDeriv ℝ n f1 x
      = c • (iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - t • iteratedFDeriv ℝ n f1 x) := by
    rw [smul_sub, smul_sub, smul_comm t c]
  rw [e, norm_smul, Real.norm_of_nonneg hc0] at hT
  exact hT

end GlobalTheory.SchwartzTranslate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLeStatement
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_seminorm_translate_sub_lineDeriv_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f) ≤ C * t ^ 2 := by
  first | exact @GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le | exact GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le | (intros; apply GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOne
open MeasureTheory

namespace GlobalTheory.UnitaryChart

open Topology Filter

theorem hasStrictFDerivAt_ofFn_prod {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedRing E] [NormedAlgebra ℝ E] :
    ∀ (N : ℕ) (g : Fin N → F → E) (g' : Fin N → F →L[ℝ] E),
      (∀ i, g i 0 = 1 ∧ HasStrictFDerivAt (g i) (g' i) 0) →
      (List.ofFn fun i => g i 0).prod = 1 ∧
        HasStrictFDerivAt (fun t => (List.ofFn fun i => g i t).prod) (∑ i, g' i) 0 := by
  intro N
  induction N with
  | zero =>
    intro g g' _
    simpa using hasStrictFDerivAt_const (𝕜 := ℝ) (1 : E) (0 : F)
  | succ N ih =>
    intro g g' h
    obtain ⟨h1, h2⟩ := ih (fun i => g i.succ) (fun i => g' i.succ) (fun i => h i.succ)
    simp only [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    refine ⟨by rw [h1, (h 0).1, mul_one], ?_⟩
    have h3 := (h 0).2.mul' h2
    refine (h3.congr_fderiv ?_)
    ext y
    simp [h1, (h 0).1, add_comm]

theorem unitary_list_prod {E : Type} [Ring E] (σ : E → E) (hm : ∀ a b, σ (a * b) = σ b * σ a)
    (h1 : σ 1 = 1) (l : List E) (hl : ∀ u ∈ l, σ u * u = 1 ∧ u * σ u = 1) :
    σ l.prod * l.prod = 1 ∧ l.prod * σ l.prod = 1 := by
  induction l with
  | nil => simp [h1]
  | cons a l ih =>
    obtain ⟨i1, i2⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
    obtain ⟨a1, a2⟩ := hl a List.mem_cons_self
    rw [List.prod_cons, hm]
    constructor
    · calc σ l.prod * σ a * (a * l.prod) = σ l.prod * (σ a * a) * l.prod := by noncomm_ring
        _ = 1 := by rw [a1, mul_one, i1]
    · calc a * l.prod * (σ l.prod * σ a) = a * (l.prod * σ l.prod) * σ a := by noncomm_ring
        _ = 1 := by rw [i2, mul_one, a2]

theorem eq_of_skew_eq {E : Type} [NormedRing E] [NormedAlgebra ℝ E] {u v u' v' : E}
    (hu : u' * u = 1) (hv : v * v' = 1)
    (h : u - u' = v - v') (nu : ‖1 - u'‖ ≤ 1 / 2) (nv : ‖1 - v'‖ ≤ 1 / 2) : u = v := by
  set w := u - v with hw
  have e1 : w = u' - v' := by
    rw [hw]; exact sub_eq_sub_iff_sub_eq_sub.mp h
  have e2 : u' * w * v' = v' - u' := by
    calc u' * w * v' = (u' * u) * v' - u' * (v * v') := by rw [hw]; noncomm_ring
      _ = v' - u' := by rw [hu, hv, one_mul, mul_one]
  have e3 : (2 : ℝ) • w = (1 - u') * w + w * (1 - v') - (1 - u') * w * (1 - v') := by
    have : (1 - u') * w + w * (1 - v') - (1 - u') * w * (1 - v') = w - u' * w * v' := by
      noncomm_ring
    rw [this, e2, two_smul]
    nth_rewrite 2 [e1]
    abel
  have n0 := norm_nonneg w
  have n1 : ‖(1 - u') * w‖ ≤ 1 / 2 * ‖w‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right nu n0)
  have n2 : ‖w * (1 - v')‖ ≤ ‖w‖ * (1 / 2) :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left nv n0)
  have n3 : ‖(1 - u') * w * (1 - v')‖ ≤ 1 / 2 * ‖w‖ * (1 / 2) :=
    (norm_mul_le _ _).trans (mul_le_mul n1 nv (norm_nonneg _) (by positivity))
  have n4 : 2 * ‖w‖ ≤ ‖(1 - u') * w‖ + ‖w * (1 - v')‖ + ‖(1 - u') * w * (1 - v')‖ := by
    have : ‖(2 : ℝ) • w‖ = 2 * ‖w‖ := by rw [norm_smul]; simp
    rw [← this, e3]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have : ‖w‖ = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem exists_skew_coord {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
    (σ : E →ₗ[ℝ] E) {N : ℕ} (e : Fin N → E) (hσ : ∀ a, σ (σ a) = a)
    (hli : LinearIndependent ℝ e) (he : ∀ i, σ (e i) = -e i)
    (hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) :
    ∃ P : E →L[ℝ] (Fin N → ℝ), (∀ t : Fin N → ℝ, P (∑ i, t i • e i) = t) ∧
      (∀ m, σ m = m → P m = 0) ∧ ∀ u v, P u = P v → u - σ u = v - σ v := by
  let T : (Fin N → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ e
  have hT : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.mpr hli.fintypeLinearCombination_injective
  obtain ⟨Q, hQ⟩ := T.exists_leftInverse_of_injective hT
  have hQT : ∀ t, Q (∑ i, t i • e i) = t := fun t => by
    have := LinearMap.congr_fun hQ t
    simpa [T, Fintype.linearCombination_apply] using this
  let π : E →ₗ[ℝ] E := (1 / 2 : ℝ) • (LinearMap.id - σ)
  have hπ : ∀ m, π m = (1 / 2 : ℝ) • (m - σ m) := fun m => rfl
  refine ⟨LinearMap.toContinuousLinearMap (Q ∘ₗ π), fun t => ?_, fun m hm => ?_, fun u v h => ?_⟩
  · have : σ (∑ i, t i • e i) = -∑ i, t i • e i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, he]
    change Q (π _) = t
    rw [hπ, this, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
    norm_num
    simpa using hQT t
  · change Q (π _) = 0
    rw [hπ, hm, sub_self, smul_zero, map_zero]
  · change Q (π u) = Q (π v) at h
    have h2 : Q (π (u - v)) = 0 := by rw [map_sub, map_sub, h, sub_self]
    have h3 : σ (π (u - v)) = -π (u - v) := by
      rw [hπ, map_smul, map_sub, hσ, ← smul_neg, neg_sub]
    obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hsp _ h3)
    rw [← hy, hQT] at h2
    have h4 : π (u - v) = 0 := by rw [← hy, h2]; simp
    rw [hπ, smul_eq_zero] at h4
    rcases h4 with h4 | h4
    · norm_num at h4
    · rw [map_sub] at h4
      exact sub_eq_sub_iff_sub_eq_sub.mp (sub_eq_zero.mp h4)

theorem second_kind_chart : ∀ (E : Type) [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E) (N : ℕ) (e : Fin N → E) (c : Fin N → ℝ → E), (∀ a, σ (σ a) = a) → (∀ a b, σ (a * b) = σ b * σ a) → σ 1 = 1 → LinearIndependent ℝ e → (∀ i, σ (e i) = -e i) → (∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) → (∀ i, c i 0 = 1 ∧ HasStrictDerivAt (c i) (e i) 0 ∧ ∀ t, σ (c i t) * c i t = 1 ∧ c i t * σ (c i t) = 1) → ∃ (s S K : ℝ) (W : Set E), 0 < s ∧ 0 ≤ K ∧ W ∈ nhds (1 : E) ∧ ∀ x ∈ W, σ x * x = 1 → x * σ x = 1 → ∃ f : (Fin N → ℝ) → (Fin N → ℝ), (∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖f t‖ ≤ S ∧ (List.ofFn fun i => c i (f t i)).prod * x = (List.ofFn fun i => c i (t i)).prod) ∧ ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∀ t' ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖t - t'‖ ≤ K * ‖f t - f t'‖ := by
  intro E _ _ _ σ N e c hσ hm h1 hli he hsp hc
  set Θ : (Fin N → ℝ) → E := fun t => (List.ofFn fun i => c i (t i)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact (hc i).2.2 _)
  let T : (Fin N → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (e i)).comp (ContinuousLinearMap.proj i)
  have hT : ∀ t, T t = ∑ i, t i • e i := fun t => by simp [T]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    hasStrictFDerivAt_ofFn_prod N (fun i (t : Fin N → ℝ) => c i (t i)) _ (fun i =>
      ⟨(hc i).1, HasStrictFDerivAt.comp (0 : Fin N → ℝ) (g := c i)
        (hc i).2.1.hasStrictFDerivAt
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i).hasStrictFDerivAt⟩)
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_skew_coord σ e hσ hli he hsp
  have hΨ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hΨ0 : P (Θ 0) = 0 := by rw [h0]; exact hP2 _ h1
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  obtain ⟨U₁, hU₁, hA⟩ := hΨ.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
  obtain ⟨L, U₂, hU₂, hL⟩ := hD.exists_lipschitzOnWith
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := by fun_prop
    exact this.eventually_le_const (by simp [h1])
  have hΘt : Tendsto Θ (𝓝 0) (𝓝 1) := h0 ▸ hD.continuousAt
  let U : Set (Fin N → ℝ) := U₁ ∩ U₂ ∩ {t | ‖1 - σ (Θ t)‖ ≤ 1 / 2} ∩ Metric.closedBall 0 1
  have hUn : U ∈ 𝓝 0 :=
    inter_mem (inter_mem (inter_mem hU₁ hU₂) (hΘt.eventually hnear))
      (Metric.closedBall_mem_nhds _ one_pos)
  have hV : (fun t => P (Θ t)) '' U ∈ 𝓝 (0 : Fin N → ℝ) := by
    have := hΨ.map_nhds_eq_of_equiv
    rw [hΨ0] at this
    rw [← this]
    exact image_mem_map hUn
  have hM : Tendsto (fun p : (Fin N → ℝ) × E => Θ p.1 * σ p.2) (𝓝 0 ×ˢ 𝓝 1) (𝓝 1) := by
    have a : Tendsto σ (𝓝 1) (𝓝 1) := by
      simpa [h1] using hσc.tendsto 1
    simpa using (hΘt.comp tendsto_fst).mul (a.comp tendsto_snd)
  have hPM : Tendsto (fun p : (Fin N → ℝ) × E => P (Θ p.1 * σ p.2)) (𝓝 0 ×ˢ 𝓝 1) (𝓝 0) := by
    have a : Tendsto P (𝓝 1) (𝓝 0) := by
      simpa [hP2 _ h1] using P.continuous.tendsto 1
    exact a.comp hM
  obtain ⟨A, hAn, W, hWn, hAW⟩ := Filter.mem_prod_iff.mp ((hM.eventually hnear).and (hPM hV))
  obtain ⟨s, hs, hsA⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (inter_mem hAn hU₁)
  have hcube : ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), t ∈ A ∩ U₁ := by
    intro t ht
    apply hsA
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hs.le]
    intro i
    have := ht i (Set.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  refine ⟨s, 1, 2 * (‖P‖ * (L * (‖(1 : E)‖ + 1))), W ∩ Metric.closedBall 1 1, hs, by positivity,
    inter_mem hWn (Metric.closedBall_mem_nhds _ one_pos), fun x hx hx1 hx2 => ?_⟩
  have hxn : ‖x‖ ≤ ‖(1 : E)‖ + 1 := norm_le_of_mem_closedBall hx.2
  have key : ∀ t : Fin N → ℝ, ∃ y : Fin N → ℝ, t ∈ A → y ∈ U ∧ Θ y * x = Θ t := by
    intro t
    by_cases ht : t ∈ A
    · obtain ⟨k1, y, hy, k2⟩ := hAW (Set.mk_mem_prod ht hx.1)
      refine ⟨y, fun _ => ⟨hy, ?_⟩⟩
      have hv : Θ t * σ x * σ (Θ t * σ x) = 1 := by
        rw [hm, hσ]
        calc Θ t * σ x * (x * σ (Θ t)) = Θ t * (σ x * x) * σ (Θ t) := by noncomm_ring
          _ = 1 := by rw [hx1, mul_one, (hU t).2]
      have := eq_of_skew_eq (hU y).1 hv (hP3 _ _ k2) hy.1.2 k1
      rw [this, mul_assoc, hx1, mul_one]
    · exact ⟨0, fun h => absurd h ht⟩
  choose f hf using key
  refine ⟨f, fun t ht => ?_, fun t ht t' ht' => ?_⟩
  · obtain ⟨a, b⟩ := hf t (hcube t ht).1
    exact ⟨mem_closedBall_zero_iff.mp a.2, b⟩
  · obtain ⟨a, b⟩ := hf t (hcube t ht).1
    obtain ⟨a', b'⟩ := hf t' (hcube t' ht').1
    have k1 := hA t (hcube t ht).2 t' (hcube t' ht').2
    have k2 : ‖t - t'‖ ≤ 2 * ‖P (Θ t) - P (Θ t')‖ := by
      have k3 : ‖t - t'‖ ≤ ‖P (Θ t) - P (Θ t')‖ + ‖P (Θ t) - P (Θ t') - (t - t')‖ := by
        have := norm_sub_le (P (Θ t) - P (Θ t')) (P (Θ t) - P (Θ t') - (t - t'))
        simpa using this
      have k4 : ‖P (Θ t) - P (Θ t') - (t - t')‖ ≤ 1 / 2 * ‖t - t'‖ := by simpa using k1
      linarith
    have k5 : ‖Θ (f t) - Θ (f t')‖ ≤ L * ‖f t - f t'‖ := by
      simpa [dist_eq_norm] using hL.dist_le_mul _ a.1.1.2 _ a'.1.1.2
    have k6 : ‖P (Θ t) - P (Θ t')‖ ≤ ‖P‖ * (L * ‖f t - f t'‖ * (‖(1 : E)‖ + 1)) := by
      rw [← map_sub, ← b, ← b', ← sub_mul]
      refine (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact (norm_mul_le _ _).trans (mul_le_mul k5 hxn (norm_nonneg _) (by positivity))
    calc ‖t - t'‖ ≤ 2 * (‖P‖ * (L * ‖f t - f t'‖ * (‖(1 : E)‖ + 1))) := by linarith
      _ = _ := by ring

end GlobalTheory.UnitaryChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOneStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_secondKind_coordinates_near_one : ∀ (E : Type) [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E) (N : ℕ) (e : Fin N → E) (c : Fin N → ℝ → E), (∀ a, σ (σ a) = a) → (∀ a b, σ (a * b) = σ b * σ a) → σ 1 = 1 → LinearIndependent ℝ e → (∀ i, σ (e i) = -e i) → (∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) → (∀ i, c i 0 = 1 ∧ HasStrictDerivAt (c i) (e i) 0 ∧ ∀ t, σ (c i t) * c i t = 1 ∧ c i t * σ (c i t) = 1) → ∃ (s S K : ℝ) (W : Set E), 0 < s ∧ 0 ≤ K ∧ W ∈ nhds (1 : E) ∧ ∀ x ∈ W, σ x * x = 1 → x * σ x = 1 → ∃ f : (Fin N → ℝ) → (Fin N → ℝ), (∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖f t‖ ≤ S ∧ (List.ofFn fun i => c i (f t i)).prod * x = (List.ofFn fun i => c i (t i)).prod) ∧ ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∀ t' ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖t - t'‖ ≤ K * ‖f t - f t'‖ := by
  first | exact @GlobalTheory.UnitaryChart.second_kind_chart | exact GlobalTheory.UnitaryChart.second_kind_chart | (intros; apply GlobalTheory.UnitaryChart.second_kind_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecomposition
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric

noncomputable section

namespace GlobalTheory.SchwartzDiv

section Param

variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}

theorem hasFDerivAt_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) (t₀ : P) :
    HasFDerivAt (fun t => ∫ y, φ y • Θ (t, c y) ∂ν) (∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t₀ ∂ν) t₀ := by
  have hΘs : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
    ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
      (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
  have hΘ' := hΘs.continuous
  have hK : IsCompact (closedBall t₀ 1 ×ˢ S) := (isCompact_closedBall t₀ 1).prod hS
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ'.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hΘ.continuous.continuousOn
  have hm : ∀ t, AEStronglyMeasurable (fun y => φ y • Θ (t, c y)) ν := fun t =>
    hφ.1.smul ((hΘ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun t y => φ y • fderiv ℝ (fun s => Θ (s, c y)) t) (bound := fun y => ‖φ y‖ * C)
    (ball_mem_nhds t₀ one_pos) (.of_forall hm) ?_ ?_ ?_ (hφ.norm.mul_const C) ?_
  · refine Integrable.mono' (hφ.norm.mul_const C₀) (hm t₀) ?_
    filter_upwards [hcS] with y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC₀ _ ⟨mem_closedBall_self zero_le_one, hy⟩) (norm_nonneg _)
  · exact hφ.1.smul ((hΘ'.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  · filter_upwards [hcS] with y hy t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (t, c y) ⟨ball_subset_closedBall ht, hy⟩) (norm_nonneg _)
  · refine .of_forall fun y t _ => ?_
    have hd : ContDiff ℝ ∞ fun s => Θ (s, c y) := hΘ.comp (contDiff_id.prodMk contDiff_const)
    exact ((hd.differentiable (by simp)) t).hasFDerivAt.const_smul (φ y)

theorem contDiff_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ fun t => ∫ y, φ y • Θ (t, c y) ∂ν := by
  rw [contDiff_infty]
  intro n
  induction n generalizing W with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t).continuousAt)
  | succ n ih =>
    have hΘ' : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
      ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
        (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨fun t => ∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t ∂ν,
      ih hΘ', fun t => hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t⟩

end Param

def invCut (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1) * t⁻¹

theorem invCut_of_one_le {t : ℝ} (ht : 1 ≤ t) : invCut t = t⁻¹ := by
  rw [invCut, Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem invCut_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : invCut t = 0 := by
  rw [invCut, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem contDiff_invCut : ContDiff ℝ ∞ invCut := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge 0 t with h | h
  · exact ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt).mul (contDiffAt_inv ℝ h.ne')
  · have : invCut =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show t < 1 / 2 by linarith)] with s hs
      exact invCut_of_le_half hs.le
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem hasTemperateGrowth_invCut : invCut.HasTemperateGrowth := by
  refine ⟨contDiff_invCut, fun n => ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (contDiff_invCut.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).continuousOn
  refine ⟨0, max C (Nat.factorial n : ℝ), fun x => ?_⟩
  rw [pow_zero, mul_one]
  rcases lt_or_ge x (1 / 2) with h1 | h1
  · have : invCut =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      exact invCut_of_le_half hs.le
    rw [(this.iteratedFDeriv ℝ n).eq_of_nhds]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact le_max_of_le_right (Nat.cast_nonneg _)
  rcases le_or_gt x 2 with h2 | h2
  · exact (hC x ⟨h1, h2⟩).trans (le_max_left _ _)
  · have : invCut =ᶠ[𝓝 x] Inv.inv := by
      filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < x by linarith)] with s hs
      exact invCut_of_one_le hs.le
    rw [(this.iteratedFDeriv ℝ n).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, iter_deriv_inv]
    refine le_trans ?_ (le_max_right _ _)
    have hx : ‖x ^ (-1 - n : ℤ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (zpow_pos (by linarith) _)]
      exact zpow_le_one_of_nonpos₀ (by linarith) (by omega)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
    calc (Nat.factorial n : ℝ) * ‖x ^ (-1 - n : ℤ)‖ ≤ Nat.factorial n * 1 := by gcongr
      _ = Nat.factorial n := mul_one _

end GlobalTheory.SchwartzDiv

namespace GlobalTheory.SchwartzDiv

theorem hadamard (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (hf0 : f 0 = 0) :
    ∃ (n : ℕ) (L : Fin n → V →L[ℝ] ℝ) (h g : Fin n → SchwartzMap V ℂ),
      (∀ i x, g i x = (L i x : ℂ) * h i x) ∧ ∀ x, f x = ∑ i, g i x := by
  let b := Module.finBasis ℝ V
  let L : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hL : ∀ i x, L i x = b.repr x i := fun i x => by simp [L, Module.Basis.coord_apply]
  let q : V → ℝ := fun x => ∑ i, L i x ^ 2
  have hq : q.HasTemperateGrowth := by
    simp only [q]
    exact Function.HasTemperateGrowth.sum fun i _ => ((L i).hasTemperateGrowth).pow 2
  have hqs : ContDiff ℝ ∞ q := hq.1
  have hfs : ContDiff ℝ ∞ f := f.smooth ⊤
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hfs.fderiv_right (by simp)

  let k : Fin (Module.finrank ℝ V) → V → ℂ := fun i x => ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) (b i)
  have hk : ∀ i, ContDiff ℝ ∞ (k i) := by
    intro i
    have hΘ : ContDiff ℝ ∞ fun p : V × ℝ => fderiv ℝ f (p.2 • p.1) (b i) :=
      (hfd.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_const
    have key := contDiff_integral_smul_param (ν := volume.restrict (Ioc (0 : ℝ) 1)) (c := id)
      (S := Icc (0 : ℝ) 1) (φ := fun _ => (1 : ℂ)) aestronglyMeasurable_id isCompact_Icc
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => Ioc_subset_Icc_self ht)
      (integrableOn_const (by simp)) hΘ
    convert key using 2 with x
    simp [k, intervalIntegral.integral_of_le zero_le_one]
  have key : ∀ x, f x = ∑ i, (L i x : ℂ) * k i x := by
    intro x
    have hc : ∀ v : V, Continuous fun t : ℝ => fderiv ℝ f (t • x) v := fun v =>
      (hfd.continuous.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
    have h1 : ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) x = f ((1 : ℝ) • x) - f ((0 : ℝ) • x) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => f (t • x)) (fun t _ => ?_)
        ((hc x).intervalIntegrable _ _)
      have := (f.differentiableAt (x := t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
      simp only [one_smul] at this
      exact this
    rw [one_smul, zero_smul, hf0, sub_zero] at h1
    rw [← h1]
    have h2 : ∀ t : ℝ, fderiv ℝ f (t • x) x = ∑ i, (L i x : ℂ) * fderiv ℝ f (t • x) (b i) := by
      intro t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [show fderiv ℝ f (t • x) x = fderiv ℝ f (t • x) (∑ i, b.repr x i • b i) by rw [b.sum_repr], map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Complex.real_smul, hL]
    simp_rw [h2]
    rw [intervalIntegral.integral_finsetSum (f := fun i t => (L i x : ℂ) * fderiv ℝ f (t • x) (b i))
      fun i _ => (continuous_const.mul (hc (b i))).intervalIntegrable _ _]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _

  let β : V → ℝ := fun x => 1 - q x * invCut (q x)
  have hβs : ContDiff ℝ ∞ β := contDiff_const.sub (hqs.mul (contDiff_invCut.comp hqs))
  have hβ0 : ∀ x, 1 ≤ q x → β x = 0 := by
    intro x hx
    simp only [β]
    rw [invCut_of_one_le hx, mul_inv_cancel₀ (by linarith), sub_self]
  have hnorm : ∀ x, q x < 1 → ‖x‖ ≤ ∑ i, ‖b i‖ := by
    intro x hx
    have hLi : ∀ i, |L i x| ≤ 1 := by
      intro i
      have : L i x ^ 2 ≤ q x :=
        Finset.single_le_sum (f := fun j => L j x ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      exact (sq_le_one_iff_abs_le_one _).1 (by linarith)
    calc ‖x‖ = ‖∑ i, L i x • b i‖ := by simp only [hL, b.sum_repr]
      _ ≤ ∑ i, ‖L i x • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (hLi i)
  have hβc : HasCompactSupport (fun x => (β x : ℂ)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V) (∑ i, ‖b i‖)) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    have : 1 ≤ q x := by
      by_contra h
      exact absurd (hnorm x (not_le.1 h)) (not_le.2 hx)
    rw [hβ0 x this, Complex.ofReal_zero]
  have hnear : ∀ i, HasCompactSupport ((fun x => (β x : ℂ)) * k i) := fun i => hβc.mul_right
  have hnears : ∀ i, ContDiff ℝ ∞ ((fun x => (β x : ℂ)) * k i) := fun i =>
    (Complex.ofRealCLM.contDiff.comp hβs).mul (hk i)

  let a : Fin (Module.finrank ℝ V) → V → ℂ := fun i x => ((L i x * invCut (q x) : ℝ) : ℂ)
  have ha : ∀ i, (a i).HasTemperateGrowth := fun i =>
    Function.Complex.hasTemperateGrowth_ofReal.comp ((L i).hasTemperateGrowth.mul (hasTemperateGrowth_invCut.comp hq))
  have hLc : ∀ i, (fun x => (L i x : ℂ)).HasTemperateGrowth := fun i =>
    Function.Complex.hasTemperateGrowth_ofReal.comp (L i).hasTemperateGrowth
  let h : Fin (Module.finrank ℝ V) → SchwartzMap V ℂ := fun i =>
    (hnear i).toSchwartzMap (hnears i) + SchwartzMap.smulLeftCLM ℂ (a i) f
  have hh : ∀ i x, h i x = (β x : ℂ) * k i x + a i x * f x := by
    intro i x
    have e : ((hnear i).toSchwartzMap (hnears i) : V → ℂ) x = (β x : ℂ) * k i x := rfl
    simp only [h, SchwartzMap.add_apply, e, SchwartzMap.smulLeftCLM_apply_apply (ha i), smul_eq_mul]
  refine ⟨Module.finrank ℝ V, L, h, fun i => SchwartzMap.smulLeftCLM ℂ (fun x => (L i x : ℂ)) (h i),
    fun i x => by rw [SchwartzMap.smulLeftCLM_apply_apply (hLc i), smul_eq_mul], fun x => ?_⟩
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hLc _), smul_eq_mul, hh]
  have e1 : ∀ i, (L i x : ℂ) * ((β x : ℂ) * k i x + a i x * f x) =
      (β x : ℂ) * ((L i x : ℂ) * k i x) + ((L i x ^ 2 * invCut (q x) : ℝ) : ℂ) * f x := by
    intro i; simp only [a]; push_cast; ring
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, ← Finset.mul_sum, ← key x,
    ← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_mul]
  simp only [β, q]
  push_cast
  ring

end GlobalTheory.SchwartzDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecompositionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_vanishing_decomposition : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ), f 0 = 0 → ∃ (n : ℕ) (L : Fin n → V →L[ℝ] ℝ) (h g : Fin n → SchwartzMap V ℂ),
      (∀ i x, g i x = (L i x : ℂ) * h i x) ∧ ∀ x, f x = ∑ i, g i x := by
  first | exact @GlobalTheory.SchwartzDiv.hadamard | exact GlobalTheory.SchwartzDiv.hadamard | (intros; apply GlobalTheory.SchwartzDiv.hadamard <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffHasse
namespace GlobalTheory.PicDiv

variable {R : Type*} [CommRing R]

noncomputable def hasse (l : ℕ) : PowerSeries R →ₗ[R] PowerSeries R where
  toFun φ := PowerSeries.mk fun n => ((n + l).choose l : R) * PowerSeries.coeff (n + l) φ
  map_add' φ ψ := by ext n; simp [mul_add]
  map_smul' c φ := by ext n; simp [mul_left_comm]

theorem coeff_hasse (l n : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff n (hasse l φ) = ((n + l).choose l : R) * PowerSeries.coeff (n + l) φ := by
  simp [hasse]

theorem constantCoeff_hasse (l : ℕ) (φ : PowerSeries R) :
    PowerSeries.constantCoeff (hasse l φ) = PowerSeries.coeff l φ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_hasse]; simp

theorem coeff_one_hasse (l : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff 1 (hasse l φ) = ((l + 1 : ℕ) : R) * PowerSeries.coeff (l + 1) φ := by
  rw [coeff_hasse, add_comm 1 l, Nat.choose_succ_self_right]

theorem hasse_zero (φ : PowerSeries R) : hasse 0 φ = φ := by
  ext n; simp [coeff_hasse]

end GlobalTheory.PicDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEq
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem idem_germ_eq_of_isUnit_iff {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : a * a = a) (hb : b * b = b) (h : IsUnit a ↔ IsUnit b) : a = b := by
  have key : ∀ c : R, c * c = c → (IsUnit c → c = 1) ∧ (¬ IsUnit c → c = 0) := by
    intro c hc
    refine ⟨fun hu => ?_, fun hn => ?_⟩
    · obtain ⟨u, rfl⟩ := hu
      have : (u : R) * u = u * 1 := by rw [mul_one]; exact hc
      exact (Units.mul_right_inj u).mp this
    · rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h1 | h1
      · exact absurd h1 hn
      · have : (1 - c) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
        obtain ⟨u, hu⟩ := h1
        rw [← hu] at this
        simpa using this
  by_cases hau : IsUnit a
  · rw [(key a ha).1 hau, (key b hb).1 (h.mp hau)]
  · rw [(key a ha).2 hau, (key b hb).2 (fun hbu => hau (h.mpr hbu))]

theorem idempotent_eq_of_basicOpen_eq : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' →
    X.basicOpen e = X.basicOpen e' → e = e' := by
  intro X e e' he he' hb
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e e' (fun x hx => ?_)
  change X.presheaf.germ ⊤ x hx e = X.presheaf.germ ⊤ x hx e'
  apply idem_germ_eq_of_isUnit_iff (R := X.presheaf.stalk x)
  · rw [← map_mul, he]
  · rw [← map_mul, he']
  · rw [← X.mem_basicOpen e x hx, ← X.mem_basicOpen e' x hx, hb]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
noncomputable section

namespace GlobalTheory.StdLoc

def rowBlockIndicatorFrom (a : ℕ) {d : ℕ} (i : Fin d) : ℕ := if a ≤ i.1 then 1 else 0

def blockPar (R : Type) [CommRing R] (a d : ℕ) : Subgroup (GL (Fin d) R) where
  carrier := {g | (g : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)}
  mul_mem' := fun {x y} hx hy => by
    show ((x * y : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    rw [Units.val_mul]; exact hx.mul hy
  one_mem' := by
    show ((1 : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    rw [Units.val_one]; exact Matrix.blockTriangular_one
  inv_mem' := fun {x} hx => by
    show ((x⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    letI : Invertible (x : Matrix (Fin d) (Fin d) R) := Units.invertible x
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hx

theorem _root_.GlobalTheory.StdLoc.mem_blockPar {R : Type} [CommRing R] {a d : ℕ} (g : GL (Fin d) R) :
    g ∈ _root_.GlobalTheory.StdLoc.blockPar R a d ↔ ∀ i j : Fin d, j.1 < a → a ≤ i.1 → (g : Matrix (Fin d) (Fin d) R) i j = 0 := by
  show (g : Matrix (Fin d) (Fin d) R).BlockTriangular (_root_.GlobalTheory.StdLoc.rowBlockIndicatorFrom a) ↔ _
  unfold Matrix.BlockTriangular _root_.GlobalTheory.StdLoc.rowBlockIndicatorFrom
  constructor
  · intro h i j hj hi
    apply h
    simp [hi, not_le.mpr hj]
  · intro h i j hlt
    refine h i j ?_ ?_ <;> split_ifs at hlt <;> omega

def glVol (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)

def blockIdx (q : ℝ) (c a a' : ℕ) : ℝ := q ^ (c * a * a') * glVol q (a + a') / (glVol q a * glVol q a')

end GlobalTheory.StdLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRing
namespace GlobalTheory

theorem isAdicComplete_of_le_of_isNoetherianRing (R : Type) [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hIJ : I ≤ J) (hJ : IsAdicComplete J R) : IsAdicComplete I R := by
  have hle : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) ≤ J ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)
  have hH : IsHausdorff I R :=
    ⟨fun x hx => hJ.toIsHausdorff.haus x fun n => (hx n).mono (hle n)⟩
  have hP : IsPrecomplete I R := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hJ.toIsPrecomplete.prec (f := f) fun {m n} h => (hf h).mono (hle m)
    refine ⟨L, fun n => ?_⟩
    set N : Submodule R R := I ^ n • ⊤ with hN
    have hK : (⨅ m : ℕ, J ^ m • ⊤ : Submodule R (R ⧸ N)) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_le_jacobson J (by
        simpa only [Ideal.jacobson_bot] using IsAdicComplete.le_jacobson_bot J)
    rw [SModEq.sub_mem, ← Submodule.Quotient.mk_eq_zero, ← Submodule.mem_bot R, ← hK,
      Submodule.mem_iInf]
    intro m
    have h1 : f n - f (max n m) ∈ N := SModEq.sub_mem.1 (hf (le_max_left n m))
    have h2 : f (max n m) - L ∈ (J ^ m • ⊤ : Submodule R R) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right n m))
        (SModEq.sub_mem.1 (hL (max n m)))
    have h3 : N.mkQ (f (max n m) - L) ∈ (J ^ m • ⊤ : Submodule R (R ⧸ N)) := by
      have := Submodule.mem_map_of_mem (f := N.mkQ) h2
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have h4 : (Submodule.Quotient.mk (f n - L) : R ⧸ N) = N.mkQ (f (max n m) - L) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      convert h1 using 1
      ring
    rw [h4]
    exact h3
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricPointOfFaithfullyFlatFiniteTy
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricPointOfFaithfullyFlatFiniteTy
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.GeomPointLift

theorem nonempty_algHom_of_isAlgClosed (K C : Type) [Field K] [IsAlgClosed K] [CommRing C] [Nontrivial C]
    [Algebra K C] [Algebra.FiniteType K C] : Nonempty (C →ₐ[K] K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal C
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (C ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ M)
  exact ⟨(IsAlgClosed.lift : (C ⧸ M) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)⟩

theorem exists_lift (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (hff : Module.FaithfullyFlat A B)
    (hft : Algebra.FiniteType A B) (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k) :
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := by
  letI : Algebra A k := φ.toAlgebra
  haveI : Nontrivial (k ⊗[A] B) := Module.FaithfullyFlat.rTensor_nontrivial A B k
  haveI : Algebra.FiniteType k (k ⊗[A] B) := inferInstance
  obtain ⟨f⟩ := nonempty_algHom_of_isAlgClosed k (k ⊗[A] B)
  refine ⟨f.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply A k (k ⊗[A] B), AlgHom.commutes]
  rfl

end GlobalTheory.GeomPointLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricPointOfFaithfullyFlatFiniteTyStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_geometricPoint_of_faithfullyFlat_finiteType : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
    Algebra.FiniteType A B → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : A →+* k),
    ∃ φ' : B →+* k, φ'.comp (algebraMap A B) = φ := by
  first | exact @GlobalTheory.GeomPointLift.exists_lift | exact GlobalTheory.GeomPointLift.exists_lift | (intros; apply GlobalTheory.GeomPointLift.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

def krylov {F : Type} [CommRing F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => Matrix.mulVec (y ^ (j : ℕ)) e i

theorem krylov_apply {F : Type} [CommRing F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) (i j : Fin r) :
    krylov y e i j = Matrix.mulVec (y ^ (j : ℕ)) e i := rfl

end GlobalTheory.LeviDesc.Krylov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
noncomputable section
namespace GlobalTheory.DenseSec

def EtChart (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {g : ℕ} (t : Fin g → A) (h : A) : Prop :=
  letI : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h)

def pt {R A Ω : Type} [CommRing R] [CommRing A] [Algebra R A] [Field Ω] [Algebra R Ω] (a : A →ₐ[R] Ω) :
    TensorProduct R Ω A →ₐ[Ω] Ω :=
  Algebra.TensorProduct.lift (AlgHom.id Ω Ω) a (fun _ _ => Commute.all _ _)

end GlobalTheory.DenseSec
end
end
