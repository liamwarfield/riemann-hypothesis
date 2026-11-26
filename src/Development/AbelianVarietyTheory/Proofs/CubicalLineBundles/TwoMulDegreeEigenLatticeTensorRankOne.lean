module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormSumSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.HermNorm

section Form

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V) (s : K →+* ℂ)

theorem form_sum_right {J : Type} (t : Finset J) (x : V) (c : J → K) (y : J → V) :
    h.form s x (∑ j ∈ t, c j • y j) = ∑ j ∈ t, s (c j) * h.form s x (y j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using h.smul_right s 0 x 0
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, h.smul_right, ih]

theorem form_sum_left {J : Type} (t : Finset J) (c : J → K) (x : J → V) (y : V) :
    h.form s (∑ i ∈ t, c i • x i) y = ∑ i ∈ t, starRingEnd ℂ (s (c i)) * h.form s (x i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h.conj_symm, form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, h.conj_symm]

end Form

theorem hermForm_sum_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin n → ℂ) (W : Fin n → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • W i) (∑ i, a i • W i) =
      ∑ i, starRingEnd ℂ (a i) * ∑ j, a j * hermForm Hm (W j) (W i) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul,
    sum_dotProduct, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem form_eq {K : Type} [Field K] {g n : ℕ} (h : HermFam K (Fin n → K)) (s : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin n → Fin g → ℂ) (r : ℂ)
    (e : ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = r * hermForm Hm (W j) (W i)) (c : Fin n → K) :
    h.form s c c = r * hermForm Hm (∑ i, s (c i) • W i) (∑ i, s (c i) • W i) := by
  have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → K) := pi_eq_sum_univ' c
  rw [hermForm_sum_sum, Finset.mul_sum]
  conv_lhs => rw [hc, form_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [form_sum_right, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [e]; ring

theorem isLieNormSq_form : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (s : K →+* ℂ) u c, F.IsCoord u c → IsLieNormSq P u (s.comp (algebraMap (𝓞 K) K)) (h.form s c c).re := by
  rintro - - K _ _ P F h hh s u c ⟨-, w, hw, hc⟩
  obtain ⟨Q, ψ, v', U, Hm, χ, W, hQ, hA, hv, e⟩ := hh s
  refine (EllComp.isLieNormSq_iff F.fib hw s _).1 ?_
  obtain ⟨w', hw', -⟩ := existsUnique_isVecOver hQ.2.1.1 w
  have hc' := (lieComb_baseChange _ _ s _ _ ψ hQ.2.1 _ F.v w c v' w' (fun i => (hv i).1) hc).1 hw'
  refine ⟨Q, ψ, w', U, Hm, χ, ∑ i, s (c i) • W i, hQ, hw', hA,
    UnifDifferential.isDiff_of_isLieComb _ _ _ _ U W v' _ w'
      (fun i => (hv i).1.isTangent hQ.2.1 (F.basis.1 i)) (fun i => (hv i).2) hc', ?_⟩
  rw [form_eq h s Hm W _ e, Complex.re_ofReal_mul]

end GlobalTheory.CM.HermNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SingleMemSpanIffOfSelfDual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem single_mem_span_iff_of_selfDual : ∀ (O R K La I : Type) [CommRing O] [CommRing R] [Field K] [Algebra R K] [AddCommGroup La] [Module O La] [Fintype I] [DecidableEq I] (τ₀ : O →+* R) (h : La → La → O) (ev dv : La → I → K) (n : ℕ) (x y : Fin n → La), (∀ a b, algebraMap R K (τ₀ (h a b)) = ∑ i, ev a i * dv b i) → (∀ a, ev a = ∑ m, algebraMap R K (τ₀ (h a (y m))) • ev (x m)) → Submodule.span K (Set.range ev) = ⊤ → ∀ (i : I) (t : K), Pi.single i t ∈ Submodule.span R (Set.range ev) ↔ ∀ b, t * dv b i ∈ (algebraMap R K).range := by
  intro O R K La I _ _ _ _ _ _ _ _ τ₀ h ev dv n x y hh hev hspan i t
  have hsum : ∀ b, ∑ j, (Pi.single i t : I → K) j * dv b j = t * dv b i := by
    intro b
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  constructor
  · intro hm b
    rw [← hsum b]
    generalize (Pi.single i t : I → K) = v at hm
    induction hm using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      exact ⟨_, hh a b⟩
    | zero => simp
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      exact add_mem hu hw
    | smul r u _ hu =>
      have : ∑ j, (r • u) j * dv b j = algebraMap R K r * ∑ j, u j * dv b j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def, _root_.mul_assoc]
      rw [this]
      exact mul_mem ⟨r, rfl⟩ hu
  · intro hb
    have key : ∀ v : I → K, v = ∑ m, (∑ j, v j * dv (y m) j) • ev (x m) := by
      intro v
      have hv : v ∈ Submodule.span K (Set.range ev) := hspan ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, rfl⟩ := hv
        simp only [← hh]
        exact hev a
      | zero => simp
      | add u w _ _ hu hw =>
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
        rw [← hu, ← hw]
      | smul r u _ hu =>
        simp only [Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, ← Finset.mul_sum, mul_smul,
          ← Finset.smul_sum]
        rw [← hu]
    rw [key (Pi.single i t)]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [hsum]
    obtain ⟨r, hr⟩ := hb (y m)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealTraceFormRankOne
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealTraceFormRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.RankOne

variable {E : Type} [Field E] [NumberField E]

theorem trace_eq_sum {Ω : Type} [Field Ω] [CharZero Ω] [Fintype (E →+* Ω)]
    (h : Nat.card (E →+* Ω) = Module.finrank ℚ E) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : Ω) = ∑ τ : E →+* Ω, τ x := by
  classical
  rw [← eq_ratCast (algebraMap ℚ Ω)]
  exact algebraMap_trace_eq_sum_algHom_of_card (Nat.card_eq_fintype_card.symm.trans h)
    (P := fun τ : E →+* Ω => τ.toRatAlgHom) (fun τ τ' e => RingHom.ext fun y => AlgHom.congr_fun e y) x

variable [IsCMField E]

theorem re_pos_of_trace_pos {β : E} (hβ : IsCMField.complexConj E β = β) (hβ0 : β ≠ 0)
    (h : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (β * x * IsCMField.complexConj E x)) (τ : E →+* ℂ) :
    0 < (τ β).re := by
  classical
  have him : ∀ σ : E →+* ℂ, (σ β).im = 0 := fun σ => by
    rw [← Complex.conj_eq_iff_im, ← IsCMField.complexEmbedding_complexConj, hβ]
  have hne : (τ β).re ≠ 0 := fun e => (map_ne_zero τ).2 hβ0 (Complex.ext e (him τ))
  refine lt_of_le_of_ne (not_lt.1 fun hneg => ?_) hne.symm
  obtain ⟨a, ha, hb⟩ := AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
    (v := fun v : InfinitePlace E => v.1) (fun v => v.isNontrivial)
    (fun _ _ h => (InfinitePlace.eq_iff_isEquiv (K := E)).not.mp h) (InfinitePlace.mk τ)
  replace ha : 1 < ‖τ a‖ := ha
  replace hb : ∀ σ : E →+* ℂ, InfinitePlace.mk σ ≠ InfinitePlace.mk τ → ‖σ a‖ < 1 := fun σ hσ => hb _ hσ
  have ha0 : a ≠ 0 := by
    rintro rfl
    norm_num at ha
  have h1 : ∀ n : ℕ, 0 < ∑ σ : E →+* ℂ, (σ β).re * (‖σ a‖ ^ 2) ^ n := fun n => by
    have h2 := congrArg Complex.re (trace_eq_sum (Ω := ℂ) (by rw [Nat.card_eq_fintype_card, Embeddings.card])
      (β * a ^ n * IsCMField.complexConj E (a ^ n)))
    have h3 : (0 : ℝ) < (Algebra.trace ℚ E (β * a ^ n * IsCMField.complexConj E (a ^ n)) : ℚ) := by
      exact_mod_cast h _ (pow_ne_zero n ha0)
    rw [Complex.ratCast_re, Complex.re_sum] at h2
    rw [h2] at h3
    convert h3 using 2 with σ
    rw [map_mul, map_mul, IsCMField.complexEmbedding_complexConj, _root_.mul_assoc, Complex.mul_conj,
      Complex.re_mul_ofReal, map_pow, map_pow, Complex.normSq_eq_norm_sq]
  let g : (E →+* ℂ) → ℕ → ℝ := fun σ n =>
    if InfinitePlace.mk σ = InfinitePlace.mk τ then (τ β).re else (σ β).re * (‖σ a‖ ^ 2) ^ n
  have h2 : ∀ n, 0 ≤ ∑ σ, g σ n := fun n => (h1 n).le.trans (Finset.sum_le_sum fun σ _ => by
    simp only [g]
    split_ifs with hσ
    · have e1 : ‖σ a‖ = ‖τ a‖ := congrArg (fun v : InfinitePlace E => v a) hσ
      have e2 : (σ β).re = (τ β).re := by
        rcases InfinitePlace.mk_eq_iff.1 hσ with rfl | rfl
        · rfl
        · simp
      rw [e1, e2]
      have e3 : 1 ≤ (‖τ a‖ ^ 2) ^ n := one_le_pow₀ (one_le_pow₀ ha.le)
      nlinarith
    · exact le_rfl)
  have h3 : Filter.Tendsto (fun n => ∑ σ, g σ n) Filter.atTop
      (nhds (∑ σ : E →+* ℂ, if InfinitePlace.mk σ = InfinitePlace.mk τ then (τ β).re else 0)) := by
    refine tendsto_finsetSum _ fun σ _ => ?_
    simp only [g]
    split_ifs with hσ
    · exact tendsto_const_nhds
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ‖σ a‖)
        (pow_lt_one₀ (norm_nonneg _) (hb σ hσ) two_ne_zero)).const_mul (σ β).re
  refine absurd (ge_of_tendsto' h3 h2) (not_le.2 ?_)
  refine (Finset.sum_lt_sum (g := fun _ => 0) (fun σ _ => ?_) ⟨τ, Finset.mem_univ _, ?_⟩).trans_eq (by simp)
  · split_ifs
    · exact hneg.le
    · exact le_rfl
  · simpa using hneg

theorem log_absNorm_of_selfDual {𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (h𝔞 : 𝔞 ≠ 0) {c : E} (hc : c ≠ 0)
    (h : ∀ v, v ∈ 𝔞 ↔ ∀ y ∈ 𝔞, ∃ n : ℤ, Algebra.trace ℚ E (c * v * IsCMField.complexConj E y) = n) :
    2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) + Real.log |(Algebra.norm ℚ c : ℚ)| =
      -(Module.finrank ℚ E * Real.log (rootDiscr E)) := by
  have h0 := conjFrac_ne_zero h𝔞
  have h1 : FractionalIdeal.dual ℤ ℚ (conjFrac 𝔞) = FractionalIdeal.spanSingleton _ c * 𝔞 := by
    ext w
    obtain ⟨v, rfl⟩ : ∃ v, w = c * v := ⟨c⁻¹ * w, (mul_inv_cancel_left₀ hc w).symm⟩
    have : c * v ∈ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) c * 𝔞 ↔ v ∈ 𝔞 := by
      rw [FractionalIdeal.mem_singleton_mul]
      exact ⟨fun ⟨y, hy, e⟩ => mul_left_cancel₀ hc e ▸ hy, fun hv => ⟨v, hv, rfl⟩⟩
    rw [this, h, FractionalIdeal.mem_dual h0]
    constructor
    · intro hh y hy
      obtain ⟨n, hn⟩ := hh _ (cc_mem_conjFrac.2 hy)
      exact ⟨n, hn.symm⟩
    · intro hh y hy
      obtain ⟨n, hn⟩ := hh _ (mem_conjFrac.1 hy)
      refine ⟨n, ?_⟩
      rw [FD.cc, IsCMField.complexConj_apply_apply] at hn
      exact hn.symm
  rw [FractionalIdeal.dual_eq_mul_inv, ← inv_inv (FractionalIdeal.dual ℤ ℚ 1),
    ← coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)] at h1
  have nz : ∀ {𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}, 𝔞 ≠ 0 → (FractionalIdeal.absNorm 𝔞 : ℝ) ≠ 0 :=
    fun h => by simpa using h
  have h3 := congrArg (fun 𝔞 => Real.log (FractionalIdeal.absNorm 𝔞 : ℚ)) h1
  have hN : (Algebra.norm ℚ c : ℝ) ≠ 0 := by exact_mod_cast Algebra.norm_ne_zero_iff.2 hc
  have hd : (0 : ℝ) < (|discr E| : ℤ) := by exact_mod_cast abs_pos.2 (discr_ne_zero E)
  have h2 : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  simp only [map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, FractionalIdeal.coeIdeal_absNorm,
    FractionalIdeal.absNorm_span_singleton, absNorm_differentIdeal E (𝓞 E), Rat.cast_natCast, Nat.cast_natAbs,
    Rat.cast_intCast] at h3
  rw [Real.log_mul (inv_ne_zero hd.ne') (inv_ne_zero (nz h0)), Real.log_inv, Real.log_inv,
    log_absNorm_conjFrac h𝔞, Real.log_mul (by simpa using hN) (nz h𝔞)] at h3
  rw [rootDiscr_def, Real.log_rpow hd, mul_inv_cancel_left₀ h2.ne', ← Rat.cast_abs]
  linarith

theorem coe_rt_eq (H : Host E) : (H.rt : E) = 2 * (H.w0 : E) - 1 := by
  rw [HostModel.rt_eq]; push_cast; rfl

theorem conj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  rw [← H.bar_eq, HostModel.bar_rt]; push_cast; rfl

theorem coe_rt_ne_zero (H : Host E) : (H.rt : E) ≠ 0 := by
  exact_mod_cast HostModel.rt_ne_zero H

theorem log_norm_rt (H : Host E) :
    Real.log |(Algebra.norm ℚ (H.rt : E) : ℚ)| = Module.finrank ℚ E * (Real.log H.d / 2) := by
  have h := congrArg (fun z : E => Real.log |(Algebra.norm ℚ z : ℚ)|) (HostModel.coe_sq_eq_neg H.rt_sq)
  have e : (-(H.d : E)) = algebraMap ℚ E (-(H.d : ℚ)) := by simp
  simp only [e, Algebra.norm_algebraMap, map_pow, Rat.cast_pow, Real.log_abs, Real.log_pow, Rat.cast_neg,
    Real.log_neg_eq_log, Rat.cast_natCast, Nat.cast_ofNat] at h
  rw [Real.log_abs]
  linarith

theorem relTrace_eq (H : Host E) {Ω : Type} [Field Ω] [CharZero Ω] (hΩ : Nat.card (E →+* Ω) = Module.finrank ℚ E)
    (τ₀ : E →+* Ω) (z : E) :
    ((Algebra.trace ℚ E (H.w0 * z / H.rt) : ℚ) : Ω) - (Algebra.trace ℚ E (z / H.rt) : ℚ) +
      (Algebra.trace ℚ E (z / H.rt) : ℚ) * τ₀ H.w0 =
      ∑ᶠ τ : {τ : E →+* Ω // τ (H.rt : E) = τ₀ (H.rt : E)}, τ.1 z := by
  classical
  have : Finite (E →+* Ω) := Nat.finite_of_card_ne_zero (by rw [hΩ]; exact Module.finrank_pos.ne')
  have := Fintype.ofFinite (E →+* Ω)
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_subtype (Finset.univ.filter fun τ : E →+* Ω => τ (H.rt : E) = τ₀ (H.rt : E))
    (by simp) (fun τ : E →+* Ω => τ z), Finset.sum_filter, trace_eq_sum hΩ, trace_eq_sum hΩ, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h0 : τ (H.rt : E) ≠ 0 := (map_ne_zero τ).2 (coe_rt_ne_zero H)
  have h1 : ∀ σ : E →+* Ω, σ (H.rt : E) = 2 * σ H.w0 - 1 := fun σ => by
    rw [coe_rt_eq, map_sub, map_mul, map_ofNat, map_one]
  have h2 : ∀ σ : E →+* Ω, σ (H.rt : E) ^ 2 = -(H.d : Ω) := fun σ => by
    rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, map_neg, map_natCast]
  have h3 := h1 τ
  have h4 := h1 τ₀
  simp only [map_div₀, map_mul]
  split_ifs with hτ
  · field_simp
    linear_combination (τ z / 2) * (- hτ - h3 - h4)
  · have h5 := (sq_eq_sq_iff_eq_or_eq_neg.1 ((h2 τ).trans (h2 τ₀).symm)).resolve_left hτ
    field_simp
    linear_combination (τ z / 2) * (h5 - h3 - h4)

end GlobalTheory.CM.RankOne

namespace GlobalTheory.CM

open RankOne

theorem exists_ideal_traceForm_of_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), D.p + D.q = 1 → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (e : D.La →ₗ[𝓞 E] E) (β : E), 𝔞 ≠ 0 ∧ Function.Injective e ∧ LinearMap.range e = (𝔞 : Submodule (𝓞 E) E) ∧ IsCMField.complexConj E β = β ∧ (∀ τ : E →+* ℂ, 0 < (τ β).re) ∧
  (∀ (Ω : Type) [Field Ω] [CharZero Ω], Nat.card (E →+* Ω) = Module.finrank ℚ E → ∀ (τ₀ : E →+* Ω) x y, τ₀ (((h x y : OK H) : 𝓞 E) : E) = ∑ᶠ τ : {τ : E →+* Ω // τ (H.rt : E) = τ₀ (H.rt : E)}, τ.1 (β * e x * IsCMField.complexConj E (e y))) ∧
  2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) + Real.log |(Algebra.norm ℚ β : ℚ)| = Module.finrank ℚ E * (Real.log H.d / 2 - Real.log (NumberField.rootDiscr E)) := by
  intro E _ _ _ H D ε h hr hh hpos
  have hε : ((ε : ℤ) : E) * (ε : ℤ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hrt := coe_rt_ne_zero H
  have hε0 : ((ε : ℤ) : E) ≠ 0 := left_ne_zero_of_mul_eq_one hε
  have hξ : FD.cc (((ε : ℤ) : E) / H.rt) = -(((ε : ℤ) : E) / H.rt) := by
    rw [FD.cc, map_div₀, map_intCast, conj_rt, div_neg]
  obtain ⟨G, φ, hm⟩ := exists_herm_coord_of_datum E H D _ hξ (div_ne_zero hε0 hrt) 1 hr.symm
  obtain ⟨-, hfg, -, hdual⟩ := HermModel.rank_integral_selfDual E H D 1 _ G φ hξ hm
  obtain ⟨hinj, hspan, hG, hdet, hEF⟩ := hm
  rw [Matrix.det_fin_one] at hdet
  have hherm : ∀ x y, FD.herm G x y = G 0 0 * x 0 * IsCMField.complexConj E (y 0) := fun x y => by
    simp only [FD.herm, FD.cc, Fin.sum_univ_one]; ring
  simp only [hherm] at hdual hEF
  have hβ : IsCMField.complexConj E (G 0 0) = G 0 0 := hG 0 0
  generalize G 0 0 = β at hdet hdual hEF hβ
  let e : D.La →ₗ[𝓞 E] E := LinearMap.proj 0 ∘ₗ φ
  have he : ∀ x, φ x 0 = e x := fun _ => rfl
  simp only [he] at hdual hEF
  have heinj : Function.Injective e := fun x y hxy => hinj (funext fun i => by rw [Subsingleton.elim i 0]; exact hxy)
  have hfg' : (LinearMap.range e).FG := by
    rw [LinearMap.range_comp]; exact hfg.map _
  let 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨_, FractionalIdeal.isFractional_of_fg hfg'⟩
  have hmem : ∀ v, v ∈ 𝔞 ↔ ∃ x, e x = v := fun v => Iff.rfl
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank, hr]; exact one_pos)
  obtain ⟨a, ha⟩ := exists_ne (0 : D.La)
  have ha' : e a ≠ 0 := (map_ne_zero_iff _ heinj).2 ha
  have h𝔞 : 𝔞 ≠ 0 := fun h0 => ha' (FractionalIdeal.eq_zero_iff.1 h0 _ ((hmem _).2 ⟨a, rfl⟩))
  have hsm : ∀ (s : 𝓞 E) x, e (s • x) = s * e x := fun s x => by rw [map_smul]; rfl
  have hE : ∀ x y, (((ε : ℤ) * D.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ E (β * e x * IsCMField.complexConj E (e y) / H.rt) := fun x y => by
    rw [Int.cast_mul, hEF, ← zsmul_eq_mul, ← map_zsmul, zsmul_eq_mul, ← _root_.mul_assoc, ← mul_div_assoc, hε]
    congr 1; ring
  have hE' : ∀ x y, (((ε : ℤ) * D.EF (H.w0 • x) y : ℤ) : ℚ) =
      Algebra.trace ℚ E (H.w0 * (β * e x * IsCMField.complexConj E (e y)) / H.rt) := fun x y => by
    rw [hE, hsm]; congr 1; ring
  refine ⟨𝔞, e, β, h𝔞, heinj, rfl, hβ, re_pos_of_trace_pos hβ hdet fun v hv => ?_, fun Ω _ _ hΩ τ₀ x y => ?_, ?_⟩
  · obtain ⟨s, n, hn, hs⟩ : ∃ (s : 𝓞 E) (n : ℤ), n ≠ 0 ∧ (s : E) = n * (v / e a) := by
      obtain ⟨n, hn, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
        (Algebra.IsAlgebraic.isAlgebraic (v / e a))).exists_integral_multiple
      exact ⟨⟨_, hi⟩, n, hn, zsmul_eq_mul _ _⟩
    have hx : e (s • a) = n * v := by rw [hsm, hs]; field_simp
    have h1 : (0 : ℚ) < (((ε : ℤ) * D.EF (H.w0 • s • a) (s • a) : ℤ) : ℚ) := by
      exact_mod_cast hpos _ ((map_ne_zero_iff _ heinj).1 (hx ▸ mul_ne_zero (Int.cast_ne_zero.2 hn) hv))
    have h2 := hE (s • a) (s • a)
    rw [D.alt, mul_zero, Int.cast_zero] at h2
    rw [hE'] at h1
    have h3 : (H.w0 : E) * (β * e (s • a) * IsCMField.complexConj E (e (s • a))) / H.rt =
        (2⁻¹ : ℚ) • (β * e (s • a) * IsCMField.complexConj E (e (s • a)) / H.rt) +
          ((n : ℚ) ^ 2 / 2) • (β * v * IsCMField.complexConj E v) := by
      rw [hx, map_mul, map_intCast, Rat.smul_def, Rat.smul_def]
      push_cast
      field_simp
      rw [coe_rt_eq]
      ring
    rw [h3, map_add (f := _), map_smul (Algebra.trace ℚ E), map_smul (Algebra.trace ℚ E), ← h2, smul_zero, zero_add,
      smul_eq_mul] at h1
    exact (mul_pos_iff_of_pos_left (by positivity)).1 h1
  · rw [← relTrace_eq H hΩ, ← hE, ← hE', hh]
    push_cast
    simp only [map_add (f := _), map_mul, map_sub, map_intCast]
    ring
  · have h1 := log_absNorm_of_selfDual h𝔞 (mul_ne_zero (div_ne_zero hε0 hrt) hdet) fun v => by
      have h2 := hdual fun _ => v
      simp only [← _root_.mul_assoc] at h2
      constructor
      · intro hv y hy
        obtain ⟨x, rfl⟩ := (hmem _).1 hv
        obtain ⟨y, rfl⟩ := (hmem _).1 hy
        exact h2.2 ⟨x, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩ y
      · intro hv
        obtain ⟨x, hx⟩ := h2.1 fun y => hv _ ((hmem _).2 ⟨y, rfl⟩)
        exact (hmem _).2 ⟨x, congrFun hx 0⟩
    have h2 : Real.log |(Algebra.norm ℚ (((ε : ℤ) : E) / H.rt * β) : ℚ)| =
        Real.log |(Algebra.norm ℚ β : ℚ)| - Real.log |(Algebra.norm ℚ (H.rt : E) : ℚ)| := by
      have n1 : (Algebra.norm ℚ β : ℝ) ≠ 0 := by exact_mod_cast Algebra.norm_ne_zero_iff.2 hdet
      have n2 : (Algebra.norm ℚ (H.rt : E) : ℝ) ≠ 0 := by exact_mod_cast Algebra.norm_ne_zero_iff.2 hrt
      have n3 : |(Algebra.norm ℚ ((ε : ℤ) : E) : ℝ)| = 1 := by
        rw [← map_intCast (algebraMap ℚ E), Algebra.norm_algebraMap]
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
      rw [div_eq_mul_inv, map_mul, map_mul, Algebra.norm_inv]
      push_cast
      rw [abs_mul, abs_mul, n3, _root_.one_mul, Real.log_mul (by simpa using n2) (by simpa using n1), abs_inv, Real.log_inv]
      ring
    rw [h2, log_norm_rt] at h1
    linear_combination h1

end GlobalTheory.CM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealTraceFormRankOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fractionalIdeal_traceForm_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), D.p + D.q = 1 → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (e : D.La →ₗ[𝓞 E] E) (β : E), 𝔞 ≠ 0 ∧ Function.Injective e ∧ LinearMap.range e = (𝔞 : Submodule (𝓞 E) E) ∧ IsCMField.complexConj E β = β ∧ (∀ τ : E →+* ℂ, 0 < (τ β).re) ∧
  (∀ (Ω : Type) [Field Ω] [CharZero Ω], Nat.card (E →+* Ω) = Module.finrank ℚ E → ∀ (τ₀ : E →+* Ω) x y, τ₀ (((h x y : OK H) : 𝓞 E) : E) = ∑ᶠ τ : {τ : E →+* Ω // τ (H.rt : E) = τ₀ (H.rt : E)}, τ.1 (β * e x * IsCMField.complexConj E (e y))) ∧
  2 * Real.log (FractionalIdeal.absNorm 𝔞 : ℚ) + Real.log |(Algebra.norm ℚ β : ℚ)| = Module.finrank ℚ E * (Real.log H.d / 2 - Real.log (NumberField.rootDiscr E)) := by
  first | exact @GlobalTheory.CM.exists_ideal_traceForm_of_rank_one | exact GlobalTheory.CM.exists_ideal_traceForm_of_rank_one | (intros; apply GlobalTheory.CM.exists_ideal_traceForm_of_rank_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieTensorLine
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CM

private theorem isLieComb_one_iff {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (r : R)
    (v w : epsR R ⟶ G) : IsLieComb ![r] ![v] w ↔ w.left = spMap (epsScaleR r) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    exact ⟨![w], fun i ↦ by rw [Subsingleton.elim i 0]; exact h, by simp⟩

theorem lie_tensor_line :
    ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra O R] (G A : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (M : Type)
      [AddCommGroup M] [Module O M] (t : Serre.IsTensor A b G a M) (v : epsR R ⟶ G),
      Module.Finite O M → Module.Projective O M → IsLieBasis ![v] →
      (∀ c, IsLieComb ![algebraMap O R c] ![v] (v ≫ a.act c)) →
      ∃ e : TensorProduct O R M → (epsR R ⟶ A), Function.Injective e ∧
        (∀ u, IsTangent u ↔ u ∈ Set.range e) ∧ (∀ z z', e (z + z') = e z * e z') ∧
        (∀ (r : R) z, IsLieComb ![r] ![e z] (e (r • z))) ∧
        ∀ m, e (TensorProduct.tmul O 1 m) = v ≫ t.tmul m := by
  intro R O _ _ _ G A _ _ _ _ a b M _ _ t v _ _ hv hc
  have hτ := fun c ↦ (isLieComb_one_iff _ _ _).mp (hc c)
  let e := t.lieEquivLine b hv hτ
  refine ⟨fun z ↦ (e z).hom, fun z z' h ↦ e.injective (Serre.Lie.ext h), fun u ↦ ⟨fun hu ↦ ?_, ?_⟩,
    fun z z' ↦ by simp only [map_add (f := _), Serre.Lie.hom_add], fun r z ↦ ?_, fun m ↦ ?_⟩
  · exact ⟨e.symm (Serre.Lie.mk b u hu), by simp⟩
  · rintro ⟨z, rfl⟩
    exact (e z).isTangent
  · beta_reduce
    rw [isLieComb_one_iff, map_smul]
    exact Serre.Lie.hom_smul_left r (e z)
  · change (t.lieEquivLine b hv hτ _).hom = _
    rw [Serre.IsTensor.hom_lieEquivLine_tmul, GrpTangent.epsScale_one, Category.id_comp]

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegreeEigenLatticeTensorRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.TensorDeg

theorem eq_zero_of_re_diag {L : Type} [AddCommGroup L] (B : L → L → ℂ) (W : L → L) (l : ℂ) (hl : l.im ≠ 0)
    (hadd : ∀ a b c, B a (b + c) = B a b + B a c) (hsym : ∀ a b, starRingEnd ℂ (B a b) = B b a)
    (hW : ∀ a b, B a (W b) = l * B a b) (hd : ∀ a, (B a a).re = 0) (a b : L) : B a b = 0 := by
  have hre : ∀ a b, (B a b).re = (B b a).re := fun a b => by rw [← hsym a b, Complex.conj_re]
  have h0 : ∀ a b, (B a b).re = 0 := fun a b => by
    have h1 := hd (a + b)
    rw [hadd, Complex.add_re, hre (a + b) a, hre (a + b) b, hadd, hadd, Complex.add_re, Complex.add_re, hd, hd,
      hre b a] at h1
    linarith
  have h2 := h0 a (W b)
  rw [hW, Complex.mul_re, h0, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at h2
  exact Complex.ext (h0 a b) (h2.resolve_left hl)

theorem span_embeddings_eq_top {E K L I : Type} [Field E] [NumberField E] [Field K] [AddCommGroup L] [Module (𝓞 E) L]
    [Fintype I] (σ : I → (E →+* K)) (hσ : Function.Injective σ) (e : L →ₗ[𝓞 E] E) (a₀ : L) (h₀ : e a₀ ≠ 0) :
    Submodule.span K (Set.range fun a i => σ i (e a)) = ⊤ := by
  refine span_flip_eq_top_iff_linearIndependent.2 (?_ : LinearIndependent K fun i a => σ i (e a))
  have hinj : Function.Injective fun i => ((σ i).comp (algebraMap (𝓞 E) E)).toMonoidHom := fun i j hij =>
    hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => DFunLike.congr_fun hij a))
  have hli := (linearIndependent_monoidHom (𝓞 E) K).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg i
  have := hli (fun i => g i * σ i (e a₀)) (funext fun s => by
    have := congrFun hg (s • a₀)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul, Algebra.smul_def, map_mul, Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Function.comp]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.smul_def]
    ring) i
  exact (mul_eq_zero.1 this).resolve_right ((map_ne_zero _).2 h₀)

theorem form_eq_of_span {K V L I : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype I] (h : HermFam K V)
    (s : K →+* ℂ) (Φ : (I → K) →ₗ[K] V) (ev : L → I → K) (b : I → ℝ)
    (hsp : Submodule.span K (Set.range ev) = ⊤)
    (hf : ∀ x y, h.form s (Φ (ev x)) (Φ (ev y)) = ∑ i, b i * (starRingEnd ℂ (s (ev x i)) * s (ev y i))) (z w : I → K) :
    h.form s (Φ z) (Φ w) = ∑ i, b i * (starRingEnd ℂ (s (z i)) * s (w i)) := by
  have key : ∀ z, (∀ y, h.form s (Φ z) (Φ (ev y)) = ∑ i, b i * (starRingEnd ℂ (s (z i)) * s (ev y i))) →
      ∀ w, h.form s (Φ z) (Φ w) = ∑ i, b i * (starRingEnd ℂ (s (z i)) * s (w i)) := fun z hz w => by
    have hw : w ∈ Submodule.span K (Set.range ev) := hsp ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem v hv => obtain ⟨y, rfl⟩ := hv; exact hz y
    | zero => simpa using h.smul_right s 0 (Φ z) 0
    | add u v _ _ hu hv => simp only [map_add (f := _), h.add_right, hu, hv, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    | smul r u _ hu =>
      rw [map_smul, h.smul_right, hu, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp; ring
  refine key z (fun y => ?_) w
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h.conj_symm, key _ (hf y), map_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [_root_.mul_comm]

theorem exists_eigenline {E K O L V I : Type} [Field E] [NumberField E] [IsCMField E] [Field K] [NumberField K]
    [CommRing O] [AddCommGroup L] [Module (𝓞 E) L] [Module O L] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype I] (σ : I → (E →+* K)) (hσ : Function.Injective σ) (i₀ : I)
    (τ₀ : O →+* 𝓞 K) (w : O) (hw : ∀ s : K →+* ℂ, (s (τ₀ w)).im ≠ 0) (e : L →ₗ[𝓞 E] E)
    (he : ∀ i (k : O) a, σ i (e (k • a)) = τ₀ k * σ i (e a)) (a₀ : L) (h₀ : e a₀ ≠ 0) (β : E)
    (hβ : ∀ s : E →+* ℂ, 0 < (s β).re ∧ (s β).im = 0) (hK : L → L → O)
    (hh : ∀ a b, (τ₀ (hK a b) : K) = ∑ i, σ i (β * e a * IsCMField.complexConj E (e b)))
    (N : ℕ) (x y : Fin N → L) (hdual : ∀ a, a = ∑ m, hK a (y m) • x m) (h : HermFam K V) (n : (K →+* ℂ) → ℝ)
    (hn : ∀ s, 0 < n s) (c : L →+ V) (hc : ∀ (k : O) a, c (k • a) = (τ₀ k : K) • c a) (r : 𝓞 E → V →ₗ[K] V)
    (hr : ∀ s a, c (s • a) = r s (c a))
    (hnorm : ∀ s a, (h.form s (c a) (c a)).re = (s (τ₀ (hK a a))).re * n s) :
    ∃ v : V, v ≠ 0 ∧ (∀ s, (h.form s v v).re = (s (σ i₀ β)).re * n s) ∧
      ∀ z, (z ∈ Submodule.span (𝓞 K) (Set.range c) ∧ ∀ a : 𝓞 E, r a z = σ i₀ a • z) ↔
        ∃ t : K, z = t • v ∧ ∀ b, IsIntegral ℤ (t * σ i₀ (β * IsCMField.complexConj E (e b))) := by
  classical
  set ev : L → I → K := fun a i => σ i (e a) with hev
  set dv : L → I → K := fun b i => σ i (β * IsCMField.complexConj E (e b)) with hdv
  have hsp : Submodule.span K (Set.range ev) = ⊤ := span_embeddings_eq_top σ hσ e a₀ h₀
  have hh' : ∀ a b, algebraMap (𝓞 K) K (τ₀ (hK a b)) = ∑ i, ev a i * dv b i := fun a b =>
    (hh a b).trans (Finset.sum_congr rfl fun i _ => by simp only [hev, hdv, map_mul]; ring)
  have hexp : ∀ a, ev a = ∑ m, algebraMap (𝓞 K) K (τ₀ (hK a (y m))) • ev (x m) := fun a => by
    funext i
    conv_lhs => rw [hdual a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hev, map_sum, he, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let Φ : (I → K) →ₗ[K] V :=
    { toFun := fun z => ∑ m, (∑ i, z i * dv (y m) i) • c (x m)
      map_add' := fun z z' => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
      map_smul' := fun t z => by
        simp only [Pi.smul_apply, smul_eq_mul, _root_.mul_assoc, ← Finset.mul_sum, mul_smul, Finset.smul_sum,
          RingHom.id_apply] }
  have hΦ : ∀ a, Φ (ev a) = c a := fun a => by
    conv_rhs => rw [hdual a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hc]
    change ∑ m, (∑ i, ev a i * dv (y m) i) • c (x m) = _
    simp only [← hh']
  let b : (K →+* ℂ) → I → ℝ := fun s i => (s (σ i β)).re * n s
  have hb : ∀ s i, 0 < b s i := fun s i => mul_pos (hβ (s.comp (σ i))).1 (hn s)
  have hb' : ∀ (s : K →+* ℂ) i, (b s i : ℂ) = s (σ i β) * n s := fun s i => by
    have : s (σ i β) = ((s (σ i β)).re : ℂ) := Complex.ext rfl (hβ (s.comp (σ i))).2
    rw [this]
    simp [b]
  have hform : ∀ s z z', h.form s (Φ z) (Φ z') = ∑ i, b s i * (starRingEnd ℂ (s (z i)) * s (z' i)) := fun s => by
    refine form_eq_of_span h s Φ ev (b s) hsp fun a a' => sub_eq_zero.1 ?_
    refine eq_zero_of_re_diag (fun a a' => h.form s (Φ (ev a)) (Φ (ev a')) -
      ∑ i, b s i * (starRingEnd ℂ (s (ev a i)) * s (ev a' i))) (fun a => w • a) (s (τ₀ w)) (hw s)
      (fun a a' a'' => ?_) (fun a a' => ?_) (fun a a' => ?_) (fun a => ?_) a a'
    · simp only [hΦ]
      simp only [map_add (f := _), h.add_right, hev, mul_add, Finset.sum_add_distrib]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sub, h.conj_symm, map_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by simp [_root_.mul_comm]
    · simp only [hΦ]
      simp only [hc, h.smul_right, hev, he, mul_sub, Finset.mul_sum, map_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    · have : ∑ i, b s i * (starRingEnd ℂ (s (ev a i)) * s (ev a i)) = s (τ₀ (hK a a)) * n s := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hh, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have := IsCMField.complexEmbedding_complexConj E (s.comp (σ i)) (e a)
        simp only [RingHom.comp_apply] at this
        rw [hb', map_mul, map_mul, map_mul, map_mul, this]
        simp only [hev]
        ring
      rw [this, hΦ, Complex.sub_re, hnorm, Complex.re_mul_ofReal, sub_self]
  obtain ⟨s₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hinj : ∀ z, Φ z = 0 → z = 0 := fun z hz => by
    have h1 := hform s₀ z z
    have h2 : h.form s₀ 0 0 = 0 := by simpa using h.smul_right s₀ 0 0 0
    rw [hz, h2] at h1
    have h3 : ∑ i, b s₀ i * Complex.normSq (s₀ (z i)) = 0 := by
      have : ((∑ i, b s₀ i * Complex.normSq (s₀ (z i)) : ℝ) : ℂ) = 0 := by
        rw [h1]
        push_cast
        exact Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_conj_mul_self]
      exact_mod_cast this
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hb s₀ i).le (Complex.normSq_nonneg _)] at h3
    funext i
    have := (mul_eq_zero.1 (h3 i (Finset.mem_univ i))).resolve_left (hb s₀ i).ne'
    simpa using this
  have hinj' : Function.Injective Φ := (injective_iff_map_eq_zero Φ).2 hinj
  have hact : ∀ (a : 𝓞 E) z, r a (Φ z) = Φ fun i => σ i a * z i := fun a z => by
    have hz : z ∈ Submodule.span K (Set.range ev) := hsp ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨u, rfl⟩ := hv
      rw [hΦ, ← hr, ← hΦ]
      congr 1
      funext i
      simp [hev, Algebra.smul_def]
    | zero => simp only [Pi.zero_apply, mul_zero, map_zero]; exact (map_zero Φ).symm
    | add u v _ _ hu hv =>
      rw [map_add (f := _), map_add (f := _), hu, hv, ← map_add (f := _)]
      congr 1
      funext i
      simp [mul_add]
    | smul t u _ hu =>
      rw [map_smul, map_smul, hu, ← map_smul]
      congr 1
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have hmap : Submodule.span (𝓞 K) (Set.range c) =
      (Submodule.span (𝓞 K) (Set.range ev)).map (Φ.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    exact funext fun a => (hΦ a).symm
  have hline := single_mem_span_iff_of_selfDual O (𝓞 K) K L I τ₀ hK ev dv N x y hh' hexp hsp i₀
  have hint : ∀ t : K, t ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ t := fun t =>
    ⟨fun ⟨u, hu⟩ => hu ▸ u.isIntegral_coe, fun ht => ⟨⟨t, ht⟩, rfl⟩⟩
  have hsing : ∀ t : K, t • Φ (Pi.single i₀ 1) = Φ (Pi.single i₀ t) := fun t => by
    rw [← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  refine ⟨Φ (Pi.single i₀ 1), fun hv => ?_, fun s => ?_, fun z => ⟨?_, ?_⟩⟩
  · simpa using congrFun (hinj _ hv) i₀
  · rw [hform, Finset.sum_eq_single i₀ (fun i _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
    simp [b]
  · rintro ⟨hz, hz'⟩
    rw [hmap] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hu' : u = Pi.single i₀ (u i₀) := by
      funext i
      by_cases hi : i = i₀
      · simp [hi]
      · rw [Pi.single_eq_of_ne hi]
        by_contra hne
        refine hi (hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)))
        have := hz' a
        rw [LinearMap.restrictScalars_apply, hact, ← map_smul] at this
        exact mul_right_cancel₀ hne (congrFun (hinj' this) i)
    refine ⟨u i₀, by rw [hsing, ← hu']; rfl, fun a => (hint _).1 ((hline (u i₀)).1 (hu' ▸ hu) a)⟩
  · rintro ⟨t, rfl, ht⟩
    rw [hsing, hmap]
    refine ⟨⟨_, (hline t).2 fun a => (hint _).2 (ht a), rfl⟩, fun a => ?_⟩
    rw [hact, ← map_smul]
    congr 1
    funext i
    by_cases hi : i = i₀
    · simp [hi]
    · simp [Pi.single_eq_of_ne hi]

theorem two_mul_deg_eigLat : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ω : 𝓞 K) (C : Ell H (𝓞 K) ω) (D : Datum H) (ε : ℤˣ) (hK : D.La → D.La → OK H) (T : PAT H (Sp (𝓞 K))) (x : ℝ), Splits E K → D.p + D.q = 1 → IsKForm D ε hK → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → Nonempty (IsTen C D hK T) → C.HasPeriod x → ∀ (F : GenFib T.pol) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.w0 = ω → 2 * deg h (F.eigLat T.t.act τ) = x + Real.log H.d / 2 - Real.log (NumberField.rootDiscr E) := by
  intro hU hL E _ _ _ H K _ _ ω C D ε hK T x hsp hrk hKF hpos ⟨t⟩ ⟨n, hn, hx⟩ F h hh τ hτ
  classical
  obtain ⟨τ₀, hτ₀w, hτ₀⟩ := LieChar.ell_char E H (𝓞 K) ω C
  obtain ⟨τ', hτ'⟩ := (existsUnique_extend_ringOfIntegers_hom τ).exists
  have hext : ∀ σ : E →+* K, σ (H.rt : E) = τ' (H.rt : E) → ∀ k : OK H, σ ((k : 𝓞 E) : E) = τ₀ k := fun σ hσ k => by
    have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
      simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    have hw : σ (H.w0 : E) = τ₀ (wK H) := by
      rw [hτ₀w, ← hτ, ← hτ']
      have h3 := congrArg σ h2
      have h4 := congrArg τ' h2
      simp only [map_mul, map_add (f := _), map_one, map_ofNat] at h3 h4
      linear_combination (h3 - h4 + hσ) / 2
    obtain ⟨m, rfl, -⟩ := existsUnique_coord H k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_mul, map_intCast, ← hw]
    simp [wK]
  obtain ⟨𝔞, e, β, h𝔞, he, hrange, hβc, hβ, hform, hnorm⟩ := GlobalTheory.T.exists_fractionalIdeal_traceForm_rank_one E H D ε hK hrk hKF hpos
  obtain ⟨k, hk, hku, -, -, -, -, N, xs, ys, hdual⟩ := GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H D ε
  obtain rfl := hku hK hKF
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := integral_tangent_coordinates K T.pol F
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K T.pol F (𝓞 E) T.t.act
  letI : Algebra (OK H) (𝓞 K) := τ₀.toAlgebra
  obtain ⟨hfin, hproj, -⟩ := (OK_isDedekindDomain_and_projective E H).2.2.2.2.2 D.La D.fin D.proj
  obtain ⟨f, -, f2, f3, f4, f5⟩ := lie_tensor_line (𝓞 K) (OK H) C.P.A T.t.G C.act _ D.La t.ten C.v hfin hproj C.basis hτ₀
  choose co hco hcou using fun z => c1 (f z) ((f2 _).2 ⟨z, rfl⟩)
  have coadd : ∀ z z', co (z + z') = co z + co z' := fun z z' =>
    (hcou _ _ (by rw [f3]; exact c3 _ _ _ _ (hco z) (hco z'))).symm
  have cosmul : ∀ (a : 𝓞 K) z, co (a • z) = a • co z := fun a z =>
    (hcou _ _ (c4 _ _ _ _ (hco z) (f4 a z))).symm
  let c : D.La →+ (Fin F.P₀.g → K) := AddMonoidHom.mk' (fun a => co (TensorProduct.tmul (OK H) 1 a)) fun a b => by
    rw [TensorProduct.tmul_add, coadd]
  have hc : ∀ a, F.IsCoord (C.v ≫ t.ten.tmul a) (c a) := fun a => f5 a ▸ hco _
  have hlat : F.lieLat = Submodule.span (𝓞 K) (Set.range c) := by
    refine le_antisymm (fun z hz => ?_) (Submodule.span_le.2 ?_)
    · obtain ⟨u, hu⟩ := (c5 z).1 hz
      obtain ⟨z', rfl⟩ := (f2 u).1 hu.1
      rw [hcou _ _ hu]
      clear hu hz
      induction z' with
      | tmul a m =>
        rw [show TensorProduct.tmul (OK H) a m = a • TensorProduct.tmul (OK H) 1 m by
          simp [TensorProduct.smul_tmul'], cosmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      | add z z' hz hz' => rw [coadd]; exact add_mem hz hz'
    · rintro _ ⟨a, rfl⟩
      exact (c5 _).2 ⟨_, hc a⟩
  have hβ' : ∀ s : E →+* ℂ, 0 < (s β).re ∧ (s β).im = 0 := fun s => ⟨hβ s, by
    rw [← Complex.conj_eq_iff_im, ← IsCMField.complexEmbedding_complexConj E s, hβc]⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a, e a ≠ 0 := by
    by_contra! h0
    refine h𝔞 (FractionalIdeal.coeToSubmodule_eq_bot.1 ?_)
    rw [← hrange, LinearMap.range_eq_bot]
    exact LinearMap.ext h0
  have : Finite (E →+* K) := Finite.of_equiv _ (RingHom.equivRatAlgHom E K).symm
  have := Fintype.ofFinite {σ : E →+* K // σ (H.rt : E) = τ' (H.rt : E)}
  obtain ⟨v, hv0, hvn, hv⟩ := exists_eigenline (I := {σ : E →+* K // σ (H.rt : E) = τ' (H.rt : E)}) Subtype.val
    Subtype.val_injective ⟨τ', rfl⟩ τ₀ (wK H) (fun s => by
      intro him
      have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
        simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
      have h3 := congrArg (s.comp τ') h2
      have h4 := congrArg (s.comp τ') (HostModel.coe_sq_eq_neg H.rt_sq)
      have h5 : s (τ' (H.w0 : E)) = s (τ₀ (wK H)) := congrArg s (hext τ' rfl (wK H))
      simp only [map_mul, map_add (f := _), map_one, map_ofNat, map_pow, map_neg, map_natCast, RingHom.comp_apply] at h3 h4
      have h6 := congrArg Complex.im h3
      have h7 := congrArg Complex.re h4
      have h8 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      rw [h5] at h6
      simp [him] at h6
      simp [sq, ← h6] at h7
      nlinarith [mul_self_nonneg (s (τ' (H.rt : E))).re]) e
    (fun i a b => by
      rw [← hext i.1 i.2, ← map_mul, Subalgebra.smul_def, map_smul]
      rfl) a₀ ha₀ β hβ' (fun x y => k x y)
    (fun a b => by rw [← hext τ' rfl, hform K (splits_iff_card.1 hsp) τ' a b, finsum_eq_sum_of_fintype])
    N xs ys hdual h n (fun s => (hn s).1) c
    (fun a m => by
      change co _ = _ • co _
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (𝓞 K) a, cosmul]
      rfl) (fun a => r a)
    (fun s a => by
      refine (c1 _ (hc _).1).unique (hc _) ?_
      rw [t.lin, ← Category.assoc]
      exact hr s _ _ (hc a))
    (fun s a => GlobalTheory.T.lieAlgebraSquaredLength_comp_pairing_hom hU hL (𝓞 K) C.P T.pol (t.ten.tmul a) (C.act.act (k a a)) C.v (τ₀ (k a a))
      (s.comp (algebraMap (𝓞 K) K)) (n s) _ inferInstance (C.act.hom _) (t.lam a a) (C.basis.1 0) (hτ₀ _)
      (((hn s).2 _).2 rfl) (HermNorm.isLieNormSq_form hU hL K T.pol F h hh s _ _ (hc a)))
  have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  rw [GlobalTheory.T.two_mul_deg_dual_line_cmIdeal E K _ h _ v τ' 𝔞 β n h𝔞 hv0 (fun s => (hn s).1) hβ' hvn fun z => ?_, hnorm, ← hx]
  · field_simp
    ring
  · rw [(hr' τ z).1, hlat]
    refine Iff.trans (and_congr_right fun _ => forall_congr' fun a => by rw [hτ']; rfl) ((hv z).trans ?_)
    refine exists_congr fun s => and_congr_right fun _ => ⟨fun h1 b hb => ?_, fun h1 b => h1 _ ?_⟩
    · obtain ⟨a, rfl⟩ : b ∈ LinearMap.range e := hrange ▸ hb
      exact h1 a
    · exact (hrange.le ⟨b, rfl⟩ : e b ∈ (𝔞 : Submodule (𝓞 E) E))

end GlobalTheory.CM.TensorDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegreeEigenLatticeTensorRankOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_degree_eigenLattice_tensor_rankOne : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ω : 𝓞 K) (C : Ell H (𝓞 K) ω) (D : Datum H) (ε : ℤˣ) (hK : D.La → D.La → OK H) (T : PAT H (Sp (𝓞 K))) (x : ℝ), Splits E K → D.p + D.q = 1 → IsKForm D ε hK → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → Nonempty (IsTen C D hK T) → C.HasPeriod x → ∀ (F : GenFib T.pol) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.w0 = ω → 2 * deg h (F.eigLat T.t.act τ) = x + Real.log H.d / 2 - Real.log (NumberField.rootDiscr E) := by
  first | exact @GlobalTheory.CM.TensorDeg.two_mul_deg_eigLat | exact GlobalTheory.CM.TensorDeg.two_mul_deg_eigLat | (intros; apply GlobalTheory.CM.TensorDeg.two_mul_deg_eigLat <;> assumption)
end
