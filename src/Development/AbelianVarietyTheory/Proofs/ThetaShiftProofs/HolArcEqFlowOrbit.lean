module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecScalOfIsPullSec
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfTraceLattice
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ArcQ
open ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing hiding cc_mul

namespace GlobalTheory.ArcFlow

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma trace_cc (z : E) : Algebra.trace ℚ E (cc z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

lemma eq_zero_of_trace_mul (z : E) (h : ∀ β : 𝓞 E, Algebra.trace ℚ E ((β : E) * z) = 0) : z = 0 := by
  have := eq_zero_of_trace (cc z) fun β => by rw [← cc_mul, trace_cc, h]
  simpa using this

lemma map_cc (τ : E →+* ℂ) (z : E) : τ (cc z) = starRingEnd ℂ (τ z) :=
  IsCMField.complexEmbedding_complexConj E τ z

lemma re_nonneg_of_trace (s : E)
    (h : ∀ a : 𝓞 E, 0 ≤ Algebra.trace ℚ E (s * (a : E) * cc (a : E))) (τ : E →+* ℂ) : 0 ≤ (τ s).re := by
  classical
  by_contra hneg
  push Not at hneg
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit E (InfinitePlace.mk τ)
  have hlt : ∀ w : InfinitePlace E, w ≠ InfinitePlace.mk τ → w ((u : 𝓞 E) : E) < 1 := fun w hw =>
    (Real.log_neg_iff (NumberField.Units.pos_at_place u w)).1 (hu w hw)
  have hge : 1 ≤ InfinitePlace.mk τ ((u : 𝓞 E) : E) :=
    InfinitePlace.one_le_of_lt_one (a := (u : 𝓞 E)) u.ne_zero (fun z hz => hlt z hz)
  have htr : ∀ n : ℕ, 0 ≤ ∑ φ : E →+* ℂ, (φ s).re * (InfinitePlace.mk φ ((u : 𝓞 E) : E) ^ 2) ^ n := by
    intro n
    have h1 := h ((u : 𝓞 E) ^ n)
    have h2 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E)
      (x := s * (((u : 𝓞 E) ^ n : 𝓞 E) : E) * cc (((u : 𝓞 E) ^ n : 𝓞 E) : E))
    rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ)
      (fun φ : E →+* ℂ => φ (s * (((u : 𝓞 E) ^ n : 𝓞 E) : E) * cc (((u : 𝓞 E) ^ n : 𝓞 E) : E))) _
      (fun _ => rfl)] at h2
    have h3 := congrArg Complex.re h2
    rw [Complex.re_sum] at h3
    have h4 : (0 : ℝ) ≤ (algebraMap ℚ ℂ (Algebra.trace ℚ E
      (s * (((u : 𝓞 E) ^ n : 𝓞 E) : E) * cc (((u : 𝓞 E) ^ n : 𝓞 E) : E)))).re := by
      rw [eq_ratCast, Complex.ratCast_re]; exact_mod_cast h1
    rw [h3] at h4
    refine h4.trans_eq (Finset.sum_congr rfl fun φ _ => ?_)
    rw [map_mul, map_mul, map_cc, mul_assoc, Complex.mul_conj, Complex.re_mul_ofReal, Complex.normSq_eq_norm_sq,
      InfinitePlace.apply]
    push_cast
    rw [map_pow, norm_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
  let g : (E →+* ℂ) → ℕ → ℝ := fun φ n => if InfinitePlace.mk φ = InfinitePlace.mk τ then
    (if φ = τ then (τ s).re else |(φ s).re| * 0) else (φ s).re * (InfinitePlace.mk φ ((u : 𝓞 E) : E) ^ 2) ^ n
  have hle : ∀ n φ, (φ s).re * (InfinitePlace.mk φ ((u : 𝓞 E) : E) ^ 2) ^ n ≤ g φ n := by
    intro n φ
    simp only [g]
    split_ifs with h1 h2
    · subst h2
      have : 1 ≤ (InfinitePlace.mk φ ((u : 𝓞 E) : E) ^ 2) ^ n := one_le_pow₀ (one_le_pow₀ hge)
      nlinarith
    · have hre : (φ s).re = (τ s).re := by
        rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
        · rw [h]
        · rw [← h]; simp
      rw [hre, mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hneg.le (by positivity)
    · exact le_rfl
  have hlim : Filter.Tendsto (fun n => ∑ φ, g φ n) Filter.atTop
      (nhds (∑ φ : E →+* ℂ, if φ = τ then (τ s).re else 0)) := by
    refine tendsto_finsetSum _ fun φ _ => ?_
    simp only [g]
    by_cases h1 : InfinitePlace.mk φ = InfinitePlace.mk τ
    · simp only [if_pos h1, mul_zero]; exact tendsto_const_nhds
    · have h2 : φ ≠ τ := fun h => h1 (by rw [h])
      simp only [if_neg h1, if_neg h2]
      have h3 := hlt _ h1
      have h4 := apply_nonneg (InfinitePlace.mk φ) ((u : 𝓞 E) : E)
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := InfinitePlace.mk φ ((u : 𝓞 E) : E) ^ 2)
        (by positivity) (by nlinarith)).const_mul (φ s).re
      simpa using this
  have := ge_of_tendsto' hlim fun n => (htr n).trans (Finset.sum_le_sum fun φ _ => hle n φ)
  simp at this
  linarith


omit [IsCMField E] in
lemma cross_eq {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Finite ℤ Y]
    (hY : Module.finrank (𝓞 E) Y = 1) (η η' : Module.Dual ℤ Y) (x x' : Y) :
    pairE (E := E) η x * pairE η' x' = pairE η x' * pairE η' x := by
  haveI : Module.Finite (𝓞 E) Y := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hni : ¬ LinearIndependent (𝓞 E) ![x, x'] := fun h => by
    have := h.fintype_card_le_finrank
    rw [hY] at this
    simp at this
  rw [LinearIndependent.pair_iff] at hni
  push Not at hni
  obtain ⟨a, b, hab, hne⟩ := hni
  have key : ∀ θ : Module.Dual ℤ Y, (a : E) * pairE θ x + (b : E) * pairE θ x' = 0 := fun θ => by
    obtain ⟨h1, h2, -⟩ := pairE_properties E Y θ
    have h0 : pairE (E := E) θ (0 : Y) = 0 := by simpa using h1 0 0
    rw [← h1, ← h1, ← h2, hab, h0]
  have k1 := key η
  have k2 := key η'
  by_cases ha : a = 0
  · have hb : (b : E) ≠ 0 := by simpa using hne ha
    have ha' : (a : E) = 0 := by simp [ha]
    apply mul_left_cancel₀ hb
    rw [ha'] at k1 k2
    linear_combination (pairE η x) * k2 - (pairE η' x) * k1
  · have ha' : (a : E) ≠ 0 := by simpa using ha
    apply mul_left_cancel₀ ha'
    linear_combination (pairE η' x') * k1 - (pairE η x') * k2

variable {r : ℕ} (X : Data E r)

lemma eq_zero_of_herm_lattice (w : Fin r → E) (h : ∀ v ∈ X.Λ, herm X.Gm w v = 0) : w = 0 := by
  refine eq_zero_of_herm X.Gm X.Gm_det w fun y => ?_
  obtain ⟨d, hd, hy⟩ := exists_smul_mem (R := 𝓞 E) (F := E) X.Λ (x := y) (by rw [X.Λ_span]; trivial)
  have h1 := h _ hy
  rw [show d • y = (d : E) • y from rfl, herm_smul_right] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd (by simpa using h2) hd
  · exact h2

lemma eq_zero_of_trace_lattice (w : Fin r → E)
    (h : ∀ v ∈ X.Λ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm w v) = 0) : w = 0 := by
  refine eq_zero_of_herm_lattice X w fun v hv => ?_
  have := eq_zero_of_trace (X.ξ0 * herm X.Gm w v) fun β => by
    have h1 := h _ (X.Λ.smul_mem β hv)
    rw [show β • v = (β : E) • v from rfl, herm_smul_right] at h1
    rw [← h1]; congr 1; ring
  exact (mul_eq_zero.1 this).resolve_left X.ξ0_ne

lemma transvMat_mulVec (G : Matrix (Fin r) (Fin r) E) (ξ v : Fin r → E) (α : E) :
    (transvMat G ξ α).mulVec v - v = (α * herm G v ξ) • ξ := by
  funext a
  simp only [transvMat, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    herm, add_sub_cancel_left, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

section Lattice

variable {La Y : Type} [AddCommGroup La] [Module (𝓞 E) La] [AddCommGroup Y] [Module (𝓞 E) Y]
  (φ : La ≃ₗ[𝓞 E] X.Λ) (EF : LinearMap.BilinForm ℤ La)
  (iso : ∀ a b, ((EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
  (y : La →ₗ[𝓞 E] Y)

include iso in
lemma pairE_eq (t : La) (η : Module.Dual ℤ Y) (ht : ∀ v, -EF t v = η (y v)) (v : La) :
    pairE η (y v) = -X.ξ0 * herm X.Gm (φ v : Fin r → E) (φ t) := by
  obtain ⟨h1, -, h3, -⟩ := pairE_properties E Y η
  rw [← sub_eq_zero]
  refine eq_zero_of_trace_mul _ fun β => ?_
  rw [mul_sub, map_sub, ← h1, h3, ← map_smul, ← ht, Int.cast_neg, iso, ← trace_cc, cc_mul, cc_neg, X.ξ0_im,
    herm_conj _ X.Gm_herm, map_smul, show ((β • φ v : X.Λ) : Fin r → E) = (β : E) • (φ v : Fin r → E) from rfl,
    herm_smul_left, ← map_neg, ← map_sub, ← map_zero (Algebra.trace ℚ E)]
  congr 1; ring


include iso in
theorem rank_one [Module.Finite ℤ Y] (hY : Module.finrank (𝓞 E) Y = 1) (hκ : X.κ0 = 2 * X.ξ0)
    (hy : Function.Surjective y) (be : LinearMap.BilinForm ℤ Y) (hsym : ∀ a b, be a b = be b a)
    (hpos : ∀ a, a ≠ 0 → 0 < be a a) (nn : La →ₗ[𝓞 E] La) (hnn : ∀ v v', -EF (nn v) v' = be (y v) (y v'))
    (hrep : ∀ η : Module.Dual ℤ Y, ∃ t, ∀ v, -EF t v = η (y v))
    (ξ : Module.Dual ℤ Y) (hξ : ξ ≠ 0) (t : La) (ht : ∀ v, -EF t v = ξ (y v)) (hyt : y t = 0) :
    ∃ sE : E, X.IsIso (φ t : Fin r → E) ∧ IsBePar ξ be sE ∧ (∀ τ : E →+* ℂ, 0 < (τ sE).re) ∧
      (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ X.Λ, ∃ u ∈ X.Λ,
        (transvMat X.Gm (φ t : Fin r → E) (s * X.κ0)).mulVec v - v = (N : E) • u) ∧
      ∀ v, (φ (nn v) : Fin r → E) =
        (-(sE * X.κ0 * herm X.Gm (φ v : Fin r → E) (φ t))) • (φ t : Fin r → E) := by
  obtain ⟨p1, p2, p3, -⟩ := pairE_properties E Y ξ
  have hp := pairE_eq X φ EF iso y t ξ ht
  have hpn : ∀ v v', pairE (be (y v)) (y v') = -X.ξ0 * herm X.Gm (φ v' : Fin r → E) (φ (nn v)) :=
    fun v => pairE_eq X φ EF iso y (nn v) (be (y v)) (hnn v)
  have hξ0 := X.ξ0_ne
  have hc0 := X.ξ0_im
  have hcj := herm_conj X.Gm X.Gm_herm
  have hΛ : ∀ w ∈ X.Λ, ∃ v, (φ v : Fin r → E) = w := fun w hw => ⟨φ.symm ⟨w, hw⟩, by simp⟩
  have hsm : ∀ (β : 𝓞 E) v, (φ (β • v) : Fin r → E) = (β : E) • (φ v : Fin r → E) := fun β v => by
    rw [map_smul]; rfl
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, ξ (y v₀) ≠ 0 := by
    by_contra h
    push Not at h
    exact hξ (LinearMap.ext fun x => by obtain ⟨v, rfl⟩ := hy x; exact h v)
  have hp₀ : pairE (E := E) ξ (y v₀) ≠ 0 := fun h => by
    have := p3 (y v₀)
    rw [h, map_zero] at this
    exact hv₀ (by exact_mod_cast this.symm)
  set ξ' : Fin r → E := (φ t).1 with hξ'
  have hh₀ : herm X.Gm (φ v₀ : Fin r → E) ξ' ≠ 0 := fun h => hp₀ (by rw [hp, h, mul_zero])
  have hh₀' : herm X.Gm ξ' (φ v₀ : Fin r → E) ≠ 0 := by rw [← hcj]; simpa using hh₀
  have hskew : ∀ v v', herm X.Gm (φ (nn v) : Fin r → E) (φ v') = -herm X.Gm (φ v : Fin r → E) (φ (nn v')) := by
    intro v v'
    have : X.ξ0 * (herm X.Gm (φ (nn v) : Fin r → E) (φ v') + herm X.Gm (φ v : Fin r → E) (φ (nn v'))) = 0 := by
      refine eq_zero_of_trace_mul _ fun β => ?_
      have e1 : ((EF (nn (β • v)) v' : ℤ) : ℚ) = EF (nn v') (β • v) := by
        have := (hnn (β • v) v').trans ((hsym _ _).trans (hnn v' (β • v)).symm)
        exact_mod_cast neg_injective this
      rw [iso, iso, ← trace_cc (-X.ξ0 * herm X.Gm (φ (nn v') : Fin r → E) _), cc_mul, cc_neg, hc0, hcj,
        map_smul nn, hsm, hsm, herm_smul_left, herm_smul_left, ← sub_eq_zero, ← map_sub] at e1
      rw [← neg_eq_zero, ← map_neg, ← e1]
      congr 1; ring
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 this).resolve_left hξ0)
  have hmul : ∀ v, (φ (nn v) : Fin r → E) =
      (herm X.Gm (φ (nn v) : Fin r → E) (φ v₀) / herm X.Gm ξ' (φ v₀)) • ξ' := by
    intro v
    rw [← sub_eq_zero]
    refine eq_zero_of_herm_lattice X _ fun w hw => ?_
    obtain ⟨v', rfl⟩ := hΛ w hw
    have e := cross_eq (E := E) hY (be (y v)) ξ (y v') (y v₀)
    rw [hpn, hpn, hp, hp] at e
    have e' := congrArg cc e
    simp only [cc_mul, cc_neg, hc0, hcj, neg_neg] at e'
    rw [herm_sub_left, herm_smul_left]
    field_simp
    apply mul_left_cancel₀ (mul_ne_zero hξ0 hξ0)
    linear_combination e'
  obtain ⟨α, hα⟩ : ∃ α : E, ∀ v, (φ (nn v) : Fin r → E) = (α * herm X.Gm (φ v : Fin r → E) ξ') • ξ' := by
    refine ⟨-cc (herm X.Gm (φ (nn v₀) : Fin r → E) (φ v₀) / herm X.Gm ξ' (φ v₀)) / herm X.Gm ξ' (φ v₀),
      fun v => ?_⟩
    rw [hmul v, hskew v v₀]
    conv_lhs => rw [hmul v₀, herm_smul_right]
    congr 1; ring
  have hαc : cc α = -α := by
    have e := hskew v₀ v₀
    rw [hα, herm_smul_left, herm_smul_right, cc_mul, hcj] at e
    apply mul_left_cancel₀ (mul_ne_zero hh₀ hh₀')
    linear_combination e
  have hκ0 : X.κ0 ≠ 0 := by rw [hκ]; exact mul_ne_zero two_ne_zero hξ0
  have hcc2 : cc (2 : E) = 2 := by exact_mod_cast cc_natCast (E := E) 2
  have hsc : cc (-α / X.κ0) = -α / X.κ0 := by
    rw [div_eq_mul_inv, cc_mul, cc_neg, hαc, cc_inv, hκ, cc_mul, hcc2, hc0]
    field_simp
  have htr : ∀ (s : E) v v', Algebra.trace ℚ E (2 * s * pairE ξ (y v) * cc (pairE ξ (y v'))) =
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm ((s * X.κ0 * herm X.Gm (φ v : Fin r → E) ξ') • ξ') (φ v')) := by
    intro s v v'
    rw [hp, hp, cc_mul, cc_neg, hc0, hcj, herm_smul_left, hκ]
    congr 1; ring
  have hbe : IsBePar ξ be (-α / X.κ0) := by
    refine ⟨hsc, fun x x' => ?_⟩
    obtain ⟨v, rfl⟩ := hy x
    obtain ⟨v', rfl⟩ := hy x'
    rw [htr, ← hnn, Int.cast_neg, iso, hα v, ← map_neg, herm_smul_left, herm_smul_left]
    congr 1; field_simp
  refine ⟨-α / X.κ0, ⟨(φ t).2, ?_, fun h => hh₀ ?_⟩, hbe, fun τ => ?_, fun N s hs w hw => ?_, fun v => ?_⟩
  · have e := hp t
    have h0 : pairE (E := E) ξ (0 : Y) = 0 := by simpa using p1 0 0
    rw [hyt, h0] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (neg_ne_zero.2 hξ0)
  · rw [h]; simp [herm]
  · set sE := -α / X.κ0
    have hs0 : sE ≠ 0 := fun h => by
      have e := hbe.2 (y v₀) (y v₀)
      have := hpos (y v₀) fun h => hv₀ (by rw [h, map_zero])
      rw [h] at e
      simp only [mul_zero, zero_mul, map_zero] at e
      have e' : be (y v₀) (y v₀) = 0 := by exact_mod_cast e.symm
      omega
    have h1 := re_nonneg_of_trace (2 * sE * pairE ξ (y v₀) * cc (pairE ξ (y v₀))) (fun a => by
      have e := hbe.2 (a • y v₀) (a • y v₀)
      rw [p1, cc_mul] at e
      have h2 : (0 : ℤ) ≤ be (a • y v₀) (a • y v₀) := by
        by_cases h : a • y v₀ = 0
        · simp [h]
        · exact (hpos _ h).le
      have h3 : (0 : ℚ) ≤ (be (a • y v₀) (a • y v₀) : ℤ) := by exact_mod_cast h2
      rw [← e] at h3
      refine h3.trans_eq ?_
      congr 1; ring) τ
    have him : (τ sE).im = 0 := by
      have := map_cc τ sE
      rw [hsc] at this
      exact Complex.conj_eq_iff_im.1 this.symm
    have hre : (τ sE).re ≠ 0 := fun h => hs0 (τ.injective (by rw [map_zero]; exact Complex.ext h him))
    have hn : 0 < Complex.normSq (τ (pairE ξ (y v₀))) := Complex.normSq_pos.2 ((map_ne_zero τ).2 hp₀)
    rw [map_mul, map_mul, map_mul, map_cc, mul_assoc, Complex.mul_conj, Complex.re_mul_ofReal, map_ofNat] at h1
    have h4 : ((2 : ℂ) * τ sE).re = 2 * (τ sE).re := by simp
    rw [h4] at h1
    have : 0 ≤ (τ sE).re := by
      by_contra hh
      push Not at hh
      nlinarith
    exact lt_of_le_of_ne this hre.symm
  · obtain ⟨v, rfl⟩ := hΛ w hw
    obtain ⟨η, hη⟩ : ∃ η : Module.Dual ℤ Y, ∀ x,
        Algebra.trace ℚ E (2 * s * pairE ξ (y v) * cc (pairE ξ x)) = (N : ℚ) * η x := by
      by_cases hN : N = 0
      · refine ⟨0, fun x => ?_⟩
        obtain ⟨m, hm⟩ := hs.2 (y v) x
        rw [hm, hN]; simp
      · choose m hm using hs.2 (y v)
        have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
        refine ⟨(AddMonoidHom.mk' m fun a b => ?_).toIntLinearMap, hm⟩
        have e := hm (a + b)
        rw [p2, cc_add, mul_add, map_add (f := _), hm, hm, ← mul_add] at e
        exact_mod_cast (mul_left_cancel₀ hN' e).symm
    obtain ⟨t', ht'⟩ := hrep η
    refine ⟨-(φ t' : Fin r → E), X.Λ.neg_mem (φ t').2, ?_⟩
    rw [transvMat_mulVec, ← sub_eq_zero]
    refine eq_zero_of_trace_lattice X _ fun w hw => ?_
    obtain ⟨v', rfl⟩ := hΛ w hw
    have e := hη (y v')
    rw [htr, ← ht', Int.cast_neg, iso, ← map_neg, ← nsmul_eq_mul, ← map_nsmul, ← sub_eq_zero, ← map_sub] at e
    rw [← neg_eq_zero, ← map_neg, ← e, herm_sub_left, smul_neg, ← neg_smul, herm_smul_left X.Gm (-(N : E))]
    congr 1; rw [nsmul_eq_mul]; ring
  · rw [hα v]
    congr 1; field_simp

end Lattice

end GlobalTheory.ArcFlow
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.L2.Pj hiding perFr Unf relab toC gxFst gxSnd GoodEmb
open scoped LaurentSeries Matrix

namespace GlobalTheory.ArcFlow

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Frames

variable {r : ℕ} (X : Data E r)

lemma perFr_smul (x : Frame X.Ψ r) (a : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x (a • v) τ i = τ a * perFr X x v τ i := by
  have hemb : ∀ ρ : E →+* ℂ, Data.emb ρ (a • v) = ρ a • Data.emb ρ v := fun ρ => by
    funext k; simp [Data.emb]
  unfold perFr
  split_ifs
  · rw [hemb, Matrix.mulVec_smul]; rfl
  · simp
  · rw [hemb, hermC_smul_right]; simp [conjEmb]
  · simp
  · simp

lemma eq_of_hermC_lattice (τ : E →+* ℂ) (u u' : Fin r → ℂ)
    (h : ∀ v ∈ X.Λ, hermC τ X.Gm u (Data.emb τ v) = hermC τ X.Gm u' (Data.emb τ v)) : u = u' := by
  have h1 : ∀ v, hermC τ X.Gm u (Data.emb τ v) = hermC τ X.Gm u' (Data.emb τ v) := fun v => by
    obtain ⟨d, hd, hv⟩ := HermitianTraceFormVanishing.exists_smul_mem (R := 𝓞 E) (F := E) X.Λ (x := v) (by rw [X.Λ_span]; trivial)
    have h2 := h _ hv
    have hemb : Data.emb τ (d • v) = τ d • Data.emb τ v := by
      funext k; simp [Data.emb, Algebra.smul_def]
    rw [hemb, hermC_smul_right, hermC_smul_right] at h2
    refine mul_left_cancel₀ ?_ h2
    simpa using hd
  have hdet : (X.Gm.map τ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; simpa using X.Gm_det
  rw [← sub_eq_zero]
  apply Matrix.eq_zero_of_vecMul_eq_zero hdet
  funext b
  have h2 := h1 (Pi.single b 1)
  simp only [hermC, Data.emb, Pi.single_apply, apply_ite τ, apply_ite (starRingEnd ℂ), map_one, map_zero,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  simp [Matrix.vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib, h2]

lemma flow_mem_dom {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) (h : ∀ (τ : X.Ψ) (a : Fin r), (a : ℕ) < X.p0 →
      FD.col (mat (X.flow ξ s x) τ) a = FD.col (mat x' τ) a) : X.flow ξ s x ∈ X.dom := by
  refine AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩
  · have hm : mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl
    rw [hm, Matrix.det_mul]
    refine mul_ne_zero (fun h0 => ?_) (hx τ).1
    have := congrArg Matrix.det (EmbeddingHermitianPairs.flowMat_mul X hξ τ (s τ) (-s τ))
    rw [add_neg_cancel, EmbeddingHermitianPairs.flowMat_zero, Matrix.det_mul, h0] at this
    simp at this
  · have hg : X.gramPos (X.flow ξ s x) τ = X.gramPos x' τ := by
      ext a b
      rw [Data.gramPos_apply, Data.gramPos_apply]
      unfold Data.colP
      rw [h τ _ a.2, h τ _ b.2]
    rw [hg]
    exact X.gramPos_posDef hx' τ

end Frames

lemma exists_comb_single {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (z : ∀ τ : T, Fin (m τ) → (Fin g → ℂ))
    (hz : ∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (e jj).1 = τ) (j : Fin g) :
    ∃ a : Fin (m (e j).1) → ℂ, ∑ i, a i • z (e j).1 i = Pi.single j 1 := by
  classical
  obtain ⟨⟨τ, k⟩, rfl⟩ := e.symm.surjective j
  rw [Equiv.apply_symm_apply]
  dsimp only
  let A : Matrix (Fin (m τ)) (Fin (m τ)) ℂ := Matrix.of fun i i' => z τ i (e.symm ⟨τ, i'⟩)
  have hext : ∀ (a : Fin (m τ) → ℂ) (u : Fin g → ℂ), (∀ jj, u jj ≠ 0 → (e jj).1 = τ) →
      (∀ i', Matrix.vecMul a A i' = u (e.symm ⟨τ, i'⟩)) → ∑ i, a i • z τ i = u := by
    intro a u hu h
    funext jj
    obtain ⟨⟨τ', k'⟩, rfl⟩ := e.symm.surjective jj
    by_cases hτ : τ' = τ
    · subst hτ
      rw [← h]
      simp [A, Matrix.vecMul, dotProduct, Finset.sum_apply]
    · have h1 : u (e.symm ⟨τ', k'⟩) = 0 := by
        by_contra hh; exact hτ (by simpa using hu _ hh)
      rw [h1, Finset.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have h2 : z τ i (e.symm ⟨τ', k'⟩) = 0 := by
        by_contra hh; exact hτ (by simpa using (hz τ).2 i _ hh)
      simp [h2]
  have hinj : Function.Injective A.vecMul := by
    intro a a' haa
    have h0 : ∑ i, (a - a') i • z τ i = 0 := hext _ 0 (fun _ h => absurd rfl h) fun i' => by
      rw [Matrix.sub_vecMul]; simp [show Matrix.vecMul a A = Matrix.vecMul a' A from haa]
    have := Fintype.linearIndependent_iff.1 (hz τ).1 _ h0
    exact sub_eq_zero.1 (funext this)
  obtain ⟨a, ha⟩ := Matrix.vecMul_surjective_iff_isUnit.2 (Matrix.vecMul_injective_iff_isUnit.1 hinj)
    (Pi.single k 1)
  refine ⟨a, hext a _ (fun jj hjj => ?_) fun i' => ?_⟩
  · by_contra hne
    exact hjj (Pi.single_eq_of_ne (fun hh => hne (by rw [hh, Equiv.apply_symm_apply])) _)
  · rw [show Matrix.vecMul a A = Pi.single k 1 from ha]
    by_cases h : i' = k
    · subst h; simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne fun hh => h (by simpa using hh)]

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (Uw : UnfWit U)

lemma exists_comp (hL : Out.Laws) (hU : IsUnf U) (i : Fin Uw.F.n) (P : (Uw.F.Di i).La →+ (Fin Uw.g → ℂ))
    (hP : IsPeriod (Uw.F.Di i) (fun j => relab c σ (Uw.e j).1) P) :
    ∃ k, Uw.ik k = i ∧ Nonempty (U.X k).dom := by
  obtain ⟨u, -, h2, h3, h4⟩ := GlobalTheory.LieFrame.exists_eigenbasis E H Dw l Xo c σ Uw.g Uw.e Uw.F i P hP
  obtain ⟨g, hg, θ, hθ⟩ := GlobalTheory.Frames.exists_local_generator hL.secBaseChange E H Dw l Xo ℂ (Uw.F.u i P)
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hg' : IsUnit ((RingHom.id ℂ) g) := isUnit_iff_ne_zero.2 fun h => hg h
  let ψ : Localization.Away g →+* ℂ := IsLocalization.Away.lift g hg'
  have hψ : ψ.comp (algebraMap ℂ (Localization.Away g)) = RingHom.id ℂ := IsLocalization.Away.lift_comp g hg'
  have hx : Uw.F.u i P = spMap ψ ≫ spMap (algebraMap ℂ (Localization.Away g)) ≫ Uw.F.u i P := by
    have : spMap ψ ≫ spMap (algebraMap ℂ (Localization.Away g)) = 𝟙 _ := by
      unfold spMap
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      exact Spec.map_id _
    rw [← Category.assoc, this, Category.id_comp]
  obtain ⟨θ', hθ', -⟩ := GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo _ _ ψ 1 _ _ hx θ
  have hgen := (hθ ℂ ψ _ θ' hx hθ').1
  let y : FrPt Xo c (CAt σ) := ⟨Uw.F.u i P, Uw.F.over_σ i P hP, u, h2, h3, h4, θ', hgen⟩
  obtain ⟨k, x, t, ht⟩ := hU.2.2.1 y
  exact ⟨k, Uw.F.disj _ _ _ _ (Uw.period k x) hP ((Uw.lie k x).1.symm.trans ht.1.symm), ⟨x⟩⟩

lemma exists_idx (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) :
    ∃ idx : Fin Uw.g ≃ (U.X k).Ψ × Fin r,
      (∀ j, relab c σ (Uw.e j).1 =
        if ((idx j).2 : ℕ) < Dw.q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧
      (∀ j, ((idx j).2 : ℕ) < Dw.q → ((Uw.e j).2 : ℕ) < Dw.q) ∧
      ∀ (x : Frame (U.X k).Ψ r) (v : Fin r → E) j, perFr (U.X k) x v (relab c σ (Uw.e j).1) (Uw.e j).2 =
        if ((idx j).2 : ℕ) < Dw.q then
          hermC (idx j).1.1 (U.X k).Gm (FD.col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
        else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij
    Dw.mult (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
      (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin Uw.g ≃ (U.X k).Ψ × Fin r, ∀ j,
      (relab c σ (Uw.e j).1 ∈ (U.X k).Ψ ∧ (idx j).1.1 = relab c σ (Uw.e j).1 ∧
        ((idx j).2 : ℕ) = Dw.q + (Uw.e j).2) ∨
      (relab c σ (Uw.e j).1 ∉ (U.X k).Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (Uw.e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (Uw.e j).2 ∧ ((Uw.e j).2 : ℕ) < Dw.q) :=
    ⟨Uw.e.trans f, fun j => hf (Uw.e j)⟩
  refine ⟨idx, fun j => ?_, fun j hj => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · omega
    · exact d
  · have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rw [← hp0] at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ (Uw.e j).1) ∈ (U.X k).Ψ from hτ), dite_eq_left hn]
      rfl

lemma exists_frame (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (hκ : (U.X k).κ0 = 2 * (U.X k).ξ0)
    (P : (Uw.F.Di (Uw.ik k)).La →+ (Fin Uw.g → ℂ))
    (hP : IsPeriod (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) P) : ∃ x, Uw.Pm k x = P := by
  obtain ⟨idx, hty, -, hper⟩ := exists_idx Uw hσ hU k
  obtain ⟨hp, hq⟩ := Uw.F.sig (Uw.ik k)
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  rw [← hq] at hty hper hp0
  let φ : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (Uw.φ k).toLinearMap
  have hrange : LinearMap.range φ = (U.X k).Λ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨x, hx, h⟩ := exists_frame_of_isPeriod E H (Uw.F.Di (Uw.ik k)) r (-(U.X k).ξ0) (U.X k).Gm φ (U.X k).Ψ hΨ
    Uw.g idx _ hty (by rw [HermitianTraceFormVanishing.cc_neg, (U.X k).ξ0_im]) (fun τ hτ => by
      have := (U.X k).κ0_sign ⟨τ, hτ⟩
      rw [hκ, map_mul, map_ofNat] at this
      simp at this ⊢
      linarith)
    ⟨Subtype.val_injective.comp (Uw.φ k).injective, by rw [← LinearMap.coe_range, hrange]; exact (U.X k).Λ_span,
      (U.X k).Gm_herm, (U.X k).Gm_det, Uw.iso k⟩ (by rw [hp, hq]; exact hU.1) P hP
  rw [← hp0] at hx
  exact ⟨⟨x, hx⟩, AddMonoidHom.ext fun v => funext fun j =>
    (Uw.Pm_eq k _ v j).trans ((hper x _ j).trans (h v j).symm)⟩

lemma flow_period (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (hκ : (U.X k).κ0 = 2 * (U.X k).ξ0)
    (nn : (Uw.F.Di (Uw.ik k)).La → (Uw.F.Di (Uw.ik k)).La) (ξ' : Fin r → E) (hξ' : herm (U.X k).Gm ξ' ξ' = 0)
    (sE : E) (hs : cc sE = sE)
    (hnn : ∀ v, (Uw.φ k (nn v) : Fin r → E) =
      (-(sE * (U.X k).κ0 * herm (U.X k).Gm (Uw.φ k v : Fin r → E) ξ')) • ξ')
    (x : (U.X k).dom) (d : ℂ) (P : (Uw.F.Di (Uw.ik k)).La →+ (Fin Uw.g → ℂ))
    (hP : IsPeriod (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) P)
    (hPx : ∀ v, P v = Uw.Pm k x v + d • Uw.Pm k x (nn v)) :
    ∃ hx : (U.X k).flow ξ' (fun τ => d * ((τ.1 sE).re : ℂ)) x.1 ∈ (U.X k).dom, Uw.Pm k ⟨_, hx⟩ = P := by
  obtain ⟨idx, hty, hlt, hper⟩ := exists_idx Uw hσ hU k
  obtain ⟨hp0, -⟩ := hU.2.1 k
  have hre : ∀ τ : E →+* ℂ, ((τ sE).re : ℂ) = τ sE := fun τ => by
    have := map_cc τ sE
    rw [hs] at this
    exact Complex.conj_eq_iff_re.1 this.symm
  have key : ∀ v j, perFr (U.X k) ((U.X k).flow ξ' (fun τ => d * ((τ.1 sE).re : ℂ)) x.1)
      (Uw.φ k v : Fin r → E) (relab c σ (Uw.e j).1) (Uw.e j).2 = P v j := by
    intro v j
    rw [hPx, Pi.add_apply, Pi.smul_apply, Uw.Pm_eq, Uw.Pm_eq, hnn, perFr_smul, hty j]
    split_ifs with hj
    · have h := GlobalTheory.PerFlow.flow_conj (U.X k) ξ' (fun τ => d * ((τ.1 sE).re : ℂ)) x.1 (Uw.φ k v : Fin r → E)
        (idx j).1 (Uw.e j).2 (hp0 ▸ hlt j hj)
      have h2 : conjEmb (idx j).1.1 sE = (((idx j).1.1 sE).re : ℂ) := by
        rw [← hre (conjEmb (idx j).1.1)]; simp [conjEmb]
      change perFr _ _ _ (conjEmb (idx j).1.1) _ = perFr _ _ _ (conjEmb (idx j).1.1) _ +
        d • (conjEmb (idx j).1.1 _ * perFr _ _ _ (conjEmb (idx j).1.1) _)
      rw [h, mul_assoc sE, map_neg, map_mul _ sE, h2, smul_eq_mul]
      ring
    · rw [GlobalTheory.PerFlow.flow_mem (U.X k) hξ', mul_assoc sE, map_neg, map_mul _ sE, hre, smul_eq_mul]
      ring
  obtain ⟨x', hx'⟩ := exists_frame Uw hσ hU k hκ P hP
  have hx : (U.X k).flow ξ' (fun τ => d * ((τ.1 sE).re : ℂ)) x.1 ∈ (U.X k).dom := by
    refine flow_mem_dom (U.X k) hξ' _ x.2 x'.2 fun τ a ha => eq_of_hermC_lattice (U.X k) τ.1 _ _ fun w hw => ?_
    have h1 := key ((Uw.φ k).symm ⟨w, hw⟩) (idx.symm (τ, a))
    rw [← hx', Uw.Pm_eq, hper, hper] at h1
    rw [hp0] at ha
    simpa only [Equiv.apply_symm_apply, if_pos ha, LinearEquiv.apply_symm_apply] using h1
  exact ⟨hx, AddMonoidHom.ext fun v => funext fun j => (Uw.Pm_eq k _ v j).trans (key v j)⟩

lemma orbit (hL : Out.Laws) (hσ : GoodEmb c σ) (hU : IsUnf U) {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite ℤ Y] (hY : Module.finrank (𝓞 E) Y = 1) (be : LinearMap.BilinForm ℤ Y)
    (hsym : ∀ a b, be a b = be b a) (hpos : ∀ a, a ≠ 0 → 0 < be a a) (i : Fin Uw.F.n) (T : ℝ)
    (Pw : ℂ → ((Uw.F.Di i).La →+ (Fin Uw.g → ℂ))) (y : (Uw.F.Di i).La →ₗ[𝓞 E] Y) (hy : Function.Surjective y)
    (hPw : ∀ w : ℂ, T < w.im → IsPeriod (Uw.F.Di i) (fun j => relab c σ (Uw.e j).1) (Pw w))
    (nn : (Uw.F.Di i).La →ₗ[𝓞 E] (Uw.F.Di i).La)
    (hlin : ∀ w w₁ v, Pw w v = Pw w₁ v + (w - w₁) • Pw w₁ (nn v))
    (hnn : ∀ v v', -(Uw.F.Di i).EF (nn v) v' = be (y v) (y v'))
    (hker : ∀ t, (∀ v', y v' = 0 → (Uw.F.Di i).EF t v' = 0) → y t = 0)
    (hrep : ∀ η : Module.Dual ℤ Y, ∃ t, ∀ v', -(Uw.F.Di i).EF t v' = η (y v'))
    (ξ : Module.Dual ℤ Y) (hξ : ξ ≠ 0) (w₁ : ℂ) (hw₁ : T < w₁.im) :
    ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E), (U.X k).IsIso ξ' ∧ IsBePar ξ be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ ∀ (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ x ∈ (U.X k).dom, ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di i).EF t v' = ξ (y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') ∧ ∀ w : ℂ, T < w.im → ∃ hx : (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x ∈ (U.X k).dom, (∀ v, Uw.Pm k ⟨_, hx⟩ (γ v) = L (Pw w v)) ∧ AnLie Uw.F i (Pw w) (U.un k ⟨_, hx⟩) z := by
  classical
  obtain ⟨k, rfl, ⟨x₀⟩⟩ := exists_comp Uw hL hU i _ (hPw w₁ hw₁)
  obtain ⟨t, ht⟩ := hrep ξ
  have hyt : y t = 0 := hker t fun v' hv' => by
    have := ht v'
    rw [hv', map_zero] at this
    exact neg_eq_zero.1 this
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      have ht0 : t = 0 := (Uw.φ k).injective (Subtype.ext (Subsingleton.elim _ _))
      refine absurd (LinearMap.ext fun a => ?_) hξ
      obtain ⟨v, rfl⟩ := hy a
      rw [← ht, ht0]; simp
    · exact h
  obtain ⟨-, -, -, -, Hm, hHm⟩ := Uw.period k x₀
  have hκ := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k x₀ Hm hσ hU hHm).2.1 hr
  obtain ⟨sE, hiso, hbe, hsp, hlev, hform⟩ := rank_one (U.X k) (Uw.φ k) _ (Uw.iso k) y hY hκ hy be hsym hpos nn hnn
    hrep ξ hξ t ht hyt
  refine ⟨k, _, sE, hiso, hbe, fun τ => hsp τ.1, hlev, fun z hz => ?_⟩
  obtain ⟨V, hVu, hVt, hVw⟩ := GlobalTheory.CoverFrame.exists_inverse_block Uw.e (fun j => z (Uw.e j).1 (Uw.e j).2)
    (fun j => by
      obtain ⟨a, ha⟩ := exists_comb_single Uw.e z hz j
      refine ⟨a, ?_⟩
      rw [← ha]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Equiv.apply_symm_apply])
  have hVz : ∀ τ i, V *ᵥ z τ i = Pi.single (Uw.e.symm ⟨τ, i⟩) 1 := fun τ i => by
    have := hVw (Uw.e.symm ⟨τ, i⟩)
    rwa [Equiv.apply_symm_apply] at this
  have hP' : ∀ w : ℂ, T < w.im → ∃ P', IsPeriod (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) P' ∧
      ∀ a, P' a = V *ᵥ Pw w a := fun w hw =>
    GlobalTheory.PeriodLin.exists_period_mulVec E H _ _ _ _ V (hPw w hw) hVu (fun j j' h => by rw [hVt j j' h])
  obtain ⟨P₁, hP₁, hP₁e⟩ := hP' w₁ hw₁
  obtain ⟨x, hx⟩ := exists_frame Uw hσ hU k hκ P₁ hP₁
  have hu : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).2 hVu
  refine ⟨x.1, x.2, LinearEquiv.ofBijective V.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hu, Matrix.mulVec_surjective_iff_isUnit.2 hu⟩,
    LinearEquiv.refl _ _, fun _ _ => rfl, hVz, ⟨t, ht, rfl⟩, fun w hw => ?_⟩
  obtain ⟨P, hP, hPe⟩ := hP' w hw
  obtain ⟨hxw, hPw'⟩ := flow_period Uw hσ hU k hκ nn _ hiso.2.1 sE hbe.1 hform x (w - w₁) P hP fun v => by
    rw [hx, hPe, hP₁e, hP₁e, hlin w w₁ v, Matrix.mulVec_add, Matrix.mulVec_smul]
  obtain ⟨-, hpt, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ _ _ Uw.F _ (Pw w) P
    (LinearEquiv.refl _ _) V (hPw w hw) hP (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hPe
  have hlie := Uw.lie k ⟨_, hxw⟩
  rw [hPw'] at hlie
  refine ⟨hxw, fun v => by rw [hPw']; exact hPe v, hlie.1.trans hpt.symm, fun τ i => ?_⟩
  refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F _ _ (hPw w hw) _ P (Matrix.mulVecLin V) hP hex
    _ _).2 ?_
  rw [Matrix.mulVecLin_apply, hVz]
  exact hlie.2 τ i

theorem holArc_eq_flow_orbit : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F), GoodEmb c σ → IsUnf U → Module.finrank (𝓞 E) a.D₀.X = 1 → ∀ ξ : Module.Dual ℤ a.D₀.X, ξ ≠ 0 → ∀ w₁ : ℂ, Ha.T < w₁.im → ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E), (U.X k).IsIso ξ' ∧ IsBePar ξ a.be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ ∀ (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ x ∈ (U.X k).dom, ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') ∧ ∀ w : ℂ, Ha.T < w.im → ∃ hx : (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x ∈ (U.X k).dom, (∀ v, Uw.Pm k ⟨_, hx⟩ (γ v) = L (Ha.Pw w v)) ∧ AnLie Uw.F Ha.i (Ha.Pw w) (U.un k ⟨_, hx⟩) z := by
  intro hL _ E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha hσ hU hY ξ hξ w₁ hw₁
  obtain ⟨nn, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha
  refine orbit Uw hL hσ hU hY a.be a.be_symm a.be_pos Ha.i Ha.T Ha.Pw Ha.y Ha.y_onto Ha.period nn
    (fun w w₁ v => ?_) h2 h5 (fun η => (h6 η).exists) ξ hξ w₁ hw₁
  rw [Ha.Pw_eq, Ha.Pw_eq, Ha.Pw_eq, h1 (nn v), h4 _ (h3 v), map_zero, smul_zero, add_zero, ← h1, sub_smul]
  abel

end GlobalTheory.ArcFlow
