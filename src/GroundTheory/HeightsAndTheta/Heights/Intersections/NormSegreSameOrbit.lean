module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.CardLeRingKrullDim
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.NormSegreSameOrbit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

namespace PullbackDegreeCount

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem sameOrbit_self (z : (Σ k', ι' k') → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem sameOrbit_comp {a b c : (Σ k', ι' k') → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) :
    SameOrbit a c := by
  obtain ⟨s, hs, rfl⟩ := h1
  obtain ⟨t, ht, rfl⟩ := h2
  exact ⟨fun k => s k * t k, fun k => mul_ne_zero (hs k) (ht k), by funext p; simp [mul_assoc]⟩


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem sameOrbit_flip {a b : (Σ k', ι' k') → ℂ} (h : SameOrbit a b) : SameOrbit b a := by
  obtain ⟨s, hs, rfl⟩ := h
  refine ⟨fun k => (s k)⁻¹, fun k => inv_ne_zero (hs k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hs p.1)]


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem normSegre_sameOrbit {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {z₁ z₂ : (Σ k', ι' k') → ℂ} (h : SameOrbit z₁ z₂) :
    (Ψ (segre fun p => z₁ (v p)) 0)⁻¹ • segre (fun p => z₁ (v p)) =
      (Ψ (segre fun p => z₂ (v p)) 0)⁻¹ • segre (fun p => z₂ (v p)) := by
  obtain ⟨c, hc, rfl⟩ := h
  have h1 : (fun p => c (v p).1 * z₂ (v p)) = fun p : Σ k, ι k => (c ∘ κ) p.1 * z₂ (v p) := by
    funext p
    rw [hv.2.2.1 p]
    rfl
  have hne : ∏ k, (c ∘ κ) k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)
  rw [h1, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hne, mul_one]


omit [Fintype K'] in
theorem ncard_pullW_eq {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ)
    (hB : ∀ z' ∈ mcPts P', z' ∈ mcPts J' →
      (Ψ (segre fun p => z' (v p)) 0)⁻¹ • segre (fun p => z' (v p)) ≠ w) :
    {x | pullW R v Ψ x = w}.ncard = (ptsOver P' v Ψ w).ncard := by
  refine Set.ncard_congr (fun x _ => {z'' | SameOrbit z'' (R.lift x x)}) ?_ ?_ ?_
  · intro x hx
    exact ⟨R.lift x x, R.mem x x (R.mem_U x), rfl, hx⟩
  · intro x x' hx hx' h
    have hxB : R.lift x x ∉ mcPts J' := fun hJ => hB _ (R.mem x x (R.mem_U x)) hJ hx
    have hmem : R.lift x x ∈ {z'' | SameOrbit z'' (R.lift x' x')} := h ▸ sameOrbit_self _
    exact R.inj x x' hxB hmem
  · rintro O ⟨z', hz', rfl, hw⟩
    have hzB : z' ∉ mcPts J' := fun hJ => hB z' hz' hJ hw
    obtain ⟨x, hx⟩ := R.surj z' hz' hzB
    refine ⟨x, ?_, ?_⟩
    · show (Ψ (segre fun p => R.lift x x (v p)) 0)⁻¹ • segre (fun p => R.lift x x (v p)) = w
      rw [← hw]
      exact normSegre_sameOrbit hv Ψ hx
    · ext z''
      exact ⟨fun h => sameOrbit_comp h hx, fun h => sameOrbit_comp h (sameOrbit_flip hx)⟩

end PullbackDegreeCount


open PullbackDegreeCount in
theorem PullbackDegreeCount.proof (hDim : FibreDimStatement) (hRank : ChartRankAdjoin.Statement)
    (hCount : GenericPointsCount.Statement) (hB : PullbackVanishingOfNullCycle.Statement) (hBad : pullbackBadImage_holds.Statement) :
    PullbackDegreeCount.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n G J R Ψ hv hP' hP hJ hΨ
  classical
  have hfib : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 := hDim K ι K' ι' κ v P' (n + 1) 0 G hv hP' hP
  choose i hi using hfib.1.2.2
  have hz : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0 := by
    intro k h0
    apply hi k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact h0
  have he : J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 Fin.elim0 = (Module.finrank G.Φ (IntermediateField.adjoin G.Φ
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) : ℤ) := by
    rw [hJ.1 _ Fin.elim0 i hfib hi]
    exact congrArg _ (hRank (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) i hz hfib.1.2.1)
  have hN := measure_union_null (hB K ι K' ι' κ v P' J' n Ψ hv hP' hP hΨ R.homog R.nondeg)
    (hBad K ι K' ι' κ v P' J' n R Ψ hv hP' hP hΨ)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN, hCount K ι K' ι' κ v P' n G i Ψ hv hP' hP hΨ hz]
    with y hy hc
  intro w hw
  obtain ⟨-, -, -, hΨw⟩ := id hw
  have hset : ({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ) = {x | pullW R v Ψ x = w} := by
    ext x
    refine ⟨fun h => h.1.2, fun hx => ?_⟩
    have hx' : pullW R v Ψ x = w := hx
    have h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0 := by
      intro h0
      have h1 := congrFun hΨw 0
      rw [← hx', pullW, h0, inv_zero, zero_smul, map_zero] at h1
      simp at h1
    have hq : pullQ R v Ψ x = y := by
      funext m
      have h1 := congrFun hΨw m.succ
      rw [← hx', pullW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at h1
      rw [pullQ, ← h1, div_eq_inv_mul]
    exact ⟨⟨hq, hx'⟩, fun hbad => hy (Or.inr ⟨x, ⟨hbad, h0⟩, hq⟩)⟩
  rw [hset, ncard_pullW_eq hv R Ψ w fun z' hz' hJ' hzw => hy (Or.inl ⟨z', hz', hJ', hzw ▸ hw⟩), hc w hw, he]
end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.DetRestrictScalarsEqZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter

namespace pullbackBadImage_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}


omit [Fintype K'] in
theorem pullQ_eq_local (hv : IsBlockMap κ v) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Ψ z = fun i =>
      Ψ (segre fun p => R.lift x z (v p)) i.succ / Ψ (segre fun p => R.lift x z (v p)) 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  have hpt : pullPt R v z = fun p => (c ∘ κ) p.1 * R.lift x z (v p) := by
    funext p
    simp only [pullPt, hzc, Function.comp_apply, hv.2.2.1 p]
  have hpc : ∏ k, (c ∘ κ) k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)
  funext i
  simp only [pullQ, hpt, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem analyticAt_pullQ (hv : IsBlockMap κ v) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) (j : Fin R.A.n)
    (hj : x ∈ (R.A.chart j).source) (h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0) :
    AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  classical
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hl := analyticAt_lift_chart R x j hu
  have hs : AnalyticAt ℂ (fun w => segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  have hH : AnalyticAt ℂ (fun w => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p))) u :=
    (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs
  have hH0 : AnalyticAt ℂ (fun w => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre fun p => R.lift x ((R.A.chart j).symm u) (v p)) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun w => fun i : Fin n =>
      Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) i.succ /
        Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu]
    with w hw
  exact (pullQ_eq_local hv R Ψ hw.2).symm

theorem det_restrictScalars_eq_zero {m : ℕ} (f : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (h : LinearMap.det (f : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = 0) :
    (f.restrictScalars ℝ).det = 0 := by
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h)
  show LinearMap.det ((f.restrictScalars ℝ : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) :
    (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ)) = 0
  refine LinearMap.det_eq_zero_iff_ker_ne_bot.mpr ((Submodule.ne_bot_iff _).mpr ⟨w, ?_, hw0⟩)
  simpa using hw

end pullbackBadImage_holds


open pullbackBadImage_holds in
theorem pullbackBadImage_holds.proof : pullbackBadImage_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n R Ψ hv _ _ _
  classical
  let S₁ : Fin R.A.n → Set (Fin n → ℂ) := fun j => (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹'
    ({x | R.lift x x ∈ mcPts J'} ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0})
  let S₂ : Fin R.A.n → Set (Fin n → ℂ) := fun j => {u | u ∈ (R.A.chart j).target ∧
    Ψ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 ∧
    LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}
  have hsub : pullQ R v Ψ '' (pullBad R v Ψ ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0}) ⊆
      ⋃ j, ((pullQ R v Ψ ∘ (R.A.chart j).symm) '' S₁ j ∪
        (pullQ R v Ψ ∘ (R.A.chart j).symm) '' S₂ j) := by
    rintro _ ⟨x, ⟨hx, h0⟩, rfl⟩
    rcases hx with (hB | hz) | ⟨j, hj, hn⟩
    · obtain ⟨j, hj⟩ := R.A.cover x
      refine Set.mem_iUnion.mpr ⟨j, Or.inl ⟨R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩⟩
      · rw [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact ⟨hB, h0⟩
      · simp [(R.A.chart j).left_inv hj]
    · exact absurd hz h0
    · have hd : LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0 := by
        by_contra hd
        exact hn ⟨analyticAt_pullQ hv R Ψ x j hj h0, hd⟩
      refine Set.mem_iUnion.mpr ⟨j, Or.inr ⟨R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_, hd⟩, ?_⟩⟩
      · rw [(R.A.chart j).left_inv hj]; exact h0
      · simp [(R.A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_iUnion_null fun j => measure_union_null ?_ ?_)
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
        (R.null j))
    intro u hu
    have hx := (R.A.chart j).map_target hu.1
    have hcu : R.A.chart j ((R.A.chart j).symm u) = u := (R.A.chart j).right_inv hu.1
    have := analyticAt_pullQ hv R Ψ _ j hx hu.2.2
    rw [hcu] at this
    exact (this.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u).restrictScalars ℝ) ?_ ?_
    · intro u hu
      have hx := (R.A.chart j).map_target hu.1
      have hcu : R.A.chart j ((R.A.chart j).symm u) = u := (R.A.chart j).right_inv hu.1
      have := analyticAt_pullQ hv R Ψ _ j hx hu.2.1
      rw [hcu] at this
      exact (this.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro u hu
      exact det_restrictScalars_eq_zero _ hu.2.2

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockGenFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace BlockGenFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem eval_smul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ)
    (u : (Σ k, ι k) → ℂ) :
    eval (fun p ↦ c p.1 * u p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval u (map (Int.castRingHom ℂ) s) := by
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hprod : ∏ p, (c p.1 * u p) ^ d p = (∏ k, c k ^ a k) * ∏ p, u p ^ d p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
  rw [hprod]
  ring


omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem eval_map_rename (v : (Σ k, ι k) → (Σ k', ι' k')) (s : MRing ι) (z' : (Σ k', ι' k') → ℂ) :
    eval z' (map (Int.castRingHom ℂ) (rename v s)) = eval (fun p ↦ z' (v p)) (map (Int.castRingHom ℂ) s) := by
  rw [map_rename, eval_rename]
  rfl

end BlockGenFinite


open BlockGenFinite in
theorem BlockGenFinite.proof (hR : BlockRatioAlg.Statement) : BlockGenFinite.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n hv hP' hP
  have hrel := hP'.2.1.2.2
  have hpr := hP'.2.1.1
  have hrel' : ∀ k : FibreBlock κ, ∃ i : ι' k.1, (X (⟨k.1, i⟩ : Σ k', ι' k') : MRing ι') ∉ P' := fun k ↦ hrel k.1
  choose c hc using hrel'
  have hA := fun q : (Σ k : FibreBlock κ, ι' k.1) ↦
    hR K ι K' ι' κ v P' n hv hP' hP ⟨q.1.1, q.2⟩ ⟨q.1.1, c q.1⟩ rfl (hc q.1)
  choose m A a hAh hAl hAP using hA
  refine ⟨(∏ q, rename v (A q (Fin.last (m q)))) * ∏ k : FibreBlock κ, X ⟨k.1, c k⟩,
    (∑ q, Function.extend κ (a q) 0) + ∑ k : FibreBlock κ, Pi.single k.1 1, ?_, ?_, ?_⟩
  · exact AvoidRing.isMultiHomog_mul
      (AvoidRing.isMultiHomog_prod _ _ _ fun q _ ↦ ArithmeticIntersectionHorizontal.isMultiHomog_rename hv (hAh q _))
      (AvoidRing.isMultiHomog_prod _ _ _ fun k _ ↦ AvoidRing.isMultiHomog_X _ _)
  · intro h
    rcases hpr.mul_mem_iff_mem_or_mem.mp h with h | h
    · obtain ⟨q, -, hq⟩ := hpr.prod_mem_iff.mp h
      exact hAl q hq
    · obtain ⟨k, -, hk⟩ := hpr.prod_mem_iff.mp h
      exact hc k hk
  intro u

  obtain ⟨pol, hpol⟩ : ∃ pol : (Σ k : FibreBlock κ, ι' k.1) → Polynomial ℂ, ∀ q, pol q =
      ∑ j : Fin (m q + 1), Polynomial.C (eval u (map (Int.castRingHom ℂ) (A q j))) * Polynomial.X ^ (j : ℕ) :=
    ⟨_, fun _ ↦ rfl⟩

  obtain ⟨build, hbuild⟩ : ∃ build : ((Σ k : FibreBlock κ, ι' k.1) → ℂ) → (Σ k', ι' k') → ℂ, ∀ ρ p',
      build ρ p' = if h : p'.1 ∈ Set.range κ then u (hv.2.2.2 p' h).choose else ρ ⟨⟨p'.1, h⟩, p'.2⟩ :=
    ⟨_, fun _ _ ↦ rfl⟩
  refine ⟨(Fintype.piFinset fun q ↦ (pol q).roots.toFinset).image build, ?_⟩
  rintro z' hz' hf0 ⟨d, hd, hzd⟩
  have hzd' : ∀ p, z' (v p) = d p.1 * u p := fun p ↦ congrFun hzd p
  simp only [map_mul, map_prod, map_X, eval_X] at hf0
  have hcz : ∀ k : FibreBlock κ, z' ⟨k.1, c k⟩ ≠ 0 := fun k ↦
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hf0) k (Finset.mem_univ _)
  have hlead : ∀ q, eval u (map (Int.castRingHom ℂ) (A q (Fin.last (m q)))) ≠ 0 := by
    intro q h
    have := Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hf0) q (Finset.mem_univ _)
    rw [eval_map_rename, show (fun p ↦ z' (v p)) = fun p ↦ d p.1 * u p from hzd,
      eval_smul_of_isMultiHomog (hAh q _), h, mul_zero] at this
    exact this rfl

  have hroot : ∀ q, z' ⟨q.1.1, q.2⟩ / z' ⟨q.1.1, c q.1⟩ ∈ (pol q).roots.toFinset := by
    intro q
    have hne : pol q ≠ 0 := by
      intro h0
      have h1 := congrArg (fun f ↦ _root_.AddMonoidAlgebra.coeff (M := ℕ) f (m q)) h0
      simp only [hpol, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at h1
      rw [Finset.sum_eq_single (Fin.last (m q))] at h1
      · simp only [Fin.val_last, if_true] at h1
        exact hlead q h1
      · intro j _ hj
        rw [if_neg]
        intro e
        exact hj (Fin.ext (by simp [e]))
      · simp
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
    have hrel0 := hz'.2 _ (hAP q)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, map_X, eval_X, eval_map_rename,
      show (fun p ↦ z' (v p)) = fun p ↦ d p.1 * u p from hzd, eval_smul_of_isMultiHomog (hAh q _)] at hrel0
    have hD : (∏ k, d k ^ a q k) * z' ⟨q.1.1, c q.1⟩ ^ m q ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hd k)) (pow_ne_zero _ (hcz q.1))
    refine (mul_eq_zero.mp ?_).resolve_left hD
    rw [hpol, Polynomial.eval_finsetSum, Finset.mul_sum, ← hrel0]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj : (j : ℕ) ≤ m q := Nat.lt_succ_iff.mp j.2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← pow_sub_mul_pow (z' ⟨q.1.1, c q.1⟩) hj, div_pow]
    field_simp [pow_ne_zero _ (hcz q.1)]

  refine ⟨build fun q ↦ z' ⟨q.1.1, q.2⟩ / z' ⟨q.1.1, c q.1⟩,
    Finset.mem_image_of_mem _ (Fintype.mem_piFinset.mpr hroot), ?_⟩
  refine ⟨fun k' ↦ if h : k' ∈ Set.range κ then d h.choose else z' ⟨k', c ⟨k', h⟩⟩,
    fun k' ↦ ?_, funext fun p' ↦ ?_⟩
  · dsimp only
    split_ifs with h
    · exact hd _
    · exact hcz ⟨k', h⟩
  · rw [hbuild]
    by_cases h : p'.1 ∈ Set.range κ
    · rw [dite_eq_left h]
      dsimp only
      rw [dite_eq_left h]
      obtain ⟨p, rfl⟩ := hv.2.2.2 p' h
      rw [show h.choose = p.1 from hv.1 (h.choose_spec.trans (hv.2.2.1 p)),
        show (hv.2.2.2 (v p) h).choose = p from hv.2.1 (hv.2.2.2 (v p) h).choose_spec]
      exact hzd' p
    · rw [dite_eq_right h]
      dsimp only
      rw [dite_eq_right h]
      have hc' := hcz ⟨p'.1, h⟩
      dsimp only at hc'
      field_simp [hc']

end GroundTheory.Heights₂.Heights.Inter
end
end
