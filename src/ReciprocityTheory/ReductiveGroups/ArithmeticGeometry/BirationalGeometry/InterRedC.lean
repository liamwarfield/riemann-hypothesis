module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_smul_of_isMultiHomog {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hms : m ∈ s.support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [MvPolynomial.coeff_map, h0, map_zero])
  have hsub : ∀ f : (Σ k, ι k) → ℂ, ∏ i ∈ m.support, f i ^ m i = ∏ i, f i ^ m i := fun f =>
    Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  rw [hsub, hsub, mul_left_comm]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show (∏ s, c (⟨k, s⟩ : Σ k, ι k).fst ^ m ⟨k, s⟩) = ∏ s, c k ^ m ⟨k, s⟩ from rfl,
    Finset.prod_pow_eq_pow_sum, hs m hms k]

theorem analyticAt_eval_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → (Σ k, ι k) → ℂ} {y : E} (hF : ∀ p, AnalyticAt ℂ (fun y => F y p) y) (f : MRing ι) :
    AnalyticAt ℂ (fun y => eval (F y) (map (Int.castRingHom ℂ) f)) y := by
  induction (map (Int.castRingHom ℂ) f) using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (hF i)

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem holoOn_eval_lift (R : AnLogRes P J e) (x : R.X) (f : MRing ι) :
    R.A.HoloOn (R.U x) (fun y => eval (R.lift x y) (map (Int.castRingHom ℂ) f)) := by
  intro j w hw
  exact analyticAt_eval_comp (F := fun w => R.lift x ((R.A.chart j).symm w))
    (fun p => R.holo x p j w hw) f

theorem isSection_lift (R : AnLogRes P J e) {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s) :
    IsSection R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) := by
  obtain ⟨a, ha, hsa, -⟩ := hs
  refine ⟨fun x => holoOn_eval_lift R x s, fun x x' y hy => ?_⟩
  obtain ⟨c, hc, hxy⟩ := R.compat x x' y hy
  have h1 := A.pos _ (R.mem x y hy.1).1
  have h2 := A.pos _ (R.mem x' y hy.2).1
  have hsm := A.smul c (R.lift x' y) hc
  rw [← hxy] at hsm
  have he : eval (R.lift x y) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval (R.lift x' y) (map (Int.castRingHom ℂ) s) := by
    rw [hxy]
    exact eval_smul_of_isMultiHomog hsa c _
  simp only [potOf]
  rw [Real.exp_neg, Real.exp_neg, Real.exp_log h1, Real.exp_log h2, he, hsm]
  simp only [ha, zpow_natCast, norm_mul, norm_prod, norm_pow]
  have hP : 0 < ∏ k, ‖c k‖ ^ a k :=
    Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hc k)) _
  field_simp

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeE
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem analyticAt_lift_chart (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => R.lift x ((R.A.chart j).symm v)) u := by
  rw [analyticAt_pi_iff]
  intro p
  exact R.holo x p j u hu

theorem brQ_eq_local {x z : R.X} (hz : z ∈ R.U x) :
    brQ R Ψ z = fun i => Ψ (segre (R.lift x z)) i.succ / Ψ (segre (R.lift x z)) 0 := by
  obtain ⟨c, hc0, hc⟩ := R.compat x z z ⟨hz, R.mem_U z⟩
  have hseg : segre (R.lift x z) = (∏ k, c k) • segre (R.lift z z) := by
    funext i
    simp only [segre, Pi.smul_apply, smul_eq_mul, hc, Finset.prod_mul_distrib]
  have hC : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc0 k
  funext i
  simp only [brQ, hseg, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hC]

theorem analyticAt_segre_lift (x : R.X) (j : Fin R.A.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.lift x ((R.A.chart j).symm v)))) u := by
  classical
  have hl := analyticAt_lift_chart R x j hu
  have hseg : AnalyticAt ℂ (fun v => segre (R.lift x ((R.A.chart j).symm v))) u := by
    rw [analyticAt_pi_iff]
    intro i
    simp only [segre]
    have hp := Finset.analyticAt_prod (Finset.univ : Finset K) fun k _ => (analyticAt_pi_iff.mp hl) ⟨k, i k⟩
    exact hp.congr (Filter.Eventually.of_forall fun v => by simp [Finset.prod_apply])
  have := ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp hseg
  exact this

theorem analyticAt_brQ (x : R.X) (j : Fin R.A.n) (hj : x ∈ (R.A.chart j).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  have hxs : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmemT : R.A.chart j x ∈ (R.A.chart j).target := (R.A.chart j).map_source hj
  have hnhd : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x ∈ 𝓝 (R.A.chart j x) := by
    apply Filter.inter_mem ((R.A.chart j).open_target.mem_nhds hmemT)
    apply ((R.A.chart j).continuousAt_symm hmemT).preimage_mem_nhds
    rw [hxs]
    exact (R.isOpen_U x).mem_nhds (R.mem_U x)
  have heq : (fun v => fun i : Fin e => Ψ (segre (R.lift x ((R.A.chart j).symm v))) i.succ /
      Ψ (segre (R.lift x ((R.A.chart j).symm v))) 0) =ᶠ[𝓝 (R.A.chart j x)]
      brQ R Ψ ∘ (R.A.chart j).symm := by
    filter_upwards [hnhd] with v hv
    exact (brQ_eq_local R Ψ hv.2).symm
  refine AnalyticAt.congr ?_ heq
  have hs := analyticAt_segre_lift R Ψ x j ⟨hmemT, by simp [hxs, R.mem_U x]⟩
  have hcomp := analyticAt_pi_iff.mp hs
  rw [analyticAt_pi_iff]
  intro i
  apply AnalyticAt.div (hcomp i.succ) (hcomp 0)
  simpa [hxs] using h0

theorem brQ_image_null_of
    (hS : ∀ j, volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 := by
  have hsub : brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0}) ⊆
      ⋃ j, (brQ R Ψ ∘ (R.A.chart j).symm) '' ((R.A.chart j).target ∩
        (R.A.chart j).symm ⁻¹' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := R.A.cover x
    refine Set.mem_iUnion.mpr ⟨j, R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, (R.A.chart j).left_inv hj]
      exact hx
    · simp [(R.A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  apply MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
  · intro v hv
    have hvs : (R.A.chart j).symm v ∈ (R.A.chart j).source := (R.A.chart j).map_target hv.1
    have hA := analyticAt_brQ R Ψ ((R.A.chart j).symm v) j hvs hv.2.2
    rw [(R.A.chart j).right_inv hv.1] at hA
    exact (hA.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · exact measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)) (hS j)

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
