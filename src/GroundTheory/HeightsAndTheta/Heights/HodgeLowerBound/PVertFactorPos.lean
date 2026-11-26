module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace VertFactorPos

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_eq_eval_map (z : (Σ k, ι k) → ℂ) (F : MRing ι) :
    aeval z F = eval z (map (Int.castRingHom ℂ) F) := by
  rw [aeval_def, eval_map, algebraMap_int_eq]

theorem mem_mCoordIdeal_iff_of_homog {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {F : MRing ι}
    {d : K → ℕ} (hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F d) : F ∈ mCoordIdeal y ↔ aeval y F = 0 := by
  refine ⟨fun h => ?_, mem_mCoordIdeal_of_aeval_eq_zero y hF⟩
  have h' : mConeMap y F = 0 := RingHom.mem_ker.mp h
  rw [mConeMap_of_isMultiHomog y hF] at h'
  have hm : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  exact C_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hm)

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem X_mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (q : Σ k, ι k) :
    (X q : MRing ι) ∈ mCoordIdeal y ↔ y q = 0 := by
  show X q ∈ RingHom.ker (mConeMap y) ↔ _
  rw [RingHom.mem_ker]
  simp [mConeMap, X_ne_zero]

theorem mCoordIdeal_le {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) : mCoordIdeal y ≤ mCoordIdeal z := by
  classical
  intro F hF
  show F ∈ RingHom.ker (mConeMap z)
  rw [RingHom.mem_ker]
  ext m
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ← Finsupp.equivFunOnFinite_symm_coe m,
    HilbertSamuel.GenFibreHomog.coeff_mConeMap, aeval_eq_eval_map]
  exact hz.2 _ (HilbertSamuel.GenFibreHomog.isMultiHomogIdeal_mCoordIdeal y F hF _)

theorem prod_X_pow_add (d d' : K → ℕ) {R : Type} [CommRing R] :
    (∏ k, (X k : MvPolynomial K R) ^ (d + d') k) =
      (∏ k, (X k : MvPolynomial K R) ^ d k) * ∏ k, (X k : MvPolynomial K R) ^ d' k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

theorem prod_X_pow_eq_monomial (d : K → ℕ) {R : Type} [CommRing R] :
    (∏ k, (X k : MvPolynomial K R) ^ d k) = monomial (Finsupp.equivFunOnFinite.symm d) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
  simp

theorem isMultiHomog_chartForm [DecidableEq K] (c : (k : K) → ι k) (d : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  apply HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted
  have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ : MRing ι) ^ d k)
    (fun k => d k • NumbersDVR.blockWeight ι ⟨k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ (NumbersDVR.blockWeight ι) ⟨k, c k⟩).pow (d k))
  convert this using 1
  funext k
  simp [NumbersDVR.blockWeight, Finset.sum_apply, Pi.single_apply]

theorem exists_value {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {p : ℕ} (hp : p ≠ 0) {b : K → ℤ} {f g : MRing ι}
    (hV : IsVerticalDivisorAt (mCoordIdeal y) p b f g) (c : (k : K) → ι k)
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    ∃ v, v ≠ 0 ∧ IsValueAt y (aeval y f / aeval y g * chartMono y c (-b)) z v := by
  classical
  have hPW : mCoordIdeal y ≤ mCoordIdeal z := mCoordIdeal_le hz
  have hWp : (mCoordIdeal z).IsPrime := RingHom.ker_isPrime _
  have hrel : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (mCoordIdeal z) := fun k =>
    ⟨c k, fun h => hc k ((X_mem_mCoordIdeal_iff z _).1 h)⟩
  have hpW : (C (p : ℤ) : MRing ι) ∉ mCoordIdeal z := by
    intro h
    have h' : mConeMap z (C (p : ℤ)) = 0 := RingHom.mem_ker.mp h
    simp [mConeMap, hp] at h'
  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_fibre _ hWp hPW hrel hpW
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  have hfy : aeval y f ≠ 0 := fun h => hV.num_not_mem ((mem_mCoordIdeal_iff_of_homog y hf).2 h)
  have hgy : aeval y g ≠ 0 := fun h => hV.den_not_mem ((mem_mCoordIdeal_iff_of_homog y hg).2 h)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h =>
    hc k ((X_mem_mCoordIdeal_iff z _).1 (hPW ((X_mem_mCoordIdeal_iff y _).2 h)))

  have hu' : mConeMap z u ≠ 0 := fun h => hu (RingHom.mem_ker.mpr h)
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 hu'
  set e : K → ℕ := ⇑m with he
  set ue := weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e u with hue_def
  have hue : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog ue e := HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted
    (weightedHomogeneousComponent_isWeightedHomogeneous e u)
  have huez : aeval z ue ≠ 0 := by
    rw [← Finsupp.equivFunOnFinite_symm_coe m, HilbertSamuel.GenFibreHomog.coeff_mConeMap] at hm
    exact hm
  have hueW : ue ∉ mCoordIdeal z := fun h => huez ((mem_mCoordIdeal_iff_of_homog z hue).1 h)
  have huey : aeval y ue ≠ 0 := fun h => hueW (hPW ((mem_mCoordIdeal_iff_of_homog y hue).2 h))

  have hrel' : mConeMap y u * (C (aeval y f) * ∏ k, (X k : MvPolynomial K Ω) ^ bf k) =
      mConeMap y v * (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k) := by
    have h : mConeMap y (u * f - v * g) = 0 := RingHom.mem_ker.mp huv
    rw [map_sub, map_mul, map_mul, sub_eq_zero, mConeMap_of_isMultiHomog y hf,
      mConeMap_of_isMultiHomog y hg] at h
    exact h

  have hcoef := congrArg (AddMonoidAlgebra.coeff · (m + Finsupp.equivFunOnFinite.symm bf)) hrel'
  rw [prod_X_pow_eq_monomial, prod_X_pow_eq_monomial, C_mul_monomial, C_mul_monomial,
    coeff_mul_monomial', coeff_mul_monomial', if_pos le_add_self, add_tsub_cancel_right, mul_one,
    mul_one] at hcoef
  have hcu : AddMonoidAlgebra.coeff (mConeMap y u) m = aeval y ue := by
    rw [← Finsupp.equivFunOnFinite_symm_coe m, HilbertSamuel.GenFibreHomog.coeff_mConeMap]
  rw [hcu] at hcoef
  by_cases hle : Finsupp.equivFunOnFinite.symm bg ≤ m + Finsupp.equivFunOnFinite.symm bf
  swap
  · rw [if_neg hle] at hcoef
    exact absurd hcoef (mul_ne_zero huey hfy)
  rw [if_pos hle] at hcoef
  set d' : K → ℕ := ⇑(m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg) with hd'
  set a := weightedHomogeneousComponent (NumbersDVR.blockWeight ι) d' v with ha_def
  have ha : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog a d' := HilbertSamuel.GenFibreHomog.isMultiHomog_of_weighted
    (weightedHomogeneousComponent_isWeightedHomogeneous d' v)
  have hcv : AddMonoidAlgebra.coeff (mConeMap y v)
      (m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg) = aeval y a := by
    rw [← Finsupp.equivFunOnFinite_symm_coe
      (m + Finsupp.equivFunOnFinite.symm bf - Finsupp.equivFunOnFinite.symm bg),
      HilbertSamuel.GenFibreHomog.coeff_mConeMap]
  rw [hcv] at hcoef

  have hdeg : d' + bg = e + bf := by
    have := congrArg (⇑) (tsub_add_cancel_of_le hle)
    simpa [hd', he, Finsupp.coe_add] using this

  have hkey : a * u - ue * v ∈ mCoordIdeal y := by
    show _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, map_sub, map_mul, map_mul, sub_eq_zero, mConeMap_of_isMultiHomog y ha,
      mConeMap_of_isMultiHomog y hue]
    have hG : (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k) ≠ 0 :=
      mul_ne_zero (C_ne_zero.2 hgy) (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k))
    refine mul_right_cancel₀ hG ?_
    calc C (aeval y a) * (∏ k, (X k : MvPolynomial K Ω) ^ d' k) * mConeMap y u *
          (C (aeval y g) * ∏ k, (X k : MvPolynomial K Ω) ^ bg k)
        = C (aeval y a * aeval y g) * (∏ k, (X k : MvPolynomial K Ω) ^ (d' + bg) k) *
            mConeMap y u := by rw [prod_X_pow_add, map_mul]; ring
      _ = C (aeval y ue * aeval y f) * (∏ k, (X k : MvPolynomial K Ω) ^ (e + bf) k) *
            mConeMap y u := by rw [hcoef, hdeg]
      _ = C (aeval y ue) * (∏ k, (X k : MvPolynomial K Ω) ^ e k) *
            (mConeMap y u * (C (aeval y f) * ∏ k, (X k : MvPolynomial K Ω) ^ bf k)) := by
          rw [prod_X_pow_add, map_mul]; ring
      _ = _ := by rw [hrel']; ring
  have haW : a ∉ mCoordIdeal z := by
    intro h
    have h2 : ue * v ∈ mCoordIdeal z := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right u _ h) (hPW hkey)
      simpa using this
    rcases hWp.mem_or_mem h2 with h3 | h3
    · exact hueW h3
    · exact hv h3
  have haz : aeval z a ≠ 0 := fun h => haW ((mem_mCoordIdeal_iff_of_homog z ha).2 h)

  have hMz : ∀ d : K → ℕ, eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k)) =
      ∏ k, z ⟨k, c k⟩ ^ d k := fun d => by simp [map_prod]
  have hMy : ∀ d : K → ℕ, aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) = ∏ k, y ⟨k, c k⟩ ^ d k :=
    fun d => by simp [map_prod]
  have hMz0 : ∀ d : K → ℕ, (∏ k, z ⟨k, c k⟩ ^ d k) ≠ 0 := fun d =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hMy0 : ∀ d : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := fun d =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
  have hchart : chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k = ∏ k, y ⟨k, c k⟩ ^ bg k := by
    rw [chartMono, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hb, Pi.neg_apply, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k)]
    congr 1
    ring
  refine ⟨eval z (map (Int.castRingHom ℂ) (a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bg k)) /
    eval z (map (Int.castRingHom ℂ) (ue * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bf k)), ?_,
    e + bf, a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bg k, ue * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ bf k,
    ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp only [map_mul]
    rw [hMz, hMz, ← aeval_eq_eval_map, ← aeval_eq_eval_map]
    exact div_ne_zero (mul_ne_zero haz (hMz0 _)) (mul_ne_zero huez (hMz0 _))
  · rw [← hdeg]
    exact LowerBoundFree.isMultiHomog_mul ha (isMultiHomog_chartForm c bg)
  · exact LowerBoundFree.isMultiHomog_mul hue (isMultiHomog_chartForm c bf)
  · rw [map_mul, hMy]
    exact mul_ne_zero huey (hMy0 _)
  · rw [map_mul, map_mul, hMy, hMy, ← hchart]
    field_simp
    linear_combination (-(chartMono y c (-b) * ∏ k, y ⟨k, c k⟩ ^ bf k)) * hcoef
  · simp only [map_mul]
    rw [hMz, ← aeval_eq_eval_map]
    exact mul_ne_zero huez (hMz0 _)

end VertFactorPos


open VertFactorPos in
theorem VertFactorPos.proof : VertFactorPos.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D p hp z hz
  have hex : ∃ c : (k : K) → ι k, ∀ k, z ⟨k, c k⟩ ≠ 0 :=
    ⟨fun k => (hz.1 k).choose, fun k => (hz.1 k).choose_spec⟩
  rw [ComponentData.vertFactor, dite_eq_left hex]
  obtain ⟨v, hv0, hv⟩ := exists_value hz (D.S_prime p hp).ne_zero (D.vertical p hp) hex.choose
    hex.choose_spec
  rw [valAt_eq hz hv]
  exact mul_pos (norm_pos_iff.2 hv0) (norm_pos_iff.2
    (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hex.choose_spec k)))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace TopNPoly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem orbitRep_orbitRep (z : (Σ k, ι k) → ℂ) : orbitRep (orbitRep z) = orbitRep z := by
  simp only [orbitRep, Quotient.out_eq]

theorem orbitRep_blocks {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, orbitRep z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, -, hzc⟩ := exists_eq_smul_orbitRep z
  intro k
  obtain ⟨i, hi⟩ := hz k
  refine ⟨i, fun h => hi ?_⟩
  rw [hzc]
  simp [torusSmul, h]

theorem hermOfFun_h_orbitRep {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hF : 0 < F (orbitRep z)) :
    (hermOfFun ι a F).h (orbitRep z) = F (orbitRep z) := by
  have hR := refNorm_pos a (orbitRep_blocks hz)
  simp only [hermOfFun]
  rw [orbitRep_orbitRep, Real.exp_log (div_pos hF hR), mul_div_cancel₀ _ hR.ne']

theorem hermOfFun_h_smul {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) (hzc : z = torusSmul c (orbitRep z)) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hF : 0 < F (orbitRep z)) :
    (hermOfFun ι a F).h z = (∏ k, ‖c k‖ ^ a k) * F (orbitRep z) := by
  have h1 := hermOfFun_h_orbitRep (a := a) hz hF
  conv_lhs => rw [hzc]
  exact ((hermOfFun ι a F).smul c (orbitRep z) hc).trans (by rw [h1]; rfl)

theorem prod_norm_zpow_add {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a b : K → ℤ) (q : ℕ) :
    (∏ k, ‖c k‖ ^ ((q : ℤ) • a + ((1 : ℕ) : ℤ) • b) k) = (∏ k, ‖c k‖ ^ a k) ^ q * ∏ k, ‖c k‖ ^ b k := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]
  rw [zpow_add₀ h0, show (q : ℤ) * a k = a k * q by ring, zpow_mul, zpow_natCast]

theorem smoothRep_smooth_of {P : Ideal (MRing ι)} {A Z : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (ha : Z.a = A.a) (hZ : IsSmoothHerm Z)
    (hh : ∀ z ∈ mcPts P, Z.h z = A.h z) : IsSmoothHerm (smoothRep P A) := by
  classical
  unfold smoothRep
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact absurd ⟨Z, ha, hZ, hh⟩ h

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]


omit [DecidableEq Ψ] in
theorem NbarQ_h_eq (hV : VertFactorPos.Statement) (X : ComponentSetting D O Lt) (B q : ℕ) (t : ℝ)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    (X.NbarQ B 1 q t).h z = (muReg X.H X.S B t).h z ^ q * D.A'.h z := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hz0 := hz.1
  have hw0 := orbitRep_blocks hz0
  have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul D.arith.2.1.2.1 (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
    convert h using 1
    funext p
    have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hvf : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z) :=
    Finset.prod_pos fun p' hp' => hV II Ψ K ι Ω E D p' (Finset.mem_filter.1 hp').1 _ hwP
  have hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)
  have hreg : (X.S.regLine t).h (orbitRep z) =
      X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    hermOfFun_h_orbitRep hz0 hG0
  have hM : (muReg X.H X.S B t).h z = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) *
      ((X.S.regLine t).h (orbitRep z) * ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) := by
    unfold muReg
    rw [smoothRep_h _ hz]
    exact hermOfFun_h_smul hc hzc hz0 (by rw [hreg]; exact mul_pos hG0 hvf)
  have hN : (X.NbarQ B 1 q t).h z = (∏ k, ‖c k‖ ^ ((q : ℤ) • muTwDeg X.H B + ((1 : ℕ) : ℤ) • D.a') k) *
      ((X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z)))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) ^ q * D.A'.h (orbitRep z) ^ 1) := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_h _ hz]
    exact hermOfFun_h_smul hc hzc hz0
      (mul_pos (mul_pos (pow_pos hG0 _) (pow_pos hvf _)) (pow_pos (D.A'.pos _ hw0) _))
  have hA : D.A'.h z = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h (orbitRep z) := by
    conv_lhs => rw [hzc]
    exact (D.A'.smul c (orbitRep z) hc).trans (by rw [D.A'_deg])
  rw [hN, hM, hA, hreg, prod_norm_zpow_add hc]
  ring

end TopNPoly


open TopNPoly in
theorem TopNPoly.proof (hIso : HilbertSamuel.IsomInvariance.Statement) (hV : VertFactorPos.Statement)
    (hS : MuRegSmooth.Statement) : TopNPoly.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII _
  have hP : IsArithVar (mCoordIdeal D.y) (D.n + 1) := D.arith
  have hA : IsSmoothHerm D.A' := D.A'_pos.1
  refine ⟨fun i t => if i = 0 then arLimFun X.H X.S B t else ((D.n + 1).choose i : ℝ) *
      II K ι (mCoordIdeal D.y) (D.n + 1)
        (fun j : Fin (D.n + 1) => if (j : ℕ) < D.n + 1 - i then muReg X.H X.S B t else D.A'),
    by funext t; simp, fun q hq => ?_⟩
  filter_upwards [hS II Ψ K ι Ω E D O Lt X B] with t ht
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set Z := HilbertSamuel.HermLine.zcomb (muReg X.H X.S B t) D.A' (q : ℤ) ((1 : ℕ) : ℤ) with hZdef
  have hZ : IsSmoothHerm Z := HilbertSamuel.ZCombLimit.isSmoothHerm_zcomb_int ht hA _ _
  have hagree : ∀ z ∈ mcPts (mCoordIdeal D.y), Z.h z = (X.NbarQ B 1 q t).h z := by
    intro z hz
    rw [NbarQ_h_eq hV X B q t hz]
    show (muReg X.H X.S B t).h z ^ (q : ℤ) * D.A'.h z ^ ((1 : ℕ) : ℤ) = _
    simp
  have hdeg : Z.a = (X.NbarQ B 1 q t).a := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_a]
    show (q : ℤ) • (muReg X.H X.S B t).a + ((1 : ℕ) : ℤ) • D.A'.a = _
    rw [muReg, smoothRep_a, D.A'_deg]
    rfl
  have hN : IsSmoothHerm (X.NbarQ B 1 q t) := by
    unfold ComponentSetting.NbarQ
    refine smoothRep_smooth_of (Z := Z) ?_ hZ fun z hz => ?_
    · rw [hdeg]; unfold ComponentSetting.NbarQ; rw [smoothRep_a]
    · rw [hagree z hz]; unfold ComponentSetting.NbarQ; rw [smoothRep_h _ hz]
  have hne : (1 : MRing ι) ∉ mCoordIdeal D.y := fun h =>
    hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hiso : ∀ j : Fin (D.n + 1), HilbertSamuel.IsIsometricOn (mCoordIdeal D.y)
      ((fun _ => X.NbarQ B 1 q t) j) ((fun _ => Z) j) := fun _ =>
    ⟨1, 1, 0, 0, by simpa using isMultiHomog_C_zero (ι := ι) 1, by simpa using isMultiHomog_C_zero (ι := ι) 1,
      hne, hne, fun k => by simp [hdeg], rfl, fun z hz => by simp [hagree z hz]⟩
  have hI := hIso K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B 1 q t) (fun _ => Z) hP
    (fun _ => hN) (fun _ => hZ) hiso
  have hE := (HilbertSamuel.ZCombExpand.proof K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1)
    (muReg X.H X.S B t) D.A' q 1 hP ht hA).1
  show II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B 1 q t) / (q : ℝ) ^ (D.n + 1) = _
  rw [hI, hE, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ D.n + 1 := by simp at hi; omega
  have hpow : (q : ℝ) ^ (D.n + 1) = (q : ℝ) ^ (D.n + 1 - i) * (q : ℝ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  split_ifs with h0
  · subst h0
    have hall : (fun j : Fin (D.n + 1) => if (j : ℕ) < D.n + 1 - 0 then muReg X.H X.S B t else D.A') =
        fun _ => muReg X.H X.S B t := by
      funext j; simp [j.isLt]
    rw [hall]
    simp only [arLimFun, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, Nat.sub_zero, pow_zero]
    field_simp
  · rw [hpow, Nat.cast_one, one_pow, mul_one, one_div, inv_pow]
    field_simp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuSheetLeviNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuSheetLeviNonneg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ)),
    IsGoodProj (mCoordIdeal D.y) Q →
      ∀ᵐ y : Fin D.n → ℂ, ∀ (w : ((k : K) → ι k) → ℂ) (γ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ),
        IsSheet (mCoordIdeal D.y) Q y w γ →
          ContDiffAt ℝ 2 (fun y' => phMu X.H (γ y')) y ∧
            ∀ v : Fin D.n → ℂ, 0 ≤ leviForm (fun y' => phMu X.H (γ y')) y v

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsParamImageNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def ParamImageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d m : ℕ)
    (V A : Fin m → Set (Fin d → ℂ)) (γ : Fin m → (Fin d → ℂ) → (Σ k, ι k) → ℂ) (N : Set ((Σ k, ι k) → ℂ)),
    (∀ i, IsOpen (V i)) → (∀ i, A i ⊆ V i) → (∀ i, volume (A i) = 0) → (∀ i, AnalyticOnNhd ℂ (γ i) (V i)) →
    (∀ z ∈ N ∩ mcPts P, ∃ i, ∃ w ∈ A i, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (γ i w)) →
    IsPtsNull P d N

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelLogIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def ModelLogIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (u : M.Xc → ℝ) (C C' : ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → IsPtsNull P e N → @Measurable M.Xc ℝ (borel M.Xc) _ u →
    (∀ x ∈ R.Yo, |u x| ≤ C + C' * Real.log (R.r x)) →
    (∀ z ∈ mcPts P, z ∉ N → M.proj z ∈ R.Yo → g z = u (M.proj z)) →
      IsPtsIntegrable P (fun (_ : Fin e) z => c * Real.log (L.h z)) g

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTpCuspIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def TpCuspIntegrable.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ),
    IsSmoothHerm (X.NbarQ B p q t) →
      IsPtsIntegrable (mCoordIdeal D.y) (X.omN B p q t) (fun z => X.Cd.cuspWeight z / 2)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PGenLeadMinorNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem leadMinor_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) :
    f (leadMinor M a) = leadMinor (f.mapMatrix M) a := by
  unfold leadMinor pivotMinor
  rw [RingHom.map_det]
  rfl

theorem leadMinor_one {R : Type} [CommRing R] {n : ℕ} (a : Fin (n - 1)) :
    leadMinor (1 : Matrix (Fin n) (Fin n) R) a = 1 := by
  unfold leadMinor pivotMinor
  have h : (1 : Matrix (Fin n) (Fin n) R).submatrix (Fin.castLE (n := (a : ℕ) + 1) (m := n) (by have := a.2; omega))
      (pivotCols a (Fin.castLE (Nat.sub_le n 1) a)) = (1 : Matrix (Fin ((a : ℕ) + 1)) (Fin ((a : ℕ) + 1)) R) := by
    ext i j
    have hj : pivotCols a (Fin.castLE (Nat.sub_le n 1) a) j = Fin.castLE (n := (a : ℕ) + 1) (m := n) (by have := a.2; omega) j := by
      unfold pivotCols
      split_ifs with hlt
      · rfl
      · ext
        simp only [Fin.val_castLE]
        have := j.2
        omega
    rw [Matrix.submatrix_apply, hj, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castLE_inj]
  rw [h, Matrix.det_one]

theorem genMatFr_eq_map (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) :
    genMatFr F Ψ n τ = (algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)).mapMatrix
      (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (Ψ × Fin n × Fin n) F)) := by
  ext i j
  simp [genMatFr]

theorem GenLeadMinorNeZero.full : GenLeadMinorNeZero.Statement := by
  intro F _ Ψ n τ a
  rw [genMatFr_eq_map, ← leadMinor_map]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))).2 ?_
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)) h0
  rw [leadMinor_map, map_zero] at h1
  have hP : (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)).mapMatrix
      (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (Ψ × Fin n × Fin n) F)) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  rw [hP, leadMinor_one] at h1
  exact one_ne_zero h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBirationalRatioClosure
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace BirationalRatioClosure

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_prod_mul (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {g : MRing ι} {d : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) :
    aeval y g = (∏ k, y ⟨k, c k⟩ ^ d k) * aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [mul_left_comm]
  congr 1
  have h1 : (∏ p, y p ^ m p) =
      ∏ p : Σ k, ι k, (y ⟨p.1, c p.1⟩ ^ m p * (y p / y ⟨p.1, c p.1⟩) ^ m p) := by
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [← mul_pow, mul_div_cancel₀ _ (hc p.1)]
  rw [h1, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = y ⟨k, c k⟩ ^ d k
  rw [Finset.prod_pow_eq_pow_sum, hg m hm k]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_mem_closure (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (g : MRing ι) :
    aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) g ∈ Subfield.closure (coneRatios y c) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, algebraMap_int_eq, eq_intCast]
    exact intCast_mem _ a
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    exact mul_mem hp (Subfield.subset_closure ⟨i, rfl⟩)

theorem full : BirationalRatioClosure.Statement := by
  intro K _ ι _ Ω _ y c hy hc
  refine eq_top_iff.2 fun s _ ↦ ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hy s
  have hP : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (hc k)
  rw [aeval_eq_prod_mul y c hc hg, aeval_eq_prod_mul y c hc hh] at hgs
  rw [aeval_eq_prod_mul y c hc hh] at hh0
  have hr := right_ne_zero_of_mul hh0
  have hs : s = aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) g / aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) h := by
    rw [eq_div_iff hr]
    exact (mul_left_cancel₀ hP (hgs.trans (mul_left_comm _ _ _))).symm
  rw [hs]
  exact div_mem (aeval_mem_closure y c g) (aeval_mem_closure y c h)

end BirationalRatioClosure

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesStep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

namespace StokesStep

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_multicone : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem ptsIntegral_congr_g (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  classical
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w => finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1]
    · rfl
  · rfl

theorem isConeTangent_lift {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X)
    (j : Fin R.A.n) {y : Fin e → ℂ}
    (hy : y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) (w : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (R.lift x ((R.A.chart j).symm y))
      (fderiv ℂ (fun y' => R.lift x ((R.A.chart j).symm y')) y w) := by
  set τ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y') with hτdef
  have hO : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :=
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  have hτ : AnalyticAt ℂ τ y := analyticAt_pi_iff.mpr fun p => R.holo x p j y hy
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have h0 : (fun y' => eval (τ y') F) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hO.mem_nhds hy] with y' hy'
    exact (R.mem x _ hy'.2).2 f hf
  have hD := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (τ y)).comp y hτ.differentiableAt.hasFDerivAt
  have hD0 : HasFDerivAt (fun y' => eval (τ y') F) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq h0
  have h1 := congrArg (fun L => L w) (hD.unique hD0)
  simpa [smul_eq_mul, mul_comm] using h1

theorem isPsh_potOf {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hA : IsSemipositiveH P A) : IsPsh R.A (potOf R A) := by
  intro x j y hy w
  have hy' : y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x := hy
  set τ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y') with hτdef
  have hτ : AnalyticAt ℂ τ y := analyticAt_pi_iff.mpr fun p => R.holo x p j y hy'
  have hz : τ y ∈ mcPts P := R.mem x _ hy'.2
  have hS : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ y) :=
    isOpen_multicone.mem_nhds hz.1
  have hφ : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (τ y) :=
    ((hA.1.contDiffAt hS).of_le (WithTop.coe_le_coe.mpr le_top)).log (A.pos _ hz.1).ne'
  have hc : (potOf R A).φ x ∘ (R.A.chart j).symm = (fun z => Real.log (A.h z)) ∘ τ := rfl
  rw [hc, ReciprocityTheory.AnForm.levi_comp w hτ hφ]
  exact hA.2 _ hz _ (isConeTangent_lift R x j hy' w)

end StokesStep


open StokesStep in
theorem StokesStep.proof (hE : ResExistsStatement) : StokesStep.Statement := by
  intro K _ ι _ P n i A A' hP ha hA hA' hi
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  set C := A'.tensor A.inv with hCdef
  have hC0 : C.a = 0 := by simp [C, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, ha]
  have hCs : IsSmoothHerm C := hA'.1.mul (isSmoothHerm_inv hA.1)
  have hlogC : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      Real.log (C.h z) = Real.log (A'.h z) - Real.log (A.h z) := by
    intro z hz
    show Real.log (A'.h z * (A.h z)⁻¹) = _
    rw [Real.log_mul (A'.pos z hz).ne' (inv_ne_zero (A.pos z hz).ne'), Real.log_inv]
    ring
  let L : ℕ → Fin (m + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun l j => if j.val < l then A' else A
  have hpot : ∀ l, stokesMixPot A A' (m + 1) l = pot (L l) := by
    intro l
    funext j z
    simp only [stokesMixPot, pot, L]
    split_ifs <;> rfl
  have hLsp : ∀ l j, IsSemipositiveH P (L l j) := fun l j => by
    simp only [L]
    split_ifs
    exacts [hA', hA]
  have hL : ∀ l j, IsSmoothHerm (L l j) := fun l j => (hLsp l j).1
  have hs := isSectionOn_inv_one hP.2.1.1 hC0
  set v : R.X → ℝ := fun x => Real.log (C.h (R.lift x x)) with hvdef
  have key : ∀ l, ptsIntegral P (stokesMixPot A A' (m + 1) l)
      (fun z => Real.log (A'.h z) - Real.log (A.h z)) = mInt R.A (fun j => potOf R (L l j)) v := by
    intro l
    rw [ptsIntegral_congr_g P _ (g' := logNorm C.inv 1) fun z hz => by
      rw [logNorm_inv_one, hlogC z hz.1], hpot,
      ptsIntegral_eq_mInt' hE resBridge R hP (hL l) (isSmoothHerm_inv hCs) hs]
    congr 1
    funext x
    exact logNorm_inv_one C _
  rw [key, key]

  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 ⟨i, hi⟩ with hσ
  rw [← mIntSymm R.A (fun j => potOf R (L (i + 1) j)) σ v,
    ← mIntSymm R.A (fun j => potOf R (L i j)) σ v]
  set T : Fin m → LocPot R.X := fun k => potOf R (L i (σ k.succ)) with hT
  have hne : ∀ j : Fin (m + 1), j ≠ ⟨i, hi⟩ → L (i + 1) j = L i j := by
    intro j hj
    have hj' : j.val ≠ i := fun h => hj (Fin.ext h)
    simp only [L]
    by_cases h : j.val < i
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hσs : ∀ k : Fin m, σ k.succ ≠ ⟨i, hi⟩ := by
    intro k hk
    rw [hσ, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hk
    exact Fin.succ_ne_zero k hk
  have e1 : (fun j => potOf R (L (i + 1) j)) ∘ σ = Fin.cons (potOf R A') T := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [σ, L]
    · simp only [Function.comp_apply, Fin.cons_succ, T]
      rw [hne _ (hσs k)]
  have e0 : (fun j => potOf R (L i j)) ∘ σ = Fin.cons (potOf R A) T := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [σ, L]
    · simp only [Function.comp_apply, Fin.cons_succ, T]
  rw [e1, e0]

  have hv : R.A.Smooth v := smooth_diag R hCs hC0
  have hgerm : mInt R.A (Fin.cons (potOf R A') T) v =
      mInt R.A (Fin.cons (potOf R A + LocPot.ofFun v) T) v := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr R.A (locDens_cons_congr R.A T fun j y hy => ?_) fun _ => rfl
    set x0 := (R.A.chart j).symm y
    filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)).mem_nhds
      ⟨hy, R.mem_U x0⟩] with y' hy'
    have hmc := (R.mem x0 _ hy'.2).1
    show Real.log (A'.h (R.lift x0 _)) = Real.log (A.h (R.lift x0 _)) + v _
    rw [hvdef]
    simp only
    rw [← h_eq_of_sameOrbit hC0 (R.compat x0 _ _ ⟨hy'.2, R.mem_U _⟩), hlogC _ hmc]
    ring
  have hpA : IsPotential R.A (potOf R A) := isPotential_potOf R hA.1
  have hpv : IsPotential R.A (LocPot.ofFun v) := isPotential_ofFun R.A v hv
  have hTp : ∀ k, IsPotential R.A (T k) := fun k => isPotential_potOf R (hL i _)
  have hTpsh : ∀ k, IsPsh R.A (T k) := fun k => isPsh_potOf R (hLsp i _)
  have hcons : ∀ Q, IsPotential R.A Q → ∀ k, IsPotential R.A ((Fin.cons Q T : Fin (m + 1) → LocPot R.X) k) :=
    fun Q hQ k => by
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hQ
      · simpa using hTp k
  have hvc : Continuous v := PLC.continuous_of_smooth R.A hv
  have hadd := mIntAdd R.A (potOf R A) (LocPot.ofFun v) T hpA hpv hTp v
    (mIntegrableCont R.A _ (hcons _ hpA) v hvc) (mIntegrableCont R.A _ (hcons _ hpv) v hvc)
  have hneg := byPartsNonpos R.A v hv T hTp hTpsh
  rw [hgerm, hadd]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPivotMinorFlag
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem PivotMinorFlag.full : PivotMinorFlag.Statement := by
  intro R _ n M a b hab
  exact ⟨⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩, pivotMinor_eq_flagMinor M a b hab⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioFieldEq
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def HodgeFlagRatioFieldEq.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (c : ∀ k, Pl.ιY k), (∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0) →
    IntermediateField.adjoin Ω (coneRatios (Pl.flagGenericPoint B) c) =
      IntermediateField.adjoin Ω (Set.range (flagMinorRatio0 Ω Ψ D.N D.j))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBoundaryPtsNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def BoundaryPtsNull.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E),
    IsPtsNull (mCoordIdeal D.y) D.n D.Bd

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDivisorPreimageNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def DivisorPreimageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (M : CxModel P d) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas),
    IsPtsNull P d {z | M.proj z ∉ R.Yo}

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
