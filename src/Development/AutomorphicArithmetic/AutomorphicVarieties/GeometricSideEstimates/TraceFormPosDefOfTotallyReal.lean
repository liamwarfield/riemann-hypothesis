module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceMomentIdentity

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TraceFormCauchySchwarzCmDatum
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private lemma re_mul_conj (z : ℂ) : (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

private lemma sum_mul_le {ι : Type} [Fintype ι] (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, f i * g i ≤ (∑ i, f i) * ∑ i, g i := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => hg j) (Finset.mem_univ i)) (hf i)

private lemma cs_norm {ι : Type} [Fintype ι] (f g : ι → ℂ) :
    ‖∑ i, f i * g i‖ ^ 2 ≤ (∑ i, ‖f i‖ ^ 2) * ∑ i, ‖g i‖ ^ 2 := by
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖f i‖) (fun i => ‖g i‖))
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private lemma qf_eq (w : Fin a → Cinf E) : qf w = ∑ v : InfinitePlace E, ∑ i, ‖w i v‖ ^ 2 := by
  unfold qf; exact Finset.sum_comm

private lemma trF_eq (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF X Y = (∑ p : InfinitePlace E × Fin a × Fin a, X p.2.1 p.2.2 p.1 * Y p.2.2 p.2.1 p.1).re := by
  simp [trF, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_apply]

private lemma quad_eq (w x : Fin a → Cinf E) :
    quad (vecMulVec w (star w)) x = ∑ v : InfinitePlace E, ‖(x ⬝ᵥ w) v‖ ^ 2 := by
  unfold quad
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.vecMul_vecMulVec, smul_dotProduct, ← re_mul_conj]
  congr 1
  simp [dotProduct, Finset.sum_apply, mul_comm]

end

theorem UpperTheory.traceForm_cauchy_schwarz_cmDatum :
    RankOne := by
  intro E _ _ a w
  refine ⟨?_, fun M => ?_, fun x => ⟨?_, ?_, fun h => ?_⟩⟩
  · rw [qf_eq]
    unfold trF
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Matrix.one_mul, Matrix.trace, Matrix.diag, vecMulVec_apply, Finset.sum_apply, Complex.re_sum,
      Pi.mul_apply, Pi.star_apply, Complex.star_def, re_mul_conj]
  · have hM : ∀ i j v, M.1 j i v = (starRingEnd ℂ) (M.1 i j v) := by
      intro i j v
      have h : star M.1 = M.1 := M.2
      conv_lhs => rw [← h]
      rfl
    have h1 : trF M.1 M.1 = ∑ p : InfinitePlace E × Fin a × Fin a, ‖M.1 p.2.1 p.2.2 p.1‖ ^ 2 := by
      rw [trF_eq, Complex.re_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hM p.2.1 p.2.2, re_mul_conj]
    have h2 : ∑ p : InfinitePlace E × Fin a × Fin a, ‖(vecMulVec w (star w)) p.2.2 p.2.1 p.1‖ ^ 2 ≤ qf w ^ 2 := by
      rw [qf_eq, sq (∑ v : InfinitePlace E, ∑ i, ‖w i v‖ ^ 2)]
      refine le_trans (le_of_eq ?_) (sum_mul_le _ _ (fun v => by positivity) (fun v => by positivity))
      simp only [Fintype.sum_prod_type, Finset.sum_mul_sum, vecMulVec_apply, Pi.mul_apply, Pi.star_apply,
        norm_mul, norm_star, mul_pow, mul_comm]
    rw [h1, trF_eq]
    refine le_trans ?_ ((cs_norm _ _).trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
    exact sq_le_sq' (abs_le.1 (Complex.abs_re_le_norm _)).1 (abs_le.1 (Complex.abs_re_le_norm _)).2
  · rw [quad_eq]
    have hs : 0 ≤ ∑ v : InfinitePlace E, ‖(x ⬝ᵥ w) v‖ ^ 2 := by positivity
    rw [← Real.le_sqrt (norm_nonneg _) hs]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [Real.le_sqrt (norm_nonneg _) hs]
    exact Finset.single_le_sum (f := fun v => ‖(x ⬝ᵥ w) v‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ v)
  · rw [quad_eq, qf_eq, qf_eq, mul_comm]
    refine le_trans ?_ (sum_mul_le _ _ (fun v => by positivity) (fun v => by positivity))
    refine Finset.sum_le_sum fun v _ => ?_
    have := cs_norm (fun i => x i v) (fun i => w i v)
    simpa [dotProduct, Finset.sum_apply] using this
  · rw [quad_eq, h]; simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianPointEmbeddingInjective
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideComparison
open UpperTheory.V.Lit.Geo

set_option maxHeartbeats 800000 in
theorem UpperTheory.geometric_side_comparison :
    MeanLow := by
  unfold MeanLow
  refine ⟨Real.exp (-Real.pi) / 16, by positivity, ?_⟩
  intro A V _ _ _ φ hinj hS hT h2
  classical
  haveI : IsAddTorsionFree V := by
    constructor
    intro n hn x y _ hxy
    have h : ((n : ℝ)) • x = ((n : ℝ)) • y := by simpa [Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective V (Nat.cast_ne_zero.mpr hn) h
  have hfin : {x : A | ‖φ x‖ < 1}.Finite := by
    have h := hS.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-Real.pi)))
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    intro x (hx : ‖φ x‖ < 1)
    simp only [Set.mem_setOf_eq, not_lt]
    apply Real.exp_le_exp.mpr
    have ha2 : ‖φ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (φ x)]
    nlinarith [Real.pi_pos]
  have hfin2 : {x : A | ‖φ x‖ < 1 / 2}.Finite :=
    hfin.subset (fun x (hx : ‖φ x‖ < 1 / 2) => show ‖φ x‖ < 1 by linarith)
  set H := hfin.toFinset with hH
  set F := hfin2.toFinset with hF
  have hFH : F ⊆ H := by
    intro x hx
    simp only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    linarith
  have hcd : 2 * F.card - 1 ≤ H.card := by
    have h0 : (0 : A) ∈ F := by
      simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_zero, norm_zero]
      norm_num
    have hne : (F.image φ).Nonempty := ⟨φ 0, Finset.mem_image_of_mem _ h0⟩
    have hcdv := cauchy_davenport_of_isAddTorsionFree hne hne
    have hcard : (F.image φ).card = F.card := Finset.card_image_of_injective _ hinj
    open scoped Pointwise in
    have hsub : F.image φ + F.image φ ⊆ H.image φ := by
      intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      refine Finset.mem_image.mpr ⟨x + y, ?_, map_add φ x y⟩
      simp only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add (f := _)]
      calc ‖φ x + φ y‖ ≤ ‖φ x‖ + ‖φ y‖ := norm_add_le _ _
        _ < 1 := by linarith
    have hle := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hle
    rw [hcard] at hcdv
    omega
  have hsd := Finset.card_sdiff_add_card_eq_card hFH
  have hreal : (F.card : ℝ) ≤ ((H \ F).card : ℝ) + 1 := by
    have : F.card ≤ (H \ F).card + 1 := by omega
    exact_mod_cast this
  have hT2 : ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) ≤
      ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
    refine le_trans ?_ (hT.sum_le_tsum (H \ F) (fun x _ => by positivity))
    have hpt : ∀ x ∈ H \ F, Real.exp (-Real.pi) / 4 ≤ ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
      intro x hx
      simp only [Finset.mem_sdiff, hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx
      obtain ⟨h1, h3⟩ := hx
      have ha2 : ‖φ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (φ x)]
      have e1 : Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have e2 : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2 := by nlinarith
      have := Real.exp_pos (-Real.pi)
      nlinarith
    calc ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) = ∑ x ∈ H \ F, Real.exp (-Real.pi) / 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hpt
  have hS1 : ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
      4 * ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) + F.card := by
    have hg : Summable (fun x => if x ∈ F then (1 : ℝ) else 0) :=
      summable_of_ne_finset_zero (s := F) (fun x hx => if_neg hx)
    have hsum : ∑' x, (if x ∈ F then (1 : ℝ) else 0) = F.card := by
      rw [tsum_eq_sum (s := F) (fun x hx => if_neg hx)]
      simp
    have hle : ∀ x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
        4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0) := by
      intro x
      have hp := Real.exp_pos (-Real.pi * ‖φ x‖ ^ 2)
      by_cases hx : x ∈ F
      · rw [if_pos hx]
        have : Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg ‖φ x‖])
        nlinarith [sq_nonneg ‖φ x‖]
      · rw [if_neg hx]
        simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx
        have : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2 := by nlinarith
        nlinarith
    calc _ ≤ ∑' x, (4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0)) :=
          Summable.tsum_le_tsum hle hS ((hT.mul_left 4).add hg)
      _ = _ := by rw [Summable.tsum_add (hT.mul_left 4) hg, tsum_mul_left, hsum]
  have hE := Real.exp_pos (-Real.pi)
  have hE1 : Real.exp (-Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
  have hT0 : 0 ≤ ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
    tsum_nonneg (fun x => by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hS1 hE.le, mul_le_mul_of_nonneg_left hreal hE.le,
    mul_le_mul_of_nonneg_left h2 hE.le, mul_le_mul_of_nonneg_right hE1 hT0]
end

open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
private theorem pt_injective {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (g : GA E a) :
    Function.Injective (pt g) := by
  intro v v' h
  have hu : IsUnit (GeneralLinearGroup.map (pInf E) g).val := Units.isUnit _
  have h1 : vInf v = vInf v' := Matrix.vecMul_injective_of_isUnit hu h
  funext i
  have h2 : ((pInf E).comp (algebraMap E (Ad E))) (v i) = ((pInf E).comp (algebraMap E (Ad E))) (v' i) := congrFun h1 i
  exact ((pInf E).comp (algebraMap E (Ad E))).injective h2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
theorem UpperTheory.hermitian_point_embedding_injective :
    GradA := by
  intro E _ _ _ a ha L hL
  obtain ⟨c, hc, hlow⟩ := UpperTheory.geometric_side_comparison
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C, -, hC⟩ := UpperTheory.moment_bound_of_pointwise_moments N 1
  have hD : (0 : ℝ) < (a : ℝ) * Fintype.card (InfinitePlace E) := by
    have h1 : (0 : ℝ) < a := by exact_mod_cast ha
    have h2 : (0 : ℝ) < Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
    exact mul_pos h1 h2
  refine ⟨c / ((a : ℝ) * Fintype.card (InfinitePlace E)), div_pos hc hD, fun g hg => ?_⟩
  have hell : ell E a (toL (mom L g).1) = trF (mom L g).1 1 / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
    simp only [trF, mul_one, Matrix.trace, Matrix.diag, Finset.sum_apply, Complex.re_sum]
    rfl
  rw [hell]
  refine div_le_div_of_nonneg_right ?_ hD.le
  rw [UpperTheory.hermitian_space_moment_identity E a ha L hL g 1, le_div_iff₀ (by linarith)]
  simp only [(UpperTheory.geometric_side_quadraticForm_identity E a).1]
  let φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E) :=
    ((euc (E := E) (a := a)).toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype
  have hφ : ∀ v : lat L g, ‖φ v‖ ^ 2 = qf (pt (rt g) v.1) := fun v => norm_euc_sq _
  have hinj : Function.Injective φ := fun v v' h =>
    Subtype.ext (pt_injective (rt g) ((euc (E := E) (a := a)).injective h))
  have hs0 : Summable fun v : lat L g => Real.exp (-Real.pi * qf (pt (rt g) v.1)) := by
    simpa only [one_mul] using ((hN g).2 1 1 one_pos le_rfl).1
  have hs1 : Summable fun v : lat L g => qf (pt (rt g) v.1) * Real.exp (-Real.pi * qf (pt (rt g) v.1)) := by
    refine ((hC _ _ (hN g)).1.sub hs0).congr fun v => ?_
    ring
  have := hlow (lat L g) _ φ hinj
  simp only [hφ] at this
  exact this hs0 hs1 hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGradientEstimate
open UpperTheory.V.Lit.Geo

private theorem gradB_pt {z n W q c : ℝ} (hc : 0 < c) (hq : 0 ≤ q)
    (h1 : n ^ 2 ≤ z) (h2 : z ≤ W * q) (h3 : z = 0 ∨ c ≤ n) :
    z ≤ W ^ 2 / c ^ 2 * (1 + q) ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  rcases h3 with h | h
  · rw [h]; positivity
  · have hz : c ^ 2 ≤ z := (pow_le_pow_left₀ hc.le h 2).trans h1
    have hz0 : 0 ≤ z := hc2.le.trans hz
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    have a1 : z * c ^ 2 ≤ z * z := mul_le_mul_of_nonneg_left hz hz0
    have a2 : z * z ≤ (W * q) * (W * q) := mul_self_le_mul_self hz0 h2
    have a3 : q ^ 2 ≤ (1 + q) ^ 2 := by nlinarith
    have a4 : W ^ 2 * q ^ 2 ≤ W ^ 2 * (1 + q) ^ 2 := mul_le_mul_of_nonneg_left a3 (sq_nonneg W)
    nlinarith

theorem UpperTheory.hermitian_space_gradient_estimate :
    GradB := by
  intro E _ _ _ a ha L hL
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C, hC0, hC⟩ := UpperTheory.moment_bound_of_pointwise_moments N 2
  refine ⟨C, fun g w c hc hsep => ?_⟩
  obtain ⟨hs, hle⟩ := hC _ _ (hN g)
  have hTh : 1 ≤ Th L g := ((UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1 g).1
  have hTh0 : 0 < Th L g := lt_of_lt_of_le one_pos hTh
  have hR := (UpperTheory.traceForm_cauchy_schwarz_cmDatum E a w).2.2
  rw [UpperTheory.hermitian_space_moment_identity E a ha L hL g, div_le_iff₀ hTh0]
  have hK : 0 ≤ qf w ^ 2 / c ^ 2 := by positivity
  have hpt : ∀ v : lat L g, quad (Matrix.vecMulVec w (star w)) (pt (rt g) v.1) * gauss (pt (rt g) v.1) ≤
      qf w ^ 2 / c ^ 2 * ((1 + qf (pt (rt g) v.1)) ^ 2 * Real.exp (-Real.pi * qf (pt (rt g) v.1))) := by
    intro v
    obtain ⟨r1, r2, r3⟩ := hR (pt (rt g) v.1)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (gradB_pt hc (qf_nonneg _) r1 r2 ((hsep v.1 v.2).imp r3 id)) (Real.exp_pos _).le
  have hnn : ∀ v : lat L g, 0 ≤ quad (Matrix.vecMulVec w (star w)) (pt (rt g) v.1) * gauss (pt (rt g) v.1) :=
    fun v => mul_nonneg ((sq_nonneg _).trans (hR _).1) (Real.exp_pos _).le
  have hs2 := hs.mul_left (qf w ^ 2 / c ^ 2)
  have hs1 := Summable.of_nonneg_of_le hnn hpt hs2
  refine (hs1.tsum_le_tsum hpt hs2).trans ?_
  rw [tsum_mul_left]
  refine (mul_le_mul_of_nonneg_left hle hK).trans (le_of_eq ?_)
  change _ * (C * Th L g) = _
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.ConvexSeparationPositiveDistance
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.PositivityAtAllPlaces
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.Reduction

private theorem cont_pInf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : Continuous (pInf E) := by
  have c2 : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact c2.comp continuous_fst

private theorem pInf_pos {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (s : ℝ) (hs : 0 < s) :
    pInf E ((posIdele (K := E) s hs : GroundTheory.Global.IdeleGroup E) : Ad E) = fun _ => (s : ℂ) := by
  funext w
  have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  have h : ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ) := by
    rw [← GroundTheory.Global.IdeleGroup.coe_infiniteProj, infiniteProj_posIdele]
    change GroundTheory.Global.posRealElem w _ = _
    unfold GroundTheory.Global.posRealElem
    rw [dite_eq_right hw]
    simp [InfinitePlace.mult, hw, Real.sqrt_sq hs.le]
  change (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
    (((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w) = _
  rw [h, RingEquiv.apply_symm_apply]

private theorem pFin_pos {E : Type} [Field E] [NumberField E] (s : ℝ) (hs : 0 < s) :
    pFin E ((posIdele (K := E) s hs : GroundTheory.Global.IdeleGroup E) : Ad E) = 1 := by
  change ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (1 : Af E)
  exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl

private theorem col_eq {R : Type} [CommRing R] {a : ℕ} (i₀ : Fin a) (g γ b d k : GL (Fin a) R) (u : Fin a → R)
    (hd : d.val = Matrix.diagonal u) (hb : ∀ i, i ≠ i₀ → (b⁻¹).val i i₀ = 0) (h : γ * g = b * d * k) :
    u i₀ • ((g⁻¹).val *ᵥ fun i => (γ⁻¹).val i i₀) = fun i => (k⁻¹ * b⁻¹).val i i₀ := by
  have h1 : g⁻¹ * γ⁻¹ = k⁻¹ * d⁻¹ * b⁻¹ := by
    rw [← _root_.mul_inv_rev, h]; simp [mul_assoc]
  have h2 : ((g⁻¹).val *ᵥ fun i => (γ⁻¹).val i i₀) = (k⁻¹ * d⁻¹).val *ᵥ fun i => (b⁻¹).val i i₀ := by
    funext i
    have := congrArg (fun x : GL (Fin a) R => x.val i i₀) h1
    simpa only [Units.val_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h3 : u i₀ • (fun i => (b⁻¹).val i i₀) = d.val *ᵥ fun i => (b⁻¹).val i i₀ := by
    funext i
    rw [hd, Matrix.mulVec_diagonal]
    by_cases hi : i = i₀
    · subst hi; rfl
    · simp only [Pi.smul_apply, hb i hi, smul_zero, mul_zero]
  rw [h2, ← Matrix.mulVec_smul, h3, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_right]
  rfl

theorem UpperTheory.positivity_at_all_places :
    SiegelCol := by
  intro E _ _ _ a ha
  obtain ⟨Ω, C, N, hΩ, hB, hS⟩ := UpperTheory.height_bound_of_quasiHeight_le E a
  obtain ⟨-, -, -, hsm, -, -⟩ := UpperTheory.geometric_side_quadraticForm_identity E a
  let i₀ : Fin a := ⟨0, ha⟩
  have hK : IsCompact (maxCompact (K := E) (n := a) : Set (GA E a)) := isCompact_maxCompact
  let f : GA E a × GA E a → Fin a → Ad E := fun p i => (p.1⁻¹ * p.2⁻¹).val i i₀
  have hf : Continuous f := continuous_pi fun i =>
    (Units.continuous_val.comp (continuous_fst.inv.mul continuous_snd.inv)).matrix_elem i i₀
  have hc := hK.prod hΩ
  have hF : Continuous fun p i => pFin E (f p i) := continuous_pi fun i =>
    continuous_snd.comp ((continuous_apply i).comp hf)
  have hI : Continuous fun p => qf (fun i => pInf E (f p i)) := by
    unfold qf
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun w _ =>
      (((continuous_apply w).comp (cont_pInf.comp ((continuous_apply i).comp hf))).norm).pow 2
  obtain ⟨M, hM⟩ := hc.bddAbove_image hI.continuousOn
  refine ⟨_, |C| * M ^ N, N, hc.image hF, fun g => ?_⟩
  obtain ⟨γ, b, k, ρ, hρ, hb, hk, he, hh⟩ := hS g
  have hh0 := (hh i₀).2 rfl
  have hcol := col_eq i₀ (g.1 : GA E a) (ratGL E a γ) b _ k
    (fun i => ((posIdele (K := E) (ρ i) (hρ i) : GroundTheory.Global.IdeleGroup E) : Ad E)) (coe_diagUnits _ _)
    (fun i hi => mem_adelicBorel.1 (inv_mem (hB b hb)) (Fin.lt_def.2 (Nat.pos_of_ne_zero fun h => hi (Fin.ext h)))) he
  have hγ : (fun i => ((ratGL E a γ)⁻¹).val i i₀) = fun i => algebraMap E (Ad E) ((γ⁻¹).val i i₀) := by
    rw [← map_inv]; rfl
  rw [hγ] at hcol
  refine ⟨fun i => (γ⁻¹).val i i₀, fun h0 => ?_, ⟨(k, b), ⟨hk, hb⟩, ?_⟩, ?_⟩
  · have h1 : (γ * γ⁻¹).val i₀ i₀ = 0 := by
      rw [Units.val_mul, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun j _ => by rw [congrFun h0 j]; simp
    simp at h1
  · funext i
    have h1 := congrArg (pFin E) (congrFun hcol i)
    rw [Pi.smul_apply, smul_eq_mul, map_mul, pFin_pos, one_mul, RingHom.map_mulVec] at h1
    exact h1.symm
  · have h1 : (fun i => pInf E (f (k, b) i)) =
        ρ i₀ • ((GeneralLinearGroup.map (pInf E) (g.1⁻¹ : GA E a)).val *ᵥ vInf fun i => (γ⁻¹).val i i₀) := by
      funext i
      have h1 := congrArg (pInf E) (congrFun hcol i)
      rw [Pi.smul_apply, smul_eq_mul, map_mul, pInf_pos, RingHom.map_mulVec] at h1
      refine h1.symm.trans ?_
      funext w
      rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul]
      rfl
    have h2 : qf (fun i => pInf E (f (k, b) i)) ≤ M := hM ⟨(k, b), ⟨hk, hb⟩, rfl⟩
    rw [h1, hsm] at h2
    set q := qf ((GeneralLinearGroup.map (pInf E) (g.1⁻¹ : GA E a)).val *ᵥ vInf fun i => (γ⁻¹).val i i₀) with hq
    have hq0 : 0 ≤ q := qf_nonneg _
    calc _ ≤ C * ρ i₀ ^ (2 * N) * q ^ N := mul_le_mul_of_nonneg_right hh0 (pow_nonneg hq0 N)
      _ = C * (ρ i₀ ^ 2 * q) ^ N := by rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ |C| * M ^ N := mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) h2 N) (by positivity) (abs_nonneg C)
end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

private theorem dot_cancel {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S) (g : GL (Fin a) R)
    (x y : Fin a → S) :
    (x ᵥ* (GeneralLinearGroup.map f g).val) ⬝ᵥ ((GeneralLinearGroup.map f g⁻¹).val *ᵥ y) = x ⬝ᵥ y := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Matrix.one_mulVec]

private theorem back {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (f : R →+* S) (g : GL (Fin a) R)
    (y : Fin a → S) (h : (GeneralLinearGroup.map f g⁻¹).val *ᵥ y = 0) : y = 0 := by
  have h2 := congrArg (fun z => (GeneralLinearGroup.map f g).val *ᵥ z) h
  simp only [Matrix.mulVec_zero] at h2
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Matrix.one_mulVec] at h2

private theorem abs_inf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : E) (w : InfinitePlace E) :
    ‖pInf E (algebraMap E (Ad E) x) w‖ = w x := by
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq]

private theorem inf_ne {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : E) (hx : x ≠ 0) :
    pInf E (algebraMap E (Ad E) x) ≠ 0 := by
  intro h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have h1 := abs_inf x w
  rw [h] at h1
  have h2 := InfinitePlace.pos_iff (w := w).2 hx
  simp at h1
  exact h2.ne h1

private theorem sep {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (T : Set (Af E)) (hT : IsCompact T) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, algebraMap E (Af E) x ∈ T → x = 0 ∨ c ≤ ‖pInf E (algebraMap E (Ad E) x)‖ := by
  have hf := UpperTheory.V.Lit.Dr.finField E 1 T hT
  have hf2 := (hf.subset (Set.diff_subset (t := {0}))).image fun x => ‖pInf E (algebraMap E (Ad E) x)‖⁻¹
  obtain ⟨M, hM⟩ := hf2.bddAbove
  refine ⟨(max M 1)⁻¹, by positivity, fun x hx => ?_⟩
  by_cases h0 : x = 0
  · exact Or.inl h0
  right
  have hp : 0 < ‖pInf E (algebraMap E (Ad E) x)‖ := norm_pos_iff.2 (inf_ne x h0)
  rw [inv_le_comm₀ (by positivity) hp]
  by_cases h1 : ∀ w : InfinitePlace E, w x ≤ 1
  · exact (hM ⟨x, ⟨⟨h1, hx⟩, h0⟩, rfl⟩).trans (le_max_left _ _)
  · push Not at h1
    obtain ⟨w, hw⟩ := h1
    refine le_trans (inv_le_one_of_one_le₀ ?_) (le_max_right _ _)
    rw [← abs_inf] at hw
    exact hw.le.trans (norm_le_pi_norm _ w)

theorem UpperTheory.convex_separation_positive_distance :
    ShortCol := by
  intro E _ _ _ a ha L hL
  obtain ⟨T, C, N, hT, H⟩ := UpperTheory.positivity_at_all_places E a ha
  obtain ⟨-, hR, -⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  have hc : IsCompact ((fun p : (Fin a → Af E) × (Fin a → Af E) => p.1 ⬝ᵥ p.2) '' ((L : Set (Fin a → Af E)) ×ˢ T)) :=
    (hL.isCompact.prod hT).image (continuous_fst.dotProduct continuous_snd)
  obtain ⟨c, hc0, hsep⟩ := sep _ hc
  refine ⟨c, C, N, hc0, fun g => ?_⟩
  obtain ⟨ξ, hξ, h1, h2⟩ := H (retractOne g)
  change (GeneralLinearGroup.map (pFin E) (rt g)⁻¹).val *ᵥ vFin ξ ∈ T at h1
  change qht (rt g) * qf ((GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ) ^ N ≤ C at h2
  refine ⟨(GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ, fun h => hξ ?_, (hR g).2.1 ▸ h2, fun v hv => ?_⟩
  · have h3 := back _ _ _ h
    funext i
    by_contra hi
    exact inf_ne (ξ i) hi (congrFun h3 i)
  · have e1 : pt (rt g) v ⬝ᵥ ((GeneralLinearGroup.map (pInf E) (rt g)⁻¹).val *ᵥ vInf ξ)
        = pInf E (algebraMap E (Ad E) (v ⬝ᵥ ξ)) := by
      refine (dot_cancel (pInf E) (rt g) (vInf v) (vInf ξ)).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, vInf, map_sum, map_mul]
    have e2 : ptF (rt g) v ⬝ᵥ ((GeneralLinearGroup.map (pFin E) (rt g)⁻¹).val *ᵥ vFin ξ)
        = algebraMap E (Af E) (v ⬝ᵥ ξ) := by
      refine (dot_cancel (pFin E) (rt g) (vFin v) (vFin ξ)).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, vFin, map_sum, map_mul]
    have hv' : ptF (rt g) v ∈ L := by rw [(hR g).2.2]; exact hv
    rw [e1]
    rcases hsep (v ⬝ᵥ ξ) ⟨(_, _), ⟨hv', h1⟩, e2⟩ with h | h
    · left; rw [h, map_zero, map_zero]
    · exact Or.inr h
end

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem trF_sub_smul {E : Type} [Field E] [NumberField E] {a : ℕ}
    (X W : Matrix (Fin a) (Fin a) (Cinf E)) (r : ℝ) :
    trF (X - r • (1 : Matrix (Fin a) (Fin a) (Cinf E))) W = trF X W - r * trF 1 W := by
  simp [trF, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]

private theorem qf_pos {E : Type} [Field E] [NumberField E] {a : ℕ} {w : Fin a → Cinf E} (hw : w ≠ 0) :
    0 < qf w := by
  rw [← norm_euc_sq]
  exact pow_pos (norm_pos_iff.2 fun h => hw (euc.map_eq_zero_iff.1 h)) 2

theorem UpperTheory.traceForm_posDef_of_totallyReal :
    Grad := by
  intro E _ _ _ a ha L hL
  obtain ⟨cA, hcA, hA⟩ := UpperTheory.hermitian_point_embedding_injective E a ha L hL
  obtain ⟨CB, hB⟩ := UpperTheory.hermitian_space_gradient_estimate E a ha L hL
  obtain ⟨c, C, N, hc, hS⟩ := UpperTheory.convex_separation_positive_distance E a ha L hL
  obtain ⟨CF, hF⟩ := UpperTheory.hermitian_space_log_estimate E a ha L hL
  have hT := (UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1
  have hq := (UpperTheory.V.Lit.Geo.qhtFacts E a).1
  set δ : ℝ := cA / 2 * c ^ 2 / (|CB| + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨(cA / 2) ^ 2, max (Real.log 2) (|CF| * (1 + Real.log (C / δ ^ N)) + 1), by positivity, fun g hg => ?_⟩
  have h2 : 2 ≤ Th L g :=
    (Real.log_le_log_iff two_pos (one_pos.trans_le (hT g).1)).1 ((le_max_left _ _).trans hg)
  obtain ⟨w, hw, hwC, hwv⟩ := hS g
  have hw0 := qf_pos hw
  have hq1 : 1 ≤ qht g := hq g
  have hsm : qf w ≤ δ := by
    by_contra hn
    have h1 : qht g ≤ C / δ ^ N := by
      rw [le_div_iff₀ (by positivity)]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0.le (not_le.1 hn).le N) (by linarith)).trans hwC
    have h3 := Real.log_le_log (by linarith) h1
    have h4 := Real.log_nonneg hq1
    have h5 := (le_max_right _ _).trans hg
    have h6 : CF * (1 + Real.log (qht g)) ≤ |CF| * (1 + Real.log (C / δ ^ N)) :=
      mul_le_mul (le_abs_self _) (by linarith) (by linarith) (abs_nonneg _)
    linarith [hF g]
  obtain ⟨r1, r2, -⟩ := UpperTheory.traceForm_cauchy_schwarz_cmDatum E a w
  have hb := hB g w c hc hwv
  have ha' := hA g h2
  have hb' : CB * qf w ^ 2 / c ^ 2 ≤ cA / 2 * qf w := by
    rw [div_le_iff₀ (by positivity)]
    have h7 : qf w * (|CB| + 1) ≤ cA / 2 * c ^ 2 := (le_div_iff₀ (by positivity)).1 hsm
    have h8 : CB ≤ |CB| + 1 := (le_abs_self _).trans (by linarith)
    calc CB * qf w ^ 2 ≤ (|CB| + 1) * qf w ^ 2 := mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = qf w * (|CB| + 1) * qf w := by ring
      _ ≤ cA / 2 * c ^ 2 * qf w := mul_le_mul_of_nonneg_right h7 hw0.le
      _ = _ := by ring
  have he : trF (dev L g).1 (vecMulVec w (star w)) =
      trF (mom L g).1 (vecMulVec w (star w)) - ell E a (toL (mom L g).1) * qf w := by
    rw [← r1, ← trF_sub_smul]
    rfl
  have h9 : cA / 2 * qf w ≤ -trF (dev L g).1 (vecMulVec w (star w)) := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right ha' hw0.le]
  have h10 := pow_le_pow_left₀ (by positivity) h9 2
  rw [neg_sq, mul_pow] at h10
  exact le_of_mul_le_mul_right (h10.trans (r2 (dev L g))) (by positivity)
