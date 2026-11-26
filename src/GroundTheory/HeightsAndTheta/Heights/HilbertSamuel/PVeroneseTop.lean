module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealFormsOnPoints
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace VeroneseTop

theorem sum_le_weighted {n : ℕ} (f : Fin n × Fin n → ℝ) (hf : ∀ i j, f (i, j) = f (j, i)) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2), (if p.1 = p.2 then (1 : ℝ) else 2) * f p =
      ∑ p, f p := by
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1), f p =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simpa using hp
    · intro p hp
      simpa using hp
    · intro p _
      rfl
    · intro p _
      rfl
    · intro p _
      exact hf p.1 p.2
  have h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2), (if p.1 = p.2 then 0 else f p) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_filter]
    congr 1
    ext p
    simp [lt_iff_le_and_ne]
  have h3 : Finset.univ.filter (fun p : Fin n × Fin n => ¬ p.1 ≤ p.2) =
      Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1) := by
    ext p
    simp
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin n × Fin n => p.1 ≤ p.2), h3, h1, h2,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> ring

theorem sum_wt_mul {D : ℕ} (a : Fin (D + 1) → ℝ) :
    ∑ q : Ix (Veronese.Idx D), Veronese.wt q * (a q.2.1.1 * a q.2.1.2) = (∑ i, a i) ^ 2 := by
  rw [Fintype.sum_sigma, Fintype.sum_unique]
  calc ∑ y : Veronese.Idx D, Veronese.wt (⟨default, y⟩ : Ix (Veronese.Idx D)) * (a y.1.1 * a y.1.2)
      = ∑ y : Veronese.Idx D, (if y.1.1 = y.1.2 then (1 : ℝ) else 2) * (a y.1.1 * a y.1.2) := rfl
    _ = ∑ p ∈ Finset.univ.filter (fun p : Fin (D + 1) × Fin (D + 1) => p.1 ≤ p.2),
          (if p.1 = p.2 then (1 : ℝ) else 2) * (a p.1 * a p.2) := by
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    _ = ∑ p : Fin (D + 1) × Fin (D + 1), a p.1 * a p.2 :=
      sum_le_weighted (fun p => a p.1 * a p.2) (fun i j => mul_comm _ _)
    _ = (∑ i, a i) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]

theorem fs_sq {J : Type} [Fintype J] (z : J → ℂ) :
    (fsMetric (ι := J)).ρ z ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  show ‖WithLp.toLp 2 z‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq]

theorem fs_nonneg {J : Type} [Fintype J] (z : J → ℂ) : 0 ≤ (fsMetric (ι := J)).ρ z :=
  norm_nonneg (WithLp.toLp 2 z)

theorem metric_nonneg (D : ℕ) (u : Ix (Veronese.Idx D) → ℂ) : 0 ≤ (Veronese.metric D).ρ u :=
  fs_nonneg (Veronese.scale D u)

theorem metric_sq (D : ℕ) (u : Ix (Veronese.Idx D) → ℂ) :
    (Veronese.metric D).ρ u ^ 2 = ∑ q, Veronese.wt q * ‖u q‖ ^ 2 := by
  show (fsMetric (ι := Ix (Veronese.Idx D))).ρ (Veronese.scale D u) ^ 2 = _
  rw [fs_sq]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hw : 0 ≤ Veronese.wt q := (Veronese.wt_pos q).le
  rw [Veronese.scale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hw]

theorem formApply_forms (D : ℕ) (w : Ix (Fin (D + 1)) → ℂ) (q : Ix (Veronese.Idx D)) :
    formApply (Veronese.forms D) w q = w ⟨(), q.2.1.1⟩ * w ⟨(), q.2.1.2⟩ := by
  simp [formApply, Veronese.forms]

theorem metric_forms (D : ℕ) (w : Ix (Fin (D + 1)) → ℂ) :
    (Veronese.metric D).ρ (formApply (Veronese.forms D) w) =
      (fsMetric (ι := Ix (Fin (D + 1)))).ρ w * (fsMetric (ι := Ix (Fin (D + 1)))).ρ w := by
  have h0 : 0 ≤ (Veronese.metric D).ρ (formApply (Veronese.forms D) w) :=
    metric_nonneg D _
  have h1 : 0 ≤ (fsMetric (ι := Ix (Fin (D + 1)))).ρ w * (fsMetric (ι := Ix (Fin (D + 1)))).ρ w :=
    mul_nonneg (fs_nonneg w) (fs_nonneg w)
  refine (sq_eq_sq₀ h0 h1).1 ?_
  have hw : (fsMetric (ι := Ix (Fin (D + 1)))).ρ w * (fsMetric (ι := Ix (Fin (D + 1)))).ρ w =
      ∑ i : Fin (D + 1), ‖w ⟨(), i⟩‖ ^ 2 := by
    rw [← sq, fs_sq, Fintype.sum_sigma, Fintype.sum_unique]
  rw [hw, metric_sq, ← sum_wt_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [formApply_forms, norm_mul, mul_pow]

theorem isMultiHomog_forms (D : ℕ) (q : Ix (Veronese.Idx D)) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (Veronese.forms D q) ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) := by
  have h := Inter.AvoidRing.isMultiHomog_mul
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.1)
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.2)
  have e : ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) = Pi.single () 1 + Pi.single () 1 := by
    funext k
    cases k
    simp
  rw [e]
  exact h

theorem isBasePtFree_forms (D : ℕ) : IsBasePtFree (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) := by
  intro k₂ i
  refine ⟨2, Ideal.mem_sup_right (Ideal.subset_span ⟨⟨(i (), i ()), le_rfl⟩, ?_⟩)⟩
  cases k₂
  simp [Veronese.forms, pow_two]

theorem tensor_self {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} (hF : IsIntersectionFamily F)
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n) {T : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hT : IsSmoothHerm T) :
    F P n (fun _ => T.tensor T) = 2 ^ n * F P n (fun _ => T) := by
  have hTT : IsSmoothHerm (T.tensor T) := hT.mul hT
  have intersection_update_fsHerm_neg_one : ∀ L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ i, IsSmoothHerm (L i)) → ∀ j : Fin n,
      F P n (Function.update L j (T.tensor T)) = 2 * F P n (Function.update L j T) := by
    intro L hL j
    cases n with
    | zero => exact j.elim0
    | succ m =>
      have e : ∀ X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm X →
          F P (m + 1) (Function.update L j X) =
            F P (m + 1) (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
        intro X hX
        rw [← Inter.ThmIMultilin.update_comp_swap]
        exact (hF.1 P (m + 1) _ _ hP (Inter.ThmIMultilin.smooth_update hL j hX)).symm
      rw [e _ hTT, e T hT, hF.2.1 P m _ T T hP (fun i => hL _) hT hT]
      ring
  have step : ∀ k, k ≤ n →
      F P n (fun i => if (i : ℕ) < k then T.tensor T else T) = 2 ^ k * F P n (fun _ => T) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hL : ∀ i : Fin n, IsSmoothHerm (if (i : ℕ) < k then T.tensor T else T) := by
        intro i
        split_ifs
        · exact hTT
        · exact hT
      have h1 : (fun i : Fin n => if (i : ℕ) < k + 1 then T.tensor T else T) =
          Function.update (fun i : Fin n => if (i : ℕ) < k then T.tensor T else T) ⟨k, hk⟩ (T.tensor T) := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp
        · have h' : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
          rw [Function.update_of_ne h]
          by_cases hi : (i : ℕ) < k
          · simp [hi, show (i : ℕ) < k + 1 by omega]
          · simp [hi, show ¬ (i : ℕ) < k + 1 by omega]
      have h2 : Function.update (fun i : Fin n => if (i : ℕ) < k then T.tensor T else T) ⟨k, hk⟩ T =
          fun i : Fin n => if (i : ℕ) < k then T.tensor T else T := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp
        · rw [Function.update_of_ne h]
      rw [h1, intersection_update_fsHerm_neg_one _ hL, h2, ih (by omega), pow_succ]
      ring
  have hn := step n le_rfl
  simp only [Fin.is_lt, ite_true] at hn
  exact hn

end VeroneseTop


open VeroneseTop in
theorem VeroneseTop.proof (hCM : GraphChangeOfModel.Statement) (hA : VeroneseArith.Statement)
    (hIm : VeroneseGraphImage.Statement) (hDeg : VeroneseGraphDeg.Statement) : VeroneseTop.Statement := by
  intro D hD I hI
  obtain ⟨G, J, hJ, hJ1⟩ := hDeg D hD
  have hfs : IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))) :=
    BlockImageTop.isSmoothHerm_ofCone ProjLine.isSmoothMetric_fs
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (D + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot D
  have key := hCM I hI Unit (GlobalTheory (Fin (D + 1))) Unit (GlobalTheory (Veronese.Idx D)) ⊥ (D + 1) (Veronese.forms D)
    (fun _ _ => 2) G J (fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone (Veronese.metric D))
    (fun _ => (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))).tensor
      (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))))
    hP (isMultiHomog_forms D) (isBasePtFree_forms D) (by rw [hIm D]; exact hA D hD) hJ
    (fun _ => BlockImageTop.isSmoothHerm_ofCone (Veronese.isSmoothMetric_metric D)) (fun _ => hfs.mul hfs)
    (fun _ k => by cases k; simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone])
    (fun _ z _ => (metric_forms D z).symm)
  rw [hIm D, hJ1] at key
  have h2 := tensor_self (hI Unit (GlobalTheory (Fin (D + 1)))) hP hfs
  rw [Int.cast_one, one_mul] at key
  rw [top, hhOf, ← key, ← h2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockMeasureChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory Matrix
  SupBoundCount

noncomputable section

namespace BlockMeasureChange

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem sup_one_le (hS : SupBoundBlock.Statement) (d : HSMBlockDatum D K ι Ω) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ F : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F (blockDeg d.k₀ n) →
      ∀ z ∈ mcPts (mCoordIdeal d.y),
        ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ (C * (n : ℝ) ^ ((D : ℝ) / 2)) * blockL2Norm d n F := by
  obtain ⟨C, hC⟩ := hS D K ι Ω d
  refine ⟨max C 1, le_max_right _ _, fun n hn F hF z hz => (hC n hn F hF z hz).trans ?_⟩
  have h0 : 0 ≤ blockL2Norm d n F := Real.sqrt_nonneg _
  have h1 : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) h1) h0

theorem integral_le_of_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ}
    {c : ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgc : ∀ x, g x ≤ c) : ∫ x, g x ∂μ ≤ c := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := c)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hg0 x)]; exact hgc x)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

theorem quad_nonneg (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f k) (blockDeg d.k₀ n)) (a : Fin r → ℝ) :
    0 ≤ a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) := by
  rw [gram_quad d n f hf a]
  have hp : ∀ (w : ℂ) (t : ℝ), 0 ≤ ‖w‖ ^ 2 / t ^ (2 * n) := fun w t =>
    div_nonneg (sq_nonneg _) (by rw [pow_mul']; exact sq_nonneg _)
  have := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n)) fun x => hp _ _
  have := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n))
    fun x => hp _ _
  positivity

theorem quad_le (d d' : HSMBlockDatum D K ι Ω) (hy : d'.y = d.y) (hk : d'.k₀ = d.k₀) (hA : d'.A = d.A) (n : ℕ)
    {r : ℕ} (f : Fin r → MRing ι) (hf : ∀ k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f k) (blockDeg d.k₀ n)) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ F : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n F) (a : Fin r → ℝ) :
    a ⬝ᵥ (blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) ≤
      c ^ 2 * (a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)) := by
  have hf' : ∀ k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f k) (blockDeg d'.k₀ n) := fun k => by rw [hk]; exact hf k
  have := d'.vol.1
  have hQ := quad_nonneg d n f hf a
  set Q := a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)
  have hpt : ∀ z ∈ mcPts (mCoordIdeal d.y), ‖comb f a z‖ ^ 2 / d.A.h z ^ (2 * n) ≤ c ^ 2 * Q := by
    intro z hz
    have h1 := sup_real d n f hf hc hsup a hz
    have h0 : 0 ≤ ‖comb f a z‖ / d.A.h z ^ n :=
      div_nonneg (norm_nonneg _) (pow_pos (d.A.pos z hz.1) n).le
    have h2 := pow_le_pow_left₀ h0 h1 2
    rwa [div_pow, ← pow_mul', mul_pow, Real.sq_sqrt hQ] at h2
  have hp : ∀ (w : ℂ) (t : ℝ), 0 ≤ ‖w‖ ^ 2 / t ^ (2 * n) := fun w t =>
    div_nonneg (sq_nonneg _) (by rw [pow_mul']; exact sq_nonneg _)
  have hmem : ∀ x, blockPt d' x ∈ mcPts (mCoordIdeal d.y) := fun x => hy ▸ blockPt_mem d' x
  rw [gram_quad d' n f hf' a, hA]
  have i1 := integral_le_of_le d'.dV (fun x => hp _ _) fun x => hpt _ (hmem x)
  have i2 := integral_le_of_le d'.dV (fun x => hp _ _) fun x => hpt _ (conjPt_mem_mcPts (hmem x))
  linarith

theorem det_le {r : ℕ} {G G' : Matrix (Fin r) (Fin r) ℝ} (hG : G.IsHermitian) (hG' : G'.PosSemidef) {c : ℝ}
    (h : ∀ a, a ⬝ᵥ (G' *ᵥ a) ≤ c * (a ⬝ᵥ (G *ᵥ a))) : G'.det ≤ c ^ r * G.det := by
  have hH : (c • G - G').IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    have e1 := hG.apply i j
    have e2 := hG'.1.apply i j
    simp only [star_trivial] at e1 e2 ⊢
    simp only [Matrix.sub_apply, Matrix.smul_apply, e1, e2]
  have hpsd : (c • G - G').PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun a => ?_
    rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linarith [h a]
  have := GroundTheory.Heights₂.Heights.MCDet.re_det_mono hG' (by simpa using hpsd)
  simpa [det_smul] using this

end BlockMeasureChange


open BlockMeasureChange in
theorem BlockMeasureChange.proof (hS : SupBoundBlock.Statement) : BlockMeasureChange.Statement := by
  intro D K _ _ ι _ Ω _ _ d d' hy hk hA
  obtain ⟨C, hC, hsup⟩ := sup_one_le hS d
  obtain ⟨C', hC', hsup'⟩ := sup_one_le hS d'
  set L := max C C' with hL
  have hL1 : 1 ≤ L := hC.trans (le_max_left _ _)

  have key : ∀ n : ℕ, 1 ≤ n → |blockChi d' n - blockChi d n| ≤
      (2 * L ^ 2 * (Real.log L + D)) * ((n : ℝ) ^ D * (1 + Real.log n)) := by
    intro n hn
    have hex := exists_isSecBasisM d.y d.k₀ n
    have hb := hex.choose_spec
    choose f hf hfe using hb.1
    have hbf : hex.choose.2 = fun j => map (Int.castRingHom ℚ) (f j) := funext hfe
    have hf' : ∀ k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f k) (blockDeg d'.k₀ n) := fun k => by rw [hk]; exact hf k
    have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
      have := hb.2.1
      simp only [hbf, SupBoundCount.aeval_map_int] at this
      exact this
    have hli' : LinearIndependent ℤ fun k => aeval d'.y (f k) := by rw [hy]; exact hli
    have hsame : ∀ (y' : (Σ k, ι k) → Ω) (k' : K), y' = d.y → k' = d.k₀ →
        ∀ h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM y' k' n p.2,
          h.choose = hex.choose := by
      rintro _ _ rfl rfl h; rfl
    have hex' : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d'.y d'.k₀ n p.2 := by
      rw [hy, hk]; exact hex
    have e1 : blockChi d n = -(1 / 2) *
        Real.log (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))).det := by
      rw [blockChi, dite_eq_left hex, hbf]
    have e2 : blockChi d' n = -(1 / 2) *
        Real.log (blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j))).det := by
      rw [blockChi, dite_eq_left hex', hsame _ _ hy hk hex', hbf]
    set G := blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))
    set G' := blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j))
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set s := (n : ℝ) ^ ((D : ℝ) / 2) with hs
    have hs1 : 1 ≤ s := Real.one_le_rpow hnR (by positivity)
    have hs2 : s ^ 2 = (n : ℝ) ^ D := by
      rw [hs, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1
      ring
    have hlogs : Real.log s = (D / 2) * Real.log n := by
      rw [hs, Real.log_rpow (by positivity)]
    set c := C * s
    set c' := C' * s
    have hc : 1 ≤ c := one_le_mul_of_one_le_of_one_le hC hs1
    have hc' : 1 ≤ c' := one_le_mul_of_one_le_of_one_le hC' hs1
    have hG : G.PosDef := gram_posDef d n f hf hli (by linarith) (hsup n hn)
    have hG' : G'.PosDef := gram_posDef d' n f hf' hli' (by linarith) (hsup' n hn)
    have q1 := quad_le d d' hy hk hA n f hf (by linarith) (hsup n hn)
    have q2 := quad_le d' d hy.symm hk.symm hA.symm n f hf' (by linarith) (hsup' n hn)
    have d1 := det_le hG.isHermitian hG'.posSemidef q1
    have d2 := det_le hG'.isHermitian hG.posSemidef q2
    have hr := SupBoundCount.rank_le d n f hf hli (by linarith) (hsup n hn)
    have p1 := hG.det_pos
    have p2 := hG'.det_pos
    have l1 : Real.log G'.det ≤ hex.choose.1 * Real.log (c ^ 2) + Real.log G.det := by
      rw [← Real.log_pow, ← Real.log_mul (by positivity) p1.ne']
      exact Real.log_le_log p2 d1
    have l2 : Real.log G.det ≤ hex.choose.1 * Real.log (c' ^ 2) + Real.log G'.det := by
      rw [← Real.log_pow, ← Real.log_mul (by positivity) p2.ne']
      exact Real.log_le_log p1 d2
    have lc : Real.log c ≤ Real.log L + D * Real.log n := by
      have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
      rw [Real.log_mul (by linarith) (by linarith), hlogs]
      have := Real.log_le_log (by linarith) (le_max_left C C')
      nlinarith
    have lc' : Real.log c' ≤ Real.log L + D * Real.log n := by
      have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
      rw [Real.log_mul (by linarith) (by linarith), hlogs]
      have := Real.log_le_log (by linarith) (le_max_right C C')
      nlinarith
    have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
    have hlc' : 0 ≤ Real.log c' := Real.log_nonneg hc'
    have hr0 : (0 : ℝ) ≤ (hex.choose.1 : ℝ) := Nat.cast_nonneg _
    have hrb : (hex.choose.1 : ℝ) ≤ 2 * L ^ 2 * (n : ℝ) ^ D := by
      have : c ^ 2 ≤ L ^ 2 * (n : ℝ) ^ D := by
        rw [mul_pow, hs2]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (le_max_left _ _) 2) (by positivity)
      linarith
    rw [Real.log_pow] at l1 l2
    push_cast at l1 l2
    have hdiff : |blockChi d' n - blockChi d n| ≤ hex.choose.1 * (Real.log L + D * Real.log n) := by
      have m1 := mul_le_mul_of_nonneg_left lc hr0
      have m2 := mul_le_mul_of_nonneg_left lc' hr0
      rw [e1, e2, abs_le]
      constructor <;> linarith
    have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
    have hlL : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hnD : 0 ≤ (n : ℝ) ^ D := by positivity
    refine hdiff.trans ?_
    calc (hex.choose.1 : ℝ) * (Real.log L + D * Real.log n)
        ≤ (2 * L ^ 2 * (n : ℝ) ^ D) * (Real.log L + D * Real.log n) :=
          mul_le_mul_of_nonneg_right hrb (by positivity)
      _ ≤ (2 * L ^ 2 * (Real.log L + D)) * ((n : ℝ) ^ D * (1 + Real.log n)) := by
          have : Real.log L + D * Real.log n ≤ (Real.log L + D) * (1 + Real.log n) := by
            have h3 : 0 ≤ Real.log L * Real.log n := mul_nonneg hlL hln
            have h4 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
            have e : (Real.log L + D) * (1 + Real.log n) =
                Real.log L + D * Real.log n + (D + Real.log L * Real.log n) := by ring
            rw [e]
            linarith
          calc (2 * L ^ 2 * (n : ℝ) ^ D) * (Real.log L + D * Real.log n)
              ≤ (2 * L ^ 2 * (n : ℝ) ^ D) * ((Real.log L + D) * (1 + Real.log n)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring

  have hO : (fun n : ℕ => blockChi d' n - blockChi d n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D * (1 + Real.log n) := by
    refine IsBigO.of_bound (2 * L ^ 2 * (Real.log L + D)) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (key n hn).trans (le_of_eq ?_)
    congr 1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (mul_nonneg (by positivity) (by linarith [Real.log_nonneg hnR]))]
  have hlog : (fun n : ℕ => 1 + Real.log n) =o[atTop] fun n : ℕ => (n : ℝ) := by
    have h1 := (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
    have h2 := Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
    exact h1.add h2
  have ho : (fun n : ℕ => (n : ℝ) ^ D * (1 + Real.log n)) =o[atTop] pw D := by
    have := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO hlog
    refine this.congr_right fun n => ?_
    simp [pw, pow_succ]
  exact hO.trans_isLittleO ho

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftSectionSeparation
section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample
section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample.Objects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder

namespace Line

end Line

section FS


end FS

section Reg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure WeightReg (ι : K → Type) [∀ k, Fintype (ι k)] where

  reg : ℝ → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι
  deg : ∀ t A, (reg t A).a = A.a
  smooth : ∀ t A, IsSmoothHerm A → IsSmoothHerm (reg t A)
  shift : ∀ t (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (k : ℝ), 0 < k → A'.a = A.a →
    (∀ z : (Σ b, ι b) → ℂ, (∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) → A'.h z = k * A.h z) →
    ∀ z : (Σ b, ι b) → ℂ, (∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) → (reg t A').h z = k * (reg t A).h z


open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet in
def weightRegRef : WeightReg (PBlk 2) where
  reg _ A := (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := PBlk 2 k)) A.a).tensor
    (constLine (A.h (fun _ => 1) / (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := PBlk 2 k)) A.a).h (fun _ => 1))
      (div_pos (A.pos _ fun _ => ⟨0, one_ne_zero⟩)
        ((ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := PBlk 2 k)) A.a).pos _ fun _ => ⟨0, one_ne_zero⟩)))
  deg _ A := by simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, constLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics]
  smooth _ A _ := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor (Inter.isSmoothHerm_ofMetrics_fs _) (isSmoothHerm_constLine _ _)
  shift _ A A' k hk ha hh z _ := by
    have h1 := hh (fun _ => 1) fun _ => ⟨0, one_ne_zero⟩
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, constLine, ha, h1]
    ring

end Reg

section Heights

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

end Heights

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo Line

section Curve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem inter_constLine_eq [Nonempty K] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    (hH : IsMultiHomogIdeal W) (hdeg : 0 < degC W) (M : ℝ) (hM : 0 < M) :
    I W 1 ![constLine M hM] = Real.log M * degC W := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW (isSmoothHerm_constLine M hM) (d := 0) (fun k ↦ rfl)
    (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one]
  have h : logNorm (constLine (ι := ι) M hM) 1 = fun _ ↦ -Real.log M := by
    funext z
    simp [logNorm, constLine, Real.log_inv]
  have hfin : Finite (projPts W) := by
    rw [degC_eq_card_projPts] at hdeg
    exact (Nat.card_pos_iff.mp hdeg).2
  have key : ∀ φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ, ptsIntegral W φ (fun _ ↦ (1 : ℝ)) = degC W := by
    intro φ
    obtain rfl : φ = Fin.elim0 := funext fun j ↦ j.elim0
    rw [PtsIntegralPoints.homogProof K ι W (fun _ ↦ 1) hH hfin (fun _ _ _ _ ↦ rfl),
      degC_eq_card_projPts]
    have := Fintype.ofFinite (projPts W)
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  unfold arInt
  rw [h, Inter.Conservation.ptsIntegral_const, key]
  ring

end Curve

section Point

def ptIdeal : Ideal (MRing (PBlk 2)) := orbitIdeal samplePoint

end Point

section Shift


end Shift

section Main

end Main

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine constLine isSmoothHerm_powLine isSmoothHerm_constLine
  inter_tensor inter_powLine)

noncomputable section

namespace ShiftSectionSeparation

variable {K : Type} [Fintype K] {ι : K → Type}

theorem hermLine_ext {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

theorem powLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m : ℕ) (z : (Σ k, ι k) → ℂ) : (powLine A m).h z = A.h z ^ m := by
  induction m with
  | zero => simp [powLine, constLine]
  | succ m ih => simp [powLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ih, pow_succ]

theorem zcomb_eq [∀ k, Fintype (ι k)] (A H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (q : ℕ) :
    HermLine.zcomb A H (q : ℤ) 1 = (powLine A q).tensor H := by
  refine hermLine_ext ?_ ?_
  · funext k
    simp [HermLine.zcomb, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, IndefiniteRowSideFullHecke.HeightsSet.powLine_a]
  · funext z
    simp [HermLine.zcomb, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, powLine_h]

end ShiftSectionSeparation


open ShiftSectionSeparation in
theorem ShiftSectionSeparation.proof (h₁ : ArithIntersectionSystemStatement)
    (h₂ : IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement) (h₃ : SmallSectionPointHeight.Statement) :
    ShiftSectionSeparation.Statement := by
  intro K _ ι _ Ω _ y D A hP hy hA
  obtain ⟨II, hII⟩ := h₁
  have hIS : IsIntersectionSystem II := hII.1
  have hI : IsIntersectionFamily (II K ι) := hIS K ι
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  obtain ⟨C₀, F, hF, hFW⟩ := h₂ K ι (II K ι) (mCoordIdeal y) D (fsH ι) hI hP hH rfl
  obtain ⟨k, C₁, hk⟩ := IndefiniteRowSideFullHecke.HeightsSet.HeightComparison.proof IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full
    K ι (II K ι) A (fsH ι) hI hA hH rfl
  refine ⟨|(k : ℝ) * C₀ + C₁| + |C₀|, by positivity, fun q _ n s hs hs0 c hc hb => ?_⟩
  set C := |(k : ℝ) * C₀ + C₁| + |C₀| with hC
  rw [zcomb_eq] at hs hb
  set N := (powLine A q).tensor (fsH ι) with hNdef
  have hN : IsSmoothHerm N := isSmoothHerm_tensor (isSmoothHerm_powLine hA q) hH
  set X := C * n * ((q : ℝ) + 1) with hX
  set c₁ := max c (Real.exp (-X) / 2) with hc₁
  have hc₁pos : 0 < c₁ := lt_max_of_lt_right (by positivity)
  have hc₁lt : c₁ < Real.exp (-X) := max_lt hc (by linarith [Real.exp_pos (-X)])
  set B := (powLine N n).tensor (constLine c₁ hc₁pos) with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_tensor (isSmoothHerm_powLine hN n) (isSmoothHerm_constLine _ _)
  have hBa : ∀ k, ((1 : ℕ) : ℤ) * B.a k = (n : ℤ) * N.a k := fun k => by
    simp [hBdef, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, IndefiniteRowSideFullHecke.HeightsSet.powLine_a, constLine]
  have hsB : s ∈ chartLat y B.a 1 := by
    intro c' hc'
    have h := hs c' hc'
    simp only [hBa]
    exact h
  have hsmall : IsSmallH (mCoordIdeal y) y B 1 s := by
    intro dg dh g h z hg hh hd hgh hz
    have hd' : ∀ k, (dg k : ℤ) = dh k + n * N.a k := fun k => by rw [hd k, hBa k]
    have h1 := hb dg dh g h z hg hh hd' hgh hz
    have hBh : B.h z = N.h z ^ n * c₁ := by simp [hBdef, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, powLine_h, constLine]
    have hnn : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * N.h z ^ n :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (N.pos z hz.1).le _)
    rw [pow_one, hBh]
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * N.h z ^ n := h1
      _ ≤ c₁ * (‖eval z (map (Int.castRingHom ℂ) h)‖ * N.h z ^ n) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
      _ = _ := by ring
  obtain ⟨f, hfd, hfP, hfW⟩ := h₃ K ι Ω y D B 1 s II hIS hP hy hB le_rfl
    (SmallSectionPointHeight.chartLat_le_chartLatNm _ _ _ hsB) hs0 hsmall
  obtain ⟨W, hWF, hfW'⟩ := hF f hfd hfP
  obtain ⟨hW, hPW, hWH⟩ := hFW W hWF
  have h0 := hfW W hW hPW hfW'
  have : Nonempty K := hW.1
  have hdegN := LowerBoundFree.degC_pos_of_isArithVar_one hW
  have hdeg : (0 : ℝ) < degC W := Nat.cast_pos.2 hdegN
  rw [hBdef, inter_tensor _ hI hW (isSmoothHerm_powLine hN n) (isSmoothHerm_constLine _ _),
    inter_powLine _ hI hW hN n, hNdef, inter_tensor _ hI hW (isSmoothHerm_powLine hA q) hH,
    inter_powLine _ hI hW hA q,
    LowerBoundFree.inter_constLine_eq _ hI hW hW.2.1.2.1 hdegN c₁ hc₁pos] at h0
  have hcmp := hk W hW
  simp only [IndefiniteRowSideFullHecke.HeightsSet.height] at hcmp hWH
  set d : ℝ := (degC W : ℝ)
  set a := II K ι W 1 ![A] / d with ha
  set b := II K ι W 1 ![fsH ι] / d with hb'
  have hIA : II K ι W 1 ![A] = a * d := by rw [ha]; field_simp
  have hIH : II K ι W 1 ![fsH ι] = b * d := by rw [hb']; field_simp
  rw [hIA, hIH] at h0
  have hkey : 0 ≤ (n : ℝ) * ((q : ℝ) * a + b) + Real.log c₁ := by
    have e : (n : ℝ) * ((q : ℝ) * (a * d) + b * d) + Real.log c₁ * d =
        d * ((n : ℝ) * ((q : ℝ) * a + b) + Real.log c₁) := by ring
    rw [e] at h0
    exact (mul_nonneg_iff_of_pos_left hdeg).mp h0
  have hak : a ≤ (k : ℝ) * C₀ + C₁ := by
    have := mul_le_mul_of_nonneg_left hWH (Nat.cast_nonneg (α := ℝ) k)
    linarith [le_abs_self a]
  have hq1 : (q : ℝ) * a ≤ (q : ℝ) * C :=
    mul_le_mul_of_nonneg_left (hak.trans ((le_abs_self _).trans (by rw [hC]; linarith [abs_nonneg C₀])))
      (Nat.cast_nonneg q)
  have hb1 : b ≤ C := hWH.trans ((le_abs_self _).trans (by rw [hC]; linarith [abs_nonneg ((k : ℝ) * C₀ + C₁)]))
  have h2 : (n : ℝ) * ((q : ℝ) * a + b) ≤ (n : ℝ) * (C * ((q : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg n)
  have hlog : Real.log c₁ < -X := by
    have := Real.log_lt_log hc₁pos hc₁lt
    rwa [Real.log_exp] at this
  rw [hX] at hlog
  nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
