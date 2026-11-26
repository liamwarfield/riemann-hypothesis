module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveDegreeVert
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveDegreeVert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

noncomputable section

namespace CurveDegreeVert

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def fsLine (b : K → ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (b k : ℤ))

theorem isSmoothHerm_fsLine (b : K → ℕ) : IsSmoothHerm (fsLine b : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := by
  have hfun : (fsLine b : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι).h =
      fun z => ∏ k, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) ^ b k := by
    funext z
    simp only [fsLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics, fsMetric, zpow_natCast, EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => (ContDiffOn.sqrt ?_ fun z hz => ?_).pow (b k)
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_refl (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), by funext p; simp [mul_assoc]⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sum_eq_of_transversal {P : Ideal (MRing ι)} {R R' : Finset ((Σ k, ι k) → ℂ)}
    (hRP : ∀ t ∈ R, t ∈ mcPts P) (hRu : ∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t)
    (hR'P : ∀ t ∈ R', t ∈ mcPts P) (hR'u : ∀ z ∈ mcPts P, ∃! t, t ∈ R' ∧ SameOrbit z t)
    (h : ((Σ k, ι k) → ℂ) → ℝ) (hh : ∀ z z', z ∈ mcPts P → SameOrbit z z' → h z = h z') :
    ∑ t ∈ R, h t = ∑ t ∈ R', h t := by
  refine Finset.sum_bij (fun t ht => (hR'u t (hRP t ht)).exists.choose)
    (fun t ht => (hR'u t (hRP t ht)).exists.choose_spec.1) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ he
    have e1 := (hR'u t₁ (hRP t₁ h₁)).exists.choose_spec.2
    have e2 := (hR'u t₂ (hRP t₂ h₂)).exists.choose_spec.2
    rw [he] at e1
    exact (hRu t₂ (hRP t₂ h₂)).unique ⟨h₁, sameOrbit_trans e2 (sameOrbit_symm e1)⟩ ⟨h₂, sameOrbit_refl t₂⟩
  · intro t' ht'
    obtain ⟨t, ⟨htR, hto⟩, -⟩ := hRu t' (hR'P t' ht')
    exact ⟨t, htR, (hR'u t (hRP t htR)).unique (hR'u t (hRP t htR)).exists.choose_spec
      ⟨ht', sameOrbit_symm hto⟩⟩
  · intro t ht
    exact hh _ _ (hRP t ht) (hR'u t (hRP t ht)).exists.choose_spec.2

theorem logNorm_sameOrbit {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    logNorm A s z = logNorm A s z' := by
  obtain ⟨c, hc, rfl⟩ := h
  unfold logNorm
  have hn : ∏ k, ‖c k‖ ^ A.a k = ‖∏ k, c k ^ a k‖ := by
    simp [ha, norm_prod, norm_pow]
  have h0 : ‖∏ k, c k ^ a k‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  rw [eval_smul_homog s a hs c z', A.smul c z' hc, norm_mul, hn, mul_div_mul_left _ _ h0]

omit [∀ k, Fintype (ι k)] in
theorem norm_eval_curveChartMono (c : ∀ k, ι k) (e : K → ℕ) (z : (Σ k, ι k) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) (curveChartMono c e))‖ = ∏ k, ‖z ⟨k, c k⟩‖ ^ e k := by
  simp [curveChartMono, map_prod, norm_prod]

theorem proof : CurveDegreeVert.Statement := by
  intro K _ ι _ P A II c R b d hII hP hA hc hRP hRu hd
  have hI := hII K ι
  have hpr : P.IsPrime := hP.2.1.1
  have hL : ∀ j, IsSmoothHerm ((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) := fun j => j.elim0
  have hsnoc : ∀ C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι,
      (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) C : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = fun _ => C :=
    fun C => funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl
  have hmono : ∀ e : K → ℕ, curveChartMono c e ∉ P := by
    intro e h
    rw [curveChartMono, hpr.prod_mem_iff] at h
    obtain ⟨k, _, hk⟩ := h
    exact hc k (hpr.mem_of_pow_mem _ hk)
  set B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fsLine b with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_fsLine b
  have hBa : ∀ k, B.a k = b k := fun k => rfl
  have hABa : ∀ k, (A.tensor B).a k = d k := fun k => by
    show A.a k + B.a k = d k
    rw [hBa, hd k]
  have hsd : IsSectionOn P (A.tensor B) (curveChartMono c d) :=
    ⟨d, hABa, isMultiHomog_curveChartMono c d, hmono d⟩
  have hsb : IsSectionOn P B (curveChartMono c b) := ⟨b, hBa, isMultiHomog_curveChartMono c b, hmono b⟩

  have hnz : ∀ z ∈ mcPts P, ∀ k, z ⟨k, c k⟩ ≠ 0 := by
    intro z hz k
    have hs1 : IsSectionOn P (fsLine (fun _ => 1) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c fun _ => 1) :=
      ⟨fun _ => 1, fun _ => rfl, isMultiHomog_curveChartMono c _, hmono _⟩
    have h1 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne arithVarZero hP hs1 hz)
    rw [norm_eval_curveChartMono] at h1
    have h2 := Finset.prod_ne_zero_iff.mp h1 k (Finset.mem_univ k)
    simpa using h2

  have hadd := hI.2.1 P 0 Fin.elim0 A B hP hL hA hB
  have hRd := hI.2.2 P 0 Fin.elim0 (A.tensor B) (curveChartMono c d) d hP hL
    (hA.mul hB) hABa (isMultiHomog_curveChartMono c d) (hmono d)
  have hRb := hI.2.2 P 0 Fin.elim0 B (curveChartMono c b) b hP hL hB hBa
    (isMultiHomog_curveChartMono c b) (hmono b)
  rw [hsnoc, hsnoc, hsnoc] at hadd
  rw [hsnoc] at hRd hRb
  rw [recR_eq, cycR_eq_vertR_of_dimOne arithVarZero _ hP hsd] at hRd
  rw [recR_eq, cycR_eq_vertR_of_dimOne arithVarZero _ hP hsb] at hRb

  obtain ⟨R', hR'P, hR'u, hsum⟩ := regularityPointsSum_holds.proof K ι P hP
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) => Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).h z)) =
      (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := funext fun j => j.elim0
  have hint : ∀ (C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (e : K → ℕ), (∀ k, C.a k = e k) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s e →
      arInt P s C (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ∑ t ∈ R, logNorm C s t := by
    intro C s e hCe hse
    have hinv : ∀ z z', z ∈ mcPts P → SameOrbit z z' → logNorm C s z = logNorm C s z' :=
      fun z z' _ h => logNorm_sameOrbit hCe hse h
    rw [arInt, hφ, hsum _ hinv]
    exact (sum_eq_of_transversal hRP hRu hR'P hR'u _ hinv).symm
  rw [hint _ _ d hABa (isMultiHomog_curveChartMono c d)] at hRd
  rw [hint _ _ b hBa (isMultiHomog_curveChartMono c b)] at hRb

  have hpt : ∀ t ∈ R, logNorm B (curveChartMono c b) t - logNorm (A.tensor B) (curveChartMono c d) t =
      Real.log (chartRadius A c t) := by
    intro t ht
    have hz := hRP t ht
    have hk := hnz t hz
    have hApos := A.pos t hz.1
    have hBpos := B.pos t hz.1
    have hpos : ∀ e : K → ℕ, 0 < ∏ k, ‖t ⟨k, c k⟩‖ ^ e k := fun e =>
      Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hk k)) _
    have hsplit : ∏ k, ‖t ⟨k, c k⟩‖ ^ d k =
        (∏ k, ‖t ⟨k, c k⟩‖ ^ b k) * ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (norm_ne_zero_iff.mpr (hk k)), hd k, add_comm]
    unfold logNorm chartRadius
    rw [norm_eval_curveChartMono, norm_eval_curveChartMono, show (A.tensor B).h t = A.h t * B.h t from rfl,
      ← Real.log_div (div_pos (hpos b) hBpos).ne' (div_pos (hpos d) (mul_pos hApos hBpos)).ne', hsplit]
    congr 1
    have := hpos b
    have hq : 0 < ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hk k)) _
    field_simp
  rw [← Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
  linarith

end CurveDegreeVert

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSClosed
section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelSectionsLarge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelSectionsLarge

theorem chartMonomial_mem_relSecM {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (b : K → ℕ) :
    ∏ k, y ⟨k, c0 k⟩ ^ b k ∈ relSecM R y b := by
  classical
  have h := monomial_mem_relSecM R y (b := b) (fun p => if p.2 = c0 p.1 then b p.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single (c0 k) (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem descend {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (n₁ : ℕ)
    (hstep : ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → ∀ k0 : K,
      ∀ t ∈ relChartLat R y (fun k => (b k : ℤ)) 1, y ⟨k0, c0 k0⟩ * t ∈ relSecM R y (b + Pi.single k0 1) →
        t ∈ relSecM R y b) :
    ∀ (m : ℕ) (e : K → ℕ), ∑ k, e k = m → ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) →
      ∀ s ∈ relChartLat R y (fun k => (b k : ℤ)) 1,
        s * ∏ k, y ⟨k, c0 k⟩ ^ e k ∈ relSecM R y (b + e) → s ∈ relSecM R y b := by
  intro m
  induction m with
  | zero =>
    intro e he b _ s _ hs
    have h0 : e = 0 := funext fun k => by
      simpa using (Finset.sum_eq_zero_iff.mp he) k (Finset.mem_univ k)
    subst h0
    simpa using hs
  | succ m ih =>
    intro e he b hb s hsL hs
    obtain ⟨k0, hk0⟩ : ∃ k0, 0 < e k0 := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : ∑ k, e k = 0 := Finset.sum_eq_zero fun k _ => Nat.le_zero.mp (hcon k)
      omega
    set e' : K → ℕ := e - Pi.single k0 1 with he'
    have hee : e = e' + Pi.single k0 1 := by
      funext k
      simp only [he', Pi.add_apply, Pi.sub_apply]
      by_cases hk : k = k0
      · subst hk; simp; omega
      · simp [hk]
    have hsum : ∑ k, e' k = m := by
      have : ∑ k, e k = ∑ k, e' k + 1 := by
        rw [hee]; simp only [Pi.add_apply]; rw [Finset.sum_add_distrib]; simp
      omega
    refine ih e' hsum b hb s hsL ?_
    have htL : s * ∏ k, y ⟨k, c0 k⟩ ^ e' k ∈ relChartLat R y (fun k => ((b + e') k : ℤ)) 1 :=
      mul_prod_mem_relChartLat R y (a := fun k => (b k : ℤ)) (a' := fun k => ((b + e') k : ℤ)) (n := 1) e' c0
        (fun k => by simp only [Pi.add_apply]; push_cast; ring) hsL
    have hb' : ∀ k, n₁ ≤ (b + e') k := fun k => le_trans (hb k) (Nat.le_add_right _ _)
    refine hstep (b + e') hb' k0 _ htL ?_
    have hprod : y ⟨k0, c0 k0⟩ * (s * ∏ k, y ⟨k, c0 k⟩ ^ e' k) = s * ∏ k, y ⟨k, c0 k⟩ ^ e k := by
      rw [hee]
      have h1 : ∏ k, y ⟨k, c0 k⟩ ^ (Pi.single k0 1 : K → ℕ) k = y ⟨k0, c0 k0⟩ := by
        rw [Fintype.prod_eq_single k0 (fun k hk => by simp [hk])]
        simp
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, h1]
      ring
    rw [hprod, add_assoc, ← hee]
    exact hs

theorem proof (hC : RelChartPoly.Statement) (hO : RelOneStep.Statement) : RelSectionsLarge.Statement := by
  classical
  intro K _ ι _ Ω _ R hR y hy
  choose c0 hc0 using hy
  obtain ⟨n₁, hn₁⟩ := hO K ι Ω R hR y c0 hc0
  refine ⟨n₁, fun b hb s hs => ?_⟩
  obtain ⟨N, hN⟩ := hC K ι Ω R y c0 _ (hs c0 hc0)
  have hform := mul_mem_relSecM R y hN (chartMonomial_mem_relSecM R y c0 b)
  refine descend R y c0 n₁ hn₁ (∑ _k : K, N) (fun _ => N) rfl b hb s hs ?_
  rw [add_comm]
  convert hform using 1
  have hcancel : (∏ k, y ⟨k, c0 k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * ∏ k, y ⟨k, c0 k⟩ ^ b k = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [Nat.cast_one, one_mul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hc0 k))]
  rw [← Finset.prod_pow]
  linear_combination (-(s * ∏ k, y ⟨k, c0 k⟩ ^ N)) * hcancel

end RelSectionsLarge

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem RelSectionsLarge.full : RelSectionsLarge.Statement :=
  RelSectionsLarge.proof RelChartPoly.proof (RelOneStep.proof RelChartPoly.proof RelTorsionBound.proof)

end GroundTheory.Heights₂.Heights.Targets
end
