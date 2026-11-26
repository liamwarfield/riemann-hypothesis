module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointUnitSection
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveDegreeVert
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem genFibreExists : GenFibreExistsStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d' _ hP'
  exact Inter.GenericPointExists.proof K ι K' ι' v P' hP'.2.1.1

theorem existsUniqueAll : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)], ExistsUniqueStatement F ι := by
  intro F _ K _ ι _
  exact ExistsUnique.full F ι

theorem ChangeOfModel.of_found (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hIso : HilbertSamuel.IsomInvariance.Statement) (hGI : HilbertSamuel.GraphIsometric.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement :=
  HilbertSamuel.ChangeOfModel.proof hAI3 hGr genFibreExists existsUniqueAll hIso hGI

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeSliceIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ConeSliceIdeal.proof : ConeSliceIdeal.Statement := by
  intro n C t V hC hV f hf
  have hℓ : (linForm t).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
  obtain ⟨G, D, hG, hGf⟩ := ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) f hℓ
  have hLG : linForm t * G ∈ V := by
    refine hV ?_
    rw [mem_vanishingIdeal_iff]
    intro c hc
    show eval c (linForm t * G) = 0
    rw [map_mul]
    by_cases hl : eval c (linForm t) = 0
    · rw [hl, zero_mul]
    · set l := eval c (linForm t)
      have hsl : eval (l⁻¹ • c) (linForm t) = 1 := by
        rw [GoodChartZeroSet.eval_smul_of_isHomogeneous hℓ, pow_one, inv_mul_cancel₀ hl]
      have hmem : l⁻¹ • c ∈ {x | x ∈ C ∧ eval x (linForm t) = 1} :=
        ⟨hC c hc _ (inv_ne_zero hl), hsl⟩
      have hf0 : eval (l⁻¹ • c) f = 0 := (mem_vanishingIdeal_iff.mp hf) _ hmem
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hGf
      have hGv : eval (l⁻¹ • c) G = 0 := by
        have h := congrArg (eval (l⁻¹ • c)) hq
        rw [map_sub, map_mul, map_sub, hsl, hf0, map_one] at h
        simpa using h
      have hc' : c = l • (l⁻¹ • c) := by rw [smul_smul, mul_inv_cancel₀ hl, one_smul]
      rw [hc', GoodChartZeroSet.eval_smul_of_isHomogeneous hG, hGv, mul_zero, mul_zero]
  have e : f = linForm t * G - (linForm t - 1) * G - (G - f) := by ring
  rw [e]
  refine Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mem_sup_left hLG) ?_) (Ideal.mem_sup_right hGf)
  exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeVanishingHomog
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset

theorem ConeVanishingHomog.proof : ConeVanishingHomog.Statement := by
  intro n C hC f hf d
  rw [mem_vanishingIdeal_iff] at hf ⊢
  intro c hc
  replace hf : ∀ x ∈ C, eval x f = 0 := hf
  show eval c (homogeneousComponent d f) = 0

  set p : Polynomial ℂ := ∑ i ∈ range (f.totalDegree + 1),
    Polynomial.C (eval c (homogeneousComponent i f)) * Polynomial.X ^ i with hp
  have hroot : ∀ a : ℂ, a ≠ 0 → p.IsRoot a := by
    intro a ha
    have h0 := hf (a • c) (hC c hc a ha)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_homogeneousComponent f, map_sum] at h0
    rw [Polynomial.IsRoot, hp, Polynomial.eval_finsetSum, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GoodChartZeroSet.eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i f)]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  have hinf : Set.Infinite {x | p.IsRoot x} := by
    refine Set.Infinite.mono (s := ({0} : Set ℂ)ᶜ) ?_
      (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro x hx
    exact hroot x (by simpa using hx)
  have hp0 : p = 0 := Polynomial.eq_zero_of_infinite_isRoot p hinf
  by_cases hd : d ≤ f.totalDegree
  · have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff d) hp0
    simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoeff
    rw [Finset.sum_ite_eq] at hcoeff
    simpa [Finset.mem_range, Nat.lt_succ_of_le hd] using hcoeff
  · rw [homogeneousComponent_eq_zero d f (by omega), map_zero]

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertIndexSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def curveSectionMod (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Submodule (curveRing y) Ω where
  carrier := chartLat y a 1
  zero_mem' := (chartLat y a 1).zero_mem
  add_mem' := fun ha hb => (chartLat y a 1).add_mem ha hb
  smul_mem' := fun b m hm c hc => by
    have hb : (b : Ω) ∈ chartRingZ y c := mem_curveRing.mp b.2 c hc
    have hm' := hm c hc
    rw [Subring.smul_def, smul_eq_mul, mul_assoc]
    exact mul_mem hb hm'

abbrev curveSectionQuot (y : (Σ k, ι k) → Ω) (a : K → ℤ) (x : Ω) : Type _ :=
  ↥(curveSectionMod y a) ⧸ (Submodule.span (curveRing y) {x}).comap (curveSectionMod y a).subtype

end Objects

def CurveSectionQuotFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      Finite (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s))

def CurveVertPointLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      Set.BijOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)
          {m | m.IsMaximal ∧ locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0} ∧
        ∀ W ∈ divSupp (mCoordIdeal y) s,
          multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
            locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s))

def CurveVertPointResidue.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s,
        (geoNum 0 W Fin.elim0 : ℝ) * Real.log (charOf W) =
          Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W))

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosDensIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsPosDensIntegrable.proof (hMass : PtsSemiPosMassFinite.Statement) : PtsPosDensIntegrable.Statement := by
  intro K _ ι _ P e Ψ L g hP hΨ hL hg
  classical
  obtain ⟨M, hMb⟩ := PtsPosDens.exists_bound hg
  choose T hTs hTp hLTp using fun j => Inter.SemiPosTwist.proof Inter.TorusInvLevi.proof K ι (L j) (hL j)
  set N : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => ((L j).tensor (T j)).tensor (T j) with hNdef
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j =>
    ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hL j) (hTs j)
  have hNs : ∀ j, IsSmoothHerm (N j) := fun j => ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hLT j) (hTs j)
  have hNp : ∀ j, Inter.IsSemiPosHerm (N j) := fun j =>
    PtsPosDens.isSemiPosHerm_tensor (hLT j) (hTs j) (hLTp j) (hTp j)
  have hfinM := hMass K ι P e Ψ N hP hΨ hNs hNp
  have hfib := fibreFinite K ι P e Ψ hP hΨ
  set C : ℝ := max M 0 * 3 ^ e with hCdef
  have hC : 0 ≤ C := by positivity

  have key : ∀ y w, max (sheetDensity P Ψ (pot L) g y w) 0 ≤
      C * max (sheetDensity P Ψ (pot N) (fun _ => 1) y w) 0 := by
    intro y w
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · rw [dite_eq_left hγ, dite_eq_left hγ]
      have hS := hγ.choose_spec
      have hab : |maDensity (fun j y' => pot L j (hγ.choose y')) y| ≤
          3 ^ e * maDensity (fun j y' => pot N j (hγ.choose y')) y :=
        Inter.PointsAbsIntegrable.abs_maDensity_le hL hTs hTp hLTp hS
      have hmc : hγ.choose y ∈ mcPts P := hS.2.self_of_nhds.2.1
      have hgb : |g (hγ.choose y)| ≤ max M 0 := (hMb _ hmc.1).trans (le_max_left _ _)
      have hn : 0 ≤ maDensity (fun j y' => pot N j (hγ.choose y')) y :=
        nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hab) (by positivity)
      calc max (g (hγ.choose y) * maDensity (fun j y' => pot L j (hγ.choose y')) y) 0
          ≤ |g (hγ.choose y) * maDensity (fun j y' => pot L j (hγ.choose y')) y| :=
            max_le (le_abs_self _) (abs_nonneg _)
        _ = |g (hγ.choose y)| * |maDensity (fun j y' => pot L j (hγ.choose y')) y| := abs_mul _ _
        _ ≤ max M 0 * (3 ^ e * maDensity (fun j y' => pot N j (hγ.choose y')) y) :=
            mul_le_mul hgb hab (abs_nonneg _) (le_max_right _ _)
        _ = C * max (1 * maDensity (fun j y' => pot N j (hγ.choose y')) y) 0 := by
            rw [one_mul, max_eq_left hn, hCdef]
            ring
    · rw [dite_eq_right hγ, dite_eq_right hγ, max_self, mul_zero]

  have hpt : ∀ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y) ≤
      ENNReal.ofReal C * ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) := by
    intro y
    rw [← ENNReal.ofReal_mul hC]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold ptsPosDens
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfib y), finsum_mem_eq_finite_toFinset_sum _ (hfib y),
      Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => key y w
  have hnn : ∀ y, 0 ≤ ptsPosDens P Ψ (pot L) g y := fun y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _
  refine ⟨PtsPosDens.aestronglyMeasurable hP hΨ hL hg, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  calc ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y)
      ≤ ∫⁻ y, ENNReal.ofReal C * ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) := lintegral_mono hpt
    _ = ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinM

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveRingFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain

noncomputable section

namespace CurveRingFiniteAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_integer_of_mem_chartRingZ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (z : (Σ k, ι k) → F) (c : ∀ k, ι k)
    (hc : ∀ p : Σ k, ι k, v.valuation F (z p) ≤ v.valuation F (z ⟨p.1, c p.1⟩)) {b : F}
    (hb : b ∈ chartRingZ z c) : b ∈ (v.valuation F).integer := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    rw [Valuation.mem_integer_iff, map_div₀]
    rcases eq_or_ne (v.valuation F (z ⟨p.1, c p.1⟩)) 0 with h0 | h0
    · simp [h0]
    · exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hc p)
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x w _ _ hx hw => exact add_mem hx hw
  | mul x w _ _ hx hw => exact mul_mem hx hw


omit [Fintype K] in
theorem mem_integralClosure {F : Type} [Field F] [NumberField F] (z : (Σ k, ι k) → F) (c0 : ∀ k, ι k)
    (hc0 : ∀ k, z ⟨k, c0 k⟩ ≠ 0) {b : F}
    (hb : ∀ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) → b ∈ chartRingZ z c) :
    b ∈ integralClosure ℤ F := by
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F b ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F b hv
    rw [← hr]
    exact r.2
  intro v
  have hmax : ∀ k, ∃ i, ∀ j, v.valuation F (z ⟨k, j⟩) ≤ v.valuation F (z ⟨k, i⟩) := fun k => by
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => v.valuation F (z ⟨k, j⟩))
      ⟨c0 k, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hcz : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    have h1 := hc k (c0 k)
    rw [h0, map_zero] at h1
    exact hc0 k ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  exact mem_integer_of_mem_chartRingZ v z c (fun p => hc p.1 p.2) (hb c hcz)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charZero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : IsHorizontal (mCoordIdeal y)) :
    CharZero Ω := by
  refine charZero_of_injective_algebraMap (R := ℤ) ((injective_iff_map_eq_zero _).mpr fun m hm => ?_)
  have h : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C,
      MvPolynomial.algebraMap_apply, hm, C_0]
  rwa [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hy, Ideal.mem_bot] at h

end CurveRingFiniteAlt


open CurveRingFiniteAlt IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree in
theorem CurveRingFinite.proof : CurveRingFinite.Statement := by
  intro K _ ι _ Ω _ y hy
  classical
  have := CurveRingFiniteAlt.charZero y hy.2.2.1
  choose c0 hc0 using hy.2.1.2.2
  have hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k h => hc0 k (X_mem_of_eq_zero h)
  let r : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c0 p.1⟩
  let κ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (Set.range r)
  have : FiniteDimensional ℚ κ := IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨p, rfl⟩ := hx
    exact (isAlgebraic_ratio hy c0 hy0 p).isIntegral
  have : NumberField κ :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ κ).injective
      to_finiteDimensional := inferInstance }
  let z : (Σ k, ι k) → κ := fun p => ⟨r p, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩
  have hzy : ∀ p q : Σ k, ι k, p.1 = q.1 → ((z p / z q : κ) : Ω) = y p / y q := by
    rintro ⟨k, i⟩ ⟨k', j⟩ h
    simp only at h
    subst h
    exact div_div_div_cancel_right₀ (hy0 k) _ _
  have hyz : ∀ p, z p ≠ 0 → y p ≠ 0 := fun p h hp => h (Subtype.ext (by
    show y p / y ⟨p.1, c0 p.1⟩ = 0
    rw [hp, zero_div]))
  let φ : κ →ₐ[ℤ] Ω := (IntermediateField.val κ).toRingHom.toIntAlgHom
  have hmap : ∀ c : ∀ k, ι k, chartRingZ y c = (chartRingZ z c).map φ := fun c => by
    rw [chartRingZ, chartRingZ, AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    funext p
    exact (hzy p ⟨p.1, c p.1⟩ rfl).symm
  have hκ : ∀ b ∈ curveRing y, b ∈ κ := fun b hb => by
    have h := mem_curveRing.mp hb c0 hy0
    rw [hmap, Subalgebra.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    exact x.2
  have hint : ∀ b (hb : b ∈ curveRing y), (⟨b, hκ b hb⟩ : κ) ∈ integralClosure ℤ κ := fun b hb => by
    refine mem_integralClosure z c0 (fun k h => ?_) fun c hc => ?_
    · have h1 := congrArg (fun x : κ => (x : Ω)) h
      have h2 : y ⟨k, c0 k⟩ / y ⟨k, c0 k⟩ = 0 := h1
      exact one_ne_zero ((div_self (hy0 k)).symm.trans h2)
    · have h := mem_curveRing.mp hb c (fun k => hyz _ (hc k))
      rw [hmap, Subalgebra.mem_map] at h
      obtain ⟨x, hx, hxb⟩ := h
      have e : x = ⟨b, hκ b hb⟩ := Subtype.ext hxb
      exact e ▸ hx
  have : Module.Finite ℤ (integralClosure ℤ κ) := inferInstanceAs (Module.Finite ℤ (𝓞 κ))
  let f : curveRing y →ₗ[ℤ] integralClosure ℤ κ :=
    { toFun := fun b => ⟨⟨b, hκ b b.2⟩, hint b b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h =>
    Subtype.ext (congrArg (fun w : integralClosure ℤ κ => ((w : κ) : Ω)) h)

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveClosedPointChart
section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def segre (y : (Σ k, ι k) → Ω) : (Σ _ : Unit, ∀ k, ι k) → Ω :=
  fun q ↦ ∏ k, y ⟨k, q.2 k⟩

omit [∀ k, Fintype (ι k)] in
theorem segre_ne_zero_iff (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) :
    segre y ⟨(), f⟩ ≠ 0 ↔ ∀ k, y ⟨k, f k⟩ ≠ 0 := by
  simp [segre, Finset.prod_ne_zero_iff]


omit [∀ k, Fintype (ι k)] in
theorem segre_ratio (y : (Σ k, ι k) → Ω) (f g : ∀ k, ι k) :
    segre y ⟨(), g⟩ / segre y ⟨(), f⟩ = ∏ k, y ⟨k, g k⟩ / y ⟨k, f k⟩ := by
  simp [segre, Finset.prod_div_distrib]


omit [∀ k, Fintype (ι k)] in
theorem prod_ratio_update [DecidableEq K] (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0)
    (p : Σ k, ι k) :
    ∏ k, y ⟨k, Function.update f p.1 p.2 k⟩ / y ⟨k, f k⟩ = y p / y ⟨p.1, f p.1⟩ := by
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    rw [Function.update_of_ne hk, div_self (hf k)]
  · simp


omit [∀ k, Fintype (ι k)] in
theorem chartRingZ_segre (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) :
    chartRingZ (segre y) (fun _ ↦ f) = chartRingZ y f := by
  classical
  apply le_antisymm
  · rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
    change segre y ⟨(), g⟩ / segre y ⟨(), f⟩ ∈ chartRingZ y f
    rw [segre_ratio]
    exact prod_mem fun k _ ↦ Algebra.subset_adjoin ⟨⟨k, g k⟩, rfl⟩
  · rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    change y p / y ⟨p.1, f p.1⟩ ∈ chartRingZ (segre y) (fun _ ↦ f)
    rw [← prod_ratio_update y f hf p, ← segre_ratio]
    exact Algebra.subset_adjoin ⟨⟨(), Function.update f p.1 p.2⟩, rfl⟩

theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn ↦ ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C]
    rw [eq_intCast, Int.cast_natCast, ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

theorem exists_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    ∃ f : ∀ k, ι k, ∀ k, y ⟨k, f k⟩ ≠ 0 := by
  have h : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k ↦ by
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]
  choose f hf using h
  exact ⟨f, hf⟩

theorem isAlgebraic_segre_ratio [CharZero Ω] {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1)
    (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) :
    IsAlgebraic ℚ (segre y ⟨(), g⟩ / segre y ⟨(), f⟩) := by
  rw [segre_ratio]
  refine (IsIntegral.prod _ fun k _ ↦ ?_).isAlgebraic
  exact (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_ratio hP f hf ⟨k, g k⟩).isIntegral

theorem isArithVar_segre [DecidableEq K] [CharZero Ω] {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1)
    (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) : IsArithVar (mCoordIdeal (segre y)) 1 := by
  refine CoordConeArithVar.full Unit (fun _ ↦ ∀ k, ι k) Ω (segre y) (fun _ ↦ f) 0 Fin.elim0 ⟨()⟩
    (fun _ ↦ (segre_ne_zero_iff y f).mpr hf) algebraicIndependent_empty_type (fun i ↦ i.elim0) ?_
  rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
  exact IsAlgebraic.extendScalars (RingHom.injective _) (isAlgebraic_segre_ratio hP f hf g)

end SegreChart

end

end GroundTheory.Heights₂.Heights.Targets
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

noncomputable section

namespace CurveClosedPointChartAlt

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω] (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k)

abbrev fld : IntermediateField ℚ Ω :=
  CoordinateConeArithVar.ratioField (SegreChart.segre y) (fun _ ↦ f)

def pt : (Σ _ : Unit, ∀ k, ι k) → fld y f :=
  CoordinateConeArithVar.ratioPtL (SegreChart.segre y) (fun _ ↦ f)

theorem coe_pt (q : Σ _ : Unit, ∀ k, ι k) :
    ((pt y f q : fld y f) : Ω) = SegreChart.segre y q / SegreChart.segre y ⟨(), f⟩ := rfl

variable {y f}

theorem numberField (hP : IsArithVar (mCoordIdeal y) 1) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) : NumberField (fld y f) := by
  have : Finite (coneRatios (SegreChart.segre y) fun _ ↦ f) := (Set.finite_range _).to_subtype
  have : FiniteDimensional ℚ (fld y f) := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
    exact (SegreChart.isAlgebraic_segre_ratio hP f hf g).isIntegral)
  exact {}

theorem isArithVar_pt (hP : IsArithVar (mCoordIdeal y) 1) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) :
    IsArithVar (mCoordIdeal (pt y f)) 1 := by
  rw [pt, CoordinateConeArithVar.mCoordIdeal_ratioPtL _ _ fun _ ↦ (SegreChart.segre_ne_zero_iff y f).mpr hf]
  exact SegreChart.isArithVar_segre hP f hf

theorem pt_ne_zero_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) :
    pt y f ⟨(), g⟩ ≠ 0 ↔ ∀ k, y ⟨k, g k⟩ ≠ 0 := by
  rw [← SegreChart.segre_ne_zero_iff, ne_eq, ← ZeroMemClass.coe_eq_zero, coe_pt, div_eq_zero_iff, not_or,
    and_iff_left ((SegreChart.segre_ne_zero_iff y f).mpr hf)]

theorem coe_pt_ratio (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g h : ∀ k, ι k) :
    ((pt y f ⟨(), h⟩ / pt y f ⟨(), g⟩ : fld y f) : Ω) =
      SegreChart.segre y ⟨(), h⟩ / SegreChart.segre y ⟨(), g⟩ := by
  rw [IntermediateField.coe_div, coe_pt, coe_pt,
    div_div_div_cancel_right₀ ((SegreChart.segre_ne_zero_iff y f).mpr hf)]

theorem map_chartRingZ (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) (hg : ∀ k, y ⟨k, g k⟩ ≠ 0) :
    (chartRingZ (pt y f) (fun _ ↦ g)).map (algebraMap (fld y f) Ω).toIntAlgHom = chartRingZ y g := by
  rw [chartRingZ, ← Algebra.adjoin_image, ← Set.range_comp, ← SegreChart.chartRingZ_segre y g hg, chartRingZ]
  congr 2
  funext q
  obtain ⟨⟨⟩, h⟩ := q
  exact coe_pt_ratio hf g h

theorem mem_chartRingZ_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) (hg : ∀ k, y ⟨k, g k⟩ ≠ 0)
    (x : fld y f) : x ∈ chartRingZ (pt y f) (fun _ ↦ g) ↔ (x : Ω) ∈ chartRingZ y g := by
  rw [← map_chartRingZ hf g hg, Subalgebra.mem_map]
  refine ⟨fun h ↦ ⟨x, h, rfl⟩, ?_⟩
  rintro ⟨x', hx', he⟩
  rwa [show x' = x from Subtype.ext he] at hx'

theorem mem_curveRing_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (x : fld y f) :
    x ∈ curveRing (pt y f) ↔ (x : Ω) ∈ curveRing y := by
  rw [mem_curveRing, mem_curveRing]
  refine ⟨fun h g hg ↦ (mem_chartRingZ_iff hf g hg x).1 (h _ fun _ ↦ (pt_ne_zero_iff hf g).2 hg),
    fun h c hc ↦ ?_⟩
  have hc' := (pt_ne_zero_iff hf (c ())).1 (hc ())
  exact (mem_chartRingZ_iff hf (c ()) hc' x).2 (h _ hc')

theorem exists_of_mem_curveRing (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) {b : Ω} (hb : b ∈ curveRing y) :
    ∃ x : fld y f, (x : Ω) = b := by
  have h := mem_curveRing.mp hb f hf
  rw [← map_chartRingZ hf f hf, Subalgebra.mem_map] at h
  obtain ⟨x, -, hx⟩ := h
  exact ⟨x, hx⟩

end CurveClosedPointChartAlt


open CurveClosedPointChartAlt in
theorem CurveClosedPointChart.proof : CurveClosedPointChart.Statement := by
  classical
  intro K _ ι _ Ω _ y hP m hm
  have := SegreChart.charZero_of_isArithVar hP
  obtain ⟨f, hf⟩ := SegreChart.exists_chart hP
  have := numberField hP hf
  let φ : curveRing (pt y f) →+* curveRing y :=
    RingHom.codRestrict ((algebraMap (fld y f) Ω).comp (curveRing (pt y f)).subtype) (curveRing y)
      fun x ↦ (mem_curveRing_iff hf x).1 x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, rfl⟩ := exists_of_mem_curveRing hf hb
    exact ⟨⟨x, (mem_curveRing_iff hf x).2 hb⟩, rfl⟩
  have hm' : (m.comap φ).IsMaximal := Ideal.comap_isMaximal_of_surjective φ hφ
  obtain ⟨t, ht, hrat⟩ := ClosedPointChart.proof ClosedPointUnitSection.proof (∀ k, ι k) (fld y f) (pt y f)
    (isArithVar_pt hP hf) (m.comap φ) hm'
  have hyt := (pt_ne_zero_iff hf t).1 ht
  refine ⟨t, hyt, fun p ↦ ?_⟩
  obtain ⟨a, b, hb, hab⟩ := hrat (Function.update t p.1 p.2)
  refine ⟨φ a, φ b, hb, ?_⟩
  have h1 := congrArg (fun x : fld y f ↦ (x : Ω)) hab
  simp only [IntermediateField.coe_mul] at h1
  rw [coe_pt_ratio hf, SegreChart.segre_ratio, SegreChart.prod_ratio_update y t hyt p] at h1
  exact h1

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveFieldNumber
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveFieldNumber.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 → Birational y → NumberField Ω

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartLatFull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def ChartLatFull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [NumberField Ω]
    (y : (Σ k, ι k) → Ω), Birational y →
    ∀ (a : K → ℤ) (τ : ℕ) (s : Ω), ∃ n : ℕ, 0 < n ∧ (n : Ω) * s ∈ chartLat y a τ

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveEmbedOrbit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveEmbedOrbit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar (mCoordIdeal y) 1 → Birational y →
    (∀ t ∈ R, t ∈ mcPts (mCoordIdeal y)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t) →
    ∃ e : R ≃ (Ω →+* ℂ), ∀ t : R, SameOrbit (t : (Σ k, ι k) → ℂ) (fun p => e t (y p))

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

def CurveBoxLattice.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar (mCoordIdeal y) 1 → Birational y → IsConjInvariantH A → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    (∀ t ∈ R, t ∈ mcPts (mCoordIdeal y)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t) →
    ∃ C : ℝ, ∀ τ : ℕ, 1 ≤ τ →
      (τ : ℝ) * ∑ t ∈ R, Real.log (chartRadius A c t) + chartIndexLog y c A.a τ - C ≤
        Real.log (Nat.card {s : chartLat y A.a τ //
          ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / chartUnit y c A.a τ)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ})

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxSmall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

def CurveBoxSmall.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k),
    IsArithVar (mCoordIdeal y) 1 → Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ (τ : ℕ) (s : Ω), IsSmallH (mCoordIdeal y) y A τ s ↔
      ∀ σ : Ω →+* ℂ, ‖σ (s / chartUnit y c A.a τ)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ

namespace CurveBoxSmall

end CurveBoxSmall

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveCountLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

theorem CurveCountLower.proof (hD : CurveDegreeVert.Statement) (hV : CurveVertIndex.Statement)
    (hL : CurveIndexLinear.Statement) (hN : CurveBoxCount.Statement) : CurveCountLower.Statement := by
  intro K _ ι _ Ω _ y A II hII hP hB hS hC
  obtain ⟨c, hcX, hc⟩ := exists_chart hP
  obtain ⟨R, hRP, hRu, -⟩ := regularityPointsSum_holds.proof K ι _ hP
  set b : K → ℕ := fun k => (A.a k).natAbs with hb
  set d : K → ℕ := fun k => (A.a k + b k).toNat with hd'
  have hd : ∀ k, (d k : ℤ) = A.a k + b k := fun k =>
    Int.toNat_of_nonneg (by simp only [hb]; omega)
  have h1 := hD K ι _ A II c R b d hII hP hS hcX hRP hRu hd
  have h2 := hV K ι Ω y _ d hP (isMultiHomog_curveChartMono c d) (curveChartMono_notMem hc d)
  have h3 := hV K ι Ω y _ b hP (isMultiHomog_curveChartMono c b) (curveChartMono_notMem hc b)
  rw [aeval_curveChartMono] at h2 h3
  obtain ⟨hadd, hpow⟩ := hL K ι Ω y c hP hc
  have h4 := hadd A.a (fun k => (b k : ℤ))
  rw [show A.a + (fun k => (b k : ℤ)) = fun k => (d k : ℤ) from funext fun k => (hd k).symm] at h4
  have hI : II K ι (mCoordIdeal y) 1 (fun _ => A) =
      chartIndexLog y c A.a 1 + ∑ t ∈ R, Real.log (chartRadius A c t) := by
    have e2 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c d) =
        chartIndexLog y c (fun k => (d k : ℤ)) 1 := h2
    have e3 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c b) =
        chartIndexLog y c (fun k => (b k : ℤ)) 1 := h3
    rw [h1, e2, e3, h4]
    ring
  obtain ⟨C, hCC⟩ := hN K ι Ω y A c R hP hB hC hc hRP hRu
  refine ⟨C, fun τ hτ => ?_⟩
  have h5 := hCC τ hτ
  rw [hpow A.a τ] at h5
  rw [hI]
  linarith [mul_add (τ : ℝ) (chartIndexLog y c A.a 1) (∑ t ∈ R, Real.log (chartRadius A c t))]

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveRatSectionSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveRationalSectionSum

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logNorm_smul {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    logNorm X s (fun p => c p.1 * z p) = logNorm X s z := by
  unfold logNorm
  rw [eval_smul_homog s a hs c z, X.smul c z hc, norm_mul]
  have hprod : (∏ k, ‖c k‖ ^ X.a k) = ‖∏ k, c k ^ a k‖ := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hXa k, zpow_natCast, norm_pow]
  rw [hprod, mul_div_mul_left _ _
    (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)))]

theorem arInt_eq_sum {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {s : MRing ι} {a : K → ℕ} (hXa : ∀ k, X.a k = a k) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    arInt P s X (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
      ∑ᶠ q : projPts P, logNorm X s (Quot.out q : mcPts P) := by
  have : Nonempty K := hP.1
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) =>
      Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).h z)) = Fin.elim0 :=
    funext fun j => j.elim0
  unfold arInt
  rw [hφ]
  exact PtsIntegralPoints.homogProof K ι P _ hP.2.1.2.1 (HilbertSamuel.CurvePointsFinite.proof K ι P hP)
    fun c z hc _ => logNorm_smul hXa hs c z hc


end CurveRationalSectionSum


end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PotFinCons
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem pot_fin_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (M : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem PoincareLelongRegularised.proof (hInt : PtsIntegrableStatement)
    (hMeas : GroundTheory.Heights₂.Heights.Inter.PtsAbsMeasurable.Statement) : PoincareLelongRegularised.Statement := by
  intro K _ ι _ P n L A B s hP hL hA hB _ hs
  obtain ⟨a, ha, hsa, hsP⟩ := id hs
  have hM : ∀ j, IsSmoothHerm ((Fin.cons B L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) := fun j =>
    Fin.cases (by simpa using hB) (fun i => by simpa using hL i) j
  have hlim := GroundTheory.Heights₂.Heights.Inter.PtsRegLimit.proof hInt
    (GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.proof hInt hMeas) K ι P (n + 1) (Fin.cons B L) A s
    ⟨a, ha, hsa⟩ hP hM hA hsP
  rw [pot_fin_cons] at hlim
  have hg : ∀ ε, (fun z => Real.log ((GroundTheory.Heights₂.Heights.Inter.regLine A s ⟨a, ha, hsa⟩ ε).h z)) =
      regLog A s ε := by
    intro ε
    funext z
    rw [GroundTheory.Heights₂.Heights.Inter.log_regLine_h]
    rfl
  simpa only [hg] using hlim

end GroundTheory.Heights₂.Heights.Targets
end
