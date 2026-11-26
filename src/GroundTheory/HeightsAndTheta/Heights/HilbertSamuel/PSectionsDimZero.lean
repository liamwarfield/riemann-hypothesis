module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionsDimZero

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def monVal (z : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) : Ω :=
  ∏ p, z p ^ m p

def blockDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ :=
  ∑ i, m ⟨k, i⟩

def rt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω :=
  fun p => y p / y ⟨p.1, c p.1⟩

theorem aeval_monomial_int (z : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (q : ℤ) :
    aeval z (monomial m q : MRing ι) = (q : Ω) * monVal z m := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), eq_intCast]
  rfl

theorem aeval_monomial_rat (z : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (q : ℚ) :
    aeval z (monomial m q : MvPolynomial (Σ k, ι k) ℚ) = q • monVal z m := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Algebra.smul_def]
  rfl

theorem monVal_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (m : (Σ k, ι k) →₀ ℕ) :
    monVal y m = monVal (rt y c) m * ∏ k, y ⟨k, c k⟩ ^ blockDeg m k := by
  have h : ∀ p : Σ k, ι k, y p ^ m p = rt y c p ^ m p * y ⟨p.1, c p.1⟩ ^ m p := fun p => by
    rw [← mul_pow, rt, div_mul_cancel₀ _ (hc p.1)]
  simp only [monVal, h, Finset.prod_mul_distrib, blockDeg]
  congr 1
  rw [Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_pow_eq_pow_sum Finset.univ (fun i => m ⟨k, i⟩) (y ⟨k, c k⟩)

theorem rt_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) : rt y c p ∈ chartRingQ y c :=
  Algebra.subset_adjoin ⟨p, rfl⟩

theorem monVal_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (m : (Σ k, ι k) →₀ ℕ) :
    monVal (rt y c) m ∈ chartRingQ y c :=
  prod_mem fun p _ => pow_mem (rt_mem y c p) _

theorem inv_mem_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    (y ⟨k, i⟩ / y ⟨k, c k⟩)⁻¹ ∈ chartRingQ y c :=
  Subalgebra.inv_mem_of_algebraic (A := chartRingQ y c) (x := ⟨_, rt_mem y c ⟨k, i⟩⟩)
    (CoordCurveDegree.isAlgebraic_ratio hP c hc ⟨k, i⟩)

theorem zpow_mem_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) (e : ℤ) :
    (y ⟨k, i⟩ / y ⟨k, c k⟩) ^ e ∈ chartRingQ y c := by
  rcases e with e | e
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem (rt_mem y c ⟨k, i⟩) _
  · rw [zpow_negSucc, ← inv_pow]
    exact pow_mem (inv_mem_chart hP c hc k i) _

theorem chart_le {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c c' : ∀ k, ι k)
    (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) : chartRingQ y c ≤ chartRingQ y c' := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨p, rfl⟩
  have e : y p / y ⟨p.1, c p.1⟩ = rt y c' p * (y ⟨p.1, c p.1⟩ / y ⟨p.1, c' p.1⟩)⁻¹ := by
    rw [rt, inv_div, div_mul_div_cancel₀ (hc' p.1)]
  show y p / y ⟨p.1, c p.1⟩ ∈ chartRingQ y c'
  rw [e]
  exact mul_mem (rt_mem y c' p) (inv_mem_chart hP c' hc' p.1 (c p.1))

theorem finrank_map_mulRight (L : Subalgebra ℚ Ω) {w : Ω} (hw : w ≠ 0) :
    Module.finrank ℚ ((Subalgebra.toSubmodule L).map (LinearMap.mulRight ℚ w)) = Module.finrank ℚ L := by
  have hinj : Function.Injective (LinearMap.mulRight ℚ w) := fun s t h => by
    simp only [LinearMap.mulRight_apply] at h
    exact mul_right_cancel₀ hw h
  rw [← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, Subalgebra.finrank_toSubmodule]

theorem chartLatQ_eq {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) (n : ℕ) :
    chartLatQ y a n = (Subalgebra.toSubmodule (chartRingQ y c)).map
      (LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ ((n : ℤ) * a k))) := by
  have hu : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      (∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c' k⟩ ^ ((n : ℤ) * a k) = 1 := by
    intro c' hc'
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [← zpow_add₀ (hc' k), neg_add_cancel, zpow_zero]
  ext s
  constructor
  · intro hs
    refine Submodule.mem_map.mpr ⟨s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)), hs c hc, ?_⟩
    rw [LinearMap.mulRight_apply, mul_assoc, hu c hc, mul_one]
  · rintro ⟨t, ht, rfl⟩ c' hc'
    rw [LinearMap.mulRight_apply]
    have e : (∏ k, y ⟨k, c k⟩ ^ ((n : ℤ) * a k)) * ∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * a k)) =
        ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ ((n : ℤ) * a k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [div_zpow, zpow_neg, div_eq_mul_inv]
    rw [mul_assoc, e]
    exact mul_mem (chart_le hP c c' hc' ht) (prod_mem fun k _ => zpow_mem_chart hP c' hc' k (c k) _)

theorem valueSpan_le (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    valueSpan y d ≤ (Subalgebra.toSubmodule (chartRingQ y c)).map
      (LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ d k)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [SetLike.mem_coe, g.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [aeval_monomial_int, monVal_eq y c hc m]
  have hb : ∀ k, blockDeg m k = d k := fun k => hg m hm k
  simp only [hb]
  exact Submodule.mem_map.mpr ⟨((AddMonoidAlgebra.coeff g m : ℤ) : Ω) * monVal (rt y c) m,
    (mul_mem (intCast_mem _ _) (monVal_mem y c m) : _ * _ ∈ chartRingQ y c),
    by rw [LinearMap.mulRight_apply, mul_assoc]⟩

theorem mem_valueSpan (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ)
    (m : (Σ k, ι k) →₀ ℕ) (hm : ∀ k, blockDeg m k ≤ d k) :
    monVal (rt y c) m * ∏ k, y ⟨k, c k⟩ ^ d k ∈ valueSpan y d := by
  classical
  set m' : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun p => m p + if p.2 = c p.1 then d p.1 - blockDeg m p.1 else 0) with hm'_def
  have hm' : ∀ p, m' p = m p + if p.2 = c p.1 then d p.1 - blockDeg m p.1 else 0 := fun p => by
    simp [hm'_def]
  have hdeg : ∀ k, blockDeg m' k = d k := by
    intro k
    have h1 : blockDeg m' k = blockDeg m k + (d k - blockDeg m k) := by
      simp only [blockDeg, hm', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have := hm k
    omega
  have hextra : ∏ p, rt y c p ^ (if p.2 = c p.1 then d p.1 - blockDeg m p.1 else 0) = 1 := by
    refine Finset.prod_eq_one fun p _ => ?_
    obtain ⟨k, i⟩ := p
    dsimp only
    split_ifs with h
    · subst h
      rw [rt, div_self (hc k), one_pow]
    · exact pow_zero _
  have hval : monVal (rt y c) m' = monVal (rt y c) m := by
    unfold monVal
    simp only [hm', pow_add, Finset.prod_mul_distrib, hextra, mul_one]
  refine Submodule.subset_span ⟨monomial m' 1, ?_, ?_⟩
  · intro e he k
    rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at he
    rw [he]
    exact hdeg k
  · rw [aeval_monomial_int, Int.cast_one, one_mul, monVal_eq y c hc, hval]
    simp only [hdeg]

theorem exists_le_span {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : ∃ D : ℕ, Subalgebra.toSubmodule (chartRingQ y c) ≤
      Submodule.span ℚ {x | ∃ m, (∀ k, blockDeg m k ≤ D) ∧ monVal (rt y c) m = x} := by
  set V : ℕ → Submodule ℚ Ω := fun D =>
    Submodule.span ℚ {x | ∃ m, (∀ k, blockDeg m k ≤ D) ∧ monVal (rt y c) m = x} with hV
  have hmono : Monotone V := fun D D' h => Submodule.span_mono (by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, fun k => (hm k).trans h, rfl⟩)
  have hfin : Module.Finite ℚ (chartRingQ y c) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) (by
      rintro _ ⟨p, rfl⟩
      exact (CoordCurveDegree.isAlgebraic_ratio hP c hc p).isIntegral)
  have hfg : (Subalgebra.toSubmodule (chartRingQ y c)).FG := Module.Finite.iff_fg.mp hfin
  have hcpt := (isCompactElement_iff_le_of_directed_sSup_le _).mp
    ((Submodule.fg_iff_compact _).mp hfg)
  obtain ⟨_, ⟨D, rfl⟩, hD⟩ := hcpt (Set.range V) (Set.range_nonempty V)
    (directedOn_range.mpr hmono.directed_le) (by
      intro x hx
      change x ∈ chartRingQ y c at hx
      rw [chartRingQ, Algebra.adjoin_range_eq_range_aeval] at hx
      obtain ⟨f, rfl⟩ := hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, f.as_sum, map_sum]
      refine Submodule.sum_mem _ fun m _ => ?_
      rw [aeval_monomial_rat]
      refine Submodule.smul_mem _ _ ?_
      exact (le_sSup (Set.mem_range_self (∑ k, blockDeg m k)) : V _ ≤ _) (Submodule.subset_span
        ⟨m, fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k), rfl⟩))
  exact ⟨D, hD⟩

theorem valueSpan_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (D : ℕ)
    (hD : Subalgebra.toSubmodule (chartRingQ y c) ≤
      Submodule.span ℚ {x | ∃ m, (∀ k, blockDeg m k ≤ D) ∧ monVal (rt y c) m = x})
    (d : K → ℕ) (hd : ∀ k, D ≤ d k) :
    valueSpan y d = (Subalgebra.toSubmodule (chartRingQ y c)).map
      (LinearMap.mulRight ℚ (∏ k, y ⟨k, c k⟩ ^ d k)) := by
  refine le_antisymm (valueSpan_le y c hc d) ?_
  rw [Submodule.map_le_iff_le_comap]
  refine hD.trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact mem_valueSpan y c hc d m fun k => (hm k).trans (hd k)

theorem eventualValue_eq {f : (K → ℤ) → ℤ} {v : ℤ} (h : ∀ᶠ m in atTop, f m = v) :
    NumbersDVR.eventualValue f = v := by
  have hex : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨v, h⟩
  rw [NumbersDVR.eventualValue, dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and h).exists
  rw [← h1, h2]

end SectionsDimZero


open SectionsDimZero in
theorem SectionsDimZero.proof : SectionsDimZero.Statement := by
  intro K _ ι _ Ω _ _ y a n hP
  classical
  choose c hcX using hP.2.1.2.2
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k (CoordCurveDegree.X_mem_of_eq_zero h0)
  obtain ⟨D, hD⟩ := exists_le_span hP c hc
  rw [chartLatQ_eq hP c hc, finrank_map_mulRight _
    (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k))]
  symm
  unfold genDeg NumbersDVR.intNum
  simp only [NumbersDVR.mixedDiff, List.ofFn_zero, List.foldr_nil]
  apply eventualValue_eq
  filter_upwards [eventually_ge_atTop (fun _ : K => (D : ℤ))] with m hm
  have hm0 : ∀ k, (D : ℤ) ≤ m k := hm
  have e : m = fun k => (((m k).toNat : ℕ) : ℤ) := funext fun k => by
    have := hm0 k
    omega
  rw [e, HilbFnValueSpan.proof, valueSpan_eq y c hc D hD _ (fun k => by have := hm0 k; omega),
    finrank_map_mulRight _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallGenTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBoundedMul

noncomputable section

namespace SmallGenTwist

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def SmallGen (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : Prop :=
  ∃ (n : ℕ) (w : Fin n → Ω), (∀ j, w j ∈ chartLat y A.a 1) ∧ KH.GeneratesOn y A.a w ∧
    ∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)

theorem exists_chart (y : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hz.1
  refine ⟨c, hc, fun k h0 => ?_⟩
  have hX : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, c k⟩ : MRing ι) _ :=
    (by have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1
        rwa [← X] at h)
  have hmem := mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])
  have hz0 := hz.2 _ hmem
  simp only [map_X, eval_X] at hz0
  exact hc k hz0


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLat (y : (Σ k, ι k) → Ω) {a b : K → ℤ} {s t : Ω} (hs : s ∈ chartLat y a 1)
    (ht : t ∈ chartLat y b 1) : s * t ∈ chartLat y (a + b) 1 := by
  intro c hc
  have h := mul_mem (hs c hc) (ht c hc)
  convert h using 1
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Nat.cast_one, one_mul]
  ring


omit [∀ k, Fintype (ι k)] in
theorem generatesOn_mul (y : (Σ k, ι k) → Ω) {a b : K → ℤ} {n m : ℕ} {w : Fin n → Ω} {v : Fin m → Ω}
    (hw : KH.GeneratesOn y a w) (hv : KH.GeneratesOn y b v) :
    KH.GeneratesOn y (a + b)
      (fun j : Fin (n * m) => w (finProdFinEquiv.symm j).1 * v (finProdFinEquiv.symm j).2) := by
  intro c hc
  obtain ⟨u, hu, hsum⟩ := hw c hc
  obtain ⟨u', hu', hsum'⟩ := hv c hc
  refine ⟨fun j => u (finProdFinEquiv.symm j).1 * u' (finProdFinEquiv.symm j).2,
    fun j => mul_mem (hu _) (hu' _), ?_⟩
  set Pa := ∏ k, y ⟨k, c k⟩ ^ (-a k) with hPa
  set Pb := ∏ k, y ⟨k, c k⟩ ^ (-b k) with hPb
  have hP : ∏ k, y ⟨k, c k⟩ ^ (-((a + b) k)) = Pa * Pb := by
    rw [hPa, hPb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [hP, Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin n × Fin m => u p.1 * u' p.2 * (w p.1 * v p.2 * (Pa * Pb))) (fun _ => rfl),
    Fintype.sum_prod_type]
  calc ∑ i, ∑ l, u i * u' l * (w i * v l * (Pa * Pb))
      = (∑ i, u i * (w i * Pa)) * ∑ l, u' l * (v l * Pb) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    _ = 1 := by rw [hsum, hsum', one_mul]

theorem isSmallH_mul (y : (Σ k, ι k) → Ω) (A B C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hCa : ∀ k, C.a k = A.a k + B.a k)
    (hCh : ∀ z, C.h z = A.h z * B.h z) {s t : Ω} (hs : s ∈ chartLat y A.a 1) (ht : t ∈ chartLat y B.a 1)
    (hbs : IsSmallH (mCoordIdeal y) y A 1 s) (hbt : IsSmallH (mCoordIdeal y) y B 1 t) :
    IsSmallH (mCoordIdeal y) y C 1 (s * t) := by
  intro dg dh g h z hg hh hdeg he hz
  obtain ⟨c, hc, hy⟩ := exists_chart y hz
  obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a 1 hs c hy
  obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y B.a 1 ht c hy
  have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
  have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

  have hdeq : dgs + dgt + dh = dg + (N + M) := by
    funext k
    have e1 := hdgs k
    have e2 := hdgt k
    have e3 := hdeg k
    have e4 := hCa k
    simp only [Pi.add_apply]
    have : ((dgs k + dgt k + dh k : ℕ) : ℤ) = ((dg k + (N k + M k) : ℕ) : ℤ) := by
      push_cast at e1 e2 e3 ⊢
      linear_combination e1 + e2 - e3 - e4
    exact_mod_cast this
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (gs * gt * h - g * chartMono c (N + M)) (dgs + dgt + dh) := by
    refine isMultiHomog_sub (SectionBoundedMul.isMultiHomog_mul (SectionBoundedMul.isMultiHomog_mul hgs hgt) hh) ?_
    rw [hdeq]
    exact SectionBoundedMul.isMultiHomog_mul hg (isMultiHomog_chartMono c (N + M))
  have hmono : ∀ (w : (Σ k, ι k) → Ω), aeval w (chartMono c (N + M)) =
      aeval w (chartMono c N) * aeval w (chartMono c M) := fun w => by
    rw [aeval_chartMono, aeval_chartMono, aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hF0 : aeval y (gs * gt * h - g * chartMono c (N + M)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_mul, hvs, hvt, he, hmono]
    ring
  have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
  simp only [map_sub, map_mul] at hz0
  rw [sub_eq_zero] at hz0

  set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
  have hmz : ev (chartMono c (N + M)) = ev (chartMono c N) * ev (chartMono c M) := by
    simp only [hev, eval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ := by
    refine mul_pos (norm_pos_iff.mpr ?_) (norm_pos_iff.mpr ?_) <;>
    · simp only [hev, eval_chartMono]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have key : ‖ev g‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) =
      ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖ := by
    rw [← norm_mul, ← hmz, ← norm_mul, ← norm_mul, ← norm_mul]
    exact congrArg norm hz0.symm
  have hprod : ‖ev gs‖ * ‖ev gt‖ ≤
      (‖ev (chartMono c N)‖ * A.h z ^ 1) * (‖ev (chartMono c M)‖ * B.h z ^ 1) :=
    mul_le_mul bs bt (norm_nonneg _) ((norm_nonneg _).trans bs)
  refine le_of_mul_le_mul_right ?_ hpos
  rw [key]
  calc ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖
      ≤ (‖ev (chartMono c N)‖ * A.h z ^ 1) * (‖ev (chartMono c M)‖ * B.h z ^ 1) * ‖ev h‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ‖ev h‖ * C.h z ^ 1 * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) := by
        rw [hCh]
        ring

theorem smallGen_mul (y : (Σ k, ι k) → Ω) (A B C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hCa : C.a = A.a + B.a)
    (hCh : ∀ z, C.h z = A.h z * B.h z) (hA : SmallGen y A) (hB : SmallGen y B) : SmallGen y C := by
  obtain ⟨n, w, hw, hgw, hsw⟩ := hA
  obtain ⟨m, v, hv, hgv, hsv⟩ := hB
  refine ⟨n * m, fun j => w (finProdFinEquiv.symm j).1 * v (finProdFinEquiv.symm j).2,
    fun j => ?_, ?_, fun j => ?_⟩
  · rw [hCa]
    exact mul_mem_chartLat y (hw _) (hv _)
  · rw [hCa]
    exact generatesOn_mul y hgw hgv
  · exact isSmallH_mul y A B C (fun k => by rw [hCa]; rfl) hCh (hw _) (hv _) (hsw _) (hsv _)

theorem smallGen_of_trivial (y : (Σ k, ι k) → Ω) (E : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hEa : E.a = 0) (hEh : ∀ z, E.h z = 1) :
    SmallGen y E := by
  refine ⟨1, fun _ => 1, fun _ => ?_, ?_, fun _ => ?_⟩
  · intro c hc
    simp [hEa]
  · intro c hc
    refine ⟨fun _ => 1, fun _ => one_mem _, ?_⟩
    simp [hEa]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = dh := funext fun k => by
      have := hdeg k
      rw [hEa] at this
      simp only [Pi.zero_apply, mul_zero, add_zero] at this
      exact_mod_cast this
    subst hd
    have h0 : aeval y (g - h) = 0 := by rw [map_sub, he, one_mul, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_sub hg hh) h0)
    simp only [map_sub, sub_eq_zero] at hz0
    rw [hz0, hEh, pow_one, mul_one]


omit [∀ k, Fintype (ι k)] in
theorem fsH_a [∀ k, Fintype (ι k)] : (fsH ι).a = fun _ => 1 := by
  funext k
  simp [fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics]

theorem smallGen_fsH (y : (Σ k, ι k) → Ω) : SmallGen y (fsH ι) := by
  classical
  set e := Fintype.equivFin (∀ k, ι k) with he_def
  refine ⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) 1), fun j => ?_, ?_, fun j => ?_⟩
  · intro c hc
    beta_reduce
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    refine prod_mem fun k _ => ?_
    have hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c :=
      Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩
    convert hmem using 1
    simp [fsH_a, div_eq_mul_inv]
  · intro c hc
    refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩
    rw [Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) *
      (aeval y (chartMono i 1) * ∏ k, y ⟨k, c k⟩ ^ (-(fsH ι).a k))) (fun _ => rfl)]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by simp [fsH_a, hc k]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = 1 + dh := funext fun k => by
      have := hdeg k
      simp only [fsH_a, Nat.cast_one, one_mul] at this
      simp only [Pi.add_apply, Pi.one_apply]
      omega
    have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g - chartMono (e.symm j) 1 * h) dg :=
      isMultiHomog_sub hg (by rw [hd]; exact SectionBoundedMul.isMultiHomog_mul (isMultiHomog_chartMono _ 1) hh)
    have h0 : aeval y (g - chartMono (e.symm j) 1 * h) = 0 := by
      rw [map_sub, map_mul, he, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)
    simp only [map_sub, map_mul, sub_eq_zero] at hz0
    rw [hz0, norm_mul, eval_chartMono, pow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [Pi.one_apply, pow_one, norm_prod]
    have hH : (fsH ι).h z = ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ := by
      simp [fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics, fsMetric]
    rw [hH]
    refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => ?_
    have := PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) ((e.symm j) k)
    rwa [PiLp.toLp_apply] at this

theorem smallGen_zcomb (y : (Σ k, ι k) → Ω) (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hL : SmallGen y L) (q p : ℕ) :
    SmallGen y (HermLine.zcomb L (fsH ι) q p) := by
  induction q with
  | zero =>
    induction p with
    | zero =>
      exact smallGen_of_trivial y _ (by funext k; simp [HermLine.zcomb]) (fun z => by simp [HermLine.zcomb])
    | succ p ih =>
      refine smallGen_mul y _ (fsH ι) _ ?_ (fun z => ?_) ih (smallGen_fsH y)
      · funext k
        simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      · simp only [HermLine.zcomb, zpow_natCast, pow_succ]
        ring
  | succ q ih =>
    refine smallGen_mul y _ L _ ?_ (fun z => ?_) ih hL
    · funext k
      simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    · simp only [HermLine.zcomb, zpow_natCast, pow_succ]
      ring

end SmallGenTwist

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResolutionMixedIntegral.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)), IsSmoothMetric m₁ →
    ∑ i ∈ Finset.range (D + 1),
        ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ d.x) (mixPot d.m m₁ D i) (logRatio d.m m₁) =
      ((D : ℝ) + 1) * resMetricInt d m₁

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGraphDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameGraphDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∃ (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))))
      (J : IFamily G.Φ (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) (Sum.inr : Unit → Unit ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = (projDeg x e : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionInterpIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionInterpIntegral.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)), IsSmoothMetric m₁ →
    ((D : ℝ) + 1) * resMetricInt d m₁ =
      ∑ i ∈ Finset.range (D + 1),
        mInt d.R.A (fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m)
          (fun y => logRatio d.m m₁ (resPt d y))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreRelLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def FibreRelLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (ℓ : ℕ) (a : K → ℤ) (r : ℕ) (s : Fin r → Ω)
    (J : KH.Cell K ι 0)
    (u : Fin r → LocalizedModule (KH.cellMon (ZMod ℓ) J.1) (MRingOver (ZMod ℓ) ι ⧸ GenOnFibres.idealOver y (ZMod ℓ))),
    (∀ j, s j ∈ chartLat y a 1) → (∀ k, y ⟨k, GenOnFibres.cellChart J k⟩ ≠ 0) →
    (∀ j, u j ∈ KH.locPart ι (KH.quotPart (ZMod ℓ) (GenOnFibres.idealOver y (ZMod ℓ))) (KH.cellMon (ZMod ℓ) J.1) (-a)) →
    ∑ j, u j * GenOnFibres.secCoch (y := y) (S := ZMod ℓ) (s j) a J = 1 →
    ∃ (u' : Fin r → Ω) (v : Ω), (∀ j, u' j ∈ chartRingZ y (GenOnFibres.cellChart J)) ∧
      v ∈ chartRingZ y (GenOnFibres.cellChart J) ∧
      ∑ j, u' j * (s j * ∏ k, y ⟨k, GenOnFibres.cellChart J k⟩ ^ (-a k)) + ℓ * v = 1

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftQuotientBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def ShiftQuotientBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ) (c : ∀ k, ι k),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1 ⧸ chartDivSec y c ((n : ℤ) • a + b)) : ℝ) ≤
        C * (n : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealFormsOnPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RealFormsOnPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ) (e : K → ℕ) (r : ℕ) (g : Fin r → MRing ι),
    IsArithVar (mCoordIdeal y) d → (∀ i, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g i) e) →
    LinearIndependent ℤ (fun i => aeval y (g i)) →
    ∀ c : Fin r → ℝ,
      (∀ z ∈ mcPts (mCoordIdeal y), ∑ i, (c i : ℂ) * eval z (map (Int.castRingHom ℂ) (g i)) = 0) →
      c = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexGramMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def ComplexGramMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))) (hs : IsSmoothMetric m₁)
    (hc : IsConjInvariant m₁) (hle : P0₁ ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone m₁)) (e : Fin (D + 1) → Ix κ),
    IsProjFrame d.x e →
    (fun n => resCChi (d.withMetric m₁ P0₁ hs hc hle hp) n - resCChi d n -
        (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * resMetricInt d m₁) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockTop.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m 0) = top I x m D ∧
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m' 1) =
        top I (matAct B x) m' D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockStepLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockStepLocal.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a b : ℕ, a₀ ≤ a → a₀ ≤ b →
      |twoBlockStep x (matAct B x) a b -
          ∑ i ∈ Finset.range (D + 1), twoBlockCoeff I x (matAct B x) m m' D i *
            ((a : ℝ) ^ i * (b : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ)))| ≤
        C * ((a + b : ℝ) + 1) ^ D / ((a + b : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockChainSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockChainSum.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    (fun n : ℕ => ∑ j ∈ Finset.range n, twoBlockStep x (matAct B x) (n - j - 1) j -
        (I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m' 1) -
          I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m 0)) *
          (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenSESStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenSESStep.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M' : Type) [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
    [IsScalarTower S (MRingOver S ι) M'] (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (M'' : Type) [AddCommGroup M''] [Module (MRingOver S ι) M''] [Module S M'']
    [IsScalarTower S (MRingOver S ι) M'']
    (𝓜' : (K → ℤ) → Submodule S M') (𝓜 : (K → ℤ) → Submodule S M) (𝓜'' : (K → ℤ) → Submodule S M'')
    (g : M' →ₗ[MRingOver S ι] M) (h : M →ₗ[MRingOver S ι] M''),
    KH.IsMGraded S ι 𝓜' → KH.IsMGraded S ι 𝓜 → KH.IsMGraded S ι 𝓜'' →
    KH.IsMGradedMap S ι 𝓜' 𝓜 g → KH.IsMGradedMap S ι 𝓜 𝓜'' h →
    Function.Injective g → Function.Surjective h → LinearMap.range g = LinearMap.ker h →
    ∀ d : K → ℤ, Subsingleton (KH.cechHc ι 𝓜' d 1) → GeneratedMod S ι 𝓜' d → GeneratedMod S ι 𝓜'' d →
      GeneratedMod S ι 𝓜 d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBisAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

noncomputable section

def TensorPowerL2Degree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (μ : Measure ((Σ k, ι k) → ℂ)) (m : ℕ),
      IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧ IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      1 ≤ m ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop,
        ∀ (r : ℕ) (ψ : chartLat y A.a (m * q) →+ EuclideanSpace ℝ (Fin r)), Function.Injective ψ →
          (∀ s : chartLat y A.a (m * q), ‖ψ s‖ = sectionL2Norm μ y A (m * q) (s : Ω)) →
          ∀ [DiscreteTopology (imageLattice ψ)] [IsZLattice ℝ (imageLattice ψ)],
            -Real.log (ZLattice.covolume (imageLattice ψ)) ≤
              (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
                (((m * q : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMetricPair
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def ResolutionMetricPair.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))), IsSmoothMetric m₁ →
    P0₁ ≤ coordIdeal ℤ d.x → IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone m₁) →
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W₀ W₁ : Weight L) (dV : SmoothVolume A)
      (σ : ℕ → MvPolynomial (Ix κ) ℚ → Fin A.n → d.R.X → ℂ),
      A.Compatible d.R.A ∧ W₀.IsSemipositive ∧ W₁.IsSemipositive ∧ dV.μ = d.dV ∧
      (∀ (n : ℕ) (b : MvPolynomial (Ix κ) ℚ), b.IsHomogeneous n → σ n b ∈ L.sections n) ∧
      (∀ y : d.R.X, ∃ c : ℂ, c ≠ 0 ∧
        (∀ (n : ℕ) (b : MvPolynomial (Ix κ) ℚ), b.IsHomogeneous n →
          σ n b (chartIdx A y) y = eval (c • resPt d y) (map (algebraMap ℚ ℂ) b)) ∧
        W₀.φ (chartIdx A y) y = 2 * Real.log (d.m.ρ (c • resPt d y)) ∧
        W₁.φ (chartIdx A y) y = 2 * Real.log (m₁.ρ (c • resPt d y))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ g : d.R.X → ℝ, Continuous g →
        ∫ y, g y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
          mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) g / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAmpleOfGenTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem AmpleOfGenTwist.proof (hGen : GenTwistGenerated.Statement) (hVan : GenTwistVanish.Statement) :
    AmpleOfGenTwist.Statement := by
  intro S _ K _ _ ι _ _ V α p q hV hα hp
  refine ⟨1, le_rfl, ?_, fun e => ?_⟩
  · rw [one_smul]
    exact hGen S K ι V α q p hα
  · obtain ⟨c₀, hc₀⟩ := hVan S K ι V α hV hα e
    refine ⟨c₀, fun c hc => ?_⟩
    have hN : e + (c * 1) • ((q : ℤ) • α + fun _ => (p : ℤ)) =
        e + ((c * q : ℕ) : ℤ) • α + fun _ => ((c * p : ℕ) : ℤ) := by
      funext k
      change e k + (c * 1) • ((q : ℤ) • α k + (p : ℤ)) = e k + ((c * q : ℕ) : ℤ) • α k + ((c * p : ℕ) : ℤ)
      simp only [nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
    rw [hN]
    exact hc₀ (c * q) (c * p) (le_trans hc (Nat.le_mul_of_pos_right c hp))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
