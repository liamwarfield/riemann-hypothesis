module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ArithmeticVolumeBigDimensionOne.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    II K ι (mCoordIdeal y) 1 (fun _ => A) ≤ arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 0

namespace ArithmeticVolumeBigDimensionOne

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end ArithmeticVolumeBigDimensionOne

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionPointValue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionPointValue.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (mCoordIdeal y) → ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
    ∃ w : ∀ n : ℕ, chartLat y A.a n →+ (((Σ k, ι k) → ℂ) → ℂ),
      (∀ (n : ℕ) (s : chartLat y A.a n), ContinuousOn (w n s) (mcPts (mCoordIdeal y))) ∧
      (∀ (n : ℕ) (s : chartLat y A.a n) (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
        ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + n * A.a k) →
        aeval y g = (s : Ω) * aeval y h → z ∈ mcPts (mCoordIdeal y) →
        eval z (map (Int.castRingHom ℂ) g) =
          w n s z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) ∧
      (∀ (n : ℕ) (s : chartLat y A.a n), ∀ z ∈ mcPts (mCoordIdeal y),
        secNormAt y A n (s : Ω) z = ‖w n s z‖) ∧
      (∀ (n k : ℕ) (s : chartLat y A.a n) (t : chartLat y A.a k) (st : chartLat y A.a (n + k)),
        (st : Ω) = s * t → ∀ z ∈ mcPts (mCoordIdeal y), w (n + k) st z = w n s z * w k t z) ∧
      ∀ (n r : ℕ) (s : Fin r → chartLat y A.a n),
        ∃ (e e' : K → ℕ) (h : MRing ι) (g : Fin r → MRing ι),
          ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h e' ∧ (∀ i, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g i) e) ∧ (∀ k, (e k : ℤ) = e' k + n * A.a k) ∧
          aeval y h ≠ 0 ∧ ∀ i, aeval y (g i) = (s i : Ω) * aeval y h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

theorem ConstantsRegular.proof (hD : ConstantsDescend.Statement)
    (hC : ChartConstantsDetermined.Statement) : ConstantsRegular.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y hy
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hfin : Module.Finite ℤ (intsIn F Ω) :=
    Module.Finite.of_surjective
      ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict.toLinearMap
      (AlgHom.rangeRestrict_surjective _)
  have key : ∀ c : ∀ k, ι k, ∃ m : ℕ, 1 ≤ m ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ intsIn F Ω, (m : Ω) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · have hfg : (chartRingZ y c).FG :=
        ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩, by
          simp [chartRingZ, Set.image_univ]⟩
      obtain ⟨m, hm, h⟩ := hD Ω (chartRingZ y c) (intsIn F Ω) hfg hfin (hC K ι Ω F y hy c hc)
      exact ⟨m, hm, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose m hm hmem using key
  refine ⟨∏ c, m c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
    fun c _ => Nat.one_le_iff_ne_zero.mp (hm c)), ?_⟩
  intro θ c hc
  have ht : algebraMap F Ω (θ : F) ∈ intsIn F Ω := (AlgHom.mem_range _).mpr ⟨θ, rfl⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), Nat.cast_mul, mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hmem c hc _ ht)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralAgainstPositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

noncomputable section

namespace IntegralAgainstPositive

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem finsum_nonpos_of {α : Sort*} {f : α → ℝ} (h : ∀ x, f x ≤ 0) : ∑ᶠ x, f x ≤ 0 := by
  have h0 : 0 ≤ ∑ᶠ x, -f x := finsum_nonneg fun x => neg_nonneg.2 (h x)
  rw [finsum_neg_distrib] at h0
  exact neg_nonneg.1 h0


omit [∀ k, Fintype (ι k)] in
theorem isOpen_blocksNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem isConeTangent_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y
    hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun T => T ξ) (hd.unique h0)
  simpa [smul_eq_mul] using this

theorem maDensity_nonneg_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hsp : ∀ j, IsSemipositiveRel P0 P (L j))
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun j y' => Real.log ((L j).h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j => ?_
  have hh : ContDiffAt ℝ 2 (L j).h (γ y) :=
    ((hsp j).1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log ((L j).h z)) (γ y) :=
    hh.log ((L j).pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log ((L j).h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log ((L j).h z)) ξ hA hlog
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log ((L j).h z)) ∘ γ) y ξ
  rw [hl]
  exact (hsp j).2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)

theorem proof : IntegralAgainstPositive.Statement := by
  intro K _ ι _ P P0 e L g hP0 hsp hg
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine integral_nonpos fun y => ?_
    have key : ∀ w, sheetDensity P hΨ.choose (pot L) g y w ≤ 0 := by
      intro w
      unfold sheetDensity
      split_ifs with hγ
      · have hsh := hγ.choose_spec
        have hz : hγ.choose y ∈ mcPts P := hsh.2.self_of_nhds.2.1
        exact mul_nonpos_of_nonpos_of_nonneg (hg _ hz) (maDensity_nonneg_of_sheet hP0 hsp hsh)
      · exact le_rfl
    exact finsum_nonpos_of fun w => finsum_nonpos_of fun _ => key w
  · exact le_rfl

end IntegralAgainstPositive

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartConstantsDetermined
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

namespace ChartConstantsDetermined

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_chart_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : MRing ι) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = eval (fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap y f) := by
  have h := MvPolynomial.ringHom_ext
    (f := (aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] Ω).toRingHom)
    (g := (eval (fun k => (y ⟨k, c k⟩)⁻¹)).comp (mConeMap y).toRingHom)
    (fun r => by simp) (fun p => by simp [mConeMap, div_eq_mul_inv])
  exact RingHom.congr_fun h f

theorem aeval_chart_of_isMultiHomog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {f : MRing ι} {d : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = aeval y f * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
  rw [aeval_chart_eq, ProjLine.mConeMap_eq_of_isMultiHomog y hf]
  simp only [map_mul, eval_C, map_prod, map_pow, eval_X]

theorem aeval_chart_eq_zero (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = 0 := by
  rw [aeval_chart_eq, show mConeMap y f = 0 from RingHom.mem_ker.mp hf, map_zero]

variable (F : Type) [Field F] [NumberField F] [Algebra F Ω]

def chartCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) : ↥(chartRingZ y c ⊔ intsIn F Ω) :=
  ⟨y p / y ⟨p.1, c p.1⟩, le_sup_left (a := chartRingZ y c) (Algebra.subset_adjoin (Set.mem_range_self p))⟩

variable {F}

def pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : (Σ k, ι k) → ℂ :=
  fun p => w (chartCoord F y c p)

theorem coe_aeval_chartCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : MRing ι) :
    ((aeval (chartCoord F y c) f : ↥(chartRingZ y c ⊔ intsIn F Ω)) : Ω) =
      aeval (fun p => y p / y ⟨p.1, c p.1⟩) f := by
  show (Subalgebra.val _) (aeval (chartCoord F y c) f) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

theorem eval_pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ)
    (f : MRing ι) :
    eval (pointOf y c w) (map (Int.castRingHom ℂ) f) = w (aeval (chartCoord F y c) f) := by
  rw [eval_map]
  have h := MvPolynomial.ringHom_ext (f := eval₂Hom (Int.castRingHom ℂ) (pointOf y c w))
    (g := w.comp (aeval (chartCoord F y c) : MRing ι →ₐ[ℤ] _).toRingHom)
    (fun r => by simp) (fun p => by simp [pointOf])
  exact RingHom.congr_fun h f

theorem pointOf_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : pointOf y c w ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
  · have h1 : chartCoord F y c ⟨k, c k⟩ = 1 := Subtype.ext (by simp [chartCoord, hc k])
    simp [pointOf, h1]
  · rw [eval_pointOf]
    have h0 : aeval (chartCoord F y c) f = 0 :=
      Subtype.ext (by rw [coe_aeval_chartCoord]; simpa using aeval_chart_eq_zero y c hf)
    simp [h0]

def intsMap {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : 𝓞 F →+* ℂ :=
  w.comp ((Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom.comp
    (((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict).toRingHom)

theorem intsMap_apply {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) (a : 𝓞 F) :
    intsMap w a = w ⟨algebraMap F Ω (algebraMap (𝓞 F) F a),
      le_sup_right (a := chartRingZ y c) (AlgHom.mem_range_self _ a)⟩ := rfl

theorem intsMap_injective {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) :
    Function.Injective (intsMap w) := by
  refine (RingHom.injective_iff_ker_eq_bot _).mpr (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  refine eq_bot_iff.2 fun n hn => ?_
  rw [Ideal.mem_bot]
  simpa [Ideal.mem_comap, RingHom.mem_ker] using hn

theorem liesOver_pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) :
    LiesOver y (IsFractionRing.lift (K := F) (intsMap_injective w)) (pointOf y c w) := by
  intro d g h θ hg hh hrel
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) θ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hψb : intsMap w b ≠ 0 := (map_ne_zero_iff _ (intsMap_injective w)).mpr hb0
  have hB : algebraMap F Ω (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb0
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap, eval_pointOf, eval_pointOf,
    div_mul_eq_mul_div, eq_div_iff hψb, intsMap_apply, intsMap_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, coe_aeval_chartCoord]
  rw [aeval_chart_of_isMultiHomog y c hg, aeval_chart_of_isMultiHomog y c hh, hrel, map_div₀]
  field_simp

theorem proof : Statement := by
  intro K _ ι _ Ω _ F _ _ _ y hU c hc w w' hw
  have hz : pointOf y c w = pointOf y c w' := funext fun p =>
    RingHom.congr_fun hw ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin (Set.mem_range_self p)⟩
  obtain ⟨sg, -, huniq⟩ := hU _ (pointOf_mem y c hc w)
  have e1 := huniq _ (liesOver_pointOf y c w)
  have e2 := huniq (IsFractionRing.lift (K := F) (intsMap_injective w'))
    (by rw [hz]; exact liesOver_pointOf y c w')
  ext x
  rcases x with ⟨_, a, rfl⟩
  show intsMap w a = intsMap w' a
  rw [← IsFractionRing.lift_algebraMap (K := F) (intsMap_injective w) a,
    ← IsFractionRing.lift_algebraMap (K := F) (intsMap_injective w') a, e1, e2]

end ChartConstantsDetermined

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSupBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionSupBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartPiece (c : ∀ k, ι k) : Set ((Σ k, ι k) → ℂ) :=
  Metric.closedBall 0 1 ∩ {w | ∀ k, w ⟨k, c k⟩ = 1}

theorem isCompact_chartPiece (c : ∀ k, ι k) : IsCompact (chartPiece c) := by
  refine (isCompact_closedBall _ _).inter_right ?_
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun k => isClosed_eq (continuous_apply _) continuous_const

theorem exists_lower (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) (c : ∀ k, ι k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) →
      (∀ k, z ⟨k, c k⟩ ≠ 0) → ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k ≤ M * A.h z := by
  have hsub : chartPiece c ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun w hw k =>
    ⟨c k, by rw [hw.2 k]; exact one_ne_zero⟩
  have hcont : ContinuousOn (fun w => (A.h w)⁻¹) (chartPiece c) :=
    (hA.mono hsub).inv₀ fun w hw => (A.pos w (hsub hw)).ne'
  obtain ⟨M, hM⟩ := (isCompact_chartPiece c).exists_bound_of_continuousOn hcont
  refine ⟨|M|, abs_nonneg M, fun z hmax hz0 => ?_⟩
  have hr : ∀ k, 0 < ‖z ⟨k, c k⟩‖ := fun k => norm_pos_iff.mpr (hz0 k)
  set s : K → ℂ := fun k => (z ⟨k, c k⟩)⁻¹ with hs
  have hs0 : ∀ k, s k ≠ 0 := fun k => inv_ne_zero (hz0 k)
  set w : (Σ k, ι k) → ℂ := fun p => s p.1 * z p with hw
  have hwS : w ∈ chartPiece c := by
    refine ⟨?_, fun k => inv_mul_cancel₀ (hz0 k)⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro p
    obtain ⟨k, i⟩ := p
    show ‖(z ⟨k, c k⟩)⁻¹ * z ⟨k, i⟩‖ ≤ 1
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (hr k), mul_one]
    exact hmax k i
  have hwpos : 0 < A.h w := A.pos w (hsub hwS)
  have h1 : 1 ≤ |M| * A.h w := by
    have := (hM w hwS).trans (le_abs_self M)
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hwpos] at this
    rw [inv_le_iff_one_le_mul₀ hwpos] at this
    exact this
  have hAw : A.h w = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * A.h z := by
    rw [hw, A.smul s z hs0, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hs, norm_inv, inv_zpow]
  have hR : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (hr k) _
  rw [hAw] at h1
  calc ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * 1 := (mul_one _).symm
    _ ≤ (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * (|M| * ((∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * A.h z)) :=
        mul_le_mul_of_nonneg_left h1 hR.le
    _ = |M| * A.h z := by field_simp

end SectionSupBound


open SectionBounded SectionSupBound in
theorem SectionSupBound.proof : SectionSupBound.Statement := by
  intro K _ ι _ Ω _ y A τ e hA he
  classical
  choose M hM0 hM using fun c => SectionSupBound.exists_lower A hA c
  choose B hB0 hB using fun c hc => SectionBounded.exists_upper y A.a τ he c hc
  set S : ℝ := ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c ^ τ else 0 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun c' _ => by
    split_ifs with hc'
    · exact mul_nonneg (hB0 c' hc') (pow_nonneg (hM0 c') τ)
    · exact le_rfl
  refine ⟨Real.log (1 + S), Real.log_nonneg (by linarith), ?_⟩
  rw [Real.exp_log (by linarith)]
  intro dg dh g h z hg hh hdeg hgy hz
  have hmax : ∀ k, ∃ i, ∀ i', ‖z ⟨k, i'⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz.1 k
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z ⟨k, i⟩‖) ⟨i0, Finset.mem_univ _⟩
    exact ⟨i, fun i' => hi i' (Finset.mem_univ _)⟩
  choose c hcmax using hmax
  have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have := hcmax k i0
    rw [h0, norm_zero] at this
    exact hi0 (norm_le_zero_iff.mp this)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hz0 k (by
    have := vanish hz (homog_X ⟨k, c k⟩) (by rw [aeval_X]; exact h0)
    simpa using this)
  have h1 := hB c hyc dg dh g h z hg hh hdeg hgy hz hcmax hz0
  have h2 := hM c z hcmax hz0
  have hpow : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) ^ τ := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]
  have h3 : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) ≤ M c ^ τ * A.h z ^ τ := by
    rw [hpow, ← mul_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _) h2 τ
  have hCge : B c hyc * M c ^ τ ≤ 1 + S := by
    have := Finset.single_le_sum (f := fun c : (∀ k, ι k) =>
        if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c ^ τ else 0)
      (fun c' _ => by
        split_ifs with hc'
        · exact mul_nonneg (hB0 c' hc') (pow_nonneg (hM0 c') τ)
        · exact le_rfl) (Finset.mem_univ c)
    simp only [dif_pos hyc] at this
    linarith
  have hAh : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) := h1
    _ ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * (M c ^ τ * A.h z ^ τ) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (hB0 c hyc) (norm_nonneg _))
    _ = (B c hyc * M c ^ τ) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by ring
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsRankBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ κ, Fintype (ι κ)] {Ω : Type} [Field Ω]


omit [∀ κ, Fintype (ι κ)] in
theorem shift_mem (y : (Σ κ, ι κ) → Ω) (c : ∀ κ, ι κ) (a a' : K → ℤ) (τ τ' : ℕ) (e : K → ℕ)
    (he : ∀ κ, (τ : ℤ) * a κ + e κ = τ' * a' κ) {s : Ω} (hs : s ∈ chartLatNm y a τ) :
    (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s ∈ chartLatNm y a' τ' := by
  intro c' hc'
  have hmem : ∀ κ, y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩ ∈ chartRingZ y c' := fun κ =>
    Algebra.subset_adjoin ⟨⟨κ, c κ⟩, rfl⟩
  have hk : ∀ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) =
      y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ)) * (y ⟨κ, c' κ⟩ ^ e κ)⁻¹ := by
    intro κ
    rw [← he κ, neg_add, zpow_add₀ (hc' κ), zpow_neg (y ⟨κ, c' κ⟩) (e κ : ℤ), zpow_natCast]
  have heq : (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) =
      (s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ))) * ∏ κ, (y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩) ^ e κ := by
    simp only [hk, div_pow, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_inv_distrib]
    ring
  rw [heq]
  refine Subalgebra.mul_mem _ (hs c' hc') (Subalgebra.prod_mem _ fun κ _ => Subalgebra.pow_mem _ ?_ _)
  exact (integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem κ⟩

theorem proof (h₁ : NmSectionsFinite.Statement) (h₂ : SecMRankBound.Statement) :
    NmSectionsRankBound.Statement := by
  intro K _ ι _ Ω _ y D a hvar hbir
  classical

  have hy : ∀ κ, ∃ i, y ⟨κ, i⟩ ≠ 0 := by
    intro κ
    obtain ⟨i, hi⟩ := hvar.2.1.2.2 κ
    refine ⟨i, fun h0 => hi ?_⟩
    simp [mCoordIdeal, RingHom.mem_ker, mConeMap, h0]

  have hchar : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simp [mCoordIdeal, RingHom.mem_ker, mConeMap]
      rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hvar.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  choose c hc using hy
  set b : K → ℕ := fun κ => (a κ).toNat + 1 with hb
  have hb1 : ∀ κ, 1 ≤ b κ := fun κ => Nat.le_add_left 1 _
  have hab : ∀ κ, a κ ≤ (b κ : ℤ) := fun κ => by simp only [hb]; push_cast; omega
  obtain ⟨J, _, d, e, τ₁, -, hgen⟩ := h₁ K ι Ω y b hb1 (fun κ => ⟨c κ, hc κ⟩) hbir 0
  obtain ⟨hfin, C, hC0, hC⟩ := h₂ K ι Ω y D b hvar hb1

  have hbig : ∀ τ, τ₁ ≤ τ → Module.Finite ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ∧
      (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ) ≤
        Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by
    intro τ hτ
    let M : J → AddSubgroup Ω := fun j => secM y (fun κ => (τ - d j) * b κ)
    let Φ : (∀ j, M j) →ₗ[ℤ] Ω :=
      ∑ j, (LinearMap.mulRight ℤ (e j)).comp ((M j).subtype.toIntLinearMap.comp (LinearMap.proj j))
    have hle : ∀ s ∈ chartLatNm y (fun κ => (b κ : ℤ)) τ, s ∈ LinearMap.range Φ := by
      intro s hs
      obtain ⟨r, hr, rfl⟩ := hgen τ hτ s hs
      exact ⟨fun j => ⟨r j, hr j⟩, by simp [Φ, M]⟩
    let f : chartLatNm y (fun κ => (b κ : ℤ)) τ →ₗ[ℤ] LinearMap.range Φ :=
      LinearMap.codRestrict _ (chartLatNm y (fun κ => (b κ : ℤ)) τ).subtype.toIntLinearMap
        (fun x => hle x x.2)
    have hinj : Function.Injective f := fun x x' hxx => by
      have h := congrArg Subtype.val hxx
      exact Subtype.ext h
    have : ∀ j, Module.Finite ℤ (M j) := fun j => hfin (τ - d j)
    have : ∀ j, Module.IsTorsionFree ℤ (M j) := fun j =>
      Function.Injective.moduleIsTorsionFree (M j).subtype Subtype.val_injective (fun _ _ => rfl)
    refine ⟨Module.Finite.of_injective f hinj, ?_⟩
    have h1 : Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ≤ ∑ j, Module.finrank ℤ (M j) :=
      (LinearMap.finrank_le_finrank_of_injective hinj).trans
        ((LinearMap.finrank_range_le Φ).trans_eq (Module.finrank_pi_fintype ℤ))
    calc (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ)
        ≤ ∑ j, (Module.finrank ℤ (M j) : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ _j : J, C * ((τ : ℝ) + 1) ^ D := by
          refine Finset.sum_le_sum fun j _ => (hC (τ - d j)).trans ?_
          gcongr
          exact_mod_cast Nat.sub_le τ (d j)
      _ = Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

  have hmap : ∀ τ, ∃ f : chartLatNm y a τ →ₗ[ℤ] chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁),
      Function.Injective f := by
    intro τ
    set τ' := max τ τ₁
    set ex : K → ℕ := fun κ => ((τ' : ℤ) * b κ - τ * a κ).toNat
    have hex : ∀ κ, (τ : ℤ) * a κ + ex κ = τ' * (b κ : ℤ) := by
      intro κ
      have h0 : (τ : ℤ) * a κ ≤ τ' * b κ :=
        calc (τ : ℤ) * a κ ≤ τ * b κ := mul_le_mul_of_nonneg_left (hab κ) (by positivity)
          _ ≤ τ' * b κ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left τ τ₁) (by positivity)
      simp only [ex]
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    set u : Ω := ∏ κ, y ⟨κ, c κ⟩ ^ ex κ
    have hu : u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hc κ)
    let F : chartLatNm y a τ →+ chartLatNm y (fun κ => (b κ : ℤ)) τ' :=
      ((AddMonoidHom.mulLeft u).comp (chartLatNm y a τ).subtype).codRestrict _
        (fun x => shift_mem y c a _ τ τ' ex hex x.2)
    refine ⟨F.toIntLinearMap, fun x x' hxx => ?_⟩
    have h : u * (x : Ω) = u * x' := congrArg Subtype.val hxx
    exact Subtype.ext (mul_left_cancel₀ hu h)
  refine ⟨fun τ => ?_, Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D, by positivity, fun τ => ?_⟩
  · obtain ⟨f, hf⟩ := hmap τ
    have := (hbig (max τ τ₁) (le_max_right _ _)).1
    exact Module.Finite.of_injective f hf
  · obtain ⟨f, hf⟩ := hmap τ
    obtain ⟨hF, hR⟩ := hbig (max τ τ₁) (le_max_right _ _)
    have h1 : (Module.finrank ℤ (chartLatNm y a τ) : ℝ) ≤
        Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁)) := by
      exact_mod_cast LinearMap.finrank_le_finrank_of_injective hf
    have h2 : ((max τ τ₁ : ℕ) : ℝ) + 1 ≤ ((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1) := by
      rcases le_total τ τ₁ with h | h
      · rw [max_eq_right h]; nlinarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]
      · rw [max_eq_left h]; nlinarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]
    calc (Module.finrank ℤ (chartLatNm y a τ) : ℝ)
        ≤ Fintype.card J * C * (((max τ τ₁ : ℕ) : ℝ) + 1) ^ D := h1.trans hR
      _ ≤ Fintype.card J * C * ((((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1)) ^ D) := by
          gcongr
      _ = Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D * ((τ : ℝ) + 1) ^ D := by rw [mul_pow]; ring

end NmSectionsRankBound

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartTaylorCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
open scoped ContDiff

noncomputable section

namespace ChartTaylorCover

theorem inv_sum_pos {ι : Type*} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    0 < (∑ k ∈ t, 1 / a k + 1)⁻¹ := by
  have : 0 ≤ ∑ k ∈ t, 1 / a k := Finset.sum_nonneg fun k _ => (one_div_pos.2 (ha k)).le
  positivity

theorem inv_sum_le {ι : Type*} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 < a i) {i : ι}
    (hi : i ∈ t) : (∑ k ∈ t, 1 / a k + 1)⁻¹ ≤ a i := by
  have h1 : 1 / a i ≤ ∑ k ∈ t, 1 / a k :=
    Finset.single_le_sum (f := fun k => 1 / a k) (fun k _ => (one_div_pos.2 (ha k)).le) hi
  have h0 : 0 < ∑ k ∈ t, 1 / a k + 1 := by
    have : 0 ≤ ∑ k ∈ t, 1 / a k := Finset.sum_nonneg fun k _ => (one_div_pos.2 (ha k)).le
    linarith
  rw [inv_le_comm₀ h0 (ha i), ← one_div]
  linarith

theorem norm_sq_le_sum {D : ℕ} (z : Fin D → ℂ) : ‖z‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := by positivity
  have h : ‖z‖ ≤ √(∑ i, ‖z i‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    exact (Real.le_sqrt (norm_nonneg _) hS).2
      (Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun k _ => by positivity)
        (Finset.mem_univ i))
  calc ‖z‖ ^ 2 ≤ (√(∑ i, ‖z i‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, ‖z i‖ ^ 2 := Real.sq_sqrt hS

theorem taylor_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) {y z : E} {M : ℝ}
    (hB : closedBall y ‖z‖ ⊆ U) (hM : ∀ w ∈ closedBall y ‖z‖, ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M) :
    f (y + z) ≤ f y + fderiv ℝ f y z + M * ‖z‖ ^ 2 := by
  set s := closedBall y ‖z‖ with hs
  have hconv : Convex ℝ s := convex_closedBall _ _
  have hys : y ∈ s := mem_closedBall_self (norm_nonneg z)
  have hyzs : y + z ∈ s := by
    rw [hs, mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ f) y)) (hM y hys)
  have hca : ∀ w ∈ U, ContDiffAt ℝ 2 f w := fun w hw => hf.contDiffAt (hU.mem_nhds hw)
  have hd1 : ∀ w ∈ s, DifferentiableAt ℝ f w := fun w hw =>
    (hca w (hB hw)).differentiableAt (by norm_num)
  have hd2 : ∀ w ∈ s, DifferentiableAt ℝ (fderiv ℝ f) w := fun w hw =>
    ((hca w (hB hw)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set ℓ := fderiv ℝ f y with hℓ
  have h1 : ∀ w ∈ s, ‖fderiv ℝ f w - ℓ‖ ≤ M * ‖z‖ := by
    intro w hw
    have := hconv.norm_image_sub_le_of_norm_fderiv_le hd2 hM hys hw
    have hw' : ‖w - y‖ ≤ ‖z‖ := by rwa [hs, mem_closedBall, dist_eq_norm] at hw
    exact this.trans (mul_le_mul_of_nonneg_left hw' hM0)
  have hh : ∀ w ∈ s, HasFDerivWithinAt (fun w => f w - ℓ w) (fderiv ℝ f w - ℓ) s w :=
    fun w hw => ((hd1 w hw).hasFDerivAt.sub ℓ.hasFDerivAt).hasFDerivWithinAt
  have h2 := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hh h1 hys hyzs
  have h3 := (Real.le_norm_self _).trans h2
  rw [map_add (f := _), add_sub_cancel_left] at h3
  have h4 : M * ‖z‖ * ‖z‖ = M * ‖z‖ ^ 2 := by ring
  linarith

theorem weight_contDiffOn {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) (j : Fin A.n) :
    ContDiffOn ℝ 2 (W.φ j ∘ (A.chart j).symm) (A.chart j).target :=
  ((W.smooth j j).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)).mono fun _ hy => ⟨hy, (A.chart j).map_target hy⟩

theorem proof : ChartTaylorCover.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV
  classical
  have hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source := fun p =>
    Classical.choose_spec (A.cover p)

  have hrad : ∀ p : X, ∃ ρ : ℝ, 0 < ρ ∧
      closedBall (A.chart (chartIdx A p) p) (2 * ρ) ⊆ (A.chart (chartIdx A p)).target := by
    intro p
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (A.chart (chartIdx A p)).open_target _
      ((A.chart _).map_source (hsrc p))
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hball⟩
  choose ρ hρ hρB using hrad

  have hdens : ∀ p : X, ∃ c : ℝ, 0 < c ∧
      ∀ y ∈ closedBall (A.chart (chartIdx A p) p) (2 * ρ p), c ≤ dV.dens (chartIdx A p) y := by
    intro p
    have hne : (closedBall (A.chart (chartIdx A p) p) (2 * ρ p)).Nonempty :=
      nonempty_closedBall.2 (by linarith [hρ p])
    obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_closedBall _ _).exists_isMinOn hne
      ((dV.smooth _).continuousOn.mono (hρB p))
    exact ⟨dV.dens _ y₀, dV.pos _ _ (hρB p hy₀), fun y hy => isMinOn_iff.1 hmin y hy⟩
  choose c hc hcB using hdens

  have hsec : ∀ (W : Weight L) (p : X), ∃ M : ℝ,
      ∀ w ∈ closedBall (A.chart (chartIdx A p) p) (2 * ρ p),
        ‖fderiv ℝ (fderiv ℝ (W.φ (chartIdx A p) ∘ (A.chart (chartIdx A p)).symm)) w‖ ≤ M := by
    intro W p
    have hop := (A.chart (chartIdx A p)).open_target
    have h1 := (weight_contDiffOn W (chartIdx A p)).fderiv_of_isOpen hop (m := 1) (by norm_num)
    exact (isCompact_closedBall _ _).exists_bound_of_continuousOn
      ((h1.continuousOn_fderiv_of_isOpen hop le_rfl).mono (hρB p))
  choose M hM using hsec

  let V : X → Set X := fun p => (A.chart (chartIdx A p)).source ∩
    (A.chart (chartIdx A p)) ⁻¹' ball (A.chart (chartIdx A p) p) (ρ p)
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun p _ => mem_iUnion.2 ⟨p, hsrc p, by exact Set.mem_preimage.mpr (mem_ball_self (hρ p))⟩)
  set Mt := ∑ p ∈ t, (|M W₀ p| + |M W₁ p|) with hMt
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun p _ => by positivity
  refine ⟨(∑ p ∈ t, 1 / ρ p + 1)⁻¹, inv_sum_pos t ρ hρ, Mt, (∑ p ∈ t, 1 / c p + 1)⁻¹,
    inv_sum_pos t c hc, ?_⟩
  intro x
  obtain ⟨p, hpt, hxV⟩ : ∃ p ∈ t, x ∈ V p := by simpa using ht (mem_univ x)
  set j := chartIdx A p with hj
  have hxs : x ∈ (A.chart j).source := hxV.1
  have hxb : A.chart j x ∈ ball (A.chart j p) (ρ p) := hxV.2
  have hr := inv_sum_le t ρ hρ hpt
  have hsub : closedBall (A.chart j x) (∑ p ∈ t, 1 / ρ p + 1)⁻¹ ⊆
      closedBall (A.chart j p) (2 * ρ p) := by
    refine closedBall_subset_closedBall' ?_
    have := mem_ball.1 hxb
    linarith
  refine ⟨j, hxs, hsub.trans (hρB p), fun y hy => (inv_sum_le t c hc hpt).trans (hcB p y (hsub hy)),
    ?_⟩

  have key : ∀ W : Weight L, |M W p| ≤ Mt → ∃ ℓ : (Fin D → ℂ) →L[ℝ] ℝ, ∀ z : Fin D → ℂ,
      ‖z‖ ≤ (∑ p ∈ t, 1 / ρ p + 1)⁻¹ →
        W.φ j ((A.chart j).symm (A.chart j x + z)) ≤ W.φ j x + ℓ z + Mt * ∑ i, ‖z i‖ ^ 2 := by
    intro W hWM
    refine ⟨fderiv ℝ (W.φ j ∘ (A.chart j).symm) (A.chart j x), fun z hz => ?_⟩
    have hzB : closedBall (A.chart j x) ‖z‖ ⊆ closedBall (A.chart j p) (2 * ρ p) :=
      (closedBall_subset_closedBall hz).trans hsub
    have hT := taylor_le (A.chart j).open_target (weight_contDiffOn W j) (hzB.trans (hρB p))
      (fun w hw => (hM W p w (hzB hw)).trans (le_abs_self _))
    have hx' : (W.φ j ∘ (A.chart j).symm) (A.chart j x) = W.φ j x := by
      simp only [Function.comp_apply, (A.chart j).left_inv hxs]
    rw [hx'] at hT
    have h1 : |M W p| * ‖z‖ ^ 2 ≤ Mt * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right hWM (by positivity)
    have h2 : Mt * ‖z‖ ^ 2 ≤ Mt * ∑ i, ‖z i‖ ^ 2 := mul_le_mul_of_nonneg_left (norm_sq_le_sum z) hMt0
    simp only [Function.comp_apply] at hT
    linarith
  intro W hW
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
  rcases hW with rfl | rfl
  · refine key _ ?_
    calc |M W p| ≤ |M W p| + |M W₁ p| := le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ Mt := Finset.single_le_sum (f := fun p => |M W p| + |M W₁ p|)
          (fun k _ => by positivity) hpt
  · refine key _ ?_
    calc |M W p| ≤ |M W₀ p| + |M W p| := le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ Mt := Finset.single_le_sum (f := fun p => |M W₀ p| + |M W p|)
          (fun k _ => by positivity) hpt

end ChartTaylorCover

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreSectionLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def FibreSectionLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D p : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → p.Prime →
    Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) a 1) →
    ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) a 0,
      ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch (y := y) (S := ZMod p) s a = z

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricTransportSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def MetricTransportSmooth.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)),
    IsInvMat B → IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) → IsSmoothMetric m'

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealGramComparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def RealGramComparison.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ), IsProjFrame d.x e →
    (fun n => resChi d n - resCChi d n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionFormsIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResolutionFormsIndependent.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ) (n r : ℕ)
    (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b → ∀ a : Fin r → ℂ,
    (∀ y : d.R.X, ∑ k, a k * eval (resPt d y) (map (algebraMap ℚ ℂ) (b k)) = 0) → a = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionDegree.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (m : ConeMetric ℂ (Ix κ)), IsProjFrame d.x e → IsSmoothMetric m →
    mInt d.R.A (fun _ => resPot d m) (fun _ => 1) = (projDeg d.x e : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameImage.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsProjFrame x e →
    imageZ (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
      (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))) = ⊥

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
