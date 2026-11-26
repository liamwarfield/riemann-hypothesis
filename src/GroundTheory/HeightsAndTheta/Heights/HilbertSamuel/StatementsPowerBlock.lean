module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


variable (ι) in
def addIdx (N : ℕ) : Option K → Type := fun k => Option.elim k (Fin N) ι

instance addIdx.instFintype (N : ℕ) : ∀ k, Fintype (addIdx ι N k)
  | none => inferInstanceAs (Fintype (Fin N))
  | some k => inferInstanceAs (Fintype (ι k))

def addBlock {Ω : Type} (y : (Σ k, ι k) → Ω) {N : ℕ} (v : Fin N → Ω) : (Σ k, addIdx ι N k) → Ω
  | ⟨none, j⟩ => v j
  | ⟨some k, i⟩ => y ⟨k, i⟩

def basePart₂ {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) : (Σ k, ι k) → ℂ := fun p => z ⟨some p.1, p.2⟩

end Objects

def PowerBlockDatum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (m N : ℕ) (v : Fin N → Ω) (d : HSMBlockDatum D (Option K) (addIdx ι N) Ω)
      (μ : Measure ((Σ k, ι k) → ℂ)),
      1 ≤ m ∧ d.y = addBlock y v ∧ d.k₀ = none ∧
      (∀ j, v j ∈ chartLat y A.a m) ∧ KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), ∀ j : Fin N,
        secNormAt y A m (v j) (basePart₂ z) * d.A.h z = ‖z ⟨none, j⟩‖) ∧
      (∀ᶠ q : ℕ in atTop, chartLat y A.a (m * q) = secM d.y (blockDeg (none : Option K) q)) ∧
      IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧ IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      ∀ (q : ℕ) (f : MRing (addIdx ι N)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg (none : Option K) q) →
        sectionL2Norm μ y A (m * q) (aeval d.y f) = blockL2Norm d q f

def PowerBlockTop.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N : ℕ) (v : Fin N → Ω) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι N))
    (I : AllFam),
    I.IsFamily → IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A → 1 ≤ m →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    B.a = unitDeg (none : Option K) → IsSmoothHerm B →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    I (Option K) (addIdx ι N) (mCoordIdeal (addBlock y v)) (D + 1) (fun _ => B) =
      (m : ℝ) ^ (D + 1) * I K ι (mCoordIdeal y) (D + 1) (fun _ => A)

def BlockChiCovolume.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) (E : AddSubgroup Ω), E = secM d.y (blockDeg d.k₀ n) →
    ∀ (r : ℕ) (ψ : E →+ EuclideanSpace ℝ (Fin r)), Function.Injective ψ →
      (∀ (s : E) (f : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n) → aeval d.y f = (s : Ω) →
        ‖ψ s‖ = blockL2Norm d n f) →
      ∀ [DiscreteTopology (imageLattice ψ)] [IsZLattice ℝ (imageLattice ψ)],
        -Real.log (ZLattice.covolume (imageLattice ψ)) = blockChi d n

open ProjLine

namespace PowerBlockProjectiveLine

end PowerBlockProjectiveLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace CurvePointsFinite

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_eq_eval₂ {F : Type*} [CommRing F] {inst : Algebra ℤ F} (y : (Σ k, ι k) → F) (f : MRing ι) :
    @aeval ℤ F _ _ _ inst y f = eval₂ (Int.castRingHom F) y f := by
  rw [aeval_def]
  congr 1
  exact RingHom.ext_int _ _

def genericPt (W : Ideal (MRing ι)) [W.IsPrime] : (Σ k, ι k) → FractionRing (MRing ι ⧸ W) :=
  fun p ↦ algebraMap (MRing ι ⧸ W) _ (Ideal.Quotient.mk W (X p))

theorem aeval_genericPt (W : Ideal (MRing ι)) [W.IsPrime] (f : MRing ι) :
    aeval (genericPt W) f = algebraMap (MRing ι ⧸ W) _ (Ideal.Quotient.mk W f) := by
  have h : (aeval (genericPt W) : MRing ι →ₐ[ℤ] _).toRingHom =
      (algebraMap (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (Ideal.Quotient.mk W) :=
    ringHom_ext (fun n ↦ by simp) (fun p ↦ by simp [genericPt])
  exact RingHom.congr_fun h f

theorem aeval_genericPt_eq_zero_iff (W : Ideal (MRing ι)) [W.IsPrime] (f : MRing ι) :
    aeval (genericPt W) f = 0 ↔ f ∈ W := by
  rw [aeval_genericPt, ← Ideal.Quotient.eq_zero_iff_mem]
  exact (IsFractionRing.injective (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).eq_iff' (map_zero _)

theorem mCoordIdeal_genericPt (W : Ideal (MRing ι)) [W.IsPrime] (hW : IsMultiHomogIdeal W) :
    mCoordIdeal (genericPt W) = W := by
  apply le_antisymm
  · intro f hf
    rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_sum_multihomogeneous_components f]
    refine Ideal.sum_mem _ fun b _ ↦ ?_
    have h1 := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2comp_mem (CoordinateConeArithVar.isMultiHomogIdeal _) b hf
    rw [mCoordIdeal, RingHom.mem_ker,
      ProjLine.mConeMap_eq_of_isMultiHomog _ (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_i2comp b f)] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact (aeval_genericPt_eq_zero_iff W _).1 (by
        have h' := MvPolynomial.C_eq_zero.1 h
        rw [aeval_eq_eval₂] at h' ⊢
        exact h')
    · exact absurd h (Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k))
  · obtain ⟨S, hS, hWS⟩ := hW
    calc W = Ideal.span S := hWS
      _ ≤ mCoordIdeal (genericPt W) := Ideal.span_le.2 fun f hf ↦ by
        obtain ⟨a, ha⟩ := hS f hf
        have hfW : f ∈ W := hWS ▸ Ideal.subset_span hf
        show f ∈ RingHom.ker (mConeMap (genericPt W))
        have h0 := (aeval_genericPt_eq_zero_iff W f).2 hfW
        rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog _ ha]
        exact mul_eq_zero_of_left (MvPolynomial.C_eq_zero.2 (by
          rw [aeval_eq_eval₂] at h0 ⊢
          exact h0)) _

theorem charZero_fractionRing (W : Ideal (MRing ι)) [W.IsPrime] (hH : IsHorizontal W) :
    CharZero (FractionRing (MRing ι ⧸ W)) := by
  have hinj : Function.Injective (algebraMap ℤ (FractionRing (MRing ι ⧸ W))) := by
    have e : algebraMap ℤ (FractionRing (MRing ι ⧸ W)) =
        (algebraMap (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (algebraMap ℤ (MRing ι ⧸ W)) :=
      RingHom.ext_int _ _
    rw [e]
    exact (IsFractionRing.injective (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (CoordinateConeArithVar.algebraMap_injective W hH)
  exact charZero_of_injective_algebraMap hinj

end CurvePointsFinite


open CurvePointsFinite in
theorem CurvePointsFinite.proof : CurvePointsFinite.Statement := by
  intro K _ ι _ W hW
  have : W.IsPrime := hW.2.1.1
  have := charZero_fractionRing W hW.2.2.1
  have hEq := mCoordIdeal_genericPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (genericPt W)) 1 := by rw [hEq]; exact hW
  have hdeg := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.degC_eq hP
  rw [hEq, GroundTheory.Heights₂.Heights.degC_eq_card_projPts] at hdeg
  have := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_blockFnField hP
  set L := ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (genericPt W)
  set S : Set (FractionRing (MRing ι ⧸ W)) :=
    {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = genericPt W p / genericPt W q}
  have hSfin : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) ↦
      genericPt W pq.1 / genericPt W pq.2).subset fun t ⟨p, q, _, ht⟩ ↦ ⟨(p, q), ht.symm⟩
  have : Finite S := hSfin.to_subtype
  have hint : ∀ t ∈ S, IsIntegral ℚ t := fun t ht ↦
    ((Algebra.IsAlgebraic.isAlgebraic (⟨t, IntermediateField.subset_adjoin ℚ S ht⟩ : L)).isIntegral).map
      L.val
  have : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin hint
  have hpos : 0 < Nat.card (L →ₐ[ℚ] ℂ) := Nat.card_pos_iff.2 ⟨⟨IsAlgClosed.lift⟩, inferInstance⟩
  exact (Nat.card_pos_iff.1 (hdeg ▸ hpos)).2

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PieceDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (sg sg' : F →+* ℂ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) →
    ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) =
      ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg' z}.indicator fun _ => (1 : ℝ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem exists_nat_mul_mem_adjoin_int {Ω : Type} [Field Ω] [CharZero Ω] (S : Set Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ S) : ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * x ∈ Algebra.adjoin ℤ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, le_rfl, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_pos, ?_⟩
    have h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : ((r.den : ℕ) : Ω) ≠ 0 := by exact_mod_cast r.den_pos.ne'
      rw [eq_ratCast (algebraMap ℚ Ω) r, Rat.cast_def, mul_div_cancel₀ _ hd]
    rw [h]
    exact intCast_mem _ _
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
    have h : ((n * m : ℕ) : Ω) * (x + y) = (m : ℤ) • ((n : Ω) * x) + (n : ℤ) • ((m : Ω) * y) := by
      simp only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]; ring
    rw [h]
    exact add_mem (zsmul_mem hnx _) (zsmul_mem hmy _)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
    have h : ((n * m : ℕ) : Ω) * (x * y) = ((n : Ω) * x) * ((m : Ω) * y) := by
      push_cast; ring
    rw [h]
    exact mul_mem hnx hmy

theorem ChartDenominator.proof : ChartDenominator.Statement := by
  intro K _ ι _ Ω _ _ y b τ s hs
  classical
  have key : ∀ c : ∀ k, ι k, ∃ n : ℕ, 1 ≤ n ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin_int _ (hs c hc)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose N hN1 hN using key
  refine ⟨∏ c, N c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => by
    have := hN1 c; omega), ?_⟩
  intro c hc
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ c)
  have h : ((∏ c, N c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)) =
      (m : ℤ) • ((N c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)))) := by
    rw [hm]; simp only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]; ring
  rw [h]
  exact zsmul_mem (hN c hc) _

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace Conductor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def invMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℕ) : Ω := ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹

theorem invMon_add (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ ε : K → ℕ) :
    invMon y c (δ + ε) = invMon y c δ * invMon y c ε := by
  rw [invMon, invMon, invMon, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add, mul_inv]

theorem invMon_sum {β : Type} (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (s : Finset β) (δ : β → K → ℕ) :
    ∏ b ∈ s, invMon y c (δ b) = invMon y c (∑ b ∈ s, δ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [invMon]
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, invMon_add]

theorem prod_zpow_eq_invMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(δ k : ℤ)) = invMon y c δ := by
  simp [invMon, zpow_neg, zpow_natCast]

theorem form_mul_invMon_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {δ : K → ℕ} {g : MRing ι}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g δ) : aeval y g * invMon y c δ ∈ chartRingZ y c := by
  rw [← prod_zpow_eq_invMon, NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ,
    Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem isFractionRing_chartRingZ (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ y c) Ω := by
  refine IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : invMon y c d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => inv_ne_zero (pow_ne_zero _ (hc k))
  refine ⟨⟨_, form_mul_invMon_mem y c hg⟩, ⟨_, form_mul_invMon_mem y c hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]

theorem exists_chart_conductor (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (δ : K → ℕ) (F : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F δ ∧ aeval y F ≠ 0 ∧
      ∀ x ∈ integralClosure (chartRingZ y c) Ω, aeval y F * invMon y c δ * x ∈ chartRingZ y c := by
  classical
  set A := chartRingZ y c
  have := isFractionRing_chartRingZ y hbir c hc
  have : Algebra.FiniteType ℤ A := .adjoin_of_finite (Set.finite_range _)
  have hfin : Module.Finite A (integralClosure A Ω) := Model.FiniteIntegralClosure.proof A Ω Ω
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun z : integralClosure A Ω => (z : Ω))
  have key : ∀ z : integralClosure A Ω, ((b : A) : Ω) * (z : Ω) ∈ A := by
    intro z
    have hz : z ∈ Submodule.span A (s : Set (integralClosure A Ω)) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨u, hu⟩ := hb _ (Finset.mem_image_of_mem _ hw)
      have : (u : Ω) = ((b : A) : Ω) * (w : Ω) := by rw [Algebra.smul_def] at hu; exact hu
      rw [← this]; exact u.2
    | zero => simp
    | add w v _ _ hw hv => rw [Subalgebra.coe_add, mul_add]; exact add_mem hw hv
    | smul r w _ hw =>
      rw [Subalgebra.coe_smul, Algebra.smul_def, mul_left_comm]
      exact mul_mem r.2 hw
  have hb0 : ((b : A) : Ω) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext h)
  obtain ⟨δ, e, he, hv⟩ := SectionBounded.exists_form_of_mem_chartRingZ y c hc (b : A).2
  have hm : (∏ k, y ⟨k, c k⟩ ^ δ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hbv : aeval y e * invMon y c δ = ((b : A) : Ω) := by
    rw [hv, invMon, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hm, mul_one]
  refine ⟨δ, e, he, by rw [hv]; exact mul_ne_zero hb0 hm, fun x hx => ?_⟩
  rw [hbv]
  exact key ⟨x, hx⟩

theorem homog_prod {β : Type} (s : Finset β) (F : β → MRing ι) (δ : β → K → ℕ)
    (h : ∀ b ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (F b) (δ b)) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ b ∈ s, F b) (∑ b ∈ s, δ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (SectionBounded.homog_one (ι := ι))
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact SectionBounded.homog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

end Conductor

theorem Conductor.proof (hS : SecEq.Statement) : KH.CondStatement := by
  classical
  intro K _ ι _ Ω _ y a ha hy hbir
  obtain ⟨τ₀, hτ₀⟩ := hS K ι Ω y a ha hy
  let C := {c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}
  choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2
  choose i0 hi0 using hy
  set Δ : K → ℕ := ∑ c : C, δ c
  set k' : ℕ := τ₀ + ∑ κ, Δ κ
  have hΔ : ∀ κ, Δ κ ≤ k' * a κ := fun κ =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)).trans
      ((Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ (ha κ)))
  set e : K → ℕ := fun κ => k' * a κ - Δ κ
  set Φ : MRing ι := (∏ c : C, F c) * SectionBounded.chartMon i0 e
  have hΦ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog Φ (fun κ => k' * a κ) :=
    SectionBounded.homog_congr (SectionBounded.homog_mul
      (Conductor.homog_prod Finset.univ F δ fun c _ => hF c) (SectionBounded.homog_chartMon i0 e))
      fun κ => by simp only [Pi.add_apply, e]; exact Nat.add_sub_cancel' (hΔ κ)
  have hM : aeval y (SectionBounded.chartMon i0 e) ≠ 0 := by
    rw [SectionBounded.aeval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hi0 κ)
  have hΦ0 : aeval y Φ ≠ 0 := by
    rw [map_mul, map_prod]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c) hM
  refine ⟨k', Φ, hΦ, hΦ0, fun τ s hs => ?_⟩
  rw [← hτ₀ (τ + k') (by omega)]
  intro c' hc'
  set c : C := ⟨c', hc'⟩
  have hx := hs c' hc'
  have hτ : (fun κ => τ * a κ) + Δ + e = fun κ => (τ + k') * a κ := by
    funext κ
    simp only [Pi.add_apply, e]
    rw [add_assoc, Nat.add_sub_cancel' (hΔ κ)]
    ring
  have hexp : ∀ n : K → ℕ, (∏ κ, y ⟨κ, c' κ⟩ ^ (-((n κ : ℕ) : ℤ))) = Conductor.invMon y c' n :=
    Conductor.prod_zpow_eq_invMon y c'
  beta_reduce at hx ⊢
  have e1 : ∀ κ, -((τ : ℤ) * (a κ : ℤ)) = -(((τ * a κ : ℕ)) : ℤ) := fun κ => by push_cast; ring
  have e2 : ∀ κ, -(((τ + k' : ℕ) : ℤ) * (a κ : ℤ)) = -((((τ + k') * a κ : ℕ)) : ℤ) := fun κ => by push_cast; ring
  simp only [e1] at hx
  simp only [e2]
  rw [hexp (fun κ => τ * a κ)] at hx
  rw [hexp (fun κ => (τ + k') * a κ), ← hτ, Conductor.invMon_add, Conductor.invMon_add,
    ← Conductor.invMon_sum y c' Finset.univ δ]
  have hsplit : aeval y Φ * s * (Conductor.invMon y c' (fun κ => τ * a κ) *
      (∏ b : C, Conductor.invMon y c' (δ b)) * Conductor.invMon y c' e) =
      (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) *
        (aeval y (SectionBounded.chartMon i0 e) * Conductor.invMon y c' e) *
        (aeval y (F c) * Conductor.invMon y c' (δ c) * (s * Conductor.invMon y c' (fun κ => τ * a κ))) := by
    rw [map_mul, map_prod]
    rw [← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c),
      ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c),
      Finset.prod_mul_distrib]
    ring
  rw [hsplit]
  refine mul_mem (mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b))
    (Conductor.form_mul_invMon_mem y c' (SectionBounded.homog_chartMon i0 e))) ?_
  exact hcond c _ hx

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology MeasureTheory

noncomputable section

namespace ConstantShift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem sheetDensity_add_const (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∃ c : ℝ, ∀ z ∈ mcPts P, φ' j z = φ j z + c)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ' g y w = sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs with hγ
  · congr 1
    have hH : ∀ k, cxHessian (fun y' => φ' k (hγ.choose y')) y =
        cxHessian (fun y' => φ k (hγ.choose y')) y := by
      intro k
      obtain ⟨c, hc⟩ := h k
      have h1 : (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y] fun y' => φ k (hγ.choose y') + c := by
        filter_upwards [hγ.choose_spec.2] with y' hy'
        exact hc _ hy'.2.1
      have h2 : fderiv ℝ (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y]
          fderiv ℝ (fun y' => φ k (hγ.choose y')) := by
        filter_upwards [h1.eventuallyEq_nhds] with x hx
        rw [hx.fderiv_eq, fderiv_add_const]
      unfold cxHessian
      rw [h2.fderiv_eq]
    simp only [maDensity, hH]
  · rfl


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_add_const (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∃ c : ℝ, ∀ z ∈ mcPts P, φ' j z = φ j z + c) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ' g = ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, sheetDensity_add_const P h]
  · rfl


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_const (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (r : ℝ) :
    ptsIntegral P φ (fun _ => r) = r * ptsIntegral P φ (fun _ => 1) := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ (fun _ => r) y w = r * sheetDensity P Ψ φ (fun _ => 1) y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, hs]
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
  · simp

theorem proof : ConstantShift.Statement := by
  intro K _ ι _ I P D A η hI hP hA
  have hS : IsSmoothHerm (HermLine.constShift A η) := isSmoothHerm_constShift hA η
  set g := geomDeg P A D with hg
  let L : ℕ → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun n i =>
    if (i : ℕ) < n then HermLine.constShift A η else A
  have hLs : ∀ n i, IsSmoothHerm (L n i) := by
    intro n i
    dsimp only [L]
    split_ifs
    exacts [hS, hA]
  have hLpot : ∀ n i, ∃ c : ℝ, ∀ z ∈ mcPts P, Real.log ((L n i).h z) = Real.log (A.h z) + c := by
    intro n i
    dsimp only [L]
    split_ifs
    · refine ⟨-η, fun z hz => ?_⟩
      rw [constShift_h, Real.log_mul (A.pos z hz.1).ne' (Real.exp_pos _).ne', Real.log_exp]
    · exact ⟨0, fun z _ => by rw [add_zero]⟩
  have step : ∀ n, n < D + 1 → I P (D + 1) (L (n + 1)) = I P (D + 1) (L n) - η * g := by
    intro n hn
    set j : Fin (D + 1) := ⟨n, hn⟩ with hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := Fin.init (L n ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (n + 1) ∘ σ) = M := by
      funext i
      have hv : ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) ≠ n := fun h' => hne i (Fin.ext h')
      have hiff : ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) < n + 1 ↔
          ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) < n := by omega
      simp only [hMdef, Fin.init, Function.comp, L, hiff]
    have e0 : L n ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L n ∘ σ)
      have hl : (L n ∘ σ) (Fin.last D) = A := by
        simp only [Function.comp, hσl, hj, L, lt_irrefl, if_false]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (n + 1) ∘ σ = Fin.snoc M (HermLine.constShift A η) := by
      have h0 := Fin.snoc_init_self (q := L (n + 1) ∘ σ)
      have hl : (L (n + 1) ∘ σ) (Fin.last D) = HermLine.constShift A η := by
        simp only [Function.comp, hσl, hj, L, lt_add_one, if_true]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs n _
    have hmc : I P (D + 1) (Fin.snoc M (HermLine.constShift A η)) =
        I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => η) :=
      metricChange K ι I hI P D M A (fun _ => η) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const
    have hint : ptsIntegral P (pot M) (fun _ => η) = η * g := by
      rw [ptsIntegral_const, hg, geomDeg]
      congr 1
      exact ptsIntegral_add_const P (fun i => hLpot n _) _
    rw [← hI.1 P (D + 1) (L (n + 1)) σ hP (hLs (n + 1)), ← hI.1 P (D + 1) (L n) σ hP (hLs n), e0, e1,
      hmc, hint]
  have hall : ∀ n, n ≤ D + 1 → I P (D + 1) (L n) = I P (D + 1) (L 0) - n * η * g := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [step n (by omega), ih (by omega)]
      push_cast
      ring
  have hL0 : L 0 = fun _ => A := by
    funext i
    simp [L]
  have hLD : L (D + 1) = fun _ => HermLine.constShift A η := by
    funext i
    simp [L, i.isLt]
  have := hall (D + 1) le_rfl
  rw [hL0, hLD] at this
  rw [this]
  push_cast
  ring

end ConstantShift

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsQuotPartGraded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def QuotPartGraded.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (V : Ideal (MRingOver S ι)), IsMultiHomogIdeal V → KH.IsMGraded S ι (KH.quotPart S V)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormCharpoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def pullField (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ {x | ∃ i j, aeval y (L j) ≠ 0 ∧ x = aeval y (L i) / aeval y (L j)}

end Defs

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegreeSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def SublatticeExtension.Statement : Prop :=
  ∀ (E E' : Type) [AddCommGroup E] [AddCommGroup E'] (R R' : ℕ) (φ : E →+ EuclideanSpace ℝ (Fin R))
    (φ' : E' →+ EuclideanSpace ℝ (Fin R')) [DiscreteTopology (imageLattice φ)]
    [DiscreteTopology (imageLattice φ')] [IsZLattice ℝ (imageLattice φ')] (ψ : E' →+ E),
    Function.Injective φ → Function.Injective φ' → Function.Injective ψ → (∀ x, ‖φ (ψ x)‖ ≤ ‖φ' x‖) →
    ∃ Ψ : EuclideanSpace ℝ (Fin R') →ₗ[ℝ] EuclideanSpace ℝ (Fin R),
      (∀ x, Ψ (φ' x) = φ (ψ x)) ∧ (∀ y, ‖Ψ y‖ ≤ ‖y‖) ∧ Function.Injective Ψ

def SpanningExtension.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ι : Type) [Fintype ι]
    (v : ι → V) (S : Set V), LinearIndependent ℝ v → Submodule.span ℝ S = ⊤ →
    ∃ w : Fin (Module.finrank ℝ V - Fintype.card ι) → V, (∀ j, w j ∈ S) ∧ LinearIndependent ℝ (Sum.elim v w)

def CovolumeLeGram.Statement : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (ι : Type) [Fintype ι] [DecidableEq ι] (x : ι → EuclideanSpace ℝ (Fin n)), (∀ i, x i ∈ L) →
    LinearIndependent ℝ x → Fintype.card ι = n → ZLattice.covolume L ≤ Real.sqrt (Matrix.gram ℝ x).det

def GramContraction.Statement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (Ψ : EuclideanSpace ℝ ι →ₗ[ℝ] V) (u : ι → EuclideanSpace ℝ ι) (w : κ → V),
    (∀ y, ‖Ψ y‖ ≤ ‖y‖) →
      (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det ≤ (Matrix.gram ℝ u).det * ∏ j, ‖w j‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIsomInvariance
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace IsomInvariance

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_ratSection {P : Ideal (MRing ι)} (hP : P.IsPrime) (hrel : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant P) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    ∃ s t : MRing ι, IsRatSectionOn P B s t := by
  classical
  let c : ∀ k, ι k := fun k => (hrel k).choose
  have hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P := fun k => (hrel k).choose_spec
  exact ⟨_, _, fun k => (B.a k).toNat, fun k => (-B.a k).toNat, Inter.AvoidRing.isMultiHomog_coordProd c _,
    Inter.AvoidRing.isMultiHomog_coordProd c _, Inter.AvoidRing.coordProd_not_mem hP c hc _,
    Inter.AvoidRing.coordProd_not_mem hP c hc _, fun k => Int.toNat_sub_toNat_neg _⟩

theorem snoc_eq (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {m : ℕ} (N : Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (hP : IsArithVar P (m + 1)) (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAB : IsIsometricOn P A B) : I P (m + 1) (Fin.snoc N A) = I P (m + 1) (Fin.snoc N B) := by
  obtain ⟨f, g, α, β, hf, hg, hfP, hgP, hdeg, hdiv, hnorm⟩ := hAB
  have hPp : P.IsPrime := hP.2.1.1
  have nm : ∀ {x y : MRing ι}, x ∉ P → y ∉ P → x * y ∉ P := fun hx hy h => (hPp.mem_or_mem h).elim hx hy
  obtain ⟨s, t, σ, τ, hs, ht, hsP, htP, hst⟩ := exists_ratSection hPp hP.2.1.2.2 B
  have hB' : IsRatSectionOn P B (s * g) (t * g) :=
    ⟨σ + β, τ + β, Inter.AvoidRing.isMultiHomog_mul hs hg, Inter.AvoidRing.isMultiHomog_mul ht hg,
      nm hsP hgP, nm htP hgP, fun k => by have := hst k; simp only [Pi.add_apply]; push_cast; linarith⟩
  have hA' : IsRatSectionOn P A (s * f * g) (t * g * g) :=
    ⟨σ + α + β, τ + β + β,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul hs hf) hg,
      Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_mul ht hg) hg,
      nm (nm hsP hfP) hgP, nm (nm htP hgP) hgP,
      fun k => by have := hst k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith⟩
  rw [hR K ι I hI P m N A _ _ hP hN hA hA', hR K ι I hI P m N B _ _ hP hN hB hB']
  unfold recRRat
  have hfg : cycR I P N f = cycR I P N g := by
    rw [Inter.cycR_eq_sum, Inter.cycR_eq_sum, hdiv]
  have hint : ptsIntegral P (pot N) (logNormRat A (s * f * g) (t * g * g)) =
      ptsIntegral P (pot N) (logNormRat B (s * g) (t * g)) := by
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun _ _ _ => rfl) fun z hz => ?_
    unfold logNormRat
    congr 1
    have ha := A.pos z hz.1
    have hb := B.pos z hz.1
    have hn := hnorm z hz
    simp only [map_mul, norm_mul] at hn ⊢
    set S := ‖eval z (map (Int.castRingHom ℂ) s)‖
    set T := ‖eval z (map (Int.castRingHom ℂ) t)‖
    set F := ‖eval z (map (Int.castRingHom ℂ) f)‖
    set G := ‖eval z (map (Int.castRingHom ℂ) g)‖
    rcases eq_or_ne T 0 with hT | hT
    · simp [hT]
    rcases eq_or_ne G 0 with hG | hG
    · simp [hG]
    rw [div_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (S * G * G * T) * hn
  rw [Inter.cycR_mul I hPp N (nm hsP hfP) hgP, Inter.cycR_mul I hPp N hsP hfP,
    Inter.cycR_mul I hPp N (nm htP hgP) hgP, Inter.cycR_mul I hPp N htP hgP,
    Inter.cycR_mul I hPp N hsP hgP, hint, hfg]
  ring

theorem update_eq (hR : RatRStatement) {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (j : Fin n)
    (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hP : IsArithVar P n) (hL : ∀ i, IsSmoothHerm (L i)) (hB : IsSmoothHerm B)
    (hLB : IsIsometricOn P (L j) B) : I P n L = I P n (Function.update L j B) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) j.2))
  have hL' : ∀ i, IsSmoothHerm (Function.update L j B i) := fun i => by
    by_cases hi : i = j
    · subst hi; simpa using hB
    · simpa [Function.update_of_ne hi] using hL i
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
  let N : Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun i => L (σ i.castSucc)
  have hne : ∀ i : Fin m, σ i.castSucc ≠ j := fun i h => by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact Fin.castSucc_ne_last i h
  have e1 : L ∘ σ = Fin.snoc N (L j) := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp [N]
  have e2 : Function.update L j B ∘ σ = Fin.snoc N B := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [σ]
    · simp [N, Function.update_of_ne (hne i)]
  rw [← hI.1 P _ L σ hP hL, ← hI.1 P _ _ σ hP hL', e1, e2]
  exact snoc_eq hR hI N (L j) B hP (fun i => hL _) (hL j) hB hLB

end IsomInvariance

theorem IsomInvariance.proof (hR : Inter.RatR.Statement) : IsomInvariance.Statement := by
  classical
  intro K _ ι _ I hI P n L L' hP hL hL' hiso
  let M : Finset (Fin n) → Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun S j => if j ∈ S then L' j else L j
  have hM : ∀ S j, IsSmoothHerm (M S j) := fun S j => by
    by_cases h : j ∈ S
    · simpa [M, h] using hL' j
    · simpa [M, h] using hL j
  have key : ∀ S : Finset (Fin n), I P n L = I P n (M S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [M]
    | insert a S ha ih =>
      have e : M (insert a S) = Function.update (M S) a (L' a) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp [M]
        · simp [M, hj]
      have hMa : M S a = L a := by simp [M, ha]
      rw [ih, e]
      exact IsomInvariance.update_eq hR hI (M S) a (L' a) hP (hM S) (hL' a) (hMa ▸ hiso a)
  have hU : M Finset.univ = L' := by funext j; simp [M]
  rw [key Finset.univ, hU]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedProductNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedProductNonneg.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (m : ℕ)
    (β : Fin m → K → ℤ),
    IsFieldIntersection I → IsProjVarF V m → (∀ j, KH.GeneratedV F V (β j)) → 0 ≤ I V m β

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameBasePtFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameBasePtFree.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsProjFrame x e →
    IsBasePtFree (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x)
      (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleimanTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleimanTop.Statement : Prop :=
  ∀ d : ℕ, 2 ≤ d → MixedKleiman.AtDim (d - 1) → MixedKleiman.LowAt d → MixedKleiman.TopAt d

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
