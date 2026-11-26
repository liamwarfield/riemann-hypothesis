module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomogPrime
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NumericalSegreClosed

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideRest
theorem UpperTheory.Reformulated.B.Yla8.main :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {T : Type} [Finite T] (y : T → Ω),
      (∃ (x : T), y x ≠ (0 : Ω)) → ∃ (x₀ : T), y x₀ ≠ (0 : Ω) ∧ ∀ (x : T), y x / y x₀ ∈ A := by
  intro Ω _ A T _ y ⟨x1, hx1⟩
  have : Nonempty {x : T // y x ≠ 0} := ⟨⟨x1, hx1⟩⟩
  obtain ⟨⟨x₀, h0⟩, hmax⟩ := Finite.exists_max (fun z : {x : T // y x ≠ 0} => A.valuation (y z.1))
  refine ⟨x₀, h0, fun x => ?_⟩
  by_cases hx : y x = 0
  · rw [hx, zero_div]; exact A.zero_mem
  · rw [← A.valuation_le_one_iff, map_div₀]
    have hpos : (0 : A.ValueGroup) < A.valuation (y x₀) := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr h0
    exact (div_le_one₀ hpos).mpr (hmax ⟨x, hx⟩)
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsCurvePoint
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.AevalZeroOfMem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo PositivityTheory.HtPt
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace LevelTowerAlt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem aeval_zero_of_mem {Ω : Type} [Field Ω] {x : (Σ k, J k) → Ω} {f : MRing J} (hf : f ∈ mCoordIdeal x) :
    aeval x f = 0 := by
  have h0 : mConeMap x f = 0 := hf
  have e : ((MvPolynomial.eval fun _ : K => (1 : Ω)).comp (mConeMap x).toRingHom) =
      (aeval x : MRing J →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro p
      simp [mConeMap]
  have h1 : (aeval x : MRing J →ₐ[ℤ] Ω) f = (MvPolynomial.eval fun _ : K => (1 : Ω)) ((mConeMap x) f) :=
    (congrArg (fun g => g f) e).symm
  rw [h1, h0, map_zero]

theorem hom_X (p : Σ k, J k) : ∃ d, IsMultiHomog (X p : MRing J) d := by
  classical
  exact ⟨_, (Gf.hom_iff _ _).2 (isWeightedHomogeneous_X ℤ _ p)⟩

theorem exists_homog (c : ∀ k, J k) (f : MRing J) : ∃ (d : K → ℕ) (h : MRing J), IsMultiHomog h d ∧
    ∀ (Ω : Type) [Field Ω] (z : (Σ k, J k) → Ω), (∀ k, z ⟨k, c k⟩ = 1) → aeval z h = aeval z f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, (Gf.hom_iff _ _).2 (isWeightedHomogeneous_C _ _), fun _ _ _ _ => rfl⟩
  | add f g hf hg =>
    obtain ⟨d, h, hh, e⟩ := hf
    obtain ⟨d', h', hh', e'⟩ := hg
    refine ⟨d + d', h * Gf.mon c d' + Gf.mon c d * h',
      Gf.hom_add (Gf.hom_mul hh (Gf.hom_mon c d')) (Gf.hom_mul (Gf.hom_mon c d) hh'), fun Ω _ z hz => ?_⟩
    simp only [map_add (f := _), map_mul, Gf.aeval_mon, hz, one_pow, Finset.prod_const_one, mul_one, one_mul, e Ω z hz,
      e' Ω z hz]
  | mul_X f p hf =>
    obtain ⟨d, h, hh, e⟩ := hf
    obtain ⟨d', h'⟩ := hom_X p
    exact ⟨_, h * X p, Gf.hom_mul hh h', fun Ω _ z hz => by rw [map_mul, map_mul, e Ω z hz]⟩

theorem le_mCoordIdeal {Ω : Type} [Field Ω] {P : Ideal (MRing J)} (hP : IsMultiHomogIdeal P) {w : (Σ k, J k) → Ω}
    (h : ∀ g ∈ P, aeval w g = 0) : P ≤ mCoordIdeal w := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine Ideal.span_le.2 fun g hg => ?_
  obtain ⟨d, hd⟩ := hS g hg
  exact Gf.mem_mCoordIdeal hd (h g (Ideal.subset_span hg))

theorem aeval_hom {A B : Type} [CommRing A] [CommRing B] (σ : A →+* B) (z : (Σ k, J k) → A) (g : MRing J) :
    σ (aeval z g) = aeval (fun p => σ (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp => simp [hp]

theorem hom_eq_aeval {B : Type} [CommRing B] (F : MRing J →+* B) (z : (Σ k, J k) → B) (h : ∀ p, F (X p) = z p)
    (g : MRing J) : F g = aeval z g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp => simp [hp, h]

theorem exists_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {T : Type} [Finite T] (y : T → Ω)
    (h : ∃ x, y x ≠ 0) : ∃ x₀, y x₀ ≠ 0 ∧ ∀ x, y x / y x₀ ∈ A :=
  _root_.UpperTheory.Reformulated.B.Yla8.main A y h

variable {K' : Type} [Fintype K'] {J' : K' → Type} [∀ k, Fintype (J' k)]

theorem exists_lift_blk {Ω L : Type} [Field Ω] [Field L] (y' : (Σ k, J' k) → Ω) (bk : K → K')
    (bx : ∀ k, J k ≃ J' (bk k)) (hbk : Function.Injective bk) (hy' : ∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0)
    (w : (Σ k, J k) → L) (c : ∀ k, J k) (hc : ∀ k, w ⟨k, c k⟩ = 1)
    (hle : mCoordIdeal (fun p : Σ k, J k => y' ⟨bk p.1, bx p.1 p.2⟩) ≤ mCoordIdeal w) :
    ∃ (k₀ L₁ : Type) (_ : Field k₀) (_ : Field L₁) (σ : k₀ →+* L) (_ : Algebra k₀ L₁) (_ : Module.Finite k₀ L₁)
      (w₀ : (Σ k, J k) → k₀) (w' : (Σ k, J' k) → L₁), (∀ p, σ (w₀ p) = w p) ∧
      (∀ p : Σ k, J k, w' ⟨bk p.1, bx p.1 p.2⟩ = algebraMap k₀ L₁ (w₀ p)) ∧ (∀ k, ∃ x, w' ⟨k, x⟩ ≠ 0) ∧
      mCoordIdeal y' ≤ mCoordIdeal w' := by
  classical
  set z : (Σ k, J k) → Ω := fun p => y' ⟨bk p.1, bx p.1 p.2⟩ with hz
  have hzc : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨d, hd⟩ := hom_X (J := J) ⟨k, c k⟩
    have := aeval_zero_of_mem (hle (Gf.mem_mCoordIdeal hd (by rw [aeval_X, h0])))
    rw [aeval_X, hc] at this
    exact one_ne_zero this
  let φ : MRing J →+* Ω := (aeval (ratioPt z c) : MRing J →ₐ[ℤ] Ω)
  let ψ : MRing J →+* L := (aeval w : MRing J →ₐ[ℤ] L)
  have hker : ∀ f, φ f = 0 → ψ f = 0 := fun f hf => by
    obtain ⟨d, h, hh, e⟩ := exists_homog c f
    have h1 : aeval (ratioPt z c) h = 0 := (e Ω _ fun k => div_self (hzc k)).trans hf
    have h2 := Gf.mem_mCoordIdeal hh h1
    rw [← mCoordIdeal_ratioPt z c hzc] at h2
    exact (e L w hc).symm.trans (aeval_zero_of_mem (hle h2))
  let q : Ideal (MRing J) := RingHom.ker ψ
  have : q.IsPrime := RingHom.ker_isPrime ψ
  have hu : ∀ s : q.primeCompl, IsUnit (φ s) := fun s => IsUnit.mk0 _ fun h => s.2 (hker _ h)
  let f : Localization.AtPrime q →+* Ω := IsLocalization.lift hu
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hf : ∀ g, f (algebraMap _ _ g) = φ g := fun g => IsLocalization.lift_eq hu g
  have hφA : ∀ g, φ g ∈ A := fun g => hf g ▸ hA _
  let φA : MRing J →+* A := φ.codRestrict A.toSubring hφA
  have hφA' : ∀ g, φA g = f.codRestrict A.toSubring hA (algebraMap _ _ g) := fun g => Subtype.ext (hf g).symm
  let θ : MRing J →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp φA
  have hθ : ∀ g, θ g = 0 ↔ g ∈ q := fun g => by
    change IsLocalRing.residue A (φA g) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hφA']
    have h1 : IsUnit (f.codRestrict A.toSubring hA (algebraMap _ _ g)) ↔
        IsUnit (algebraMap _ (Localization.AtPrime q) g) := ⟨fun h => hloc.1 _ h, fun h => h.map _⟩
    refine (not_congr h1).trans ?_
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q g]
    exact not_not
  let τ : q.ResidueField →+* IsLocalRing.ResidueField A := Ideal.ResidueField.lift q θ
    (fun g hg => (hθ g).2 hg) fun g hg => IsUnit.mk0 _ fun h => hg ((hθ g).1 h)
  let σ : q.ResidueField →+* L := Ideal.ResidueField.lift q ψ le_rfl fun g hg => IsUnit.mk0 _ hg
  have hch : ∀ k', ∃ x₀ : J' k', y' ⟨k', x₀⟩ ≠ 0 ∧ (∀ x, y' ⟨k', x⟩ / y' ⟨k', x₀⟩ ∈ A) ∧
      ∀ k, bk k = k' → y' ⟨k', x₀⟩ = z ⟨k, c k⟩ := by
    intro k'
    by_cases hk : k' ∈ Set.range bk
    · obtain ⟨k, rfl⟩ := hk
      refine ⟨bx k (c k), hzc k, fun x => ?_, fun k₁ h => ?_⟩
      · have := hφA (X ⟨k, (bx k).symm x⟩)
        simpa [φ, ratioPt, hz] using this
      · obtain rfl := hbk h
        rfl
    · obtain ⟨x₀, h1, h2⟩ := exists_val A (fun x => y' ⟨k', x⟩) (hy' k')
      exact ⟨x₀, h1, h2, fun k h => absurd ⟨k, h⟩ hk⟩
  choose c' hc'0 hc'A hc'z using hch
  let u : (Σ k, J' k) → A := fun p => ⟨ratioPt y' c' p, hc'A p.1 p.2⟩
  let ub : (Σ k, J' k) → IsLocalRing.ResidueField A := fun p => IsLocalRing.residue A (u p)
  let E : MvPolynomial (Σ k, J' k) q.ResidueField →+* IsLocalRing.ResidueField A := eval₂Hom τ ub
  obtain ⟨m, hm, hEm⟩ := Ideal.exists_le_maximal (RingHom.ker E) (RingHom.ker_ne_top E)
  let _ : Field (MvPolynomial (Σ k, J' k) q.ResidueField ⧸ m) := Ideal.Quotient.field m
  let _ : Algebra q.ResidueField (MvPolynomial (Σ k, J' k) q.ResidueField ⧸ m) := Ideal.Quotient.algebra _
  refine ⟨q.ResidueField, MvPolynomial (Σ k, J' k) q.ResidueField ⧸ m, inferInstance, inferInstance, σ, inferInstance,
    finite_of_finite_type_of_isJacobsonRing _ _, fun p => algebraMap _ _ (X p : MRing J),
    fun p => Ideal.Quotient.mk m (X p), fun p => ?_, fun p => ?_, fun k => ⟨c' k, ?_⟩, ?_⟩
  · exact (Ideal.ResidueField.lift_algebraMap q ψ _ _ (X p)).trans (aeval_X _ _)
  · change Ideal.Quotient.mk m _ = Ideal.Quotient.mk m (C _)
    rw [Ideal.Quotient.eq]
    refine hEm ?_
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    simp only [E, coe_eval₂Hom, eval₂_X, eval₂_C]
    refine Eq.trans ?_ (Ideal.ResidueField.lift_algebraMap q θ _ _ (X p)).symm
    change IsLocalRing.residue A _ = IsLocalRing.residue A _
    congr 1
    apply Subtype.ext
    change y' _ / y' ⟨bk p.1, c' (bk p.1)⟩ = φ (X p)
    rw [hc'z _ p.1 rfl]
    simp [φ, ratioPt, hz]
  · have h1 : Ideal.Quotient.mk m (X ⟨k, c' k⟩) = Ideal.Quotient.mk m 1 := by
      rw [Ideal.Quotient.eq]
      refine hEm ?_
      rw [RingHom.mem_ker, map_sub, sub_eq_zero, map_one]
      simp only [E, coe_eval₂Hom, eval₂_X]
      have : u ⟨k, c' k⟩ = 1 := Subtype.ext (div_self (hc'0 k))
      simp only [ub, this, map_one]
    intro h0
    exact one_ne_zero ((map_one _).symm.trans (h1.symm.trans h0))
  · refine le_mCoordIdeal (isMultiHomogIdeal y') fun g hg => ?_
    rw [mCoordIdeal_ratioPt y' c' hc'0] at hg
    have h1 : aeval u g = 0 := by
      apply Subtype.ext
      exact (aeval_hom A.subtype u g).trans (aeval_zero_of_mem hg)
    have h3 : IsLocalRing.residue A (aeval u g) = 0 := by rw [h1, map_zero]
    have h4 := hom_eq_aeval (E.comp (MvPolynomial.map (Int.castRingHom q.ResidueField))) ub
      (fun p => by simp only [RingHom.comp_apply, map_X, E, coe_eval₂Hom, eval₂_X]) g
    have h2 : E (MvPolynomial.map (Int.castRingHom q.ResidueField) g) = 0 :=
      h4.trans ((aeval_hom (IsLocalRing.residue A) u g).symm.trans h3)
    have h5 := hom_eq_aeval ((Ideal.Quotient.mk m).comp (MvPolynomial.map (Int.castRingHom q.ResidueField)))
      (fun p => Ideal.Quotient.mk m (X p)) (fun p => by simp only [RingHom.comp_apply, map_X]) g
    exact h5.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 (hEm h2))

end LevelTowerAlt
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo PositivityTheory.HtPt GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace LevelTowerAlt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]

theorem ker_red_le {W : Ideal (MRing J)} (hpW : (C (p : ℤ) : MRing J) ∈ W) :
    RingHom.ker (Bridge.GeoNum.red (ι := J) p) ≤ W := by
  classical
  rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
  exact hpW

theorem map_red_prime [DecidableEq K] {W : Ideal (MRing J)} (hW : IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : MRing J) ∈ W) : NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) := by
  have hker := ker_red_le p hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2

theorem exists_curve_point {W : Ideal (MRing J)} (hW : IsMultiProjPrime W) (hpW : (C (p : ℤ) : MRing J) ∈ W)
    (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (ZMod p) L) (w : (Σ k, J k) → L) (c : ∀ k, J k),
      Algebra.trdeg (ZMod p) L = 1 ∧ (∀ k, w ⟨k, c k⟩ = 1) ∧ mCoordIdeal w = W := by
  classical
  obtain ⟨hQ, hQd⟩ := NefAddBlock.map_red p hW hpW 1 hdim
  have hcm := Bridge.GeoNum.comap_map_eq p (ker_red_le p hpW)
  set Q := W.map (Bridge.GeoNum.red p)
  have := hQ.isPrime
  obtain ⟨n, hn, hrn⟩ := FieldNumbers.FunctionFieldFinite.relDim_eq_trdeg FieldNumbers.MChartDehomog.proof
    (FieldNumbers.MChartTrdeg.proof FieldNumbers.MChartHomog.proof) Q hQ
  have hn1 : n = 1 := by
    rw [hQd] at hrn
    exact_mod_cast (WithTop.coe_injective (WithBot.coe_injective hrn)).symm
  choose c hc using hQ.relevant
  let π : NumbersDVR.MRing J (ZMod p) →+* FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q) :=
    (algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ g, π g = 0 ↔ g ∈ Q := fun g => by
    change algebraMap (NumbersDVR.MRing J (ZMod p) ⧸ Q) _ (Ideal.Quotient.mk Q g) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let y₀ : (Σ k, J k) → FractionRing (NumbersDVR.MRing J (ZMod p) ⧸ Q) := fun x => π (X x)
  have hy₀ := hom_eq_aeval (π.comp (Bridge.GeoNum.red p)) y₀ fun x => by simp only [RingHom.comp_apply, map_X, y₀]
  have hyc : ∀ k, y₀ ⟨k, c k⟩ ≠ 0 := fun k h => hc k ((hπ _).1 h)
  have hW₀ : mCoordIdeal y₀ = W := by
    refine le_antisymm (fun g hg => ?_) (le_mCoordIdeal hW.2.1 fun g hg => ?_)
    · rw [← hcm]
      exact (hπ _).1 ((hy₀ g).trans (aeval_zero_of_mem hg))
    · exact (hy₀ g).symm.trans ((hπ _).2 (Ideal.mem_map_of_mem _ hg))
  have hmem : ∀ x, ratioPt y₀ c x ∈ FieldNumbers.homFracDegZero Q := fun x =>
    IntermediateField.subset_adjoin _ _ ⟨_, X x, X ⟨x.1, c x.1⟩, isWeightedHomogeneous_X _ _ x,
      isWeightedHomogeneous_X _ _ (⟨x.1, c x.1⟩ : Σ k, J k), hc x.1, rfl⟩
  refine ⟨FieldNumbers.homFracDegZero Q, inferInstance, inferInstance, fun x => ⟨_, hmem x⟩, c,
    by rw [hn, hn1, Nat.cast_one], fun k => Subtype.ext (div_self (hyc k)), ?_⟩
  rw [← hW₀, mCoordIdeal_ratioPt y₀ c hyc]
  exact (mCoordIdeal_comp (FieldNumbers.homFracDegZero Q).val.toRingHom fun x => ⟨_, hmem x⟩).symm

theorem dim_le {L : Type} [Field L] [Algebra (ZMod p) L] (hL : Algebra.trdeg (ZMod p) L ≤ 1) (w : (Σ k, J k) → L) :
    (C (p : ℤ) : MRing J) ∈ mCoordIdeal w ∧ ∃ m : ℕ, m ≤ 1 + Fintype.card K ∧
      ringKrullDim (NumbersDVR.MRing J (ZMod p) ⧸ (mCoordIdeal w).map (Bridge.GeoNum.red p)) = m := by
  classical
  let Φ : NumbersDVR.MRing J (ZMod p) →ₐ[ZMod p] MvPolynomial K L := aeval fun x => C (w x) * X x.1
  have hΦ : ∀ g : MRing J, mConeMap w g = Φ (Bridge.GeoNum.red p g) := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add (f := _), hf, hg]
    | mul_X f x hf => simp only [map_mul, hf, map_X]; simp [mConeMap, Φ]
  have hcm : mCoordIdeal w = (RingHom.ker Φ).comap (Bridge.GeoNum.red p) := by
    ext g
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hΦ]
    rfl
  have hm : (mCoordIdeal w).map (Bridge.GeoNum.red p) = RingHom.ker Φ := by
    rw [hcm, Ideal.map_comap_of_surjective _ (Bridge.GeoNum.red_surjective p)]
  refine ⟨?_, ?_⟩
  · rw [hcm]
    refine Bridge.GeoNum.ker_le_comap p _ ?_
    rw [Bridge.GeoNum.ker_red]
    exact Ideal.mem_span_singleton_self _
  · rw [hm]
    have : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime _
    obtain ⟨m, h1, h2⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := ZMod p)
      (A := NumbersDVR.MRing J (ZMod p) ⧸ RingHom.ker Φ)
    refine ⟨m, ?_, h1⟩
    have h3 := trdeg_le_of_injective (Ideal.kerLiftAlg Φ) (Ideal.kerLiftAlg_injective Φ)
    rw [h2, ← trdeg_add_eq (ZMod p) L, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Cardinal.lift_natCast] at h3
    have h4 : (m : Cardinal) ≤ 1 + (Fintype.card K : Cardinal) := h3.trans (by gcongr)
    exact_mod_cast h4

end LevelTowerAlt
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial in
theorem LevelTowerAlt.nef_fibres_block_embedding : PB.Inputs → ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (a : K → ℤ) (a' : K' → ℤ), Function.Injective bk → (∀ k x, y' ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) → (∀ k, ∃ x, y' ⟨k, x⟩ ≠ 0) → (∀ k, a' (bk k) = a k) → (∀ k', k' ∉ Set.range bk → a' k' = 0) → NefOnFibres (mCoordIdeal y') a' → NefOnFibres (mCoordIdeal y) a := by
  classical
  intro _ Ω Ω' _ _ _ i K K' _ _ J J' _ _ y y' bk bx a a' hbk hy hy' ha ha' hnef W hW hle hchar hdim
  have hp : (charOf W).Prime := PB.prime_charOf_of_ne_zero hW.1 hchar
  have hpW := Inter.C_charOf_mem W
  generalize charOf W = p at hp hpW
  have : Fact p.Prime := ⟨hp⟩
  let v : (Σ k, J k) → Σ k, J' k := fun x => ⟨bk x.1, bx x.1 x.2⟩
  have hv : IsBlockMap bk v := by
    refine ⟨hbk, ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, x⟩ ⟨k₁, x₁⟩ h
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h
      obtain rfl := hbk h1
      obtain rfl := (bx k).injective (eq_of_heq h2)
      rfl
    · rintro ⟨_, x⟩ ⟨k, rfl⟩
      exact ⟨⟨k, (bx k).symm x⟩, by simp [v]⟩
  obtain ⟨L, _, _, w, c, hL, hc, hw⟩ := LevelTowerAlt.exists_curve_point p hW hpW hdim
  have hle' : mCoordIdeal (fun x : Σ k, J k => y' ⟨bk x.1, bx x.1 x.2⟩) ≤ mCoordIdeal w := by
    simp only [hy]
    rw [hw, CoordinateConeArithVar.mCoordIdeal_comp i y]
    exact hle
  obtain ⟨k₀, L₁, _, _, σ, _, _, w₀, w', h1, h2, h3, h4⟩ := LevelTowerAlt.exists_lift_blk y' bk bx hbk hy' w c hc hle'
  have : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
  have : CharP k₀ p := σ.charP σ.injective p
  have : CharP L₁ p := charP_of_injective_algebraMap (algebraMap k₀ L₁).injective p
  let _ : Algebra (ZMod p) k₀ := ZMod.algebra k₀ p
  let _ : Algebra (ZMod p) L₁ := ZMod.algebra L₁ p
  have : IsScalarTower (ZMod p) k₀ L₁ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hL₁ : Algebra.trdeg (ZMod p) L₁ ≤ 1 := by
    rw [← trdeg_add_eq (ZMod p) k₀, trdeg_eq_zero (R := k₀), add_zero, ← hL]
    exact trdeg_le_of_injective ⟨σ, fun r => RingHom.congr_fun
      (Subsingleton.elim (σ.comp (algebraMap (ZMod p) k₀)) (algebraMap (ZMod p) L)) r⟩ σ.injective
  obtain ⟨hpW', m, hm, hmd⟩ := LevelTowerAlt.dim_le p hL₁ w'
  choose c' hc' using h3
  have hW' : IsMultiProjPrime (mCoordIdeal w') := ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal w',
    CoordinateConeArithVar.relevant w' c' hc'⟩
  have himg : AI.I4.imageZ v (mCoordIdeal w') = W := by
    rw [← Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v hv, ← hw, ← funext h1,
      CoordinateConeArithVar.mCoordIdeal_comp σ w₀, ← CoordinateConeArithVar.mCoordIdeal_comp (algebraMap k₀ L₁) w₀]
    exact congrArg _ (funext h2)
  have hQ' := LevelTowerAlt.map_red_prime p hW' hpW'
  have hcm' := Bridge.GeoNum.comap_map_eq p (LevelTowerAlt.ker_red_le p hpW')
  have hcm := Bridge.GeoNum.comap_map_eq p (LevelTowerAlt.ker_red_le p hpW)
  set Q' := (mCoordIdeal w').map (Bridge.GeoNum.red p) with hQ'_def
  set Q := W.map (Bridge.GeoNum.red p) with hQ_def
  have hiv : imageVar (ZMod p) v Q' = Q := by
    ext f
    obtain ⟨g, rfl⟩ := Bridge.GeoNum.red_surjective p f
    change rename v (Bridge.GeoNum.red p g) ∈ Q' ↔ g ∈ Q.comap (Bridge.GeoNum.red p)
    rw [hcm, ← himg, Bridge.GeoNum.red, ← map_rename]
    change rename v g ∈ Q'.comap (Bridge.GeoNum.red p) ↔ _
    rw [hcm']
    rfl
  have hQd : ringKrullDim (MRingOver (ZMod p) J ⧸ Q) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p Q), hcm]
    exact hdim
  have hcd : FieldNumbers.relDim (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') =
      ((1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, ← Targets.ProjContract.ringKrullDim_imageVar hv, hiv]
    exact hQd
  have hge := FieldNumbers.ContractRelDimLe.proof (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q' hQ'
  have hrel : FieldNumbers.relDim Q' = ((((m : ℤ) - Fintype.card K' : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
    unfold FieldNumbers.relDim
    rw [hmd]
    rfl
  have hm' : m = 1 + Fintype.card K' := by
    rw [hcd, hrel] at hge
    have h5 : ((1 : ℕ) : ℤ) ≤ (m : ℤ) - Fintype.card K' :=
      WithTop.coe_le_coe.1 (WithBot.coe_le_coe.1 hge)
    omega
  subst hm'
  have hQ'd := (FieldNumbers.CutRegular.relDim_eq_natCast_iff Q' 1).2 hmd
  have hdim' : ringKrullDim (MRing J' ⧸ mCoordIdeal w') = ((1 + Fintype.card K' : ℕ) : WithBot ℕ∞) := by
    rw [← hcm', ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p Q')]
    exact hmd
  have h6 := hnef _ hW' h4 (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.charOf_ne_zero_of_mem hp.ne_zero (by simpa using hpW')) hdim'
  rw [← Bridge.intNum_map_eq_geoNum p 1 _ hW' hpW' hdim'] at h6
  rw [← Bridge.intNum_map_eq_geoNum p 1 _ hW hpW hdim]
  have := hQ'.isPrime
  have h7 := (GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q' hQ' 1
    hQ'd hcd fun _ => a).2
  have h8 := FieldNumbers.FunctionFieldFinite.proof FieldNumbers.MChartDehomog.proof
    (FieldNumbers.MChartTrdeg.proof FieldNumbers.MChartHomog.proof) (ZMod p) K K' (Targets.ProjContract.emb hv) J' Q'
    hQ' (hcd.trans hQ'd.symm)
  have h9 : FieldNumbers.pullDeg (Targets.ProjContract.emb hv) a = a' := by
    funext k'
    by_cases hk : k' ∈ Set.range bk
    · obtain ⟨k, rfl⟩ := hk
      rw [ha]
      exact hbk.extend_apply _ _ k
    · rw [ha' k' hk]
      exact Function.extend_apply' _ _ _ hk
  have h10 := FieldNumbers.RenameIntNum.full (ZMod p) K K J (fun k => J' (Targets.ProjContract.emb hv k))
    (Equiv.refl K) (Targets.ProjContract.blockEquiv hv)
    (fun x => hbk ((congrArg Sigma.fst (Targets.ProjContract.blockIncl_blockEquiv hv x))))
    (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') 1 fun _ => a
  have h11 : NumbersDVR.intNum (ZMod p) Q (fun _ : Fin 1 => a) =
      NumbersDVR.intNum (ZMod p) (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) Q') (fun _ : Fin 1 => a) := by
    rw [← hiv, Targets.ProjContract.imageVar_eq hv]
    exact h10
  rw [h9, ← h11] at h7
  change 0 ≤ NumbersDVR.intNum (ZMod p) Q' (fun _ : Fin 1 => a') at h6
  rw [h7] at h6
  exact nonneg_of_mul_nonneg_right h6 (by exact_mod_cast Nat.pos_of_ne_zero h8)
