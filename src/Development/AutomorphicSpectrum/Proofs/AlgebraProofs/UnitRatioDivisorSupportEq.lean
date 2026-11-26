module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MapFirstPower
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1

section Rel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_zero_of_mem_mCoordIdeal (y : (Σ k, ι k) → Ω) {h : MRing ι}
    (hh : h ∈ mCoordIdeal y) : aeval y h = 0 := by
  let φ : MvPolynomial K Ω →ₐ[ℤ] Ω :=
    (aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ
  have e : φ.comp (mConeMap y) = aeval y := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp [φ, mConeMap]
  have h0 : mConeMap y h = 0 := hh
  rw [← e, AlgHom.comp_apply, h0, map_zero]

theorem exists_monic_rel (y : (Σ k, ι k) → Ω) {f g : MRing ι} {d : K → ℕ} {θ : Ω}
    (hf : IsMultiHomog f d) (hg : IsMultiHomog g d) (hθ : IsIntegral ℤ θ)
    (he : aeval y f = θ * aeval y g) :
    ∃ (n : ℕ) (c : ℕ → MRing ι),
      1 * f ^ n + ∑ j ∈ Finset.range n, c j * f ^ j * g ^ (n - j) ∈ mCoordIdeal y := by
  classical
  obtain ⟨p, hpm, hp⟩ := hθ
  set n := p.natDegree
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp
  refine ⟨n, fun j => C (p.coeff j), ?_⟩
  rw [one_mul]
  refine LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y (d := n • d) ?_ ?_
  · refine LocalRep.isMultiHomog_add (SectionOrderAtPoint.isMultiHomog_pow' hf n)
      (SectionOrderAtPoint.isMultiHomog_sum' _ _ fun j hj => ?_)
    have h1 := LocalRep.isMultiHomog_mul (LocalRep.isMultiHomog_mul
      (LocalRep.isMultiHomog_C (ι := ι) (p.coeff j)) (SectionOrderAtPoint.isMultiHomog_pow' hf j))
      (SectionOrderAtPoint.isMultiHomog_pow' hg (n - j))
    convert h1 using 1
    have hj' : j ≤ n := (Finset.mem_range.mp hj).le
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, zero_add]
    rw [← add_mul, Nat.add_sub_cancel' hj']
  · have hsum : ∀ j ∈ Finset.range n,
        aeval y (C (p.coeff j) * f ^ j * g ^ (n - j)) =
          aeval y g ^ n * (algebraMap ℤ Ω (p.coeff j) * θ ^ j) := by
      intro j hj
      have hj' : j ≤ n := (Finset.mem_range.mp hj).le
      have e3 : aeval y g ^ n = aeval y g ^ j * aeval y g ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hj']
      simp only [map_mul, map_pow, aeval_C, he]
      rw [e3]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, Finset.sum_congr rfl hsum, ← Finset.mul_sum, map_pow, he, mul_pow]
    linear_combination (aeval y g ^ n) * hp

end Rel

theorem mem_minimalPrimes_of_rel {R : Type*} [CommRing R] [IsNoetherianRing R] {P W : Ideal R}
    (hP : P.IsPrime) {a b : R} (ha : a ∉ P) {n : ℕ} (c : ℕ → R)
    (hrel : 1 * a ^ n + ∑ j ∈ Finset.range n, c j * a ^ j * b ^ (n - j) ∈ P)
    (hW : W ∈ (P ⊔ Ideal.span {b}).minimalPrimes) : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hbW : b ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
  have h1 : (1 : R) ∉ W := (Ideal.ne_top_iff_one W).mp hWp.ne_top
  have haW : a ∈ W := SectionOrderAtPoint.mem_of_rel hWp hbW h1 c (hPW hrel)
  refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr haW)⟩, fun Q hQ hQW => ?_⟩
  exact (eq_of_le_of_mem_minimalPrimes hP hW hQ.1 (le_sup_left.trans hQ.2)
    (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))) ha hQW).ge

theorem divCycle_eq_of_unit_ratio : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (d : K → ℕ) (f g : MRing ι) (θ : Ω), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog f d → IsMultiHomog g d → aeval y g ≠ 0 → θ ≠ 0 → IsIntegral ℤ θ → IsIntegral ℤ θ⁻¹ → aeval y f = θ * aeval y g → divSupp (mCoordIdeal y) f = divSupp (mCoordIdeal y) g ∧ ∀ W ∈ divSupp (mCoordIdeal y) g, multAt ((mCoordIdeal y) ⊔ Ideal.span {f}) W = multAt ((mCoordIdeal y) ⊔ Ideal.span {g}) W := by
  intro K _ ι _ Ω _ y D d f g θ hV hf hg hgy hθ0 hθ hθi he
  have hP : (mCoordIdeal y).IsPrime := hV.2.1.1
  have hfy : aeval y f ≠ 0 := by
    rw [he]
    exact mul_ne_zero hθ0 hgy
  have hfP : f ∉ mCoordIdeal y := fun h => hfy (aeval_eq_zero_of_mem_mCoordIdeal y h)
  have hgP : g ∉ mCoordIdeal y := fun h => hgy (aeval_eq_zero_of_mem_mCoordIdeal y h)
  obtain ⟨n, c, hrel⟩ := exists_monic_rel y hf hg hθ he
  obtain ⟨m, c', hrel'⟩ := exists_monic_rel y hg hf hθi
    (by rw [he, ← mul_assoc, inv_mul_cancel₀ hθ0, one_mul])
  refine ⟨?_, ?_⟩
  · ext W
    exact ⟨fun h => ⟨mem_minimalPrimes_of_rel hP hgP c' hrel' h.1, h.2⟩,
      fun h => ⟨mem_minimalPrimes_of_rel hP hfP c hrel h.1, h.2⟩⟩
  · intro W hW
    have hWg := hW.1
    have hWf := mem_minimalPrimes_of_rel hP hfP c hrel hWg
    have hWp : W.IsPrime := hWg.1.1
    have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hWg.1.2
    have h1 : (1 : MRing ι) ∉ W := (Ideal.ne_top_iff_one W).mp hWp.ne_top
    let pW : PrimeSpectrum (MRing ι) := ⟨W, hWp⟩
    have hle1 := SectionOrderAtPoint.locLen_le_of_rel hP hfP hgP pW hPW h1 c hrel (locLen_ne_top hWg)
    have hle2 := SectionOrderAtPoint.locLen_le_of_rel hP hgP hfP pW hPW h1 c' hrel' (locLen_ne_top hWf)
    have := congrArg ENat.toNat (le_antisymm hle2 hle1)
    simpa [multAt, hWp, ReciprocityTheory.ChartRestriction.G.AI.locLen] using this

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEqStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_ratio_divisor_support_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (d : K → ℕ) (f g : MRing ι) (θ : Ω), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog f d → IsMultiHomog g d → aeval y g ≠ 0 → θ ≠ 0 → IsIntegral ℤ θ → IsIntegral ℤ θ⁻¹ → aeval y f = θ * aeval y g → divSupp (mCoordIdeal y) f = divSupp (mCoordIdeal y) g ∧ ∀ W ∈ divSupp (mCoordIdeal y) g, multAt ((mCoordIdeal y) ⊔ Ideal.span {f}) W = multAt ((mCoordIdeal y) ⊔ Ideal.span {g}) W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.divCycle_eq_of_unit_ratio | exact GlobalTheory.CompanionTheory.Ar.Giv.divCycle_eq_of_unit_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.divCycle_eq_of_unit_ratio <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalDataBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalDataBaseChange
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem map_mats_baseChange : ∀ (R R₂ : Type) [CommRing R] [CommRing R₂] (f : R →+* R₂) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R₂ d O), IsMapOf f B B₂ → (∀ a, rho B₂ a = (rho B a).map f ∧ bil (B₂.ad a) 1 1 = (bil (B.ad a) 1 1).map f) ∧ bil B₂.sy 1 1 = (bil B.sy 1 1).map f ∧ ∀ p, hw B₂ p = (hw B p).map f ∧ am B₂ p = (am B p).map f :=
  PositivityTheory.HtPt.Cc.map_mats

end GlobalTheory.CompanionTheory.Ar.Conj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalDataBaseChangeStatement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_data_base_change : ∀ (R R₂ : Type) [CommRing R] [CommRing R₂] (f : R →+* R₂) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R₂ d O), IsMapOf f B B₂ → (∀ a, rho B₂ a = (rho B a).map f ∧ bil (B₂.ad a) 1 1 = (bil (B.ad a) 1 1).map f) ∧ bil B₂.sy 1 1 = (bil B.sy 1 1).map f ∧ ∀ p, hw B₂ p = (hw B p).map f ∧ am B₂ p = (am B p).map f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.map_mats_baseChange | exact GlobalTheory.CompanionTheory.Ar.Conj.map_mats_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.map_mats_baseChange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FunctionFieldCurveExists
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.InhConj
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc


open GroundTheory.FunctionField in
def ffCurve (k K : Type) [Field k] [Field K] [Algebra k K] [IsFunctionField k K] : ACurve K where
  I := Place k K
  v := fun v => v.valuation
  w := fun v => v.deg
  fin := fun x hx => (Place.finite_ord_ne_zero (k := k) x).subset fun v hv h0 => hv (by
    rw [v.valuation_eq_exp_neg_ord hx, h0]; simp)
  prod := fun x _ => by
    have h := Divisor.deg_divisor (k := k) x
    rw [Divisor.deg_apply, Finsupp.sum] at h
    have e : ∀ v : Place k K, (v.deg : ℤ) * WithZero.log (v.valuation x) =
        -((divisor x : Divisor k K) v * v.deg) := fun v => by
      rw [divisor_apply, Place.ord]; ring
    simp only [e]
    rw [finsum_neg_distrib, finsum_eq_sum_of_support_subset (s := (divisor x : Divisor k K).support), h, neg_zero]
    intro v hv
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    exact fun h0 => hv (by simp only [h0, zero_mul])

private theorem place_nonempty_of_isFunctionField (k K : Type) [Field k] [Field K] [Algebra k K]
    [GroundTheory.FunctionField.IsFunctionField k K] : Nonempty (GroundTheory.FunctionField.Place k K) := by
  obtain ⟨t, ht, -⟩ := GroundTheory.FunctionField.IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hR : IsIntegrallyClosedIn (integralClosure k K).toSubring K := by infer_instance
  have htR : t ∉ (integralClosure k K).toSubring := fun h => ht (IsIntegral.isAlgebraic h)
  obtain ⟨V, hV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn htR
  exact ⟨⟨V, fun h => htV (h ▸ trivial), fun c => hV (isIntegral_algebraMap (x := c))⟩⟩

theorem inh_ff : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K], ∃ C : ACurve K, IsFFCurve k C ∧ Nonempty C.I ∧ ∀ i (x : K), IsAlgebraic k x → C.v i x ≤ 1 := by
  intro k K _ _ _ _
  refine ⟨ffCurve k K, ⟨Equiv.refl _, fun i => ⟨rfl, rfl⟩⟩, place_nonempty_of_isFunctionField k K, ?_⟩
  intro i x hx
  obtain ⟨v, rfl⟩ : ∃ v : GroundTheory.FunctionField.Place k K, v = i := ⟨i, rfl⟩
  show v.valuation x ≤ 1
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have hd := GroundTheory.FunctionField.divisor_eq_zero_of_isAlgebraic hx h0
    have ho : v.ord x = 0 := by
      have e := GroundTheory.FunctionField.divisor_apply (k := k) x v
      rw [hd] at e
      exact e.symm
    rw [v.valuation_eq_exp_neg_ord h0, ho]
    simp

end PositivityTheory.HtPt.Cc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FunctionFieldCurveExists
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.FF

theorem places_form_curve : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K], ∃ C : ACurve K, IsFFCurve k C ∧ Nonempty C.I ∧ ∀ i (x : K), IsAlgebraic k x → C.v i x ≤ 1 :=
  @PositivityTheory.HtPt.Cc.inh_ff

end GlobalTheory.CompanionTheory.Ar.FF
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FunctionFieldCurveExistsStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_curve_exists : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K], ∃ C : ACurve K, IsFFCurve k C ∧ Nonempty C.I ∧ ∀ i (x : K), IsAlgebraic k x → C.v i x ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FF.places_form_curve | exact GlobalTheory.CompanionTheory.Ar.FF.places_form_curve | (intros; apply GlobalTheory.CompanionTheory.Ar.FF.places_form_curve <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitCharactersUnramified
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitCharactersUnramified
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc

open Module

theorem injective_of_charZero (E : Type) [Field E] [NumberField E] {L : Type} [Field L] [CharZero L]
    (g : 𝓞 E →+* L) : Function.Injective g := by
  refine (injective_iff_map_eq_zero g).2 fun x hx => ?_
  by_contra h
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker g) h
    (RingHom.mem_ker.2 hx) (Algebra.IsIntegral.isIntegral x)
  apply hne
  rw [eq_bot_iff]
  intro n hn
  have h0 : g (algebraMap ℤ (𝓞 E) n) = 0 := RingHom.mem_ker.1 (Ideal.mem_comap.1 hn)
  have h1 : (n : L) = 0 := by simpa using h0
  simpa using h1

theorem det_sq_eq_discr (E : Type) [Field E] [NumberField E] (R S : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Fintype S] [DecidableEq S] (σ : S → (𝓞 E →+* R)) (hσ : Function.Injective σ)
    (hc : Fintype.card S = finrank ℚ E) (e : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ S) :
    (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).det ^ 2 = (NumberField.discr E : R) := by
  let F := FractionRing R
  let Ω := AlgebraicClosure F
  let i₀ : R →+* Ω := (algebraMap F Ω).comp (algebraMap R F)
  have hi₀ : Function.Injective i₀ :=
    (algebraMap F Ω).injective.comp (IsFractionRing.injective R F)
  have : CharZero Ω := charZero_of_injective_ringHom hi₀
  let ρ : S → (𝓞 E →+* Ω) := fun s => i₀.comp (σ s)
  have hρ : ∀ s, Function.Injective (ρ s) := fun s => injective_of_charZero E (ρ s)
  let τ : S → (E →ₐ[ℚ] Ω) := fun s => (IsFractionRing.lift (hρ s)).toRatAlgHom
  have hτ : ∀ s (a : 𝓞 E), τ s (algebraMap (𝓞 E) E a) = i₀ (σ s a) := fun s a => by
    change IsFractionRing.lift (hρ s) (algebraMap (𝓞 E) E a) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hinj : Function.Injective τ := by
    intro s t hst
    apply hσ
    ext a
    apply hi₀
    rw [← hτ, ← hτ, hst]
  have hbij : Function.Bijective τ :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by rw [AlgHom.card, hc]⟩
  let e' : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Ω) := e.trans (Equiv.ofBijective τ hbij)
  have key := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω (integralBasis E) e'
  rw [← coe_discr] at key
  have hm : Algebra.embeddingsMatrixReindex ℚ Ω (integralBasis E) e' =
      (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).map i₀ := by
    ext i j
    simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, integralBasis_apply]
    exact hτ _ _
  rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_pow] at key
  apply hi₀
  rw [← key]
  simp

theorem isSplit_of_det {O k S ι : Type} [CommRing O] [Field k] [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]
    (χ : S → (O →+* k)) (b : Basis ι ℤ O) (e : ι ≃ S)
    (h : (Matrix.of fun i j => χ (e j) (b i)).det ≠ 0) : IsSplit χ := by
  unfold IsSplit
  let B := Algebra.TensorProduct.basis k b
  let B' := (Pi.basisFun k S).reindex e.symm
  let f := (Algebra.TensorProduct.lift (Algebra.ofId k (S → k)) (AlgHom.pi fun s => (χ s).toIntAlgHom)
    (fun _ _ => Commute.all _ _))
  have hm : LinearMap.toMatrix B B' f.toLinearMap = (Matrix.of fun i j => χ (e j) (b i)).transpose := by
    ext i j
    simp [LinearMap.toMatrix_apply, B, B', f]
  have hu : IsUnit (LinearMap.toMatrix B B' f.toLinearMap).det := by
    rw [hm, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 h
  exact (LinearEquiv.ofIsUnitDet hu).bijective

theorem exists_isSplit (E : Type) [Field E] [NumberField E] (R K S : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Field K] [Fintype S] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (σ : S → (𝓞 E →+* R)) (π : R →+* K)
    (hσ : Function.Injective σ) (hc : Fintype.card S = finrank ℚ E) (hp : ¬ (p : ℤ) ∣ NumberField.discr E) :
    ∃ χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K), IsSplit χ ∧
      ∀ s a, ((χ s a : algebraicClosure (ZMod p) K) : K) = π (σ s a) := by
  classical
  have hchar : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hmem : ∀ s a, (π.comp (σ s)) a ∈ algebraicClosure (ZMod p) K := fun s a => by
    have h1 : IsIntegral ℤ ((π.comp (σ s)) a) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (π.comp (σ s)).toIntAlgHom
    exact mem_algebraicClosure_iff'.2 (h1.tower_top)
  let χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K) := fun s =>
    (π.comp (σ s)).codRestrict (algebraicClosure (ZMod p) K) (hmem s)
  refine ⟨χ, ?_, fun s a => rfl⟩
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card S := by
    rw [hc, finrank_eq_card_basis (integralBasis E)]
  let e : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ S := Fintype.equivOfCardEq hcard
  refine isSplit_of_det χ (RingOfIntegers.basis E) e fun h0 => hp ?_
  have hsq := congrArg π (det_sq_eq_discr E R S σ hσ hc e)
  have hmap : (algebraMap (algebraicClosure (ZMod p) K) K).mapMatrix
      (Matrix.of fun i j => χ (e j) (RingOfIntegers.basis E i)) =
      π.mapMatrix (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)) := by
    ext i j
    rfl
  have hdet : π (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).det = 0 := by
    rw [RingHom.map_det, ← hmap, ← RingHom.map_det]
    simp [h0]
  rw [map_pow, hdet] at hsq
  have hz : ((NumberField.discr E : ℤ) : K) = 0 := by
    simpa using hsq.symm
  exact (CharP.intCast_eq_zero_iff K p _).1 hz

end GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitCharactersUnramifiedStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_characters_unramified : ∀ (E : Type) [Field E] [NumberField E] (R K S : Type) [CommRing R] [IsDomain R] [CharZero R] [Field K] [Fintype S] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (σ : S → (𝓞 E →+* R)) (π : R →+* K), Function.Injective σ → Fintype.card S = Module.finrank ℚ E → ¬ (p : ℤ) ∣ NumberField.discr E → ∃ χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K), IsSplit χ ∧ ∀ s a, ((χ s a : algebraicClosure (ZMod p) K) : K) = π (σ s a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit | exact GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc.exists_isSplit <;> assumption)
end
end
