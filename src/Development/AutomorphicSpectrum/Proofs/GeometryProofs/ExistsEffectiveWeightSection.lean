module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefPolarization
public import Development.WeilBound.CoreStatements.CentralCharts.GapPolynomialPositive
public import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalReferenceGapPositive
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalReferenceGapPositive
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.global_reference_gap_positive : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ), (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → 0 < MvPolynomial.eval (fun a => (gapN ν a : ℝ)) A.Sys.degPoly := by
  first | exact @AnalyticReference.gap_polynomial_positive | exact AnalyticReference.gap_polynomial_positive
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalReferenceGapPositiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_reference_gap_positive : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ), (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → 0 < MvPolynomial.eval (fun a => (gapN ν a : ℝ)) A.Sys.degPoly := by
  first | exact @GlobalTheory.CompanionTheory.Relay.global_reference_gap_positive | exact GlobalTheory.CompanionTheory.Relay.global_reference_gap_positive | (intros; apply GlobalTheory.CompanionTheory.Relay.global_reference_gap_positive <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReferenceGeometryMultihomogForm
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReferenceGeometryMultihomogForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm

open MvPolynomial

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def bdeg (m : (Σ k, J k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩


open Classical in
def bcomp (g : MRing J) (d : K → ℕ) : MRing J :=
  ∑ m ∈ g.support.filter (fun m => bdeg m = d), monomial m (AddMonoidAlgebra.coeff g m)

open Classical in
theorem coeff_bcomp (g : MRing J) (d : K → ℕ) (m : (Σ k, J k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (bcomp g d) m = if bdeg m = d then AddMonoidAlgebra.coeff g m else 0 := by
  rw [bcomp, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_support_iff]
  by_cases h : bdeg m = d <;> by_cases h' : AddMonoidAlgebra.coeff g m = 0 <;> simp [h, h']

theorem bcomp_homog (g : MRing J) (d : K → ℕ) : IsMultiHomog (bcomp g d) d := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_bcomp] at hm
  have h : bdeg m = d := by
    by_contra h
    exact hm (if_neg h)
  exact congrFun h k

theorem sum_bcomp [DecidableEq (K → ℕ)] (g : MRing J) : ∑ d ∈ g.support.image bdeg, bcomp g d = g := by
  classical
  ext m
  rw [coeff_sum]
  by_cases h : AddMonoidAlgebra.coeff g m = 0
  · rw [h]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [coeff_bcomp]
    split_ifs
    · exact h
    · rfl
  · rw [Finset.sum_eq_single (bdeg m)]
    · rw [coeff_bcomp, if_pos rfl]
    · intro d _ hd
      rw [coeff_bcomp, if_neg (Ne.symm hd)]
    · intro hn
      exact absurd (Finset.mem_image_of_mem _ (mem_support_iff.2 h)) hn

theorem bcomp_eq_zero [DecidableEq (K → ℕ)] (g : MRing J) {d : K → ℕ} (h : d ∉ g.support.image bdeg) : bcomp g d = 0 := by
  classical
  ext m
  rw [coeff_bcomp, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with e
  · by_contra h0
    exact h (e ▸ Finset.mem_image_of_mem _ (mem_support_iff.2 h0))
  · rfl

theorem exists_aeval_bcomp_ne {Ω : Type} [Field Ω] (t : (Σ k, J k) → Ω) (g : MRing J) (h : aeval t g ≠ 0) :
    ∃ d : K → ℕ, aeval t (bcomp g d) ≠ 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_bcomp g, map_sum] at h
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨d, hd⟩

theorem aeval_bcomp_eq_zero (w : (Σ k, J k) → ℂ) (g : MRing J)
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → aeval (fun p => w p * c p.1) g = 0) (d : K → ℕ) :
    aeval w (bcomp g d) = 0 := by
  classical
  have h0 : mConeMap w g = 0 := by
    refine funext_set (fun _ => ({0}ᶜ : Set ℂ)) (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl) fun c hc => ?_
    rw [map_zero, GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.eval_mConeMap]
    exact h c fun k => hc k (Set.mem_univ k)
  have h1 : mConeMap w g = ∑ d' ∈ g.support.image bdeg, C (aeval w (bcomp g d')) * ∏ k, X k ^ d' k := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← sum_bcomp g, map_sum]
    exact Finset.sum_congr rfl fun d' _ =>
      GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mConeMap_eq_of_isMultiHomog w (bcomp_homog g d')
  have hm : ∀ d' : K → ℕ, (∏ k, (X k : MvPolynomial K ℂ) ^ d' k) = monomial (Finsupp.equivFunOnFinite.symm d') 1 := by
    intro d'
    rw [monomial_eq, C_1, _root_.one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  by_cases hd : d ∈ g.support.image bdeg
  · have h2 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm d)) (h1.symm.trans h0)
    rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h2
    simp only [hm, coeff_C_mul, coeff_monomial, mul_ite, _root_.mul_one, mul_zero, EmbeddingLike.apply_eq_iff_eq] at h2
    rwa [Finset.sum_ite_eq', if_pos hd] at h2
  · rw [bcomp_eq_zero g hd, map_zero]

theorem mem_chartLat {Ω : Type} [Field Ω] {y : (Σ k, J k) → Ω} {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g ∈ chartLat y (fun κ => (d κ : ℤ)) 1 := by
  intro c _
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (d k : ℤ))) = ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Nat.cast_one, _root_.one_mul, zpow_neg, zpow_natCast, inv_pow]
  rw [hprod, ← GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_scale hg y (fun k => (y ⟨k, c k⟩)⁻¹),
    chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  refine ⟨g, ?_⟩
  simp only [div_eq_mul_inv]
  rfl

theorem dehom_eq {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d)
    (c : ∀ k, J k) :
    aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((1 : ℕ) * (d k : ℤ))) = aeval (fun p => y p / y ⟨p.1, c p.1⟩) g := by
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (d k : ℤ))) = ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Nat.cast_one, _root_.one_mul, zpow_neg, zpow_natCast, inv_pow]
  rw [hprod, ← GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_scale hg y (fun k => (y ⟨k, c k⟩)⁻¹)]
  simp only [div_eq_mul_inv]

end Forms

theorem nonempty_hom_complex (k : Type) [Field k] [CharZero k] [Countable k] : Nonempty (k →+* ℂ) :=
  (GlobalTheory.nonempty_algHom_complex_of_countable ℤ k).map AlgHom.toRingHom

theorem exists_hom_ker {A : Type} [CommRing A] [Countable A] (P : Ideal A) [P.IsPrime]
    (hP : ∀ r : ℕ, r.Prime → (r : A) ∉ P) : ∃ ψ : A →+* ℂ, ∀ a, ψ a = 0 ↔ a ∈ P := by
  let B := A ⧸ P
  let F := FractionRing B
  have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
  have hB : Countable B := Quotient.countable
  have hF : Countable F := by
    refine Function.Surjective.countable (f := fun q : B × B => algebraMap B F q.1 / algebraMap B F q.2) ?_
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact ⟨(a, b), rfl⟩
  have hc : CharZero F := by
    obtain ⟨q, hq⟩ := CharP.exists F
    rcases CharP.char_is_prime_or_zero F q with h | h
    · exfalso
      refine hP q h ?_
      have h1 : algebraMap B F (q : B) = 0 := by
        rw [map_natCast]
        exact (CharP.cast_eq_zero_iff F q q).2 dvd_rfl
      have h2 : (q : B) = 0 := hinj (h1.trans (map_zero _).symm)
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact h2
    · subst h
      exact CharP.charP_to_charZero F
  obtain ⟨j⟩ := nonempty_hom_complex F
  refine ⟨j.comp ((algebraMap B F).comp (Ideal.Quotient.mk P)), fun a => ?_⟩
  simp only [RingHom.comp_apply]
  rw [map_eq_zero_iff _ j.injective, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]

section Points

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem coordsAt_scale {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w : (Σ k, J k) → ℂ} (h : CoordsAt ξ y z w) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    CoordsAt ξ y z (fun p => w p * c p.1) := by
  refine ⟨fun k => (h.1 k).imp fun i hi => hi.mul (Ne.isUnit (hc k)), fun k i hu => ?_⟩
  have hu' : IsUnit (w ⟨k, i⟩) := Ne.isUnit (left_ne_zero_of_mul hu.ne_zero)
  obtain ⟨h0, h1⟩ := h.2 k i hu'
  refine ⟨h0, fun j => ?_⟩
  obtain ⟨r, hr, e⟩ := h1 j
  refine ⟨r, hr, ?_⟩
  show w ⟨k, j⟩ * c k = r * (w ⟨k, i⟩ * c k)
  rw [e, _root_.mul_assoc]

theorem isUnit_stalk_iff (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(u.isUnit.map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1),
      map_units_inv (genMap ξ p) u⟩⟩
  · rintro ⟨h0, -, t, ht⟩
    refine isUnit_iff_exists_inv.2 ⟨t, hξ.inj p ?_⟩
    rw [map_mul, ht, mul_inv_cancel₀ h0, map_one]

theorem isUnit_stalk_point {z : Spec (CommRingCat.of ℂ) ⟶ X} (s : X.presheaf.stalk (centre z)) :
    IsUnit s ↔ (Scheme.stalkClosedPointTo z).hom s ≠ 0 :=
  ⟨fun h => (h.map (Scheme.stalkClosedPointTo z).hom).ne_zero, fun h =>
    (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.mpr h)⟩

theorem centre_eq_of_ker {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (p : Cpt ξ)
    (hp : InChart ξ x c p) (ψ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* ℂ)
    (hψ : ∀ a, ψ a = 0 ↔ ¬ unitAt ξ p (a : Ω)) {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z)
    (hval : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), ValAt ξ z (a : Ω) (ψ a)) : centre z = p.1 := by
  obtain ⟨U, hU, hmem⟩ := T.affine c hc
  have hpU : p.1 ∈ U := (hmem _).2 ⟨p.2, hp⟩
  have hzU : centre z ∈ U := by
    refine (hmem _).2 ⟨hz, hc, fun j => ?_⟩
    obtain ⟨h, s, e, -⟩ := hval ⟨x j / x c, Algebra.subset_adjoin ⟨j, rfl⟩⟩
    exact ⟨s, e⟩
  have hg : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let q : Cpt ξ := ⟨centre z, hz⟩
  have key : ∀ f : Γ(X, U), p.1 ∈ X.basicOpen f ↔ centre z ∈ X.basicOpen f := by
    intro f
    have e1 := SheetDecomposition.CovSch.genMap_germ' p U hpU hg f
    have e2 := SheetDecomposition.CovSch.genMap_germ' q U hzU hg f
    have ha : SheetDecomposition.CovSch.val ξ U hg f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
      (T.ring c hc _).2 fun r hr => ⟨_, SheetDecomposition.CovSch.genMap_germ' r U ((hmem _).2 ⟨r.2, hr⟩) hg f⟩
    obtain ⟨h, s, e3, e4⟩ := hval ⟨_, ha⟩
    have hs : s = X.presheaf.germ U (centre z) hzU f := T.gen.inj q (e3.trans e2.symm)
    rw [Scheme.mem_basicOpen _ f _ hpU, Scheme.mem_basicOpen _ f _ hzU, isUnit_stalk_iff T.gen p, e1, ← hs,
      isUnit_stalk_point, e4, ne_eq, hψ, not_not]
  have hP : ∀ (t : U) (f : Γ(X, U)), f ∉ (hU.primeIdealOf t).asIdeal ↔ t.1 ∈ X.basicOpen f := by
    intro t f
    have h1 : hU.fromSpec (hU.primeIdealOf t) = t.1 := hU.fromSpec_primeIdealOf t
    have h2 : hU.primeIdealOf t ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ t.1 ∈ X.basicOpen f := by
      rw [← h1]
      rfl
    rw [hU.fromSpec_preimage_basicOpen f] at h2
    exact h2
  have hEq : hU.primeIdealOf ⟨p.1, hpU⟩ = hU.primeIdealOf ⟨centre z, hzU⟩ := by
    refine PrimeSpectrum.ext (Ideal.ext fun f => ?_)
    have h1 := hP ⟨p.1, hpU⟩ f
    have h2 := hP ⟨centre z, hzU⟩ f
    exact not_iff_not.1 (h1.trans ((key f).trans h2.symm))
  have h1 : hU.fromSpec (hU.primeIdealOf ⟨p.1, hpU⟩) = p.1 := hU.fromSpec_primeIdealOf ⟨p.1, hpU⟩
  have h2 : hU.fromSpec (hU.primeIdealOf ⟨centre z, hzU⟩) = centre z := hU.fromSpec_primeIdealOf ⟨centre z, hzU⟩
  rw [← h2, ← hEq, h1]

theorem exists_point_at {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (cc : ∀ k, J k) (p : Cpt ξ)
    (hp : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc p)
    (hchar : ∀ r : ℕ, r.Prime → unitAt ξ p (r : Ω)) :
    ∃ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), centre z = p.1 ∧ CoordsAt ξ y z w ∧
      ∀ g : MRing J, unitAt ξ p (aeval (fun s => y s / y ⟨s.1, cc s.1⟩) g) → aeval w g ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : ((k : K) → J k) → Ω, x = fun c' => ∏ k, y ⟨k, c' k⟩ := ⟨_, rfl⟩
  rw [← hx] at T hp
  have hc : x cc ≠ 0 := hp.1
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => by
    rw [hx] at hc
    exact (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ k)
  have hreg : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x cc), (a : Ω) ∈ regAt ξ p :=
    fun a => (T.ring cc hc a).1 a.2 p hp
  let inc : Algebra.adjoin ℤ (Set.range fun j => x j / x cc) →+* regAt ξ p :=
    { toFun := fun a => ⟨a, hreg a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  haveI : IsLocalRing (regAt ξ p) := GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt X Ω ξ T.gen p
  let P : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) := (IsLocalRing.maximalIdeal (regAt ξ p)).comap inc
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hPmem : ∀ a, a ∈ P ↔ ¬ unitAt ξ p (a : Ω) := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
      have hb' : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hb'
      exact ⟨h0, hreg a, by rw [inv_eq_of_mul_eq_one_right hb']; exact b.2⟩
    · rintro ⟨h0, -, h2⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  have hcount : Countable (Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) := by
    have hcm : Countable (MvPolynomial ((k : K) → J k) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      refine MvPolynomial.cardinalMk_le_max.trans ?_
      first
        | exact max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl
        | exact max_le (max_le (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0) (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0)) le_rfl
    have hs : (((Algebra.adjoin ℤ (Set.range fun j => x j / x cc) : Subalgebra ℤ Ω)) : Set Ω).Countable := by
      rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.coe_range]
      exact Set.countable_range _
    exact hs.to_subtype
  have hP : ∀ r : ℕ, r.Prime → (r : Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) ∉ P := by
    intro r hr h
    refine (hPmem _).1 h ?_
    have := hchar r hr
    simpa using this
  obtain ⟨ψ, hψ⟩ := exists_hom_ker P hP
  obtain ⟨z, hz, hval⟩ := SheetDecomposition.ChartForm.exists_point_hom T cc hc ψ
  have htA : ∀ s : Σ k, J k, y s / y ⟨s.1, cc s.1⟩ ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x cc) := by
    rintro ⟨k, i⟩
    have h1 : y ⟨k, i⟩ / y ⟨k, cc k⟩ = x (Function.update cc k i) / x cc := by
      rw [hx]
      exact (GlobalTheory.CompanionTheory.Ar.TiePoints.ratio_update y cc hy k i).symm
    rw [h1]
    exact Algebra.subset_adjoin ⟨_, rfl⟩
  let t' : (Σ k, J k) → Algebra.adjoin ℤ (Set.range fun j => x j / x cc) := fun s => ⟨_, htA s⟩
  refine ⟨z, fun s => ψ (t' s), centre_eq_of_ker T cc hc p hp ψ (fun a => (hψ a).trans (hPmem a)) hz hval,
    SheetDecomposition.CovSch.coordsAt_of_val cc hy (fun s => hval (t' s)) (fun k => ?_), fun g hg h0 => ?_⟩
  · have : t' ⟨k, cc k⟩ = 1 := Subtype.ext (div_self (hy k))
    rw [this, map_one]
  · have e1 : aeval (fun s => ψ (t' s)) g = ψ (aeval t' g) :=
      (GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.ringHom_aeval ψ t' g).symm
    have e2 : ((aeval t' g : Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) : Ω) =
        aeval (fun s => y s / y ⟨s.1, cc s.1⟩) g :=
      GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.ringHom_aeval (Algebra.adjoin ℤ (Set.range fun j => x j / x cc)).val.toRingHom t' g
    rw [e1] at h0
    refine (hψ _).1 h0 |> (hPmem _).1 <| ?_
    rw [e2]
    exact hg

end Points

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β₀ : O →+* c.F} {Y : Model Xo c β₀}

theorem exists_chart_form (G : RefGeo Y) : ∃ (c : ∀ k, G.J k) (g : MRing G.J), g ∈ G.bd ∧ (∀ k, G.y ⟨k, c k⟩ ≠ 0) ∧
    aeval (fun p => G.y p / G.y ⟨p.1, c p.1⟩) g ≠ 0 := by
  obtain ⟨c, hc⟩ := G.𝔐.tie.cover ⟨genPt G.𝔐.ξ, specializes_rfl⟩
  have hy : ∀ k, G.y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc.1) k (Finset.mem_univ k)
  by_contra hno
  have hz : ∀ g ∈ G.bd, aeval (fun p => G.y p / G.y ⟨p.1, c p.1⟩) g = 0 := by
    intro g hg
    by_contra h
    exact hno ⟨c, g, hg, hy, h⟩
  obtain ⟨m, f, a, -, -, hsum, hS⟩ := G.snc c hy
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  obtain ⟨-, z, n, -, hli, -, hq⟩ := hS l hl _ rfl
  obtain ⟨i, -, hi⟩ := (hq ⊥ Ideal.isPrime_bot).1 fun g hg s hs =>
    Ideal.mem_bot.2 (Subtype.ext (hs.trans (hz g hg)))
  have h1 := hli.ne_zero i
  rw [Ideal.mem_bot.1 hi, map_zero] at h1
  exact h1 rfl

end Main

theorem bd_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β₀ : O →+* c.F) (Y : Model Xo c β₀) (G : RefGeo Y), ∃ (β : MRing G.J) (dβ : G.K → ℕ), IsMultiHomog β dβ ∧ β ∉ mCoordIdeal G.y ∧ MvPolynomial.aeval G.y β ≠ 0 ∧ MvPolynomial.aeval G.y β ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1 ∧ ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G → ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p → ¬ unitAt G.𝔐.ξ p (MvPolynomial.aeval G.y β * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ)))) := by
  intro E _ _ _ H D l Xo c O _ β₀ Y G
  obtain ⟨c₀, g, hg, hy, hne⟩ := exists_chart_form G
  obtain ⟨d, hd⟩ := exists_aeval_bcomp_ne _ g hne
  have hhom := bcomp_homog g d
  have hyne : aeval G.y (bcomp g d) ≠ 0 := by
    intro h0
    rw [← dehom_eq G.y hhom c₀, h0, zero_mul] at hd
    exact hd rfl
  refine ⟨bcomp g d, d, hhom, fun hm => hyne ?_, hyne, mem_chartLat hhom, fun p hchar hab cc hp hu => ?_⟩
  · have h1 := GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_eq_zero_of_mem hm (fun _ => 1)
    simpa using h1
  · rw [dehom_eq G.y hhom cc] at hu
    obtain ⟨z, w, hcen, hco, hval⟩ := exists_point_at G.𝔐.tie cc p hp (fun r hr => not_not.1 (hchar r hr))
    refine hval _ hu (aeval_bcomp_eq_zero w g (fun t ht => ?_) d)
    have hnot : ¬ G.𝔐.Interior z := fun hi => hab (hcen ▸ hi)
    have h1 := (G.bd_iff z _ (coordsAt_scale hco ht)).2 hnot
    have h2 := h1.2 g hg
    rwa [MvPolynomial.eval_map] at h2

end GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReferenceGeometryMultihomogFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reference_geometry_multihomog_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β₀ : O →+* c.F) (Y : Model Xo c β₀) (G : RefGeo Y), ∃ (β : MRing G.J) (dβ : G.K → ℕ), IsMultiHomog β dβ ∧ β ∉ mCoordIdeal G.y ∧ MvPolynomial.aeval G.y β ≠ 0 ∧ MvPolynomial.aeval G.y β ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1 ∧ ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G → ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p → ¬ unitAt G.𝔐.ξ p (MvPolynomial.aeval G.y β * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form | exact GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form | (intros; apply GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEffectiveWeightSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.ExRefEff

theorem tele (F : ℕ → ℤ) (k M : ℕ) (hk : k ≤ M) :
    ∑ n ∈ Finset.range M, (if k ≤ n then F n - F (n + 1) else 0) = F k - F M := by
  induction M, hk using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro n hn
      rw [if_neg (by simpa using hn)]
  | succ M hM ih =>
    rw [Finset.sum_range_succ, ih, if_pos hM]
    ring

theorem abel (N : ℕ) (f x : Fin N → ℤ) :
    ∑ i : Fin N, (f i - if h : (i : ℕ) + 1 < N then f ⟨i + 1, h⟩ else 0) * ∑ k ∈ Finset.Iic i, x k =
      ∑ k, f k * x k := by
  classical
  let F : ℕ → ℤ := fun n => if h : n < N then f ⟨n, h⟩ else 0
  have hF : ∀ i : Fin N, (f i - if h : (i : ℕ) + 1 < N then f ⟨i + 1, h⟩ else 0) = F i - F (i + 1) := by
    intro i
    simp [F, i.2]
  have hFN : F N = 0 := by simp [F]
  have h1 : ∀ k : Fin N, ∑ i ∈ Finset.Ici k, (F i - F (i + 1)) = f k := by
    intro k
    have h2 := tele F k N k.2.le
    rw [hFN, sub_zero, ← Fin.sum_univ_eq_sum_range (fun n => if (k : ℕ) ≤ n then F n - F (n + 1) else 0) N] at h2
    have h3 : Finset.Ici k = Finset.univ.filter (fun i => k ≤ i) := by ext i; simp
    rw [h3, Finset.sum_filter]
    simp only [Fin.le_def]
    rw [h2]
    simp [F, k.2]
  simp_rw [hF, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun k => Finset.Ici k) (by intro i k; simp)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, h1]

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
  {J : K → Type} {y : (Σ k, J k) → Ω}

theorem ne_of_chart {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 :=
  (Finset.prod_ne_zero_iff.1 h.1) k (Finset.mem_univ k)

theorem ratio_mem {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    (k : K) (i : J k) : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h1 := h.2 (Function.update c k i)
  have h2 : (∏ l, y ⟨l, Function.update c k i l⟩) / ∏ l, y ⟨l, c l⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro l _ hl
      rw [Function.update_of_ne hl, div_self (ne_of_chart h l)]
    · simp
  rwa [h2] at h1

theorem chart_update {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    [DecidableEq K] (k₀ : K) (i : J k₀) (hi : InChart ξ (fun i' : J k₀ => y ⟨k₀, i'⟩) i p) :
    InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) (Function.update c k₀ i) p := by
  have hne : ∀ k, y ⟨k, Function.update c k₀ i k⟩ ≠ 0 := by
    intro k
    by_cases hk : k = k₀
    · subst hk
      simpa using hi.1
    · rw [Function.update_of_ne hk]
      exact ne_of_chart h k
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hne k, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, Function.update c k₀ i k⟩ ∈ regAt ξ p
  rw [← Finset.prod_div_distrib]
  refine Subring.prod_mem _ fun k _ => ?_
  by_cases hk : k = k₀
  · subst hk
    simpa using hi.2 (c' k)
  · rw [Function.update_of_ne hk]
    exact ratio_mem h k (c' k)

theorem chartRing_mem {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    {a : Ω} (ha : a ∈ chartRingZ y c) : a ∈ regAt ξ p := by
  unfold chartRingZ at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    exact ratio_mem h q.1 q.2
  | algebraMap r => simpa using intCast_mem (regAt ξ p) r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

end Chart

section Ref

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β₀ : O →+* c.F} {Y : Model Xo c β₀}

theorem comb_a {G : RefGeo Y} (A : G.An) (ν : RootIx D → ℤ) (κ : G.K) :
    (PB.combLine A.Re.ref (gapN ν)).a κ = -∑ r, ν r * G.xdeg r κ := by
  rw [PB.combLine_a, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  simp only [gapN, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := abel (D.p + D.q) (fun i => ν (τ, i)) (fun k => G.xdeg (τ, k) κ)
  rw [← h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [A.fund_deg τ i]
  simp [Finset.sum_apply]


open Classical in
theorem isEff_of_data (G : RefGeo Y) (n : RootIx D → ℤ) (e : G.Ω) (b : G.Ω) (dβ : G.K → ℕ)
    (i₀ : ∀ k, G.J k) (hi₀ : ∀ k, G.y ⟨k, i₀ k⟩ ≠ 0)
    (he : e ∈ chartLat G.y (fun κ => (∑ r, (-n r) • G.xdeg r) κ - 1 - dβ κ) 1)
    (hb : b ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1)
    (hbd : ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G →
      ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p →
        ¬ unitAt G.𝔐.ξ p (b * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ))))) :
    G.IsEff n 1 (e * b * (∏ κ ∈ Finset.univ.erase G.k₀, G.y ⟨κ, i₀ κ⟩) * ∏ r, G.e r ^ (-n r)) := by
  classical
  have hDeg := GlobalTheory.T.lattice_tensor_power_degree _ _ G.𝔐.ξ G.K G.J G.y _ G.Fl.rootLat Set.univ G.xdeg G.e G.lines (fun r => -n r)
  intro p hp i t hi ht
  obtain ⟨c0, hc0⟩ := G.𝔐.tie.cover p
  have hc := chart_update hc0 G.k₀ i hi
  set cc := Function.update c0 G.k₀ i with hcc
  have hcck : cc G.k₀ = i := by simp [hcc]
  have hne := ne_of_chart hc
  have hgen := hDeg.2 p (Set.mem_univ _) cc hc
  set a : G.K → ℤ := ∑ r, (-n r) • G.xdeg r with ha
  set E₀ : G.Ω := ∏ r, G.e r ^ (-n r) with hE₀
  have hE₀0 : E₀ ≠ 0 := hDeg.1
  set Pa : G.Ω := ∏ k, G.y ⟨k, cc k⟩ ^ a k with hPa
  have hPa0 : Pa ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)
  have hsp : (Lat.tens G.Fl.rootLat fun r => -n r) p = Submodule.span (regAt G.𝔐.ξ p) {Pa * E₀} := by
    rw [hgen, smul_eq_mul]
  have hg0 : Pa * E₀ ≠ 0 := mul_ne_zero hPa0 hE₀0
  obtain ⟨ht0, htp⟩ := ht
  have hgt : Pa * E₀ ∈ Submodule.span (regAt G.𝔐.ξ p) {t} := by
    rw [← htp, hsp]; exact Submodule.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 hgt
  have hv' : (v : G.Ω) * t = Pa * E₀ := hv
  have hv0 : (v : G.Ω) ≠ 0 := fun h => hg0 (by rw [← hv', h, zero_mul])
  have hvm : (v : G.Ω) ∈ regAt G.𝔐.ξ p := v.2
  have hW := chartRing_mem hc (he cc hne)
  have hB := chartRing_mem hc (hb cc hne)
  set Q1 : G.Ω := ∏ k, G.y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * (a k - 1 - dβ k))) with hQ1
  set Q2 : G.Ω := ∏ k, G.y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * (dβ k : ℤ))) with hQ2
  set M : G.Ω := ∏ κ ∈ Finset.univ.erase G.k₀, G.y ⟨κ, i₀ κ⟩ with hM
  set Ec : G.Ω := ∏ κ ∈ Finset.univ.erase G.k₀, G.y ⟨κ, cc κ⟩ with hEc
  have hEc0 : Ec ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hne k
  have hMc : M / Ec ∈ regAt G.𝔐.ξ p := by
    rw [hM, hEc, ← Finset.prod_div_distrib]
    exact Subring.prod_mem _ fun k _ => ratio_mem hc k (i₀ k)
  have hP : Q1 * Q2 * Pa = G.y ⟨G.k₀, i⟩ * Ec := by
    have h1 : G.y ⟨G.k₀, i⟩ * Ec = ∏ k, G.y ⟨k, cc k⟩ := by
      rw [hEc, ← Finset.mul_prod_erase Finset.univ (fun k => G.y ⟨k, cc k⟩) (Finset.mem_univ G.k₀), hcck]
    rw [h1, hQ1, hQ2, hPa, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hne k), ← zpow_add₀ (hne k)]
    have : -(((1 : ℕ) : ℤ) * (a k - 1 - dβ k)) + -(((1 : ℕ) : ℤ) * (dβ k : ℤ)) + a k = 1 := by
      push_cast; ring
    rw [this, zpow_one]
  have hX : e * b * M * E₀ * G.y ⟨G.k₀, i⟩ ^ 1 / t =
      (v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)) := by
    have ht' : t = Pa * E₀ / v := by field_simp; rw [mul_comm]; exact hv'
    have hq : Q1 * Q2 = G.y ⟨G.k₀, i⟩ * Ec / Pa := by field_simp; exact hP
    have : (e * Q1) * (b * Q2) * (M / Ec) = e * b * (Q1 * Q2) * (M / Ec) := by ring
    rw [this, hq, ht']
    field_simp
  rw [hX]
  refine ⟨mul_mem hvm (mul_mem (mul_mem hW hB) hMc), fun hab hu => ?_⟩
  refine hbd p hp hab cc hc ⟨?_, hB, ?_⟩
  · intro h0
    apply hu.1
    rw [h0]; simp
  · have hb0 : b * Q2 ≠ 0 := fun h0 => hu.1 (by rw [h0]; simp)
    have : (b * Q2)⁻¹ = ((v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)))⁻¹ * ((v : G.Ω) * (e * Q1) * (M / Ec)) := by
      have hx := hu.1
      have hx1 : (v : G.Ω) * (e * Q1) * (M / Ec) ≠ 0 := by
        intro h0
        apply hx
        have : (v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)) = ((v : G.Ω) * (e * Q1) * (M / Ec)) * (b * Q2) := by ring
        rw [this, h0, zero_mul]
      have : (v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)) = ((v : G.Ω) * (e * Q1) * (M / Ec)) * (b * Q2) := by ring
      have key : ∀ w z : G.Ω, w ≠ 0 → z ≠ 0 → z⁻¹ = (w * z)⁻¹ * w := by
        intro w z hw hz
        field_simp
      rw [this]
      exact key _ _ hx1 hb0
    rw [this]
    exact mul_mem hu.2.2 (mul_mem (mul_mem hvm hW) hMc)

end Ref

theorem exists_eff : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y), Nonempty G.An → ∀ ν : RootIx D → ℤ, (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → ∃ (k q' : ℕ) (s : G.Ω), 0 < k ∧ 0 < q' ∧ s ≠ 0 ∧ G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s := by
  intro hG E _ _ _ H D Xo l c Y hgl hp hq G ⟨A⟩ ν hν
  classical
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  haveI : Nonempty G.K := ⟨G.k₀⟩
  have hb : Birational G.y := (GlobalTheory.T.hodge_cpt_birational_arith_var E H D l (Xo l) c (𝓞 c.F) (algebraMap _ _) Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl
    (RingOfIntegers.coe_injective)).1
  obtain ⟨β, dβ, hβ, hβP, hb0, hβc, hbd⟩ := GlobalTheory.T.reference_geometry_multihomog_form E H D l (Xo l) c _ _ Y G
  let Fl : Set (Option (RootIx D)) := {a | ∃ (τ : CMType H) (i : Fin (D.p + D.q)), (i : ℕ) + 1 = D.p + D.q ∧ a = some (τ, i)}
  have hFl : ∀ a ∈ Fl, ∀ t, ReciprocityTheory.AnForm.M.IsPsh A.Sys.A ((A.Sys.potT a t).rsmul (-1)) ∧
      ReciprocityTheory.AnForm.M.IsPsh A.Sys.A (A.Sys.potT a t) := by
    rintro _ ⟨τ, i, hi, rfl⟩ t
    exact A.flat τ i hi t
  have hn : ∀ a ∉ Fl, 0 ≤ gapN ν a := by
    intro a ha
    cases a with
    | none => simp [gapN]
    | some r =>
      obtain ⟨τ, i⟩ := r
      have hi : (i : ℕ) + 1 < D.p + D.q := by
        by_contra h
        exact ha ⟨τ, i, by have := i.2; omega, rfl⟩
      have := hν τ i ⟨i + 1, hi⟩ (by simp [Fin.lt_def])
      simp only [gapN, dif_pos hi]
      omega
  obtain ⟨-, h2⟩ := GlobalTheory.T.nef_polarization hIn _ _ A.Sys Fl hFl G.K G.J G.Ω G.y A.Re A.J_top hb
    (fun V _ L => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ V L) (GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ G.K G.J) (gapN ν) hn
  obtain ⟨k, hk, e, he, he0⟩ := h2 (GlobalTheory.T.global_reference_gap_positive hG E H D Xo l c Y hgl hp hq G A ν hν) β dβ hβ hβP
  have hne0 : ∀ κ, ∃ i, G.y ⟨κ, i⟩ ≠ 0 := by
    obtain ⟨c0, hc0⟩ := G.𝔐.tie.cover ⟨genPt G.𝔐.ξ, specializes_rfl⟩
    exact fun κ => ⟨c0 κ, ne_of_chart hc0 κ⟩
  choose i₀ hi₀ using hne0
  set n : RootIx D → ℤ := fun r => ((k * 1 : ℕ) : ℤ) * ν r with hn'
  have hdeg : ∀ κ, (∑ r, (-n r) • G.xdeg r) κ = (k : ℤ) * (PB.combLine A.Re.ref (gapN ν)).a κ := by
    intro κ
    rw [comb_a, Finset.sum_apply, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [hn']
    ring
  have he' : e ∈ chartLat G.y (fun κ => (∑ r, (-n r) • G.xdeg r) κ - 1 - dβ κ) 1 := by
    have : (fun κ => (∑ r, (-n r) • G.xdeg r) κ - 1 - (dβ κ : ℤ)) =
        fun κ => (k : ℤ) * (PB.combLine A.Re.ref (gapN ν)).a κ - 1 - dβ κ := by
      funext κ
      rw [hdeg]
    rw [this]
    exact he
  refine ⟨k, 1, _, by omega, one_pos, ?_, isEff_of_data G n e _ dβ i₀ hi₀ he' hβc hbd⟩
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero he0 hb0) (Finset.prod_ne_zero_iff.2 fun κ _ => hi₀ κ)) ?_
  have hDeg := GlobalTheory.T.lattice_tensor_power_degree _ _ G.𝔐.ξ G.K G.J G.y _ G.Fl.rootLat Set.univ G.xdeg G.e G.lines (fun r => -n r)
  exact hDeg.1

end GlobalTheory.CompanionTheory.Ar.ExRefEff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEffectiveWeightSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_effective_weight_section : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y), Nonempty G.An → ∀ ν : RootIx D → ℤ, (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → ∃ (k q' : ℕ) (s : G.Ω), 0 < k ∧ 0 < q' ∧ s ≠ 0 ∧ G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff | exact GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff | (intros; apply GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff <;> assumption)
end
