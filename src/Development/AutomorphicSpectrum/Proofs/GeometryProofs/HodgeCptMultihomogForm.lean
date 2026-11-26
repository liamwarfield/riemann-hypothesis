module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilLocal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLogPeriodFamily
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FunctionFamilyChartFacts

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogForm
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogForm
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.HInterior

open GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section Noeth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {κ : Type} [Finite κ]

theorem isNoetherianRing_chart (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (hT : CoordTie ℤ ξ x) (c : κ)
    (hc : x c ≠ 0) (U : X.Opens) (hU : IsAffineOpen U)
    (hUm : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (hη : genPt ξ ∈ U) :
    IsNoetherianRing Γ(X, U) := by
  have sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hUm q).1 hq).1
  let A : Subalgebra ℤ Ω := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  have hreg : ∀ a : Ω, a ∈ A ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    refine (hT.ring c hc a).trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  let ρ : Γ(X, U) →+* A := (ev ξ U hη).codRestrict A
    fun s => (hreg _).2 fun q hq => ⟨_, genMap_germ hη q hq s⟩
  have hinj : Function.Injective ρ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs
    have h0 : ev ξ U hη s = 0 := congrArg Subtype.val hs
    refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun q hq => ?_
    apply hT.gen.inj ⟨q, sp q hq⟩
    have h1 := genMap_germ hη ⟨q, sp q hq⟩ hq s
    rw [h0] at h1
    refine h1.trans ?_
    simp only [map_zero]
  have hsurj : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ := exists_ev_eq hU hη sp a ((hreg a).1 ha)
    exact ⟨s, Subtype.ext hs⟩
  haveI : Algebra.FiniteType ℤ A :=
    (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  exact isNoetherianRing_of_ringEquiv A (RingEquiv.ofBijective ρ ⟨hinj, hsurj⟩).symm

theorem isLocallyNoetherian_of_coordTie (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (hT : CoordTie ℤ ξ x)
    (hall : ∀ q : X, genPt ξ ⤳ q) : IsLocallyNoetherian X := by
  have key : ∀ p : X, ∃ U : X.affineOpens, p ∈ U.1 ∧ IsNoetherianRing Γ(X, U.1) := by
    intro p
    obtain ⟨c, hch⟩ := hT.cover ⟨p, hall p⟩
    obtain ⟨U, hU, hUm⟩ := hT.affine c hch.1
    have hp : p ∈ U := (hUm p).2 ⟨hall p, hch⟩
    exact ⟨⟨U, hU⟩, hp, isNoetherianRing_chart ξ x hT c hch.1 U hU hUm ((hall p).mem_open U.isOpen hp)⟩
  choose S hS hN using key
  exact isLocallyNoetherian_of_affine_cover (S := S)
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hS p⟩) hN

end Noeth

section Form

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem exists_homog_form_point (ξ : Spec (CommRingCat.of Ω) ⟶ X) (y : (Σ k, J k) → Ω)
    (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) (V : X.Opens) (hV : genPt ξ ∈ V) :
    ∃ (f : MRing J) (d : K → ℕ), IsMultiHomog f d ∧ f ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w f ≠ 0 →
      ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, CoordsAt ξ y z w ∧ centre z ∈ V := by
  classical
  obtain ⟨c, hch⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  have hcx := hch.1
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcx k (Finset.mem_univ k)
  obtain ⟨U, hU, hUm⟩ := hT.affine c hcx
  have hη : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, hch⟩
  have sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hUm q).1 hq).1
  have hreg : ∀ a : Ω, a ∈ chartRingZ y c ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    have h := hT.ring c hcx a
    rw [show (Algebra.adjoin ℤ (Set.range fun j : (∀ k, J k) => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) =
      chartRingZ y c from segre_chart y c hc] at h
    refine h.trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  let ρ : Γ(X, U) →+* chartRingZ y c := (ev ξ U hη).codRestrict (chartRingZ y c)
    fun s => (hreg _).2 fun q hq => ⟨_, genMap_germ hη q hq s⟩
  obtain ⟨s, hsV, hsη⟩ := hU.exists_basicOpen_le (V := V) ⟨genPt ξ, hV⟩ hη
  have ha0 : ev ξ U hη s ≠ 0 :=
    (((Scheme.mem_basicOpen X s _ hη).1 hsη).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  obtain ⟨g₀, hg₀⟩ := ratMap_surjective y c (ρ s)
  obtain ⟨m, G₀, hG₀, eG⟩ := exists_form c g₀
  have hy₀ : aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g₀ = ev ξ U hη s := by
    rw [← ratMap_coe, hg₀]
    rfl
  have hf0 : aeval y (G₀ * cMon c 1) ≠ 0 := by
    rw [map_mul, aeval_cMon, ← eG Ω y hc, hy₀]
    exact mul_ne_zero (mul_ne_zero ha0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  refine ⟨G₀ * cMon c 1, m + 1, homog_mul hG₀ (homog_cMon c 1), fun hmem => hf0 ?_, fun w hw hne => ?_⟩
  · have h := aeval_scaled y (fun _ => 1) (G₀ * cMon c 1)
    have h0 : mConeMap y (G₀ * cMon c 1) = 0 := hmem
    rw [h0, map_zero] at h
    simpa only [mul_one] using h
  have hne' : aeval w (G₀ * cMon c 1) ≠ 0 := by
    rw [← evC_eq_aeval]
    exact hne
  rw [map_mul, aeval_cMon] at hne'
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by
    have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne') k (Finset.mem_univ k)
    simpa using this
  obtain ⟨e, he⟩ := exists_chartEval y c hc w hw hwc
  obtain ⟨z, hz, hval⟩ := exists_pt hU (e.comp ρ)
  have hval' : ∀ k i, ∃ s : Γ(X, U), ev ξ U hη s = y ⟨k, i⟩ / y ⟨k, c k⟩ ∧
      (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) = w ⟨k, i⟩ / w ⟨k, c k⟩ := by
    intro k i
    have hm : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c := Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩
    obtain ⟨s, hs⟩ := exists_ev_eq hU hη sp _ ((hreg _).1 hm)
    refine ⟨s, hs, ?_⟩
    have e1 : ρ s = ratMap y c (MvPolynomial.X ⟨k, i⟩) := Subtype.ext (by rw [ratMap_coe, aeval_X]; exact hs)
    rw [hval]
    change e (ρ s) = _
    rw [e1, he, aeval_X]
  have hs0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) ≠ 0 := by
    rw [hval]
    change e (ρ s) ≠ 0
    rw [← hg₀, he]
    intro h0
    apply left_ne_zero_of_mul hne'
    rw [← eG ℂ w hwc, h0, zero_mul]
  refine ⟨z, ⟨fun k => ⟨c k, (IsUnit.mk0 _ (hwc k))⟩, fun k c₀ hu => ?_⟩, hsV ?_⟩
  · have hw0 : w ⟨k, c₀⟩ ≠ 0 := hu.ne_zero
    obtain ⟨sv, hsv, hev⟩ := hval' k c₀
    have hev0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz sv) ≠ 0 := by
      rw [hev]
      exact div_ne_zero hw0 (hwc k)
    have hy0 : y ⟨k, c₀⟩ ≠ 0 := by
      intro h0
      apply hev0
      have h1 : ρ sv = 0 := Subtype.ext (by
        change ev ξ U hη sv = 0
        rw [hsv, h0, zero_div])
      rw [hval]
      change e (ρ sv) = 0
      rw [h1, map_zero]
    refine ⟨hy0, fun i => ?_⟩
    obtain ⟨su, hsu, heu⟩ := hval' k i
    refine ⟨w ⟨k, i⟩ / w ⟨k, c₀⟩, ?_, by field_simp⟩
    have h := valAt_quot hη sp z hz su sv hev0
    rw [hsu, hsv, heu, hev, div_div_div_cancel_right₀ (hc k), div_div_div_cancel_right₀ (hwc k)] at h
    exact h
  · exact (Scheme.mem_basicOpen X s _ hz).2
      (isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (IsUnit.mk0 _ hs0))

end Form

end GlobalTheory.CompanionTheory.Ar.Cmp.HInterior

theorem GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c), A.ξ ≫ A.f = x ≫ Y.j → Mono (spMap β) → ∃ (b : MRing ι) (d : K → ℕ), IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w b ≠ 0 → ∃ z : Spec (CommRingCat.of ℂ) ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ ι _ y A x hx _
  haveI : IsLocallyNoetherian A.X := GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.isLocallyNoetherian_of_coordTie A.ξ _ A.tie A.all
  let V : A.X.Opens := ⟨abLocus A.t.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian A.t.G A.t.semi⟩
  have hV : genPt A.ξ ∈ V := by
    refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 (genPt A.ξ)).1 ?_
    have h1 : A.f (genPt A.ξ) = Y.j (x (IsLocalRing.closedPoint Ω)) := by
      have := congrArg (fun g : Sp Ω ⟶ Y.X => g (IsLocalRing.closedPoint Ω)) hx
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans (this.trans (Scheme.Hom.comp_apply _ _ _))
    rw [h1]
    exact GlobalTheory.ModelScope.range_j_subset_abLocus Y ⟨_, rfl⟩
  obtain ⟨b, d, hb, hbI, hw⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_homog_form_point A.ξ y A.tie V hV
  refine ⟨b, d, hb, hbI, fun w hwm hne => ?_⟩
  obtain ⟨z, hz, hzV⟩ := hw w hwm hne
  exact ⟨z, hz, hzV⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogFormStatement
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_multihomog_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c), A.ξ ≫ A.f = x ≫ Y.j → Mono (spMap β) → ∃ (b : MRing ι) (d : K → ℕ), IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w b ≠ 0 → ∃ z : Spec (CommRingCat.of ℂ) ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior | exact GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem pull_eq {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X)
    {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F] (L : Lat ξ E) (j : E →+ F)
    (p' : Cpt ξ') (hq : genPt ξ ⤳ f p'.1) :
    L.pull ξ' f j p' = Submodule.span (regAt ξ' p') (j '' (L ⟨f p'.1, hq⟩ : Set E)) := by
  unfold Lat.pull
  congr 1
  ext e'
  constructor
  · rintro ⟨_, e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨hq, e, he, rfl⟩

theorem unitAt_natCast {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} (q : Cpt ξ) (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    simpa [unitAt] using (regAt ξ q).one_mem
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := fun e => hn (by simp [e])
    have hb0 : b ≠ 0 := fun e => hn (by simp [e])
    obtain ⟨a1, a2, a3⟩ := ha ha0 fun p hp hd => h p hp (hd.mul_right _)
    obtain ⟨b1, b2, b3⟩ := hb hb0 fun p hp hd => h p hp (hd.mul_left _)
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.cast_mul]; exact mul_ne_zero a1 b1
    · rw [Nat.cast_mul]; exact (regAt ξ q).mul_mem a2 b2
    · rw [Nat.cast_mul, mul_inv]; exact (regAt ξ q).mul_mem a3 b3

theorem noeth_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hg : IsCptGen ξ) (q : Cpt ξ)
    (h : IsNoetherianRing (regAt ξ q)) : IsNoetherianRing (X.presheaf.stalk q.1) :=
  isNoetherianRing_of_ringEquiv (regAt ξ q) (RingEquiv.ofBijective (genMap ξ q).rangeRestrict
    ⟨fun a b e => hg.inj q (congrArg Subtype.val e), (genMap ξ q).rangeRestrict_surjective⟩).symm

set_option maxHeartbeats 1000000 in
theorem hodgeCpt_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (Z : Scheme.{0}) (ξ' : Sp Ω' ⟶ Z) (h : Z ⟶ A.X), A.ξ ≫ A.f = x ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn {q | InFibre A.ξ p q} (labelRk D s) ⊤) → (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t (e.hom ≫ h)), A'.ξ ≫ e.hom = ξ' ∧ A'.f = e.hom ≫ h ≫ A.f ∧ A'.m.φ = m.φ ≫ A.m.φ ∧ A'.cst = i.comp A.cst ∧ A'.R = A.R ∧ IsExtOver i j ∧ (∀ v, (A'.M.pt (j v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) ∧ (∀ p ∈ S, ∀ s, ((A'.M.htOm A'.t.PP.L (p ^ A'.R p)).map (A'.Vgen s).dualRestrict).IsVBOn {q | InFibre A'.ξ p q} (labelRk D s) ⊤) ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω Ω' _ _ i K K' _ _ J J' _ _ y y' A x Z ξ' h hx hS hvb hall htie hnorm hdom
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  haveI : CharZero Ω' := charZero_of_injective_ringHom i.injective
  have hgen := A.tie.gen
  have hgen' := htie.gen
  obtain ⟨t', ⟨mh⟩⟩ : ∃ t' : SAB H Z, Nonempty (SABMap t' A.t h) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM Out.proved_CubePullSt h A.t⟩⟩
  obtain ⟨mf, hmf⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ A.m mh
  obtain ⟨Li', acg', mod', ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Z t'.G Ω' ξ'
  obtain ⟨ρ', hρ', -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act Z t'.G Ω' ξ' Li' M' (𝓞 E) t'.act.act t'.act.hom t'.act.one
    t'.act.mul t'.act.add
  obtain ⟨j, hj⟩ := GlobalTheory.T.lie_model_pullback_map A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' hdom mh.cart
  have hsm : Smooth A.t.G.hom := A.t.semi.smooth
  obtain ⟨hext, hspan, hlat⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j hgen hgen' hdom
    mh.cart hsm hj
  have hρj := GlobalTheory.T.lie_model_pullback_action A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j (𝓞 E) A.t.act.act t'.act.act A.ρ ρ'
    hdom mh.cart hj A.act hρ' (fun a => mh.act a)
  obtain ⟨jd, hjd⟩ := GlobalTheory.T.dual_map_of_field_extension Ω Ω' i A.Li Li' j hext hspan
  have hW : ∀ s, eigSp ρ' ((i.comp A.cst).comp (labelEmb c s)) = Submodule.span Ω' (j '' (A.Vgen s : Set A.Li)) := fun s =>
    GlobalTheory.T.eigenspace_field_extension E Ω Ω' i A.Li Li' j A.ρ ρ' (A.emb s) hext hspan hρj
  have hdm := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates A.X Ω A.ξ Z Ω' ξ' h i hdom
  have hsp : ∀ p' : Cpt ξ', genPt A.ξ ⤳ h p'.1 := fun p' => (hdm p').choose
  have hreg : ∀ (p' : Cpt ξ'), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, i a ∈ regAt ξ' p' := fun p' => (hdm p').choose_spec.1
  have hun : ∀ (p' : Cpt ξ'), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, unitAt ξ' p' (i a) → unitAt A.ξ ⟨h p'.1, hsp p'⟩ a :=
    fun p' => (hdm p').choose_spec.2 hgen'
  have hfib : ∀ (p : ℕ) (p' : Cpt ξ'), InFibre ξ' p p' ↔ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := by
    intro p p'
    refine not_congr ⟨fun hu => ?_, fun ⟨a, b, d⟩ => ?_⟩
    · have hr : (p : Ω) ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := natCast_mem _ p
      exact hun p' _ hr (by simpa using hu)
    · refine ⟨?_, ?_, ?_⟩
      · intro e; apply a; apply i.injective; simpa using e
      · simpa using hreg p' _ b
      · simpa using hreg p' _ d
  have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1
  have hnoeth' := (GlobalTheory.T.regAt_noetherian_model_noetherian Z Ω' ξ' ℤ _ _ htie).1
  have hic : ∀ q : Cpt A.ξ, IsIntegrallyClosed (A.X.presheaf.stalk q.1) := fun q => A.normal.isIntegrallyClosed_stalk q.1
  have hic' : ∀ q : Cpt ξ', IsIntegrallyClosed (Z.presheaf.stalk q.1) := fun q => (hnorm q.1).2
  have htors : ∀ p ∈ S, FullTorsion t'.G ξ' (p ^ A.R p) := fun p hp =>
    GlobalTheory.T.full_torsion_pullback A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ _ hdom mh.cart (A.tors p hp)
  have hint : ∀ (s) (q : Cpt A.ξ) (a : 𝓞 E), A.emb s a ∈ regAt A.ξ q := fun s q a =>
    GlobalTheory.T.integral_element_regular A.X Ω A.ξ q hgen (hic q) _ ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)

  have hω : ∀ p ∈ S, ∀ p' : Cpt ξ', 0 < D.p + D.q → M'.htOm t'.PP.L (p ^ A.R p) p' =
      Submodule.span (regAt ξ' p') (jd '' (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩ : Set _)) := by
    intro p hp p' hpos
    have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
    obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c O β Y A.X A.f A.t A.m Ω A.ξ x hx
    obtain ⟨s0', o', ⟨m0'⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c O β Y Z (h ≫ A.f) t' mf Ω' ξ' (spMap i ≫ x) (by
      rw [← Category.assoc, hdom, Category.assoc, hx, Category.assoc])
    have hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (h p'.1)) := hic ⟨h p'.1, hsp p'⟩
    have hn1 : IsNoetherianRing (A.X.presheaf.stalk (h p'.1)) := noeth_stalk hgen ⟨h p'.1, hsp p'⟩ (hnoeth _)
    have h1 := GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨h p'.1, hsp p'⟩ hgen hN
      (A.tors p hp) hc1 hn1
    have h1' := GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) Z Ω' ξ' s0' o' t' m0' Li' M' (p ^ A.R p) p' hgen' hN
      (htors p hp) (hic' _) (noeth_stalk hgen' _ (hnoeth' _))
    have h2 := GlobalTheory.T.omega_lattice_dominant_compat A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j hgen hgen' hdom mh.cart hsm hj jd hjd
      (p ^ A.R p) hN p' (hsp p') hc1 hn1 (h1.2.1 hpos) h1.1
    rw [h1'.2.2, h2, pull_eq ξ' h _ jd p' (hsp p'), h1.2.2]
  have hpos : ∀ s, 0 < labelRk D s → 0 < D.p + D.q := by
    intro s hs
    rcases s with τ | τ
    · have : 0 < D.p := hs
      omega
    · have : 0 < D.q := hs
      omega
  have hdual : ∀ p ∈ S, ∀ s, ∀ p' : Cpt ξ', InFibre ξ' p p' →
      M'.htDual t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) p' =
        Submodule.span (regAt ξ' p') (j '' (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    have hq := (hfib p p').1 hf
    obtain ⟨U, hU, b, hb, hfr⟩ := hvb p hp s ⟨h p'.1, hsp p'⟩ hq
    obtain ⟨hli, hbs⟩ := hfr ⟨h p'.1, hsp p'⟩ hq hU
    exact GlobalTheory.T.dual_lattice_basis_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt ξ' p') A.Li Li' j jd (A.Vgen s) _
      (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩) (M'.htOm t'.PP.L (p ^ A.R p) p') (labelRk D s) b hext (hreg p') hjd
      (hW s) (fun hr => hω p hp p' (hpos s hr)) hli hb hbs
  have hhtw : ∀ p ∈ S, ∀ s, ∀ p' : Cpt ξ', InFibre ξ' p p' →
      M'.htW t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) (differentIdeal ℤ (𝓞 E)) p' =
        Submodule.span (regAt ξ' p')
          (j '' (A.M.htW A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) (differentIdeal ℤ (𝓞 E)) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    haveI := regAt_isLocalRing (ξ := A.ξ) ⟨h p'.1, hsp p'⟩
    obtain ⟨d₀, hd₀, hne, hdv⟩ := GlobalTheory.T.different_ideal_local_generator E Ω (regAt A.ξ ⟨h p'.1, hsp p'⟩) (A.emb s) (hint s _)
    exact GlobalTheory.T.different_scaled_lattice_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt ξ' p') A.Li Li' j (A.Vgen s) _ (𝓞 E) (A.emb s)
      (differentIdeal ℤ (𝓞 E)) d₀ (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩)
      (M'.htDual t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) p') hext (hreg p') (hW s) hd₀ hne hdv
      (fun e he => LieModel.mem_eigSp_of_mem_htDual _ _ _ _ _ he) (hdual p hp s p' hf)
  have hV : ∀ s, Lat.patch S (M'.eigLat ρ' ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel M' t'.PP.L (p ^ A.R p) ρ' (fun s' => (i.comp A.cst).comp (labelEmb c s')) s) =
      (A.V s).pull ξ' h j := by
    intro s
    funext p'
    rw [pull_eq ξ' h _ j p' (hsp p')]
    by_cases hc : ∃ p ∈ S, InFibre ξ' p p'
    · obtain ⟨p, hp, hf⟩ := hc
      rw [Lat.patch_of_unique S _ _ hp hf fun p2 hp2 h2 =>
        inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) hf h2]
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.HT p s ⟨h p'.1, hsp p'⟩ :=
        Lat.patch_of_unique S _ _ hp ((hfib p p').1 hf) fun p2 hp2 h2 =>
          inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) ((hfib p p').1 hf) h2
      rw [e1]
      rcases s with τ | τ
      · exact hhtw p hp _ p' hf
      · exact hdual p hp _ p' hf
    · have hc' : ∀ p ∈ S, ¬ InFibre ξ' p p' := fun p hp hf => hc ⟨p, hp, hf⟩
      rw [Lat.patch_of_not S _ _ hc']
      have hc'' : ∀ p ∈ S, ¬ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := fun p hp hf => hc' p hp ((hfib p p').2 hf)
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.dR s ⟨h p'.1, hsp p'⟩ := Lat.patch_of_not S _ _ hc''
      rw [e1]
      have hdisc : (((NumberField.discr E : ℤ) : Ω))⁻¹ ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := by
        have hn0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
        obtain ⟨-, -, hu⟩ := unitAt_natCast (ξ := A.ξ) ⟨h p'.1, hsp p'⟩ _ hn0 fun p hpp hd => by
          have hin := hS p hpp (Int.natCast_dvd.2 hd)
          exact not_not.1 (hc'' p hin)
        rcases Int.natAbs_eq (NumberField.discr E) with e | e
        · rw [e]; simpa using hu
        · rw [e]
          simpa using (regAt A.ξ ⟨h p'.1, hsp p'⟩).neg_mem hu
      show M'.lat p' ⊓ _ = _
      rw [hlat, pull_eq ξ' h _ j p' (hsp p')]
      exact GlobalTheory.T.lattice_eigen_field_extension E Ω Ω' i A.Li Li' j A.ρ ρ' (A.emb s) _ _ (A.M.lat ⟨h p'.1, hsp p'⟩) hext hρj (hreg p')
        (fun a e he => GlobalTheory.T.lie_lattice_stable_under_action A.X Ω A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) (hint s _) hdisc
  have hvb' : ∀ s, (Lat.patch S (M'.eigLat ρ' ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel M' t'.PP.L (p ^ A.R p) ρ' (fun s' => (i.comp A.cst).comp (labelEmb c s')) s)).IsVB (labelRk D s)
      (eigSp ρ' ((i.comp A.cst).comp (labelEmb c s))) := by
    intro s
    rw [hV s, hW s]
    have h3 := GlobalTheory.T.lattice_vector_bundle_pullback A.X Ω A.ξ A.Li Z Ω' ξ' h i Li' j (A.V s) Set.univ (labelRk D s) (A.Vgen s) hdom hext.1 hext.2
      (A.vb s)
    intro p' _
    obtain ⟨U, hU, b, hb, hfr⟩ := h3 p' ⟨hsp p', trivial⟩
    exact ⟨U, hU, b, hb, fun q _ hq => hfr q ⟨hsp q, trivial⟩ hq⟩
  have hvbt : ∀ p ∈ S, ∀ s, ((M'.htOm t'.PP.L (p ^ A.R p)).map
      (eigSp ρ' ((i.comp A.cst).comp (labelEmb c s))).dualRestrict).IsVBOn {q | InFibre ξ' p q} (labelRk D s) ⊤ := by
    intro p hp s
    exact GlobalTheory.T.lattice_flag_field_extension A.X Z Ω Ω' A.ξ ξ' h i A.Li Li' j jd (A.Vgen s) _ (A.M.htOm A.t.PP.L (p ^ A.R p))
      (M'.htOm t'.PP.L (p ^ A.R p)) {q | InFibre A.ξ p q} {q | InFibre ξ' p q} (labelRk D s) hdom hgen' hext hjd (hW s)
      (hvb p hp s) fun p' hf => ⟨hsp p', (hfib p p').1 hf, fun hr => hω p hp p' (hpos s hr)⟩
  let m' : SABMap t' A.t ((Iso.refl Z).hom ≫ h) :=
    { cm := mh.cm
      cart := by simpa using mh.cart
      base := by simpa using mh.base
      act := mh.act
      lin := mh.lin }
  refine ⟨{ X := Z, ξ := ξ', all := hall, tie := htie, normal := ⟨fun x => (hnorm x).1, fun x => (hnorm x).2⟩, f := h ≫ A.f, Ω₀ := A.Ω₀, ξ₀ := A.ξ₀,
            gen₀ := A.gen₀, cst := i.comp A.cst, cst_over := ?_, fn := i.comp A.fn, fn_over := ?_, t := t', m := mf,
            Li := Li', M := M', ρ := ρ', act := hρ', S_prime := A.S_prime, R := A.R, R_ge := A.R_ge, tors := htors,
            vb := hvb' }, Iso.refl Z, j, m', ?_, ?_, ?_, rfl, rfl, hext, hj, hvbt, ?_⟩
  · have e : ξ' ≫ h = spMap i ≫ A.ξ := hdom
    have e2 : ξ' ≫ h ≫ A.f ≫ Y.s = spMap i ≫ A.ξ ≫ A.f ≫ Y.s := by
      rw [← Category.assoc, e, Category.assoc]
    simp only [Category.assoc]
    rw [e2, A.cst_over]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · have := A.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this ⊢
    rw [← Category.assoc, hdom, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · simp
  · simp
  · exact hmf
  · intro s
    have e : (Iso.refl Z).hom ≫ h = h := Category.id_comp h
    refine (hV s).trans ?_
    exact congrArg (fun g => (A.V s).pull ξ' g j) e.symm

end GlobalTheory.CompanionTheory.Ar.HcptPull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (Z : Scheme.{0}) (ξ' : Sp Ω' ⟶ Z) (h : Z ⟶ A.X), A.ξ ≫ A.f = x ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn {q | InFibre A.ξ p q} (labelRk D s) ⊤) → (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) → IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t (e.hom ≫ h)), A'.ξ ≫ e.hom = ξ' ∧ A'.f = e.hom ≫ h ≫ A.f ∧ A'.m.φ = m.φ ≫ A.m.φ ∧ A'.cst = i.comp A.cst ∧ A'.R = A.R ∧ IsExtOver i j ∧ (∀ v, (A'.M.pt (j v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) ∧ (∀ p ∈ S, ∀ s, ((A'.M.htOm A'.t.PP.L (p ^ A'.R p)).map (A'.Vgen s).dualRestrict).IsVBOn {q | InFibre A'.ξ p q} (labelRk D s) ⊤) ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcptPull.hodgeCpt_pull | exact GlobalTheory.CompanionTheory.Ar.HcptPull.hodgeCpt_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.HcptPull.hodgeCpt_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateOmegaCoherent
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilEndomorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilEndomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtEnd

theorem pullPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {A B : Over X} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.comp_mul, ih]

theorem homPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {Z : Over X} (a : G ⟶ G) [IsMonHom a] (x : Z ⟶ G) (n : ℕ) :
    (x ^ n) ≫ a = (x ≫ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.mul_comp, ih]

theorem epiSp {Ω K : Type} [Field Ω] [Field K] (a : Ω →+* K) : Epi (spMap a) := by
  letI := a.toAlgebra
  haveI : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom a)) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom a)) := by
    rw [AlgebraicGeometry.surjective_iff]
    intro y
    exact ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective _

theorem powDescend {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω K : Type} [Field Ω] [Field K]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {N : ℕ} (a : Ω →+* K)
    {g₀ : Over.mk ξ ⟶ G} {g : Over.mk (spMap a ≫ ξ) ⟶ G} (e : g.left = spMap a ≫ g₀.left) (hg : g ^ N = 1) :
    g₀ ^ N = 1 := by
  let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a)
  haveI : Epi ψ := Over.epi_of_epi_left ψ (hk := epiSp a)
  have hψ : ψ ≫ g₀ = g := Over.OverMorphism.ext (by simp [ψ, e])
  apply (cancel_epi ψ).mp
  rw [pullPow, hψ, hg, CategoryTheory.MonObj.comp_one]

theorem secVal_app {B : Type} [CommRing B] {Z Z' : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (φ : Z ⟶ Z')
    (W : Z'.Opens) (f : Γ(Z', W)) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ W) :
    secVal x (φ ⁻¹ᵁ W) h ((φ.app W).hom f) = secVal (x ≫ φ) W h' f := by
  simp only [secVal, Scheme.Hom.comp_appLE]
  rfl

end GlobalTheory.CompanionTheory.Ar.HtEnd


open GlobalTheory.CompanionTheory.Ar.HtEnd in
theorem GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ (y y' : Over.mk ξ ⟶ G), y ^ n = 1 → y' ^ n = 1 → (∀ g, g ^ n = 1 → e y' g = e y (g ≫ a)) → ∀ (q : Cpt ξ) (w : Module.Dual Ω E), M.IsHTAt L n y q w → M.IsHTAt L n y' q (w ∘ₗ A) := by
  intro X _ Ω _ _ ξ _ _ G _ _ L n _ hFT ep hW E _ _ M a _ A hA y y' hy hy' hyy' q w hH
  obtain ⟨hw, W, f, hη, P1, P2⟩ := hH
  have hExt : ∀ {e' : E} {v}, M.Extends q e' v → M.Extends q (A e') (v ≫ a) := by
    intro e' v hv
    refine ⟨?_, ?_⟩
    · have h1 := hv.1
      unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, CategoryTheory.MonObj.one_comp]
    · rw [hA e', Over.comp_left, hv.2]
      erw [Category.assoc]
  have hlat : ∀ e' ∈ M.lat q, A e' ∈ M.lat q := by
    intro e' he'
    have hle : M.lat q ≤ (M.lat q).comap (A.restrictScalars (regAt ξ q)) := by
      refine Submodule.span_le.mpr ?_
      rintro e'' ⟨v, hv⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      exact Submodule.subset_span ⟨v ≫ a, hExt hv⟩
    exact hle he'
  have hw' : ∀ e' ∈ M.lat q, w e' ∈ regAt ξ q := hw
  refine ⟨?_, a.left ⁻¹ᵁ W, (a.left.app W).hom f, ?_, ?_, ?_⟩
  · show ∀ e' ∈ M.lat q, (w ∘ₗ A) e' ∈ regAt ξ q
    intro e' he'
    exact hw' (A e') (hlat e' he')
  · have h1 : (η[G] ≫ a).left = (η[G]).left := by rw [IsMonHom.one_hom]
    show a.left ((η[G]).left q.1) ∈ W
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
    exact hη
  · intro k _ _ i xk g c h hx hg hWe
    have h2 : ⊤ ≤ (g.left ≫ a.left) ⁻¹ᵁ W := h
    rw [secVal_app g.left a.left W f h h2]
    obtain ⟨g₀, hg₀⟩ := hFT k i g hg
    have hg₀n : g₀ ^ n = 1 := powDescend i hg₀ hg
    have hga : (g ≫ a) ^ n = 1 := by rw [← homPow, hg, CategoryTheory.MonObj.one_comp]
    have hg₀a : (g₀ ≫ a) ^ n = 1 := by rw [← homPow, hg₀n, CategoryTheory.MonObj.one_comp]
    have hc : (c : k) = i (ep y' g₀) := (hW.weil y' g₀ hy' hg₀n k i xk g c hx hg₀).mp hWe
    rw [hyy' g₀ hg₀n] at hc
    let xk0 : Over.mk (spMap i ≫ ξ) ⟶ G := Over.homMk (spMap i ≫ y.left)
    have hg' : (g ≫ a).left = spMap i ≫ (g₀ ≫ a).left := by
      rw [Over.comp_left, Over.comp_left, hg₀, Category.assoc]
    have hWa := (hW.weil y (g₀ ≫ a) hy hg₀a k i xk0 (g ≫ a) c rfl hg').mpr hc
    exact P1 k i xk0 (g ≫ a) c h2 rfl hga hWa
  · intro e' v hv h
    have h2 : ⊤ ≤ (v.left ≫ a.left) ⁻¹ᵁ W := h
    obtain ⟨r, hr, hE⟩ := P2 (A e') (v ≫ a) (hExt hv) h2
    refine ⟨r, hr, ?_⟩
    rw [LinearMap.comp_apply, secVal_app v.left a.left W f h h2]
    exact hE
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilEndomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_weil_endomorphism : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ (y y' : Over.mk ξ ⟶ G), y ^ n = 1 → y' ^ n = 1 → (∀ g, g ^ n = 1 → e y' g = e y (g ≫ a)) → ∀ (q : Cpt ξ) (w : Module.Dual Ω E), M.IsHTAt L n y q w → M.IsHTAt L n y' q (w ∘ₗ A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end | exact GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end | (intros; apply GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateOmegaCoherent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HTCoh

theorem htOm_coherent : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), (M.htOm L n).IsCohOn Set.univ ∧ ∀ q : Cpt ξ, (∀ u ∈ M.omLat q, n • u ∈ M.htOm L n q) ∧ M.htOm L n q ≤ M.omLat q ∧ ∀ (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ w ∈ M.htOm L n q, w ∘ₗ A ∈ M.htOm L n q := by
  intro X _ Ω _ _ ξ hgen hnorm G _ hsemi L n hn hfull e hW E _ _ M
  have gen : ∀ (q : Cpt ξ) (x : Over.mk ξ ⟶ G) (w : Module.Dual Ω E),
      x ^ n = 1 → M.IsHTAt L n x q w → w ∈ M.htOm L n q := by
    intro q x w hx hw
    simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
    exact Submodule.subset_span ⟨x, hx, hw⟩
  have mult : ∀ (q : Cpt ξ) (u : Module.Dual Ω E), u ∈ M.omLat q → n • u ∈ M.htOm L n q := by
    intro q u hu
    obtain ⟨⟨U, hqU, w, hw⟩, hdiff⟩ :=
      GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M q
    have h1 : (1 : Over.mk ξ ⟶ G) ^ n = 1 := one_pow n
    have h0 : M.IsHTAt L n 1 q (w 1) := hw 1 h1 q hqU
    have h2 : M.IsHTAt L n 1 q (w 1 + n • u) := (hdiff 1 (w 1) _ h1 h0).2 ⟨u, hu, rfl⟩
    have hsub := Submodule.sub_mem _ (gen q 1 _ h1 h2) (gen q 1 _ h1 h0)
    rwa [add_sub_cancel_left] at hsub
  refine ⟨?_, fun q => ⟨fun u hu => mult q u hu, ?_, ?_⟩⟩
  · intro p _
    haveI := hsemi
    haveI : IsCommMonObj G := IsSemiAbelian.comm
    have hsm : AlgebraicGeometry.Smooth G.hom := IsSemiAbelian.smooth
    obtain ⟨-, hVB⟩ := GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ G E M hgen hsm
    obtain ⟨U2, hpU2, bv, -, hfr⟩ := hVB p (Set.mem_univ p)
    obtain ⟨⟨U1, hpU1, w, hw⟩, -⟩ :=
      GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M p
    haveI : Finite {x : Over.mk ξ ⟶ G // x ^ n = 1} := hW.finite
    obtain ⟨k, ⟨eqv⟩⟩ := Finite.exists_equiv_fin {x : Over.mk ξ ⟶ G // x ^ n = 1}
    let b1 : Fin k → Module.Dual Ω E := fun i => w (eqv.symm i).1
    let b2 : Fin (Module.finrank Ω E) → Module.Dual Ω E := fun j => n • bv j
    refine ⟨U1 ⊓ U2, TopologicalSpace.Opens.mem_inf.2 ⟨hpU1, hpU2⟩, k + Module.finrank Ω E, Fin.append b1 b2, ?_⟩
    intro q _ hqU
    have hq1 := (TopologicalSpace.Opens.mem_inf.1 hqU).1
    have hq2 := (TopologicalSpace.Opens.mem_inf.1 hqU).2
    obtain ⟨-, hframe⟩ := hfr q (Set.mem_univ q) hq2
    obtain ⟨-, hdiff⟩ := GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M q
    apply le_antisymm
    · simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
      refine Submodule.span_le.mpr ?_
      rintro w' ⟨y, hy, hyw'⟩
      have hwy : M.IsHTAt L n y q (w y) := hw y hy q hq1
      obtain ⟨u, hu, rfl⟩ := (hdiff y (w y) w' hy hwy).1 hyw'
      refine Submodule.add_mem _ ?_ ?_
      · apply Submodule.subset_span
        refine ⟨Fin.castAdd _ (eqv ⟨y, hy⟩), ?_⟩
        simp [b1, Fin.append_left]
      · rw [hframe] at hu
        clear hyw'
        induction hu using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨j, rfl⟩ := hv
          apply Submodule.subset_span
          exact ⟨Fin.natAdd k j, by simp [b2, Fin.append_right]⟩
        | zero => rw [smul_zero]; exact Submodule.zero_mem _
        | add v1 v2 _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
        | smul r v _ h => rw [smul_comm]; exact Submodule.smul_mem _ r h
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left]
        exact gen q _ _ (eqv.symm i).2 (hw _ (eqv.symm i).2 q hq1)
      | right j =>
        rw [Fin.append_right]
        exact mult q _ (by rw [hframe]; exact Submodule.subset_span ⟨j, rfl⟩)
  · simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, -, hw⟩
    exact hw.1
  · intro a _ A hA w hw
    simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm] at hw ⊢
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, hxw⟩ := hw
      obtain ⟨y', hy', hrel⟩ := hW.perfect (fun g => e x (g ≫ a)) (by
        intro g g' hg hg'
        show e x ((g * g') ≫ a) = e x (g ≫ a) * e x (g' ≫ a)
        rw [MonObj.mul_comp]
        exact hW.mul_right x _ _ hx (by rw [← MonObj.pow_comp, hg, MonObj.one_comp])
          (by rw [← MonObj.pow_comp, hg', MonObj.one_comp]))
      exact Submodule.subset_span ⟨y', hy', GlobalTheory.T.hodge_tate_weil_endomorphism X Ω ξ hgen hnorm G hsemi L n hn hfull e hW
        E M a A hA x y' hx hy' (fun g hg => (hrel g hg).symm) q w hxw⟩
    | zero => rw [LinearMap.zero_comp]; exact Submodule.zero_mem _
    | add w1 w2 _ _ h1 h2 => rw [LinearMap.add_comp]; exact Submodule.add_mem _ h1 h2
    | smul r w _ h =>
      have hc : (r • w) ∘ₗ A = r • (w ∘ₗ A) := LinearMap.ext fun _ => rfl
      rw [hc]; exact Submodule.smul_mem _ r h

end GlobalTheory.CompanionTheory.Ar.HTCoh
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateOmegaCoherentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_omega_coherent : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), (M.htOm L n).IsCohOn Set.univ ∧ ∀ q : Cpt ξ, (∀ u ∈ M.omLat q, n • u ∈ M.htOm L n q) ∧ M.htOm L n q ≤ M.omLat q ∧ ∀ (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ w ∈ M.htOm L n q, w ∘ₗ A ∈ M.htOm L n q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HTCoh.htOm_coherent | exact GlobalTheory.CompanionTheory.Ar.HTCoh.htOm_coherent | (intros; apply GlobalTheory.CompanionTheory.Ar.HTCoh.htOm_coherent <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsRiemannForm
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeFamilyLocalSections
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeFamilyLocalSections
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_logPeriods_of_local_markings : ∀ (n a g : ℕ) (_h : a ≤ n) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : LinearMap.BilinForm ℤ Λ) (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Hf : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (U : Set (Fin n → ℂ)) (Γ₀ : Submodule ℤ (Fin g → ℂ)) (S : Γ₀ → (Fin n → ℂ) → (Fin g → ℂ)), U = {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0} → Module.finrank ℤ Λ = 2 * g → (∀ x, E x x = 0) → Function.Bijective E → (∀ z ∈ U, (Hf z).IsHermitian ∧ ∀ x : Fin g → ℂ, x ≠ 0 → 0 < (x ⬝ᵥ Hf z *ᵥ star x).re) → (∀ z₀ ∈ U, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ U ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧ ∀ z ∈ N, Function.Injective (P z) ∧ (P z).range = Γ z ∧ ∀ x y, (P z x ⬝ᵥ Hf z *ᵥ star (P z y)).im = E x y) → (∀ x, DifferentiableOn ℂ (S x) (ball 0 1) ∧ S x 0 = x ∧ ∀ z ∈ U, S x z ∈ Γ z) → (∀ x y z, S (x + y) z = S x z + S y z) → (∀ s : (Fin n → ℂ) → (Fin g → ℂ), ContinuousAt s 0 → (∀ z ∈ U, s z ∈ Γ z) → s 0 ∈ Γ₀) → Submodule.span ℂ (Γ₀ : Set (Fin g → ℂ)) = ⊤ → (∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → ∀ z ∈ U, ∃ k : ℤ, (S x z ⬝ᵥ Hf z *ᵥ star (S y z)).im = N * k) → ∃ L : LogPeriods n a g Λ, L.H = Hf := by
  intro n a g h Λ _ _ _ E Γ Hf U Γ₀ S hU hr hE hEb hH hloc hS hadd hlim hspan hcount
  obtain ⟨L, hL, -⟩ := GlobalTheory.T.period_lattice_on_punctured_disc n a g h Λ E Γ Hf U Γ₀ S hU hr hE hEb hH hloc hS hadd hlim
    hspan hcount
  exact ⟨L, hL⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeFamilyLocalSectionsStatement
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_local_sections : ∀ (n a g : ℕ) (_h : a ≤ n) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : LinearMap.BilinForm ℤ Λ) (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Hf : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (U : Set (Fin n → ℂ)) (Γ₀ : Submodule ℤ (Fin g → ℂ)) (S : Γ₀ → (Fin n → ℂ) → (Fin g → ℂ)), U = {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0} → Module.finrank ℤ Λ = 2 * g → (∀ x, E x x = 0) → Function.Bijective E → (∀ z ∈ U, (Hf z).IsHermitian ∧ ∀ x : Fin g → ℂ, x ≠ 0 → 0 < (x ⬝ᵥ Hf z *ᵥ star x).re) → (∀ z₀ ∈ U, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ U ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧ ∀ z ∈ N, Function.Injective (P z) ∧ (P z).range = Γ z ∧ ∀ x y, (P z x ⬝ᵥ Hf z *ᵥ star (P z y)).im = E x y) → (∀ x, DifferentiableOn ℂ (S x) (ball 0 1) ∧ S x 0 = x ∧ ∀ z ∈ U, S x z ∈ Γ z) → (∀ x y z, S (x + y) z = S x z + S y z) → (∀ s : (Fin n → ℂ) → (Fin g → ℂ), ContinuousAt s 0 → (∀ z ∈ U, s z ∈ Γ z) → s 0 ∈ Γ₀) → Submodule.span ℂ (Γ₀ : Set (Fin g → ℂ)) = ⊤ → (∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → ∀ z ∈ U, ∃ k : ℤ, (S x z ⬝ᵥ Hf z *ᵥ star (S y z)).im = N * k) → ∃ L : LogPeriods n a g Λ, L.H = Hf := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_of_local_markings | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_of_local_markings | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_of_local_markings <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsRiemannForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Link

theorem exists_logPeriods_isRiem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : LogPeriods n a C.g Λ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  intro E _ _ _ H D l Xo σ n a C hpq hσ
  obtain ⟨g', ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo σ g' ty hpq hσ hty
  have hsemi : IsSemiAbelian C.t.G := C.t.semi
  obtain ⟨ε, hε, hεB, ⟨e₀⟩⟩ := GlobalTheory.T.exists_family_exponential_locally C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ hsemi.smooth C.hol 0
    (Metric.mem_ball_self one_pos)
  have h0ε : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ε := Metric.mem_ball_self hε
  obtain ⟨Γ₀, hΓ₀, -, hfin, hfree⟩ := GlobalTheory.T.period_lattice_discrete_free C.R C.t.G C.g n C.M _ C.ψ e₀ 0 h0ε
  let Q : (Fin n → ℂ) → AddSubgroup (Fin C.g → ℂ) := fun b => AddSubgroup.closure (e₀.per b)
  have hQ : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, ∀ p, p ∈ Q b ↔ p ∈ e₀.per b := fun b hb p =>
    mem_closure_per e₀ hb p
  have hsp : ∀ x : Γ₀, ∃ (ε' : ℝ) (s : (Fin n → ℂ) → (Fin C.g → ℂ)), 0 < ε' ∧
      DifferentiableOn ℂ s (Metric.ball 0 ε') ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε', s b ∈ Q b := by
    intro x
    obtain ⟨ε', s, h0, hsub, hd, hs0, hs⟩ := GlobalTheory.T.period_holomorphic_continuation C.R C.t.G C.g n C.M _ C.ψ e₀ Metric.isOpen_ball 0 h0ε x
      (by rw [← hΓ₀]; exact x.2)
    exact ⟨ε', s, h0, hd, hs0, fun b hb => (hQ b (hsub hb) _).2 (hs b hb)⟩
  obtain ⟨ρ, hρ0, hρc, S, hSd, hS0, hSa, hSq⟩ := exists_additive_sections Γ₀ Q (min 1 ε) (lt_min one_pos hε) hsp
  have hρ1 : ρ ≤ 1 := hρc.trans (min_le_left _ _)
  have hball : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 ε :=
    Metric.ball_subset_ball (hρc.trans (min_le_right _ _))
  have hball1 : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 1 := Metric.ball_subset_ball hρ1
  have h0ρ : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ0
  let e : FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ := restrict e₀ Metric.isOpen_ball hball
  have hQ' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ p, p ∈ Q b ↔ p ∈ e.per b := fun b hb p => hQ b (hball hb) p
  have hΓ₀' : (Γ₀ : Set (Fin C.g → ℂ)) = e.per 0 := hΓ₀
  have hSp : ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ e.per b := fun x b hb =>
    (hQ' b hb _).1 (hSq x b hb)
  obtain ⟨i, Hf, hrank, hopen, hloc⟩ := GlobalTheory.T.boundary_chart_hodge_matrix E H D l Xo σ n a C g' ty FU ρ e hρ0 hρ1
  obtain ⟨hfreeL, hfinL, -⟩ := GlobalTheory.Coisotropic.lattice_rank E H (FU.Di i)
  have hU : ∀ z ∈ punct n a 1, (ρ : ℂ) • z ∈ punct n a ρ := fun z hz => (smul_mem_punct hρ0).2 hz
  have hsm : Differentiable ℂ (fun z : Fin n → ℂ => (ρ : ℂ) • z) := differentiable_id.fun_const_smul _
  have key : ∃ L : LogPeriods n a C.g (FU.Di i).La, L.H = (fun z => Hf ((ρ : ℂ) • z)) := by
    refine GlobalTheory.T.lattice_family_local_sections n a C.g C.a_le (FU.Di i).La (FU.Di i).EF (fun z => Q ((ρ : ℂ) • z))
      (fun z => Hf ((ρ : ℂ) • z)) (punct n a 1) Γ₀ (fun x z => S x ((ρ : ℂ) • z)) rfl hrank (FU.Di i).alt
      (FU.Di i).unimod ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun z hz => ⟨(hopen _ (hU z hz)).1, fun x hx => (hopen _ (hU z hz)).2.1 x hx⟩
    · intro z₀ hz₀
      obtain ⟨N, hNo, hzN, hNp, P, hPd, hP⟩ := hloc _ (hU z₀ hz₀)
      refine ⟨(fun z => (ρ : ℂ) • z) ⁻¹' N, hNo.preimage hsm.continuous, hzN,
        fun z hz => (smul_mem_punct hρ0).1 (hNp hz), fun z => P ((ρ : ℂ) • z), fun x => ?_, fun z hz => ?_⟩
      · exact (hPd x).comp hsm.differentiableOn (fun z hz => hz)
      · obtain ⟨h1, h2, h3⟩ := hP _ hz
        refine ⟨h1, ?_, h3⟩
        ext p
        have h4 : p ∈ (P ((ρ : ℂ) • z)).range ↔ p ∈ e.per ((ρ : ℂ) • z) := by
          rw [← SetLike.mem_coe, h2]
        rw [h4]
        exact (hQ' _ (punct_subset_ball (hNp hz)) p).symm
    · intro x
      refine ⟨(hSd x).comp hsm.differentiableOn (fun z hz => smul_mem_ball hρ0 hz), ?_,
        fun z hz => hSq x _ (smul_mem_ball hρ0 hz.1)⟩
      show S x ((ρ : ℂ) • 0) = x
      rw [smul_zero]
      exact hS0 x
    · exact fun x y z => hSa x y _
    · intro s hs hsU
      obtain ⟨u, hu, huU⟩ := exists_seq_punct (n := n) (a := a)
      have hρc' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
      have htend : Tendsto (fun k => (ρ : ℂ) • u k) atTop (𝓝 0) := by
        have h := hu.const_smul (ρ : ℂ)
        rwa [smul_zero] at h
      have hcl := GlobalTheory.T.period_set_closed C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e hsemi.separated
        ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono hball1⟩ 0 h0ρ (fun b => s ((ρ : ℂ)⁻¹ • b))
        (ContinuousAt.comp_of_eq hs (continuous_const_smul _).continuousAt (smul_zero _))
        (htend.frequently (Eventually.frequently (Eventually.of_forall fun k => by
          refine ⟨punct_subset_ball (hU _ (huU k)), ?_⟩
          show s ((ρ : ℂ)⁻¹ • (ρ : ℂ) • u k) ∈ e.per ((ρ : ℂ) • u k)
          rw [smul_smul, inv_mul_cancel₀ hρc', _root_.one_smul]
          exact (hQ' _ (punct_subset_ball (hU _ (huU k))) _).1 (hsU _ (huU k)))))
      have h0 : s 0 ∈ e.per 0 := by simpa using hcl
      rw [← hΓ₀'] at h0
      exact h0
    · rw [hΓ₀']
      exact GlobalTheory.T.period_lattice_spans C.R C.t.G C.g n C.M _ C.ψ e hsemi 0 h0ρ
    · intro N hN
      obtain ⟨T, hT, hTw⟩ := GlobalTheory.T.torsion_periods_finite_quotient E H C.R C.t C.g n C.M (Metric.ball 0 ρ) C.ψ e C.dim 0 h0ρ Γ₀ hΓ₀' N hN
      refine ⟨T, hT, fun x y hx z hz => ?_⟩
      have hb := hU z hz
      have hbm := punct_subset_ball hb
      have hc := cubWeil_carry e hρ0 N hN (S x) (S y) (hSd x) (hSd y) (hSp x) (hSp y) 1 (by
        rw [hS0 x, hS0 y]
        have h1 : unitOn (1 : ℂˣ) = 1 := map_one _
        rw [h1]
        exact hTw x y hx) _ hbm
      have hz' := (hopen _ hb).2.2.2 N 1 hN _ (hSp x _ hbm) _ (hSp y _ hbm) hc
      exact exists_int_of_exp_eq_one hN hz'
  obtain ⟨L, hLH⟩ := key
  refine ⟨ρ, (FU.Di i).La, inferInstance, L, hρ0, hρ1, fun z hz => ?_⟩
  rw [hLH]
  exact (hopen _ (hU z hz)).2.2.1

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsRiemannFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_periods_riemann_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : LogPeriods n a C.g Λ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_isRiem | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_isRiem | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_isRiem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeRelay
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeRelay
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω := by
  first | exact @PositivityTheory.Xgn.function_family_chart_facts | exact PositivityTheory.Xgn.function_family_chart_facts
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeRelayStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω := by
  first | exact @GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay | exact GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay <;> assumption)
end
end
