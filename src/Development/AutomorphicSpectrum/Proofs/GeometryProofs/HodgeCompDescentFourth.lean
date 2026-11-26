module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointVectors

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourth
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgUnit

theorem mem_regAt_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type}
    [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R} (h : ValAt ξ z a r) (p : Cpt ξ)
    (hp : p.1 = centre z) : a ∈ regAt ξ p := by
  obtain ⟨x, hx⟩ := p
  dsimp only at hp
  subst hp
  obtain ⟨_, s, hs, -⟩ := h
  exact ⟨s, hs⟩

theorem inChart_of_coordsAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type}
    [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {w : (Σ k, J k) → R} (hw : CoordsAt ξ y z w) (c : (k : K) → J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) (p : Cpt ξ) (hp : p.1 = centre z) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (hw.2 k _ (hc k)).1, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / (∏ k, y ⟨k, c k⟩) ∈ regAt ξ p
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (hw.2 k _ (hc k)).2 (c' k)
  exact mem_regAt_of_valAt hr p hp

theorem exists_unit_of_span_eq {Ω : Type} [Field Ω] (R : Subring Ω) {a b : Ω} (ha : a ≠ 0)
    (h : Submodule.span R {a} = Submodule.span R {b}) : ∃ u : Ω, u ∈ R ∧ u⁻¹ ∈ R ∧ a = u * b := by
  have h1 : a ∈ Submodule.span R {b} := h ▸ Submodule.mem_span_singleton_self a
  have h2 : b ∈ Submodule.span R {a} := h ▸ Submodule.mem_span_singleton_self b
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h2
  have hr' : (r : Ω) * b = a := hr
  have ht' : (t : Ω) * a = b := ht
  have hrt : (r : Ω) * t = 1 := by
    apply mul_right_cancel₀ ha
    rw [_root_.mul_assoc, ht', hr', _root_.one_mul]
  refine ⟨r, r.2, ?_, hr'.symm⟩
  rw [inv_eq_of_mul_eq_one_right hrt]
  exact t.2

theorem zpow_mem_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (n : ℤ) :
    u ^ n ∈ R := by
  cases n with
  | ofNat m => simpa using pow_mem h m
  | negSucc m =>
    rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h' _

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem tens_unit_eq {Λ : Lat ξ Ω} {p : Cpt ξ} {s : Ω} (hs : Λ.IsGenAt p s) (n : ℤ) :
    Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {s ^ n} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨s', hs', rfl⟩
    have h' := hs' ()
    obtain ⟨u, hu, hu', e⟩ := exists_unit_of_span_eq (regAt ξ p) h'.1 (h'.2.symm.trans hs.2)
    refine Submodule.mem_span_singleton.2 ⟨⟨u ^ n, zpow_mem_of_inv_mem _ hu hu' n⟩, ?_⟩
    show u ^ n * s ^ n = _
    simp [e, mul_zpow]
  · refine Submodule.span_le.2 ?_
    rintro t rfl
    exact Submodule.subset_span ⟨fun _ => s, fun _ => hs, by simp⟩

theorem exists_gen_of_tens {Λ : Lat ξ Ω} {p : Cpt ξ} {g : Ω} {n : ℤ} (hg : g ≠ 0)
    (h : Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {g}) : ∃ s, Λ.IsGenAt p s := by
  by_contra hn
  have hempty : {t | ∃ s : Unit → Ω, (∀ i, Λ.IsGenAt p (s i)) ∧ t = ∏ i, s i ^ (fun _ => n) i} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨s, hs, -⟩
    exact hn ⟨_, hs ()⟩
  have h0 : Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = ⊥ := by
    show Submodule.span _ _ = ⊥
    rw [hempty, Submodule.span_empty]
  have hm : g ∈ Submodule.span (regAt ξ p) {g} := Submodule.mem_span_singleton_self g
  rw [← h, h0] at hm
  exact hg ((Submodule.mem_bot _).1 hm)

theorem exists_value_of_unit (hξ : IsCptGen ξ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (hz : genPt ξ ⤳ centre z) {f : Ω}
    (hf : f ≠ 0) (h1 : f ∈ regAt ξ ⟨centre z, hz⟩) (h2 : f⁻¹ ∈ regAt ξ ⟨centre z, hz⟩) :
    ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z f u := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have hst : s * t = 1 := hξ.inj ⟨centre z, hz⟩ (by rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ hf])
  refine ⟨(Scheme.stalkClosedPointTo z).hom s, fun h0 => ?_, hz, s, hs, rfl⟩
  exact ((IsUnit.of_mul_eq_one t hst).map (Scheme.stalkClosedPointTo z).hom).ne_zero h0

theorem comparison_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (r : CMType H × Fin (D.p + D.q)), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → (Fl₀.rootLat r).IsDegOn Set.univ y₀ a₀ e₀ → (Fl.rootLat r).IsDegOn Set.univ y a e → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt 𝔐₀.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl bk bx a a₀ e e₀ r hβ hΩ
    hy hgen hdeg₀ hdeg hunit hreg hco z w hw cc c₀ hc hc₀
  haveI := hΩ
  have hz : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  let q : Cpt 𝔐.ξ := ⟨centre z, hz⟩
  let q₀ : Cpt 𝔐₀.ξ := pushCpt hd q
  have hw₀ := hco z w hw
  have huc : ∀ k, IsUnit (w ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (hc k)
  have huc₀ : ∀ k, IsUnit ((fun p => w (blkV bk bx p)) (⟨k, c₀ k⟩ : Σ k, J₀ k)) := fun k => IsUnit.mk0 _ (hc₀ k)
  have hq₀c : q₀.1 = centre (z ≫ h) := rfl
  have hq : (Fl.rootLat r) q = Submodule.span (regAt 𝔐.ξ q) {(∏ k, y ⟨k, cc k⟩ ^ a k) * e} :=
    hdeg.2 q trivial cc (inChart_of_coordsAt hw cc huc q rfl)
  have hq₀ : (Fl₀.rootLat r) q₀ = Submodule.span (regAt 𝔐₀.ξ q₀) {(∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀} :=
    hdeg₀.2 q₀ trivial c₀ (inChart_of_coordsAt hw₀ c₀ huc₀ q₀ hq₀c)
  have hg : (∏ k, y ⟨k, cc k⟩ ^ a k) * e ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k _ (huc k)).1) hdeg.1
  have hg₀ : (∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw₀.2 k _ (huc₀ k)).1) hdeg₀.1
  obtain ⟨s₀, hs₀⟩ := exists_gen_of_tens
    (Λ := (𝔐₀.V (HodgeCpt.rootIdx D r).1).gr (Fl₀.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
    (n := HodgeCpt.rootSgn D r) hg₀ hq₀
  have e₁ := tens_unit_eq hs₀ (HodgeCpt.rootSgn D r)
  obtain ⟨u₀, hu₀, hu₀', hgu⟩ := exists_unit_of_span_eq (regAt 𝔐₀.ξ q₀) hg₀ (hq₀.symm.trans e₁)
  have hs : ((𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2).IsGenAt q
      (i s₀) := hgen q (fun p hp => not_inFibre 𝔐.ξ z hz hp) _ _ s₀ hs₀
  have e₂ := tens_unit_eq hs (HodgeCpt.rootSgn D r)
  obtain ⟨v, hv, hv', hgv⟩ := exists_unit_of_span_eq (regAt 𝔐.ξ q) (zpow_ne_zero _ hs.1) (e₂.symm.trans hq)
  have hfe : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, cc k⟩ ^ a k) * e) = i u₀ * v := by
    rw [hgu, map_mul, map_zpow₀, hgv, ← _root_.mul_assoc (i u₀) v]
    exact mul_div_cancel_right₀ _ hg
  have hf : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, cc k⟩ ^ a k) * e) ≠ 0 :=
    div_ne_zero ((map_ne_zero i).2 hg₀) hg
  refine exists_value_of_unit 𝔐.tie.gen z hz hf ?_ ?_
  · rw [hfe]
    exact mul_mem (hreg q _ hu₀) hv
  · rw [hfe, mul_inv, ← map_inv₀]
    exact mul_mem (hreg q _ hu₀') hv'

end GlobalTheory.CompanionTheory.Ar.ChgUnit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourthStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_fourth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (r : CMType H × Fin (D.p + D.q)), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → (Fl₀.rootLat r).IsDegOn Set.univ y₀ a₀ e₀ → (Fl.rootLat r).IsDegOn Set.univ y a e → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt 𝔐₀.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit | exact GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.ChgUnit.comparison_unit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionPotentialPullback
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionPotentialPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.Twist

section Holo

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem continuousAt_holo (A : FinHolAtlas e X) {W : Set X} {g : X → ℂ} (hg : A.HoloOn W g) {x : X}
    (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) :=
    (hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩).continuousAt
  have h3 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm) h1 ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

theorem holoOn_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h) {U : Set X}
    {g : X → ℂ} (hg : A.HoloOn U g) : B.HoloOn (h ⁻¹' U) (fun y => g (h y)) := by
  rintro j y ⟨hy, hyU⟩
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm y))
  have a1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y := hh.2 j k y ⟨hy, hk⟩
  have a2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart j).symm) y) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      simpa [Function.comp, (A.chart k).left_inv hk] using hyU⟩
  refine (a2.comp a1).congr ?_
  filter_upwards [((B.chart j).isOpen_inter_preimage_symm
    ((A.chart k).open_source.preimage hh.1)).mem_nhds ⟨hy, hk⟩] with y' hy'
  simp [Function.comp, (A.chart k).left_inv hy'.2]

theorem exists_log (A : FinHolAtlas e X) {W : Set X} (hW : IsOpen W) {c : X → ℂ} (hc : A.HoloOn W c) {x : X}
    (hx : x ∈ W) (h0 : c x ≠ 0) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ ∃ L : X → ℂ, A.HoloOn V L ∧
      ∀ y ∈ V, c y ≠ 0 ∧ (L y).re = Real.log ‖c y‖ := by
  have hcont : ContinuousOn (fun y => c y / c x) W := fun y hy =>
    ((continuousAt_holo A hc hy).div_const _).continuousWithinAt
  have hV : IsOpen (W ∩ (fun y => c y / c x) ⁻¹' Complex.slitPlane) :=
    hcont.isOpen_inter_preimage hW Complex.isOpen_slitPlane
  refine ⟨_, hV, ⟨hx, ?_⟩, Set.inter_subset_left, fun y => Complex.log (c y / c x) + (Real.log ‖c x‖ : ℂ), ?_, ?_⟩
  · simp [div_self h0]
  · rintro j z ⟨hz, hzW, hzs⟩
    have a1 : AnalyticAt ℂ (c ∘ (A.chart j).symm) z := hc j z ⟨hz, hzW⟩
    have a2 : AnalyticAt ℂ (fun z => (c ∘ (A.chart j).symm) z / c x) z := a1.div analyticAt_const h0
    exact (a2.clog hzs).add analyticAt_const
  · rintro y ⟨-, hy⟩
    have hy' : c y / c x ≠ 0 := Complex.slitPlane_ne_zero hy
    have hcy : c y ≠ 0 := fun e => hy' (by simp [e])
    refine ⟨hcy, ?_⟩
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hcy) (norm_ne_zero_iff.2 h0)]
    ring

end Holo

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type}
  [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k}
  {P₀ Jd₀ : Ideal (MRing J₀)} {P Jd : Ideal (MRing J)} {D : ℕ}

theorem orbit_key (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (hv : IsBlockMap κ v) (h : R.X → R₀.X)
    (ho : ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) {x y : R.X} (hy : y ∈ R.U x)
    (hy₀ : h y ∈ R₀.U (h x)) :
    ∃ c : K₀ → ℂ, (∀ k, c k ≠ 0) ∧ ∀ p, R.lift x y (v p) = c p.1 * R₀.lift (h x) (h y) p := by
  obtain ⟨c₁, h₁, e₁⟩ := R.compat x y y ⟨hy, R.mem_U y⟩
  obtain ⟨c₂, h₂, e₂⟩ := ho y
  obtain ⟨c₃, h₃, e₃⟩ := R₀.compat (h x) (h y) (h y) ⟨hy₀, R₀.mem_U _⟩
  refine ⟨fun k => c₁ (κ k) / (c₃ k * c₂ k), fun k => div_ne_zero (h₁ _) (mul_ne_zero (h₃ k) (h₂ k)), fun p => ?_⟩
  have a₁ := congrFun e₁ (v p)
  have a₂ := congrFun e₂ p
  have a₃ := congrFun e₃ p
  simp only at a₁ a₂ a₃
  have n₂ := h₂ p.1
  have n₃ := h₃ p.1
  rw [a₃, a₂, a₁, hv.2.2.1 p]
  field_simp

theorem exists_coeff_log (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (hv : IsBlockMap κ v) (h : R.X → R₀.X)
    (hh : HoloMap R.A R₀.A h)
    (ho : ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) (x : R.X) (k : K₀) :
    ∃ V : Set R.X, IsOpen V ∧ x ∈ V ∧ V ⊆ R.U x ∩ h ⁻¹' R₀.U (h x) ∧ ∃ L : R.X → ℂ, R.A.HoloOn V L ∧
      ∀ y ∈ V, ∀ c : K₀ → ℂ, (∀ k, c k ≠ 0) →
        (∀ p, R.lift x y (v p) = c p.1 * R₀.lift (h x) (h y) p) → (L y).re = Real.log ‖c k‖ := by
  have oW : IsOpen (R.U x ∩ h ⁻¹' R₀.U (h x)) := (R.isOpen_U x).inter ((R₀.isOpen_U _).preimage hh.1)
  have mW : x ∈ R.U x ∩ h ⁻¹' R₀.U (h x) := ⟨R.mem_U x, R₀.mem_U _⟩
  obtain ⟨i, hi⟩ := (R₀.mem (h x) (h x) (R₀.mem_U _)).1 k
  obtain ⟨cx, hcx, ecx⟩ := orbit_key R₀ R hv h ho (R.mem_U x) (R₀.mem_U (h x))
  have hn : R.A.HoloOn (R.U x ∩ h ⁻¹' R₀.U (h x)) (fun y => R.lift x y (v ⟨k, i⟩)) := fun j z hz =>
    R.holo x (v ⟨k, i⟩) j z ⟨hz.1, hz.2.1⟩
  have hd : R.A.HoloOn (R.U x ∩ h ⁻¹' R₀.U (h x)) (fun y => R₀.lift (h x) (h y) ⟨k, i⟩) := fun j z hz =>
    holoOn_comp hh (R₀.holo (h x) ⟨k, i⟩) j z ⟨hz.1, hz.2.2⟩
  have hnx : R.lift x x (v ⟨k, i⟩) ≠ 0 := by
    rw [ecx ⟨k, i⟩]
    exact mul_ne_zero (hcx k) hi
  obtain ⟨Vn, oVn, mVn, sVn, Ln, hLn, eLn⟩ := exists_log R.A oW hn mW hnx
  obtain ⟨Vd, oVd, mVd, -, Ld, hLd, eLd⟩ := exists_log R.A oW hd mW hi
  refine ⟨Vn ∩ Vd, oVn.inter oVd, ⟨mVn, mVd⟩, Set.inter_subset_left.trans sVn, fun y => Ln y - Ld y, ?_, ?_⟩
  · rintro j z ⟨hz, hzn, hzd⟩
    exact (hLn j z ⟨hz, hzn⟩).sub (hLd j z ⟨hz, hzd⟩)
  · rintro y ⟨hyn, hyd⟩ c hc ec
    obtain ⟨-, e1⟩ := eLn y hyn
    obtain ⟨d0, e2⟩ := eLd y hyd
    simp only [Complex.sub_re, e1, e2]
    rw [ec ⟨k, i⟩, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 d0)]
    ring

theorem samePot_twist : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (κ : K₀ → K) (v : (Σ k, J₀ k) → Σ k, J k) (P₀ Jd₀ : Ideal (MRing J₀)) (P Jd : Ideal (MRing J)) (D : ℕ) (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (X : Type) [TopologicalSpace X] (B : FinHolAtlas D X) (Θ : LocPot X) (A₀ : HermLine J₀) (T : HermLine J) (π : R₀.X → X) (hπ : HoloMap R₀.A B π) (h : R.X → R₀.X) (hv : IsBlockMap κ v) (hc : Continuous (π ∘ h)), HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) → SamePot R₀.A Set.univ (potOf R₀ A₀) (Θ.pullback π hπ.1) → IsFlatOn R T → SamePot R.A Set.univ (potOf R ((pullHerm hv A₀).tensor T)) (Θ.pullback (π ∘ h) hc) := by
  intro K₀ K _ _ J₀ J _ _ κ v P₀ Jd₀ P Jd D R₀ R X _ B Θ A₀ T π hπ h hv hc hh ho h0 hF x _
  obtain ⟨V₀, oV₀, mV₀, G₀, hG₀, e₀⟩ := h0 (h x) trivial
  obtain ⟨V₁, oV₁, mV₁, G₁, hG₁, e₁⟩ := hF x trivial
  choose Vk oVk mVk sVk L hL eL using exists_coeff_log R₀ R hv h hh ho x
  refine ⟨(⋂ k, Vk k) ∩ ((h ⁻¹' V₀ ∩ V₁) ∩ (R.U x ∩ h ⁻¹' R₀.U (h x))),
    (isOpen_iInter_of_finite oVk).inter (((oV₀.preimage hh.1).inter oV₁).inter
      ((R.isOpen_U x).inter ((R₀.isOpen_U _).preimage hh.1))),
    ⟨Set.mem_iInter.2 mVk, ⟨mV₀, mV₁⟩, R.mem_U x, R₀.mem_U _⟩,
    fun y => G₀ (h y) + G₁ y + ∑ k, ((A₀.a k : ℝ) : ℂ) * L k y, ?_, ?_⟩
  · rintro j z ⟨hz, hzk, ⟨hz₀, hz₁⟩, -⟩
    have t0 : AnalyticAt ℂ (fun z => G₀ (h ((R.A.chart j).symm z))) z := holoOn_comp hh hG₀ j z ⟨hz, hz₀⟩
    have t1 : AnalyticAt ℂ (fun z => G₁ ((R.A.chart j).symm z)) z := hG₁ j z ⟨hz, hz₁⟩
    have t2 : ∀ k ∈ (Finset.univ : Finset K₀),
        AnalyticAt ℂ (fun z => ((A₀.a k : ℝ) : ℂ) * L k ((R.A.chart j).symm z)) z := fun k _ =>
      analyticAt_const.mul (hL k j z ⟨hz, Set.mem_iInter.1 hzk k⟩)
    exact (t0.add t1).add (Finset.analyticAt_fun_sum _ t2)
  · rintro y ⟨hyk, ⟨hy₀, hy₁⟩, hyU, hyU₀⟩
    obtain ⟨c, hc0, ec⟩ := orbit_key R₀ R hv h ho hyU hyU₀
    have E0 : Real.log (A₀.h (R₀.lift (h x) (h y))) - Θ.φ (π (h x)) (π (h y)) = (G₀ (h y)).re := e₀ (h y) hy₀
    have E1 : Real.log (T.h (R.lift x y)) - 0 = (G₁ y).re := e₁ y hy₁
    have E2 : (fun p => R.lift x y (v p)) = fun p => c p.1 * R₀.lift (h x) (h y) p := funext ec
    show Real.log (((pullHerm hv A₀).tensor T).h (R.lift x y)) - Θ.φ (π (h x)) (π (h y)) = _
    rw [log_tensor_pull hv A₀ T (R.mem x y hyU).1, E2, log_h_smul A₀ hc0 (R₀.mem _ _ hyU₀).1]
    simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, ← E0, ← E1,
      fun k => eL k y (Set.mem_iInter.1 hyk k) c hc0 ec]
    ring

end GlobalTheory.CompanionTheory.Ar.Chg.Twist
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionPotentialPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_potential_pullback : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (κ : K₀ → K) (v : (Σ k, J₀ k) → Σ k, J k) (P₀ Jd₀ : Ideal (MRing J₀)) (P Jd : Ideal (MRing J)) (D : ℕ) (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (X : Type) [TopologicalSpace X] (B : FinHolAtlas D X) (Θ : LocPot X) (A₀ : HermLine J₀) (T : HermLine J) (π : R₀.X → X) (hπ : HoloMap R₀.A B π) (h : R.X → R₀.X) (hv : IsBlockMap κ v) (hc : Continuous (π ∘ h)), HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) → SamePot R₀.A Set.univ (potOf R₀ A₀) (Θ.pullback π hπ.1) → IsFlatOn R T → SamePot R.A Set.univ (potOf R ((pullHerm hv A₀).tensor T)) (Θ.pullback (π ∘ h) hc) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist | exact GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.Twist.samePot_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelRankEqGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelRankEqGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.LieRank

variable {S : Scheme.{0}}

theorem dualMap_apply {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (a : DualNumber R) :
    dualMap c a = TrivSqZeroExt.inl (c a.fst) + TrivSqZeroExt.inr (c a.snd) := rfl

theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    (dualMap c).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp c := by
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    TrivSqZeroExt.snd_inl, map_zero, TrivSqZeroExt.inr_zero, add_zero]

theorem fst_comp_dualMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  change (dualMap c a).fst = c a.fst
  simp [dualMap_apply]

theorem dualMap_comp_epsMul {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (r : R) :
    (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
  refine RingHom.ext fun a => ?_
  change dualMap c (TrivSqZeroExt.map (r • (LinearMap.id : R →ₗ[R] R)) a) =
    TrivSqZeroExt.map (c r • (LinearMap.id : R' →ₗ[R'] R')) (dualMap c a)
  ext <;> simp [dualMap_apply, mul_comm]

def epsPull {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') (x : Sp R ⟶ S) :
    epsAt (spMap c ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap c)) (by
    change spMap (dualMap c) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap c ≫ x
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (dualMap_comp_algebraMap c))

theorem one_left_pull (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) :
    (1 : Over.mk (spMap c ≫ x) ⟶ G).left = spMap c ≫ (1 : Over.mk x ⟶ G).left := by
  have h := MonObj.comp_one (Over.homMk (spMap c) rfl : Over.mk (spMap c ≫ x) ⟶ Over.mk x) (M := G)
  exact (congrArg (fun k => k.left) h).symm

theorem isTanAt_pull (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    IsTanAt G (spMap c ≫ x) (epsPull c x ≫ v) := by
  unfold IsTanAt at hv ⊢
  rw [one_left_pull, ← hv]
  change _ ≫ spMap (dualMap c) ≫ v.left = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (by
    refine RingHom.ext fun a => ?_
    exact (RingHom.congr_fun (fst_comp_dualMap c) a))

theorem epsPull_comp_left (G : Over S) {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    (x : Sp R ⟶ S) (v : epsAt x ⟶ G) : (epsPull c x ≫ v).left = spMap (dualMap c) ≫ v.left := by
  simp [epsPull]

theorem exists_lift (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (x : Sp R ⟶ S) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] [Module R E']
    [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') :
    ∃ j : E →ₗ[R] E', ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := by
  have hex : ∀ e, ∃ e', M'.pt e' = epsPull (algebraMap R R') x ≫ M.pt e := fun e =>
    M'.onto _ (isTanAt_pull G _ x _ (M.tan e))
  choose f hf using hex
  have hadd : ∀ a b, f (a + b) = f a + f b := fun a b => by
    apply M'.inj
    rw [M'.add, hf, hf, hf, M.add, MonObj.comp_mul]
  have hsmul : ∀ (r : R) a, f (r • a) = r • f a := fun r a => by
    apply M'.inj
    apply Over.OverMorphism.ext
    rw [← algebraMap_smul R' r (f a), M'.smul, hf, hf, epsPull_comp_left, epsPull_comp_left, M.smul,
      ← Category.assoc, ← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (dualMap_comp_epsMul (algebraMap R R') r)
  have hl : ∀ e, ((M'.pt (f e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left) := fun e => by
    rw [hf, Category.comp_id, epsPull_comp_left]
  exact ⟨⟨⟨f, hadd⟩, hsmul⟩, hl⟩

theorem finrank_of_isBaseChange {A F : Type} [CommRing A] [Field F] [Algebra A F] {E E' : Type} [AddCommGroup E]
    [Module A E] [AddCommGroup E'] [Module F E'] [Module A E'] [IsScalarTower A F E'] [Module.Finite A E]
    [Module.Projective A E] (j : E →ₗ[A] E') (hj : IsBaseChange F j) (p : PrimeSpectrum F) :
    Module.finrank F E' = Module.rankAtStalk E (PrimeSpectrum.comap (algebraMap A F) p) := by
  rw [← Module.rankAtStalk_baseChange (S := F) (M := E) p]
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact (LinearEquiv.finrank_eq hj.equiv).symm

theorem finrank_eq_of_isBaseChange_fractionRing {D L : Type} [CommRing D] [IsDomain D] [Field L] [Algebra D L]
    [IsFractionRing D L] {E E' : Type} [AddCommGroup E] [Module D E] [AddCommGroup E'] [Module L E'] [Module D E']
    [IsScalarTower D L E'] (j : E →ₗ[D] E') (hj : IsBaseChange L j) :
    Module.finrank D E = Module.finrank L E' := by
  have : IsLocalizedModule (nonZeroDivisors D) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors D) L j).2 hj
  have h1 := IsLocalizedModule.rank_eq (nonZeroDivisors D) le_rfl j
  have h2 := IsLocalization.rank_eq L (N := E') (nonZeroDivisors D) le_rfl
  simp only [Module.finrank, h1, h2]

end GlobalTheory.CompanionTheory.Ar.LieRank

namespace GlobalTheory.CompanionTheory.Ar.LieRank

theorem exists_factor {X : Scheme.{0}} {A F : Type} [CommRing A] [Field F] (i₀ : Sp A ⟶ X) [IsOpenImmersion i₀]
    (y : Sp F ⟶ X) (h : genPt y ∈ Set.range i₀) : ∃ φ : A →+* F, spMap φ ≫ i₀ = y := by
  have hr : Set.range y ⊆ Set.range i₀ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint F := Subsingleton.elim _ _
    rw [hp]
    exact h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom, ?_⟩
  have e : spMap (Spec.preimage (IsOpenImmersion.lift i₀ y hr)).hom = IsOpenImmersion.lift i₀ y hr :=
    Spec.map_preimage _
  rw [e]
  exact IsOpenImmersion.lift_fac i₀ y hr

theorem genPt_comp {X : Scheme.{0}} {A F : Type} [CommRing A] [Field F] (i₀ : Sp A ⟶ X) (φ : A →+* F) :
    genPt (spMap φ ≫ i₀) = i₀ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint F)) := rfl

theorem finrank_fieldPt {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] {A F : Type} [CommRing A] [Field F]
    (i₀ : Sp A ⟶ S) {E Li : Type} [AddCommGroup E] [Module A E] [AddCommGroup Li] [Module F Li]
    (MA : LieModel G i₀ E) (φ : A →+* F) (M : LieModel G (spMap φ ≫ i₀) Li) :
    Module.finrank F Li = Module.rankAtStalk E (PrimeSpectrum.comap φ (IsLocalRing.closedPoint F)) := by
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective S G A i₀ E MA
  letI : Algebra A F := φ.toAlgebra
  letI : Module A Li := Module.compHom Li φ
  haveI : IsScalarTower A F Li := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := exists_lift G i₀ MA M
  exact finrank_of_isBaseChange j (GlobalTheory.T.lie_model_isBaseChange S G A F i₀ E Li MA M j hj) _

theorem finrank_eq_of_specializes {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (y₁ : Sp F₁ ⟶ X) (y₂ : Sp F₂ ⟶ X) (h : genPt y₁ ⤳ genPt y₂)
    {E₁ E₂ : Type} [AddCommGroup E₁] [Module F₁ E₁] [AddCommGroup E₂] [Module F₂ E₂]
    (M₁ : LieModel G y₁ E₁) (M₂ : LieModel G y₂ E₂) :
    Module.finrank F₁ E₁ = Module.finrank F₂ E₂ := by
  obtain ⟨U, hU, hqU, -⟩ := exists_isAffineOpen_mem_and_subset (x := genPt y₂) (U := ⊤) trivial
  have h₁U : genPt y₁ ∈ U := h.mem_open U.isOpen hqU
  have hr : Set.range hU.fromSpec = (U : Set X) := hU.range_fromSpec
  obtain ⟨φ₁, rfl⟩ := exists_factor (A := Γ(X, U)) hU.fromSpec y₁ (by rw [hr]; exact h₁U)
  obtain ⟨φ₂, rfl⟩ := exists_factor (A := Γ(X, U)) hU.fromSpec y₂ (by rw [hr]; exact hqU)
  obtain ⟨E, _, _, ⟨MA⟩⟩ := lieModel_exists X G Γ(X, U) hU.fromSpec
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective X G Γ(X, U) hU.fromSpec E MA
  haveI := Module.finitePresentation_of_projective Γ(X, U) E
  rw [finrank_fieldPt G _ MA φ₁ M₁, finrank_fieldPt G _ MA φ₂ M₂]
  rw [genPt_comp, genPt_comp] at h
  have hs := (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).1 h
  exact (hs.map (Module.isLocallyConstant_rankAtStalk (R := Γ(X, U)) (M := E)).continuous).eq

end GlobalTheory.CompanionTheory.Ar.LieRank

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_finrank_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V), Module.finrank (𝓞 L) V = Module.finrank Ω Li := by
  intro X Ω _ ξ hsp G _ _ _ Li _ _ M L _ _ z V _ _ MB
  obtain ⟨V', _, _, ⟨M'⟩⟩ := lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)
  letI : Module (𝓞 L) V' := Module.compHom V' (algebraMap (𝓞 L) L)
  haveI : IsScalarTower (𝓞 L) L V' := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := LieRank.exists_lift G z MB M'
  rw [LieRank.finrank_eq_of_isBaseChange_fractionRing j (GlobalTheory.T.lie_model_isBaseChange X G (𝓞 L) L z V V' MB M' j hj)]
  exact (LieRank.finrank_eq_of_specializes G ξ _ (hsp _) M M').symm

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelRankEqGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_rank_eq_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V), Module.finrank (𝓞 L) V = Module.finrank Ω Li := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq | exact GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingRegularPush
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingRegularPush
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg.Stalk

theorem regular_along_dominant : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i), IsCptGen ξ → (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → i a ∈ regAt ξ p) ∧ (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → unitAt ξ p (i a) → unitAt ξ₀ (pushCpt hd p) a) ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), genPt ξ ⤳ centre z → ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) := by
  intro X X₀ Ω Ω₀ _ _ ξ ξ₀ h i hd hc
  refine ⟨fun p a ha => ?_, fun p a ha hu => ?_, fun z a r hz hv => ?_⟩
  · obtain ⟨hh, h1, -⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X₀ Ω₀ ξ₀ X Ω ξ h i hd p
    exact h1 a ha
  · obtain ⟨hh, -, h2⟩ := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates X₀ Ω₀ ξ₀ X Ω ξ h i hd p
    exact h2 hc a ha hu
  · obtain ⟨h0, s, hs1, hs2⟩ := hv
    refine ⟨hz, (Scheme.Hom.stalkMap h (centre z)).hom s, ?_, ?_⟩
    · rw [GlobalTheory.CompanionTheory.Ar.RegAtDom.genMap_stalkMap hd (centre z) hz h0 s]
      exact congrArg i hs1
    · rw [Scheme.stalkClosedPointTo_comp] at hs2
      rw [← hs2]
      rfl

end GlobalTheory.CompanionTheory.Ar.Chg.Stalk
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingRegularPushStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominating_regular_push : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i), IsCptGen ξ → (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → i a ∈ regAt ξ p) ∧ (∀ (p : Cpt ξ) (a : Ω₀), a ∈ regAt ξ₀ (pushCpt hd p) → unitAt ξ p (i a) → unitAt ξ₀ (pushCpt hd p) a) ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), genPt ξ ⤳ centre z → ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.Stalk.regular_along_dominant | exact GlobalTheory.CompanionTheory.Ar.Chg.Stalk.regular_along_dominant | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.Stalk.regular_along_dominant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenAtComponentStalk
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenAtComponentStalk
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem mem_eigSp_iff_forall {R V O : Type} [CommRing R] [AddCommGroup V] [Module R V] [CommRing O]
    (ρ : O →+* Module.End R V) (τ : O →+* R) (u : V) :
    u ∈ eigSp ρ τ ↔ ∀ a, ρ a u = τ a • u := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem spMap_dualMap_id {A : Type} [CommRing A] : spMap (dualMap (RingHom.id A)) = 𝟙 _ := by
  have h : dualMap (RingHom.id A) = RingHom.id _ := RingHom.ext fun a => by
    show TrivSqZeroExt.inl (TrivSqZeroExt.fst a) + TrivSqZeroExt.inr (TrivSqZeroExt.snd a) = a
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq a
  rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem frame_of_stableEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (p : Cpt (Z.ξ₀ ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk p.1) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt (Y.X.fromSpecStalk p.1) ⟶ Y.t.G)), (genMap (Z.ξ₀ ≫ Y.j) p).comp κ = Z.inc → StableEig Y.t (Y.X.fromSpecStalk p.1) κ σ e → ∃ b : Fin r → Z.V, (∀ i, Z.M.Extends p (b i) (e i)) ∧ (Z.eig σ).IsFrameAt b p := by
  classical
  intro E _ _ _ H D l Xo c U O _ β Y Z p κ σ r e hκ hs
  obtain ⟨F, _, _, ⟨MA⟩⟩ := lieModel_exists Y.X Y.t.G (Y.X.presheaf.stalk p.1) (Y.X.fromSpecStalk p.1)
  obtain ⟨ρA, hρA, -⟩ := lieModel_exists_unique_act Y.X Y.t.G (Y.X.presheaf.stalk p.1) (Y.X.fromSpecStalk p.1) F MA (𝓞 E)
    Y.t.act.act Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  have hg : spMap (genMap (Z.ξ₀ ≫ Y.j) p) ≫ Y.X.fromSpecStalk p.1 = Z.ξ₀ ≫ Y.j := LieTangent.spec_genMap _ p
  obtain ⟨j, hj⟩ := LieVB.exists_tr (A := Y.X.presheaf.stalk p.1) (Y.X.fromSpecStalk p.1) (Z.ξ₀ ≫ Y.j) (genMap (Z.ξ₀ ≫ Y.j) p) hg MA Z.M
  have h0 : IsEigFrame Y.t.act (Y.X.fromSpecStalk p.1) (((RingHom.id _).comp κ).comp (tauIn c σ)) e :=
    hs _ (RingHom.id _) _ (by simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]; exact Category.id_comp _) e (fun i => by rw [spMap_dualMap_id, Category.id_comp])
  choose f hf using fun i => MA.onto (e i) (h0.1 i).1
  have hfe : (fun k => MA.pt (f k)) = e := funext hf
  have hfr := ((GlobalTheory.T.lie_model_eigenvectors_action Y.X (Y.X.presheaf.stalk p.1) Y.t.G (Y.X.fromSpecStalk p.1) F MA).2 (𝓞 E) Y.t.act ρA
    (((RingHom.id _).comp κ).comp (tauIn c σ)) hρA).2 r f
  rw [hfe] at hfr
  obtain ⟨-, hfs⟩ := hfr.1 h0
  have hb : ∀ i, (Z.M.pt (j (f i))).left = spMap (dualMap (genMap (Z.ξ₀ ≫ Y.j) p)) ≫ (e i).left :=
    fun i => by rw [hj, hf]
  have hext : ∀ i, Z.M.Extends p (j (f i)) (e i) := fun i => ⟨(h0.1 i).1, hb i⟩
  have h1 : IsEigFrame Y.t.act (Z.ξ₀ ≫ Y.j) (((genMap (Z.ξ₀ ≫ Y.j) p).comp κ).comp (tauIn c σ))
      (fun i => Z.M.pt (j (f i))) := hs _ _ _ hg _ hb
  rw [hκ] at h1
  obtain ⟨hbi, hbs⟩ := (((GlobalTheory.T.lie_model_eigenvectors_action Y.X Z.Ω Y.t.G (Z.ξ₀ ≫ Y.j) Z.V Z.M).2 (𝓞 E) Y.t.act Z.ρ
    (Z.inc.comp (tauIn c σ)) Z.act).2 r fun i => j (f i)).1 h1
  refine ⟨fun i => j (f i), hext, hbi, le_antisymm ?_ (Submodule.span_le.2 ?_)⟩
  · intro e' he'
    obtain ⟨hl, hE⟩ : e' ∈ Z.M.lat p ∧ e' ∈ eigSp Z.ρ (Z.inc.comp (tauIn c σ)) := he'
    obtain ⟨v, hv⟩ := (Z.M.mem_lat_iff p e').1 hl
    obtain ⟨w, rfl⟩ := MA.onto v hv.1
    have hw : e' = j w := LieVB.pt_left_inj Z.M (hv.2.trans (hj w).symm)
    letI : Algebra c.F (Y.X.presheaf.stalk p.1) := κ.toAlgebra
    letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
    obtain ⟨ft, ⟨hft1, hft2⟩, -⟩ := GlobalTheory.Frames.existsUnique_eigen_sum E H l c (Y.X.presheaf.stalk p.1) F ρA w
    have hint : ∀ a y, Z.ρ a (j y) = j (ρA a y) := fun a y => LieVB.pt_left_inj Z.M (by
      have h2 := congrArg (fun q => q.left) (Z.act a (j y))
      have h3 := congrArg (fun q => q.left) (hρA a y)
      simp only [Over.comp_left] at h2 h3
      rw [h2, hj, hj, h3, Category.assoc])
    obtain ⟨_, -, huq⟩ := GlobalTheory.Frames.existsUnique_eigen_sum E H l c Z.Ω Z.V Z.ρ e'
    have e1 := huq (fun τ => j (ft τ)) ⟨fun τ a => by
      show Z.ρ a (j (ft τ)) = _
      rw [hint, hft1, j.map_smulₛₗ]
      show (genMap (Z.ξ₀ ≫ Y.j) p) (κ _) • _ = Z.inc _ • _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hκ]; rfl, by rw [← map_sum, hft2, hw]⟩
    have e2 := huq (fun τ => if τ = σ then e' else 0) ⟨fun τ a => by
      by_cases h : τ = σ
      · subst h
        simp only [if_true]
        exact (mem_eigSp_iff_forall _ _ _).1 hE a
      · simp [h], by simp⟩
    have e3 : j (ft σ) = e' := by simpa using congrFun (e1.trans e2.symm) σ
    have hmem : ft σ ∈ eigSp ρA (((RingHom.id _).comp κ).comp (tauIn c σ)) :=
      (mem_eigSp_iff_forall _ _ _).2 fun a => hft1 σ a
    rw [← hfs] at hmem
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e3, ← ha, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [j.map_smulₛₗ]
    exact Submodule.smul_mem _ (⟨genMap (Z.ξ₀ ≫ Y.j) p (a i), _, rfl⟩ : regAt (Z.ξ₀ ≫ Y.j) p)
      (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact ⟨(Z.M.mem_lat_iff p _).2 ⟨_, hext i⟩, hbs ▸ Submodule.subset_span ⟨i, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenAtComponentStalkStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_eigen_at_component_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (p : Cpt (Z.ξ₀ ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk p.1) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt (Y.X.fromSpecStalk p.1) ⟶ Y.t.G)), (genMap (Z.ξ₀ ≫ Y.j) p).comp κ = Z.inc → StableEig Y.t (Y.X.fromSpecStalk p.1) κ σ e → ∃ b : Fin r → Z.V, (∀ i, Z.M.Extends p (b i) (e i)) ∧ (Z.eig σ).IsFrameAt b p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig | exact GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.frame_of_stableEig <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairLatticeSumComap
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairLatticeSumComap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeSum

section LinearAlgebra

open Submodule

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]

theorem range_append {α : Type} {r s : ℕ} (f : Fin r → α) (g : Fin s → α) :
    Set.range (Fin.append f g) = Set.range f ∪ Set.range g := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · exact Or.inl ⟨i, by simp⟩
    · exact Or.inr ⟨i, by simp⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd s i, by simp⟩
    · exact ⟨Fin.natAdd r i, by simp⟩

theorem linearIndependent_append {r s : ℕ} {f : Fin r → V} {g : Fin s → V} (hf : LinearIndependent Ω f)
    (hg : LinearIndependent Ω g) (hd : Disjoint (span Ω (Set.range f)) (span Ω (Set.range g))) :
    LinearIndependent Ω (Fin.append f g) := by
  have h := hf.sum_type hg hd
  have e : Fin.append f g = Sum.elim f g ∘ finSumFinEquiv.symm := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp
  rw [e]
  exact h.comp _ finSumFinEquiv.symm.injective

theorem span_lift_eq_top {W : Submodule Ω V} {n : ℕ} {v : Fin n → V} {c : Fin n → W} (hc : ∀ k, (c k : V) = v k)
    (hv : span Ω (Set.range v) = W) : span Ω (Set.range c) = ⊤ := by
  apply Submodule.map_injective_of_injective W.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  have e : (W.subtype ∘ c) = v := funext hc
  rw [show (⇑W.subtype ∘ c) = v from e, hv]

theorem comap_sup_span (A : Subring Ω) {W : Submodule Ω V} {r s : ℕ} {f : Fin r → V} {g : Fin s → V}
    {c : Fin (r + s) → W} (hc : ∀ k, (c k : V) = Fin.append f g k) :
    (span A (Set.range f) ⊔ span A (Set.range g)).comap (W.subtype.restrictScalars A) =
      span A (Set.range c) := by
  have hinj : Function.Injective (W.subtype.restrictScalars A) := W.injective_subtype
  have e : span A (Set.range f) ⊔ span A (Set.range g) =
      (span A (Set.range c)).map (W.subtype.restrictScalars A) := by
    rw [Submodule.map_span, ← Set.range_comp, ← Submodule.span_union, ← range_append]
    congr 2
    exact funext fun k => (hc k).symm
  rw [e, Submodule.comap_map_eq_of_injective hinj]

end LinearAlgebra

end GlobalTheory.CompanionTheory.Ar.HodgeSum

theorem GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H), a ≠ b → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsVB (labelRk D a + labelRk D b) ⊤ := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 a b hab
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, -, -, -, -, hind, -⟩ :=
    GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω K J y 𝔐 hβ
  have hdisj : Disjoint (𝔐.Vgen a) (𝔐.Vgen b) := hind.pairwiseDisjoint hab
  intro p _
  obtain ⟨Ua, hpa, f, hfs, hff⟩ := 𝔐.vb a p (Set.mem_univ _)
  obtain ⟨Ub, hpb, g, hgs, hgf⟩ := 𝔐.vb b p (Set.mem_univ _)
  have hfs' : Submodule.span Ω (Set.range f) = 𝔐.Vgen a := hfs
  have hgs' : Submodule.span Ω (Set.range g) = 𝔐.Vgen b := hgs
  have hspan : Submodule.span Ω (Set.range (Fin.append f g)) = 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
    rw [HodgeSum.range_append, Submodule.span_union, hfs', hgs']
  have hmem : ∀ k, Fin.append f g k ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := fun k => by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self k)
  have hli : LinearIndependent Ω (Fin.append f g) :=
    HodgeSum.linearIndependent_append (hff p (Set.mem_univ _) hpa).1 (hgf p (Set.mem_univ _) hpb).1
      (by rw [hfs', hgs']; exact hdisj)
  refine ⟨Ua ⊓ Ub, ⟨hpa, hpb⟩, fun k => ⟨Fin.append f g k, hmem k⟩,
    HodgeSum.span_lift_eq_top (fun _ => rfl) hspan, fun q _ hq => ⟨?_, ?_⟩⟩
  · exact LinearIndependent.of_comp (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype hli
  · have h1 : 𝔐.V a q = Submodule.span (regAt 𝔐.ξ q) (Set.range f) := (hff q (Set.mem_univ _) hq.1).2
    have h2 : 𝔐.V b q = Submodule.span (regAt 𝔐.ξ q) (Set.range g) := (hgf q (Set.mem_univ _) hq.2).2
    show (𝔐.V a q ⊔ 𝔐.V b q).comap ((𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype.restrictScalars (regAt 𝔐.ξ q)) = _
    rw [h1, h2]
    exact HodgeSum.comap_sup_span (regAt 𝔐.ξ q) fun _ => rfl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairLatticeSumComapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_lattice_sum_comap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H), a ≠ b → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsVB (labelRk D a + labelRk D b) ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup | exact GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisAdjoinInverse
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisAdjoinInverse
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem differentials_basis_invAdj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 → ∀ (e : ℕ) (z : Fin e → A) (z' : Fin e → Mdl.invAdj A g), (∀ i, (z' i : Ω) = z i) → LinearIndependent A (fun i => KaehlerDifferential.D ℚ A (z i)) → Submodule.span A (Set.range fun i => KaehlerDifferential.D ℚ A (z i)) = ⊤ → LinearIndependent (Mdl.invAdj A g) (fun i => KaehlerDifferential.D ℚ (Mdl.invAdj A g) (z' i)) ∧ Submodule.span (Mdl.invAdj A g) (Set.range fun i => KaehlerDifferential.D ℚ (Mdl.invAdj A g) (z' i)) = ⊤ := by
  intro Ω _ _ A g hg hg0 e z z' hz hli hsp
  have hAB : A ≤ Mdl.invAdj A g := fun x hx =>
    show x ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) from
      Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
  have hginv : g⁻¹ ∈ Mdl.invAdj A g :=
    show g⁻¹ ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) from
      Algebra.subset_adjoin (Set.mem_insert _ _)
  have hden : ∀ x ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)), ∃ n : ℕ, x * g ^ n ∈ A := by
    let S : Subalgebra ℚ Ω :=
      { carrier := {x | ∃ n : ℕ, x * g ^ n ∈ A}
        mul_mem' := by
          rintro x y ⟨n, hn⟩ ⟨m, hm⟩
          refine ⟨n + m, ?_⟩
          rw [show x * y * g ^ (n + m) = (x * g ^ n) * (y * g ^ m) by ring]
          exact A.mul_mem hn hm
        one_mem' := ⟨0, by simpa using A.one_mem⟩
        add_mem' := by
          rintro x y ⟨n, hn⟩ ⟨m, hm⟩
          refine ⟨n + m, ?_⟩
          rw [show (x + y) * g ^ (n + m) = (x * g ^ n) * g ^ m + (y * g ^ m) * g ^ n by ring]
          exact A.add_mem (A.mul_mem hn (A.pow_mem hg m)) (A.mul_mem hm (A.pow_mem hg n))
        zero_mem' := ⟨0, by simpa using A.zero_mem⟩
        algebraMap_mem' := fun r => ⟨0, by simpa using A.algebraMap_mem r⟩ }
    have hle : Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) ≤ S := by
      refine Algebra.adjoin_le ?_
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hg0]; exact A.one_mem⟩
      · exact ⟨0, by simpa using hx⟩
    exact fun x hx => hle hx
  letI : Algebra A (Mdl.invAdj A g) := (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  have hinc : ∀ a : A, ((algebraMap A (Mdl.invAdj A g) a : Mdl.invAdj A g) : Ω) = a := fun _ => rfl
  haveI : IsScalarTower ℚ A (Mdl.invAdj A g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  let g' : A := ⟨g, hg⟩
  haveI : IsLocalization (Submonoid.powers g') (Mdl.invAdj A g) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      have hu : IsUnit (algebraMap A (Mdl.invAdj A g) g') :=
        isUnit_iff_exists_inv.mpr ⟨⟨g⁻¹, hginv⟩, Subtype.ext (by
          show g * g⁻¹ = 1
          exact mul_inv_cancel₀ hg0)⟩
      show IsUnit (algebraMap A (Mdl.invAdj A g) (g' ^ n))
      rw [map_pow]
      exact hu.pow n
    · intro b
      obtain ⟨n, hn⟩ := hden b b.2
      refine ⟨(⟨(b : Ω) * g ^ n, hn⟩, ⟨g' ^ n, n, rfl⟩), ?_⟩
      apply Subtype.ext
      show (b : Ω) * ((g' ^ n : A) : Ω) = (b : Ω) * g ^ n
      simp only [SubmonoidClass.coe_pow]
      rfl
    · intro x y h
      refine ⟨1, ?_⟩
      have hxy : x = y := Subtype.ext (by simpa [hinc] using congrArg Subtype.val h)
      rw [hxy]
  haveI : Algebra.FormallyEtale A (Mdl.invAdj A g) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g')
  have hzz : ∀ i, algebraMap A (Mdl.invAdj A g) (z i) = z' i := fun i =>
    Subtype.ext ((hinc (z i)).trans (hz i).symm)
  have key := GlobalTheory.CompanionTheory.Ar.SncRes.coords_of_formallyEtale (S := ↥(Mdl.invAdj A g)) z hli hsp
  simp only [hzz] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisAdjoinInverseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_basis_adjoin_inverse : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 → ∀ (e : ℕ) (z : Fin e → A) (z' : Fin e → Mdl.invAdj A g), (∀ i, (z' i : Ω) = z i) → LinearIndependent A (fun i => KaehlerDifferential.D ℚ A (z i)) → Submodule.span A (Set.range fun i => KaehlerDifferential.D ℚ A (z i)) = ⊤ → LinearIndependent (Mdl.invAdj A g) (fun i => KaehlerDifferential.D ℚ (Mdl.invAdj A g) (z' i)) ∧ Submodule.span (Mdl.invAdj A g) (Set.range fun i => KaehlerDifferential.D ℚ (Mdl.invAdj A g) (z' i)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.differentials_basis_invAdj | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.differentials_basis_invAdj | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.differentials_basis_invAdj <;> assumption)
end
end
