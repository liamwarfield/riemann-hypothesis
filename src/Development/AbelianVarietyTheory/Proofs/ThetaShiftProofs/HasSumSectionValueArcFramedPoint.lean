module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumThetaGeneratorChartRatio

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChartCoordinatesHasSum
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChartCoordinatesHasSum
noncomputable section

namespace GlobalTheory.ArcPoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Conv GlobalTheory.Points
open scoped LaurentSeries PowerSeries

def upI : Filter ℂ := comap Complex.im atTop

theorem eventually_upI {p : ℂ → Prop} : (∀ᶠ w in upI, p w) ↔ ∃ T : ℝ, ∀ w : ℂ, T < w.im → p w := by
  rw [upI, eventually_comap]
  constructor
  · intro h
    obtain ⟨T, hT⟩ := eventually_atTop.1 h
    exact ⟨T, fun w hw => hT _ hw.le w rfl⟩
  · rintro ⟨T, hT⟩
    filter_upwards [eventually_gt_atTop T] with t ht w hw using hT w (hw ▸ ht)

def sumRing (w : ℂ) : Subring (ℂ⸨X⸩ × ℂ) where
  carrier := {q | HasSum (fun m : ℤ => q.1.coeff m * eTwoPi w ^ m) q.2}
  mul_mem' {a b} ha hb := by
    have h := hasSum_mul_laurent (eTwoPi_ne_zero w) ha.summable hb.summable
    rw [lsum, lsum, ha.tsum_eq, hb.tsum_eq] at h
    exact h
  one_mem' := by simpa using hasSum_single_laurent 0 1 (eTwoPi w)
  add_mem' {a b} ha hb := by simpa [add_mul] using HasSum.add ha hb
  zero_mem' := by simpa using hasSum_zero
  neg_mem' {a} ha := by simpa using HasSum.neg ha

theorem mem_sumRing {w : ℂ} {s : ℂ⸨X⸩} {x : ℂ} :
    (s, x) ∈ sumRing w ↔ HasSum (fun m : ℤ => s.coeff m * eTwoPi w ^ m) x := Iff.rfl

theorem add_mem_sumRing {w : ℂ} {s t : ℂ⸨X⸩} {x y : ℂ} (h : (s, x) ∈ sumRing w)
    (h' : (t, y) ∈ sumRing w) : (s + t, x + y) ∈ sumRing w := by
  rw [← Prod.mk_add_mk]
  exact add_mem h h'

theorem mul_mem_sumRing {w : ℂ} {s t : ℂ⸨X⸩} {x y : ℂ} (h : (s, x) ∈ sumRing w)
    (h' : (t, y) ∈ sumRing w) : (s * t, x * y) ∈ sumRing w := by
  rw [← Prod.mk_mul_mk]
  exact mul_mem h h'

theorem neg_mem_sumRing {w : ℂ} {s : ℂ⸨X⸩} {x : ℂ} (h : (s, x) ∈ sumRing w) :
    (-s, -x) ∈ sumRing w := by
  rw [← Prod.neg_mk]
  exact neg_mem h

theorem mem_sumRing_coe {w : ℂ} {s : ℂ⟦X⟧} {x : ℂ} :
    (HahnSeries.ofPowerSeries ℤ ℂ s, x) ∈ sumRing w ↔ SumsAt s w x := sumsAt_iff.symm

theorem mem_convLaurent_of_eventually {s : ℂ⸨X⸩} {v : ℂ → ℂ}
    (h : ∀ᶠ w in upI, (s, v w) ∈ sumRing w) : s ∈ convLaurent := by
  obtain ⟨T, hT⟩ := eventually_upI.1 h
  exact mem_convLaurent_iff_halfRing.2 ⟨T, fun w hw => (mem_sumRing.1 (hT w hw)).summable⟩

theorem eventually_ne_zero {s : ℂ⸨X⸩} {v : ℂ → ℂ}
    (h : ∀ᶠ w in upI, (s, v w) ∈ sumRing w) (h0 : s ≠ 0) : ∀ᶠ w in upI, v w ≠ 0 := by
  filter_upwards [h, eventually_upI.2
    (exists_lsum_eTwoPi_ne_zero (mem_convLaurent_of_eventually h) h0)] with w h1 h2
  rwa [lsum, (mem_sumRing.1 h1).tsum_eq] at h2

theorem eventually_of_mul {s t : ℂ⸨X⸩} {v u : ℂ → ℂ}
    (hst : ∀ᶠ w in upI, (s * t, v w * u w) ∈ sumRing w) (ht : ∀ᶠ w in upI, (t, u w) ∈ sumRing w)
    (h0 : t ≠ 0) : ∀ᶠ w in upI, (s, v w) ∈ sumRing w := by
  have hs : s ∈ convLaurent := by
    have := mul_mem (mem_convLaurent_of_eventually hst)
      (convLaurent.inv_mem (mem_convLaurent_of_eventually ht))
    rwa [mul_inv_cancel_right₀ h0] at this
  obtain ⟨T, hT⟩ := mem_convLaurent_iff_halfRing.1 hs
  filter_upwards [hst, ht, eventually_ne_zero ht h0, eventually_upI.2 ⟨T, hT⟩] with w h1 h2 h3 h4
  have h5 : (s, lsum s (eTwoPi w)) ∈ sumRing w := h4.hasSum
  have h6 := (mem_sumRing.1 (mul_mem_sumRing h5 h2)).unique (mem_sumRing.1 h1)
  rwa [mul_right_cancel₀ h3 h6] at h5

theorem eventually_of_affine {Z : Scheme.{0}} (y : Sp ℂ⸨X⸩ ⟶ Z) (z : ℂ → (Sp ℂ ⟶ Z))
    {U : Z.Opens} (hU : IsAffineOpen U) (hy : ⊤ ≤ y ⁻¹ᵁ U) (hz : ∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ U)
    (hf : ∀ f : Γ(Z, U), ∀ᶠ w in upI, (valR y U f, valR (z w) U f) ∈ sumRing w)
    {V : Z.Opens} (hV : ⊤ ≤ y ⁻¹ᵁ V) :
    (∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ V) ∧
      ∀ f : Γ(Z, V), ∀ᶠ w in upI, (valR y V f, valR (z w) V f) ∈ sumRing w := by
  let p : PrimeSpectrum ℂ⸨X⸩ := default
  obtain ⟨h, hle, hp⟩ := hU.exists_basicOpen_le (V := V) ⟨y p, hV (x := p) trivial⟩
    (hy (x := p) trivial)
  have hyh : ⊤ ≤ y ⁻¹ᵁ Z.basicOpen h := by
    intro q _
    obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum ℂ⸨X⸩) _ _
    exact hp
  have h0 : valR y U h ≠ 0 := ((le_preimage_basicOpen_iff y hy h).1 hyh).ne_zero
  have hzh : ∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ Z.basicOpen h := by
    filter_upwards [hz, eventually_ne_zero (hf h) h0] with w h1 h2
    exact (le_preimage_basicOpen_iff _ h1 h).2 h2.isUnit
  refine ⟨hzh.mono fun w hw => le_preimage_mono _ hle hw, fun f => ?_⟩
  haveI := hU.isLocalization_basicOpen h
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj h ((Z.presheaf.map (homOfLE hle).op).hom f)
  have hb' : (Z.presheaf.map (homOfLE hle).op).hom f *
      (Z.presheaf.map (homOfLE (Z.basicOpen_le h)).op).hom h ^ n =
      (Z.presheaf.map (homOfLE (Z.basicOpen_le h)).op).hom b := hb
  have key : ∀ {C : Type} [CommRing C] (x : Sp C ⟶ Z), ⊤ ≤ x ⁻¹ᵁ Z.basicOpen h →
      valR x V f * valR x U h ^ n = valR x U b := by
    intro C _ x hx
    rw [← valR_res x hle hx, ← valR_res x (Z.basicOpen_le h) hx, ← valR_res x (Z.basicOpen_le h) hx,
      ← valR_pow x _ hx, ← valR_mul x _ hx, hb']
  refine eventually_of_mul (t := valR y U h ^ n) (u := fun w => valR (z w) U h ^ n) ?_ ?_
    (pow_ne_zero n h0)
  · filter_upwards [hzh, hf b] with w h1 h2
    rwa [key y hyh, key _ h1]
  · filter_upwards [hf h] with w h1 using pow_mem h1 n

theorem eventually_of_isPullback {Y Z : Scheme.{0}} {O F : Type} [CommRing O] [CommRing F]
    {β : O →+* F} {g : Z ⟶ Y} {s : Y ⟶ Sp O} {t : Z ⟶ Sp F} (H : IsPullback g t s (spMap β))
    (y : Sp ℂ⸨X⸩ ⟶ Z) (z : ℂ → (Sp ℂ ⟶ Z)) (σ : F →+* ℂ) (τ : F →+* ℂ⸨X⸩)
    (hτ : ∀ x, τ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (σ x)))
    (hyt : y ≫ t = spMap τ) (hzt : ∀ᶠ w in upI, z w ≫ t = spMap σ)
    {U : Y.Opens} (hU : IsAffineOpen U) (hy : ⊤ ≤ (y ≫ g) ⁻¹ᵁ U)
    (hz : ∀ᶠ w in upI, ⊤ ≤ (z w ≫ g) ⁻¹ᵁ U)
    (hf : ∀ f : Γ(Y, U), ∀ᶠ w in upI, (valR (y ≫ g) U f, valR (z w ≫ g) U f) ∈ sumRing w)
    {V : Z.Opens} (hV : ⊤ ≤ y ⁻¹ᵁ V) :
    (∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ V) ∧
      ∀ f : Γ(Z, V), ∀ᶠ w in upI, (valR y V f, valR (z w) V f) ∈ sumRing w := by
  haveI : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := g ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hy' : ⊤ ≤ y ⁻¹ᵁ (g ⁻¹ᵁ U) := hy
  have hz' : ∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ (g ⁻¹ᵁ U) := hz
  refine eventually_of_affine y z (hU.preimage g) hy' hz' (fun r => ?_) hV
  have hr := (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top r)
  induction hr using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · filter_upwards [hz', hf a] with w h1 h2
      rwa [valR_appLE _ _ _ hy', valR_appLE _ _ _ h1]
    · obtain ⟨b, rfl⟩ :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective b
      filter_upwards [hz', hzt] with w h1 h2
      rw [valR_appLE _ _ _ hy', valR_appLE _ _ _ h1, hyt, h2]
      have e1 := valR_specMap (CommRingCat.ofHom τ) b
      have e2 := valR_specMap (CommRingCat.ofHom σ) b
      have e3 : (τ b, σ b) ∈ sumRing w := by
        rw [hτ]
        exact mem_sumRing_coe.2 (hasSum_C _ _)
      exact (congrArg (· ∈ sumRing w) (congrArg₂ Prod.mk e1 e2)).mpr e3
  | zero =>
    filter_upwards [hz'] with w h1
    rw [valR_zero _ _ hy', valR_zero _ _ h1]
    exact zero_mem _
  | one =>
    filter_upwards [hz'] with w h1
    rw [valR_one _ _ hy', valR_one _ _ h1]
    exact one_mem _
  | add a b _ _ ha hb =>
    filter_upwards [hz', ha, hb] with w h1 h2 h3
    rw [valR_add _ _ hy', valR_add _ _ h1]
    exact add_mem_sumRing h2 h3
  | neg a _ ha =>
    filter_upwards [hz', ha] with w h1 h2
    rw [valR_neg _ _ hy', valR_neg _ _ h1]
    exact neg_mem_sumRing h2
  | mul a b _ _ ha hb =>
    filter_upwards [hz', ha, hb] with w h1 h2 h3
    rw [valR_mul _ _ hy', valR_mul _ _ h1]
    exact mul_mem_sumRing h2 h3

theorem eventually_chart {Z : Scheme.{0}} {F R : Type} [CommRing F] [CommRing R] [Algebra F R]
    [Algebra.FiniteType F R] (t : Z ⟶ Sp F) (k : Sp R ⟶ Z) [IsOpenImmersion k]
    (hk : k ≫ t = spMap (algebraMap F R)) (φ : R →+* ℂ⸨X⸩) (σ : F →+* ℂ)
    (hφ : ∀ x, φ (algebraMap F R x) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (σ x)))
    (z : ℂ → (Sp ℂ ⟶ Z)) (hzt : ∀ᶠ w in upI, z w ≫ t = spMap σ)
    (hz : ∀ᶠ w in upI, ⊤ ≤ z w ⁻¹ᵁ k.opensRange)
    (hf : ∀ f : Γ(Z, k.opensRange), ∀ᶠ w in upI,
      (valR (spMap φ ≫ k) k.opensRange f, valR (z w) k.opensRange f) ∈ sumRing w) :
    ∀ᶠ w in upI, ∃ ψ : R →+* ℂ, spMap ψ ≫ k = z w ∧ (∀ x, ψ (algebraMap F R x) = σ x) ∧
      ∀ f, (φ f, ψ f) ∈ sumRing w := by
  have e : ⊤ ≤ k ⁻¹ᵁ k.opensRange := k.preimage_opensRange.ge
  have hsurj : ∀ r : R, ∃ f : Γ(Z, k.opensRange), ∀ {C : Type} [CommRing C] (ψ : R →+* C),
      valR (spMap ψ ≫ k) k.opensRange f = ψ r := by
    intro r
    have hiso : IsIso (k.appLE k.opensRange ⊤ e) := by
      have := k.isIso_app k.opensRange le_rfl
      rw [Scheme.Hom.appLE]
      have : IsIso (homOfLE e) := (isIso_iff_of_thin _).2 ⟨homOfLE le_top⟩
      infer_instance
    obtain ⟨f, hf⟩ := (asIso (k.appLE k.opensRange ⊤ e)).commRingCatIsoToRingEquiv.surjective
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
    refine ⟨f, fun ψ => ?_⟩
    rw [← valR_appLE _ k e (le_preimage_top _)]
    exact (congrArg (valR (spMap ψ) ⊤) hf).trans (valR_specMap (CommRingCat.ofHom ψ) r)
  choose sec hsec using hsurj
  obtain ⟨S, hS⟩ := Algebra.FiniteType.out (R := F) (A := R)
  filter_upwards [hzt, hz, (eventually_all_finset S).2 fun r _ => hf (sec r)] with w h1 h2 h3
  have hr : Set.range (z w) ⊆ Set.range k := by
    rintro _ ⟨q, rfl⟩
    exact h2 (x := q) trivial
  let ψ : R →+* ℂ := (Spec.preimage (IsOpenImmersion.lift k (z w) hr)).hom
  have hψ : spMap ψ ≫ k = z w := by
    rw [← IsOpenImmersion.lift_fac k (z w) hr]
    congr 1
    exact Spec.map_preimage _
  have hσ : ∀ x, ψ (algebraMap F R x) = σ x := by
    rw [← hψ, Category.assoc, hk, ← Spec.map_comp] at h1
    exact fun x => congrArg (fun a => a.hom x) (Spec.map_injective h1)
  refine ⟨ψ, hψ, hσ, fun f => ?_⟩
  have hf' : f ∈ Algebra.adjoin F (S : Set R) := hS.ge Algebra.mem_top
  induction hf' using Algebra.adjoin_induction with
  | mem r hr' =>
    have := h3 r hr'
    rwa [← hψ, hsec, hsec] at this
  | algebraMap x =>
    rw [hφ, hσ]
    exact mem_sumRing_coe.2 (hasSum_C _ _)
  | add a b _ _ ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem_sumRing ha hb
  | mul a b _ _ ha hb =>
    rw [map_mul, map_mul]
    exact mul_mem_sumRing ha hb

end GlobalTheory.ArcPoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem GlobalTheory.ArcPoint.chart_coordinates_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (φ : p.R →ₐ[c.F] ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → IsOpenImmersion j → j ≫ pullback.snd _ _ = spMap (algebraMap c.F p.R) → spMap φ.toRingHom ≫ j ≫ Y.j = spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∃ ψ : p.R →ₐ[c.F] CAt σ, spMap ψ.toRingHom ≫ j ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ ∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi w ^ m) (Formalism.L2.Pj.toC (ψ f)) := by
  intro E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ p j φ hσ hχ _ hj hjs hφ
  have hex : ∀ w : ℂ, Ha.T < w.im → ∃ yF : Sp ℂ ⟶ Xo.XF c,
      yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ yF ≫ pullback.snd _ _ = spMap σ := by
    intro w hw
    refine ⟨pullback.lift (Fu.u Ha.i (Ha.Pw w)) (spMap σ) ?_, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
    rw [Fu.over_σ _ _ (Ha.period w hw), ← Spec.map_comp]
    rfl
  have hex' : ∀ w : ℂ, ∃ yF : Sp ℂ ⟶ Xo.XF c, Ha.T < w.im →
      yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ yF ≫ pullback.snd _ _ = spMap σ := by
    intro w
    by_cases hw : Ha.T < w.im
    · obtain ⟨yF, h⟩ := hex w hw
      exact ⟨yF, fun _ => h⟩
    · obtain ⟨yF, -⟩ := hex (((Ha.T + 1 : ℝ) : ℂ) * Complex.I) (by simp)
      exact ⟨yF, fun h => absurd h hw⟩
  choose yF hyF using hex'
  have hyF' := GlobalTheory.ArcPoint.eventually_upI.2 ⟨Ha.T, hyF⟩
  haveI := Y.jQ_open
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y.X) (U := ⊤)
    (x := χ (IsLocalRing.closedPoint (PowerSeries ℂ))) trivial
  have hχU : ⊤ ≤ χ ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of (PowerSeries ℂ)) χ hxU).ge
  have hpt : ∀ f : Γ(Y.X, U), ∀ᶠ w in GlobalTheory.ArcPoint.upI, ⊤ ≤ (yF w ≫ Y.j) ⁻¹ᵁ U ∧
      SumsAt (valR χ U f) w (valAt' (yF w ≫ Y.j) U f) := by
    intro f
    filter_upwards [hyF', GlobalTheory.ArcPoint.eventually_upI.2 (Ha.point U f hχU)] with w h1 h2
    exact h2 _ h1.1 h1.2
  have hk : (j ≫ Y.jQ) ≫ pullback.snd _ _ = spMap (algebraMap c.F p.R) := by
    rw [Category.assoc, Y.jQ_over, hjs]
  have hφσ : ∀ x, φ.toRingHom (algebraMap c.F p.R x) =
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (σ x)) := fun x => (φ.commutes x).trans (hσ x)
  have hzt : ∀ᶠ w in GlobalTheory.ArcPoint.upI, (yF w ≫ Y.jQ) ≫ pullback.snd _ _ = spMap σ :=
    hyF'.mono fun w h => by rw [Category.assoc, Y.jQ_over, h.2]
  have hφ' : (spMap φ.toRingHom ≫ j ≫ Y.jQ) ≫ pullback.fst _ _ =
      spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ := by
    rw [← hφ]
    simp only [Category.assoc, Model.j]
  have hz' : ∀ w, (yF w ≫ Y.jQ) ≫ pullback.fst _ _ = yF w ≫ Y.j := fun w => Category.assoc _ _ _
  obtain ⟨h1, h2⟩ := GlobalTheory.ArcPoint.eventually_of_isPullback (IsPullback.of_hasPullback Y.s (spMap β))
    (spMap φ.toRingHom ≫ j ≫ Y.jQ) (fun w => yF w ≫ Y.jQ) σ
    (φ.toRingHom.comp (algebraMap c.F p.R)) hφσ
    (by rw [Category.assoc, hk, ← Spec.map_comp]; rfl) hzt hU
    (by rw [hφ']; exact fun q _ => hχU (x := spMap _ q) trivial)
    ((hpt 0).mono fun w h => by rw [hz']; exact h.1)
    (fun f => (hpt f).mono fun w h => by
      rw [hφ', hz', GlobalTheory.Points.valR_spMap_comp _ _ _ hχU]
      exact GlobalTheory.ArcPoint.mem_sumRing_coe.2 h.2)
    (V := (j ≫ Y.jQ).opensRange) (fun q _ => ⟨spMap φ.toRingHom q, rfl⟩)
  have h3 := GlobalTheory.ArcPoint.eventually_chart (pullback.snd Y.s (spMap β)) (j ≫ Y.jQ) hk φ.toRingHom σ
    hφσ (fun w => yF w ≫ Y.jQ) hzt h1 h2
  refine GlobalTheory.ArcPoint.eventually_upI.1 ?_
  filter_upwards [h3, hyF'] with w ⟨ψ, e1, e2, e3⟩ h
  refine ⟨{ toRingHom := (show p.R →+* CAt σ from ψ), commutes' := e2 }, ?_, e3⟩
  have e4 : spMap ψ ≫ j = yF w := by
    rw [← cancel_mono Y.jQ, Category.assoc]
    exact e1
  have e5 : spMap ψ ≫ j ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) := by
    rw [← Category.assoc, e4, h.1]
  exact e5
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChartCoordinatesHasSumStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holArc_chart_coordinates_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (φ : p.R →ₐ[c.F] ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → IsOpenImmersion j → j ≫ pullback.snd _ _ = spMap (algebraMap c.F p.R) → spMap φ.toRingHom ≫ j ≫ Y.j = spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∃ ψ : p.R →ₐ[c.F] CAt σ, spMap ψ.toRingHom ≫ j ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) ∧ ∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi w ^ m) (Formalism.L2.Pj.toC (ψ f)) := by
  first | exact @GlobalTheory.ArcPoint.chart_coordinates_hasSum | exact GlobalTheory.ArcPoint.chart_coordinates_hasSum | (intros; apply GlobalTheory.ArcPoint.chart_coordinates_hasSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumSectionValueArcFramedPoint
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcQ

section Ring

variable {K : Type} [Field K] (σ : K →+* ℂ) [Algebra K ℂ⸨X⸩]
  (hK : ∀ x : K, algebraMap K ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
  {v : ℂ} (hv : v ≠ 0)


include hK in
theorem hasSum_algebraMap_const (v : ℂ) (x : K) :
    HasSum (fun n : ℤ => (algebraMap K ℂ⸨X⸩ x).coeff n * v ^ n) (σ x) := by
  rw [hK, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  simpa using GlobalTheory.Conv.hasSum_single_laurent 0 (σ x) v

def ptRing : Subalgebra K ℂ⸨X⸩ where
  carrier := {s | Summable fun n : ℤ => s.coeff n * v ^ n}
  mul_mem' hf hg := (GlobalTheory.Conv.hasSum_mul_laurent hv hf hg).summable
  add_mem' hf hg := by simpa [add_mul] using Summable.add hf hg
  algebraMap_mem' x := (hasSum_algebraMap_const σ hK v x).summable

def ptEv : ptRing σ hK hv →ₐ[K] CAt σ where
  toFun s := (GlobalTheory.Conv.lsum s v : ℂ)
  map_one' := by
    have := (hasSum_algebraMap_const σ hK v 1).tsum_eq
    rw [map_one, map_one] at this
    exact this
  map_mul' f g := (GlobalTheory.Conv.hasSum_mul_laurent hv f.2 g.2).tsum_eq
  map_zero' := by
    have := (hasSum_algebraMap_const σ hK v 0).tsum_eq
    rw [map_zero, map_zero] at this
    exact this
  map_add' f g := by
    have := Summable.tsum_add f.2 g.2
    show GlobalTheory.Conv.lsum (f + g : ℂ⸨X⸩) v = GlobalTheory.Conv.lsum f v + GlobalTheory.Conv.lsum g v
    simpa [GlobalTheory.Conv.lsum, add_mul] using this
  commutes' x := (hasSum_algebraMap_const σ hK v x).tsum_eq

theorem hasSum_ptEv (s : ptRing σ hK hv) :
    HasSum (fun n : ℤ => (s : ℂ⸨X⸩).coeff n * v ^ n) (Formalism.L2.Pj.toC (ptEv σ hK hv s)) :=
  Summable.hasSum s.2

theorem ptEv_eq (s : ptRing σ hK hv) {x : CAt σ}
    (h : HasSum (fun n : ℤ => (s : ℂ⸨X⸩).coeff n * v ^ n) (Formalism.L2.Pj.toC x)) : ptEv σ hK hv s = x :=
  h.tsum_eq

theorem isUnit_ptRing (s : ptRing σ hK hv) (h0 : (s : ℂ⸨X⸩) ≠ 0)
    (h : Summable fun n : ℤ => ((s : ℂ⸨X⸩)⁻¹).coeff n * v ^ n) : IsUnit s :=
  IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext (mul_inv_cancel₀ h0))

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frMap_of_frChg_map {R A T : Type} [CommRing R] [Algebra c.F R] [CommRing A] [Algebra c.F A]
    [CommRing T] [Algebra c.F T] (φ : R →ₐ[c.F] A) (κ : A →ₐ[c.F] T)
    (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A) (s : A)
    {y₀ : FrPt Xo c R} {u₁ u : FrPt Xo c A} {y₁ y : FrPt Xo c T} (h₁ : FrMap φ y₀ u₁) (hu : FrChg G s u₁ u)
    (h₂ : FrMap (κ.comp φ) y₀ y₁) (hy : FrChg (fun τ => (G τ).map κ) (κ s) y₁ y) : FrMap κ u y :=
  ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c A).2.2.1 T κ G s u₁ u y₁ y hu
    (Formalism.L2.Pj.frMap_cancel R A T φ κ y₀ u₁ y₁ h₁ h₂)).2 hy

theorem hasSum_evR_of_chart (hL : GlobalTheory.Reg.EvLaws Xo c) (σ : c.F →+* ℂ) [Algebra c.F ℂ⸨X⸩]
    (hK : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    {v : ℂ} (hv : v ≠ 0) {R : Type} [CommRing R] [Algebra c.F R] (φ : R →ₐ[c.F] ℂ⸨X⸩) (ψ : R →ₐ[c.F] CAt σ)
    (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ⸨X⸩) (s : ℂ⸨X⸩)
    (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ)
    {y₀ : FrPt Xo c R} {y₁ y : FrPt Xo c ℂ⸨X⸩} {yw₁ yw : FrPt Xo c (CAt σ)}
    (h₁ : FrMap φ y₀ y₁) (hy : FrChg G s y₁ y) (hw₁ : FrMap ψ y₀ yw₁) (hyw : FrChg Gw sw yw₁ yw)
    (hφ : ∀ f, HasSum (fun n : ℤ => (φ f).coeff n * v ^ n) (Formalism.L2.Pj.toC (ψ f)))
    (hG : ∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * v ^ n) (Formalism.L2.Pj.toC (Gw τ i k)))
    (hs : HasSum (fun n : ℤ => s.coeff n * v ^ n) (Formalism.L2.Pj.toC sw))
    (hG' : ∀ τ, Summable fun n : ℤ => ((G τ).det⁻¹).coeff n * v ^ n)
    (hs' : Summable fun n : ℤ => (s⁻¹).coeff n * v ^ n)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c) (hF : F ∈ sec Xo c a n) :
    HasSum (fun m : ℤ => (evR Xo c F y).coeff m * v ^ m) (Formalism.L2.Pj.toC (evR Xo c F yw)) := by
  let A := ptRing σ hK hv
  let φA : R →ₐ[c.F] A := φ.codRestrict A fun f => (hφ f).summable
  let GA : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A :=
    fun τ i k => ⟨G τ i k, (hG τ i k).summable⟩
  let sA : A := ⟨s, hs.summable⟩
  obtain ⟨hu1, hu2⟩ := (frChg_exists_unique_units E H Dw l Xo c _ G s y₁).2.2.1 y hy
  have hdet : ∀ τ, ((GA τ).det : ℂ⸨X⸩) = (G τ).det := fun τ => A.val.map_det (GA τ)
  obtain ⟨u₁, hu₁⟩ := hL.bc _ _ φA y₀
  obtain ⟨u, hu⟩ := (frChg_exists_unique_units E H Dw l Xo c A GA sA u₁).1
    (fun τ => isUnit_ptRing σ hK hv _ (by rw [hdet]; exact (hu1 τ).ne_zero) (by rw [hdet]; exact hG' τ))
    (isUnit_ptRing σ hK hv sA hu2.ne_zero hs')
  have e₁ : FrMap A.val u y := frMap_of_frChg_map φA A.val GA sA hu₁ hu h₁ hy
  have eψ : (ptEv σ hK hv).comp φA = ψ := AlgHom.ext fun f => ptEv_eq σ hK hv _ (hφ f)
  have eG : (fun τ => (GA τ).map (ptEv σ hK hv)) = Gw := by
    funext τ
    ext i k
    exact ptEv_eq σ hK hv _ (hG τ i k)
  have es : ptEv σ hK hv sA = sw := ptEv_eq σ hK hv _ hs
  have e₂ : FrMap (ptEv σ hK hv) u yw :=
    frMap_of_frChg_map φA (ptEv σ hK hv) GA sA hu₁ hu (by rw [eψ]; exact hw₁) (by rw [eG, es]; exact hyw)
  have nat := (evR_natural_weight_scaling E H Dw l Xo c hL a n F hF A).1
  rw [nat _ _ u y e₁, nat _ _ u yw e₂]
  exact hasSum_ptEv σ hK hv _

theorem exists_algHom_of_mem_range {R L : Type} [CommRing R] [Algebra c.F R] [Field L] [Algebra c.F L]
    (j : Sp R ⟶ Xo.XF c) [IsOpenImmersion j] (hj : j ≫ pullback.snd _ _ = spMap (algebraMap c.F R))
    (z : Sp L ⟶ Xo.XF c) (hz : z ≫ pullback.snd _ _ = spMap (algebraMap c.F L))
    (h : z (IsLocalRing.closedPoint L) ∈ Set.range j) :
    ∃ φ : R →ₐ[c.F] L, spMap φ.toRingHom ≫ j = z := by
  have hr : Set.range z ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have : x = IsLocalRing.closedPoint L := Subsingleton.elim (α := PrimeSpectrum L) _ _
    exact this ▸ h
  let f : R →+* L := (Spec.preimage (IsOpenImmersion.lift j z hr)).hom
  have hf : spMap f ≫ j = z := by
    show Spec.map (Spec.preimage (IsOpenImmersion.lift j z hr)) ≫ j = z
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hc : f.comp (algebraMap c.F R) = algebraMap c.F L := by
    have : spMap (f.comp (algebraMap c.F R)) = spMap (algebraMap c.F L) := by
      rw [← hz, ← hf, Category.assoc, hj]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  exact ⟨{ f with commutes' := fun x => DFunLike.congr_fun hc x }, hf⟩

theorem hasSum_evR_arc : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ a' n (F : Rul Xo c), F ∈ sec Xo c a' n → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (Formalism.L2.Pj.toC (evR Xo c F yw)) := by
  intro hL1 hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ y e th Θ z hL hK hχ hβ hP hth hy hz
  obtain ⟨pt, -, -, -, -, hpt1, hpt2, -⟩ := id hy
  have hpt3 : pt ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ⸨X⸩) := by
    rw [← cancel_mono (spMap β), Category.assoc, ← Y.jQ_over, Category.assoc, ← pullback.condition,
      ← Category.assoc Y.jQ, ← Category.assoc]
    show (pt ≫ Y.j) ≫ Y.s = _
    rw [hpt1, Category.assoc, hχ]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (hK (β x)).symm
  obtain ⟨p, j, y₀, hch, hmem⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hL1.secBaseChange E H Dw l Xo c (pt (IsLocalRing.closedPoint ℂ⸨X⸩))
  haveI := hch.1
  obtain ⟨φ, hφ⟩ := exists_algHom_of_mem_range j hch.2.2 pt hpt3 hmem
  obtain ⟨y₁, hy₁⟩ := hL.bc _ _ φ y₀
  obtain ⟨G, s, hGs⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 y₁).2.2.2 y
    (by rw [hy₁.1, ← hch.2.1, ← Category.assoc, hφ, hpt2])
  obtain ⟨T₁, h₁⟩ := GlobalTheory.T.holArc_chart_coordinates_hasSum E H Dw l Xo c σ O β Y a χ W g ty Fu Ha p j φ hK hχ hβ hch.1 hch.2.2
    (by rw [← Category.assoc, hφ, hpt1])
  obtain ⟨T₂, h₂⟩ := GlobalTheory.T.frame_matrix_hasSum_alt hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th z p j y₀ φ y₁ G s
    hK hχ hβ hy hz hch hy₁ hGs
  obtain ⟨T₃, h₃⟩ := GlobalTheory.T.hasSum_thetaGenerator_chart_ratio hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th Θ p j y₀ φ y₁ G s
    hK hχ hβ hP hth hy hch hy₁ hGs
  have key : ∀ w : ℂ, max T₁ (max T₂ T₃) < w.im → ∀ yw, AnFr Ha Θ z w yw →
      ∃ (ψ : p.R →ₐ[c.F] CAt σ) (yw₁ : FrPt Xo c (CAt σ))
        (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ),
        FrMap ψ y₀ yw₁ ∧ FrChg Gw sw yw₁ yw ∧
        (∀ f, HasSum (fun n : ℤ => (φ f).coeff n * eTwoPi w ^ n) (Formalism.L2.Pj.toC (ψ f))) ∧
        (∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * eTwoPi w ^ n) (Formalism.L2.Pj.toC (Gw τ i k))) ∧
        HasSum (fun n : ℤ => s.coeff n * eTwoPi w ^ n) (Formalism.L2.Pj.toC sw) := by
    intro w hw yw hyw
    rw [max_lt_iff, max_lt_iff] at hw
    obtain ⟨ψ, hψ1, hψ2⟩ := h₁ w hw.1
    obtain ⟨yw₁, hyw₁⟩ := hL.bc _ _ ψ y₀
    obtain ⟨Gw, sw, hw'⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 yw₁).2.2.2 yw
      (by rw [hyw₁.1, ← hch.2.1, hψ1]; exact hyw.1.1)
    exact ⟨ψ, yw₁, Gw, sw, hyw₁, hw', hψ2, h₂ w hw.2.1 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1 hw',
      h₃ w hw.2.2 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1.1 hyw.2 hw'⟩
  by_cases hex : ∃ w : ℂ, max T₁ (max T₂ T₃) < w.im ∧ ∃ yw, AnFr Ha Θ z w yw
  · obtain ⟨w₀, hw₀, yw₀, hyw₀⟩ := hex
    obtain ⟨-, -, Gw₀, sw₀, -, -, -, hG₀, hs₀⟩ := key w₀ hw₀ yw₀ hyw₀
    have hv₀ := GlobalTheory.Conv.eTwoPi_ne_zero w₀
    have cs : s⁻¹ ∈ GlobalTheory.Conv.convLaurent :=
      inv_mem (GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ hs₀.summable)
    have cG : ∀ τ, (G τ).det⁻¹ ∈ GlobalTheory.Conv.convLaurent := fun τ => by
      refine inv_mem ?_
      rw [Matrix.det_apply']
      exact sum_mem fun π _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ =>
        GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ (hG₀ τ _ _).summable)
    obtain ⟨T₄, h₄⟩ := GlobalTheory.Conv.exists_forall_mem_halfRing
      (S := insert s⁻¹ (Set.range fun τ => (G τ).det⁻¹)) ((Set.finite_range _).insert _)
      (by rintro _ (rfl | ⟨τ, rfl⟩); exacts [cs, cG τ])
    refine ⟨max T₄ (max T₁ (max T₂ T₃)), fun w hw yw hyw a' n F hF => ?_⟩
    rw [max_lt_iff] at hw
    obtain ⟨ψ, yw₁, Gw, sw, k₁, k₂, k₃, k₄, k₅⟩ := key w hw.2 yw hyw
    exact hasSum_evR_of_chart hL σ hK (GlobalTheory.Conv.eTwoPi_ne_zero w) φ ψ G s Gw sw hy₁ hGs k₁ k₂ k₃ k₄ k₅
      (fun τ => h₄ _ (Or.inr ⟨τ, rfl⟩) w hw.1) (h₄ _ (Or.inl rfl) w hw.1) a' n F hF
  · exact ⟨_, fun w hw yw hyw => absurd ⟨w, hw, yw, hyw⟩ hex⟩

end GlobalTheory.ArcQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumSectionValueArcFramedPointStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_sectionValue_arc_framedPoint : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ a' n (F : Rul Xo c), F ∈ sec Xo c a' n → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (Formalism.L2.Pj.toC (evR Xo c F yw)) := by
  first | exact @GlobalTheory.ArcQ.hasSum_evR_arc | exact GlobalTheory.ArcQ.hasSum_evR_arc | (intros; apply GlobalTheory.ArcQ.hasSum_evR_arc <;> assumption)
end
