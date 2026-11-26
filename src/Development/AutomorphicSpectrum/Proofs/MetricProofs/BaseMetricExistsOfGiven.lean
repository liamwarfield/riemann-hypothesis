module

public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerBoundHeightOnBoundary
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsLocal
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsBounds
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsPeriod
public import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsHom

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsImmersion
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.FderivValueZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open scoped Matrix ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem exists_embedding (K k : Type) [Field K] [Field k] [Countable K] [Countable k] (β : K →+* k) (s : K →+* ℂ) :
    ∃ j : k →+* ℂ, j.comp β = s := by
  letI := β.toAlgebra
  letI := s.toAlgebra
  obtain ⟨I₁, x, hx⟩ := exists_isTranscendenceBasis' K k
  obtain ⟨κ, z, hz⟩ := exists_isTranscendenceBasis' K ℂ
  have hI₁ : Countable I₁ := hx.1.injective.countable
  have hκ : Cardinal.mk ℂ = Cardinal.mk κ := by
    have := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' z hz
      (Cardinal.mk_le_aleph0_iff.2 inferInstance) (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    exact this
  have hle : Cardinal.mk I₁ ≤ Cardinal.mk κ := by
    rw [← hκ, Cardinal.mk_complex]
    exact (Cardinal.mk_le_aleph0_iff.2 hI₁).trans Cardinal.aleph0_le_continuum
  obtain ⟨e⟩ := hle
  have hz' : AlgebraicIndependent K (z ∘ e) := hz.1.comp e e.injective
  letI : Algebra (MvPolynomial I₁ K) k := (MvPolynomial.aeval x : MvPolynomial I₁ K →ₐ[K] k).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial I₁ K) ℂ := (MvPolynomial.aeval (z ∘ e) : MvPolynomial I₁ K →ₐ[K] ℂ).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial I₁ K) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hx.1
  haveI : FaithfulSMul (MvPolynomial I₁ K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hz'
  haveI : Algebra.IsAlgebraic (MvPolynomial I₁ K) k := by
    haveI := hx.isAlgebraic
    exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq (S := Algebra.adjoin K (Set.range x)) (B := k) hx.1.aevalEquiv
      (RingHom.id k) hx.1.aevalEquiv.surjective Function.injective_id
      (RingHom.ext fun p => hx.1.algebraMap_aevalEquiv p)
  let j : k →ₐ[MvPolynomial I₁ K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨j.toRingHom, RingHom.ext fun a => ?_⟩
  have h := j.commutes (MvPolynomial.C a)
  have h1 : algebraMap (MvPolynomial I₁ K) k (MvPolynomial.C a) = β a := MvPolynomial.aeval_C x a
  have h2 : algebraMap (MvPolynomial I₁ K) ℂ (MvPolynomial.C a) = s a := MvPolynomial.aeval_C (z ∘ e) a
  rw [h1, h2] at h
  exact h

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_bij (hξ : IsCptGen ξ) (q : X) (hq : q = genPt ξ) (h : genPt ξ ⤳ q) :
    Function.Bijective (genMap ξ ⟨q, h⟩) := by
  subst hq
  have : X.presheaf.stalkSpecializes h = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  refine ⟨hξ.inj _, ?_⟩
  unfold genMap
  simp only [this]
  exact hξ.bij.2

theorem countable_of_tie {κ : Type} [Finite κ] {x : κ → Ω} (h : CoordTie ℤ ξ x) : Countable Ω := by
  obtain ⟨c, hc⟩ := h.cover ⟨genPt ξ, specializes_rfl⟩
  haveI : Countable (MvPolynomial κ ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
  refine Function.Surjective.countable (f := fun a : MvPolynomial κ ℤ × MvPolynomial κ ℤ =>
    MvPolynomial.aeval (fun j => x j / x c) a.1 / MvPolynomial.aeval (fun j => x j / x c) a.2) fun a => ?_
  obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h c _ hc a).1 ((genMap_bij h.gen _ rfl _).2 a)
  rw [Algebra.adjoin_range_eq_range_aeval] at hs hsa
  obtain ⟨f, hf⟩ := hs
  obtain ⟨g, hg⟩ := hsa
  refine ⟨(g, f), ?_⟩
  have hf' : MvPolynomial.aeval (fun j => x j / x c) f = s := hf
  have hg' : MvPolynomial.aeval (fun j => x j / x c) g = s * a := hg
  simp only [hf', hg']
  exact mul_div_cancel_left₀ _ hu.1

theorem cancel_gen (hξ : IsCptGen ξ) {R : Type} [CommRing R] {a b : Ω →+* R} (h : spMap a ≫ ξ = spMap b ≫ ξ) :
    a = b := by
  have e := LieTangent.spec_genMap ξ ⟨genPt ξ, specializes_rfl⟩
  have h' : (spMap a ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ =
      (spMap b ≫ Spec.map (CommRingCat.ofHom (genMap ξ ⟨genPt ξ, specializes_rfl⟩))) ≫ X.fromSpecStalk _ := by
    rw [Category.assoc, Category.assoc, e, h]
  rw [cancel_mono, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp] at h'
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
  refine RingHom.ext fun t => ?_
  obtain ⟨s, rfl⟩ := (genMap_bij hξ _ rfl specializes_rfl).2 t
  exact DFunLike.congr_fun h2 s

theorem factor_gen (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] (V : Sp R ⟶ X)
    (hV : centre V = genPt ξ) : ∃ δ : Ω →+* R, spMap δ ≫ ξ = V := by
  have h : genPt ξ ⤳ centre V := hV ▸ specializes_rfl
  let e := RingEquiv.ofBijective _ (genMap_bij hξ _ hV h)
  refine ⟨(Scheme.stalkClosedPointTo V).hom.comp e.symm.toRingHom, ?_⟩
  have e1 := LieTangent.spec_genMap ξ ⟨centre V, h⟩
  have e2 := LieTangent.spec_centre V
  refine (congrArg (spMap _ ≫ ·) e1.symm).trans (Eq.trans ?_ e2)
  rw [← Category.assoc, spMap, ← Spec.map_comp]
  congr 2
  ext s
  exact congrArg (Scheme.stalkClosedPointTo V).hom (e.symm_apply_apply s)

theorem hom_dual_ext {F₀ F : Type} [Field F₀] [Field F] [CharZero F] (i : F₀ →+* F)
    (hfin : 0 < (letI := i.toAlgebra; Module.finrank F₀ F)) {δ δ' : F →+* DualNumber ℂ} (h : δ.comp i = δ'.comp i)
    (h' : ∀ x, (δ x).fst = (δ' x).fst) : δ = δ' := by
  letI := i.toAlgebra
  letI := (δ.comp i).toAlgebra
  haveI : CharZero F₀ := i.charZero
  haveI : Module.Finite F₀ F := Module.finite_of_finrank_pos hfin
  have hu : Algebra.FormallyUnramified F₀ F := Algebra.FormallyUnramified.of_isSeparable F₀ F
  have h := Algebra.FormallyUnramified.ext' (R := F₀) (A := F) (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
    ⟨2, by
      rw [Submodule.zero_eq_bot, eq_bot_iff, sq, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']⟩
    { δ with commutes' := fun _ => rfl } { δ' with commutes' := fun r => (DFunLike.congr_fun h r).symm } h'
  exact RingHom.ext fun x => DFunLike.congr_fun h x

theorem const_of_finite {Y : Scheme.{0}} {Ω₀ : Type} [Field Ω₀] [CharZero Ω] {ξ₀ : Sp Ω₀ ⟶ Y} (hξ : IsCptGen ξ)
    (hξ₀ : IsCptGen ξ₀) {f : X ⟶ Y} {i : Ω₀ →+* Ω} (hf : ξ ≫ f = spMap i ≫ ξ₀)
    (hfin : 0 < (letI := i.toAlgebra; Module.finrank Ω₀ Ω)) {φ : Ω →+* ℂ} {V : Sp (DualNumber ℂ) ⟶ X}
    (h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V = spMap φ ≫ ξ)
    (h2 : V ≫ f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (spMap φ ≫ ξ) ≫ f) :
    V = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ ≫ ξ := by
  have hc : centre V = genPt ξ := by
    have a1 : centre (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ V) = centre V := by
      exact congrArg V (Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom))
    rw [← a1, h1]
    exact SheetDecomposition.CovSch.centre_spMap φ ξ
  obtain ⟨δ, rfl⟩ := factor_gen hξ V hc
  have sc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)
  have e1 : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp δ = φ := cancel_gen hξ (by rw [sc, Category.assoc, h1])
  have e2 : δ.comp i = ((algebraMap ℂ (DualNumber ℂ)).comp φ).comp i := cancel_gen hξ₀ (by
    rw [sc, sc _ ((algebraMap ℂ (DualNumber ℂ)).comp φ), sc φ, Category.assoc, Category.assoc, Category.assoc, ← hf]
    simpa only [Category.assoc] using h2)
  rw [hom_dual_ext i hfin e2 fun x => by
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using DFunLike.congr_fun e1 x, sc, Category.assoc]

theorem fderiv_value_zero (hξ : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) {n : ℕ} {B : Set (Fin n → ℂ)}
    {p : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hp : IsHolTo B p) (h0 : 0 ∈ B) (hc : centre (p 0) = centre ξ) {v : Fin n → ℂ}
    (hv : IsDerivAt0 p v (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0)) {a : Ω} {r : (Fin n → ℂ) → ℂ}
    (hr : ∀ᶠ u in nhds 0, ValAt ξ (p u) a (r u)) : fderiv ℂ r 0 v = 0 := by
  obtain ⟨g, rfl⟩ := hξ.bij.2 a
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  have hU0 : ⊤ ≤ p 0 ⁻¹ᵁ U := (SheetDecomposition.CovSch.top_le_iff _ _).2 (hc ▸ hU)
  have he : r =ᶠ[nhds 0] fun u => valAt' (p u) U s := by
    filter_upwards [hr, GlobalTheory.LocalLift.hol_eventually_mem hp h0 hU0] with u h1 h2
    have h3 := (SheetDecomposition.CovSch.top_le_iff _ _).1 h2.2
    rw [SheetDecomposition.CovSch.valAt'_eq _ _ h3]
    exact SheetDecomposition.CovSch.v_unique hξ h1 (SheetDecomposition.CovSch.valAt_sec (hall _) U h3 hU s)
  have h1 : ⊤ ≤ (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0) ⁻¹ᵁ U := fun q _ => hU0 (Set.mem_univ _)
  rw [he.fderiv_eq, ← hv.2 U h1 s]
  have := GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap ℂ (DualNumber ℂ)) (p 0) U hU0 h1 s
  refine (congrArg TrivSqZeroExt.snd this).trans ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end PositivityTheory.Xgp.c_bm_exists_period
end
end

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

open PositivityTheory.Xgp.c_bm_exists_period FramePeriods in
theorem PositivityTheory.Xgp.t_c_bm_exists_immersion : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (d : ℕ), 𝔐.IsCover d → ∀ (Rb : AnLogRes (mCoordIdeal M.x) ⊤ (Fintype.card (CMType H) * D.p * D.q)) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ l, IsOpen (O l)) → (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ l, ∃ x ∈ O l \ bdry s, ∃ (V : Set Rb.X) (Pi : CMType H → Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), x ∈ V ∧ IsPeriodOn Rb.A D.p V Pi (fun τ x' => blockG (baseGram tie (F l) τ Rb x')) ∧ ∀ k, x ∈ (Rb.A.chart k).source → ∀ v : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ, (∀ τ (a b : Fin (D.p + D.q)), D.p + D.q - D.p ≤ (a : ℕ) → (b : ℕ) < D.p + D.q - D.p → ((Pi τ x)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => Pi τ ((Rb.A.chart k).symm w) a b) (Rb.A.chart k x) v) a b = 0) → v = 0 := by
  intro hG E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie hp1 _ d hd Rb s hInt hcl q O F hO hcov hF hgood
  have hpq : 1 ≤ D.p + D.q := by omega
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  haveI : Countable M.Ω := countable_of_tie 𝔐.tie
  haveI : Countable c.F := 𝔐.cst.injective.countable
  obtain ⟨φ, hφ⟩ := exists_embedding c.F M.Ω 𝔐.cst c.F.val.toRingHom
  have tp := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  obtain ⟨w, hw⟩ := tp.2.1 (spMap φ ≫ 𝔐.ξ) (𝔐.all _)
  have htop : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing (baseIdx ι M.blk))) := fun z h => by simpa using h.2 1 trivial
  obtain ⟨x, a, ha, hxa⟩ := Rb.surj w ((GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie w).2 ⟨_, 𝔐.all _, hw⟩) (htop w)
  have hz : CoordsAt 𝔐.ξ M.x (spMap φ ≫ 𝔐.ξ) (Rb.lift x x) :=
    ((tp.2.2 _ _ (𝔐.all _) hw).2 _).2 ⟨fun k => Units.mk0 (a k) (ha k), hxa⟩
  have hcz : centre (spMap φ ≫ 𝔐.ξ) = centre 𝔐.ξ := SheetDecomposition.CovSch.centre_spMap φ 𝔐.ξ
  have hx : x ∉ bdry s := (hInt x _ hz).2 (by
    change centre _ ∈ _
    rw [hcz]
    exact (GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c _ _ Y S M.Ω _ _ M.x 𝔐 (FaithfulSMul.algebraMap_injective _ _)).1)
  obtain ⟨l₀, hl₀⟩ := hcov x
  obtain ⟨j, r, p, hr, hj, hwd, hp⟩ := exists_family (𝔐 := 𝔐) Rb hcl hx
  have hhol : IsHolTo (Metric.ball 0 1) p := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie 𝔐.all _ _ _ p
    Metric.isOpen_ball hwd fun u hu => (hp u hu).2.1
  obtain ⟨τ₀, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) _ p hhol
  have hint : ∀ u ∈ Metric.ball 0 1, 𝔐.Interior (p u) := fun u hu => (hInt _ _ (hp u hu).2.2).1 (hp u hu).1
  have hb0 : 0 ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) 1 := Metric.mem_ball_self one_pos
  have hc0 : CoordsAt 𝔐.ξ M.x (p 0) (Rb.lift x x) := by
    have := (hp 0 hb0).2.1
    rwa [smul_zero, add_zero, (Rb.A.chart j).left_inv hj] at this
  have hp0 : p 0 = spMap φ ≫ 𝔐.ξ :=
    (tp.1 _ hz.1 (tp.2.2 _ _ (𝔐.all _) hz).1).unique ⟨𝔐.all _, hc0⟩ ⟨𝔐.all _, hz⟩
  have hτ₀ : τ₀ = c.F.val.toRingHom := by
    have h1 := hτ 0 hb0
    rw [hp0, Category.assoc, 𝔐.cst_over, spMap, spMap, spMap, ← Spec.map_comp] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    rw [← hφ]
    exact IsFractionRing.ringHom_ext (A := 𝓞 c.F) fun t => (DFunLike.congr_fun h2 t).symm
  obtain ⟨ρ, B, Pi, Γ, hρ, hρ', hB, h0, hsub, hPi, hgr, hder⟩ := family_period hG.1.2.2.1 tie hpq (hF l₀) p τ₀
    (by rw [hτ₀]; rfl) hhol hτ hint (by rw [ptIdeal_centre hc0]; exact hgood l₀ x hl₀)
  obtain ⟨h1, h2, h3⟩ := to_manifold Rb.A j hj (r := (r : ℂ) * ρ) hB h0
  have hne : (r : ℂ) * ρ ≠ 0 := by exact_mod_cast (mul_pos hr hρ).ne'
  have hback : ∀ x' ∈ (Rb.A.chart j).source, (Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • (ρ : ℂ) •
      (((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j x' - Rb.A.chart j x))) = x' := fun x' hx' => by
    rw [smul_smul (r : ℂ), smul_inv_smul₀ hne, add_sub_cancel, (Rb.A.chart j).left_inv hx']
  refine ⟨l₀, x, ⟨hl₀, hx⟩, _, fun τ x' => Pi τ (((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j x' - Rb.A.chart j x)), h2,
    ⟨h1, fun τ a b => h3 _ (hPi τ a b), fun τ x' hx' => ?_⟩, fun k hk v hv => ?_⟩
  · have hm := smul_mem_ball' hρ hρ' (hsub hx'.2)
    have hc := (hp _ hm).2.2
    rw [hback x' hx'.1] at hc
    simp only
    rw [baseGram, gramFn_eq hc (hint _ hm) (hgr τ _ hx'.2).1]
    exact (hgr τ _ hx'.2).2
  let ψ : (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) → (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) :=
    fun t => ((r : ℂ) * ρ)⁻¹ • (Rb.A.chart j ((Rb.A.chart k).symm t) - Rb.A.chart j x)
  have hkx : (Rb.A.chart k).symm (Rb.A.chart k x) = x := (Rb.A.chart k).left_inv hk
  have hψ0 : ψ (Rb.A.chart k x) = 0 := by simp only [ψ, hkx, sub_self, smul_zero]
  have hψ : DifferentiableAt ℂ ψ (Rb.A.chart k x) :=
    by
    have := ((Rb.A.holo k j _ ⟨(Rb.A.chart k).map_source hk, by rw [Set.mem_preimage, hkx]; exact hj⟩).differentiableAt.sub_const
      (Rb.A.chart j x)).const_smul (((r : ℂ) * ρ)⁻¹)
    exact this
  have chain : ∀ f : (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) → ℂ, DifferentiableAt ℂ f 0 →
      HasFDerivAt (fun t => f (ψ t)) ((fderiv ℂ f 0).comp (fderiv ℂ ψ (Rb.A.chart k x))) (Rb.A.chart k x) :=
    fun f hf => HasFDerivAt.comp _ (by rw [hψ0]; exact hf.hasFDerivAt) hψ.hasFDerivAt
  obtain ⟨V, hV1, hV2⟩ := hder (fderiv ℂ ψ (Rb.A.chart k x) v) fun τ a b h₁ h₂ => by
    have := hv τ a b h₁ h₂
    simp only [sub_self, smul_zero] at this
    convert this using 3
    ext a' b'
    exact (congrArg (· v) (chain _ ((hPi τ a' b').differentiableAt (hB.mem_nhds h0))).fderiv).symm
  have hV3 : V = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0 := by
    have e1 := hV1.1
    simp only [smul_zero] at e1
    rw [hp0] at e1 hV2 ⊢
    exact const_of_finite 𝔐.tie.gen 𝔐.gen₀ 𝔐.fn_over (hd.2 ▸ hd.1) e1 hV2
  choose pc hpc using hz.1
  have hball : ∀ᶠ u in nhds (0 : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ), u ∈ Metric.ball 0 1 :=
    Metric.isOpen_ball.mem_nhds hb0
  let wv : (Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ := fun u =>
    Rb.lift x ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • (ρ : ℂ) • u))
  have hwv0 : wv 0 = Rb.lift x x := by simp only [wv, smul_zero, add_zero, (Rb.A.chart j).left_inv hj]
  have hwv : ∀ q', DifferentiableAt ℂ (fun u => wv u q') 0 := fun q' => by
    have a1 := (differentiableOn_pi.1 hwd q').differentiableAt hball
    have a2 : DifferentiableAt ℂ (fun u : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ => (ρ : ℂ) • u) 0 := by
      fun_prop
    exact DifferentiableAt.comp (0 : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ) (by rw [smul_zero]; exact a1) a2
  have hne0 : ∀ k', wv 0 ⟨k', pc k'⟩ ≠ 0 := fun k' => by rw [hwv0]; exact (hpc k').ne_zero
  have hhol' : IsHolTo (Metric.ball 0 1) fun u => p ((ρ : ℂ) • u) :=
    GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie 𝔐.all _ _ wv _ Metric.isOpen_ball
      (hwd.comp (by fun_prop) fun u hu => smul_mem_ball' hρ hρ' hu) fun u hu => (hp _ (smul_mem_ball' hρ hρ' hu)).2.1
  have hA : ∀ q', DifferentiableAt ℂ (fun u => affCoord pc (wv u) q') 0 ∧
      fderiv ℂ (fun u => affCoord pc (wv u) q') 0 (fderiv ℂ ψ (Rb.A.chart k x) v) = 0 := fun q' => by
    refine ⟨by
      simp only [affCoord, div_eq_mul_inv]
      exact (hwv q').mul ((hwv ⟨q'.1, pc q'.1⟩).inv (hne0 q'.1)), fderiv_value_zero 𝔐.tie.gen 𝔐.all hhol' hb0
      (by simp only [smul_zero]; rw [hp0, hcz]) (by simp only [smul_zero]; rw [← hV3]; exact hV1)
      (a := M.x q' / M.x ⟨q'.1, pc q'.1⟩) ?_⟩
    filter_upwards [hball, (hwv _).continuousAt.eventually_ne (hne0 q'.1)] with u hu hu'
    obtain ⟨t, ht, e⟩ := ((hp _ (smul_mem_ball' hρ hρ' hu)).2.1.2 q'.1 (pc q'.1) (IsUnit.mk0 _ hu')).2 q'.2
    have e' : wv u q' = t * wv u ⟨q'.1, pc q'.1⟩ := e
    rw [affCoord, e', mul_div_cancel_right₀ _ hu']
    exact ht
  have hker := Rb.immersion x (htop _) pc (fun k' => (hpc k').ne_zero) k hk
  have hev : (fun t => affCoord pc (Rb.lift x ((Rb.A.chart k).symm t))) =ᶠ[nhds (Rb.A.chart k x)]
      fun t q' => affCoord pc (wv (ψ t)) q' := by
    have hs : (Rb.A.chart j).source ∈ nhds ((Rb.A.chart k).symm (Rb.A.chart k x)) := by
      rw [hkx]; exact (Rb.A.chart j).open_source.mem_nhds hj
    filter_upwards [((Rb.A.chart k).continuousAt_symm ((Rb.A.chart k).map_source hk)).eventually hs] with t ht
    simp only [wv, ψ, hback _ ht]
  rw [hev.fderiv_eq, (hasFDerivAt_pi.2 fun q' => chain _ (hA q').1).fderiv] at hker
  rw [← Submodule.mem_bot ℂ, ← hker]
  exact funext fun q' => (hA q').2
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalHoloIsPeriodGramBlockGBaseGram
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalHoloIsPeriodGramBlockGBaseGram
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_local_holo_isPeriodGram_blockG_baseGram : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (x : Rb.X), x ∉ bdry s → M.GoodAt F (mCoordIdeal (Rb.lift x x)) → ∃ (V : Set Rb.X) (P : Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), IsOpen V ∧ x ∈ V ∧ (∀ a b, Rb.A.HoloOn V fun x' => P x' a b) ∧ ∀ x' ∈ V, IsPeriodGram D.p (P x') (blockG (baseGram tie F τ Rb x')) := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_period | exact PositivityTheory.Xgp.t_c_bm_exists_period
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalHoloIsPeriodGramBlockGBaseGramStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_holo_isPeriodGram_blockG_baseGram : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (x : Rb.X), x ∉ bdry s → M.GoodAt F (mCoordIdeal (Rb.lift x x)) → ∃ (V : Set Rb.X) (P : Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), IsOpen V ∧ x ∈ V ∧ (∀ a b, Rb.A.HoloOn V fun x' => P x' a b) ∧ ∀ x' ∈ V, IsPeriodGram D.p (P x') (blockG (baseGram tie F τ Rb x')) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_local_holo_isPeriodGram_blockG_baseGram | exact GlobalTheory.CompanionTheory.Relay.exists_local_holo_isPeriodGram_blockG_baseGram | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_local_holo_isPeriodGram_blockG_baseGram <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelHeightLowerEstimate
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelHeightLowerEstimate
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flagModel_height_lower_estimate : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (d : ℕ), 𝔐.IsCover d → ∀ (Rb : AnLogRes (mCoordIdeal M.x) ⊤ (Fintype.card (CMType H) * D.p * D.q)) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ l, IsOpen (O l)) → (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ l, ∃ x ∈ O l \ bdry s, ∃ (V : Set Rb.X) (Pi : CMType H → Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), x ∈ V ∧ IsPeriodOn Rb.A D.p V Pi (fun τ x' => blockG (baseGram tie (F l) τ Rb x')) ∧ ∀ k, x ∈ (Rb.A.chart k).source → ∀ v : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ, (∀ τ (a b : Fin (D.p + D.q)), D.p + D.q - D.p ≤ (a : ℕ) → (b : ℕ) < D.p + D.q - D.p → ((Pi τ x)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => Pi τ ((Rb.A.chart k).symm w) a b) (Rb.A.chart k x) v) a b = 0) → v = 0 := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_immersion | exact PositivityTheory.Xgp.t_c_bm_exists_immersion
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelHeightLowerEstimateStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_height_lower_estimate : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), 1 ≤ D.p → 1 ≤ D.q → ∀ (d : ℕ), 𝔐.IsCover d → ∀ (Rb : AnLogRes (mCoordIdeal M.x) ⊤ (Fintype.card (CMType H) * D.p * D.q)) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → IsClosed (bdry s) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ l, IsOpen (O l)) → (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ l, ∃ x ∈ O l \ bdry s, ∃ (V : Set Rb.X) (Pi : CMType H → Rb.X → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), x ∈ V ∧ IsPeriodOn Rb.A D.p V Pi (fun τ x' => blockG (baseGram tie (F l) τ Rb x')) ∧ ∀ k, x ∈ (Rb.A.chart k).source → ∀ v : Fin (Fintype.card (CMType H) * D.p * D.q) → ℂ, (∀ τ (a b : Fin (D.p + D.q)), D.p + D.q - D.p ≤ (a : ℕ) → (b : ℕ) < D.p + D.q - D.p → ((Pi τ x)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => Pi τ ((Rb.A.chart k).symm w) a b) (Rb.A.chart k x) v) a b = 0) → v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flagModel_height_lower_estimate | exact GlobalTheory.CompanionTheory.Relay.flagModel_height_lower_estimate | (intros; apply GlobalTheory.CompanionTheory.Relay.flagModel_height_lower_estimate <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelGlobalHeightIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsFramePeriodsNoGlobal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.FramePeriods
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

theorem exists_isFramePeriods_noGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∀ (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → (∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord y) cc p → unitAt 𝔐.ξ p f → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb p) → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
  intro E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 a b N bb n Bd χ t₀ cc f hBd ht₀ hfr hdom
  classical
  obtain ⟨a₀, π, ρ₀, ha, hρ₀, hρ₀', hπ, hgeo⟩ := GlobalTheory.T.snc_chart_local_normal_form K J Ω y _ n Bd χ t₀ cc f ht₀ hdom
  have hw : DifferentiableOn ℂ (fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u)) (Metric.ball 0 1) := by
    refine χ.analytic.differentiableOn.comp ?_ fun u hu => (hgeo ρ₀ hρ₀ le_rfl u hu).1
    unfold HodgeMetric.recentre
    exact (differentiable_const _ |>.add (differentiable_pi.2 fun i => by
      simpa using (differentiable_apply (π i) : Differentiable ℂ fun u : Fin n → ℂ => u (π i)).const_mul (ρ₀ : ℂ))).differentiableOn
  set w : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u) with hwdef
  have htie := 𝔐.tie
  have hall := 𝔐.all
  have hex : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, ∃ z : Sp ℂ ⟶ 𝔐.X, genPt 𝔐.ξ ⤳ centre z ∧ CoordsAt 𝔐.ξ y z (w u) := fun u hu =>
    (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y htie (w u)).1 (χ.mem _ (hgeo ρ₀ hρ₀ le_rfl u hu).1)
  haveI : Nonempty (Sp ℂ ⟶ 𝔐.X) := ⟨(hex 0 (by simp)).choose⟩
  choose! p hp₀ hp using hex
  have huniq : ∀ (z z' : Sp ℂ ⟶ 𝔐.X) (w' : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w' → CoordsAt 𝔐.ξ y z' w' → z = z' := fun z z' w' h h' => by
    obtain ⟨e1, -, e3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y htie ℂ
    exact (e1 w' h.1 (e3 z w' (hall _) h).1).unique ⟨hall _, h⟩ ⟨hall _, h'⟩

  have fin : ∀ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (ρ₁ : ℝ)
      (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), 0 < ρ₁ → ρ₁ ≤ 1 →
      (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) →
      (∀ u ∈ GlobalTheory.CompanionTheory.Ar.Flat.punct n a₀ 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w ((ρ₁ : ℂ) • u)) →
        𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (HodgeMetric.periodGram L U u)) →
      ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
    intro g Λ _ L ρ₁ U h1 h2 h3 h4 h5
    have hle : ρ₀ * ρ₁ ≤ ρ₀ := by nlinarith
    have hpos : 0 < ρ₀ * ρ₁ := mul_pos hρ₀ h1
    refine ⟨a₀, g, Λ, inferInstance, L, π, ρ₀ * ρ₁, U, hpos, by nlinarith, h3, h4, hπ, fun u hu => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hgeo _ hpos hle u hu
    refine ⟨g1, g2, g3, fun hup z hz => ?_⟩
    rw [recentre_mul] at hz
    exact h5 u hup z hz
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := by simp
  have hfr0 : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p 0), hall _⟩ := by
    have hd := (hgeo ρ₀ hρ₀ le_rfl 0 hb0).2.1
    obtain ⟨c1, c2⟩ := GlobalTheory.T.frame_domain_in_segre_chart 𝔐.X Ω 𝔐.ξ K J y htie (p 0) (w 0) cc f (hall _) (hp 0 hb0) hd
    exact hfr _ c1 c2
  by_cases hpq : D.p + D.q = 0
  · have hV : ∀ s, 𝔐.Vgen s = ⊥ := fun s => by
      obtain ⟨-, -, b', hb', -⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
      have hr : labelRk D s = 0 := by
        rcases s with s | s <;> simp only [labelRk, Sum.elim_inl, Sum.elim_inr] <;> omega
      have : IsEmpty (Fin (labelRk D s)) := by rw [hr]; infer_instance
      have e : Set.range b' = ∅ := Set.range_eq_empty b'
      rw [e, Submodule.span_empty] at hb'
      exact hb'.symm
    have hli := hfr0.1
    haveI : Subsingleton ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := by
      rw [hV a, hV b, sup_bot_eq]
      infer_instance
    haveI : IsEmpty (Fin N) := ⟨fun k => hli.ne_zero k (Subsingleton.elim _ _)⟩
    obtain ⟨Λ, _, ⟨L⟩⟩ := zeroPeriods n a₀ ha
    exact fin 0 Λ _ L 1 (fun _ _ => 0) one_pos le_rfl (fun k => isEmptyElim k) linearIndependent_empty_type
      fun u _ z _ => ⟨fun k => isEmptyElim k, fun k => isEmptyElim k, fun k => isEmptyElim k⟩
  have hpq' : 1 ≤ D.p + D.q := Nat.one_le_iff_ne_zero.2 hpq
  have hhol : IsHolTo (Metric.ball 0 1) p := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ w p Metric.isOpen_ball hw hp
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) n p hhol
  have hint : ∀ u ∈ GlobalTheory.CompanionTheory.Ar.Flat.punct n a₀ 1, 𝔐.Interior (p u) := fun u hu => by
    have h1 := (hgeo ρ₀ hρ₀ le_rfl u hu.1).2.2
    have h2 := hBd (p u) (w u) (hp u hu.1)
    by_contra h
    exact (h1.2 hu) (h2.2 h)
  set σ : KA l →+* ℂ := τ.comp (IntermediateField.inclusion c.le).toRingHom with hσ
  have hsq : (σ (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hs | hs
  · obtain ⟨g, Λ, _, L, ρ₁, U, h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p τ hpq' hs ha hhol hτ hint (hall _) hfr0
    refine fin g Λ _ L ρ₁ U h1 h2 h3 h4 fun u hu z hz => ?_
    rw [huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
    exact h5 u hu
  · have hcc : (spMap (starRingEnd ℂ) : Sp ℂ ⟶ Sp ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
      refine (Spec.map_comp (CommRingCat.ofHom (starRingEnd ℂ)) (CommRingCat.ofHom (starRingEnd ℂ))).symm.trans ?_
      convert Spec.map_id (CommRingCat.of ℂ)
      ext x
      simp
    set p' : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X) := fun u => spMap (starRingEnd ℂ) ≫ p (star u) with hp'
    have hcoord : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (p' u) (fun q => star (w (star u) q)) := fun u hu =>
      (GlobalTheory.T.conjugate_point_same_centre 𝔐.X Ω 𝔐.ξ K J y _ _).2 (hp _ (star_mem_ball' hu))
    have hcen : ∀ u, centre (p' u) = centre (p (star u)) := fun u => (GlobalTheory.T.conjugate_point_same_centre 𝔐.X Ω 𝔐.ξ K J y _ (w 0)).1
    have hhol' : IsHolTo (Metric.ball 0 1) p' := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ _ p' Metric.isOpen_ball
      (diffOn_star' hw) hcoord
    have hτ' : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u ≫ 𝔐.f ≫ Y.s =
        spMap (((starRingEnd ℂ).comp τ).comp (algebraMap (𝓞 c.F) c.F)) := fun u hu => by
      rw [hp', Category.assoc, hτ _ (star_mem_ball' hu)]
      exact (Spec.map_comp (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))).symm
    have hint' : ∀ u ∈ GlobalTheory.CompanionTheory.Ar.Flat.punct n a₀ 1, 𝔐.Interior (p' u) := fun u hu => by
      change centre (p' u) ∈ _
      rw [hcen]
      exact hint _ (star_mem_punct' hu)
    have hs' : (((starRingEnd ℂ).comp τ).comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
      change (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
      rw [hs, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have hfr0' : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p' 0), hall _⟩ := by
      have e : (⟨centre (p' 0), hall _⟩ : Cpt 𝔐.ξ) = ⟨centre (p 0), hall _⟩ := Subtype.ext (by
        show centre (p' 0) = centre (p 0)
        rw [hcen, star_zero])
      rw [e]
      exact hfr0
    obtain ⟨g, Λ, _, L', ρ₁, U', h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p' _ hpq' hs' ha hhol' hτ' hint' (hall _) hfr0'
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_conjugate_log_periods n a₀ g N Λ L' U' (GlobalTheory.T.bijective_logPeriods_T n a₀ g Λ L')
    refine fin g Λ _ L ρ₁ (fun k u' => star (U' k (star u'))) h1 h2 (fun k => diffOn_star' (h3 k)) ?_ fun u hu z hz => ?_
    · refine Fintype.linearIndependent_iff.2 fun c' hc' k => ?_
      have e := congrArg star hc'
      simp only [star_sum, star_smul, star_star, star_zero] at e
      have := Fintype.linearIndependent_iff.1 h4 (fun k => star (c' k)) (by simpa [star_smul] using e) k
      simpa using this
    · rw [hL u hu, huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
      have := GlobalTheory.T.gramAt_conj_point_map_conj E H D l (Xo l) c Y S Ω K J y 𝔐 _ N _ _ (h5 (star u) (star_mem_punct' hu))
      have e : spMap (starRingEnd ℂ) ≫ p' ((ρ₁ : ℂ) • star u) = p ((ρ₁ : ℂ) • u) := by
        rw [hp']
        simp only
        rw [← Category.assoc, hcc, Category.id_comp, star_smul, star_star]
        simp
      rwa [e] at this

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelGlobalHeightIdentity
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


set_option maxHeartbeats 1000000 in
open PositivityTheory.Xgp.c_bm_exists_local GroundTheory.Heights₂.Heights.LowerBoundFree in
theorem GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (Bat : FinHolAtlas n Rb.X), IsPotential Rb.A L → IsSection Rb.A L s → (∀ p, logNormSec L s p ≤ 0) → IsAdaptedAtlas Rb.A Bat L s → (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (k : Fin Bat.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → M.GoodAt F (mCoordIdeal (Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀))) → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (Bat.chart k).symm w ∉ bdry s → (baseGram tie F τ Rb ((Bat.chart k).symm w)).PosDef ∧ ((baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ)).PosSemidef ∧ (((C * rW L s ((Bat.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) - (baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w‖ ≤ C * Real.exp (rW L s ((Bat.chart k).symm w) / 2) := by
  intro _ E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie n Rb L s Bat _ _ hnorm hAd hInt F hF τ k w₀ hw₀ hgood
  classical
  obtain ⟨hAB, hball, -, M₀, hM⟩ := hAd
  obtain ⟨S₀, m, hm, hS, hr⟩ := hM k
  have tp := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  have uniq : ∀ {z z' : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w}, CoordsAt 𝔐.ξ M.x z w → CoordsAt 𝔐.ξ M.x z' w → z = z' :=
    fun {z z' w} h h' => (tp.1 w h.1 (tp.2.2 z w (𝔐.all _) h).1).unique ⟨𝔐.all _, h⟩ ⟨𝔐.all _, h'⟩
  have orb : ∀ {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w w'}, CoordsAt 𝔐.ξ M.x z w → SameOrbit w' w →
      CoordsAt 𝔐.ξ M.x z w' := fun {z w w'} h ⟨a, ha, e⟩ =>
    ((tp.2.2 z w (𝔐.all _) h).2 _).2 ⟨fun k => Units.mk0 (a k) (ha k), e⟩
  have pts : ∀ w ∈ mcPts (mCoordIdeal M.x), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z w := fun w hw => by
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie w).1 hw
    exact ⟨z, hz⟩
  have gfn : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w Γ, CoordsAt 𝔐.ξ M.x z w → 𝔐.Interior z →
      𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ → HodgeMetric.gramFn 𝔐 (gb tie F τ) w = Γ := by
    intro z w Γ hw hi hΓ
    have hex : ∃ (Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
        CoordsAt 𝔐.ξ M.x z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ := ⟨Γ, z, hw, hi, hΓ⟩
    unfold HodgeMetric.gramFn
    rw [dite_eq_left hex]
    obtain ⟨z₀, hw₀, hi₀, hΓ₀⟩ := hex.choose_spec
    rw [uniq hw₀ hw] at hΓ₀
    exact GlobalTheory.T.gram_matrix_change_frame E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _
      (GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z hi) hΓ₀ hΓ
  let Bd : Set ((Σ k, baseIdx ι M.blk k) → ℂ) :=
    {w | ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z w → ¬ 𝔐.Interior z}
  have hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ M.x z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z) :=
    fun z w hz => ⟨fun h => h z hz, fun h z' hz' => uniq hz hz' ▸ h⟩
  have hZ : ∀ x₀, ∀ x ∈ Rb.U x₀, Rb.lift x₀ x ∈ Bd ↔ x ∈ bdry s := by
    intro x₀ x hx
    obtain ⟨z, hz⟩ := pts _ (Rb.mem x₀ x hx)
    rw [hBd z _ hz, ← hInt x z (orb hz (Rb.compat x x₀ x ⟨Rb.mem_U x, hx⟩)), not_not]
  have hw₀' : ‖w₀‖ ≤ 3 / 2 := mem_closedBall_zero_iff.1 hw₀
  have hw₀t : w₀ ∈ (Bat.chart k).target := hball k (mem_closedBall_zero_iff.2 (by linarith))
  obtain ⟨ρ, π, χ, hρ, hρ', hU, hγ, ha⟩ := exists_sncChart Rb Bat hAB k w₀ hw₀t Bd (bdry s) S₀ hS hZ
  have hγ0 : χ.γ 0 = Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀) := by
    rw [hγ, HodgeMetric.recentre_zero]
  obtain ⟨z₀, hz₀⟩ := pts _ (Rb.mem _ _ (Rb.mem_U ((Bat.chart k).symm w₀)))
  obtain ⟨f, hf, hfg⟩ := exists_goodDomain M F 𝔐.tie (𝔐.all _) hz₀ hgood
  obtain ⟨a₀, g, Λ, _, LP, π', ρ', U, hP⟩ := exists_isFramePeriods_noGlobal E H D Xo l c Y S M.Ω _ _ M.x 𝔐 (.inl τ) (.inr τ) _
    (gbS tie F τ) n Bd χ 0 F.c f hBd (Metric.mem_ball_self one_pos)
    (fun p h1 h2 => PositivityTheory.Xgp.isFrameAt_comap_gbS E H D Xo l c Y S K ι Φ y M 𝔐 tie F hF τ p (hfg p h1 h2))
    (hγ0 ▸ hf)
  obtain ⟨ε, c₀, C, hε, hερ, hc₀, hC, hb⟩ := GlobalTheory.T.period_gram_comparison_bound n a₀ g _ χ.a Λ LP U 0 π' ρ' hP.1 hP.2.1 hP.2.2.1
    hP.2.2.2.1 hP.2.2.2.2.1
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_uncentre w₀ ρ π
  have hcu : Continuous (HodgeMetric.uncentre w₀ ρ π) := (HodgeMetric.contDiff_uncentre w₀ ρ π).continuous
  have hcu' : Continuous (HodgeMetric.uncentre 0 ρ' π') := (HodgeMetric.contDiff_uncentre 0 ρ' π').continuous

  have pg : ∀ w ∈ Metric.ball w₀ ρ, HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w) ∈ GlobalTheory.CompanionTheory.Ar.Flat.punct n a₀ 1 →
      baseGram tie F τ Rb ((Bat.chart k).symm w) =
        HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w)) := by
    intro w hw hu
    obtain ⟨hb1, -, hbd, hg⟩ := hP.2.2.2.2.2 _ hu.1
    rw [HodgeMetric.recentre_uncentre 0 hP.1, hγ, HodgeMetric.recentre_uncentre w₀ hρ] at hbd hg
    obtain ⟨z, hz⟩ := pts _ (Rb.mem _ _ (hU w hw).2)
    have hi : 𝔐.Interior z := by_contra fun h => hbd.2 hu ((hBd z _ hz).2 h)
    exact gfn z _ _ (orb hz (Rb.compat _ _ _ ⟨Rb.mem_U _, (hU w hw).2⟩)) hi (hg hu z hz)
  have h0 : ∀ᶠ w in nhds w₀, ‖HodgeMetric.uncentre w₀ ρ π w - 0‖ < ε := by
    have : ContinuousAt (fun w => ‖HodgeMetric.uncentre w₀ ρ π w - 0‖) w₀ := by fun_prop
    refine this.eventually_lt continuousAt_const ?_
    simpa [HodgeMetric.uncentre_self] using hε
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1 h0
  refine ⟨min ε₁ ρ, c₀, C * (1 + |M₀|) + C * Real.exp (|M₀| / 2) * ‖A‖, lt_min hε₁ hρ, hc₀, by positivity,
    fun w hw hwb => ?_⟩
  have hwρ : ‖w - w₀‖ < ρ := hw.trans_le (min_le_right _ _)
  have hwB : w ∈ Metric.ball w₀ ρ := mem_ball_iff_norm.2 hwρ
  have ht := hb₁ w (mem_ball_iff_norm.2 (hw.trans_le (min_le_left _ _)))
  have ht1 := HodgeMetric.uncentre_mem_ball hρ π hwρ
  have hub := HodgeMetric.uncentre_mem_ball hP.1 π' (ht.trans_le hερ)
  have hu : HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w) ∈ GlobalTheory.CompanionTheory.Ar.Flat.punct n a₀ 1 := by
    have hcl := (hP.2.2.2.2.2 _ hub).2.2.1
    rw [HodgeMetric.recentre_uncentre 0 hP.1, hγ, HodgeMetric.recentre_uncentre w₀ hρ, hZ _ _ (hU w hwB).2] at hcl
    exact hcl.1 hwb
  obtain ⟨b1, b2, b3⟩ := hb _ ht (mem_ball_zero_iff.1 ht1) hu
  have hev : ∀ᶠ w' in nhds w, baseGram tie F τ Rb ((Bat.chart k).symm w') =
      HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w')) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hwB,
      (hcu'.comp hcu).continuousAt.eventually ((HodgeMetric.isOpen_punct n a₀ 1).mem_nhds hu)] with w' h1 h2
    exact pg w' h1 h2
  have hw2 : ‖w‖ ≤ 2 := by
    have := norm_add_le (w - w₀) w₀
    rw [sub_add_cancel] at this
    linarith
  have hlog := logR_le hρ (by linarith) hm hw2
    (fun i hi h => hwb ((hS w (hU w hwB).1).2 ⟨i, hi, h⟩)) ha
  have hrM := abs_le.1 ((hr w (mem_closedBall_zero_iff.2 hw2) hwb).trans (le_abs_self M₀))
  have hre : 1 ≤ rW L s ((Bat.chart k).symm w) := by
    have := hnorm ((Bat.chart k).symm w)
    have h2 := Real.add_one_le_exp (1 : ℝ)
    unfold rW
    linarith
  generalize (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < χ.a then
    Real.log (1 / ‖HodgeMetric.uncentre w₀ ρ π w i‖ ^ 2) else 0) = R at b2 b3 hlog
  generalize rW L s ((Bat.chart k).symm w) = r at hrM hre ⊢
  have hR : R ≤ r + |M₀| := by linarith [hrM.1]
  have hM0 := abs_nonneg M₀
  have hX : 0 ≤ C * Real.exp (|M₀| / 2) * ‖A‖ := by positivity
  rw [hev.self_of_nhds]
  refine ⟨posDef_of_inv hc₀ b1, b1, psd_mono ?_ b2, fun a b => ?_⟩
  · have h1 : R ≤ (1 + |M₀|) * r := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hC.le
    nlinarith
  · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' t) a b) (HodgeMetric.uncentre w₀ ρ π w) :=
      (GlobalTheory.T.period_gram_smooth_punctured n a₀ g _ Λ LP U hP.2.2.1 a b _ hu).comp _ (HodgeMetric.contDiff_uncentre 0 ρ' π').contDiffAt
    have h2 : (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) =ᶠ[nhds w]
        (fun t => HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' t) a b) ∘ HodgeMetric.uncentre w₀ ρ π := by
      filter_upwards [hev] with w' hw'
      rw [hw']
      rfl
    refine ⟨(h1.comp w (HodgeMetric.contDiff_uncentre w₀ ρ π).contDiffAt).congr_of_eventuallyEq h2, ?_⟩
    rw [h2.fderiv_eq, fderiv_comp w (h1.differentiableAt (by simp)) (hA w).differentiableAt, (hA w).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h3 : Real.exp (R / 2) ≤ Real.exp (|M₀| / 2) * Real.exp (r / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have h4 := (b3 a b).trans (mul_le_mul_of_nonneg_left h3 hC.le)
    have h5 := mul_le_mul_of_nonneg_right h4 (norm_nonneg A)
    have h6 : 0 ≤ C * (1 + |M₀|) * Real.exp (r / 2) := by positivity
    nlinarith
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelGlobalHeightIdentityStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_global_height_identity : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (Bat : FinHolAtlas n Rb.X), IsPotential Rb.A L → IsSection Rb.A L s → (∀ p, logNormSec L s p ≤ 0) → IsAdaptedAtlas Rb.A Bat L s → (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (k : Fin Bat.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → M.GoodAt F (mCoordIdeal (Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀))) → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (Bat.chart k).symm w ∉ bdry s → (baseGram tie F τ Rb ((Bat.chart k).symm w)).PosDef ∧ ((baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ)).PosSemidef ∧ (((C * rW L s ((Bat.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) - (baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w‖ ≤ C * Real.exp (rW L s ((Bat.chart k).symm w) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelResolutionIntegrability
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelResolutionIntegrability
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flagModel_resolution_integrability : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ hom : CMType H × Fin (D.p + D.q) → HermLine ι, (∀ p, (hom p).a = M.dy p) ∧ (∀ l, ∀ x ∈ O l \ bdry s, ∀ p, M.IsInducedAt (F l) (Rb.lift x x) p (blockG (baseGram tie (F l) p.1 Rb x)) (hom p)) ∧ ∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry s → SameOrbit (basePart M.blk z) (Rb.lift x x) → (hom p).h (fun q => starRingEnd ℂ (z q)) = (hom p).h z := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_hom | exact PositivityTheory.Xgp.t_c_bm_exists_hom
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelResolutionIntegrabilityStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_resolution_integrability : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ hom : CMType H × Fin (D.p + D.q) → HermLine ι, (∀ p, (hom p).a = M.dy p) ∧ (∀ l, ∀ x ∈ O l \ bdry s, ∀ p, M.IsInducedAt (F l) (Rb.lift x x) p (blockG (baseGram tie (F l) p.1 Rb x)) (hom p)) ∧ ∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry s → SameOrbit (basePart M.blk z) (Rb.lift x x) → (hom p).h (fun q => starRingEnd ℂ (z q)) = (hom p).h z := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flagModel_resolution_integrability | exact GlobalTheory.CompanionTheory.Relay.flagModel_resolution_integrability | (intros; apply GlobalTheory.CompanionTheory.Relay.flagModel_resolution_integrability <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelFrameHeightComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelFrameHeightComparison
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flagModel_frame_height_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (w : (Σ k, baseIdx ι M.blk k) → ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z w → 𝔐.Interior z → M.GoodAt F (mCoordIdeal w) → 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) (HodgeMetric.gramFn 𝔐 (gb tie F τ) w) ∧ (HodgeMetric.gramFn 𝔐 (gb tie F τ) w).PosDef ∧ ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
  first | exact @PositivityTheory.Xgp.t_c_bm_exists_gram | exact PositivityTheory.Xgp.t_c_bm_exists_gram
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelFrameHeightComparisonStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagModel_frame_height_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (w : (Σ k, baseIdx ι M.blk k) → ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z w → 𝔐.Interior z → M.GoodAt F (mCoordIdeal w) → 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) (HodgeMetric.gramFn 𝔐 (gb tie F τ) w) ∧ (HodgeMetric.gramFn 𝔐 (gb tie F τ) w).PosDef ∧ ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flagModel_frame_height_comparison | exact GlobalTheory.CompanionTheory.Relay.flagModel_frame_height_comparison | (intros; apply GlobalTheory.CompanionTheory.Relay.flagModel_frame_height_comparison <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockGBlockDiagPosDef
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockGBlockDiagPosDef
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

theorem blockG_isBlockDiag_posDef :
    ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef →
      IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef :=
  PositivityTheory.Xgp.t_c_bm_exists_blockpos

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockGBlockDiagPosDefStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockG_blockDiag_posDef : ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef → IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CutoffFunctionOnCompatibleAtlas
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CutoffFunctionOnCompatibleAtlas
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds : ∀ (n p q : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas n X) (Z Cl U : Set X) (r : X → ℝ) (Γ : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), A.Compatible B → (∀ k, Metric.closedBall (0 : Fin n → ℂ) 2 ⊆ (B.chart k).target) → (∀ x, ∃ k, x ∈ (B.chart k).source ∧ B.chart k x ∈ Metric.ball (0 : Fin n → ℂ) 1) → IsClosed Z → IsClosed Cl → IsOpen U → U ⊆ Cl → (∀ x, x ∉ Z → Real.exp 1 ≤ r x) → (∀ (k : Fin B.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → (B.chart k).symm w₀ ∈ Cl → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (B.chart k).symm w ∉ Z → (Γ ((B.chart k).symm w)).PosDef ∧ ((Γ ((B.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)).PosSemidef ∧ (((C * r ((B.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - (Γ ((B.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => Γ ((B.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => Γ ((B.chart k).symm w') a b) w‖ ≤ C * Real.exp (r ((B.chart k).symm w) / 2)) → (∀ a b, A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).re) ∧ A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).im)) ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → (∀ x ∈ Cl \ Z, (((r x ^ C : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ x)).PosSemidef ∧ (((r x ^ C : ℝ) : ℂ) • blockG (Γ x) - 1).PosSemidef) ∧ ∀ (a b : Fin (p + q)) (k : Fin B.n), ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2), (B.chart k).symm w ∈ Cl \ Z → ‖fderiv ℝ (fun w' => blockG (Γ ((B.chart k).symm w')) a b) w‖ ≤ C * r ((B.chart k).symm w) ^ C * Real.exp (r ((B.chart k).symm w) / 2) :=
  @PositivityTheory.Xgp.t_c_bm_exists_bounds
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CutoffFunctionOnCompatibleAtlasStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_function_on_compatible_atlas : ∀ (n p q : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas n X) (Z Cl U : Set X) (r : X → ℝ) (Γ : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), A.Compatible B → (∀ k, Metric.closedBall (0 : Fin n → ℂ) 2 ⊆ (B.chart k).target) → (∀ x, ∃ k, x ∈ (B.chart k).source ∧ B.chart k x ∈ Metric.ball (0 : Fin n → ℂ) 1) → IsClosed Z → IsClosed Cl → IsOpen U → U ⊆ Cl → (∀ x, x ∉ Z → Real.exp 1 ≤ r x) → (∀ (k : Fin B.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → (B.chart k).symm w₀ ∈ Cl → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (B.chart k).symm w ∉ Z → (Γ ((B.chart k).symm w)).PosDef ∧ ((Γ ((B.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)).PosSemidef ∧ (((C * r ((B.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - (Γ ((B.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => Γ ((B.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => Γ ((B.chart k).symm w') a b) w‖ ≤ C * Real.exp (r ((B.chart k).symm w) / 2)) → (∀ a b, A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).re) ∧ A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).im)) ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → (∀ x ∈ Cl \ Z, (((r x ^ C : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ x)).PosSemidef ∧ (((r x ^ C : ℝ) : ℂ) • blockG (Γ x) - 1).PosSemidef) ∧ ∀ (a b : Fin (p + q)) (k : Fin B.n), ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2), (B.chart k).symm w ∈ Cl \ Z → ‖fderiv ℝ (fun w' => blockG (Γ ((B.chart k).symm w')) a b) w‖ ≤ C * r ((B.chart k).symm w) ^ C * Real.exp (r ((B.chart k).symm w) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds | exact GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds | (intros; apply GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFiniteFrameCover
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFiniteFrameCover
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames

theorem exists_finite_good_frames : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), ∃ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι Ψ N M.Ω M.blk), (∀ l, IsOpen (O l)) ∧ (∀ x, ∃ l, x ∈ O l) ∧ (∀ l, M.IsFrame (F l)) ∧ ∀ l, ∀ x ∈ closure (O l), M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) := by
  exact @PositivityTheory.Xgp.t_c_bm_exists_frames

end GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFiniteFrameCoverStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_frame_cover : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), ∃ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι Ψ N M.Ω M.blk), (∀ l, IsOpen (O l)) ∧ (∀ x, ∃ l, x ∈ O l) ∧ (∀ l, M.IsFrame (F l)) ∧ ∀ l, ∀ x ∈ closure (O l), M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames.exists_finite_good_frames | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames.exists_finite_good_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames.exists_finite_good_frames <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricExistsOfGiven
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem card_cmType_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 0 < Fintype.card (CMType H) := by
  intro E _ _ _ H
  have h := (GlobalTheory.T.cm_host_rank_bounds E H).2.2
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  by_contra h0
  have h3 : Fintype.card (CMType H) = 0 := by omega
  simp_all

theorem exists_coordsAt_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (x : Rb.X), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z (Rb.lift x x) := by
  intro E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 n Rb x
  obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie _).1 (Rb.mem x x (Rb.mem_U x))
  exact ⟨z, hz⟩

theorem mem_bdry_conj_iff : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (x₀ : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)) (Rb : AnLogRes (mCoordIdeal x₀) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec z ∈ mcPts (mCoordIdeal x₀) ∩ mcPts bd) → ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → (p' ∈ bdry s ↔ p ∈ bdry s) := by
  intro K _ J _ Ω _ x₀ n bd Rb s hb htor hconj p p' ho
  obtain ⟨c, hc, e⟩ := ho
  have hm : ∀ p, Rb.lift p p ∈ mcPts (mCoordIdeal x₀) := fun p => Rb.mem p p (Rb.mem_U p)
  rw [hb p', hb p]
  constructor
  · intro h
    have h1 := hconj _ ⟨hm p', h⟩
    have h2 := htor _ h1 (fun k => (starRingEnd ℂ (c k))⁻¹) (fun k => inv_ne_zero ((map_ne_zero _).2 (hc k)))
    have e2 : GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul (fun k => (starRingEnd ℂ (c k))⁻¹)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec (Rb.lift p' p')) = Rb.lift p p := by
      funext q
      simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec]
      rw [e]
      simp [inv_mul_cancel_left₀, (map_ne_zero (starRingEnd ℂ)).2 (hc q.1)]
    rw [e2] at h2
    exact h2.2
  · intro h
    have h1 := hconj _ ⟨hm p, h⟩
    have h2 := htor _ h1 c hc
    have e2 : GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c
        (GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec (Rb.lift p p)) = Rb.lift p' p' := by
      funext q
      simp only [GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec]
      rw [e]
    rw [e2] at h2
    exact h2.2

theorem gramAt_sub {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} {L : LB G.left}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} {r r' : ℕ} {b : Fin r → Li} {Γ : Matrix (Fin r) (Fin r) ℂ}
    (h : M.GramAt L z b Γ) (e : Fin r' → Fin r) : M.GramAt L z (fun i => b (e i)) (Γ.submatrix e e) := by
  obtain ⟨v, hv, h'⟩ := h
  exact ⟨fun i => v (e i), fun i => hv _, fun p q => h' _ _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

theorem gb_wEmb (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) (a : Fin D.p) :
    gb tie F τ (wEmb D.p D.q a) = tie.wFrame F τ a := by
  simp only [gb, gbS, ← blockEquiv_inr, Equiv.symm_apply_apply, Sum.elim_inr]

theorem gb_omEmb (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) (a : Fin D.q) :
    gb tie F τ (omEmb D.p D.q a) = (dualFam tie F τ a : 𝔐.Li) := by
  simp only [gb, gbS, ← blockEquiv_inl, Equiv.symm_apply_apply, Sum.elim_inl]

theorem gramAt_wFrame (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ}
    (h : 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ) :
    𝔐.M.GramAt 𝔐.t.PP.L z (tie.wFrame F τ) (wBlock (blockG Γ)) := by
  rw [wBlock_blockG]
  have := gramAt_sub h (wEmb D.p D.q)
  simp only [gb_wEmb] at this
  exact this

theorem dualGramAt_omFrame (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ}
    (h : 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ) (hp : Γ.PosDef)
    (hd : ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0) :
    DualGramAt 𝔐.M 𝔐.t.PP.L z (𝔐.Vgen (.inr τ)) (tie.omFrame F τ) (omBlock (blockG Γ)) := by
  refine ⟨dualFam tie F τ, omBlock Γ, hd, ?_, ?_⟩
  · have := gramAt_sub h (omEmb D.p D.q)
    simp only [gb_omEmb] at this
    exact this
  · have hpos : (omBlock Γ).PosDef := hp.submatrix (omEmb_strictMono D.p D.q).injective
    have hu : IsUnit (omBlock Γ).det := (Matrix.isUnit_iff_isUnit_det _).1 hpos.isUnit
    rw [omBlock_blockG, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    exact Matrix.nonsing_inv_mul _ hu

theorem baseMetricExists_of_given : Given → PB.BaseMetricExists := by
  intro hG E _ _ _ H D l Xo₀ c Y S K _ ι _ Φ _ y M 𝔐 tie d hp hq hcov hsnc
  classical
  obtain ⟨Xo, rfl⟩ : ∃ Xo : ∀ l' : Level H, Moduli D l', Xo l = Xo₀ :=
    ⟨Function.update (fun l' => (hG.1.2.1 E H D l' (by omega)).some) l Xo₀, Function.update_self ..⟩
  classical
  set n := Fintype.card (CMType H) * D.p * D.q with hn
  have hn1 : 1 ≤ n := by
    have : 0 < Fintype.card (CMType H) := card_cmType_pos E H
    exact Nat.mul_pos (Nat.mul_pos this hp) hq
  obtain ⟨bd, hbd, hint⟩ := hsnc
  have harith := GlobalTheory.T.isArithVar_of_snc_model 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x n bd hn1 𝔐.tie hbd
  obtain ⟨hcl, htor, hconj⟩ := GlobalTheory.T.boundary_points_closed 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x
    (abLocus 𝔐.t.G) bd 𝔐.tie hint
  obtain ⟨Rb, L, s, nb, m, W, potL, sec, snc, norm_le, hbdry, hrconj⟩ :=
    GlobalTheory.T.lowerBound_height_on_boundary (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x n bd hbd harith hcl htor hconj
  obtain ⟨Bat, adapted⟩ := GlobalTheory.T.adapted_atlas_snc_section Rb.A L s m W potL sec snc norm_le
  have hInt : ∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) →
      (x ∉ bdry s ↔ 𝔐.Interior z) := fun x z hz => by
    rw [hbdry x, hint z _ hz, not_not]
  have hZ : IsClosed (bdry s) := GlobalTheory.T.isClosed_section_boundary n Rb.X Rb.A L s sec
  obtain ⟨q, O, F, hO, hOc, hF, hgood⟩ :=
    GlobalTheory.T.exists_finite_frame_cover K ι Φ y (CMType H) (D.p + D.q) D.p n M Rb
  have hgood' : ∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) :=
    fun l x hx => hgood l x (subset_closure hx)
  have hr : ∀ x, x ∉ bdry s → Real.exp 1 ≤ rW L s x := fun x _ => by
    have := norm_le x
    unfold rW
    linarith
  have hb := fun (i : Fin q) (τ : CMType H) => GlobalTheory.T.cutoff_function_on_compatible_atlas n D.p D.q Rb.X Rb.A Bat (bdry s) (closure (O i)) (O i) (rW L s)
    (baseGram tie (F i) τ Rb) adapted.1 adapted.2.1 adapted.2.2.1 hZ isClosed_closure (hO i) subset_closure hr
    (fun k w₀ hw₀ hc => GlobalTheory.T.flagModel_global_height_identity hG E H D Xo l c Y S K ι Φ y M 𝔐 tie n Rb L s Bat potL sec norm_le adapted hInt (F i)
      (hF i) τ k w₀ hw₀ (hgood i _ hc))
  choose C₀ hC₀ using fun i τ => (hb i τ).2
  obtain ⟨Cst, hCst⟩ : ∃ Cst : ℝ, ∀ i τ, C₀ i τ ≤ Cst := by
    refine ⟨∑ i, ∑ τ, |C₀ i τ|, fun i τ => ?_⟩
    calc C₀ i τ ≤ |C₀ i τ| := le_abs_self _
      _ ≤ ∑ τ, |C₀ i τ| := Finset.single_le_sum (f := fun τ => |C₀ i τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
      _ ≤ ∑ i, ∑ τ, |C₀ i τ| := Finset.single_le_sum (f := fun i => ∑ τ, |C₀ i τ|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hcoords : ∀ x : Rb.X, ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z (Rb.lift x x) := exists_coordsAt_lift E H D Xo l c Y S K ι Φ y M 𝔐 n Rb
  have hgr := fun (i : Fin q) (τ : CMType H) (x : Rb.X) (hx : x ∈ O i \ bdry s) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X)
      (hz : CoordsAt 𝔐.ξ M.x z (Rb.lift x x)) =>
    GlobalTheory.T.flagModel_frame_height_comparison E H D Xo l c Y S K ι Φ y M 𝔐 tie (F i) (hF i) τ (Rb.lift x x) z hz ((hInt x z hz).1 hx.2) (hgood' i x hx.1)
  obtain ⟨hom, hdeg, hind, hconjH⟩ := GlobalTheory.T.flagModel_resolution_integrability E H D Xo l c Y S K ι Φ y M 𝔐 tie n Rb s hInt q O F hOc hF hgood'
  have hper : ∀ i, ∀ x ∈ O i \ bdry s, ∃ V Pi, x ∈ V ∧
      IsPeriodOn Rb.A D.p V Pi (fun τ x' => blockG (baseGram tie (F i) τ Rb x')) := by
    intro i x hx
    have := fun τ => GlobalTheory.T.exists_local_holo_isPeriodGram_blockG_baseGram hG E H D Xo l c Y S K ι Φ y M 𝔐 tie hp hq n Rb s hInt hZ (F i) (hF i) τ x hx.2 (hgood' i x hx.1)
    choose V P hV hxV hP hPG using this
    refine ⟨⋂ τ, V τ, P, Set.mem_iInter.2 hxV, isOpen_iInter_of_finite hV, fun τ a b => ?_, fun τ x' hx' => hPG τ x' (Set.mem_iInter.1 hx' τ)⟩
    intro k
    exact (hP τ a b k).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.iInter_subset _ τ)))
  obtain ⟨lI, xI, hxI, VI, PiI, hxV, hPer, himm⟩ := GlobalTheory.T.flagModel_height_lower_estimate hG E H D Xo l c Y S K ι Φ y M 𝔐 tie hp hq d hcov Rb s hInt hZ q O F hO hOc hF hgood'
  refine ⟨{ Rb := Rb, L := L, s := s, nb := nb, m := m, W := W, potL := potL, sec := sec, snc := snc, norm_le := norm_le,
            Bat := Bat, adapted := adapted, q := q, O := O, O_open := hO, O_cover := hOc, F := F, isFrame := hF, good := hgood'
            G := fun i τ x => blockG (baseGram tie (F i) τ Rb x)
            G_pos := ?_, G_smooth := fun i τ a b => (hb i τ).1 a b
            Cst := Cst
            size := fun i τ x hx => ((hC₀ i τ Cst (hCst i τ)).1 x ⟨subset_closure hx.1, hx.2⟩)
            grad := fun i τ a b k w hw hx => (hC₀ i τ Cst (hCst i τ)).2 a b k w hw ⟨subset_closure hx.1, hx.2⟩
            period := hper
            immersion := ⟨lI, xI, hxI, VI, PiI, hxV, hPer, himm⟩
            hom := hom, hom_deg := hdeg, induced := hind }, ?_, ?_⟩
  · intro i τ x hx
    obtain ⟨z, hz⟩ := hcoords x
    exact GlobalTheory.T.blockG_blockDiag_posDef D.p D.q _ (hgr i τ x hx z hz).2.1
  · refine ⟨hInt, fun i τ x hx z hz => ?_, fun i τ x hx z hz => ?_⟩
    · exact gramAt_wFrame tie (F i) τ (hgr i τ x hx z hz).1
    · exact dualGramAt_omFrame tie (F i) τ (hgr i τ x hx z hz).1 (hgr i τ x hx z hz).2.1 (hgr i τ x hx z hz).2.2
  · refine ⟨fun x x' ho => ?_, fun p z hz x hx ho => hconjH p z hz x hx ho⟩
    exact ⟨mem_bdry_conj_iff (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x n bd Rb s hbdry htor hconj x x' ho, hrconj x x' ho⟩

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricExistsOfGivenStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_metric_exists_of_given : Given → PB.BaseMetricExists := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given <;> assumption)
end
