module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliSchemesExist

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpData
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg


open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 in
theorem exists_sec_ne_zero_int : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), ∃ t : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), t ≠ 0 := by
  intro E _ _ _ H L _ _ D
  have hS : SecBaseChangeAnySt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have := D.tK.semi.smooth
  have := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.tK.G.hom) (𝟙 _) (𝟙 _) D.tK.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected D.tK.G.hom (eSec D.tK.G (default : PrimeSpectrum L))
  obtain ⟨-, ws, gs', -⟩ := D.tK.sym
  obtain ⟨hprop, hamp, hkt⟩ := D.princ
  have eid : spMap (RingHom.id L) = 𝟙 (Sp L) := by
    simp [spMap]
  have hpb : IsPullback (𝟙 D.tK.G.left) D.tK.G.hom D.tK.G.hom (spMap (RingHom.id L)) := by
    rw [eid]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨β, hβ⟩ : ∃ β : LB.Sec D.tK.PP.L, ¬ ∀ y j, (𝟙 D.tK.G.left : D.tK.G.left ⟶ D.tK.G.left) y ∈ D.tK.PP.L.U j →
      gs (𝟙 D.tK.G.left) y _ (β.f j) = 0 := exists_sec_ne hS
    { A := D.tK.G, g := d, smoothDim := hd, L := D.tK.PP.L, isLB := D.tK.PP.isLB
      ample := hamp
      ktriv := hkt
      isAb := ⟨inferInstance, inferInstance, hprop, ‹_›⟩
      rigid := ⟨D.tK.PP.rig, D.tK.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ } (RingHom.id L) hpb
  obtain ⟨w, gw', -⟩ := D.m.lin
  have := D.t.semi.separated
  have := D.t.semi.quasiCompact
  have : CompactSpace D.t.G.left := QuasiCompact.compactSpace_of_compactSpace D.t.G.hom
  obtain ⟨a, ha, σ, hσ⟩ := exists_extend (nonZeroDivisors (𝓞 L)) D.m.cart.1 D.t.PP.isLB D.tK.PP.isLB
    ((isGen_iff w).1 gw') β
  obtain ⟨w₁, hw₁⟩ := exists_iso_linComb (F := 𝟙 D.t.G.left) D.t.PP.isLB (K := Fin 1) (fun _ => 𝟙 _)
    (fun _ => ((1 : ℕ) : ℤ)) (fun U _ k => by simp)
  have hM := linComb_isLB D.t.PP.L D.t.PP.isLB (K := Fin 1) (fun _ => 𝟙 D.t.G.left) (fun _ => ((1 : ℕ) : ℤ))
  obtain ⟨τ, hτ⟩ := sec_pull_down ((isGen_iff w₁).1 hw₁) D.t.PP.isLB hM σ
  refine ⟨τ, fun h0 => hβ fun y k hk => ?_⟩
  obtain ⟨j, hj⟩ := exists_chart D.t.PP.isLB (D.m.φ y)
  obtain ⟨k', hk'⟩ := exists_chart hM (D.m.φ y)
  have hz : LB.Sec.f τ k' = 0 := congrArg (fun s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _)
    (fun _ => ((1 : ℕ) : ℤ))) => LB.Sec.f s k') h0
  have e₁ := hτ _ D.m.φ y j k' hj hk'
  rw [hz, gs_zero _ y _ hk', mul_zero, Category.comp_id] at e₁
  have e₂ := hσ y j k hj hk
  rw [e₁, D.m.cart.1.w, cst_comp] at e₂
  have ha' : algebraMap (𝓞 L) L a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 (nonZeroDivisors.ne_zero ha)
  have u₁ : IsUnit (cst D.tK.G.hom y (algebraMap (𝓞 L) L a)) :=
    IsUnit.of_mul_eq_one (cst D.tK.G.hom y (algebraMap (𝓞 L) L a)⁻¹) (by
      rw [← cst_mul, mul_inv_cancel₀ ha', cst_one])
  exact (Units.isUnit _).mul_right_eq_zero.1 (u₁.mul_right_eq_zero.1 e₂.symm)

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_pp_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), ∃ t : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), t ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_sec_ne_zero_int <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleDivisibleAtPrime
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleDivisibleAtPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv

theorem mem_map_of_mem_primes {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A]
    (m : Ideal R) [hm : m.IsMaximal] (a : A)
    (h : ∀ P : Ideal A, P.IsPrime → m.map (algebraMap R A) ≤ P → a ∈ P) : a ∈ m.map (algebraMap R A) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hr : _root_.IsReduced ((R ⧸ m) ⊗[R] A) := isReduced_of_smooth_alg (R ⧸ m) _
  have hr' : _root_.IsReduced (A ⊗[R] (R ⧸ m)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R A (R ⧸ m)).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm R A (R ⧸ m)).injective
  have hq : _root_.IsReduced (A ⧸ m.map (algebraMap R A)) :=
    isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m).toRingEquiv.toRingHom
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m).injective
  have hrad : (m.map (algebraMap R A)).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2 hq
  refine hrad ?_
  rw [Ideal.radical_eq_sInf]
  refine Ideal.mem_sInf.2 ?_
  rintro P ⟨hP, hPp⟩
  exact h P hPp hP

theorem dvd_mul_of_mem_map {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (m : Ideal R) {c e : R}
    (h : ∀ π ∈ m, e ∣ c * π) {a : A} (ha : a ∈ m.map (algebraMap R A)) :
    algebraMap R A e ∣ algebraMap R A c * a := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨π, hπ, rfl⟩ := hx
    rw [← map_mul]
    exact map_dvd _ (h π hπ)
  | zero => rw [MulZeroClass.mul_zero]; exact dvd_zero _
  | add x y _ _ hx hy => rw [mul_add]; exact dvd_add hx hy
  | smul t x _ hx => rw [smul_eq_mul, mul_left_comm]; exact hx.mul_left _

theorem mem_basicOpen_map {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : X) :
    y ∈ X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) ↔ y ∈ V ∧ y ∈ X.basicOpen f := by
  have e : X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
    Scheme.basicOpen_res X f (homOfLE h).op
  rw [e]
  rfl

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem mem_basicOpen_top_of_notMem (p : X ⟶ Sp R) (x : X) {r : R} (hx : r ∉ (p x).asIdeal) :
    x ∈ X.basicOpen ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have hmem : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    have e := basicOpen_eq_of_affine (R := CommRingCat.of R) r
    exact (congrArg (fun U : (Sp R).Opens => p x ∈ U) e).mpr hx
  rw [← Scheme.preimage_basicOpen]
  exact hmem

theorem isUnit_cst_of_notMem (p : X ⟶ Sp R) (x : X) {r : R} (hx : r ∉ (p x).asIdeal) : IsUnit (cst p x r) := by
  have hu := (Scheme.mem_basicOpen X ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) x
    (show x ∈ p ⁻¹ᵁ ⊤ from trivial)).1 (mem_basicOpen_top_of_notMem p x hx)
  rw [cst, gs_eq p x ⊤ (show p x ∈ (⊤ : (Sp R).Opens) from trivial)]
  exact hu

theorem cst_mul (p : X ⟶ Sp R) (x : X) (a b : R) : cst p x (a * b) = cst p x a * cst p x b := by
  simp only [cst, map_mul]
  exact gs_mul p x ⊤ trivial _ _

theorem exists_smul_eq_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Sp R) [Smooth p] (M : LB X) (b : Sp R), b.asIdeal.IsMaximal → ∀ u : SecMod p M, (∀ y : X, p y = b → y ∉ Out.nonzeroLocus (M := M) u) → ∀ c e : R, e ≠ 0 → (∀ π ∈ b.asIdeal, e ∣ c * π) → ∃ u' : SecMod p M, e • u' = c • u := by
  intro R _ _ X p _ M b hb u hu c e he hdiv
  have key : ∀ j, ∀ x ∈ M.U j, cst p x e ∣ gs (𝟙 X) x (M.U j) (LB.Sec.f (c • u : SecMod p M) j) := by
    intro j x hx
    rw [smul_f, gs_mul _ x _ hx, gs_constFn p _ _ x hx, Category.id_comp]
    by_cases hxb : b.asIdeal ≤ (p x).asIdeal
    ·
      obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := M.U j) (x := x) hx
      have hle : V ≤ M.U j := hVU
      have sm := HasRingHomProperty.appLE @Smooth p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
      have sm' : RingHom.Smooth ((p.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
        RingHom.Smooth.comp
          (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective) sm
      letI := ((p.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
      have : Algebra.Smooth R Γ(X, V) := sm'
      have hconst : ∀ r : R, algebraMap R Γ(X, V) r = constFn p V r := fun _ => rfl
      have hmem : (X.presheaf.map (homOfLE hle).op).hom (LB.Sec.f u j) ∈ b.asIdeal.map (algebraMap R Γ(X, V)) := by
        have := hb
        refine mem_map_of_mem_primes b.asIdeal _ fun P hP hbP => ?_
        let y : X := hV.fromSpec (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))
        have hbo : ∀ f : Γ(X, V), y ∈ X.basicOpen f ↔ f ∉ P := fun f => by
          have e := hV.fromSpec_preimage_basicOpen f
          have e' := congrArg (fun O : (Spec Γ(X, V)).Opens => (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ∈ O) e
          exact iff_of_eq e'
        have hyV : y ∈ V := by
          have h4 : y ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
          rw [hV.range_fromSpec] at h4
          exact h4
        have hcl : p y = b := by
          have hle' : b.asIdeal ≤ (p y).asIdeal := fun π hπ => by
            by_contra hn
            have h2 := mem_basicOpen_top_of_notMem p y hn
            have h3 : y ∈ X.basicOpen (constFn p V π) := by
              have e : constFn p V π = (X.presheaf.map (homOfLE le_top).op).hom
                  ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)) := rfl
              rw [e]
              exact (mem_basicOpen_map le_top _ y).2 ⟨hyV, h2⟩
            exact (hbo _).1 h3 (hbP (Ideal.mem_map_of_mem _ hπ))
          exact PrimeSpectrum.ext (hb.eq_of_le (p y).isPrime.ne_top hle').symm
        by_contra hn
        have h1 := (hbo _).2 hn
        exact hu y hcl (TopologicalSpace.Opens.mem_iSup.2 ⟨j, ((mem_basicOpen_map hle _ y).1 h1).2⟩)
      obtain ⟨t, ht⟩ := dvd_mul_of_mem_map b.asIdeal hdiv hmem
      refine ⟨gs (𝟙 X) x V t, ?_⟩
      have e' := congrArg (gs (𝟙 X) x V) ht
      rw [hconst, hconst, gs_mul _ x _ hxV, gs_mul _ x _ hxV, gs_constFn p _ _ x hxV, gs_constFn p _ _ x hxV,
        gs_res _ x _ hxV, Category.id_comp] at e'
      exact e'
    ·
      obtain ⟨π, hπ, hπx⟩ := Set.not_subset.1 hxb
      have hunit := isUnit_cst_of_notMem p x hπx
      obtain ⟨t, ht⟩ := hdiv π hπ
      have h1 : cst p x e ∣ cst p x c * cst p x π := by
        rw [← cst_mul, ht, cst_mul]
        exact dvd_mul_right _ _
      exact ((hunit.dvd_mul_right).1 h1).mul_right _
  obtain ⟨s', hs'⟩ := exists_div_sec p he (show LB.Sec M from (c • u : SecMod p M)) key
  exact ⟨s', SecMod.ext fun j => (hs' j).symm⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleDivisibleAtPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_module_divisible_at_prime : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Sp R) [Smooth p] (M : LB X) (b : Sp R), b.asIdeal.IsMaximal → ∀ u : SecMod p M, (∀ y : X, p y = b → y ∉ Out.nonzeroLocus (M := M) u) → ∀ c e : R, e ≠ 0 → (∀ π ∈ b.asIdeal, e ∣ c * π) → ∃ u' : SecMod p M, e • u' = c • u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv.exists_smul_eq_smul | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv.exists_smul_eq_smul | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv.exists_smul_eq_smul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleBoundedDenominator
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleBoundedDenominator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom

theorem exists_den {R A : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (φ : R →+* A) {f : A} (hf : f ≠ 0) (T : Set (R × R × A))
    (hT : ∀ q ∈ T, q.2.1 ≠ 0 ∧ φ q.2.1 * q.2.2 = φ q.1 * f) :
    ∃ D : R, D ≠ 0 ∧ ∀ q ∈ T, φ q.2.1 ∣ φ (D * q.1) := by
  classical
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    ((fun q : R × R × A => q.2.2) '' T)).1
    (IsNoetherian.noetherian (Ideal.span ((fun q : R × R × A => q.2.2) '' T)))
  have hex : ∀ g ∈ s, ∃ q ∈ T, q.2.2 = g := fun g hg => by
    obtain ⟨q, hq, rfl⟩ := hsS hg
    exact ⟨q, hq, rfl⟩
  choose! q hqT hqg using hex
  refine ⟨∏ g ∈ s, (q g).2.1, Finset.prod_ne_zero_iff.2 fun g hg => (hT _ (hqT g hg)).1, ?_⟩
  set D := ∏ g ∈ s, (q g).2.1 with hD
  have key : ∀ a ∈ Submodule.span A (s : Set A), ∃ b, φ D * a = b * f := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem g hg =>
      have hg' : g ∈ s := hg
      refine ⟨φ (∏ g' ∈ s.erase g, (q g').2.1) * φ (q g).1, ?_⟩
      have e := (hT _ (hqT g hg')).2
      rw [hqg g hg'] at e
      rw [hD, ← Finset.prod_erase_mul s _ hg', map_mul, _root_.mul_assoc, e, _root_.mul_assoc]
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [mul_add, ha', hb', add_mul]⟩
    | smul c a _ ha =>
      obtain ⟨a', ha'⟩ := ha
      refine ⟨c * a', ?_⟩
      rw [smul_eq_mul, mul_left_comm, ha', _root_.mul_assoc]
  intro r hr
  obtain ⟨b, hb⟩ := key r.2.2 (by
    rw [← hs]
    exact Ideal.subset_span ⟨r, hr, rfl⟩)
  refine ⟨b, mul_right_cancel₀ hf ?_⟩
  have e := (hT r hr).2
  calc φ (D * r.1) * f = φ D * (φ r.1 * f) := by rw [map_mul, _root_.mul_assoc]
    _ = φ r.2.1 * (φ D * r.2.2) := by rw [← e, mul_left_comm]
    _ = φ r.2.1 * b * f := by rw [hb, _root_.mul_assoc]

variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}}

theorem f_ne_zero [IsIntegral X] {p : X ⟶ Sp R} {M : LB X} {t : SecMod p M} {i j : M.ι}
    (hi : LB.Sec.f t i ≠ 0) (hj : (M.U j : Set X).Nonempty) : LB.Sec.f t j ≠ 0 := by
  intro h0
  have hine : (M.U i : Set X).Nonempty := by
    by_contra hc
    have hb : M.U i = ⊥ := by
      ext x
      simp only [Set.not_nonempty_iff_eq_empty] at hc
      simp [hc]
    have : Subsingleton Γ(X, M.U i) := by
      rw [hb]
      infer_instance
    exact hi (Subsingleton.elim _ _)
  have hne : ((M.U i ⊓ M.U j : X.Opens) : Set X).Nonempty :=
    nonempty_preirreducible_inter (M.U i).isOpen (M.U j).isOpen hine hj
  have : Nonempty (M.U i ⊓ M.U j : X.Opens) := hne.to_subtype
  have e := LB.Sec.compat t i j
  rw [h0, map_zero, MulZeroClass.mul_zero] at e
  refine hi (map_injective_of_isIntegral X (homOfLE (inf_le_left : M.U i ⊓ M.U j ≤ M.U i)) ?_)
  exact e.trans (map_zero _).symm

theorem exists_den_open [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp R) (M : LB X) (t : SecMod p M) (j : M.ι)
    (V : X.Opens) (hV : IsAffineOpen V) (hne : (V : Set X).Nonempty) (hVj : V ≤ M.U j) (ht : LB.Sec.f t j ≠ 0) :
    ∃ D : R, D ≠ 0 ∧ ∀ (x d : R) (u : SecMod p M), d ≠ 0 → d • u = x • t →
      constHom p V d ∣ constHom p V (D * x) := by
  have : Nonempty V := hne.to_subtype
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let r := (X.presheaf.map (homOfLE hVj).op).hom
  have hinj : Function.Injective r := map_injective_of_isIntegral X (homOfLE hVj)
  obtain ⟨D, hD, h⟩ := exists_den (constHom p V) (f := r (LB.Sec.f t j))
    (fun h0 => ht (hinj (by rw [map_zero]; exact h0)))
    {q | q.2.1 ≠ 0 ∧ constHom p V q.2.1 * q.2.2 = constHom p V q.1 * r (LB.Sec.f t j)} fun q hq => hq
  refine ⟨D, hD, fun x d u hd e => h (x, d, r (LB.Sec.f u j)) ⟨hd, ?_⟩⟩
  have e' := congrArg r (congrArg (fun s : SecMod p M => LB.Sec.f s j) e)
  simp only [smul_f, r, map_mul, res_constFn] at e'
  exact e'

theorem dvd_of_forall_point (p : X ⟶ Sp R) [Flat p] (hp : Function.Surjective p) {a b : R} (ha : a ≠ 0)
    (h : ∀ y : X, cst p y a ∣ cst p y b) : a ∣ b := by
  have hh : ∀ z ∈ (⊤ : (Sp R).Opens), cst (𝟙 (Sp R)) z a ∣
      gs (𝟙 (Sp R)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) := by
    intro z _
    obtain ⟨y, rfl⟩ := hp z
    apply dvd_descend p y
    rw [cst, ← gs_stalkMap p y ⊤ trivial, ← gs_stalkMap p y ⊤ trivial]
    exact h y
  obtain ⟨g, hg⟩ := exists_div (𝟙 (Sp R)) ha ⊤ _ hh
  have e : constFn (𝟙 (Sp R)) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := by
    have e₀ : (𝟙 (Sp R) : Sp R ⟶ Sp R).appLE ⊤ ⊤ (fun _ _ => trivial) = 𝟙 _ := by
      simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
      exact (Sp R).presheaf.map_id _
    rw [constFn, e₀]
    rfl
  rw [e] at hg
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom g, ?_⟩
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hg
  simpa using this

theorem bounded_denominators : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G]
    [Smooth G.hom] [GeometricallyConnected G.hom] [QuasiCompact G.hom] (M : LB G.left), M.IsLB →
    ∀ t : SecMod G.hom M, t ≠ 0 → ∃ d₀ : R, d₀ ≠ 0 ∧ ∀ (x d : R) (u : SecMod G.hom M), d ≠ 0 → d • u = x • t →
      d ∣ d₀ * x := by
  classical
  intro R _ _ _ G _ _ _ _ M hM t ht
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hsurj : Function.Surjective G.hom := (inferInstance : Surjective G.hom).surj
  obtain ⟨i₀, hi₀⟩ : ∃ i, LB.Sec.f t i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ht (SecMod.ext fun i => by rw [hc i]; rfl)
  have hc : ∀ y : G.left, ∃ j, y ∈ M.U j := fun y => by
    have : y ∈ (⨆ i, M.U i : G.left.Opens) := by rw [hM.cover]; trivial
    simpa using this
  choose j hj using hc
  have hV : ∀ y : G.left, ∃ V : G.left.Opens, IsAffineOpen V ∧ y ∈ V ∧ V ≤ M.U (j y) := fun y => by
    obtain ⟨V, hVa, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (hj y)
    exact ⟨V, hVa, hy, hle⟩
  choose V hVa hVy hVj using hV
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover (fun y => (V y : Set G.left))
    (fun y => (V y).isOpen.mem_nhds (hVy y))
  have hD := fun y => exists_den_open G.hom M t (j y) (V y) (hVa y) ⟨y, hVy y⟩ (hVj y)
    (f_ne_zero hi₀ ⟨y, hj y⟩)
  choose D hD0 hD using hD
  refine ⟨∏ y ∈ s, D y, Finset.prod_ne_zero_iff.2 fun y _ => hD0 y, fun x d u hd e => ?_⟩
  refine dvd_of_forall_point G.hom hsurj hd fun y => ?_
  obtain ⟨w, hw, hyw⟩ : ∃ w ∈ s, y ∈ V w := by
    have : y ∈ ⋃ x ∈ s, (V x : Set G.left) := by rw [hs]; trivial
    simpa using this
  have h₁ : constHom G.hom (V w) d ∣ constHom G.hom (V w) ((∏ y ∈ s, D y) * x) := by
    refine (hD w x d u hd e).trans (map_dvd _ ?_)
    exact mul_dvd_mul_right (Finset.dvd_prod_of_mem _ hw) _
  obtain ⟨c, hc⟩ := h₁
  have e' := congrArg (gs (𝟙 G.left) y (V w)) hc
  rw [constHom_apply, constHom_apply, gs_mul _ y _ hyw, gs_constFn _ _ _ y hyw, gs_constFn _ _ _ y hyw,
    Category.id_comp] at e'
  exact ⟨_, e'⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleBoundedDenominatorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_module_bounded_denominator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] [QuasiCompact G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∃ d₀ : R, d₀ ≠ 0 ∧ ∀ (x d : R) (u : SecMod G.hom M), d ≠ 0 → d • u = x • t → d ∣ d₀ * x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom.bounded_denominators | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom.bounded_denominators | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom.bounded_denominators <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibre
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen

theorem exists_generic_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  intro R _ _ _ G _ _ _ M hM t ht b hb
  haveI hI : IsIntegral (Sp R) := by unfold Sp; infer_instance
  haveI hN : IsLocallyNoetherian (Sp R) := by unfold Sp; infer_instance
  haveI hGI : GeometricallyIntegral G.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres G.hom
  haveI hGR : GeometricallyReduced G.hom := inferInstance
  haveI hRed : AlgebraicGeometry.IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.hom
  have hgen : GeneralizingMap G.hom.base := Flat.generalizingMap G.hom
  have hne : ∃ y, y ∈ Out.nonzeroLocus (M := M) t := by
    by_contra hcon
    simp only [not_exists] at hcon
    apply ht
    apply SecMod.ext
    intro k
    rw [zero_f, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    exact absurd (by unfold Out.nonzeroLocus; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hy⟩) (hcon y)
  obtain ⟨y, hy⟩ := hne
  have hle : b.asIdeal ≤ (G.hom.base y).asIdeal := by rw [hb]; exact bot_le
  have hsp : b ⤳ G.hom.base y := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨y', hy'sp, hy'eq⟩ := hgen hsp
  exact ⟨y', hy'eq, hy'sp.mem_open (Out.nonzeroLocus (M := M) t).isOpen hy⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_section_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalExtensionProjectiveModule
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalExtensionProjectiveModule
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Basis

theorem projective_of_torsionFree {R M : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.IsTorsionFree R M] : Module.Projective R M := by
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite _ _
  haveI : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  exact Module.Flat.projective_of_finitePresentation

theorem finrank_ideal {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (hI : I ≠ ⊥) :
    Module.finrank R I = 1 := by
  have h := Submodule.finrank_quotient_add_finrank I
  have h0 : Module.finrank R (R ⧸ I) = 0 := by
    rw [Module.finrank_eq_zero_iff]
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    intro x
    refine ⟨a, ha0, ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact I.mul_mem_right y ha
  rw [h0, zero_add, Module.finrank_self] at h
  exact h

theorem exists_ideal_cover {R : Type} [CommRing R] [IsDedekindDomain R] (g : ℕ) :
    ∀ (B : Type) [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.IsTorsionFree R B],
      Module.finrank R B = g →
      ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal R) (b : ∀ i, I i →ₗ[R] B),
        Fintype.card ι = g ∧ (∀ i, I i ≠ ⊥) ∧ ⨆ i, LinearMap.range (b i) = ⊤ := by
  induction g with
  | zero =>
    intro B _ _ _ _ hB
    have hs : Subsingleton B := by
      refine subsingleton_of_forall_eq 0 fun x => ?_
      obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.1 hB x
      exact (smul_eq_zero.1 hax).resolve_left ha
    refine ⟨Empty, inferInstance, Empty.elim, fun i => i.elim, Fintype.card_empty, fun i => i.elim, ?_⟩
    exact Subsingleton.elim _ _
  | succ g ih =>
    intro B _ _ _ _ hB
    haveI : Module.Projective R B := projective_of_torsionFree
    haveI : Nontrivial B := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      rw [Module.finrank_zero_of_subsingleton] at hB
      omega
    obtain ⟨x, hx⟩ := exists_ne (0 : B)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero R hx
    let J : Ideal R := LinearMap.range f
    have hJ : J ≠ ⊥ := fun h => hf (by
      have : f x ∈ J := ⟨x, rfl⟩
      rw [h] at this
      simpa using this)
    haveI : Module.Projective R J := projective_of_torsionFree
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
      (LinearMap.range_rangeRestrict f)
    have hrank : Module.finrank R (LinearMap.ker f) = g := by
      have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
      rw [f.quotKerEquivRange.finrank_eq, hB] at h1
      have h2 : Module.finrank R (LinearMap.range f) = 1 := finrank_ideal J hJ
      omega
    obtain ⟨ι, _, I, b, hc, hI, hsup⟩ := ih (LinearMap.ker f) hrank
    let I' : Option ι → Ideal R := fun o => o.elim J I
    let b' : ∀ o, I' o →ₗ[R] B := fun o => match o with
      | none => s
      | some i => (LinearMap.ker f).subtype ∘ₗ b i
    refine ⟨Option ι, inferInstance, I', b', by simp [hc], ?_, ?_⟩
    · rintro (_ | i)
      · exact hJ
      · exact hI i
    · set T : Submodule R B := ⨆ o, LinearMap.range (b' o) with hT
      have hker : (⨆ i, LinearMap.range (b i)) ≤ T.comap (LinearMap.ker f).subtype := by
        refine iSup_le fun i => ?_
        rintro _ ⟨a, rfl⟩
        exact Submodule.mem_iSup_of_mem (some i) ⟨a, rfl⟩
      rw [hsup] at hker
      rw [eq_top_iff]
      intro z _
      have hz : f (z - s (f.rangeRestrict z)) = 0 := by
        have h3 : f.rangeRestrict (s (f.rangeRestrict z)) = f.rangeRestrict z :=
          LinearMap.congr_fun hs _
        have h4 : f (s (f.rangeRestrict z)) = f z := congrArg Subtype.val h3
        rw [map_sub, h4, sub_self]
      have h5 : z - s (f.rangeRestrict z) ∈ T :=
        hker (Submodule.mem_top (x := (⟨_, hz⟩ : LinearMap.ker f)))
      have h6 : s (f.rangeRestrict z) ∈ T :=
        Submodule.mem_iSup_of_mem none ⟨f.rangeRestrict z, rfl⟩
      simpa using T.add_mem h5 h6

theorem span_of_root (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (h : ℕ) (hh : h ≠ 0) (c : 𝓞 K)
    (hc : I ^ h = Ideal.span {c}) (z : K') (hz : z ^ h = algebraMap K K' (c : K)) :
    ∃ y : 𝓞 K', y ≠ 0 ∧ I.map (algebraMap (𝓞 K) (𝓞 K')) = Ideal.span {y} := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero] at hc
    exact pow_ne_zero h hI hc
  have hcK : (c : K) ≠ 0 := fun h0 => hc0 (RingOfIntegers.ext h0)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hh] at hz
    exact hcK ((map_eq_zero _).mp hz.symm)
  have hint : IsIntegral ℤ z := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hh) ?_
    rw [hz]
    exact (c.2 : IsIntegral ℤ (c : K)).map (IsScalarTower.toAlgHom ℤ K K')
  let y : 𝓞 K' := ⟨z, hint⟩
  have hyz : (y : K') = z := rfl
  have hy0 : y ≠ 0 := fun h0 => hz0 (by rw [← hyz, h0]; rfl)
  have hyc : y ^ h = algebraMap (𝓞 K) (𝓞 K') c := by
    apply RingOfIntegers.ext
    exact (map_pow (algebraMap (𝓞 K') K') y h).trans hz
  have hspan : Ideal.span {y} ^ h = (I.map (algebraMap (𝓞 K) (𝓞 K'))) ^ h := by
    rw [Ideal.span_singleton_pow, hyc, ← Ideal.map_pow, hc, Ideal.map_span, Set.image_singleton]
  have hs0 : Ideal.span {y} ≠ ⊥ := by simpa using hy0
  refine ⟨y, hy0, (GlobalTheory.CompanionTheory.Lines.ideal_eq_of_pow_eq hh hs0 ?_ hspan).symm⟩
  intro h0
  rw [h0, ← Ideal.zero_eq_bot, zero_pow hh] at hspan
  exact pow_ne_zero h hs0 hspan

theorem exists_extension_principal {ι : Type} [Fintype ι] (L : Type) [Field L] [NumberField L]
    (J : ι → Ideal (𝓞 L)) (hJ : ∀ i, J i ≠ ⊥) :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : ι → 𝓞 L'),
      ∀ i, y i ≠ 0 ∧ (J i).map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y i} := by
  classical
  choose h c hh hc using fun i => GlobalTheory.UnRep.exists_pow_eq_span_singleton L (J i) (hJ i)
  let q : ι → Polynomial L := fun i => Polynomial.X ^ h i - Polynomial.C (c i : L)
  let p : Polynomial L := ∏ i, q i
  have hq0 : ∀ i, q i ≠ 0 := fun i => Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (hh i)) _
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hq0 i
  haveI : FiniteDimensional ℚ p.SplittingField := FiniteDimensional.trans ℚ L p.SplittingField
  haveI : NumberField p.SplittingField := NumberField.mk
  have hroot : ∀ i, ∃ z : p.SplittingField, z ^ h i = algebraMap L p.SplittingField (c i : L) := by
    intro i
    have hdvd : (q i).map (algebraMap L p.SplittingField) ∣ p.map (algebraMap L p.SplittingField) :=
      Polynomial.map_dvd _ (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    have hsp := (Polynomial.SplittingField.splits p).of_dvd
      (Polynomial.map_ne_zero hp0) hdvd
    have hdeg : (q i).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero (hh i))]
      exact_mod_cast hh i
    obtain ⟨z, hz⟩ := hsp.exists_eval_eq_zero (by rwa [Polynomial.degree_map])
    exact ⟨z, by simpa [q, sub_eq_zero] using hz⟩
  choose z hz using hroot
  choose y hy using fun i => span_of_root L p.SplittingField (J i) (hJ i) (h i) (hh i) (c i) (hc i)
    (z i) (hz i)
  exact ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, y, hy⟩

theorem exists_image_element {R R' B B' : Type} [CommRing R] [CommRing R'] [AddCommGroup B]
    [Module R B] [AddCommGroup B'] [Module R' B'] (φ : R →+* R') (I : Ideal R) (b : I →ₗ[R] B)
    (io : B →ₛₗ[φ] B') (x : R') (hx : x ∈ I.map φ) :
    ∃ e : B', ∀ a : I, φ a • e = x • io (b a) := by
  have hx' : x ∈ Submodule.span R' (φ '' (I : Set R)) := hx
  induction hx' using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a', ha', rfl⟩ := h
    refine ⟨io (b ⟨a', ha'⟩), fun a => ?_⟩
    have h1 : (a : R) • (⟨a', ha'⟩ : I) = a' • a := Subtype.ext (by simp [mul_comm])
    have h2 : (a : R) • b ⟨a', ha'⟩ = a' • b a := by
      rw [← b.map_smul, ← b.map_smul, h1]
    calc φ a • io (b ⟨a', ha'⟩) = io ((a : R) • b ⟨a', ha'⟩) := (io.map_smulₛₗ _ _).symm
      _ = io (a' • b a) := by rw [h2]
      _ = φ a' • io (b a) := io.map_smulₛₗ _ _
  | zero => exact ⟨0, fun a => by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨e₁, h₁⟩ := hu (by assumption)
    obtain ⟨e₂, h₂⟩ := hv (by assumption)
    exact ⟨e₁ + e₂, fun a => by rw [smul_add, h₁, h₂, add_smul]⟩
  | smul r u _ hu =>
    obtain ⟨e, h⟩ := hu (by assumption)
    exact ⟨r • e, fun a => by rw [smul_comm, h, smul_smul, smul_eq_mul]⟩

theorem exists_spanning {R R' B B' ι : Type} [CommRing R] [CommRing R'] [IsDomain R']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R' B'] [Module.IsTorsionFree R' B']
    (φ : R →+* R') (I : ι → Ideal R) (b : ∀ i, I i →ₗ[R] B)
    (hsup : ⨆ i, LinearMap.range (b i) = ⊤) (io : B →ₛₗ[φ] B')
    (hspan : Submodule.span R' (Set.range io) = ⊤) (y : ι → R') (hy0 : ∀ i, y i ≠ 0)
    (hy : ∀ i, (I i).map φ = Ideal.span {y i}) :
    ∃ e : ι → B', Submodule.span R' (Set.range e) = ⊤ := by
  choose e he using fun i => exists_image_element φ (I i) (b i) io (y i)
    (by rw [hy i]; exact Ideal.mem_span_singleton_self _)
  refine ⟨e, ?_⟩
  set S := Submodule.span R' (Set.range e) with hS
  have hle : (⨆ i, LinearMap.range (b i)) ≤ S.comap io := by
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    have hmem : φ a ∈ (I i).map φ := Ideal.mem_map_of_mem φ a.2
    rw [hy i, Ideal.mem_span_singleton'] at hmem
    obtain ⟨r, hr⟩ := hmem
    have h1 := he i a
    rw [← hr, mul_comm, mul_smul] at h1
    have h2 : r • e i = io (b i a) := smul_right_injective B' (hy0 i) h1
    change io (b i a) ∈ S
    rw [← h2]
    exact S.smul_mem r (Submodule.subset_span ⟨i, rfl⟩)
  rw [hsup] at hle
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, rfl⟩
  exact hle (Submodule.mem_top (x := x))

theorem linearIndependent_of_span_card {R M ι : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Fintype ι] (e : ι → M)
    (hs : Submodule.span R (Set.range e) = ⊤) (hc : Fintype.card ι = Module.finrank R M) :
    LinearIndependent R e := by
  classical
  let f : (ι → R) →ₗ[R] M := Fintype.linearCombination R e
  have hr : LinearMap.range f = ⊤ := by
    rw [Fintype.range_linearCombination, hs]
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  rw [f.quotKerEquivRange.finrank_eq, hr, finrank_top, Module.finrank_pi, hc] at h1
  have h0 : Module.finrank R (LinearMap.ker f) = 0 := by omega
  have hk : LinearMap.ker f = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.1 h0 ⟨x, hx⟩
    have h2 : a • x = 0 := congrArg Subtype.val hax
    exact (smul_eq_zero.1 h2).resolve_left ha
  refine Fintype.linearIndependent_iff.2 fun c hcz i => ?_
  have hmem : c ∈ LinearMap.ker f := by
    simpa [f, Fintype.linearCombination_apply] using hcz
  rw [hk, Submodule.mem_bot] at hmem
  exact congrFun hmem i

theorem exists_basis_after_extension : ∀ (L : Type) [Field L] [NumberField L] (B : Type) [AddCommGroup B] [Module (𝓞 L) B] [Module.Finite (𝓞 L) B] [Module.Projective (𝓞 L) B] (I : Ideal (𝓞 L)), I ≠ ⊥ → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : 𝓞 L'), I.map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y} ∧ ∀ (B' : Type) [AddCommGroup B'] [Module (𝓞 L') B'] [Module.Finite (𝓞 L') B'] [Module.Projective (𝓞 L') B'] (io : B →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] B'), Submodule.span (𝓞 L') (Set.range io) = ⊤ → Module.finrank (𝓞 L') B' = Module.finrank (𝓞 L) B → ∃ e : Fin (Module.finrank (𝓞 L') B') → B', LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  intro L _ _ B _ _ _ _ I hI
  haveI : Module.IsTorsionFree (𝓞 L) B := Module.Flat.isTorsionFree
  obtain ⟨ι, _, J, b, hc, hJ, hsup⟩ := exists_ideal_cover (Module.finrank (𝓞 L) B) B rfl
  obtain ⟨L', _, _, _, y, hy⟩ := exists_extension_principal L (fun o : Option ι => o.elim I J)
    (by rintro (_ | i); exacts [hI, hJ i])
  refine ⟨L', inferInstance, inferInstance, inferInstance, y none, (hy none).2, ?_⟩
  intro B' _ _ _ _ io hspan hrk
  haveI : Module.IsTorsionFree (𝓞 L') B' := Module.Flat.isTorsionFree
  obtain ⟨e, he⟩ := exists_spanning (algebraMap (𝓞 L) (𝓞 L')) J b hsup io hspan
    (fun i => y (some i)) (fun i => (hy (some i)).1) (fun i => (hy (some i)).2)
  have hli : LinearIndependent (𝓞 L') e :=
    linearIndependent_of_span_card e he (hc.trans hrk.symm)
  let ε : Fin (Module.finrank (𝓞 L') B') ≃ ι :=
    (Fintype.equivFinOfCardEq (hc.trans hrk.symm)).symm
  refine ⟨e ∘ ε, hli.comp _ ε.injective, ?_⟩
  rw [Set.range_comp, ε.surjective.range_eq, Set.image_univ, he]

end GlobalTheory.CompanionTheory.Ar.Basis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalExtensionProjectiveModuleStatement
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_extension_projective_module : ∀ (L : Type) [Field L] [NumberField L] (B : Type) [AddCommGroup B] [Module (𝓞 L) B] [Module.Finite (𝓞 L) B] [Module.Projective (𝓞 L) B] (I : Ideal (𝓞 L)), I ≠ ⊥ → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : 𝓞 L'), I.map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y} ∧ ∀ (B' : Type) [AddCommGroup B'] [Module (𝓞 L') B'] [Module.Finite (𝓞 L') B'] [Module.Projective (𝓞 L') B'] (io : B →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] B'), Submodule.span (𝓞 L') (Set.range io) = ⊤ → Module.finrank (𝓞 L') B' = Module.finrank (𝓞 L) B → ∃ e : Fin (Module.finrank (𝓞 L') B') → B', LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension | exact GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension | (intros; apply GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSectionNotInSet
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSectionNotInSet
open NumberField

namespace GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes

theorem exists_multiple_not_mem :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M], (∀ (a : R) (m : M), a ≠ 0 → a • m = 0 → m = 0) → ∀ t : M, t ≠ 0 → ∀ d₀ : R, d₀ ≠ 0 → (∀ (x d : R) (u : M), d ≠ 0 → d • u = x • t → d ∣ d₀ * x) → ∀ (V : Set M) (P : Ideal R), P.IsMaximal → P ≠ ⊥ → (∀ u ∈ V, ∀ c e : R, e ≠ 0 → (∀ π ∈ P, e ∣ c * π) → ∃ u' : M, e • u' = c • u) → ∃ (x : R) (u : M), d₀ • u = x • t ∧ u ∉ V := by
  intro R _ _ _ M _ _ htf t _ d₀ hd₀ hb V P hP hP0 hV
  by_contra hcon
  push_neg at hcon
  let I : Ideal R :=
    { carrier := {x | ∃ u : M, d₀ • u = x • t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨u, hu⟩
        refine ⟨c • u, ?_⟩
        rw [smul_comm, hu, smul_eq_mul, mul_smul] }
  have hImem : ∀ x, x ∈ I ↔ ∃ u : M, d₀ • u = x • t := fun x => Iff.rfl
  have hI0 : I ≠ ⊥ := by
    intro h
    have : d₀ ∈ I := (hImem _).2 ⟨t, rfl⟩
    rw [h] at this
    exact hd₀ (by simpa using this)
  obtain ⟨e, heP, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hle : Ideal.span {e} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 heP
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 hle
  have hcz : ∀ c ∈ C, ∀ z ∈ I, c * z ∈ Ideal.span {e} * I := by
    intro c hc z hz
    obtain ⟨u, hu⟩ := (hImem z).1 hz
    have huV : u ∈ V := hcon z u hu
    have hdiv : ∀ π ∈ P, e ∣ c * π := by
      intro π hπ
      have : π * c ∈ Ideal.span {e} := by
        rw [hC]
        exact Ideal.mul_mem_mul hπ hc
      rw [mul_comm]
      exact Ideal.mem_span_singleton.1 this
    obtain ⟨u', hu'⟩ := hV u huV c e he0 hdiv
    have h1 : (d₀ * e) • u' = (c * z) • t := by
      rw [mul_smul, hu', smul_comm, hu, mul_smul]
    have h2 : d₀ * e ∣ d₀ * (c * z) := hb (c * z) (d₀ * e) u' (mul_ne_zero hd₀ he0) h1
    obtain ⟨w, hw⟩ := (mul_dvd_mul_iff_left hd₀).1 h2
    have h3 : d₀ • u' = w • t := by
      have h4 : e • (d₀ • u' - w • t) = 0 := by
        rw [smul_sub, smul_comm, ← mul_smul e w, ← hw, ← h1, mul_smul, sub_self]
      exact sub_eq_zero.1 (htf e _ he0 h4)
    have hwI : w ∈ I := (hImem w).2 ⟨u', h3⟩
    rw [hw]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self e) hwI
  have hCI : C * I ≤ Ideal.span {e} * I := Ideal.mul_le.2 hcz
  have h5 : Ideal.span {e} * I ≤ Ideal.span {e} * (P * I) := by
    calc Ideal.span {e} * I = P * (C * I) := by rw [hC, mul_assoc]
      _ ≤ P * (Ideal.span {e} * I) := Ideal.mul_mono_right hCI
      _ = Ideal.span {e} * (P * I) := by ring
  have h6 : I ≤ P * I := (Ideal.span_singleton_mul_right_mono he0).1 h5
  have h8 : P * I = ⊤ * I := by
    rw [Ideal.top_mul]
    exact le_antisymm Ideal.mul_le_right h6
  exact hP.ne_top (mul_right_cancel₀ hI0 h8)

end GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSectionNotInSetStatement
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_not_in_set : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M], (∀ (a : R) (m : M), a ≠ 0 → a • m = 0 → m = 0) → ∀ t : M, t ≠ 0 → ∀ d₀ : R, d₀ ≠ 0 → (∀ (x d : R) (u : M), d ≠ 0 → d • u = x • t → d ∣ d₀ * x) → ∀ (V : Set M) (P : Ideal R), P.IsMaximal → P ≠ ⊥ → (∀ u ∈ V, ∀ c e : R, e ≠ 0 → (∀ π ∈ P, e ∣ c * π) → ∃ u' : M, e • u' = c • u) → ∃ (x : R) (u : M), d₀ • u = x • t ∧ u ∉ V := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes.exists_multiple_not_mem | exact GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes.exists_multiple_not_mem | (intros; apply GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes.exists_multiple_not_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonvanishingSectionFieldExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyGen

theorem section_and_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D') (s : Out.H0 D'.t.PP.L 1) (e : Fin D'.g → D'.B.carrier), KeyDeg.NonVan D'.t.G.hom s ∧ LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  intro E _ _ _ H L _ _ D _
  have : Smooth D.t.G.hom := D.t.semi.smooth
  have : GeometricallyConnected D.t.G.hom := D.t.semi.geomConnected
  have : QuasiCompact D.t.G.hom := D.t.semi.quasiCompact
  have hN : (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))).IsLB :=
    LB.isLB_linComb D.t.PP.isLB _ _
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_nonzero_section_pp_data E H L D
  obtain ⟨d₀, hd₀, hb⟩ := GlobalTheory.T.section_module_bounded_denominator (𝓞 L) D.t.G _ hN t ht
  let I : Ideal (𝓞 L) :=
    { carrier := {x | ∃ u : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), d₀ • u = x • t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨u, hu⟩
        exact ⟨c • u, by rw [smul_comm, hu, smul_eq_mul, mul_smul]⟩ }
  have hI : I ≠ ⊥ := fun h0 => hd₀ (by
    have : d₀ ∈ I := ⟨t, rfl⟩
    rw [h0] at this
    simpa using this)
  obtain ⟨L', _, _, _, y, hy, hB⟩ := GlobalTheory.T.principal_extension_projective_module L D.B.carrier I hI
  obtain ⟨⟨D', m⟩⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').1
  obtain ⟨hgg, -, io, -, hspan, -⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').2 D' m
  obtain ⟨e, he1, he2⟩ := hB D'.B.carrier io hspan hgg
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.T.section_module_field_ext_map E H L D L' D' m
  have : Smooth D'.t.G.hom := D'.t.semi.smooth
  let φ := algebraMap (𝓞 L) (𝓞 L')
  let W : Ideal (𝓞 L') :=
    { carrier := {z | ∃ v : SecMod D'.t.G.hom (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), φ d₀ • v = z • P t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨u, hu⟩
        exact ⟨c • u, by rw [smul_comm, hu, smul_eq_mul, mul_smul]⟩ }
  have hIW : I.map φ ≤ W := Ideal.map_le_iff_le_comap.2 fun x ⟨u, hu⟩ =>
    ⟨P u, by rw [← hP1, hu, hP1]⟩
  obtain ⟨s, hs⟩ : y ∈ W := hIW (hy ▸ Ideal.mem_span_singleton_self y)
  refine ⟨L', inferInstance, inferInstance, inferInstance, D', m, s, e, ?_, he1, he2⟩
  intro b'
  let b : Sp (𝓞 L) := spMap φ b'

  obtain ⟨x, u, hu, yy, hyy, hmem⟩ : ∃ (x : 𝓞 L) (u : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))),
      d₀ • u = x • t ∧ ∃ yy : D.t.G.left, D.t.G.hom yy = b ∧ yy ∈ Out.nonzeroLocus (M := LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) u := by
    by_cases hb0 : b.asIdeal = ⊥
    · exact ⟨d₀, t, rfl, GlobalTheory.T.nonzero_section_generic_fibre (𝓞 L) D.t.G _ hN t ht b hb0⟩
    · have hmax : b.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hb0 b.isPrime
      obtain ⟨x, u, hu, hV⟩ := GlobalTheory.T.exists_section_not_in_set (𝓞 L) _ (fun a m ha h => eq_zero_of_smul_eq_zero ha h) t ht d₀ hd₀ hb
        {u | ∀ yy : D.t.G.left, D.t.G.hom yy = b → yy ∉ Out.nonzeroLocus (M := LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) u}
        b.asIdeal hmax hb0 (fun u hu c e he h => GlobalTheory.T.section_module_divisible_at_prime (𝓞 L) _ D.t.G.hom _ b hmax u hu c e he h)
      simp only [Set.mem_setOf_eq, not_forall, not_not] at hV
      obtain ⟨yy, hyy, hmem⟩ := hV
      exact ⟨x, u, hu, yy, hyy, hmem⟩
  obtain ⟨y', hy', hm'⟩ := hP2 u b' yy hyy hmem
  refine ⟨y', hy', ?_⟩
  have hxI : φ x ∈ I.map φ := Ideal.mem_map_of_mem φ (show x ∈ I from ⟨u, hu⟩)
  rw [hy, Ideal.mem_span_singleton'] at hxI
  obtain ⟨w, hw⟩ := hxI
  have hφ : φ d₀ ≠ 0 := fun h0 => hd₀ (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 L') (h0.trans (map_zero _).symm))
  have hPu : P u = w • s := by
    have : φ d₀ • (P u - w • s) = 0 := by
      rw [smul_sub, ← hP1, hu, hP1, smul_comm, hs, smul_smul, ← hw, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_smul_eq_zero hφ this)
  rw [hPu] at hm'
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm'
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  have : y' ∈ D'.t.G.left.basicOpen (constFn D'.t.G.hom _ w * LB.Sec.f (show SecMod D'.t.G.hom _ from s) k) := hk
  rw [Scheme.basicOpen_mul] at this
  exact this.2

end GlobalTheory.CompanionTheory.Ar.Sl.KeyGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonvanishingSectionFieldExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishing_section_field_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D') (s : Out.H0 D'.t.PP.L 1) (e : Fin D'.g → D'.B.carrier), KeyDeg.NonVan D'.t.G.hom s ∧ LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyGen.section_and_basis | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyGen.section_and_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyGen.section_and_basis <;> assumption)
end
