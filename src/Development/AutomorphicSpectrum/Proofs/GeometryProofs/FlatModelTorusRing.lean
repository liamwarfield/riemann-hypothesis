module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangents
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpen
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionExteriorValue

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsSpreadFromStalk
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsSpreadFromStalk
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Spread

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (d.comp c) = spMap d ≫ spMap c := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_ringHom {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (x : Sp A ⟶ X) [IsOpenImmersion x]
    (z : Sp B ⟶ X) (hr : Set.range z ⊆ Set.range x) : ∃ a : A →+* B, spMap a ≫ x = z := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift x z hr)).hom, ?_⟩
  change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x z hr)).hom) ≫ x = z
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem ringHom_ext {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (x : Sp A ⟶ X) [IsOpenImmersion x]
    {a b : A →+* B} (h : spMap a ≫ x = spMap b ≫ x) : a = b := by
  have h2 := Spec.map_injective ((cancel_mono x).1 h)
  exact congrArg (fun g => g.hom) h2

theorem exists_frac {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [IsOpenImmersion x] (P : X)
    (hP : P ∈ x.opensRange) (θ : R →+* X.presheaf.stalk P) (hθ : spMap θ ≫ x = X.fromSpecStalk P)
    (a : X.presheaf.stalk P) : ∃ r s : R, IsUnit (θ s) ∧ a * θ s = θ r := by
  have hU : IsAffineOpen x.opensRange := isAffineOpen_opensRange x
  let R₂ : Type := Γ(X, x.opensRange)
  let x₂ : Sp R₂ ⟶ X := hU.fromSpec
  have : IsOpenImmersion x₂ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hrange : Set.range x₂ = Set.range x := by
    change Set.range hU.fromSpec = _
    rw [hU.range_fromSpec]
    rfl
  obtain ⟨φ, hφ⟩ := exists_ringHom x x₂ hrange.le
  obtain ⟨φ', hφ'⟩ := exists_ringHom x₂ x hrange.ge
  have hcomp : φ.comp φ' = RingHom.id R₂ := ringHom_ext x₂ (by
    rw [spMap_comp, Category.assoc, hφ', hφ]
    simp [spMap])
  let g : R₂ →+* X.presheaf.stalk P := (X.presheaf.germ x.opensRange P hP).hom
  have hg : spMap g ≫ x₂ = X.fromSpecStalk P := by
    rw [← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU hP]
    rfl
  have hgφ : g.comp φ = θ := ringHom_ext x (by
    rw [spMap_comp, Category.assoc, hφ, hg, hθ])
  have hgs : ∀ t, θ (φ' t) = g t := fun t => by
    rw [← hgφ]
    exact congrArg g (RingHom.congr_fun hcomp t)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨P, hP⟩ : x.opensRange)
  haveI := hU.isLocalization_stalk ⟨P, hP⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl a
  refine ⟨φ' r, φ' s, ?_, ?_⟩
  · rw [hgs]
    exact IsLocalization.map_units (X.presheaf.stalk P) (M := (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl) s
  · rw [hgs, hgs]
    exact hrs

end GlobalTheory.CompanionTheory.Ar.LocFn.Spread

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem exists_chart_spread : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (P : X) (ι : Type) [Finite ι] (e : ι → (epsAt (X.fromSpecStalk P) ⟶ G)) (f : X.presheaf.stalk P), (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G (X.fromSpecStalk P) (e i)) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (θ : R →+* X.presheaf.stalk P) (e' : ι → (epsAt x ⟶ G)) (f' : R), P ∈ x.opensRange ∧ spMap θ ≫ x = X.fromSpecStalk P ∧ θ f' = f ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (e' i)) ∧ ∀ i, (e i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e' i).left := by
  intro X G _ _ _ P ι _ e f he
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨R₁, _, x₁, hx₁, F, _, _, MF, n, b, hP⟩ := LieVB.exists_chart G P
  have hP' : (X.fromSpecStalk P) (IsLocalRing.closedPoint (X.presheaf.stalk P)) ∈ x₁.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hP
  obtain ⟨θ₁, hθ₁⟩ := LieVB.exists_lift (A := X.presheaf.stalk P) x₁ (X.fromSpecStalk P) hP'
  obtain ⟨Fs, _, _, ⟨Ms⟩⟩ := lieModel_exists X G (X.presheaf.stalk P) (X.fromSpecStalk P)
  obtain ⟨β, B, hB, hβ⟩ := LieVB.basis_tr (A := X.presheaf.stalk P) θ₁ x₁ (X.fromSpecStalk P) hθ₁ MF Ms b
  choose s hs using fun i => Ms.onto (e i) (he i)
  let c : ι → Fin n → X.presheaf.stalk P := fun i k => B.repr (s i) k
  choose num den hden hfrac using Spread.exists_frac x₁ P hP θ₁ hθ₁
  let h : R₁ := den f * ∏ i, ∏ k, den (c i k)
  have hunit : IsUnit (θ₁ h) := by
    simp only [h, map_mul, map_prod]
    exact (hden f).mul (IsUnit.prod_univ_iff.2 fun i => IsUnit.prod_univ_iff.2 fun k => hden _)
  let R : Type := Localization.Away h
  let θ : R →+* X.presheaf.stalk P := IsLocalization.Away.lift h hunit
  have hθc : θ.comp (algebraMap R₁ R) = θ₁ := IsLocalization.Away.lift_comp h hunit
  let x : Sp R ⟶ X := spMap (algebraMap R₁ R) ≫ x₁
  have hopen : IsOpenImmersion (spMap (algebraMap R₁ R)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away h)))))
  have hx : IsOpenImmersion x := inferInstance
  have hxθ : spMap θ ≫ x = X.fromSpecStalk P := by
    change spMap θ ≫ spMap (algebraMap R₁ R) ≫ x₁ = _
    rw [← Category.assoc, ← Spread.spMap_comp, hθc, hθ₁]
  have hlift : ∀ a, den a ∣ h → ∃ a' : R, θ a' = a := fun a hd => by
    have hu : IsUnit (algebraMap R₁ R (den a)) :=
      isUnit_of_dvd_unit (map_dvd _ hd) (IsLocalization.Away.algebraMap_isUnit h)
    obtain ⟨u, hu⟩ := hu
    have hθu : θ (algebraMap R₁ R (den a)) = θ₁ (den a) := RingHom.congr_fun hθc _
    refine ⟨algebraMap R₁ R (num a) * (u⁻¹ : Rˣ), ?_⟩
    have h1 : θ ((u⁻¹ : Rˣ) : R) * θ₁ (den a) = 1 := by
      rw [← hθu, ← hu, ← map_mul, Units.inv_mul, map_one]
    have h2 : θ (algebraMap R₁ R (num a)) = θ₁ (num a) := RingHom.congr_fun hθc _
    rw [map_mul, h2, ← hfrac a, mul_assoc, mul_comm (θ₁ (den a)), h1, mul_one]
  have hdvd : ∀ i k, den (c i k) ∣ h := fun i k =>
    Dvd.dvd.mul_left ((Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ k, den (c i k)) (Finset.mem_univ i))) _
  choose c' hc' using fun i k => hlift (c i k) (hdvd i k)
  obtain ⟨f', hf'⟩ := hlift f (Dvd.intro _ rfl)
  obtain ⟨F', _, _, ⟨MR⟩⟩ := lieModel_exists X G R x
  obtain ⟨β₁, B₁, hB₁, hβ₁⟩ := LieVB.basis_tr (algebraMap R₁ R) x₁ x rfl MF MR b
  obtain ⟨j, hj⟩ := LieVB.exists_tr (A := R) (B := X.presheaf.stalk P) x (X.fromSpecStalk P) θ hxθ MR Ms
  have hjB : ∀ k, j (B₁ k) = B k := fun k => LieVB.pt_left_inj Ms (by
    rw [hj, hB₁, hβ₁, ← Category.assoc, LieVB.spMap_dual_comp, hθc, hB, hβ])
  refine ⟨R, inferInstance, x, hx, θ, fun i => MR.pt (∑ k, c' i k • B₁ k), f', ?_, hxθ, hf',
    fun i => MR.tan _, fun i => ?_⟩
  · refine ⟨(spMap θ) (IsLocalRing.closedPoint (X.presheaf.stalk P)), ?_⟩
    rw [← Scheme.Hom.comp_apply, hxθ]
    exact Scheme.fromSpecStalk_closedPoint
  · have hsum : j (∑ k, c' i k • B₁ k) = s i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (B.sum_repr (s i))
      rw [j.map_smulₛₗ, hc', hjB]
    rw [← hj, hsum, hs]

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsSpreadFromStalkStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vectors_spread_from_stalk : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (P : X) (ι : Type) [Finite ι] (e : ι → (epsAt (X.fromSpecStalk P) ⟶ G)) (f : X.presheaf.stalk P), (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G (X.fromSpecStalk P) (e i)) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (θ : R →+* X.presheaf.stalk P) (e' : ι → (epsAt x ⟶ G)) (f' : R), P ∈ x.opensRange ∧ spMap θ ≫ x = X.fromSpecStalk P ∧ θ f' = f ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (e' i)) ∧ ∀ i, (e i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e' i).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_chart_spread | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_chart_spread | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_chart_spread <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointMultiplicityCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointMultiplicityCompat
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Spread

theorem exists_away_lift {X : Scheme.{0}} {S R : Type} [CommRing S] [CommRing R] (x : Sp R ⟶ X) [IsOpenImmersion x]
    (w : Sp S ⟶ X) (q : Ideal S) [q.IsPrime] (θ : R →+* Localization.AtPrime q)
    (h : spMap θ ≫ x = spMap (algebraMap S (Localization.AtPrime q)) ≫ w) :
    ∃ (g₀ : S) (θ₀ : R →+* Localization.Away g₀), g₀ ∉ q ∧
      spMap θ₀ ≫ x = spMap (algebraMap S (Localization.Away g₀)) ≫ w ∧
      ∀ ι : Localization.Away g₀ →+* Localization.AtPrime q,
        ι.comp (algebraMap S _) = algebraMap S _ → ι.comp θ₀ = θ := by
  let p : PrimeSpectrum S := ⟨q, inferInstance⟩
  let t : Sp (Localization.AtPrime q) := (IsLocalRing.closedPoint (Localization.AtPrime q) : PrimeSpectrum _)
  have hcl : (spMap (algebraMap S (Localization.AtPrime q))) t = (p : Sp S) :=
    PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal)
  have hmem : w (p : Sp S) ∈ Set.range x := by
    refine ⟨(spMap θ) t, ?_⟩
    have := congrArg (fun f : Sp (Localization.AtPrime q) ⟶ X => f t) h
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, hcl]
  have hopen : IsOpen (w ⁻¹' Set.range x : Set (PrimeSpectrum S)) :=
    x.opensRange.isOpen.preimage w.continuous
  obtain ⟨_, ⟨g₀, rfl⟩, hg, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (w ⁻¹' Set.range x : Set (PrimeSpectrum S)) from hmem) hopen
  have hrange : Set.range (spMap (algebraMap S (Localization.Away g₀)) ≫ w) ⊆ Set.range x := by
    rintro _ ⟨y, rfl⟩
    have hy : (spMap (algebraMap S (Localization.Away g₀))) y ∈
        ((PrimeSpectrum.basicOpen g₀ : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g₀) g₀]
      exact ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hle hy
  let ℓ := IsOpenImmersion.lift x _ hrange
  have hℓ : ℓ ≫ x = _ := IsOpenImmersion.lift_fac x _ hrange
  let θ₀ : R →+* Localization.Away g₀ := (Spec.preimage ℓ).hom
  have hθ₀ : spMap θ₀ = ℓ := by
    simp only [spMap, θ₀, CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨g₀, θ₀, hg, by rw [hθ₀, hℓ], fun ι hι => ?_⟩
  have e : spMap (ι.comp θ₀) ≫ x = spMap θ ≫ x := by
    rw [← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, hθ₀, hℓ, ← Category.assoc,
      GlobalTheory.Frames.ChgBC.spMap_comp_ring, hι, h]
  have e' := (cancel_mono x).1 e
  have e'' := Spec.map_injective e'
  exact congrArg CommRingCat.Hom.hom e''

theorem exists_kill {S : Type} [CommRing S] (q : Ideal S) [q.IsPrime] (g₀ : S)
    (ι : Localization.Away g₀ →+* Localization.AtPrime q)
    (hι : ι.comp (algebraMap S _) = algebraMap S _) (b : Localization.Away g₀) (hb : ι b = 0) :
    ∃ s, s ∉ q ∧ algebraMap S (Localization.Away g₀) s * b = 0 := by
  obtain ⟨⟨t, m⟩, ht⟩ := IsLocalization.surj (Submonoid.powers g₀) b
  have h0 : algebraMap S (Localization.AtPrime q) t = 0 := by
    have := congrArg ι ht
    rw [map_mul, hb, zero_mul] at this
    rw [← hι]
    exact this.symm
  obtain ⟨⟨s, hs⟩, hst⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) t).1 h0
  refine ⟨s, hs, ?_⟩
  have h1 : algebraMap S (Localization.Away g₀) s * b * algebraMap S _ (m : S) = 0 := by
    rw [_root_.mul_assoc, ht, ← map_mul]
    have : s * t = 0 := hst
    rw [this, map_zero]
  exact ((IsLocalization.map_units (Localization.Away g₀) m).mul_left_eq_zero).1 h1

theorem exists_spread {S : Type} [CommRing S] (q : Ideal S) [hq : q.IsPrime] (g₀ : S) (hg₀ : g₀ ∉ q)
    (ι : Localization.Away g₀ →+* Localization.AtPrime q)
    (hι : ι.comp (algebraMap S _) = algebraMap S _) (Z : Finset (Localization.Away g₀))
    (hZ : ∀ b ∈ Z, ι b = 0) (d : Localization.Away g₀) (hd : IsUnit (ι d)) :
    ∃ (g : S) (ρ : Localization.Away g₀ →+* Localization.Away g), g ∉ q ∧
      ρ.comp (algebraMap S _) = algebraMap S _ ∧ (∀ b ∈ Z, ρ b = 0) ∧ IsUnit (ρ d) := by
  classical
  have hk : ∃ s, s ∉ q ∧ ∀ b ∈ Z, algebraMap S (Localization.Away g₀) s * b = 0 := by
    induction Z using Finset.induction_on with
    | empty => exact ⟨1, fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h), by simp⟩
    | insert b Z _ ih =>
      obtain ⟨s, hs, h⟩ := ih fun c hc => hZ c (Finset.mem_insert_of_mem hc)
      obtain ⟨s', hs', h'⟩ := exists_kill q g₀ ι hι b (hZ b (Finset.mem_insert_self _ _))
      refine ⟨s * s', fun hm => (hq.mem_or_mem hm).elim hs hs', fun c hc => ?_⟩
      rcases Finset.mem_insert.1 hc with rfl | hc
      · rw [map_mul, mul_comm (algebraMap S _ s), _root_.mul_assoc, mul_comm (algebraMap S _ s),
          ← _root_.mul_assoc, h', zero_mul]
      · rw [map_mul, mul_comm (algebraMap S _ s), _root_.mul_assoc, h c hc, mul_zero]
  obtain ⟨s, hs, hsZ⟩ := hk
  obtain ⟨⟨t, m⟩, ht⟩ := IsLocalization.surj (Submonoid.powers g₀) d
  have hιm : ∀ a : S, ι (algebraMap S _ a) = algebraMap S (Localization.AtPrime q) a := fun a =>
    RingHom.congr_fun hι a
  have hm : (m : S) ∉ q := by
    obtain ⟨k, hk⟩ := m.2
    intro hmem
    rw [← hk] at hmem
    exact hg₀ (hq.mem_of_pow_mem k hmem)
  have htq : t ∉ q := by
    have h1 : IsUnit (algebraMap S (Localization.AtPrime q) t) := by
      rw [← hιm, ← ht, map_mul, hιm]
      exact hd.mul ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).2 hm)
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q t).1 h1
  let g := g₀ * s * t
  have hg : g ∉ q := fun hmem =>
    (hq.mem_or_mem hmem).elim (fun h => (hq.mem_or_mem h).elim hg₀ hs) htq
  have hgu : IsUnit (algebraMap S (Localization.Away g) g) := IsLocalization.Away.algebraMap_isUnit g
  have hgm : algebraMap S (Localization.Away g) g =
      algebraMap S _ g₀ * algebraMap S _ s * algebraMap S _ t := by
    simp only [g, map_mul]
  rw [hgm] at hgu
  have ht' : IsUnit (algebraMap S (Localization.Away g) t) := isUnit_of_mul_isUnit_right hgu
  have hgs := isUnit_of_mul_isUnit_left hgu
  have hg₀' : IsUnit (algebraMap S (Localization.Away g) g₀) := isUnit_of_mul_isUnit_left hgs
  have hs' : IsUnit (algebraMap S (Localization.Away g) s) := isUnit_of_mul_isUnit_right hgs
  let ρ : Localization.Away g₀ →+* Localization.Away g := IsLocalization.Away.lift g₀ hg₀'
  have hρ : ρ.comp (algebraMap S _) = algebraMap S _ := IsLocalization.Away.lift_comp g₀ hg₀'
  have hρa : ∀ a : S, ρ (algebraMap S _ a) = algebraMap S (Localization.Away g) a := fun a =>
    RingHom.congr_fun hρ a
  refine ⟨g, ρ, hg, hρ, fun b hb => ?_, ?_⟩
  · have := congrArg ρ (hsZ b hb)
    rw [map_mul, map_zero, hρa] at this
    exact (hs'.mul_right_eq_zero).1 this
  · have h1 : IsUnit (ρ d * ρ (algebraMap S _ (m : S))) := by
      rw [← map_mul, ht, hρa]
      exact ht'
    exact isUnit_of_mul_isUnit_left h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}


open MonoidalCategory CartesianMonoidalCategory MonObj in
theorem one_left_eq {X : Scheme.{0}} {A : Type} [CommRing A] (G : Over X) [GrpObj G] (x : Sp A ⟶ X) :
    (1 : Over.mk x ⟶ G).left = x ≫ η[G].left := by
  simp [Hom.one_def, Out.PullGtPf.toUnit_left']

theorem fst_dualMap {A B : Type} [CommRing A] [CommRing B] (θ : A →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (Formalism.L2.Pj.dualMap θ) =
      θ.comp (TrivSqZeroExt.fstHom A A A).toRingHom :=
  RingHom.ext fun a => by simp [Formalism.L2.Pj.dualMap]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    (Formalism.L2.Pj.dualMap f).comp (Formalism.L2.Pj.dualMap g) = Formalism.L2.Pj.dualMap (f.comp g) :=
  RingHom.ext fun a => by
    ext <;> simp [Formalism.L2.Pj.dualMap]


open MonoidalCategory CartesianMonoidalCategory MonObj in
theorem exists_tied (Y : Model Xo c β) {B : Type} [CommRing B] (y : Sp B ⟶ Xo.XF c)
    (v' : Sp (DualNumber B) ⟶ Y.t.G.left)
    (hv : v' ≫ Y.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ y ≫ Y.j)
    (h0 : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ v' = y ≫ Y.j ≫ η[Y.t.G].left) :
    ∃ V, Tied Y y V v' ∧ Formalism.L2.Pj.IsTanAt (y ≫ pullback.fst _ _) V := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have hv2 : v' ≫ Y.t.G.hom = (spMap (algebraMap B (DualNumber B)) ≫ y) ≫ Y.j := by
    rw [Category.assoc]; exact hv
  let u := hq.lift v' (spMap (algebraMap B (DualNumber B)) ≫ y) hv2
  have hu1 : u ≫ Y.m.φ = v' := hq.lift_fst _ _ _
  have hu2 : u ≫ Y.oF.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ y := hq.lift_snd _ _ _
  have e1 : η[Y.oF.t.G].left ≫ Y.m.φ = Y.j ≫ η[Y.t.G].left :=
    Out.PullGtPf.IsGrpPullback.one_left Y.m.cart
  have e2 : η[Y.oF.t.G].left ≫ Y.m0.toSABMap.φ = pullback.fst _ _ ≫ η[Xo.univ.t.G].left :=
    Out.PullGtPf.IsGrpPullback.one_left Y.m0.cart
  have e3 : η[Y.oF.t.G].left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w η[Y.oF.t.G]
  have hsec : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (algebraMap B (DualNumber B)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom B B B).toRingHom.comp (algebraMap B (DualNumber B)) = RingHom.id B :=
      RingHom.ext fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [GlobalTheory.Frames.ChgBC.spMap_comp_ring, e, GlobalTheory.Frames.ChgBC.spMap_id]
  have u0 : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ u = y ≫ η[Y.oF.t.G].left := by
    refine hq.hom_ext ?_ ?_
    · rw [Category.assoc, hu1, h0, Category.assoc, e1]
    · rw [Category.assoc, hu2, ← Category.assoc, hsec, Category.id_comp, Category.assoc, e3]
      exact (Category.comp_id y).symm
  refine ⟨u ≫ Y.m0.toSABMap.φ, ⟨u, hu2, rfl, hu1⟩, ?_, ?_⟩
  · rw [Category.assoc, hp.w, ← Category.assoc, hu2, Category.assoc]
  · rw [← Category.assoc, u0, Category.assoc, e2, one_left_eq, Category.assoc]

theorem Tied.unique_left {Y : Model Xo c β} {B : Type} [CommRing B] {y : Sp B ⟶ Xo.XF c}
    {V₁ V₂ : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {v' : Sp (DualNumber B) ⟶ Y.t.G.left}
    (h₁ : Tied Y y V₁ v') (h₂ : Tied Y y V₂ v') : V₁ = V₂ := by
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  obtain ⟨u₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨u₂, a₂, b₂, c₂⟩ := h₂
  have : u₁ = u₂ := hq.hom_ext (c₁.trans c₂.symm) (a₁.trans a₂.symm)
  rw [← b₁, ← b₂, this]

theorem Tied.pull {Y : Model Xo c β} {B B' : Type} [CommRing B] [CommRing B'] (ρ : B →+* B')
    {y : Sp B ⟶ Xo.XF c} {V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} {v' : Sp (DualNumber B) ⟶ Y.t.G.left}
    (h : Tied Y y V v') :
    Tied Y (spMap ρ ≫ y) (spMap (Formalism.L2.Pj.dualMap ρ) ≫ V) (spMap (Formalism.L2.Pj.dualMap ρ) ≫ v') := by
  obtain ⟨u, a, b, c⟩ := h
  refine ⟨spMap (Formalism.L2.Pj.dualMap ρ) ≫ u, ?_, by rw [Category.assoc, b], by rw [Category.assoc, c]⟩
  rw [Category.assoc, a, ← Category.assoc, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring,
    GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_alg]

theorem comb_total_iff {B : Type} [CommRing B] (xB : Sp B ⟶ Xo.X)
    (uu : ∀ τ : E →+* ℂ, Fin (D.mult τ) → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left))
    (hu : ∀ τ i, Formalism.L2.Pj.IsTanAt xB (uu τ i)) {n : ℕ} (e : Fin n ≃ Σ τ : E →+* ℂ, Fin (D.mult τ))
    (a : ∀ τ : E →+* ℂ, Fin (D.mult τ) → B) (σ : E →+* ℂ) (ha : ∀ τ, τ ≠ σ → a τ = 0)
    (w : Sp (DualNumber B) ⟶ Xo.univ.t.G.left) :
    Formalism.L2.Pj.IsCombAt xB (fun j => uu (e j).1 (e j).2) (fun j => a (e j).1 (e j).2) w ↔
      Formalism.L2.Pj.IsCombAt xB (uu σ) (a σ) w := by
  classical
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H D l Xo B xB
  choose b hb using fun τ i => (htan (uu τ i)).1 (hu τ i)
  obtain rfl : uu = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  have key : ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2 = ∑ i, a σ i • b σ i := by
    rw [e.sum_comp (fun p : Σ τ : E →+* ℂ, Fin (D.mult τ) => a p.1 p.2 • b p.1 p.2), Fintype.sum_sigma,
      Finset.sum_eq_single σ]
    · intro τ _ hτ
      simp [ha τ hτ]
    · simp
  exact (hcomb _ (fun j => b (e j).1 (e j).2) _ _).trans
    (by rw [key]; exact (hcomb _ (b σ) _ _).symm)

theorem isTanAt_of_comb {B : Type} [CommRing B] {xB : Sp B ⟶ Xo.X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left)} (hu : ∀ i, Formalism.L2.Pj.IsTanAt xB (u i))
    {a : Fin m → B} {w : Sp (DualNumber B) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt xB u a w) :
    Formalism.L2.Pj.IsTanAt xB w := by
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H D l Xo B xB
  choose b hb using fun i => (htan (u i)).1 (hu i)
  obtain rfl : u = fun i => v (b i) := by funext i; exact (hb i).symm
  rw [(hcomb _ b _ _).1 h]
  exact (htan _).2 ⟨_, rfl⟩


open MonoidalCategory CartesianMonoidalCategory MonObj in
theorem tan_pull (Y : Model Xo c β) {R B : Type} [CommRing R] [CommRing B] {x : Sp R ⟶ Y.X} (θ₀ : R →+* B)
    (y : Sp B ⟶ Xo.XF c) (h : spMap θ₀ ≫ x = y ≫ Y.j) (v : epsAt x ⟶ Y.t.G) (hv : IsTanAt Y.t.G x v) :
    ∃ V, Tied Y y V (spMap (Formalism.L2.Pj.dualMap θ₀) ≫ v.left) ∧ Formalism.L2.Pj.IsTanAt (y ≫ pullback.fst _ _) V := by
  refine exists_tied Y y _ ?_ ?_
  · have hw : v.left ≫ Y.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := Over.w v
    rw [Category.assoc, hw, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring,
      GlobalTheory.Frames.ChgBC.dualMap_alg, ← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, h]
  · have hv' : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = x ≫ η[Y.t.G].left :=
      (show _ = _ from hv).trans (one_left_eq Y.t.G x)
    rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, fst_dualMap,
      ← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, hv', ← Category.assoc, h, Category.assoc]

theorem tan_family {B : Type} [CommRing B] {xB : Sp B ⟶ Xo.X}
    {uu : ∀ τ : E →+* ℂ, Fin (D.mult τ) → (Sp (DualNumber B) ⟶ Xo.univ.t.G.left)}
    {n : ℕ} (e : Fin n ≃ Σ τ : E →+* ℂ, Fin (D.mult τ))
    (h : GlobalTheory.Frames.TanBasis xB (fun j => uu (e j).1 (e j).2)) (τ : E →+* ℂ) (k : Fin (D.mult τ)) :
    Formalism.L2.Pj.IsTanAt xB (uu τ k) :=
  (fun p : (Σ τ : E →+* ℂ, Fin (D.mult τ)) => by
    obtain ⟨j, rfl⟩ := e.surjective p
    exact h.1 j : ∀ p : (Σ τ : E →+* ℂ, Fin (D.mult τ)), Formalism.L2.Pj.IsTanAt xB (uu p.1 p.2)) ⟨τ, k⟩

theorem spread_family (Y : Model Xo c β) {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S)
    (q : Ideal S) [q.IsPrime] {R : Type} [CommRing R] (x : Sp R ⟶ Y.X) (θ : R →+* Localization.AtPrime q)
    (σ : E →+* ℂ) (e : Fin (D.mult σ) → (epsAt x ⟶ Y.t.G))
    (C : Matrix (Fin (D.mult σ)) (Fin (D.mult σ)) (Localization.AtPrime q)) (g₀ : S)
    (θ₀ : R →+* Localization.Away g₀) (ι : Localization.Away g₀ →+* Localization.AtPrime q)
    (hι : ι.comp (algebraMap S _) = algebraMap S _) (hιθ : ι.comp θ₀ = θ)
    (hθ₀ : spMap θ₀ ≫ x = spMap (algebraMap S (Localization.Away g₀)) ≫ zPt z ≫ Y.j)
    (ht : ∀ i, IsTanAt Y.t.G x (e i)) (hC : IsUnit C.det)
    (hyp : ∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left,
      Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V
        (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e i).left) ∧
      Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x)
        (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u σ k) (C i) V) :
    ∃ (Z : Finset (Localization.Away g₀)) (d : Localization.Away g₀), (∀ b ∈ Z, ι b = 0) ∧ IsUnit (ι d) ∧
      ∀ (B : Type) [CommRing B] (ρ : Localization.Away g₀ →+* B), (∀ b ∈ Z, ρ b = 0) → IsUnit (ρ d) →
        ∃ C' : Matrix (Fin (D.mult σ)) (Fin (D.mult σ)) B, IsUnit C'.det ∧
          ∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left,
            Tied Y (spMap (ρ.comp (algebraMap S _)) ≫ zPt z) V
              (spMap (Formalism.L2.Pj.dualMap (ρ.comp θ₀)) ≫ (e i).left) ∧
            Formalism.L2.Pj.IsCombAt (spMap (ρ.comp (algebraMap S _)) ≫ z.x)
              (fun k => spMap (Formalism.L2.Pj.dualMap (ρ.comp (algebraMap S _))) ≫ z.u σ k) (C' i) V := by
  classical
  let φ₀ := algebraMap S (Localization.Away g₀)
  let φT := algebraMap S (Localization.AtPrime q)
  let n := Fintype.card (Σ τ : E →+* ℂ, Fin (D.mult τ))
  let ee : Fin n ≃ Σ τ : E →+* ℂ, Fin (D.mult τ) := (Fintype.equivFin _).symm
  have hB : GlobalTheory.Frames.TanBasis z.x (fun j => z.u (ee j).1 (ee j).2) :=
    (GlobalTheory.Frames.eigBasis_iff_tanBasis E H D l Xo c S z.x z.u n ee z.tan z.eig).1 z.basis
  have hB₀ := GlobalTheory.Frames.tanBasis_baseChange E H D l Xo S _ φ₀ z.x n _ hB
  have hBT := GlobalTheory.Frames.tanBasis_baseChange E H D l Xo S _ φT z.x n _ hB
  have hv : ∀ i, ∃ V₀, Tied Y (spMap φ₀ ≫ zPt z) V₀ (spMap (Formalism.L2.Pj.dualMap θ₀) ≫ (e i).left) ∧
      Formalism.L2.Pj.IsTanAt (spMap φ₀ ≫ z.x) V₀ := by
    intro i
    obtain ⟨V, h1, h2⟩ := tan_pull Y θ₀ (spMap φ₀ ≫ zPt z) (by rw [hθ₀, Category.assoc]) (e i) (ht i)
    refine ⟨V, h1, ?_⟩
    rwa [Category.assoc, zPt_fst] at h2
  choose V₀ hV₀ hV₀t using hv
  choose a ha hau using fun i => hB₀.2 (V₀ i) (hV₀t i)
  have hι' : ι.comp φ₀ = φT := hι
  let sg : Fin (D.mult σ) → ∀ τ : E →+* ℂ, Fin (D.mult τ) → Localization.AtPrime q := fun i =>
    Pi.single (M := fun τ : E →+* ℂ => Fin (D.mult τ) → Localization.AtPrime q) σ (C i)
  have hsgσ : ∀ i, sg i σ = C i := fun i => Pi.single_eq_same _ _
  have hsg0 : ∀ i τ, τ ≠ σ → sg i τ = 0 := fun i τ h => Pi.single_eq_of_ne h _
  have key : ∀ i j, ι (a i j) = sg i (ee j).1 (ee j).2 := by
    intro i j
    obtain ⟨V, hVt, hVc⟩ := hyp i
    have h1 := Tied.pull ι (hV₀ i)
    have hy : spMap ι ≫ spMap φ₀ ≫ zPt z = spMap φT ≫ zPt z := by
      rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, hι']
    have hv' : spMap (Formalism.L2.Pj.dualMap ι) ≫ spMap (Formalism.L2.Pj.dualMap θ₀) ≫ (e i).left =
        spMap (Formalism.L2.Pj.dualMap θ) ≫ (e i).left := by
      rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp, hιθ]
    rw [hy, hv'] at h1
    have hVV := Tied.unique_left h1 hVt
    have hxT : spMap φT ≫ z.x = spMap ι ≫ spMap φ₀ ≫ z.x := by
      rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, hι']
    have c1 : Formalism.L2.Pj.IsCombAt (spMap φT ≫ z.x)
        (fun j => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u (ee j).1 (ee j).2) (fun j => ι (a i j)) V :=
      GlobalTheory.Frames.ChgBC.isCombAt_pull ι hxT
        (fun j => by rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp, hι']) hVV.symm (ha i)
    have hT := tan_family (uu := fun τ k => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u τ k) ee hBT
    have c2 : Formalism.L2.Pj.IsCombAt (spMap φT ≫ z.x)
        (fun j => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u (ee j).1 (ee j).2)
        (fun j => sg i (ee j).1 (ee j).2) V :=
      (comb_total_iff _ (fun τ k => spMap (Formalism.L2.Pj.dualMap φT) ≫ z.u τ k) hT ee (sg i) σ (hsg0 i) V).2
        (by rw [hsgσ]; exact hVc)
    have hVtan := isTanAt_of_comb hBT.1 c1
    exact congrFun ((hBT.2 V hVtan).unique c1 c2) j
  let M : Matrix (Fin (D.mult σ)) (Fin (D.mult σ)) (Localization.Away g₀) :=
    fun i k => a i (ee.symm ⟨σ, k⟩)
  have hM : ∀ i k, ι (M i k) = C i k := by
    intro i k
    have h1 := key i (ee.symm ⟨σ, k⟩)
    have h2 : ∀ p : (Σ τ : E →+* ℂ, Fin (D.mult τ)), p = ⟨σ, k⟩ → sg i p.1 p.2 = C i k := by
      rintro _ rfl
      exact congrFun (hsgσ i) k
    exact h1.trans (h2 _ (ee.apply_symm_apply _))
  refine ⟨Finset.univ.image (fun p : Fin (D.mult σ) × Fin n =>
    if (ee p.2).1 = σ then 0 else a p.1 p.2), M.det, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.1 hb
    dsimp only
    split_ifs with h
    · exact map_zero ι
    · rw [key, hsg0 i _ h]
      rfl
  · have h1 : ι M.det = C.det := by
      rw [RingHom.map_det]
      congr 1
      ext i k
      exact hM i k
    rw [h1]
    exact hC
  · intro B _ ρ hZ hd
    have hρ0 : ∀ i j, (ee j).1 ≠ σ → ρ (a i j) = 0 := by
      intro i j h
      exact hZ (a i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, by simp [h]⟩)
    have hBB := GlobalTheory.Frames.tanBasis_baseChange E H D l Xo S B (ρ.comp φ₀) z.x n _ hB
    refine ⟨M.map ρ, ?_, fun i => ⟨spMap (Formalism.L2.Pj.dualMap ρ) ≫ V₀ i, ?_, ?_⟩⟩
    · have h1 : (M.map ρ).det = ρ M.det := by
        rw [RingHom.map_det]
        rfl
      rw [h1]
      exact hd
    · have h1 := Tied.pull ρ (hV₀ i)
      have hy : spMap ρ ≫ spMap φ₀ ≫ zPt z = spMap (ρ.comp φ₀) ≫ zPt z := by
        rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring]
      have hv' : spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (Formalism.L2.Pj.dualMap θ₀) ≫ (e i).left =
          spMap (Formalism.L2.Pj.dualMap (ρ.comp θ₀)) ≫ (e i).left := by
        rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp]
      rw [hy, hv'] at h1
      exact h1
    · let A : ∀ τ : E →+* ℂ, Fin (D.mult τ) → B := fun τ k => ρ (a i (ee.symm ⟨τ, k⟩))
      have hA0 : ∀ τ, τ ≠ σ → A τ = 0 := by
        intro τ h
        funext k
        refine hρ0 i _ ?_
        rw [ee.apply_symm_apply]
        exact h
      have hx : spMap (ρ.comp φ₀) ≫ z.x = spMap ρ ≫ spMap φ₀ ≫ z.x := by
        rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring]
      have c1 : Formalism.L2.Pj.IsCombAt (spMap (ρ.comp φ₀) ≫ z.x)
          (fun j => spMap (Formalism.L2.Pj.dualMap (ρ.comp φ₀)) ≫ z.u (ee j).1 (ee j).2) (fun j => ρ (a i j))
          (spMap (Formalism.L2.Pj.dualMap ρ) ≫ V₀ i) :=
        GlobalTheory.Frames.ChgBC.isCombAt_pull ρ hx
          (fun j => by rw [← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring, dualMap_comp]) rfl (ha i)
      have hAe : (fun j => ρ (a i j)) = fun j => A (ee j).1 (ee j).2 := by
        funext j
        simp [A]
      rw [hAe] at c1
      exact (comb_total_iff _ (fun τ k => spMap (Formalism.L2.Pj.dualMap (ρ.comp φ₀)) ≫ z.u τ k)
        (tan_family (uu := fun τ k => spMap (Formalism.L2.Pj.dualMap (ρ.comp φ₀)) ≫ z.u τ k) ee hBB) ee A σ hA0 _).1 c1

theorem exists_away_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (q : Ideal S) [q.IsPrime] (R : Type) [CommRing R] (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (θ : R →+* (Localization.AtPrime q)) (σ₁ σ₂ : E →+* ℂ) (n₁ n₂ : ℕ) (h₁ : D.mult σ₁ = n₁) (h₂ : D.mult σ₂ = n₂) (e₁ : Fin n₁ → (epsAt x ⟶ Y.t.G)) (e₂ : Fin n₂ → (epsAt x ⟶ Y.t.G)) (C₁ : Matrix (Fin n₁) (Fin n₁) (Localization.AtPrime q)) (C₂ : Matrix (Fin n₂) (Fin n₂) (Localization.AtPrime q)), spMap θ ≫ x = spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z ≫ Y.j → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) → IsUnit C₁.det → IsUnit C₂.det → (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u σ₁ (k.cast h₁.symm)) (C₁ i) V) → (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u σ₂ (k.cast h₂.symm)) (C₂ i) V) → ∃ (g : S) (θ' : R →+* (Localization.Away g)) (C₁' : Matrix (Fin n₁) (Fin n₁) (Localization.Away g)) (C₂' : Matrix (Fin n₂) (Fin n₂) (Localization.Away g)), g ∉ q ∧ spMap θ' ≫ x = spMap (algebraMap S (Localization.Away g)) ≫ zPt z ≫ Y.j ∧ IsUnit C₁'.det ∧ IsUnit C₂'.det ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.Away g)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.Away g)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ') ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.Away g)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.Away g))) ≫ z.u σ₁ (k.cast h₁.symm)) (C₁' i) V) ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.Away g)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.Away g)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ') ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.Away g)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.Away g))) ≫ z.u σ₂ (k.cast h₂.symm)) (C₂' i) V) := by
  intro E _ _ _ H D l Xo c O _ β Y S _ _ z q _ R _ x _ θ σ₁ σ₂ n₁ n₂ h₁ h₂ e₁ e₂ C₁ C₂ hθ ht₁ ht₂ hC₁ hC₂ hy₁ hy₂
  subst h₁ h₂
  obtain ⟨g₀, θ₀, hg₀, hθ₀, hι⟩ := exists_away_lift x (zPt z ≫ Y.j) q θ hθ
  have hu₀ : IsUnit (algebraMap S (Localization.AtPrime q) g₀) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q g₀).2 hg₀
  let ι : Localization.Away g₀ →+* Localization.AtPrime q := IsLocalization.Away.lift g₀ hu₀
  have hιφ : ι.comp (algebraMap S _) = algebraMap S _ := IsLocalization.Away.lift_comp g₀ hu₀
  obtain ⟨Z₁, d₁, hZ₁, hd₁, F₁⟩ := spread_family Y z q x θ σ₁ e₁ C₁ g₀ θ₀ ι hιφ (hι ι hιφ) hθ₀ ht₁ hC₁ hy₁
  obtain ⟨Z₂, d₂, hZ₂, hd₂, F₂⟩ := spread_family Y z q x θ σ₂ e₂ C₂ g₀ θ₀ ι hιφ (hι ι hιφ) hθ₀ ht₂ hC₂ hy₂
  classical
  obtain ⟨g, ρ, hg, hρ, hZ, hd⟩ := exists_spread q g₀ hg₀ ι hιφ (Z₁ ∪ Z₂)
    (fun b hb => (Finset.mem_union.1 hb).elim (hZ₁ b) (hZ₂ b)) (d₁ * d₂)
    (by rw [map_mul]; exact hd₁.mul hd₂)
  rw [map_mul] at hd
  obtain ⟨C₁', u₁, G₁⟩ := F₁ (Localization.Away g) ρ (fun b hb => hZ b (Finset.mem_union_left _ hb))
    (isUnit_of_mul_isUnit_left hd)
  obtain ⟨C₂', u₂, G₂⟩ := F₂ (Localization.Away g) ρ (fun b hb => hZ b (Finset.mem_union_right _ hb))
    (isUnit_of_mul_isUnit_right hd)
  rw [hρ] at G₁ G₂
  refine ⟨g, ρ.comp θ₀, C₁', C₂', hg, ?_, u₁, u₂, G₁, G₂⟩
  rw [← GlobalTheory.Frames.ChgBC.spMap_comp_ring, Category.assoc, hθ₀, ← Category.assoc,
    GlobalTheory.Frames.ChgBC.spMap_comp_ring, hρ]

end GlobalTheory.CompanionTheory.Ar.LocFn.Spread
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointMultiplicityCompatStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_point_multiplicity_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (q : Ideal S) [q.IsPrime] (R : Type) [CommRing R] (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (θ : R →+* (Localization.AtPrime q)) (σ₁ σ₂ : E →+* ℂ) (n₁ n₂ : ℕ) (h₁ : D.mult σ₁ = n₁) (h₂ : D.mult σ₂ = n₂) (e₁ : Fin n₁ → (epsAt x ⟶ Y.t.G)) (e₂ : Fin n₂ → (epsAt x ⟶ Y.t.G)) (C₁ : Matrix (Fin n₁) (Fin n₁) (Localization.AtPrime q)) (C₂ : Matrix (Fin n₂) (Fin n₂) (Localization.AtPrime q)), spMap θ ≫ x = spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z ≫ Y.j → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) → IsUnit C₁.det → IsUnit C₂.det → (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u σ₁ (k.cast h₁.symm)) (C₁ i) V) → (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u σ₂ (k.cast h₂.symm)) (C₂ i) V) → ∃ (g : S) (θ' : R →+* (Localization.Away g)) (C₁' : Matrix (Fin n₁) (Fin n₁) (Localization.Away g)) (C₂' : Matrix (Fin n₂) (Fin n₂) (Localization.Away g)), g ∉ q ∧ spMap θ' ≫ x = spMap (algebraMap S (Localization.Away g)) ≫ zPt z ≫ Y.j ∧ IsUnit C₁'.det ∧ IsUnit C₂'.det ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.Away g)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.Away g)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ') ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.Away g)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.Away g))) ≫ z.u σ₁ (k.cast h₁.symm)) (C₁' i) V) ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.Away g)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.Away g)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ') ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.Away g)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.Away g))) ≫ z.u σ₂ (k.cast h₂.symm)) (C₂' i) V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.Spread.exists_away_frames | exact GlobalTheory.CompanionTheory.Ar.LocFn.Spread.exists_away_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.Spread.exists_away_frames <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffRatioRegular
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffRatioRegular
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem iotaMulti_ne_zero_of_linearIndependent {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ}
    {b : Fin r → V} (hb : LinearIndependent Ω b) : exteriorPower.ιMulti Ω r b ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := r) hb).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin r)).toOrderEmbedding)
  intro h0
  apply h
  simpa [exteriorPower.ιMulti_family] using h0

theorem exists_unit_of_span_eq {Ω W : Type} [Field Ω] [AddCommGroup W] [Module Ω W] (R : Subring Ω) {c m : W}
    (hm : m ≠ 0) (h : Submodule.span R {c} = Submodule.span R {m}) :
    ∃ u : Ω, u ≠ 0 ∧ u ∈ R ∧ u⁻¹ ∈ R ∧ c = u • m := by
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self (R := R) c)
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 (h.symm ▸ Submodule.mem_span_singleton_self (R := R) m)
  have hu' : (u : Ω) • m = c := hu
  have hv' : (v : Ω) • c = m := hv
  have h1 : ((v : Ω) * u - 1) • m = 0 := by
    rw [sub_smul, mul_smul, hu', hv', one_smul, sub_self]
  have h2 : (v : Ω) * u = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hm)
  have h3 : (u : Ω) ≠ 0 := right_ne_zero_of_mul_eq_one h2
  refine ⟨u, h3, u.2, ?_, hu'.symm⟩
  rw [inv_eq_of_mul_eq_one_left h2]
  exact v.2

theorem exists_coeff_regular_of_frames : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (b₁ : Fin p → V) (b₂ : Fin q → V), IsCoeffAt A B p q a b x 1 → A.IsFrameAt b₁ x → B.IsFrameAt b₂ x → ∃ α κ : Ω, a = α • exteriorPower.ιMulti Ω p b₁ ∧ b = κ • exteriorPower.ιMulti Ω q b₂ ∧ α / κ ∈ regAt ξ x := by
  intro X Ω _ ξ V _ _ A B p q a b x b₁ b₂ hc f₁ f₂
  obtain ⟨α₀, β₀, hα, hβ, hA, hB, h1⟩ := hc
  rw [one_mul] at h1
  subst h1
  rw [Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₁] at hA
  rw [Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₂] at hB
  obtain ⟨u, -, hu, -, hau⟩ := exists_unit_of_span_eq (regAt ξ x)
    (iotaMulti_ne_zero_of_linearIndependent f₁.1) hA.symm
  obtain ⟨t, ht0, -, hti, hbt⟩ := exists_unit_of_span_eq (regAt ξ x)
    (iotaMulti_ne_zero_of_linearIndependent f₂.1) hB.symm
  refine ⟨u / α₀, t / α₀, ?_, ?_, ?_⟩
  · rw [div_eq_inv_mul, mul_smul, ← hau, smul_smul, inv_mul_cancel₀ hα, one_smul]
  · rw [div_eq_inv_mul, mul_smul, ← hbt, smul_smul, inv_mul_cancel₀ hα, one_smul]
  · have : u / α₀ / (t / α₀) = u * t⁻¹ := by field_simp
    rw [this]
    exact mul_mem hu hti

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffRatioRegularStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exterior_coeff_ratio_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (b₁ : Fin p → V) (b₂ : Fin q → V), IsCoeffAt A B p q a b x 1 → A.IsFrameAt b₁ x → B.IsFrameAt b₂ x → ∃ α κ : Ω, a = α • exteriorPower.ιMulti Ω p b₁ ∧ b = κ • exteriorPower.ιMulti Ω q b₂ ∧ α / κ ∈ regAt ξ x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_coeff_regular_of_frames | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_coeff_regular_of_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_coeff_regular_of_frames <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatModelTorusRing
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem dualMap_eq {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    GlobalTheory.CompanionTheory.Ar.dualMap φ = Formalism.L2.Pj.dualMap φ := by
  ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, Formalism.L2.Pj.dualMap]

theorem exists_frame_ring {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] (z : Formalism.L2.Pj.FrPt Xo c S)
    (ψ : S →+* T) (x : Sp T ⟶ Xo.X) (hx : x = spMap ψ ≫ z.x) (τ : E →+* ℂ) (n : ℕ) (h : D.mult τ = n) :
    ∃ v : Fin n → (epsAt x ⟶ Xo.univ.t.G),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast h.symm)) ∧
        IsEigFrame Xo.univ.t.act x ((ψ.comp (algebraMap c.F S)).comp (tauIn c τ)) v := by
  subst hx
  subst h
  letI : Algebra c.F T := (ψ.comp (algebraMap c.F S)).toAlgebra
  let ψa : S →ₐ[c.F] T := { ψ with commutes' := fun _ => rfl }
  have htan : ∀ i, Formalism.L2.Pj.IsTanAt (spMap ψ ≫ z.x) (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isTanAt_baseChange ψ (z.tan τ i)
  have heig : ∀ i, Formalism.L2.Pj.IsEigAt c τ (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) :=
    fun i => GlobalTheory.Frames.EigenBaseChange.isEigAt_baseChange ψa τ (z.eig τ i)
  let v : Fin (D.mult τ) → (epsAt (spMap ψ ≫ z.x) ⟶ Xo.univ.t.G) :=
    fun i => Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ i) (htan i).1
  refine ⟨v, fun i => rfl, fun i => (FrameEig.isEigVec_iff τ (v i)).2 ⟨htan i, heig i⟩, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := (FrameEig.isEigVec_iff τ w).1 hw
  obtain ⟨a, ha, hu⟩ := GlobalTheory.Frames.eigenbasis_baseChange E H D l Xo c S T ψa z τ w.left h1 h2
  exact ⟨a, (FrameEig.isComb_iff a v w).2 ha, fun b hb => hu b ((FrameEig.isComb_iff b v w).1 hb)⟩


set_option backward.isDefEq.respectTransparency false in
theorem exists_localData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (q : Ideal S) [q.IsPrime] (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib → centre (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) ∈ U → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ Y.X) (_ : IsOpenImmersion x) (θ : R →+* (Localization.AtPrime q)) (φ₂ : R →+* Z.Ω) (e₁ : Fin D.p → (epsAt x ⟶ Y.t.G)) (e₂ : Fin D.q → (epsAt x ⟶ Y.t.G)) (f : R) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (α κ : Z.Ω) (C₁ : Matrix (Fin D.p) (Fin D.p) (Localization.AtPrime q)) (C₂ : Matrix (Fin D.q) (Fin D.q) (Localization.AtPrime q)), spMap θ ≫ x = spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z ≫ Y.j ∧ spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j ∧ a = α • exteriorPower.ιMulti Z.Ω D.p b₁ ∧ b = κ • exteriorPower.ιMulti Z.Ω D.q b₂ ∧ φ₂ f = α / κ ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) ∧ (∀ i, (Z.M.pt (b₁ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₁ i).left) ∧ (∀ i, (Z.M.pt (b₂ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₂ i).left) ∧ IsUnit C₁.det ∧ IsUnit C₂.det ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u τ (k.cast hp.symm)) (C₁ i) V) ∧ (∀ i, ∃ V : Sp (DualNumber (Localization.AtPrime q)) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S (Localization.AtPrime q)) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S (Localization.AtPrime q)) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S (Localization.AtPrime q))) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) (C₂ i) V) := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z a b S _ _ z q _ hp hq hgen hcen
  classical
  let T := Localization.AtPrime q
  let y : Sp T ⟶ Xo.XF c := spMap (algebraMap S T) ≫ zPt z
  let c₀ : c.F →+* T := (algebraMap S T).comp (algebraMap c.F S)
  have hy2 : y ≫ pullback.snd _ _ = spMap c₀ := by
    simp only [y, c₀, Category.assoc, zPt_snd, spMap, ← Spec.map_comp]
    rfl
  have hy1 : under y = spMap (algebraMap S T) ≫ z.x := by
    simp only [y, under, Category.assoc, zPt_fst]
  obtain ⟨h, κ, hκ₁, hκ₂⟩ := GlobalTheory.T.local_point_specializes_component E H D l Xo c U O β Y Z T y c₀ hy2 hcen
  let P : Cpt (Z.ξ₀ ≫ Y.j) := ⟨centre (y ≫ Y.j), h⟩
  let x₀ := Y.X.fromSpecStalk P.1
  let θs : Y.X.presheaf.stalk P.1 →+* T := (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom
  have hθs : spMap θs ≫ x₀ = y ≫ Y.j := Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  have hκ₂' : θs.comp κ = c₀ := hκ₂
  obtain ⟨r₁, e₁, he₁⟩ := GlobalTheory.T.exists_stable_eigen_tangents E H l c Y.X Y.t (Y.X.presheaf.stalk P.1) x₀ κ τ
  obtain ⟨r₂, e₂, he₂⟩ := GlobalTheory.T.exists_stable_eigen_tangents E H l c Y.X Y.t (Y.X.presheaf.stalk P.1) x₀ κ (ComplexEmbedding.conjugate τ)
  obtain ⟨V₁, hV₁, hVf₁⟩ := GlobalTheory.T.stable_eigen_tangents_pullback E H D l Xo c O β Y T y _ x₀ κ θs τ r₁ e₁ hθs he₁
  obtain ⟨V₂, hV₂, hVf₂⟩ := GlobalTheory.T.stable_eigen_tangents_pullback E H D l Xo c O β Y T y _ x₀ κ θs _ r₂ e₂ hθs he₂
  rw [hκ₂'] at hVf₁ hVf₂
  obtain ⟨u₁, hu₁, huf₁⟩ := exists_frame_ring z (algebraMap S T) (under y) hy1 τ D.p hp
  obtain ⟨u₂, hu₂, huf₂⟩ := exists_frame_ring z (algebraMap S T) (under y) hy1 (ComplexEmbedding.conjugate τ) D.q hq
  obtain ⟨hr₁, M₁, hM₁, M₁', hl₁, -⟩ := GlobalTheory.T.eigen_frames_invertible_change Xo.X T Xo.univ.t.G (under y) _ Xo.univ.t.act _ _ _ u₁ V₁ huf₁ hVf₁
  obtain ⟨hr₂, M₂, hM₂, M₂', hl₂, -⟩ := GlobalTheory.T.eigen_frames_invertible_change Xo.X T Xo.univ.t.G (under y) _ Xo.univ.t.act _ _ _ u₂ V₂ huf₂ hVf₂
  subst hr₁ hr₂
  obtain ⟨b₁, hbE₁, hbF₁⟩ := GlobalTheory.T.stable_eigen_at_component_stalk E H D l Xo c U O β Y Z P κ τ _ e₁ hκ₁ he₁
  obtain ⟨b₂, hbE₂, hbF₂⟩ := GlobalTheory.T.stable_eigen_at_component_stalk E H D l Xo c U O β Y Z P κ _ _ e₂ hκ₁ he₂
  have hP : P ∈ Z.genFib := by
    have key : ∀ t : Sp T, (y ≫ Y.j) t = pullback.fst Y.s (spMap β) (Y.jQ (y t)) := fun t => by
      simp only [Model.j, Scheme.Hom.comp_apply]
    exact ⟨Y.jQ (y (IsLocalRing.closedPoint T)), (key _).symm⟩
  obtain ⟨α, κ', ha, hb, s, hs⟩ := GlobalTheory.T.exterior_coeff_ratio_regular Y.X Z.Ω _ Z.V _ _ _ _ a b P b₁ b₂ (hgen.2.2 P hP) hbF₁ hbF₂
  haveI := Y.t.semi.smooth
  obtain ⟨R, _, x, _, θA, e', f', -, hθA, hf', ht, hleft⟩ := GlobalTheory.T.tangent_vectors_spread_from_stalk Y.X Y.t.G P.1 (Fin D.p ⊕ Fin D.q)
    (Sum.elim e₁ e₂) s (by rintro (i | i); exacts [(hbE₁ i).1, (hbE₂ i).1])
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hθ : spMap (θs.comp θA) ≫ x = spMap (algebraMap S T) ≫ zPt z ≫ Y.j := by
    rw [hcomp, Category.assoc, hθA]
    exact hθs.trans (Category.assoc _ _ _)
  have hcε : ∀ i : Fin D.p ⊕ Fin D.q, spMap (Formalism.L2.Pj.dualMap θs) ≫ (Sum.elim e₁ e₂ i).left =
      spMap (Formalism.L2.Pj.dualMap (θs.comp θA)) ≫ (e' i).left := fun i => by
    rw [hleft i, ← dualMap_eq, ← dualMap_eq, ← Category.assoc, LieVB.spMap_dual_comp]
  have hcγ : ∀ i : Fin D.p ⊕ Fin D.q, (genMap (Z.ξ₀ ≫ Y.j) P).comp θA = (genMap (Z.ξ₀ ≫ Y.j) P).comp θA ∧
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (genMap (Z.ξ₀ ≫ Y.j) P)) ≫ (Sum.elim e₁ e₂ i).left =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap ((genMap (Z.ξ₀ ≫ Y.j) P).comp θA)) ≫ (e' i).left := fun i => ⟨rfl, by
    rw [hleft i, ← Category.assoc, LieVB.spMap_dual_comp]⟩
  refine ⟨R, inferInstance, x, inferInstance, θs.comp θA, (genMap (Z.ξ₀ ≫ Y.j) P).comp θA, fun i => e' (Sum.inl i),
    fun j => e' (Sum.inr j), f', b₁, b₂, α, κ', M₁, M₂, hθ, ?_, ha, hb, ?_, fun i => ht _, fun j => ht _, ?_, ?_,
    Matrix.isUnit_det_of_right_inverse hl₁, Matrix.isUnit_det_of_right_inverse hl₂, ?_, ?_⟩
  · rw [hcomp, Category.assoc, hθA]
    exact LieTangent.spec_genMap _ P
  · change genMap (Z.ξ₀ ≫ Y.j) P (θA f') = α / κ'
    rw [hf']; exact hs
  · intro i
    rw [(hbE₁ i).2]
    exact (hcγ (Sum.inl i)).2
  · intro i
    rw [(hbE₂ i).2]
    exact (hcγ (Sum.inr i)).2
  · intro i
    refine ⟨(V₁ i).left, ?_, ?_⟩
    · have := hV₁ i
      rw [show spMap (Formalism.L2.Pj.dualMap θs) ≫ (e₁ i).left = _ from hcε (Sum.inl i)] at this
      exact this
    · rw [← hy1]
      have := (FrameEig.isComb_iff (M₁ i) u₁ (V₁ i)).1 (hM₁ i)
      simpa only [hu₁] using this
  · intro i
    refine ⟨(V₂ i).left, ?_, ?_⟩
    · have := hV₂ i
      rw [show spMap (Formalism.L2.Pj.dualMap θs) ≫ (e₂ i).left = _ from hcε (Sum.inr i)] at this
      exact this
    · rw [← hy1]
      have := (FrameEig.isComb_iff (M₂ i) u₂ (V₂ i)).1 (hM₂ i)
      simpa only [hu₂] using this

theorem spMap_field_pt {S F : Type} [CommRing S] [Field F] (ψ : S →+* F) (t : Sp F) :
    (spMap ψ) t = (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum S) := by
  refine PrimeSpectrum.ext ?_
  change Ideal.comap ψ (t : PrimeSpectrum F).asIdeal = RingHom.ker ψ
  haveI := PrimeSpectrum.isPrime (t : PrimeSpectrum F)
  rw [Ideal.eq_bot_of_prime (t : PrimeSpectrum F).asIdeal]
  rfl

theorem spMap_local_pt {S : Type} [CommRing S] (q : Ideal S) [hq : q.IsPrime] :
    (spMap (algebraMap S (Localization.AtPrime q))) (IsLocalRing.closedPoint (Localization.AtPrime q)) =
      (⟨q, hq⟩ : PrimeSpectrum S) :=
  PrimeSpectrum.ext (by
    change Ideal.comap _ _ = q
    exact Localization.AtPrime.under_maximalIdeal)

theorem exists_regular_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsClopen U → IsLineFn U τ φ → FlatOnModel Z τ φ → ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (k : Type) [Field k] (ψ₀ : p.R →+* k) (y₀ : Sp k ⟶ Xo.XF c), under y₀ = spMap ψ₀ ≫ z.x → y₀ ≫ pullback.snd _ _ = spMap (ψ₀.comp (algebraMap c.F p.R)) → Set.range y₀ ⊆ U → ∃ g a : p.R, ψ₀ g ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → ψ g ≠ 0 → Set.range y ⊆ U ∧ ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ a = ψ g * φ F y v w := by
  intro E _ _ _ H D l Xo c U τ O _ β Y Z φ hτ hU hL hF p z k _ ψ₀ y₀ hy₁ hy₂ hy₃
  classical
  let q : Ideal p.R := RingHom.ker ψ₀
  haveI hqp : q.IsPrime := RingHom.ker_isPrime ψ₀
  have hy₀ : y₀ = spMap ψ₀ ≫ zPt z := eq_zPt z ψ₀ y₀ hy₁ hy₂
  have hmemU : zPt z (⟨q, hqp⟩ : PrimeSpectrum p.R) ∈ U := by
    obtain ⟨t⟩ : Nonempty (Sp k) := ⟨IsLocalRing.closedPoint k⟩
    have h := hy₃ ⟨t, rfl⟩
    rw [hy₀, Scheme.Hom.comp_apply, spMap_field_pt] at h
    exact h
  have hcen : centre (spMap (algebraMap p.R (Localization.AtPrime q)) ≫ zPt z) ∈ U := by
    have key : ∀ t : Sp (Localization.AtPrime q), (spMap (algebraMap p.R (Localization.AtPrime q)) ≫ zPt z) t =
        zPt z ((spMap (algebraMap p.R (Localization.AtPrime q))) t) := fun t => by rw [Scheme.Hom.comp_apply]
    have e : centre (spMap (algebraMap p.R (Localization.AtPrime q)) ≫ zPt z) = zPt z (⟨q, hqp⟩ : PrimeSpectrum p.R) :=
      (key _).trans (congrArg (zPt z) (spMap_local_pt q))
    rw [e]
    exact hmemU
  have hWo : IsOpen ((zPt z) ⁻¹' U : Set (PrimeSpectrum p.R)) := hU.isOpen.preimage (zPt z).continuous
  obtain ⟨_, ⟨gU, rfl⟩, hgU, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show (⟨q, hqp⟩ : PrimeSpectrum p.R) ∈ ((zPt z) ⁻¹' U : Set (PrimeSpectrum p.R)) from hmemU) hWo
  have hgU0 : ψ₀ gU ≠ 0 := hgU
  have hrange : ∀ (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x →
      y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → ψ gU ≠ 0 → Set.range y ⊆ U := by
    rintro F _ ψ y h1 h2 hg _ ⟨t, rfl⟩
    rw [eq_zPt z ψ y h1 h2, Scheme.Hom.comp_apply, spMap_field_pt]
    exact hsub (show (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum p.R) ∈ PrimeSpectrum.basicOpen gU from hg)
  by_cases hpq : D.mult τ = D.p ∧ D.mult (ComplexEmbedding.conjugate τ) = D.q
  swap
  · exact ⟨gU, 0, hgU0, fun F _ ψ y h1 h2 hg => ⟨hrange F ψ y h1 h2 hg, fun v w hp hq => (hpq ⟨hp, hq⟩).elim⟩⟩
  obtain ⟨hp, hq⟩ := hpq
  obtain ⟨a, b, hgen, hrep⟩ := hF.exists_gen
  obtain ⟨R, _, x, _, θ, φ₂, e₁, e₂, f, b₁, b₂, α, κ, C₁, C₂, hθ, hφ₂, ha, hb, hf, ht₁, ht₂, hb₁, hb₂, hu₁, hu₂,
    hc₁, hc₂⟩ := exists_localData E H D l Xo c U τ O β Y Z a b p.R z q hp hq hgen hcen
  obtain ⟨g, θ', C₁', C₂', hgq, hθ', hu₁', hu₂', hc₁', hc₂'⟩ := GlobalTheory.T.frame_point_multiplicity_compat E H D l Xo c O β Y p.R z q R x θ τ _ _ _
    hp hq e₁ e₂ C₁ C₂ hθ ht₁ ht₂ hu₁ hu₂ hc₁ hc₂
  have FS := GlobalTheory.T.frame_function_exterior_value E H D l Xo c U τ O β Y Z φ a b p.R z hp hq R x φ₂ e₁ e₂ f b₁ b₂ α κ
    (Localization.Away g) θ' C₁' C₂' hL hrep hφ₂ ha hb hf ht₁ ht₂ hb₁ hb₂ hθ' hu₁' hu₂' hc₁' hc₂'
  obtain ⟨m, a₀, hm⟩ := IsLocalization.Away.surj g (θ' f * C₁'.det * ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g))
  have hg0 : ψ₀ g ≠ 0 := hgq
  refine ⟨g ^ (m + 1) * gU, a₀ * g * gU, ?_, ?_⟩
  · rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hg0) hgU0
  intro F _ ψ y h1 h2 hg
  rw [map_mul, map_pow] at hg
  have hg1 : ψ g ≠ 0 := fun h => hg (by rw [h]; simp)
  have hg2 : ψ gU ≠ 0 := right_ne_zero_of_mul hg
  have hr := hrange F ψ y h1 h2 hg2
  refine ⟨hr, fun v w hp' hq' hv hw => ?_⟩
  let ψ' : Localization.Away g →+* F := IsLocalization.Away.lift g (isUnit_iff_ne_zero.2 hg1)
  have hψ : ψ'.comp (algebraMap p.R (Localization.Away g)) = ψ := IsLocalization.Away.lift_comp g _
  have hy : y = spMap ψ' ≫ spMap (algebraMap p.R (Localization.Away g)) ≫ zPt z := by
    rw [eq_zPt z ψ y h1 h2, ← Category.assoc]
    congr 1
    conv_lhs => rw [← hψ]
    simp only [spMap, ← Spec.map_comp]
    rfl
  have X := FS F ψ' y hy hr v w (by rw [hψ]; exact hv) (by rw [hψ]; exact hw)
  have hψa : ∀ s, ψ' (algebraMap p.R (Localization.Away g) s) = ψ s := fun s => RingHom.congr_fun hψ s
  have hinv : ψ' C₂'.det * ψ' ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have h3 := congrArg ψ' hm
  simp only [map_mul, map_pow, hψa] at h3
  have hφ : φ F y v w = ψ' (θ' f) * ψ' C₁'.det * ψ' ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g) := by
    calc φ F y v w = φ F y v w * (ψ' C₂'.det * ψ' ((hu₂'.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g)) := by
          rw [hinv, mul_one]
      _ = _ := by rw [← mul_assoc, X]
  rw [hφ, map_mul, map_mul, map_mul, map_pow, ← h3]
  ring

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatModelTorusRingStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_model_torus_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsClopen U → IsLineFn U τ φ → FlatOnModel Z τ φ → ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (k : Type) [Field k] (ψ₀ : p.R →+* k) (y₀ : Sp k ⟶ Xo.XF c), under y₀ = spMap ψ₀ ≫ z.x → y₀ ≫ pullback.snd _ _ = spMap (ψ₀.comp (algebraMap c.F p.R)) → Set.range y₀ ⊆ U → ∃ g a : p.R, ψ₀ g ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → ψ g ≠ 0 → Set.range y ⊆ U ∧ ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ a = ψ g * φ F y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_regular_near | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_regular_near | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_regular_near <;> assumption)
end
