module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSnc
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartIdealLocalizationMap
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHomAdjoinInv
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartHom

theorem exists_hom_adjoin_inv {σ Ω R : Type*} [Field Ω] [CharZero Ω] [CommRing R]
    (u : σ → Ω) (θ : MvPolynomial σ ℚ →+* R)
    (hker : ∀ G : MvPolynomial σ ℚ, aeval u G = (0 : Ω) → θ G = 0)
    (F : MvPolynomial σ ℚ) (hF : IsUnit (θ F))
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (aeval u F : Ω)⁻¹ (Set.range u))) :
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial σ ℚ) (s : S), (s : Ω) = aeval u G → ψ s = θ G := by
  classical
  by_cases hf : (aeval u F : Ω) = 0
  · have h0 : θ F = 0 := hker F hf
    have hR : Subsingleton R := by
      have : IsUnit (0 : R) := h0 ▸ hF
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp this)
    refine ⟨{ toFun := fun _ => 0, map_one' := Subsingleton.elim _ _, map_mul' := fun _ _ => Subsingleton.elim _ _,
              map_zero' := rfl, map_add' := fun _ _ => Subsingleton.elim _ _ }, fun _ _ _ => Subsingleton.elim _ _⟩
  · let B := Localization.Away F
    have hunit : ∀ y : Submonoid.powers F, IsUnit (aeval u (y : MvPolynomial σ ℚ) : Ω) := by
      rintro ⟨_, n, rfl⟩
      simpa using (IsUnit.mk0 _ hf).pow n
    let Φ : B →ₐ[ℚ] Ω := IsLocalization.liftAlgHom (M := Submonoid.powers F) (f := aeval u) hunit
    have hΦ : ∀ a : MvPolynomial σ ℚ, Φ (algebraMap _ B a) = aeval u a := fun a =>
      by simp [Φ, IsLocalization.liftAlgHom_apply]
    let Θ : B →+* R := IsLocalization.Away.lift F hF
    have hΘ : ∀ a : MvPolynomial σ ℚ, Θ (algebraMap _ B a) = θ a := fun a =>
      IsLocalization.Away.lift_eq F hF a
    have hnum : ∀ z : B, ∃ (n : ℕ) (a : MvPolynomial σ ℚ), z * algebraMap _ B (F ^ n) = algebraMap _ B a := by
      intro z
      obtain ⟨n, a, h⟩ := IsLocalization.Away.surj F z
      exact ⟨n, a, by simpa using h⟩
    have hmem : ∀ a : MvPolynomial σ ℚ, (aeval u a : Ω) ∈ S := by
      intro a
      have : (aeval u a : Ω) ∈ Algebra.adjoin ℚ (Set.range u) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨a, rfl⟩
      rw [hS]
      exact Algebra.adjoin_mono (Set.subset_insert _ _) this
    have hinv : (aeval u F : Ω)⁻¹ ∈ S := by
      rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
    have hΦS : ∀ z : B, Φ z ∈ S := by
      intro z
      obtain ⟨n, a, h⟩ := hnum z
      have h2 := congrArg Φ h
      rw [map_mul, hΦ, hΦ, map_pow] at h2
      have : Φ z = aeval u a * ((aeval u F : Ω)⁻¹) ^ n := by
        rw [← h2, inv_pow, _root_.mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hf), _root_.mul_one]
      rw [this]
      exact S.mul_mem (hmem a) (S.pow_mem hinv n)
    let Φ' : B →+* S := (Φ : B →+* Ω).codRestrict S.toSubsemiring hΦS
    have hΦ' : ∀ z, ((Φ' z : S) : Ω) = Φ z := fun _ => rfl
    have hsurj : Function.Surjective Φ' := by
      have hle : S ≤ Φ.range := by
        rw [hS]
        refine Algebra.adjoin_le ?_
        rintro _ (rfl | ⟨p, rfl⟩)
        · have hu : IsUnit (algebraMap _ B F) := IsLocalization.Away.algebraMap_isUnit F
          obtain ⟨v, hv⟩ := hu
          refine ⟨(↑v⁻¹ : B), ?_⟩
          have h1 : Φ (↑v⁻¹ : B) * aeval u F = 1 := by
            rw [← hΦ, ← hv, ← map_mul]; simp
          exact eq_inv_of_mul_eq_one_left h1
        · exact ⟨algebraMap (MvPolynomial σ ℚ) B (X p), (hΦ (X p)).trans (aeval_X u p)⟩
      intro s
      obtain ⟨z, hz⟩ := hle s.2
      exact ⟨z, Subtype.ext hz⟩
    have hkerΘ : RingHom.ker Φ' ≤ RingHom.ker Θ := by
      intro z hz
      rw [RingHom.mem_ker] at hz ⊢
      have hz0 : Φ z = 0 := by
        have := congrArg (Subtype.val) hz
        simpa [hΦ'] using this
      obtain ⟨n, a, h⟩ := hnum z
      have h2 := congrArg Φ h
      rw [map_mul, hz0, zero_mul, hΦ] at h2
      have ha : θ a = 0 := hker a h2.symm
      have h3 := congrArg Θ h
      rw [map_mul, hΘ, hΘ, ha, map_pow] at h3
      exact (hF.pow n).mul_left_eq_zero.mp h3
    refine ⟨RingHom.liftOfSurjective Φ' hsurj ⟨Θ, hkerΘ⟩, fun G s hs => ?_⟩
    have hsG : s = Φ' (algebraMap _ B G) := Subtype.ext (by rw [hΦ', hΦ, hs])
    rw [hsG, RingHom.liftOfRightInverse_comp_apply]
    exact hΘ G

end GlobalTheory.CompanionTheory.Ar.ChartHom
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartIdealLocalizationMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartHom

theorem exists_hom_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R),
    (∀ g ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c, θ g = 0) →
    ∀ (F : MvPolynomial (Σ k, J k) ℚ), IsUnit (θ (map (algebraMap ℚ ℂ) F)) →
    ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) F : Ω)⁻¹
        (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)) →
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S),
      (s : Ω) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G → ψ s = θ (map (algebraMap ℚ ℂ) G) := by
  intro K _ J _ Ω _ _ y c hc R _ θ hθ F hF S hS
  exact exists_hom_adjoin_inv (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)
    (θ.comp (map (algebraMap ℚ ℂ)))
    (fun G hG => hθ _ (GlobalTheory.CompanionTheory.Ar.ChartDehom.map_mem_chartIdeal K J Ω y c hc G hG)) F hF S hS

end GlobalTheory.CompanionTheory.Ar.ChartHom
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartIdealLocalizationMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ideal_localization_map : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R),
    (∀ g ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c, θ g = 0) →
    ∀ (F : MvPolynomial (Σ k, J k) ℚ), IsUnit (θ (map (algebraMap ℚ ℂ) F)) →
    ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) F : Ω)⁻¹
        (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)) →
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S),
      (s : Ω) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G → ψ s = θ (map (algebraMap ℚ ℂ) G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart | exact GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem top_le_iff_centre (y : Sp ℂ ⟶ X) (U : X.Opens) : ⊤ ≤ y ⁻¹ᵁ U ↔ centre y ∈ U :=
  ⟨fun h => h trivial, fun h => (Scheme.preimage_eq_top_of_closedPoint_mem y h).ge⟩

theorem val_germ (y : Sp ℂ ⟶ X) (N : X.Opens) (h : centre y ∈ N) (v : Γ(X, N)) :
    (Scheme.stalkClosedPointTo y).hom (X.presheaf.germ N (centre y) h v) = valAt' y N v := by
  have e := congrArg (fun q => q.hom v) (germ_stalkClosedPointTo_eq y N h)
  rw [valAt'_of _ _ ((top_le_iff_centre y N).2 h)]
  simp only [valAt]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

def genV (ξ : Sp Ω ⟶ X) (N : X.Opens) (h : genPt ξ ∈ N) : Γ(X, N) →+* Ω :=
  ((X.presheaf.germ N (genPt ξ) h) ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (N : X.Opens) {q : X} (hq : genPt ξ ⤳ q) (hN : q ∈ N) (h : genPt ξ ∈ N) (v : Γ(X, N)) :
    genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q hN v) = genV ξ N h v := by
  have e := X.presheaf.germ_stalkSpecializes hN hq
  simp only [genMap, genV]
  rw [← e]
  rfl

theorem genPt_mem {N : X.Opens} {q : X} (hq : genPt ξ ⤳ q) (hN : q ∈ N) : genPt ξ ∈ N :=
  hq.mem_open N.isOpen hN

theorem ValAt.of_section {y : Sp ℂ ⟶ X} {N : X.Opens} (hy : centre y ∈ N) (h : genPt ξ ⤳ centre y) {v : Γ(X, N)}
    {a : Ω} (ha : genMap ξ ⟨centre y, h⟩ (X.presheaf.germ N (centre y) hy v) = a) :
    ValAt ξ y a (valAt' y N v) :=
  ⟨h, _, ha, val_germ y N hy v⟩

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem ValAt.unique (hξ : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h₁, s, hs, rfl⟩ := h
  obtain ⟨h₂, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h₁⟩ (hs.trans hs'.symm)]

theorem ValAt.mul {z : Spec (CommRingCat.of R) ⟶ X} {a b : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z b r') : ValAt ξ z (a * b) (r * r') := by
  obtain ⟨h₁, s, hs, rfl⟩ := h
  obtain ⟨h₂, s', hs', rfl⟩ := h'
  exact ⟨h₁, s * s', by rw [map_mul, hs]; congr 1, map_mul _ _ _⟩

theorem ValAt.one {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) :=
  ⟨h, 1, map_one _, map_one _⟩

theorem ValAt.exists_of_mem {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

theorem ValAt.exists_ne_zero (hξ : IsCptGen ξ) {z : Sp ℂ ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : unitAt ξ ⟨centre z, h⟩ a) : ∃ r : ℂ, r ≠ 0 ∧ ValAt ξ z a r := by
  obtain ⟨r, hr⟩ := ValAt.exists_of_mem h ha.2.1
  obtain ⟨r', hr'⟩ := ValAt.exists_of_mem h ha.2.2
  have e := ValAt.unique hξ (ValAt.mul hr hr') (by rw [mul_inv_cancel₀ ha.1]; exact ValAt.one h)
  exact ⟨r, left_ne_zero_of_mul_eq_one e, hr⟩

theorem exists_section {q : X} (h : genPt ξ ⤳ q) {a : Ω} (ha : a ∈ regAt ξ ⟨q, h⟩) (M : X.Opens) (hM : q ∈ M) :
    ∃ (N : X.Opens) (hq : q ∈ N) (v : Γ(X, N)), N ≤ M ∧ genMap ξ ⟨q, h⟩ (X.presheaf.germ N q hq v) = a := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨N, hq, v, hv⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf s
  refine ⟨N ⊓ M, ⟨hq, hM⟩, X.presheaf.map (homOfLE inf_le_left).op v, inf_le_right, ?_⟩
  have e : X.presheaf.germ (N ⊓ M) q ⟨hq, hM⟩ (X.presheaf.map (homOfLE inf_le_left).op v) =
      X.presheaf.germ N q hq v := TopCat.Presheaf.germ_res_apply _ _ _ _ _
  exact congrArg (genMap ξ ⟨q, h⟩) (e.trans hv)

theorem exists_unit_section (hξ : IsCptGen ξ) {q : X} (h : genPt ξ ⤳ q) {a : Ω} (ha : unitAt ξ ⟨q, h⟩ a)
    (M : X.Opens) (hM : q ∈ M) :
    ∃ (N : X.Opens) (hq : q ∈ N) (v : Γ(X, N)), N ≤ M ∧ IsUnit v ∧
      genMap ξ ⟨q, h⟩ (X.presheaf.germ N q hq v) = a := by
  obtain ⟨N₁, h₁, v, l₁, e₁⟩ := exists_section h ha.2.1 M hM
  obtain ⟨N₂, h₂, w, l₂, e₂⟩ := exists_section h ha.2.2 M hM
  let i₁ : N₁ ⊓ N₂ ⟶ N₁ := homOfLE inf_le_left
  let i₂ : N₁ ⊓ N₂ ⟶ N₂ := homOfLE inf_le_right
  have hq : q ∈ N₁ ⊓ N₂ := ⟨h₁, h₂⟩
  have g₁ : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₁.op v) = X.presheaf.germ N₁ q h₁ v :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have g₂ : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₂.op w) = X.presheaf.germ N₂ q h₂ w :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have one : X.presheaf.germ (N₁ ⊓ N₂) q hq (X.presheaf.map i₁.op v * X.presheaf.map i₂.op w) =
      X.presheaf.germ (N₁ ⊓ N₂) q hq 1 := by
    apply hξ.inj ⟨q, h⟩
    rw [map_mul, g₁, g₂, map_mul, e₁, e₂, mul_inv_cancel₀ ha.1, map_one, map_one]
  obtain ⟨N₃, h₃, j₁, j₂, e₃⟩ := TopCat.Presheaf.germ_eq X.presheaf q hq hq _ _ one
  have hj : j₁ = j₂ := Subsingleton.elim _ _
  subst hj
  refine ⟨N₃, h₃, X.presheaf.map (j₁ ≫ i₁).op v, (leOfHom (j₁ ≫ i₁)).trans l₁, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one (X.presheaf.map (j₁ ≫ i₂).op w) ?_
    rw [map_mul, map_one] at e₃
    simpa [op_comp, Functor.map_comp] using e₃
  · rw [TopCat.Presheaf.germ_res_apply, e₁]

theorem unitAt_div_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {a b : Ω} (ha : Λ.IsGenAt p a) (hb : Λ.IsGenAt p b) :
    unitAt ξ p (b / a) := by
  have h₁ : b ∈ Submodule.span (regAt ξ p) {a} := by
    rw [← ha.2, hb.2]; exact Submodule.mem_span_singleton_self b
  have h₂ : a ∈ Submodule.span (regAt ξ p) {b} := by
    rw [← hb.2, ha.2]; exact Submodule.mem_span_singleton_self a
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h₁
  obtain ⟨e, he⟩ := Submodule.mem_span_singleton.1 h₂
  have hc' : (c : Ω) * a = b := hc
  have he' : (e : Ω) * b = a := he
  refine ⟨div_ne_zero hb.1 ha.1, ?_, ?_⟩
  · rw [← hc', mul_div_cancel_right₀ _ ha.1]; exact c.2
  · rw [inv_div, ← he', mul_div_cancel_right₀ _ hb.1]; exact e.2

theorem isGenAt_mul_of_unitAt {Λ : Lat ξ Ω} {p : Cpt ξ} {a u : Ω} (ha : Λ.IsGenAt p a) (hu : unitAt ξ p u) :
    Λ.IsGenAt p (u * a) := by
  refine ⟨mul_ne_zero hu.1 ha.1, ?_⟩
  rw [ha.2]
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨⟨u⁻¹, hu.2.2⟩, ?_⟩
    show u⁻¹ * (u * a) = a
    rw [← _root_.mul_assoc, inv_mul_cancel₀ hu.1, _root_.one_mul]
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨u, hu.2.1⟩, rfl⟩

structure IsChart (s : X ⟶ Sp ℂ) {d : ℕ} (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) : Prop where
  isOpen : IsOpen B
  hol : IsHolTo B Y
  isOver : ∀ b ∈ B, Y b ≫ s = 𝟙 _
  factor : ∀ (m : ℕ) (B' : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B' → IsHolTo B' y →
    (∀ b ∈ B', y b ≫ s = 𝟙 _) → ∀ b₀ ∈ B', ∀ b₁ ∈ B, y b₀ = Y b₁ →
    ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B' ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧
      κ b₀ = b₁ ∧ ∀ b ∈ ball b₀ ε, κ b ∈ B ∧ y b = Y (κ b)

theorem IsChart.mono {s : X ⟶ Sp ℂ} {d : ℕ} {B B₂ : Set (Fin d → ℂ)} {Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)}
    (h : IsChart s B Y) (o : IsOpen B₂) (l : B₂ ⊆ B) : IsChart s B₂ Y := by
  refine { isOpen := o, hol := ?_, isOver := fun b hb => h.isOver b (l hb), factor := ?_ }
  · intro U f
    have e : {b ∈ B₂ | ⊤ ≤ Y b ⁻¹ᵁ U} = B₂ ∩ {b ∈ B | ⊤ ≤ Y b ⁻¹ᵁ U} := by
      ext b; exact ⟨fun hb => ⟨hb.1, l hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
    rw [e]
    exact ⟨o.inter (h.hol U f).1, (h.hol U f).2.mono Set.inter_subset_right⟩
  · intro m B' y oB hy ov b₀ h₀ b₁ h₁ e
    obtain ⟨ε, κ, ε0, sub, dκ, k₀, hκ⟩ := h.factor m B' y oB hy ov b₀ h₀ b₁ (l h₁) e
    have c : ContinuousAt κ b₀ := (dκ.differentiableAt (ball_mem_nhds _ ε0)).continuousAt
    have m₂ : κ ⁻¹' B₂ ∈ 𝓝 b₀ := c.preimage_mem_nhds (o.mem_nhds (k₀ ▸ h₁))
    obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem m₂ (ball_mem_nhds b₀ ε0))
    have sb : ball b₀ δ ⊆ ball b₀ ε := fun b hb => (hδ hb).2
    exact ⟨δ, κ, δ0, sb.trans sub, dκ.mono sb, k₀, fun b hb => ⟨(hδ hb).1, (hκ b (sb hb)).2⟩⟩

structure HChart (s : X ⟶ Sp ℂ) (ξ : Sp Ω ⟶ X) (W U : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T : Ω) {d : ℕ}
    (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (H : (Fin d → ℂ) → ℂ) : Prop where
  chart : IsChart s B Y
  inU : ∀ b ∈ B, centre (Y b) ∈ U
  cpt : ∀ b ∈ B, genPt ξ ⤳ centre (Y b)
  dense : ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W
  hol : DifferentiableOn ℂ H B
  ne : ∀ b ∈ B, H b ≠ 0
  rel : ∀ b ∈ B, centre (Y b) ∈ W → ∀ r : ℂ, ValAt ξ (Y b) T r → F (Y b) = H b * r

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetQuotientFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetQuotientFormula
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section Pow1

variable {k : Type} [Field k] {d : ℕ}

theorem aeval_firstOrder {B A : Type} [CommRing B] [Algebra k B] [CommRing A] [Algebra k A]
    (τ : B →ₐ[k] A) (ε : A) (hε : ε * ε = 0) (c : Fin d → k) (z : Fin d → B)
    (P : MvPolynomial (Fin 2 × Fin d) k) :
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then algebraMap k A (c q.2) * ε else τ (z q.2)) P =
      τ (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2) P) +
      ε * ∑ i, algebraMap k A (c i) * τ (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2)
        (MvPolynomial.pderiv ((0 : Fin 2), i) P)) := by
  set θ : MvPolynomial (Fin 2 × Fin d) k →ₐ[k] B :=
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2) with hθ
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    simp only [map_add (f := _), hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P q hP =>
    obtain ⟨a, j⟩ := q
    rw [map_mul, hP, MvPolynomial.aeval_X]
    by_cases ha : a = 0
    · subst ha
      have key : ∀ i, τ (θ (MvPolynomial.pderiv ((0 : Fin 2), i) (P * MvPolynomial.X ((0 : Fin 2), j)))) =
          if j = i then τ (θ P) else 0 := by
        intro i
        have hX : θ (MvPolynomial.X ((0 : Fin 2), j)) = 0 := by simp [hθ]
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, hX, zero_mul, add_zero,
          MvPolynomial.pderiv_X]
        by_cases hij : j = i
        · subst hij; simp
        · simp [Pi.single_apply, hij, Ne.symm hij]
      simp only [key, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hX : θ (P * MvPolynomial.X ((0 : Fin 2), j)) = 0 := by simp [hθ]
      rw [hX, map_zero, zero_add]
      linear_combination (algebraMap k A (c j) * ∑ i, algebraMap k A (c i) * τ (θ (MvPolynomial.pderiv ((0 : Fin 2), i) P))) * hε
    · have key : ∀ i, θ (MvPolynomial.pderiv ((0 : Fin 2), i) (P * MvPolynomial.X (a, j))) =
          θ (MvPolynomial.pderiv ((0 : Fin 2), i) P) * z j := by
        intro i
        have h0 : MvPolynomial.pderiv ((0 : Fin 2), i) (MvPolynomial.X (a, j) : MvPolynomial (Fin 2 × Fin d) k) = 0 := by
          rw [MvPolynomial.pderiv_X, Pi.single_apply, if_neg]
          intro h; exact ha (congrArg Prod.fst h)
        rw [Derivation.leibniz, h0, smul_zero, zero_add, smul_eq_mul, map_mul, mul_comm]
        simp [hθ, ha]
      have hX : θ (P * MvPolynomial.X (a, j)) = θ P * z j := by simp [hθ, ha]
      simp only [key, hX, ha, if_false, map_mul, Finset.mul_sum, Finset.sum_mul, add_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

theorem mk_psTrunc_of_le {κ : Type} [Fintype κ] [DecidableEq κ] {m N : ℕ} (hN : m ≤ N)
    (f : MvPowerSeries κ k) :
    Ideal.Quotient.mk (orig k κ ^ (m + 1)) (psTrunc N f) = psJet m f := by
  rw [psJet, Ideal.Quotient.eq]
  refine GermD.mem_orig_pow_of fun e he => ?_
  by_contra hlt
  push Not at hlt
  apply MvPolynomial.mem_support_iff.mp he
  rw [MvPolynomial.coeff_sub, GermFun.coeff_psTrunc _ _ _ (by omega), GermFun.coeff_psTrunc _ _ _ (by omega), sub_self]

theorem mk_pderiv_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] {m N : ℕ} (hN : m + 1 ≤ N)
    (f : MvPowerSeries κ k) (q : κ) :
    Ideal.Quotient.mk (orig k κ ^ (m + 1)) (MvPolynomial.pderiv q (psTrunc N f)) =
      psJet m (MvPowerSeries.pderiv (R := k) q f) := by
  rw [psJet, Ideal.Quotient.eq]
  refine GermD.mem_orig_pow_of fun e he => ?_
  by_contra hlt
  push Not at hlt
  apply MvPolynomial.mem_support_iff.mp he
  have hd : (e + Finsupp.single q 1).degree = e.degree + 1 := by simp
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_pderiv, GermFun.coeff_psTrunc _ _ _ (by omega),
    GermFun.coeff_psTrunc _ _ _ (by omega), MvPowerSeries.coeff_pderiv, sub_self]

theorem aeval_axis_eq_psJet (m : ℕ) (P : MvPolynomial (Fin 2 × Fin d) k) (h : Germ.PS k 2 d)
    (hP : Ideal.Quotient.mk (orig k (Fin 2 × Fin d) ^ (m + 1)) P = psJet m h) :
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : Jet k (Fin 1 × Fin d) m)
      else Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2))) P =
      psJet m (Germ.ev (n := 1) ![0, Germ.pt k d 0] h) := by
  have ha : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) q.1 q.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a <;> simp [Germ.pt]
  rw [Germ.ev, FBIdJet.psJet_subst m _ ha, ← hP, GermD.jetMap_mk]
  have e : (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : Jet k (Fin 1 × Fin d) m)
      else Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2))) : MvPolynomial (Fin 2 × Fin d) k →ₐ[k] _) =
      (Ideal.Quotient.mkₐ k _).comp (MvPolynomial.aeval fun q : Fin 2 × Fin d =>
        psTrunc m ((![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) q.1 q.2)) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    obtain ⟨a, j⟩ := q
    rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.aeval_X]
    show _ = psJet m _
    fin_cases a
    · simp [psJet, psTrunc]
    · have : (![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) 1 j =
          ((MvPolynomial.X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries _ k) := by
        simp [Germ.pt]
      simp only [Fin.mk_one, this, ExpGF.psJet_coe]
      simp
  rw [e]
  rfl

theorem psJet_sum_C_mul {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (u : Fin d → k)
    (h : Fin d → MvPowerSeries κ k) :
    psJet m (∑ i, MvPowerSeries.C (u i) * h i) = ∑ i, algebraMap k (Jet k κ m) (u i) * psJet m (h i) := by
  have hadd : ∀ f g : MvPowerSeries κ k, psJet m (f + g) = psJet m f + psJet m g := fun f g => by
    simp [psJet, psTrunc, Finset.sum_add_distrib]
  have hzero : psJet m (0 : MvPowerSeries κ k) = 0 := by simp [psJet, psTrunc]
  have hC : ∀ c : k, psJet m (MvPowerSeries.C c : MvPowerSeries κ k) = algebraMap k (Jet k κ m) c := fun c => by
    have : (MvPowerSeries.C c : MvPowerSeries κ k) = ((MvPolynomial.C c : MvPolynomial κ k) : MvPowerSeries κ k) := by simp
    rw [this, ExpGF.psJet_coe]
    rfl
  let L : MvPowerSeries κ k →+ Jet k κ m := ⟨⟨psJet m, hzero⟩, hadd⟩
  have := map_sum L (fun i => MvPowerSeries.C (u i) * h i) Finset.univ
  refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
  show psJet m _ = _
  rw [FBIdJet.psJet_mul, hC]

theorem jq_psJet_ptPow (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d m : ℕ) (w : Fin d → k)
    (g : Germ.PS k 2 d) (hg : AxOne g) :
    jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) =
      1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer g fun i => w i ^ p)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set B := Jet k (Fin 1 × Fin d) m with hB
  set A := Jet B Unit p with hA
  have hε : dQ B p ^ p * dQ B p ^ p = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (by omega) (dQ_pow B p)
  have ha : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) q.1 q.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a
    · simp [ptPow, hp]
    · simp [Germ.pt]
  have hjq : ∀ Q : MvPolynomial (Fin 2 × Fin d) k, jq w p m (Ideal.Quotient.mk _ Q) =
      MvPolynomial.aeval (fun q : Fin 2 × Fin d =>
        if q.1 = 0 then algebraMap k A (w q.2) * dQ B p
        else inR (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2)))) Q := fun Q => rfl
  have step : jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) =
      MvPolynomial.aeval (fun q : Fin 2 × Fin d =>
        if q.1 = 0 then algebraMap k A (w q.2 ^ p) * dQ B p ^ p
        else inR (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2)))) (psTrunc (p + m + 1) g) := by
    rw [Germ.ev, FBIdJet.psJet_subst _ _ ha, psJet, GermD.jetMap_mk, hjq, MvPolynomial.comp_aeval_apply]
    congr 2
    funext q
    obtain ⟨a, j⟩ := q
    rw [← hjq]
    show jq w p m (psJet _ _) = _
    fin_cases a
    · have : (![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) 0 j =
          ((MvPolynomial.X ((0 : Fin 2), j) ^ p : MvPolynomial (Fin 2 × Fin d) k) : MvPowerSeries _ k) := by
        simp [ptPow]
      simp only [Fin.zero_eta, this, ExpGF.psJet_coe, hjq]
      simp [mul_pow]
    · have : (![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) 1 j =
          ((MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin d) k) : MvPowerSeries _ k) := by
        simp [Germ.pt]
      simp only [Fin.mk_one, this, ExpGF.psJet_coe, hjq]
      simp
  rw [step, aeval_firstOrder (inR (k := k) B p) (dQ B p ^ p) hε (fun i => w i ^ p)
    (fun j => Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) (psTrunc (p + m + 1) g)]
  rw [aeval_axis_eq_psJet m _ g (mk_psTrunc_of_le (by omega) g), hg.1, FBIdJet.psJet_one, map_one]
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dSer, psJet_sum_C_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_axis_eq_psJet m _ _ (mk_pderiv_psTrunc (by omega) g _), map_mul]
  rw [← IsScalarTower.algebraMap_apply]
  rfl

end Pow1

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetQuotientFormulaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_jet_quotient_formula : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d m : ℕ) (w : Fin d → k) (g : Germ.PS k 2 d), AxOne g → jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) = 1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer g fun i => w i ^ p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.jq_psJet_ptPow | exact GlobalTheory.CompanionTheory.Ar.Coc.jq_psJet_ptPow | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.jq_psJet_ptPow <;> assumption)
end
end
