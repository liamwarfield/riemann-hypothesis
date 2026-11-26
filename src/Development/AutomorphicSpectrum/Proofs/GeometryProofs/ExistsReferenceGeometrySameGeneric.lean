module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsWithConstantsMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbedsGenericOfCharZero
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbedsGenericOfCharZero
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EmbedsOfTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isLocalRing_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  unfold regAt
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem unitAt_iff_isUnit {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ) (s : regAt ξ p) :
    unitAt ξ p (s : Ω) ↔ IsUnit s := by
  constructor
  · rintro ⟨h0, -, hinv⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨(s : Ω)⁻¹, hinv⟩, ?_⟩
    exact Subtype.ext (mul_inv_cancel₀ h0)
  · intro hs
    obtain ⟨t, ht⟩ := isUnit_iff_exists_inv.mp hs
    have ht' : (s : Ω) * (t : Ω) = 1 := by simpa using congrArg Subtype.val ht
    have h0 : (s : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one ht'
    refine ⟨h0, s.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right ht']
    exact t.2

theorem mem_adjoin_rat_of_int [CharZero Ω] {S : Set Ω} {a : Ω} (h : a ∈ Algebra.adjoin ℤ S) :
    a ∈ Algebra.adjoin ℚ S := by
  induction h using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ Ω) r]
    exact intCast_mem _ r
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem embedsGeneric_of_coordTie : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → EmbedsGeneric ξ x := by
  intro X Ω _ _ ξ κ x h
  unfold EmbedsGeneric
  intro p _
  refine ⟨h.cover p, fun i hi => ⟨?_, ?_⟩⟩
  · intro a ha
    obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h i p hi a).mp ha
    exact ⟨s, mem_adjoin_rat_of_int hs, hu, mem_adjoin_rat_of_int hsa⟩
  · intro q _ hq hpq
    haveI := isLocalRing_regAt h.gen p
    have hmem : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x i), a ∈ regAt ξ p :=
      fun a ha => (h.ring i hi.1 a).mp ha p hi
    let φ : Algebra.adjoin ℤ (Set.range fun j => x j / x i) →+* regAt ξ p :=
      { toFun := fun s => ⟨s, hmem s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let I : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x i)) :=
      Ideal.comap φ (IsLocalRing.maximalIdeal (regAt ξ p))
    have hI : I.IsPrime := Ideal.comap_isPrime φ _
    have key : ∀ s : Algebra.adjoin ℤ (Set.range fun j => x j / x i), s ∉ I ↔ unitAt ξ p (s : Ω) := by
      intro s
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact (unitAt_iff_isUnit p (φ s)).symm
    obtain ⟨p', -, huniq⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x h i hi.1 I hI
    have e1 := huniq p ⟨hi, key⟩
    have e2 := huniq q ⟨hq, fun s => (key s).trans (hpq s (mem_adjoin_rat_of_int s.2))⟩
    exact e1.trans e2.symm

end GlobalTheory.CompanionTheory.Ar.EmbedsOfTie
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EmbedsGenericOfCharZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeds_generic_of_char_zero : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → EmbedsGeneric ξ x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EmbedsOfTie.embedsGeneric_of_coordTie | exact GlobalTheory.CompanionTheory.Ar.EmbedsOfTie.embedsGeneric_of_coordTie | (intros; apply GlobalTheory.CompanionTheory.Ar.EmbedsOfTie.embedsGeneric_of_coordTie <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericCharZero
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.CharZeroModel

theorem charZero_of_flat {X : Scheme.{0}} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
    (s : X ⟶ Spec (CommRingCat.of R)) [Flat s] {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : Function.Injective (Scheme.stalkClosedPointTo ξ).hom) : CharZero Ω := by
  classical
  set x := ξ.base (IsLocalRing.closedPoint Ω) with hx
  have hfl : (s.stalkMap x).hom.Flat := Flat.stalkMap s x
  have hinv : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
  have hgerm := germ_injective_of_isIntegral (X := Spec (CommRingCat.of R)) (U := ⊤) (x := s.base x)
    (hx := trivial)
  have hA : ∀ n : ℕ, n ≠ 0 → (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) ≠ 0 := by
    intro n hn h0
    apply (Nat.cast_ne_zero (R := R)).mpr hn
    apply hinv
    apply hgerm
    simp only [map_zero, map_natCast]
    exact h0
  have hO : ∀ n : ℕ, n ≠ 0 → (n : X.presheaf.stalk x) ≠ 0 := by
    intro n hn h0
    let _ := (s.stalkMap x).hom.toAlgebra
    have : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) (X.presheaf.stalk x) := hfl
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
      (mem_nonZeroDivisors_of_ne_zero (hA n hn))
    have h3 : (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (1 : X.presheaf.stalk x) =
        (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (0 : X.presheaf.stalk x) := by
      rw [smul_zero, Algebra.smul_def, _root_.mul_one, map_natCast]
      exact h0
    exact one_ne_zero (hreg h3)
  exact charZero_of_inj_zero fun n hn => by
    by_contra hne
    apply hO n hne
    apply h
    rw [map_natCast, map_zero]
    exact hn

theorem charZero_function_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → CharZero Ω₀ := by
  intro E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hξ
  have := Y.flat
  exact charZero_of_flat Y.s ξ₀ hξ.bij.1

end GlobalTheory.CompanionTheory.Ar.CharZeroModel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericCharZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_generic_char_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → CharZero Ω₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CharZeroModel.charZero_function_field | exact GlobalTheory.CompanionTheory.Ar.CharZeroModel.charZero_function_field | (intros; apply GlobalTheory.CompanionTheory.Ar.CharZeroModel.charZero_function_field <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReferenceGeometrySameGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

section Segre

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

abbrev segJ (J : K → Type) : K ⊕ Unit → Type := Sum.elim J fun _ : Unit => ∀ k, J k

instance segJ.instFintype : ∀ k, Fintype (segJ J k)
  | .inl k => inferInstanceAs (Fintype (J k))
  | .inr _ => (Fintype.ofFinite (∀ k, J k) : Fintype (∀ k, J k))

def segBlock (y : (Σ k, J k) → Ω) : (Σ _ : Unit, ∀ k, J k) → Ω := fun p => ∏ k, y ⟨k, p.2 k⟩

def segY (y : (Σ k, J k) → Ω) : (Σ k, segJ J k) → Ω
  | ⟨.inl k, i⟩ => y ⟨k, i⟩
  | ⟨.inr _, c⟩ => ∏ k, y ⟨k, c k⟩

theorem segY_prod (y : (Σ k, J k) → Ω) (c : (k : K ⊕ Unit) → segJ J k) :
    ∏ k, segY y ⟨k, c k⟩ = (∏ k, y ⟨k, c (Sum.inl k)⟩) * ∏ k, y ⟨k, c (Sum.inr ()) k⟩ := by
  rw [Fintype.prod_sum_type]
  simp [segY]

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {y : (Σ k, J k) → Ω}

theorem segTie (h : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) :
    CoordTie ℤ ξ fun c' : (k : K ⊕ Unit) → segJ J k => ∏ k, segY y ⟨k, c' k⟩ := by
  have key := @GlobalTheory.T.coords_join_blocks X Ω _ ξ K _ J _ y Unit _ (fun _ => ∀ k, J k) (fun _ => Fintype.ofFinite _) (segBlock y) h
    (fun _ p => by
      obtain ⟨c, hc⟩ := h.cover p
      exact ⟨c, hc⟩)
  have e : (fun c' : (k : K ⊕ Unit) → segJ J k => ∏ k, segY y ⟨k, c' k⟩) =
      fun c' : (k : K ⊕ Unit) → Sum.elim J (fun _ : Unit => ∀ k, J k) k =>
        (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, segBlock y ⟨k, c' (Sum.inr k)⟩ := by
    funext c'
    rw [segY_prod]
    simp [segBlock]
  rw [e]
  exact key

theorem segChart {c : (k : K ⊕ Unit) → segJ J k} {p : Cpt ξ}
    (h : InChart ξ (fun c' : (k : K ⊕ Unit) → segJ J k => ∏ k, segY y ⟨k, c' k⟩) c p) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) (fun k => c (Sum.inl k)) p := by
  obtain ⟨h0, h1⟩ := h
  simp only [segY_prod] at h0 h1
  have hB := right_ne_zero_of_mul h0
  refine ⟨left_ne_zero_of_mul h0, fun c' => ?_⟩
  have h2 := h1 (fun k => match k with
    | .inl k => c' k
    | .inr u => c (Sum.inr u))
  simp only at h2
  rwa [mul_div_mul_right _ _ hB] at h2

theorem segDeg {F : Type} [AddCommGroup F] [Module Ω F] {L : Lat ξ F} {a : K → ℤ} {e₀ : F}
    (h : L.IsDegOn Set.univ y a e₀) : L.IsDegOn Set.univ (segY y) (Sum.elim a 0) e₀ := by
  refine ⟨h.1, fun p _ c' hc => ?_⟩
  have h1 := h.2 p trivial (fun k => c' (Sum.inl k)) (segChart hc)
  have e : (∏ k, segY y ⟨k, c' k⟩ ^ (Sum.elim a 0 : K ⊕ Unit → ℤ) k) =
      ∏ k, y ⟨k, c' (Sum.inl k)⟩ ^ a k := by
    rw [Fintype.prod_sum_type]
    simp [segY]
  rw [e]
  exact h1

end Segre

section Ideal

variable {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)]
  [∀ k, Fintype (J' k)]

theorem mem_mcPts_map (v : (Σ k, J k) → Σ k, J' k) (bd : Ideal (MRing J)) (w : (Σ k, J' k) → ℂ)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hw' : ∀ k, ∃ i, w (v ⟨k, i⟩) ≠ 0) :
    w ∈ mcPts (bd.map (MvPolynomial.rename v)) ↔ (fun p => w (v p)) ∈ mcPts bd := by
  have e : ∀ f : MRing J, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ)
      (MvPolynomial.rename v f)) =
      MvPolynomial.eval (fun p => w (v p)) (MvPolynomial.map (Int.castRingHom ℂ) f) := by
    intro f
    rw [MvPolynomial.map_rename, MvPolynomial.eval_rename]
    rfl
  constructor
  · intro h
    exact ⟨hw', fun f hf => by
      rw [← e]
      exact h.2 _ (Ideal.mem_map_of_mem _ hf)⟩
  · intro h
    refine ⟨hw, fun f hf => ?_⟩
    let φ : MRing J' →+* ℂ := (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ))
    have hle : bd.map (MvPolynomial.rename v) ≤ RingHom.ker φ :=
      Ideal.map_le_iff_le_comap.2 fun g hg => by
        show φ (MvPolynomial.rename v g) = 0
        show MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.rename v g)) = 0
        rw [e]
        exact h.2 g hg
    exact hle hf

end Ideal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HodgeCpt.retie {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {K₂ : Type} [Fintype K₂] {J₂ : K₂ → Type} {y₂ : (Σ k, J₂ k) → Ω}
    (h : CoordTie ℤ 𝔐.ξ fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) : HodgeCpt Y S y₂ where
  X := 𝔐.X
  ξ := 𝔐.ξ
  all := 𝔐.all
  tie := h
  normal := 𝔐.normal
  f := 𝔐.f
  Ω₀ := 𝔐.Ω₀
  ξ₀ := 𝔐.ξ₀
  gen₀ := 𝔐.gen₀
  cst := 𝔐.cst
  cst_over := 𝔐.cst_over
  fn := 𝔐.fn
  fn_over := 𝔐.fn_over
  t := 𝔐.t
  m := 𝔐.m
  Li := 𝔐.Li
  M := 𝔐.M
  ρ := 𝔐.ρ
  act := 𝔐.act
  S_prime := 𝔐.S_prime
  R := 𝔐.R
  R_ge := 𝔐.R_ge
  tors := 𝔐.tors
  vb := 𝔐.vb

def HodgeCpt.Flag.retie {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} (Fl : 𝔐.Flag) {K₂ : Type} [Fintype K₂] {J₂ : K₂ → Type}
    {y₂ : (Σ k, J₂ k) → Ω} (h : CoordTie ℤ 𝔐.ξ fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) :
    (𝔐.retie h).Flag where
  b := Fl.b
  sub := Fl.sub
  Li₀ := Fl.Li₀
  acg := Fl.acg
  mod := Fl.mod
  M₀ := Fl.M₀
  j := Fl.j
  j_pt := Fl.j_pt
  V₀ := Fl.V₀
  V₀_mem := Fl.V₀_mem
  deg := Fl.deg
  generic := Fl.generic

end GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_refGeo : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∃ G : RefGeo Y, genPt G.𝔐.ξ₀ = genPt ξ₀ := by
  intro hRes E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hgen
  haveI : CharZero Ω₀ := GlobalTheory.T.component_generic_char_zero E H D l Xo c Y Ω₀ ξ₀ hgen
  obtain ⟨K₀, _, J₀, _, y₀, X₀, ξ', f₀, cst₀, t₀, m₀, Li', _, _, M', ρ', L', bd₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ :=
    GlobalTheory.T.exists_coords_for_component hRes E H D l Xo c Y Ω₀ ξ₀ hgen
  obtain ⟨Ω, _, _, _, K, _, J, _, y, X, ξ, f, cst, t, m, Li, _, _, M, ρ, Li₀, _, _, M₀, j, V₀, b, bd,
    hall, htie, hnorm, hdom, hcst, hact, hjpt, hV, hflag, hvb, hsnc, hbd⟩ :=
    GlobalTheory.T.coords_with_constants_map E H D l Xo c Y Ω₀ ξ₀ K₀ J₀ y₀ X₀ ξ' f₀ cst₀ t₀ m₀ Li' M' ρ' L' bd₀ hgen h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  obtain ⟨K', _, J', _, y', bk, bx, 𝔐, g, Fl, xdeg, e, hbk, hy, hξ, hf, hg0, hdeg, hlines, -, hreg, hinj⟩ :=
    GlobalTheory.T.generic_coords_descend_subfield E H D l Xo c Y Ω K J y X ξ f Ω₀ ξ₀ cst t m Li M ρ Li₀ M₀ j V₀ b 1 hall htie hnorm hgen hdom hcst
      hact hjpt hV hflag hvb
  have tie₂ := segTie (y := y') 𝔐.tie
  have hy₂ : ∀ k (a : J k), segY y' ⟨Sum.inl (bk k), bx k a⟩ = y ⟨k, a⟩ := hy
  let v : (Σ k, J k) → Σ k, segJ J' k := fun p => ⟨Sum.inl (bk p.1), bx p.1 p.2⟩
  refine ⟨{ Ω := Ω, K := K' ⊕ Unit, J := segJ J', y := segY y', 𝔐 := 𝔐.retie tie₂, Fl := Fl.retie tie₂,
            deg_one := hdeg, xdeg := fun r => Sum.elim (xdeg r) 0, e := e, lines := ?_,
            bd := bd.map (MvPolynomial.rename v), snc := ?_, bd_iff := ?_, k₀ := Sum.inr (), embeds := ?_ }, hg0⟩
  · exact fun r => segDeg (hlines r)
  · exact GlobalTheory.T.snc_model_reindexed_coords X 𝔐.X Ω ξ 𝔐.ξ g K J y (K' ⊕ Unit) (segJ J') (segY y') (fun k => Sum.inl (bk k)) bx _ bd
      hall 𝔐.all htie tie₂ hξ hy₂ hreg hinj hsnc
  · intro z w hw
    have hw₁ := GlobalTheory.T.complex_coords_reindexed X 𝔐.X Ω ξ 𝔐.ξ g K J y (K' ⊕ Unit) (segJ J') (segY y') (fun k => Sum.inl (bk k)) bx z w
      hall 𝔐.all 𝔐.tie.gen hξ hy₂ hreg hw
    have hne : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => (hw.1 k).imp fun _ h => h.ne_zero
    have hne' : ∀ k, ∃ i, w (v ⟨k, i⟩) ≠ 0 := fun k => (hw₁.1 k).imp fun _ h => h.ne_zero
    rw [mem_mcPts_map v bd w hne hne']
    refine (show (fun p => w (v p)) ∈ mcPts bd ↔ _ from hbd (z ≫ g) _ hw₁).trans ?_
    have hab := abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (centre z)
    have hc : f (centre (z ≫ g)) = 𝔐.f (centre z) := by
      rw [hf]
      rfl
    rw [hc]
    exact not_congr hab
  · exact GlobalTheory.T.embeds_generic_of_char_zero 𝔐.X Ω 𝔐.ξ _ _ 𝔐.tie

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReferenceGeometrySameGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reference_geometry_same_generic : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∃ G : RefGeo Y, genPt G.𝔐.ξ₀ = genPt ξ₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_refGeo | exact GlobalTheory.CompanionTheory.Ar.exists_refGeo | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_refGeo <;> assumption)
end
