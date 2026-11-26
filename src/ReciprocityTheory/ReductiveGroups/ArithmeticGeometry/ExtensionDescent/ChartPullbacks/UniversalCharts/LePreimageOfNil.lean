module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R₀ : Type} [CommRing R₀]

abbrev sp (P : Type) [CommRing P] [Algebra R₀ P] : Over (Spec (CommRingCat.of R₀)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R₀ P)))

def spMap {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P'] (g : P →ₐ[R₀] P') :
    sp (R₀ := R₀) P' ⟶ sp P :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    simp only [sp, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact g.comp_algebraMap)

theorem spMap_left {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P'] (g : P →ₐ[R₀] P') :
    (spMap g).left = Spec.map (CommRingCat.ofHom g.toRingHom) := rfl

theorem spMap_comp {P P' P'' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P']
    [CommRing P''] [Algebra R₀ P''] (g : P →ₐ[R₀] P') (g' : P' →ₐ[R₀] P'') :
    spMap g' ≫ spMap g = spMap (R₀ := R₀) (g'.comp g) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, spMap_left, spMap_left, spMap_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

section Chart

variable (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]

structure Chart where
  U : G.left.Opens
  hU : IsAffineOpen U
  he : ⊤ ≤ (η[G]).left ⁻¹ᵁ U

variable {G}

def alg0 (C : Chart G) : R₀ →+* Γ(G.left, C.U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ G.hom.appLE ⊤ C.U le_top).hom

instance (C : Chart G) : Algebra R₀ Γ(G.left, C.U) := (alg0 C).toAlgebra

theorem fromSpec_over (C : Chart G) :
    C.hU.fromSpec ≫ G.hom = Spec.map (CommRingCat.ofHom (alg0 C)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec G.hom (isAffineOpen_top _) C.hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

def pt (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (h : Γ(G.left, C.U) →ₐ[R₀] P) : sp P ⟶ G :=
  Over.homMk (Spec.map (CommRingCat.ofHom h.toRingHom) ≫ C.hU.fromSpec) (by
    simp only [sp, Over.mk_hom]
    rw [Category.assoc, fromSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact h.comp_algebraMap)

theorem pt_left (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (h : Γ(G.left, C.U) →ₐ[R₀] P) :
    (pt C h).left = Spec.map (CommRingCat.ofHom h.toRingHom) ≫ C.hU.fromSpec := rfl

theorem spMap_pt (C : Chart G) {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P']
    (g : P →ₐ[R₀] P') (h : Γ(G.left, C.U) →ₐ[R₀] P) : spMap g ≫ pt C h = pt C (g.comp h) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, spMap_left, pt_left, pt_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem pt_injective (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] {h h' : Γ(G.left, C.U) →ₐ[R₀] P}
    (H : pt C h = pt C h') : h = h' := by
  have h1 : (pt C h).left = (pt C h').left := by rw [H]
  rw [pt_left, pt_left] at h1
  have h2 := (cancel_mono C.hU.fromSpec).mp h1
  have h3 := Spec.map_injective h2
  apply AlgHom.ext
  intro a
  exact congrArg (fun f => f.hom a) h3

theorem chart_eq (C : Chart G) {P : Type} [CommRing P] (x : Spec (CommRingCat.of P) ⟶ G.left)
    (hx : ⊤ ≤ x ⁻¹ᵁ C.U) :
    Spec.map (x.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom) ≫ C.hU.fromSpec = x := by
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec x C.hU (isAffineOpen_top _) hx,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem exists_pt (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (x : sp P ⟶ G)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ C.U) : ∃ h : Γ(G.left, C.U) →ₐ[R₀] P, x = pt C h := by
  have hx' : Spec.map (x.left.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom) ≫ C.hU.fromSpec =
      x.left := chart_eq C x.left hx
  have hc : (x.left.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom.comp (alg0 C) =
      algebraMap R₀ P := by
    have e : Spec.map (CommRingCat.ofHom ((x.left.appLE C.U ⊤ hx ≫
        (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom.comp (alg0 C))) =
        Spec.map (CommRingCat.ofHom (algebraMap R₀ P)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, ← fromSpec_over, ← Category.assoc, hx']
      exact Over.w x
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  refine ⟨{ (x.left.appLE C.U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom with
    commutes' := fun r => RingHom.congr_fun hc r }, ?_⟩
  apply Over.OverMorphism.ext
  rw [pt_left]
  exact hx'.symm

theorem le_preimage_of_nil (C : Chart G) {P P₀ : Type} [CommRing P] [Algebra R₀ P] [CommRing P₀]
    [Algebra R₀ P₀] (q : P →ₐ[R₀] P₀) (hq : Function.Surjective q)
    (hn : ∀ a ∈ RingHom.ker q, IsNilpotent a) (x : sp P ⟶ G) (h₀ : Γ(G.left, C.U) →ₐ[R₀] P₀)
    (hx : spMap q ≫ x = pt C h₀) : ⊤ ≤ x.left ⁻¹ᵁ C.U := by
  intro p _
  have hker : RingHom.ker q.toRingHom ≤ PrimeSpectrum.asIdeal p := by
    intro a ha
    obtain ⟨k, hk⟩ := hn a ha
    exact (PrimeSpectrum.isPrime p).mem_of_pow_mem k (by rw [hk]; exact Ideal.zero_mem _)
  haveI := PrimeSpectrum.isPrime p
  let p₀ : PrimeSpectrum P₀ :=
    ⟨(PrimeSpectrum.asIdeal p).map q.toRingHom, Ideal.map_isPrime_of_surjective hq hker⟩
  have hp₀ : (Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀ = p := by
    apply PrimeSpectrum.ext
    show Ideal.comap q.toRingHom (Ideal.map q.toRingHom (PrimeSpectrum.asIdeal p)) = PrimeSpectrum.asIdeal p
    exact (Ideal.comap_map_of_surjective' q.toRingHom hq _).trans (sup_eq_left.mpr hker)
  have e : Spec.map (CommRingCat.ofHom q.toRingHom) ≫ x.left =
      Spec.map (CommRingCat.ofHom h₀.toRingHom) ≫ C.hU.fromSpec := by
    rw [← spMap_left, ← Over.comp_left, hx, pt_left]
  have hmem : C.hU.fromSpec.base ((Spec.map (CommRingCat.ofHom h₀.toRingHom)).base p₀) ∈ C.U := by
    rw [← SetLike.mem_coe, ← C.hU.range_fromSpec]
    exact Set.mem_range_self _
  have h3 : (Spec.map (CommRingCat.ofHom q.toRingHom) ≫ x.left).base p₀ =
      (Spec.map (CommRingCat.ofHom h₀.toRingHom) ≫ C.hU.fromSpec).base p₀ := by
    rw [e]
  have h2 : x.left.base ((Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀) ∈ C.U := by
    have h4 : x.left.base ((Spec.map (CommRingCat.ofHom q.toRingHom)).base p₀) =
        C.hU.fromSpec.base ((Spec.map (CommRingCat.ofHom h₀.toRingHom)).base p₀) := h3
    rw [h4]
    exact hmem
  rw [← hp₀]
  exact h2

end Chart

section ChartB

theorem exists_chart [IsLocalRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] :
    Nonempty (Chart G) := by
  obtain ⟨U, hU, hmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (η[G]).left.base (IsLocalRing.closedPoint R₀)) (U := ⊤) (by trivial)
  refine ⟨⟨U, hU, ?_⟩⟩
  intro y _
  exact (IsLocalRing.specializes_closedPoint (R := R₀) y).mem_open ((η[G]).left ⁻¹ᵁ U).isOpen hmem

variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G]

def epsHom (C : Chart G) : Γ(G.left, C.U) ⟶ CommRingCat.of R₀ :=
  Scheme.Hom.appLE (η[G]).left C.U ⊤ C.he ≫ (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom

theorem epsHom_spec (C : Chart G) : Spec.map (epsHom C) ≫ C.hU.fromSpec = (η[G]).left := chart_eq C (η[G]).left C.he

theorem epsHom_comp (C : Chart G) : (epsHom C).hom.comp (alg0 C) = RingHom.id R₀ := by
  have e : Spec.map (CommRingCat.ofHom ((epsHom C).hom.comp (alg0 C))) =
      Spec.map (CommRingCat.ofHom (RingHom.id R₀)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, ← fromSpec_over, ← Category.assoc,
      epsHom_spec, CommRingCat.ofHom_id, Spec.map_id]
    exact Over.w (η[G])
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

def eps (C : Chart G) : Γ(G.left, C.U) →ₐ[R₀] R₀ :=
  { (epsHom C).hom with commutes' := fun r => RingHom.congr_fun (epsHom_comp C) r }

theorem pt_eps (C : Chart G) (P : Type) [CommRing P] [Algebra R₀ P] :
    pt C ((Algebra.ofId R₀ P).comp (eps C)) = (1 : sp P ⟶ G) := by
  apply Over.OverMorphism.ext
  rw [pt_left]
  have e : CommRingCat.ofHom ((Algebra.ofId R₀ P).comp (eps C)).toRingHom =
      epsHom C ≫ CommRingCat.ofHom (algebraMap R₀ P) := rfl
  rw [e, Spec.map_comp, Category.assoc, epsHom_spec]
  rfl

end ChartB

section Smooth

variable {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] (C : Chart G)

theorem chart_smooth [Smooth G.hom] : Algebra.Smooth R₀ Γ(G.left, C.U) := by
  have h1 : Smooth (C.hU.fromSpec ≫ G.hom) := inferInstance
  rw [fromSpec_over] at h1
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h1

end Smooth

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open MvPolynomial

section Jet

variable (R : Type) [CommRing R]

abbrev JetR (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ R ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))) ^ (m + 1)

def jetTruncR (κ : Type) (m : ℕ) : JetR R κ (m + 1) →ₐ[R] JetR R κ m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

def jetZeroR (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ 0 :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

variable {R}

abbrev zR {κ : Type} (m : ℕ) (j : κ) : JetR R κ m := Ideal.Quotient.mk _ (MvPolynomial.X j)

variable (R)

theorem span_X_le_ker_aeval_zero (κ : Type) :
    Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) ≤
      RingHom.ker (MvPolynomial.aeval (R := R) (fun _ : κ => (0 : R))) := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  simp

def jetAug (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (fun _ : κ => (0 : R))) (fun a ha =>
    span_X_le_ker_aeval_zero R κ (Ideal.pow_le_self (by omega) ha))

variable {R}

theorem jetAug_zR {κ : Type} (m : ℕ) (j : κ) : jetAug R κ m (zR m j) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X j) = 0
  simp

theorem jet_ext {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] {ψ₁ ψ₂ : JetR R κ m →ₐ[R] A}
    (h : ∀ j, ψ₁ (zR (R := R) m j) = ψ₂ (zR (R := R) m j)) : ψ₁ = ψ₂ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  exact h j


variable (R) in
def jetLift {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] (J : Ideal A) (hJ : J ^ (m + 1) = ⊥)
    (b : κ → A) (hb : ∀ j, b j ∈ J) : JetR R κ m →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval b) (fun a ha => by
    have h1 : Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) ≤
        J.comap (MvPolynomial.aeval (R := R) b) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simpa using hb j
    have h2 : a ∈ (J ^ (m + 1)).comap (MvPolynomial.aeval (R := R) b) :=
      Ideal.le_comap_pow _ (m + 1) (Ideal.pow_right_mono h1 (m + 1) ha)
    rw [hJ] at h2
    exact h2)

theorem jetLift_zR {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] (J : Ideal A)
    (hJ : J ^ (m + 1) = ⊥) (b : κ → A) (hb : ∀ j, b j ∈ J) (j : κ) :
    jetLift (R := R) J hJ b hb (zR m j) = b j := by
  show MvPolynomial.aeval b (MvPolynomial.X j) = b j
  simp

theorem sub_const_mem_span_X {κ : Type} (p : MvPolynomial κ R) :
    p - MvPolynomial.C (MvPolynomial.aeval (fun _ : κ => (0 : R)) p) ∈
      Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) := by
  classical
  have hs : Set.range (MvPolynomial.X : κ → MvPolynomial κ R) = MvPolynomial.X '' Set.univ := by
    rw [Set.image_univ]
  rw [hs, MvPolynomial.mem_ideal_span_X_image]
  intro mono hm
  by_contra hcon
  push Not at hcon
  have h0 : mono = 0 := by
    ext i
    exact hcon i (Set.mem_univ i)
  subst h0
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl] at hm
  apply hm
  rw [sub_eq_zero, MvPolynomial.aeval_zero', ← MvPolynomial.constantCoeff_eq]
  rfl

theorem ker_jetAug_pow (κ : Type) (m : ℕ) : (RingHom.ker (jetAug R κ m)) ^ (m + 1) = ⊥ := by
  have hle : RingHom.ker (jetAug R κ m) ≤
      (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hp : MvPolynomial.aeval (fun _ : κ => (0 : R)) p = 0 := hx
    have := sub_const_mem_span_X (R := R) p
    rw [hp, map_zero, sub_zero] at this
    exact Ideal.mem_map_of_mem _ this
  rw [← le_bot_iff]
  calc (RingHom.ker (jetAug R κ m)) ^ (m + 1)
      ≤ ((Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))).map (Ideal.Quotient.mk _)) ^ (m + 1) :=
        Ideal.pow_right_mono hle _
    _ = ((Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))) ^ (m + 1)).map (Ideal.Quotient.mk _) :=
        (Ideal.map_pow _ _ _).symm
    _ = ⊥ := Ideal.map_quotient_self _

theorem ker_jetAug_nil (κ : Type) (m : ℕ) : IsNilpotent (RingHom.ker (jetAug R κ m)) :=
  ⟨m + 1, by rw [ker_jetAug_pow, Ideal.zero_eq_bot]⟩

theorem zR_mem_ker {κ : Type} (m : ℕ) (j : κ) : zR (R := R) m j ∈ RingHom.ker (jetAug R κ m) :=
  jetAug_zR m j

end Jet

section Etale

variable {R : Type} [CommRing R] {n : ℕ} {S : Type} [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial (Fin n) R) S] [IsScalarTower R (MvPolynomial (Fin n) R) S]


variable (R) in
abbrev sX (j : Fin n) : S := algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X j)

variable [Algebra.FormallyEtale (MvPolynomial (Fin n) R) S] (ε : S →ₐ[R] R)

theorem etale_ext {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R)
    (hJ : IsNilpotent (RingHom.ker aug)) (φ₁ φ₂ : S →ₐ[R] A) (h1 : aug.comp φ₁ = ε) (h2 : aug.comp φ₂ = ε)
    (hs : ∀ j : Fin n, φ₁ (sX (R := R) (S := S) j) = φ₂ (sX (R := R) (S := S) j)) : φ₁ = φ₂ := by
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A := φ₁.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) S)
  have hρ2 : φ₂.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) S) = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) A := IsScalarTower.of_algebraMap_eq (fun r => (ρ.commutes r).symm)
  let ψ₁ : S →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : S →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  have : ψ₁ = ψ₂ := by
    apply Algebra.FormallyUnramified.lift_unique (RingHom.ker aug) hJ
    ext x
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (AlgHom.congr_fun h1 x).trans (AlgHom.congr_fun h2 x).symm
  ext x
  exact AlgHom.congr_fun this x

theorem etale_exists {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R)
    (hJ : IsNilpotent (RingHom.ker aug)) (b : Fin n → A) (hb : ∀ j, aug (b j) = ε (sX (R := R) j)) :
    ∃ φ : S →ₐ[R] A, aug.comp φ = ε ∧ ∀ j, φ (sX (R := R) j) = b j := by
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A := MvPolynomial.aeval b
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) A := IsScalarTower.of_algebraMap_eq (fun r => (ρ.commutes r).symm)
  let J := RingHom.ker aug
  let mk : A →ₐ[MvPolynomial (Fin n) R] A ⧸ J := Ideal.Quotient.mkₐ _ J
  have hmkR : ∀ a : A, mk a = Ideal.Quotient.mk J (algebraMap R A (aug a)) := by
    intro a
    show Ideal.Quotient.mk J a = Ideal.Quotient.mk J (algebraMap R A (aug a))
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  let f₀r : S →+* A ⧸ J := (Ideal.Quotient.mk J).comp ((algebraMap R A).comp ε.toRingHom)
  have hf₀ : ∀ p : MvPolynomial (Fin n) R, f₀r (algebraMap _ S p) = algebraMap _ (A ⧸ J) p := by
    have : f₀r.comp (algebraMap (MvPolynomial (Fin n) R) S) = algebraMap (MvPolynomial (Fin n) R) (A ⧸ J) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show Ideal.Quotient.mk J (algebraMap R A (ε (algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.C r)))) =
          Ideal.Quotient.mk J (ρ (MvPolynomial.C r))
        rw [MvPolynomial.aeval_C, show algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.C r) = algebraMap R S r from
          (IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) S r).symm, AlgHom.commutes,
          Algebra.algebraMap_self, RingHom.id_apply]
      · intro j
        show Ideal.Quotient.mk J (algebraMap R A (ε (sX (R := R) j))) = Ideal.Quotient.mk J (ρ (MvPolynomial.X j))
        rw [MvPolynomial.aeval_X, Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes,
          Algebra.algebraMap_self, RingHom.id_apply, hb, sub_self]
    exact fun p => RingHom.congr_fun this p
  let f₀ : S →ₐ[MvPolynomial (Fin n) R] A ⧸ J := { f₀r with commutes' := hf₀ }
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker (mk : A →+* A ⧸ J)) := by
    have : RingHom.ker (mk : A →+* A ⧸ J) = J := Ideal.mk_ker
    rw [this]
    exact hJ
  let φ' := Algebra.FormallySmooth.liftOfSurjective f₀ mk hmk hker
  have hφ' : mk.comp φ' = f₀ := Algebra.FormallySmooth.comp_liftOfSurjective f₀ mk hmk hker
  refine ⟨φ'.restrictScalars R, ?_, ?_⟩
  · ext x
    have e1 := AlgHom.congr_fun hφ' x
    simp only [AlgHom.comp_apply] at e1
    rw [hmkR] at e1
    have e2 : (Ideal.Quotient.mk J) (algebraMap R A (aug (φ' x))) = (Ideal.Quotient.mk J) (algebraMap R A (ε x)) := e1
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.id_apply, sub_eq_zero] at e2
    exact e2
  · intro j
    show φ' (algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X j)) = b j
    rw [AlgHom.commutes]
    show ρ (MvPolynomial.X j) = b j
    exact MvPolynomial.aeval_X b j

end Etale

end ReciprocityTheory.ChartRestriction.G.Chart
end
end
