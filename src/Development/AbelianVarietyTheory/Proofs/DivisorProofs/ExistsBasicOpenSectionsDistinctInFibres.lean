module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealSubfieldNegativeTwoPlacesNormEverywher
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetOnCompactTorus
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualizerSectionsClosedIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionsEq
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.IdealSectionsFactorization

theorem comp_eq_iff_factors {S X B W : Scheme.{0}} (p : X ⟶ B) (x y : S ⟶ X)
    (h : x ≫ p = y ≫ p) (g : W ⟶ S) :
    g ≫ x = g ≫ y ↔
      ∃ l : W ⟶ pullback (pullback.lift x y h) (pullback.diagonal p),
        l ≫ pullback.fst _ _ = g := by
  constructor
  · intro hg
    refine ⟨pullback.lift g (g ≫ x) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp [pullback.diagonal_fst, pullback.lift_fst]
    · simp [pullback.diagonal_snd, pullback.lift_snd, hg]
  · rintro ⟨l, rfl⟩
    have hc := pullback.condition (f := pullback.lift x y h) (g := pullback.diagonal p)
    have h1 := congrArg (· ≫ pullback.fst p p) hc
    have h2 := congrArg (· ≫ pullback.snd p p) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd, Category.comp_id] at h1 h2
    rw [Category.assoc, Category.assoc, h1, h2]

theorem factors_iff_kills {R T : Type} [CommRing R] [CommRing T] (I : Ideal R) (ψ : R →+* T) :
    (∃ l : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (R ⧸ I)),
      l ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = Spec.map (CommRingCat.ofHom ψ)) ↔
      ∀ r ∈ I, ψ r = 0 := by
  constructor
  · rintro ⟨l, hl⟩ r hr
    obtain ⟨φ, rfl⟩ := Spec.map_surjective l
    rw [← Spec.map_comp] at hl
    have h := Spec.map_injective hl
    have h' : φ.hom (Ideal.Quotient.mk I r) = ψ r :=
      congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of T => k.hom r) h
    rw [← h', Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  · intro h
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ h)), ?_⟩
    rw [← Spec.map_comp]
    congr 1

theorem exists_ideal_sections_eq (R : Type) [CommRing R]
    (X : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) (hX : IsSeparated X.hom)
    (x y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ X.left)
    (hx : x ≫ X.hom = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R))
    (hy : y ≫ X.hom = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) :
    ∃ I : Ideal R, ∀ (T : Type) [CommRing T] (ψ : R →+* T),
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ x = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ y ↔
        ∀ r ∈ I, ψ r = 0 := by
  have h : x ≫ X.hom = y ≫ X.hom := hx.trans hy.symm
  have hc : IsClosedImmersion
      (pullback.fst (pullback.lift x y h) (pullback.diagonal X.hom)) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ _).flip hX.isClosedImmersion_diagonal
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp hc
  refine ⟨I, fun T _ ψ => ?_⟩
  rw [comp_eq_iff_factors X.hom x y h, ← factors_iff_kills I ψ, he]
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ e.hom, by rw [Category.assoc]; exact hl⟩
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ e.inv, by rw [Category.assoc, e.inv_hom_id_assoc]; exact hl⟩

end GlobalTheory.IdealSectionsFactorization
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualizerSectionsClosedIdeal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sections_eqLocus_ideal : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom →
    ∀ (x y : Sp R ⟶ X.left), x ≫ X.hom = 𝟙 _ → y ≫ X.hom = 𝟙 _ → ∃ I : Ideal R,
      ∀ (T : Type) [CommRing T] (ψ : R →+* T), (spMap ψ ≫ x = spMap ψ ≫ y ↔ ∀ r ∈ I, ψ r = 0) := by
  first
  | exact @_root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq
  | exact _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq
  | (apply _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdealSectionsFactorization.exists_ideal_sections_eq ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualizerSectionsClosedIdealStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalizer_sections_closed_ideal : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (x y : Sp R ⟶ X.left), x ≫ X.hom = 𝟙 _ → y ≫ X.hom = 𝟙 _ → ∃ I : Ideal R, ∀ (T : Type) [CommRing T] (ψ : R →+* T), (spMap ψ ≫ x = spMap ψ ≫ y ↔ ∀ r ∈ I, ψ r = 0) := by
  first | exact @GlobalTheory.sections_eqLocus_ideal | exact GlobalTheory.sections_eqLocus_ideal | (intros; apply GlobalTheory.sections_eqLocus_ideal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibres
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionsSpread

theorem sep_elem (R : Type) [CommRing R] (X : Over (Sp R)) (hX : IsSeparated X.hom)
    (K : Type) [Field K] (e : R →+* K) (x y : Sp R ⟶ X.left)
    (hx : x ≫ X.hom = 𝟙 _) (hy : y ≫ X.hom = 𝟙 _) (hne : spMap e ≫ x ≠ spMap e ≫ y) :
    ∃ r : R, e r ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), ψ r ≠ 0 →
      spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  obtain ⟨I, hI⟩ := GlobalTheory.T.equalizer_sections_closed_ideal R X hX x y hx hy
  have h1 : ¬ ∀ r ∈ I, e r = 0 := fun h => hne ((hI K e).2 h)
  push_neg at h1
  obtain ⟨r, hrI, hr⟩ := h1
  refine ⟨r, hr, fun F _ ψ hψ heq => hψ ((hI F ψ).1 heq r hrI)⟩

theorem pairs : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ t : Finset (Sp R ⟶ X.left), (∀ x ∈ t, x ≫ X.hom = 𝟙 _) → (∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap e ≫ x ≠ spMap e ≫ y) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → ∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  intro R _ X hX K _ e _ t ht hsep
  classical
  let g : (Sp R ⟶ X.left) × (Sp R ⟶ X.left) → R := fun p =>
    if h : p.1 ∈ t ∧ p.2 ∈ t ∧ p.1 ≠ p.2 then
      Classical.choose (sep_elem R X hX K e p.1 p.2 (ht _ h.1) (ht _ h.2.1) (hsep _ h.1 _ h.2.1 h.2.2))
    else 1
  have hg : ∀ p : (Sp R ⟶ X.left) × (Sp R ⟶ X.left), e (g p) ≠ 0 ∧
      ∀ (F : Type) [Field F] (ψ : R →+* F), ψ (g p) ≠ 0 → p.1 ∈ t → p.2 ∈ t → p.1 ≠ p.2 →
        spMap ψ ≫ p.1 ≠ spMap ψ ≫ p.2 := by
    intro p
    by_cases h : p.1 ∈ t ∧ p.2 ∈ t ∧ p.1 ≠ p.2
    · have hs := Classical.choose_spec
        (sep_elem R X hX K e p.1 p.2 (ht _ h.1) (ht _ h.2.1) (hsep _ h.1 _ h.2.1 h.2.2))
      simp only [g, dif_pos h]
      exact ⟨hs.1, fun F _ ψ hψ _ _ _ => hs.2 F ψ hψ⟩
    · simp only [g, dif_neg h]
      exact ⟨by simp, fun F _ ψ _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  refine ⟨∏ p ∈ t ×ˢ t, g p, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun p _ => (hg p).1
  · intro F _ ψ hu x hx y hy hxy
    have hmem : (x, y) ∈ t ×ˢ t := Finset.mem_product.2 ⟨hx, hy⟩
    have hdvd : g (x, y) ∣ ∏ p ∈ t ×ˢ t, g p := Finset.dvd_prod_of_mem g hmem
    have hu' : IsUnit (ψ (g (x, y))) := isUnit_of_dvd_unit (map_dvd ψ hdvd) hu
    exact (hg (x, y)).2 F ψ hu'.ne_zero hx hy hxy

end GlobalTheory.SectionsSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibresStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_sections_distinct_in_fibres : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ t : Finset (Sp R ⟶ X.left), (∀ x ∈ t, x ≫ X.hom = 𝟙 _) → (∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap e ≫ x ≠ spMap e ≫ y) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → ∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  first | exact @GlobalTheory.SectionsSpread.pairs | exact GlobalTheory.SectionsSpread.pairs | (intros; apply GlobalTheory.SectionsSpread.pairs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveMarkOfIrreducible
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.MoveMark

section Field

variable {F M : Type} [Field F] [Field M] [Algebra F M]

theorem exists_emb (pb : PowerBasis F M) (τ : F →+* ℂ) (z : ℂ) (hz : (minpoly F pb.gen).eval₂ τ z = 0) :
    ∃ e : M →+* ℂ, (∀ x, e (algebraMap F M x) = τ x) ∧ e pb.gen = z := by
  letI : Algebra F ℂ := τ.toAlgebra
  have h : Polynomial.aeval z (minpoly F pb.gen) = 0 := hz
  exact ⟨(pb.lift z h : M →ₐ[F] ℂ), fun x => (pb.lift z h).commutes x, pb.lift_gen z h⟩

theorem gen_ind (pb : PowerBasis F M) (q : M → Prop) (h0 : q pb.gen) (h1 : ∀ x, q (algebraMap F M x))
    (h2 : ∀ x y, q x → q y → q (x + y)) (h3 : ∀ x y, q x → q y → q (x * y)) (y : M) : q y := by
  have hy : y ∈ Algebra.adjoin F {pb.gen} := by rw [pb.adjoin_gen_eq_top]; trivial
  induction hy using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h0
  | algebraMap r => exact h1 r
  | add x y _ _ hx hy => exact h2 x y hx hy
  | mul x y _ _ hx hy => exact h3 x y hx hy

theorem emb_ext (pb : PowerBasis F M) (e e' : M →+* ℂ) (h1 : ∀ x, e (algebraMap F M x) = e' (algebraMap F M x))
    (h0 : e pb.gen = e' pb.gen) : e = e' :=
  RingHom.ext (gen_ind pb (fun y => e y = e' y) h0 h1 (fun x y hx hy => by simp only [map_add (f := _), hx, hy])
    (fun x y hx hy => by simp only [map_mul, hx, hy]))

theorem emb_root (pb : PowerBasis F M) (e : M →+* ℂ) :
    (minpoly F pb.gen).eval₂ (e.comp (algebraMap F M)) (e pb.gen) = 0 := by
  rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

variable [NumberField F] [IsCMField F]

theorem ne_conj (τ : F →+* ℂ) (e e' : M →+* ℂ) (h : ∀ x, e (algebraMap F M x) = τ x)
    (h' : ∀ x, e' (algebraMap F M x) = τ x) : e ≠ ComplexEmbedding.conjugate e' := by
  intro he
  apply IsCMField.complexConj_ne_one F
  ext x
  apply τ.injective
  rw [IsCMField.complexEmbedding_complexConj, ← h' x]
  have := DFunLike.congr_fun he (algebraMap F M x)
  rw [ComplexEmbedding.conjugate_coe_eq] at this
  rw [← this, h]
  rfl

omit [NumberField F] [IsCMField F] in
theorem place_eq (v w : InfinitePlace F) (e e' : M →+* ℂ) (h : ∀ x, e (algebraMap F M x) = w.embedding x)
    (h' : ∀ x, e' (algebraMap F M x) = v.embedding x) (he : e = e' ∨ e = ComplexEmbedding.conjugate e') : w = v := by
  rw [← w.mk_embedding, ← v.mk_embedding]
  rcases he with he | he
  · congr 1
    ext x
    rw [← h, ← h', he]
  · rw [← InfinitePlace.mk_conjugate_eq v.embedding]
    congr 1
    ext x
    rw [← h, he, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h']

end Field

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_add (x y : G.C) : sh G (x + y) = sh G x + sh G y := by
  simp only [sh, map_add (f := _), MulOpposite.unop_add]

variable {M : Type} [Field M] [NumberField M] [Algebra G.F M]

theorem conj_law (P : Pair G) (pb : PowerBasis G.F M) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = P.γ) (σ : M →+* M)
    (hσ : ∀ x : G.F, σ (algebraMap G.F M x) = algebraMap G.F M (IsCMField.complexConj G.F x))
    (hπ : σ pb.gen * pb.gen = ((P.c : ℚ) : M)) (y : M) : (P.β : G.C) * sh G (j y) = j (σ y) * P.β := by
  refine gen_ind pb (fun y => (P.β : G.C) * sh G (j y) = j (σ y) * P.β) ?_ ?_ ?_ ?_ y
  · have h1 : (P.γ : G.C) * j (σ pb.gen) = algebraMap ℚ G.C P.c := by
      rw [← hj, ← map_mul, mul_comm, hπ, IsScalarTower.algebraMap_apply ℚ G.F G.C, ← j.commutes]
      congr 1
      simp
    show (P.β : G.C) * sh G (j pb.gen) = j (σ pb.gen) * P.β
    apply P.γ.isUnit.mul_left_cancel
    rw [hj, ← mul_assoc, P.sim, ← mul_assoc, h1]
  · intro x
    show (P.β : G.C) * sh G (j (algebraMap G.F M x)) = j (σ (algebraMap G.F M x)) * P.β
    rw [hσ, j.commutes, j.commutes, sh, G.star_F, Algebra.commutes]
  · intro x y hx hy
    show (P.β : G.C) * sh G (j (x + y)) = j (σ (x + y)) * P.β
    rw [map_add (f := _), sh_add, mul_add, hx, hy, map_add (f := _), map_add (f := _), add_mul]
  · intro x y hx hy
    show (P.β : G.C) * sh G (j (x * y)) = j (σ (x * y)) * P.β
    rw [map_mul, sh_mul, ← mul_assoc, hy, mul_assoc, hx, ← mul_assoc, ← map_mul, ← map_mul, mul_comm y x]

omit [NumberField M] in
theorem comm_law (γ : G.C) (pb : PowerBasis G.F M) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = γ) (y : G.C)
    (hy : y * γ = γ * y) (m : M) : y * j m = j m * y := by
  refine gen_ind pb (fun m => y * j m = j m * y) ?_ ?_ ?_ ?_ m
  · show y * j pb.gen = j pb.gen * y
    rw [hj, hy]
  · intro x
    show y * j (algebraMap G.F M x) = j (algebraMap G.F M x) * y
    rw [j.commutes, Algebra.commutes]
  · intro a b ha hb
    show y * j (a + b) = j (a + b) * y
    rw [map_add (f := _), mul_add, add_mul, ha, hb]
  · intro a b ha hb
    show y * j (a * b) = j (a * b) * y
    rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]

theorem triv_mul_inv (R : Type) [CommRing R] [Algebra ℚ R] (β β' : G.C) (x U : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ)
    (hU : (U : R ⊗[ℚ] G.C) * inC G R β * (starT G.star R U).unop = inC G R β') (hx : Triv G R β x t) :
    Triv G R β' (x * U⁻¹) t := by
  unfold Triv at hx ⊢
  have h1 : (starT G.star R U).unop * (starT G.star R ((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  rw [← hx, ← hU, Units.val_mul, map_mul, MulOpposite.unop_mul]
  calc _ = (x : R ⊗[ℚ] G.C) * (((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * U) * inC G R β *
        ((starT G.star R U).unop * (starT G.star R ((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop) *
        (starT G.star R x).unop := by simp only [mul_assoc]
    _ = _ := by rw [h1, Units.inv_mul, mul_one, mul_one]


omit [NumberField M] in
theorem exists_basis (ha : G.a = 1) (P : Pair G) (μ : ℂ) (hm : P.Mark μ) (pb : PowerBasis G.F M)
    (hpol : P.pol = minpoly G.F pb.gen) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = P.γ) (w : InfinitePlace G.F) :
    ∃ (Z : GL (Fin G.n) ℂ) (d : Fin G.n → ℝ) (e : Fin G.n → (M →+* ℂ)),
      (∀ i x, e i (algebraMap G.F M x) = w.embedding x) ∧ Function.Injective (fun i => e i pb.gen) ∧
      (∀ z : ℂ, P.pol.eval₂ w.embedding z = 0 → ∃ i, e i pb.gen = z) ∧
      (∀ y, G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) ∧ (∀ i, d i ≠ 0) ∧
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * (G.gram w * G.psi w ((P.β⁻¹ : G.Cˣ) : G.C)) *
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  obtain ⟨Z, lam, hinj, hroot, hZ⟩ := GlobalTheory.T.exists_eigenbasis_psi_infinitePlace_distinct_roots p G P w
  have hr : ∀ i, P.pol.eval₂ w.embedding (lam i) = 0 := fun i => (hroot _).2 ⟨i, rfl⟩
  choose e he he' using fun i => exists_emb pb w.embedding (lam i) (hpol ▸ hr i)
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P w
  obtain ⟨d, hd, hD⟩ := GlobalTheory.T.exists_diagonal_congr_of_similitude_distinct_eigenvalues _ (G.psi w P.γ) ((P.c : ℚ) : ℝ) Z lam h1 h2
    (by exact_mod_cast P.c.ne_zero) (by rw [h3]; simp) hinj
    (fun i => GlobalTheory.T.marked_similitude_pair_minpoly_roots_normSq_eq p G P μ ha hm _ _ (hr i)) hZ
  have hl : (fun i => e i pb.gen) = lam := funext he'
  refine ⟨Z, d, e, he, hl ▸ hinj, fun z hz => ?_, fun y => ?_, hd, hD⟩
  · obtain ⟨i, hi⟩ := (hroot z).1 hz
    exact ⟨i, (he' i).trans hi⟩
  · refine gen_ind pb (fun y => G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) ?_ ?_ ?_ ?_ y
    · show G.psi w (j pb.gen) * _ = _
      rw [hj, hl, hZ]
    · intro x
      show G.psi w (j (algebraMap G.F M x)) * _ = _
      simp only [he]
      rw [j.commutes, G.psi_F]
      exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
    · intro a b h h'
      show G.psi w (j (a + b)) * _ = _
      simp only [map_add (f := _)]
      rw [Matrix.add_mul, h, h', ← Matrix.mul_add, Matrix.diagonal_add]
    · intro a b h h'
      show G.psi w (j (a * b)) * _ = _
      simp only [map_mul]
      rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]

end GlobalTheory.LKMid.MoveMark

namespace GlobalTheory.LKMid

end GlobalTheory.LKMid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylFormulaCompactTorusIdentityOfIngredients
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeSplitsCompactNoncompact
section

open Finset

namespace GlobalTheory.PsCo.PcEF.VandermondeCompactNoncompactSplit

variable {n : ℕ}

theorem lhs_eq (t : Fin n → ℂ) :
    (∏ a, ∏ b ∈ Finset.Ioi a, (t a - t b)) =
      ∏ x : Fin n × Fin n, if x.1 < x.2 then t x.1 - t x.2 else 1 := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext b
  simp

theorem wden_eq (ε : Fin n → Bool) (t : Fin n → ℂ) :
    ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε t =
      ∏ x : Fin n × Fin n, if x.1 < x.2 ∧ ε x.1 = ε x.2 then t x.1 - t x.2 else 1 := by
  rw [Fintype.prod_prod_type]
  rfl

theorem mode_eq (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (t x.1.1 - t x.1.2)) =
      ∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false then t x.1 - t x.2 else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype _ (fun x => by simp) (fun x : Fin n × Fin n => t x.1 - t x.2)).symm

theorem sign_eq (ε : Fin n → Bool) :
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then (-1 : ℂ) else 1) =
      (-1) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε := by
  rw [← Finset.prod_filter, Finset.prod_const]
  rfl

theorem swap_eq (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then t x.2 - t x.1 else 1) =
      ∏ x : Fin n × Fin n, if ε x.2 = true ∧ ε x.1 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1 :=
  Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)

theorem mode_split (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false then t x.1 - t x.2 else 1) =
      (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) *
        ((∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then (-1 : ℂ) else 1) *
          ∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 then t x.2 - t x.1 else 1) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  obtain ⟨a, b⟩ := x
  rcases lt_trichotomy a b with h | rfl | h
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [h, lt_asymm h]
  · cases h1 : ε a <;> simp
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [h, lt_asymm h]

theorem lhs_split (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ x : Fin n × Fin n, if x.1 < x.2 then t x.1 - t x.2 else 1) =
      (∏ x : Fin n × Fin n, if x.1 < x.2 ∧ ε x.1 = ε x.2 then t x.1 - t x.2 else 1) *
        ((∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) *
          ∏ x : Fin n × Fin n, if ε x.2 = true ∧ ε x.1 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  obtain ⟨a, b⟩ := x
  rcases lt_trichotomy a b with h | rfl | h
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [h]
  · simp
  · cases h1 : ε a <;> cases h2 : ε b <;> simp [lt_asymm h]

end GlobalTheory.PsCo.PcEF.VandermondeCompactNoncompactSplit

namespace GlobalTheory.PsCo.PcEF


open VandermondeCompactNoncompactSplit in
theorem vandermonde_splits_compactNoncompact (n : ℕ) (ε : Fin n → Bool) (t : Fin n → ℂ) :
    (∏ a, ∏ b ∈ Finset.Ioi a, (t a - t b)) =
      ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε t *
        ((-1) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε *
          ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (t x.1.1 - t x.1.2)) := by
  rw [lhs_eq, wden_eq, mode_eq, mode_split, sign_eq, swap_eq, lhs_split]
  have hs : ((-1 : ℂ) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε) * (-1) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε = 1 := by
    rw [← mul_pow]; norm_num
  generalize (-1 : ℂ) ^ ReciprocityTheory.ChartRestriction.DS.TRGap.sDeg ε = s at hs ⊢
  linear_combination (-((∏ x : Fin n × Fin n, if x.1 < x.2 ∧ ε x.1 = ε x.2 then t x.1 - t x.2 else 1) *
    (∏ x : Fin n × Fin n, if ε x.1 = true ∧ ε x.2 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1) *
    ∏ x : Fin n × Fin n, if ε x.2 = true ∧ ε x.1 = false ∧ x.1 < x.2 then t x.1 - t x.2 else 1)) * hs

end GlobalTheory.PsCo.PcEF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumShiftHolds
namespace GlobalTheory.PsCo.PcEG

theorem numShift_holds (n : ℕ) (ε : Fin n → Bool) (m : Fin n → ℤ) (c : Bool → ℤ)
    (t : Fin n → ℂ) (ht : ∀ a, t a ≠ 0) :
    ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (fun a => m a - c (ε a)) t =
      (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε),
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, t a ^ m (w.symm a)) * ∏ a, t a ^ (-c (ε a)) := by
  delta ReciprocityTheory.ChartRestriction.TR.Weyl.numK
  have hfilt : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, ε (σ i) = ε i)) =
      Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε) := by
    ext w; simp [funext_iff]
  rw [hfilt, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' : ∀ i, ε (w i) = ε i := fun i => congrFun (Finset.mem_filter.1 hw).2 i
  rw [mul_assoc]
  congr 1
  have h1 : ∏ i, t (w i) ^ (m i - c (ε i)) =
      (∏ i, t (w i) ^ m i) * ∏ i, t (w i) ^ (-c (ε (w i))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hw', sub_eq_add_neg, zpow_add₀ (ht _)]
  rw [h1]
  congr 1
  · have := Equiv.prod_comp w (fun a => t a ^ m (w.symm a))
    simpa using this
  · exact Equiv.prod_comp w (fun a => t a ^ (-c (ε a)))

end GlobalTheory.PsCo.PcEG
end

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.HCChar (dsChar)

namespace GlobalTheory.PsCo.PcEF

namespace WeylCompactTorusIdentity

theorem alg {W S C M s p x : ℂ} (hs : s * s = 1) (hp : p * p = 1) (hW : W ≠ 0) (hM : M ≠ 0) (hs0 : s ≠ 0)
    (hx : W * x = S * C) : s * x = p * S / (W * (s * M)) * (p * M * C) := by
  have hden : W * (s * M) ≠ 0 := mul_ne_zero hW (mul_ne_zero hs0 hM)
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (M * s * s) * hx + (M * S * C) * hs - (M * S * C) * hp

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

end WeylCompactTorusIdentity


open WeylCompactTorusIdentity in
theorem weylFormulaCompactTorusIdentity_of_ingredients : VdmSplit → PhysTor → NumShift → TorusId := by
  intro hV hP hN n ε lam Λ m hm hΛ θ hinj x hx
  have ht0 : ∀ a, tor θ a ≠ 0 := fun a => Complex.exp_ne_zero _
  obtain ⟨hPD, -⟩ := hP n ε θ
  have hVd := hV n ε (tor θ)
  have hx' : ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x =
      (∑ w ∈ GlobalTheory.HCChar.compactWeyl ε,
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, tor θ a ^ m (w.symm a)) *
        ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) := by
    rw [hx]
    exact (congrArg (fun μ => ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε μ (tor θ)) (funext hΛ)).trans
      (hN n ε m (fun b : Bool => if b then (0 : ℤ) else (pOf ε : ℤ)) (tor θ) ht0)
  have hV0 : (∏ a, ∏ b ∈ Finset.Ioi a, (tor θ a - tor θ b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
    exact sub_ne_zero.mpr (fun h => (Finset.mem_Ioi.mp hb).ne (hinj h))
  rw [hVd] at hV0
  rw [GlobalTheory.HCChar.dsChar_eq ε hm θ, hPD, hVd]
  exact alg (neg_one_pow_mul_self _) (neg_one_pow_mul_self _)
    (left_ne_zero_of_mul hV0) (right_ne_zero_of_mul (right_ne_zero_of_mul hV0))
    (pow_ne_zero _ (by norm_num)) hx'

end GlobalTheory.PsCo.PcEF

end
end

namespace GlobalTheory.PsCo.PcEF
open GlobalTheory.PsCo.PcEG

theorem torusId_full : TorusId := weylFormulaCompactTorusIdentity_of_ingredients vandermonde_splits_compactNoncompact adjointDet_onCompactTorus numShift_holds

end GlobalTheory.PsCo.PcEF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapMemMaximalIdealIff
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.LocalTangent

open IsLocalRing

variable {k S : Type} [Field k] [CommRing S] [IsLocalRing S] [Algebra k S]

theorem algebraMap_mem_maximalIdeal_iff (c : k) :
    algebraMap k S c ∈ maximalIdeal S ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
    exact h ((isUnit_iff_ne_zero.mpr hc).map (algebraMap k S))
  · rintro rfl
    simp

theorem residue_eq {π : S → k} (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (s : S) (c : k) (h : s - algebraMap k S c ∈ maximalIdeal S) : π s = c := by
  have hm : algebraMap k S (π s - c) ∈ maximalIdeal S := by
    have := sub_mem h (hπ s)
    rw [map_sub]; convert this using 1; ring
  rw [algebraMap_mem_maximalIdeal_iff] at hm
  exact sub_eq_zero.mp hm

def tangentHom (π : S → k) (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (f : S →ₗ[k] k) (hf1 : f 1 = 0) (hf2 : ∀ y ∈ maximalIdeal S ^ 2, f y = 0) :
    S →ₐ[k] DualNumber k where
  toFun s := TrivSqZeroExt.inl (π s) + TrivSqZeroExt.inr (f s)
  map_one' := by
    have : π 1 = 1 := residue_eq hπ 1 1 (by simp)
    ext <;> simp [this, hf1]
  map_mul' s t := by
    have hm : π (s * t) = π s * π t := residue_eq hπ _ _ (by
      rw [map_mul]
      convert add_mem (Ideal.mul_mem_right t _ (hπ s)) (Ideal.mul_mem_left _ (algebraMap k S (π s)) (hπ t))
        using 1
      ring)
    have hfa : ∀ c, f (algebraMap k S c) = 0 := by
      intro c; rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_zero]
    have e : s * t = algebraMap k S (π s * π t) + π s • (t - algebraMap k S (π t)) +
        π t • (s - algebraMap k S (π s)) +
        (s - algebraMap k S (π s)) * (t - algebraMap k S (π t)) := by
      simp only [Algebra.smul_def, map_mul]; ring
    have hf : f (s * t) = π s * f t + π t * f s := by
      have huv := hf2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hπ s) (hπ t))
      rw [e, map_add (f := _), map_add (f := _), map_add (f := _), map_smul, map_smul, huv, map_sub, map_sub, hfa, hfa, hfa]
      simp
    ext <;> simp [hm, hf] <;> ring
  map_zero' := by
    have : π 0 = 0 := residue_eq hπ 0 0 (by simp)
    ext <;> simp [this]
  map_add' s t := by
    have : π (s + t) = π s + π t := residue_eq hπ _ _ (by
      rw [map_add (f := _)]; convert add_mem (hπ s) (hπ t) using 1; ring)
    ext <;> simp [this]
  commutes' c := by
    have : π (algebraMap k S c) = c := residue_eq hπ _ _ (by simp)
    have h0 : f (algebraMap k S c) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_zero]
    ext <;> simp [this, h0, TrivSqZeroExt.algebraMap_eq_inl]

theorem tangentHom_snd (π : S → k) (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (f : S →ₗ[k] k) (hf1 : f 1 = 0) (hf2 : ∀ y ∈ maximalIdeal S ^ 2, f y = 0) (s : S) :
    (tangentHom π hπ f hf1 hf2 s).snd = f s := by
  simp [tangentHom]

theorem epsScaleR_snd (c : k) (x : DualNumber k) : (epsScaleR c x).snd = c * x.snd := by
  simp [epsScaleR]

end GlobalTheory.LocalTangent

namespace GlobalTheory.LocalTangent

open IsLocalRing

variable {k S : Type} [Field k] [CommRing S] [IsLocalRing S] [Algebra k S]

theorem exists_form {a b : S} (ha : a ∈ maximalIdeal S) (hb : b ∈ maximalIdeal S)
    (h : ∀ c : k, a - c • b ∉ maximalIdeal S ^ 2) :
    ∃ f : S →ₗ[k] k, f 1 = 0 ∧ (∀ y ∈ maximalIdeal S ^ 2, f y = 0) ∧ f b = 0 ∧ f a = 1 := by
  let P : Submodule k S := Submodule.span k {1, b} ⊔ (maximalIdeal S ^ 2).restrictScalars k
  have haP : a ∉ P := by
    intro hP
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hP
    obtain ⟨l, r, rfl⟩ := Submodule.mem_span_pair.mp hy
    have hz2 : z ∈ maximalIdeal S ^ 2 := hz
    have hz' : z ∈ maximalIdeal S := Ideal.pow_le_self two_ne_zero hz2
    have hl : l = 0 := by
      rw [← algebraMap_mem_maximalIdeal_iff (S := S)]
      have e : algebraMap k S l = a - r • b - z := by
        rw [← hyz, Algebra.algebraMap_eq_smul_one]; abel
      rw [e]
      exact sub_mem (sub_mem ha (Submodule.smul_of_tower_mem _ r hb)) hz'
    apply h r
    have e : a - r • b = z := by rw [← hyz, hl]; simp
    rw [e]; exact hz2
  obtain ⟨g, hga, hgP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem haP (by infer_instance)
  have hg0 : ∀ y ∈ P, g y = 0 := fun y hy => by
    have : g y ∈ P.map g := Submodule.mem_map_of_mem hy
    rw [hgP] at this; exact (Submodule.mem_bot k).mp this
  refine ⟨(g a)⁻¹ • g, ?_, ?_, ?_, ?_⟩
  · simp [hg0 1 (Submodule.mem_sup_left (Submodule.subset_span (by simp)))]
  · intro y hy
    simp [hg0 y (Submodule.mem_sup_right hy)]
  · simp [hg0 b (Submodule.mem_sup_left (Submodule.subset_span (by simp)))]
  · simp [hga]

theorem pair_dependent
    (h1 : ∀ a : S, ∃ c : k, a - algebraMap k S c ∈ maximalIdeal S)
    (h3 : ∀ ψ₁ ψ₂ : S →ₐ[k] DualNumber k, ∃ c : k,
      (ψ₁ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₂ : S →+* DualNumber k) ∨
      (ψ₂ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₁ : S →+* DualNumber k))
    {a b : S} (ha : a ∈ maximalIdeal S) (hb : b ∈ maximalIdeal S) :
    ∃ c : k, a - c • b ∈ maximalIdeal S ^ 2 ∨ b - c • a ∈ maximalIdeal S ^ 2 := by
  by_contra hne
  push_neg at hne
  choose π hπ using h1
  obtain ⟨f₁, h11, h12, h13, h14⟩ := exists_form ha hb (fun c => (hne c).1)
  obtain ⟨f₂, h21, h22, h23, h24⟩ := exists_form hb ha (fun c => (hne c).2)
  obtain ⟨c, hc | hc⟩ := h3 (tangentHom π hπ f₁ h11 h12) (tangentHom π hπ f₂ h21 h22)
  · have := congrArg (fun φ : S →+* DualNumber k => (φ a).snd) hc
    simp only [RingHom.coe_coe, RingHom.comp_apply, epsScaleR_snd, tangentHom_snd] at this
    rw [h14, h23, mul_zero] at this
    exact one_ne_zero this
  · have := congrArg (fun φ : S →+* DualNumber k => (φ b).snd) hc
    simp only [RingHom.coe_coe, RingHom.comp_apply, epsScaleR_snd, tangentHom_snd] at this
    rw [h24, h13, mul_zero] at this
    exact one_ne_zero this

theorem maximalIdeal_isPrincipal : ∀ (k : Type) [Field k] (S : Type) [CommRing S] [IsLocalRing S] [Algebra k S],
    (∀ a : S, ∃ c : k, a - algebraMap k S c ∈ IsLocalRing.maximalIdeal S) →
    IsNilpotent (IsLocalRing.maximalIdeal S) →
    (∀ ψ₁ ψ₂ : S →ₐ[k] DualNumber k, ∃ c : k,
      (ψ₁ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₂ : S →+* DualNumber k) ∨
      (ψ₂ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₁ : S →+* DualNumber k)) →
    (IsLocalRing.maximalIdeal S).IsPrincipal := by
  intro k _ S _ _ _ h1 hnil h3
  set m := maximalIdeal S with hm
  have hx : ∃ x ∈ m, m ≤ Ideal.span {x} ⊔ m ^ 2 := by
    by_cases hle : m ≤ m ^ 2
    · exact ⟨0, zero_mem _, le_sup_of_le_right hle⟩
    · obtain ⟨x, hxm, hx2⟩ := Set.not_subset.mp hle
      refine ⟨x, hxm, fun a ha => ?_⟩
      have key : ∃ c : k, a - c • x ∈ m ^ 2 := by
        obtain ⟨c, hc | hc⟩ := pair_dependent h1 h3 ha hxm
        · exact ⟨c, hc⟩
        · have hc0 : c ≠ 0 := by
            rintro rfl; apply hx2; simpa using hc
          refine ⟨c⁻¹, ?_⟩
          have e : a - c⁻¹ • x = (-c⁻¹) • (x - c • a) := by
            rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hc0, neg_smul, neg_smul, one_smul]; abel
          rw [e]; exact Submodule.smul_of_tower_mem _ _ hc
      obtain ⟨c, hc⟩ := key
      have e : a = c • x + (a - c • x) := by abel
      rw [e]
      refine Submodule.add_mem_sup ?_ hc
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)
  obtain ⟨x, hxm, hle⟩ := hx
  set I := Ideal.span {x}
  have hstep : ∀ n : ℕ, m ≤ I ⊔ m ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc m ≤ I ⊔ m ^ 2 := hle
        _ = I ⊔ m * m := by rw [pow_two]
        _ ≤ I ⊔ m * (I ⊔ m ^ (n + 1)) := sup_le_sup_left (Ideal.mul_mono_right ih) _
        _ = I ⊔ (m * I ⊔ m ^ (n + 1 + 1)) := by rw [Ideal.mul_sup, ← pow_succ']
        _ ≤ I ⊔ m ^ (n + 1 + 1) := sup_le (le_sup_left) (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
  obtain ⟨n, hn⟩ := hnil
  have hmI : m ≤ I := by
    have := hstep n
    rwa [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, sup_bot_eq] at this
  have hIm : I ≤ m := (Ideal.span_singleton_le_iff_mem _).mpr hxm
  exact ⟨⟨x, le_antisymm hmI hIm⟩⟩

end GlobalTheory.LocalTangent
end
end
