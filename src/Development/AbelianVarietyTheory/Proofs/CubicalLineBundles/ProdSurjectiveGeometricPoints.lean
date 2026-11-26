module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GeomSurj


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.GeomSurj.exists_lift_of_surjective {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ A) :
    ∃ p : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ P, x = p ≫ ψ := by
  have hΩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω = Spec (CommRingCat.of Ω) := rfl
  haveI : JacobsonSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance
  haveI : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance
  haveI : JacobsonSpace (pullback ψ x :) := LocallyOfFiniteType.jacobsonSpace (pullback.snd ψ x)
  obtain ⟨q₀, -⟩ := (pullback.snd ψ x).surjective (Classical.arbitrary _)
  obtain ⟨q, hq⟩ : (closedPoints (pullback ψ x :)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hc := closure_closedPoints (X := (pullback ψ x :))
    rw [h, closure_empty] at hc
    exact (hc ▸ Set.mem_univ q₀ : q₀ ∈ (∅ : Set _))
  haveI : LocallyOfFiniteType ((pullback ψ x).fromSpecResidueField q) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hq
  let g : Spec ((pullback ψ x).residueField q) ⟶ Spec (CommRingCat.of Ω) :=
    (pullback ψ x).fromSpecResidueField q ≫ pullback.snd ψ x
  have hg : LocallyOfFiniteType (Spec.map (Spec.preimage g)) := by
    rw [Spec.map_preimage]; dsimp only [g]; infer_instance
  have hft := HasRingHomProperty.Spec_iff.mp hg
  set f := Spec.preimage g with hf
  letI : Algebra Ω ((pullback ψ x).residueField q) := f.hom.toAlgebra
  haveI : Algebra.FiniteType Ω ((pullback ψ x).residueField q) := hft
  haveI : Module.Finite Ω ((pullback ψ x).residueField q) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  let φ : (pullback ψ x).residueField q →ₐ[Ω] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have key : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g = 𝟙 _ := by
    rw [← Spec.map_preimage g, ← hf, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of Ω)
    ext a
    exact φ.commutes a
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullback ψ x).fromSpecResidueField q ≫
    pullback.fst ψ x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition,
    ← Category.assoc (Scheme.fromSpecResidueField _ _), ← Category.assoc]
  change x = (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g) ≫ x
  rw [key, Category.id_comp]

end GlobalTheory.GeomSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PureTypeVectorSpansQuadraticLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureTypeVector

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.PureTypeVector.hermForm_smul_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : ℂ) (u v : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z • u) (w • v) = z * starRingEnd ℂ w * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm u v := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.PureTypeVector.hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (v : Fin g → ℂ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm v v).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  have key : ∀ u : Fin g → ℂ, star (star u ⬝ᵥ Hm.mulVec u) = star u ⬝ᵥ Hm.mulVec u := by
    intro u
    rw [← Matrix.star_dotProduct (Hm.mulVec u) u, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]
  have := key (star v)
  rw [star_star] at this
  exact this

end PureTypeVector


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.pureType_vector_spans_quadratic_lattice :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty Pe → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) →
  (∀ x y, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe x) (Pe y)).im = D.EF x y) →
  ∀ (ρ : ℂ) (a : D.La), ρ ^ 2 = -(H.d : ℂ) → (∀ i, ty i (H.rt : E) ≠ ρ → Pe a i = 0) →
  (∀ m n : ℤ, ((m : ℂ) + n * ((1 + Complex.I * Real.sqrt H.d) / 2)) • Pe a ∈ Pe.range) ∧
  ∀ z w : ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z • Pe a) (w • Pe a) = ((D.EF (H.w0 • a) a).natAbs : ℂ) * (2 * z * starRingEnd ℂ w / Real.sqrt H.d) := by
  intro E _ _ _ H D g ty Pe Hm hP hH hpos hE ρ a hρ hsupp
  have hw0 : ∀ i, Pe (H.w0 • a) i = (1 + ρ) / 2 * Pe a i := by
    intro i
    rw [hP.1 H.w0 a i]
    by_cases hi : ty i (H.rt : E) = ρ
    · have h2 : (2 : ℂ) * ty i (H.w0 : E) = 1 + ty i (H.rt : E) := by
        have := congrArg (fun x : 𝓞 E => ty i (x : E)) H.two_weight_eq_one_add_root
        simp only [map_mul, map_add (f := _), map_one, RingOfIntegers.coe_eq_algebraMap, map_ofNat] at this
        linear_combination this
      rw [hi] at h2
      have h3 : ty i (H.w0 : E) = (1 + ρ) / 2 := by linear_combination h2 / 2
      rw [h3]
    · rw [hsupp i hi]
      simp
  have hw0' : Pe (H.w0 • a) = ((1 + ρ) / 2) • Pe a := funext fun i => by simp [hw0 i]
  have hsqd : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = H.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hsq : ρ = Complex.I * Real.sqrt H.d ∨ ρ = -(Complex.I * Real.sqrt H.d) := by
    have hprod : (ρ - Complex.I * Real.sqrt H.d) * (ρ + Complex.I * Real.sqrt H.d) = 0 := by
      linear_combination hρ + hsqd - ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 * Complex.I_sq
    rcases mul_eq_zero.1 hprod with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  constructor
  · intro m n
    rcases hsq with h | h
    · refine ⟨m • a + n • (H.w0 • a), ?_⟩
      rw [map_add (f := _), map_zsmul, map_zsmul]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply]
      simp only [smul_eq_mul, zsmul_eq_mul, hw0 i, h]
      ring
    · refine ⟨(m + n) • a - n • (H.w0 • a), ?_⟩
      rw [map_sub, map_zsmul, map_zsmul]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply]
      simp only [smul_eq_mul, zsmul_eq_mul, hw0 i, h]
      push_cast
      ring
  · intro z w
    rw [_root_.GlobalTheory.PureTypeVector.hermForm_smul_smul]
    have him : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).im = 0 := _root_.GlobalTheory.PureTypeVector.hermForm_self_im hH _
    have hre : 0 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re := by
      by_cases h0 : Pe a = 0
      · simp [h0, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm]
      · exact (hpos _ h0).le
    have hc : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (((1 + ρ) / 2) • Pe a) (Pe a) = (1 + ρ) / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a) := by
      simpa using _root_.GlobalTheory.PureTypeVector.hermForm_smul_smul Hm ((1 + ρ) / 2) 1 (Pe a) (Pe a)
    have hEF := hE (H.w0 • a) a
    rw [hw0', hc] at hEF
    have hh : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a) = ((_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re : ℂ) :=
      Complex.ext rfl (by simp [him])
    have hs : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (Nat.cast_pos.2 H.d_prime.pos)
    have habs : |((D.EF (H.w0 • a) a : ℤ) : ℝ)| = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 := by
      rw [hh] at hEF
      have hnn : 0 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 :=
        div_nonneg (mul_nonneg hre hs.le) zero_le_two
      rcases hsq with h | h
      · rw [h] at hEF
        simp [Complex.mul_im, Complex.div_re, Complex.div_im] at hEF
        have he : ((D.EF (H.w0 • a) a : ℤ) : ℝ) = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 := by
          linarith
        rw [he, abs_of_nonneg hnn]
      · rw [h] at hEF
        simp [Complex.mul_im, Complex.div_re, Complex.div_im] at hEF
        have he : ((D.EF (H.w0 • a) a : ℤ) : ℝ) = -((_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2) := by
          linarith
        rw [he, abs_neg, abs_of_nonneg hnn]
    have hcast : (((D.EF (H.w0 • a) a).natAbs : ℕ) : ℂ) = ((|((D.EF (H.w0 • a) a : ℤ) : ℝ)| : ℝ) : ℂ) := by
      rw [Nat.cast_natAbs, ← Int.cast_abs, Complex.ofReal_intCast]
    have hs' : ((Real.sqrt H.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
    rw [hcast, habs]
    conv_lhs => rw [hh]
    push_cast
    field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TraceFormIntegralPerfectOfIsUnf
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem traceForm_integral_perfect_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ k, (∀ x ∈ (U.X k).Λ, ∀ y ∈ (U.X k).Λ, ∃ n : ℤ, EFf (U.X k).ξ0 (U.X k).Gm x y = n) ∧ ∀ φ : (U.X k).Λ →+ ℤ, ∃ x ∈ (U.X k).Λ, ∀ y : (U.X k).Λ, (φ y : ℚ) = EFf (U.X k).ξ0 (U.X k).Gm x y := by
  intro E _ _ _ H Dw l Xo c σ r U hU k
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hφ, -⟩ := hU
  refine ⟨fun x hx y hy => ?_, fun ψ => ?_⟩
  · refine ⟨(F.Di (ik k)).EF ((φ k).symm ⟨x, hx⟩) ((φ k).symm ⟨y, hy⟩), ?_⟩
    rw [hφ k]
    simp only [LinearEquiv.apply_symm_apply, EFf]
  · obtain ⟨a, ha⟩ := (F.Di (ik k)).unimod.2
      (ψ.comp (φ k).toLinearMap.toAddMonoidHom).toIntLinearMap
    refine ⟨φ k a, (φ k a).2, fun y => ?_⟩
    have h := hφ k a ((φ k).symm y)
    rw [ha] at h
    simpa [EFf] using h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOrEqNegOfPurelyImaginaryOfNormEq
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem eq_or_eq_neg_of_purelyImaginary_of_norm_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ ξ' : E) (τ : E →+* ℂ),
      cc ξ = -ξ → cc ξ' = -ξ' → ‖τ ξ‖ = ‖τ ξ'‖ → ξ' = ξ ∨ ξ' = -ξ := by
  intro E _ _ _ ξ ξ' τ h h' hn
  have key : ∀ x : E, cc x = -x → τ (x ^ 2) = -((‖τ x‖ ^ 2 : ℝ) : ℂ) := by
    intro x hx
    have h1 : τ (cc x) = (starRingEnd ℂ) (τ x) := IsCMField.complexEmbedding_complexConj E τ x
    rw [hx, map_neg] at h1
    have h2 := Complex.mul_conj' (τ x)
    rw [← h1] at h2
    rw [map_pow]
    push_cast
    linear_combination -h2
  have h3 : τ (ξ' ^ 2) = τ (ξ ^ 2) := by rw [key ξ h, key ξ' h', hn]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (τ.injective h3)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosNatMemFractionalIdeal
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem exists_pos_nat_mem_fractionalIdeal {E : Type} [Field E] [NumberField E]
    {a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (ha : a ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (n : E) ∈ a := by
  obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger ha
  have hI : (Ideal.span {x} : Ideal (𝓞 E)) ≠ ⊥ := by simpa using hx0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x}))
  refine ⟨Ideal.absNorm (Ideal.span {x}),
    Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩
  have h := (a : Submodule (𝓞 E) E).smul_mem e hx
  rw [Algebra.smul_def, ← map_mul, he, map_natCast] at h
  exact h

theorem fractionalIdeal_smul_eq_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (L : Submodule (𝓞 E) (Fin r → E)) :
    (a : Submodule (𝓞 E) E) • L =
      Submodule.span (𝓞 E) {v | ∃ α ∈ a, ∃ u ∈ L, v = α • u} := by
  refine le_antisymm (Submodule.smul_le.2 fun α hα u hu => Submodule.subset_span ⟨α, hα, u, hu, rfl⟩)
    (Submodule.span_le.2 ?_)
  rintro _ ⟨α, hα, u, hu, rfl⟩
  exact Submodule.smul_mem_smul hα hu

theorem exists_dataX_of_perfect_traceForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (𝔄 𝔄b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (k : ℝ) (g : ℕ), (∀ a : E, a ∈ 𝔄b ↔ cc a ∈ 𝔄) → FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 * 𝔄 * 𝔄b * (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1 → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = k) → k ≤ 1 → (∀ x ∈ X.Λ, ∀ y ∈ X.Λ, ∃ n : ℤ, EFf X.ξ0 X.Gm x y = n) → (∀ φ : X.Λ →+ ℤ, ∃ x ∈ X.Λ, ∀ y : X.Λ, (φ y : ℚ) = EFf X.ξ0 X.Gm x y) → 0 < g → (∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ X.Γ) → ∃ Xx : DataX E r, Xx.toData = X ∧ Xx.g = g ∧ Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  intro E _ _ _ r X 𝔄 𝔄b k g hb hone habs hk hint hperf hg hcong
  have hbc : 𝔄b = conjFrac 𝔄 := by
    ext a; rw [mem_conjFrac]; exact hb a
  subst hbc
  have hA : 𝔄 ≠ 0 := by
    rintro rfl
    simp at hone
  have hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  have hd := (perfect_iff_hermDual_eq X.ξ0_ne X.Gm_det hΛ).1 ⟨hint, hperf⟩
  have hself : hermDual X.Gm (((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) • X.Λ) =
      ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ := by
    rw [hermDual_smul (inv_ne_zero hA), conjFrac_inv, inv_inv, hd, ← fractionalIdeal_mul_smul]
    congr 2
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hone]; ring
  obtain ⟨hi, hdual⟩ := hermDual_eq_self_iff.1 hself
  obtain ⟨NA, hNA, hNA'⟩ := exists_pos_nat_mem_fractionalIdeal (inv_ne_zero hA)
  obtain ⟨NC, hNC, hNC'⟩ := exists_pos_nat_mem_fractionalIdeal hA
  have hk0 : 0 < k := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← habs τ, norm_pos_iff]
    exact (map_ne_zero τ).2 X.ξ0_ne
  refine ⟨{ toData := X
            k0 := 2 * k
            minWeight_pos := by positivity
            k0_le := by linarith
            ξ0_abs := fun τ => by rw [habs]; ring
            EF_int := hint
            EF_perf := hperf
            L' := ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ
            L'_fg := (isLattice_fractionalIdeal_smul (inv_ne_zero hA) hΛ).1
            L'_int := hi
            L'_dual := hdual
            NA := NA
            NC := NC
            NA_pos := hNA
            NC_pos := hNC
            NA_sub := fun x hx => Submodule.smul_mem_smul hNA' hx
            NC_sub := fun x hx => ?_
            g := g
            g_pos := hg
            cong := hcong }, rfl, rfl, ?_⟩
  · have h := Submodule.smul_mem_smul (show (NC : E) ∈ (𝔄 : Submodule (𝓞 E) E) from hNC') hx
    rwa [fractionalIdeal_smul_inv_smul hA] at h
  · change X.Λ = _
    rw [← fractionalIdeal_smul_eq_span, fractionalIdeal_smul_inv_smul hA]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TraceMulConjIntIffMemOfMulDifferentEqOne
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

namespace GlobalTheory

open NumberField in
open scoped Matrix in
private theorem fractionalIdeal_eq_one_of_smul_submodule_eq_self {E : Type} [Field E] [NumberField E]
    {r : ℕ} {c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hc : c ≠ 0)
    {L : Submodule (𝓞 E) (Fin r → E)} (hL : L ≠ ⊥) (hfg : L.FG)
    (h : (↑c : Submodule (𝓞 E) E) • L = L) : c = 1 := by
  have key : ∀ d : FractionalIdeal (nonZeroDivisors (𝓞 E)) E,
      (↑d : Submodule (𝓞 E) E) • L = L → d ≤ 1 := by
    intro d hd a ha
    have hint : IsIntegral (𝓞 E) a :=
      isIntegral_of_smul_mem_submodule L hL hfg a fun n hn =>
        hd ▸ Submodule.smul_mem_smul ha hn
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact (FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩
  have h1 : c ≤ 1 := key c h
  have h2 : c⁻¹ ≤ 1 := key c⁻¹ (by
    conv_rhs => rw [← _root_.GlobalTheory.fractionalIdeal_inv_smul_smul hc L]
    rw [h])
  refine le_antisymm h1 ?_
  calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = c * c⁻¹ := (mul_inv_cancel₀ hc).symm
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one c


open NumberField in
open scoped Matrix in
theorem _root_.GlobalTheory.trace_xi_mul_conj_int_iff_mem :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 0 < r → 𝔄 ≠ 0 → X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u} → ∀ x : E, (∀ y ∈ 𝔄, ∃ n : ℤ, Algebra.trace ℚ E (X.ξ0 * x * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y) = n) ↔ x ∈ 𝔄 := by
  intro E _ _ _ r X 𝔄 hr h𝔄 hΛ x
  haveI : NeZero r := ⟨hr.ne'⟩
  have hξ : X.ξ0 ≠ 0 := X.ξ0_ne
  have hlat : _root_.ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  have hself : _root_.GlobalTheory.traceFormDual X.ξ0 X.Gm X.Λ = X.Λ :=
    (_root_.GlobalTheory.perfect_iff_traceFormDual_eq hξ X.Gm_det hlat).1 ⟨X.EF_int, X.EF_perf⟩
  have hL : _root_.GlobalTheory.hermDual X.Gm X.L' = X.L' :=
    _root_.GlobalTheory.hermDual_eq_self_iff.2 ⟨X.L'_int, X.L'_dual⟩
  have hΛ' : X.Λ = (↑𝔄 : Submodule (𝓞 E) E) • X.L' := by
    rw [hΛ]
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro v ⟨a, ha, u, hu, rfl⟩
      exact Submodule.smul_mem_smul ha hu
    · exact Submodule.smul_le.2 fun a ha u hu => Submodule.subset_span ⟨a, ha, u, hu, rfl⟩
  have hLne : X.L' ≠ ⊥ := by
    intro hbot
    have hspan := X.Λ_span
    rw [hΛ', hbot, Submodule.smul_bot, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
    exact bot_ne_top hspan
  set 𝔇 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
      ↑(differentIdeal ℤ (𝓞 E)) with h𝔇
  have hconj0 : _root_.GlobalTheory.conjFrac 𝔄 ≠ 0 := _root_.GlobalTheory.conjFrac_ne_zero h𝔄
  have hsp0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ
  have hd0 := _root_.GlobalTheory.coe_different_ne_zero (E := E)
  have h𝔇0 : 𝔇 ≠ 0 := mul_ne_zero hsp0 hd0
  have heq : (↑𝔄 : Submodule (𝓞 E) E) • X.L' =
      (↑(𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹) : Submodule (𝓞 E) E) • X.L' := by
    rw [← hΛ', ← hself, _root_.GlobalTheory.traceFormDual_eq hξ, hΛ',
      _root_.GlobalTheory.hermDual_smul h𝔄, hL, _root_.GlobalTheory.fractionalIdeal_mul_smul]
  have h𝔅 : 𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹ = 𝔄 := by
    have hc := fractionalIdeal_eq_one_of_smul_submodule_eq_self
      (c := 𝔄⁻¹ * (𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹))
      (mul_ne_zero (inv_ne_zero h𝔄) (mul_ne_zero (inv_ne_zero h𝔇0) (inv_ne_zero hconj0)))
      hLne X.L'_fg (by
        rw [_root_.GlobalTheory.fractionalIdeal_mul_smul, ← heq,
          _root_.GlobalTheory.fractionalIdeal_inv_smul_smul h𝔄])
    calc _ = 𝔄 * (𝔄⁻¹ * (𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹)) := by
          rw [← mul_assoc, mul_inv_cancel₀ h𝔄, one_mul]
      _ = 𝔄 := by rw [hc, mul_one]
  have hmain : 𝔄 * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
      _root_.GlobalTheory.conjFrac 𝔄) = (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
    rw [show 𝔄 * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
        _root_.GlobalTheory.conjFrac 𝔄) = (𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹) *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
        _root_.GlobalTheory.conjFrac 𝔄) by rw [h𝔅], h𝔇, mul_inv]
    calc _ = (↑(differentIdeal ℤ (𝓞 E)))⁻¹ *
          ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0)⁻¹ *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0) *
          ((_root_.GlobalTheory.conjFrac 𝔄)⁻¹ * _root_.GlobalTheory.conjFrac 𝔄) := by
          first | ring | simp only [mul_comm, mul_left_comm, mul_assoc]
      _ = _ := by rw [inv_mul_cancel₀ hsp0, inv_mul_cancel₀ hconj0, mul_one, mul_one]
  have hcc : ∀ w : E, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc w) = w := by
    intro w
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    simp
  constructor
  · intro hx
    set K := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
      _root_.GlobalTheory.conjFrac 𝔄 with hK
    have hK0 : K ≠ 0 := mul_ne_zero hsp0 hconj0
    have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x * K ≤
        (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
      rw [hK, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [_root_.GlobalTheory.mem_inv_different_iff]
      intro a ha
      have h1 : (z : E) * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
        _root_.GlobalTheory.mem_one_fractionalIdeal_iff.2 ((RingOfIntegers.isIntegral_coe z).mul ha)
      have hw : (z : E) * a * j ∈ _root_.GlobalTheory.conjFrac 𝔄 := by
        have := FractionalIdeal.mul_mem_mul h1 hj
        rwa [one_mul] at this
      obtain ⟨n, hn⟩ := hx (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((z : E) * a * j)) (_root_.GlobalTheory.mem_conjFrac.1 hw)
      refine ⟨n, ?_⟩
      rw [← hn, hcc]
      congr 1
      change (z : E) * (x * X.ξ0) * j * a = _
      ring
    have hsub : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x ≤ 𝔄 := by
      calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x
          = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x * K * K⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hK0, mul_one]
        _ ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ * K⁻¹ := by gcongr
        _ = 𝔄 := by rw [← hmain, mul_assoc, mul_inv_cancel₀ hK0, mul_one]
    exact FractionalIdeal.spanSingleton_le_iff_mem.1 hsub
  · intro hx y hy
    have hmem : X.ξ0 * x * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y ∈ (↑(differentIdeal ℤ (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ := by
      rw [← hmain]
      have := FractionalIdeal.mul_mem_mul hx (FractionalIdeal.mul_mem_mul
        (FractionalIdeal.mem_spanSingleton_self _ X.ξ0)
        (_root_.GlobalTheory.cc_mem_conjFrac.2 hy))
      convert this using 1
      ring
    obtain ⟨k, hk⟩ := (_root_.GlobalTheory.mem_inv_different_iff.1 hmem) 1 isIntegral_one
    exact ⟨k, by simpa using hk⟩

end GlobalTheory
end
