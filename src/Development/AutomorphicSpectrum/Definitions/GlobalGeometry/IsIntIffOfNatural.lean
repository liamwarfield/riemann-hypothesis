module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformized

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFiniteExtAllModelsUniformised
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.IntegralPull

theorem exists_finite_ext_all_models_uniformised {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr)
    (y : IntFr Xo c T io) (e : ℕ) (la : HeightOneSpectrum (𝓞 c.F)) (ho : OverLa la T.V io e) (hy : y.IsAlg) :
    ∃ (T' : CDVR) (φ : T.V →+* T'.V) (φF : T.Fr →+* T'.Fr) (e₁ : ℕ) (z' : IntFr Xo c T' (φF.comp io)),
      Function.Injective φ ∧ IsLocalHom φ ∧ φ.Finite ∧
      φF.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp φ ∧
      0 < e₁ ∧ OverLa la T'.V (φF.comp io) (e * e₁) ∧ z'.IsAlg ∧
      (letI := io.toAlgebra; letI := (φF.comp io).toAlgebra
        FrMap ({ φF with commutes' := fun _ => rfl } : T.Fr →ₐ[c.F] T'.Fr) y.1 z'.1) ∧
      ∀ I : IntData Xo c T' (φF.comp io) z'.1, ∃ P : PELUnif (maximalIdeal T'.V) I.G, P.TorsionIso := by
  have : Finite (ResidueField T.V) := hy
  obtain ⟨G, t, m1, m2, -⟩ := y.2.2
  obtain ⟨W, _, _, _, hc, _, hf, hi, hr, hS⟩ := GlobalTheory.UnifAfterExt.exists_split_baseChange T.V G.G G.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  let T' : Formalism.L2.Pj.CDVR := { V := W }
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  obtain ⟨φ, hφ⟩ : ∃ φ : T.Fr →+* T'.Fr, ∀ v, φ (algebraMap T.V T.Fr v) = algebraMap T'.V T'.Fr (algebraMap T.V W v) :=
    ⟨IsFractionRing.lift hj, IsFractionRing.lift_algebraMap hj⟩
  obtain ⟨r, hr0, hv⟩ := exists_index (V' := T'.V) (algebraMap T.V W) φ hφ
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c _ _ ψ y.1
  obtain ⟨p, χ, y₀, hy₀⟩ := y.2.1
  let y' : IntFr Xo c T' (φ.comp io) :=
    ⟨z, ⟨p, ψ.comp χ, y₀, Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ χ ψ y₀ y.1 z hy₀ hz⟩,
      integral_baseChange T T' io (φ.comp io) _ hi ψ hφ y.1 z hz y.2.2⟩
  refine ⟨T', algebraMap T.V W, φ, r, y', hi, hl, RingHom.finite_algebraMap.2 hf, RingHom.ext hφ, hr0, ?_, hr, hz,
    fun I => exists_unif_of_split T T' _ φ hφ m1 m2 hz.1 I.m1 I.m2 hS⟩
  rw [Nat.mul_comm]
  exact ho.bc φ hr0 hv

end GlobalTheory.IntegralPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TypingsAgree
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionFactsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Operators

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

end Operators

section Data

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]


open QForm in
theorem bOf_balance {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] (ιD : D.toPre.OAct O) (hQ : IsQ D.toPre ϖ Q) (a : O) (χ χ' : D.toPre.X) :
    bOf D.toPre Q (a • χ) χ' = bOf D.toPre Q χ (star a • χ') := by
  have hL := D.toPre.P.isLB
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  obtain ⟨u, hu, hnorm⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb D.toPre.P.isLB _ _ (ιD.onB.rosati a)
  have hc := ιD.tau_bal a u hu hnorm χ χ'
  obtain ⟨_, _, hsA, hA⟩ := tau_val hϖ D hQ (a • χ) χ'
  obtain ⟨_, _, hsB, hB⟩ := tau_val hϖ D hQ χ (star a • χ')
  have hu0 := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ u hu (lift (D.toPre.c χ) (D.toPre.c χ')).left
    (D.toPre.pt2 χ χ') (by simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hA hu0
  have := genHasVal_unique hϖ D.toPre.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _
      (sumElim_sec hsA (fun k => by
        obtain ⟨q, hq⟩ := rosatiφ_over D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k
        show (_ ≫ rosatiφ D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k) ≫ _ = _
        rw [hq]; exact over_sec _ _)) hsB _ _
      (genHasVal_isGen D.toPre.P.L _ _ _ _ _ hB) hc h1) hB
  linarith

end Data

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
  (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [Algebra (FractionRing V) F]

end Unif

end GlobalTheory.TorsionFactsCompare
end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ref

open NumberField IsDedekindDomain IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def periodForm {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
    (P : PELUnif (maximalIdeal V) t) {ϖ : V} (hϖ : Irreducible ϖ) {Q : P.D.toPre.X → ℤ}
    (hQ : QForm.IsQ P.D.toPre ϖ Q) : SymB (cjE E) P.D.toPre.X :=
  ⟨LinearMap.mk₂ ℤ (fun a b => (QForm.bHom hϖ P.D hQ a b : ℝ)) (by simp) (by simp) (by simp) (by simp),
    fun a b => by
      simp only [LinearMap.mk₂_apply, QForm.bHom_apply, QForm.bOf_comm P.D a b],
    fun x x' hx a b => by
      have hx' : x' = H.bar x := RingOfIntegers.ext (hx.trans (cjE_coe H x))
      subst hx'
      letI := H.starRing
      simp only [LinearMap.mk₂_apply, QForm.bHom_apply]
      exact congrArg _ (GlobalTheory.TorsionFactsCompare.bOf_balance P.D hϖ P.oD hQ x a b)⟩

theorem exists_isPhiAt {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1)
    (P : PELUnif (maximalIdeal T.V) I.G) (hP : P.TorsionIso) : ∃ t, IsPhiAt Xo c la T io y t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have h2 : ∀ a, (periodForm P hϖ hQ : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ) := fun a => by
    show ((QForm.bOf P.D.toPre Q a a : ℤ) : ℝ) = _
    rw [← QForm.two_Q_eq hϖ P.D hQ]; push_cast; rfl
  refine ⟨phiC (cjE E) (periodForm P hϖ hQ) / e, e, ho, I, P, ϖ, Q, periodForm P hϖ hQ, hP, hϖ, hQ,
    fun _ _ => rfl, h2, fun a => ?_, by field_simp⟩
  rw [h2]
  by_cases ha : a = 0
  · rw [ha, QForm.Q_zero hϖ P.D hQ]; simp
  · have : (1 : ℝ) ≤ Q a := by exact_mod_cast QForm.Q_pos hϖ P.D hQ ha
    linarith

theorem nonempty_intData {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) : Nonempty (IntData Xo c T io y.1) := by
  obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, k1, k2, k3, k4⟩ := y.2.2
  exact ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, k1, k2, k3, k4⟩⟩


variable (Xo c) in
theorem unifAll_holds : UnifAll Xo c := by
  intro la T io e ho y hy
  obtain ⟨T', φV, φ, -, z, hi, hl, hf, hc, -, -, hz, hm, hU⟩ :=
    GlobalTheory.IntegralPull.exists_finite_ext_all_models_uniformised Xo c T io y e la ho hy
  obtain ⟨r, hr, hv⟩ := GlobalTheory.IntegralPull.exists_index (V' := T'.V) φV φ (RingHom.congr_fun hc)
  obtain ⟨I⟩ := nonempty_intData z
  obtain ⟨P, hP⟩ := hU I
  obtain ⟨t, ht⟩ := exists_isPhiAt (ho.bc φ hr hv) z I P hP
  exact ⟨T', φV, φ, r, z, t, ⟨hi, hl, hf, hc, hr, hv⟩, hm, hz, ht⟩

end GlobalTheory.CompanionTheory.Ar.Ref
