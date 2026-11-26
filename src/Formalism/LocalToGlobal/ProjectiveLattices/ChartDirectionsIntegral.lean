module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)

attribute [local instance] Over.cartesianMonoidalCategory

def IsIntPS (T : CDVR) {n d : ℕ} (f : Germ.PS T.Fr n d) : Prop :=
  ∀ m, MvPowerSeries.coeff m f ∈ (algebraMap T.V T.Fr).range

instance (T : CDVR) : Algebra ℚ T.Fr := DivisionRing.toRatAlgebra

section Jet

variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (κ : Type) (m : ℕ)

theorem mem_orig_pow_map {a : MvPolynomial κ R} (ha : a ∈ orig R κ ^ (m + 1)) :
    MvPolynomial.map f a ∈ orig R' κ ^ (m + 1) := by
  have h : MvPolynomial.map f a ∈ Ideal.map (MvPolynomial.map f : MvPolynomial κ R →+* MvPolynomial κ R')
      (orig R κ ^ (m + 1)) := Ideal.mem_map_of_mem _ ha
  rw [map_orig_pow] at h
  simpa [MvPolynomial.map_X, orig] using h

def jetCoef : Jet R κ m →+* Jet R' κ m :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (orig R' κ ^ (m + 1))).comp (MvPolynomial.map f)) fun _ ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (mem_orig_pow_map f κ m ha)

end Jet

section Flat

variable {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ)

lemma wchart_pull_le (j : K → PUnit.{1} → L.ι) :
    LB.wchart (L.pull F) φ j ≤ LB.wchart L (fun k => φ k ≫ F) (fun k => j k ⟨⟩) := by
  intro y hy
  show y ∈ (⋂ k, (φ k ≫ F).base ⁻¹' (L.U (j k ⟨⟩) : Set _))
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : (φ k).base y ∈ LB.wchart L (fun _ : PUnit.{1} => F) (j k) := Set.mem_iInter.1 hy k
  have h2 : F.base ((φ k).base y) ∈ L.U (j k ⟨⟩) := Set.mem_iInter.1 h1 ⟨⟩
  exact h2

def flatGen (c : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) : LB.Gen (LB.LinComb (L.pull F) φ ε) where
  s := fun j => res (wchart_pull_le L F φ j) (c.s (fun k => j k ⟨⟩))

end Flat

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

structure IntData (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) where
  G : SAB H (Sp T.V)
  t' : SAB H (Sp T.Fr)
  m1 : letI := io.toAlgebra; SABMap t' Xo.univ.t y.x
  m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))
  ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)
  tan : ∀ τ i, IsTan (ub τ i)
  eig : ∀ τ i, IsEigV c io G τ (ub τ i)
  basis : ∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w →
    ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w
  lift : letI := io.toAlgebra; ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = y.u τ i ∧
    u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left
  θ : LB.Sec G.PP.L
  θgen : ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
    σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i
  w1 : letI := io.toAlgebra; LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)
  w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)
  σ : LB.Sec t'.PP.L
  s1 : letI := io.toAlgebra; LB.Sec (Xo.univ.t.PP.L.pull m1.φ)
  θ2 : LB.Sec (G.PP.L.pull m2.φ)
  rig1 : letI := io.toAlgebra; RigIso m1 w1
  rig2 : RigIso m2 w2
  maps1 : letI := io.toAlgebra; IsoMaps w1 σ s1
  maps2 : IsoMaps w2 σ θ2
  pull : PullSec m2.φ θ θ2
  gen1 : letI := io.toAlgebra; ∀ g : t'.G.left ⟶ Gx y.x, g ≫ (CartesianMonoidalCategory.snd (Over.mk y.x) Xo.univ.t.G).left = m1.φ →
    g ≫ (CartesianMonoidalCategory.fst (Over.mk y.x) Xo.univ.t.G).left = t'.G.hom →
    ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit)),
      s1.f j = (g.appLE _ _ h).hom (y.s.f (fun _ => j PUnit.unit))

def IntegralIffSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr),
    Integral T io y ↔ Nonempty (IntData Xo c T io y)

end Data

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

def primφ (t : SAB H X0) : Fin 1 ⊕ ULift (Finset (Fin 2)) → (t.G.left ⟶ t.G.left) :=
  Sum.elim (fun _ : Fin 1 => 𝟙 t.G.left) (cφG t ![𝟙 t.G, t.act.act H.w0])

def primε : Fin 1 ⊕ ULift (Finset (Fin 2)) → ℤ := Sum.elim (fun _ => 1) fun I => -cε 2 I

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

abbrev chD {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (ch : letI := io.toAlgebra; ChartAt Xo c y.1) : ℕ :=
  letI := io.toAlgebra; ch.d

def IsGenFibreChart {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
    (ch : letI := io.toAlgebra; ChartAt Xo c y.1) (I : IntData Xo c T io y.1)
    (FT : Fin (chD ch) → PS T.V 2 (chD ch)) (actT : 𝓞 E → Fin (chD ch) → PS T.V 1 (chD ch)) (ph1T ph2T : PS T.V 3 (chD ch))
    (syT : PS T.V 2 (chD ch)) (adT : 𝓞 E → PS T.V 2 (chD ch)) (uvecT : Lt1 Dw → Fin (chD ch) → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) (chD ch) m 1 ⟶ I.G.G) (eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) (chD ch) xT m)
    (wPT : PrimTyG I.G) : Prop :=
  letI := io.toAlgebra
  ((∀ j, ch.B.G.F j = MvPowerSeries.map (algebraMap T.V T.Fr) (FT j)) ∧
    (∀ a j, ch.B.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (actT a j)) ∧
    ch.B.ph1 = MvPowerSeries.map (algebraMap T.V T.Fr) ph1T ∧
    ch.B.ph2 = MvPowerSeries.map (algebraMap T.V T.Fr) ph2T ∧
    ch.B.sy = MvPowerSeries.map (algebraMap T.V T.Fr) syT ∧
    (∀ a, ch.B.ad a = MvPowerSeries.map (algebraMap T.V T.Fr) (adT a)) ∧
    ∀ ℓ i, ch.uvec ℓ i = algebraMap T.V T.Fr (uvecT ℓ i)) ∧
  ∃ x' : ∀ m, jOG (𝟙 (Sp T.Fr)) ch.d m 1 ⟶ I.t'.G,
    (∀ m, (x' m).left ≫ I.m2.φ =
      spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin ch.d) m) ≫ (xT m).left) ∧
    (∀ m, (x' m).left ≫ I.m1.φ = (ch.x m).left) ∧
    (∃ e' : ∀ m, FrTyG I.t' (𝟙 (Sp T.Fr)) ch.d x' m, ∀ m, (e' m).IsGen ∧
      (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L
          (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (0 : Fin 2),
            jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (1 : Fin 2)] J ≫ I.m2.φ) (cε 2)),
        LB.Gen.Corr I.G.PP.L _ _ _ _ c₂
          (LB.pullGen I.G.PP.L _ _ (eT m) (spMap (jetCoef (algebraMap T.V T.Fr) (Fin 2 × Fin ch.d) m))) ∧
        LB.Gen.Maps (LB.linCombIso I.w2 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (0 : Fin 2),
            jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (1 : Fin 2)]) (cε 2)) (e' m)
          (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
      ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L
          (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (0 : Fin 2),
            jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (1 : Fin 2)] J ≫ I.m1.φ) (cε 2)),
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (ch.e m) ∧
        LB.Gen.Maps (LB.linCombIso I.w1 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (0 : Fin 2),
            jptG I.t' (𝟙 (Sp T.Fr)) ch.d x' m (1 : Fin 2)]) (cε 2)) (e' m)
          (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)) ∧
    ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
      (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
        LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
        LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
      ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ ch.wP I.m1.φ) ∧
        LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)

variable (Xo c)

structure IntegralChartA3 (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) where
  ch : letI := io.toAlgebra; ChartAt Xo c y.1
  I : IntData Xo c T io y.1
  FT : Fin (chD ch) → PS T.V 2 (chD ch)
  actT : 𝓞 E → Fin (chD ch) → PS T.V 1 (chD ch)
  ph1T : PS T.V 3 (chD ch)
  ph2T : PS T.V 3 (chD ch)
  syT : PS T.V 2 (chD ch)
  adT : 𝓞 E → PS T.V 2 (chD ch)
  uvecT : Lt1 Dw → Fin (chD ch) → T.V
  tgT : Fin (chD ch) → (Sp (DualNumber T.V) ⟶ I.G.G.left)
  xT : ∀ m, jOG (𝟙 (Sp T.V)) (chD ch) m 1 ⟶ I.G.G
  eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) (chD ch) xT m
  wPT : PrimTyG I.G

  tgBasis : (∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
    ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin (chD ch) → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w
  chartT : IsChartG I.G (𝟙 (Sp T.V)) (chD ch) FT actT tgT (fun j : Fin (chD ch) => Pi.single j (1 : T.V)) xT
  dirT : ∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
    (fun j : Fin (chD ch) => (homAt (𝟙 (Sp T.V))
      (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin (chD ch)) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
    (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left
  frameT : IsFrameG I.G (𝟙 (Sp T.V)) (chD ch) xT FT actT ph1T ph2T syT adT eT
  primT : IsPrimG I.G wPT
  gen : IsGenFibreChart ch I FT actT ph1T ph2T syT adT uvecT xT eT wPT

def ChartSaturated : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ),
    (∃ (w : Fin (chD C.ch) → Fin (chD C.ch) → T.V) (emb : Fin (Dw.mult τ) ↪ Fin (chD C.ch)),
      (∀ i, w (emb i) = C.uvecT ⟨τ, i⟩) ∧
      ∀ v : Fin (chD C.ch) → T.V, ∃! a : Fin (chD C.ch) → T.V, ∀ j, ∑ k, a k * w k j = v j) ∧
    ∀ (v : Fin (chD C.ch) → T.V) (a : T.V), a ≠ 0 →
      a • v ∈ Submodule.span T.V (Set.range fun i : Fin (Dw.mult τ) => C.uvecT ⟨τ, i⟩) →
      v ∈ Submodule.span T.V (Set.range fun i : Fin (Dw.mult τ) => C.uvecT ⟨τ, i⟩)

def IntegralChartExists : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y)

end Comparison₂

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def KapFG : Prop := ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (kap Z)).FG

def KapTrdeg (d : ℕ) : Prop := ∀ Z : Comp Xo c, Algebra.trdeg c.F (kap Z) = d

theorem fnFG_of (h : KapFG Xo c) : FnFG Xo c := by
  intro Z
  classical
  obtain ⟨s, hs⟩ := h Z
  have hfin : (Set.range fun i : FlagVar Dw =>
      algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) (MvPolynomial.X i)).Finite := Set.finite_range _
  refine ⟨s.image (algebraMap (kap Z) (Om Z)) ∪ hfin.toFinset, ?_⟩
  set K := IntermediateField.adjoin c.F
    ((s.image (algebraMap (kap Z) (Om Z)) ∪ hfin.toFinset : Finset (Om Z)) : Set (Om Z)) with hK
  have hC : ∀ a : kap Z, algebraMap (kap Z) (Om Z) a ∈ K := by
    intro a
    have ha : a ∈ IntermediateField.adjoin c.F (s : Set (kap Z)) := by
      rw [hs]
      exact IntermediateField.mem_top
    have h1 : IsScalarTower.toAlgHom c.F (kap Z) (Om Z) a ∈
        (IntermediateField.adjoin c.F (s : Set (kap Z))).map (IsScalarTower.toAlgHom c.F (kap Z) (Om Z)) :=
      by
        first
          | exact ⟨a, ha, rfl⟩
          | (rw [← SetLike.mem_coe, IntermediateField.coe_map]; exact Set.mem_image_of_mem _ ha)
    rw [IntermediateField.adjoin_map] at h1
    refine IntermediateField.adjoin.mono _ _ _ ?_ h1
    rintro _ ⟨b, hb, rfl⟩
    exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hb))
  have hP : ∀ q : MvPolynomial (FlagVar Dw) (kap Z),
      algebraMap (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) q ∈ K := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact hC a
    next p₁ p₂ h₁ h₂ =>
      rw [map_add (f := _)]
      exact K.add_mem h₁ h₂
    next p₁ i h₁ =>
      rw [map_mul]
      refine K.mul_mem h₁ (IntermediateField.subset_adjoin c.F _ ?_)
      exact Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin.mem_toFinset.mpr ⟨i, rfl⟩))
  rw [eq_top_iff]
  rintro x -
  obtain ⟨⟨p₁, p₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (nonZeroDivisors (MvPolynomial (FlagVar Dw) (kap Z))) x
  dsimp only
  rw [IsFractionRing.mk'_eq_div]
  exact K.div_mem (hP p₁) (hP p₂)

private lemma isAlgebraic_frac_lemma {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (x : K) : IsAlgebraic A x := by
  obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  dsimp only
  have hq : algebraMap A K (q : A) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors q.2
  refine ⟨Polynomial.C (q : A) * Polynomial.X - Polynomial.C p, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun f : Polynomial A => f.coeff 1) h0
    simp at h1
    try exact nonZeroDivisors.ne_zero q.2 h1
  · rw [IsFractionRing.mk'_eq_div]
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [mul_div_cancel₀ _ hq, sub_self]

theorem fnTrdeg_of (d : ℕ) (h : KapTrdeg Xo c d) : FnTrdeg Xo c (d + Nat.card (FlagVar Dw)) := by
  intro Z
  haveI h1 : FaithfulSMul (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (kap Z) (MvPolynomial (FlagVar Dw) (kap Z))).injective
  haveI h2 : FaithfulSMul (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (IsFractionRing.injective (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z))
  haveI h3 : FaithfulSMul c.F (kap Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap c.F (kap Z)).injective
  haveI h4 : FaithfulSMul (kap Z) (Om Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap (kap Z) (Om Z)).injective
  have e1 : Algebra.trdeg (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) = Cardinal.mk (FlagVar Dw) := by
    first
      | (rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id])
      | (rw [Algebra.trdeg_mvPolynomial, Cardinal.lift_id])
      | (rw [MvPolynomial.trdeg_eq, Cardinal.lift_id])
      | (rw [MvPolynomial.lift_trdeg, Cardinal.lift_id])
      | (rw [Algebra.trdeg_MvPolynomial, Cardinal.lift_id])
      | (rw [MvPolynomial.trdeg_eq_cardinalMk, Cardinal.lift_id])
  have e2 : Algebra.trdeg (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) = 0 := by
    unfold Algebra.trdeg
    refine le_antisymm (ciSup_le' fun s => ?_) zero_le
    refine (Cardinal.mk_eq_zero_iff.mpr ⟨fun x => ?_⟩).le
    exact s.2.transcendental x (isAlgebraic_frac_lemma _)
  have hcard : Cardinal.mk (FlagVar Dw) = ((Nat.card (FlagVar Dw) : ℕ) : Cardinal) := by
    first
      | exact Nat.cast_card.symm
      | simp [Cardinal.mk_fintype, Nat.card_eq_fintype_card]
  have T1 := lift_trdeg_add_eq (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z)
  have T2 := lift_trdeg_add_eq c.F (kap Z) (Om Z)
  simp only [Cardinal.lift_id] at T1 T2
  show Algebra.trdeg c.F (Om Z) = ((d + Nat.card (FlagVar Dw) : ℕ) : Cardinal)
  rw [← T2, h Z, ← T1, e1, e2, add_zero, hcard, Nat.cast_add]

end Formalism.L2.Pj

end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]


variable (Xo c) in
def supR (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f : Rul Xo c) : ℝ :=
  supAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f


variable (Xo c) in
def SupBdd (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    Prop :=
  ∀ σ, BddAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f


variable (Xo c) in
def PTNe : Prop := ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), (PT (Ω := Om Z) σ).Nonempty

theorem ptNe_of_fnFG (hfg : FnFG Xo c) : PTNe Xo c := fun Z σ => exists_embedding_over (hfg Z) σ

def ValAtCx (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ‖P (evC h Z f)‖ = cabs (evR Xo c f (yP Z P))

def NZSome (h : GenFrEx Xo c) (f : Rul Xo c) : Prop := ∃ Z, evC h Z f ≠ 0

section Pf

variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem meanK_mono' {K : Type} [Field K] [NumberField K] {F G : (K →+* ℂ) → ℝ} (hFG : ∀ sg, F sg ≤ G sg) :
    meanK F ≤ meanK G := by
  unfold meanK
  gcongr with sg _
  exact hFG sg

theorem exZ_wtZ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (i : Ix Dw) : exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by
  cases i <;> rfl

theorem nrmC_valC_le (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (Z : Comp Xo c) (P : Om Z →+* ℂ) :
    nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P ≤ supR Xo c fn (sgOf P) a n f := by
  have hb := hB (sgOf P)
  unfold BddAt at hb
  have hle := le_ciSup hb (yP Z P)
  have hc : (valC h a n f Z).coeff (wtZ a n) = evC h Z f := by
    unfold valC
    simp
  have heq : nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P =
      ptNorm (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
    unfold nrmC ptNorm
    rw [hc, hcx Z P a n f hS]
    simp only [exZ_wtZ, zpow_neg, zpow_natCast, inv_pow] <;> rfl
  rw [heq]
  exact hle

theorem log_supN_le (hfn : FnNe Xo c fn) (hPT : PTNe Xo c) (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (hN : NZSome h f) (σ : c.F →+* ℂ) :
    Real.log (⨆ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ), nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) ≤
      Real.log (supR Xo c fn σ a n f) := by
  have hbd : ∀ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ),
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2 ≤ supR Xo c fn σ a n f := by
    rintro ⟨Z, P, hP⟩
    have hσ : sgOf P = σ := hP
    have key := nrmC_valC_le (h := h) (yP := yP) hcx hS hB Z P
    rw [hσ] at key
    exact key
  obtain ⟨Z0, hZ0⟩ := hN
  obtain ⟨P0, hP0⟩ := hPT Z0 σ
  have hpos : 0 < nrmC fn (yP Z0) (wtZ a n) (valC h a n f Z0) P0 := by
    have hc : (valC h a n f Z0).coeff (wtZ a n) = evC h Z0 f := by
      unfold valC
      simp
    unfold nrmC
    rw [hc]
    apply mul_pos
    · exact norm_pos_iff.mpr ((map_ne_zero P0).mpr hZ0)
    · apply Finset.prod_pos
      intro i _
      exact zpow_pos (abs_pos.mpr (hfn _ _ i)) _
  have hne : Nonempty (Σ Z : Comp Xo c, PT (Ω := Om Z) σ) := ⟨⟨Z0, P0, hP0⟩⟩
  have hB' : BddAbove (Set.range fun p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ) =>
      nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) := ⟨_, Set.forall_mem_range.mpr hbd⟩
  apply Real.log_le_log
  · exact lt_of_lt_of_le hpos (le_ciSup hB' ⟨Z0, P0, hP0⟩)
  · exact ciSup_le hbd

end Pf

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Clauses

variable (Xo : Moduli Dw l) (c : Coeff l)

def FrChartF : Prop :=
  FrChart (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)

def BorChartF : Prop :=
  BorChart (K := c.F) (ι := Ix Dw) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')

end Clauses

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem evalWD_fr (h : FrChartF Xo c) :
    EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
  evalWD_of_frChart h

theorem wtField_of_borChart (h : BorChartF Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  exact wtAll_of_borChart h (ex Dw a n) hf.1 hf.2 S t y y' hy hy' hb

theorem unitIndep_of_charts (h : BorChartF Xo c) (hL : IntLatU Xo c) : UnitIndep Xo c :=
  unitIndep_of (wtField_of_borChart h) (intDiagUnit_of hL)

end Proofs

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

section Fin

variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))

def DivFin : Prop := ∀ (Z : Comp Xo c) (r : Om Z), r ≠ 0 → {v | d.admitted Z v ∧ v r ≠ 0}.Finite

def FrShFin (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ Z : Comp Xo c, {v | d.admitted Z v ∧ δ Z v ≠ 0}.Finite

theorem lawA3'_of (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (hord : ∀ Z v, d.ord Z v = ordC (δ Z v) v) (hD : DivFin d) (hF : FrShFin d δ) : LawA3' d := by
  intro Z G f hf hf0
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
  have ha : a ≠ 0 := by
    rintro rfl
    exact hf0 (zero_smul _ _)
  have hcoeff : (a • (AddMonoidAlgebra.single G (1 : Om Z))).coeff G = a := by
    first
      | simp
      | simp [AddMonoidAlgebra.smul_single']
      | (rw [AddMonoidAlgebra.smul_single', mul_one]; rfl)
  refine ((hD Z a ha).union (hF Z)).subset ?_
  rintro v ⟨hadm, hne⟩
  rw [hord] at hne
  unfold ordC at hne
  rw [hcoeff] at hne
  by_cases hv : v a = 0
  · refine Or.inr ⟨hadm, fun hδ => hne ?_⟩
    rw [hv, hδ]
    have hz : frW (0 : Ix Dw → ℤ) G = 0 := by
      unfold frW
      simp
    rw [hz]
    rfl
  · exact Or.inl ⟨hadm, hv⟩

end Fin

section Data

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

theorem lawA3'_dataOf
    (hD : DivFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (hF : FrShFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) δ) :
    LawA3' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) :=
  lawA3'_of _ δ (fun _ _ => rfl) hD hF

end Data

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ContDiffAtOfDiff
noncomputable section

namespace Formalism.L2.Pj.I2FramePointLemmas

open ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.PullbackSections NumberField
open scoped ContDiff

section Deriv

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Deriv

section Pi

variable {E : Type} [Field E] [NumberField E]

end Pi

section Log

variable {E : Type} [Field E] [NumberField E]

theorem dstar_pos (X : PT E) {dg : ℕ} (P : Par X dg) : 0 < dstar (E := E) P.m := by
  unfold dstar
  have h1 := P.hfr
  have h2 := P.hm1
  have hf : 0 < PT.f E := by
    rcases Nat.eq_zero_or_pos (PT.f E) with h | h
    · rw [h] at h1; simp at h1
    · exact h
  exact Nat.mul_pos (Nat.mul_pos two_pos hf) h2

theorem jbound_pos (X : PT E) {dg : ℕ} (P : Par X dg) (n : ℕ) : 0 < P.Jbound n := by
  have hd0 : (0 : ℝ) < (dstar (E := E) P.m : ℝ) := by exact_mod_cast dstar_pos X P
  have hd : (0 : ℝ) < 2 * (dstar (E := E) P.m : ℝ) := by linarith
  have hB := Real.rpow_pos_of_pos hd ((dstar (E := E) P.m : ℝ) / 2)
  have h6 : (0 : ℝ) < 6 * (2 * (dstar (E := E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2) :=
    mul_pos (by norm_num) hB
  unfold Par.Jbound
  exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (inv_pos.2 h6) _))
    (pow_pos (by norm_num) _)) (Real.exp_pos _)

end Log

end Formalism.L2.Pj.I2FramePointLemmas
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.LawA13OfContinuous
noncomputable section

namespace Formalism.L2.Pj

open MeasureTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

section Gen

variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))

def A13ContinuousOffNull : Prop :=
  ∀ Z (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∃ S : Set (Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1),
      MeasurableSet S ∧ d.sphMeasure S = 0 ∧
      ContinuousOn (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
        ∑ᶠ P ∈ d.ST Z sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
          Real.log (d.nrm Z G f P)) Sᶜ

theorem lawA13_of_continuous (hc : A13ContinuousOffNull d) : A13Measurable d := by
  intro Z sg G f hf hf0
  obtain ⟨S, hSm, hS0, hcont⟩ := hc Z sg hf hf0
  have h1 := hcont.aemeasurable (μ := d.sphMeasure) hSm.compl
  have h2 : d.sphMeasure.restrict Sᶜ = d.sphMeasure :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 hS0)
  rw [h2] at h1
  exact h1

end Gen

def NrmContOff (h : GenFrEx Xo c) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)) : Prop :=
  ∀ Z (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∃ S : Set (Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1),
      MeasurableSet S ∧
      Measure.pi (fun _ => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere) S = 0 ∧
      ContinuousOn (fun t : Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1 =>
        ∑ᶠ P ∈ {P : Om Z →+* ℂ | P ∈ PT sg ∧ ∀ i, ∑ j, (t i : EuclideanSpace ℂ (Fin (N + 1))) j *
            P (ratio (Ω := Om Z) (valG h uL (wR j) Z) (valG h uL (wR (jc Z)) Z)) = 0},
          Real.log (nrmC fn (yP Z) G f P)) Sᶜ

theorem lawA13_of_data (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (hc : NrmContOff h fn yP Dd N uL wR jc) :
    A13Measurable (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR
      etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) :=
  lawA13_of_continuous _ hc

end Formalism.L2.Pj
end
end
