module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkZeroOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem exists_qk_zero_over : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ b : TF (R := V) F ⟶ D.P.A, b ^ k = 1 → ∃ p : QkPt D F k, p.y = 0 ∧ p.g.b = b := by
  intro V _ _ D hB F _ _ _ k hk b hb
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  exact exists_qk_over (F := F) hJ hB hk 0 b (by rw [hb, cPoint_zero])

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem spMap_comp_tf {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V) {F₀ F : Type}
    [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F) (hj : Ext f j) :
    spMap j ≫ (TF (R := R) F₀).hom = (TF (R := V) F).hom ≫ spMap f := by
  simp only [TF, jFK, jK, spMap, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact hj r

theorem tr_base {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {f : R →+* V} {D₀ : DegPre R}
    {D : DegPre V} {hD : IsPullDeg f D₀ D} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F]
    [Algebra (FractionRing V) F] {j : F₀ →+* F} (hj : Ext f j) {g₀ : GtPtF D₀ F₀} {g : GtPtF D F}
    (h : Tr f hD j g₀ g) {X : Scheme.{0}} (m : D₀.P.A.left ⟶ X) (k : Sp R ⟶ X)
    (hg₀ : g₀.b.left ≫ m = (TF (R := R) F₀).hom ≫ k) :
    g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f)) ≫ m = (TF (R := V) F).hom ≫ spMap f ≫ k := by
  obtain ⟨g₁, ⟨hb, -⟩, hp⟩ := h
  rw [← Category.assoc, hp.1, hb, Category.assoc, hg₀, ← Category.assoc, spMap_comp_tf f j hj, Category.assoc]

theorem exists_level_pairs : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (D₁ D₂ : DegData V J') (ω : L.W →+* R) (β : D₀.toPre.P.A.left ⟶ L.T.B.left), IsGrpPullback D₀.toPre.P.A L.T.B (spMap ω) β → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ → Ext f₂ j₂ → (∀ p₀ : QkPt D₀.toPre F₀ n, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = 0 ∧ p₁.g.b.left ≫ ((hD₁.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₁)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₁.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ ((hD₂.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₂)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₂.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) := by
  intro o _ ζ n L hn R _ _ V _ _ J J' D₀ D₁ D₂ ω β hβ f₁ f₂ hD₁ hD₂ F₀ _ _ _ F _ _ j₁ j₂ b φ hj₁ hj₂ H l
  have hc := IsGrpPullback.comp hβ L.cart
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.SiegelPull.push_surjective hc (TF (R := R) F₀) (toUnit _ ≫ L.F.univ.lev l)
  have hb₀' : b₀.left ≫ β ≫ L.β = (TF (R := R) F₀).hom ≫ spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫
      (L.F.univ.lev l).left := by
    have e := congrArg (fun z => z.left) hb₀
    simp only [pushHom, pushPt, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left] at e
    rw [e]
    simp
  have hpow : b₀ ^ n = 1 := by
    apply GlobalTheory.SiegelPull.push_injective hc
    rw [map_pow, hb₀, ← MonObj.comp_pow, L.F.univ.lev_tors, MonObj.comp_one, map_one]
  obtain ⟨p₀, hp₀y, hp₀b⟩ := GlobalTheory.TInj.exists_qk_zero_over R D₀.toPre D₀.tau_bimult F₀ n hn b₀ hpow
  obtain ⟨p₁, p₂, h1y, htr1, h2y, htr2, hq⟩ := H p₀
  have hg₀ : p₀.g.b.left ≫ β ≫ L.β = (TF (R := R) F₀).hom ≫ (spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫
      (L.F.univ.lev l).left) := by rw [hp₀b, hb₀']
  have hsp : ∀ f : R →+* V, spMap (f.comp ω) = spMap f ≫ spMap ω := fun f => by
    simp only [spMap, ← Spec.map_comp]; rfl
  refine ⟨p₁, p₂, by rw [h1y, hp₀y, map_zero], ?_, by rw [h2y, hp₀y, map_zero], ?_, hq⟩
  · have e := tr_base hj₁ htr1 _ _ hg₀
    rw [hsp]
    simpa only [Category.assoc] using e
  · have e := tr_base hj₂ htr2 _ _ hg₀
    rw [hsp]
    simpa only [Category.assoc] using e

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_point_pairs_lower_base : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (D₁ D₂ : DegData V J') (ω : L.W →+* R) (β : D₀.toPre.P.A.left ⟶ L.T.B.left), IsGrpPullback D₀.toPre.P.A L.T.B (spMap ω) β → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ → Ext f₂ j₂ → (∀ p₀ : QkPt D₀.toPre F₀ n, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = 0 ∧ p₁.g.b.left ≫ ((hD₁.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₁)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₁.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ ((hD₂.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₂)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₂.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) := by
  exact @GlobalTheory.TInj.exists_level_pairs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabExtOfTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

theorem Trait.exists_lift {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (F : Type) [Field F] [Algebra (FractionRing W) F] (z : Sp F ⟶ C.G.left)
    (hz : z ≫ C.G.hom = jFK (R := W) F ≫ jK W ≫ T.ξ) :
    ∃ x : TFK (R := W) F ⟶ T.A.A, x.left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = z := by
  have w₁ : z ≫ C.G.hom = (jFK (R := W) F ≫ jK W) ≫ T.ξ := by rw [hz, Category.assoc]
  have w₂ : T.cart.1.lift z (jFK (R := W) F ≫ jK W) w₁ ≫ T.G.hom = jFK (R := W) F ≫ jK W :=
    T.cart.1.lift_snd _ _ _
  let g₂ : Sp F ⟶ pullback T.G.hom (jK W) := pullback.lift (T.cart.1.lift z (jFK (R := W) F ≫ jK W) w₁) (jFK (R := W) F) w₂
  have hs : T.U.gen.hom.left ≫ T.A.A.hom = pullback.snd T.G.hom (jK W) := Over.w T.U.gen.hom
  have hgi : T.U.gen.hom.left ≫ T.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  refine ⟨Over.homMk (g₂ ≫ T.U.gen.hom.left) (by
    show (g₂ ≫ T.U.gen.hom.left) ≫ T.A.A.hom = jFK (R := W) F
    rw [Category.assoc, hs]
    exact pullback.lift_snd _ _ _), ?_⟩
  show (g₂ ≫ T.U.gen.hom.left) ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = z
  rw [Category.assoc, reassoc_of% hgi, pullback.lift_fst_assoc]
  exact T.cart.1.lift_fst _ _ _

end GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull

theorem labExt_of_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], Nonempty (Trait C W) →
    ∀ σ : Kb R →ₐ[FractionRing R] Kb R, LabExt σ (C.lab j) (C.lab j) := by
  intro R _ _ _ hR D C j W _ _ _ ⟨T⟩ σ p q hpq
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  have hGF := hL.globalFns
  have := hR.2
  have hB := D.tau_bimult
  have hW := T.cdvr
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hk : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap T.inj)).toAlgebra
  have cF : Compat T.φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap T.inj r)
  obtain ⟨em⟩ := nonempty_lift (FractionRing R) (Kb W)
  obtain ⟨r, hr⟩ := exists_ext hB em q
  have hr' : QkExt (em.comp σ).toRingHom p r := qkExt_trans hpq hr
  have hr₁ := isPullGtF_pullGt T.hD hGF cF r.g

  have hgp : jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ = jFK (R := R) (Kb W) ≫ C.gp := by
    let ρ : R →+* Kb W := (algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp T.φ)
    have hρ : Function.Injective ρ :=
      (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp T.inj)
    have hy : (jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ) ≫ C.π = spMap ρ := by
      rw [Category.assoc, Category.assoc, T.ξ_π, spMap_comp, spMap_comp]
    obtain ⟨ga, hga, e⟩ := Modif.factor_gp R C.toModif (Kb W) ρ _ hρ hy
    have hga' : ga = algebraMap (FractionRing R) (Kb W) :=
      IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun s => (hga s).trans (cF s).symm)
    rw [e, hga']
  have hz : ∀ (τ : Kb R →ₐ[FractionRing R] Kb W) (x : TFK (R := R) (Kb R) ⟶ C.A.A),
      (spMap τ.toRingHom ≫ x.left ≫ C.α) ≫ C.G.hom = jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ := by
    intro τ x
    rw [hgp, Category.assoc, Category.assoc, C.α_cart.1.w, ← Category.assoc x.left, Over.w x, ← Category.assoc]
    show (spMap τ.toRingHom ≫ spMap (algebraMap (FractionRing R) (Kb R))) ≫ C.gp = _
    rw [← spMap_comp]; exact congrArg (fun f => spMap f ≫ C.gp) τ.comp_algebraMap
  obtain ⟨x₁, hx₁⟩ := T.exists_lift (Kb W) _ (hz em (C.lab j q))
  obtain ⟨x₂, hx₂⟩ := T.exists_lift (Kb W) _ (hz (em.comp σ) (C.lab j p))
  have t₁ := T.lab (Kb W) em cF j q r (pullQk T.hD hGF cF hB T.D'.tau_bimult r) x₁ hr rfl hr₁ hx₁
  have t₂ := T.lab (Kb W) (em.comp σ) cF j p r (pullQk T.hD hGF cF hB T.D'.tau_bimult r) x₂ hr' rfl hr₁ hx₂
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause W _ bW T.D' T.A T.G hGs T.U (Kb W) (C.n ^ j) hk
  have e : x₁ = x₂ := ((hf.1 _ _).1 t₁).trans ((hf.1 _ _).1 t₂).symm
  subst e
  have e' := hx₁.symm.trans hx₂
  haveI : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  refine (cancel_epi (spMap em.toRingHom)).1 (C.α_cart.1.hom_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc, e', Category.assoc, ← Category.assoc (spMap em.toRingHom), ← spMap_comp]
    rfl
  · rw [Category.assoc, Over.w (C.lab j q), Category.assoc, Category.assoc, Over.w (C.lab j p)]
    exact congrArg (spMap em.toRingHom ≫ ·) ((spMap_comp _ _).symm.trans (congrArg spMap σ.comp_algebraMap)).symm

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueImageEqImageValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueImageEqImageValue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep
open GlobalTheory.Points


open GlobalTheory.ZH.RatModel in
theorem Tower.valF_app_p {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    {U : X₁.M.Z.Opens} (hU : (U : Set X₁.M.Z).Nonempty) (a : Γ(X₁.M.Z, U)) :
    valF 𝔗.X₂.M.pt (𝔗.p ⁻¹ᵁ U) (𝔗.p.app U a) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (valF X₁.M.pt U a) := by
  refine (valR_comp 𝔗.X₂.M.pt 𝔗.p U a).symm.trans ?_
  rw [𝔗.p_pt]
  exact valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt hU) a

theorem Tower.stalkHom_stalkMap_p {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    (z₂ : 𝔗.X₂.M.Z) (x : X₁.M.Z.presheaf.stalk (𝔗.p z₂)) :
    𝔗.X₂.M.stalkHom z₂ (𝔗.p.stalkMap z₂ x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) := by
  obtain ⟨U, hz, f, rfl⟩ := X₁.M.Z.presheaf.germ_exist x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ hz f]
  exact (RatModel.stalkHom_germ (M := 𝔗.X₂.M) (U := 𝔗.p ⁻¹ᵁ U) hz _).trans (𝔗.valF_app_p ⟨_, hz⟩ f)

theorem Tower.val_comp_p {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    {K : Type} [Field K] (y : Sp K ⟶ 𝔗.X₂.M.Z) (w : Sp K) {x : X₁.Ω₁} (hx : x ∈ X₁.M.O (𝔗.p (y w))) :
    X₁.M.val (y ≫ 𝔗.p) x = 𝔗.X₂.M.val y (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (𝔗.p ⁻¹ᵁ U : 𝔗.X₂.M.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [← 𝔗.valF_app_p ⟨_, hz⟩ a, RatModel.val_valF h1,
    RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact valR_comp y 𝔗.p U a

theorem RatModel.val_spMap_comp_field {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {K K' : Type} [Field K]
    [Field K'] (σ : K →+* K') (y : Sp K ⟶ M.Z) (w : Sp K) {x : Ω} (hx : x ∈ M.O (y w)) :
    M.val (spMap σ ≫ y) x = σ (M.val y x) := by
  obtain ⟨U, g, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ U := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [RatModel.val_valF h1, RatModel.val_valF (by rintro _ ⟨w', rfl⟩; exact h1 ⟨_, rfl⟩)]
  exact valR_spMap_comp σ y U ((top_le_preimage_iff _ _).2 h1) g

theorem Tower.val_om_ext : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → 𝔗.Ext ev io ev₂ → RegAt X₁ z₁ ev → ∀ a : X₁.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.om a) = f (X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hz V V' _ _ _ _ ev io ev₂ f hf hio hext hreg a
  subst hz
  have e1 : ev₂.comp (𝔗.p.stalkMap z₂).hom = io.comp ev :=
    RingHom.ext fun x => hext.2 x _ (𝔗.stalkHom_stalkMap_p z₂ x)
  have e2 : jK V' ≫ spMap io = spMap f ≫ jK V := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext v
    exact (hf v).symm
  have h1 : (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) ≫ 𝔗.p =
      spMap f ≫ (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) := by
    have e3 : spMap ev₂ ≫ Spec.map (𝔗.p.stalkMap z₂) = spMap io ≫ spMap ev := by
      show Spec.map (CommRingCat.ofHom ev₂) ≫ Spec.map (CommRingCat.ofHom (𝔗.p.stalkMap z₂).hom) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e1, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc (spMap ev₂), e3,
      Category.assoc, ← Category.assoc (jK V'), e2]
    simp only [Category.assoc]
  have hmem := hreg a a.2
  have hp : 𝔗.p ((jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))) =
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) (closedPoint (FractionRing V)) := by
    have e := congrArg (fun q : Sp (FractionRing V') ⟶ X₁.M.Z => q (closedPoint (FractionRing V'))) h1
    refine e.trans ?_
    show (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) ((spMap f) (closedPoint (FractionRing V'))) = _
    rw [Subsingleton.elim ((spMap f) (closedPoint (FractionRing V'))) (closedPoint (FractionRing V))]
  rw [𝔗.om_eq, ← 𝔗.val_comp_p (K := FractionRing V') _ (closedPoint (FractionRing V')) (hp ▸ hmem), h1,
    RatModel.val_spMap_comp_field (K := FractionRing V) f _ (closedPoint (FractionRing V)) hmem]

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueImageEqImageValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deeperTheta_value_image_eq_image_value : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → 𝔗.Ext ev io ev₂ → RegAt X₁ z₁ ev → ∀ a : X₁.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.om a) = f (X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.val_om_ext | exact GlobalTheory.Poinc.Sep.Tower.val_om_ext | (intros; apply GlobalTheory.Poinc.Sep.Tower.val_om_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstOfSpecialisationInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstOfSpecialisationInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory

theorem fibre_exists_finite_generizing {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z)
    (hq : Continuous q) (z : Z) :
    ∃ T : Set Y, T.Finite ∧ (∀ e ∈ T, q e = z) ∧ ∀ w, q w = z → ∃ e ∈ T, e ⤳ w := by
  have hfin : (irreducibleComponents (q ⁻¹' {z})).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have key : ∀ C : irreducibleComponents (q ⁻¹' {z}),
      ∃ e : Y, q e = z ∧ ∀ c ∈ C.1, e ⤳ (c : Y) := by
    intro C
    have hC : IsIrreducible C.1 := C.2.1
    have hCi : IsIrreducible (((↑) : q ⁻¹' {z} → Y) '' C.1) :=
      hC.image _ continuous_subtype_val.continuousOn
    have hgen := hCi.isGenericPoint_genericPoint_closure
    refine ⟨hCi.genericPoint, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hC.nonempty
      have hcz : q c = z := c.2
      have h1 : hCi.genericPoint ⤳ (c : Y) := hgen.specializes (subset_closure ⟨c, hc, rfl⟩)
      have h2 : hCi.genericPoint ∈ closure (((↑) : q ⁻¹' {z} → Y) '' C.1) := hgen.mem
      have h3 : closure (((↑) : q ⁻¹' {z} → Y) '' C.1) ⊆ q ⁻¹' closure {z} :=
        (closure_mono (by rintro _ ⟨d, -, rfl⟩; exact d.2)).trans (hq.closure_preimage_subset _)
      have h4 : z ⤳ q hCi.genericPoint := specializes_iff_mem_closure.2 (h3 h2)
      have h5 : q hCi.genericPoint ⤳ z := by
        have := h1.map hq
        rwa [hcz] at this
      exact (h5.antisymm h4).eq
    · intro c hc
      exact hgen.specializes (subset_closure ⟨c, hc, rfl⟩)
  choose f hf using key
  haveI : Finite (irreducibleComponents (q ⁻¹' {z})) := hfin.to_subtype
  refine ⟨Set.range f, Set.finite_range f, ?_, ?_⟩
  · rintro _ ⟨C, rfl⟩
    exact (hf C).1
  · intro w hw
    let w' : q ⁻¹' {z} := ⟨w, hw⟩
    refine ⟨f ⟨_, irreducibleComponent_mem_irreducibleComponents w'⟩, ⟨_, rfl⟩, ?_⟩
    exact (hf _).2 w' mem_irreducibleComponent

theorem fibre_const_of_specializes_invariant : ∀ (Y Z : Type) [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z), Continuous q → ∀ z : Z, _root_.IsPreconnected (q ⁻¹' {z}) → ∀ P : Y → Prop, (∀ a b, q a = z → q b = z → a ⤳ b → (P a ↔ P b)) → ∀ a b, q a = z → q b = z → P a → P b := by
  intro Y Z _ _ _ _ _ q hq z hpc P hP a b ha hb hPa
  obtain ⟨T, hTf, hTz, hTs⟩ := fibre_exists_finite_generizing q hq z
  by_contra hPb
  have closed : ∀ R : Y → Prop, IsClosed (⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y)) :=
    fun R => (hTf.subset (show {e ∈ T | R e} ⊆ T from fun _ h => h.1)).isClosed_biUnion (fun _ _ => isClosed_closure)
  have mem : ∀ (R : Y → Prop) (e w : Y), e ∈ T → R e → e ⤳ w →
      w ∈ ⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y) := by
    intro R e w he hR hs
    exact Set.mem_biUnion ⟨he, hR⟩ (specializes_iff_mem_closure.1 hs)
  have mem' : ∀ (R : Y → Prop) (w : Y), w ∈ ⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y) →
      ∃ e, e ∈ T ∧ R e ∧ e ⤳ w := by
    intro R w hw
    obtain ⟨e, ⟨he, hR⟩, hc⟩ := Set.mem_iUnion₂.1 hw
    exact ⟨e, he, hR, specializes_iff_mem_closure.2 hc⟩
  obtain ⟨w, hwS, hwt, hwt'⟩ := isPreconnected_closed_iff.1 hpc _ _ (closed P) (closed (fun e => ¬ P e))
    (by
      intro w hw
      obtain ⟨e, he, hs⟩ := hTs w hw
      by_cases h : P e
      · exact Or.inl (mem P e w he h hs)
      · exact Or.inr (mem _ e w he h hs))
    (by
      obtain ⟨e, he, hs⟩ := hTs a ha
      exact ⟨a, ha, mem P e a he ((hP e a (hTz e he) ha hs).2 hPa) hs⟩)
    (by
      obtain ⟨e, he, hs⟩ := hTs b hb
      exact ⟨b, hb, mem (fun e => ¬ P e) e b he (fun h => hPb ((hP e b (hTz e he) hb hs).1 h)) hs⟩)
  have hwz : q w = z := hwS
  obtain ⟨e₁, h₁, hP₁, hs₁⟩ := mem' P w hwt
  obtain ⟨e₂, h₂, hP₂, hs₂⟩ := mem' _ w hwt'
  exact hP₂ ((hP e₂ w (hTz e₂ h₂) hwz hs₂).2 ((hP e₁ w (hTz e₁ h₁) hwz hs₁).1 hP₁))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstOfSpecialisationInvariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_const_of_specialisation_invariant : ∀ (Y Z : Type) [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z), Continuous q → ∀ z : Z, _root_.IsPreconnected (q ⁻¹' {z}) → ∀ P : Y → Prop, (∀ a b, q a = z → q b = z → a ⤳ b → (P a ↔ P b)) → ∀ a b, q a = z → q b = z → P a → P b := by
  first | exact @GlobalTheory.fibre_const_of_specializes_invariant | exact GlobalTheory.fibre_const_of_specializes_invariant | (intros; apply GlobalTheory.fibre_const_of_specializes_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelCongruenceEndoAllAlgClosedFields
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelCongruenceEndoAllAlgClosedFields
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8
namespace GlobalTheory.LabelTransfer

theorem isAlgebraic_padicAlgCl (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V] (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V)
    [Algebra (FractionRing V) (PadicAlgCl p)]
    (hV : ∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔
      x ∈ Set.range (algebraMap V (FractionRing V))) :
    Algebra.IsAlgebraic (FractionRing V) (PadicAlgCl p) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨P, hP0, hPz⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[p]) z
  set κ := algebraMap (FractionRing V) (PadicAlgCl p)
  have hl : P.map (algebraMap ℚ_[p] (PadicAlgCl p)) ∈ Polynomial.lifts κ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV _
  obtain ⟨P', hP'⟩ := hl
  rw [Polynomial.coe_mapRingHom] at hP'
  refine ⟨P', fun h => hP0 ?_, ?_⟩
  · have : P.map (algebraMap ℚ_[p] (PadicAlgCl p)) = 0 := by rw [← hP', h, Polynomial.map_zero]
    exact (Polynomial.map_eq_zero_iff (algebraMap ℚ_[p] (PadicAlgCl p)).injective).1 this
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    change Polynomial.eval z (P'.map κ) = 0
    rw [hP', ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def, hPz]

end GlobalTheory.LabelTransfer

namespace GlobalTheory.LabelTransfer

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (eA : u.A.A ⟶ u.A.A) (s : u.D.toPre.X →+ u.D.toPre.X), (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left = x.left ≫ eA.left → CongMod m pk'.y (s pk.y)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing u.V) F] (k : ℕ), 1 ≤ k → IsUnit (k : u.V) → ∀ (q q' : QkPt u.D.toPre F k) (a a' : TFK (R := u.V) F ⟶ u.A.A), QkToAkU u.U.toUnifPre F k q a → QkToAkU u.U.toUnifPre F k q' a' → a.left = a'.left ≫ eA.left → CongMod k q.y (s q'.y) := by
  intro o Ω _ _ _ S ρ p _ y₀ u eA s H F _ _ _ k hk _ q q' a a' hq hq' haa
  haveI : CharZero (FractionRing u.V) := (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : Algebra.IsAlgebraic (FractionRing u.V) (PadicAlgCl p) :=
    isAlgebraic_padicAlgCl p u.V u.complete u.norm_le
  let emb : PadicAlgCl p →ₐ[FractionRing u.V] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra (PadicAlgCl p) F := emb.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing u.V) (PadicAlgCl p) F :=
    IsScalarTower.of_algebraMap_eq fun c => (emb.commutes c).symm
  have hf : (algebraMap (PadicAlgCl p) F).comp (algebraMap (FractionRing u.V) (PadicAlgCl p)) =
      algebraMap (FractionRing u.V) F := (IsScalarTower.algebraMap_eq _ _ _).symm
  have hk0 : ((k : ℕ) : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.QkClosure.exists_qkExt_descent (algebraMap (PadicAlgCl p) F) hf hk0 q
  obtain ⟨q₀', hq₀'⟩ := GlobalTheory.QkClosure.exists_qkExt_descent (algebraMap (PadicAlgCl p) F) hf hk0 q'
  obtain ⟨f₀, hf₀, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) k hk
  obtain ⟨f₁, hf₁, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U F k hk
  have hL := GlobalTheory.firstFiveLaws
  have e₁ : QkToAkU u.U.toUnifPre F k q (GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀) :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow u.U hk hq₀ _).1 ((hf₀ _ _).2 rfl)
  have e₂ : QkToAkU u.U.toUnifPre F k q' (GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀') :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow u.U hk hq₀' _).1 ((hf₀ _ _).2 rfl)
  have ha : a = GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀ :=
    ((hf₁ _ _).1 hq).trans ((hf₁ _ _).1 e₁).symm
  have ha' : a' = GlobalTheory.TorsionExt.fieldMap (PadicAlgCl p) F ≫ f₀ q₀' :=
    ((hf₁ _ _).1 hq').trans ((hf₁ _ _).1 e₂).symm
  have hepi : Epi (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left := by
    have : Flat (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      inferInstanceAs (Flat (Spec.map (CommRingCat.ofHom (algebraMap (PadicAlgCl p) F))))
    have : Surjective (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      ⟨fun z => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _⟩⟩
    have : QuasiCompact (GlobalTheory.TorsionExt.fieldMap (R := u.V) (PadicAlgCl p) F).left :=
      inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap (PadicAlgCl p) F))))
    exact Flat.epi_of_flat_of_surjective _
  have hx : (f₀ q₀).left = (f₀ q₀').left ≫ eA.left := by
    rw [ha, ha', Over.comp_left, Over.comp_left, Category.assoc] at haa
    exact (cancel_epi _).1 haa
  have := H k q₀' q₀ (f₀ q₀') (f₀ q₀) hk ((hf₀ _ _).2 rfl) ((hf₀ _ _).2 rfl) hx
  rw [hq₀.1, hq₀'.1]
  exact this

end GlobalTheory.LabelTransfer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelCongruenceEndoAllAlgClosedFieldsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelCongruence_endo_all_algClosed_fields : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (eA : u.A.A ⟶ u.A.A) (s : u.D.toPre.X →+ u.D.toPre.X), (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left = x.left ≫ eA.left → CongMod m pk'.y (s pk.y)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing u.V) F] (k : ℕ), 1 ≤ k → IsUnit (k : u.V) → ∀ (q q' : QkPt u.D.toPre F k) (a a' : TFK (R := u.V) F ⟶ u.A.A), QkToAkU u.U.toUnifPre F k q a → QkToAkU u.U.toUnifPre F k q' a' → a.left = a'.left ≫ eA.left → CongMod k q.y (s q'.y) := by
  first | exact @GlobalTheory.LabelTransfer.main | exact GlobalTheory.LabelTransfer.main | (intros; apply GlobalTheory.LabelTransfer.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinJetConjDirectionDiagonalExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAddDirection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAddDirection
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem jet_add_dir_of_hasLevel : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im →
    jet (2 * s) L κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet (2 * s) L μ τ c t := by
  intro hE F _ _ _ hf s N L hs hN hL τ c t v κ hτ
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, -, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  exact GlobalTheory.T.hilbertEisensteinLatticeJet_split_direction_add F (2 * s) 𝔞 𝔟 _ a x τ c t v κ (even_two_mul s) ha hτ

end GlobalTheory.HilbFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAddDirectionStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_add_direction : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet (2 * s) L μ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_add_dir_of_hasLevel | exact GlobalTheory.HilbFam.jet_add_dir_of_hasLevel | (intros; apply GlobalTheory.HilbFam.jet_add_dir_of_hasLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinJetConjDirectionDiagonalExpansion
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem jet_conj_expand : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ : ℍ) (κ : Emb F → ℕ) (Ch : ℍ → ℂ), jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ i, (κ i - μ i)) * hfun (2 * s) L μ Ch τ := by
  intro hE F _ _ _ hf s N L hs hN hL τ κ Ch
  have him : 0 < (τ : ℂ).im := τ.im_pos
  have hne : τ.im ≠ 0 := τ.im_pos.ne'
  set v : ℂ := ((Real.pi / τ.im : ℝ) : ℂ) with hv
  set T : ℂ := 2 * Real.pi * Complex.I with hT
  have hT0 : T ≠ 0 := by
    simp [hT, Real.pi_ne_zero, Complex.I_ne_zero]
  have hw : v * (starRingEnd ℂ (τ : ℂ) - τ) = -T := by
    have : starRingEnd ℂ (τ : ℂ) - τ = -(2 * ((τ : ℂ).im : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp <;> ring
    rw [this, hv, hT]
    have : ((τ : ℂ).im : ℂ) = (τ.im : ℂ) := rfl
    rw [this]; push_cast
    have h0 : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
    field_simp
  set C : ℂ := T ^ 2 * Ch τ with hC
  have h1 := GlobalTheory.T.hilbert_eisenstein_jet_smul_direction hE F hf s N L hs hN hL τ 1 (starRingEnd ℂ (τ : ℂ) - τ) v κ him
  have h2 := GlobalTheory.T.hilbert_eisenstein_jet_add_direction hE F hf s N L hs hN hL τ C (-T) (v - C) κ him
  rw [mul_one, hw] at h1
  have h3 : jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * v ^ (∑ i, κ i) = jet (2 * s) L κ τ (C + (v - C)) (-T) := by
    rw [add_sub_cancel, h1, mul_comm]
  rw [h3, h2, Finset.sum_div]
  refine Finset.sum_congr rfl fun μ hμ ↦ ?_
  have hle : μ ≤ κ := Finset.mem_Iic.mp hμ
  have hwt : wt (2 * s) κ = wt (2 * s) μ + 2 * ∑ i, (κ i - μ i) := by
    have : ∑ i, κ i = ∑ i, μ i + ∑ i, (κ i - μ i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ (Nat.add_sub_of_le (hle i)).symm
    simp only [wt, this]; ring
  have hsub : v / T ^ 2 - Ch τ = (v - C) / T ^ 2 := by
    rw [hC]; field_simp
  rw [hsub, hfun, ← hT, ← hC, hwt, pow_add, pow_mul, div_pow]
  field_simp

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinJetConjDirectionDiagonalExpansionStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_jet_conj_direction_diagonal_expansion : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ : ℍ) (κ : Emb F → ℕ) (Ch : ℍ → ℂ), jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ i, (κ i - μ i)) * hfun (2 * s) L μ Ch τ := by
  first | exact @GlobalTheory.HilbFam.jet_conj_expand | exact GlobalTheory.HilbFam.jet_conj_expand | (intros; apply GlobalTheory.HilbFam.jet_conj_expand <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialsDifferByUnitsPositiveBoundaryCombinatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialsDifferByUnitsPositiveBoundaryCombinatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
namespace GlobalTheory.TInj

theorem coneval : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (r m N n : ℕ), 1 ≤ n → ∀ (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin r → ℤ)) (s₁ s₂ : (Fin m ⊕ Fin N) → V) (ga : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)), (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → (∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (a) (b))) → ∃ c₁ c₂ : Fin m → ℕ, (∀ k, 0 < c₁ k) ∧ (∀ k, 0 < c₂ k) ∧ ∑ k, c₁ k • ε (.inl k) = ∑ k, c₂ k • pull ga.toLinearMap (ε (.inl k)) := by
  intro V _ _ _ r m N n hn ε s₁ s₂ ga h1m h1u h2m h2u hprod
  classical
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  let ℓ : FractionRing V → ℤ := fun x => WithZero.log (v x)
  have hinj := IsFractionRing.injective V (FractionRing V)
  have hne : ∀ x : V, x ≠ 0 → algebraMap V (FractionRing V) x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ hinj).2 hx
  have hv0 : ∀ x : FractionRing V, x ≠ 0 → v x ≠ 0 := fun x hx => (Valuation.ne_zero_iff v).2 hx
  have ℓmul : ∀ x y : FractionRing V, x ≠ 0 → y ≠ 0 → ℓ (x * y) = ℓ x + ℓ y := fun x y hx hy => by
    simp only [ℓ, map_mul, WithZero.log_mul (hv0 x hx) (hv0 y hy)]
  have ℓzpow : ∀ (x : FractionRing V) (z : ℤ), ℓ (x ^ z) = z * ℓ x := fun x z => by
    simp only [ℓ, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  have ℓprod : ∀ (J : Type) (t : Finset J) (g : J → FractionRing V), (∀ i, g i ≠ 0) →
      ℓ (∏ i ∈ t, g i) = ∑ i ∈ t, ℓ (g i) := by
    intro J t g hg
    induction t using Finset.induction_on with
    | empty => simp [ℓ]
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ℓmul _ _ (hg j)
        (Finset.prod_ne_zero_iff.2 fun i _ => hg i), ih]
  have hunit : ∀ x : V, IsUnit x → ℓ (algebraMap V (FractionRing V) x) = 0 := by
    intro x hx
    have h1 : v (algebraMap V (FractionRing V) x) = 1 := by
      refine le_antisymm (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ x) ?_
      by_contra hlt
      have := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal V) x).1 (lt_of_not_ge hlt)
      exact (IsLocalRing.mem_maximalIdeal x).1 this hx
    simp only [ℓ, h1, WithZero.log_one]
  have hneg : ∀ x : V, x ∈ maximalIdeal V → x ≠ 0 → ℓ (algebraMap V (FractionRing V) x) < 0 := by
    intro x hm hx
    have h1 : v (algebraMap V (FractionRing V) x) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal V) x).2 hm
    have := (WithZero.log_lt_log (hv0 _ (hne x hx)) one_ne_zero).2 h1
    simpa [ℓ, WithZero.log_one] using this
  have hs0 : ∀ (s : (Fin m ⊕ Fin N) → V), (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) →
      (∀ k, IsUnit (s (.inr k))) → ∀ i, algebraMap V (FractionRing V) (s i) ≠ 0 := by
    intro s hm hu i
    rcases i with k | k
    · exact hne _ (hm k).2
    · exact hne _ (hu k).ne_zero
  have hsum : ∀ (s : (Fin m ⊕ Fin N) → V), (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) →
      (∀ k, IsUnit (s (.inr k))) → ∀ z : (Fin m ⊕ Fin N) → ℤ,
      ℓ (∏ i, algebraMap V (FractionRing V) (s i) ^ z i) =
        ∑ k, z (.inl k) * ℓ (algebraMap V (FractionRing V) (s (.inl k))) := by
    intro s hm hu z
    rw [ℓprod _ _ _ (fun i => zpow_ne_zero _ (hs0 s hm hu i)), Fintype.sum_sum_type]
    simp only [ℓzpow, hunit _ (hu _), mul_zero, Finset.sum_const_zero, add_zero]
  let c₁ : Fin m → ℕ := fun k => (-ℓ (algebraMap V (FractionRing V) (s₁ (.inl k)))).toNat
  let c₂ : Fin m → ℕ := fun k => (-ℓ (algebraMap V (FractionRing V) (s₂ (.inl k)))).toNat
  have hc₁ : ∀ k, (c₁ k : ℤ) = -ℓ (algebraMap V (FractionRing V) (s₁ (.inl k))) := fun k => by
    have := hneg _ (h1m k).1 (h1m k).2
    simp only [c₁]; omega
  have hc₂ : ∀ k, (c₂ k : ℤ) = -ℓ (algebraMap V (FractionRing V) (s₂ (.inl k))) := fun k => by
    have := hneg _ (h2m k).1 (h2m k).2
    simp only [c₂]; omega
  refine ⟨c₁, c₂, fun k => ?_, fun k => ?_, ?_⟩
  · have := hc₁ k; have := hneg _ (h1m k).1 (h1m k).2; omega
  · have := hc₂ k; have := hneg _ (h2m k).1 (h2m k).2; omega
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  obtain ⟨u, hu⟩ := hprod a b
  have key := congrArg ℓ hu
  rw [ℓmul _ _ (hne _ u.ne_zero) (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hs0 s₁ h1m h1u i)),
    hunit _ u.isUnit, zero_add, hsum s₂ h2m h2u, hsum s₁ h1m h1u] at key
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, nsmul_eq_mul]
  beta_reduce at key
  have key' : (n:ℤ) * ∑ k, ((c₂ k : ℤ) * ε (.inl k) (ga a) (ga b)) = (n:ℤ) * ∑ k, ((c₁ k:ℤ) * ε (.inl k) a b) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      Finset.sum_congr rfl (fun k _ => show (n:ℤ) * ((c₂ k : ℤ) * ε (.inl k) (ga a) (ga b)) = -((n:ℤ) * ε (.inl k) (ga a) (ga b) * ℓ (algebraMap V (FractionRing V) (s₂ (.inl k)))) by rw [hc₂]; ring),
      Finset.sum_congr rfl (fun k _ => show (n:ℤ) * ((c₁ k : ℤ) * ε (.inl k) a b) = -((n:ℤ) * ε (.inl k) a b * ℓ (algebraMap V (FractionRing V) (s₁ (.inl k)))) by rw [hc₁]; ring),
      Finset.sum_neg_distrib, Finset.sum_neg_distrib, key]
  have := (mul_left_cancel₀ hn' key').symm
  exact this

end GlobalTheory.TInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialsDifferByUnitsPositiveBoundaryCombinatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (r m N n : ℕ), 1 ≤ n → ∀ (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin r → ℤ)) (s₁ s₂ : (Fin m ⊕ Fin N) → V) (ga : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)), (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → (∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (a) (b))) → ∃ c₁ c₂ : Fin m → ℕ, (∀ k, 0 < c₁ k) ∧ (∀ k, 0 < c₂ k) ∧ ∑ k, c₁ k • ε (.inl k) = ∑ k, c₂ k • pull ga.toLinearMap (ε (.inl k)) := by
  first | exact @GlobalTheory.TInj.coneval | exact GlobalTheory.TInj.coneval | (intros; apply GlobalTheory.TInj.coneval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalisationProjectiveQuasiFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalisationProjectiveQuasiFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegMin

theorem finite_of_finite_closedPoints {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    (h : (closedPoints T).Finite) : Finite T := by
  have hc : IsClosed (closedPoints T) := by
    rw [← Set.biUnion_of_singleton (closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx
  have e := JacobsonSpace.closure_inter_closedPoints (isClosed_univ (X := T))
  rw [Set.univ_inter, hc.closure_eq] at e
  rw [← Set.finite_univ_iff, ← e]
  exact h

theorem exists_embedding_closedPoint_fiber {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (z : f.fiber y) (hz : IsClosed ({z} : Set (f.fiber y))) :
    ∃ σ : (f.fiber y).residueField z ⟶ CommRingCat.of (AlgebraicClosure (Y.residueField y)),
      Spec.map σ ≫ (f.fiber y).fromSpecResidueField z ≫ f.fiberToSpecResidueField y =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
          (AlgebraicClosure (Y.residueField y)))) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    show LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have := isClosed_singleton_iff_isClosedImmersion.mp hz
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    ((f.fiber y).fromSpecResidueField z ≫ f.fiberToSpecResidueField y)
  have h1 : LocallyOfFiniteType (Spec.map ψ) := hψ ▸ inferInstance
  have h2 : IsFinite (Spec.map ψ) := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr h1
  rw [IsFinite.SpecMap_iff] at h2
  letI := ψ.hom.toAlgebra
  haveI : Module.Finite (Y.residueField y) ((f.fiber y).residueField z) := h2
  let σ : (f.fiber y).residueField z →ₐ[Y.residueField y] AlgebraicClosure (Y.residueField y) :=
    IsAlgClosed.lift
  refine ⟨CommRingCat.ofHom σ.toRingHom, ?_⟩
  rw [← hψ]
  refine (Spec.map_comp _ _).symm.trans ?_
  congr 1
  ext a
  exact σ.commutes a

theorem finite_preimage_singleton_of_qFin {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : QFin f) (y : Y) : (f ⁻¹' {y}).Finite := by
  let K := AlgebraicClosure (Y.residueField y)
  choose σ hσ using exists_embedding_closedPoint_fiber f y
  let Φ : closedPoints (f.fiber y) → (Sp K ⟶ X) := fun z ↦
    Spec.map (σ z.1 z.2) ≫ (f.fiber y).fromSpecResidueField z.1 ≫ f.fiberι y
  have hΦf (z) : Φ z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
      Y.fromSpecResidueField y := by
    simp only [Φ, Category.assoc, Scheme.Hom.fiber_fac]
    rw [← hσ z.1 z.2]
    simp only [Category.assoc]
  have hΦpt (z) : Φ z (IsLocalRing.closedPoint K : Sp K) = f.fiberι y z.1 := by
    have hm : (f.fiber y).fromSpecResidueField z.1 (Spec.map (σ z.1 z.2)
        (IsLocalRing.closedPoint K : Sp K)) ∈ Set.range ((f.fiber y).fromSpecResidueField z.1) :=
      ⟨_, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hm
    show (Spec.map (σ z.1 z.2) ≫ (f.fiber y).fromSpecResidueField z.1 ≫ f.fiberι y)
      (IsLocalRing.closedPoint K : Sp K) = _
    exact congrArg (f.fiberι y) (Set.mem_singleton_iff.mp hm)
  have hΦinj : Function.Injective Φ := by
    intro z z' h
    have := hΦpt z
    rw [h, hΦpt z'] at this
    exact Subtype.ext ((f.fiberι y).isEmbedding.injective this).symm
  have hcp : (closedPoints (f.fiber y)).Finite := by
    rcases (closedPoints (f.fiber y)).eq_empty_or_nonempty with he | ⟨z₀, hz₀⟩
    · rw [he]; exact Set.finite_empty
    · have hS := hf K (Φ ⟨z₀, hz₀⟩)
      haveI := hS.to_subtype
      have : Finite (closedPoints (f.fiber y)) :=
        Finite.of_injective (β := {w : Sp K ⟶ X | w ≫ f = Φ ⟨z₀, hz₀⟩ ≫ f})
          (fun z ↦ ⟨Φ z, by simp only [Set.mem_setOf_eq, hΦf]⟩)
          (fun a b h ↦ hΦinj (congrArg Subtype.val h))
      exact Set.toFinite _
  haveI := finite_of_finite_closedPoints hcp
  exact Set.finite_coe_iff.mp ((f.fiberHomeo y).finite_iff.mp inferInstance)

theorem exists_finite_openImmersion_of_qFin : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra.FiniteType ℤ o] (N : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp o) (f : X ⟶ PSpace o N), IsIntegral X → Geo.Tor.IsNormalScheme X → LocallyOfFiniteType s → QuasiCompact s → IsSeparated s → f ≫ PSpace.str o N = s → QFin f → ∃ (Z : Scheme.{0}) (p : Z ⟶ PSpace o N) (i : X ⟶ Z), IsFinite p ∧ IsOpenImmersion i ∧ i ≫ p = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧ Dense (Set.range i) := by
  intro o _ _ _ N X s f hX hN _ _ _ hfs hq
  subst hfs
  haveI := isProper_str o N
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (PSpace.str o N)
  haveI : QuasiCompact f := QuasiCompact.of_comp f (PSpace.str o N)
  haveI : IsSeparated f := IsSeparated.of_comp f (PSpace.str o N)
  haveI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (finite_preimage_singleton_of_qFin f hq)
  exact GlobalTheory.ZMain.exists_finite_openImmersion_pSpace o N X f hX hN inferInstance inferInstance
    inferInstance inferInstance

end GlobalTheory.SiegMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalisationProjectiveQuasiFiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_normalisation_projective_quasiFinite : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra.FiniteType ℤ o] (N : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp o) (f : X ⟶ PSpace o N), IsIntegral X → Geo.Tor.IsNormalScheme X → LocallyOfFiniteType s → QuasiCompact s → IsSeparated s → f ≫ PSpace.str o N = s → QFin f → ∃ (Z : Scheme.{0}) (p : Z ⟶ PSpace o N) (i : X ⟶ Z), IsFinite p ∧ IsOpenImmersion i ∧ i ≫ p = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧ Dense (Set.range i) := by
  first | exact @GlobalTheory.SiegMin.exists_finite_openImmersion_of_qFin | exact GlobalTheory.SiegMin.exists_finite_openImmersion_of_qFin | (intros; apply GlobalTheory.SiegMin.exists_finite_openImmersion_of_qFin <;> assumption)
end
end
