module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiSecPull
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechDR

theorem bijective_liftSemi_secPull : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ p : Pair φ, p.1.1.1 = φ ⁻¹ᵁ p.1.2.1 → ∀ f : Sec s p.1.2.1 →ₛₗ[algebraMap R R'] Sec s' p.1.1.1, (∀ b, f b = secPull s s' p b) → Function.Bijective (liftSemi f) := by
  intro R R' _ _ _ X X' s s' φ H p hp f hf
  have hUY : p.1.1.1 = φ ⁻¹ᵁ p.1.2.1 ⊓ s' ⁻¹ᵁ ⊤ := by rw [hp]; simp
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := p.1.2.1) (UY := p.1.1.1) le_top le_top hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) p.1.2.2)
  have po' : IsPushout (CommRingCat.ofHom (algebraMap R (Sec s p.1.2.1))) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (secPull s s' p)) (CommRingCat.ofHom (algebraMap R' (Sec s' p.1.1.1))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of R')) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans ((Scheme.ΓSpecIso (.of R)).hom_inv_id_assoc _).symm
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans ((Scheme.ΓSpecIso (.of R')).hom_inv_id_assoc _).symm
  letI : Algebra (Sec s p.1.2.1) (Sec s' p.1.1.1) := (secPull s s' p).toAlgebra
  letI : Algebra R (Sec s' p.1.1.1) := ((algebraMap R' (Sec s' p.1.1.1)).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' p.1.1.1) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R (Sec s p.1.2.1) (Sec s' p.1.1.1) :=
    .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) po'.w).symm
  have h : Algebra.IsPushout R R' (Sec s p.1.2.1) (Sec s' p.1.1.1) :=
    (CommRingCat.isPushout_iff_isPushout.mp po').symm
  have e : ⇑(liftSemi f) = ⇑h.out.equiv := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c v => rw [liftSemi_tmul, h.out.equiv_tmul, hf]; rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [e]
  exact h.out.equiv.bijective

end GlobalTheory.CechDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingEqUniformiserZpowMulUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingEqUniformiserZpowMulUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem DVR.fractionRing_eq_zpow_mul_unit : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (y : FractionRing V), y ≠ 0 → ∃ (v : ℤ) (w : Vˣ), y = algebraMap V (FractionRing V) ϖ ^ v * algebraMap V (FractionRing V) (w : V) := by
  intro V _ _ _ ϖ hϖ y hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by rintro rfl; simp at hy
  obtain ⟨n₁, u₁, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨n₂, u₂, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨(n₁ : ℤ) - n₂, u₁ * u₂⁻¹, ?_⟩
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V)), (IsFractionRing.injective V (FractionRing V)).eq_iff]
    exact hϖ.ne_zero
  have hu : ∀ u : Vˣ, algebraMap V (FractionRing V) (u : V) ≠ 0 := fun u => by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V)), (IsFractionRing.injective V (FractionRing V)).eq_iff]
    exact u.ne_zero
  have h2 := hu u₂
  have h1 := hu u₁
  have key : algebraMap V (FractionRing V) ((u₂⁻¹ : Vˣ) : V) = (algebraMap V (FractionRing V) (u₂ : V))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  simp only [Units.val_mul, map_mul, map_pow, key, zpow_sub₀ hϖ0, zpow_natCast]
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingEqUniformiserZpowMulUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRing_eq_uniformiser_zpow_mul_unit : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (y : FractionRing V), y ≠ 0 → ∃ (v : ℤ) (w : Vˣ), y = algebraMap V (FractionRing V) ϖ ^ v * algebraMap V (FractionRing V) (w : V) := by
  first | exact @GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit | exact GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit | (intros; apply GlobalTheory.DVR.fractionRing_eq_zpow_mul_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescalePsiEvenTauBimultIff
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.QuadIff

variable {R : Type} [CommRing R] [IsDomain R]

def germU (z : (TK R).left) : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
  (gm (𝟙 (TK R).left) z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom.toMonoidHom)

theorem bimult_iff (D : DegPre R) : D.TauBimult ↔ ∀ (a a' b : D.X) z J, Good D.P.L z J →
    val (D.tau (a + a') b) (𝟙 _) z J *
      val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J :=
  ⟨fun h a a' b _ _ hJ => (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a a' b) (𝟙 _)).trans (val_mul hJ _ _ _)),
    fun h a a' b => corr_of_val D.P.isLB fun y J hJ =>
      (val_mul hJ _ _ _).trans ((h a a' b y J hJ).trans (val_mul hJ _ _ _).symm)⟩

theorem val_tau_eq (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_psi_rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (χ : D.X) : val ((rescale D g).psi χ) (𝟙 (TK R).left) z J =
      germU z (g χ) * val (D.psi χ) (𝟙 (TK R).left) z J :=
  GlobalTheory.UU.val_scaleGen (Y := (TK R).left) (L := D.P.L) (unitOn (g χ)) (D.psi χ) (𝟙 _) hJ

theorem val_tau_rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val ((rescale D g).tau a b) (𝟙 (TK R).left) z J =
      germU z (g (a + b)) * (germU z (g a))⁻¹ * (germU z (g b))⁻¹ * val (D.tau a b) (𝟙 (TK R).left) z J := by
  have key : ∀ (A B C p q r s : ((TK R).left.presheaf.stalk z)ˣ),
      A * p * (B * q)⁻¹ * (C * r)⁻¹ * s = A * B⁻¹ * C⁻¹ * (p * q⁻¹ * r⁻¹ * s) := fun A B C p q r s => by
    simp only [_root_.mul_inv]
    ac_rfl
  refine (val_tau_eq (rescale D g) hJ a b).trans (Eq.trans ?_ (congrArg (_ * ·) (val_tau_eq D hJ a b)).symm)
  refine Eq.trans ?_ (key _ _ _ _ _ _ _)
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (val_psi_rescale D g hJ (a + b))
    (congrArg (·⁻¹) (val_psi_rescale D g hJ a))) (congrArg (·⁻¹) (val_psi_rescale D g hJ b))) rfl

end GlobalTheory.PolDeg.QuadIff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelValueProdZpowLocalUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelValueProdZpowLocalUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem RatModel.val_prod_zpow : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z) (z : M.Z), (∀ w, y w ⤳ z) → ∀ {ι : Type} (s : Finset ι) (f : ι → Ω) (m : ι → ℤ), (∀ i, f i ≠ 0 ∧ f i ∈ M.O z ∧ (f i)⁻¹ ∈ M.O z) → M.val y (∏ i ∈ s, f i ^ m i) = ∏ i ∈ s, M.val y (f i) ^ m i := by
  intro o' Ω _ _ _ M K _ y z h ι s f m hf
  have hmem : ∀ i, f i ^ m i ∈ M.O z := by
    intro i
    rcases Int.eq_nat_or_neg (m i) with ⟨n, hn | hn⟩
    · rw [hn, zpow_natCast]; exact pow_mem (hf i).2.1 n
    · rw [hn, zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem (hf i).2.2 n
  have hval : ∀ i, M.val y (f i ^ m i) = M.val y (f i) ^ m i := by
    intro i
    have hinv : M.val y (f i)⁻¹ = (M.val y (f i))⁻¹ := by
      have e := RatModel.val_mul h (hf i).2.1 (hf i).2.2
      rw [mul_inv_cancel₀ (hf i).1, RatModel.val_one] at e
      exact (eq_inv_of_mul_eq_one_right e.symm)
    rcases Int.eq_nat_or_neg (m i) with ⟨n, hn | hn⟩
    · rw [hn, zpow_natCast, zpow_natCast]
      exact map_pow (RatModel.valHomOf y z h) ⟨f i, (hf i).2.1⟩ n
    · rw [hn, zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow, ← inv_pow, ← hinv]
      exact map_pow (RatModel.valHomOf y z h) ⟨(f i)⁻¹, (hf i).2.2⟩ n
  have e := map_prod (RatModel.valHomOf y z h) (fun i => (⟨f i ^ m i, hmem i⟩ : M.O z)) s
  have hc : (↑(∏ i ∈ s, (⟨f i ^ m i, hmem i⟩ : M.O z)) : Ω) = ∏ i ∈ s, f i ^ m i := by
    exact map_prod (M.O z).subtype _ s
  rw [RatModel.valHomOf_apply, hc] at e
  rw [e]
  exact Finset.prod_congr rfl fun i _ => by rw [RatModel.valHomOf_apply]; exact hval i

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelValueProdZpowLocalUnitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralModel_value_prod_zpow_localUnits : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z) (z : M.Z), (∀ w, y w ⤳ z) → ∀ {ι : Type} (s : Finset ι) (f : ι → Ω) (m : ι → ℤ), (∀ i, f i ≠ 0 ∧ f i ∈ M.O z ∧ (f i)⁻¹ ∈ M.O z) → M.val y (∏ i ∈ s, f i ^ m i) = ∏ i ∈ s, M.val y (f i) ^ m i := by
  first | exact @GlobalTheory.Poinc.RatModel.val_prod_zpow | exact GlobalTheory.Poinc.RatModel.val_prod_zpow | (intros; apply GlobalTheory.Poinc.RatModel.val_prod_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenyPairBaseChangeGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenyPairBaseChangeGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem pullQuasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsAbelianScheme B → IsQuasiInv k ψ ψ' → IsGrpPullback A₁ A t φ → ∃ (B₁ : Over T) (_ : GrpObj B₁) (_ : IsCommMonObj B₁) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ ∧ IsGrpPullback B₁ B t θ ∧ IsQuasiInv k ψ₁ ψ₁' ∧ φ ≫ ψ.left = ψ₁.left ≫ θ ∧ θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  intro T Y t A B _ _ _ _ k ψ ψ' A₁ _ _ φ hB hq hA
  obtain ⟨hψ, hψ', h1, h2⟩ := hq
  obtain ⟨e, he, hφ⟩ := grpPullback_iso hA (isGrpPullback_pullback A t)
  have hinv : IsMonHom e.inv := inferInstance
  have hinvφ : e.inv.left ≫ φ = pullback.fst A.hom t := by
    rw [← hφ, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hmap : ∀ (X M : Over Y) [MonObj M] (f : X ⟶ M) (n : ℕ),
      (Over.pullback t).map (f ^ n) = ((Over.pullback t).map f) ^ n := fun X M _ f n => by
    rw [← Functor.homMonoidHom_apply, map_pow, Functor.homMonoidHom_apply]
  have hid : ∀ (M : Over Y) [GrpObj M], (Over.pullback t).map ((𝟙 M) ^ k) = (𝟙 _) ^ k := fun M _ => by
    rw [hmap, CategoryTheory.Functor.map_id]
  refine ⟨(Over.pullback t).obj B, inferInstance, inferInstance, pullback.fst B.hom t,
    e.hom ≫ (Over.pullback t).map ψ, (Over.pullback t).map ψ' ≫ e.inv,
    ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t B hB, isGrpPullback_pullback B t, ⟨inferInstance, inferInstance, ?_, ?_⟩, ?_, ?_⟩
  · calc (e.hom ≫ (Over.pullback t).map ψ) ≫ (Over.pullback t).map ψ' ≫ e.inv
          = e.hom ≫ (Over.pullback t).map (ψ ≫ ψ') ≫ e.inv := by simp
      _ = e.hom ≫ ((𝟙 ((Over.pullback t).obj A)) ^ k) ≫ e.inv := by rw [h1, hid]
      _ = (𝟙 A₁) ^ k := by
        rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, e.hom_inv_id]
  · calc ((Over.pullback t).map ψ' ≫ e.inv) ≫ e.hom ≫ (Over.pullback t).map ψ
          = (Over.pullback t).map (ψ' ≫ ψ) := by simp
      _ = (𝟙 _) ^ k := by rw [h2, hid]
  · rw [Over.comp_left, Category.assoc]
    show φ ≫ ψ.left = e.hom.left ≫ pullback.lift _ _ _ ≫ pullback.fst B.hom t
    rw [pullback.lift_fst, ← Category.assoc, hφ]
  · rw [Over.comp_left, Category.assoc, hinvφ]
    show pullback.fst B.hom t ≫ ψ'.left = pullback.lift _ _ _ ≫ pullback.fst A.hom t
    rw [pullback.lift_fst]

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenyPairBaseChangeGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsAbelianScheme B → IsQuasiInv k ψ ψ' → IsGrpPullback A₁ A t φ → ∃ (B₁ : Over T) (_ : GrpObj B₁) (_ : IsCommMonObj B₁) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ ∧ IsGrpPullback B₁ B t θ ∧ IsQuasiInv k ψ₁ ψ₁' ∧ φ ≫ ψ.left = ψ₁.left ≫ θ ∧ θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.pullQuasiInv) | (exact GlobalTheory.UPel.HT.ES.pullQuasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.pullQuasiInv  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingOnOfMemModelLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingOnOfMemModelLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

noncomputable section
namespace GlobalTheory.Poinc

theorem exists_eq_div_of_mem_O_affine : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z ∈ U, ∀ x ∈ M.O z, ∃ a ∈ M.ringOn (U : Set M.Z), ∃ b ∈ M.ringOn (U : Set M.Z), b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x = a / b := by
  intro o Ω _ _ _ M U hU z hz x hx
  obtain ⟨W, f, hzW, rfl⟩ := hx
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgW, hzg⟩ := hU.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzg⟩
  have := hU.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgW f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, U), M.res _ hg (algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen g) t) = M.res U hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, res_resG, res_apply, ← map_pow, res_apply, res_apply] at h1
  have hu := (isUnit_O_iff _).1 ((isUnit_valF_iff hz g).2 hzg)
  have hb : valF M.pt U (g ^ n) = valF M.pt U g ^ n := by
    rw [← M.res_apply U hne, map_pow, res_apply]
  have h0 : valF M.pt U (g ^ n) ≠ 0 := by
    rw [hb]
    exact pow_ne_zero _ hu.1
  refine ⟨_, (mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _, (mem_ringOn_iff_exists hne).2 ⟨g ^ n, rfl⟩, h0, ?_,
    (eq_div_iff h0).2 h1⟩
  rw [hb, ← inv_pow]
  exact pow_mem hu.2 n

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingOnOfMemModelLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z ∈ U, ∀ x ∈ M.O z, ∃ a ∈ M.ringOn (U : Set M.Z), ∃ b ∈ M.ringOn (U : Set M.Z), b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x = a / b := by
  first | exact @GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine | exact GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine | (intros; apply GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpPowOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.EighthPowerLocal

open GlobalTheory.SS GlobalTheory.CechPic GlobalTheory.MatrixBundle

theorem relAmple_diag_lam {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {B : Over (Sp R)} [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen)
    (ha : Out.RelAmple B M) : Out.RelAmple B ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) := by
  have hlam : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
  let q := Out.powIsPowGrp B 2
  have hG : IsAbelianScheme (Out.powObj B 2) := (PowGrp.powers _ _ B 2 q).2.2.2.1 hB
  let ψ : B ⟶ Out.powObj B 2 := (Out.powIsLimit B 2).lift (Fan.mk B ![𝟙 B, (𝟙 B)⁻¹])
  have hψ : ∀ u, ψ ≫ q.pr u = ![𝟙 B, (𝟙 B)⁻¹] u := fun u => (Out.powIsLimit B 2).fac _ ⟨u⟩
  have hbox : (Out.boxLB M q.pr).IsLB := LB.isLB_linComb hM _ _
  have hfin : IsFinite ψ.left := by
    have := hB.proper
    have := hG.proper
    have : IsSeparated ((q.pr 0).left ≫ B.hom) := by rw [Over.w]; infer_instance
    have : IsSeparated (q.pr 0).left := IsSeparated.of_comp _ B.hom
    have : IsFinite (ψ.left ≫ (q.pr 0).left) := by
      rw [← Over.comp_left, hψ]
      exact inferInstanceAs (IsFinite (𝟙 B.left))
    exact IsFinite.of_comp _ (q.pr 0).left
  have hid : IsFinite (𝟙 B : B ⟶ B).left := inferInstanceAs (IsFinite (𝟙 B.left))
  have a₁ := (relAmple_finite_pow_iso _ B _ ψ _ 1 one_pos hB hG hbox hfin).1
    (relAmple_boxLB _ _ B 2 q M hM ha)
  refine (relAmple_finite_pow_iso _ B B (𝟙 B) _ 1 one_pos hB hB (pull_isLB hbox _) hid).2.2.2 _
    (pull_isLB hlam _) ((cls_eq_iff (pull_isLB hbox _) (pull_isLB hlam _)).1 ?_) a₁
  have h₀ : pull (1 : B ⟶ B).left (cls M hM) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨N, hN, e⟩ := cls_surj (pull (η[B]).left (cls M hM))
    have z : cls N hN = 0 := (cls_eq_zero_iff hN).2 (DVR.exists_gen_of_isLB_local (V := R) N hN)
    rw [← e, z, map_zero]
  have h₁ : cls _ hlam = lam (cls M hM) (fst B B) (snd B B) := cls_cube_two hM _ _ hlam
  have h₂ := lam_mul_left hM hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left, lam.eq_1 _ (𝟙 B)⁻¹, inv_mul_cancel, h₀] at h₂
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_pull hbox, cls_pull hlam, h₁, pull_lam, lift_fst, lift_snd, cls_linComb hM, map_sum, Fin.sum_univ_two,
    one_smul, one_smul, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, hψ, hψ]
  refine Eq.trans ?_ (eq_neg_of_add_eq_zero_left h₂.symm).symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  abel


end GlobalTheory.EighthPowerLocal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiOfSemilinearHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiOfSemilinearHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kaehler_liftSemi_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B') (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B'), (∀ b, f b = α b) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi h.m1) := by
  intro R R' _ _ _ B B' _ _ _ _ α h f hf hb
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  let g : B →ₗ[R] B' := (IsScalarTower.toAlgHom R B B').toLinearMap
  have e1 : ⇑(g.liftBaseChange R') = ⇑(liftSemi f) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [g, hf]; rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  haveI : Algebra.IsPushout R R' B B' :=
    ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective (g.liftBaseChange R') (e1 ▸ hb)) fun n ↦ by simp [g]⟩
  have e2 : ∀ ω : Ω[B⁄R], h.m1 ω = KaehlerDifferential.map R R' B B' ω := by
    intro ω
    have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [SemiHom.m1_D, KaehlerDifferential.map_D]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul b x _ hx =>
      rw [SemiHom.oneFormMap_smul_semilinear, hx, LinearMap.map_smul_of_tower]
      exact algebraMap_smul B' b _
  have e3 : ⇑(liftSemi h.m1) = ⇑(KaehlerDifferential.tensorKaehlerEquivBase R R' B B') := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x ω => rw [liftSemi_tmul, KaehlerDifferential.tensorKaehlerEquivBase_tmul, e2]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [e3]
  exact (KaehlerDifferential.tensorKaehlerEquivBase R R' B B').bijective

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiOfSemilinearHomStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_liftSemi_of_semilinear_hom : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B') (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B'), (∀ b, f b = α b) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi h.m1) := by
  first | exact @GlobalTheory.kaehler_liftSemi_bijective | exact GlobalTheory.kaehler_liftSemi_bijective | (intros; apply GlobalTheory.kaehler_liftSemi_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

namespace GlobalTheory.Points

theorem eq_of_forall_mem_basicOpen_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {z z' : X} (hz : z ∈ U) (hz' : z' ∈ U)
    (h : ∀ f : Γ(X, U), z ∈ X.basicOpen f ↔ z' ∈ X.basicOpen f) : z = z' := by
  have key : ∀ (x : U) (f : Γ(X, U)),
      f ∉ (hU.primeIdealOf x).asIdeal ↔ x.1 ∈ X.basicOpen f := by
    intro x f
    have e1 := hU.fromSpec_primeIdealOf x
    have e2 := hU.fromSpec_preimage_basicOpen f
    have : hU.primeIdealOf x ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x.1 ∈ X.basicOpen f := by
      rw [← e1]; rfl
    rw [← this, e2]; rfl
  have e : hU.primeIdealOf ⟨z, hz⟩ = hU.primeIdealOf ⟨z', hz'⟩ := by
    apply PrimeSpectrum.ext
    ext f
    rw [← not_iff_not, key, key]
    exact h f
  have e1 := hU.fromSpec_primeIdealOf ⟨z, hz⟩
  have e2 := hU.fromSpec_primeIdealOf ⟨z', hz'⟩
  rw [e] at e1
  exact e1.symm.trans e2

theorem point_eq_of_inv_mem_iff :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z z' : M.Z, z ∈ U → z' ∈ U → (∀ a ∈ M.ringOn (U : Set M.Z), a ≠ 0 → (a⁻¹ ∈ M.O z ↔ a⁻¹ ∈ M.O z')) → z = z' := by
  intro o Ω _ _ _ M U hU z z' hz hz' h
  refine eq_of_forall_mem_basicOpen_iff hU hz hz' fun f => ?_
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  have ha : valF M.pt U f ∈ M.ringOn U := (mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩
  rw [← isUnit_valF_iff hz f, ← isUnit_valF_iff hz' f, isUnit_O_iff, isUnit_O_iff]
  exact and_congr_right fun h0 => h _ ha h0

end GlobalTheory.Points
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_affine_point_eq_of_inverse_mem_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z z' : M.Z, z ∈ U → z' ∈ U → (∀ a ∈ M.ringOn (U : Set M.Z), a ≠ 0 → (a⁻¹ ∈ M.O z ↔ a⁻¹ ∈ M.O z')) → z = z' := by
  first | exact @GlobalTheory.Points.point_eq_of_inv_mem_iff | exact GlobalTheory.Points.point_eq_of_inv_mem_iff | (intros; apply GlobalTheory.Points.point_eq_of_inv_mem_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackBaseChangeWithSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackBaseChangeWithSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GrpPB

theorem isGrpPullback_comp {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {P : Over T} [GrpObj P] {f : S' ⟶ S} {t : T ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : P.left ⟶ G'.left}
    (h₁ : IsGrpPullback P G' t ψ) (h₂ : IsGrpPullback G' G f φ) :
    IsGrpPullback P G (t ≫ f) (ψ ≫ φ) := by
  refine ⟨h₁.1.paste_horiz h₂.1, fun T₀ x y x₀ y₀ hx hy => ?_⟩
  have wx : ∀ z : T₀ ⟶ P, (z.left ≫ ψ) ≫ G'.hom = (Over.mk (T₀.hom ≫ t)).hom := fun z => by
    rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w z]; rfl
  let x' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (x.left ≫ ψ) (wx x)
  let y' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (y.left ≫ ψ) (wx y)
  have e₁ : (x' * y').left = (x * y).left ≫ ψ := h₁.2 T₀ x y x' y' rfl rfl
  let e : Over.mk ((Over.mk (T₀.hom ≫ t)).hom ≫ f) ⟶ Over.mk (T₀.hom ≫ t ≫ f) :=
    Over.homMk (𝟙 _) (by simp)
  have e₂ : ((e ≫ x₀) * (e ≫ y₀)).left = (x' * y').left ≫ φ :=
    h₂.2 _ x' y' (e ≫ x₀) (e ≫ y₀) (by simp [e, x', hx]) (by simp [e, y', hy])
  rw [← MonObj.comp_mul, Over.comp_left] at e₂
  simp only [e, Over.homMk_left, Category.id_comp] at e₂
  rw [e₂, e₁, Category.assoc]

theorem baseChange_square {S S' T : Scheme.{0}} (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) (t : T ⟶ S') :
    IsGrpPullback ((Over.pullback t).obj G') G (t ≫ f) (pullback.fst G'.hom t ≫ φ) ∧
      ∃ φ₂ : (G2 ((Over.pullback t).obj G')).left ⟶ (G2 G).left, IsSquare (pullback.fst G'.hom t ≫ φ) φ₂ := by
  have hc := isGrpPullback_comp (isGrpPullback_pullback G' t) h
  refine ⟨hc, ?_⟩
  set P := (Over.pullback t).obj G'
  have w : ∀ q : P ⊗ P ⟶ P, (q.left ≫ pullback.fst G'.hom t ≫ φ) ≫ G.hom = (Over.mk ((P ⊗ P).hom ≫ t ≫ f)).hom :=
    fun q => by
      rw [Category.assoc, Category.assoc, ← Category.assoc _ φ, hc.1.w, ← Category.assoc, Over.w q]; rfl
  let a : Over.mk ((P ⊗ P).hom ≫ t ≫ f) ⟶ G := Over.homMk _ (w (fst P P))
  let b : Over.mk ((P ⊗ P).hom ≫ t ≫ f) ⟶ G := Over.homMk _ (w (snd P P))
  refine ⟨(lift a b).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]; rfl
  · rw [← Over.comp_left, lift_snd]; rfl

end GlobalTheory.GrpPB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackBaseChangeWithSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_baseChange_with_square : ∀ {S S' T : Scheme.{0}} (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ t : T ⟶ S', IsGrpPullback ((Over.pullback t).obj G') G (t ≫ f) (pullback.fst G'.hom t ≫ φ) ∧ ∃ φ₂ : (G2 ((Over.pullback t).obj G')).left ⟶ (G2 G).left, IsSquare (pullback.fst G'.hom t ≫ φ) φ₂ := by
  first | exact @GlobalTheory.GrpPB.baseChange_square | exact GlobalTheory.GrpPB.baseChange_square | (intros; apply GlobalTheory.GrpPB.baseChange_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyRestrictAdjointBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyRestrictAdjointBijective
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjHyp

def counitCoef {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) {G : C' ⥤ C} {H : C ⥤ C'} (adj : G ⊣ H) :
    CoefMap (RingHom.id R) (G ⋙ F) F where
  G := H
  α V := (mp F (adj.counit.app V)).toRingHom
  naturality {V V'} φ b := by
    change mp F (adj.counit.app V') (mp F (G.map (H.map φ)) b) = mp F φ (mp F (adj.counit.app V) b)
    rw [← mp_comp, ← mp_comp]
    have e := adj.counit.naturality φ
    simp only [Functor.comp_map, Functor.id_map] at e
    rw [e]
  smul V r b := by
    change mp F (adj.counit.app V) (r • b) = r • mp F (adj.counit.app V) b
    exact map_smul _ r b

theorem main : ∀ (R : Type) [CommRing R] (C C' : Type) [Category.{0} C] [Category.{0} C']
    (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C'), (G ⊣ H) →
    Function.Bijective (pullHyp1 (CoefMap.restrict F G)) := by
  intro R _ C C' _ _ F G H adj
  have hl : ∀ c, pullHyp1 (counitCoef F adj) (pullHyp1 (CoefMap.restrict F G) c) = c := by
    intro c
    rw [← pullHyp1_comp]
    exact (pullHyp1_eq_of_natTrans _ (CoefMap.id F) adj.counit (fun T b ↦ rfl) c).trans
      (pullHyp1_id c)
  have hr : ∀ c, pullHyp1 (CoefMap.restrict F G) (pullHyp1 (counitCoef F adj) c) = c := by
    intro c
    rw [← pullHyp1_comp]
    refine ((pullHyp1_eq_of_natTrans (CoefMap.id (G ⋙ F))
      ((counitCoef F adj).comp (CoefMap.restrict F G)) adj.unit (fun T b ↦ ?_) c).symm.trans
      (pullHyp1_id c))
    change mp F (adj.counit.app (G.obj T)) (mp F (G.map (adj.unit.app T)) b) = b
    exact (mp_comp F (G.map (adj.unit.app T)) (adj.counit.app (G.obj T)) b).symm.trans
      ((congrArg (fun ξ ↦ mp F ξ b) (adj.left_triangle_components T)).trans (mp_id F (G.obj T) b))
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

end GlobalTheory.AdjHyp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperCohomologyRestrictAdjointBijectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyper_cohomology_restrict_adjoint_bijective : ∀ (R : Type) [CommRing R] (C C' : Type) [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C'), (G ⊣ H) → Function.Bijective (pullHyp1 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.AdjHyp.main | exact GlobalTheory.AdjHyp.main | (intros; apply GlobalTheory.AdjHyp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtTrans

theorem ptTrans : ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (K : Type) [Field K] [Algebra (FractionRing V) K] [Algebra (FractionRing V') K] (A : PolAV (Sp (FractionRing V))) (A' : PolAV (Sp (FractionRing V'))) (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ A.A.left) (a' : P₀.A.left ⟶ A'.A.left), IsGrpPullback P₀.A A.A (spMap (algebraMap (FractionRing V) K)) a → IsGrpPullback P₀.A A'.A (spMap (algebraMap (FractionRing V') K)) a' → ∀ (m : ℕ) (x : TFK (R := V) K ⟶ A.A), x ^ m = 1 → ∃ (w : Sp K ⟶ P₀.A.left) (x' : TFK (R := V') K ⟶ A'.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x' ^ m = 1 := by
  intro V V' _ _ _ _ K _ _ _ A A' P₀ a a' h h' m x hx
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let e : TFK (R := V) K ⟶ Over.mk (T.hom ≫ spMap (algebraMap (FractionRing V) K)) :=
    Over.homMk (𝟙 _) (by simp [T])
  let e' : TFK (R := V') K ⟶ Over.mk (T.hom ≫ spMap (algebraMap (FractionRing V') K)) :=
    Over.homMk (𝟙 _) (by simp [T])
  let Φ : (T ⟶ P₀.A) →* (TFK (R := V) K ⟶ A.A) := (preHom e).comp (pushHom h T)
  let Φ' : (T ⟶ P₀.A) →* (TFK (R := V') K ⟶ A'.A) := (preHom e').comp (pushHom h' T)
  have hΦ : ∀ u : T ⟶ P₀.A, (Φ u).left = u.left ≫ a := fun u => by
    simp [Φ, e, preHom, pushHom, pushPt]
  have hΦ' : ∀ u : T ⟶ P₀.A, (Φ' u).left = u.left ≫ a' := fun u => by
    simp [Φ', e', preHom, pushHom, pushPt]
  have inj : Function.Injective Φ := fun u v huv => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← hΦ, ← hΦ, huv]
    · rw [Over.w u, Over.w v]
  have hsq : x.left ≫ A.A.hom = 𝟙 (Sp K) ≫ spMap (algebraMap (FractionRing V) K) := by
    rw [Over.w x, Category.id_comp]; rfl
  let w : T ⟶ P₀.A := Over.homMk (h.1.lift x.left (𝟙 _) hsq) (by simp [T])
  have hw : Φ w = x := by
    apply Over.OverMorphism.ext
    rw [hΦ]
    simp [w]
  have hwm : w ^ m = 1 := by
    apply inj
    rw [map_pow, hw, hx, map_one]
  refine ⟨w.left, Φ' w, ?_, ?_, ?_, ?_⟩
  · simpa [T] using Over.w w
  · rw [← hΦ, hw]
  · rw [hΦ']
  · rw [← map_pow, hwm, map_one]

end GlobalTheory.PtTrans
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback : ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (K : Type) [Field K] [Algebra (FractionRing V) K] [Algebra (FractionRing V') K] (A : PolAV (Sp (FractionRing V))) (A' : PolAV (Sp (FractionRing V'))) (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ A.A.left) (a' : P₀.A.left ⟶ A'.A.left), IsGrpPullback P₀.A A.A (spMap (algebraMap (FractionRing V) K)) a → IsGrpPullback P₀.A A'.A (spMap (algebraMap (FractionRing V') K)) a' → ∀ (m : ℕ) (x : TFK (R := V) K ⟶ A.A), x ^ m = 1 → ∃ (w : Sp K ⟶ P₀.A.left) (x' : TFK (R := V') K ⟶ A'.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x' ^ m = 1 := by
  first | exact @GlobalTheory.PtTrans.ptTrans | exact GlobalTheory.PtTrans.ptTrans | (intros; apply GlobalTheory.PtTrans.ptTrans <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserZpowMulUnitExponentUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserZpowMulUnitExponentUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem exponent_uniformiser_unique {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {ϖ : V} (hϖ : Irreducible ϖ) (a b : ℤ) (w w' : Vˣ)
    (h : algebraMap V (FractionRing V) ϖ ^ a * algebraMap V (FractionRing V) (w : V) =
      algebraMap V (FractionRing V) ϖ ^ b * algebraMap V (FractionRing V) (w' : V)) : a = b := by
  have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  have hx : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hϖ.ne_zero
  have hw : algebraMap V (FractionRing V) (w : V) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact w.ne_zero
  have key : ∀ (n : ℕ) (u : Vˣ), algebraMap V (FractionRing V) ϖ ^ n =
      algebraMap V (FractionRing V) (u : V) → n = 0 := by
    intro n u hn
    rw [← map_pow] at hn
    have h1 := hinj hn
    by_contra hne
    apply hϖ.not_isUnit
    rw [← isUnit_pow_iff hne, h1]; exact u.isUnit
  have hab : algebraMap V (FractionRing V) ϖ ^ (a - b) =
      algebraMap V (FractionRing V) ((w' * w⁻¹ : Vˣ) : V) := by
    rw [zpow_sub₀ hx, Units.val_mul, map_mul, map_units_inv, div_eq_iff (zpow_ne_zero _ hx)]
    field_simp
    linear_combination h
  rcases Int.eq_nat_or_neg (a - b) with ⟨n, hn | hn⟩
  · rw [hn, zpow_natCast] at hab
    have := key n _ hab
    omega
  · rw [hn, zpow_neg, zpow_natCast] at hab
    have h2 : algebraMap V (FractionRing V) ϖ ^ n =
        algebraMap V (FractionRing V) (((w' * w⁻¹)⁻¹ : Vˣ) : V) := by
      rw [map_units_inv, ← hab, inv_inv]
    have := key n _ h2
    omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserZpowMulUnitExponentUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (a b : ℤ) (w w' : Vˣ), algebraMap V (FractionRing V) ϖ ^ a * algebraMap V (FractionRing V) (w : V) = algebraMap V (FractionRing V) ϖ ^ b * algebraMap V (FractionRing V) (w' : V) → a = b := by
  first | exact @GlobalTheory.exponent_uniformiser_unique | exact GlobalTheory.exponent_uniformiser_unique | (intros; apply GlobalTheory.exponent_uniformiser_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TorusExt

open GlobalTheory.BXOf ReciprocityTheory.ChartRestriction.G.DVR

theorem gtExt_eq_self_of_charVal_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : F →+* F) (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F) (g : GtPtF D F), spMap σ ≫ g.b.left = g.b.left → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → GlobalTheory.TorusExt.gtExt D σ hσ g = g := by
  intro R _ _ D F _ _ σ hσ g hb J hJ hfix
  have hb' : extMap σ hσ ≫ g.b = g.b := Over.OverMorphism.ext hb
  have hφ0 : ∀ χ k, Spec.map (CommRingCat.ofHom σ) ≫ DegPre.gtφ D F g.b χ k = DegPre.gtφ D F g.b χ k := by
    intro χ k
    show (extMap σ hσ).left ≫ DegPre.gtφ D F g.b χ k = DegPre.gtφ D F g.b χ k
    fin_cases k
    · show (extMap σ hσ ≫ (cP D _ χ * g.b)).left = (cP D _ χ * g.b).left
      rw [MonObj.comp_mul, comp_cP, hb']
    · show (extMap σ hσ ≫ cP D _ χ).left = (cP D _ χ).left
      rw [comp_cP]
    · show (extMap σ hσ ≫ g.b).left = g.b.left
      rw [hb']
    · show (extMap σ hσ ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left
      rw [MonObj.comp_one]
  refine gt_ext_val ((gtExt_b σ hσ g).trans hb') fun χ y J' hJ' => ?_
  obtain rfl : y = closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hdel : ∀ ψ : Spec (CommRingCat.of F) ⟶ D.P.A.left, Spec.map (CommRingCat.ofHom σ) ≫ ψ = ψ →
      GlobalTheory.BXOf.del D.P.L σ J J' ψ = GlobalTheory.BXOf.del D.P.L (RingHom.id F) J J' ψ := by
    intro ψ h
    unfold GlobalTheory.BXOf.del
    rw [h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have e₁ := val_nat (g.isGen χ) σ hJ hJ' (𝟙 _)
  have e₂ := val_nat (g.isGen χ) (RingHom.id F) hJ hJ' (𝟙 _)
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at e₂
  have hu : Units.map σ.toMonoidHom (sig F (charVal g χ (closedPoint F) J)) = sig F (charVal g χ (closedPoint F) J) :=
    Units.ext (hfix χ)
  have hu' : Units.map (RingHom.id F).toMonoidHom (sig F (charVal g χ (closedPoint F) J)) =
      sig F (charVal g χ (closedPoint F) J) := Units.ext rfl
  have key : sig F (charVal (gtExt D σ hσ g) χ (closedPoint F) J') = sig F (charVal g χ (closedPoint F) J') := by
    rw [gtExt_val σ hσ g χ hJ', extMap_left, ← Category.comp_id (spMap σ)]
    refine e₁.trans (Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ DegPre.gtε k)
      (hdel _ ((congrArg _ (Category.id_comp _)).trans ((hφ0 χ k).trans (Category.id_comp _).symm))))
      (hu.trans hu'.symm)) e₂.symm)
  exact Units.map_injective (f := (stalkClosedPointIso (CommRingCat.of F)).hom.hom.toMonoidHom)
    (stalkClosedPointIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective key

end GlobalTheory.TorusExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : F →+* F) (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F) (g : GtPtF D F), spMap σ ≫ g.b.left = g.b.left → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → GlobalTheory.TorusExt.gtExt D σ hσ g = g := by
  first | exact @GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed | exact GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed | (intros; apply GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingEssFiniteTypeInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingEssFiniteTypeInt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

theorem essFiniteType_int_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  intro o Ω _ _ _ hA M x
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o := M.s x
  letI A : Algebra o ((Sp o).presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o _ ((Sp o).presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o ((Sp o).presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o := hA.ft
  have h₀ : (algebraMap ℤ o).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h₃ : (M.stalkEquiv x).toRingHom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ (M.stalkEquiv x).surjective).essFiniteType
  have h := ((h₀.comp h₂).comp h₁)
  have h' := h.comp h₃
  rw [← RingHom.essFiniteType_algebraMap]
  convert h'
  exact RingHom.ext_int _ _

end GlobalTheory.Izumi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingEssFiniteTypeIntStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelLocalRing_essFiniteType_int : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  first | exact @GlobalTheory.Izumi.essFiniteType_int_O | exact GlobalTheory.Izumi.essFiniteType_int_O | (intros; apply GlobalTheory.Izumi.essFiniteType_int_O <;> assumption)
end
end
