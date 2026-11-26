module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPairQuotientHorizontalGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.IdemImage

theorem isSemiAbelian_image : ∀ (S : Scheme.{0}) (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ e : G' ⟶ G', IsMonHom e → e ≫ e = e → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (inc : G ⟶ G') (pr : G' ⟶ G), IsSemiAbelian G ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G ∧ pr ≫ inc = e := by
  intro S G' _ _ hG e he hee
  have hsm : GlobalTheory.SS.SmConn G' :=
    ⟨hG.comm, hG.smooth, hG.separated, hG.quasiCompact, hG.geomConnected⟩
  obtain ⟨G, hgrp, inc, pr, hG₁, hinc, hpr, hip, hpi⟩ :=
    GlobalTheory.SS.smConn_idempotent_splits S G' hsm e he hee
  exact ⟨G, hgrp, hG₁.1, inc, pr,
    GlobalTheory.SS.isSemiAbelian_of_retract S G' G hG hG₁ inc pr hpr hip, hinc, hpr, hip, hpi⟩

end GlobalTheory.Mum.IdemImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.TauCoordQuot

open GlobalTheory.PsiTauCoordRel GlobalTheory.PeriodBalance

theorem gm_psi {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
    (ξ : Spec (CommRingCat.of (FractionRing R))) (χ : D.X) (j : PUnit → D.P.L.ι)
    (hj : IsIntChart D (D.c χ) (j PUnit.unit)) (x : (FractionRing R)ˣ) (hx : IsPsiCoord D χ x) :
    ∃ u : Rˣ, gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) =
      Units.map (kst ξ).toMonoidHom (Units.map (algebraMap R (FractionRing R)).toMonoidHom u * x) := by
  have h : ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j :=
    fun y _ => Set.mem_iInter.2 fun _ => hj (Set.mem_univ (jK R y))
  obtain ⟨u, hu⟩ := IsPsiCoord.unique (⟨j, h, hj, rfl⟩ : IsPsiCoord D χ (genVal (D.psi χ) j h)) hx
  refine ⟨u, ?_⟩
  rw [← hu]
  exact Units.ext (gm_genVal ξ (D.psi χ) j h)

theorem alg_quot {A B C : Type} [CommGroup A] [CommGroup B] [CommGroup C] (k : B →* C) (f : A →* B)
    (c1 c2 c3 c4 : A) (x₁ x₂ x₃ : B) :
    k (f c1 * x₁) * (k (f c2 * x₂))⁻¹ * (k (f c3 * x₃))⁻¹ * (k (f c4))⁻¹ =
      k (f (c1 * c2⁻¹ * c3⁻¹ * c4⁻¹) * x₁ * x₂⁻¹ * x₃⁻¹) := by
  simp only [map_mul, map_inv, mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X)
    (x x₁ x₂ x₃ : (FractionRing R)ˣ), IsTauCoord D a b x → IsPsiCoord D (a + b) x₁ → IsPsiCoord D a x₂ →
      IsPsiCoord D b x₃ → ∃ u : Rˣ, (x : FractionRing R) =
        algebraMap R (FractionRing R) u * x₁ * (x₂ : FractionRing R)⁻¹ * (x₃ : FractionRing R)⁻¹ := by
  intro R _ _ _ D a b x x₁ x₂ x₃ hx h₁ h₂ h₃
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom
  let aU : Rˣ →* (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom
  obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
  have hm := h (show ξ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
  have eT := gm_genVal ξ (D.tau a b) j h
  have dT : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) = _ := gm_mulGen _ _ ξ j hm
  rw [gm_mulGen _ _ ξ _ (mem_inl hm), gm_mulGen _ _ ξ _ (mem_inl (mem_inl hm)), gm_invGen, gm_invGen,
    gm_invGen] at dT
  obtain ⟨c1, g1⟩ := gm_psi D ξ (a + b) (((j ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inl) i1 x₁ h₁
  obtain ⟨c2, g2⟩ := gm_psi D ξ a (((j ∘ Sum.inl) ∘ Sum.inl) ∘ Sum.inr) i2 x₂ h₂
  obtain ⟨c3, g3⟩ := gm_psi D ξ b ((j ∘ Sum.inl) ∘ Sum.inr) i3 x₃ h₃
  obtain ⟨c4, g4⟩ := gm_rigK D ξ (j ∘ Sum.inr) i4 (mem_inr hm)
  have g4' : gm (𝟙 _) ξ (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A) (j ∘ Sum.inr))
      (D.rigK.s (j ∘ Sum.inr)) = kU (aU c4) := g4
  have eT' : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.tau a b).s j) =
      kU (genVal (D.tau a b) j h) := Units.ext eT
  have key : kU (genVal (D.tau a b) j h) =
      kU (aU c1 * x₁) * (kU (aU c2 * x₂))⁻¹ * (kU (aU c3 * x₃))⁻¹ * (kU (aU c4))⁻¹ :=
    eT'.symm.trans (dT.trans (by rw [g1, g2, g3, g4']))
  have key2 : genVal (D.tau a b) j h = aU (c1 * c2⁻¹ * c3⁻¹ * c4⁻¹) * x₁ * x₂⁻¹ * x₃⁻¹ := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    exact key.trans (alg_quot kU aU c1 c2 c3 c4 x₁ x₂ x₃)
  refine ⟨c1 * c2⁻¹ * c3⁻¹ * c4⁻¹, ?_⟩
  rw [key2, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  rfl

end GlobalTheory.TauCoordQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotientStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tauCoordinate_eq_unit_mul_psi_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X)
    (x x₁ x₂ x₃ : (FractionRing R)ˣ), IsTauCoord D a b x → IsPsiCoord D (a + b) x₁ → IsPsiCoord D a x₂ →
      IsPsiCoord D b x₃ → ∃ u : Rˣ, (x : FractionRing R) =
        algebraMap R (FractionRing R) u * x₁ * (x₂ : FractionRing R)⁻¹ * (x₃ : FractionRing R)⁻¹ := by
  first | exact @GlobalTheory.TauCoordQuot.main | exact GlobalTheory.TauCoordQuot.main | (intros; apply GlobalTheory.TauCoordQuot.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DivDeep

open GlobalTheory.ThetaCompare

theorem torsFrame_two_levels {S : Scheme.{0}} (P : PolAV S) {T : Over S} {m M : ℕ}
    {rig rig' : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} {τ τ'} (H : IsTorsFrame P rig m x τ)
    (H' : IsTorsFrame P rig' M x τ') {y : T.left} {J} (hJ : Good P.L y J) :
    (val τ (𝟙 _) y J / val τ' (𝟙 _) y J) ^ (m ^ 2 * M ^ 2) =
      (val rig T.hom y J / val rig' T.hom y J) ^ (m ^ 2 * M ^ 2) := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P m T
  obtain ⟨β, hβ⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P M T
  have a := torsFrame_pow hG P hα H hJ
  have b := torsFrame_pow hG P hβ H' hJ
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  have rβ := Reg.two (y := y) (J := J) β hβ (snd T P.A) (snd T P.A ^ M) rfl rfl
  have c := (((rα.pow hJ (M ^ 2)).mul hJ (rβ.pull hJ (snd T P.A ^ m))).mul hJ
    ((rβ.pow hJ (m ^ 2)).mul hJ (rα.pull hJ (snd T P.A ^ M))).inv).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, ← pow_mul, mul_comm M m]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) x 1
  simp only [SymLiftOdd.comp_pow', pt_snd, H.1, H'.1, one_pow] at c
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div] at a b c ⊢
  linear_combination (norm := module) (M ^ 2) • a - (m ^ 2) • b + c

theorem exists_cst {K : Type} [Field K] (z : Sp K) : ∃ c : K →+* (Sp K).presheaf.stalk z, Function.Injective c ∧
    ∀ a, gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = c a :=
  ⟨((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom, RingHom.injective _,
    fun _ => gs_eq (𝟙 _) z ⊤ trivial _⟩

theorem same_ratio {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ε} {ρ' : S'.Real} {ε'} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
    (h : Same ρ ε ρ' ε' lab φ) (a b : S.Gam) :
    ∃ k, 0 < k ∧ (S'.th (lab a) * φ (S.th b)) ^ k = (S'.th (lab b) * φ (S.th a)) ^ k := by
  obtain ⟨P₀, f, f', -, gp, gp', lb, lb', -, hw⟩ := h
  choose w hw hw' using hw
  have hs : ∀ x, w x ≫ P₀.A.hom = 𝟙 _ := fun x => by
    have e : (w x ≫ P₀.A.hom) ≫ spMap S'.R.val.toRingHom = 𝟙 _ ≫ spMap S'.R.val.toRingHom := by
      rw [Category.assoc, ← gp'.1.w, ← Category.assoc, hw', Category.assoc, Over.w, Category.id_comp]
      exact Category.comp_id _
    haveI : IsFractionRing S'.R Ω' := IsFractionRing.of_field _ _ fun x => by
      obtain ⟨a, ha, b, hb, e⟩ := S'.frac x
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
    haveI : IsPreimmersion (spMap S'.R.val.toRingHom) :=
      IsPreimmersion.of_isLocalization (R := S'.R) (S := Ω') (nonZeroDivisors S'.R)
    exact (cancel_mono _).1 e
  let x : S.Gam → (baseOver (Sp Ω') ⟶ P₀.A) := fun a => Over.homMk (w a) (hs a)
  obtain ⟨rig, τ, -, hτ, ht⟩ := FrameMove.exists_move (T := baseOver (Sp S.R)) (T' := baseOver (Sp Ω'))
    (h := spMap (φ.comp S.R.val.toRingHom)) gp lb ((Category.comp_id _).trans (Category.id_comp _).symm) ρ.rig_gen
    (x := ρ.pt) (x' := x) hw ρ.fr_tors
  obtain ⟨rig', τ', -, hτ', ht'⟩ := FrameMove.exists_move (T := baseOver (Sp S'.R)) (T' := baseOver (Sp Ω'))
    (h := spMap S'.R.val.toRingHom) gp' lb' ((Category.comp_id _).trans (Category.id_comp _).symm) ρ'.rig_gen
    (x := fun a => ρ'.pt (lab a)) (x' := x) hw' (fun a => ρ'.fr_tors (lab a))
  obtain ⟨t, ht⟩ := ht 1 ρ.th₁
  obtain ⟨t', ht'⟩ := ht' 1 ρ'.th₁
  let z : Sp Ω' := IsLocalRing.closedPoint Ω'
  obtain ⟨V, hV, hθ⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny P₀ z
  obtain ⟨θ, hθ⟩ := hθ Ω' (𝟙 _) (by rintro _ ⟨v, rfl⟩; rw [Subsingleton.elim v z]; exact hV)
  obtain ⟨r, hr⟩ := hθ t
  obtain ⟨r', hr'⟩ := hθ t'
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' (Z := (baseOver (Sp Ω')).left) P₀.isLB z
  obtain ⟨c, hc, hcv⟩ : ∃ c : Ω' →+* (baseOver (Sp Ω')).left.presheaf.stalk z, Function.Injective c ∧
      ∀ a, gs (𝟙 (Sp Ω')) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom a) = c a := exists_cst z
  have pf : ∀ {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
      (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))),
      powFrame A L x τ 1 = τ := fun x τ => congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))
  have v : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r * sval (L := P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left)
      (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (φ (S.th a)) * (val (τ a) (𝟙 _) z J).val := fun a => by
    have e := (sval_smul hr (x a) hJ).symm.trans (ht a _ (by rw [pf]; exact ρ.th_val a) z J hJ)
    rw [pf] at e
    exact e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))
  have v' : ∀ a, gs (𝟙 (baseOver (Sp Ω')).left) z ⊤ r' * sval (L := P₀.L) (φ := fun _ : Fin 1 => (snd (baseOver (Sp Ω')) P₀.A).left)
      (ε := fun _ => 1) θ (ptSecT P₀.A (x a)).left z J = c (S'.th (lab a)) * (val (τ' a) (𝟙 _) z J).val := fun a => by
    have e := (sval_smul hr' (x a) hJ).symm.trans (ht' a _ (by rw [pf]; exact ρ'.th_val (lab a)) z J hJ)
    rw [pf] at e
    exact e.trans (congrArg (· * _) ((FrameMove.gs_spMap _ z _).trans (hcv _)))
  have q := (torsFrame_two_levels P₀ (hτ a) (hτ' a) hJ).trans (torsFrame_two_levels P₀ (hτ b) (hτ' b) hJ).symm
  have p₁ : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have p₂ : 0 < S'.r * S'.N := Nat.mul_pos S'.r_pos (by have := S'.N_ge; omega)
  refine ⟨(S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2, by positivity, hc ?_⟩
  generalize (S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2 = k at q
  have va := v a
  have vb := v b
  have va' := v' a
  have vb' := v' b
  generalize val (τ a) (𝟙 _) z J = ua at *
  generalize val (τ b) (𝟙 _) z J = ub at *
  generalize val (τ' a) (𝟙 _) z J = ua' at *
  generalize val (τ' b) (𝟙 _) z J = ub' at *
  have e : c (S'.th (lab a) * φ (S.th b)) * (ua' * ub).val = c (S'.th (lab b) * φ (S.th a)) * (ub' * ua).val := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm, ← va', ← vb, _root_.mul_mul_mul_comm (c _), ← vb', ← va]
    ring
  have q' : (ua' * ub) ^ k = (ub' * ua) ^ k := by
    apply Additive.ofMul.injective
    replace q := congrArg Additive.ofMul q
    simp only [ofMul_mul, ofMul_pow, ofMul_div] at q ⊢
    linear_combination (norm := module) -q
  have e' := congrArg (· ^ k) e
  simp only [mul_pow, ← Units.val_pow_eq_pow_val, q'] at e'
  rw [map_pow, map_pow]
  exact (Units.mul_left_inj _).1 e'

end GlobalTheory.Poinc.DivDeep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

theorem exists_objMap_cancel_φ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) : ∃ m₁ : ObjMap o₁ o₂ f, m₁.φ ≫ m₂.φ = m.φ := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := MapComp.exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := MapComp.isSquare_unique m.sq (hφ ▸ MapComp.isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (MapComp.lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }, hφ⟩

theorem classify_equivariant : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
  (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)), HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
  ∀ (ρ : sympSimGrp h M → (X ⟶ X)), SympActs s s₁ u lev ρ →
  ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)), (∀ a, ρ a ≫ s₁ = s₁ ≫ spMap (σ a)) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M))
    (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)) (o' : Obj b N (Y.hom ≫ t)) (m : ObjMap o' o Y.hom)
    (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y.left) ⟶ o'.A)), (∀ a, (lv' a).left ≫ m.φ = (lu a).left) →
    (∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv')) →
    ∀ (y : Y.left ⟶ X) (my : ObjMap o' u y), (∀ a, (lv' a).left ≫ my.φ = y ≫ (lev a).left) →
    y ≫ s = Y.hom ≫ t → y ≫ s₁ = t₁ →
    ∀ (r : sympSimGrp h M → (Y ⟶ Y)), (∀ a, (r a).left ≫ t₁ = t₁ ≫ spMap (σ a)) →
    (∀ a c, r a ≫ lu c = sympTwist a lu c) → ∀ a, (r a).left ≫ y = y ≫ ρ a := by
  intro p _ D R _ b N h M X s s₁ u lev hU ρ hρ σ hσ S t o Y t₁ lu o' m lv' hlv' hlev y my hmy hys hys₁ r hrt hr a
  let compObj : ∀ {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
      {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃},
      ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → ObjMap o₁ o₃ (f ≫ g) := by
    intro S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₁ m₂
    exact { φ := m₁.φ ≫ m₂.φ
            φ₂ := m₁.φ₂ ≫ m₂.φ₂
            cart := m₁.cart.comp m₂.cart
            sq := MapComp.isSquare_comp m₁.sq m₂.sq
            act := fun c => by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
            pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol
              (MapComp.lbIso_pull_comp m₂.pol m₁.φ₂ rfl)
            eta := fun c => by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc] }
  have cast : ∀ {f f' : Y.left ⟶ S} (_ : f = f') (m₀ : ObjMap o' o f), ∃ m' : ObjMap o' o f', m'.φ = m₀.φ := by
    intro f f' e m₀; subst e; exact ⟨m₀, rfl⟩
  have hrY : (r a).left ≫ Y.hom = Y.hom := Over.w (r a)
  obtain ⟨ma, hma⟩ := (hρ a).2.2

  have h₁ : (y ≫ ρ a) ≫ s = Y.hom ≫ t ∧ (y ≫ ρ a) ≫ s₁ = t₁ ≫ spMap (σ a) ∧
      ∃ m' : ObjMap o' u (y ≫ ρ a), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = (y ≫ ρ a) ≫ (lev c).left := by
    refine ⟨by rw [Category.assoc, (hρ a).1, hys], by rw [Category.assoc, hσ, ← Category.assoc, hys₁],
      compObj my ma, fun c => ?_⟩
    have e₁ := hmy (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M c)))
    have e₂ := hma c
    simp only [sympTwist] at e₂ ⊢
    dsimp [compObj]
    change _ ≫ my.φ ≫ ma.φ = _
    rw [← Category.assoc, e₁, Category.assoc, e₂, Category.assoc]

  obtain ⟨mr, hmr⟩ := cast hrY.symm m
  obtain ⟨m₂, hφ⟩ := exists_objMap_cancel_φ mr m
  rw [hmr] at hφ
  have hpull : ∀ c, (sympTwist a lv' c).left ≫ m₂.φ = (r a).left ≫ (lv' c).left := by
    intro c
    apply m.cart.1.hom_ext
    · rw [Category.assoc, hφ, Category.assoc, hlv' c]
      simp only [sympTwist] at hlv' ⊢
      rw [hlv', ← Over.comp_left, hr a c]
      rfl
    · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, Over.w (sympTwist a lv' c), Category.assoc,
        Over.w (lv' c)]
      simp
  have h₂ : ((r a).left ≫ y) ≫ s = Y.hom ≫ t ∧ ((r a).left ≫ y) ≫ s₁ = t₁ ≫ spMap (σ a) ∧
      ∃ m' : ObjMap o' u ((r a).left ≫ y), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = ((r a).left ≫ y) ≫ (lev c).left := by
    refine ⟨by rw [Category.assoc, hys, ← Category.assoc, hrY], by rw [Category.assoc, hys₁, hrt],
      compObj m₂ my, fun c => ?_⟩
    dsimp [compObj]
    change _ ≫ m₂.φ ≫ my.φ = _
    rw [← Category.assoc, hpull c, Category.assoc, hmy c, Category.assoc]
  exact (hU Y.left (Y.hom ≫ t) (t₁ ≫ spMap (σ a)) o' (sympTwist a lv') (hlev a)).unique h₂ h₁

end GlobalTheory.HTSympCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classifyingMap_symplecticLevel_equivariant : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
  (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)), HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
  ∀ (ρ : sympSimGrp h M → (X ⟶ X)), SympActs s s₁ u lev ρ →
  ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)), (∀ a, ρ a ≫ s₁ = s₁ ≫ spMap (σ a)) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M))
    (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)) (o' : Obj b N (Y.hom ≫ t)) (m : ObjMap o' o Y.hom)
    (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y.left) ⟶ o'.A)), (∀ a, (lv' a).left ≫ m.φ = (lu a).left) →
    (∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv')) →
    ∀ (y : Y.left ⟶ X) (my : ObjMap o' u y), (∀ a, (lv' a).left ≫ my.φ = y ≫ (lev a).left) →
    y ≫ s = Y.hom ≫ t → y ≫ s₁ = t₁ →
    ∀ (r : sympSimGrp h M → (Y ⟶ Y)), (∀ a, (r a).left ≫ t₁ = t₁ ≫ spMap (σ a)) →
    (∀ a c, r a ≫ lu c = sympTwist a lu c) → ∀ a, (r a).left ≫ y = y ≫ ρ a := by
  first | exact @GlobalTheory.HTSympCover.classify_equivariant | exact GlobalTheory.HTSympCover.classify_equivariant | (intros; apply GlobalTheory.HTSympCover.classify_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

def SameAt {R₁ R₂ B M Γ : Type} [CommRing R₁] [CommRing R₂] [CommRing B] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂))
    (f₁ : R₁ →+* B) (f₂ : R₂ →+* B) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A))
    (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)) : Prop :=
  ∃ (P : PolAV (Sp B)) (a₁ : P.A.left ⟶ P₁.A.left) (a₂ : P.A.left ⟶ P₂.A.left),
    IsGrpPullback P.A P₁.A (spMap f₁) a₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) a₂ ∧
    LBIso P.L (P₁.L.pull a₁) ∧ LBIso P.L (P₂.L.pull a₂) ∧
    (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ a₁ = a₁ ≫ (e₁ E).left ∧ e.left ≫ a₂ = a₂ ≫ (e₂ E).left) ∧
    ∀ x, ∃ w : Sp B ⟶ P.A.left, w ≫ a₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ a₂ = spMap f₂ ≫ (t₂ x).left

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLab
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

def Deep.GalLab (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam) : Prop :=
  ∃ (P₀ : PolAV (Sp D.X.Ω₁)) (b : P₀.A.left ⟶ D.X.ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left)
    (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)),
    IsGrpPullback P₀.A D.X.ρ.P.A (spMap D.X.S.R.val.toRingHom) b ∧
    IsGrpPullback P₀.A P₀.A (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) t ∧
    LBIso P₀.L (D.X.ρ.P.L.pull b) ∧ LBIso P₀.L (P₀.L.pull t) ∧
    (∀ E, (ε₀ E).left ≫ b = b ≫ (D.ε E).left ∧ (ε₀ E).left ≫ t = t ≫ (ε₀ E).left) ∧
    ∀ x (w w' : Sp D.X.Ω₁ ⟶ P₀.A.left), w ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left →
      w' ≫ t = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w →
        w' ≫ b = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt (a x)).left

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isSemiAbelian_of_isGrpPullback_square : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S')
    [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → IsSemiAbelian G → IsSemiAbelian G' := by
  intro S S' f G _ G' _ F h hG
  have := hG.comm
  have : IsCommMonObj G' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback h
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemiAbelian_of_isGrpPullback_divisor : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → IsSemiAbelian G → IsSemiAbelian G' := by
  first | exact @GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square | exact GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square | (intros; apply GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem app_bijective_of_flat_baseChange : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R)
    (p : Z ⟶ Y) (q : Z ⟶ S), QuasiCompact π → QuasiSeparated π → Function.Bijective π.appTop.hom → Flat y →
    IsPullback p q y π → ∀ V : Y.Opens, Function.Bijective (p.app V).hom := by
  intro R _ S Y Z π y p q hqc hqs hbij hy H V
  have : IsIso π.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hV : IsIso (p.app V) := GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens p (fun W ↦
    have : IsAffine W.1 := W.2
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback
      ((isPullback_morphismRestrict p W.1).flip.paste_horiz H.flip)) V
  exact (ConcreteCategory.isIso_iff_bijective _).mp hV

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), QuasiCompact π → QuasiSeparated π → Function.Bijective π.appTop.hom → Flat y → IsPullback p q y π → ∀ V : Y.Opens, Function.Bijective (p.app V).hom := by
  first | exact @GlobalTheory.Mum.app_bijective_of_flat_baseChange | exact GlobalTheory.Mum.app_bijective_of_flat_baseChange | (intros; apply GlobalTheory.Mum.app_bijective_of_flat_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceEverywhere
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem archEx_continuous_det {r : ℕ} {Ψ : Finset (E →+* ℂ)} (τ : Ψ) :
    Continuous fun y : Frame Ψ r => (mat y τ).det :=
  Continuous.matrix_det (continuous_apply τ)

theorem archEx_continuousOn_horizGen {r : ℕ} (X : Data E r) (τ : X.Ψ) : ContinuousOn (horizGen τ) X.dom :=
  (archEx_continuous_det τ).continuousOn.inv₀ fun _ hy => (hy τ).1

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem archEx_relab_mem {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (τ : Psi H) (k : U.Comp) :
    relab c σ τ.1 ∈ (U.X k).Ψ := by
  refine ((hU.2.1 k).2 _).2 ?_
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  exact (congrArg σ (Subtype.ext τ.2)).trans hσ0

end SlopeTestRemainingChoices

end GlobalTheory.FlatCore

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombination
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

theorem GlobalTheory.VolBr.Pair.exists_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (P : Pair p) (a b : ℤ), ∃ M : HermLB p, P.Rep a b M := by
  intro k _ X _ p P a b
  obtain ⟨hL, hA, -⟩ := Pair.rep_base k X p P
  have cast (x y x' y' : ℤ) (M : HermLB p) (h : P.Rep x y M) (hx : x = x') (hy : y = y') :
      P.Rep x' y' M := by subst hx; subst hy; exact h
  have hLa := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ a.toNat hL)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-a).toNat hL))
  have hAb := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ b.toNat hA)
    (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ (-b).toNat hA))
  refine ⟨_, cast _ _ _ _ _ (Pair.rep_tens k X p P _ _ _ _ _ _ hLa hAb) ?_ ?_⟩
  · have h1 := Int.toNat_sub_toNat_neg a
    simp only [mul_one, mul_zero, neg_zero, add_zero]
    omega
  · have h1 := Int.toNat_sub_toNat_neg b
    simp only [mul_one, mul_zero, neg_zero, zero_add]
    omega
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombinationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianRepresentative_integerCombination : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b : ℤ), ∃ M : HermLB p, P.Rep a b M := by
  first | exact @GlobalTheory.VolBr.Pair.exists_rep | exact GlobalTheory.VolBr.Pair.exists_rep | (intros; apply GlobalTheory.VolBr.Pair.exists_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem sig_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (ρ : B →ₐ[R] B') (φ : B₀ →ₐ[R₀] B₀'), (∀ b, p' (ρ b) = φ (p b)) → ∀ (σ : R₁ ⊗[R₀] B₀ →+ B) (σ' : R₁ ⊗[R₀] B₀' →+ B'), α.IsSig p σ → α.IsSig p' σ' → (∀ y, ρ (σ y) = σ' (extHom R₁ φ y)) ∧ ∀ y, α.KerQ y → α.KerQ (extHom R₁ φ y) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker B' B₀' _ _ _ _ p' hs' hp' hker' ρ φ hρ σ σ' hσ hσ'
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r b₀ =>
      obtain ⟨b, rfl⟩ := hp b₀
      rw [hσ r b]
      simp only [extHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [← hρ b, hσ' r (ρ b), map_smul]
    | add x z hx hz => simp only [map_add (f := _), hx, hz]
  · have key : ∀ y : R₁ ⊗[R₀] B₀,
        Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀') (extHom R₁ φ y) =
          Algebra.TensorProduct.map (AlgHom.id R₀ R₀) φ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r b₀ => simp [extHom]
      | add x z hx hz => simp only [map_add (f := _), hx, hz]
    unfold Aug.KerQ at hy ⊢
    rw [key, hy, map_zero]

end GlobalTheory.Obs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNaturalStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_sigma_map_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (ρ : B →ₐ[R] B') (φ : B₀ →ₐ[R₀] B₀'), (∀ b, p' (ρ b) = φ (p b)) → ∀ (σ : R₁ ⊗[R₀] B₀ →+ B) (σ' : R₁ ⊗[R₀] B₀' →+ B'), α.IsSig p σ → α.IsSig p' σ' → (∀ y, ρ (σ y) = σ' (extHom R₁ φ y)) ∧ ∀ y, α.KerQ y → α.KerQ (extHom R₁ φ y) := by
  first | exact @GlobalTheory.Obs.sig_natural | exact GlobalTheory.Obs.sig_natural | (intros; apply GlobalTheory.Obs.sig_natural <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasis
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FibreBasisSpread

theorem exists_away_linearCombination_bijective : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (J : Type) [Fintype J] (v : J → M) (p : Ideal R) [p.IsPrime],
    Function.Bijective (Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i)) →
    ∃ g : R, g ∉ p ∧ (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R v c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R v c = 0 → ∃ n : ℕ, g ^ n • c = 0) := by
  intro R _ M _ _ _ _ J _ v p _ hbij
  classical
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let Rp := Localization.AtPrime p
  have hloc : Function.Bijective (IsLocalizedModule.map p.primeCompl
      (Finsupp.mapRange.linearMap (Algebra.linearMap R Rp)) (TensorProduct.mk R Rp M 1)
      (Finsupp.linearCombination R v)) := by
    rw [IsLocalizedModule.map_linearCombination, LinearMap.coe_restrictScalars]
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [← (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).comp_bijective]
    have heq : (AlgebraTensorModule.cancelBaseChange R Rp p.ResidueField p.ResidueField M).toLinearMap ∘ₗ
        Finsupp.linearCombination p.ResidueField
          (TensorProduct.mk Rp p.ResidueField (Rp ⊗[R] M) 1 ∘ (TensorProduct.mk R Rp M 1 ∘ v)) =
        Finsupp.linearCombination p.ResidueField (fun i => (1 : p.ResidueField) ⊗ₜ[R] v i) := by
      ext i
      simp
    convert hbij using 1
    rw [← heq, LinearMap.coe_comp]
    rfl
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective
    (Finsupp.linearCombination R v) p _ _ hloc
  refine ⟨g, hg, fun x => ?_, fun c hc => ?_⟩
  · obtain ⟨y, hy⟩ := h.2 (LocalizedModule.mk x 1)
    induction y using LocalizedModule.induction_on with
    | h c s =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨⟨u, hu⟩, hu'⟩ := hy
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, hb⟩ := s.2
      refine ⟨a + b, g ^ a • c, ?_⟩
      have hb' : (s : R) = g ^ b := hb.symm
      simp only [Submonoid.smul_def, one_smul] at hu'
      rw [map_smul, hu', hb', smul_smul, pow_add]
  · have h0 : LocalizedModule.map (Submonoid.powers g) (Finsupp.linearCombination R v)
        (LocalizedModule.mk c 1) = LocalizedModule.map (Submonoid.powers g)
        (Finsupp.linearCombination R v) 0 := by
      rw [LocalizedModule.map_mk, hc, map_zero, LocalizedModule.zero_mk]
    have h1 := h.1 h0
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
    obtain ⟨⟨u, hu⟩, hu'⟩ := h1
    obtain ⟨a, rfl⟩ := hu
    exact ⟨a, by simpa [Submonoid.smul_def] using hu'⟩

end GlobalTheory.FibreBasisSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquare
open CategoryTheory Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbBaseChangeSq

theorem exists_baseChange_and_sq : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (A : Over (Sp R₀)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (B : Over (Sp R₁)) (_ : GrpObj B) (pr : B.left ⟶ A.left) (pr' : (B ⊗ B).left ⟶ (A ⊗ A).left), IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsPullback pr B.hom A.hom (spMap (algebraMap R₀ R₁)) ∧ IsPullback pr' (B ⊗ B).hom (A ⊗ A).hom (spMap (algebraMap R₀ R₁)) ∧ (μ[B]).left ≫ pr = pr' ≫ (μ[A]).left ∧ (fst B B).left ≫ pr = pr' ≫ (fst A A).left ∧ (snd B B).left ≫ pr = pr' ≫ (snd A A).left ∧ (CartesianMonoidalCategory.lift (𝟙 B) (1 : B ⟶ B)).left ≫ pr' = pr ≫ (CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ A)).left ∧ (CartesianMonoidalCategory.lift (1 : B ⟶ B) (𝟙 B)).left ≫ pr' = pr ≫ (CartesianMonoidalCategory.lift (1 : A ⟶ A) (𝟙 A)).left := by
  intro R₀ R₁ _ _ _ A _ g hA hg
  let f : Sp R₁ ⟶ Sp R₀ := spMap (algebraMap R₀ R₁)
  let F := Over.pullback f
  let B : Over (Sp R₁) := F.obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsGrpPullback B A f (pullback.fst A.hom f) := isGrpPullback_pullback A f
  obtain ⟨hAB, hgB⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ A B _ g hB hA hg
  have mapL : ∀ {X Y : Over (Sp R₀)} (a : X ⟶ Y),
      (F.map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left := fun a => pullback.lift_fst _ _ _
  let m := Functor.LaxMonoidal.μ F A A
  refine ⟨B, inferInstance, pullback.fst A.hom f, m.left ≫ pullback.fst (A ⊗ A).hom f, hAB, hgB, hB.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : IsIso m := inferInstanceAs (IsIso (Functor.Monoidal.μIso F A A).hom)
    haveI : IsIso m.left := (Over.forget _).map_isIso m
    have h1 : IsPullback m.left (B ⊗ B).hom (F.obj (A ⊗ A)).hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w m⟩
    have h2 := h1.paste_horiz (IsPullback.of_hasPullback (A ⊗ A).hom f)
    rwa [Category.id_comp] at h2
  · have e : μ[B] = m ≫ F.map μ[A] := Functor.obj.μ_def (F := F) A
    rw [e, Over.comp_left, Category.assoc, mapL, Category.assoc]
  · rw [Category.assoc, ← mapL, ← Category.assoc, ← Over.comp_left]
    simp [m]
    rfl
  · rw [Category.assoc, ← mapL, ← Category.assoc, ← Over.comp_left]
    simp [m]
    rfl
  · have e : lift (𝟙 B) (1 : B ⟶ B) ≫ m = F.map (lift (𝟙 A) (1 : A ⟶ A)) := by
      rw [← Functor.Monoidal.lift_μ, F.map_id, Functor.map_one]
    rw [← Category.assoc, ← Over.comp_left, e, mapL]
  · have e : lift (1 : B ⟶ B) (𝟙 B) ≫ m = F.map (lift (1 : A ⟶ A) (𝟙 A)) := by
      rw [← Functor.Monoidal.lift_μ, F.map_id, Functor.map_one]
    rw [← Category.assoc, ← Over.comp_left, e, mapL]

end GlobalTheory.AbBaseChangeSq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianScheme_baseChange_and_square : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (A : Over (Sp R₀)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (B : Over (Sp R₁)) (_ : GrpObj B) (pr : B.left ⟶ A.left) (pr' : (B ⊗ B).left ⟶ (A ⊗ A).left), IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsPullback pr B.hom A.hom (spMap (algebraMap R₀ R₁)) ∧ IsPullback pr' (B ⊗ B).hom (A ⊗ A).hom (spMap (algebraMap R₀ R₁)) ∧ (μ[B]).left ≫ pr = pr' ≫ (μ[A]).left ∧ (fst B B).left ≫ pr = pr' ≫ (fst A A).left ∧ (snd B B).left ≫ pr = pr' ≫ (snd A A).left ∧ (CartesianMonoidalCategory.lift (𝟙 B) (1 : B ⟶ B)).left ≫ pr' = pr ≫ (CartesianMonoidalCategory.lift (𝟙 A) (1 : A ⟶ A)).left ∧ (CartesianMonoidalCategory.lift (1 : B ⟶ B) (𝟙 B)).left ≫ pr' = pr ≫ (CartesianMonoidalCategory.lift (1 : A ⟶ A) (𝟙 A)).left := by
  first | exact @GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq | exact GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq | (intros; apply GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory CartesianMonoidalCategory MonObj

open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem act_natCast {E : Type} [Field E] {X' : Scheme.{0}} {G : Over X'} [GrpObj G] (act : OAct (𝓞 E) G) (n : ℕ) :
    act.act (n : 𝓞 E) = mulN G n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    have h0 : act.act 0 = 1 := mul_eq_left.mp h.symm
    rw [Nat.cast_zero, h0, Hom.one_def]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ, act.add, ih, act.one, Hom.mul_def]
    rfl

theorem eta_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw : (η[G'].left ≫ φ) ≫ G.hom = (Over.mk ((𝟙_ (Over S')).hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w η[G']]
    rfl
  let x₀ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk (η[G'].left ≫ φ) hw
  have h1 : (η[G'] : 𝟙_ (Over S') ⟶ G') * η[G'] = η[G'] := by
    have e : (η[G'] : 𝟙_ (Over S') ⟶ G') = 1 := by
      rw [Hom.one_def]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ η[G']) (toUnit_unique _ _))
    rw [e, _root_.mul_one]
  have h2 := h.2 (𝟙_ (Over S')) η[G'] η[G'] x₀ x₀ rfl rfl
  rw [h1] at h2
  have h3 : x₀ * x₀ = x₀ := Over.OverMorphism.ext h2
  have h4 : x₀ = 1 := mul_eq_left.mp h3
  have h5 := congrArg (fun q => q.left) h4
  simp only [x₀, Over.homMk_left] at h5
  rw [h5, Hom.one_def, Over.comp_left]
  congr 1

theorem exists_lift_torsion {X' : Scheme.{0}} {G : Over X'} [GrpObj G] (n : ℕ) {Y : Over X'} (a : Y ⟶ G)
    (h : a ≫ mulN G n = 1) : ∃ aT : Y ⟶ torsion G n, aT ≫ torsion.ι G n = a :=
  ⟨pullback.lift a (toUnit Y) (by rw [h, Hom.one_def]), pullback.lift_fst _ _ _⟩

theorem mono_torsion_ι {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) : Mono (torsion.ι G n).left := by
  have : Mono (η[G] : 𝟙_ (Over X') ⟶ G) := ⟨fun g h _ => toUnit_unique g h⟩
  have : Mono (torsion.ι G n) := ⟨fun a b hab => pullback.hom_ext hab (toUnit_unique _ _)⟩
  infer_instance

theorem isDomain_stalk_of_etale {X' W : Scheme.{0}} [GlobalTheory.IsNormalScheme X'] (h : W ⟶ X') [Etale h] (q : W) :
    IsDomain (W.presheaf.stalk q) :=
  (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth h
    (fun y => ⟨GlobalTheory.IsNormalScheme.isDomain_stalk y, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk y⟩) q).1

end GlobalTheory.TorsSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMeasureRatioLe
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasureRatio

theorem log_r_add_three_le (D : D7) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) :
    Real.log ((D.R.r : ℝ) + 3) ≤ L := by
  have hr : 6 ≤ D.R.r := by
    unfold Ranks.r; have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hf : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  have hn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr' : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hf' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hn' : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast hn
  have h1 := hL.1
  rw [← Real.log_exp L]
  refine Real.log_le_log (by positivity) ?_
  have a1 : 2 * (D.R.r : ℝ) ≤ (D.R.f : ℝ) * D.R.r := mul_le_mul_of_nonneg_right hf' (by positivity)
  have a2 : 2 * (D.R.r : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * D.R.nV :=
    mul_le_mul a1 hn' (by positivity) (by positivity)
  have : (D.R.r : ℝ) + 3 ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by nlinarith
  linarith

end GlobalTheory.OneMeasureRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rep_ev_of_isPullback : ∀ (S : Scheme.{0}) (A B S' S'' B'' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (h : S'' ⟶ S') (k : B'' ⟶ B) (b'' : B'' ⟶ S''), Rep A b P → IsPullback k b'' b h → Rep A b'' (ev P (fst A B'') (snd A B'' ≫ k)) := by
  first | exact @GlobalTheory.DualCon.Rep.baseChange | exact GlobalTheory.DualCon.Rep.baseChange | (intros; apply GlobalTheory.DualCon.Rep.baseChange <;> assumption)
end
