module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwoTorsPull

theorem twoTorsRat_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (K' : Type) (_ : Field K') (_ : Algebra (FractionRing R) K'), Module.Finite (FractionRing R) K' ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] (ρ : R →+* R₂) (i : K' →+* FractionRing R₂), (∀ r : R, i (algebraMap (FractionRing R) K' (algebraMap R (FractionRing R) r)) = algebraMap R₂ (FractionRing R₂) (ρ r)) → ∀ (G₁ : Over (Sp R₂)) [GrpObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → TwoTorsRat G₁ := by
  intro R _ _ G _ A gen hgen
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A 2)
    (AbTorsionAnyBase.isFinite_and_flat_torsion _ A.A A.isAb 2 (by norm_num)).1
  refine ⟨K', inferInstance, inferInstance, hfin, ?_⟩
  intro R₂ _ _ ρ i hi G₁ _ β hβ F _ _ x hx
  let f : FractionRing R →+* FractionRing R₂ := i.comp (algebraMap (FractionRing R) K')
  letI : Algebra K' (FractionRing R₂) := i.toAlgebra
  letI : Algebra (FractionRing R) (FractionRing R₂) := f.toAlgebra
  haveI : IsScalarTower (FractionRing R) K' (FractionRing R₂) := IsScalarTower.of_algebraMap_eq' rfl
  let σ : FractionRing R₂ →+* F := algebraMap (FractionRing R₂) F
  have hsq : spMap f ≫ jK R = jK R₂ ≫ spMap ρ := by
    rw [jK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact hi r
  have hx2 : x ^ 2 = 1 := by rw [pow_two, hx]

  let x0 := ObjPull.pushEquiv hβ _ x
  have hx0 : x0 ^ 2 = 1 := by simp only [x0, ← map_pow, hx2, map_one]
  have hx0l : x0.left = x.left ≫ β := rfl

  let T : Over (Sp (FractionRing R)) := Over.mk (spMap σ ≫ spMap f)
  have hT : T.hom ≫ jK R = (Over.mk (spMap σ ≫ jK R₂)).hom ≫ spMap ρ := by
    show (spMap σ ≫ spMap f) ≫ jK R = (spMap σ ≫ jK R₂) ≫ spMap ρ
    rw [Category.assoc, hsq, Category.assoc]
  let e : Over.mk (T.hom ≫ jK R) ⟶ Over.mk ((Over.mk (spMap σ ≫ jK R₂)).hom ≫ spMap ρ) :=
    Over.homMk (𝟙 _) (by simpa using hT.symm)
  let x1 := preHom e x0
  have hx1 : x1 ^ 2 = 1 := by rw [← map_pow, hx0, map_one]
  have hx1l : x1.left = x0.left := by
    show (e ≫ x0).left = _
    rw [Over.comp_left]
    exact Category.id_comp _
  let hpb := isGrpPullback_pullback G (jK R)
  let x2 := (ObjPull.pushEquiv hpb T).symm x1
  have hx2' : x2 ^ 2 = 1 := by simp only [x2, ← map_pow, hx1, map_one]
  have hx2l : x2.left ≫ pullback.fst G.hom (jK R) = x1.left := ObjPull.pushEquiv_symm_left hpb T x1
  let x3 := x2 ≫ gen.hom
  have hx3 : x3 ^ 2 = 1 := by
    simp only [x3, pow_two] at hx2' ⊢
    rw [← MonObj.mul_comp, hx2', MonObj.one_comp]
  have hmul : x3 ≫ mulN A.A 2 = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx3, Hom.one_def]
  let t0 : T ⟶ torsion A.A 2 := pullback.lift x3 (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι A.A 2 = x3 := pullback.lift_fst _ _ _
  have hs : T.hom = spMap (σ.comp (algebraMap (FractionRing R) (FractionRing R₂))) := by
    show spMap σ ≫ spMap f = _
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨w, hw⟩ := H (FractionRing R₂) F σ t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion A.A 2).hom = spMap f := by
    have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
        {X : Scheme} (y y' : Sp K ⟶ X)
        (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
      obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
      obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
      simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
      have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
          spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
            (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
        intro q ψ
        simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
      rw [e, e] at h
      have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
      simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h3⟩ := h2
      have h4 : φ = φ' := by
        have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
        ext x
        apply gam.injective
        have := congrArg (fun f => f.hom x) h5
        simpa using this
      rw [h4]
    refine spec_map_field_cancel σ _ _ ?_
    rw [← Category.assoc, hw, Over.w t0]
    rfl
  let z : Sp (FractionRing R₂) ⟶ G.left := w ≫ (torsion.ι A.A 2).left ≫ gen.inv.left ≫ pullback.fst G.hom (jK R)
  have hz : z ≫ G.hom = jK R₂ ≫ spMap ρ := by
    simp only [z, Category.assoc]
    have hgi : gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w gen.inv
    rw [pullback.condition, ← Category.assoc gen.inv.left, hgi, ← Category.assoc (torsion.ι A.A 2).left,
      Over.w (torsion.ι A.A 2), ← Category.assoc w, hw2, hsq]
  let y : Over.mk (jK R₂) ⟶ G₁ := Over.homMk (hβ.1.lift z (jK R₂) hz) (hβ.1.lift_snd _ _ _)
  refine ⟨y, hβ.1.hom_ext ?_ ?_⟩
  · show x.left ≫ β = spMap σ ≫ hβ.1.lift z (jK R₂) hz ≫ β
    rw [hβ.1.lift_fst, ← hx0l, ← hx1l, ← hx2l]
    have hgh : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    simp only [z, ← Category.assoc]
    rw [hw, ← Over.comp_left, ht0]
    show x2.left ≫ pullback.fst G.hom (jK R) = ((x2.left ≫ gen.hom.left) ≫ gen.inv.left) ≫ pullback.fst G.hom (jK R)
    rw [Category.assoc x2.left, hgh, Category.comp_id]
  · show x.left ≫ G₁.hom = spMap σ ≫ hβ.1.lift z (jK R₂) hz ≫ G₁.hom
    rw [hβ.1.lift_snd]
    exact Over.w x

end GlobalTheory.TwoTorsPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_ext_two_torsion_rational_pullbacks : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (K' : Type) (_ : Field K') (_ : Algebra (FractionRing R) K'), Module.Finite (FractionRing R) K' ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] (ρ : R →+* R₂) (i : K' →+* FractionRing R₂), (∀ r : R, i (algebraMap (FractionRing R) K' (algebraMap R (FractionRing R) r)) = algebraMap R₂ (FractionRing R₂) (ρ r)) → ∀ (G₁ : Over (Sp R₂)) [GrpObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → TwoTorsRat G₁ := by
  first | exact @GlobalTheory.TwoTorsPull.twoTorsRat_of_pullback | exact GlobalTheory.TwoTorsPull.twoTorsRat_of_pullback | (intros; apply GlobalTheory.TwoTorsPull.twoTorsRat_of_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataLatticeFactorProps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataLatticeFactorProps
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem mul_single_mul_apply (M N : Matrix (Fin r) (Fin r) ℤ) (i₀ i j : Fin r) :
    (M * Matrix.single i₀ i₀ (1:ℤ) * N) i j = M i i₀ * N i₀ j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single i₀]
  · congr 1
    simp [Matrix.mul_apply, Matrix.single_apply]
  · intro b _ hb
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm hb]
  · simp

theorem mul_single_apply' (M : Matrix (Fin r) (Fin r) ℤ) (i₀ i j : Fin r) :
    (M * Matrix.single i₀ i₀ (1:ℤ)) i j = if j = i₀ then M i i₀ else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
  · by_cases h : j = i₀
    · subst h; simp
    · simp [Matrix.single_apply, Ne.symm h, h]
  · intro b _ hb
    simp [Matrix.single_apply, Ne.symm hb]
  · simp

theorem Tens.xe_xi (T : Tens D D' W) (i₀ : Fin r) (y : D.X) :
    T.xe (T.xi i₀ y) = Pi.single i₀ y := by
  simp [Tens.xi]

theorem Tens.xe_smul_xi (T : Tens D D' W) (s : SymUnit r) (a : TensO s) (i₀ : Fin r) (y : D.X) (i : Fin r) :
    letI := T.mod s
    T.xe (a • T.xi i₀ y) i = TensO.mat s a i i₀ • y := by
  letI := T.mod s
  rw [Tens.xe_smul]
  simp only [Tens.xe_xi]
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem TensO.mat_star_idem_mul_binv {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    TensO.mat s (star (TensO.idem s i₀) * TensO.binv s) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 := by
  change TensO.mat s (star (TensO.idem s i₀)) * TensO.mat s (TensO.binv s) = _
  rw [TensO.star_def]
  show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (Matrix.single i₀ i₀ (1:ℤ)).transpose *
      (s.1 : Matrix (Fin r) (Fin r) ℤ) * ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) = _
  rw [Matrix.transpose_single, Matrix.mul_assoc _ (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.mul_one]

theorem TensO.mat_star_idem {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    TensO.mat s (star (TensO.idem s i₀)) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) := by
  rw [TensO.star_def]
  show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * (Matrix.single i₀ i₀ (1:ℤ)).transpose *
      (s.1 : Matrix (Fin r) (Fin r) ℤ) = _
  rw [Matrix.transpose_single]

theorem SymUnit.inv_col_ne {r : ℕ} (s : SymUnit r) (i₀ : Fin r) :
    ∃ i, ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) i i₀ ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 := congrFun (congrFun (Units.mul_inv s.1) i₀) i₀
  rw [Matrix.mul_apply, Finset.sum_eq_zero (fun k _ => by rw [h k, mul_zero]), Matrix.one_apply_eq] at h1
  exact zero_ne_one h1

theorem tens_factor_latt : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (s : SymUnit r) (i₀ : Fin r), letI := T.mod s;
    (∀ y, T.xp i₀ (T.xi i₀ y) = y) ∧ (∀ z, T.xi i₀ (T.xp i₀ z) = TensO.idem s i₀ • z) ∧
    Function.Injective (fun y => star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) ∧
    ∀ z, ∃ y, star (TensO.idem s i₀) • z = star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y := by
  intro R _ _ D D' r W T s i₀
  letI := T.mod s
  have key : ∀ y i, T.xe (star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) i =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) i i₀ • y := by
    intro y i
    rw [← mul_smul, Tens.xe_smul_xi, TensO.mat_star_idem_mul_binv, mul_single_apply']
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    show T.xe (T.xi i₀ y) i₀ = y
    rw [Tens.xe_xi]; simp
  · intro z
    apply T.xe.injective
    funext i
    rw [Tens.xe_xi, Tens.xe_smul]
    show Pi.single (M := fun _ => D.X) i₀ (T.xe z i₀) i = _
    simp only [TensO.idem, TensO.ofMat, TensO.mat, Matrix.single_apply]
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [hi, Ne.symm hi]
  · intro y y' h
    obtain ⟨i, hi⟩ := SymUnit.inv_col_ne s i₀
    have h' := congrArg (fun z => T.xe z i) h
    simp only [key] at h'
    exact smul_right_injective D.X hi h'
  · intro z
    refine ⟨∑ j, (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ j • T.xe z j, ?_⟩
    apply T.xe.injective
    funext i
    rw [key, Tens.xe_smul, TensO.mat_star_idem, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_single_mul_apply, mul_smul]
end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataLatticeFactorPropsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorData_latticeFactor_props : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (s : SymUnit r) (i₀ : Fin r), letI := T.mod s; (∀ y, T.xp i₀ (T.xi i₀ y) = y) ∧ (∀ z, T.xi i₀ (T.xp i₀ z) = TensO.idem s i₀ • z) ∧ Function.Injective (fun y => star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) ∧ ∀ z, ∃ y, star (TensO.idem s i₀) • z = star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y := by
  first | exact @GlobalTheory.Mum.tens_factor_latt | exact GlobalTheory.Mum.tens_factor_latt | (intros; apply GlobalTheory.Mum.tens_factor_latt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOfExpansionModMaximalIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOfExpansionModMaximalIdeal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ExpandNonzero

open ReciprocityTheory.ChartRestriction.G.Semi

theorem mem_wchart {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (y : Y) : y ∈ LB.wchart L φ j ↔ ∀ k, (φ k).base y ∈ L.U (j k) := by
  show y ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X) ↔ _
  exact Set.mem_iInter

theorem sec_mem_basicOpen {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) (i j : L.ι) {x : X}
    (hx : x ∈ X.basicOpen (s.f j)) (hi : x ∈ L.U i) : x ∈ X.basicOpen (s.f i) := by
  have hxj : x ∈ L.U j := X.basicOpen_le _ hx
  have h := congrArg X.basicOpen (s.compat i j)
  simp only [Scheme.basicOpen_res, Scheme.basicOpen_mul,
    Scheme.basicOpen_of_isUnit _ (L.g i j).isUnit] at h
  have hm : x ∈ (L.U i ⊓ L.U j) ⊓ ((L.U i ⊓ L.U j) ⊓ X.basicOpen (s.f j)) :=
    ⟨⟨hi, hxj⟩, ⟨hi, hxj⟩, hx⟩
  rw [← h] at hm
  exact hm.2

theorem nonzero_of_expandsAt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (k : ℕ) (s : H0 U.LG.L k)
      (f : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt 0 k s f →
      (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) →
      ∀ y : (thickObj R (maximalIdeal R) 0 G).left,
      (∃ j : Fin 4 → D.toPre.P.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
          (((U.gt 0).pG.left.app _).hom ((f 0).f j))) →
      ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
        (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  intro R _ _ _ D A G _ _ U k s f hexp hzero y hy
  classical
  obtain ⟨j, hj⟩ := hy
  obtain ⟨S, hS, hE⟩ := hexp
  have hcovM : ∀ ψ : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left,
      ∃ i, ψ.base y ∈ D.toPre.P.L.U i := fun ψ => by
    have : ψ.base y ∈ ⨆ i, D.toPre.P.L.U i := by rw [D.toPre.P.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨iL, hiL⟩ : ∃ i, (fstG (maximalIdeal R) 0 G).left.base y ∈ U.LG.L.U i := by
    have : (fstG (maximalIdeal R) 0 G).left.base y ∈ ⨆ i, U.LG.L.U i := by
      rw [U.LG.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  let idx : ((thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι :=
    fun ψ => (hcovM ψ).choose
  have hidx : ∀ ψ, ψ.base y ∈ D.toPre.P.L.U (idx ψ) := fun ψ => (hcovM ψ).choose_spec
  refine ⟨fun _ => iL, ?_⟩
  have h0S : (0 : D.toPre.X) ∈ S := by
    by_contra h
    have h' := hS 0 h j
    rw [h', Scheme.basicOpen_zero] at hj
    exact hj
  have key := hE (fun _ => idx (U.gt 0).pG.left, fun _ => iL) (fun _ => iL)
    (fun α i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB α i))
    (fun α i => idx (D.toPre.Oφ (U.gt 0).pG α i)) rfl (by
      intro a b hab
      rcases a with _ | (a | a) <;> rcases b with _ | (b | b) <;> exact congrArg idx hab)

  have hyW : y ∈ U.expW 0 (fun _ => idx (U.gt 0).pG.left, fun _ => iL) (fun _ => iL) S
      (fun α i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB α i))
      (fun α i => idx (D.toPre.Oφ (U.gt 0).pG α i)) := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact (mem_wchart _ _ _ y).2 fun _ => hidx _
    · exact (mem_wchart _ _ _ y).2 fun _ => hiL
    · show (fstG (maximalIdeal R) 0 G).left.base y ∈ LB.wchart _ _ _
      exact (mem_wchart _ _ _ _).2 fun _ => hiL
    · refine Finset.inf_induction
        (p := fun V : (thickObj R (maximalIdeal R) 0 G).left.Opens => y ∈ V)
        (show y ∈ (⊤ : (thickObj R (maximalIdeal R) 0 G).left.Opens) from trivial)
        (fun a ha b hb => TopologicalSpace.Opens.mem_inf.2 ⟨ha, hb⟩) fun α _ =>
          TopologicalSpace.Opens.mem_inf.2 ⟨?_, ?_⟩
      · show (U.gt 0).pG.left.base y ∈ LB.wchart _ _ _
        exact (mem_wchart _ _ _ _).2 fun i => hidx ((U.gt 0).pG.left ≫ D.toPre.famφB α i)
      · exact (mem_wchart _ _ _ y).2 fun i => hidx _

  have hf0 : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
      (((U.gt 0).pG.left.app _).hom
        ((f 0).f (fun i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB 0 i)))) := by
    rw [← Scheme.preimage_basicOpen] at hj ⊢
    exact sec_mem_basicOpen (f 0) _ j hj
      ((mem_wchart _ _ _ _).2 fun i => hidx ((U.gt 0).pG.left ≫ D.toPre.famφB 0 i))
  rw [Finset.sum_eq_single ⟨0, h0S⟩ (fun b _ hb => by
      have hb' : b.1 ≠ 0 := fun h => hb (Subtype.ext h)
      refine mul_eq_zero_of_left ?_ _
      exact (congrArg _ (hzero b.1 hb' _)).trans (map_zero _))
    (fun h => absurd (Finset.mem_attach _ _) h)] at key
  have hL := (congrArg (fun a => y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen a) key).mpr (by
    simp only [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _),
      Scheme.basicOpen_res, TopologicalSpace.Opens.mem_inf]
    exact ⟨⟨hyW, hf0⟩, hyW⟩)
  simp only [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ ((Units.isUnit _).pow k),
    Scheme.basicOpen_res, TopologicalSpace.Opens.mem_inf] at hL
  exact hL.2.2

end GlobalTheory.Mum.ExpandNonzero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOfExpansionModMaximalIdealStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_nonzero_of_expansion_mod_maximalIdeal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (k : ℕ) (s : H0 U.LG.L k)
      (f : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt 0 k s f →
      (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) →
      ∀ y : (thickObj R (maximalIdeal R) 0 G).left,
      (∃ j : Fin 4 → D.toPre.P.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
          (((U.gt 0).pG.left.app _).hom ((f 0).f j))) →
      ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
        (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  first | exact @GlobalTheory.Mum.ExpandNonzero.nonzero_of_expandsAt_zero | exact GlobalTheory.Mum.ExpandNonzero.nonzero_of_expandsAt_zero | (intros; apply GlobalTheory.Mum.ExpandNonzero.nonzero_of_expandsAt_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivation
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Lift

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem rel_isTwoSided (h : ∀ x ∈ rel R δ, ∀ y, x * y ∈ rel R δ) : (rel R δ).IsTwoSided :=
  ⟨fun b ha ↦ h _ ha b⟩

variable [(rel R δ).IsTwoSided]

def kq : K1 R δ →ₗ[B] DR R B ⧸ rel R δ :=
  (N1 R δ).liftQ ((Ideal.Quotient.mkₐ B (rel R δ)).toLinearMap ∘ₗ ι1) fun x hx ↦ by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hx

theorem kq_mk (ω : Ω[B⁄R]) : kq δ (Submodule.Quotient.mk ω) = Ideal.Quotient.mk (rel R δ) (ι1 ω) := rfl

end Lift

theorem exists_lift_of_pdDerivation (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (C : Type) [CommRing C] [Algebra R C] (JC : Ideal C) (δC : DividedPowers JC)
    (π : C →ₐ[R] B) (w : C →+ K1 R δ) (hw : ∀ x y, w (x * y) = π x • w y + π y • w x)
    (hw0 : ∀ r, w (algebraMap R C r) = 0)
    (hwd : ∀ n, ∀ a ∈ JC, w (δC.dpow (n + 1) a) = π (δC.dpow n a) • w a) :
    ∃ ρ : DR R C → DR R B, (∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) ∧ (∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R δ) ∧
      (∀ c, ρ (algebraMap C (DR R C) c) - algebraMap B (DR R B) (π c) ∈ rel R δ) ∧
      (∀ c ω, Submodule.Quotient.mk ω = w c → ρ (ι1 (D R C c)) - ι1 ω ∈ rel R δ) ∧
      (∀ x ∈ rel R δC, ρ x ∈ rel R δ) ∧ (∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) ∧
      ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ := by
  haveI : (rel R δ).IsTwoSided := rel_isTwoSided δ ((GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base.1 R B J δ).1)
  letI algC : Algebra C (DR R B ⧸ rel R δ) :=
    ((algebraMap B (DR R B ⧸ rel R δ)).comp (π : C →+* B)).toAlgebra' fun c x ↦ Algebra.commutes (π c) x
  haveI : IsScalarTower R C (DR R B ⧸ rel R δ) := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change _ = algebraMap B _ (π (algebraMap R C r))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have smulC : ∀ (c : C) (q : DR R B ⧸ rel R δ), c • q = π c • q := fun c q ↦ by
    rw [Algebra.smul_def, Algebra.smul_def]; rfl
  let v : Derivation R C (DR R B ⧸ rel R δ) := Derivation.mk'
    { toFun := fun c ↦ kq δ (w c)
      map_add' := fun a b ↦ by simp
      map_smul' := fun r c ↦ by
        rw [RingHom.id_apply, Algebra.smul_def r c, hw, hw0, smul_zero, add_zero, map_smul, AlgHom.commutes,
          algebraMap_smul] }
    fun a b ↦ by
      change kq δ (w (a * b)) = a • kq δ (w b) + b • kq δ (w a)
      rw [hw, map_add (f := _), map_smul, map_smul, smulC, smulC]
  have hv : ∀ c, v c = kq δ (w c) := fun _ ↦ rfl
  have key : ∀ ω : Ω[C⁄R], ∃ η : Ω[B⁄R], v.liftKaehlerDifferential ω = Ideal.Quotient.mk (rel R δ) (ι1 η) := by
    intro ω
    induction ω using ind1 with
    | h b c =>
      obtain ⟨η, hη⟩ := Submodule.Quotient.mk_surjective _ (w c)
      refine ⟨π b • η, ?_⟩
      rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, hv, ← hη, kq_mk, smulC, map_smul,
        Algebra.smul_def (π b) (ι1 η), map_mul, Ideal.Quotient.mk_algebraMap, Algebra.smul_def]
    | h0 => exact ⟨0, by simp⟩
    | ha x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]⟩
  let Φ : DR R C →ₐ[C] DR R B ⧸ rel R δ := ExteriorAlgebra.lift C ⟨v.liftKaehlerDifferential, fun m ↦ by
    obtain ⟨η, h⟩ := key m
    rw [h, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]⟩
  have hΦι : ∀ ω : Ω[C⁄R], Φ (ι1 ω) = v.liftKaehlerDifferential ω := fun ω ↦ ExteriorAlgebra.lift_ι_apply _ _ _ _
  have hΦD : ∀ c, Φ (ι1 (D R C c)) = kq δ (w c) := fun c ↦ by
    rw [hΦι, Derivation.liftKaehlerDifferential_comp_D, hv]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : DR R C → DR R B, ∀ x, Ideal.Quotient.mk (rel R δ) (ρ x) = Φ x :=
    ⟨_, fun x ↦ Function.surjInv_eq Ideal.Quotient.mk_surjective (Φ x)⟩
  have cv : ∀ x a, ρ x - a ∈ rel R δ ↔ Φ x = Ideal.Quotient.mk (rel R δ) a := fun x a ↦ by
    rw [← Ideal.Quotient.eq, hρ]
  refine ⟨ρ, fun x y ↦ ?_, fun x y ↦ ?_, fun c ↦ ?_, fun c ω h ↦ ?_, fun x hx ↦ ?_, fun x ↦ ?_, fun j x hx ↦ ?_⟩
  · rw [sub_sub]
    exact (cv _ _).2 (by rw [map_add (f := _), map_add (f := _), hρ, hρ])
  · exact (cv _ _).2 (by rw [map_mul, map_mul, hρ, hρ])
  · exact (cv _ _).2 (by rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]; rfl)
  · exact (cv _ _).2 (by rw [hΦD, ← h, kq_mk])
  · rw [← Ideal.Quotient.eq_zero_iff_mem, hρ]
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, a, ha, rfl⟩ := hx
      rw [map_sub, map_smul, map_sub, map_smul, hΦD, hΦD, hwd n a ha, map_smul, smulC, sub_self]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul r x _ ih => rw [smul_eq_mul, map_mul, ih, mul_zero]
  · obtain ⟨η, h⟩ := key x
    exact ⟨η, (cv _ _).2 (by rw [hΦι, h])⟩
  · induction hx using Submodule.pow_induction_on_left' with
    | algebraMap c =>
      refine ⟨algebraMap B _ (π c), ?_, (cv _ _).2 (by rw [AlgHom.commutes, Ideal.Quotient.mk_algebraMap]; rfl)⟩
      change _ ∈ LinearMap.range _ ^ 0
      rw [pow_zero]; exact Submodule.algebraMap_mem _
    | add x y i _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, add_mem ha hb, (cv _ _).2 (by rw [map_add (f := _), (cv _ _).1 ha', (cv _ _).1 hb', map_add (f := _)])⟩
    | mem_mul m hm i x hx ih =>
      obtain ⟨ω, rfl⟩ := hm
      obtain ⟨η, hη⟩ := key ω
      obtain ⟨y, hy, hy'⟩ := ih
      refine ⟨ι1 η * y, ?_, (cv _ _).2 ?_⟩
      · have := GlobalTheory.CechDR.mul_mem (ι_mem η) hy
        rwa [add_comm] at this
      · rw [map_mul, (cv _ _).1 hy', map_mul, ← hη, ← hΦι]

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivationStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C] [Algebra R C] (JC : Ideal C) (δC : DividedPowers JC) (π : C →ₐ[R] B) (w : C →+ K1 R δ), (∀ x y, w (x * y) = π x • w y + π y • w x) → (∀ r, w (algebraMap R C r) = 0) → (∀ n, ∀ a ∈ JC, w (δC.dpow (n + 1) a) = π (δC.dpow n a) • w a) → ∃ ρ : DR R C → DR R B, (∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) ∧ (∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R δ) ∧ (∀ c, ρ (algebraMap C (DR R C) c) - algebraMap B (DR R B) (π c) ∈ rel R δ) ∧ (∀ c ω, Submodule.Quotient.mk ω = w c → ρ (ι1 (D R C c)) - ι1 ω ∈ rel R δ) ∧ (∀ x ∈ rel R δC, ρ x ∈ rel R δ) ∧ (∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ := by
  first | exact @GlobalTheory.PDForm.exists_lift_of_pdDerivation | exact GlobalTheory.PDForm.exists_lift_of_pdDerivation | (intros; apply GlobalTheory.PDForm.exists_lift_of_pdDerivation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOfGroupSchemeIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOfGroupSchemeIso
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolOfIso

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem relAmple_pull_of_affine (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w)
    (hf : ∀ U' : S'.Opens, IsAffineOpen U' → ∃ U : S.Opens, IsAffineOpen U ∧ U' ≤ f ⁻¹ᵁ U) (hA : RelAmple A L) :
    RelAmple A' L' := by
  intro U' hU'
  obtain ⟨U, hU, le⟩ := hf U' hU'
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA U hU
  have le' : A'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy => (congrArg (fun q => q y ∈ U) h.w).mpr (le hy)
  let ψ := φ.resLE (A.hom ⁻¹ᵁ U) (A'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (A'.hom ∣_ U') (A.hom ∣_ U) (f.resLE U U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict A.hom U).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict A'.hom U').flip.paste_horiz h
    · rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w, Category.assoc,
        Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine U := hU
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have hP' := linComb_isLB L' hL' (K := Fin N) (fun _ => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (A'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A' L' U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (Geo.Tor.mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (Geo.Tor.mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L U N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A' L' U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((f.resLE U U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

theorem sym_pull_of_iso [GrpObj A] [GrpObj A'] (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w) (hs : Sym A L) : Sym A' L' := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := hs (f s)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  have le' : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy =>
    (congrArg (fun q => q y ∈ U) h.1.w).mpr hy
  have hψ : φ.resLE _ _ le' ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  obtain ⟨t', ht'⟩ := gen_chartPull (chartPullSame L
    (fun k => ![(A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ (GrpObj.inv : A' ⟶ A').left, (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι] k ≫ φ) _ _
    (φ.resLE _ _ le') fun k => by
      fin_cases k
      · show (_ ≫ _) ≫ φ = _ ≫ _ ≫ _
        rw [Category.assoc, PolBaseChange.inv_comm h, ← Category.assoc, ← hψ, Category.assoc]
      · exact hψ.symm) t ht
  exact exists_down hw hL hL' t' ht'

end GlobalTheory.PolOfIso

namespace GlobalTheory

theorem polarisation_of_iso :
    ∀ (S : Scheme.{0}) (P : PolAV S) (B : Over S) [GrpObj B] (e : B ≅ P.A), IsMonHom e.hom → ∀ L : LB B.left, L.IsLB → LBIso L (P.L.pull e.hom.left) → IsProper B.hom ∧ SmoothOfRelativeDimension P.g B.hom ∧ Sym B L ∧ RelAmple B L ∧ KTriv B L := by
  intro S P B _ e he L hL ⟨w, hw⟩
  have h := isGrpPullback_of_iso e
  have hw' := (isGen_iff w).1 hw
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) h.1 P.isAb.proper,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim,
    PolOfIso.sym_pull_of_iso h P.isLB hL hw' P.sym,
    PolOfIso.relAmple_pull_of_affine h.1 P.isLB hL hw' (fun U hU => ⟨U, hU, fun _ hy => hy⟩) P.ample,
    kTriv_pull h P.isLB hL hw' P.ktriv⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOfGroupSchemeIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarisation_of_groupScheme_iso : ∀ (S : Scheme.{0}) (P : PolAV S) (B : Over S) [GrpObj B] (e : B ≅ P.A), IsMonHom e.hom → ∀ L : LB B.left, L.IsLB → LBIso L (P.L.pull e.hom.left) → IsProper B.hom ∧ SmoothOfRelativeDimension P.g B.hom ∧ Sym B L ∧ RelAmple B L ∧ KTriv B L := by
  first | exact @GlobalTheory.polarisation_of_iso | exact GlobalTheory.polarisation_of_iso | (intros; apply GlobalTheory.polarisation_of_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeformationChartPointSpecMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeformationChartPointSpecMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

theorem valR_spMap_comp {Z : Scheme.{0}} {S S' : Type} [CommRing S] [CommRing S'] (σ : S →+* S')
    (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(Z, U)) :
    valR (spMap σ ≫ z) U f = σ (valR z U f) := by
  have h' := GlobalTheory.FlagMod.le_preimage_comp (spMap σ) h
  rw [valR_eq_ev _ _ h', valR_eq_ev _ _ h, GlobalTheory.FlagMod.ev_spMap σ z U h h']
  rfl

theorem top_le_transl {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens}
    (h : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ (transl φ x v) ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (DualNumber B) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← (isTransl_transl φ x hx v).red hv] at this
  exact this

theorem transl_spMap {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {B B' : Type} [CommRing B] [CommRing B']
    (φ : K →+* B) (σ : B →+* B') (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (v : epsR K ⟶ A) :
    transl (σ.comp φ) (spMap σ ≫ x) v = spMap (dualMap σ) ≫ transl φ x v := by
  have hx' : (spMap σ ≫ x) ≫ A.hom = spMap (σ.comp φ) := by
    rw [Category.assoc, hx, Cris.spMap_comp]
  exact (isTransl_transl _ _ hx' v).unique ((isTransl_transl φ x hx v).map σ)

theorem baseMap_eq {K : Type} [Field K] {B B' : Type} [CommRing B] [Algebra (DualNumber K) B] [CommRing B']
    [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B') :
    baseMap K B' = (ρ : B →+* B').comp (baseMap K B) :=
  RingHom.ext fun k ↦ by simp [baseMap]

theorem dualMap_snd {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (c : DualNumber B) :
    (dualMap σ c).snd = σ c.snd := by
  simp [dualMap]

section Map

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
  {B B' : Type} [CommRing B] [Algebra (DualNumber K) B] [CommRing B'] [Algebra (DualNumber K) B']

theorem dlogAt_spMap (ρ : B →ₐ[DualNumber K] B') {x : Sp B ⟶ A.left}
    (hx : x ≫ A.hom = spMap (baseMap K B)) {v : epsR K ⟶ A} (hv : IsTangent v) {Wo : A.left.Opens}
    (g : Γ(A.left, Wo)ˣ) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) :
    dlogAt (baseMap K B') (spMap (ρ : B →+* B') ≫ x) v Wo g = ρ (dlogAt (baseMap K B) x v Wo g) := by
  rw [dlogAt, dlogAt, baseMap_eq ρ, transl_spMap _ _ x hx v,
    valR_spMap_comp _ _ _ (top_le_transl _ x hx hv hxWo), valR_spMap_comp _ _ _ hxWo, dualMap_snd, map_mul]
  rfl

theorem chartVal_spMap {Z : Scheme.{0}} (m : A.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω))
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    (ρ : B →ₐ[DualNumber K] B') {x : Sp B ⟶ A.left}
    (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo)
    (hut : ∀ a, IsTangent (u a)) (f : Γ(Z, Ω)) :
    chartVal m Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) f = ρ (chartVal m Ω δ u θ Wo g x f) := by
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω := hxΩ
  have ht : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω := fun a ↦
    top_le_transl _ x hx (hut a) hxΩ
  have hd : ∀ b, dlogAt (baseMap K B') (spMap (ρ : B →+* B') ≫ x) (u b) Wo g =
      ρ (dlogAt (baseMap K B) x (u b) Wo g) := fun b ↦ dlogAt_spMap ρ hx (hut b) g hxWo
  have htr : ∀ a, transl (baseMap K B') (spMap (ρ : B →+* B') ≫ x) (u a) =
      spMap (dualMap (ρ : B →+* B')) ≫ transl (baseMap K B) x (u a) := fun a ↦ by
    rw [baseMap_eq ρ]; exact transl_spMap _ _ x hx (u a)
  simp only [chartVal, hd, htr, Category.assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [valR_spMap_comp _ _ _ hxm, valR_spMap_comp _ _ _ (ht _), dualMap_snd, map_add (f := _), map_mul, map_sum]
  simp only [RingHom.coe_coe, AlgHom.commutes, baseMap_eq ρ, RingHom.comp_apply]

end Map

theorem isChartPt_spMap : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {Ω : Z.Opens} {δ : Γ(Z, Ω) → Γ(Z, Ω)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω δ u θ Wo g x l) (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'), IsChartPt A' m m' Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) (spMap (ρ : B →+* B') ≫ l) := by
  intro K _ A _ A' Z m m' Ω δ n u θ Wo g B _ _ x l hx hxΩ hxWo hut hl B' _ _ ρ
  obtain ⟨h1, h2, h3⟩ := hl
  refine ⟨?_, ?_, fun f ↦ ?_⟩
  · rw [Category.assoc, h1, ← Cris.spMap_comp, AlgHom.comp_algebraMap]
  · rw [Category.assoc]
    exact GlobalTheory.FlagMod.le_preimage_comp _ h2
  · rw [Category.assoc, valR_spMap_comp _ _ _ h2, h3 f, chartVal_spMap m Ω δ u θ Wo g ρ hx hxΩ hxWo hut f]
    rfl

end GlobalTheory.CechKS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeformationChartPointSpecMapStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeformationChartPoint_spec_map : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {Ω : Z.Opens} {δ : Γ(Z, Ω) → Γ(Z, Ω)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω)) (hxWo : ⊤ ≤ x ⁻¹ᵁ Wo) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω δ u θ Wo g x l) (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'), IsChartPt A' m m' Ω δ u θ Wo g (spMap (ρ : B →+* B') ≫ x) (spMap (ρ : B →+* B') ≫ l) := by
  first | exact @GlobalTheory.CechKS.isChartPt_spMap | exact GlobalTheory.CechKS.isChartPt_spMap | (intros; apply GlobalTheory.CechKS.isChartPt_spMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfRangeSupSmulTopEqTop
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem surjective_of_range_sup_smul_top_eq_top (R : Type) [CommRing R] (M : Type 1)
    [AddCommGroup M] [Module R M] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N)
    (h : ∀ I : Ideal R, I.IsMaximal → LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤) :
    Function.Surjective f := by
  set S := LinearMap.range f

  have key : ∀ I : Ideal R, I.IsMaximal → ¬ Module.annihilator R (N ⧸ S) ≤ I := by
    intro I hI hle
    have hle' : (⊤ : Submodule R (N ⧸ S)) ≤ I • (⊤ : Submodule R (N ⧸ S)) := by
      have h1 := congrArg (Submodule.map S.mkQ) (h I hI)
      rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
      have h2 : Submodule.map S.mkQ S = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        simpa [Submodule.mem_bot] using (Submodule.Quotient.mk_eq_zero S).mpr hx
      rw [h2, bot_sup_eq] at h1
      rw [h1]
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
      (Module.Finite.fg_top) hle'
    have hrA : r ∈ Module.annihilator R (N ⧸ S) :=
      Module.mem_annihilator.mpr fun m => hr m trivial
    have hrI : r ∈ I := hle hrA
    have h1I : (1 : R) ∈ I := by
      have := I.sub_mem hrI hr1
      simpa using this
    exact hI.ne_top ((Ideal.eq_top_iff_one I).mpr h1I)
  have htop : Module.annihilator R (N ⧸ S) = ⊤ := by
    by_contra hne
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hne
    exact key I hI hle
  have hS : S = ⊤ := by
    rw [eq_top_iff]
    intro n _
    have h1 : (1 : R) ∈ Module.annihilator R (N ⧸ S) := htop ▸ Submodule.mem_top
    have h2 := Module.mem_annihilator.mp h1 (S.mkQ n)
    rw [one_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  exact LinearMap.range_eq_top.mp hS

end GlobalTheory
end
