module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveLatticeCoordMapEquivariantDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdicCompletion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.IntPointFn

theorem comp_padd_c_zero (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c 0)).left = b.left := by
  rw [← Over.comp_left, GlobalTheory.Poinc.ThetaOne.c_zero]
  simp only [padd, comp_one]
  show (b ≫ (𝟙 D.P.A * 1)).left = b.left
  rw [_root_.mul_one, Category.comp_id]

theorem comp_toUnit_c_zero (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (toUnit D.P.A ≫ D.c 0).left = (η[D.P.A]).left := by
  rw [← Over.comp_left, GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq, ← Category.assoc,
    toUnit_unique (b ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

theorem comp_toUnit_eta (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (η[D.P.A]).left := by
  rw [← Over.comp_left, ← Category.assoc, toUnit_unique (b ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

end GlobalTheory.IntPointFn

namespace GlobalTheory.IntPointFn

theorem fn_of_theta : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ f : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ b.left) z J * (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom f) * (val ρ₀ r z J).val := by
  intro V _ _ D θ b t ht ρ₀ hρ
  have hL := D.P.isLB
  have hu := mulGen_isGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ ρ₀) ht (invGen_isGen _ _ _ _ hρ)
  have hF : FormEq (Sum.elim (fun k => b.left ≫ D.famφB 0 k)
      (Sum.elim ![(η[D.P.A]).left, b.left] (fun _ : PUnit => eSec D.P.A)))
      (Sum.elim (DegPre.famε 1) (Sum.elim (DegPre.lineε 1) (fun _ : PUnit => -(1 : ℤ))))
      (PEmpty.elim : PEmpty → (Sp V ⟶ D.P.A.left)) (PEmpty.elim : PEmpty → ℤ) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Fin.prod_univ_two,
      Fintype.prod_empty, Fintype.prod_unique, DegPre.famφB, DegPre.famε, DegPre.lineε, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, Nat.cast_one, sub_self,
      comp_padd_c_zero, comp_toUnit_c_zero, comp_toUnit_eta, eSec]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
    abel
  obtain ⟨s', hs'⟩ := exists_sec hL hF (pullMulSec (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) b.left
    (LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ ρ₀)) hu)
  have hle : (⊤ : (Sp V).Opens) ≤ LB.wchart D.P.L (PEmpty.elim : PEmpty → (Sp V ⟶ D.P.A.left)) (PEmpty.elim : PEmpty → D.P.L.ι) :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
    (((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι))), fun Z r z J hJ => ?_⟩
  have e1 := (hs' Z r z J hJ).trans (sval_pullMulSec _ _ _ hu r z hJ)
  rw [val_mul hJ, val_inv,
    sval_of s' r z J (PEmpty.elim : PEmpty → D.P.L.ι) (fun k => k.elim)] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
      (((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι)))) =
      ((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι)) := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have e3 := gs_res r z hle (by trivial) (s'.f (PEmpty.elim : PEmpty → D.P.L.ι))
  rw [e2]
  erw [e3, e1]
  rw [Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel,
    Units.val_one, _root_.mul_one]

end GlobalTheory.IntPointFn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_function_thetaSection_integralPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ f : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ b.left) z J * (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom f) * (val ρ₀ r z J).val := by
  first | exact @GlobalTheory.IntPointFn.fn_of_theta | exact GlobalTheory.IntPointFn.fn_of_theta | (intros; apply GlobalTheory.IntPointFn.fn_of_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFrameSqOfTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFrameSqOfTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
noncomputable section

namespace GlobalTheory.USep

open GlobalTheory.TorsFrame

theorem isTorsFrame_sq : ∀ (S : Scheme.{0}) (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (n : ℕ) (T : Over S)
    (x : T ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))),
    IsTorsFrame P rig n x τ → IsTorsFrame P rig (n ^ 2) x τ := by
  intro S P rig n T x τ ⟨hx, hτ, α, hα, hN, hC⟩
  have hL := P.isLB
  have eN : (mulA P.A n).left ≫ (mulA P.A n).left = (mulA P.A (n ^ 2)).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ← pow_mul, ← sq]
  have ex : x.left ≫ (mulA P.A n).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx, one_left]
  obtain ⟨α', hα', vα'⟩ := exists_gen hL (φ' := ![𝟙 P.A.left, (mulA P.A (n ^ 2)).left])
    (ε' := ![((n ^ 2 : ℕ) : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id, eN]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (mulA P.A n).left) (GeneratorPullback.powGen P.L _ _ α (n ^ 2)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.powGen_isGen _ _ _ _ hα _))
  have vα₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J), Good P.L z J →
      val α' r z J = val α (r ≫ (mulA P.A n).left) z J * val α r z J ^ (n ^ 2) := fun Z r z J hJ => by
    rw [vα' _ _ z J hJ, val_mul hJ, val_pull hJ, val_powGen]
  refine ⟨by rw [sq, pow_mul, hx, one_pow], hτ, α', hα', corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩
  · have h0 := val_corr hJ hN (𝟙 (𝟙_ (Over S)).left)
    rw [val_pull hJ, val_mul hJ, val_inv] at h0 ⊢
    rw [vα₂ _ _ z J hJ, Category.assoc, eSec_mulA, h0]
    have hp : ∀ k : ℤ, val (rigPow P.A P.L rig k) (𝟙 (𝟙_ (Over S)).left) z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig (𝟙 (𝟙_ (Over S)).left) z J ^ k := fun k => map_zpow _ _ _
    rw [hp, hp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    push_cast
    module
  · have h1 := val_corr hJ hC (𝟙 T.left)
    have h2 := val_corr hJ hN T.hom
    have hp : ∀ k : ℤ, val (rigPow P.A P.L rig k) T.hom z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig T.hom z J ^ k := fun k => map_zpow _ _ _
    have hf : ∀ k : ℤ, val (powFrame P.A P.L x τ k) (𝟙 T.left) z J = val τ (𝟙 T.left) z J ^ k :=
      fun k => map_zpow _ _ _
    rw [val_pull hJ, val_mul hJ, val_inv, hp] at h2
    rw [hf, val_mul hJ, val_pull hJ, val_rigT rig _ z hJ] at h1
    simp only [Category.id_comp] at h1
    rw [hf, val_mul hJ, val_pull hJ, val_rigT rig _ z hJ]
    simp only [Category.id_comp]
    rw [vα₂ _ _ z J hJ, ex, h2]
    have ha : val α x.left z J = val τ (𝟙 T.left) z J ^ ((n : ℤ) ^ 2) *
        (val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig T.hom z J)⁻¹ := by
      rw [h1, mul_inv_cancel_right]
    rw [ha]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    push_cast
    module

end GlobalTheory.USep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFrameSqOfTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorsionFrame_sq_of_torsion : ∀ (S : Scheme.{0}) (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (n : ℕ) (T : Over S) (x : T ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))), IsTorsFrame P rig n x τ → IsTorsFrame P rig (n ^ 2) x τ := by
  first | exact @GlobalTheory.USep.isTorsFrame_sq | exact GlobalTheory.USep.isTorsFrame_sq | (intros; apply GlobalTheory.USep.isTorsFrame_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProdIsoOfPowIsoBirigidified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProdIsoOfPowIsoBirigidified
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BirigidRoot

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem pow_comp_hom {Z H : Over S} [GrpObj H] (f : A ⟶ H) [IsMonHom f] (x : Z ⟶ A) (n : ℕ) :
    (x ^ n) ≫ f = (x ≫ f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem pull_eq_evc {P : LB (A ⊗ A).left} (hP : P.IsLB) {Y : Over S} (w : Y ⟶ A ⊗ A) :
    CechPic.pull w.left (cls P hP) = evc hP (w ≫ fst A A) (w ≫ snd A A) := by
  rw [evc, lift_comp_fst_snd]

theorem cube_rel (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : P.IsLB) {Y : Over S}
    (x y z : Y ⟶ A ⊗ A) :
    CechPic.pull (x * y * z).left (cls P hP) - CechPic.pull (x * y).left (cls P hP)
      - CechPic.pull (x * z).left (cls P hP) - CechPic.pull (y * z).left (cls P hP)
      + CechPic.pull x.left (cls P hP) + CechPic.pull y.left (cls P hP) + CechPic.pull z.left (cls P hP)
      - CechPic.pull (1 : Y ⟶ A ⊗ A).left (cls P hP) = 0 := by
  have hX := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have t := GlobalTheory.CubeTop.cubeTheorem S (A ⊗ A) hX P hP Y x y z
  have z0 := (cls_linComb hP _ _ (LB.isLB_linComb hP _ _)).symm.trans
    ((cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 t)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    one_zsmul, neg_one_zsmul, add_zero] at z0
  rw [← z0]
  abel

theorem additive_of_birigid (hA : IsAbelianScheme A) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (h₁ : Triv (ev P (1 : A ⟶ A) (𝟙 A))) (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ A))) :
    IsAdditive P ∧ IsAdditive (swap P) := by
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (BirigidLift.isAdditive_swap_iff hP).2 fun Y a t t' ↦ ?_⟩
  · have e := cube_rel hA hP (lift a 1) (lift a' 1) (lift 1 t)
    simp only [pull_eq_evc hP, MonObj.mul_comp, lift_fst, lift_snd, MonObj.one_comp, _root_.mul_one,
      _root_.one_mul, evc_one_right hP h₂, evc_one_left hP h₁] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := cube_rel hA hP (lift a 1) (lift 1 t) (lift 1 t')
    simp only [pull_eq_evc hP, MonObj.mul_comp, lift_fst, lift_snd, MonObj.one_comp, _root_.mul_one,
      _root_.one_mul, evc_one_right hP h₂, evc_one_left hP h₁] at e
    rw [← sub_eq_zero, ← e]
    abel

end GlobalTheory.BirigidRoot

theorem GlobalTheory.BirigidRoot.iso_of_lbPow_iso : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ)
    (P₁ P₂ : LB (G2 A).left), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → P₁.IsLB →
    (∃ t : (P₁.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P₁.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → P₂.IsLB →
    (∃ t : (P₂.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P₂.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso (lbPow P₁ k) (lbPow P₂ k) →
    LBIso P₁ P₂ := by
  intro S A _ _ k P₁ P₂ hA hk _ hP₁ h₁ h₂ hP₂ h₁' h₂' e
  obtain ⟨a₁, b₁⟩ := GlobalTheory.BirigidRoot.additive_of_birigid hA hP₁ h₁ h₂
  obtain ⟨a₂, b₂⟩ := GlobalTheory.BirigidRoot.additive_of_birigid hA hP₂ h₁' h₂'
  obtain ⟨D, _, Q, -, -, q, q'⟩ := GlobalTheory.dualAbelianScheme S A hA
  obtain ⟨x₁, hx₁, ex₁⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP₁ a₁ b₁
  obtain ⟨x₂, hx₂, ex₂⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP₂ a₂ b₂
  have hk' : k • cls P₁ hP₁ = k • cls P₂ hP₂ := by
    rw [← cls_lbPow hP₁ k (LB.isLB_linComb hP₁ _ _), ← cls_lbPow hP₂ k (LB.isLB_linComb hP₂ _ _)]
    exact (cls_eq_iff _ _).2 e
  have pw : ∀ (y : A ⟶ D) (n : ℕ), evc q.isLB (fst A A) (snd A A ≫ y ^ n) =
      n • evc q.isLB (fst A A) (snd A A ≫ y) := by
    intro y n
    induction n with
    | zero => rw [pow_zero, MonObj.comp_one, zero_smul]; exact evc_one_right q.isLB q.zero _
    | succ n ih =>
      rw [pow_succ, MonObj.comp_mul, (GlobalTheory.BirigidLift.isAdditive_swap_iff q.isLB).1 q'.additive, ih, succ_nsmul]
  have hpow : x₁ ^ k = x₂ ^ k := GlobalTheory.BirigidLift.dual_ext q (by rw [pw, pw, ← ex₁, ← ex₂, hk'])
  have hx : x₁ = x₂ := by
    obtain ⟨hfl, hsu, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA k hk
    haveI := hfl
    haveI := hsu
    haveI : Epi ((𝟙 A) ^ k).left := Flat.epi_of_flat_of_surjective _
    have c : (((𝟙 A) ^ k) ≫ x₁).left = (((𝟙 A) ^ k) ≫ x₂).left := by
      rw [GlobalTheory.BirigidRoot.pow_comp_hom, GlobalTheory.BirigidRoot.pow_comp_hom, Category.id_comp, Category.id_comp, hpow]
    rw [Over.comp_left, Over.comp_left] at c
    exact Over.OverMorphism.ext ((cancel_epi ((𝟙 A) ^ k).left).1 c)
  subst hx
  exact (cls_eq_iff hP₁ hP₂).1 (ex₁.trans ex₂.symm)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProdIsoOfPowIsoBirigidifiedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_prod_iso_of_pow_iso_birigidified : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ) (P₁ P₂ : LB (G2 A).left), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → P₁.IsLB → (∃ t : (P₁.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P₁.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → P₂.IsLB → (∃ t : (P₂.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P₂.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso (lbPow P₁ k) (lbPow P₂ k) → LBIso P₁ P₂ := by
  first | (exact @GlobalTheory.BirigidRoot.iso_of_lbPow_iso) | (exact GlobalTheory.BirigidRoot.iso_of_lbPow_iso) | (intros; apply GlobalTheory.BirigidRoot.iso_of_lbPow_iso  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameIsValueAtThetaConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameIsValueAtThetaConstant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section
namespace GlobalTheory.Ex.OneGen

open TorsFrame CommPairing

theorem ThG.exists_isTorsFrame_isValueAt : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m : ℕ), Odd m → ∀ (T : Over S) (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (y : T ⟶ P.A) (c : Γ(T.left, ⊤)), GlobalTheory.Ex.OneGen.ThG P.A P.L rig m th y c → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (y ^ m).left) (fun _ => 1)), IsTorsFrame P rig m (y ^ m) τ ∧ IsValueAt P.A P.L ((1 : ℕ) : ℤ) th (y ^ m) (powFrame P.A P.L (y ^ m) τ ((1 : ℕ) : ℤ)) c := by
  intro S _ P rig hr m hm T th y c H
  obtain ⟨hy, t, αT, s₁, θ, hαT, hnT, hs₁, hθ, ht, hc⟩ := H
  have hLaw : Laws := abelianSchemeLaws_all.1
  have hL := P.isLB
  obtain ⟨α₀, h₀⟩ := hLaw.mulPull S P m
  obtain ⟨α, hα, vα⟩ := exists_norm hL hr h₀
  obtain ⟨ν, hν⟩ := exists_gen_negLB hLaw.globalFns S P 1 T
  have e₁ : y.left ≫ (mulA P.A m).left = (y ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have e₂ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, lift_snd, GlobalTheory.TorsFrame.one_left]
  have e₃ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (translPt P.A θ.pt).left = y.left := by
    rw [← Over.comp_left, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, hθ.pt_eq]
    exact congrArg (·.left) (_root_.mul_one y)
  have e₄ : (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]

  obtain ⟨α', hα', vα'⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₄]
      push_cast; rfl)
    (LB.pullGen P.L _ _ α (snd T P.A).left) (DVR.pullGen_isGen _ _ _ _ hα _)

  have eα : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ P.A).left) (z : Z) (J), Good P.L z J →
      val αT r z J = val α (r ≫ (snd T P.A).left) z J := by
    intro Z r z J hJ
    refine (gen_unique hL (fst T P.A).left (ptSecT P.A 1).left NormTheta.ptSec_fst
      (CommPairing.surj_fst hLaw.globalFns P.isAb T) hαT hα' (fun w J hJ => ?_) Z r z J hJ).trans
      ((vα' _ _ z J hJ).trans (val_pull hJ _ _ _))
    have a := val_corr hJ hnT (𝟙 _)
    rw [val_pull hJ, Category.id_comp, Ex.OneGen.val_rigT _ _ w hJ, Category.id_comp] at a
    rw [a, vα' _ _ w J hJ, val_pull hJ, show (ptSecT P.A 1).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A from e₂,
      vα _ _ w J hJ, zpow_sub_one, zpow_natCast]
  obtain ⟨τ, hτ, vτ⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (y ^ m).left) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen P.L _ _ _ _ (GeneratorPullback.powGen P.L _ _
        (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) rig T.hom) (m ^ 2))
      (LB.invGen P.L _ _ (LB.mulGen P.L _ _ _ _
        (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(m ^ 2 : ℕ), -(m ^ 2 : ℕ)] θ.φ
          (lift (𝟙 T) (1 : T ⟶ P.A)).left) (LB.pullGen P.L _ _ α y.left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _) _)
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
        (DVR.pullGen_isGen _ _ _ _ hα _))))
  have c₀ : ∀ (z : T.left) (J), Good P.L z J → val (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left]
      ![(m ^ 2 : ℕ), -(m ^ 2 : ℕ)] θ.φ (lift (𝟙 T) (1 : T ⟶ P.A)).left) (𝟙 T.left) z J =
        tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J := fun z J hJ =>
    (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)

  have vτ' : ∀ (z : T.left) (J), Good P.L z J → val τ (𝟙 T.left) z J =
      val rig T.hom z J ^ (m ^ 2) * (tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J * val α y.left z J)⁻¹ := by
    intro z J hJ
    rw [vτ _ _ z J hJ, val_mul hJ, val_inv, val_mul hJ, c₀ z J hJ, val_powGen, val_pull hJ, val_pull hJ,
      Category.id_comp, Category.id_comp]
  refine ⟨τ, ⟨by rw [← pow_mul, ← sq, hy], hτ, α, hα, corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩, ThetaCoord.isValueAt_of_sv hL (EvVal.powFrame_isGen P.A P.L _ τ hτ _)
      fun z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).trans ((vα _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  · have a : val (powFrame P.A P.L (y ^ m) τ ((m : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ (m ^ 2) :=
      (map_zpow _ _ _).trans (by rw [← Nat.cast_pow, zpow_natCast]; rfl)
    have b := tval_pow hLaw.globalFns P.isAb hL hν hm hα hy hθ hJ
    rw [GlobalTheory.TorsFrame.one_left, vα _ _ z J hJ] at b
    rw [a, vτ' z J hJ, val_mul hJ, val_pull hJ, GlobalTheory.TorsFrame.val_rigT rig _ z hJ, Category.id_comp, Category.id_comp,
      mul_pow, inv_pow, mul_pow, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  ·
    have p₁ : (ptSecT P.A 1).left ≫ (translT P.A θ.pt).left = (lift (𝟙 T) y).left := by
      rw [ptSecT, ThetaCoord.lift_translT, Category.id_comp, hθ.pt_eq, _root_.mul_one]
    have p₂ : (lift (𝟙 T) y).left ≫ (mulT P.A T m).left = (lift (𝟙 T) (y ^ m)).left :=
      ThetaCoord.lift_mulT _ _ _
    have q₁ := VVRank.sv_of_isTwistPull P.A ht (ptSecT P.A 1).left z hJ
    have q₂ := VVRank.sv_of_isTwistPull P.A hs₁ (lift (𝟙 T) y).left z hJ
    rw [p₁, q₂, p₂, hc z J hJ, Ex.OneGen.val_rigT _ _ z hJ, Category.id_comp] at q₁
    rw [eα _ _ z J hJ, show (lift (𝟙 T) y).left ≫ (snd T P.A).left = y.left by rw [← Over.comp_left, lift_snd]] at q₁
    have v₁ : val (powFrame P.A P.L (y ^ m) τ ((1 : ℕ) : ℤ)) (𝟙 T.left) z J = val τ (𝟙 T.left) z J :=
      (map_zpow _ _ _).trans (zpow_one _)
    rw [v₁, vτ' z J hJ]
    rw [zpow_natCast, show val θ.φ (ptSecT P.A 1).left z J = tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J from rfl] at q₁
    have hu := (tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J * val α y.left z J).inv_mul
    rw [Units.val_mul] at hu
    rw [Units.val_mul, ← _root_.mul_assoc, q₁]
    linear_combination (-(VVRank.sv P.A th (lift (𝟙 T) (y ^ m)).left z J)) * hu

end GlobalTheory.Ex.OneGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameIsValueAtThetaConstantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionFrame_isValueAt_thetaConstant : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m : ℕ), Odd m → ∀ (T : Over S) (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (y : T ⟶ P.A) (c : Γ(T.left, ⊤)), GlobalTheory.Ex.OneGen.ThG P.A P.L rig m th y c → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (y ^ m).left) (fun _ => 1)), IsTorsFrame P rig m (y ^ m) τ ∧ IsValueAt P.A P.L ((1 : ℕ) : ℤ) th (y ^ m) (powFrame P.A P.L (y ^ m) τ ((1 : ℕ) : ℤ)) c := by
  first | exact @GlobalTheory.Ex.OneGen.ThG.exists_isTorsFrame_isValueAt | exact GlobalTheory.Ex.OneGen.ThG.exists_isTorsFrame_isValueAt | (intros; apply GlobalTheory.Ex.OneGen.ThG.exists_isTorsFrame_isValueAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPullbackLocalMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPullbackLocalMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocalPull


set_option maxHeartbeats 3200000 in
theorem exists_pelUnif_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (θ : R →+* V), IsLocalHom θ → ∀ f : R, θ f ≠ 0 → (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg θ P.D.toPre P'.D.toPre), Nonempty (SABMap t' t (spMap θ)) ∧ (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧ (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (P.oD.onB.act x)) := by
  intro E _ _ _ H R V _ _ _ _ _ _ hR hV t P θ hθ f hf hψ
  letI := H.starRing
  obtain ⟨-, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have aR := hR.1
  have aV := hV.1
  have hI : (maximalIdeal R).map θ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff θ a).2 ha
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (spMap θ) t
  let t' : SAB H (Sp V) := ⟨(Over.pullback (spMap θ)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (spMap θ) := m₁
  have hm₀ : m₀.φ = pullback.fst t.G.hom (spMap θ) := hm₁
  let W : (Sp R).Opens := PrimeSpectrum.basicOpen f
  have hψW : ∀ y, PsiUnitOn P.D.toPre y (W : Set (Sp R)) := hψ
  have hgen : (specOf θ).base (genericPoint (Sp V)) ∈ W := by
    rw [genericPoint_eq_bot_of_affine]
    show f ∉ Ideal.comap θ ⊥
    rw [Ideal.mem_comap, Ideal.mem_bot]
    exact hf

  let x : Sp (FractionRing V) ⟶ Sp R := jK V ≫ specOf θ
  have hxW : Set.range x ⊆ (W : Set (Sp R)) := by
    rintro _ ⟨z, rfl⟩
    have hz : (jK V).base z = genericPoint (Sp V) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap V (FractionRing V)) z.asIdeal = ⊥
      haveI := z.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
    show (specOf θ).base ((jK V).base z) ∈ W
    rw [hz]
    exact hgen
  obtain ⟨hamp, hkt⟩ := GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre R hR P.D P.A t.G t.semi P.U W hψW (FractionRing V) x hxW
  obtain ⟨PK, cubK, symK, adjK, primK, mK, hmK⟩ := sabPull CubePf.cubePull x t
  let tK : SAB H (Sp (FractionRing V)) := ⟨(Over.pullback x).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PK, cubK, symK, adjK, primK⟩
  have hLK : LBIso tK.PP.L (P.U.LG.L.pull (pullback.fst t.G.hom x)) := by
    obtain ⟨wK, gK, -⟩ := mK.lin
    rw [P.bundle, ← hmK]
    exact ⟨wK, gK⟩
  have hMK : (P.U.LG.L.pull (pullback.fst t.G.hom x)).IsLB := pull_isLB P.U.LG.isLB _
  have hp : IsProper tK.G.hom := GlobalTheory.ZH.isProper_hom_of_relAmple hamp
  haveI := hp
  have hA : RelAmple tK.G tK.PP.L :=
    GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull (f := 𝟙 _) (φ := 𝟙 _) (IsPullback.of_horiz_isIso ⟨by simp⟩) hMK tK.PP.isLB
      (hLK.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl)) hamp
  have hK : KTriv tK.G tK.PP.L := GlobalTheory.MulDescent.kTriv_of_lbIso hMK tK.PP.isLB hLK.symm hkt

  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have dA : d = P.A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    P.A.smoothDim (eSec P.A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hpbG := isGrpPullback_pullback t.G x
  have hdB : SmoothOfRelativeDimension P.A.g tK.G.hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpbG.1 hd
  let A' : PolAV (Sp (FractionRing V)) := GlobalTheory.GenericPol.toPolAV tK P.A.g hdB hp hA hK
  let oA' : A'.OAct (𝓞 E) := ⟨tK.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj tK⟩
  have mR : IsMonHom (Iso.refl t'.G).hom := by show IsMonHom (𝟙 _); infer_instance
  have hbc : IsGrpPullback t'.G t.G (specOf θ) ((Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ)) :=
    ((isGrpPullback_of_iso (Iso.refl t'.G)).comp (isGrpPullback_pullback t.G (specOf θ))).congr (Category.id_comp _) rfl
  have hgK := (isGrpPullback_pullback t'.G (jK V)).comp hbc
  obtain ⟨eA, meA, heA⟩ := grpPullback_iso hgK hpbG
  have wA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (P.U.LG.L.pull (pullback.fst t'.G.hom (jK V) ≫ (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ))),
      wA.IsGen := by
    rw [← heA]
    exact LBIso.trans (pull_isLB tK.PP.isLB _) (pull_isLB hMK _) (pull_isLB P.U.LG.isLB _)
      (GlobalTheory.RigidBundleGlue.LBIso.pull hLK _) ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen P.U.LG.isLB _ _⟩

  have hbc' : (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (specOf θ) = pullback.fst t.G.hom (spMap θ) :=
    Category.id_comp _
  obtain ⟨wL, heL, gL, rL⟩ := rigIso_congr P.bundle m₀.cm m₀.lin (hbc'.trans hm₀.symm) (e := specOf θ) m₀.base.symm
  have hψn := GlobalTheory.PelCoordPull.nonempty_psiOn P.D.toPre W ⟨_, hgen⟩ hψW
  have extA₀ : ∀ a, (Over.pullback (jK V)).map (t'.act.act a) ≫ eA.hom =
      eA.hom ≫ (OAct.pullback x t.G t.act).act a := by
    intro a
    apply Over.OverMorphism.ext
    apply hpbG.1.hom_ext
    · have a₁ : ((Over.pullback (jK V)).map (t'.act.act a)).left ≫ pullback.fst t'.G.hom (jK V) =
          pullback.fst t'.G.hom (jK V) ≫ (t'.act.act a).left := pullback.lift_fst _ _ _
      have a₂ : (t'.act.act a).left ≫ pullback.fst t.G.hom (specOf θ) =
          pullback.fst t.G.hom (specOf θ) ≫ (t.act.act a).left := pullback.lift_fst _ _ _
      have a₃ : ((OAct.pullback x t.G t.act).act a).left ≫ pullback.fst t.G.hom x =
          pullback.fst t.G.hom x ≫ (t.act.act a).left := pullback.lift_fst _ _ _
      have i₀ : (Iso.refl t'.G).hom.left = 𝟙 _ := rfl
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₃, heA, ← Category.assoc eA.hom.left, heA,
        i₀, Category.id_comp, reassoc_of% a₁, a₂, Category.assoc]
    · exact (Over.w _).trans (Over.w _).symm
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := h4.unifBaseChange R V _ _ aR aV θ hI P.D P.A t.G t.semi P.U W hψn hgen
    t'.G (Iso.refl _) mR A' rfl eA meA wA t'.PP wL heL gL rL
  have extA : ∀ a, (Over.pullback (jK V)).map (t'.act.toRingAct.act a) ≫ U'.gen.hom = U'.gen.hom ≫ oA'.act a := by
    intro a
    rw [hgenU]
    exact extA₀ a
  obtain ⟨mod', oD', xl, el, lin', w0'⟩ := h5.oLinBaseChange R V _ _ aR aV θ P.D P.A t.G P.U t'.G (Iso.refl _) mR
    A' D' hD U' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct
    (fun a => (Category.comp_id _).trans (Category.id_comp _).symm) oA' extA
  let P' : PELUnif (maximalIdeal V) t' :=
    { D := D'
      mod := mod'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := hLG
      lin := lin'
      w0 := w0' H.w0 P.w0 }
  exact ⟨t', P', hD, ⟨m₀⟩, xl, el⟩

end GlobalTheory.LocalPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPullbackLocalMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearUniformisation_pullback_localMap : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (θ : R →+* V), IsLocalHom θ → ∀ f : R, θ f ≠ 0 → (∀ y, PsiUnitOn P.D.toPre y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) → ∃ (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg θ P.D.toPre P'.D.toPre), Nonempty (SABMap t' t (spMap θ)) ∧ (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧ (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map (P.oD.onB.act x)) := by
  first | exact @GlobalTheory.LocalPull.exists_pelUnif_pull | exact GlobalTheory.LocalPull.exists_pelUnif_pull | (intros; apply GlobalTheory.LocalPull.exists_pelUnif_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeMapAtClosedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOverOpenPartSubsetAbelianLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOverOpenPartSubsetAbelianLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.KerAb

theorem subset_abLocus {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Zh : ZHOut ρ M U₀ EE) (hO : S.Over₀ M U₀) :
    (U₀ : Set M.Z) ⊆ abLocus Zh.G := by
  intro z hz
  rw [Zh.ab]
  show S.TT M z = ⊥
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  have h1 : S.perp ⊥ = ⊤ := by
    refine top_unique fun a _ h hh => ?_
    rw [AddSubgroup.mem_bot.mp hh]
    simp [ZH.eStd]
  rw [ZH.ThetaSys.TT, ZH.ThetaSys.HH, hO.supI_eq hz, S.supp, ← h1, hpp]

theorem ker_mem_and_subset_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∀ (R : Type) [CommRing R] (q : Sp R ⟶ M.Z) (V' : Type) [CommRing V'] [IsDomain V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → spMap g' ≫ q = spMap h ≫ ξ → (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) ∈ q ⁻¹' (U₀ : Set M.Z) ∧ (U₀ : Set M.Z) ⊆ abLocus out.G := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm T ξ hξ R _ q V' _ _ h g' hh hq
  refine ⟨?_, subset_abLocus out hAdm.1⟩
  obtain ⟨ξ₀, h₀, -⟩ := hξ
  let w : Sp V' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V')
  let v : Sp (FractionRing T.V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing T.V))
  have e₁ : spMap g' w = (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) :=
    PrimeSpectrum.ext (RingHom.ker_eq_comap_bot g').symm
  have e₂ : spMap h w = jK T.V v := by
    refine PrimeSpectrum.ext ?_
    show Ideal.comap h ⊥ = Ideal.comap (algebraMap T.V (FractionRing T.V)) ⊥
    rw [← RingHom.ker_eq_comap_bot, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hh,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective T.V (FractionRing T.V))]
  have e₃ : q (spMap g' w) = U₀.ι (ξ₀ v) := by
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply, e₂, ← Scheme.Hom.comp_apply, ← h₀, Scheme.Hom.comp_apply]
  rw [← e₁]
  show q (spMap g' w) ∈ U₀
  rw [e₃]
  exact (ξ₀ v).2

end GlobalTheory.UPoinc.KerAb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOverOpenPartSubsetAbelianLocusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_over_openPart_subset_abelianLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∀ (R : Type) [CommRing R] (q : Sp R ⟶ M.Z) (V' : Type) [CommRing V'] [IsDomain V'] (h : T.V →+* V') (g' : R →+* V'), Function.Injective h → spMap g' ≫ q = spMap h ≫ ξ → (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) ∈ q ⁻¹' (U₀ : Set M.Z) ∧ (U₀ : Set M.Z) ⊆ abLocus out.G := by
  first | exact @GlobalTheory.UPoinc.KerAb.ker_mem_and_subset_abLocus | exact GlobalTheory.UPoinc.KerAb.ker_mem_and_subset_abLocus | (intros; apply GlobalTheory.UPoinc.KerAb.ker_mem_and_subset_abLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeMapAtClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.TraitAtClosed

theorem exists_trait_lattice_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsGrpPullback G out.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ T.P.D.toPre.X), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (g' r ^ 2) (h T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm f hf hT x hx R _ _ _ j hR hj G _ _ gm hgm D A U hLB hPsi m hm T ξ hξ hsp
  obtain ⟨hft, hcpl⟩ := GlobalTheory.T.closedPoint_completion_positive_residueChar X₁.o₁ X₁.Ω₁ M x hx
  obtain ⟨-, p, hp, hpR⟩ := hcpl R j hj
  haveI := hft
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : CharZero T.V := T.cdvr.2.2
  let f₀ : M.Z.presheaf.stalk x →+* T.V := (M.Z.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ).hom
  have hf₀ : spMap f₀ ≫ M.Z.fromSpecStalk x = ξ := by
    have e : spMap f₀ = Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (M.Z.presheaf.stalkSpecializes hsp) := by
      simp only [f₀, spMap, CommRingCat.ofHom_hom, Spec.map_comp]
    rw [e, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  obtain ⟨V', _, _, _, h, g', hcomp, hinj, hloc, hgj, hirr⟩ :=
    GlobalTheory.TraitLift.exists_lift_of_isCpl (M.Z.presheaf.stalk x) R T.V j hj f₀
  have eq1 : spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ := by
    have e : spMap g' ≫ spMap j = spMap h ≫ spMap f₀ := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hgj]
    rw [← hf₀, ← Category.assoc, e, Category.assoc]
  haveI hch : CharZero V' := charZero_of_injective_ringHom hinj
  have hV' : GlobalTheory.Mum.Base V' := ⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR ⟨inferInstance, hcomp, hch⟩, hch⟩
  obtain ⟨tW, mW, PW, e, he⟩ := GlobalTheory.T.exists_linear_uniformisation_pulled_back_trait E H Dw l Xo c T V' hV' inferInstance h hinj hloc
  obtain ⟨βT, hβT, hLT, hactT⟩ := hT T ξ hξ
  have hβ' : IsGrpPullback tW.G out.G (spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x)) (mW.φ ≫ βT) := by
    rw [eq1]; exact mW.cart.comp hβT
  have w : (mW.φ ≫ βT) ≫ out.G.hom = (tW.G.hom ≫ spMap g') ≫ (spMap j ≫ M.Z.fromSpecStalk x) := by
    rw [hβ'.1.w, Category.assoc]
  let β : tW.G.left ⟶ G.left := hgm.1.lift (mW.φ ≫ βT) (tW.G.hom ≫ spMap g') w
  have hβgm : β ≫ gm = mW.φ ≫ βT := hgm.1.lift_fst _ _ _
  have hβG : β ≫ G.hom = tW.G.hom ≫ spMap g' := hgm.1.lift_snd _ _ _
  have hβ : IsGrpPullback tW.G G (spMap g') β := hgm.cancel (by rw [hβgm]; exact hβ') hβG
  have hLBW : LBIso PW.U.LG.L (U.LG.L.pull β) := by
    rw [PW.bundle]
    exact LBIso.trans tW.PP.isLB (pull_isLB out.L.isLB _) (pull_isLB U.LG.isLB _)
      (LBIso.trans tW.PP.isLB (pull_isLB T.t.PP.isLB _) (pull_isLB out.L.isLB _)
        (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mW) (GlobalTheory.LN.GenericPoint.lbIso_pull hLT mW.φ rfl))
      (GlobalTheory.LN.GenericPoint.lbIso_pull hLB β hβgm.symm).symm
  have hGs : IsSemiAbelian G := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ out.G G gm hgm out.semi
  obtain ⟨hker, hU₀ab⟩ := GlobalTheory.T.kernel_over_openPart_subset_abelianLocus E H Dw l Xo c C X₁ M U₀ EE out hAdm T ξ hξ R
    (spMap j ≫ M.Z.fromSpecStalk x) V' h g' hinj eq1
  have hWo : IsOpen ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z)) :=
    U₀.isOpen.preimage (spMap j ≫ M.Z.fromSpecStalk x).continuous
  have hPsiW : ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z)) :=
    fun y jj V hV hVU => hPsi y jj V hV (hVU.trans (Set.preimage_mono hU₀ab))
  obtain ⟨ρ, hρs, hρc, hρe⟩ := GlobalTheory.T.exists_surjective_lattice_coordMap_equivariant_dvr R hR G hGs D A U V' hV' inferInstance tW.G tW.semi PW.D PW.A PW.U g' β p hp
    hpR _ hWo hPsiW hker hβ hLBW
  refine ⟨V', inferInstance, inferInstance, inferInstance, h, g', e.toAddEquiv.toAddMonoidHom.comp ρ, hinj, hirr T.ϖ T.irr,
    eq1, e.surjective.comp hρs, ?_, ?_⟩
  · intro y r hr
    obtain ⟨h0, r', hr', hass⟩ := he (ρ y)
    exact ⟨h0, ((hρc y r r' hr hr').pow_pow (n := 2)).trans hass⟩
  · intro a y
    obtain ⟨fR, hfRmon, hfRgm, hfRchar⟩ := hm a
    have hcompat : (tW.act.act a).left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc ((tW.act.act a).left ≫ β) ≫ gm = (tW.act.act a).left ≫ mW.φ ≫ βT := by rw [Category.assoc, hβgm]
          _ = mW.φ ≫ (T.t.act.act a).left ≫ βT := by rw [← Category.assoc, mW.act a, Category.assoc]
          _ = mW.φ ≫ βT ≫ (f a).left := by rw [hactT a]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, hfRgm, reassoc_of% hβgm]
      · rw [Category.assoc, hβG, Category.assoc, Over.w fR, hβG, ← Category.assoc, Over.w (tW.act.act a)]
    have key := hρe fR (tW.act.act a) hfRmon (tW.act.hom a) hcompat (m a) _ hfRchar (GlobalTheory.T.endomorphism_characterAction_conjugate E H V' hV' tW PW a) y
    show e (ρ (m a y)) = H.bar a • e (ρ y)
    rw [key]
    exact e.map_smul _ _

end GlobalTheory.UPoinc.TraitAtClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeMapAtClosedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_lattice_map_at_closedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsGrpPullback G out.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ T.P.D.toPre.X), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (g' r ^ 2) (h T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  first | exact @GlobalTheory.UPoinc.TraitAtClosed.exists_trait_lattice_map | exact GlobalTheory.UPoinc.TraitAtClosed.exists_trait_lattice_map | (intros; apply GlobalTheory.UPoinc.TraitAtClosed.exists_trait_lattice_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongMonomialFamilyEqSpanMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongMonomialFamilyEqSpanMonomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.UGZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

theorem s_ne_zero {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V)
    (k : Fin Cm.m) : Cm.s k ≠ 0 := by
  intro hk
  have hδ : Cm.δ k ≠ 0 := Cm.cone.linearIndependent.ne_zero k
  have hsym := (Cm.cone.mem k).1
  obtain ⟨y, hy⟩ : ∃ y, Cm.δ k y y ≠ 0 := by
    by_contra h
    push_neg at h
    apply hδ
    refine LinearMap.ext₂ fun a b => ?_
    have h1 := h (a + b)
    have h2 := h a
    have h3 := h b
    simp only [map_add (f := _), LinearMap.add_apply] at h1
    rw [hsym b a] at h1
    simp only [LinearMap.zero_apply]
    omega
  obtain ⟨u, n, hn, hc⟩ := Cm.mono y
  have hM : (0 : ℤ) < (l.M' : ℤ) := by exact_mod_cast GlobalTheory.LevelExist.M'_pos l
  have hnk : n k ≠ 0 := by
    intro h0
    have e := hn k
    rw [h0] at e
    simp only [LinearMap.smul_apply, smul_eq_mul, Nat.cast_zero, mul_zero] at e
    rcases mul_eq_zero.1 e with e | e
    · omega
    · exact hy e
  apply GlobalTheory.PsiCoordLocal.ne_zero_of_coord hc
  rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; exact zero_pow hnk), mul_zero]

end GlobalTheory.UGZero

namespace GlobalTheory.UGZero

theorem idlAlong_eq_span_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∃ b : Fin Cm.m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ ((l.M' : ℤ) • Cm.δ k)) ∧ idlAlong J (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) = Ideal.span {∏ k, Cm.s k ^ b k} := by
  intro E _ _ _ H Dw hpq l Xo c C φ hpf d J hJ hval S π hbl V _ _ _ Cm hV ξ hξ
  haveI : Module.Projective (𝓞 E) Cm.P.D.toPre.X := GlobalTheory.Forms.projective_of_int _ _
  have hP := hpf Cm.P.D.toPre.X Cm.rank
  have key0 : ∀ k, ∃ n : ℕ, φ.evalZ ((l.M' : ℤ) • Cm.δ k) = n := fun k =>
    hP.exists_nat (Submodule.smul_mem _ _ (Cm.cone.mem k)) (fun y => by
      simp only [LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (Cm.cone.nonneg k y))
  choose n hn using key0
  refine ⟨fun k => d * n k, fun k => by rw [hn]; push_cast; ring, ?_⟩
  set f := ∏ k, Cm.s k ^ (d * n k) with hf
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.NormBlPrincipal.idlAlong_comap_principal π _ hbl V ξ
  rw [GlobalTheory.PullAlong.idlAlong_comap_eq, GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc] at hg₀
  rw [hg₀]
  have hV' := hV
  obtain ⟨⟨hNoeth, -, hIC, -⟩, hchar⟩ := hV'
  have key : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : V →+* W,
      Function.Injective ψ → IsLocalHom ψ → Ideal.span {ψ g₀} = Ideal.span {ψ f} := by
    intro W _ _ _ hW ψ hψi hψl
    haveI : IsDiscreteValuationRing W := ((GlobalTheory.LN.cDvr_iff W).1 hW).1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hw : ∀ k, ∃ w : ℕ, Associated (ψ (Cm.s k)) (ϖ ^ w) := fun k => by
      have h0 : ψ (Cm.s k) ≠ 0 := fun h => s_ne_zero Cm k (hψi (h.trans (map_zero ψ).symm))
      obtain ⟨w, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
      exact ⟨w, ⟨u⁻¹, by rw [hu, mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩⟩
    choose w hw using hw
    have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp ψ) :=
      (IsFractionRing.injective W (FractionRing W)).comp hψi
    obtain ⟨gam, e⟩ : ∃ gam : FractionRing V →+* FractionRing W,
        gam.comp (algebraMap V (FractionRing V)) = (algebraMap W (FractionRing W)).comp ψ :=
      ⟨IsFractionRing.lift hinj, RingHom.ext fun r => by
        rw [RingHom.comp_apply, RingHom.comp_apply]; exact IsFractionRing.lift_algebraMap hinj r⟩
    have hκ : spMap gam ≫ jK V = jK W ≫ spMap ψ := by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    obtain ⟨t, tK, P, ⟨a1⟩, ⟨a2⟩, be, hbe, hmono, hφbe⟩ :=
      GlobalTheory.UChart.pull_trait Xo c φ V hV Cm W hW ψ hψi hψl ϖ hϖ w hw (spMap gam) hκ
    have hy : (spMap gam ≫ Cm.y) ≫ C.i = jK W ≫ (spMap ψ ≫ ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) := by
      simp only [UCompact.i, Category.assoc]
      rw [reassoc_of% hξ, reassoc_of% hκ]
    obtain ⟨N, hN, hid⟩ := hval W hW ϖ hϖ _ (spMap gam ≫ Cm.y) hy t tK ⟨a1⟩ ⟨a2⟩ P be hbe hmono
    rw [GlobalTheory.TraitOrder.idlAlong_comp, hg₀, Ideal.map_span, Set.image_singleton] at hid
    rw [hid]
    have hNe : N = ∑ k, w k * (d * n k) := by
      have : (N : ℝ) = ((∑ k, w k * (d * n k) : ℕ) : ℝ) := by
        rw [hN, hφbe]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hn]; ring
      exact_mod_cast this
    refine Ideal.span_singleton_eq_span_singleton.2 ?_
    rw [hf, map_prod, hNe, ← Finset.prod_pow_eq_pow_sum]
    refine (Associated.prod Finset.univ (fun k => ψ (Cm.s k ^ (d * n k))) (fun k => ϖ ^ (w k * (d * n k)))
      fun k _ => ?_).symm
    rw [map_pow, pow_mul ϖ (w k)]
    exact (hw k).pow_pow
  haveI := hNoeth
  haveI := hIC
  haveI := hchar
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (s_ne_zero Cm k)
  have hg0 : g₀ ≠ 0 := by
    rintro rfl
    obtain ⟨W, _, _, _, ψ, hW, hψi, hψl⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating V
    have := key W hW ψ hψi hψl
    rw [map_zero, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at this
    exact hf0 (hψi (this.trans (map_zero ψ).symm))
  have hkey' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W →
      ∀ ψ : V →+* W, Function.Injective ψ → IsLocalHom ψ → Associated (ψ g₀) (ψ f) := by
    intro W _ _ _ hc ψ hψi hψl
    have : CharZero W := charZero_of_injective_ringHom hψi
    exact Ideal.span_singleton_eq_span_singleton.1 (key W ((GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hc, this⟩) ψ hψi hψl)
  have d1 := GlobalTheory.Poinc.dvd_of_forall_complete_dvr V g₀ f hf0 fun W _ _ _ hc ψ hψi hψl => (hkey' W hc ψ hψi hψl).symm.dvd
  have d2 := GlobalTheory.Poinc.dvd_of_forall_complete_dvr V f g₀ hg0 fun W _ _ _ hc ψ hψi hψl => (hkey' W hc ψ hψi hψl).dvd
  exact Ideal.span_singleton_eq_span_singleton.2 (associated_of_dvd_dvd d2 d1)

end GlobalTheory.UGZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongMonomialFamilyEqSpanMonomialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealAlong_monomialFamily_eq_span_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∃ b : Fin Cm.m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ ((l.M' : ℤ) • Cm.δ k)) ∧ idlAlong J (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) = Ideal.span {∏ k, Cm.s k ^ b k} := by
  first | exact @GlobalTheory.UGZero.idlAlong_eq_span_monomial | exact GlobalTheory.UGZero.idlAlong_eq_span_monomial | (intros; apply GlobalTheory.UGZero.idlAlong_eq_span_monomial <;> assumption)
end
end
