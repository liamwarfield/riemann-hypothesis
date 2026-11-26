module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq
open GlobalTheory.LogDerProj

noncomputable section
set_option autoImplicit false

namespace GlobalTheory.LogDerProj

theorem exists_pow_smul_eq_of_res_eq {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R)
    [IsLocalization.Away f S] (φ : k →+* R) (hφ : φ.FiniteType) (J : Ideal R) (D₁ D₂ : logSub φ J)
    (h : res (S := S) f φ J D₁ = res (S := S) f φ J D₂) : ∃ c : Submonoid.powers f, c • D₁ = c • D₂ := by
  classical
  set E : Derivation ℤ R R := D₁.1 - D₂.1 with hE
  have hloc : ∀ r, ∃ m : Submonoid.powers f, (m : R) * E r = 0 := by
    intro r
    have h1 := congrArg (fun D => D.1 (algebraMap R S r)) h
    simp only [res_apply] at h1
    have h2 : algebraMap R S (E r) = 0 := by
      rw [hE, Derivation.sub_apply, map_sub, h1, sub_self]
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) S _).1 h2
  choose m hm using hloc
  letI := φ.toAlgebra
  have hft : Algebra.FiniteType k R := hφ
  obtain ⟨s, hs⟩ := hft.out
  let c : Submonoid.powers f := ∏ x ∈ s, m x
  have hcs : ∀ x ∈ s, (c : R) * E x = 0 := by
    intro x hx
    have : (c : R) = (∏ y ∈ s.erase x, m y : Submonoid.powers f) * m x := by
      simp only [c]
      rw [← Submonoid.coe_mul, ← Finset.prod_erase_mul s m hx]
    rw [this, mul_assoc, hm x, mul_zero]
  have hall : ∀ r, (c : R) * E r = 0 := by
    intro r
    have hr : r ∈ Algebra.adjoin k (s : Set R) := by rw [hs]; trivial
    induction hr using Algebra.adjoin_induction with
    | mem x hx => exact hcs x hx
    | algebraMap a =>
      have e1 : D₁.1 (φ a) = 0 := D₁.2.1 a
      have e2 : D₂.1 (φ a) = 0 := D₂.2.1 a
      show (c : R) * E (φ a) = 0
      rw [hE, Derivation.sub_apply, e1, e2, sub_self, mul_zero]
    | add x y _ _ hx hy => rw [map_add (f := _), mul_add, hx, hy, add_zero]
    | mul x y _ _ hx hy =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
      calc (c : R) * (x * E y) + (c : R) * (y * E x) = x * ((c : R) * E y) + y * ((c : R) * E x) := by ring
        _ = 0 := by rw [hx, hy, mul_zero, mul_zero, add_zero]
  refine ⟨c, ?_⟩
  apply Subtype.ext
  ext r
  rw [Submonoid.smul_def, Submonoid.smul_def]
  show ((c : R) • D₁.1) r = ((c : R) • D₂.1) r
  rw [Derivation.smul_apply, Derivation.smul_apply, smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub]
  have := hall r
  rwa [hE, Derivation.sub_apply] at this

end GlobalTheory.LogDerProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEqStatement
open GlobalTheory.LogDerProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_of_logDerivation_extend_eq : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (D₁ D₂ : logSub φ J), res (S := S) f φ J D₁ = res (S := S) f φ J D₂ → ∃ c : Submonoid.powers f, c • D₁ = c • D₂ := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompData

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_isPullDeg_of_valW {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (ψW.psi (xe x)) g z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ (∀ x, hD.xe x = xe x) ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ D'.P.A.left) (y : Y) (a : D.P.L.ι) (c : D'.P.L.ι), gw hD.w f y a c = gw w f y a c := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := hψ x y J J' hJ hJ'
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, fun _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

end GlobalTheory.PullDegCompData

namespace GlobalTheory.Mum

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerSymmetricAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerSymmetricAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section
namespace GlobalTheory.EighthPowerBundle

open GlobalTheory.CechPic

def pre0 {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left)
    (hP : IsSymmetricPair h A P) : SiegPre 0 1 (0 : ℤ) (specZIsTerminal.from S) where
  A := A
  ab := hP.1
  P := P
  isLB := hP.2.2.1
  rig₁ := hP.2.2.2.1
  rig₂ := hP.2.2.2.2.1
  symm := hP.2.2.2.2.2
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := fun k _ _ x β z _ hz => by
    rw [map_zero] at hz
    exact absurd hz z.ne_zero

theorem powLB_props : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left),
    IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → IsAbelianScheme (Out.powObj A 8) ∧ (powLB A P).IsLB ∧
      Out.RelAmple (Out.powObj A 8) (powLB A P) ∧ Out.Rigidified (Out.powObj A 8) (powLB A P) ∧
      Out.Sym (Out.powObj A 8) (powLB A P) := by
  intro S h A _ _ P hP hA
  let c := pre0 h A P hP
  have hA' : Out.RelAmple c.A c.diag := hA
  obtain ⟨hpos, -⟩ := isE8_W8
  let pr : Fin 8 → (Out.powObj A 8 ⟶ A) := Out.powPr A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (powLB A P).IsLB := LB.isLB_linComb hP.2.2.1 _ _
  have hLW : cls (powLB A P) hL = PrincipalIntegral.quad (cls c.P c.isLB) W8 pr := cls_linComb hP.2.2.1 _ _ _
  have hadd := PrincipalIntegral.pair_mul c SemiRigid.globalFns hA'
  exact ⟨AbelianSchemeGerms.isAbelianScheme_powObj A hP.1 7, hL,
    PosDefAmple.relAmple_linComb_of_posDef SemiRigid.globalFns 0 1 8 ℤ 0 S _ c (Out.powObj A 8) pr W8 hmon huniv hA'
      hpos,
    PrincipalIntegral.rigidified hadd hmon hL hLW,
    PrincipalIntegral.sym hadd (PrincipalIntegral.pair_comm c) hmon hL hLW⟩

end GlobalTheory.EighthPowerBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerSymmetricAmpleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighth_power_symmetric_ample : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → IsAbelianScheme (Out.powObj A 8) ∧ (powLB A P).IsLB ∧ Out.RelAmple (Out.powObj A 8) (powLB A P) ∧ Out.Rigidified (Out.powObj A 8) (powLB A P) ∧ Out.Sym (Out.powObj A 8) (powLB A P) := by
  first | exact @GlobalTheory.EighthPowerBundle.powLB_props | exact GlobalTheory.EighthPowerBundle.powLB_props | (intros; apply GlobalTheory.EighthPowerBundle.powLB_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCotValEqTanVal
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def sqToEps {M S : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [CommRing S] [Algebra R S] (k : M →ₗ[R] S) : TrivSqZeroExt R M →ₐ[R] DualNumber S where
  toFun z := (algebraMap R S z.fst, k z.snd)
  map_one' := TrivSqZeroExt.ext (map_one (algebraMap R S)) (map_zero k)
  map_mul' a b := TrivSqZeroExt.ext (map_mul (algebraMap R S) _ _) (by
    change k (a.fst • b.snd + MulOpposite.op b.fst • a.snd) =
      algebraMap R S a.fst * k b.snd + k a.snd * algebraMap R S b.fst
    rw [op_smul_eq_smul, map_add (f := _), map_smul, map_smul, Algebra.smul_def, Algebra.smul_def,
      mul_comm (k a.snd)])
  map_zero' := TrivSqZeroExt.ext (map_zero (algebraMap R S)) (map_zero k)
  map_add' a b := TrivSqZeroExt.ext (map_add (algebraMap R S) _ _) (map_add k _ _)
  commutes' _ := TrivSqZeroExt.ext rfl (map_zero k)

attribute [local instance] cotOp cotCentral cotTower

theorem tanDer_cotVal {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R} (t : G.TorsionTower A)
    (β : Form (A.hom ≫ 𝟙 _)) {v : epsR R ⟶ A} (hv : IsTangent v) (n : ℕ) :
    t.tanDer hv n (cotVal β.1 (t.y n)) = algebraMap R (PDiv.ModPow p R n) (tanVal v β) := by
  let S := PDiv.ModPow p R n
  let E : SqExt R := SqExt.ofModule R S S
  let ρ : (cotExt R (G.A n)).C →ₐ[R] DualNumber S := sqToEps (t.tanDer hv n)
  let y' : Pt A (cotExt R (G.A n)).C := spOver (cotPt R (G.A n)) ≫ t.y n
  have hρ : ρ.comp (cotPt R (G.A n)) = t.tanPt hv n := AlgHom.ext fun a ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [t.fst_tanPt]
      exact congrArg (algebraMap R S) (add_zero _)
    · rw [← t.tanDer_d]
      exact congrArg (t.tanDer hv n) (zero_add _)
  have e : spOver ρ ≫ y' = epsRedPow p n v := by
    rw [← Category.assoc, spOver_comp, hρ, t.tanPt_y]
  have k1 := (cotExt R (G.A n)).val_map E ρ (Algebra.ofId R S) (fun _ ↦ rfl)
    (fun _ ↦ TrivSqZeroExt.ext rfl (map_zero (t.tanDer hv n))) y'.left y'.w _
    (Pt.w (epsRedPow p n v)) (congrArg Over.Hom.left e) β
  have k2 := (SqExt.dual R).val_map E (epsTo R S) (Algebra.ofId R S) (fun c ↦ (fst_epsTo S c).symm)
    (fun c ↦ TrivSqZeroExt.ext (fst_epsTo S _) ((snd_epsTo S _).trans (map_zero _))) v.left (pt_w v) _
    (Pt.w (epsRedPow p n v)) rfl β
  have h0 : fv β.1 (G.A n) (cotExt R (G.A n)).C (cotPt R (G.A n)) (t.y n) = 0 := β.2 _ rfl rfl
  have k3 := congrArg TrivSqZeroExt.snd (k1.symm.trans k2)
  rw [snd_epsTo] at k3
  refine Eq.trans ?_ k3
  change t.tanDer hv n (cotSnd R _ (_ - fv β.1 (G.A n) (cotExt R (G.A n)).C (cotPt R (G.A n)) (t.y n))) = _
  rw [h0, sub_zero]
  rfl

theorem lie_cotVal_eq_tanVal : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), IsNilpotent (p : R) → ∀ (β : Form (A.hom ≫ 𝟙 _)) (w : G.omega), (∀ n, w.1 n = cotVal β.1 (t.y n)) → ∀ (x : G.Lie) (v : epsR R ⟶ A), t.LieCorr x v → x w = tanVal v β := by
  intro R _ A _ p G t ⟨n, hn⟩ β w hw x v h
  have h1 := (t.lieCorr_iff h.1 x).1 h n w
  rw [hw, tanDer_cotVal] at h1
  have h2 := Ideal.Quotient.eq.1 h1
  rw [hn, Ideal.mem_span_singleton, zero_dvd_iff] at h2
  exact sub_eq_zero.1 h2

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeFrobeniusGrpSchemeCharP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeFrobeniusGrpSchemeCharP
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelFrobGrp

open GlobalTheory.AbDual GlobalTheory.PDiv

variable {R R' : Type} [CommRing R] [CommRing R'] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
  {σ : R →+* R'} {φ : A'.left ⟶ A.left}

def down (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x : Y ⟶ A') :
    Over.mk (Y.hom ≫ spMap σ) ⟶ A :=
  Over.homMk (x.left ≫ φ) (by simp [m.w])

theorem down_mul (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ (spMap σ) φ) {Y : Over (Sp R')} (x y : Y ⟶ A') :
    down m (x * y) = down m x * down m y :=
  Over.OverMorphism.ext (m.mul Y x y (down m x) (down m y) rfl rfl).symm

theorem main : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left), IsGrpPullback A₁ A (spMap (frobR p R hR)) π → ∃ F : A ⟶ A₁, IsMonHom F ∧ F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A) := by
  intro p _ R _ hR A A₁ _ _ π hπ
  have mF : GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (frobR p R hR)
      (spMap (frobR p R hR)) (GlobalTheory.VB.frob A.left p (cast_left p R hR A)) := by
    refine ⟨isDPMorphism_of_eq_bot _ rfl _ _, ?_, frob_comp_hom p R hR A.hom _, ?_⟩
    · simp
    · intro T x y x₀ y₀ hx hy
      have hT : (p : Γ(T.left, ⊤)) = 0 := cast_left p R hR T
      have hn (f : T.left ⟶ A.left) :
          GlobalTheory.VB.frob T.left p hT ≫ f = f ≫ GlobalTheory.VB.frob A.left p (cast_left p R hR A) :=
        GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out hT _
      let j : Over.mk (T.hom ≫ spMap (frobR p R hR)) ⟶ T :=
        Over.homMk (GlobalTheory.VB.frob T.left p hT) (by simpa using frob_comp_hom p R hR T.hom hT)
      have ex : x₀ = j ≫ x := Over.OverMorphism.ext (by
        simp only [hx, Over.comp_left, Over.homMk_left, j, hn])
      have ey : y₀ = j ≫ y := Over.OverMorphism.ext (by
        simp only [hy, Over.comp_left, Over.homMk_left, j, hn])
      subst ex ey
      rw [← MonObj.comp_mul]
      simp only [Over.comp_left, Over.homMk_left, j]
      exact hn (x * y).left
  have mπ := grpMor_of_isGrpPullback hπ
  let F : A ⟶ A₁ := liftPt hπ A.hom _ mF.w
  have hF : F.left ≫ π = _ := liftPt_left hπ A.hom _ mF.w
  have dF : ∀ {Y : Over (Sp R)} (t : Y ⟶ A), down mπ (t ≫ F) = down mF t := fun t ↦
    Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (t.left ≫ ·) hF))
  refine ⟨F, isMonHom_of_mul _ fun T x y ↦ pt_ext hπ ?_, hF⟩
  have e : down mπ ((x * y) ≫ F) = down mπ ((x ≫ F) * (y ≫ F)) := by rw [down_mul, dF, dF, dF, down_mul]
  exact congrArg (fun z ↦ z.left) e

end GlobalTheory.RelFrobGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeFrobeniusGrpSchemeCharPStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relativeFrobenius_grpScheme_charP : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left), IsGrpPullback A₁ A (spMap (frobR p R hR)) π → ∃ F : A ⟶ A₁, IsMonHom F ∧ F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A) := by
  first | exact @GlobalTheory.RelFrobGrp.main | exact GlobalTheory.RelFrobGrp.main | (intros; apply GlobalTheory.RelFrobGrp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackFractionFieldFiniteLocalExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackFractionFieldFiniteLocalExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.CommonCover

theorem exists_cover_field (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (K' : Type) [Field K']
    (io : FractionRing R →+* K') (hfin : io.Finite) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'),
      FinExt ρ ∧ IsLocalHom ρ ∧ τ.comp (io.comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  obtain ⟨⟨hN, -, hIC, hC⟩, hc0⟩ := hR
  letI : Algebra (FractionRing R) K' := io.toAlgebra
  letI : Algebra R K' := (io.comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (FractionRing R) K' := hfin
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : Algebra.IsSeparable (FractionRing R) K' := inferInstance
  let C := integralClosure R K'
  haveI : Module.Finite R C := IsIntegralClosure.finite R (FractionRing R) K' C
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension (FractionRing R) K'
  have hφ : Function.Injective (algebraMap R C) := fun a b h => by
    have h' : io (algebraMap R (FractionRing R) a) = io (algebraMap R (FractionRing R) b) := congrArg Subtype.val h
    exact IsFractionRing.injective R (FractionRing R) (io.injective h')
  obtain ⟨R', _, _, _, ρ, σ, hCN, hρ, hfin', hloc, hσ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (algebraMap R C) ⟨hN, hIC, hC, hc0⟩ hφ (RingHom.finite_algebraMap.2 inferInstance)
  have hσi : Function.Injective σ := by
    refine (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := R) ?_)
    change (RingHom.ker σ).comap (algebraMap R C) = ⊥
    rw [RingHom.comap_ker, hσ]
    exact (RingHom.injective_iff_ker_eq_bot ρ).1 hρ
  have hg : Function.Injective ((algebraMap R' (FractionRing R')).comp σ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hσi
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, IsFractionRing.lift (A := C) hg,
    ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hρ, hfin'⟩, hloc, ?_⟩
  ext r
  have e : io (algebraMap R (FractionRing R) r) = algebraMap C K' (algebraMap R C r) := rfl
  simp only [RingHom.comp_apply]
  rw [e, IsFractionRing.lift_algebraMap, RingHom.comp_apply, ← RingHom.comp_apply σ, hσ]

theorem exists_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegPre R) (E₁ E₂ : DegPre (FractionRing R)), IsPullDeg (algebraMap R (FractionRing R)) D₁ E₁ → IsPullDeg (algebraMap R (FractionRing R)) D₂ E₂ → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (E₃ : DegPre K'), io.Finite → IsPullDeg io E₁ E₃ → IsPullDeg io E₂ E₃ → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (E : DegPre (FractionRing R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) := by
  intro R _ _ _ hR D₁ D₂ E₁ E₂ p₁ p₂ K' _ io E₃ hfin q₁ q₂
  obtain ⟨R', _, _, _, ρ, τ, hE, hloc, hτ⟩ := exists_cover_field R hR K' io hfin
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨E, t, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hL.polBaseChange K' (FractionRing R') τ E₃ ⊤
    (GlobalTheory.FieldPull.nonempty_psiOn_field E₃) trivial
  have ha : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hio : Function.Injective (io.comp (algebraMap R (FractionRing R))) := io.injective.comp ha
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, E, hE, hloc, ?_, ?_⟩
  · obtain ⟨a⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp ha io.injective p₁ q₁
    rw [← hτ]
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hio τ.injective a t
  · obtain ⟨a⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp ha io.injective p₂ q₂
    rw [← hτ]
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hio τ.injective a t

end GlobalTheory.CommonCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackFractionFieldFiniteLocalExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_commonPullback_fractionField_finiteLocalExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegPre R) (E₁ E₂ : DegPre (FractionRing R)), IsPullDeg (algebraMap R (FractionRing R)) D₁ E₁ → IsPullDeg (algebraMap R (FractionRing R)) D₂ E₂ → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (E₃ : DegPre K'), io.Finite → IsPullDeg io E₁ E₃ → IsPullDeg io E₂ E₃ → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (E : DegPre (FractionRing R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) := by
  first | exact @GlobalTheory.CommonCover.exists_common_pull | exact GlobalTheory.CommonCover.exists_common_pull | (intros; apply GlobalTheory.CommonCover.exists_common_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfIsDual
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem isAdditive_swap_of_isDual (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hd : IsDual A B P) :
    IsAdditive (swap P) := by
  have hP := hd.isLB
  have ext : ∀ {Y : Over S} {x y : Y ⟶ B},
      (∀ (Z : Over S) (u : Z ⟶ Y) (a : Z ⟶ A), evc hP a (u ≫ x) = evc hP a (u ≫ y)) → x = y := by
    intro Y x y h
    have hM : (ev P (fst A Y) (snd A Y ≫ x)).IsLB := pull_isLB hP _
    refine (hd.univ Y _ hM ((isAdditive_iff hM).2 fun Z a a' t ↦ ?_)).unique
      ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB hP _)).1 ?_)
    · simp only [evc_ev hP, lift_fst, lift_snd_assoc]
      exact (isAdditive_iff hP).1 hd.additive _ _ _ _
    · exact h (A ⊗ Y) (snd A Y) (fst A Y)
  have h₁ : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ fst B B)).IsLB := pull_isLB hP _
  have h₂ : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ snd B B)).IsLB := pull_isLB hP _
  have hM := isLB_tens h₁ h₂
  have eM : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B ⊗ B),
      evc hM a t = evc hP a (t ≫ fst B B) + evc hP a (t ≫ snd B B) := by
    intro Y a t
    show CechPic.pull _ (cls _ hM) = _
    rw [cls_tens h₁ h₂ hM, map_add (f := _)]
    exact congrArg₂ (· + ·) ((evc_ev hP _ _ h₁ a t).trans (by rw [lift_fst, lift_snd_assoc]))
      ((evc_ev hP _ _ h₂ a t).trans (by rw [lift_fst, lift_snd_assoc]))
  obtain ⟨m, hm, -⟩ := hd.univ (B ⊗ B) _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ by
    rw [eM, eM, eM, (isAdditive_iff hP).1 hd.additive, (isAdditive_iff hP).1 hd.additive]
    abel)
  have hm' : (ev P (fst A (B ⊗ B)) (snd A (B ⊗ B) ≫ m)).IsLB := pull_isLB hP _
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B ⊗ B),
      evc hP a (t ≫ m) = evc hP a (t ≫ fst B B) + evc hP a (t ≫ snd B B) := by
    intro Y a t
    have e : evc hM a t = evc hm' a t := by rw [evc, evc, (cls_eq_iff hM hm').2 hm]
    rw [← eM, e, evc_ev hP, lift_fst, lift_snd_assoc]
  have hl : ∀ {Y : Over S} (b : Y ⟶ B), lift b 1 ≫ m = b := fun b ↦ ext fun Z u a ↦ by
    rw [← Category.assoc, key]
    simp only [Category.assoc, comp_lift, lift_fst, lift_snd, MonObj.comp_one, evc_one_right hP hd.zero, add_zero]
  have hr : ∀ {Y : Over S} (b : Y ⟶ B), lift 1 b ≫ m = b := fun b ↦ ext fun Z u a ↦ by
    rw [← Category.assoc, key]
    simp only [Category.assoc, comp_lift, lift_fst, lift_snd, MonObj.comp_one, evc_one_right hP hd.zero, zero_add]
  have e1 : ∀ (X : Over S) [MonObj X], (1 : 𝟙_ (Over S) ⟶ X) = η[X] := fun X _ ↦ by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hη : η[B ⊗ B] ≫ m = η[B] := by
    have e : (1 : 𝟙_ (Over S) ⟶ B ⊗ B) = lift (1 : 𝟙_ (Over S) ⟶ B) 1 := by
      ext <;> simp
    rw [← e1 (B ⊗ B), ← e1 B, e, hl]
  haveI : IsMonHom m := GlobalTheory.rigidity_holds S (B ⊗ B) B (AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB) hB m hη
  have hs : (swap P).IsLB := pull_isLB hP _
  refine (isAdditive_iff hs).2 fun Y b b' a ↦ ?_
  rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs]
  have e : b * b' = lift b b' ≫ m := by
    have e' : lift b b' = lift b 1 * lift 1 b' := by
      ext <;> simp [MonObj.mul_comp]
    rw [e', MonObj.mul_comp, hl, hr]
  rw [e, key, lift_fst, lift_snd]

theorem isDual_isAdditive_swap : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left),
    IsAbelianScheme B → IsDual A B P → IsAdditive (swap P) :=
  fun _ _ _ _ _ _ hB hd ↦ isAdditive_swap_of_isDual hB hd

end GlobalTheory.AbDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisationDataIsEvenCubicalOnClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisationDataIsEvenCubicalOnClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.PreEven
open GlobalTheory.UU GlobalTheory.ClosedPol


set_option maxHeartbeats 1000000 in
theorem evenOn_preU : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P := by
  intro R _ _ _ D A G _ _ U
  have hG := GlobalTheory.firstFiveLaws.1.globalFns
  set g := U.gt 0 with hg
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.P.isAb
  have := hB.comm
  obtain ⟨O, h₁, h₂, h₃, hd⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ D.X (thickObj R (maximalIdeal R) 0 G)
    (thickObj R (maximalIdeal R) 0 D.P.A) hB g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj inferInstance g.isKernel
  obtain ⟨d, hdq, hdi⟩ := hd hB
  let Q : TQ (thickObj R (maximalIdeal R) 0 G) D.X :=
    { B := thickObj R (maximalIdeal R) 0 D.P.A
      isAb := hB
      q := g.q
      i := g.i
      q_hom := g.q_hom
      i_hom := g.i_hom
      q_flat := g.q_flat
      q_surj := g.q_surj
      q_affine := g.q_affine
      isKernel := g.isKernel
      loc := by
        have l := (TQ.ofGtDatum d).loc
        rw [show (TQ.ofGtDatum d).q = g.q from hdq, show (TQ.ofGtDatum d).i = g.i from hdi] at l
        exact l }
  obtain ⟨P₀, hlev⟩ := exists_isLevelCP (maximalIdeal R) 0 U.P
  obtain ⟨w₀, h₀⟩ := hlev
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U.P.L.isLB _) _ (pullIso_isGen U.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := isCPMap_w hG U 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U.gt 0).pG)
  obtain ⟨M, wM, hM⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hG D)
  obtain ⟨w₄, k₄⟩ := cpMap_congr rfl (Category.id_comp _) k₃
    (by rw [Category.assoc, pullback.condition, Category.id_comp]; simpa using Over.w g.pG)
  obtain ⟨w₅, k₅, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M P₀ _ _ _ g.q.left
    ((Over.w g.q).trans (Category.comp_id _).symm) _ hM).2
    (toBase_mul_of_isMonHom g.q _) w₄ k₄
  have De : Q.Desc P₀ := ⟨M, w₅, k₅⟩
  exact ⟨D.X, inferInstance, inferInstance, inferInstance, Q, P₀, ⟨w₀, h₀⟩,
    GlobalTheory.UniformizationSetting.exists_even_of_desc De⟩

end GlobalTheory.Mum.PreEven
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisationDataIsEvenCubicalOnClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preUniformisationData_isEvenCubicalOnClosedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P := by
  first | exact @GlobalTheory.Mum.PreEven.evenOn_preU | exact GlobalTheory.Mum.PreEven.evenOn_preU | (intros; apply GlobalTheory.Mum.PreEven.evenOn_preU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSpreadPointsEqSpreadRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSpreadPointsEqSpreadRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumPair

theorem weilIs_of_spread : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] [IsNoetherianRing T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (k : ℕ) (x x' : baseOver (Sp Ω) ⟶ A.A) (y y' : baseOver (Sp T) ⟶ P.A) (c : Tˣ), 1 ≤ k → x.left ≫ φ = spMap jT ≫ y.left → x'.left ≫ φ = spMap jT ≫ y'.left → y ^ k = 1 → y' ^ k = 1 → WeilIs A.A A.L k x x' (unitOn (Units.map jT.toMonoidHom c)) → WeilIs P.A P.L k y y' (unitOn c) := by
  intro Ω T _ _ _ _ jT hj A P φ hp hw k x x' y y' c hk hx hx' hy hy' hW
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  haveI : IsCommMonObj A.A := A.isAb.comm
  haveI : IsLocallyNoetherian (Sp T) := inferInstance
  haveI : IsLocallyNoetherian (Sp Ω) := inferInstance
  obtain ⟨c₀, hc₀, -⟩ := (hL.weil (Sp T) P k (baseOver _)).1 y y' hy hy'
  let h : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap jT) ⟶ baseOver (Sp T) := Over.homMk (spMap jT) (by simp)
  have H1 := GlobalTheory.CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h hc₀
  have H2 := (GlobalTheory.weilIs_grpPullback_of_comm' (Sp T) (Sp Ω) P.A A.A (spMap jT) φ P.L A.L P.isLB A.isLB hp hw
    (baseOver (Sp Ω)) k x x' (h ≫ y) (h ≫ y') _ hx.symm hx'.symm).2 H1
  have inj : ∀ a b : baseOver (Sp Ω) ⟶ A.A, a.left ≫ φ = b.left ≫ φ → a = b := by
    intro a b e
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext e
    rw [Over.w, Over.w]
  have tors : ∀ (a : baseOver (Sp Ω) ⟶ A.A) (b : baseOver (Sp T) ⟶ P.A), a.left ≫ φ = spMap jT ≫ b.left →
      b ^ k = 1 → a ^ k = 1 := by
    intro a b e hb
    apply inj
    have e1 : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp (baseOver (Sp Ω)) (a ^ k)) = (h ≫ b) ^ k := by
      rw [map_pow]
      congr 1
      exact Over.OverMorphism.ext e
    have e2 : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp (baseOver (Sp Ω)) 1) = (h ≫ b) ^ k := by
      rw [map_one, ← MonObj.comp_pow, hb, MonObj.comp_one]
    exact (congrArg (fun z => z.left) e1).trans (congrArg (fun z => z.left) e2).symm
  have hxk := tors x y hx hy
  have hxk' := tors x' y' hx' hy'
  have U := (hL.weil (Sp Ω) A k (baseOver _)).1 x x' hxk hxk'
  have e3 := U.unique H2 hW
  have nat : ∀ a : T, (spMap jT).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (jT a) := by
    intro a
    have := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom jT))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  have ginj : Function.Injective (spMap jT).appTop.hom := by
    intro a b e
    have ea : a = (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom a) := by
      simp
    have eb : b = (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom b) := by
      simp
    rw [ea, eb, nat, nat] at e
    have e' := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom e
    have key : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom z) = z :=
      fun z => by simp
    rw [key, key] at e'
    rw [ea, eb, hj e']
  have e4 : c₀ = unitOn c := by
    apply Units.ext
    apply ginj
    exact (congrArg Units.val e3).trans (nat (c : T)).symm
  rw [← e4]
  exact hc₀

end GlobalTheory.MumPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSpreadPointsEqSpreadRootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_spread_points_eq_spread_root : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] [IsNoetherianRing T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (k : ℕ) (x x' : baseOver (Sp Ω) ⟶ A.A) (y y' : baseOver (Sp T) ⟶ P.A) (c : Tˣ), 1 ≤ k → x.left ≫ φ = spMap jT ≫ y.left → x'.left ≫ φ = spMap jT ≫ y'.left → y ^ k = 1 → y' ^ k = 1 → WeilIs A.A A.L k x x' (unitOn (Units.map jT.toMonoidHom c)) → WeilIs P.A P.L k y y' (unitOn c) := by
  first | exact @GlobalTheory.MumPair.weilIs_of_spread | exact GlobalTheory.MumPair.weilIs_of_spread | (intros; apply GlobalTheory.MumPair.weilIs_of_spread <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricGenericPointStalkOfFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricGenericPointStalkOfFlat
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
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory

theorem lift_of_stalk_generic_flat : ∀ {X' W : Scheme.{0}} [IsIntegral X'] (h : W ⟶ X') [Flat h] (q : W)
    [IsDomain (W.presheaf.stalk q)] {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X') [IsOpenImmersion ℓ]
    (Ω : Type) [Field Ω] (y : Sp Ω ⟶ Spec (W.presheaf.stalk q)) (hy : ∀ x, (y x).asIdeal = ⊥), ∃ z : Sp Ω ⟶ V, y ≫ W.fromSpecStalk q ≫ h = z ≫ ℓ := by
  intro X' W _ h _ q _ V _ ℓ _ Ω _ y hy
  have hinj : Function.Injective (h.stalkMap q).hom := by
    letI := (h.stalkMap q).hom.toAlgebra
    haveI : Module.Flat (X'.presheaf.stalk (h q)) (W.presheaf.stalk q) := Flat.stalkMap h q
    haveI : IsLocalHom (algebraMap (X'.presheaf.stalk (h q)) (W.presheaf.stalk q)) :=
      (inferInstance : IsLocalHom (h.stalkMap q).hom)
    haveI : Module.FaithfullyFlat (X'.presheaf.stalk (h q)) (W.presheaf.stalk q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective _ _
  have hrange : Set.range (y ≫ W.fromSpecStalk q ≫ h) ⊆ Set.range ℓ := by
    rintro _ ⟨x, rfl⟩
    have key : (y ≫ W.fromSpecStalk q ≫ h) x =
        X'.fromSpecStalk (h q) (Spec.map (h.stalkMap q) (y x)) := by
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]; rfl
    rw [key]
    set p : Spec (X'.presheaf.stalk (h q)) := Spec.map (h.stalkMap q) (y x) with hpdef
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap (h.stalkMap q).hom (y x).asIdeal = ⊥
      rw [hy x]
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨s, hs⟩ : genericPoint X' ∈ Set.range (X'.fromSpecStalk (h q)) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X').specializes (Set.mem_univ _)
    have hps : p ⤳ s := (PrimeSpectrum.le_iff_specializes _ _).1 (by
      show p.asIdeal ≤ s.asIdeal
      rw [hp]; exact bot_le)
    have hgen : genericPoint X' ∈ Set.range ℓ :=
      ((genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range).2
        (by simpa using Set.range_nonempty ℓ)
    have := (hps.map (X'.fromSpecStalk (h q)).continuous).mem_open
      ℓ.isOpenEmbedding.isOpen_range (by rw [hs]; exact hgen)
    exact this
  exact ⟨IsOpenImmersion.lift ℓ _ hrange, (IsOpenImmersion.lift_fac _ _ _).symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricGenericPointStalkOfFlatStatement
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
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_geometricGenericPoint_stalk_of_flat : ∀ {X' W : Scheme.{0}} [IsIntegral X'] (h : W ⟶ X') [Flat h] (q : W)
    [IsDomain (W.presheaf.stalk q)] {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X') [IsOpenImmersion ℓ]
    (Ω : Type) [Field Ω] (y : Sp Ω ⟶ Spec (W.presheaf.stalk q)) (hy : ∀ x, (y x).asIdeal = ⊥), ∃ z : Sp Ω ⟶ V, y ≫ W.fromSpecStalk q ≫ h = z ≫ ℓ := by
  first | exact @GlobalTheory.lift_of_stalk_generic_flat | exact GlobalTheory.lift_of_stalk_generic_flat | (intros; apply GlobalTheory.lift_of_stalk_generic_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClass
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def pullCompare {Y X : Over (Sp R)} (u : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) u.left)
    {D : Type} [CommRing D] [Algebra R D] (w : Pt Y D) (z : Pt X D)
    (h : z = (w ≫ u : Pt X D)) :
    trivAt z ⟶ m.obj (trivAt w) :=
  Thick.trivHom { RingHom.id D with commutes' := fun _ ↦ rfl } (by
    subst z
    change spMap (RingHom.id D) ≫ (w ≫ u).left = w.left ≫ u.left
    rw [Cris.spMap_id, Category.id_comp, Over.comp_left])

theorem exists_crystallineCocycleOnPoints_pullback_cohomologous {Y X : Over (Sp R)} (u : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) u.left)
    (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) :
    ∃ c : Fn0 Y, ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (w : Pt Y D),
      fv (m.coef.pullbackOneCocycle f) D D' φ w = fv f D D' φ (w ≫ u) + (c D' (spOver φ ≫ w) - φ (c D w)) := by
  refine ⟨fun D _ _ w ↦ ev f (pullCompare u m w (w ≫ u) rfl), fun D _ _ D' _ _ φ w ↦ ?_⟩
  have h1 : ∀ (z : Pt X D') (h : z = (spOver φ ≫ w) ≫ u),
      @Eq D' (ev f (pullCompare u m (spOver φ ≫ w) z h))
        (ev f (pullCompare u m (spOver φ ≫ w) _ rfl)) := fun z h ↦ by subst z; rfl
  have k := ev_sq f (trivMap φ (w ≫ u))
    (pullCompare u m (spOver φ ≫ w) (spOver φ ≫ w ≫ u) (Category.assoc _ _ _).symm)
    (pullCompare u m w (w ≫ u) rfl) (m.functor.map (trivMap φ w)) fun _ ↦ rfl
  have key : ∀ a b b' c d : D', b = b' → a + b = c + d → d = a + (b' - c) :=
    fun a b b' c d e h ↦ by rw [← e]; linear_combination -h
  exact key _ _ _ _ _ (h1 _ _) k

theorem exists_isAdd_of_mem_primDR (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (hf : CatCoh.H1.mk _ f ∈ primDR A) :
    ∃ g : Fn2 A, IsAdd (fv f) g := by
  have h := (mem_prim_iff (dp0 R) (𝟙 _) A _).1 hf
  have M : ∀ u : A ⊗ A ⟶ A,
      IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ A).hom ≫ 𝟙 _) (RingHom.id R) u.left := fun u ↦
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have h' : CatCoh.H1.mk _ ((M μ[A]).coef.pullbackOneCocycle f) =
      CatCoh.H1.mk _ ((M (fst A A)).coef.pullbackOneCocycle f + (M (snd A A)).coef.pullbackOneCocycle f) := by
    rw [map_add (f := _)]; exact h
  obtain ⟨k, hk⟩ := H1.mk_eq_mk.1 h'
  obtain ⟨c, hc⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M μ[A]) f
  obtain ⟨c₁, hc₁⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M (fst A A)) f
  obtain ⟨c₂, hc₂⟩ := exists_crystallineCocycleOnPoints_pullback_cohomologous _ (M (snd A A)) f
  let k' : Fn0 (A ⊗ A) := fun D _ _ w ↦ k (trivAt w)
  refine ⟨fun D _ _ x y ↦ k' D (lift x y) - c D (lift x y) + c₁ D (lift x y) + c₂ D (lift x y),
    fun D _ _ D' _ _ φ x y ↦ ?_⟩
  have e : k' D' (spOver φ ≫ lift x y) - φ (k' D (lift x y)) =
      fv ((M μ[A]).coef.pullbackOneCocycle f) D D' φ (lift x y) -
        (fv ((M (fst A A)).coef.pullbackOneCocycle f) D D' φ (lift x y) +
          fv ((M (snd A A)).coef.pullbackOneCocycle f) D D' φ (lift x y)) :=
    congrFun (congrFun (congrFun hk _) _) (trivMap φ (lift x y))
  rw [hc, hc₁, hc₂, lift_fst, lift_snd, ← Hom.mul_def, comp_lift] at e
  simp only [map_add (f := _), map_sub]
  linear_combination e

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClassStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR A → ∃ g : Fn2 A, IsAdd (fv f) g := by
  first | exact @GlobalTheory.PtExt.exists_isAdd_of_mem_primDR | exact GlobalTheory.PtExt.exists_isAdd_of_mem_primDR | (intros; apply GlobalTheory.PtExt.exists_isAdd_of_mem_primDR <;> assumption)
end
end
