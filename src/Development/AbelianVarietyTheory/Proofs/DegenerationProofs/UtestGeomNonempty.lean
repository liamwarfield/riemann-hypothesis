module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByWeightZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AmpleCubPullAndPullPow
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaGeom
open GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift

theorem val_powFrame {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} (x : T ⟶ A) (e) (k : ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) : val (powFrame A L x e k) r z J = val e r z J ^ k :=
  map_zpow _ _ _

theorem val_rigT {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
    (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) {y : Z} {J} (hJ : Good L y J) :
    val (rigT A L rig T k) r y J =
      val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) y J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ y _ hy _).trans ?_))
  rw [val_of (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) y J (fun _ => J (r ≫ T.hom ≫ eSec A))
    (fun _ => by rw [Category.assoc])]
  exact gm_pull r T.hom y (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem sv_sum {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ} {I : Type} [Fintype I]
    (c : I → Γ(T.left, ⊤)) (v : I → SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) :
    ThetaAct.sv (∑ i, c i • v i) r z J = ∑ i, gs (r ≫ (fst T A).left) z ⊤ (c i) * ThetaAct.sv (v i) r z J := by
  let F : SecM A L k T →+ Z.presheaf.stalk z :=
    AddMonoidHom.mk' (fun v => ThetaAct.sv v r z J) fun a b => ThetaAct.sv_add a b r z hJ
  exact (map_sum F _ _).trans (Finset.sum_congr rfl fun i _ => ThetaAct.sv_smul _ _ _ _ hJ)

theorem comb_iff {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ} {I : Type} [Fintype I]
    (c : I → Γ(T.left, ⊤)) (t : I → LB.Sec (LPow A L k T)) (σ : LB.Sec (LPow A L k T)) :
    (∀ j, σ.f j = ∑ l, liftFun A _ (c l) * (t l).f j) ↔ SecM.ofSec A σ = ∑ l, c l • SecM.ofSec A (t l) := by
  have e : ∀ j, (∑ l, c l • SecM.ofSec A (t l)).1 j = ∑ l, liftFun A _ (c l) * (t l).f j := fun j => by
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    rfl
  exact ⟨fun h => Subtype.ext (funext fun j => (h j).trans (e j).symm),
    fun h j => (congrArg (fun q => q.1 j) h).trans (e j)⟩

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem genThrough_pow {x : T ⟶ A} {x₀ : T₀ ⟶ G} {e e₀}
    (H : GenThrough w (fun _ : Fin 1 => x.left) (fun _ : Fin 1 => x₀.left) (fun _ => 1) e e₀ τ) (k : ℤ) :
    GenThrough w (fun _ : Fin 1 => x.left) (fun _ : Fin 1 => x₀.left) (fun _ => k)
      (powFrame A L₁ x e k) (powFrame G L₀ x₀ e₀ k) τ := fun Z r z J J' hJ hJ' => by
  rw [val_powFrame, val_powFrame, H Z r z J J' hJ hJ', Fin.prod_univ_one, Fin.prod_univ_one, zpow_one, mul_zpow]

theorem secRel_comb {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T₀.left, ⊤)) {t : I → LB.Sec (LPow A L₁ k T)}
    {t₀ : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (t₀ l)) {σ σ₀}
    (e : SecM.ofSec A σ = ∑ l, τ.appTop.hom (c l) • SecM.ofSec A (t l))
    (e₀ : SecM.ofSec G σ₀ = ∑ l, c l • SecM.ofSec G (t₀ l)) : SecRel hp τ hτ w σ σ₀ := fun Z r z J J' hJ hJ' => by
  have a := (congrArg (fun q => ThetaAct.sv q r z J') e).trans (sv_sum _ _ r z hJ')
  have a₀ := (congrArg (fun q => ThetaAct.sv q (r ≫ psi hp τ hτ) z J) e₀).trans (sv_sum _ _ _ z hJ)
  refine a₀.trans (Eq.trans ?_ (congrArg (_ * ·) a).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, Category.assoc, psi_fst', ← Category.assoc]
  exact congrArg₂ (· * ·) (gs_pull _ τ z ⊤ trivial _).symm (h l Z r z J J' hJ hJ')

include hτ in
theorem norm_move (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {n : ℕ} {rig rig₀}
    (hr : GenThrough w (fun _ : PUnit => eSec A) (fun _ : PUnit => eSec G) (fun _ => 1) rig rig₀ f)
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, (snd T₀ G ^ n).left] ![a, -1])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, (snd T A ^ n).left] ![a, -1])}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ (snd T A ^ n).left) ^ (-1 : ℤ)) * val α r z J')
    (H₀ : LB.Gen.Corr L₀ _ _ _ _ (LB.pullGen L₀ _ _ α₀ (ptSecT G 1).left)
      (LB.mulGen L₀ _ _ _ _ (rigT G L₀ rig₀ T₀ a) (rigT G L₀ rig₀ T₀ (-1)))) :
    LB.Gen.Corr L₁ _ _ _ _ (LB.pullGen L₁ _ _ α (ptSecT A 1).left) (rigT A L₁ rig T (a - 1)) := by
  refine corr_of_val hL₁ fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  have q := val_corr hJ H₀ (𝟙 _ ≫ τ)
  have e₁ : (𝟙 _ ≫ (ptSecT A (1 : T ⟶ A)).left) ≫ (snd T A).left = (𝟙 _ ≫ T.hom) ≫ eSec A := by
    rw [Category.assoc, Category.assoc, ptSecT_snd]; rfl
  have e₂ : (𝟙 _ ≫ (ptSecT A (1 : T ⟶ A)).left) ≫ (snd T A ^ n).left = (𝟙 _ ≫ T.hom) ≫ eSec A := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, MonObj.comp_pow, ptSecT, lift_snd, one_pow]; rfl
  rw [val_pull hJ, val_mul hJ, val_rigT _ _ _ hJ, val_rigT _ _ _ hJ, Category.assoc,
    ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc, H _ _ _ _ _ hJ hJ', e₁, e₂, Category.assoc (𝟙 _) τ, hτ,
    ← Category.assoc (𝟙 _) T.hom f] at q
  have q₂ := hr _ (𝟙 _ ≫ T.hom) y J J' hJ hJ'
  rw [Fintype.prod_unique, zpow_one] at q₂
  rw [val_pull hJ', val_rigT _ _ _ hJ']
  erw [q₂] at q
  apply Additive.ofMul.injective
  replace q := congrArg Additive.ofMul q
  simp only [ofMul_mul, ofMul_zpow] at q ⊢
  linear_combination (norm := module) q

end GlobalTheory.ThetaGeom
namespace GlobalTheory.ZH
open GlobalTheory.ThetaPtMove GlobalTheory.ThetaGeom

theorem spMap_appTop_fn {R F : Type} [CommRing R] [CommRing F] (y : R →+* F) (a : R) :
    (spMap y).appTop.hom (fn a) = (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (y a) :=
  (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem valAt_of_isValueAt {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {t : SecA A F k} {x : TFK (R := R) F ⟶ A.A} {e : FrAt x}
    {c : F} (h : IsValueAt A.A A.L k t x (powFrame A.A A.L x e k) ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c)) :
    ValAt t x e c := fun z J hJ => by
  have q := sv_of_isValueAt h (𝟙 _) z hJ
  rw [Category.id_comp] at q
  exact q

theorem utest_geom_nonempty : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), Nonempty u.Geom := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨x, hx, hadd, hinj, hsurj⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain ⟨w, hw⟩ := u.lb
  obtain ⟨rig, fr, hrig, vrig, hfr⟩ := GlobalTheory.T.exists_frames_on_uniformised_fibre_through_iso o Ω S ρ p y₀ u x hx w hw
  have hp := u.cart
  have hL₀ := ρ.P.isLB
  have hL₁ := u.A.isLB
  have := u.A.isAb.comm
  let τ : (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have hτ : τ ≫ (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
    refine (Category.comp_id _).trans (Eq.trans (congrArg spMap u.fac.symm) ?_)
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ ρ.th₁
  choose s hs using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (ρ.s i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  have hpow : ∀ (n : ℕ) a, x (n • a) = x a ^ n := fun n a => by
    induction n with
    | zero =>
      have h := hadd 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 h
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hN : ∀ a, x (S.r • a) ^ S.N = 1 := fun a => by
    rw [hpow, ← pow_mul]
    exact (hfr a).1.1
  choose U hU hU' using fun a => symLift_move hp τ hτ hw hL₀ hL₁ (hx (S.r • a)).symm (hN a) (ρ.U_sym a)
  obtain ⟨r₀, hr₀, -⟩ := thetaGrp_acts_linearly hL.globalFns _ ρ.P S.N (baseOver (Sp S.R))
  obtain ⟨r₁, hr₁, -⟩ := thetaGrp_acts_linearly hL.globalFns _ u.A S.N (TFK (R := u.V) (PadicAlgCl p))
  refine ⟨⟨x, hx, hadd, fun z hz => ?_, GlobalTheory.T.weilPairing_labelledTorsion_uniformTest hL o Ω S ρ p y₀ u x hx, rig, hrig, fr, fun a => (hfr a).1, th,
    fun a z J hJ => ?_, s, fun a i => valAt_of_isValueAt ?_, α, hα,
    norm_move hp τ hτ hL₀ hL₁ vrig vα ρ.α_norm,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) hα vα hth (hs ρ.i₀) ρ.s_zero,
    U, hU, fun a i σ => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := hsurj z hz
    exact ⟨a, rfl, fun b hb => hinj hb⟩
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx a).symm (hfr a).2 hth (ρ.th_val a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    rw [val_powFrame, Nat.cast_one, zpow_one]
    exact q
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx a).symm (genThrough_pow τ (hfr a).2 S.N) (hs i) (ρ.ev_val i a)
    rw [spMap_appTop_fn] at h
    exact h
  · have a₀ : IsActOf ρ.P.A ρ.P.L S.N (ρ.U a) (ρ.s i) (SecM.toSec _ (r₀ (ρ.U a) (SecM.ofSec _ (ρ.s i)))) :=
      (hr₀ _ _ _).2 rfl
    let c : S.J → Γ((baseOver (Sp S.R)).left, ⊤) := fun l => fn (algebraMap o S.R (S.ρ a l i))
    have hc : (fun l => τ.appTop.hom (c l)) = fun l => (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom
        (y₀ (algebraMap o S.R (S.ρ a l i))) := funext fun l => spMap_appTop_fn y₀ _
    have a₁ := hU' a _ _ _ (SecM.toSec _ (∑ l, τ.appTop.hom (c l) • SecM.ofSec _ (s l))) (hs i)
      (secRel_comb hp τ hτ c hs rfl ((comb_iff _ _ _).1 (ρ.U_act a i _ a₀))) a₀
    have a₂ := (hr₁ _ _ _).1 a₁
    have a₃ := comb_iff (fun l => τ.appTop.hom (c l)) s σ
    refine (hr₁ _ _ _).trans (Iff.trans ⟨fun h => a₃.2 (h.symm.trans a₂), fun h => a₂.trans (a₃.1 h).symm⟩ ?_)
    exact forall_congr' fun j => Eq.congr_right (Finset.sum_congr rfl fun l _ => by rw [congrFun hc l])

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSabExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TripleExt

open GlobalTheory.CechPic

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def cubeCls {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem isLB_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) : (cubeLB G x L).IsLB :=
  LB.isLB_linComb hL _ _

theorem cls_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls _ (isLB_cube x hL) = cubeCls x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls_pre {T T' : Over S} (u : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) :
    pull u.left (cubeCls x c) = cubeCls (fun i => u ≫ x i) c := by
  unfold cubeCls
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun z => _ • pull (CommaMorphism.left z) c) (psum_hom (preHom u) x I.down)

theorem pull_cubeCls_push (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (u : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = u ≫ x i)
    (c : Pic G.left) : pull (Y := T'.left) u.left (cubeCls x c) = cubeCls x' (pull φ c) := by
  unfold cubeCls
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← pull_comp, psum_push h x' x u hx]

theorem cubeCls_one {n : ℕ} (c : Pic G.left) (hc : pull (eSec G) c = 0) :
    cubeCls (fun _ : Fin n => η[G]) c = 0 := by
  refine Finset.sum_eq_zero fun I _ => ?_
  have e₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have e : psum G (fun _ : Fin n => η[G]) I.down = η[G] := by
    have := psum_hom (1 : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S) ⟶ G)) (fun _ : Fin n => η[G]) I.down
    simp only [MonoidHom.one_apply, e₁] at this
    exact this.symm
  rw [e]
  exact (congrArg _ hc).trans (smul_zero _)

end Cube

theorem pic_ext (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S) {U H HU : Scheme.{0}}
    [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (hp : Smooth p)
    (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (hj : IsPullback jH pU p j) (α β : Pic H)
    (h₁ : pull jH α = pull jH β) (h₂ : pull e α = pull e β) : α = β := by
  obtain ⟨A, hA, rfl⟩ := cls_surj α
  obtain ⟨B, hB, rfl⟩ := cls_surj β
  exact (cls_eq_iff hA hB).2 ((GlobalTheory.T.lineBundleIso_extend_of_normal_base S hS U H HU j p e jH pU hp hg he hj A B hA hB
    ((cls_eq_iff (pull_isLB hA _) (pull_isLB hB _)).1 h₁)).1 ((cls_eq_iff (pull_isLB hA _) (pull_isLB hB _)).1 h₂))

theorem exists_sab_extension : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (U : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] [IsCommMonObj G] (semi : IsSemiAbelian G) (act : OAct (NumberField.RingOfIntegers E) G) (t₀ : SAB H U) (a : t₀.G.left ⟶ G.left), IsGrpPullback t₀.G G j a → (∀ x, (t₀.act.act x).left ≫ a = a ≫ (act.act x).left) → ∀ M : LB G.left, M.IsLB → LBIso (M.pull a) t₀.PP.L → ∃ (PP : RigLB G) (cub : CubicalStr G PP) (h₁ : _) (h₂ : _) (h₃ : _) (m : SABMap t₀ (SAB.mk G semi act PP cub h₁ h₂ h₃) j), m.φ = a := by
  intro S _ _ hS E _ _ _ H U _ j _ G _ _ semi act t₀ a h hact M hM hMa
  have := semi.smooth
  have := semi.geomConnected
  obtain ⟨PP, cub, m, rfl, hme, hlin, hsym⟩ := GlobalTheory.T.exists_rigidified_cubical_symmetric_extension_normalBase S hS U j G t₀.G a h t₀.PP t₀.cub M hM hMa
  have hc₀ : cls t₀.PP.L t₀.PP.isLB = pull m.F (cls PP.L PP.isLB) := by
    obtain ⟨w, hw, -⟩ := hlin
    exact (cls_eq_iff t₀.PP.isLB (pull_isLB PP.isLB _)).2 ⟨w, hw⟩
  have hrig : pull (eSec G) (cls PP.L PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  have pa : ∀ {T : Over U} (x : T ⟶ t₀.G) b,
      pushPt h.1.w (x ≫ t₀.act.act b) = pushPt h.1.w x ≫ act.act b := fun x b =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ha1 : ∀ b, η[G] ≫ act.act b = η[G] := fun b => by have := act.hom b; exact IsMonHom.one_hom _
  refine ⟨PP, cub, hsym t₀.sym, fun b => ?_, ?_, ⟨m, h, hme, hact, hlin⟩, rfl⟩
  · refine (cls_eq_iff (isLB_cube _ PP.isLB) (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB, cls_cube _ PP.isLB]
    have hsm : Smooth (G ⊗ G).hom := by
      show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
      infer_instance
    have hgc : GeometricallyConnected (G ⊗ G).hom := by
      show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
      exact GeometricallyConnected.comp _ _
    let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom j)
    let u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition
    have hy : ∀ y : G ⊗ G ⟶ G, ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ y := fun y =>
      ⟨Over.homMk (h.1.lift (u ≫ y).left T'.hom (Over.w (u ≫ y))) (h.1.lift_snd _ _ _),
        Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
    obtain ⟨y₁, hy₁⟩ := hy (fst G G)
    obtain ⟨y₂, hy₂⟩ := hy (snd G G)
    let e : 𝟙_ (Over S) ⟶ G ⊗ G := lift η[G] η[G]
    refine pic_ext S hS j (G ⊗ G).hom e.left u.left T'.hom hsm
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · have h₀ := (cls_eq_iff (isLB_cube _ t₀.PP.isLB) (isLB_cube _ t₀.PP.isLB)).2 (t₀.adj b)
      rw [cls_cube _ t₀.PP.isLB, cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := congrArg (pull (lift y₁ y₂).left) h₀
      rw [pull_cubeCls_pre, pull_cubeCls_pre] at h₁
      refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
        (h₁.trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
      · fin_cases i
        · simp [pa, hy₁]
        · simp [hy₂]
      · fin_cases i
        · simp [hy₁]
        · simp [pa, hy₂]
    · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
      congr 1
      funext i
      fin_cases i <;> simp [e, ha1]
  · refine (cls_eq_iff PP.isLB (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB]
    refine pic_ext S hS j G.hom (eSec G) m.F t₀.G.hom inferInstance
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_
    · have h₀ := (cls_eq_iff t₀.PP.isLB (isLB_cube _ t₀.PP.isLB)).2 t₀.prim
      rw [cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := pull_cubeCls_push h ![𝟙 t₀.G, t₀.act.act H.w0] ![𝟙 G, act.act H.w0] (pushPt h.1.w (𝟙 t₀.G))
        (fun i => by
          fin_cases i
          · simp
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)) (cls PP.L PP.isLB)
      have e : (pushPt h.1.w (𝟙 t₀.G)).left = m.F := Category.id_comp _
      rw [e] at h₁
      exact h₀.trans h₁.symm
    · refine hrig.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
      refine (cubeCls_one (n := 2) _ hrig).symm.trans ?_
      congr 1
      funext i
      fin_cases i <;> simp [ha1]

end GlobalTheory.TripleExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.CompleteBaseExpansion
open GlobalTheory.BaseExpansionExists

section General
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem pull_le (h : Y' ⟶ Y) (j : PUnit → K → L.ι) :
    ((LB.LinComb L φ ε).pull h).U j ≤ LB.wchart L (fun k => h ≫ φ k) (j PUnit.unit) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k

theorem le_pull (h : Y' ⟶ Y) (j : K → L.ι) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull h).U (fun _ => j) :=
  fun _ hy => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)

theorem g_pull (h : Y' ⟶ Y) (y : Y') (j j' : PUnit → K → L.ι) (hj : y ∈ ((LB.LinComb L φ ε).pull h).U j)
    (hj' : y ∈ ((LB.LinComb L φ ε).pull h).U j') :
    gs (𝟙 Y') y _ (((LB.LinComb L φ ε).pull h).g j j').val =
      (trF (fun k => h ≫ φ k) ε (𝟙 Y') y (j PUnit.unit) (j' PUnit.unit)).val := by
  have hm : (𝟙 Y' : Y' ⟶ Y') y ∈ ((LB.LinComb L φ ε).pull h).U j ⊓ ((LB.LinComb L φ ε).pull h).U j' := ⟨hj, hj'⟩
  refine (gs_unit (𝟙 Y') y _ hm _).trans (congrArg Units.val ?_)
  refine (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y j j' hj hj').trans ?_
  refine (gm_linComb L φ ε (𝟙 Y' ≫ h) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans ?_
  simp only [trF, Category.assoc]

theorem exists_in (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε)) :
    ∃ s' : LB.Sec ((LB.LinComb L φ ε).pull h), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : PUnit → K → L.ι),
      r z ∈ ((LB.LinComb L φ ε).pull h).U j →
      gs r z _ (s'.f j) = gs r z (LB.wchart L (fun k => h ≫ φ k) (j PUnit.unit)) (s.f (j PUnit.unit)) := by
  refine ⟨⟨fun j => (Y'.presheaf.map (homOfLE (pull_le h j)).op).hom (s.f (j PUnit.unit)),
    fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z j hz => gs_res r z _ hz _⟩
  refine ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (pull_le h j) hy.1 _)).trans (Eq.trans ?_
    ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·) (g_pull h y j j' hy.1 hy.2)
      ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (pull_le h j') hy.2 _)))).symm)
  exact sec_trans s (𝟙 Y') y (pull_le h j hy.1) (pull_le h j' hy.2)

theorem exists_out (h : Y' ⟶ Y) (s' : LB.Sec ((LB.LinComb L φ ε).pull h)) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs r z (LB.wchart L (fun k => h ≫ φ k) j) (s.f j) =
        gs r z (((LB.LinComb L φ ε).pull h).U (fun _ => j)) (s'.f (fun _ => j)) := by
  refine ⟨⟨fun j => (Y'.presheaf.map (homOfLE (le_pull (ε := ε) h j)).op).hom (s'.f (fun _ => j)),
    fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z j hz => gs_res r z _ hz _⟩
  have hm : (𝟙 Y' : Y' ⟶ Y') y ∈ ((LB.LinComb L φ ε).pull h).U (fun _ => j) ⊓
    ((LB.LinComb L φ ε).pull h).U (fun _ => j') := ⟨le_pull h j hy.1, le_pull h j' hy.2⟩
  refine ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (le_pull h j) hy.1 _)).trans (Eq.trans ?_
    ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ ε (𝟙 Y') y j j' hy.1 hy.2)))
      ((gs_res (𝟙 Y') y _ hy _).trans (gs_res (𝟙 Y') y (le_pull h j') hy.2 _)))).symm)
  exact (gs_res (𝟙 Y') y _ hm _).symm.trans ((congrArg (gs (𝟙 Y') y _) (s'.compat _ _)).trans
    ((gs_mul (𝟙 Y') y _ hm _ _).trans (congrArg₂ (· * ·) (g_pull h y _ _ hm.1 hm.2) (gs_res (𝟙 Y') y _ hm _))))

theorem gs_eq_of_sval (hL : L.IsLB) {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (s' : LB.Sec (LB.LinComb L φ' ε)) (r : Z ⟶ Y) (r' : Z ⟶ Y') (e : ∀ k, r ≫ φ k = r' ≫ φ' k) (z : Z)
    (h : ∀ J, Good L z J → sval s r z J = sval s' r' z J) (j : K → L.ι) (hj : r' z ∈ LB.wchart L φ' j) :
    gs r z (LB.wchart L φ j) (s.f j) = gs r' z (LB.wchart L φ' j) (s'.f j) := by
  obtain ⟨J, hJ⟩ := exists_good_pt hL z
  have hj₀ : r z ∈ LB.wchart L φ j := Set.mem_iInter.2 fun k =>
    (congrArg (fun p : Z ⟶ X => p z ∈ L.U (j k)) (e k)).mpr (Set.mem_iInter.1 hj k)
  refine (sec_trans s r z hj₀ (hJ.mem φ r)).trans (Eq.trans ?_ (sec_trans s' r' z hj (hJ.mem φ' r')).symm)
  refine congrArg₂ (· * ·) (congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)) (h J hJ)
  beta_reduce
  rw [e k]

end General

section Levels
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

theorem exists_limit (hS : SecAlgSt) (hI : IsAdicComplete I R) (D : DegPre R) (k : ℕ) (α : D.X)
    (f : ∀ e, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe I e).left ≫ D.famφB α i) (DegPre.famε k)))
    (hf : ∀ e z J, Good D.P.L z J → sval (f (e + 1)) (thickMap R I e D.P.A) z J = sval (f e) (𝟙 _) z J) :
    ∃ s : LB.Sec (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)),
      ∀ e z J, Good D.P.L z J → sval s (D.prBe I e).left z J = sval (f e) (𝟙 _) z J := by
  choose f' hf' using fun e => exists_in (φ := D.famφB α) (fstG I e D.P.A).left (f e)
  obtain ⟨s', hs', -⟩ := hS R I hI D.P.A D.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.P (IsPullback.id_horiz _)) _ (DVR.linComb_isLB _ D.P.isLB _ _) f'
    fun e z J hJ => by
      refine (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I (e + 1) D.P.A).left) _)).trans
        (Eq.trans ?_ (hf' _ _ _ z _ (hJ.mem (fun _ : PUnit => (fstG I e D.P.A).left) _)).symm)
      have E : thickMap R I e D.P.A ≫ (fstG I (e + 1) D.P.A).left = 𝟙 _ ≫ (fstG I e D.P.A).left :=
        (thickMap_fst e).trans (Category.id_comp _).symm
      beta_reduce
      rw [E]
      exact gs_eq_of_sval D.P.isLB _ _ _ _ (fun i => (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ D.famφB α i) E).trans (Category.assoc _ _ _))) z (hf e z) _
        (pull_le _ _ (hJ.mem (fun _ : PUnit => (fstG I e D.P.A).left) _))
  obtain ⟨s₁, hs₁⟩ := exists_out (𝟙 _) s'
  obtain ⟨s, hs⟩ := exists_sec D.P.isLB (φ' := D.famφB α) (ε' := DegPre.famε k)
    (fun U _ h => by simp only [Category.id_comp]) s₁
  refine ⟨s, fun e z J hJ => (hs _ _ z J hJ).trans ((hs₁ _ _ z _ (hJ.mem _ _)).trans ?_)⟩
  have hN : Good (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)) z (fun ψ i => J (ψ ≫ D.famφB α i)) :=
    fun ψ => hJ.mem _ ψ
  refine Eq.trans ?_ ((hs' e z _ hN).trans
    ((hf' _ _ _ z _ (hN.mem (fun _ : PUnit => (fstG I e D.P.A).left) _)).trans ?_))
  · exact (sval_of s' _ z _ _ (fun _ => funext fun i => congrArg J (Category.assoc _ _ _))).symm
  · exact (sval_of (f e) _ z J _ (fun i => congrArg J (Category.assoc _ _ _).symm)).symm

variable {D : DegPre R} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_expT (hS' : SecAlgSt) (hI : IsAdicComplete I R) (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) :
    ∃ f, U.ExpT (𝟙_ _) k σ f := by
  have hB := D.P.isLB
  have hG := U.P.L.isLB
  have lam : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ G).inv.left ≫ (snd (𝟙_ _) G).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]

  have lev : ∀ e : ℕ, ∃ τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => (U.gt e).pG.left) (fun _ => (k : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) JG J,
        Good U.P.L.L z JG → Good D.P.L z J →
        sval τ r z J = (gw (U.w e) r z (J (r ≫ (U.gt e).pG.left))
          (fun _ => JG (r ≫ (fstG I e G).left))).val ^ k *
          sval σ ((r ≫ (fstG I e G).left) ≫ (λ_ G).inv.left) z JG := fun e => by
    obtain ⟨s, hs⟩ := exists_pull (φ' := fun _ : Fin 1 => (fstG I e G).left)
      ((fstG I e G).left ≫ (λ_ G).inv.left)
      (fun _ => by rw [Category.assoc, lam', Category.comp_id]) σ
    obtain ⟨τ, hτ⟩ := exists_carry hG hB (U.w e) (U.w_gen e) k s
    refine ⟨τ, fun Z r z JG J hJG hJ => (hτ Z r z JG J hJG hJ).trans (congrArg _ ((hs Z r z JG hJG).trans ?_))⟩
    exact congrArg (fun p => sval σ p z JG) (Category.assoc _ _ _).symm
  choose τ hτ using lev
  have ex := fun e => existsUnique_level_expansion R I D e G (U.gt e) k (τ e)
  choose f hf hu using ex
  choose S hS hsum using hf

  have compat : ∀ α e z J, Good D.P.L z J →
      sval (f (e + 1) α) (thickMap R I e D.P.A) z J = sval (f e α) (𝟙 _) z J := by
    intro α e
    choose f' hf' using fun β => exists_pull
      (φ' := fun i => (D.prBe I e).left ≫ D.famφB β i) (thickMap R I e D.P.A)
      (fun i => ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.famφB β i) (thickMap_prBe e))).symm) (f (e + 1) β)
    have E : f' = f e := by
      refine hu e f' ⟨S (e + 1), fun β hβ => zero_of_sval hB fun y J hJ =>
        (hf' β _ _ y J hJ).trans (sval_zero (hS _ β hβ) _ hJ), fun z J hJ => ?_⟩
      obtain ⟨JG, hJG⟩ := exists_good_pt hG z
      have a := sum_of_id (hsum (e + 1)) (thickMap R I e G) z hJ
      have b : sval (τ e) (𝟙 (thickObj R I e G).left) z J =
          sval (τ (e + 1)) (thickMap R I e G) z J := by
        refine (hτ e _ _ z JG J hJG hJ).trans (Eq.trans ?_ (hτ (e + 1) _ _ z JG J hJG hJ).symm)
        have c := U.w_compat e _ (𝟙 _) z _ _ (hJ (U.gt e).pG.left) (hJG (fstG I e G).left)
        rw [Category.id_comp] at c
        rw [U.gt_q, thickMap_fst, c]
        simp only [Category.id_comp]
      refine b.trans (a.trans (Finset.sum_congr rfl fun β _ => congrArg₂ (· * ·) ?_ (congrArg Units.val ?_)))
      · exact (congrArg (fun p => sval (f (e + 1) β) p z J) (q_thickMap U e).symm).trans (hf' β _ _ z J hJ).symm
      · exact ((congrArg (fun p => val ((U.gt (e + 1)).t β) p z J) (Category.id_comp _).symm).trans
          (val_pull hJ _ _ _).symm).trans (val_corr hJ (U.gt_t e β) _)
    intro z J hJ
    rw [← E]
    exact ((hf' α _ _ z J hJ).trans (congrArg (fun p => sval (f (e + 1) α) p z J) (Category.id_comp _))).symm
  choose s hs using fun α => exists_limit hS' hI D k α (fun e => f e α) (compat α)
  choose F hF using fun α => exists_pull (snd (𝟙_ _) D.P.A).left (famφT_eq (𝟙_ _) α) (s α)
  refine ⟨F, fun e => ⟨S e, fun Z x rG rB hrG hrB _ z JG J hJG hJ => ?_⟩⟩
  have v : ∀ α, sval (F α) rB z J = sval (f e α) (x ≫ (U.gt e).q.left) z J := fun α => by
    refine (hF α _ _ z J hJ).trans ?_
    have a := sval_eq_of_id (hs α e) (x ≫ (U.gt e).q.left) z hJ
    refine Eq.trans (congrArg (fun p => sval (s α) p z J) (hrB.trans (Category.assoc _ _ _).symm)) (a.trans ?_)
    exact congrArg (fun p => sval (f e α) p z J) (Category.comp_id _)
  refine ⟨fun α hα => (v α).trans (sval_zero (hS e α hα) _ hJ), ?_⟩
  have r : rG = (x ≫ (fstG I e G).left) ≫ (λ_ G).inv.left := by
    rw [← hrG, Category.assoc, lam, Category.comp_id]
  rw [r]
  refine (hτ e _ x z JG J hJG hJ).symm.trans ((sum_of_id (hsum e) x z hJ).trans ?_)
  exact Finset.sum_congr rfl fun α _ => congrArg (· * _) (v α).symm

theorem expT_unique [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (U : PreU I D A G) (k : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (f f' : ∀ α, SecBT D (𝟙_ _) k α) (h : U.ExpT (𝟙_ _) k σ f) (h' : U.ExpT (𝟙_ _) k σ f') :
    f = f' := by
  have hd := ExpUniq.expT_diff h h'
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have lam : (snd (𝟙_ _) D.P.A).left ≫ (λ_ D.P.A).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  have lam' : (λ_ D.P.A).inv.left ≫ (snd (𝟙_ _) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.inv_hom_id, Over.id_left]
  refine funext fun α => ExpUniq.eq_of_diffSec (zero_of_sval D.P.isLB fun y J hJ => ?_)
  obtain ⟨s, hs⟩ := exists_pull (λ_ D.P.A).inv.left (fun _ => rfl) (ExpUniq.diffSec (f α) (f' α))
  have h₀ := (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.P.A).1 _ (DVR.linComb_isLB _ D.P.isLB _ _) s
    fun e j => fn_ext fun z hz => by
      have hz' : (𝟙 (thickObj R I e D.P.A).left : _ ⟶ _) z ∈ (fstG I e D.P.A).left ⁻¹ᵁ _ := hz
      refine (gs_pull (𝟙 _) (fstG I e D.P.A).left z _ hz' _).trans (Eq.trans ?_ ((gs_eq (𝟙 _) z _ hz' _).trans
        ((congrArg _ (map_zero _)).trans (map_zero _))).symm)
      refine ExpUniq.gs_eq_zero_of_sval D.P.isLB s _ z (fun J hJ => (hs _ _ z J hJ).trans ?_) j hz'
      refine ExpUniq.sval_term_eq_zero hd (fun Z r z J hJ => by rw [ExpUniq.sval_diffSec _ _ _ hJ, sub_self]) α e _
        (pullback.snd D.P.A.hom (thick R I e)) ?_ z J hJ
      rw [Category.assoc _ _ (snd (𝟙_ _) D.P.A).left, lam', Category.comp_id, Category.id_comp]
      exact pullback.condition
  have E := (hs _ (snd (𝟙_ _) D.P.A).left y J hJ).symm.trans (sval_zero h₀ _ hJ)
  rwa [lam] at E

end Levels

theorem main : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k), ∃! f : ∀ α, SecBT D (𝟙_ _) k α, U.ExpT (𝟙_ _) k σ f := by
  intro _ _ hE R _ _ _ I hR _ D A G _ _ U k σ
  have := hR.1
  have := hR.2.2.2
  exact existsUnique_of_exists_of_unique (exists_expT hE.2.2.1 hR.2.2.2 U k σ)
    (expT_unique (IsAdicComplete.le_jacobson_bot I) U k σ)

end GlobalTheory.CompleteBaseExpansion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBaseStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_expansion_section_admissible_base : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k), ∃! f : ∀ α, SecBT D (𝟙_ _) k α, U.ExpT (𝟙_ _) k σ f := by
  first | exact @GlobalTheory.CompleteBaseExpansion.main | exact GlobalTheory.CompleteBaseExpansion.main | (intros; apply GlobalTheory.CompleteBaseExpansion.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitWeightZeroIntegralCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitWeightZeroIntegralCoords
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ModPrim

theorem exists_unit_and_residue_point : Out.Laws → Out.Laws2 → ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (c : Sp (OO p) ⟶ G.left) (w : J → OO p), c ≫ G.hom = spMap j → Crd H σ c w → (∃ i, cls i = 0 ∧ IsUnit (w i)) ∧ ∃ x : m.Φ.Pt, x.left ≫ m.r = rPt p ≫ c ∧ Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
  intro L₁ L₂ p _ V _ j G _ g N N' X _ q H J _ σ cls m hB c w hc hw
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have pb : IsPullback m.r m.Φ.G.hom G.hom (rPt p ≫ spMap j) := m.cart.1
  have hsq : (rPt p ≫ c) ≫ G.hom = 𝟙 _ ≫ rPt p ≫ spMap j := by
    rw [Category.assoc, hc, Category.id_comp]
  let x : m.Φ.Pt := Over.homMk (pb.lift (rPt p ≫ c) (𝟙 _) hsq) (pb.lift_snd _ _ hsq)
  have hx : x.left ≫ m.r = rPt p ≫ c := pb.lift_fst _ _ hsq
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists (R := kb p) (m.Φ.H_isLB 1) m.F x.left
  have h₁ := m.red x v hv
  rw [hx] at h₁
  have h₂ := CrdCalc.crd_map (IsLocalRing.residue (OO p)) hw
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique h₁ h₂
  have h₃ : Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
    have := CrdCalc.crd_smul u hv
    rwa [← funext hu] at this
  refine ⟨?_, x, hx, h₃⟩
  have hcov := (GlobalTheory.T.immBy_weight_zero' L₁ L₂ (kb p) m.Φ g N N' _ J _ m.F m.pol hB m.good m.dim).1
  have hmem : (x.left : Sp (kb p) ⟶ m.Φ.G.left) (IsLocalRing.closedPoint (kb p)) ∈
      ⨆ i ∈ {i | m.xe.symm (cls i) = 0}, Out.nonzeroLocus (m.F i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hmem
  obtain ⟨i, hi, hm⟩ := hmem
  refine ⟨i, m.xe.symm.map_eq_zero_iff.1 hi, ?_⟩
  have h₄ := (CrdCalc.crd_isUnit_iff i h₃).2 ((CrdCalc.top_le_iff _ _).2 hm)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h₄.ne_zero

end GlobalTheory.ZH.ModPrim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitWeightZeroIntegralCoordsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_weightZero_integral_coords : Out.Laws → Out.Laws2 → ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (c : Sp (OO p) ⟶ G.left) (w : J → OO p), c ≫ G.hom = spMap j → Crd H σ c w → (∃ i, cls i = 0 ∧ IsUnit (w i)) ∧ ∃ x : m.Φ.Pt, x.left ≫ m.r = rPt p ≫ c ∧ Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
  first | exact @GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point | exact GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point | (intros; apply GlobalTheory.ZH.ModPrim.exists_unit_and_residue_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetryHypExtendsSemiAbelianDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetryHypExtendsSemiAbelianDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymExtendDvr

theorem isGrpPullback_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 _) (by simp)
  have e₁ : x₀ = u ≫ x ≫ e.hom := Over.OverMorphism.ext (hx.trans (Category.id_comp _).symm)
  have e₂ : y₀ = u ≫ y ≫ e.hom := Over.OverMorphism.ext (hy.trans (Category.id_comp _).symm)
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  exact Category.id_comp _

theorem hypS_of_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∀ L : RigLB G, LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → HypS G L.L := by
  intro ext V _ _ _ A G _ _ hG H gen hgen L hL
  have := hG.smooth
  have := hG.geomConnected
  have hc : IsCommMonObj ((Over.pullback (jK V)).obj G) := Functor.isCommMonObj_obj
  have hA : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  have H' : HypS ((Over.pullback (jK V)).obj G) (A.L.pull gen.hom.left) :=
    GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A _ (𝟙 _) gen.hom.left A.L _ A.isLB hA (isGrpPullback_of_iso gen)
      ((GlobalTheory.PrimNorm.lbIso_iff A.isLB _ _ _ _).2 rfl) H
  have : IsOpenImmersion (jK V) := GlobalTheory.DvrModel.isOpenImmersion_generic (K := FractionRing V) (f := 𝟙 _)
    (j := jK V) (fK := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
  refine GlobalTheory.SymExtend.hypS_extend (GlobalTheory.IsNormalScheme.pred _) (isGrpPullback_pullback G (jK V)) ?_ _ L hA hL.symm H'
  intro α hα
  obtain ⟨F, ⟨hF, eF⟩, u⟩ := ext V (FractionRing V) G G hG hG α hα
  have c : ∀ F : G ⟶ G, ((Over.pullback (jK V)).map F).left ≫ pullback.fst G.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ F.left := fun F => pullback.lift_fst _ _ _
  refine ⟨F, ⟨hF, ?_⟩, fun F' h' => u F' ⟨h'.1, ?_⟩⟩
  · rw [← eF]
    exact (c F).symm
  · refine Over.OverMorphism.ext (pullback.hom_ext ((c F').trans h'.2) ?_)
    exact (Over.w ((Over.pullback (jK V)).map F')).trans (Over.w α).symm

end GlobalTheory.SymExtendDvr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetryHypExtendsSemiAbelianDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetryHyp_extends_semiAbelian_dvr : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∀ L : RigLB G, LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → HypS G L.L := by
  first | exact @GlobalTheory.SymExtendDvr.hypS_of_generic | exact GlobalTheory.SymExtendDvr.hypS_of_generic | (intros; apply GlobalTheory.SymExtendDvr.hypS_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisSeparates
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisSeparates
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.AdaptedSep

theorem basis_separates : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → (∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → w ≠ 0) ∧ (∀ (a a' : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (u.H k) σ (u.toG a') w → a = a') ∧ ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∃ a' : u.PtC, u.toG a' = a := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k hk J _ σ cls f ⟨_, h₂, h₃, h₄, h₅, h₆, h₇⟩
  obtain ⟨m, t, ht⟩ := CrdMove.immBy_lbPow hL.1.ample _ u.A k hk
  obtain ⟨s, hs⟩ := CrdMove.exists_transport u.A.isLB u.U.LG.isLB u.U.gen.hom.left u.U.gen.inv.left
    (congrArg (fun q => q.left) u.U.gen.inv_hom_id) (congrArg (fun q => q.left) u.U.gen.hom_inv_id) _ u.U.ext k t
  choose b hb using fun i => AdaptedSpan.exists_comb hL.1.globalFns u.U (by omega : 1 ≤ k) σ cls f h₂ h₃ h₄ h₅ h₆ h₇ (s i)
  have key : ∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (lbPow u.A.L k) t (a.left ≫ u.U.gen.hom.left)
      (fun i => ∑ j, algebraMap (FractionRing u.V) (PadicAlgCl p) (b i j) * w j) := fun a w h =>
    hs _ a.left _ (CrdMove.crd_comb (pullback.condition : pullback.fst u.G.hom (jK u.V) ≫ u.G.hom = _)
      (fun _ => (Category.comp_id _).symm) σ s b hb a.left _ (Over.w a) h)
  refine ⟨fun a w h hw => ?_, fun a a' w h h' => ?_, fun a ha => ?_⟩
  · have hm : (a.left ≫ u.U.gen.hom.left : Sp (PadicAlgCl p) ⟶ u.A.A.left) (IsLocalRing.closedPoint _) ∈
        ⨆ i ∈ Set.univ, nonzeroLocus (t i) := by rw [ht.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    obtain ⟨_, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have hu := (CrdCalc.crd_isUnit_iff i (key a w h)).2 ((CrdCalc.top_le_iff _ _).2 hi)
    simp [hw] at hu
  · have e := ImmSep.eq_of_crd_eq _ _ _ _ _ t _ (DVR.linComb_isLB _ u.A.isLB _ _) ht _ _ _ _
      ((Over.w (a ≫ u.U.gen.hom)).trans (Over.w (a' ≫ u.U.gen.hom)).symm) (key a w h) (key a' w h')
    exact (cancel_mono u.U.gen.hom).1 (Over.OverMorphism.ext e)
  · have e : gPt p ≫ spMap u.j = jFK (R := u.V) (PadicAlgCl p) ≫ jK u.V :=
      (Spec.map_comp _ _).symm.trans (Eq.trans rfl (Spec.map_comp
        (CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)))
        (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p)))))
    exact ⟨Over.homMk (pullback.lift a (jFK (R := u.V) (PadicAlgCl p)) (ha.trans e)) (pullback.lift_snd _ _ _),
      pullback.lift_fst _ _ _⟩

end GlobalTheory.ZH.AdaptedSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisSeparatesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crd_ne_zero_injective_surjective_of_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → (∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → w ≠ 0) ∧ (∀ (a a' : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (u.H k) σ (u.toG a') w → a = a') ∧ ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∃ a' : u.PtC, u.toG a' = a := by
  first | exact @GlobalTheory.ZH.AdaptedSep.basis_separates | exact GlobalTheory.ZH.AdaptedSep.basis_separates | (intros; apply GlobalTheory.ZH.AdaptedSep.basis_separates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelOfExpT
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelOfExpT
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.PsiExpansion

theorem exists_sec_of_retract {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (m : Y ⟶ Y') (hm : h ≫ m = 𝟙 Y')
    (e : ∀ k, m ≫ φ' k = φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε) (fun U _ g => by simp only [e]) (H1.SectionArithmetic.pullSec s' m)
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, Category.assoc, hm, Category.comp_id]

theorem snd_lift_unit {S : Scheme.{0}} (G : Over S) :
    (snd (𝟙_ _) G).left ≫ (lift (toUnit G) (𝟙 G)).left = 𝟙 (𝟙_ (Over S) ⊗ G).left := by
  have : snd (𝟙_ _) G ≫ lift (toUnit G) (𝟙 G) = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  exact congrArg CommaMorphism.left this

variable {R : Type} [CommRing R] [IsDomain R]


omit [IsDomain R] in
theorem exists_lift_of_retraction (F : Type) [Field F] [Algebra (FractionRing R) F] (g : F →+* FractionRing R)
    (hg : ∀ a, g (algebraMap (FractionRing R) F a) = a) {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) :
    ∃ κ' : T ⟶ TF (R := R) F, κ'.left ≫ jFK (R := R) F = κ.left := by
  let i : (TK R).left ⟶ Spec (CommRingCat.of F) := Spec.map (CommRingCat.ofHom g)
  have hi : i ≫ jFK (R := R) F = 𝟙 (TK R).left := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_id _))
    exact CommRingCat.hom_ext (RingHom.ext hg)
  have hκ : (κ.left ≫ i) ≫ jFK (R := R) F = κ.left := by
    rw [Category.assoc, hi, Category.comp_id]
  exact ⟨Over.homMk (κ.left ≫ i)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hκ).trans (Over.w κ))), hκ⟩

theorem exists_lift_frac {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) :
    ∃ κ' : T ⟶ TF (R := R) (FractionRing R), κ'.left ≫ jFK (R := R) (FractionRing R) = κ.left :=
  exists_lift_of_retraction (FractionRing R) (RingHom.id _) (fun _ => rfl) κ


omit [IsDomain R] in
theorem exists_sameG {G : Over (Spec (CommRingCat.of R))} {L : LB G.left} (hL : L.IsLB) {k : ℕ}
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ)))) :
    ∃ σ : H0 L k, SameG σ s :=
  exists_sec_of_retract hL _ _ (snd_lift_unit G)
    (fun _ => congrArg CommaMorphism.left (lift_snd (toUnit G) (𝟙 G))) s

theorem exists_sameB {D : DegPre R} {k : ℕ} (s : ∀ α, SecBT D (𝟙_ _) k α) : ∃ f : ∀ α, D.SecB k α, SameB f s := by
  have H : ∀ α, ∃ f : D.SecB k α, ∀ (Z : Scheme.{0}) (r : Z ⟶ _) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval f (r ≫ (snd _ D.P.A).left) z J := fun α => by
    refine exists_sec_of_retract D.P.isLB _ _ (snd_lift_unit D.P.A) (fun i => ?_) (s α)
    fin_cases i
    · exact congrArg CommaMorphism.left (lift_snd (toUnit D.P.A) (𝟙 D.P.A))
    · refine congrArg CommaMorphism.left (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫
        padd D.P.A (snd _ _) (toUnit _ ≫ D.c α) = padd D.P.A (𝟙 _) (toUnit _ ≫ D.c α) from ?_)
      simp only [padd, ← Category.assoc, comp_lift, lift_snd, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫ toUnit _ ≫ D.c α = toUnit _ ≫ D.c α from ?_)
      rw [← Category.assoc, comp_toUnit]
    · refine congrArg CommaMorphism.left
        (show lift (toUnit D.P.A) (𝟙 D.P.A) ≫ toUnit _ ≫ η[D.P.A] = toUnit _ ≫ η[D.P.A] from ?_)
      rw [← Category.assoc, comp_toUnit]
  choose f hf using H
  exact ⟨f, hf⟩

theorem psiRel_of_levelOneEq {D : DegPre R} {f₀ : ∀ α, D.SecB 1 α} {f : ∀ α, SecBT D (𝟙_ _) 1 α}
    (hs : SameB f₀ f) (h : PsiCompare.LevelOneEq D f₀) : PsiRel D (𝟙_ _) f := by
  intro χ T ρ κ y z J hJ
  obtain ⟨κ', hκ⟩ := exists_lift_frac κ
  have l : ∀ u : T ⟶ D.P.A, (lift ρ u).left ≫ (snd _ D.P.A).left = u.left := fun u =>
    congrArg CommaMorphism.left (lift_snd ρ u)
  have e := (h χ 0 rfl T κ' y z J hJ).trans (congrArg (fun q => sval (f₀ 0) (y * cT D T χ).left z J *
    (val (D.psi χ) q z J * rigV D z J).val) hκ)
  rw [hs χ _ _ z J hJ, hs 0 _ _ z J hJ, l, l]
  exact e.trans (mul_comm _ _)

theorem psiRel_of_expT : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal V), AdmBase V I → ∀ (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U₀ : Unif I D A G), Under U U₀.toUnifPre → ∀ (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D.toPre (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 σ f → PsiRel D.toPre (𝟙_ _) f := by
  intro h₁ h₂ V _ _ _ I hV D A G _ _ U U₀ hU σ f hE
  obtain ⟨σ₁, hσ₁⟩ := exists_sameG U.P.L.isLB σ
  obtain ⟨f₀, hf₀⟩ := exists_sameB f
  have ht : H0 U.P.L.L 1 = H0 U₀.toUnifPre.LG.L 1 := by rw [hU.2.1]
  have hc : HEq (cast ht σ₁) σ₁ := cast_heq ht σ₁
  have H := ((PreForm.under_exists_and_expands h₁ h₂ V I D A G U.semi).2.2 U U₀.toUnifPre hU 1 σ f (cast ht σ₁) f₀
    (fun τ hτ z J hJ => by
      obtain rfl : τ = σ₁ := eq_of_heq (hτ.trans hc)
      rw [hσ₁ _ _ z J hJ, Category.id_comp])
    (fun α z J hJ => by rw [hf₀ α _ _ z J hJ, Category.id_comp])).1 hE
  exact psiRel_of_levelOneEq hf₀
    (PsiCompare.levelOneEq_of_expandsAt h₁.globalFns hV U₀.toUnifPre (U₀.expand 1 le_rfl) _ f₀ H)

end GlobalTheory.PsiExpansion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelOfExpTStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiRel_of_expT' : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal V), AdmBase V I → ∀ (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U₀ : Unif I D A G), Under U U₀.toUnifPre → ∀ (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D.toPre (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 σ f → PsiRel D.toPre (𝟙_ _) f := by
  first | exact @GlobalTheory.PsiExpansion.psiRel_of_expT | exact GlobalTheory.PsiExpansion.psiRel_of_expT | (intros; apply GlobalTheory.PsiExpansion.psiRel_of_expT <;> assumption)
end
end
