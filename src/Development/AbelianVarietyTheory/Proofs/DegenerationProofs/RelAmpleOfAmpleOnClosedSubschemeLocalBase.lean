module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeutralGroupModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeutralGroupModelStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleLocalBase

theorem relAmple_baseChange {S S' : Scheme.{0}} [IsAffine S] {f : S' ⟶ S} {A : Over S} {A' : Over S'}
    {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left} (h : IsPullback φ A'.hom A.hom f)
    (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hA : RelAmple A L) : RelAmple A' L' := by
  obtain ⟨w, hw⟩ := hw
  exact relAmple_pull h hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S) (fun _ => trivial) hA

theorem relAmple_of_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (M : LB B.left), Flat B.hom → IsProjBy B.hom → M.IsLB → ∀ (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀), Function.Surjective g → ∀ (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)) → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → RelAmple Y₀ N₀ → RelAmple B M := by
  intro R _ _ _ B M hF hP hM R₀ _ _ g hg Y₀ b hb N₀ hN₀ hiso hA
  have hker : RingHom.ker g ≤ RingHom.ker (IsLocalRing.residue R) := by
    rw [IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)
  let g' : R₀ →+* IsLocalRing.ResidueField R :=
    RingHom.liftOfSurjective g hg ⟨IsLocalRing.residue R, hker⟩
  have hg' : g'.comp g = IsLocalRing.residue R := RingHom.liftOfSurjective_comp g hg _
  let k := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hk : Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom g) = k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  let ψ : pullback B.hom k ⟶ Y₀.left := hb.lift (pullback.fst B.hom k)
    (pullback.snd B.hom k ≫ Spec.map (CommRingCat.ofHom g'))
    (by rw [Category.assoc, hk, pullback.condition])
  have hψ : ψ ≫ b = pullback.fst B.hom k := hb.lift_fst _ _ _
  have hψ' : IsPullback ψ (pullback.snd B.hom k) Y₀.hom (Spec.map (CommRingCat.ofHom g')) := by
    refine IsPullback.of_right ?_ (hb.lift_snd _ _ _) hb
    rw [hψ, hk]
    exact IsPullback.of_hasPullback _ _
  have h₁ : RelAmple ((Over.pullback k).obj B) (M.pull (pullback.fst B.hom k)) :=
    relAmple_baseChange (A' := (Over.pullback k).obj B) hψ' hN₀ (pull_isLB hM _)
      (LBIso.chartPull (Geo.Tor.chartPullPull N₀ ψ ψ rfl)
        (chartPullSame M (fun _ : PUnit => pullback.fst B.hom k) (fun _ => b) (fun _ => 1) ψ
          fun _ => hψ.symm) hiso).symm hA
  obtain ⟨r, hr, h₂⟩ := GlobalTheory.AmpleNear.relAmple_near_fibre R B M hF hP hM _ (IsLocalRing.residue R) (fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, 1, by simp, by simp⟩) h₁
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).1 hr
  have htop : PrimeSpectrum.basicOpen r = ⊤ := by
    exact top_le_iff.1 fun p _ => fun hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  generalize (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) = U at htop h₂
  subst htop
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) ⊤
  have : IsIso j := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  have h₃ : IsPullback (inv (pullback.fst B.hom j)) B.hom (pullback.snd B.hom j) (inv j) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]⟩
  refine relAmple_baseChange (A := (Over.pullback j).obj B) h₃ (pull_isLB hM _) hM ?_ h₂
  exact (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSec M _ _ (IsIso.inv_hom_id (pullback.fst B.hom j)))
    ⟨_, idIso_isGen (pull_isLB hM _)⟩).symm

end GlobalTheory.AmpleLocalBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBaseStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_ample_on_closed_subscheme_localBase : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (M : LB B.left), Flat B.hom → IsProjBy B.hom → M.IsLB → ∀ (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀), Function.Surjective g → ∀ (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)) → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → RelAmple Y₀ N₀ → RelAmple B M := by
  first | exact @GlobalTheory.AmpleLocalBase.relAmple_of_closed | exact GlobalTheory.AmpleLocalBase.relAmple_of_closed | (intros; apply GlobalTheory.AmpleLocalBase.relAmple_of_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Pts
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
include hp hτ

theorem exists_torsion_up [IsIso τ] {n : ℕ} (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  let x₀ : T₀ ⟶ G := Over.homMk (inv τ ≫ x.left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hp.1.w, IsIso.inv_comp_eq, hτ, ← Category.assoc, Over.w])
  have e : τ ≫ x₀.left = x.left ≫ φ := IsIso.hom_inv_id_assoc _ _
  refine ⟨x₀, e, Over.OverMorphism.ext ((cancel_epi τ).1 ?_)⟩
  rw [over_pow hp τ hτ e, hx, over_one hp τ hτ]

theorem exists_torsion_down {n : ℕ} (x₀ : T₀ ⟶ G) (hx : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have w : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w, hτ]
  let x : T ⟶ A := Over.homMk (hp.1.lift _ _ w) (hp.1.lift_snd _ _ _)
  have e : τ ≫ x₀.left = x.left ≫ φ := (hp.1.lift_fst _ _ _).symm
  refine ⟨x, e, Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩
  rw [← over_pow hp τ hτ e, hx, over_one hp τ hτ]

theorem secRel_smul {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {a : ℤ} {B : Over S}
    (σ : T.left ⟶ B.left) (hσ : σ ≫ B.hom = T.hom ≫ f) (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ)
    {th : LB.Sec (LPow A L₁ a T)} {th₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w th th₀)
    {th' : LB.Sec (LPow G L₀ a B)} {c : Γ(B.left, ⊤)}
    (hc : SecM.ofSec G th' = c • SecM.ofSec G (VVRank.pullS G a β th₀)) :
    SecRel hp σ hσ w (SecM.toSec A (σ.appTop.hom c • SecM.ofSec A th)) th' := by
  intro Z r z J J' hJ hJ'
  have e : psi hp σ hσ ≫ (β ▷ G).left = psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst', psi_fst',
        Category.assoc, hβ]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', psi_snd']
  rw [sv_of_eq_mul (s := th') (t := VVRank.pullS G a β th₀) (c := c) (fun j => congrArg (fun q => q.1 j) hc) _ z hJ,
    sv_of_eq_mul (s := SecM.toSec A (σ.appTop.hom c • SecM.ofSec A th)) (t := th) (c := σ.appTop.hom c)
      (fun j => rfl) _ z hJ',
    VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc r _ (β ▷ G).left, e, h _ _ _ _ _ hJ hJ', mul_left_comm,
    Category.assoc r _ (fst B G).left, psi_fst', ← Category.assoc]
  exact congrArg (fun q => _ * (q * _)) (gs_pull _ σ z ⊤ trivial c).symm

end Pts

theorem exists_gen_thG_generic : Laws → Laws2 → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x₀ : Sp K ⟶ S) (P : PolAV (Sp K)) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G x₀ φ → LBIso P.L (L.pull φ) → ∀ (m : ℕ), Odd m → ∀ (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ y, y ^ (m ^ 2) = 1 ↔ ∃ i, x i = y) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x₀)), IsGenSec G L ((1 : ℕ) : ℤ) th ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (e : K →+* F) (x' : Sp F ⟶ S) (h : spMap e ≫ x₀ = x') (a : F) (th' : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))), SecM.ofSec G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀) th) → (∀ i, ∃ z, ThG G L ρ m th' z (fnOf (a * e (v i)))) ∧ ∀ z (c : F), ThG G L ρ m th' z (fnOf c) → ∃ i, c = a * e (v i) := by
  intro hLaw _ S G _ L ρ hL hρ K _ _ _ x₀ P φ hp ⟨w, hw⟩ m hm Ix x v hx hv
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  have hx' : ∀ i, x i ^ (m ^ 2) = 1 := fun i => (hx _).2 ⟨i, rfl⟩
  obtain ⟨thP, hg, hth⟩ := GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants K P ρ' hρ' m Ix x v hx' hv
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x₀).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x₀).hom = (baseOver (Sp K)).hom ≫ x₀ := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨th, hrel⟩ := exists_secRel_up hp τ hτ hw hL hL₁ thP
  refine ⟨th, ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg, fun F _ _ e x' h a th' hth' => ?_⟩
  choose y hy hy' using fun i => exists_torsion_up hp τ hτ (x i) (hx' i)
  have up : ∀ i, ThG G L ρ m th (y i) (fnOf (v i)) := fun i => by
    have q := ThG.up hp τ hτ hw hL hL₁ hr (hy i) (hy' i) hrel (hth i)
    rw [hi] at q
    exact q
  let T' : Over (Sp K) := Over.mk (spMap e)
  let u : T' ⟶ baseOver (Sp K) := Over.homMk (spMap e) (Category.comp_id _)
  let τ' : T'.left ⟶ (Over.mk x₀).left := spMap e
  have hτ' : τ' ≫ (Over.mk x₀).hom = T'.hom ≫ x₀ := rfl
  let σ : T'.left ⟶ (Over.mk x').left := 𝟙 (Sp F)
  haveI : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp F)))
  have hσ : σ ≫ (Over.mk x').hom = T'.hom ≫ x₀ := (Category.id_comp _).trans h.symm
  have hj : inv σ = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨t, ht⟩ := exists_secRel hp τ' hτ' hw hL hL₁ th
  have hrel' := secRel_smul hp τ' hτ' σ hσ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀)
    (Category.id_comp _) ht hth'
  have hu : ∀ i, (u ≫ x i) ^ (m ^ 2) = 1 := fun i => by rw [← MonObj.comp_pow, hx', MonObj.comp_one]
  have down : ∀ i, ThG P.A P.L ρ' m (SecM.toSec P.A (σ.appTop.hom (fnOf a) • SecM.ofSec P.A t)) (u ≫ x i)
      (fnOf (a * e (v i))) := fun i => by
    have e₁ : τ' ≫ (y i).left = (u ≫ x i).left ≫ φ :=
      (congrArg (spMap e ≫ ·) ((Category.id_comp _).symm.trans (hy i))).trans (Category.assoc _ _ _).symm
    have q := ThG.smul (th' := SecM.toSec P.A (σ.appTop.hom (fnOf a) • SecM.ofSec P.A t)) hL₁ rfl
      (ThG.move hp τ' hτ' hw hL hL₁ hr e₁ (hu i) ht (up i))
    have e₂ : σ.appTop.hom (fnOf a) * τ'.appTop.hom (fnOf (v i)) = fnOf (a * e (v i)) :=
      (congrArg (fnOf a * ·)
        (congrArg (fun q => q.hom (v i)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e))).symm).trans
        (map_mul (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom _ _).symm
    rw [e₂] at q
    exact q
  have hK : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hm.pos.ne')
  refine ⟨fun i => ?_, fun z c hz => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := exists_torsion_up hp σ hσ _ (hu i)
    have q := ThG.up hp σ hσ hw hL hL₁ hr hz hz' hrel' (down i)
    rw [hj] at q
    exact ⟨z, q⟩
  · obtain ⟨z', hz₁, hz₂⟩ := exists_torsion_down hp σ hσ z hz.1
    obtain ⟨y', hy₁, rfl⟩ := TorsionFieldExt.exists_of_isAlgClosed hLaw P u hK
      (by rw [← map_natCast e]; exact (map_ne_zero e).2 hK) z' hz₂
    obtain ⟨i, rfl⟩ := (hx y').1 hy₁
    have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom]
      exact (IsUnit.mk0 _ hK).map _
    have q : fnOf c = fnOf (a * e (v i)) :=
      ThG.unique hLaw P hm hun (ThG.move hp σ hσ hw hL hL₁ hr hz₁ hz₂ hrel' hz) (down i)
    exact ⟨i, (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective q⟩

end GlobalTheory.Ex.OneGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtensStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_thetaConstants_over_algClosedExtensions : Laws → Laws2 → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x₀ : Sp K ⟶ S) (P : PolAV (Sp K)) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G x₀ φ → LBIso P.L (L.pull φ) → ∀ (m : ℕ), Odd m → ∀ (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ y, y ^ (m ^ 2) = 1 ↔ ∃ i, x i = y) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x₀)), IsGenSec G L ((1 : ℕ) : ℤ) th ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (e : K →+* F) (x' : Sp F ⟶ S) (h : spMap e ≫ x₀ = x') (a : F) (th' : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))), SecM.ofSec G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀) th) → (∀ i, ∃ z, ThG G L ρ m th' z (fnOf (a * e (v i)))) ∧ ∀ z (c : F), ThG G L ρ m th' z (fnOf c) → ∃ i, c = a * e (v i) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_gen_thG_generic | exact GlobalTheory.Ex.OneGen.exists_gen_thG_generic | (intros; apply GlobalTheory.Ex.OneGen.exists_gen_thG_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegra
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesTorsion
open IsLocalRing GlobalTheory.UT.ExactTerm

theorem nonempty_equiv_of_basis {G : Type} [CommGroup G] {k r : ℕ} (hk : k ≠ 0) (v : Fin r → G) (hv : ∀ i, v i ^ k = 1)
    (h : ∀ y : G, y ^ k = 1 → ∃! c : Fin r → ZMod k, (List.ofFn fun i => v i ^ (c i).val).prod = y) :
    Nonempty ((powMonoidHom k : G →* G).ker ≃* Multiplicative (Fin r → ZMod k)) := by
  have : NeZero k := ⟨hk⟩
  simp only [List.prod_ofFn] at h
  let f : Multiplicative (Fin r → ZMod k) →* (powMonoidHom k : G →* G).ker := MonoidHom.mk'
    (fun c => ⟨∏ i, v i ^ (c.toAdd i).val, by
      show (∏ i, v i ^ (c.toAdd i).val) ^ k = 1
      rw [← Finset.prod_pow]
      exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hv, one_pow]⟩)
    fun a b => Subtype.ext (by
      show ∏ i, v i ^ (a.toAdd i + b.toAdd i).val = (∏ i, v i ^ (a.toAdd i).val) * ∏ i, v i ^ (b.toAdd i).val
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add])
  refine ⟨(MulEquiv.ofBijective f ⟨fun a b e => ?_, fun y => ?_⟩).symm⟩
  · exact (h _ (f b).2).unique (congrArg Subtype.val e) rfl
  · obtain ⟨c, hc⟩ := (h y.1 y.2).exists
    exact ⟨Multiplicative.ofAdd c, Subtype.ext hc⟩

section Geom
variable (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
  (t : Sp K ⟶ S)
include hL

theorem exists_pow_eq (a : Over.mk t ⟶ P.A) {n : ℕ} (hn : 1 ≤ n) : ∃ b : Over.mk t ⟶ P.A, b ^ n = a := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hL.mulN S P n hn
  obtain ⟨s, hs⟩ := H1.SectionDivision.exists_section (k := K) (pullback.snd (mulA P.A n).left a.left)
  have hb : (s ≫ pullback.fst (mulA P.A n).left a.left) ≫ (mulA P.A n).left = a.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs]; exact Category.id_comp _
  have hw : (s ≫ pullback.fst (mulA P.A n).left a.left) ≫ P.A.hom = t := by
    rw [← Over.w (mulA P.A n), ← Category.assoc, hb]; exact Over.w a
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk t ⟶ P.A, b ^ n = b ≫ mulA P.A n := fun b =>
    (congrArg (· ^ n) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) n b).symm
  rw [e]
  exact Over.OverMorphism.ext hb

theorem exists_basis {k : ℕ} (hk : (k : K) ≠ 0) : ∃ v : Fin (2 * P.g) → (Over.mk t ⟶ P.A), (∀ i, v i ^ k = 1) ∧
    ∀ y : Over.mk t ⟶ P.A, y ^ k = 1 →
      ∃! c : Fin (2 * P.g) → ZMod k, (List.ofFn fun i => v i ^ (c i).val).prod = y := by
  have := P.isAb.comm
  let c : Γ(Sp K, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(Sp K, ⊤) := c.toMulEquiv.isDomain _
  have hk0 : k ≠ 0 := fun e => hk (by rw [e, Nat.cast_zero])
  have : NeZero (k : K) := ⟨hk⟩
  have : NeZero k := ⟨hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K k
  have hζ' : IsPrimitiveRoot (c.symm ζ) k := hζ.map_of_injective c.symm.injective
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P k (Over.mk t)
  exact PrincipalNumerics.exists_basis_of_pairing (G := Over.mk t ⟶ P.A) (g := P.g) (Nat.pos_of_ne_zero hk0)
    (fun d hd => (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hk0))).2.2.2.2 K t (by
      obtain ⟨e, rfl⟩ := hd
      rw [Nat.cast_mul] at hk
      exact left_ne_zero_of_mul hk))
    (hζ'.isUnit_unit hk0) (fun x y c => WeilIs P.A P.L k x y c) w₁ w₂ w₃
    (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) (ThetaRep.eq_one_of_weilIs hL P t hk)
end Geom

section Val
variable {C : Type} [NormedField C] (S : ValuationSubring C)

theorem affine_ext {R : Type} [CommRing R] {f g : Sp S ⟶ Sp R} (h : spMap S.subtype ≫ f = spMap S.subtype ≫ g) :
    f = g := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) f
  obtain ⟨b, rfl⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) g
  have e₁ : a ≫ CommRingCat.ofHom S.subtype = b ≫ CommRingCat.ofHom S.subtype :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_comp]; exact h)
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
    (RingHom.congr_fun (congrArg CommRingCat.Hom.hom e₁) x)))

theorem separated_ext {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) [IsSeparated p] {f g : Sp S ⟶ X}
    (h : spMap S.subtype ≫ f = spMap S.subtype ≫ g) : f = g := by
  have e : f ≫ p = g ≫ p := affine_ext S (by rw [← Category.assoc, h, Category.assoc])
  let Q : ValuativeCommSq p :=
    { R := S, K := C, i₁ := spMap S.subtype ≫ f, i₂ := f ≫ p, commSq := ⟨Category.assoc _ _ _⟩ }
  exact congrArg CommSq.LiftStruct.l ((IsSeparated.valuativeCriterion p Q).elim ⟨f, rfl, rfl⟩ ⟨g, h.symm, e.symm⟩)

variable {S} (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1)
include hS

theorem norm_valF {X : Scheme.{0}} (x : Sp S ⟶ X) (U : X.Opens) (a : Γ(X, U))
    (ha : x (closedPoint S) ∈ X.basicOpen a) : ‖valF (spMap S.subtype ≫ x) U a‖ = 1 := by
  have h₁ : x ⁻¹ᵁ X.basicOpen a = ⊤ := DVR.eq_top_of_closedPoint_mem _ ha
  have ht : ⊤ ≤ x ⁻¹ᵁ U := fun q _ => X.basicOpen_le a (h₁.ge (Set.mem_univ q))
  have h' : ⊤ ≤ (spMap S.subtype ≫ x) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap S.subtype q))
  have hu : IsUnit ((x.appLE U ⊤ ht).hom a) := by
    refine (Sp S).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ((Sp S).mem_basicOpen _ y hy).1 ?_
    rw [Scheme.basicOpen_appLE, h₁]
    exact ⟨trivial, trivial⟩
  obtain ⟨u, hu⟩ := hu.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
  have e : (spMap S.subtype ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      x.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom S.subtype := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap S.subtype) x U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  have e' : valF (spMap S.subtype ≫ x) U a = S.subtype u.val := by
    rw [valF, dite_eq_left h', hu]
    exact congrArg (fun g => g.hom a) e
  have m : ‖S.subtype u.val‖ * ‖S.subtype u.inv‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    exact (congrArg (fun q => ‖S.subtype q‖) u.val_inv).trans (by rw [map_one, norm_one])
  have b₁ : ‖S.subtype u.val‖ ≤ 1 := (hS _).1 (show S from u.val).2
  have b₂ : ‖S.subtype u.inv‖ ≤ 1 := (hS _).1 (show S from u.inv).2
  rw [e']
  nlinarith [norm_nonneg (S.subtype u.val), norm_nonneg (S.subtype u.inv)]

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (m : Sp S ⟶ Y)
  {J : (Sp C ⟶ X) → L.ι} (hm : ∀ k, ⊤ ≤ (m ≫ φ k) ⁻¹ᵁ L.U (J ((spMap S.subtype ≫ m) ≫ φ k)))
include hm

theorem norm_vF (t : LB.Gen (LB.LinComb L φ ε)) : ‖vF t (spMap S.subtype ≫ m) J‖ = 1 := by
  refine norm_valF hS m _ _ ?_
  exact (Scheme.basicOpen_of_isUnit Y (Units.isUnit _)).ge (Set.mem_iInter.2 fun k => hm k trivial)

theorem norm_sF (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ z J', Good L z J' → IsUnit (sval s (Spec.map (CommRingCat.ofHom (residue S)) ≫ m) z J')) :
    ‖sF s (spMap S.subtype ≫ m) J‖ = 1 := by
  let z : Spec (CommRingCat.of (ResidueField S)) := closedPoint (ResidueField S)
  obtain ⟨J', hJ'⟩ := GlobalTheory.UT.CoefBasic.exists_good' hL z
  have e : (Spec.map (CommRingCat.ofHom (residue S)) ≫ m) z = m (closedPoint S) :=
    congrArg m (IsLocalRing.comap_closedPoint (residue S))
  have h₁ : (Spec.map (CommRingCat.ofHom (residue S)) ≫ m) z ∈
      LB.wchart L φ fun k => J ((spMap S.subtype ≫ m) ≫ φ k) := by
    rw [e]
    exact Set.mem_iInter.2 fun k => hm k trivial
  have h₂ := (congrArg IsUnit (sec_trans s _ z (hJ'.mem φ _) h₁)).mp (h z J' hJ')
  refine norm_valF hS m _ _ ?_
  rw [← e]
  exact (isUnit_gs_iff _ z _ h₁ _).1 (isUnit_of_mul_isUnit_right h₂)
end Val

theorem exists_norm_th (hL : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {D : DegPre R} {C : Type} [NormedField C] [IsAlgClosed C] [Algebra (FractionRing R) C] (hR : CExt R ⊥ C)
    {N : NumD C} (ν : NumOf D C N) (hν : ν.IntN) {n : ℕ} (hn : 2 ≤ n) (hC : ‖(n : C)‖ = 1) (a : N.A) :
    ∃ t, t ^ n = 1 ∧ ‖N.th (a * t)‖ = 1 := by
  obtain ⟨S, hS, hI⟩ := hν
  have := D.P.isAb.proper
  let f : R →+* S := ((algebraMap (FractionRing R) C).comp (algebraMap R _)).codRestrict S fun r => (hS _).2 (hR.1 r)
  have hf : spMap S.subtype ≫ spMap f = (TF (R := R) C).hom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  let ρ : TF (R := R) C ⟶ Over.mk (spMap f) := Over.homMk (spMap S.subtype) hf
  have hJ : ∀ y : Sp S ⟶ D.P.A.left, y ≫ D.P.A.hom = spMap f →
      ⊤ ≤ y ⁻¹ᵁ D.P.L.U (ν.J (spMap S.subtype ≫ y)) := fun y hy => by
    obtain ⟨x₀, e, h⟩ := hI (Over.homMk (spMap S.subtype ≫ y) (by rw [Category.assoc, hy]; exact hf))
    obtain rfl : x₀ = y := separated_ext S D.P.A.hom e
    exact h
  obtain ⟨m₀, hm₀, -⟩ := hI (ν.eA a)
  let m : Over.mk (spMap f) ⟶ D.P.A := Over.homMk m₀ (affine_ext S (by
    rw [← Category.assoc, hm₀]; exact (Over.w (ν.eA a)).trans hf.symm))
  have hm : ρ ≫ m = ν.eA a := Over.OverMorphism.ext hm₀
  have : IsAlgClosed (ResidueField S) := isAlgClosed_residueField_of_valuationRing_of_isAlgClosed S C
  have hκ : (n : ResidueField S) ≠ 0 := by
    have h0 : (n : C) ≠ 0 := fun e => by simp [e] at hC
    have hu : IsUnit (n : S) := IsUnit.of_mul_eq_one (⟨(n : C)⁻¹, (hS _).2 (by simp [hC])⟩ : S)
      (Subtype.ext (by simp [h0]))
    have := (hu.map (residue S)).ne_zero
    rwa [map_natCast] at this
  let r : Over.mk (Spec.map (CommRingCat.ofHom (residue S)) ≫ spMap f) ⟶ Over.mk (spMap f) := Over.homMk _ rfl
  obtain ⟨β, -, hβ⟩ := exists_generator_ne_zero hL.secBaseChange D.P
  obtain ⟨th, h₀, hth⟩ := hβ (ResidueField S) (Spec.map (CommRingCat.ofHom (residue S)) ≫ spMap f)
  obtain ⟨x₀, hx₀, hu⟩ := exists_good_point hL.goodPt hL.polBaseChange D.P _ hn hκ th h₀ (r ≫ m)
  obtain ⟨hfin, hflat, -⟩ := hL.mulN _ D.P n (by omega)
  obtain ⟨x, hx, ex⟩ : ∃ x : Over.mk (spMap f) ⟶ D.P.A, x ^ n = 1 ∧
      Spec.map (CommRingCat.ofHom (residue S)) ≫ x.left = x₀.left :=
    exists_torsion_lift S D.P.A n (spMap f) x₀ hx₀
  have ex' : r ≫ x = x₀ := Over.OverMorphism.ext ex
  obtain ⟨c, hc⟩ := ν.th_gen β
  refine ⟨ν.eA.symm (ρ ≫ x), by rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one], ?_⟩
  have e : (ν.eA (a * ν.eA.symm (ρ ≫ x))).left = spMap S.subtype ≫ (m * x).left := by
    rw [map_mul, MulEquiv.apply_symm_apply, ← hm, ← MonObj.comp_mul]; rfl
  have h₁ : ‖sF ν.th (spMap S.subtype ≫ (m * x).left) ν.J‖ = 1 :=
    norm_sF hS (m * x).left (fun _ => by
      simpa only [Category.comp_id] using hJ (m * x).left (Over.w _)) D.P.isLB ν.th fun z J hz => by
      have q := hu z J hz
      rw [hth _ _ z J hz, ThetaPtMove.ptSecT_snd, ← ex', ← MonObj.comp_mul] at q
      exact isUnit_of_mul_isUnit_right ((congrArg IsUnit
        (IndivisibleSection.sval_of_secIsMul (s := β) (t := ν.th) hc _ z hz)).mp q)
  have h₂ : ‖vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
      (spMap S.subtype ≫ spMap f) ν.J‖ = 1 :=
    norm_vF hS (spMap f) (fun _ => by
      rw [Category.assoc]
      exact hJ _ (Over.w (1 : Over.mk (spMap f) ⟶ D.P.A))) _
  have h₃ := congrArg norm (ν.th_eq (a * ν.eA.symm (ρ ≫ x)))
  rw [norm_mul, e, h₁, ← hf, h₂, _root_.mul_one] at h₃
  exact h₃

theorem tors_of_integral : Laws → Laws2 → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing R) C], CExt R ⊥ C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ n : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n D.P.g := by
  intro hL _ hB R _ _ _ _ D he hb C _ _ _ _ hR N ν hν n hp ho hC
  have h0 : (n : C) ≠ 0 := fun e => by simp [e] at hC
  have hj : ∀ j : ℕ, ((n ^ j : ℕ) : C) ≠ 0 := fun j => by rw [Nat.cast_pow]; exact pow_ne_zero _ h0
  obtain ⟨hW, hU⟩ := hB R D he hb C N ν
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  refine ⟨fun x => ?_, fun j => ?_, fun j b hb h => ?_, exists_norm_th hL hR ν hν hp.two_le hC, fun j h1 x x' l hl h => ?_⟩
  · obtain ⟨y, hy⟩ := exists_pow_eq hL D.P (jFK (R := R) C ≫ jK R) (ν.eA x) hp.pos
    exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  · obtain ⟨v, hv, h⟩ := exists_basis hL D.P (jFK (R := R) C ≫ jK R) (hj j)
    refine nonempty_equiv_of_basis (pow_ne_zero j hp.ne_zero) (fun i => ν.eA.symm (v i))
      (fun i => by rw [← map_pow, hv, map_one]) fun y hy => ?_
    refine (existsUnique_congr fun c => ?_).1 (h (ν.eA y) ((tor _ _).2 hy))
    simp only [List.prod_ofFn, ← map_pow, ← map_prod, MulEquiv.symm_apply_eq]
  · refine ν.eA.map_eq_one_iff.1 (ThetaRep.eq_one_of_weilIs hL D.P (jFK (R := R) C ≫ jK R) (hj j) _
      ((tor _ _).2 hb) fun y hy => ?_)
    obtain ⟨b', rfl⟩ := ν.eA.surjective y
    have hb' := (tor _ _).1 hy
    have := hW (n ^ j) (Nat.pos_of_ne_zero (pow_ne_zero j hp.ne_zero)) b b' hb hb'
    rwa [h b' hb', show unitOn (1 : Cˣ) = 1 from map_one (Units.map _)] at this
  · obtain ⟨-, hc⟩ := hU (n ^ j) ho.pow (hj j) {b : N.A // b ^ (n ^ j) ^ 2 = 1} Subtype.val Subtype.property
    obtain ⟨-, hs, -, hsep⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C _ D.P (jFK (R := R) C ≫ jK R) (n ^ j) ho.pow (hj j)
      {b : N.A // b ^ (n ^ j) ^ 2 = 1} (fun i => ν.eA i.1) fun i => (tor _ _).2 i.2
    have h3 : 3 ≤ n ^ j := by
      have : 3 ≤ n := by
        have := hp.two_le
        obtain ⟨k, rfl⟩ := ho
        omega
      exact this.trans (Nat.le_self_pow (by omega) n)
    refine ν.eA.injective (hsep h3 (fun y hy => ?_) _ _ (fun i => N.uth (n ^ j) i.1 x) (hc x)
      ((hs _ (fun i => N.uth (n ^ j) i.1 x') _ (hc x')).2 ⟨Units.mk0 l hl, funext fun i => h i.1 i.2⟩)).1
    obtain ⟨b, rfl⟩ := ν.eA.surjective y
    exact ⟨⟨b, (tor _ _).1 hy⟩, rfl⟩

end GlobalTheory.ValuesTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegraStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral : Laws → Laws2 → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing R) C], CExt R ⊥ C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ n : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n D.P.g := by
  first | exact @GlobalTheory.ValuesTorsion.tors_of_integral | exact GlobalTheory.ValuesTorsion.tors_of_integral | (intros; apply GlobalTheory.ValuesTorsion.tors_of_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.Ex.OneGen


open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic in
theorem exists_sec_pull_locus {X Y : Scheme.{0}} {L : LB X} (s : LB.Sec L) (φ : Y ⟶ X) :
    ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)),
      nonzeroLocus s' = φ ⁻¹ᵁ nonzeroLocus s := by
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L _ j 0
  have v : ∀ (j : Fin 1 → L.ι) (z : Y), z ∈ LB.wchart L (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z _ ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) =
        gs (𝟙 Y ≫ φ) z (L.U (j 0)) (s.f (j 0)) := fun j z hj =>
    (gs_res _ z _ hj _).trans (gs_pull _ φ z _ (l j hj) _)
  let s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        have hm : (𝟙 Y ≫ φ) z ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨l j hz.1, l j' hz.2⟩
        have g : (trF (L := L) (fun _ : Fin 1 => φ) (fun _ => 1) (𝟙 Y) z j j').val =
            gs (𝟙 Y ≫ φ) z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val := by
          refine Eq.trans ?_ (gs_unit _ z _ hm _).symm
          exact congrArg Units.val ((Fin.prod_univ_one _).trans (zpow_one _))
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            ((congrArg Units.val (gm_linComb L _ _ (𝟙 Y) z j j' hz.1 hz.2)).trans g))
              ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        exact (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg _ (gs_res _ z _ hm _)))) }
  have b : ∀ (j : Fin 1 → L.ι) (y : Y), y ∈ Y.basicOpen (s'.f j) ↔
      y ∈ LB.wchart L (fun _ : Fin 1 => φ) j ∧ φ y ∈ X.basicOpen (s.f (j 0)) := fun j y => by
    change y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) ↔ _
    rw [Scheme.basicOpen_res]
    exact and_congr_right fun _ => (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f (j 0))) y).symm
  refine ⟨s', SetLike.ext fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j 0, ((b j y).1 hj).2⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ nonzeroLocus s from h)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (b _ y).2
      ⟨Set.mem_iInter.2 fun _ => X.basicOpen_le _ hi, hi⟩⟩

theorem isUnit_sval_iff {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (Geo.Tor.mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (Geo.Tor.mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

theorem nz_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) {T : Over S}
    (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) (hσ : ∀ y : T.left, ∃ g, (fst T G).left g = y ∧ g ∈ nonzeroLocus σ)
    {V : Type} [CommRing V] [IsLocalRing V] (χ : Sp V ⟶ S) (h : Over.mk χ ⟶ T) :
    NZ G L χ (VVRank.pullS G _ h σ) := by
  obtain ⟨g, hg, hn⟩ := hσ (h.left (closedPoint V))
  have P : IsPullback (h ▷ G).left (fst (Over.mk χ) G).left (fst T G).left h.left := by
    refine IsPullback.of_right (h₁₂ := (snd T G).left) (v₁₃ := G.hom) (h₂₂ := T.hom) ?_ ?_
      (IsPullback.of_hasPullback T.hom G.hom).flip
    · rw [VVRank.whisker_snd_left, Over.w h]
      exact (IsPullback.of_hasPullback χ G.hom).flip
    · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  obtain ⟨g', h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback P g (closedPoint V) hg
  refine ⟨g', h₂, ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' hL g'
  have u := (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd T G).left) σ (𝟙 _ ≫ (h ▷ G).left) g' hJ).2
    (by rw [Category.id_comp, h₁]; exact hn)
  exact (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd (Over.mk χ) G).left) _ (𝟙 _) g' hJ).1
    ((congrArg IsUnit (VVRank.sv_pullS G _ h σ (𝟙 _) g' hJ)).mpr u)

theorem exists_sec_nz_up {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {L₀ : LB G.left} {L₁ : LB A.left}
    {w : LB.Iso L₁ (L₀.pull φ)} (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (h : GlobalTheory.LN.ThetaNZ A L₁) :
    ∃ σ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) (Over.mk f)),
      ∀ y : (Over.mk f).left, ∃ g, (fst (Over.mk f) G).left g = y ∧ g ∈ nonzeroLocus σ := by
  obtain ⟨θ, hθ⟩ := h
  let T : Over S' := Over.mk (𝟙 S')
  obtain ⟨s, hs⟩ := exists_sec_pull_locus θ (snd T A).left
  have hτ : (𝟙 S' : T.left ⟶ (Over.mk f).left) ≫ (Over.mk f).hom = T.hom ≫ f := rfl
  have : IsIso (𝟙 S' : T.left ⟶ (Over.mk f).left) := IsIso.id S'
  obtain ⟨σ, hσ⟩ := exists_secRel_up (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ hw hL₀ hL₁ (a := ((1 : ℕ) : ℤ)) s
  refine ⟨σ, fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hθ y
  obtain ⟨z, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback T.hom A.hom) y g hg.symm
  have hz : z ∈ nonzeroLocus s := by
    rw [hs]
    change pullback.snd T.hom A.hom z ∈ nonzeroLocus θ
    rw [h₂]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨J, hJ⟩ := exists_good' hL₀ z
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ z
  have e₁ := psi_fst' (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ
  refine ⟨psi (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, e₁]
    exact h₁
  have u := (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd T A).left) s (𝟙 _) z hJ').2 hz
  have e := hσ _ (𝟙 _) z J J' hJ hJ'
  rw [Category.id_comp] at e
  exact (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd (Over.mk f) G).left) σ _ z hJ).1
    ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))

theorem exists_nz_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → ∃ σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ)), ∀ (W' : Type) [CommRing W'] [IsLocalRing W'] (i : W →+* W') (χ' : Sp W' ⟶ S) (h : spMap i ≫ χ = χ'), NZ t.G t.PP.L χ' (VVRank.pullS t.G _ (Over.homMk (spMap i) h : Over.mk χ' ⟶ Over.mk χ) σ) := by
  intro h₁ h₂ E _ _ _ H S t W _ _ _ χ t' m hp
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨σ, hσ⟩ := exists_sec_nz_up m.cart hw t.PP.isLB t'.PP.isLB
    (GlobalTheory.ThetaDvr.thetaNZ_of_polAt h₁ h₂ E H W t' hp)
  exact ⟨σ, fun W' _ _ i χ' h => nz_pullS t.G t.PP.isLB σ hσ χ' _⟩

end GlobalTheory.Ex.OneGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAtStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nz_of_polAt' : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → ∃ σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ)), ∀ (W' : Type) [CommRing W'] [IsLocalRing W'] (i : W →+* W') (χ' : Sp W' ⟶ S) (h : spMap i ≫ χ = χ'), NZ t.G t.PP.L χ' (VVRank.pullS t.G _ (Over.homMk (spMap i) h : Over.mk χ' ⟶ Over.mk χ) σ) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_nz_of_polAt | exact GlobalTheory.Ex.OneGen.exists_nz_of_polAt | (intros; apply GlobalTheory.Ex.OneGen.exists_nz_of_polAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubicalOfGroupSchemeIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubicalOfGroupSchemeIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.AmpIso
open GlobalTheory.SS.AmpSub

theorem ampleCub_pull {S : Scheme.{0}} {N G : Over S} [GrpObj N] [GrpObj G] (ν : N ⟶ G) [IsMonHom ν]
    [IsAffineHom ν.left] {L : LB G.left} (h : AmpleCub G L) : AmpleCub N (L.pull ν.left) := by
  obtain ⟨hL, ⟨c, hc⟩, ⟨s, hs⟩, n, hn, ha⟩ := h
  refine ⟨pull_isLB hL _, ?_, ?_, n, hn, fun x => ?_⟩
  · refine gen_chartPull (chartPullLinComb L ν.left _ _ _ (ν ⊗ₘ ν ⊗ₘ ν).left fun I => ?_) c hc
    refine congrArg (fun z => z.left) (psum_comp ν (x3 N) (x3 G) (ν ⊗ₘ ν ⊗ₘ ν) (fun k => ?_) I.down)
    fin_cases k <;> simp [x3]
  · refine gen_chartPull (chartPullLinComb L ν.left _ _ _ ν.left fun k => ?_) s hs
    fin_cases k
    · exact congrArg (fun z => z.left) (GrpObj.inv_hom ν)
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · obtain ⟨σ, hx, hσ⟩ := ha (ν.left x)
    have e : Out.nonzeroLocus (chartSec (chartPullPw L ν.left n) σ) = ν.left ⁻¹ᵁ Out.nonzeroLocus σ :=
      nonzeroLocus_chartSec _ σ fun y j hj => ⟨fun _ => j, mem_pull.2 hj⟩
    refine ⟨chartSec (chartPullPw L ν.left n) σ, ?_, ?_⟩ <;> rw [e]
    · exact hx
    · exact hσ.preimage _

theorem exists_ampleCub_of_iso : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (e : G ≅ G'), IsMonHom e.hom → ∀ L' : LB G'.left, AmpleCub G' L' → ∃ L : LB G.left, AmpleCub G L := by
  intro S G G' _ _ e he L' h
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  exact ⟨_, ampleCub_pull e.hom h⟩

end GlobalTheory.SS.AmpIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubicalOfGroupSchemeIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleCubical_of_groupScheme_iso : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (e : G ≅ G'), IsMonHom e.hom → ∀ L' : LB G'.left, AmpleCub G' L' → ∃ L : LB G.left, AmpleCub G L := by
  first | exact @GlobalTheory.SS.AmpIso.exists_ampleCub_of_iso | exact GlobalTheory.SS.AmpIso.exists_ampleCub_of_iso | (intros; apply GlobalTheory.SS.AmpIso.exists_ampleCub_of_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.NeutralLevel

theorem isGrpPullback_of_iso_inv {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {G' : Over S'} [GrpObj G']
    (e : (Over.pullback f).obj G ≅ G') (he : IsMonHom e.hom) :
    IsGrpPullback G' G f (e.inv.left ≫ pullback.fst G.hom f) :=
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  ((isGrpPullback_of_iso e.symm).comp (isGrpPullback_pullback G f)).congr (Category.id_comp _) rfl

theorem exists_extension {S S' T : Scheme.{0}} {f : S' ⟶ S} {j : T ⟶ S'} {G : Over S} {G' : Over S'} {A : Over T}
    [GrpObj G] [GrpObj G'] [GrpObj A] {φ : G'.left ⟶ G.left} {ψ : A.left ⟶ G'.left}
    (h : IsGrpPullback G' G f φ) (hA : IsGrpPullback A G' j ψ) (c : ℕ)
    (hc : ∀ a : 𝟙_ (Over T) ⟶ A, ∃ s : 𝟙_ (Over S') ⟶ G', j ≫ s.left = (a ^ c).left ≫ ψ)
    (t : T ⟶ S) (ht : t = j ≫ f) (y : Over.mk t ⟶ G) :
    ∃ s : S' ⟶ G.left, s ≫ G.hom = f ∧ j ≫ s = (y ^ c).left := by
  have H := hA.comp h
  obtain rfl : t = (𝟙_ (Over T)).hom ≫ j ≫ f := ht.trans (Category.id_comp _).symm
  let a : 𝟙_ (Over T) ⟶ A := Over.homMk (H.1.lift y.left (𝟙_ (Over T)).hom (Over.w y)) (H.1.lift_snd _ _ _)
  have ha : pushHom H _ a = y := Over.OverMorphism.ext (H.1.lift_fst _ _ _)
  obtain ⟨s, hs⟩ := hc a
  refine ⟨s.left ≫ φ, ?_, ?_⟩
  · rw [Category.assoc, h.1.w, ← Category.assoc, Over.w s]
    exact Category.id_comp _
  · rw [← ha, ← map_pow, ← Category.assoc]
    exact (congrArg (· ≫ φ) hs).trans (Category.assoc _ _ _)

theorem exists_ampleCub_fibre {S S' T : Scheme.{0}} {f : S' ⟶ S} (j : T ⟶ S') {G : Over S} {G' : Over S'}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)
    (L : LB ((Over.pullback j).obj G').left) (hL : AmpleCub ((Over.pullback j).obj G') L)
    (t : T ⟶ S) (ht : j ≫ f = t) :
    ∃ N : LB ((Over.pullback t).obj G).left, AmpleCub ((Over.pullback t).obj G) N := by
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G t)
    (((isGrpPullback_pullback G' j).comp h).congr ht rfl)
  exact GlobalTheory.T.exists_ampleCubical_of_groupScheme_iso _ _ _ e he L hL

theorem smoothOfRelativeDimension_model {K W : Type} [Field K] [CommRing W] [IsDomain W]
    [Algebra K (FractionRing W)] (P : Out.PolAV (Sp K)) (G : Over (Sp W)) [GrpObj G] (hG : SmConn G)
    (hm : IsModel (L := FractionRing W) P.A G) : SmoothOfRelativeDimension P.g G.hom := by
  obtain ⟨e, -⟩ := hm
  obtain ⟨-, _, -, -, _⟩ := hG
  refine GlobalTheory.GenericDim.smoothOfRelativeDimension_of_generic W G P.g ?_
  have w : e.hom.left ≫ _ = pullback.snd G.hom (Out.jK W) := Over.w e.hom
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨w.trans (Category.comp_id _).symm⟩)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (isGrpPullback_pullback P.A (spMap (algebraMap K (FractionRing W)))).1 P.smoothDim)

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_level_model : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (R K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra V R] [Field K'] [Algebra R K'] [Algebra K K'], SH R K' → (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) → ∀ P : Out.PolAV (Sp K), ∃ (s : Finset R) (c : ℕ), 1 ≤ c ∧ ∀ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W → IsLocalHom W.val.toRingHom → ∃ (G : Over (Sp W)) (_ : GrpObj G) (L : Type) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (_ : Algebra K L), SmConn G ∧ (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsModel (L := L) P.A G ∧ SmoothOfRelativeDimension P.g G.hom ∧ (∃ N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N) ∧ ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left := by
  intro V K _ _ _ _ _ _ R K' _ _ _ _ _ _ _ hR hc P
  have : IsFractionRing R K' := hR.2.2.2
  let f := spMap (algebraMap K K')
  let P' : Out.PolAV (Sp K') :=
    have h := isGrpPullback_pullback P.A f
    have hL' := LB.isLB_pull P.isLB (pullback.fst P.A.hom f)
    have hw := (isGen_iff _).1 (PolBaseChange.lbIso_refl hL').choose_spec
    { A := (Over.pullback f).obj P.A
      isAb := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback f P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull (pullback.fst P.A.hom f)
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  obtain ⟨G', _, hG', he, c, hc1, hext⟩ := GlobalTheory.T.exists_neutral_group_model' R K' hR P'.A P'.isAb
    (GlobalTheory.AbProj.isProjBy_of_isPullback P' (IsPullback.id_horiz _))
  obtain ⟨L', hL'⟩ := GlobalTheory.SS.exists_ampleCub_spFibre R K' hR P' G'.Y hG' G'.e he
  obtain ⟨s, hs⟩ := GlobalTheory.smConn_model_descends V K R K' hc P.A P.isAb G'.Y hG' ⟨G'.e, he⟩
  refine ⟨s, c, hc1, fun W hW hsW hl => ?_⟩
  obtain ⟨G, _, _, ε, hG, hε, hcomm, hm⟩ := hs W hW hsW hl
  have h := isGrpPullback_of_iso_inv _ G ε hε
  have hA := isGrpPullback_of_iso_inv _ G'.Y G'.e he
  exact ⟨G, inferInstance, FractionRing W, inferInstance, inferInstance, inferInstance, inferInstance, hG, hcomm, hm,
    smoothOfRelativeDimension_model P G hG hm,
    exists_ampleCub_fibre _ h L' hL' _ (spMap_comp_spMap _ _),
    fun y => exists_extension h hA c hext _ (spMap_comp_spMap _ _).symm y⟩

end GlobalTheory.NeutralLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_neronNeutralComponent_finite_level : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (R K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra V R] [Field K'] [Algebra R K'] [Algebra K K'], SH R K' → (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) → ∀ P : Out.PolAV (Sp K), ∃ (s : Finset R) (c : ℕ), 1 ≤ c ∧ ∀ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W → IsLocalHom W.val.toRingHom → ∃ (G : Over (Sp W)) (_ : GrpObj G) (L : Type) (_ : Field L) (_ : Algebra W L) (_ : IsFractionRing W L) (_ : Algebra K L), SmConn G ∧ (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsModel (L := L) P.A G ∧ SmoothOfRelativeDimension P.g G.hom ∧ (∃ N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N) ∧ ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left := by
  first | exact @GlobalTheory.NeutralLevel.exists_level_model | exact GlobalTheory.NeutralLevel.exists_level_model | (intros; apply GlobalTheory.NeutralLevel.exists_level_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsKernelPolarisationTrivialSpreadLocalisatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsKernelPolarisationTrivialSpreadLocalisatio
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem exists_kTriv : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → GlobalTheory.AbLaw.IsProjBy G.hom → KTriv A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → KTriv G' L' := by
  intro hG R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hA h hL hL₀ hw hP hk
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ G L hL
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R G hA hP L _ hL hO
  have hrep : ∀ (T : Over (Sp R)) (x : T ⟶ G), GlobalTheory.UU.InK G L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  obtain ⟨e, he⟩ := (hrep _ _).1 (GlobalTheory.UU.inK_one hL (𝟙_ _))
  have hprop := hA.proper
  have hH' : IsProper H.hom := by rw [← Over.w j]; infer_instance
  have hsec : e.left ≫ H.hom = 𝟙 (Sp R) := Over.w e
  have hcl : IsClosedImmersion e.left := by
    have : IsClosedImmersion (e.left ≫ H.hom) := by
      rw [hsec]
      exact (inferInstance : IsClosedImmersion (𝟙 (Sp R)))
    exact IsClosedImmersion.of_comp e.left H.hom
  obtain ⟨a, ha, key⟩ := GlobalTheory.T.closed_immersion_generic_unit_locus R K _ _ e.left H.hom hcl inferInstance inferInstance (fun B _ y t hy => by
    have hdi : (y ≫ j.left) ≫ G.hom = t ≫ spMap (algebraMap R K) := by
      rw [Category.assoc, Over.w j, hy]
    let x : Over.mk t ⟶ A := Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
    let z : Over.mk (t ≫ spMap (algebraMap R K)) ⟶ H := Over.homMk y hy
    have hz : z ≫ j = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
    have hx : x = 1 := GlobalTheory.UU.InK.eq_one hk (GlobalTheory.UU.inK_of_push h hL hL₀ hw x ((hrep _ _).2 ⟨z, hz⟩))
    have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
    have h1 : toUnit _ ≫ e = z := by
      rw [← cancel_mono j, hz, hx', Category.assoc, he, MonObj.comp_one]
    exact ⟨(toUnit (Over.mk (t ≫ spMap (algebraMap R K)))).left, congrArg (fun q => q.left) h1⟩)
  refine ⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' hw' B _ t x hx => ?_⟩
  obtain ⟨z, hz⟩ := (hrep _ _).1 (GlobalTheory.KTrivSpread.memKL_push h' hL hL' hw' t x hx)
  obtain ⟨y, hy⟩ := key R' g hg _ z.left t (Over.w z)
  let u : Over.mk (t ≫ spMap g) ⟶ 𝟙_ (Over (Sp R)) := Over.homMk y (by
    have := Over.w z
    rw [← hy, Category.assoc, hsec] at this
    exact this)
  have hu : u ≫ e = z := Over.OverMorphism.ext hy
  have h1 : pushPt h'.1.w x = pushPt h'.1.w (1 : Over.mk t ⟶ G') := by
    refine Eq.trans ?_ (map_one (pushHom h' (Over.mk t))).symm
    rw [← hz, ← hu, Category.assoc, he, MonObj.comp_one]
  exact Over.OverMorphism.ext (h'.1.hom_ext (congrArg (fun q => q.left) h1) (by rw [Over.w, Over.w]))

end GlobalTheory.GenSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsKernelPolarisationTrivialSpreadLocalisatioStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernelPolarisation_trivial_spread_localisation : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → GlobalTheory.AbLaw.IsProjBy G.hom → KTriv A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → KTriv G' L' := by
  first | exact @GlobalTheory.GenSpread.exists_kTriv | exact GlobalTheory.GenSpread.exists_kTriv | (intros; apply GlobalTheory.GenSpread.exists_kTriv <;> assumption)
end
end
