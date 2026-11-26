module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThickIsoOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralSectionsCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfPullbackId
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnfGroupContainsCongruenceUptoRootsOfUnity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AmpleCubPullAndPullPow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.AmpSub

def chartPullPw {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (t : ℤ) :
    ChartPull (AbLaw.pw (L.pull f) t) (AbLaw.pw L t) f where
  idx J := J PUnit.unit
  le _ _ hy := mem_pull.1 hy
  g y J J' hJ hJ' := (map_zpow _ _ _).trans
    ((congrArg (· ^ t) ((Geo.Tor.chartPullPull L f f rfl).g y J J' hJ hJ')).trans (map_zpow _ _ _).symm)

theorem hasGen_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι)
    (h : ∀ y, f y ∈ L.U i) : MulPull.HasGen L (K := PUnit) (fun _ => f) (fun _ => 1) := by
  have le : ∀ J : PUnit → L.ι, (L.pull f).U J ≤ f ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, h y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (L.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans (gm_rp₁ f y _ _ (le J) hy.1 _)).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) (gm_pull_g L f (𝟙 Y) y J J' hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_rp₁ f y _ _ (le J') hy.2 _))).trans ?_)))
  rw [Category.id_comp]
  exact gm_cocycle hL f y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (h y)

theorem exists_chart_local {X S : Scheme.{0}} {L : LB X} (hL : L.IsLB) [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (f : S ⟶ X) : ∃ i, ∀ y, f y ∈ L.U i := by
  obtain ⟨i, hi⟩ := exists_chart hL ((S.isoSpec.inv ≫ f) (IsLocalRing.closedPoint Γ(S, ⊤)))
  have e : (S.isoSpec.inv ≫ f) ⁻¹ᵁ L.U i = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 hi
  refine ⟨i, fun y => ?_⟩
  have : S.isoSpec.hom y ∈ (S.isoSpec.inv ≫ f) ⁻¹ᵁ L.U i := by rw [e]; trivial
  have h2 : (S.isoSpec.hom ≫ S.isoSpec.inv ≫ f) y ∈ L.U i := this
  rwa [Iso.hom_inv_id_assoc] at h2

theorem psum_comp {S : Scheme.{0}} {N G : Over S} [GrpObj N] [GrpObj G] (ν : N ⟶ G) [IsMonHom ν]
    {T' T : Over S} {n : ℕ} (x : Fin n → (T' ⟶ N)) (y : Fin n → (T ⟶ G)) (h : T' ⟶ T)
    (e : ∀ k, x k ≫ ν = h ≫ y k) (I : Finset (Fin n)) : psum N x I ≫ ν = h ≫ psum G y I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact (MonObj.one_comp ν).trans (MonObj.comp_one h).symm
  | cons k l ih =>
    exact (MonObj.mul_comp _ _ ν).trans ((congrArg₂ (· * ·) (e k) ih).trans (MonObj.comp_mul h _ _).symm)

theorem ampleCub_pull_and_pullPow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), AmpleCub G L → (∀ (N : Over S) [GrpObj N] (ν : N ⟶ G), IsMonHom ν → IsClosedImmersion ν.left → AmpleCub N (L.pull ν.left)) ∧ (IsLocalRing Γ(S, ⊤) → IsAffine S → ∀ n : ℕ, PullPow ((𝟙 G) ^ n).left L ((n : ℤ) ^ 2)) := by
  intro S G _ _ L ⟨hL, ⟨c, hc⟩, ⟨s, hs⟩, n, hn, ha⟩
  refine ⟨fun N _ ν hν hcl => ⟨pull_isLB hL _, ?_, ?_, n, hn, fun x => ?_⟩, fun _ _ m => ?_⟩
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
  · have hcube : MulPull.HasGen L (thφ G (x3 G)) thε := ⟨c, hc⟩
    have hsym : MulPull.HasGen L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] := ⟨s, hs⟩
    obtain ⟨i, hi⟩ := exists_chart_local (S := S) hL (eSec G)
    have hrig := hasGen_of_chart hL (eSec G) i hi
    have h := MulPull.hasGen_pow hL hcube (𝟙 G) ((hrig.pull (toUnit G).left).of_formEq hL (fun U _ h => by
        simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
          Matrix.cons_val_zero, _root_.mul_one]
        rfl))
      (hsym.inv.of_formEq hL (fun U _ h => by
        rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
        rfl)) m
    refine h.inv.of_formEq hL fun U _ h => ?_
    rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
    rfl

end GlobalTheory.SS.AmpSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZero
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

noncomputable section

namespace GlobalTheory.ZH.CoordMap

variable {X Y : Scheme.{0}}

def pullOn (B : LB X) (V : X.Opens) (g : Y ⟶ X) : LB Y where
  ι := B.ι
  U j := g ⁻¹ᵁ (V ⊓ B.U j)
  g j j' := Units.map (g.appLE (B.U j ⊓ B.U j') (g ⁻¹ᵁ (V ⊓ B.U j) ⊓ g ⁻¹ᵁ (V ⊓ B.U j'))
    (inf_le_inf (g.preimage_mono inf_le_right) (g.preimage_mono inf_le_right))).hom.toMonoidHom (B.g j j')

def pullSecOn {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j)) (h : σ ∈ secOn B V) :
    (pullOn B V g).Sec where
  f j := (g.appLE (V ⊓ B.U j) (g ⁻¹ᵁ (V ⊓ B.U j)) le_rfl).hom (σ j)
  compat j j' := by
    have hW : g ⁻¹ᵁ (V ⊓ B.U j) ⊓ g ⁻¹ᵁ (V ⊓ B.U j') ≤ g ⁻¹ᵁ (V ⊓ B.U j ⊓ B.U j') :=
      le_inf inf_le_left (inf_le_right.trans (g.preimage_mono inf_le_right))
    have e := congrArg (g.appLE _ _ hW).hom (h j j')
    rw [map_mul, ProjSpace.appLE_resG, ProjSpace.appLE_resG, ProjSpace.appLE_resG] at e
    exact (ProjSpace.resG_appLE g le_rfl inf_le_left _).trans (e.trans
      (congrArg (_ * ·) (ProjSpace.resG_appLE g le_rfl inf_le_right _).symm))

theorem resG_pullSecOn {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j)) (h : σ ∈ secOn B V)
    (j : B.ι) {T : Y.Opens} (hj : T ≤ g ⁻¹ᵁ (V ⊓ B.U j)) :
    resG Y (U := (pullOn B V g).U j) hj ((pullSecOn g σ h).f j) = (g.appLE _ T hj).hom (σ j) :=
  ProjSpace.resG_appLE g le_rfl hj _

theorem preimage_basicOpen_le {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j))
    (h : σ ∈ secOn B V) (j : B.ι) : g ⁻¹ᵁ X.basicOpen (σ j) ≤ nonzeroLocus (pullSecOn g σ h) := by
  refine le_trans ?_ (le_iSup (fun k => Y.basicOpen ((pullSecOn g σ h).f k)) j)
  refine le_trans ?_ (Scheme.basicOpen_appLE g (g ⁻¹ᵁ (V ⊓ B.U j)) _ le_rfl (σ j)).ge
  exact le_inf (g.preimage_mono (X.basicOpen_le _)) le_rfl

theorem exists_coordMap : ∀ (o : Type) [CommRing o] (X Z : Scheme.{0}) (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) (J : Type) (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) (m : ℕ) (e : Fin (m + 1) ≃ J), (∀ i, σ i ∈ secOn B V) → (∀ x ∈ V, ∃ i j, x ∈ X.basicOpen (σ i j)) → ∃ π : V.toScheme ⟶ PSpace o m, π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s ∧ (∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i) (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ V.toScheme) (j : B.ι), ⊤ ≤ (x ≫ V.ι) ⁻¹ᵁ B.U j → Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (x ≫ π) (fun k => valF (x ≫ V.ι) (V ⊓ B.U j) (σ (e k) j)) := by
  intro o _ X Z f s B V J σ m e hσ hne
  let t : Fin (m + 1) → (pullOn B V V.ι).Sec := fun k => pullSecOn V.ι (σ (e k)) (hσ _)
  have ht : ⨆ i, nonzeroLocus (t i) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, j, hij⟩ := hne (V.ι y) y.2
    obtain ⟨k, rfl⟩ := e.surjective i
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, preimage_basicOpen_le V.ι _ (hσ _) j hij⟩
  have key : ∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens)
      (hi : T ≤ ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht ⁻¹ᵁ ProjSpace.chart o m i)
      (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧
        ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) =
          ProjSpace.pullRatio _ T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j) := by
    intro i j T hi hj
    refine ⟨?_, fun k => ?_⟩
    · rw [← resG_pullSecOn V.ι _ (hσ _) j hj]
      exact ProjSpace.isUnit_resG_sec (t i) j (hi.trans (ProjSpace.toProj_preimage_chart _ t ht i).le) hj
    · rw [← resG_pullSecOn V.ι _ (hσ _) j hj, ← resG_pullSecOn V.ι _ (hσ _) j hj]
      exact ProjSpace.sec_eq_pullRatio_toProj_mul _ t ht i k j hi hj
  refine ⟨ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht, ProjSpace.toProj_str _ t ht, key, ?_⟩
  generalize ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht = π at key
  intro K _ x j hx
  obtain ⟨i, hi⟩ := Points.exists_le_preimage_of_iSup_eq_top (x ≫ π) (ProjSpace.iSup_chart o m)
  have hT : ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ ProjSpace.chart o m i ⊓ V.ι ⁻¹ᵁ (V ⊓ B.U j)) :=
    fun z hz => ⟨hi hz, (x z).2, hx hz⟩
  obtain ⟨hu, hk⟩ := key i j _ inf_le_left inf_le_right
  have hu' := hu.map (Points.valMap x _ hT).hom
  rw [← Points.valR_eq] at hu'
  refine ⟨i, hu'.unit, hi, fun k => ?_⟩
  have := congrArg (valR x _) (hk k)
  rw [Points.valR_mul x _ hT, Points.valR_appLE x _ _ hT, ProjSpace.pullRatio, Points.valR_appLE x _ _ hT] at this
  exact this.trans (mul_comm _ _)

end GlobalTheory.ZH.CoordMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZeroStatement
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projSpace_map_of_local_sections_no_common_zero : ∀ (o : Type) [CommRing o] (X Z : Scheme.{0}) (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) (J : Type) (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) (m : ℕ) (e : Fin (m + 1) ≃ J), (∀ i, σ i ∈ secOn B V) → (∀ x ∈ V, ∃ i j, x ∈ X.basicOpen (σ i j)) → ∃ π : V.toScheme ⟶ PSpace o m, π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s ∧ (∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i) (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ V.toScheme) (j : B.ι), ⊤ ≤ (x ≫ V.ι) ⁻¹ᵁ B.U j → Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (x ≫ π) (fun k => valF (x ≫ V.ι) (V ⊓ B.U j) (σ (e k) j)) := by
  first | exact @GlobalTheory.ZH.CoordMap.exists_coordMap | exact GlobalTheory.ZH.CoordMap.exists_coordMap | (intros; apply GlobalTheory.ZH.CoordMap.exists_coordMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LbIsoLinCombPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.SymExtend

theorem lbIso_linComb_pull {X X' Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) :
    LBIso (LB.LinComb (L.pull F) φ' ε) ((LB.LinComb L φ ε).pull h) :=
  have r : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ ε) := (GlobalTheory.PrimNorm.lbIso_iff hL φ ε φ ε).2 rfl
  LBIso.chartPull (chartPullLinComb L F φ' φ ε h hc) (Geo.Tor.chartPullPull _ h h rfl) r

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem lbIso_cube_zero (PP : RigLB G) {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (z : 𝟙_ (Over S) ⟶ T)
    (hz : ∀ i, z ≫ x i = 1) : LBIso ((cubeLB G x PP.L).pull z.left) (PP.L.pull (eSec G)) := by
  have h1 : GlobalTheory.PrimNorm.cls PP.L (eSec G) = 1 := by
    have := (GlobalTheory.PrimNorm.hasGen_iff PP.isLB (K := PUnit) (fun _ => eSec G) (fun _ => 1)).1 ⟨PP.rig, PP.rigGen⟩
    simpa using this
  have h2 : ∀ I : Finset (Fin n), z.left ≫ (psum G x I).left = eSec G := fun I => by
    have e : z ≫ psum G x I = psum G (fun i => z ≫ x i) I := psum_hom (preHom z) x I
    have e' : psum G (fun i => z ≫ x i) I = 1 := by
      have := psum_hom (1 : (T ⟶ G) →* (𝟙_ (Over S) ⟶ G)) x I
      rw [funext hz]
      exact this.symm
    rw [← Over.comp_left, e, e', ← MonObj.one_eq_one]
    rfl
  exact GlobalTheory.PrimNorm.lbIso_nested PP.isLB _ _ _ _ _ _ (by
    simp only [h2, h1, one_zpow, Finset.prod_const_one])

variable {U : Scheme.{0}} {A : Over U} [GrpObj A] [IsCommMonObj A] {j : U ⟶ S} {a : A.left ⟶ G.left}

omit [IsCommMonObj G] [IsCommMonObj A] in
theorem isPullback_square (h : IsGrpPullback A G j a) :
    IsPullback (lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))).left (A ⊗ A).hom (G ⊗ G).hom j := by
  let l := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have l₁ : l.left ≫ pullback.fst G.hom G.hom = pullback.fst A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have l₂ : l.left ≫ pullback.snd G.hom G.hom = pullback.snd A.hom A.hom ≫ a :=
    congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A)))
  have big : IsPullback (pullback.snd A.hom A.hom ≫ a) (pullback.fst A.hom A.hom) G.hom (A.hom ≫ j) :=
    (IsPullback.of_hasPullback A.hom A.hom).flip.paste_horiz h.1
  have h₁ : IsPullback l.left (pullback.fst A.hom A.hom) (pullback.fst G.hom G.hom) a := by
    refine IsPullback.of_right (h₁₂ := pullback.snd G.hom G.hom) (v₁₃ := G.hom) (h₂₂ := G.hom) ?_
      l₁ (IsPullback.of_hasPullback G.hom G.hom).flip
    rw [l₂, h.1.w]
    exact big
  exact h₁.paste_vert h.1

theorem hypS_extend [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S) [Nonempty U] [IsOpenImmersion j]
    [Smooth G.hom] [GeometricallyConnected G.hom] (h : IsGrpPullback A G j a)
    (ext : ∀ α : A ⟶ A, IsMonHom α → ∃! F : G ⟶ G, IsMonHom F ∧ a ≫ F.left = α.left ≫ a)
    (LA : LB A.left) (PP : RigLB G) (hLA : LA.IsLB) (hb : LBIso (PP.L.pull a) LA) (H : GlobalTheory.ZH.HypS A LA) :
    GlobalTheory.ZH.HypS G PP.L := by
  obtain ⟨w', wd', hw', hwd', hs, hp, ha⟩ := H
  obtain ⟨w, ⟨hw, ew⟩, -⟩ := ext w' hw'
  obtain ⟨wd, ⟨hwd, ewd⟩, -⟩ := ext wd' hwd'
  have hL := PP.isLB
  have hB : (PP.L.pull a).IsLB := pull_isLB hL a
  have push : ∀ {u' : A ⟶ A} {u : G ⟶ G}, a ≫ u.left = u'.left ≫ a → ∀ {T : Over U} (x : T ⟶ A),
      pushPt h.1.w (x ≫ u') = pushPt h.1.w x ≫ u := fun e _ x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ← e, Category.assoc])
  have pa := @push _ _ ew
  have pd := @push _ _ ewd
  have cube : ∀ {T : Over S} {T' : Over U} (x : Fin 2 → (T ⟶ G)) (x' : Fin 2 → (T' ⟶ A))
      (V : Over.mk (T'.hom ≫ j) ⟶ T), (∀ i, pushPt h.1.w (x' i) = V ≫ x i) →
      LBIso (cubeLB A x' LA) ((cubeLB G x PP.L).pull V.left) := fun x x' V hx =>
    LBIso.trans (DVR.linComb_isLB _ hLA _ _) (DVR.linComb_isLB _ hB _ _)
      (pull_isLB (DVR.linComb_isLB _ hL _ _) _) (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _)
      (lbIso_linComb_pull hL a _ _ _ V.left fun I => psum_push h _ _ V hx I.down)
  have cl : ∀ {T : Over S} (x : Fin 2 → (T ⟶ G)), (cubeLB G x PP.L).IsLB := fun x => DVR.linComb_isLB _ hL _ _
  have cl' : ∀ {T : Over U} (x : Fin 2 → (T ⟶ A)), (cubeLB A x LA).IsLB := fun x => DVR.linComb_isLB _ hLA _ _
  have w1 : (1 : 𝟙_ (Over S) ⟶ G) ≫ w = 1 := MonObj.one_comp w
  have wd1 : (1 : 𝟙_ (Over S) ⟶ G) ≫ wd = 1 := MonObj.one_comp wd
  refine ⟨w, wd, hw, hwd, ?_, ?_, ?_⟩
  · obtain ⟨F, -, hF⟩ := ext (𝟙 A) inferInstance
    refine (hF _ ⟨GlobalTheory.Serre.isMonHom_mul w wd, ?_⟩).trans (hF _ ⟨inferInstance, by simp⟩).symm
    have b : pushPt h.1.w (w' * wd') = pushPt h.1.w w' * pushPt h.1.w wd' := map_mul (pushHom h A) _ _
    have c := pa (𝟙 A)
    have d := pd (𝟙 A)
    rw [Category.id_comp] at c d
    rw [c, d, ← MonObj.comp_mul, hs] at b
    have e : 𝟙 A.left ≫ a = (𝟙 A.left ≫ a) ≫ (w * wd).left := congrArg (fun z => z.left) b
    simp only [Category.id_comp] at e
    simpa using e.symm
  · let V := pushPt h.1.w (𝟙 A)
    have hV : V.left = a := Category.id_comp _
    have c := cube ![𝟙 G, w] ![𝟙 A, w'] V (fun i => by
      fin_cases i
      · simp [V]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _))
    rw [hV] at c
    refine (GlobalTheory.T.lineBundleIso_extend_of_normal_base S hS U G.left A.left j G.hom (eSec G) a A.hom inferInstance
      (GlobalTheory.geometricallyIntegral_of_smooth _) (Over.w η[G]) h.1 _ _ hL (cl _)
      (hb.trans hB hLA (pull_isLB (cl _) _) (hp.trans hLA (cl' _) (pull_isLB (cl _) _) c))).1 ?_
    refine (lbIso_cube_zero PP ![𝟙 G, w] η[G] fun i => ?_).symm
    rw [MonObj.one_eq_one]
    fin_cases i
    · simp
    · exact w1
  · let V := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
    have c₁ := cube ![fst G G ≫ w, snd G G] ![fst A A ≫ w', snd A A] V (fun i => by
      fin_cases i
      · exact (pa _).trans (by simp [V])
      · simp [V])
    have c₂ := cube ![fst G G, snd G G ≫ wd] ![fst A A, snd A A ≫ wd'] V (fun i => by
      fin_cases i
      · simp [V]
      · exact (pd _).trans (by simp [V]))
    let z : 𝟙_ (Over S) ⟶ G ⊗ G := lift 1 1
    refine (GlobalTheory.T.lineBundleIso_extend_of_normal_base S hS U (G ⊗ G).left (A ⊗ A).left j (G ⊗ G).hom z.left V.left (A ⊗ A).hom
      (GlobalTheory.smooth_tensorObj_hom G G) (GlobalTheory.geometricallyIntegral_tensorObj_hom G G) (Over.w z)
      (isPullback_square h) _ _ (cl _) (cl _)
      (c₁.symm.trans (pull_isLB (cl _) _) (cl' _) (pull_isLB (cl _) _)
        (ha.trans (cl' _) (cl' _) (pull_isLB (cl _) _) c₂))).1 ?_
    refine LBIso.trans (pull_isLB (cl _) _) (pull_isLB hL _) (pull_isLB (cl _) _)
      (lbIso_cube_zero PP _ z fun i => ?_) (lbIso_cube_zero PP _ z fun i => ?_).symm
    · fin_cases i
      · simpa [z] using w1
      · simp [z]
    · fin_cases i
      · simp [z]
      · simpa [z] using wd1

end GlobalTheory.SymExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G')
  (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G)

def LevelIso : Prop :=
  ∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧
    (U'.gt e).pG.left ≫ prA hD = (j e).hom.left ≫ (U.gt e).pG.left ∧
    ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ prA hD =
        (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧
      PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x)
        ((U.gt e).t (hD.xe x)) (j e).hom.left

def AgreeAll (k : ℕ) (σ : H0 U.LG.L k) (σ' : H0 U'.LG.L k) : Prop :=
  ∀ e : ℕ, Agree U U' hD e k (j e).hom.left σ σ'

def Enough : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∀ σ₀ : H0 U.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧
      (∀ i, σ.f i = resTop _ (scal G.hom c) * σ₀.f i) ∧ AgreeAll U U' hD j k σ σ') ∧
    ∀ σ₀ : H0 U'.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧
      (∀ i, σ'.f i = resTop _ (scal G'.hom c) * σ₀.f i) ∧ AgreeAll U U' hD j k σ σ'

def GenericRel (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G)
    (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R)))
      (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))) : Prop :=
  w.IsGen ∧ ∀ k : ℕ, 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), AgreeAll U U' hD j k σ σ' →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL →
      (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' →
      gs (r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL))
          (σ.f (fun _ => jL)) =
        (Geo.Tor.gw w r z jL (fun _ => jL') ^ k).val *
          gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL'))
            (σ'.f (fun _ => jL'))

open ThickIso TorusCoordPull in
theorem exists_levelIso (hG : GlobalFnsSt) : ∃ j, LevelIso U U' hD j := by
  choose j hm hj using fun e : ℕ => exists_iso hD (U.gt e) (U'.gt e) hG
  refine ⟨j, fun e => ?_⟩
  have h₀ := hj e _ (𝟙 _)
  have hp : (U'.gt e).pG.left ≫ abMap hD = (j e).hom.left ≫ (U.gt e).pG.left := by
    simpa only [Category.id_comp] using h₀.1
  have hO := Oφ_pull hD (U.gt e).pG (U'.gt e).pG (j e).hom.left hp
  refine ⟨hm e, (hj (e + 1) _ (thickMap R I e G')).unique_right ?_, hp, fun x => ⟨hO x,
    pmaps_of_good ((isGen_iff hD.w).1 hD.w_gen) D.toPre.P.isLB D'.toPre.P.isLB (hO x) ((U'.gt e).t_gen x)
      ((U.gt e).t_gen _) fun y J J' hJ hJ' => h₀.2 x y J J' hJ hJ'⟩⟩
  simpa only [Category.id_comp] using h₀.succ (U.gt_q e) (U.gt_t e) (U'.gt_q e) (U'.gt_t e)

variable {U U' hD j}

theorem LevelIso.agreeAll (hj : LevelIso U U' hD j) {k : ℕ} {σ : H0 U.LG.L k} {σ' : H0 U'.LG.L k}
    {f : ∀ α, D.toPre.SecB k α} {f' : ∀ α, D'.toPre.SecB k α} (hE : ∀ e, U.ExpandsAt e k σ f)
    (hE' : ∀ e, U'.ExpandsAt e k σ' f')
    (hf : ∀ x, IsSecPull hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (f' x)
      (f (hD.xe x))) : AgreeAll U U' hD j k σ σ' := fun e =>
  agree_of_expandsAt _ _ hD e k _ (hj e).2.2.1 (fun x => ((hj e).2.2.2 x).1) (fun x => ((hj e).2.2.2 x).2)
    (hE e) (hE' e) hf

theorem LevelIso.enough (hj : LevelIso U U' hD j) (hG : GlobalFnsSt) (hU : ∀ k, 1 ≤ k → U.ExpBij k)
    (hU' : ∀ k, 1 ≤ k → U'.ExpBij k) : Enough U U' hD j := by
  intro k hk
  constructor
  · intro σ₀
    obtain ⟨s, hs⟩ := exists_restrict U k σ₀
    obtain ⟨F, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (hU k hk).1 s
    obtain ⟨F', hF⟩ := exists_pull hD _ hG k F
    obtain ⟨s', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (hU' k hk).2 F'
    exact ⟨r' * r, _, _, mul_ne_zero hr' hr, scale_of_restrict _ hs h₁ r', hj.agreeAll
      (fun e => expandsAt_scale _ (h₃ e) _) (fun e => expandsAt_scale _ (h₃' e) _) (integral_rel hD _ hF h₂ h₂')⟩
  · intro σ₀
    obtain ⟨s', hs⟩ := exists_restrict U' k σ₀
    obtain ⟨F', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (hU' k hk).1 s'
    obtain ⟨F, hF⟩ := exists_push hD _ hG k F'
    obtain ⟨s, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (hU k hk).2 F
    exact ⟨r * r', _, _, mul_ne_zero hr hr', scale_of_restrict _ hs h₁' r, hj.agreeAll
      (fun e => expandsAt_scale _ (h₃ e) _) (fun e => expandsAt_scale _ (h₃' e) _) (integral_rel hD _ hF h₂ h₂')⟩

open LinearUnifIso in
theorem LevelIso.act_comm (hj : LevelIso U U' hD j) (hG : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O]
    [Module O D.toPre.X] [Module O D'.toPre.X] {o : D.OAct O} {o' : D'.OAct O} {oA : A.OAct O} {oA' : A'.OAct O}
    {oG : RingAct G O} {oG' : RingAct G' O} (lin : U.OLinear O o oA oG) (lin' : U'.OLinear O o' oA' oG')
    (hx : ∀ (x : O) y, hD.xe (x • y) = x • hD.xe y)
    (hB : ∀ x, o'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (o.onB.act x))
    (a : O) (e : ℕ) : (Over.pullback (thick R I e)).map (oG'.act a) ≫ (j e).hom =
      (j e).hom ≫ (Over.pullback (thick R I e)).map (oG.act a) := by
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  have P : ∀ {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of R)) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback t).map c).left ≫ pullback.fst Y.hom t =
        pullback.fst X.hom t ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : o'.onB.act a ≫ ψ = ψ ≫ o.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ, Category.assoc, ← P, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, hB])
  obtain ⟨hm, -, hp, ht⟩ := hj e
  have hq : (j e).hom ≫ (U.gt e).q = (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
      Category.assoc, Category.assoc, P, eψ]
    exact hp.symm.trans (Category.assoc _ _ _)
  obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
    (fun x => (ht x).2)
  obtain ⟨t, tc, ti⟩ := lin.i_lin e a
  obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
  have := oG.hom a
  have := oG'.hom a
  have hts : t' ≫ s = s ≫ t := by
    refine PowTorus.torus_ext _ _ fun χ z => ?_
    obtain ⟨x, rfl⟩ := hD.xe.surjective χ
    rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
      ← gm_torusEnd tc', Category.id_comp]
  refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
      ← Functor.map_comp, ← Functor.map_comp, hψa]
  · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]

end GlobalTheory.GenericIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoPullbackUniformisedThetaModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoPullbackUniformisedThetaModel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.TestBundle

open GlobalTheory.CechPic

theorem lbIso_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (P : Over (Spec (CommRingCat.of V))) [Smooth P.hom] [GeometricallyConnected P.hom]
    (e : Spec (CommRingCat.of V) ⟶ P.left) (he : e ≫ P.hom = 𝟙 _) {L M : LB P.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : CechPic.pull (pullback.fst P.hom (jK V)) (cls L hL) =
      CechPic.pull (pullback.fst P.hom (jK V)) (cls M hM)) : LBIso L M := by
  have hN := LB.isLB_div hM hL
  have h₁ : IsPreimmersion (jK V) := IsPreimmersion.of_isLocalization (nonZeroDivisors V)
  have h₂ : Flat (jK V) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors V))
  refine GenericExtend.exists_isGen_of_densePart _ _ (jK V) ((isNormalScheme_iff_pred _).1 inferInstance) h₁ h₂
    DVR.isDominant_jK inferInstance P e (LB.div M L) he ‹_› (geometricallyIntegral_of_smooth P.hom) hN
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hN _)) ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  rw [cls_pull hN, cls_div hM hL, map_sub, h, sub_self]

theorem lbIso_pull_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L := by
  intro o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK _ F ψ ⟨_, h₁, _, h₂⟩
  have := u.semi.smooth
  have := u.semi.geomConnected
  have hL := Q.L.isLB
  have hP := ρ.P.isLB
  have hA := u.A.isLB
  have hG := u.U.LG.isLB
  refine lbIso_of_generic u.G (eSec u.G) (Over.w η[u.G]) (pull_isLB hL F) hG ?_
  have a : CechPic.pull Q.φ (cls _ hL) = CechPic.pull (pullback.fst ρ.P.A.hom Q.u₀) (cls _ hP) :=
    (cls_eq_iff (pull_isLB hL _) (pull_isLB hP _)).2 ⟨Q.w, Q.w_gen⟩
  have b : cls _ hA = CechPic.pull u.φ (cls _ hP) := (cls_eq_iff hA (pull_isLB hP _)).2 u.lb
  have c : CechPic.pull u.U.gen.hom.left (cls _ hA) = CechPic.pull (pullback.fst u.G.hom (jK u.V)) (cls _ hG) :=
    (cls_eq_iff (pull_isLB hA _) (pull_isLB hG _)).2 u.U.ext
  refine Eq.trans ?_ c
  rw [cls_pull hL, ← pull_comp, ← h₂, pull_comp, a, ← pull_comp, h₁, b]
  exact pull_comp _ _ _

end GlobalTheory.ZH.TestBundle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoPullbackUniformisedThetaModelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pullback_uniformisedThetaModel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L := by
  first | exact @GlobalTheory.ZH.TestBundle.lbIso_pull_unif | exact GlobalTheory.ZH.TestBundle.lbIso_pull_unif | (intros; apply GlobalTheory.ZH.TestBundle.lbIso_pull_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyThetaExtensionTest
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyThetaExtensionTest
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.ThetaExt

open TopologicalSpace

noncomputable def invMul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) (c : Γ(X, ⊤)ˣ) : LB.Iso B A :=
  ⟨fun p => res (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) c *
    (res (fun _ hy => ⟨hy.2, hy.1⟩ : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹⟩

theorem gm_invMul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) (c : Γ(X, ⊤)ˣ) (y : X) (a : A.ι) (b : B.ι)
    (ha : y ∈ A.U a) (hb : y ∈ B.U b) : gm (𝟙 X) y (A.U a ⊓ B.U b) ((invMul w c).s (a, b)) =
      gm (𝟙 X) y ⊤ c * (gm (𝟙 X) y (B.U b ⊓ A.U a) (w.s (b, a)))⁻¹ :=
  have hp : (𝟙 X : X ⟶ X) y ∈ A.U a ⊓ B.U b := ⟨ha, hb⟩
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hp _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))))

theorem isGen_invMul {X : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (c : Γ(X, ⊤)ˣ) :
    (invMul w c).IsGen := by
  rintro ⟨a, b⟩ ⟨a', b'⟩
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a') := ⟨⟨hy.1.2, hy.1.1⟩, hy.2.2, hy.2.1⟩
  have e := congrArg (gm (𝟙 X) y (B.U b ⊓ A.U a ⊓ (B.U b' ⊓ A.U a'))) (hw (b, a) (b', a'))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (b, a) (b', a') hm) (gm_res _ y _ hm _))))
  have alg : ∀ {a b t s u : (X.presheaf.stalk y)ˣ}, u = b * a⁻¹ * s → t * u⁻¹ = a * b⁻¹ * (t * s⁻¹) := by
    rintro a b t s _ rfl
    rw [mul_inv, mul_inv, inv_inv, mul_comm a, mul_left_comm]
  exact ((gm_res _ y _ hy _).trans (gm_invMul w c y a b hy.1.1 hy.1.2)).trans ((alg e').trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y (a, b) (a', b') hy)
      ((gm_res _ y _ hy _).trans (gm_invMul w c y a' b' hy.2.1 hy.2.2)))).symm)

variable {C : Core} (T : C.Theta) {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)

theorem isClosed_closedPoint : IsClosed ({τ.y₀ (IsLocalRing.closedPoint τ.V)} : Set C.Z) := by
  have := τ.j_loc
  have h : spMap τ.j (cPt p) = IsLocalRing.closedPoint τ.V := IsLocalRing.comap_closedPoint τ.j
  have e : y (cPt p) = τ.y₀ (IsLocalRing.closedPoint τ.V) := by
    rw [← h]
    exact (congrArg (fun g => g (cPt p)) τ.fac).symm
  rw [← e]
  exact GlobalTheory.ZH.isClosed_singleton_cPt y

theorem exists_mem_basicOpen [IsIntegral τ.H.left] [Nonempty (pullback τ.H.hom (Out.jK τ.V) :)]
    [IsOpenImmersion (pullback.fst τ.H.hom (Out.jK τ.V))] (h : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) :
    ∃ (x : (pullback τ.H.hom (Out.jK τ.V) :)) (k : T.L.L.ι), τ.φ x ∈ C.A.left.basicOpen (T.θ.f k) := by
  obtain ⟨x₀, hx₀, e₀⟩ := T.s_ne _ (isClosed_closedPoint τ)
  obtain ⟨x₁, e₁, -⟩ := Scheme.exists_preimage_of_isPullback h x₀ _ e₀
  obtain ⟨_, hx₂, x₂, rfl⟩ := nonempty_preirreducible_inter (τ.f ⁻¹ᵁ Out.nonzeroLocus T.s).isOpen
    (pullback.fst τ.H.hom (Out.jK τ.V)).isOpenEmbedding.isOpen_range ⟨x₁, show τ.f x₁ ∈ _ by rw [e₁]; exact hx₀⟩
    (Set.range_nonempty _)
  have e₂ : C.a (τ.φ x₂) = τ.f (pullback.fst τ.H.hom (Out.jK τ.V) x₂) := congrArg (fun g => g x₂) τ.φ_f
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show C.a (τ.φ x₂) ∈ Out.nonzeroLocus T.s by rw [e₂]; exact hx₂)
  have hi' := C.G.toScheme.basicOpen_le _ hi
  obtain ⟨k, hk⟩ := exists_chart T.L.isLB ((mulN C.A T.m).left (τ.φ x₂))
  have u := (SecPullIso.isUnit_gs_iff C.a _ hi' _).2 hi
  rw [T.w_sec _ i k hi' hk] at u
  have u' := (SecPullIso.isUnit_gs_iff _ _ hk _).1 (isUnit_of_mul_isUnit_right u)
  obtain ⟨x₃, e₃, -⟩ := Scheme.exists_preimage_of_isPullback τ.φ_cart.1 ((mulN C.A T.m).left (τ.φ x₂))
    (((Over.pullback (Out.jK τ.V)).obj τ.H).hom x₂)
    ((congrArg (fun g => g (τ.φ x₂)) (Over.w (mulN C.A T.m))).trans (congrArg (fun g => g x₂) τ.φ_cart.1.w))
  exact ⟨x₃, k, by rw [← e₃] at u'; exact u'⟩

end GlobalTheory.ZJ.ThetaExt

namespace GlobalTheory.ZJ

open ThetaExt TopologicalSpace

theorem Core.Theta.nonempty_ext : Semi.extend_existsSt.{0} → ∀ (C : Core) (T : C.Theta) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.TestCart → Nonempty (T.Ext τ) := by
  intro hE C T p _ y τ hC
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ τ.H
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible τ.V
  have hK := IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V)
  have hs := IsPullback.of_hasPullback τ.H.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue τ.V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := DvrModel.isOpenImmersion_generic hK
  have := DvrModel.isIntegral hK
  have : IsCommMonObj ((Over.pullback (Out.jK τ.V)).obj τ.H) := Functor.isCommMonObj_obj
  obtain ⟨ρ, hρ⟩ := gen_chartPull (chartPullLinComb T.L.L τ.φ (K := PUnit)
    (fun _ => eSec ((Over.pullback (Out.jK τ.V)).obj τ.H)) (fun _ => eSec C.A) (fun _ => 1) τ.yK
    fun _ => (cubeMapOf τ.φ_cart).e_comm) T.L.rig T.L.rigGen
  obtain ⟨L, w₀, hw₀⟩ := hE τ.V (FractionRing τ.V) τ.H (eSec ((Over.pullback (Out.jK τ.V)).obj τ.H))
    (cubeMapOf (isGrpPullback_pullback τ.H (Out.jK τ.V))).e_comm (T.L.L.pull τ.φ) (pull_isLB T.L.isLB _) ρ hρ
  obtain ⟨r, hr⟩ := SecPullIso.exists_pull τ.φ T.L.L (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) w₀ T.L.isLB
    (pull_isLB L.isLB _) hw₀ T.θ
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ L.isLB r (by
    obtain ⟨x, k, hk⟩ := exists_mem_basicOpen T τ (hC p y τ)
    obtain ⟨a, ha⟩ := exists_chart (pull_isLB L.isLB (pullback.fst τ.H.hom (Out.jK τ.V))) x
    have hk' := C.A.left.basicOpen_le _ hk
    have u := (SecPullIso.isUnit_gs_iff τ.φ x hk' _).2 hk
    rw [hr x k a hk' ha] at u
    have u' := (SecPullIso.isUnit_gs_iff (𝟙 _) x ha _).1 (isUnit_of_mul_isUnit_right u)
    exact ⟨a, fun h => by rw [h, Scheme.basicOpen_zero] at u'; exact u'⟩)
  have h0 : algebraMap τ.V (FractionRing τ.V) ϖ ^ n ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective τ.V _)).2 hϖ.ne_zero)
  have hc := (h0.isUnit.map (Scheme.ΓSpecIso (.of (FractionRing τ.V))).inv.hom).map
    (pullback.snd τ.H.hom (Out.jK τ.V)).appTop.hom
  refine ⟨⟨L, invMul w₀ hc.unit, isGen_invMul hw₀ _, σ, fun x i k hi hk => ?_, x₀, Opens.mem_iSup.2 ⟨b, hb⟩, hx₀⟩⟩
  have hi' : x ∈ (L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))).U fun _ => i := mem_pull.2 hi
  have hk' : x ∈ (T.L.L.pull τ.φ).U fun _ => k := mem_pull.2 hk
  have e₁ := congrArg (gs (𝟙 _) x _) (hσ fun _ => i)
  have e₂ := (gs_appLE _ _ _ _ (𝟙 _) x hi' _).symm.trans (e₁.trans ((gs_mul (𝟙 _) x _ hi' _ _).trans
    (congrArg (· * _) ((gs_res (𝟙 _) x le_top hi' _).trans (gs_unit (𝟙 _) x ⊤ trivial hc.unit)))))
  rw [Category.id_comp] at e₂
  refine e₂.trans (Eq.symm ?_)
  refine (congrArg₂ (· * ·) ((gs_unit (𝟙 _) x _ (show _ ∈ _ ⊓ _ from ⟨hi', hk'⟩) _).trans
    (congrArg Units.val (gm_invMul w₀ hc.unit x _ _ hi' hk'))) (hr x k _ hk hi')).trans ?_
  rw [Units.val_mul, _root_.mul_assoc]
  exact congrArg (_ * ·) (Units.inv_mul_cancel_left _ _)

end GlobalTheory.ZJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyThetaExtensionTestStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.nonempty_thetaExtension_test : Semi.extend_existsSt.{0} → ∀ (C : Core) (T : C.Theta) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.TestCart → Nonempty (T.Ext τ) := by
  first | exact @GlobalTheory.ZJ.Core.Theta.nonempty_ext | exact GlobalTheory.ZJ.Core.Theta.nonempty_ext | (intros; apply GlobalTheory.ZJ.Core.Theta.nonempty_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuasiFiniteAtGenericPointOfIsDominant
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

private theorem isFinite_pullback_unit_of_surjective_on_points (k : Type) [Field k] [IsAlgClosed k]
    (G G' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ) (hG : _root_.GlobalTheory.SS.SmConn G)
    (hG' : _root_.GlobalTheory.SS.SmConn G') (hgG : SmoothOfRelativeDimension g G.hom)
    (hgG' : SmoothOfRelativeDimension g G'.hom) (i : G ⟶ G') [IsMonHom i]
    (hpts : ∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ i = y) :
    IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  unfold _root_.GlobalTheory.SS.SmConn at hG hG'
  obtain ⟨-, hsm, hsep, hqc, hgc⟩ := hG
  obtain ⟨-, hsm', hsep', hqc', hgc'⟩ := hG'
  have hw : i.left ≫ G'.hom = G.hom := Over.w i
  have : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  have : ConnectedSpace G'.left := GeometricallyConnected.connectedSpace_of_subsingleton G'.hom
  have : IsIntegral G.left := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G.hom
  have : IsIntegral G'.left := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G'.hom
  have : LocallyOfFiniteType (i.left ≫ G'.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType i.left := locallyOfFiniteType_of_comp i.left G'.hom
  have : JacobsonSpace G'.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G'.hom
  have hcl : closedPoints G'.left ⊆ Set.range i.left := by
    intro y hy
    obtain ⟨x, hx⟩ := hpts (Over.homMk (pointOfClosedPoint (K := k) G'.hom y hy)
      (pointOfClosedPoint_comp _ _ _))
    refine ⟨x.left (IsLocalRing.closedPoint k), ?_⟩
    have h := congrArg (fun φ : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G' => φ.left (IsLocalRing.closedPoint k)) hx
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    exact h.trans (pointOfClosedPoint_apply _ _ _ _)
  have hgen : i.left (genericPoint G.left) = genericPoint G'.left := by
    have hη : closure {genericPoint G.left} = Set.univ := genericPoint_spec G.left
    have h1 : closure (Set.range i.left) = Set.univ :=
      Set.eq_univ_of_univ_subset (closure_closedPoints (X := G'.left) ▸ closure_mono hcl)
    have h2 : Set.range i.left ⊆ closure {i.left (genericPoint G.left)} := by
      rintro _ ⟨x, rfl⟩
      exact map_mem_closure i.left.continuous (hη ▸ Set.mem_univ x) (by simp)
    have h3 : IsGenericPoint (i.left (genericPoint G.left)) Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← h1]
      simpa using closure_mono h2
    exact h3.eq (genericPoint_spec G'.left)
  have hq : i.left.QuasiFiniteAt (genericPoint G.left) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have hfib : ∀ a : i.left.fiber (i.left (genericPoint G.left)),
        i.left.fiberι _ a = genericPoint G.left := by
      intro a
      have ha : i.left.fiberι _ a ∈ i.left ⁻¹' {i.left (genericPoint G.left)} := by
        rw [← Scheme.Hom.range_fiberι]; exact Set.mem_range_self a
      refine _root_.GlobalTheory.OntoFinite.eq_genericPoint (K := k) G'.hom i.left g (by rw [hw]; exact hgG)
        hgG' _ ?_
      rw [← hgen]; exact ha
    have : Subsingleton (i.left.fiber (i.left (genericPoint G.left))) :=
      ⟨fun a b => (i.left.fiberι _).isEmbedding.injective ((hfib a).trans (hfib b).symm)⟩
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun b => Subsingleton.elim b _
  have : LocallyQuasiFinite i.left :=
    _root_.GlobalTheory.OntoFinite.locallyQuasiFinite_of_quasiFiniteAt (K := k) i _ hq
  have hpb : IsPullback (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left
      (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left i.left (η[G'] : 𝟙_ _ ⟶ G').left :=
    IsPullback.map (Over.forget _) (IsPullback.of_hasPullback _ _)
  have : LocallyQuasiFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left :=
    MorphismProperty.of_isPullback hpb ‹_›
  have hsec : (η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom = 𝟙 _ := Over.w _
  have : IsClosedImmersion ((η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom) := by rw [hsec]; infer_instance
  have : IsClosedImmersion (η[G'] : 𝟙_ _ ⟶ G').left := IsClosedImmersion.of_comp _ G'.hom
  have : IsClosedImmersion (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left :=
    MorphismProperty.of_isPullback hpb.flip ‹_›
  have hw2 : (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ 𝟙 _ =
      (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom := by
    exact (Over.w (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G'))).trans
      (Over.w (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G'))).symm
  have : QuasiCompact (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
    have h2 : QuasiCompact ((pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom) := inferInstance
    rw [← hw2, Category.comp_id] at h2
    exact h2
  have : IsLocallyArtinian (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left :=
    inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of k)))
  exact IsFinite.of_locallyQuasiFinite _

theorem _root_.GlobalTheory.SS.finite_ker_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G], _root_.GlobalTheory.SS.SmConn G → ∀ f : G ⟶ G, IsMonHom f →
    (∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ f = y) →
    Finite {x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G) // x ≫ f = 1} := by
  intro k _ _ G _ hG f _ hpts
  have hG0 := hG
  unfold _root_.GlobalTheory.SS.SmConn at hG0
  obtain ⟨-, hsm, -, -, hgc⟩ := hG0
  have : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  obtain ⟨g, hg⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected G.hom ((η[G] : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k))
  have hK := isFinite_pullback_unit_of_surjective_on_points k G G g hG hG hg hg f hpts
  have hKhom : (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom = (pullback.snd f (η[G] : 𝟙_ _ ⟶ G)).left := by
    rw [← Over.w (pullback.snd f (η[G] : 𝟙_ _ ⟶ G))]; rfl
  have : IsFinite (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom := hKhom ▸ hK
  have hfin : Finite (pullback f (η[G] : 𝟙_ _ ⟶ G)).left := by
    have h := (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom.finite_preimage_singleton
      (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))
    exact Set.finite_univ_iff.mp
      (h.subset fun p _ => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))
  have hone : ∀ x : {x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G) // x ≫ f = 1},
      x.1 ≫ f = 𝟙 _ ≫ (η[G] : 𝟙_ _ ⟶ G) := fun x => by
    rw [x.2, Category.id_comp]; rfl
  refine Finite.of_injective (fun x => (pullback.lift x.1 (𝟙 _) (hone x)).left
    (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))) ?_
  intro x y hxy
  have : LocallyOfFiniteType (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))))
  have : Subsingleton (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : IsReduced (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have hl : (pullback.lift x.1 (𝟙 _) (hone x)).left = (pullback.lift y.1 (𝟙 _) (hone y)).left := by
    have : LocallyOfFiniteType ((pullback.lift x.1 (𝟙 _) (hone x)).left ≫
        (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom) := by rw [Over.w]; infer_instance
    refine ext_of_apply_eq (K := k) (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom Set.univ
      isClosed_univ.isLocallyClosed dense_univ (fun p _ _ => ?_) ((Over.w _).trans (Over.w _).symm)
    obtain rfl := Subsingleton.elim p (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))
    exact hxy
  have hl' : pullback.lift x.1 (𝟙 _) (hone x) = pullback.lift y.1 (𝟙 _) (hone y) := Over.OverMorphism.ext hl
  apply Subtype.ext
  have := congrArg (· ≫ pullback.fst f (η[G] : 𝟙_ _ ⟶ G)) hl'
  rw [pullback.lift_fst, pullback.lift_fst] at this
  exact this

end GlobalTheory.SS
end
