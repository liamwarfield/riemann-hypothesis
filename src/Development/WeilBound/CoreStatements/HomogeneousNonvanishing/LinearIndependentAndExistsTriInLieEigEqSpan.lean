module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLieModelLift
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLieModelLift
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonObj

theorem exists_val_of_isTan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (v : epsOver T.V T.V ⟶ G.G), IsTan v → ∃ w : EC, (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  intro E _ _ _ H X tX T zV G Ψ hΨ EC _ _ MC v hv
  have hbase : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (epsOver T.V T.V).hom =
      Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [LieTangent.spec_comp, LieTangent.spec_comp]
    congr 2
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hover : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ) ≫ tX.G.hom =
      (epsAt (FinRd.Roots.gen T zV)).hom := by
    have hw : v.left ≫ G.G.hom = (epsOver T.V T.V).hom := Over.w v
    rw [Category.assoc, Category.assoc, hΨ.1.w, ← Category.assoc v.left, hw, ← Category.assoc, hbase,
      Category.assoc]
    rfl
  let vt : epsAt (FinRd.Roots.gen T zV) ⟶ tX.G := Over.homMk _ hover
  have ht : GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G (FinRd.Roots.gen T zV) vt := by
    have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
        (1 : ptOver T.V T.V ⟶ G.G).left := hv
    have h1 := FrameValue.one_left_grp hΨ (Spec.map (CommRingCat.ofHom (algebraMap T.V T.V))) _ rfl
    have hp : Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.V T.V)) ≫ zV = FinRd.Roots.gen T zV := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    have h2 := FrameValue.one_left_pull (G := tX.G) (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) _ _ hp
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.Fr T.Fr T.Fr).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ = _
    rw [← Category.assoc, LieTangent.spec_fst_dual, Category.assoc, ← Category.assoc _ v.left Ψ, hv']
    exact (congrArg (fun u => Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ u) h1).trans h2
  obtain ⟨w, hw⟩ := MC.onto vt ht
  exact ⟨w, congrArg (fun u => u.left) hw⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLieModelLiftStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_lie_model_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (v : epsOver T.V T.V ⟶ G.G), IsTan v → ∃ w : EC, (MC.pt w).left = Spec.map (CommRingCat.ofHom (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_val_of_isTan | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_val_of_isTan | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_val_of_isTan <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLieModelCompleteDvr
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLieModelCompleteDvr
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan

open MonObj
open GlobalTheory.CompanionTheory.Ar.LieTangent (epsBase epsScale isTanAt_iff isTanAt_scale spec_dual_eps spec_eps_alg)

section Push

variable (T : CDVR) {X : Scheme.{0}} (zV : Spec (CommRingCat.of T.V) ⟶ X) {A : CategoryTheory.Over X} [GrpObj A]
  {B : CategoryTheory.Over (Spec (CommRingCat.of T.V))} [GrpObj B] {Ψ : B.left ⟶ A.left}

theorem epsOver_hom :
    (epsOver T.V T.V).hom = Spec.map (CommRingCat.ofHom (algebraMap T.V (DualNumber T.V))) :=
  rfl

def idU : epsAt zV ⟶ CategoryTheory.Over.mk ((epsOver T.V T.V).hom ≫ zV) :=
  CategoryTheory.Over.homMk (𝟙 _) (by rw [Category.id_comp]; rfl)

def pushAt (h : IsGrpPullback B A zV Ψ) : (epsOver T.V T.V ⟶ B) →* (epsAt zV ⟶ A) :=
  (Formalism.L2.Pj.preHom (idU T zV)).comp (pushHom h (epsOver T.V T.V))

def pushGen (h : IsGrpPullback B A zV Ψ) : (epsOver T.V T.V ⟶ B) →* (epsAt (gen T zV) ⟶ A) :=
  (Formalism.L2.Pj.preHom (epsBase (algebraMap T.V T.Fr) rfl)).comp (pushAt T zV h)

variable {T zV}

theorem pushAt_left (h : IsGrpPullback B A zV Ψ) (v : epsOver T.V T.V ⟶ B) :
    (pushAt T zV h v).left = v.left ≫ Ψ := by
  simp [pushAt, Formalism.L2.Pj.preHom, pushHom, pushPt, idU]

theorem pushGen_left (h : IsGrpPullback B A zV Ψ) (v : epsOver T.V T.V ⟶ B) :
    (pushGen T zV h v).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  simp [pushGen, Formalism.L2.Pj.preHom, pushAt_left, GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase]
private theorem key_lemma' {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {Y : Scheme.{0}} (zV : Y ⟶ X)
    {f : Y ⟶ X} (hf : f = zV) :
    (1 : CategoryTheory.Over.mk f ⟶ A).left = (1 : CategoryTheory.Over.mk zV ⟶ A).left := by
  subst hf
  rfl

private theorem one_left_comp_of_isGrpPullback_over {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {Tb : CDVR}
    {zV : Spec (CommRingCat.of Tb.V) ⟶ X} {B : CategoryTheory.Over (Spec (CommRingCat.of Tb.V))} [GrpObj B]
    {Ψ : B.left ⟶ A.left} (h : IsGrpPullback B A zV Ψ) (T' : CategoryTheory.Over (Spec (CommRingCat.of Tb.V))) :
    (1 : T' ⟶ B).left ≫ Ψ = (1 : CategoryTheory.Over.mk (T'.hom ≫ zV) ⟶ A).left := by
  have := congrArg CategoryTheory.Over.Hom.left (map_one (pushHom h T'))
  simpa [pushHom, pushPt] using this

theorem one_left (h : IsGrpPullback B A zV Ψ) :
    (1 : ptOver T.V T.V ⟶ B).left ≫ Ψ = (1 : CategoryTheory.Over.mk zV ⟶ A).left := by
  have hf : (ptOver T.V T.V).hom ≫ zV = zV := by
    simp [ptOver, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
  rw [← key_lemma' zV hf]
  exact one_left_comp_of_isGrpPullback_over h (ptOver T.V T.V)

theorem isTanAt_push (h : IsGrpPullback B A zV Ψ) {v : epsOver T.V T.V ⟶ B} (hv : IsTan v) :
    IsTanAt A zV (pushAt T zV h v) := by
  have e : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
      (1 : ptOver T.V T.V ⟶ B).left := hv
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ (pushAt T zV h v).left =
    (1 : CategoryTheory.Over.mk zV ⟶ A).left
  rw [pushAt_left, ← Category.assoc, e]
  exact one_left h

theorem isTan_of_push (h : IsGrpPullback B A zV Ψ) {v : epsOver T.V T.V ⟶ B}
    (hv : IsTanAt A zV (pushAt T zV h v)) : IsTan v := by
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
    (1 : ptOver T.V T.V ⟶ B).left
  have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ (pushAt T zV h v).left =
      (1 : CategoryTheory.Over.mk zV ⟶ A).left := hv
  rw [pushAt_left, ← Category.assoc, ← one_left h] at hv'
  refine h.1.hom_ext hv' ?_
  rw [Category.assoc, CategoryTheory.Over.w v, CategoryTheory.Over.w (1 : ptOver T.V T.V ⟶ B), epsOver_hom,
    GlobalTheory.CompanionTheory.Ar.LieTangent.spec_comp]
  simp [ptOver, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]

theorem pushAt_surj (h : IsGrpPullback B A zV Ψ) (v : epsAt zV ⟶ A) :
    ∃ v' : epsOver T.V T.V ⟶ B, pushAt T zV h v' = v := by
  have hw : v.left ≫ A.hom = (epsOver T.V T.V).hom ≫ zV := by
    rw [CategoryTheory.Over.w v, epsOver_hom]
    rfl
  refine ⟨CategoryTheory.Over.homMk (h.1.lift v.left (epsOver T.V T.V).hom hw) (h.1.lift_snd _ _ _), ?_⟩
  apply CategoryTheory.Over.OverMorphism.ext
  rw [pushAt_left]
  exact h.1.lift_fst _ _ _

end Push

section Model

variable {X : Scheme.{0}} {A : CategoryTheory.Over X} [GrpObj A] {R : Type} [CommRing R]
  {x : Spec (CommRingCat.of R) ⟶ X} {EC : Type} [AddCommGroup EC] [Module R EC]

theorem pt_list_sum (MC : LieModel A x EC) (l : List EC) : MC.pt l.sum = (l.map MC.pt).prod := by
  induction l with
  | nil =>
    simp only [List.sum_nil, List.map_nil, List.prod_nil]
    exact MC.pt_zero
  | cons a l ih => rw [List.sum_cons, MC.add, ih, List.map_cons, List.prod_cons]

theorem pt_sum (MC : LieModel A x EC) {r : ℕ} (f : Fin r → EC) :
    MC.pt (∑ i, f i) = (List.ofFn fun i => MC.pt (f i)).prod := by
  rw [← List.sum_ofFn, pt_list_sum, List.map_ofFn]
  rfl

theorem mem_eigSp_iff {O : Type} [CommRing O] (ρ : O →+* Module.End R EC) (σ : O →+* R) (w : EC) :
    w ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ σ ↔ ∀ a, ρ a w = σ a • w := by
  simp only [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

end Model

section Main

variable (T : CDVR) {X : Scheme.{0}} (zV : Spec (CommRingCat.of T.V) ⟶ X) {A : CategoryTheory.Over X} [GrpObj A]
  {B : CategoryTheory.Over (Spec (CommRingCat.of T.V))} [GrpObj B] {Ψ : B.left ⟶ A.left}

theorem eigen_span_lie_basis (h : IsGrpPullback B A zV Ψ) {O : Type} [CommRing O] (aA : O → (A ⟶ A))
    (hA : ∀ a, IsMonHom (aA a)) (aB : O → (B ⟶ B)) (hc : ∀ a, (aB a).left ≫ Ψ = Ψ ≫ (aA a).left)
    {EC : Type} [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC]
    (MC : LieModel A (FinRd.Roots.gen T zV) EC) (ρC : O →+* Module.End T.Fr EC) (hρ : MC.IsActOf aA ρC)
    (σ : O →+* T.V) {r : ℕ} (ub : Fin r → (epsOver T.V T.V ⟶ B)) (hut : ∀ i, IsTan (ub i))
    (hue : ∀ i a, (ub i ≫ aB a).left =
      Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ (ub i).left)
    (hub : ∀ w : epsOver T.V T.V ⟶ B, IsTan w →
      (∀ a, (w ≫ aB a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ w.left) →
      ∃ cf : Fin r → T.V, IsComb ub cf w)
    (yb : Fin r → EC)
    (hyb : ∀ i, (MC.pt (yb i)).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (ub i).left ≫ Ψ)
    (L : Submodule T.V EC)
    (hL : ∀ w, w ∈ L ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zV ⟶ A, GlobalTheory.CompanionTheory.Ar.IsTanAt A zV v ∧
      (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left) :
    L ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V =
      Submodule.span T.V (Set.range yb) := by
  have hue' : ∀ i a, (ub i ≫ aB a).left =
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (σ a))) ≫ (ub i).left := hue
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V (FractionRing T.V)
  apply le_antisymm
  · rintro w ⟨hwL, hwE⟩
    obtain ⟨v, hvt, hvl⟩ := (hL w).1 hwL
    obtain ⟨v', rfl⟩ := pushAt_surj h v
    have hv't := isTan_of_push h hvt
    have hwE' : ∀ a, ρC a w = ((algebraMap T.V T.Fr).comp σ) a • w := (mem_eigSp_iff _ _ _).1 hwE
    have hpw : MC.pt w = pushGen T zV h v' := by
      apply CategoryTheory.Over.OverMorphism.ext
      rw [pushGen_left, hvl, pushAt_left]
    have hv'e : ∀ a, (v' ≫ aB a).left =
        Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ v'.left := by
      intro a
      have hp := isTanAt_push h hv't
      have ht1 : GlobalTheory.CompanionTheory.Ar.IsTanAt A zV (pushAt T zV h v' ≫ aA a) := by
        have hp' := hp
        unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at hp' ⊢
        rw [CategoryTheory.Over.comp_left, ← Category.assoc, hp', ← CategoryTheory.Over.comp_left]
        have := hA a
        simp
      have ht2 : GlobalTheory.CompanionTheory.Ar.IsTanAt A zV (GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale zV (σ a) ≫ pushAt T zV h v') :=
        isTanAt_scale (σ a) hp
      have eq1 : pushAt T zV h v' ≫ aA a = GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale zV (σ a) ≫ pushAt T zV h v' := by
        refine GlobalTheory.CompanionTheory.Ar.LieTangent.tan_ext hinj ht1 ht2 ?_
        have e1 := congrArg CategoryTheory.Over.Hom.left (hρ a w)
        rw [hwE' a, MC.smul, hpw, CategoryTheory.Over.comp_left, pushGen_left] at e1
        simp only [CategoryTheory.Over.comp_left, pushAt_left, Category.assoc] at e1 ⊢
        rw [← e1]
        simp only [GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale, CategoryTheory.Over.homMk_left]
        simp only [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]
      refine h.1.hom_ext ?_ ?_
      · rw [CategoryTheory.Over.comp_left, Category.assoc, hc a, ← Category.assoc, ← pushAt_left h v',
          ← CategoryTheory.Over.comp_left, eq1, CategoryTheory.Over.comp_left, pushAt_left]
        simp only [GlobalTheory.CompanionTheory.Ar.LieTangent.epsScale, CategoryTheory.Over.homMk_left, Category.assoc]
        rfl
      · rw [CategoryTheory.Over.w (v' ≫ aB a), Category.assoc, CategoryTheory.Over.w v', epsOver_hom]
        exact (GlobalTheory.CompanionTheory.Ar.LieTangent.spec_eps_alg (σ a)).symm
    obtain ⟨cf, hcf⟩ := hub v' hv't hv'e
    obtain ⟨u, hu, hv'u⟩ := hcf
    have hw : w = ∑ i, cf i • yb i := by
      apply MC.inj
      rw [hpw, pt_sum, hv'u, map_list_prod, List.map_ofFn]
      congr 1
      apply congrArg List.ofFn
      funext i
      apply CategoryTheory.Over.OverMorphism.ext
      rw [Function.comp_apply, pushGen_left, hu i, ← algebraMap_smul T.Fr (cf i) (yb i), MC.smul, hyb i]
      simp only [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
      rw [show Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (cf i))) =
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (cf i))) from rfl, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨(hL _).2 ⟨pushAt T zV h (ub i), isTanAt_push h (hut i), by rw [hyb i, pushAt_left]⟩, ?_⟩
    show yb i ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)
    rw [mem_eigSp_iff]
    intro a
    apply MC.inj
    apply CategoryTheory.Over.OverMorphism.ext
    rw [hρ a (yb i), MC.smul, CategoryTheory.Over.comp_left, hyb i]
    simp only [Category.assoc]
    rw [← hc a, ← Category.assoc (ub i).left, ← CategoryTheory.Over.comp_left, hue' i a]
    simp only [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_eps]

end Main

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan

theorem GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan.eig_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → (∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left) → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf tX.act.act ρC → ∀ (σ : 𝓞 E →+* T.V) (r : ℕ) (ub : Fin r → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i a, (ub i ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ (ub i).left) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → (∀ a, (w ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ w.left) → ∃ cf : Fin r → T.V, IsComb ub cf w) → ∀ yb : Fin r → EC, (∀ i, (MC.pt (yb i)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (ub i).left ≫ Ψ) → ∀ L : Submodule T.V EC, (∀ w, w ∈ L ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zV ⟶ tX.G, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G zV v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left) → L ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V = Submodule.span T.V (Set.range yb) := by
  intro E _ _ _ H X tX T zV G Ψ h hc EC _ _ _ _ MC ρC hρ σ r ub hut hue hub yb hyb L hL
  exact eigen_span_lie_basis T zV h tX.act.act tX.act.hom G.act.act hc MC ρC hρ σ ub hut hue hub yb hyb L hL
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLieModelCompleteDvrStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_lie_model_complete_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → (∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left) → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf tX.act.act ρC → ∀ (σ : 𝓞 E →+* T.V) (r : ℕ) (ub : Fin r → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ i a, (ub i ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ (ub i).left) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → (∀ a, (w ≫ G.act.act a).left = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (σ a))) ≫ w.left) → ∃ cf : Fin r → T.V, IsComb ub cf w) → ∀ yb : Fin r → EC, (∀ i, (MC.pt (yb i)).left = Spec.map (CommRingCat.ofHom (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (ub i).left ≫ Ψ) → ∀ L : Submodule T.V EC, (∀ w, w ∈ L ↔ ∃ v : GlobalTheory.CompanionTheory.Ar.epsAt zV ⟶ tX.G, GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G zV v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left) → L ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V = Submodule.span T.V (Set.range yb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan.eig_span | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan.eig_span | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.EigSpan.eig_span <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointAbelianMapCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointAbelianMapCompat
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open CategoryTheory.Limits

theorem genFibre_pullback_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (y : FrPt Xo c F) (t' : SAB H (Spec (CommRingCat.of F))) (m1 : SABMap t' Xo.univ.t y.x) (g : Spec (CommRingCat.of F) ⟶ X), Small.ptY Y y = g ≫ f → ∃ b : t'.G.left ⟶ tX.G.left, IsGrpPullback t'.G tX.G g b ∧ (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (u' : Spec (CommRingCat.of (DualNumber F)) ⟶ t'.G.left), u' ≫ m1.φ = y.u τ i → u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) → u' ≫ b ≫ m.φ = Small.tanY Y y τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ y t' m1 g hg
  have wa : m1.φ ≫ Xo.univ.t.G.hom = (t'.G.hom ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [m1.cart.1.w, Category.assoc, Small.ptF_fst]
  let a : t'.G.left ⟶ Y.oF.t.G.left := Y.m0.cart.1.lift m1.φ (t'.G.hom ≫ Small.ptF y) wa
  have ha1 : a ≫ Y.m0.toSABMap.φ = m1.φ := IsPullback.lift_fst _ _ _ _
  have ha2 : a ≫ Y.oF.t.G.hom = t'.G.hom ≫ Small.ptF y := IsPullback.lift_snd _ _ _ _
  have gpa : IsGrpPullback t'.G Y.oF.t.G (Small.ptF y) a :=
    IsGrpPullback.cancel Y.m0.cart (m1.cart.congr (Small.ptF_fst y).symm ha1.symm) ha2
  have gpY : IsGrpPullback t'.G Y.t.G (g ≫ f) (a ≫ Y.m.φ) := (gpa.comp Y.m.cart).congr hg rfl
  have wb : (a ≫ Y.m.φ) ≫ Y.t.G.hom = (t'.G.hom ≫ g) ≫ f := by
    rw [gpY.1.w, Category.assoc]
  let b : t'.G.left ⟶ tX.G.left := m.cart.1.lift (a ≫ Y.m.φ) (t'.G.hom ≫ g) wb
  have hb1 : b ≫ m.φ = a ≫ Y.m.φ := IsPullback.lift_fst _ _ _ _
  have hb2 : b ≫ tX.G.hom = t'.G.hom ≫ g := IsPullback.lift_snd _ _ _ _
  have acta : ∀ r, (t'.act.act r).left ≫ a = a ≫ (Y.oF.t.act.act r).left := by
    intro r
    apply Y.m0.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha1, Y.m0.act r, ← Category.assoc, ha1, m1.act r]
    · rw [Category.assoc, Category.assoc, ha2, Over.w (Y.oF.t.act.act r), ha2, ← Category.assoc,
        Over.w (t'.act.act r)]
  refine ⟨b, IsGrpPullback.cancel m.cart (gpY.congr rfl hb1.symm) hb2, fun r => ?_, fun τ i u' h1 h2 => ?_⟩
  · apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hb1, m.act r, ← Category.assoc b, hb1, Category.assoc, ← Y.m.act r,
        ← Category.assoc, acta r, Category.assoc]
    · rw [Category.assoc, Category.assoc, hb2, Over.w (tX.act.act r), hb2, ← Category.assoc,
        Over.w (t'.act.act r)]
  · have e : u' ≫ a = Small.tanF Y y τ i := by
      apply Small.eq_tanF
      · rw [Category.assoc, ha1, h1]
      · rw [Category.assoc, ha2, ← Category.assoc, h2]
    rw [hb1, ← Category.assoc, e]
    rfl

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointAbelianMapCompatStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_point_abelian_map_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (y : FrPt Xo c F) (t' : SAB H (Spec (CommRingCat.of F))) (m1 : SABMap t' Xo.univ.t y.x) (g : Spec (CommRingCat.of F) ⟶ X), Small.ptY Y y = g ≫ f → ∃ b : t'.G.left ⟶ tX.G.left, IsGrpPullback t'.G tX.G g b ∧ (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (u' : Spec (CommRingCat.of (DualNumber F)) ⟶ t'.G.left), u' ≫ m1.φ = y.u τ i → u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) → u' ≫ b ≫ m.φ = Small.tanY Y y τ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.genFibre_pullback_cover | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.genFibre_pullback_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.genFibre_pullback_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameFinal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameFinal
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.PtEq

set_option backward.isDefEq.respectTransparency false

theorem exists_factor' {O' R Ω C : Type} [CommRing O'] [CommRing R] [CommRing Ω] [CommRing C] (g : O' →+* Ω)
    (cl : O' →+* C) (hg : Function.Injective g) (φ : R →+* Ω) (ψ : R →+* C)
    (h : ∀ r, ∃ s, g s = φ r ∧ cl s = ψ r) : ∃ θ : R →+* O', g.comp θ = φ ∧ cl.comp θ = ψ := by
  choose θ h1 h2 using h
  exact ⟨{ toFun := θ
           map_one' := hg (by simp [h1])
           map_mul' := fun a b => hg (by simp [h1])
           map_zero' := hg (by simp [h1])
           map_add' := fun a b => hg (by simp [h1]) }, RingHom.ext h1, RingHom.ext h2⟩

theorem pts_eq' {O' Ω R₀ : Type} [CommRing O'] [Field Ω] [CommRing R₀] (g : O' →+* Ω) (hg : Function.Injective g)
    {B : Scheme.{0}} (s : B ⟶ Sp R₀) [IsSeparated s] {a b : Sp O' ⟶ B} (h : spMap g ≫ a = spMap g ≫ b) : a = b := by
  haveI : IsDomain O' := hg.isDomain g
  haveI : IsDominant (spMap g) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot g).1 hg]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated s ?_ (spMap g) h
  refine ext_of_isDominant (spMap g) ?_
  rw [← Category.assoc, h, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.PtEq

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots


open PtEq in
set_option maxHeartbeats 600000 in
theorem ptY_eq_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → (letI := io.toAlgebra; Small.ptY Y zT = FinRd.Roots.gen T zV ≫ Or.𝔐.f) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hv hG la T io e y evT zT t hI zV hR
  letI := io.toAlgebra
  letI := Small.cstAlg Or
  obtain ⟨-, -, -, -, -, -, ⟨q, φ, ψ, yq, hφ, hψ, hr⟩, -⟩ := hI
  have hgen : genPt Or.𝔐.ξ ⤳ centre (gen T zV) := Or.𝔐.all _
  let P : Cpt Or.𝔐.ξ := ⟨centre (gen T zV), hgen⟩
  have hinj : Function.Injective (genMap Or.𝔐.ξ P) := Or.𝔐.tie.gen.inj P
  have hreg : ∀ r, ∃ s', genMap Or.𝔐.ξ P s' = φ.toRingHom r ∧
      (Scheme.stalkClosedPointTo (gen T zV)).hom s' = ψ.toRingHom r := fun r => by
    obtain ⟨h, e'⟩ := hr r
    obtain ⟨h', s', hs, hs'⟩ := hR ⟨φ r, h⟩
    exact ⟨s', hs, hs'.trans e'.symm⟩
  obtain ⟨θ, hθ1, hθ2⟩ := exists_factor' _ _ hinj φ.toRingHom ψ.toRingHom hreg
  have hsep : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have he : Or.𝔐.X.fromSpecStalk P.1 ≫ Or.𝔐.f = spMap θ ≫ Small.ptY Y yq := by
    refine pts_eq' (genMap Or.𝔐.ξ P) hinj Y.s ?_
    rw [← Category.assoc, ← Category.assoc]
    have e1 : spMap (genMap Or.𝔐.ξ P) ≫ Or.𝔐.X.fromSpecStalk P.1 = Or.𝔐.ξ := LieTangent.spec_genMap _ _
    rw [e1, ← Fr.pt_eq, Small.ptY_map Y hφ, ← hθ1, LieTangent.spec_comp]
  have e2 : spMap (Scheme.stalkClosedPointTo (gen T zV)).hom ≫ Or.𝔐.X.fromSpecStalk P.1 = gen T zV :=
    LieTangent.spec_centre (gen T zV)
  rw [Small.ptY_map Y hψ]
  have e3 : ψ.toRingHom = (Scheme.stalkClosedPointTo (gen T zV)).hom.comp θ := hθ2.symm
  have e4 : spMap ((Scheme.stalkClosedPointTo (gen T zV)).hom.comp θ) =
      spMap (Scheme.stalkClosedPointTo (gen T zV)).hom ≫ spMap θ := (LieTangent.spec_comp θ _).symm
  rw [e3, e4, Category.assoc]
  exact (congrArg (fun u => spMap (Scheme.stalkClosedPointTo (gen T zV)).hom ≫ u) he.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun u => u ≫ Or.𝔐.f) e2))

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameFinalStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_generic_frame_final : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → (letI := io.toAlgebra; Small.ptY Y zT = FinRd.Roots.gen T zV ≫ Or.𝔐.f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen <;> assumption)
end
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits

theorem lieEig_basis_rf : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (u : Fin (labelRk Dw s) → EC) (σ : 𝓞 E →+* T.V), (∀ i, FinRd.Roots.IsFrameVec Or io zT MC (u i) s i) → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → LinearIndependent T.Fr u ∧ ∃ yb : Fin (labelRk Dw s) → EC, FinRd.Roots.TriIn u (fun i => (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr)) yb ∧ FinRd.Roots.lieEig Or MC ρC σ = Submodule.span T.V (Set.range yb) := by
  intro hGiven E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hval hA la T io e y evT zT t hI zV hR EC _ _ _ _ MC ρC hρ s u σ hu hσ
  letI := io.toAlgebra
  obtain ⟨hp, hOver, hAlg, hphi, hcst, hnorm, hsp, hBor⟩ := hI
  have hI' : FinRd.IsIntPt Fr A ev la T io e y evT zT t := ⟨hp, hOver, hAlg, hphi, hcst, hnorm, hsp, hBor⟩
  have hExt : GlobalTheory.Published.SemiAbelianHomExtension := hGiven.2.2.1
  have hξ : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  have hptz : Small.ptY Y zT = FinRd.Roots.gen T zV ≫ Or.𝔐.f :=
    GlobalTheory.T.root_origin_generic_frame_final E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hA la T io e y evT zT t hI' zV hR
  have hpty : Small.ptY Y y.1 = FinRd.Roots.gen T zV ≫ Or.𝔐.f := by
    rw [← hptz, Small.ptY, Small.ptY]
    congr 1
    apply Limits.pullback.hom_ext
    · rw [Small.ptF_fst, Small.ptF_fst, hBor.1]
    · rw [Small.ptF_snd, Small.ptF_snd]
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbasis, hlift⟩, -⟩ := y.2.2
  obtain ⟨b, hb, hbact, hbu⟩ := GlobalTheory.T.frame_point_abelian_map_compat E H Dw l Xo c O β Y Or.𝔐.X Or.𝔐.t Or.𝔐.f Or.𝔐.m T.Fr y.1 t' m1 _ hpty
  obtain ⟨Ψ, hΨ, hm2, hΨact⟩ := GlobalTheory.T.complete_dvr_pullback_semiabelian E H hExt Or.𝔐.X Or.𝔐.t T zV G t' m2 b hb hbact
  have hsig : ∀ a, algebraMap T.V T.Fr (σ a) = io (embK c (Small.labelC s) a) := fun a => by
    rw [Small.embK_labelC]
    have h1 := hA.1 (labelEmb c s a)
    have h2 := hR ⟨_, h1⟩
    have h3 := LieTangent.valAt_base hξ (algebraMap T.V T.Fr) (hσ a)
    rw [← hcst _ h1]
    exact LieTangent.valAt_unique hξ h3 h2
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hyb : ∀ i, ∃ w : EC, (MC.pt w).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap T.V T.Fr))) ≫
      (ub (Small.labelC s) (Small.labelFin Dw s i)).left ≫ Ψ := fun i =>
    GlobalTheory.T.tangent_vector_lie_model_lift E H Or.𝔐.X Or.𝔐.t T zV G Ψ hΨ EC MC _ (htan _ _)
  choose yb hyb using hyb
  have hybT : ∀ i, (MC.pt (yb i)).left ≫ Or.𝔐.m.φ = Small.tanY Y y.1 (Small.labelC s) (Small.labelFin Dw s i) := fun i => by
    obtain ⟨u', hu1, hu2⟩ := hlift (Small.labelC s) (Small.labelFin Dw s i)
    have hu2' : u' ≫ m2.φ = Spec.map (CommRingCat.ofHom (dualMap (algebraMap T.V T.Fr))) ≫
        (ub (Small.labelC s) (Small.labelFin Dw s i)).left := hu2
    have hbase : u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) :=
      base_eq T G t' m2 _ u' hu2'
    rw [← hbu _ _ u' hu1 hbase, hyb, ← hm2]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map _), ← hu2']
    simp only [Category.assoc]
  have hr : labelRk Dw s = Dw.mult (Small.labelC s) := (Small.mult_labelC Dw s).symm
  have hu' : ∀ i, (MC.pt (u i)).left ≫ Or.𝔐.m.φ = Small.tanY Y zT (Small.labelC s) (Fin.cast hr i) := hu
  refine ⟨GlobalTheory.T.abelian_map_lie_model_eigen_frame E H Dw l Xo c O β Y Or.𝔐.X Or.𝔐.t Or.𝔐.f Or.𝔐.m T.Fr _ EC MC zT hptz _ _ hr u hu', yb,
    GlobalTheory.T.abelian_map_lie_model_lattice E H Dw l Xo c O β Y Or.𝔐.X Or.𝔐.t Or.𝔐.f Or.𝔐.m T.Fr _ EC MC zT hptz y.1 t hBor _ _ hr u yb hu' hybT, ?_⟩
  have hsm : AlgebraicGeometry.Smooth Or.𝔐.t.G.hom := Or.𝔐.t.semi.smooth
  refine GlobalTheory.T.eigen_lie_model_complete_dvr E H Or.𝔐.X Or.𝔐.t T zV G Ψ hΨ hΨact EC MC ρC hρ σ _ (fun i => ub (Small.labelC s) (Small.labelFin Dw s i))
    (fun i => htan _ _) (fun i a => heig _ _ a _ (hsig a)) ?_ yb hyb _ (fun w =>
      lieLat_fibAt_iff _ _ _ _ _ Or.𝔐.M T.V zV T.Fr EC MC hξ hsm (Or.𝔐.all _) (Or.𝔐.all _) w)
  intro w hw hwe
  have hw' : IsEigV c io G (Small.labelC s) w := fun a z' hz' => by
    have : z' = σ a := hinj (hz'.trans (hsig a).symm)
    rw [this]; exact hwe a
  obtain ⟨cf, hcf, -⟩ := hbasis _ w hw hw'
  exact ⟨_, isComb_cast hr _ _ _ hcf⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.PositivityTheory.UnitarySelfGeneration.linearIndependent_and_exists_triIn_lieEig_eq_span : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (u : Fin (labelRk Dw s) → EC) (σ : 𝓞 E →+* T.V), (∀ i, FinRd.Roots.IsFrameVec Or io zT MC (u i) s i) → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → LinearIndependent T.Fr u ∧ ∃ yb : Fin (labelRk Dw s) → EC, FinRd.Roots.TriIn u (fun i => (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr)) yb ∧ FinRd.Roots.lieEig Or MC ρC σ = Submodule.span T.V (Set.range yb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.lieEig_basis_rf | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.lieEig_basis_rf | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.lieEig_basis_rf <;> assumption)

end
