module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjByOfOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyClosedRepresentsFixedPullbackHoms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedBundlePullbackIsoOfLocalIsoAbelianHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedBundlePullbackIsoOfLocalIsoAbelianHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomFixLocal

open GlobalTheory.CechPic

theorem lbIso_pull_of_local : ∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left) := by
  intro H A B _ _ _ _ L M Φ hΦ hA _ hL hM rL rM loc
  haveI := hΦ
  refine GlobalTheory.ThetaAffineGlue.lbIso_of_local GlobalTheory.SemiRigid.globalFns A hA hL (pull_isLB hM Φ.left) rL ?_ loc
  refine (GlobalTheory.PolProd.rigidified_iff A (pull_isLB hM Φ.left)).2 ?_
  rw [cls_pull hM, ← pull_comp, GlobalTheory.PolProd.eSec_comp Φ]
  exact (GlobalTheory.PolProd.rigidified_iff B hM).1 rM

end GlobalTheory.HomFixLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedBundlePullbackIsoOfLocalIsoAbelianHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedBundle_pullbackIso_of_localIso_abelianHom : ∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left) := by
  first | exact @GlobalTheory.HomFixLocal.lbIso_pull_of_local | exact GlobalTheory.HomFixLocal.lbIso_pull_of_local | (intros; apply GlobalTheory.HomFixLocal.lbIso_pull_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSchemeRepresentingPolarizedHoms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRepresentingSchemeHomFixedPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionBasesTransferTotalSpaceIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionBasesTransferTotalSpaceIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecBasisTransfer

def chartPullUnLinComb {X X' Y Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (g : Y ⟶ Y') (hc : ∀ k, g ≫ ψ' k ≫ F = ψ k) :
    ChartPull (LB.LinComb L ψ ε) (LB.LinComb (L.pull F) ψ' ε) g :=
  have pt : ∀ k (y : Y), F (ψ' k (g y)) = ψ k y := fun k y => by
    rw [← hc k]; rfl
  have le : ∀ j : K → L.ι, LB.wchart L ψ j ≤ g ⁻¹ᵁ LB.wchart (L.pull F) ψ' (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by
      show F (ψ' k (g y)) ∈ L.U (j k)
      rw [pt k y]; exact Set.mem_iInter.1 hy k)
  { idx := fun j k _ => j k
    le := le
    g := fun y j j' hj hj' => by
      have m : g y ∈ LB.wchart (L.pull F) ψ' (fun k _ => j k) := le j hj
      have m' : g y ∈ LB.wchart (L.pull F) ψ' (fun k _ => j' k) := le j' hj'
      refine (gm_linComb L ψ ε (𝟙 Y) y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull F) ψ' ε g y _ _ m m').symm)
      refine Eq.trans ?_ (gm_pull_g L F (g ≫ ψ' k) y (fun _ => j k) (fun _ => j' k)
        (Set.mem_iInter.1 m k) (Set.mem_iInter.1 m' k)).symm
      rw [Category.assoc, hc k, Category.id_comp] }

theorem sec_eq_of_f {Y : Scheme.{0}} {N : LB Y} {s t : LB.Sec N} (e : s.f = t.f) : s = t := by
  obtain ⟨a, ha⟩ := s
  obtain ⟨b, hb⟩ := t
  cases e
  rfl

theorem pullSec_pullSec {Y Y' : Scheme.{0}} {M : LB Y} {M' : LB Y'} {g : Y ⟶ Y'} {h : Y' ⟶ Y}
    (c' : ChartPull M M' g) (c : ChartPull M' M h) (hh : g ≫ h = 𝟙 Y) (hidx : ∀ j, c.idx (c'.idx j) = j)
    (s : LB.Sec M) : GlobalTheory.SecTwist.pullSec c' (GlobalTheory.SecTwist.pullSec c s) = s := by
  refine sec_eq_of_f (funext fun j => fn_ext fun y hy => ?_)
  have hy' : (𝟙 Y ≫ g) y ∈ M'.U (c'.idx j) := c'.le j hy
  rw [GlobalTheory.SecTwist.gs_pullSec c' _ (𝟙 Y) y j hy, GlobalTheory.SecTwist.gs_pullSec c s (𝟙 Y ≫ g) y _ hy',
    Category.id_comp, hh, hidx j]

theorem gs_liftHom {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} {Z : Scheme.{0}}
    (f : Z ⟶ (T ⊗ A).left) (z : Z) (W : (T ⊗ A).left.Opens) (hz : f z ∈ W) (r : Γ(T.left, ⊤)) :
    gs f z W (liftHom A W r) = gs (f ≫ (fst T A).left) z ⊤ r :=
  (gs_res f z le_top hz _).trans (gs_pull f (fst T A).left z ⊤ trivial _)

def pullLin {S S' Z : Scheme.{0}} (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A'] (L : LB A.left)
    (L' : LB A'.left) (k k' : ℤ) (y : Z ⟶ S) (x : Z ⟶ S') {h : (Over.mk x ⊗ A').left ⟶ (Over.mk y ⊗ A).left}
    (c : ChartPull (LPow A' L' k' (Over.mk x)) (LPow A L k (Over.mk y)) h)
    (hfst : h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) A').left) :
    SecM A L k (Over.mk y) →ₗ[Γ(Z, ⊤)] SecM A' L' k' (Over.mk x) where
  toFun m := SecM.ofSec A' (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m))
  map_add' m₁ m₂ := Subtype.ext (funext fun i => fn_ext fun z hz => by
    have hz' : (𝟙 _ ≫ h) z ∈ (LPow A L k (Over.mk y)).U (c.idx i) := c.le i hz
    show gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A (m₁ + m₂))).f i) =
      gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A m₁)).f i +
        (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m₂)).f i)
    rw [gs_add _ z _ hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz,
      GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz]
    exact gs_add _ z _ hz' _ _)
  map_smul' r m := Subtype.ext (funext fun i => fn_ext fun z hz => by
    have hz' : (𝟙 _ ≫ h) z ∈ (LPow A L k (Over.mk y)).U (c.idx i) := c.le i hz
    show gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A (r • m))).f i) =
      gs (𝟙 _) z _ (liftHom A' _ r * (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m)).f i)
    rw [gs_mul _ z _ hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz]
    refine (gs_mul _ z _ hz' (liftHom A _ r) _).trans (congrArg (· * _) ?_)
    rw [gs_liftHom A _ z _ hz' r, gs_liftHom A' (𝟙 _) z _ hz r, Category.assoc, hfst])

theorem li_span_map {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] {I : Type*} (E : M ≃ₗ[R] M') (v : I → M) (hli : LinearIndependent R v)
    (hsp : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent R (E ∘ v) ∧ Submodule.span R (Set.range (E ∘ v)) = ⊤ := by
  refine ⟨hli.map' E.toLinearMap E.ker, ?_⟩
  rw [Set.range_comp, ← E.coe_toLinearMap, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]

theorem bases_transfer : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  intro S S' A _ Ag _ φ L _ k R _ x y h hc _ hfst m b b' hb' hli hsp
  let c := chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left)
    (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc
  have hc' : ∀ _ : Fin 1, inv h ≫ (snd (Over.mk x) Ag).left ≫ φ = (snd (Over.mk y) A).left := fun _ => by
    rw [hc 0, IsIso.inv_hom_id_assoc]
  let c' := chartPullUnLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left)
    (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) (inv h) hc'
  have hfst' : inv h ≫ (fst (Over.mk x) Ag).left = (fst (Over.mk y) A).left := by
    rw [← hfst, IsIso.inv_hom_id_assoc]
  let F := pullLin A Ag L (L.pull φ) k k y x c hfst
  let G := pullLin Ag A (L.pull φ) L k k x y c' hfst'
  have GF : ∀ s : LB.Sec (LPow A L k (Over.mk y)),
      GlobalTheory.SecTwist.pullSec c' (GlobalTheory.SecTwist.pullSec c s) = s :=
    pullSec_pullSec c' c (IsIso.inv_hom_id h) (fun _ => rfl)
  have FG : ∀ s : LB.Sec (LPow Ag (L.pull φ) k (Over.mk x)),
      GlobalTheory.SecTwist.pullSec c (GlobalTheory.SecTwist.pullSec c' s) = s :=
    pullSec_pullSec c c' (IsIso.hom_inv_id h) (fun _ => rfl)
  let E : SecM A L k (Over.mk y) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)] SecM Ag (L.pull φ) k (Over.mk x) :=
    { F with
      invFun := G
      left_inv := fun n => congrArg (SecM.ofSec A) (GF (SecM.toSec A n))
      right_inv := fun n => congrArg (SecM.ofSec Ag) (FG (SecM.toSec Ag n)) }
  have hv : (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) =
      E ∘ fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y)) :=
    funext fun i => by rw [hb' i]; rfl
  have key := li_span_map E _ hli hsp
  rw [← hv] at key
  exact key

end GlobalTheory.SecBasisTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionBasesTransferTotalSpaceIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionBases_transfer_totalSpaceIso : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  first | (exact @GlobalTheory.SecBasisTransfer.bases_transfer) | (exact GlobalTheory.SecBasisTransfer.bases_transfer) | (intros; apply GlobalTheory.SecBasisTransfer.bases_transfer  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HomFixLocBasis

theorem isIso_compare : ∀ {S S' : Scheme.{0}} (u : S' ⟶ S) (A : Over S) (Ag : Over S') (φ : Ag.left ⟶ A.left), IsPullback φ Ag.hom A.hom u → ∀ (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S), x ≫ u = y → ∀ (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left), h ≫ (snd (Over.mk y) A).left = (snd (Over.mk x) Ag).left ≫ φ → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → IsIso h := by
  intro S S' u A Ag φ hφ R _ x y hxy h h1 h2
  subst hxy
  have P := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (Over.mk x)).paste_horiz hφ
  have Q : IsPullback (snd (Over.mk (x ≫ u)) A).left (fst (Over.mk (x ≫ u)) A).left A.hom (x ≫ u) :=
    GlobalTheory.AbLaw.SecBC.isPullback_snd A (Over.mk (x ≫ u))
  have P' : IsPullback ((snd (Over.mk x) Ag).left ≫ φ) (fst (Over.mk x) Ag).left A.hom (x ≫ u) := P
  have e : h = (P'.isoIsPullback _ _ Q).hom :=
    Q.hom_ext (by rw [h1]; exact (IsPullback.isoIsPullback_hom_fst _ _ P' Q).symm) (by rw [h2]; exact (IsPullback.isoIsPullback_hom_snd _ _ P' Q).symm)
  rw [e]
  infer_instance

theorem exists_basicOpen_le {Rg : Type} [CommRing Rg] (V : (Sp Rg).Opens) (p : Sp Rg) (hpV : p ∈ V) :
    ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧
      ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Rg)) ⊆ (V : Set (Sp Rg))) := by
  have hVo : IsOpen (X := PrimeSpectrum Rg) (V : Set (Sp Rg)) := V.isOpen
  have hpV' : (p : PrimeSpectrum Rg) ∈ (V : Set (Sp Rg)) := hpV
  obtain ⟨W, ⟨f, rfl⟩, h1, h2⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := Rg)).exists_subset_of_mem_open
    (a := (p : PrimeSpectrum Rg)) (u := ((V : Set (Sp Rg)) : Set (PrimeSpectrum Rg))) hpV' hVo
  exact ⟨f, h1, h2⟩

theorem exists_factor_away {Rg : Type} [CommRing Rg] (V : (Sp Rg).Opens) (f g : Rg)
    (hfV : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Rg)) ⊆ (V : Set (Sp Rg)))
    (hg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ∃ uV : Sp (Localization.Away g) ⟶ V.toScheme, uV ≫ V.ι = spMap (algebraMap Rg (Localization.Away g)) := by
  have hu : Set.range (spMap (algebraMap Rg (Localization.Away g))) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have h1 : PrimeSpectrum.comap (algebraMap Rg (Localization.Away g)) x ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum Rg)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact ⟨x, rfl⟩
    exact hfV (hg h1)
  exact ⟨_, IsOpenImmersion.lift_fac V.ι _ hu⟩

theorem secBasis_of_factor {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (k : ℕ) (V : (Sp Rg).Opens) (m : ℕ)
    (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)))
    (hb : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) V).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤)
    {S' : Scheme.{0}} (u : S' ⟶ Sp Rg) (uV : S' ⟶ V.toScheme) (huV : uV ≫ V.ι = u)
    (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (hφ : IsGrpPullback Ag A u φ) :
    ∃ (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver S') ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S') ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤ := by
  have hAgw : φ ≫ A.hom = Ag.hom ≫ u := hφ.1.w
  have hw : ((snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ) ≫ A.hom =
      ((fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV) ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by
    have e := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (overRes (T := baseOver S') ⊤)).w
    simp only [Category.assoc, hAgw]
    rw [← Category.assoc, e]
    simp [overRes, baseOver, huV]
  obtain ⟨H, hH1, hH2⟩ : ∃ H : (overRes (T := baseOver S') ⊤ ⊗ Ag).left ⟶ (overRes (T := baseOver (Sp Rg)) V ⊗ A).left,
      H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left = (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ ∧
      H ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left = (fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV :=
    ⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw⟩
  have hc : ∀ _ : Fin 1, (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ = H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left :=
    fun _ => hH1.symm
  refine ⟨fun i => GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left)
    (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i), ?_⟩
  intro R _ t b' hb'
  obtain ⟨t', ht'⟩ : ∃ t' : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) V).left, t' = t ≫ (⊤ : S'.Opens).ι ≫ uV := ⟨_, rfl⟩
  choose b'' hb'' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec A L (k : ℤ) (homAt t') (b i)
  have hB := hb R t' b'' hb''
  have hxy : (t ≫ (overRes (T := baseOver S') ⊤).hom) ≫ u = t' ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by
    rw [ht']
    simp [overRes, baseOver, huV]
  have hw2 : ((snd (baseAt t) Ag).left ≫ φ) ≫ A.hom = (fst (baseAt t) Ag).left ≫ (baseAt t').hom := by
    have e := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (baseAt t)).w
    simp only [Category.assoc, hAgw]
    rw [← Category.assoc, e]
    simp [baseAt, overRes, baseOver, ht', huV]
  obtain ⟨h, hh1, hh2⟩ : ∃ h : (baseAt t ⊗ Ag).left ⟶ (baseAt t' ⊗ A).left,
      h ≫ (snd (baseAt t') A).left = (snd (baseAt t) Ag).left ≫ φ ∧
      h ≫ (fst (baseAt t') A).left = (fst (baseAt t) Ag).left :=
    ⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw2, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw2⟩
  have hc' : ∀ _ : Fin 1, (snd (baseAt t) Ag).left ≫ φ = h ≫ (snd (baseAt t') A).left := fun _ => hh1.symm
  refine GlobalTheory.T.sectionBases_transfer_totalSpaceIso A Ag φ L hL (k : ℤ) R _ _ h hc' (isIso_compare u A Ag φ hφ.1 R _ _ hxy h hh1 hh2) hh2 m b'' b' ?_ hB.1 hB.2
  have hcomp : (homAt t ▷ Ag).left ≫ H = h ≫ (homAt t' ▷ A).left := by
    apply (GlobalTheory.AbLaw.SecBC.isPullback_snd A (overRes (T := baseOver (Sp Rg)) V)).hom_ext
    · rw [Category.assoc, hH1, Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, ← Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, hh1]
    · have e1 := GlobalTheory.AbLaw.SecBC.fst_eq Ag (homAt t)
      have e2 := GlobalTheory.AbLaw.SecBC.fst_eq A (homAt t')
      calc ((homAt t ▷ Ag).left ≫ H) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left
            = ((homAt t ▷ Ag).left ≫ (fst (overRes (T := baseOver S') ⊤) Ag).left) ≫ (⊤ : S'.Opens).ι ≫ uV := by
              rw [Category.assoc, hH2, Category.assoc]
        _ = (fst (baseAt t) Ag).left ≫ t ≫ (⊤ : S'.Opens).ι ≫ uV := by
              rw [e1]
              try simp [homAt]
        _ = (h ≫ (homAt t' ▷ A).left) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left := by
              rw [Category.assoc, e2, reassoc_of% hh2, ht']
              try simp [homAt]
  intro i
  apply GlobalTheory.SecTwist.sec_ext_loc
  intro y
  obtain ⟨j, hj⟩ : ∃ j, y ∈ (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j :=
    exists_chart (LB.isLB_linComb (LB.isLB_pull hL φ) _ _ : (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).IsLB) y
  refine ⟨j, hj, ?_⟩
  have hj1 := chart_le_res Ag (L.pull φ) (homAt t ▷ Ag) (whiskerRight_snd _ _) (k : ℤ) j hj
  have hj2 : h y ∈ (LPow A L (k : ℤ) (baseAt t')).U (fun k => j k PUnit.unit) := by
    have := (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
      (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc').le j hj
    exact this
  have lhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j) ((b' i).f j) =
      gs ((homAt t ▷ Ag).left ≫ H) y ((LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit))
        ((b i).f (fun k => j k PUnit.unit)) := by
    rw [hb' i j, GlobalTheory.AbLaw.SecBC.gs_rp _ _ (𝟙 _) y hj, Category.id_comp]
    exact GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left)
      (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i) (homAt t ▷ Ag).left y j hj1
  have rhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j)
      ((GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
        (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i)).f j) =
      gs (h ≫ (homAt t' ▷ A).left) y ((LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit))
        ((b i).f (fun k => j k PUnit.unit)) := by
    have e1 := GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
        (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i) (𝟙 _) y j hj
    rw [Category.id_comp] at e1
    refine e1.trans ?_
    erw [hb'' i (fun k => j k PUnit.unit)]
    exact GlobalTheory.AbLaw.SecBC.gs_rp _ _ h y hj2 _
  rw [lhs, rhs, hcomp]

theorem exists_basicOpen_secBasis : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ k : ℕ, 1 ≤ k → ∀ p : Sp Rg, ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧ ∀ g : Rg, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f → ∀ (Ag : Over (Sp (Localization.Away g))) [GrpObj Ag] [IsCommMonObj Ag] (φ : Ag.left ⟶ A.left), IsGrpPullback Ag A (spMap (algebraMap Rg (Localization.Away g))) φ → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver (Sp (Localization.Away g))) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp (Localization.Away g))) ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤) := by
  intro Rg _ _ A _ _ L hAb hL hRig hAmp k hk p
  obtain ⟨V, hpV, m, b, hb⟩ := GlobalTheory.AmpleSecBC.secBaseChange_relAmple (Sp Rg) A L hAb hL hRig hAmp k hk p
  have hx := exists_basicOpen_le (Rg := Rg) V p hpV
  refine ⟨hx.choose, hx.choose_spec.1, fun g hg Ag _ _ φ hφ => ⟨m, ?_⟩⟩
  have hu := exists_factor_away V _ g hx.choose_spec.2 hg
  exact secBasis_of_factor A L hL k V m b hb _ hu.choose hu.choose_spec Ag φ hφ

end GlobalTheory.HomFixLocBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ k : ℕ, 1 ≤ k → ∀ p : Sp Rg, ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧ ∀ g : Rg, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f → ∀ (Ag : Over (Sp (Localization.Away g))) [GrpObj Ag] [IsCommMonObj Ag] (φ : Ag.left ⟶ A.left), IsGrpPullback Ag A (spMap (algebraMap Rg (Localization.Away g))) φ → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver (Sp (Localization.Away g))) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp (Localization.Away g))) ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤) := by
  first | exact @GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis | exact GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis | (intros; apply GlobalTheory.HomFixLocBasis.exists_basicOpen_secBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedPullbackHomSchemeOfSectionBases
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepOfAffineTests
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepOfAffineTests
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.EndLoc.HomFixGlue

variable {S H : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {AH BH : Over H} [GrpObj AH] [GrpObj BH]

def IsSol (π : H ⟶ S) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH) {T : Scheme.{0}} (t : T ⟶ S)
    (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B')
    (h : T ⟶ H) : Prop :=
  h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
    IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left

def IsRestr {T U : Scheme.{0}} (g : U ⟶ T) {A' B' : Over T} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B')
    {A'' B'' : Over U} [GrpObj A''] [GrpObj B''] (Φ'' : A'' ⟶ B'') (ρA : A''.left ⟶ A'.left)
    (ρB : B''.left ⟶ B'.left) : Prop :=
  IsGrpPullback A'' A' g ρA ∧ IsGrpPullback B'' B' g ρB ∧ Φ''.left ≫ ρB = ρA ≫ Φ'.left

variable {π : H ⟶ S} {φA : AH.left ⟶ A.left} {φB : BH.left ⟶ B.left} {Φ : AH ⟶ BH}

theorem isRestr_pullback {T U : Scheme.{0}} (g : U ⟶ T) {A' B' : Over T} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B') :
    IsRestr g Φ' ((Over.pullback g).map Φ') (pullback.fst A'.hom g) (pullback.fst B'.hom g) :=
  ⟨isGrpPullback_pullback A' g, isGrpPullback_pullback B' g, pullback.lift_fst _ _ _⟩

theorem IsSol.restr {T U : Scheme.{0}} {t : T ⟶ S} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {h : T ⟶ H}
    (hs : IsSol π φA φB Φ t A' B' φA' φB' Φ' h) {g : U ⟶ T} {A'' B'' : Over U} [GrpObj A''] [GrpObj B'']
    {Φ'' : A'' ⟶ B''} {ρA : A''.left ⟶ A'.left} {ρB : B''.left ⟶ B'.left} (hr : IsRestr g Φ' Φ'' ρA ρB) :
    IsSol π φA φB Φ (g ≫ t) A'' B'' (ρA ≫ φA') (ρB ≫ φB') Φ'' (g ≫ h) := by
  obtain ⟨h1, ψA, ψB, pA, pB, eA, eB, eΦ⟩ := hs
  obtain ⟨rA, rB, rΦ⟩ := hr
  refine ⟨by rw [Category.assoc, h1], ρA ≫ ψA, ρB ≫ ψB, rA.comp pA, rB.comp pB, by rw [Category.assoc, eA],
    by rw [Category.assoc, eB], ?_⟩
  rw [← Category.assoc, rΦ, Category.assoc, eΦ, Category.assoc]

theorem IsRestr.factor {T U W : Scheme.{0}} {f : U ⟶ T} {k : W ⟶ U} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {Φ' : A' ⟶ B'} {Aα Bα : Over U} [GrpObj Aα] [GrpObj Bα] {Φα : Aα ⟶ Bα} {ρAα : Aα.left ⟶ A'.left}
    {ρBα : Bα.left ⟶ B'.left} (hα : IsRestr f Φ' Φα ρAα ρBα) {AW BW : Over W} [GrpObj AW] [GrpObj BW]
    {ΦW : AW ⟶ BW} {ρAW : AW.left ⟶ A'.left} {ρBW : BW.left ⟶ B'.left} (hW : IsRestr (k ≫ f) Φ' ΦW ρAW ρBW) :
    ∃ (σA : AW.left ⟶ Aα.left) (σB : BW.left ⟶ Bα.left), IsRestr k Φα ΦW σA σB ∧ σA ≫ ρAα = ρAW ∧
      σB ≫ ρBα = ρBW := by
  obtain ⟨aα, bα, cα⟩ := hα
  obtain ⟨aW, bW, cW⟩ := hW
  have wA : ρAW ≫ A'.hom = (AW.hom ≫ k) ≫ f := by rw [aW.1.w, Category.assoc]
  have wB : ρBW ≫ B'.hom = (BW.hom ≫ k) ≫ f := by rw [bW.1.w, Category.assoc]
  refine ⟨aα.1.lift _ _ wA, bα.1.lift _ _ wB, ⟨aα.cancel (aW.congr rfl (aα.1.lift_fst _ _ wA).symm)
    (aα.1.lift_snd _ _ wA), bα.cancel (bW.congr rfl (bα.1.lift_fst _ _ wB).symm) (bα.1.lift_snd _ _ wB), ?_⟩,
    aα.1.lift_fst _ _ wA, bα.1.lift_fst _ _ wB⟩
  apply bα.1.hom_ext
  · rw [Category.assoc, Category.assoc, bα.1.lift_fst, cW, cα, ← Category.assoc, aα.1.lift_fst]
  · rw [Category.assoc, Category.assoc, bα.1.lift_snd, Over.w Φα, aα.1.lift_snd, ← Category.assoc, Over.w ΦW]

theorem IsSol.pull {T U W : Scheme.{0}} {t : T ⟶ S} {f : U ⟶ T} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {Aα Bα : Over U} [GrpObj Aα] [GrpObj Bα]
    {Φα : Aα ⟶ Bα} {ρAα : Aα.left ⟶ A'.left} {ρBα : Bα.left ⟶ B'.left} (hα : IsRestr f Φ' Φα ρAα ρBα) {hα' : U ⟶ H}
    (hs : IsSol π φA φB Φ (f ≫ t) Aα Bα (ρAα ≫ φA') (ρBα ≫ φB') Φα hα') (k : W ⟶ U) {g : W ⟶ T} (hg : g = k ≫ f)
    {AW BW : Over W} [GrpObj AW] [GrpObj BW] {ΦW : AW ⟶ BW} {ρAW : AW.left ⟶ A'.left} {ρBW : BW.left ⟶ B'.left}
    (hW : IsRestr g Φ' ΦW ρAW ρBW) : IsSol π φA φB Φ (g ≫ t) AW BW (ρAW ≫ φA') (ρBW ≫ φB') ΦW (k ≫ hα') := by
  subst hg
  obtain ⟨σA, σB, hr, eA, eB⟩ := hα.factor hW
  have := hs.restr hr
  rw [← eA, ← eB]
  simp only [Category.assoc] at this ⊢
  exact this

theorem isSol_of_local (pbA : IsGrpPullback AH A π φA) (pbB : IsGrpPullback BH B π φB) {T : Scheme.{0}} {t : T ⟶ S}
    {A' B' : Over T} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'}
    (hA : IsGrpPullback A' A t φA') (hB : IsGrpPullback B' B t φB') {h : T ⟶ H} (hh : h ≫ π = t) {Idx : Type}
    {U : Idx → Scheme.{0}} (f : ∀ i, U i ⟶ T) (Aα Bα : ∀ i, Over (U i)) [∀ i, GrpObj (Aα i)] [∀ i, GrpObj (Bα i)]
    (Φα : ∀ i, Aα i ⟶ Bα i) (ρA : ∀ i, (Aα i).left ⟶ A'.left) (ρB : ∀ i, (Bα i).left ⟶ B'.left)
    (hr : ∀ i, IsRestr (f i) Φ' (Φα i) (ρA i) (ρB i))
    (hs : ∀ i, IsSol π φA φB Φ (f i ≫ t) (Aα i) (Bα i) (ρA i ≫ φA') (ρB i ≫ φB') (Φα i) (f i ≫ h))
    (hepi : ∀ (u v : A'.left ⟶ BH.left), (∀ i, ρA i ≫ u = ρA i ≫ v) → u = v) :
    IsSol π φA φB Φ t A' B' φA' φB' Φ' h := by
  have wA : φA' ≫ A.hom = (A'.hom ≫ h) ≫ π := by rw [hA.1.w, Category.assoc, hh]
  have wB : φB' ≫ B.hom = (B'.hom ≫ h) ≫ π := by rw [hB.1.w, Category.assoc, hh]
  refine ⟨hh, pbA.1.lift _ _ wA, pbB.1.lift _ _ wB,
    pbA.cancel (hA.congr hh.symm (pbA.1.lift_fst _ _ wA).symm) (pbA.1.lift_snd _ _ wA),
    pbB.cancel (hB.congr hh.symm (pbB.1.lift_fst _ _ wB).symm) (pbB.1.lift_snd _ _ wB),
    pbA.1.lift_fst _ _ wA, pbB.1.lift_fst _ _ wB, hepi _ _ fun i => ?_⟩
  obtain ⟨-, ψA, ψB, pA, pB, eA, eB, eΦ⟩ := hs i
  obtain ⟨rA, rB, rΦ⟩ := hr i
  have hψA : ψA = ρA i ≫ pbA.1.lift _ _ wA := pbA.1.hom_ext (by rw [eA, Category.assoc, pbA.1.lift_fst])
    (by rw [pA.1.w, Category.assoc, pbA.1.lift_snd, ← Category.assoc (ρA i), rA.1.w, Category.assoc])
  have hψB : ψB = ρB i ≫ pbB.1.lift _ _ wB := pbB.1.hom_ext (by rw [eB, Category.assoc, pbB.1.lift_fst])
    (by rw [pB.1.w, Category.assoc, pbB.1.lift_snd, ← Category.assoc (ρB i), rB.1.w, Category.assoc])
  rw [← Category.assoc, ← rΦ, Category.assoc, ← hψB, eΦ, hψA, Category.assoc]

theorem lbIso_restr {XA XB A'l B'l A''l B''l : Scheme.{0}} {L : LB XA} {M : LB XB} (hL : L.IsLB) (hM : M.IsLB)
    {φA' : A'l ⟶ XA} {φB' : B'l ⟶ XB} {Φl : A'l ⟶ B'l} {ρA : A''l ⟶ A'l} {ρB : B''l ⟶ B'l} {Φ''l : A''l ⟶ B''l}
    (e : Φ''l ≫ ρB = ρA ≫ Φl) (iso : LBIso (L.pull φA') ((M.pull φB').pull Φl)) :
    LBIso (L.pull (ρA ≫ φA')) ((M.pull (ρB ≫ φB')).pull Φ''l) := by
  have hN := pull_isLB hM φB'
  have i1 : LBIso (L.pull (ρA ≫ φA')) ((M.pull φB').pull (Φ''l ≫ ρB)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp ρA rfl e iso
  have i2 : LBIso ((M.pull φB').pull (Φ''l ≫ ρB)) (((M.pull φB').pull ρB).pull Φ''l) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hN Φ''l rfl
  have i3 : LBIso (((M.pull φB').pull ρB).pull Φ''l) ((M.pull (ρB ≫ φB')).pull Φ''l) :=
    GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hM ρB rfl)) Φ''l
  exact LBIso.trans (pull_isLB hL _) (pull_isLB hN _) (pull_isLB (pull_isLB hM _) _) i1
    (LBIso.trans (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) (pull_isLB (pull_isLB hM _) _) i2 i3)

theorem rep_of_affine : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB →
  ∀ (H : Scheme.{0}) (π : H ⟶ S) (AH : Over H) [GrpObj AH] (BH : Over H) [GrpObj BH]
    (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH),
    IsGrpPullback AH A π φA → IsGrpPullback BH B π φB →
    (∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left) →
    ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  intro S A B _ _ L M hL hM H π AH _ BH _ φA φB Φ pbA pbB haff T t A' B' _ _ φA' φB' Φ' hA hB hΦ iso
  have key : ∀ (R : Type) [CommRing R] (f : Sp R ⟶ T), ∃! k : Sp R ⟶ H, IsSol π φA φB Φ (f ≫ t)
      ((Over.pullback f).obj A') ((Over.pullback f).obj B') (pullback.fst A'.hom f ≫ φA') (pullback.fst B'.hom f ≫ φB')
      ((Over.pullback f).map Φ') k := fun R _ f =>
    haff R (f ≫ t) ((Over.pullback f).obj A') ((Over.pullback f).obj B') _ _ ((Over.pullback f).map Φ')
      ((isRestr_pullback f Φ').1.comp hA) ((isRestr_pullback f Φ').2.1.comp hB) inferInstance
      (lbIso_restr hL hM (isRestr_pullback f Φ').2.2 iso)
  let 𝒜 := T.affineOpenCover
  let 𝒰 := 𝒜.openCover
  have hloc : ∀ i, ∃! k : 𝒰.X i ⟶ H, IsSol π φA φB Φ (𝒰.f i ≫ t) ((Over.pullback (𝒰.f i)).obj A')
      ((Over.pullback (𝒰.f i)).obj B') (pullback.fst A'.hom (𝒰.f i) ≫ φA') (pullback.fst B'.hom (𝒰.f i) ≫ φB')
      ((Over.pullback (𝒰.f i)).map Φ') k := fun i => key (𝒜.X i) (𝒰.f i)
  choose k hk hku using hloc
  have hagree : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ k i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ k j := by
    intro i j
    let 𝒲 := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover
    refine 𝒲.openCover.hom_ext _ _ fun l => ?_
    let g : Sp (𝒲.X l) ⟶ T := (𝒲.openCover.f l ≫ pullback.fst _ _) ≫ 𝒰.f i
    have hg : g = (𝒲.openCover.f l ≫ pullback.snd _ _) ≫ 𝒰.f j :=
      (Category.assoc _ _ _).trans ((congrArg (𝒲.openCover.f l ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    have hu := key (𝒲.X l) g
    rw [← Category.assoc, ← Category.assoc]
    exact hu.unique (IsSol.pull (isRestr_pullback _ Φ') (hk i) _ rfl (isRestr_pullback g Φ'))
      (IsSol.pull (isRestr_pullback _ Φ') (hk j) _ hg (isRestr_pullback g Φ'))
  let hg := 𝒰.glueMorphisms k hagree
  have hι : ∀ i, 𝒰.f i ≫ hg = k i := 𝒰.ι_glueMorphisms k hagree
  have hh : hg ≫ π = t := 𝒰.hom_ext _ _ fun i => by rw [← Category.assoc, hι]; exact (hk i).1
  have hsol : IsSol π φA φB Φ t A' B' φA' φB' Φ' hg :=
    isSol_of_local pbA pbB hA hB hh 𝒰.f (fun i => (Over.pullback (𝒰.f i)).obj A')
      (fun i => (Over.pullback (𝒰.f i)).obj B') (fun i => (Over.pullback (𝒰.f i)).map Φ')
      (fun i => pullback.fst A'.hom (𝒰.f i)) (fun i => pullback.fst B'.hom (𝒰.f i))
      (fun i => isRestr_pullback _ Φ') (fun i => by rw [hι]; exact hk i)
      (fun u v h => Scheme.Cover.hom_ext (Precoverage.ZeroHypercover.pullback₁ A'.hom 𝒰) u v h)
  refine ⟨hg, hsol, fun h' hs' => 𝒰.hom_ext _ _ fun i => ?_⟩
  rw [hι]
  exact hku i _ (IsSol.restr hs' (isRestr_pullback _ Φ'))

end GlobalTheory.EndLoc.HomFixGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepOfAffineTestsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homFixedPullbackRep_of_affineTests : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB →
  ∀ (H : Scheme.{0}) (π : H ⟶ S) (AH : Over H) [GrpObj AH] (BH : Over H) [GrpObj BH]
    (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH),
    IsGrpPullback AH A π φA → IsGrpPullback BH B π φB →
    (∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left) →
    ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  first | exact @GlobalTheory.EndLoc.HomFixGlue.rep_of_affine | exact GlobalTheory.EndLoc.HomFixGlue.rep_of_affine | (intros; apply GlobalTheory.EndLoc.HomFixGlue.rep_of_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedPullbackHomSchemeOfSectionBases
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixGlob


open TopologicalSpace in
theorem lc_props {Rg : Type} [CommRing Rg] [IsNoetherianRing Rg] {N : ℕ} {X H : Scheme.{0}}
    (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (i : H ⟶ X) [IsClosedImmersion c] [IsOpenImmersion i] :
    QuasiCompact (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) ∧
    IsSeparated (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) ∧
    LocallyOfFiniteType (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) := by
  refine ⟨?_, inferInstance, ?_⟩
  · have h1 : NoetherianSpace (Sp (MvPolynomial (Fin N) Rg)) :=
      inferInstanceAs (NoetherianSpace (PrimeSpectrum (MvPolynomial (Fin N) Rg)))
    have h2 : NoetherianSpace H :=
      ((i ≫ c).isEmbedding).isInducing.noetherianSpace
    exact (quasiCompact_iff_compactSpace _).2 inferInstance
  · have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      show (algebraMap Rg (MvPolynomial (Fin N) Rg)).FiniteType
      exact RingHom.finiteType_algebraMap.2 inferInstance
    infer_instance

theorem exists_homFixRep_of_secBases : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M k hA hB hL hM rA rM aL hk vM bA bB
  obtain ⟨N, X, c, H, i, AH, _, BH, _, φA, φB, Φ, hc, hi, pA, pB, hΦ, hiso, hrep⟩ :=
    GlobalTheory.T.exists_locallyClosed_represents_fixedPullback_homs Rg A B L M k hA hB hL hM rA rM aL hk vM bA bB
  obtain ⟨q1, q2, q3⟩ := lc_props c i
  exact ⟨HomFixRep.mk H (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))))
    AH BH φA φB pA pB Φ hΦ hiso (GlobalTheory.T.homFixedPullbackRep_of_affineTests _ A B L M hL hM H _ AH BH φA φB Φ pA pB hrep), q1, q2, q3⟩

end GlobalTheory.HomFixGlob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedPullbackHomSchemeOfSectionBasesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixedPullbackHomScheme_of_sectionBases : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases) | (exact GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases) | (intros; apply GlobalTheory.HomFixGlob.exists_homFixRep_of_secBases  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAtBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 TopologicalSpace

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RelAmpleFixed

theorem veryAmpleAt_baseChange : ∀ (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] [IsCommMonObj B] (M : LB B.left),
    IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∃ k : ℕ, 1 ≤ k ∧ ∀ (R' : Type) [CommRing R'] (φ : Rg →+* R')
      (B' : Over (Sp R')) [GrpObj B'] (φB : B'.left ⟶ B.left), IsGrpPullback B' B (spMap φ) φB →
      Out.VeryAmpleAt B' (M.pull φB) k := by
  intro Rg _ B _ _ L _ hL hA
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  refine ⟨N, hN, fun R' _ fr B' _ φ hg => ?_⟩
  have h : IsPullback φ B'.hom B.hom (spMap fr) := hg.1
  have hL' : (L.pull φ).IsLB := pull_isLB hL φ
  obtain ⟨w, hw'⟩ := PolBaseChange.lbIso_refl hL'
  have hw := (isGen_iff w).1 hw'
  intro U' hU'
  have le : U' ≤ (spMap fr) ⁻¹ᵁ (⊤ : (Sp Rg).Opens) := fun y _ => trivial
  have le' : B'.hom ⁻¹ᵁ U' ≤ φ ⁻¹ᵁ (B.hom ⁻¹ᵁ ⊤) := fun y _ => trivial
  let ψ := φ.resLE (B.hom ⁻¹ᵁ ⊤) (B'.hom ⁻¹ᵁ U') le'
  have hψ : ψ ≫ (B.hom ⁻¹ᵁ ⊤).ι = (B'.hom ⁻¹ᵁ U').ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  have H : IsPullback ψ (B'.hom ∣_ U') (B.hom ∣_ ⊤) ((spMap fr).resLE ⊤ U' le) := by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict B.hom ⊤).flip
    · rw [hψ, Scheme.Hom.resLE_comp_ι]
      exact (isPullback_morphismRestrict B'.hom U').flip.paste_horiz h
    · rw [← cancel_mono (⊤ : (Sp Rg).Opens).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, Category.assoc, h.w,
        Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have : IsAffine (⊤ : (Sp Rg).Opens) := isAffineOpen_top _
  have : IsAffine U' := hU'
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (B.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1)
  have hP' := linComb_isLB (L.pull φ) hL' (K := Fin N) (fun _ => (B'.hom ⁻¹ᵁ U').ι) (fun _ => 1)
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin N => (B.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) ψ _
    fun _ => hψ.symm) (iso_linComb hw (fun _ : Fin N => (B'.hom ⁻¹ᵁ U').ι) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver B' (L.pull φ) U' N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
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
  refine ⟨M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver B L ⊤ N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver B' (L.pull φ) U' N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff, ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po,
      Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map (((spMap fr).resLE ⊤ U' le).appLE ⊤ ⊤ le_top).hom p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      exact ((congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (congrArg CommRingCat.Hom.hom po.w.symm)).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end GlobalTheory.RelAmpleFixed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRepresentingSchemeHomFixedPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.HomFixLocal

theorem exists_local_homFixRep : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∀ p : Sp Rg, ∃ U : (Sp Rg).Opens, p ∈ U ∧ ∃ (AU : Over (U).toScheme) (_ : GrpObj AU) (BU : Over (U).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U).ι φA ∧ IsGrpPullback BU B (U).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M hA hB hL hM rL rM aL aM p
  obtain ⟨k, hk, hva⟩ := GlobalTheory.RelAmpleFixed.veryAmpleAt_baseChange Rg B M hB hM aM
  obtain ⟨f₁, hp₁, hb₁⟩ := GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis Rg A L hA hL rL aL k hk p
  obtain ⟨f₂, hp₂, hb₂⟩ := GlobalTheory.T.exists_basicOpen_baseChangeStable_sectionBasis Rg B M hB hM rM aM k hk p
  have le₁ : PrimeSpectrum.basicOpen (f₁ * f₂) ≤ PrimeSpectrum.basicOpen f₁ := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_left
  have le₂ : PrimeSpectrum.basicOpen (f₁ * f₂) ≤ PrimeSpectrum.basicOpen f₂ := by
    rw [PrimeSpectrum.basicOpen_mul]; exact inf_le_right
  have hp : p ∈ PrimeSpectrum.basicOpen (f₁ * f₂) := by
    rw [PrimeSpectrum.basicOpen_mul]; exact ⟨hp₁, hp₂⟩
  refine ⟨PrimeSpectrum.basicOpen (f₁ * f₂), hp, GlobalTheory.HomFixTransport.homFixRep_basicOpen Rg A B L M (f₁ * f₂) hL hM ?_ _ rfl⟩
  intro Af Bf _ _ φA φB hpA hpB
  haveI := GlobalTheory.isCommMonObj_of_grpPullback _ _ A Af _ φA hpA
  haveI := GlobalTheory.isCommMonObj_of_grpPullback _ _ B Bf _ φB hpB
  obtain ⟨hA', hL', rL', aL'⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ _ A Af φA L hpA hA hL rL aL
  obtain ⟨hB', hM', rM', -⟩ := GlobalTheory.GrpPullbackPol.isAbelianScheme_and_pull_of_isGrpPullback _ _ _ B Bf φB M hpB hB hM rM aM
  exact GlobalTheory.T.exists_fixedPullbackHomScheme_of_sectionBases (Localization.Away (f₁ * f₂)) Af Bf (L.pull φA) (M.pull φB) k hA' hB' hL' hM' rL' rM' aL' hk
    (hva _ _ Bf φB hpB) (hb₁ _ le₁ Af φA hpA) (hb₂ _ le₂ Bf φB hpB)

end GlobalTheory.HomFixLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRepresentingSchemeHomFixedPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_representing_scheme_homFixedPullback : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∀ p : Sp Rg, ∃ U : (Sp Rg).Opens, p ∈ U ∧ ∃ (AU : Over (U).toScheme) (_ : GrpObj AU) (BU : Over (U).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U).ι φA ∧ IsGrpPullback BU B (U).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixLocal.exists_local_homFixRep) | (exact GlobalTheory.HomFixLocal.exists_local_homFixRep) | (intros; apply GlobalTheory.HomFixLocal.exists_local_homFixRep  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlueOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlueOpenCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem homFixRep_glue_opens : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (J : Type) (U : J → S.Opens), (∀ p : S, ∃ i, p ∈ U i) → (∀ i, ∃ (AU : Over (U i).toScheme) (_ : GrpObj AU) (BU : Over (U i).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U i).ι φA ∧ IsGrpPullback BU B (U i).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB J U hU hloc
  refine GlobalTheory.T.homFixedPullback_representable_glue (fun H A B _ _ _ _ L M Φ hΦ hA hB hL hM rA rB h => GlobalTheory.HomFixLocal.lbIso_pull_of_local H A B L M Φ hΦ hA hB hL hM rA rB h) S A B L M hA hB hL hM rA rB J (fun i => (U i).toScheme) (fun i => (U i).ι) (fun i => inferInstance) (fun s => ?_) (fun i => ?_)
  · obtain ⟨i, hi⟩ := hU s; exact ⟨i, by simpa [Scheme.Opens.range_ι] using hi⟩
  · obtain ⟨AU, gA, BU, gB, φA, φB, pA, pB, R, h1, h2, h3⟩ := hloc i; exact ⟨AU, BU, gA, gB, φA, φB, R, pA, pB, h1, h2, h3⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlueOpenCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homFixedPullbackRepresentable_glue_openCover : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (J : Type) (U : J → S.Opens), (∀ p : S, ∃ i, p ∈ U i) → (∀ i, ∃ (AU : Over (U i).toScheme) (_ : GrpObj AU) (BU : Over (U i).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U i).ι φA ∧ IsGrpPullback BU B (U i).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | exact @GlobalTheory.homFixRep_glue_opens | exact GlobalTheory.homFixRep_glue_opens | (intros; apply GlobalTheory.homFixRep_glue_opens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSchemeRepresentingPolarizedHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomFixAff

theorem exists_homFixRep_finiteType : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M hA hB hL hM rL rM aL aM
  have h := fun p => GlobalTheory.T.exists_local_representing_scheme_homFixedPullback Rg A B L M hA hB hL hM rL rM aL aM p
  choose U hpU hdat using h
  exact GlobalTheory.T.homFixedPullbackRepresentable_glue_openCover (Sp Rg) A B L M hA hB hL hM rL rM (Sp Rg) U (fun p => ⟨p, hpU p⟩) hdat

end GlobalTheory.HomFixAff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSchemeRepresentingPolarizedHomsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_scheme_representing_polarizedHoms : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixAff.exists_homFixRep_finiteType) | (exact GlobalTheory.HomFixAff.exists_homFixRep_finiteType) | (intros; apply GlobalTheory.HomFixAff.exists_homFixRep_finiteType  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeRestrictOpenImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeRestrictOpenImmersion
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.OpenRestrictPol

theorem exists_restrict_open : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left),
    IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ (V : Scheme.{0}) (j : V ⟶ S),
    IsOpenImmersion j → ∃ (A' : Over V) (_ : GrpObj A') (_ : IsCommMonObj A') (φ : A'.left ⟶ A.left),
    IsGrpPullback A' A j φ ∧ IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧
    Out.RelAmple A' (L.pull φ) := by
  intro S A _ _ L hA hL hr hamp V j _
  have hpb := isGrpPullback_pullback A j
  have := hA.proper
  exact ⟨(Over.pullback j).obj A, inferInstance, GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hpb,
    pullback.fst A.hom j, hpb, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb, pull_isLB hL _,
    GlobalTheory.PolBaseChange.rigidified_pull hpb hr, GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp hpb.1⟩

end GlobalTheory.OpenRestrictPol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeRestrictOpenImmersionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianScheme_restrict_openImmersion : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ (V : Scheme.{0}) (j : V ⟶ S), IsOpenImmersion j → ∃ (A' : Over V) (_ : GrpObj A') (_ : IsCommMonObj A') (φ : A'.left ⟶ A.left), IsGrpPullback A' A j φ ∧ IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧ Out.RelAmple A' (L.pull φ) := by
  first | exact @GlobalTheory.OpenRestrictPol.exists_restrict_open | exact GlobalTheory.OpenRestrictPol.exists_restrict_open | (intros; apply GlobalTheory.OpenRestrictPol.exists_restrict_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeRepresentingPolarizedHomsLocNoet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomFixGlue

theorem homFix_finiteType : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB aA aB
  refine GlobalTheory.T.homFixedPullback_representable_glue GlobalTheory.T.rigidifiedBundle_pullbackIso_of_localIso_abelianHom S A B L M hA hB hL hM rA rB S.affineOpens (fun U => Sp Γ(S, U)) (fun U => U.2.fromSpec)
    (fun U => IsAffineOpen.isOpenImmersion_fromSpec U.2) ?_ ?_
  · intro s
    obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hU.range_fromSpec.ge hs⟩
  · intro U
    haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨A', _, _, φA, gA, hA', hL', rA', aA'⟩ := GlobalTheory.T.exists_abelianScheme_restrict_openImmersion S A L hA hL rA aA _ U.2.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec U.2)
    obtain ⟨B', _, _, φB, gB, hB', hM', rB', aB'⟩ := GlobalTheory.T.exists_abelianScheme_restrict_openImmersion S B M hB hM rB aB _ U.2.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec U.2)
    obtain ⟨R, h1, h2, h3⟩ := GlobalTheory.T.exists_finiteType_scheme_representing_polarizedHoms Γ(S, U) A' B' (L.pull φA) (M.pull φB) hA' hB' hL' hM' rA' rB' aA' aB'
    exact ⟨A', B', _, _, φA, φB, R, gA, gB, h1, h2, h3⟩

end GlobalTheory.HomFixGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeRepresentingPolarizedHomsLocNoetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_representing_polarizedHoms_locNoeth : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixGlue.homFix_finiteType) | (exact GlobalTheory.HomFixGlue.homFix_finiteType) | (intros; apply GlobalTheory.HomFixGlue.homFix_finiteType  <;> assumption)
end
