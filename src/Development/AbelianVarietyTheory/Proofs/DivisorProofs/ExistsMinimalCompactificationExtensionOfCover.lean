module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameChart
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem isFrame_chart (h : IsGrpPullback H G x ψ) (j : PUnit → (hodge G g).ι) :
    IsFrame fun i => (omegaBase h).app (LB.wchart (hodge G g) (fun _ => x) j)
      (pullbackSections x (omega G) (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit) ((j PUnit.unit).e i)) :=
  (GlobalTheory.BadPt.Fibre.frame_pb x (j PUnit.unit).isFrame _).map_iso (omegaBase h)

def gen (h : IsGrpPullback H G x ψ) {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) : LB.Gen ((hodge G g).pull x) where
  s j := (isFrame_chart h j).detUnit ha le_rfl le_top

end GlobalTheory.HodgeFrameGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHodgeBundleGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitPullbackSemiAbelianModelIdentification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitPullbackSemiAbelianModelIdentification
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

theorem GlobalTheory.HodgeFrameGen.traitPullback_identification : ∀ {S' : Scheme.{0}} {G : Over S'} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ {R : Type} [CommRing R] [IsDomain R] {G₁ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ →
    ∀ {y : Sp (FractionRing R) ⟶ S'} {α : pullback G₁.hom (jK R) ⟶ G.left},
    IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α →
    ∀ {W : Type} [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsIntegrallyClosed W] (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
    ∀ (χ' : Sp W ⟶ S'), spMap gam ≫ y = jK W ≫ χ' →
    ∃ (ρ' : ((Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁)).left ⟶
        ((Over.pullback (spMap φ)).obj G₁).left) (ψ' : ((Over.pullback (spMap φ)).obj G₁).left ⟶ G.left),
      IsGrpPullback ((Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁))
        ((Over.pullback (spMap φ)).obj G₁) (jK W) ρ' ∧
      IsGrpPullback ((Over.pullback (spMap φ)).obj G₁) G χ' ψ' ∧
      ρ' ≫ ψ' = pullback.fst _ _ ≫ α ∧
      ρ' ≫ pullback.fst G₁.hom (spMap φ) = pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R) := by
  intro S' G _ _ hG R _ _ G₁ _ _ hG₁ y α hα W _ _ _ _ φ gam hgam χ' hχ
  have hsq : spMap gam ≫ jK R = jK W ≫ spMap φ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact hgam r
  let A := (Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁)
  let G₁W := (Over.pullback (spMap φ)).obj G₁
  have hA : IsGrpPullback A ((Over.pullback (jK R)).obj G₁) (spMap gam) (pullback.fst _ _) :=
    isGrpPullback_pullback _ _
  have hAG₁ : IsGrpPullback A G₁ (jK W ≫ spMap φ)
      ((pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R))) :=
    (hA.comp (isGrpPullback_pullback G₁ (jK R))).congr hsq rfl
  have hw : (pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R)) ≫ G₁.hom = (A.hom ≫ jK W) ≫ spMap φ := by
    rw [hAG₁.1.w]; simp [Category.assoc]
  let ρ' : A.left ⟶ G₁W.left := pullback.lift (pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R)) (A.hom ≫ jK W) hw
  have hρfst : ρ' ≫ pullback.fst G₁.hom (spMap φ) = pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R) :=
    pullback.lift_fst _ _ _
  have hρ : IsGrpPullback A G₁W (jK W) ρ' :=
    (isGrpPullback_pullback G₁ (spMap φ)).cancel (hAG₁.congr rfl hρfst.symm) (pullback.lift_snd _ _ _)
  have hG₁W : IsSemiAbelian G₁W := IsSemiAbelian.pullback (spMap φ) G₁ hG₁
  obtain ⟨ψ', hψ, hc⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map W y ((Over.pullback (jK R)).obj G₁) G α hG hα
    G₁W hG₁W χ' (spMap gam) hχ A ρ' (pullback.fst _ _) hρ hA
  exact ⟨ρ', ψ', hρ, hψ, hc, hρfst⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitPullbackSemiAbelianModelIdentificationStatement
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitPullback_semiAbelianModel_identification : ∀ {S' : Scheme.{0}} {G : Over S'} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ {R : Type} [CommRing R] [IsDomain R] {G₁ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ →
    ∀ {y : Sp (FractionRing R) ⟶ S'} {α : pullback G₁.hom (jK R) ⟶ G.left},
    IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α →
    ∀ {W : Type} [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsIntegrallyClosed W] (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
    ∀ (χ' : Sp W ⟶ S'), spMap gam ≫ y = jK W ≫ χ' →
    ∃ (ρ' : ((Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁)).left ⟶
        ((Over.pullback (spMap φ)).obj G₁).left) (ψ' : ((Over.pullback (spMap φ)).obj G₁).left ⟶ G.left),
      IsGrpPullback ((Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁))
        ((Over.pullback (spMap φ)).obj G₁) (jK W) ρ' ∧
      IsGrpPullback ((Over.pullback (spMap φ)).obj G₁) G χ' ψ' ∧
      ρ' ≫ ψ' = pullback.fst _ _ ≫ α ∧
      ρ' ≫ pullback.fst G₁.hom (spMap φ) = pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R) := by
  first | exact @GlobalTheory.HodgeFrameGen.traitPullback_identification | exact GlobalTheory.HodgeFrameGen.traitPullback_identification | (intros; apply GlobalTheory.HodgeFrameGen.traitPullback_identification <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePullbackGenOfFrameIsGen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePullbackGenOfFrameIsGen
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

variable {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
  {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ}

theorem pulled_back_lineBundle_transition_unit_eq_restriction {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j j' : PUnit.{1} → L.ι) :
    (L.pull f).g j j' = res (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ => f) j' PUnit.unit)))
      (pullU f _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
  have e : ∀ u : Γ(Y, L.wchart (fun _ => f) j ⊓ L.wchart (fun _ => f) j')ˣ, (∏ _k : PUnit.{1}, u ^ (1 : ℤ)) = u :=
    fun u => by simp
  exact e _

theorem pull_g_eq (h : IsGrpPullback H G x ψ) (j j' : ((hodge G g).pull x).ι) :
    ((hodge G g).pull x).g j j' =
      (isFrame_chart h j).detUnit (isFrame_chart h j') inf_le_left inf_le_right := by
  have frame_pb {X Y : Scheme.{0}} {I : Type} [Fintype I] (f : Y ⟶ X)
      {F : X.Modules} [F.IsQuasicoherent] {U : X.Opens} {e : I → Γ(F, U)} (he : IsFrame e)
      {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) : IsFrame fun i => pullbackSections f F h (e i) := by
    have k := (he.pullback f).res h
    exact (funext fun l => QCoh.res_pullbackSections f F le_rfl h (e l)) ▸ k
  have e₁ := IsFrame.detUnit_map_iso
    (frame_pb x (j PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
    (frame_pb x (j' PUnit.unit).isFrame (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
    (omegaBase h) (inf_le_left : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤ _)
    inf_le_right
  refine Eq.trans ?_ e₁.symm
  have hT : LB.wchart (hodge G g) (fun _ => x) j ⊓ LB.wchart (hodge G g) (fun _ => x) j' ≤
      x ⁻¹ᵁ ((j PUnit.unit).U ⊓ (j' PUnit.unit).U) :=
    le_inf (inf_le_left.trans (LB.wchart_le (hodge G g) (fun _ => x) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le (hodge G g) (fun _ => x) j' PUnit.unit))
  refine Eq.trans ?_ (GlobalTheory.Vert.DivPull.detUnit_congr _ _ ((j PUnit.unit).isFrame.pullback x)
    ((j' PUnit.unit).isFrame.pullback x) _ _ (hT.trans (x.preimage_mono inf_le_left))
    (hT.trans (x.preimage_mono inf_le_right))
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)
    (fun i => (QCoh.res_pullbackSections _ _ _ _ _).trans (QCoh.res_pullbackSections _ _ _ _ _).symm)).symm
  refine Units.ext ?_
  refine (congrArg Units.val (pulled_back_lineBundle_transition_unit_eq_restriction (hodge G g) x j j')).trans (Eq.trans ?_
    (IsFrame.val_detUnit_pullback (j PUnit.unit).isFrame (j' PUnit.unit).isFrame x inf_le_left inf_le_right hT).symm)
  rfl

theorem gen_isGen : ∀ {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a), (gen h ha).IsGen := by
  intro S' T G _ H _ x ψ _ g h a ha j j'
  refine (IsFrame.res_detUnit _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (pull_g_eq h j j').symm (IsFrame.res_detUnit _ _ _ _ _).symm)
  exact (IsFrame.detUnit_mul _ _ _ _ _ _).symm

end GlobalTheory.HodgeFrameGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundlePullbackGenOfFrameIsGenStatement
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen : ∀ {S' T : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a), (gen h ha).IsGen := by
  first | exact @GlobalTheory.HodgeFrameGen.gen_isGen | exact GlobalTheory.HodgeFrameGen.gen_isGen | (intros; apply GlobalTheory.HodgeFrameGen.gen_isGen <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGeneratorValuePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGeneratorValuePullback
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

theorem gm_eq_of_appLE {T Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) {U : T.Opens} {W : Z.Opens} (hW : W ≤ r ⁻¹ᵁ U)
    (hz : z ∈ W) (u : Γ(T, U)ˣ) (v : Γ(Z, W)ˣ) (e : v.val = (r.appLE U W hW).hom u.val) :
    gm r z U u = gm (𝟙 Z) z W v := by
  refine Units.ext ?_
  rw [gm_val r z U (hW hz), gm_val (𝟙 Z) z W hz, e]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE hW) z hz _).symm

theorem val_gen_pull : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  intro S' T Z G _ H _ x ψ _ g h a ha r B _ ρ q x' ψ' h' e e' b hb hab z J hJ
  have : QuasiSeparated H.hom := MorphismProperty.of_isPullback h.1 ‹_›
  rw [val_of (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J (fun _ => J x')
      (fun _ => by rw [e]),
    val_of (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J (fun _ => J x')
      (fun _ => by rw [Category.id_comp])]
  have hW : LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') ≤
      r ⁻¹ᵁ LB.wchart (hodge G g) (fun _ : PUnit => x) (fun _ => J x') := fun y hy =>
    Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy k
      rw [← e] at this ⊢
      exact this
  have hz : z ∈ LB.wchart (hodge G g) (fun _ : PUnit => x') (fun _ => J x') := Set.mem_iInter.2 fun _ => hJ x'
  have k {U : T.Opens} {V W : Z.Opens} (hV : V ≤ r ⁻¹ᵁ U) (h₁ : W ≤ V) (s : Γ(omega H, U)) :
      GlobalTheory.Twist.resM _ h₁ ((omegaBase q).app V (pullbackSections r _ hV s)) =
        (omegaBase q).app W (pullbackSections r _ (h₁.trans hV) s) := by
    rw [← GlobalTheory.QCoh.res_pullbackSections r _ hV h₁ s]
    exact congr($((omegaBase q).mapPresheaf.naturality (homOfLE h₁).op) (pullbackSections r _ hV s)).symm
  refine gm_eq_of_appLE r z hW hz _ _ ?_
  have hc := isFrame_chart h (fun _ => J x')
  refine Eq.trans ?_ (hc.val_detUnit_pullback ha r le_rfl le_top hW)
  refine congrArg Units.val ?_
  refine Eq.trans ?_ (IsFrame.detUnit_map_iso _ _ (omegaBase q) _ _)
  refine GlobalTheory.Vert.DivPull.detUnit_congr _ _ _ _ _ _ _ _ (fun i => ?_) (fun i => ?_)
  · refine Eq.trans (GlobalTheory.Twist.resM_self _ _) (Eq.trans ?_ (k _ _ _).symm)
    exact (GlobalTheory.BadPt.Fibre.omegaBase_comp h q h' e e' _ _ _ _).symm
  · rw [hab]
    exact (k _ _ _).trans (k _ _ _).symm

end GlobalTheory.HodgeFrameGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGeneratorValuePullbackStatement
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_frame_generator_value_pullback : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  first | exact @GlobalTheory.HodgeFrameGen.val_gen_pull | exact GlobalTheory.HodgeFrameGen.val_gen_pull | (intros; apply GlobalTheory.HodgeFrameGen.val_gen_pull <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHodgeBundleGenerator
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeFrameGen

theorem exists_isFrame_top_of_isLocalRing (R : Type) [CommRing R] [IsLocalRing R] (F : (Sp R).Modules) {r : ℕ}
    (h : IsVB F r) : ∃ e : Fin r → Γ(F, ⊤), IsFrame e := by
  obtain ⟨U, e, hx, he⟩ := h (IsLocalRing.closedPoint R)
  have hU : U = ⊤ := by
    refine top_le_iff.1 fun p _ => ?_
    exact (IsLocalRing.specializes_closedPoint p).mem_open U.isOpen hx
  subst hU
  exact ⟨e, he⟩

theorem spMap_jK {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W) (hgam : ∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) :
    spMap gam ≫ jK R = jK W ≫ spMap φ := by
  have e : gam.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    RingHom.ext hgam
  simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem relDim {S' : Scheme.{0}} {g : ℕ} {G : Over S'} [GrpObj G] (hGg : SmoothOfRelativeDimension g G.hom)
    {R : Type} [CommRing R] [IsDomain R] {G₁ : Over (Sp R)} [GrpObj G₁] (hG₁ : IsSemiAbelian G₁)
    {y : Sp (FractionRing R) ⟶ S'} {α : pullback G₁.hom (jK R) ⟶ G.left}
    (hα : IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α) : SmoothOfRelativeDimension g G₁.hom := by
  have := hG₁.smooth
  have h₁ : SmoothOfRelativeDimension g ((Over.pullback (jK R)).obj G₁).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hα.1 hGg
  exact GlobalTheory.SmoothRelDim.smoothOfRelativeDimension_of_generic R G₁ (FractionRing R)
    (algebraMap R (FractionRing R)) (IsFractionRing.injective R (FractionRing R)) g h₁

theorem exists_integral_hodgeGen : ∀ (S' : Scheme.{0}) (g : ℕ) (G : Over S') [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → ∃ e₀ : LB.Gen ((hodge G g).pull y), e₀.IsGen ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∀ χ' : Sp W ⟶ S', spMap gam ≫ y = jK W ≫ χ' → ∃ e₀' : LB.Gen ((hodge G g).pull χ'), e₀'.IsGen ∧ ∀ (z : Sp (FractionRing W)) (J : (Sp (FractionRing W) ⟶ S') → (hodge G g).ι), Good (hodge G g) z J → val (L := hodge G g) (φ := fun _ : PUnit => y) (ε := fun _ => 1) e₀ (spMap gam) z J = val (L := hodge G g) (φ := fun _ : PUnit => χ') (ε := fun _ => 1) e₀' (jK W) z J := by
  intro S' g G _ _ hG hGg R _ _ _ _ _ G₁ _ _ hG₁ y α hα
  haveI := hG; haveI := hG₁
  haveI : SmoothOfRelativeDimension g G₁.hom := relDim hGg hG₁ hα
  obtain ⟨ε, hε⟩ := exists_isFrame_top_of_isLocalRing R (omega G₁) (isVB_omega G₁ g)
  have p₁ := isGrpPullback_pullback G₁ (jK R)
  have ha : IsFrame fun i => (omegaBase p₁).app ⊤ (pullbackSections (jK R) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb (jK R) hε le_top).map_iso _
  refine ⟨gen hα ha, GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen hα ha, ?_⟩
  intro W _ _ _ hW φ gam hgam χ' hχ
  haveI : IsDiscreteValuationRing W := hW.1
  obtain ⟨ρ', ψ', hρ', hψ', e₁, e₂⟩ := GlobalTheory.T.traitPullback_semiAbelianModel_identification hG hG₁ hα φ gam hgam χ' hχ
  have pW := isGrpPullback_pullback G₁ (spMap φ)
  have ha' : IsFrame fun i => (omegaBase pW).app ⊤ (pullbackSections (spMap φ) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb (spMap φ) hε le_top).map_iso _
  refine ⟨gen hψ' ha', GlobalTheory.T.hodgeBundlePullbackGenOfFrame_isGen hψ' ha', fun z J hJ => ?_⟩
  have q := isGrpPullback_pullback ((Over.pullback (jK R)).obj G₁) (spMap gam)
  have hA := q.comp hα
  have hq₁ := q.comp p₁
  have hb : IsFrame fun i => (omegaBase hq₁).app ⊤ (pullbackSections (spMap gam ≫ jK R) _ le_top (ε i)) :=
    (GlobalTheory.BadPt.Fibre.frame_pb _ hε le_top).map_iso _
  refine (GlobalTheory.T.hodge_frame_generator_value_pullback hα ha (spMap gam) q _ _ hA rfl rfl hb (fun i => ?_) z J hJ).trans
    (GlobalTheory.T.hodge_frame_generator_value_pullback hψ' ha' (jK W) hρ' _ _ hA hχ.symm e₁ hb (fun i => ?_) z J hJ).symm
  · exact (GlobalTheory.BadPt.Fibre.omegaBase_comp p₁ q hq₁ rfl rfl le_top le_top le_top (ε i)).symm
  · exact (GlobalTheory.BadPt.Fibre.omegaBase_comp pW hρ' hq₁ (spMap_jK φ gam hgam).symm e₂ le_top le_top le_top (ε i)).symm

end GlobalTheory.HodgeFrameGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralHodgeBundleGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_hodgeBundle_generator : ∀ (S' : Scheme.{0}) (g : ℕ) (G : Over S') [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → ∃ e₀ : LB.Gen ((hodge G g).pull y), e₀.IsGen ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) → ∀ χ' : Sp W ⟶ S', spMap gam ≫ y = jK W ≫ χ' → ∃ e₀' : LB.Gen ((hodge G g).pull χ'), e₀'.IsGen ∧ ∀ (z : Sp (FractionRing W)) (J : (Sp (FractionRing W) ⟶ S') → (hodge G g).ι), Good (hodge G g) z J → val (L := hodge G g) (φ := fun _ : PUnit => y) (ε := fun _ => 1) e₀ (spMap gam) z J = val (L := hodge G g) (φ := fun _ : PUnit => χ') (ε := fun _ => 1) e₀' (jK W) z J := by
  first | exact @GlobalTheory.HodgeFrameGen.exists_integral_hodgeGen | exact GlobalTheory.HodgeFrameGen.exists_integral_hodgeGen | (intros; apply GlobalTheory.HodgeFrameGen.exists_integral_hodgeGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportGeneratorLbPowToAmpleBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportGeneratorLbPowToAmpleBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenTransport

variable {S' Z : Scheme.{0}} {π : S' ⟶ Z} {M : LB Z} {L : LB S'} {N : ℕ}

theorem w_trans (w : LB.Iso (M.pull π) (lbPow L N)) (hw : w.IsGen) {Y : Scheme.{0}} (f : Y ⟶ S') (y : Y)
    (i i' : L.ι) (k k' : M.ι) (hi : f y ∈ L.U i) (hi' : f y ∈ L.U i') (hk : (f ≫ π) y ∈ M.U k)
    (hk' : (f ≫ π) y ∈ M.U k') :
    gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) (w.s (fun _ => i, fun _ => k)) =
      gm f y (L.U i ⊓ L.U i') (L.g i i') ^ (N : ℤ) * (gm (f ≫ π) y (M.U k ⊓ M.U k') (M.g k k'))⁻¹ *
        gm f y ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) (w.s (fun _ => i', fun _ => k')) := by
  have m1 : f y ∈ (lbPow L N).U (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have m1' : f y ∈ (lbPow L N).U (fun _ => i') := Set.mem_iInter.2 fun _ => hi'
  have m2 : f y ∈ (M.pull π).U (fun _ => k) := Set.mem_iInter.2 fun _ => hk
  have m2' : f y ∈ (M.pull π).U (fun _ => k') := Set.mem_iInter.2 fun _ => hk'
  have hm : f y ∈ (lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) := ⟨⟨m1, m2⟩, ⟨m1', m2'⟩⟩
  have e := congrArg (gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')))) (hw (fun _ => i, fun _ => k) (fun _ => i', fun _ => k'))
  have e1 : gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) (w.s (fun _ => i, fun _ => k)) =
      gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k'))) (res inf_le_left (w.s (fun _ => i, fun _ => k))) :=
    (gm_res f y _ hm _).symm
  have e2 : gm f y ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k) ⊓
      ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k'))) (res inf_le_right (w.s (fun _ => i', fun _ => k'))) =
      gm f y ((lbPow L N).U (fun _ => i') ⊓ (M.pull π).U (fun _ => k')) (w.s (fun _ => i', fun _ => k')) :=
    gm_res f y _ hm _
  have e3 := gm_div (M.pull π) (lbPow L N) f y (fun _ => i, fun _ => k) (fun _ => i', fun _ => k') hm
  refine e1.trans (e.trans ((MonoidHom.map_mul _ _ _).trans (congrArg₂ (· * ·) (e3.trans ?_) e2)))
  exact congrArg₂ (fun a b => a * b⁻¹)
    ((gm_linComb L (fun _ => 𝟙 S') (fun _ => (N : ℤ)) f y (fun _ => i) (fun _ => i') m1 m1').trans
      (by rw [Fintype.prod_unique, Category.comp_id]))
    (gm_pull_g M π f y (fun _ => k) (fun _ => k') m2 m2')

theorem alg₁ {G : Type*} [CommGroup G] (t E W : G) (N : ℕ) :
    (t * E) ^ N * (t ^ (N : ℤ) * 1⁻¹ * W)⁻¹ = E ^ N * W⁻¹ := by
  rw [zpow_natCast, inv_one, _root_.mul_one, _root_.mul_pow, _root_.mul_inv, _root_.mul_comm (t ^ N),
    _root_.mul_assoc, mul_inv_cancel_left]

theorem alg₂ {G : Type*} [CommGroup G] (E g W : G) (N : ℕ) :
    E ^ N * ((1 : G) ^ (N : ℤ) * g⁻¹ * W)⁻¹ = g * (E ^ N * W⁻¹) := by
  rw [one_zpow, _root_.one_mul, _root_.mul_inv, inv_inv, _root_.mul_left_comm]

theorem exists_strictHenselian_absolutely_closed_local_ring (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso (M.pull π) (lbPow L N)) (hw : w.IsGen)
    {A : Scheme.{0}} (a : A ⟶ S') (e : LB.Gen (L.pull a)) (he : e.IsGen) :
    ∃ t : LB.Gen (M.pull (a ≫ π)), t.IsGen ∧ ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y) (i : L.ι) (k : M.ι),
      (r ≫ a) z ∈ L.U i → (r ≫ a ≫ π) z ∈ M.U k →
      gm r z ((M.pull (a ≫ π)).U (fun _ => k)) (t.s (fun _ => k)) =
        gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
  have loc : ∀ k : M.ι, ∃ s : Γ(A, (M.pull (a ≫ π)).U (fun _ => k))ˣ, ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y)
      (i : L.ι), (r ≫ a) z ∈ L.U i → (r ≫ a ≫ π) z ∈ M.U k →
      gm r z _ s = gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
    intro k
    let V := (M.pull (a ≫ π)).U (fun _ => k)
    let W : L.ι → A.Opens := fun i => V ⊓ (L.pull a).U (fun _ => i)
    have h1 : ∀ i, W i ≤ (L.pull a).U (fun _ => i) := fun i => inf_le_right
    have h2 : ∀ i, W i ≤ a ⁻¹ᵁ ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k)) := fun i x hx =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.2 (), Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx.1 ()⟩
    let u : ∀ i, Γ(A, W i)ˣ := fun i =>
      res (h1 i) (e.s (fun _ => i)) ^ N * (res (h2 i) (pullU a _ (w.s (fun _ => i, fun _ => k))))⁻¹
    have hu : ∀ (Y : Scheme.{0}) (r : Y ⟶ A) (z : Y) (i : L.ι), r z ∈ W i →
        gm r z (W i) (u i) = gm r z ((L.pull a).U (fun _ => i)) (e.s (fun _ => i)) ^ N *
          (gm (r ≫ a) z ((lbPow L N).U (fun _ => i) ⊓ (M.pull π).U (fun _ => k))
            (w.s (fun _ => i, fun _ => k)))⁻¹ := by
      intro Y r z i hz
      simp only [u, map_mul, map_pow, map_inv]
      exact congrArg₂ (fun p q => p ^ N * q⁻¹) (gm_res r z (h1 i) hz _)
        ((gm_res r z (h2 i) hz _).trans (gm_pull r a z _ (h2 i hz) _))
    obtain ⟨s, hs⟩ := glue_unit V W (fun i => inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL (a x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, Set.mem_iInter.2 fun _ => hi⟩) u
      (fun i j x hx => by
        have hi : (𝟙 A ≫ a) x ∈ L.U i := Set.mem_iInter.1 hx.1.2 ()
        have hj : (𝟙 A ≫ a) x ∈ L.U j := Set.mem_iInter.1 hx.2.2 ()
        have hk : ((𝟙 A ≫ a) ≫ π) x ∈ M.U k := Set.mem_iInter.1 hx.1.1 ()
        have g1 : gm (𝟙 A) x ((L.pull a).U fun _ => i) (e.s fun _ => i) =
            trF (fun _ : PUnit => a) (fun _ => 1) (𝟙 A) x (fun _ => i) (fun _ => j) *
              gm (𝟙 A) x ((L.pull a).U fun _ => j) (e.s fun _ => j) := gen_trans he (𝟙 A) x hx.1.2 hx.2.2
        rw [hu A (𝟙 A) x i hx.1, hu A (𝟙 A) x j hx.2, g1,
          w_trans w hw (𝟙 A ≫ a) x i j k k hi hj hk hk, gm_self hM _ x hk]
        simp only [trF, Fintype.prod_unique, zpow_one]
        exact alg₁ _ _ _ N)
    refine ⟨s, fun Y r z i hi hk => ?_⟩
    have hz : r z ∈ W i := ⟨Set.mem_iInter.2 fun _ => hk, Set.mem_iInter.2 fun _ => hi⟩
    rw [← gm_res r z (inf_le_left : W i ≤ V) hz, hs i, hu Y r z i hz]
  choose s hs using loc
  refine ⟨⟨fun k => s (k ())⟩, fun k k' => unit_ext fun x hx => ?_, fun Y r z i k hi hk => hs k Y r z i hi hk⟩
  refine (gm_res (𝟙 A) x _ hx _).trans (Eq.trans ?_ ((MonoidHom.map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_pull_g M (a ≫ π) (𝟙 A) x k k' hx.1 hx.2) (gm_res (𝟙 A) x _ hx _))).symm)
  obtain ⟨i, hi⟩ := exists_chart hL ((𝟙 A ≫ a) x)
  have hk : ((𝟙 A ≫ a) ≫ π) x ∈ M.U (k ()) := Set.mem_iInter.1 hx.1 ()
  have hk' : ((𝟙 A ≫ a) ≫ π) x ∈ M.U (k' ()) := Set.mem_iInter.1 hx.2 ()
  have v1 : gm (𝟙 A) x ((M.pull (a ≫ π)).U k) (s (k ())) = _ := hs (k ()) A (𝟙 A) x i hi hk
  have v2 : gm (𝟙 A) x ((M.pull (a ≫ π)).U k') (s (k' ())) = _ := hs (k' ()) A (𝟙 A) x i hi hk'
  rw [v1, v2, w_trans w hw (𝟙 A ≫ a) x i i (k ()) (k' ()) hi hi hk hk', gm_self hL (𝟙 A ≫ a) x hi, Category.assoc]
  exact alg₂ _ _ _ N

theorem transport : ∀ (S' Z : Scheme.{0}) (π : S' ⟶ Z) (M : LB Z) (L : LB S') (N : ℕ), M.IsLB → L.IsLB → LBIso (M.pull π) (lbPow L N) → ∃ T : ∀ (A : Scheme.{0}) (a : A ⟶ S'), LB.Gen (L.pull a) → LB.Gen (M.pull (a ≫ π)), (∀ (A : Scheme.{0}) (a : A ⟶ S') (e : LB.Gen (L.pull a)), e.IsGen → (T A a e).IsGen) ∧ ∀ (A A' Y : Scheme.{0}) (a : A ⟶ S') (a' : A' ⟶ S') (e : LB.Gen (L.pull a)) (e' : LB.Gen (L.pull a')) (r : Y ⟶ A) (r' : Y ⟶ A'), e.IsGen → e'.IsGen → r ≫ a = r' ≫ a' → (∀ (z : Y) (J : (Y ⟶ S') → L.ι), Good L z J → val (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z J = val (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z J) → ∀ (z : Y) (J : (Y ⟶ Z) → M.ι), Good M z J → val (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) (T A a e) r z J = val (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) (T A' a' e') r' z J := by
  intro S' Z π M L N hM hL hw0
  obtain ⟨w, hw⟩ := hw0
  classical
  refine ⟨fun A a e => if he : e.IsGen then (exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose else ⟨fun _ => 1⟩,
    fun A a e he => ?_, ?_⟩
  · simp only [dite_eq_left he]
    exact (exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose_spec.1
  · intro A A' Y a a' e e' r r' he he' hr hval z J hJ
    simp only [dite_eq_left he, dite_eq_left he']
    have hk : (r ≫ a ≫ π) z ∈ M.U (J (r ≫ a ≫ π)) := hJ _
    have hk'e : J (r' ≫ a' ≫ π) = J (r ≫ a ≫ π) := by rw [← Category.assoc, ← hr, Category.assoc]
    have hk' : (r' ≫ a' ≫ π) z ∈ M.U (J (r ≫ a ≫ π)) := hk'e ▸ hJ _
    obtain ⟨i, hi⟩ := exists_chart hL ((r ≫ a) z)
    have hi' : (r' ≫ a') z ∈ L.U i := by rw [← hr]; exact hi
    obtain ⟨JL, hJL, eJL⟩ := exists_good L hL z (K := PUnit) (fun _ => r ≫ a) (fun _ => i)
      (fun _ _ _ => rfl) (fun _ => hi)
    have v1 := val_of (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z JL (fun _ => i) (fun _ => eJL ())
    have v2 := val_of (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z JL (fun _ => i)
      (fun _ => by rw [← hr]; exact eJL ())
    have hv := hval z JL hJL
    rw [v1, v2] at hv
    rw [val_of (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) _ r z J (fun _ => J (r ≫ a ≫ π))
        (fun _ => rfl),
      val_of (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) _ r' z J (fun _ => J (r ≫ a ≫ π))
        (fun _ => hk'e)]
    refine (((exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a e he).choose_spec.2 Y r z i _ hi hk).trans ?_).trans
      ((exists_strictHenselian_absolutely_closed_local_ring hL hM w hw a' e' he').choose_spec.2 Y r' z i _ hi' hk').symm
    rw [hr]
    congr 1
    exact congrArg (· ^ N) hv

end GlobalTheory.GenTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportGeneratorLbPowToAmpleBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transport_generator_lbPow_to_ampleBundle : ∀ (S' Z : Scheme.{0}) (π : S' ⟶ Z) (M : LB Z) (L : LB S') (N : ℕ), M.IsLB → L.IsLB → LBIso (M.pull π) (lbPow L N) → ∃ T : ∀ (A : Scheme.{0}) (a : A ⟶ S'), LB.Gen (L.pull a) → LB.Gen (M.pull (a ≫ π)), (∀ (A : Scheme.{0}) (a : A ⟶ S') (e : LB.Gen (L.pull a)), e.IsGen → (T A a e).IsGen) ∧ ∀ (A A' Y : Scheme.{0}) (a : A ⟶ S') (a' : A' ⟶ S') (e : LB.Gen (L.pull a)) (e' : LB.Gen (L.pull a')) (r : Y ⟶ A) (r' : Y ⟶ A'), e.IsGen → e'.IsGen → r ≫ a = r' ≫ a' → (∀ (z : Y) (J : (Y ⟶ S') → L.ι), Good L z J → val (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z J = val (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z J) → ∀ (z : Y) (J : (Y ⟶ Z) → M.ι), Good M z J → val (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) (T A a e) r z J = val (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) (T A' a' e') r' z J := by
  first | exact @GlobalTheory.GenTransport.transport | exact GlobalTheory.GenTransport.transport | (intros; apply GlobalTheory.GenTransport.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalCompactificationExtensionOfCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TozCore

theorem exists_extension_of_cover_hodge : ∀ (o : Type) [CommRing o] (g : ℕ) (Z S' : Scheme.{0}) (z : Z ⟶ Sp o) (π : S' ⟶ Z) [IsProper z] [IsProper π] (OZ : LB Z), OZ.IsLB → GlobalTheory.IsAmpleLB OZ → ∀ (G : Over S') [GrpObj G] [IsCommMonObj G] (N : ℕ), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → LBIso (OZ.pull π) (lbPow (hodge G g) N) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (b : o →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → y ≫ π ≫ z = jK R ≫ spMap b → ∃ a : Sp R ⟶ Z, jK R ≫ a = y ≫ π := by
  intro o _ g Z S' z π _ _ OZ hOZ hA G _ _ N hG hsm hw R _ _ _ _ _ _ b G₁ _ _ hG₁ y α hα hy
  have := hA.compactSpace
  have := hA.quasiSeparatedSpace
  have := hG.separated
  have : QuasiSeparated G.hom := inferInstance
  have hL : (hodge G g).IsLB := isLB_hodge G g
  obtain ⟨T, hT, hTv⟩ := GlobalTheory.T.exists_transport_generator_lbPow_to_ampleBundle S' Z π OZ (hodge G g) N hOZ hL hw
  obtain ⟨e₀, he₀, H⟩ := GlobalTheory.T.exists_integral_hodgeBundle_generator S' g G hG hsm R G₁ hG₁ y α hα
  have amp : ∀ z : Z, ∃ (d : ℕ) (s : H0 OZ d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
    intro x
    obtain ⟨n, hn, s, hs, ha⟩ := hA.exists_affine x
    refine ⟨n, GlobalTheory.ThetaShift.secFinOne s, hn, ?_, ?_⟩
    · rw [GlobalTheory.ThetaShift.nonzeroLocus_secFinOne]; exact hs
    · rw [GlobalTheory.ThetaShift.nonzeroLocus_secFinOne]; exact ha
  refine GlobalTheory.ExtLB.exists_extension Z OZ hOZ amp R (y ≫ π) (T _ y e₀) (hT _ y e₀ he₀) ?_
  intro W _ _ _ hW φ gam hg
  have := hW.1
  have sq : spMap gam ≫ jK R = jK W ≫ spMap φ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext hg)
  obtain ⟨χ', hχ', -⟩ := val_exists (π ≫ z) (spMap gam ≫ y) (spMap φ ≫ spMap b) (by
    rw [Category.assoc, hy, ← Category.assoc, sq, Category.assoc])
  obtain ⟨e₀', he₀', hv⟩ := H W hW φ gam hg χ' hχ'.symm
  refine ⟨χ' ≫ π, by rw [← Category.assoc, ← hχ', Category.assoc], T _ χ' e₀', hT _ χ' e₀' he₀', ?_⟩
  exact hTv _ _ _ y χ' e₀ e₀' (spMap gam) (jK W) he₀ he₀' hχ'.symm hv

end GlobalTheory.TozCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalCompactificationExtensionOfCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_minimalCompactification_extension_of_cover : ∀ (o : Type) [CommRing o] (g : ℕ) (Z S' : Scheme.{0}) (z : Z ⟶ Sp o) (π : S' ⟶ Z) [IsProper z] [IsProper π] (OZ : LB Z), OZ.IsLB → GlobalTheory.IsAmpleLB OZ → ∀ (G : Over S') [GrpObj G] [IsCommMonObj G] (N : ℕ), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → LBIso (OZ.pull π) (lbPow (hodge G g) N) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (b : o →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ S') (α : pullback G₁.hom (jK R) ⟶ G.left), IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α → y ≫ π ≫ z = jK R ≫ spMap b → ∃ a : Sp R ⟶ Z, jK R ≫ a = y ≫ π := by
  first | exact @GlobalTheory.TozCore.exists_extension_of_cover_hodge | exact GlobalTheory.TozCore.exists_extension_of_cover_hodge | (intros; apply GlobalTheory.TozCore.exists_extension_of_cover_hodge <;> assumption)
end
