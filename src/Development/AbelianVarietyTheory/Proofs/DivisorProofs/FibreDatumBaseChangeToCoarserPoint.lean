module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDatumBaseChangeToCoarserPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDatumBaseChangeToCoarserPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyValsTrans

theorem exists_refactor {X X₁ X₂ A : Scheme.{0}} {L : LB X} {M : LB A} (hL : L.IsLB) (hM : M.IsLB)
    {F₁ : X₁ ⟶ X} {F₂ : X₂ ⟶ X} {φ₁ : A ⟶ X₁} {φ₂ : A ⟶ X₂} (e : φ₁ ≫ F₁ = φ₂ ≫ F₂)
    (w₂ : LB.Iso M ((L.pull F₂).pull φ₂)) (hw₂ : PGen w₂) :
    ∃ w₁ : LB.Iso M ((L.pull F₁).pull φ₁), PGen w₁ ∧
      (∀ (z : A) (J : PUnit → L.ι) (k : M.ι), F₁ (φ₁ z) ∈ L.U (J PUnit.unit) → z ∈ M.U k →
        gw w₁ (𝟙 A) z J k = gw w₂ (𝟙 A) z J k) ∧
      ∀ {Y Y₁ Y₂ B : Scheme.{0}} {u : Y ⟶ X} {u₁ : Y₁ ⟶ X₁} {u₂ : Y₂ ⟶ X₂} {v : B ⟶ A} {h₁ : Y₁ ⟶ Y} {h₂ : Y₂ ⟶ Y}
        {g₁ : B ⟶ Y₁} {g₂ : B ⟶ Y₂} (t : LB.Gen (LB.LinComb L (fun _ : PUnit => u) (fun _ => 1)))
        (t₁ : LB.Gen (LB.LinComb (L.pull F₁) (fun _ : PUnit => u₁) (fun _ => 1)))
        (t₂ : LB.Gen (LB.LinComb (L.pull F₂) (fun _ : PUnit => u₂) (fun _ => 1)))
        (a : LB.Gen (LB.LinComb M (fun _ : PUnit => v) (fun _ => 1))),
        v ≫ φ₁ = g₁ ≫ u₁ → v ≫ φ₂ = g₂ ≫ u₂ → g₁ ≫ h₁ = g₂ ≫ h₂ →
        PMaps (L := L) (F := F₁) (idIso (L.pull F₁)) (fun _ : PUnit => u₁) (fun _ => u) (fun _ => 1) t₁ t h₁ →
        PMaps (L := L) (F := F₂) (idIso (L.pull F₂)) (fun _ : PUnit => u₂) (fun _ => u) (fun _ => 1) t₂ t h₂ →
        PMaps w₂ (fun _ : PUnit => v) (fun _ => u₂) (fun _ => 1) a t₂ g₂ →
        PMaps w₁ (fun _ : PUnit => v) (fun _ => u₁) (fun _ => 1) a t₁ g₁ := by
  have hL₁ : (L.pull F₁).IsLB := LB.isLB_pull hL _
  have hL₂ : (L.pull F₂).IsLB := LB.isLB_pull hL _
  have p₁ := (isGen_iff (L := L) (F := F₁) (idIso _)).1 (idIso_isGen hL₁)
  have p₂ := (isGen_iff (L := L) (F := F₂) (idIso _)).1 (idIso_isGen hL₂)
  obtain ⟨w, T₂⟩ := exists_comp hL₂ (idIso (L.pull F₂)) w₂ p₂ hw₂ hL hM
  have pw := T₂.pgen_comp hL₂ p₂ hw₂
  have a₂ : ∀ (z : A) (J : PUnit → L.ι) (k : M.ι), (φ₂ ≫ F₂) z ∈ L.U (J PUnit.unit) → z ∈ M.U k →
      gw w (𝟙 A) z (J PUnit.unit) k = gw w₂ (𝟙 A) z J k := fun z J k hj hk => by
    have hJ : (𝟙 A ≫ φ₂) z ∈ (L.pull F₂).U J := mem_pull.2 hj
    rw [T₂ _ (𝟙 A) z (J PUnit.unit) J k hj hJ hk]
    have : gw (L := L) (F := F₂) (idIso (L.pull F₂)) (𝟙 A ≫ φ₂) z (J PUnit.unit) J = 1 := gm_self hL₂ _ z hJ
    rw [this, _root_.one_mul]
  have b₂ : ∀ {Y Y₂ B : Scheme.{0}} {u : Y ⟶ X} {u₂ : Y₂ ⟶ X₂} {v : B ⟶ A} {h₂ : Y₂ ⟶ Y}
        {g₂ : B ⟶ Y₂} (t : LB.Gen (LB.LinComb L (fun _ : PUnit => u) (fun _ => 1)))
        (t₂ : LB.Gen (LB.LinComb (L.pull F₂) (fun _ : PUnit => u₂) (fun _ => 1)))
        (a : LB.Gen (LB.LinComb M (fun _ : PUnit => v) (fun _ => 1))),
        v ≫ φ₂ = g₂ ≫ u₂ →
        PMaps (L := L) (F := F₂) (idIso (L.pull F₂)) (fun _ : PUnit => u₂) (fun _ => u) (fun _ => 1) t₂ t h₂ →
        PMaps w₂ (fun _ : PUnit => v) (fun _ => u₂) (fun _ => 1) a t₂ g₂ →
        PMaps w (fun _ : PUnit => v) (fun _ => u) (fun _ => 1) a t (g₂ ≫ h₂) :=
    fun t t₂ a hc H H' => T₂.pmaps_comp hL₂ (fun _ => hc) H H'
  clear T₂
  generalize φ₂ ≫ F₂ = H at e w pw a₂ b₂
  subst e
  obtain ⟨w₁, T₁⟩ := exists_cancel hL (idIso (L.pull F₁)) w p₁ pw hL₁ hM
  refine ⟨w₁, T₁.pgen_cancel hL p₁ pw, fun z J k hj hk => ?_, ?_⟩
  · have hJ : (𝟙 A ≫ φ₁) z ∈ (L.pull F₁).U J := mem_pull.2 hj
    rw [← a₂ z J k hj hk, T₁ _ (𝟙 A) z (J PUnit.unit) J k hj hJ hk]
    have : gw (L := L) (F := F₁) (idIso (L.pull F₁)) (𝟙 A ≫ φ₁) z (J PUnit.unit) J = 1 := gm_self hL₁ _ z hJ
    rw [this, _root_.one_mul]
  · intro Y Y₁ Y₂ B u u₁ u₂ v h₁ h₂ g₁ g₂ t t₁ t₂ a c₁ c₂ c H₁ H₂ H
    exact T₁.pmaps_cancel hL (fun _ => c₁) H₁ (c ▸ b₂ t t₂ a c₂ H₂ H)

theorem gs_locSec {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {δ : LB S}
    {σ : (CechPic.tens L.L (δ.pull G.hom)).Sec} {i : δ.ι} {R : Type} [CommRing R] {ξ : Sp R ⟶ S}
    {t : (KeyVals.bL L ξ).L.Sec} (hξ : ⊤ ≤ ξ ⁻¹ᵁ δ.U i) (ht : KeyVals.IsLocSec σ i ξ t) {Z : Scheme.{0}}
    (q : Z ⟶ (KeyVals.bG G ξ).left) (z : Z) (J : (KeyVals.bL L ξ).L.ι) (hJ : q z ∈ (KeyVals.bL L ξ).L.U J) :
    gs q z _ (t.f J) = gs (q ≫ pullback.fst G.hom ξ) z _ (σ.f (J PUnit.unit, fun _ => i)) := by
  have hle : (KeyVals.bL L ξ).L.U J ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (J PUnit.unit, fun _ => i) := by
    intro p hp
    refine ⟨mem_pull.1 hp, mem_pull.2 ?_⟩
    have e := congrArg (fun g => g p) (pullback.condition (f := G.hom) (g := ξ))
    have h2 : ξ (pullback.snd G.hom ξ p) ∈ δ.U i := hξ (show pullback.snd G.hom ξ p ∈ (⊤ : (Sp R).Opens) from trivial)
    exact e.symm ▸ h2
  rw [ht J hle]
  exact gs_appLE _ _ _ hle q z hJ _

theorem pmaps_bL {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) {R : Type} [CommRing R]
    (ξ : Sp R ⟶ S) : PMaps (L := L.L) (F := pullback.fst G.hom ξ) (idIso (L.L.pull (pullback.fst G.hom ξ))) (K := PUnit)
      (fun _ => eSec (KeyVals.bG G ξ)) (fun _ => eSec G) (fun _ => 1) (KeyVals.bL L ξ).rig L.rig (KeyVals.eb ξ) :=
  (maps_iff _ _ _ _ (KeyVals.bL L ξ).rig L.rig (KeyVals.eb ξ) (KeyVals.bL L ξ).rig
    (rigPull_le (G' := KeyVals.bG G ξ) (pullback.fst G.hom ξ) (KeyVals.eb ξ) (KeyVals.eSec_bG G ξ) L.L)
    (fun _ => rfl)).1 (idIso_maps (KeyVals.bL L ξ))

theorem keyOn_trans : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R R' K : Type) [CommRing R]
    [CommRing R'] [CommRing K] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (f : R' →+* K)
    (t : (KeyVals.bL L ξ).L.Sec) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ)) (t' : (KeyVals.bL L ξ').L.Sec)
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')) (x : KeyIn K) (hg : x.P.g = g),
    spMap r ≫ ξ = ξ' → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → KeyVals.IsLocSec σ i ξ' t' →
    (∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ) →
    KeyOn f x (KeyVals.bG G ξ') (KeyVals.bL L ξ') t' (fun j => y' (j.cast hg)) →
    KeyOn (f.comp r) x (KeyVals.bG G ξ) (KeyVals.bL L ξ) t (fun j => y (j.cast hg)) := by
  intro S G _ _ g L δ σ i R R' K _ _ _ ξ r ξ' f t y t' y' x hg hξ hU ht ht' hy hK
  obtain ⟨φ', he', ψ', F', hφ', hψ', hrig', hsec', hF1, hF2, hFv⟩ := hK
  have hU' : ⊤ ≤ ξ' ⁻¹ᵁ δ.U i := by
    intro p _
    rw [← hξ]
    exact hU (show spMap r p ∈ (⊤ : (Sp R).Opens) from trivial)
  have hP := isGrpPullback_pullback G ξ
  have hP' := isGrpPullback_pullback G ξ'
  obtain ⟨m, hm, hfst, hsnd⟩ : ∃ m : (KeyVals.bG G ξ').left ⟶ (KeyVals.bG G ξ).left,
      IsGrpPullback (KeyVals.bG G ξ') (KeyVals.bG G ξ) (spMap r) m ∧ m ≫ pullback.fst G.hom ξ = pullback.fst G.hom ξ' ∧
        m ≫ (KeyVals.bG G ξ).hom = (KeyVals.bG G ξ').hom ≫ spMap r := by
    have sq : pullback.fst G.hom ξ' ≫ G.hom = (pullback.snd G.hom ξ' ≫ spMap r) ≫ ξ := by
      rw [Category.assoc, hξ]; exact pullback.condition
    refine ⟨pullback.lift _ _ sq, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    refine IsGrpPullback.cancel hP ?_ (pullback.lift_snd _ _ _)
    rw [pullback.lift_fst, hξ]
    exact hP'
  have hφ : IsGrpPullback x.P.A (KeyVals.bG G ξ) (spMap (f.comp r)) (φ' ≫ m) := by
    rw [spMap_comp]
    exact IsGrpPullback.comp hφ' hm
  have he : eSec x.P.A ≫ φ' ≫ m = spMap (f.comp r) ≫ eSec (KeyVals.bG G ξ) := PolBaseChange.eSec_comm hφ
  have e : (φ' ≫ m) ≫ pullback.fst G.hom ξ = φ' ≫ pullback.fst G.hom ξ' := by rw [Category.assoc, hfst]
  obtain ⟨ψ, pψ, hgw, hmap⟩ := exists_refactor L.isLB x.P.isLB e ψ' ((isGen_iff ψ').1 hψ')
  have H' : PMaps ψ' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec (KeyVals.bG G ξ')) (fun _ => 1) x.rig
      (KeyVals.bL L ξ').rig (spMap f) :=
    (maps_iff ψ' _ _ _ x.rig (KeyVals.bL L ξ').rig (spMap f) _
      (rigPull_le (G' := x.P.A) φ' (spMap f) he' (KeyVals.bL L ξ').L) (fun _ => rfl)).1 hrig'
  have c : spMap (f.comp r) ≫ ξ = spMap f ≫ ξ' := by rw [spMap_comp, Category.assoc, hξ]
  have H := hmap L.rig (KeyVals.bL L ξ).rig (KeyVals.bL L ξ').rig x.rig he he' c (pmaps_bL L ξ) (pmaps_bL L ξ') H'
  have hD1 : ∀ a, Chart.dualMapR r (algebraMap R _ a) = algebraMap R' _ (r a) := fun a => by
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have hD2 : Chart.dualMapR r DualNumber.eps = DualNumber.eps := by
    ext <;> simp [Chart.dualMapR]
  refine ⟨φ' ≫ m, he, ψ, F'.comp (Chart.dualMapR r), hφ, (isGen_iff ψ).2 pψ,
    (maps_iff ψ _ _ _ x.rig (KeyVals.bL L ξ).rig (spMap (f.comp r)) _
      (rigPull_le (G' := x.P.A) (φ' ≫ m) (spMap (f.comp r)) he (KeyVals.bL L ξ).L) (fun _ => rfl)).2 H,
    ?_, fun a => ?_, ?_, fun j => ?_⟩
  · refine GlobalTheory.KeyPow.appLE_eq_of_stalk ψ t x.th ?_
    intro z J k hJ hk
    have ha : ((φ' ≫ m) ≫ pullback.fst G.hom ξ) z ∈ L.L.U (J PUnit.unit) :=
      (mem_pull (F := pullback.fst G.hom ξ)).1 hJ
    have ha' : (φ' ≫ pullback.fst G.hom ξ') z ∈ L.L.U (J PUnit.unit) := e ▸ ha
    have hJ' : φ' z ∈ (KeyVals.bL L ξ').L.U J := (mem_pull (F := pullback.fst G.hom ξ')).2 ha'
    have hW : (𝟙 x.P.A.left) z ∈ ((KeyVals.bL L ξ').L.pull φ').U (fun _ => J) ⊓ x.P.L.U k := ⟨mem_pull.2 hJ', hk⟩
    have s2 : gs (𝟙 _ ≫ φ') z _ (t'.f J) = (gw ψ' (𝟙 _) z J k).val * gs (𝟙 _) z _ (x.th.f k) := by
      have e0 := congrArg (gs (𝟙 _) z (((KeyVals.bL L ξ').L.pull φ').U (fun _ => J) ⊓ x.P.L.U k))
        (hsec' (fun _ => J) k (fun x hx => mem_pull.1 hx.1))
      exact (gs_appLE φ' _ _ _ (𝟙 _) z hW _).symm.trans (e0.trans ((gs_mul _ z _ hW _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hW _) (gs_res _ z _ hW _))))
    have e1 := gs_locSec hU ht (𝟙 _ ≫ φ' ≫ m) z J hJ
    have e2 := gs_locSec hU' ht' (𝟙 _ ≫ φ') z J hJ'
    have e3 : (𝟙 _ ≫ φ' ≫ m) ≫ pullback.fst G.hom ξ = (𝟙 _ ≫ φ') ≫ pullback.fst G.hom ξ' := by
      rw [Category.id_comp, Category.id_comp, e]
    rw [e3] at e1
    exact e1.trans (e2.symm.trans (s2.trans (congrArg (fun u : _ˣ => u.val * _) (hgw z J k ha hk).symm)))
  · rw [RingHom.comp_apply, hD1, hF1]; rfl
  · rw [RingHom.comp_apply, hD2, hF2]
  · have hv : (y' (j.cast hg)).left ≫ m = spMap (Chart.dualMapR r) ≫ (y (j.cast hg)).left := by
      refine hP.1.hom_ext ?_ ?_
      · rw [Category.assoc, hfst, Category.assoc]
        exact hy _ hD1 hD2 _
      · rw [Category.assoc, hsnd, ← Category.assoc, Over.w (y' _), Category.assoc, Over.w (y _)]
        show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact RingHom.ext fun a => (hD1 a).symm
    rw [← Category.assoc, hFv j, Category.assoc, hv, spMap_comp, Category.assoc]

end GlobalTheory.KeyValsTrans

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDatumBaseChangeToCoarserPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreDatum_baseChange_to_coarserPoint : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R R' K : Type) [CommRing R]
    [CommRing R'] [CommRing K] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (f : R' →+* K)
    (t : (KeyVals.bL L ξ).L.Sec) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ)) (t' : (KeyVals.bL L ξ').L.Sec)
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')) (x : KeyIn K) (hg : x.P.g = g),
    spMap r ≫ ξ = ξ' → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → KeyVals.IsLocSec σ i ξ' t' →
    (∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ) →
    KeyOn f x (KeyVals.bG G ξ') (KeyVals.bL L ξ') t' (fun j => y' (j.cast hg)) →
    KeyOn (f.comp r) x (KeyVals.bG G ξ) (KeyVals.bL L ξ) t (fun j => y (j.cast hg)) := by
  first | exact @GlobalTheory.KeyValsTrans.keyOn_trans | exact GlobalTheory.KeyValsTrans.keyOn_trans | (intros; apply GlobalTheory.KeyValsTrans.keyOn_trans <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStabilizerAction
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

namespace GlobalTheory.EqvInterior

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

section Moves

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)

def nu (g : LevelAut Dw l) : SABMap Xo.univ.t Xo.univ.t (GlobalTheory.CompLevelStab.mv hpq hA Xo g) :=
  (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose

theorem nu_spec (g : LevelAut Dw l) :
    IsLevMove (GlobalTheory.CompLevelStab.mv hpq hA Xo g) (nu hpq hA Xo g) (liftLa g) LinearMap.id :=
  (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose_spec.2

theorem nu_mul (c : Coeff l) (g h : LevelAut Dw l) : (nu hpq hA Xo (g * h)).φ = (nu hpq hA Xo g).φ ≫ (nu hpq hA Xo h).φ := by
  obtain ⟨μ, hμ, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).2.1 _ _ (nu hpq hA Xo g) (nu hpq hA Xo h)
  have hg := nu_spec hpq hA Xo g
  have hh := nu_spec hpq hA Xo h
  have hc : IsLevMove (GlobalTheory.CompLevelStab.mv hpq hA Xo g ≫ GlobalTheory.CompLevelStab.mv hpq hA Xo h) μ (liftLa (g * h))
      LinearMap.id := by
    refine ⟨?_, fun a => ?_, fun a => ?_⟩
    · rw [Category.assoc, hh.1, hg.1]
    · rw [GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub g h a), hμ, ← Category.assoc, hg.2.1,
        Category.assoc, hh.2.1, Category.assoc]
    · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a =
          (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
      rw [e, hμ, ← Category.assoc, hg.2.2, Category.assoc, hh.2.2, Category.assoc]
  have := (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo g).choose_spec.1
  have := (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo h).choose_spec.1
  rw [← hμ]
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c (g * h) (GlobalTheory.CompLevelStab.mv_spec hpq hA Xo (g * h)).choose_spec.1
    inferInstance (nu_spec hpq hA Xo (g * h)) hc).2

end Moves

section Lift

variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem j₀_ι' : j₀ TF.Y Z ≫ (barComp TF.Y Z).ι = i₀ TF.Y Z ≫ (TF.Y.jQ ≫ pullback.fst _ _) := j₀_ι TF.Y Z

def toF : (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ TF.Y.oF.t.G.left :=
  TF.Y.m.cart.1.lift (pullback.fst TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι))
    (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ i₀ TF.Y Z) (by
      rw [pullback.condition, Category.assoc]; exact congrArg (_ ≫ ·) (j₀_ι' TF Z))

theorem toF_m : toF TF Z ≫ TF.Y.m.φ = pullback.fst TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) :=
  TF.Y.m.cart.1.lift_fst _ _ _

theorem toF_hom : toF TF Z ≫ TF.Y.oF.t.G.hom =
    pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ i₀ TF.Y Z :=
  TF.Y.m.cart.1.lift_snd _ _ _

theorem toF_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) TF.Y.oF.t.G (i₀ TF.Y Z) (toF TF Z) :=
  IsGrpPullback.cancel TF.Y.m.cart
    ((GlobalTheory.EqvAct.isGrpPullback_pullψ TF Z (j₀ TF.Y Z)).congr (j₀_ι' TF Z) (toF_m TF Z).symm) (toF_hom TF Z)

def toU : (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ Xo.univ.t.G.left := toF TF Z ≫ TF.Y.m0.toSABMap.φ

theorem toU_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) Xo.univ.t.G (i₀ TF.Y Z ≫ pullback.fst _ _)
    (toU TF Z) :=
  (toF_cart TF Z).comp TF.Y.m0.cart

theorem hom_ext' {T : Scheme.{0}} {u u' : T ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left}
    (h₁ : u ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) =
      u' ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι))
    (h₂ : u ≫ toU TF Z = u' ≫ toU TF Z) : u = u' :=
  (toU_cart TF Z).1.hom_ext h₂ h₁

end Lift

section Move

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem nF_w (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
    (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g) :
    (toU TF Z ≫ (nu hpq hA Xo g).φ) ≫ Xo.univ.t.G.hom =
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) ≫ pullback.fst _ _ := by
  rw [Category.assoc, (nu hpq hA Xo g).cart.1.w, ← Category.assoc, (toU_cart TF Z).1.w, hr,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, GlobalTheory.CompLevelStab.mvF_fst]
  rfl

def nF (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
    (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g) :
    (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left :=
  pullback.lift
    (TF.Y.m0.cart.1.lift (toU TF Z ≫ (nu hpq hA Xo g).φ)
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) (nF_w hpq hA TF Z g r hr) ≫ TF.Y.m.φ)
    (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r) (by
      rw [Category.assoc, TF.Y.m.cart.1.w, ← Category.assoc, TF.Y.m0.cart.1.lift_snd]
      simp only [Category.assoc]
      exact congrArg (fun x => _ ≫ r ≫ x) (j₀_ι' TF Z).symm)

variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)

theorem nF_snd : nF hpq hA TF Z g r hr ≫ pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) =
    pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r :=
  pullback.lift_snd _ _ _

theorem nF_toF : nF hpq hA TF Z g r hr ≫ toF TF Z = TF.Y.m0.cart.1.lift (toU TF Z ≫ (nu hpq hA Xo g).φ)
      (pullback.snd TF.Y.t.G.hom (j₀ TF.Y Z ≫ (barComp TF.Y Z).ι) ≫ r ≫ i₀ TF.Y Z) (nF_w hpq hA TF Z g r hr) := by
  apply TF.Y.m.cart.1.hom_ext
  · rw [Category.assoc, toF_m]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, toF_hom, ← Category.assoc, nF_snd, Category.assoc, TF.Y.m0.cart.1.lift_snd]

theorem nF_toU : nF hpq hA TF Z g r hr ≫ toU TF Z = toU TF Z ≫ (nu hpq hA Xo g).φ := by
  rw [toU, ← Category.assoc, nF_toF]
  exact TF.Y.m0.cart.1.lift_fst _ _ _

theorem nF_cart : IsGrpPullback (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) r
    (nF hpq hA TF Z g r hr) := by
  refine IsGrpPullback.cancel (toU_cart TF Z) (((toU_cart TF Z).comp (nu hpq hA Xo g).cart).congr ?_ ?_) ?_
  · rw [Category.assoc, ← GlobalTheory.CompLevelStab.mvF_fst, ← Category.assoc, ← hr, Category.assoc]
  · exact (nF_toU hpq hA TF Z g r hr).symm
  · exact nF_snd hpq hA TF Z g r hr

end Move

section Laws

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)

theorem act_toF (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ toF TF Z =
    toF TF Z ≫ (TF.Y.oF.t.act.act a).left := by
  apply TF.Y.m.cart.1.hom_ext
  · rw [Category.assoc, toF_m, Category.assoc, TF.Y.m.act a, ← Category.assoc, toF_m]
    exact GlobalTheory.EqvAct.pullAct_pullψ TF Z (j₀ TF.Y Z) a
  · rw [Category.assoc, toF_hom, Category.assoc, Over.w (TF.Y.oF.t.act.act a), toF_hom, ← Category.assoc]
    exact congrArg (· ≫ i₀ TF.Y Z) (Over.w ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a))

theorem act_toU (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ toU TF Z =
    toU TF Z ≫ (Xo.univ.t.act.act a).left := by
  rw [toU, ← Category.assoc, act_toF, Category.assoc, TF.Y.m0.toSABMap.act a, Category.assoc]

variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)

theorem act_nF (a : 𝓞 E) : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ nF hpq hA TF Z g r hr =
    nF hpq hA TF Z g r hr ≫ ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left := by
  apply hom_ext' TF Z
  · rw [Category.assoc, nF_snd, Category.assoc]
    have e := Over.w ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a)
    erw [e, ← Category.assoc, e]
    exact (nF_snd hpq hA TF Z g r hr).symm
  · have e1 : ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ nF hpq hA TF Z g r hr ≫ toU TF Z =
        toU TF Z ≫ (Xo.univ.t.act.act a).left ≫ (nu hpq hA Xo g).φ := by
      rw [nF_toU, ← Category.assoc, act_toU, Category.assoc]
    have e2 : (nF hpq hA TF Z g r hr ≫ ((GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)).act a).left) ≫ toU TF Z =
        toU TF Z ≫ (nu hpq hA Xo g).φ ≫ (Xo.univ.t.act.act a).left := by
      rw [Category.assoc, act_toU, ← Category.assoc, nF_toU, Category.assoc]
    rw [Category.assoc, e1, e2, (nu hpq hA Xo g).act a]

theorem sec_toU (b : Dw.La) (w : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left)
    (hw : w ≫ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).hom = 𝟙 _)
    (hb : w ≫ GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z) = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ) :
    w ≫ toU TF Z = i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left := by
  have hF : w ≫ toF TF Z = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left := by
    apply TF.Y.m.cart.1.hom_ext
    · rw [Category.assoc, toF_m, Category.assoc]
      exact hb
    · rw [Category.assoc, toF_hom, ← Category.assoc]
      erw [hw]
      rw [Category.id_comp, Category.assoc, Over.w (TF.Y.oF.eta b)]
      exact (Category.comp_id _).symm
  rw [toU, ← Category.assoc, hF, Category.assoc, TF.Y.m0.eta b]

end Laws

end GlobalTheory.EqvInterior
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentBasisPulledFrameCompatiblePointChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentBasisPulledFrameCompatiblePointChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.Vec

open TopologicalSpace GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO LieG)

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {k : Type} [CommRing k] {x : Sp k ⟶ S}
  {G₁ : Over (Sp k)} [GrpObj G₁] {φ : G₁.left ⟶ G.left}

def form (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) :
    (Scheme.Modules.pullback x).obj (omega G) ⟶ GlobalTheory.structureModule (Sp k) :=
  omegaBase h ≫ cotMap p.1 (epsZero_comp p) ≫ (epsIso k).hom

theorem form_app (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {T : (Sp k).Opens}
    (s : Γ((Scheme.Modules.pullback x).obj (omega G), T)) :
    (form h p).app T s = dualApp (tangent p) le_top ((omegaBase h).app T s) := rfl

theorem pre_le (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {V : S.Opens} {W : G.left.Opens}
    (hW : V ≤ unitSec G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) :
    (specO k (DualNumber k)).hom ⁻¹ᵁ T ≤ p.1.left ⁻¹ᵁ φ ⁻¹ᵁ W :=
  preimage_le_of_lieG p (le_of_sq (unitSec_comp h) hW hT)

theorem form_dUnit (h : IsGrpPullback G₁ G x φ) (p : LieG G₁) {V : S.Opens} {W : G.left.Opens}
    (hW : V ≤ unitSec G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) (f : Γ(G.left, W))
    (a b : Γ(Sp k, T))
    (e : ((p.1.left ≫ φ).appLE W _ (pre_le h p hW hT) f :
        Γ((specO k (DualNumber k)).left, (specO k (DualNumber k)).hom ⁻¹ᵁ T)) =
      (specO k (DualNumber k)).hom.appLE T _ le_rfl a +
        (specO k (DualNumber k)).hom.appLE T _ le_rfl b * resG _ le_top (epsFn k)) :
    (form h p).app T (pullbackSections x (omega G) hT (dUnit G hW f)) = b := by
  have hV : T ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  rw [form_app, omegaBase_dUnit h hW hT (le_of_sq (unitSec_comp h) hW hT) le_rfl]
  exact dualApp_tangent_dUnit p _ _ hV le_rfl (pre_le h p hW hT) a b
    ((appLE_appLE rfl _ _ _ f).trans e)

variable {k' : Type} [CommRing k'] (r : k →+* k') (F : DualNumber k →+* DualNumber k')

theorem spMap_comp_hom (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a)) :
    spMap F ≫ (specO k (DualNumber k)).hom = (specO k' (DualNumber k')).hom ≫ spMap r := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext hF)

theorem spMap_epsFn (he : F DualNumber.eps = DualNumber.eps) :
    (spMap F).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn k) = epsFn k' := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom F)) DualNumber.eps).symm.trans ?_
  exact congrArg (Scheme.ΓSpecIso (.of (DualNumber k'))).inv.hom he

theorem epsZero_spMap (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) :
    sec (epsZero k') ≫ spMap F = spMap r ≫ sec (epsZero k) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change (F a).fst = r a.fst
  have : a = algebraMap k _ a.fst + algebraMap k _ a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [this, map_add (f := _), map_mul, hF, hF, he]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {G₂ : Over (Sp k')} [GrpObj G₂] {ψ : G₂.left ⟶ G.left}

theorem form_baseChange [QuasiSeparated G.hom] (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) (h₁ : IsGrpPullback G₁ G x φ) (h₂ : IsGrpPullback G₂ G (spMap r ≫ x) ψ)
    (p : LieG G₁) (q : LieG G₂) (hq : q.1.left ≫ ψ = spMap F ≫ p.1.left ≫ φ)
    {V : S.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ (spMap r ≫ x) ⁻¹ᵁ V) (s : Γ(omega G, V)) :
    ((form h₂ q).app ⊤ (pullbackSections _ (omega G) h' s) : Γ(Sp k', ⊤)) =
      (spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((form h₁ p).app ⊤ (pullbackSections x (omega G) h s) : Γ(Sp k, ⊤)) := by
  have key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧
      resG (Sp k') (le_top : T' ≤ ⊤) ((form h₂ q).app ⊤ (pullbackSections _ (omega G) h' s) : Γ(Sp k', ⊤)) =
      resG (Sp k') (le_top : T' ≤ ⊤) ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((form h₁ p).app ⊤ (pullbackSections x (omega G) h s) : Γ(Sp k, ⊤))) := by
    obtain ⟨U, W, hU, hle, c⟩ := GlobalTheory.Conormal.exists_isChart (sec_hom (MonObj.one (X := G))) (V := V)
      (x := x (spMap r y.1)) (h trivial)
    obtain ⟨T, hT, hyT, hTU⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U) (spMap r y.1) hU
    obtain ⟨f, hf⟩ := c.d_surjective (sec_hom (MonObj.one (X := G))) (resM _ hle s)
    have hf' : dUnit G c.le f = resM (omega G) hle s := hf
    have hTU' : spMap r ⁻¹ᵁ T ≤ (spMap r ≫ x) ⁻¹ᵁ U := (spMap r).preimage_mono hTU
    obtain ⟨⟨a, b⟩, e⟩ := (bijective_add_mul_epsFn k T hT).2
      ((p.1.left ≫ φ).appLE W _ (pre_le h₁ p c.le hTU) f)
    have e₁ := form_dUnit h₁ p c.le hTU f a b e.symm
    have kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap r ⁻¹ᵁ T ≤
        spMap F ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
      (le_preimage_of_comp (spMap_comp_hom r F hF)).2 le_rfl
    have kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap r ⁻¹ᵁ T ≤
        ((specO k' (DualNumber k')).hom ≫ spMap r) ⁻¹ᵁ T := le_rfl
    have n (z : Γ(Sp k, T)) : (spMap F).appLE _ _ kk
        ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) =
        (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap r).appLE T _ le_rfl z) :=
      (appLE_appLE (spMap_comp_hom r F hF) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm
    have n' : (spMap F).appLE _ _ kk (resG _ le_top (epsFn k)) =
        resG _ le_top (epsFn k') :=
      (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans
        (congrArg _ (spMap_epsFn F he)))
    have e₂ := form_dUnit h₂ q c.le hTU' f ((spMap r).appLE T _ le_rfl a)
      ((spMap r).appLE T _ le_rfl b) (by
        refine (appLE_appLE hq.symm (pre_le h₁ p c.le hTU) kk _ f).symm.trans ?_
        refine (congrArg ((spMap F).appLE _ _ kk) e.symm).trans ?_
        refine (map_add _ _ _).trans ?_
        exact congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))
    rw [hf', QCoh.pullbackSections_res] at e₁ e₂
    refine ⟨spMap r ⁻¹ᵁ T, hyT, ?_⟩
    refine (app_resM (form h₂ q) le_top _).symm.trans ?_
    rw [QCoh.res_pullbackSections, e₂, ← e₁]
    refine .trans ?_ ((appLE_resG (spMap r) (le_top : T ≤ ⊤) le_rfl _).trans
      (resG_appLE (spMap r) le_top (le_preimage_top _ _) _).symm)
    refine congrArg _ ?_
    refine .trans ?_ (app_resM (form h₁ p) le_top _)
    rw [QCoh.res_pullbackSections]
  choose T hT hs using key
  exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs

theorem exists_lieG (hF : ∀ a, F (algebraMap k _ a) = algebraMap k' _ (r a))
    (he : F DualNumber.eps = DualNumber.eps) (h₁ : IsGrpPullback G₁ G x φ) (h₂ : IsGrpPullback G₂ G (spMap r ≫ x) ψ)
    (p : LieG G₁) : ∃ q : LieG G₂, q.1.left ≫ ψ = spMap F ≫ p.1.left ≫ φ := by
  have w : (spMap F ≫ p.1.left ≫ φ) ≫ G.hom = (specO k' (DualNumber k')).hom ≫ spMap r ≫ x := by
    rw [Category.assoc, Category.assoc, h₁.1.w, ← Category.assoc p.1.left, Over.w p.1, ← Category.assoc,
      ← Category.assoc]
    exact congrArg (· ≫ x) (spMap_comp_hom r F hF)
  let q : specO k' (DualNumber k') ⟶ G₂ :=
    Over.homMk (h₂.1.lift _ (specO k' (DualNumber k')).hom w) (h₂.1.lift_snd _ _ _)
  have hq : q.left ≫ ψ = spMap F ≫ p.1.left ≫ φ := h₂.1.lift_fst _ _ _
  have ht : (toUnit (specO k' k')).left = 𝟙 (Sp k') := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  refine ⟨⟨q, Over.OverMorphism.ext (h₂.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩, hq⟩
  rw [Over.comp_left, Over.comp_left, ht, Category.assoc, hq, Category.assoc]
  have e : sec (epsZero k') ≫ spMap F ≫ p.1.left ≫ φ = (spMap r ≫ x) ≫ unitSec G := by
    rw [← Category.assoc, epsZero_spMap r F hF he, Category.assoc, ← Category.assoc (sec _), sec_epsZero_comp,
      unitSec_comp h₁, Category.assoc]
  exact e.trans ((unitSec_comp h₂).symm.trans (Category.id_comp _).symm)

theorem dual_vec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R R' : Type)
    [CommRing R] [CommRing R'] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ))
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')), spMap r ≫ ξ = ξ' → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    KeyVals.IsDual c ξ y → KeyVals.IsDual c ξ' y' →
    ∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ := by
  rintro S G _ _ g c R R' _ _ ξ r _ y y' rfl hG - ⟨hc, hy⟩ ⟨hc', hy'⟩ F hF he j
  obtain ⟨p, hp, hp'⟩ := hy j
  obtain ⟨q, hq, hq'⟩ := hy' j
  have h₁ := isGrpPullback_pullback G ξ
  have h₂ := isGrpPullback_pullback G (spMap r ≫ ξ)
  obtain ⟨w, hw⟩ := exists_lieG r F hF he h₁ h₂ p
  have hfr : VB.IsFrame (pfr c (spMap r ≫ ξ) hc') := by
    have k₁ := ((c.isFrame.pullback (spMap r ≫ ξ)).res hc').map_iso (omegaBase h₂)
    have k₂ (b : Fin g) : resM _ hc' (pullbackSections (spMap r ≫ ξ) (omega G) le_rfl (c.e b)) =
        pullbackSections (spMap r ≫ ξ) (omega G) hc' (c.e b) := QCoh.res_pullbackSections _ _ _ _ _
    simp only [k₂] at k₁
    exact k₁
  obtain rfl : w = q := tangent_injective R' _ (hfr.dual_ext le_rfl fun b => by
    rw [resM_self]
    refine (form_baseChange r F hF he h₁ h₂ p w hw hc hc' (c.e b)).trans ?_
    refine .trans (congrArg ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)) (hp' b)) (.trans ?_ (hq' b).symm)
    exact (apply_ite _ _ _ _).trans (if_congr Iff.rfl
      (map_one ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)).hom) (map_zero ((spMap r).appLE ⊤ ⊤ (le_preimage_top _ _)).hom)))
  rw [← hq, ← hp]
  exact hw

end GlobalTheory.KeyVals.Vec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualTangentBasisPulledFrameCompatiblePointChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualTangentBasis_pulledFrame_compatible_pointChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R R' : Type)
    [CommRing R] [CommRing R'] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ))
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')), spMap r ≫ ξ = ξ' → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    KeyVals.IsDual c ξ y → KeyVals.IsDual c ξ' y' →
    ∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ := by
  first | exact @GlobalTheory.KeyVals.Vec.dual_vec | exact GlobalTheory.KeyVals.Vec.dual_vec | (intros; apply GlobalTheory.KeyVals.Vec.dual_vec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFrameChangeBalancedTensorsCmType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFrameChangeBalancedTensorsCmType
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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogKSDiv.DetChange

open GlobalTheory.LogKSDiv
open Classical

theorem sandwich {ι κ K : Type} [Fintype ι] [DecidableEq ι] [CommRing K] (B : Matrix ι κ K) (a b : ι) (x y : κ) :
    (Matrix.transpose B * Matrix.of (fun u v => (if u = a ∧ v = b then (1 : K) else 0) + (if u = b ∧ v = a then 1 else 0)) * B) x y =
      B a x * B b y + B b x * B a y := by
  simp [Matrix.mul_apply, add_mul, mul_add, Finset.sum_add_distrib, ite_and, Finset.sum_mul, Finset.mul_sum]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hostRoot_conj_eq_neg_and_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hre0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨Complex.ext (by simp [hre0]) (by simp), ?_⟩
  intro h0
  rw [h0] at hre
  simp at hre
  exact H.d_prime.ne_zero hre

theorem emb_rt_cases (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [H.sqrt_neg_disc_sq, ← map_pow]
  have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  rw [this]; simp

theorem conj_off (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) ≠ H.rt0 := by
  obtain ⟨h1, h2⟩ := hostRoot_conj_eq_neg_and_ne_zero H
  rw [RingHom.comp_apply, h, h1]
  intro h3
  exact h2 (by linear_combination (-1/2 : ℂ) * h3)

theorem conj_on (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) = H.rt0 := by
  rcases emb_rt_cases H τ with h' | h'
  · exact absurd h' h
  · rw [RingHom.comp_apply, h', map_neg, (hostRoot_conj_eq_neg_and_ne_zero H).1, neg_neg]

theorem conj_conj_emb (τ : E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ := by
  ext x; simp

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {K : Type} [Field K]

theorem flatFrame_eq (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (a b : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    flatFrame A e e' (e a) (e' b) = Matrix.blockDiagonal' A a b := by
  simp [flatFrame]

def kronBlocks (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    Matrix (PairIx H Dw) (PairIx H Dw) K :=
  Matrix.blockDiagonal' fun τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} =>
    Matrix.kroneckerMap (· * ·) (A τ.1).transpose (A ((starRingEnd ℂ).comp τ.1)).transpose

theorem lhs_entry (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (P Q : PairIx H Dw) :
    (Matrix.transpose (flatFrame A e e') * symPair (R := K) e P * flatFrame A e e')
      (e' ⟨Q.1.1, Q.2.1⟩) (e' ⟨(starRingEnd ℂ).comp Q.1.1, Q.2.2⟩) = kronBlocks A Q P := by
  unfold symPair
  rw [sandwich, flatFrame_eq, flatFrame_eq, flatFrame_eq, flatFrame_eq]
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨σ, hσ⟩, i', k'⟩ := Q
  have hne : (starRingEnd ℂ).comp τ ≠ σ := fun h => conj_off H τ hτ (h ▸ hσ)
  dsimp only
  rw [Matrix.blockDiagonal'_apply_ne A _ _ hne, zero_mul, add_zero]
  by_cases h : τ = σ
  · subst h
    simp [kronBlocks, Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]
  · have h' : (⟨σ, hσ⟩ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) ≠ ⟨τ, hτ⟩ := fun h2 => h (congrArg Subtype.val h2).symm
    simp [kronBlocks, Matrix.blockDiagonal'_apply_ne _ _ _ h', Matrix.blockDiagonal'_apply_ne A _ _ h]

theorem sym_entry {n' : ℕ} (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (P Q : PairIx H Dw) :
    symPair (R := K) e' P (e' ⟨Q.1.1, Q.2.1⟩) (e' ⟨(starRingEnd ℂ).comp Q.1.1, Q.2.2⟩) = if P = Q then 1 else 0 := by
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨σ, hσ⟩, i', k'⟩ := Q
  have h2 : ¬ (e' ⟨σ, i'⟩ = e' ⟨(starRingEnd ℂ).comp τ, k⟩ ∧
      e' ⟨(starRingEnd ℂ).comp σ, k'⟩ = e' ⟨τ, i⟩) := by
    rintro ⟨h, -⟩
    have h5 : σ = (starRingEnd ℂ).comp τ := congrArg Sigma.fst (e'.injective h)
    exact conj_off H τ hτ (h5 ▸ hσ)
  simp only [symPair, Matrix.of_apply, if_neg h2, add_zero, e'.apply_eq_iff_eq]
  by_cases h : τ = σ
  · subst h
    simp [Sigma.mk.inj_iff, eq_comm]
    intro h5
    exact (conj_off H τ hτ (by rw [← h5]; exact hτ)).elim
  · have h3 : ¬ (σ = τ) := Ne.symm h
    simp [h, h3]
    intro h5
    exact (conj_off H τ hτ (by rw [← h5]; exact hσ)).elim

theorem L_eq_submatrix (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K)
    (hL : ∀ j, Matrix.transpose (flatFrame A e e') * symPair (R := K) e (ε j) * flatFrame A e e' =
      ∑ k, L k j • symPair (R := K) e' (ε' k)) :
    L = (kronBlocks A).submatrix ε' ε := by
  ext a j
  have h := congrFun (congrFun (hL j) (e' ⟨(ε' a).1.1, (ε' a).2.1⟩)) (e' ⟨(starRingEnd ℂ).comp (ε' a).1.1, (ε' a).2.2⟩)
  rw [lhs_entry, Matrix.sum_apply] at h
  simp only [Matrix.smul_apply, sym_entry, smul_eq_mul, mul_ite, mul_one, mul_zero, ε'.apply_eq_iff_eq] at h
  rw [Finset.sum_ite_eq' Finset.univ a] at h
  simpa using h.symm

theorem det_kronBlocks (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    (kronBlocks A).det = ∏ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      ((A τ.1).det ^ Dw.mult ((starRingEnd ℂ).comp τ.1) * (A ((starRingEnd ℂ).comp τ.1)).det ^ Dw.mult τ.1) := by
  rw [kronBlocks, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod]
  simp [Matrix.det_kronecker, Matrix.det_transpose]

theorem prod_pairs (f : (E →+* ℂ) → K) :
    ∏ τ : E →+* ℂ, f τ ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) =
      ∏ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
        (f τ.1 ^ Dw.mult ((starRingEnd ℂ).comp τ.1) * f ((starRingEnd ℂ).comp τ.1) ^ Dw.mult τ.1) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0), Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr (by convert rfl) fun τ _ => ?_
    rw [if_pos τ.2, Datum.mult, if_neg (conj_off H τ.1 τ.2)]
  · symm
    refine Fintype.prod_equiv
      { toFun := fun τ => ⟨(starRingEnd ℂ).comp τ.1, conj_off H τ.1 τ.2⟩
        invFun := fun σ => ⟨(starRingEnd ℂ).comp σ.1, conj_on H σ.1 σ.2⟩
        left_inv := fun τ => Subtype.ext (conj_conj_emb τ.1)
        right_inv := fun σ => Subtype.ext (conj_conj_emb σ.1) } _ _ (fun τ => ?_)
    simp only [Equiv.coe_fn_mk]
    rw [if_neg (conj_off H τ.1 τ.2), Datum.mult, if_pos τ.2]

end GlobalTheory.LogKSDiv.DetChange

theorem GlobalTheory.LogKSDiv.det_frameChange_balanced :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (K : Type) [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (n n' : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K),
    (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := K) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
      ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := K) e' (ε' k)) →
    ∃ u : K, (u = 1 ∨ u = -1) ∧
      L.det = u * ∏ τ : E →+* ℂ, (A τ).det ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) := by
  intro E _ _ _ H Dw K _ A n n' e e' ε ε' L hL
  classical
  rw [GlobalTheory.LogKSDiv.DetChange.L_eq_submatrix A e e' ε ε' L hL]
  have hs : (GlobalTheory.LogKSDiv.DetChange.kronBlocks A).submatrix ε' ε =
      ((GlobalTheory.LogKSDiv.DetChange.kronBlocks A).submatrix ε ε).submatrix (ε'.trans ε.symm) id := by
    ext a b; simp
  refine ⟨((Equiv.Perm.sign (ε'.trans ε.symm) : ℤ) : K), ?_, ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (ε'.trans ε.symm)) with h | h <;> simp [h]
  · rw [hs, Matrix.det_permute, Matrix.det_submatrix_equiv_self, GlobalTheory.LogKSDiv.DetChange.det_kronBlocks,
      GlobalTheory.LogKSDiv.DetChange.prod_pairs]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFrameChangeBalancedTensorsCmTypeStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_frameChange_balancedTensors_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (K : Type) [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (n n' : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K),
    (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := K) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
      ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := K) e' (ε' k)) →
    ∃ u : K, (u = 1 ∨ u = -1) ∧
      L.det = u * ∏ τ : E →+* ℂ, (A τ).det ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) := by
  first | exact @GlobalTheory.LogKSDiv.det_frameChange_balanced | exact GlobalTheory.LogKSDiv.det_frameChange_balanced | (intros; apply GlobalTheory.LogKSDiv.det_frameChange_balanced <;> assumption)
end
end
