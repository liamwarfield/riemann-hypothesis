module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnifPolarizationSquareIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigIsoOfIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigLBIso


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_rig_iso_of_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L₁ L₂ : RigLB G), LBIso L₁.L L₂.L → ∃ wL : LB.Iso L₁.L L₂.L, wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  rintro S G _ _ L₁ L₂ ⟨w, hw⟩
  let gv {X : Scheme.{0}} {L' L : LB X} (w : LB.Iso L' L) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
    gm f y _ (w.s (j, k))

  have gm_isGen {X : Scheme.{0}} {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j j' : L.ι)
      (k k' : L'.ι) (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
      gv w f y j k = gm f y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gv w f y j' k' := by
    have hV : f y ∈ (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have hw' : res (inf_le_left : (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j ⊓ L'.U k) (w.s (j, k)) =
        res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j ⊓ L.U j') (L.g j j') *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ *
        res (inf_le_right : (L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k') ≤ L.U j' ⊓ L'.U k') (w.s (j', k')) :=
      hw (j, k) (j', k')
    have key := congrArg (gm f y ((L.U j ⊓ L'.U k) ⊓ (L.U j' ⊓ L'.U k'))) hw'
    simp only [map_mul, map_inv, gm_res f y _ hV] at key
    rw [gm_res f y (U := L.U j ⊓ L'.U k) _ hV (w.s (j, k)),
      gm_res f y (U := L.U j' ⊓ L'.U k') _ hV (w.s (j', k'))] at key
    exact key

  let isoPullId {X : Scheme.{0}} {L' L : LB X} (w : LB.Iso L' L) {F : X ⟶ X} (hF : F = 𝟙 X) : LB.Iso L' (L.pull F) :=
    ⟨fun p => res (fun y hy => ⟨by have := mem_pull.1 hy.1; rw [hF] at this; exact this, hy.2⟩ :
      (LB.pull L F).U p.1 ⊓ L'.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L'.U p.2) (w.s (p.1 PUnit.unit, p.2))⟩

  have gw_isoPullId {X : Scheme.{0}} {L' L : LB X} (w : LB.Iso L' L) {F : X ⟶ X} (hF : F = 𝟙 X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y)
      (j : L.ι) (k : L'.ι) (hj : f y ∈ L.U j) (hk : f y ∈ L'.U k) :
      gw (isoPullId w hF) f y j k = gv w f y j k := by
    have hmem : f y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 (by rw [hF]; exact hj), hk⟩
    exact gm_res f y _ hmem (w.s (j, k))

  have isoPullId_pgen {X : Scheme.{0}} {L' L : LB X} {w : LB.Iso L' L} (hw : w.IsGen) {F : X ⟶ X} (hF : F = 𝟙 X) :
      PGen (isoPullId w hF) := by
    intro Y f y j j' k k' hj hj' hk hk'
    subst hF
    rw [gw_isoPullId w rfl f y j k hj hk, gw_isoPullId w rfl f y j' k' hj' hk', Category.comp_id]
    exact gm_isGen hw f y j j' k k' hj hj' hk hk'

  have hw₀ : PGen (isoPullId w (F := 𝟙 G.left) rfl) := isoPullId_pgen hw rfl
  obtain ⟨c, hc⟩ := GlobalTheory.Unif.RigidifyIso.exists_ratio (K := PUnit) (φ' := fun _ => eSec G)
    (φ := fun _ => eSec G) (ε := fun _ => 1) hw₀ L₂.isLB L₁.isLB (𝟙 _)
    (fun _ => by rw [Category.comp_id, Category.id_comp]) L₁.rig L₁.rigGen L₂.rig L₂.rigGen
  let π : G.left ⟶ (𝟙_ (Over S)).left := G.hom
  have hs : eSec G ≫ π = 𝟙 _ := Over.w η[G]
  let wL : LB.Iso L₁.L L₂.L := ⟨fun i => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s i⟩
  have hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : L₂.L.ι) (k : L₁.L.ι), f y ∈ L₂.L.U j →
      f y ∈ L₁.L.U k → gv wL f y j k = gm (f ≫ π) y ⊤ c * gv w f y j k := by
    intro Y f y j k hj hk
    have hz : f y ∈ L₂.L.U j ⊓ L₁.L.U k := ⟨hj, hk⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res f y _ hz _).trans (gm_pull f π y ⊤ trivial c)) rfl)
  refine ⟨wL, ?_, ?_⟩
  · rintro p q
    apply unit_ext
    intro x hx
    have h1 : (𝟙 G.left) x ∈ L₂.L.U p.1 := hx.1.1
    have h2 : (𝟙 G.left) x ∈ L₁.L.U p.2 := hx.1.2
    have h3 : (𝟙 G.left) x ∈ L₂.L.U q.1 := hx.2.1
    have h4 : (𝟙 G.left) x ∈ L₁.L.U q.2 := hx.2.2
    have eL : gm (𝟙 G.left) x _ (res (inf_le_left : (L₂.L.div L₁.L).U p ⊓ (L₂.L.div L₁.L).U q ≤ _) (wL.s p)) =
        gv wL (𝟙 G.left) x p.1 p.2 := gm_res (𝟙 G.left) x _ hx _
    have eR : gm (𝟙 G.left) x _ ((L₂.L.div L₁.L).g p q *
        res (inf_le_right : (L₂.L.div L₁.L).U p ⊓ (L₂.L.div L₁.L).U q ≤ _) (wL.s q)) =
        gm (𝟙 G.left) x _ (L₂.L.g p.1 q.1) * (gm (𝟙 G.left) x _ (L₁.L.g p.2 q.2))⁻¹ * gv wL (𝟙 G.left) x q.1 q.2 :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L₁.L L₂.L (𝟙 G.left) x p q hx) (gm_res (𝟙 G.left) x _ hx _))
    rw [eL, eR, hv _ _ x _ _ h1 h2, hv _ _ x _ _ h3 h4, gm_isGen hw (𝟙 G.left) x p.1 q.1 p.2 q.2 h1 h3 h2 h4]
    exact mul_left_comm _ _ _
  · rintro ⟨P, Q⟩
    apply unit_ext
    intro x hx
    have hj : (eSec G) x ∈ L₂.L.U (P PUnit.unit) := Set.mem_iInter.1 hx.1 PUnit.unit
    have hk : (eSec G) x ∈ L₁.L.U (Q PUnit.unit) := Set.mem_iInter.1 hx.2 PUnit.unit
    have hj' : (𝟙 _ ≫ eSec G) x ∈ L₂.L.U (P PUnit.unit) := Set.mem_iInter.1 hx.1 PUnit.unit
    have hk' : (𝟙 _ ≫ eSec G) x ∈ L₁.L.U (Q PUnit.unit) := Set.mem_iInter.1 hx.2 PUnit.unit
    have hc' := hc _ (𝟙 _) x P Q (by simp only [Category.comp_id]; exact hx.1) hx.2
    have ep : ReciprocityTheory.ChartRestriction.G.Geo.Tor.pw (isoPullId w (F := 𝟙 G.left) rfl) (K := PUnit) (fun _ => eSec G) (fun _ => 1)
        (𝟙 _) x P Q = gv w (𝟙 _ ≫ eSec G) x (P PUnit.unit) (Q PUnit.unit) := by
      show ∏ k : PUnit, _ = _
      rw [Fintype.prod_unique, zpow_one]
      exact gw_isoPullId w rfl _ x _ _ hj' hk'
    rw [Category.comp_id, ep] at hc'
    have eL : gm (𝟙 _) x _ (res (inf_le_left : LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q ≤ _)
        (L₂.rig.s P)) = gm (𝟙 _) x _ (L₂.rig.s P) := gm_res (𝟙 _) x _ hx _
    have eR : gm (𝟙 _) x _ (@id (Γ((𝟙_ (Over S)).left, LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q)ˣ) ((LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s (P, Q)) *
        res (inf_le_right : LB.wchart L₂.L (fun _ => eSec G) P ⊓ LB.wchart L₁.L (fun _ => eSec G) Q ≤ _) (L₁.rig.s Q)) =
        gv wL (𝟙 _ ≫ eSec G) x (P PUnit.unit) (Q PUnit.unit) * gm (𝟙 _) x _ (L₁.rig.s Q) := by
      refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res (𝟙 _) x _ hx _))
      show gm (𝟙 _) x _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (wL.s (P PUnit.unit, Q PUnit.unit)))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact (gm_res (𝟙 _) x _ hx _).trans (gm_pull (𝟙 _) (eSec G) x (L₂.L.U (P PUnit.unit) ⊓ L₁.L.U (Q PUnit.unit)) ⟨hj, hk⟩ _)
    refine eL.trans (hc'.trans (Eq.trans ?_ eR.symm))
    rw [hv _ _ x _ _ hj' hk', Category.assoc, hs, Category.comp_id]
    exact (mul_assoc _ _ _).symm

end GlobalTheory.RigLBIso
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.TwoUnifTors


set_option maxHeartbeats 1600000 in
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorRef in
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G G' : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (D D' : DegData V (maximalIdeal V)) (U : Unif (maximalIdeal V) D A G) (U' : Unif (maximalIdeal V) D' A G'), ∃ ε : D.toPre.X ≃+ D'.toPre.X, (∀ y r r', PsiCoord D.toPre y r → PsiCoord D'.toPre (ε y) r' → Associated r r') ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (k : ℕ) (q : QkPt D.toPre K k) (q' : QkPt D'.toPre K k) (x : TFK (R := V) K ⟶ A.A), 1 ≤ k → QkToAkU U.toUnifPre K k q x → QkToAkU U'.toUnifPre K k q' x → CongMod k q'.y (ε q.y) := by
  intro V _ _ _ _ hc A G G' _ _ _ _ hG hG' D D' U U'
  have hCN : IsCN V := ⟨inferInstance, inferInstance, hc, inferInstance⟩
  have aV := admissibleBase_of_completeNormalLocalCharZero hCN

  have hext := GlobalTheory.homExtDvr_and_laws.1
  have m₁ : IsMonHom (U.gen.hom ≫ U'.gen.inv) := by
    haveI := U.gen_hom; haveI := U'.gen_hom; infer_instance
  have m₂ : IsMonHom (U'.gen.hom ≫ U.gen.inv) := by
    haveI := U.gen_hom; haveI := U'.gen_hom; infer_instance
  obtain ⟨f, ⟨hfm, hfK⟩, -⟩ := hext V G G' hG hG' (U.gen.hom ≫ U'.gen.inv) m₁
  obtain ⟨g, ⟨hgm, hgK⟩, -⟩ := hext V G' G hG' hG (U'.gen.hom ≫ U.gen.inv) m₂
  have fg : f ≫ g = 𝟙 G := by
    have u := hext V G G hG hG (𝟙 _) inferInstance
    refine u.unique ⟨inferInstance, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_comp, hfK, hgK]; simp
  have gf : g ≫ f = 𝟙 G' := by
    have u := hext V G' G' hG' hG' (𝟙 _) inferInstance
    refine u.unique ⟨inferInstance, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_comp, hfK, hgK]; simp
  let ψ : G ≅ G' := ⟨f, g, fg, gf⟩
  haveI : IsMonHom ψ.hom := hfm
  have hψK : (Over.pullback (jK V)).map ψ.hom ≫ U'.gen.hom = U.gen.hom := by
    change (Over.pullback (jK V)).map f ≫ U'.gen.hom = U.gen.hom
    rw [hfK]; simp

  have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.specOf_id V
  have hpb : IsGrpPullback G G' (spMap (RingHom.id V)) ψ.hom.left := by
    rw [hid]; exact isGrpPullback_of_iso ψ
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hpb (isGrpPullback_pullback G' (spMap (RingHom.id V)))
  have he : eSec G ≫ bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V)) =
      spMap (RingHom.id V) ≫ eSec G' := by
    rw [hbc]; exact GlobalTheory.PolBaseChange.eSec_comm hpb
  let L' : RigLB G := ⟨U'.LG.L.pull (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V))),
    rigPullOf (G' := G) (G := G') (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V))) (spMap (RingHom.id V))
      he U'.LG.L U'.LG.rig, pull_isLB U'.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G) (G := G') (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V)))
      (spMap (RingHom.id V)) he U'.LG.L U'.LG.rig U'.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap (RingHom.id V)) G' G _ he U'.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U'.LG.isLB _))

  have wA : LBIso (A.L.pull U.gen.hom.left)
      (U'.LG.L.pull (pullback.fst G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)))) := by
    have k₁ : pullback.fst G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)) =
        ((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V) := by
      rw [hbc]; exact (pullback.lift_fst _ _ _).symm
    have k₂ : U.gen.hom.left = ((Over.pullback (jK V)).map ψ.hom).left ≫ U'.gen.hom.left := by
      rw [← Over.comp_left, hψK]
    rw [k₁, k₂]
    have t₁ : LBIso (A.L.pull (((Over.pullback (jK V)).map ψ.hom).left ≫ U'.gen.hom.left))
        ((A.L.pull U'.gen.hom.left).pull ((Over.pullback (jK V)).map ψ.hom).left) :=
      LBIso.symm ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen A.isLB _ _⟩
    have t₂ : LBIso ((A.L.pull U'.gen.hom.left).pull ((Over.pullback (jK V)).map ψ.hom).left)
        ((U'.LG.L.pull (pullback.fst G'.hom (jK V))).pull ((Over.pullback (jK V)).map ψ.hom).left) :=
      GlobalTheory.RigidBundleGlue.LBIso.pull U'.ext _
    have t₃ : LBIso ((U'.LG.L.pull (pullback.fst G'.hom (jK V))).pull ((Over.pullback (jK V)).map ψ.hom).left)
        (U'.LG.L.pull (((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V))) :=
      ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U'.LG.isLB _ _⟩
    exact (t₁.trans (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
      (pull_isLB (pull_isLB U'.LG.isLB _) _) t₂).trans (pull_isLB A.isLB _)
      (pull_isLB (pull_isLB U'.LG.isLB _) _) (pull_isLB U'.LG.isLB _) t₃

  obtain ⟨W, hW, hWψ⟩ := GlobalTheory.psiOnExists V (maximalIdeal V) aV D'
  have hWg : (specOf (RingHom.id V)).base (genericPoint (Spec (CommRingCat.of V))) ∈ W := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.specOf_id]; exact hW
  have hI : (maximalIdeal V).map (RingHom.id V) ≤ maximalIdeal V := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', -, hgen, hPU⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds V V _ _ aV aV (RingHom.id V) hI D' A G'
    hG' U' W hWψ hWg G bc mbc A rfl U.gen U.gen_hom wA L' wL he gL rL

  have h5 : Laws5 := GlobalTheory.allSixLaws.2.2.2.2.1
  have hUq : UnifUniqSt := GlobalTheory.allSixLaws.2.2.2.2.2.unifUniq
  have hQ : QkPullExistsSt := qkPullExists GlobalTheory.allSixLaws.1.globalFns

  have hLG : LBIso U''.LG.L U.LG.L := by
    refine GlobalTheory.FewAtTest.lbIso_of_generic hG U''.LG U.LG ?_
    have e1 := U''.ext
    rw [hgen] at e1
    exact LBIso.trans (pull_isLB U''.LG.isLB _) (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) (LBIso.symm e1) U.ext
  obtain ⟨wL₀, hwg₀, hwm₀⟩ := GlobalTheory.RigLBIso.exists_rig_iso_of_iso _ G U''.LG U.LG hLG
  obtain ⟨hD₀, hlev₀, -⟩ := hUq V (maximalIdeal V) aV D D'' A A G hG U U'' wL₀ hwg₀ hwm₀
  have hpb₀ : IsGrpPullback G G (spMap (RingHom.id V)) (Iso.refl G).hom.left := by
    haveI : IsMonHom (Iso.refl G).hom := by show IsMonHom (𝟙 G); infer_instance
    rw [hid]; exact isGrpPullback_of_iso (Iso.refl G)
  obtain ⟨bc₀, mbc₀, hbc₀⟩ := grpPullback_iso hpb₀ (isGrpPullback_pullback G (spMap (RingHom.id V)))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id V)) = 𝟙 _ := hbc₀
  have hPU₀ : IsPullUnif (RingHom.id V) hD₀ bc₀ U U'' :=
    isPullUnif_of_uniq U U'' hD₀ wL₀ hwg₀ hwm₀ hlev₀ bc₀ hbc₀'
  have hbc' : bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)) = ψ.hom.left := hbc

  have k₁ : U.gen.inv ≫ (Over.pullback (jK V)).map ψ.hom = U'.gen.inv := by
    rw [Iso.inv_comp_eq, ← hψK, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have k₂ : ((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ ψ.hom.left := pullback.lift_fst _ _ _
  refine ⟨hD₀.xe.symm.trans hD.xe, fun y r r' hr hr' => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := GlobalTheory.SameCoord.psiCoord_of_isPullDeg_id hD₀ (hD₀.xe.symm y) r
      (by rw [AddEquiv.apply_symm_apply]; exact hr)
    obtain ⟨u', hu'⟩ := GlobalTheory.SameCoord.psiCoord_of_isPullDeg_id hD (hD₀.xe.symm y) r' hr'
    have h1 : Associated (u * r) (u' * r') := GlobalTheory.TorRef.psiCoord_associated hu hu'
    exact ((associated_unit_mul_left r u u.isUnit).symm.trans h1).trans (associated_unit_mul_left r' u' u'.isUnit)
  · intro K _ _ _ k q q' x hk hq hq'
    obtain ⟨f, hf, -, hinj, -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G D U K k hk
    obtain ⟨f', hf', -, hinj', -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G' D' U' K k hk
    obtain ⟨f'', hf'', hsurj'', -, -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G D'' U'' K k hk
    obtain ⟨w, hw⟩ := U.ext
    have hxk := (hq w hw).1
    obtain ⟨q'', hq''⟩ := hsurj'' x hxk
    have hF : ∀ r : V, algebraMap (FractionRing V) K (algebraMap V (FractionRing V) r) =
        algebraMap (FractionRing V) K (algebraMap V (FractionRing V) ((RingHom.id V) r)) := fun _ => rfl

    obtain ⟨p, hp₁, hp₂⟩ := hQ V V (RingHom.id V) D.toPre D''.toPre hD₀ K hF k q''
    have A₁ : QkToAkU U''.toUnifPre K k q'' (f p) :=
      h5.qkBaseChange V V _ _ aV aV (RingHom.id V) D A G U G bc₀ mbc₀ A D'' hD₀ U'' hPU₀ K hF k hk p (f p) q''
        (f p) hp₁ hp₂ (by rw [hbc₀', Category.comp_id, hgen]) ((hf p (f p)).2 rfl)
    have hpx : f p = x := ((hf'' q'' (f p)).1 A₁).trans hq''
    obtain ⟨z, hz, -⟩ := (hinj p q).1 (hpx.trans ((hf q x).1 hq))

    obtain ⟨p', hp₁', hp₂'⟩ := hQ V V (RingHom.id V) D'.toPre D''.toPre hD K hF k q''
    have B₁ : QkToAkU U''.toUnifPre K k q'' (f' p') :=
      h5.qkBaseChange V V _ _ aV aV (RingHom.id V) D' A G' U' G bc mbc A D'' hD U'' hPU K hF k hk p' (f' p') q''
        (f' p') hp₁' hp₂' (by rw [hgen, hbc', ← k₂, ← k₁, Over.comp_left]; simp only [Category.assoc])
        ((hf' p' (f' p')).2 rfl)
    have hpx' : f' p' = x := ((hf'' q'' (f' p')).1 B₁).trans hq''
    obtain ⟨z', hz', -⟩ := (hinj' p' q').1 (hpx'.trans ((hf' q' x).1 hq'))
    refine ⟨z' - hD.xe (hD₀.xe.symm z), ?_⟩
    show q'.y = hD.xe (hD₀.xe.symm q.y) + k • (z' - hD.xe (hD₀.xe.symm z))
    rw [hz', hz]
    simp only [map_add (f := _), map_nsmul]
    rw [← hp₁, hp₁', AddEquiv.apply_symm_apply, smul_sub]
    abel

end GlobalTheory.TwoUnifTors
