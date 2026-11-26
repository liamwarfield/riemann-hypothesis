module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSeparationRegularDeterminant
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToroidalFlagNonempty

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeLineBundleBignessOnShimuraVariety
section
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
namespace GlobalTheory.HSApp
private def commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) : LB Y where
  ι := C.J
  U j := (B s).U (C.idx s j)
  g j j' := (B s).g (C.idx s j) (C.idx s j')
private theorem isLB_commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    (commonRestr C s).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := C.cover y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (C.mem s j y).2 hj⟩
  g_self j := (C.isLB s).g_self (C.idx s j)
  cocycle i j k := (C.isLB s).cocycle (C.idx s i) (C.idx s j) (C.idx s k) }
private theorem commonRestr_iso {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    LBIso (commonRestr C s) (B s) :=
  iso_of_chart (C.isLB s)
    { idx := C.idx s
      le := fun _ _ h => h
      g := fun _ _ _ _ _ => rfl }
private theorem commonRestr_iso_tens {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    LBIso (commonRestr C (a + b)) (tens (B a) (B b)) :=
  iso_of_chart (isLB_tens (C.isLB a) (C.isLB b))
    { idx := fun j => (C.idx a j, C.idx b j)
      le := fun j y h => by
        have h' : y ∈ C.U j := (C.mem (a + b) j y).1 h
        exact ⟨(C.mem a j y).2 h', (C.mem b j y).2 h'⟩
      g := fun y j j' hj hj' => by
        have h₁ : y ∈ C.U j := (C.mem (a + b) j y).1 hj
        have h₂ : y ∈ C.U j' := (C.mem (a + b) j' y).1 hj'
        refine (C.add a b y j j' h₁ h₂).trans ?_
        exact (tr_tens (B a) (B b) y (a := (C.idx a j, C.idx b j)) (b := (C.idx a j', C.idx b j'))
          ⟨(C.mem a j y).2 h₁, (C.mem b j y).2 h₁⟩ ⟨(C.mem a j' y).2 h₂, (C.mem b j' y).2 h₂⟩).symm }
private theorem cls_common_add {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    cls (B (a + b)) (C.isLB (a + b)) = cls (B a) (C.isLB a) + cls (B b) (C.isLB b) := by
  have e₁ := (cls_eq_iff (isLB_commonRestr C (a + b)) (C.isLB (a + b))).2 (commonRestr_iso C (a + b))
  have e₂ := (cls_eq_iff (isLB_commonRestr C (a + b)) (isLB_tens (C.isLB a) (C.isLB b))).2
    (commonRestr_iso_tens C a b)
  rw [← e₁, e₂, cls_tens (C.isLB a) (C.isLB b)]
end GlobalTheory.HSApp
namespace GlobalTheory.HodgeBig
theorem hodgeLineBundle_isBig : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p → 1 ≤ Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) → letI := algebraΓOfHom (s₀ TF.Y Z); IsBig c.F δ := by
  intro hP _ _ hS hK E _ _ _ H Dw l Xo c TF Z _ _ hF δ hδ hpull
  classical
  obtain ⟨ω, hω, e, hdom⟩ := HodgeDominates.exists_lb_dominates hP.p22 hS hK.toroidalChartsForFan TF
  obtain ⟨_, -, hproj, -, hsurj, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  have hprojY : IsProjOver (str₀ TF.X Z) := (GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF).2.1
  have hN := hP.q7
  let χ : AllWt.Weight Dw := fun _ i => if (i : ℕ) < Dw.p then (1 : ℤ) else -1
  have hB : (ω.pull (barComp TF.Y Z).ι).IsLB := pull_isLB hω _
  have hBp : CechPic.pull (π₀ TF.X Z) (cls _ hB) = cls (L₀ TF.X Z χ) (isLB_L₀ TF.X Z _) := by
    rw [cls_pull hω _ hB, ← CechPic.pull_comp, morphismRestrict_ι, CechPic.pull_comp, ← e]
    exact (cls_pull (TF.X.isLB_Llam _) _ _).symm
  let C := common₀ TF.X Z
  let φ := AddMonoidHom.mk' (fun a => cls (L₀ TF.X Z a) (C.isLB a)) (cls_common_add C)
  have hφ : ∀ a, cls (L₀ TF.X Z a) (isLB_L₀ TF.X Z a) = φ a := fun _ => rfl
  let w : AllWt.Weight Dw := ∑ τ : Psi H, NefWt.unitWt τ (-1)
  have ew : 2 • hodgeWt Dw - χ = w := by
    funext τ i
    simp only [w, Finset.sum_apply, NefWt.unitWt_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply,
      Pi.smul_apply, hodgeWt, CompHt.barWt, χ, smul_eq_mul]
    split_ifs <;> norm_num
  have hwnef : (letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z w)) := by
    letI := algebraΓOfHom (str₀ TF.X Z)
    obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hprojY
    refine IsNef.of_cls_eq_sum Finset.univ
      (fun τ : Psi H => (_root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight (_root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems hP) hN E H Dw l Xo c TF Z hF τ).2) (fun _ => 1) hA
      (isLB_L₀ TF.X Z w) ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, map_sum]
    exact Finset.sum_congr rfl fun τ _ => (one_smul _ _).symm
  letI := algebraΓOfHom (s₀ TF.Y Z)
  have hf : ∀ r : c.F, algebraMap c.F Γ(X₀ TF.Y Z, ⊤) r =
      (s₀ TF.Y Z).appTop ((Scheme.ΓSpecIso (.of c.F)).inv r) := fun _ => rfl
  have hp' : IsProjOver (strHom c.F (X := (X₀ TF.Y Z))) := by rw [strHom_eq hf]; exact hproj
  have h2 := isLB_lbPow hδ 2
  have hNl := LB.isLB_div h2 hB
  have hNp : CechPic.pull (π₀ TF.X Z) (cls _ hNl) = cls (L₀ TF.X Z w) (isLB_L₀ TF.X Z _) := by
    rw [cls_div h2 hB hNl, map_sub, cls_lbPow hδ 2 h2, map_nsmul, hpull, hBp, hφ, hφ, hφ, ← ew, map_sub, map_nsmul]
  have hNnef : IsNef c.F (LB.div (lbPow δ 2) (ω.pull (barComp TF.Y Z).ι)) :=
    GlobalTheory.NefDescent.isNef_of_pull c.F _ _ (π₀ TF.X Z) (s₀ TF.Y Z) (str₀ TF.X Z) _ hNl _
      (isLB_L₀ TF.X Z w) (π₀_s₀ TF.X Z) hproj hprojY hsurj hNp hwnef
  have : IsProper (s₀ TF.Y Z) := ThetaDescent.isProper_of_isProjOver hproj
  have : CompactSpace (X₀ TF.Y Z) := QuasiCompact.compactSpace_of_compactSpace (s₀ TF.Y Z)
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver TF.Y.proj
  have hA₀ : IsAmpleLB (A.pull (barComp TF.Y Z).ι) := hA.pull_of_isOpenImmersion _
  have hw : TF.Y.j (genPt Z) ∈ barComp TF.Y Z := (j_mem_barComp Z _).2 (CompSplitPfB.cspB_genPt_mem Z)
  obtain ⟨m, hm, s, hs⟩ := hdom (genPt Z) A hA.isLB
  have hD := LB.isLB_div (isLB_lbPow hω m) hA.isLB
  have ht : (⟨_, hw⟩ : X₀ TF.Y Z) ∈ nonzeroLocus (lbSecPull _ s (barComp TF.Y Z).ι) := by
    rw [HodgeDominates.nonzeroLocus_lbSecPull]
    exact hs
  have hNm := hNnef.pow hA₀ m
  have hbig := hNm.isBig_tens_ample hN hp' hA₀
  have hδm : IsBig c.F (lbPow δ (2 * m)) :=
    hbig.of_cls_eq_add hf hproj (pull_isLB hD _) ⟨_, sec_ne_zero_of_mem ht⟩ (isLB_lbPow hδ _) (by
      rw [cls_tens hNm.isLB hA₀.isLB, cls_lbPow hNl, cls_div h2 hB hNl, cls_lbPow hδ, cls_lbPow hδ, cls_pull hω,
        cls_pull hA.isLB, cls_pull hD, cls_div (isLB_lbPow hω m) hA.isLB, cls_lbPow hω, map_sub, map_nsmul,
        smul_sub, mul_comm, mul_smul]
      abel)
  exact hδm.of_pow hδ (by omega) fun n => finite_coh_zero_twist_of_isProjOver hf hproj (isLB_lbPow hδ n)
end GlobalTheory.HodgeBig
end

section
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
theorem _root_.GlobalTheory.T.hodgeLineBundle_bigness_on_shimuraVariety : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p → 1 ≤ Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) → letI := algebraΓOfHom (s₀ TF.Y Z); IsBig c.F δ := by
  first | exact @_root_.GlobalTheory.HodgeBig.hodgeLineBundle_isBig | exact _root_.GlobalTheory.HodgeBig.hodgeLineBundle_isBig | (intros; apply _root_.GlobalTheory.HodgeBig.hodgeLineBundle_isBig <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeLineBundleRationalLinearEquivClass
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.EquivariantLinearizationPullbackCompat
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.EquivariantActionEqOfAgreeOnGenerators
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.InteriorEquivariantActionInvariant
section
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
end Moves
section Lift
variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
end Lift
section Move
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)
end Move
section Laws
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)
end Laws
theorem equivariant_action_preserves_interior : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹) → ∃ n : Γ → ((GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left), GlobalTheory.EqvAct.IsEqvAct ρ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)) n ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ (𝟙 (V₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z)) n := by
  intro _ E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ
  refine ⟨fun γ => nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).asIso.hom (hρ γ),
    ⟨fun γ => nF_cart hpq hA TF Z _ _ (hρ γ), fun γ a => act_nF hpq hA TF Z _ _ (hρ γ) a, fun γ₁ γ₂ => ?_⟩,
    fun γ a b hab w w' hw hw' hb ha => ?_⟩
  · apply hom_ext' TF Z
    · rw [nF_snd, Category.assoc, nF_snd, ← Category.assoc, nF_snd, Category.assoc, map_mul, Aut.mul_asIso]
      rfl
    · rw [nF_toU, Category.assoc, nF_toU, ← Category.assoc, nF_toU, Category.assoc, ← nu_mul hpq hA Xo c, map_mul,
        mul_inv_rev]
  · apply hom_ext' TF Z
    · rw [Category.assoc, nF_snd, ← Category.assoc, Category.assoc (ρ γ).asIso.hom]
      erw [hw, hw']
      rw [Category.id_comp, Category.comp_id]
    · have hq : b - liftLa (ι γ)⁻¹ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
        rw [← Submodule.Quotient.eq]
        exact hab.trans (liftLa_spec (ι γ)⁻¹ a).symm
      have L : (w ≫ nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).asIso.hom (hρ γ)) ≫ toU TF Z =
          i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left ≫ (nu hpq hA Xo (ι γ)⁻¹).φ := by
        rw [Category.assoc, nF_toU, ← Category.assoc, sec_toU TF Z b w hw hb, Category.assoc, Category.assoc]
      have R : ((ρ γ).asIso.hom ≫ w') ≫ toU TF Z = (ρ γ).asIso.hom ≫ i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta a).left := by
        rw [Category.assoc, sec_toU TF Z a w' hw' ha]
      rw [L, R, GlobalTheory.LevelActionLaws.eta_congr Xo hq, (nu_spec hpq hA Xo (ι γ)⁻¹).2.1 a,
        ← Category.assoc (pullback.fst _ _), ← GlobalTheory.CompLevelStab.mvF_fst]
      simp only [← Category.assoc]
      rw [← hρ γ]
end GlobalTheory.EqvInterior
end
end

section
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
theorem _root_.GlobalTheory.T.interior_equivariant_action_invariant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹) → ∃ n : Γ → ((GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left), GlobalTheory.EqvAct.IsEqvAct ρ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)) n ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ (𝟙 (V₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z)) n := by
  first | exact @_root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior | exact _root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior | (intros; apply _root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior <;> assumption)
end
end

section
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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EqvAct
theorem equivariant_action_ext : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∃ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA1 Γ _ ι ρ hact X' _ φ ℓ ρ' hN hproj hℓ hℓφ hρ
  have hA : l.A.Coprime l.M := by rw [hA1]; exact Nat.coprime_one_left _
  obtain ⟨n, hn, hη⟩ := _root_.GlobalTheory.T.interior_equivariant_action_invariant hP E H Dw l Xo c TF Z hpq hA Γ ι ρ (GlobalTheory.T.interiorLevelAction_eq_restriction_levelMove_inv E H Dw l Xo c TF Z hpq hA Γ ι ρ hact)
  haveI := hℓ
  haveI : AlgebraicGeometry.IsNoetherian X' := isNoetherian_of_isProjOver hproj
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' := (isNormalScheme_iff_pred X').mp hN
  have hne : Nonempty (V₀ TF.Y Z) :=
    ⟨⟨genPt Z, (j_mem_barComp Z _).2 (CompSplitPfB.cspB_genPt_mem Z)⟩⟩
  haveI : IsDominant ℓ := ⟨ℓ.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hG' : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian (pullG TF Z φ) :=
    IsSemiAbelian.pullback _ _ TF.Y.t.semi
  have hcomp : j₀ TF.Y Z ≫ (barComp TF.Y Z).ι = ℓ ≫ φ ≫ (barComp TF.Y Z).ι := by
    rw [← Category.assoc, hℓφ]
  have hκ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (φ ≫ (barComp TF.Y Z).ι) ℓ
    ((isGrpPullback_pullψ TF Z (j₀ TF.Y Z)).congr hcomp rfl)
  obtain ⟨κ, hκ, hκψ⟩ : ∃ κ : (pullG TF Z (j₀ TF.Y Z)).left ⟶ (pullG TF Z φ).left,
      IsGrpPullback (pullG TF Z (j₀ TF.Y Z)) (pullG TF Z φ) ℓ κ ∧ κ ≫ pullψ TF Z φ = pullψ TF Z (j₀ TF.Y Z) :=
    ⟨_, hκ, pullback.lift_fst _ _ _⟩
  have hκw : κ ≫ (pullG TF Z φ).hom = (pullG TF Z (j₀ TF.Y Z)).hom ≫ ℓ := hκ.1.w
  have hM : ∀ γ, ∃ M : (pullG TF Z φ).left ⟶ (pullG TF Z φ).left,
      IsGrpPullback (pullG TF Z φ) (pullG TF Z φ) (ρ' γ).asIso.hom M ∧ κ ≫ M = n γ ≫ κ := fun γ =>
    exists_isGrpPullback_extend hP.p22 X' (V₀ TF.Y Z) hS ℓ (ρ γ).asIso.hom (ρ' γ).asIso.hom (hρ γ) (pullG TF Z φ) hG' (pullG TF Z (j₀ TF.Y Z)) κ hκ
      (n γ) (hn.1 γ)
  choose m hm hmκ using hM
  have huniq := eq_of_comp_eq_of_isGrpPullback hS ℓ (pullG TF Z φ) hG' (pullG TF Z (j₀ TF.Y Z)) κ hκ
  have hact' : ∀ a : 𝓞 E, κ ≫ ((pullAct TF Z φ).act a).left = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ := by
    intro a
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      change κ ≫ (((pullAct TF Z φ).act a).left ≫ pullψ TF Z φ) = _ ≫ (κ ≫ pullψ TF Z φ)
      rw [pullAct_pullψ, ← Category.assoc, hκψ, pullAct_pullψ]
    · rw [Category.assoc, Category.assoc]
      change κ ≫ (((pullAct TF Z φ).act a).left ≫ (pullG TF Z φ).hom) = _ ≫ (κ ≫ (pullG TF Z φ).hom)
      rw [Over.w, hκw, ← Category.assoc, Over.w]
  refine ⟨m, ⟨hm, fun γ a => ?_, fun γ₁ γ₂ => ?_⟩, ?_⟩
  · refine huniq _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, Over.w, (hm γ).1.w, ← Category.assoc, Over.w]
    · calc κ ≫ ((pullAct TF Z φ).act a).left ≫ m γ
          = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ ≫ m γ := by rw [← Category.assoc, hact', Category.assoc]
        _ = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ n γ ≫ κ := by rw [hmκ]
        _ = n γ ≫ ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ := by
          rw [← Category.assoc, hn.2.1 γ a, Category.assoc]
        _ = n γ ≫ κ ≫ ((pullAct TF Z φ).act a).left := by rw [hact']
        _ = κ ≫ m γ ≫ ((pullAct TF Z φ).act a).left := by rw [← Category.assoc, ← hmκ, Category.assoc]
  · refine huniq _ _ ?_ ?_
    · rw [(hm _).1.w, Category.assoc, (hm γ₁).1.w, ← Category.assoc, (hm γ₂).1.w, Category.assoc, map_mul,
        Aut.mul_asIso]
      rfl
    · calc κ ≫ m (γ₁ * γ₂) = n (γ₁ * γ₂) ≫ κ := hmκ _
        _ = n γ₂ ≫ n γ₁ ≫ κ := by rw [hn.2.2, Category.assoc]
        _ = n γ₂ ≫ κ ≫ m γ₁ := by rw [hmκ]
        _ = κ ≫ m γ₂ ≫ m γ₁ := by rw [← Category.assoc, ← hmκ, Category.assoc]
  · intro γ a b hab w w' hw hw' hwb hwa
    have lift : ∀ v : V₀ TF.Y Z ⟶ (pullG TF Z φ).left, v ≫ (pullG TF Z φ).hom = ℓ →
        ∃ u : V₀ TF.Y Z ⟶ (pullG TF Z (j₀ TF.Y Z)).left, u ≫ (pullG TF Z (j₀ TF.Y Z)).hom = 𝟙 _ ∧
          u ≫ pullψ TF Z (j₀ TF.Y Z) = v ≫ pullψ TF Z φ ∧ u ≫ κ = v := by
      intro v hv
      have e : (v ≫ pullψ TF Z φ) ≫ TF.Y.t.G.hom = 𝟙 _ ≫ j₀ TF.Y Z ≫ (barComp TF.Y Z).ι := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (v ≫ (pullG TF Z φ).hom) ≫ _ = _
        rw [hv, Category.id_comp, hcomp]
      refine ⟨pullback.lift _ _ e, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, ?_⟩
      apply pullback.hom_ext
      · rw [Category.assoc]
        change _ ≫ (κ ≫ pullψ TF Z φ) = v ≫ pullψ TF Z φ
        rw [hκψ]; exact pullback.lift_fst _ _ _
      · rw [Category.assoc]
        change _ ≫ (κ ≫ (pullG TF Z φ).hom) = v ≫ (pullG TF Z φ).hom
        rw [hκw, ← Category.assoc]
        change (pullback.lift _ _ e ≫ pullback.snd _ _) ≫ ℓ = _
        rw [pullback.lift_snd, Category.id_comp, hv]
    obtain ⟨u, hu1, hu2, hu3⟩ := lift w hw
    obtain ⟨u', hu1', hu2', hu3'⟩ := lift w' hw'
    have := hη γ a b hab u u' hu1 hu1' (by rw [hu2, hwb]) (by rw [hu2', hwa])
    rw [← hu3, ← hu3', Category.assoc, hmκ, ← Category.assoc, this, Category.assoc]
end GlobalTheory.EqvAct
end
end

section
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
theorem _root_.GlobalTheory.T.equivariant_action_eq_of_agree_on_generators : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∃ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m := by
  first | exact @_root_.GlobalTheory.EqvAct.equivariant_action_ext | exact _root_.GlobalTheory.EqvAct.equivariant_action_ext | (intros; apply _root_.GlobalTheory.EqvAct.equivariant_action_ext <;> assumption)
end
end

section
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
namespace GlobalTheory.EqvAct
theorem equivariant_linearization_pullback : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed (Xo := Xo) (c := c) → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∃ (G' : Over X') (_ : GrpObj G') (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA hF I g hI hMb Γ _ _ ι ρ hU hAct X' _ φ ℓ ρ' hN hPr hO hj heq
  obtain ⟨m, hm, hmv⟩ := _root_.GlobalTheory.T.equivariant_action_eq_of_agree_on_generators hP E H Dw l Xo c TF Z hpq hA Γ ι ρ hAct X' φ ℓ ρ' hN hPr hO hj heq
  have hT := GlobalTheory.T.torsion_fibre_injects_levelModule E H Dw l Xo c TF Z hpq hA I g hI hMb Γ ι ρ hAct X' φ ℓ ρ' hN hPr hO hj heq m hm hmv
  exact ⟨pullG TF Z φ, inferInstance, pullψ TF Z φ, pullAct TF Z φ, m,
    isGrpPullback_pullψ TF Z φ, pullAct_pullψ TF Z φ, hm.1, hm.2.1, hm.2.2,
    GlobalTheory.T.fibre_action_trivial_of_fixed_point_residue_field E H Dw l Xo c TF Z hpq hA I g hI hMb Γ ι hU X' φ ρ' hN hPr m hm hT⟩
end GlobalTheory.EqvAct
end
end

section
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
theorem _root_.GlobalTheory.T.equivariant_linearization_pullback_compat : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed (Xo := Xo) (c := c) → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∃ (G' : Over X') (_ : GrpObj G') (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m := by
  first | exact @_root_.GlobalTheory.EqvAct.equivariant_linearization_pullback | exact _root_.GlobalTheory.EqvAct.equivariant_linearization_pullback | (intros; apply _root_.GlobalTheory.EqvAct.equivariant_linearization_pullback <;> assumption)
end
end

section
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
namespace GlobalTheory.HodgeLin
theorem hodgeLineBundle_rationally_linear : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed (Xo := Xo) (c := c) → ∃ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) ∧ ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → RatLin ρ' (δ.pull φ) (LB.isLB_pull hδ φ) := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA hF
  obtain ⟨hI, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  obtain ⟨φ₀, f₀, hφ₀, hD⟩ := GlobalTheory.T.exists_cartierDivisor_det_lieEigenparts_toroidal E H Dw l Xo c TF Z
  obtain ⟨D, hDp, hDe⟩ := hD (GlobalTheory.HodgeLin.offCM H)
  refine ⟨toLB D, isLB_toLB D, ?_, ?_⟩
  · rw [hDp]
    have key : ∀ (L L' : LB (Y₀ TF.X Z)) (hL : L.IsLB) (hL' : L'.IsLB), L = L' → cls L hL = cls L' hL' := by
      rintro _ _ _ _ rfl; rfl
    exact key _ _ _ _ (congrArg (LL₀ TF.X Z) (GlobalTheory.HodgeLin.exOf_hodgeWt Dw)).symm
  · intro I g hI' hMb Γ _ _ ι ρ hU hAct X' _ φ ℓ ρ' hN hP' hO hj heq
    obtain ⟨G', _, ψ, act', m, hE⟩ := _root_.GlobalTheory.T.equivariant_linearization_pullback_compat hP E H Dw l Xo c TF Z hpq hA hF I g hI' hMb Γ ι ρ hU hAct X' φ ℓ ρ' hN hP' hO hj heq
    obtain ⟨v, hv⟩ := GlobalTheory.GenInterior.exists_j₀_eq_genericPoint E H Dw l Xo c TF Z
    have hd : IsDominant φ := ⟨by
      refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
      rw [← (genericPoint_spec (X₀ TF.Y Z)).def]
      exact closure_mono (Set.singleton_subset_iff.2 ⟨ℓ v, by rw [← Scheme.Hom.comp_apply, hj, hv]⟩)⟩
    haveI : Nonempty (V₀ TF.Y Z) := ⟨v⟩
    haveI : IsDominant ℓ := ⟨ℓ.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
    have hρ : ∀ γ, (ρ' γ).asIso.hom ≫ φ ≫ s₀ TF.Y Z = φ ≫ s₀ TF.Y Z := fun γ => by
      refine ext_of_isDominant ℓ ?_
      rw [← Category.assoc, ← heq, Category.assoc, ← Category.assoc ℓ φ, hj]
      exact hAct.1 γ
    exact GlobalTheory.T.lieDeterminant_linearisation_equivariant_pullback E H Dw l Xo c TF Z φ₀ f₀ (GlobalTheory.HodgeLin.offCM H) D hφ₀ hDe Γ X' φ ρ' hd hρ G' ψ act' m hE
end GlobalTheory.HodgeLin
end
end

section
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
theorem _root_.GlobalTheory.T.hodgeLineBundle_rational_linear_equiv_class : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed (Xo := Xo) (c := c) → ∃ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) ∧ ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → RatLin ρ' (δ.pull φ) (LB.isLB_pull hδ φ) := by
  first | exact @_root_.GlobalTheory.HodgeLin.hodgeLineBundle_rationally_linear | exact _root_.GlobalTheory.HodgeLin.hodgeLineBundle_rationally_linear | (intros; apply _root_.GlobalTheory.HodgeLin.hodgeLineBundle_rationally_linear <;> assumption)
end
end

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
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
namespace GlobalTheory.OrbitSep
set_option maxHeartbeats 2000000 in
theorem separate_orbits_by_cusp (hP2 : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSg : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS)
    (hLie : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7}
    {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂))
    {I : Ideal (𝓞 D.host.E)} {g : ℕ} (hI : NeatPrime I g ((T.Q.Dw j).p + (T.Q.Dw j).q)) (hM : Y.d.l₂.Mb ≤ I)
    (hS : ∀ γ ∈ S, UnipAt I γ) (s : ℕ)
    (hs : (T.Q.Dw j).p + (T.Q.Dw j).q + ((T.Q.Dw j).dim + 1).choose 2 + 1 ≤ s) (Z : Comp Y.d.Xo₂ Y.d.c₂) :
    ∃ y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ, LiesOn Z y ∧
      ∀ [Fintype {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)}]
        (a : {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)} → ℂ),
        (∀ u ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) ((s : ℤ) • hodgeWt (T.Q.Dw j)) 0),
          ∑ h, a h * evR Y.d.Xo₂ Y.d.c₂ u (move Y.d.Xo₂ Y.d.c₂ (h.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) = 0) → a = 0 := by
  have hP : _root_.GlobalTheory.CovTop.Hypotheses'' := _root_.GlobalTheory.T.covering_topology_refinement hP2
  have hA : Y.d.l₂.A = 1 := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := hA ▸ Nat.coprime_one_left _
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hdim : 1 ≤ (T.Q.Dw j).dim := Nat.mul_pos (Nat.mul_pos (by omega) hp) hq
  have hfl : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) := by
    refine Nat.mul_pos (by omega) ?_
    exact Nat.choose_pos (by omega)
  obtain ⟨TF⟩ : Nonempty (TorFlag Y.d.Xo₂ Y.d.c₂) :=
    _root_.GlobalTheory.T.torFlag_nonempty_of_one_le_dimFlag hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hfl
  have hF := hY.geo
  have hV := GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hF
  obtain ⟨hint, hsm, hpr, hgc, hsurj, hnorm, hgen⟩ := GlobalTheory.T.compactificationComponent_integral_smooth_projective _ _ _ _ _ _ TF Z hF
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_complexFramedPoint_over_componentGenericPoint _ _ _ _ Y.d.Xo₂ Y.d.c₂ Z
  have hyZ : LiesOn Z y := fun s => hy s ▸ (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)).mem
  refine ⟨y, hyZ, fun a ha => ?_⟩
  have lift : ∀ w : FrPt Y.d.Xo₂ Y.d.c₂ ℂ, LiesOn Z w → ∃ v : Sp ℂ ⟶ V₀ TF.Y Z, v ≫ i₀ TF.Y Z = ptF w := fun w hw =>
    ⟨IsOpenImmersion.lift (i₀ TF.Y Z) (ptF w) (by
      rintro _ ⟨s, rfl⟩
      exact ⟨⟨_, (j_mem_barComp Z _).2 (hw s)⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨v₁, hv₁⟩ := lift y hyZ
  choose v hv using fun h : {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y)} => lift _ h.2
  obtain ⟨Γ, ρ, hΓ, hρ, hmem⟩ := GlobalTheory.T.componentStabilizer_acts_by_levelChange _ _ _ _ _ _ TF.Y Z hpq hA S
  obtain ⟨X', W, φ, ℓ, ρ', q, sW, hint', n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ :=
    GlobalTheory.T.equivariant_normal_projective_compactification Y.d.c₂.F _ _ (s₀ TF.Y Z) (j₀ TF.Y Z) Γ ρ hpr ⟨v₁ (IsLocalRing.closedPoint ℂ)⟩ hnorm hρ.1
  obtain ⟨δ, hδ, eδ, hlin⟩ := _root_.GlobalTheory.T.hodgeLineBundle_rational_linear_equiv_class hP2 _ _ _ _ _ _ TF Z hpq hA hF
  obtain ⟨N, hN, eN⟩ := GlobalTheory.T.exists_descent_linearised_lineBundle_finiteGroup_quotient Y.d.c₂.F X' W q sW Γ ρ' _ _ (n7 ▸ n2) n6
    (hlin I g hI hM Γ Γ.subtype ρ (fun γ => hS _ (hΓ γ.2)) hρ X' φ ℓ ρ' n1 n2 n3 n4 n5)
  let K := CanonLB.all (s₀ TF.Y Z) (T.Q.Dw j).dim
  obtain ⟨κ, hκ, eκ, θ, hθ⟩ := GlobalTheory.T.exists_toroidalCanonicalBundle_weight_line _ _ _ _ _ _ TF Z hpq hF K
  set m := ((T.Q.Dw j).dim + 1).choose 2 + 1 with hm
  obtain ⟨t, rfl⟩ : ∃ t, s = m + t := Nat.exists_eq_add_of_le (by omega)
  obtain ⟨N', hN', eN'⟩ := cls_surj (t • cls δ hδ - cls κ hκ)
  obtain ⟨B, hB, eB⟩ := cls_surj (m • cls δ hδ + cls N' hN')
  have C := common₀ TF.X Z
  have nef : ∀ (L : LB (X₀ TF.Y Z)) (hL : L.IsLB) (w : AllWt.Weight (T.Q.Dw j)), GapGe 0 w →
      CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z w) (isLB_L₀ TF.X Z w) →
      (letI := algebraΓOfHom (s₀ TF.Y Z); IsNef Y.d.c₂.F L) := fun L hL w hw e =>
    GlobalTheory.T.isNefLineBundle_of_pullback_surjective_projective _ _ _ _ _ _ L hL _ _ (π₀_s₀ TF.X Z) hpr hV.2.1 hsurj e
      (_root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hQ.nef hLie _ _ _ _ _ _ TF Z hF w hw)
  have ens : ∀ n : ℕ, cls (L₀ TF.X Z ((n : ℤ) • hodgeWt (T.Q.Dw j))) (isLB_L₀ TF.X Z _) =
      n • cls (L₀ TF.X Z (hodgeWt (T.Q.Dw j))) (isLB_L₀ TF.X Z _) := fun n => by
    rw [natCast_zsmul]; exact cls_nsmul (common₀ TF.X Z) n _
  have nefN' := nef N' hN' ((t : ℤ) • hodgeWt (T.Q.Dw j) - kapBase _) (gapGe_sub_kapBase _ (by omega)) (by
    have h := GlobalTheory.HSApp.cls_common_add (common₀ TF.X Z) ((t : ℤ) • hodgeWt (T.Q.Dw j) - kapBase _) (kapBase _)
    rw [sub_add_cancel] at h
    rw [eN', map_sub, map_nsmul, eδ, eκ, ← ens, sub_eq_iff_eq_add]
    exact h)
  have hKB := isLB_tens K.isLB hB
  have hθB := LB.isLB_div hκ K.isLB
  obtain ⟨Φ, hΦ, hval⟩ := GlobalTheory.T.exists_cuspRule_of_boundaryVanishing_componentSection D T j Y e o hY hf Z TF (((m + t : ℕ) : ℤ) • hodgeWt (T.Q.Dw j)) _
    (isLB_tens hθB hKB) (by
      rw [cls_tens hθB hKB, cls_div hκ K.isLB, cls_tens K.isLB hB, eB, eN', ens, ← eδ, ← map_nsmul]
      refine congrArg _ ?_
      have key : ∀ (A : Type 1) [AddCommGroup A] (a b k : A) (m t : ℕ),
          b - k + (k + (m • a + (t • a - b))) = (m + t) • a := fun A _ a b k m t => by
        rw [add_nsmul, ← add_assoc, sub_add_cancel, add_left_comm, add_sub_cancel]
      exact key _ _ _ _ _ _)
  choose k hk using fun h => exists_chart_pt hKB (v h ≫ j₀ TF.Y Z)
  choose k' hk' using fun h => exists_chart_pt hθB (v h ≫ j₀ TF.Y Z)
  choose lam hlam using fun h => hval _ (v h) (hv h) (k' h, k h) (fun s hs => ⟨hk' h hs, hk h hs⟩)
  have hc : ∀ h, H0.val (v h ≫ j₀ TF.Y Z) (k' h) le_top (hk' h) (H0.ofSec (s₀ TF.Y Z) ⊤ θ) ≠ 0 := fun h =>
    val_ofSec_ne_zero _ θ _ _ _ fun s => hθ ▸ ⟨v h s, rfl⟩
  have hvρ : ∀ h, v h = v₁ ≫ (ρ ⟨h.1, hmem _ h.1.2 y hyZ h.2⟩).asIso.hom := fun h => by
    rw [← cancel_mono (i₀ TF.Y Z), hv, Category.assoc, hρ.2 _ ℂ y v₁ hv₁]; rfl
  have h1 : LiesOn Z (move Y.d.Xo₂ Y.d.c₂ ((1 : S) : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) := by
    rw [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']; exact hyZ
  have key := GlobalTheory.T.sections_separate_quotient_generic_fibre_descends hP2.q15 hQ.nef hP2.q16 Y.d.c₂.F (algebraMap _ ℂ) (X₀ TF.Y Z) X' W (V₀ TF.Y Z) (s₀ TF.Y Z) _ φ q sW
    (j₀ TF.Y Z) ℓ hpr hgc hdim n2 n8 n10 n11 n7 inferInstance n3 n4 K δ N' B hδ hN' hB N hN m eN
    (nef δ hδ _ gapGe_hodgeWt eδ) (_root_.GlobalTheory.T.hodgeLineBundle_bigness_on_shimuraVariety hP2 hG hQ hSg hKS _ _ _ _ _ _ TF Z hp hq hF δ hδ eδ) nefN' (by omega) eB _ v
    (fun h h' e => ?_) (fun h => ?_) (fun h h' => ?_) ⟨⟨1, h1⟩, fun s => hgen _ ?_⟩ k hk
    (fun h => a h * (lam h * H0.val (v h ≫ j₀ TF.Y Z) (k' h) le_top (hk' h) (H0.ofSec (s₀ TF.Y Z) ⊤ θ))) fun u => ?_
  · funext h
    exact (mul_eq_zero.1 (congrFun key h)).resolve_right (mul_ne_zero (lam h).ne_zero (hc h))
  · have e' := (hv h').symm.trans (e ▸ hv h)
    have e₂ : move Y.d.Xo₂ Y.d.c₂ (h'.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y =
        move Y.d.Xo₂ Y.d.c₂ ((h.1 * h'.1⁻¹ : S) : LevelAut (T.Q.Dw j) Y.d.l₂)
          (move Y.d.Xo₂ Y.d.c₂ (h.1 : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ y) := by
      rw [← LevDesc.move_mul hpq hA']; simp
    rw [e₂] at e'
    have := GlobalTheory.T.levelAutomorphism_unipotent_fixes_complexPoint_eq_one _ _ _ _ _ _ hpq hA I g hI hM _ (hS _ (h.1 * h'.1⁻¹).2) _ e'
    exact Subtype.ext (mul_inv_eq_one.1 (Subtype.ext this))
  · have e₁ : TF.Y.j ≫ TF.Y.s = pullback.snd _ _ := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over]
      exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
    rw [← Category.assoc (j₀ _ _), j₀_ι, Category.assoc, e₁, ← Category.assoc, hv]
    exact pullback.lift_snd _ _ _
  · rw [hvρ h, hvρ h', Category.assoc, Category.assoc, reassoc_of% n5, reassoc_of% n5, n6.comp_eq, n6.comp_eq]
  · change (v ⟨1, h1⟩ ≫ i₀ TF.Y Z) s = _
    rw [hv]
    simp only [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']
    exact hy s
  · let P := tensChart hθB hKB
    have hu := ha _ (hΦ (P.mul (H0.ofSec (s₀ TF.Y Z) ⊤ θ) u) fun x hx => ?_)
    · rw [← hu]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [hlam, mul_assoc, mul_assoc]
      exact congrArg (fun x => a h * (lam h * x)) (P.val_mul _ _ (k' h, k h) _ le_top (hk' h) (hk h) _).symm
    · obtain ⟨τ, ha', hb', hc'⟩ := P.cover x
      have hu := (isUnit_ger_iff _ hc').2 hx
      rw [ger_toSec, P.germ_mul _ _ τ x _ ha' hb' hc', H0.germ_ofSec] at hu
      exact hθ ▸ (isUnit_ger_iff θ ha').1 (isUnit_of_mul_isUnit_left hu)
end GlobalTheory.OrbitSep
namespace GlobalTheory.OrbitSep
open Formalism.MainNotions _root_.Formalism.L2.Theta GlobalTheory.DegVal GlobalTheory.DegCmp GlobalTheory.BadCount
theorem exists_cusp_regular_level_determinant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ S u * f = 0 → f = 0 := by
  classical
  intro hP2 hG hQ hSg hKS hLie D T hT j hp hq hf hj Y e o hY _ hg fr S hS
  have hA : Y.d.l₂.A = 1 := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := hA ▸ Nat.coprime_one_left _
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hdat := hT.pins.2.2.2 j hj
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hdat.1, hdat.2.1]; exact Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hT.pins.2.1.1]
  obtain ⟨I, g, hI, hMb, hU⟩ := GlobalTheory.T.exists_neatPrime_levelAutSubgroup_unipotent D _ (T.Q.Dw j) Y.d.l₂ ⟨_, hM⟩ (hr ▸ hg) fr S hS
  have hs : (T.Q.Dw j).p + (T.Q.Dw j).q + ((T.Q.Dw j).dim + 1).choose 2 + 1 ≤ cZeroN D j := by
    have := (cZeroN_isLeast D j).1.2.1
    rw [hr, Datum.dim, GlobalTheory.FlagDim.finrank_host_div_two, hdat.1, hdat.2.1]
    omega
  choose y hyZ hy using _root_.GlobalTheory.OrbitSep.separate_orbits_by_cusp hP2 hG hQ hSg hKS hLie Y hY hf hp hq S hI hMb hU _ hs
  have : Finite (Comp Y.d.Xo₂ Y.d.c₂) := CompFin.finite_comp _ _
  let G := wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0
  let ev : Comp Y.d.Xo₂ Y.d.c₂ → Y.V G →ₗ[Y.d.c₂.F] (S → ℂ) := fun Z => LinearMap.pi fun h =>
    evalL (K := Y.d.c₂.F) (fun R _ _ => FrPt Y.d.Xo₂ Y.d.c₂ R) (fun φ y z => FrMap φ y z)
      (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ (y Z)) ∘ₗ (Y.V G).subtype
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_vector_groupDeterminants_ne_zero Y.d.c₂.F (Y.V G) S _ ev
    (fun Z => {h : S // LiesOn Z (move Y.d.Xo₂ Y.d.c₂ (h : LevelAut (T.Q.Dw j) Y.d.l₂)⁻¹ (y Z))}) (fun _ h => h.1)
    (fun Z => (AllWt.suppOn Z).comap (Y.V G).subtype)
    (fun Z => ⟨⟨1, by rw [OneMemClass.coe_one, inv_one, LevDesc.move_one hpq hA']; exact hyZ Z⟩, rfl⟩)
    (fun Z v hv h hh => hv ℂ _ ((AllWt.liesOff_iff Z _).2 fun h' => hh ⟨⟨h, h'⟩, rfl⟩))
    (fun Z a ha => hy Z a fun u hu => ha ⟨u, hu.1⟩ hu.2)
  have hu' := AllWt.cuspW_le_secZ _ u.2
  refine ⟨u, u.2, GlobalTheory.T.integerExponentSection_mul_eq_zero_imp_eq_zero _ _ _ _ _ _ _ _ (LevDesc.levDet_mem_secZ hpq hA' hu') fun Z => ⟨y Z, hyZ Z, ?_⟩⟩
  have ht := GlobalTheory.FlagTan.fromTest_of_isLocalRing (y Z)
  let χ : Rul Y.d.Xo₂ Y.d.c₂ →+* ℂ :=
    { toFun := fun f => evR Y.d.Xo₂ Y.d.c₂ f (y Z)
      map_one' := evalAt_one _ _ _ ht
      map_mul' := fun f g => evalAt_mul _ _ f g _
      map_zero' := evalAt_zero _ _ _
      map_add' := fun f g => evalAt_add _ _ f g _ }
  have e₁ := χ.map_det (LevDesc.levMat Y.d.Xo₂ Y.d.c₂ S u)
  refine fun h0 => hu Z ?_
  rw [← h0]
  refine Eq.trans ?_ (e₁.symm.trans ?_)
  · congr 1
    ext h g
    exact (GlobalTheory.LevelKeeps.evR_transl hpq hA' _ hu' (y Z)).symm
  · change χ _ = χ _
    unfold levDet
    congr!
end GlobalTheory.OrbitSep
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbits_separated_by_regular_cusp : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂) (S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ S u * f = 0 → f = 0 := by
  first | exact @_root_.GlobalTheory.OrbitSep.exists_cusp_regular_level_determinant | exact _root_.GlobalTheory.OrbitSep.exists_cusp_regular_level_determinant | (intros; apply _root_.GlobalTheory.OrbitSep.exists_cusp_regular_level_determinant <;> assumption)
end
