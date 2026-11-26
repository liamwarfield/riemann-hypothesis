module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSaturated
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PfOmega

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverSystemCechPullNatural
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechConnectingPullNatural
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechConnectingPullNatural
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

noncomputable section

namespace GlobalTheory.CompanionTheory.CechOne

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') (s : G.obj.obj (op ⊤)) :
    hPull f φ 0 ((Sheaf.H.equiv₀ G isTerminalTop).symm s) =
      (Sheaf.H.equiv₀ G' isTerminalTop).symm
        (G'.obj.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op (φ.hom.app (op ⊤) s)) := by
  have hx : (Sheaf.H.equiv₀ G isTerminalTop).symm s =
      GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s) := by
    rw [AddEquiv.symm_apply_eq]
    refine Eq.symm ((GlobalTheory.SiteCoh.equiv₀_terminalEquiv G isTerminalTop _).trans ?_)
    exact (GlobalTheory.SheafLES.equivZero.{0} G ⊤).apply_symm_apply s
  rw [hx, AddEquiv.eq_symm_apply]
  have h1 : hPull f φ 0 (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s)) =
      GlobalTheory.SiteCoh.terminalEquiv G' 0 isTerminalTop
        (pull.{0, 0} f φ 0 (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤)
          ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s)) := by
    simp only [hPull, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
  rw [h1]
  refine (GlobalTheory.SiteCoh.equiv₀_terminalEquiv G' isTerminalTop _).trans ?_
  refine (SheafPull.equivZero_pull f φ (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤) _).trans ?_
  rw [AddEquiv.apply_symm_apply]

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
    {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (Q.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op
        (φ.app (op ⊤) s))).1 := by
  funext t
  change res Q (inter_le_map f V U τ hτ t) (φ.app (op (inter V (τ ∘ t))) (res P _ s)) =
    res Q _ (Q.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op (φ.app (op ⊤) s))
  rw [app_res_map, res_res]
  change _ = res Q _ (res Q _ (φ.app (op ⊤) s))
  rw [res_res]

theorem cechHOneEquiv_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : GroundTheory.Arith.SchemeCoh.CechAcyclic S.X₂.obj V) (hS' : S'.ShortExact) [Injective S'.X₂]
    (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : GroundTheory.Arith.SchemeCoh.CechAcyclic S'.X₂.obj U) (α : S ⟶ S'.map (push f))
    (x : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V 1) :
    (cechHOneEquiv U hU hS' hC' hI' : GroundTheory.Arith.SchemeCoh.cechH S'.X₁.obj U 1 ≃+ Sheaf.H.{0} S'.X₁ 1) (cechPullH f α.τ₁.hom V U τ hτ 1 x) =
      hPull f α.τ₁ 1 ((cechHOneEquiv V hV hS hC hI : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V 1 ≃+ Sheaf.H.{0} S.X₁ 1) x) := by
  obtain ⟨s, hs⟩ := cechOneProj_surjective V hV hC hI x
  rw [← hs]
  have h₁₂ : ∀ W y, α.τ₂.hom.app W (S.f.hom.app W y) = S'.f.hom.app _ (α.τ₁.hom.app W y) := fun W y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g => g.hom) α.comm₁₂.symm) W) y
  have h₂₃ : ∀ W y, α.τ₃.hom.app W (S.g.hom.app W y) = S'.g.hom.app _ (α.τ₂.hom.app W y) := fun W y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g => g.hom) α.comm₂₃.symm) W) y
  have hmap : cechPullH f α.τ₁.hom V U τ hτ 1 (cechOneProj V hC s) =
      cechOneProj U hC' (S'.X₃.obj.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op
        (α.τ₃.hom.app (op ⊤) s)) := by
    change cechPullH f α.τ₁.hom V U τ hτ (0 + 1) (hC.delta 0 (globalCocycle S.X₃.obj V s)) =
      hC'.delta 0 (globalCocycle S'.X₃.obj U _)
    refine (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ 0 _).trans ?_
    exact congrArg (hC'.delta 0) (Subtype.ext (pullCoch_globalCocycle f α.τ₃.hom V U τ hτ s))
  rw [hmap, cechHOneEquiv_cechOneProj, cechHOneEquiv_cechOneProj]
  change H.δ hS' 0 1 rfl ((Sheaf.H.equiv₀ S'.X₃ isTerminalTop).symm _) =
    hPull f α.τ₁ 1 (H.δ hS 0 1 rfl ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s))
  rw [GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α 0 _]
  exact congrArg (H.δ hS' 0 1 rfl) (hPull_zero f α.τ₃ s).symm

end GlobalTheory.CompanionTheory.CechOne
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechConnectingPullNaturalStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_connecting_pull_natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj V) (hS' : S'.ShortExact) [Injective S'.X₂]
    (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : CechAcyclic S'.X₂.obj U) (α : S ⟶ S'.map (push f))
    (x : cechH S.X₁.obj V 1),
    (cechHOneEquiv U hU hS' hC' hI' : cechH S'.X₁.obj U 1 ≃+ Sheaf.H.{0} S'.X₁ 1) (cechPullH f α.τ₁.hom V U τ hτ 1 x) =
      hPull f α.τ₁ 1 ((cechHOneEquiv V hV hS hC hI : cechH S.X₁.obj V 1 ≃+ Sheaf.H.{0} S.X₁ 1) x) := by
  first | exact @GlobalTheory.CompanionTheory.CechOne.cechHOneEquiv_pull | exact GlobalTheory.CompanionTheory.CechOne.cechHOneEquiv_pull | (intros; apply GlobalTheory.CompanionTheory.CechOne.cechHOneEquiv_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechSheafCohomologyPullCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechSheafCohomologyPullCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechStep

theorem cechHEquivStep_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : GroundTheory.Arith.SchemeCoh.CechAcyclic S.X₂.obj V)
    (hS' : S'.ShortExact) [Injective S'.X₂] (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : GroundTheory.Arith.SchemeCoh.CechAcyclic S'.X₂.obj U)
    (α : S ⟶ S'.map (push f)) (m : ℕ) (e : GroundTheory.Arith.SchemeCoh.cechH S.X₃.obj V (m + 1) ≃+ Sheaf.H.{0} S.X₃ (m + 1))
    (e' : GroundTheory.Arith.SchemeCoh.cechH S'.X₃.obj U (m + 1) ≃+ Sheaf.H.{0} S'.X₃ (m + 1))
    (he : ∀ y, e' (cechPullH f α.τ₃.hom V U τ hτ (m + 1) y) = hPull f α.τ₃ (m + 1) (e y))
    (x : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V (m + 2)) :
    cechHEquivStep U hS' hC' hI' m e' (cechPullH f α.τ₁.hom V U τ hτ (m + 2) x) =
      hPull f α.τ₁ (m + 2) (cechHEquivStep V hS hC hI m e x) := by
  have h₁₂ : ∀ W z, α.τ₂.hom.app W (S.f.hom.app W z) =
      S'.f.hom.app ((Opens.map f).op.obj W) (α.τ₁.hom.app W z) := fun W z => by
    have h := congrArg (fun k => k.hom.app W) α.comm₁₂
    exact (ConcreteCategory.congr_hom h z).symm
  have h₂₃ : ∀ W z, α.τ₃.hom.app W (S.g.hom.app W z) =
      S'.g.hom.app ((Opens.map f).op.obj W) (α.τ₂.hom.app W z) := fun W z => by
    have h := congrArg (fun k => k.hom.app W) α.comm₂₃
    exact (ConcreteCategory.congr_hom h z).symm
  obtain ⟨y, rfl⟩ := (hC.deltaEquiv hI m).surjective x
  have hδ : (hC'.deltaEquiv hI' m).symm (cechPullH f α.τ₁.hom V U τ hτ (m + 2) (hC.deltaEquiv hI m y)) =
      cechPullH f α.τ₃.hom V U τ hτ (m + 1) y := by
    rw [AddEquiv.symm_apply_eq]
    obtain ⟨σ, hσ, rfl⟩ := GroundTheory.Arith.SchemeCoh.exists_cls y
    exact (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ (m + 1)
      ⟨σ, (GroundTheory.Arith.SchemeCoh.mem_cocycles σ).2 hσ⟩).trans rfl
  simp only [cechHEquivStep, AddEquiv.trans_apply, AddEquiv.symm_apply_apply, hδ, he]
  exact (GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α (m + 1) (e y)).symm

end GlobalTheory.CompanionTheory.CechStep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechSheafCohomologyPullCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_sheaf_cohomology_pull_compat : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj V)
    (hS' : S'.ShortExact) [Injective S'.X₂] (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : CechAcyclic S'.X₂.obj U)
    (α : S ⟶ S'.map (push f)) (m : ℕ) (e : cechH S.X₃.obj V (m + 1) ≃+ Sheaf.H.{0} S.X₃ (m + 1))
    (e' : cechH S'.X₃.obj U (m + 1) ≃+ Sheaf.H.{0} S'.X₃ (m + 1))
    (he : ∀ y, e' (cechPullH f α.τ₃.hom V U τ hτ (m + 1) y) = hPull f α.τ₃ (m + 1) (e y))
    (x : cechH S.X₁.obj V (m + 2)),
    cechHEquivStep U hS' hC' hI' m e' (cechPullH f α.τ₁.hom V U τ hτ (m + 2) x) =
      hPull f α.τ₁ (m + 2) (cechHEquivStep V hS hC hI m e x) := by
  first | exact @GlobalTheory.CompanionTheory.CechStep.cechHEquivStep_pull | exact GlobalTheory.CompanionTheory.CechStep.cechHEquivStep_pull | (intros; apply GlobalTheory.CompanionTheory.CechStep.cechHEquivStep_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechH0PullCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechH0PullCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechZero

theorem cechHZeroEquiv_cls {X : TopCat.{0}} {ι : Type} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0})
    (U : ι → Opens X) (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P) (hU : iSup U = ⊤)
    (s : P.obj (op ⊤)) (σ : Cochain P U 0) (h : GroundTheory.Arith.SchemeCoh.d P U 0 σ = 0)
    (hσ : σ = (globalCocycle P U s).1) :
    GroundTheory.Arith.SchemeCoh.cechHZeroEquiv P U hP hU (GroundTheory.Arith.SchemeCoh.cls σ h) = s := by
  subst hσ
  simp only [GroundTheory.Arith.SchemeCoh.cechHZeroEquiv, AddEquiv.trans_apply]
  exact (globalCocycleEquiv P U hP hU).symm_apply_apply s

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
    {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (GroundTheory.Arith.SchemeCoh.res Q (le_top : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤)
        (φ.app (op ⊤) s))).1 := by
  funext t
  change GroundTheory.Arith.SchemeCoh.res Q _ (φ.app _ (GroundTheory.Arith.SchemeCoh.res P _ s)) =
    GroundTheory.Arith.SchemeCoh.res Q _ (GroundTheory.Arith.SchemeCoh.res Q _ (φ.app (op ⊤) s))
  rw [app_res_map, res_res, res_res]

theorem zeroEquiv_eq_equivZero {X : TopCat.{0}} (F : AbSheaf X) (W : Opens X) (x : Sheaf.H'.{0} F 0 W) :
    GlobalTheory.SiteCoh.zeroEquiv F W x = GlobalTheory.SheafLES.equivZero.{0} F W x := by
  obtain ⟨φ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).surjective x
  rw [GlobalTheory.SheafLES.equivZero_mk₀]
  exact GlobalTheory.SiteCoh.zeroEquiv_mk₀ F W φ

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') (z : Sheaf.H.{0} G 0) :
    Sheaf.H.equiv₀ G' isTerminalTop (hPull f φ 0 z) =
      GroundTheory.Arith.SchemeCoh.res G'.obj (le_top : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤)
        (φ.hom.app (op ⊤) (Sheaf.H.equiv₀ G isTerminalTop z)) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop).surjective z
  change Sheaf.H.equiv₀ G' isTerminalTop (GlobalTheory.SiteCoh.terminalEquiv G' 0 isTerminalTop
    (pull.{0, 0} f φ 0 (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤)
      ((GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop).symm
        (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop y)))) = _
  rw [AddEquiv.symm_apply_apply, GlobalTheory.SiteCoh.equiv₀_terminalEquiv,
    GlobalTheory.SiteCoh.equiv₀_terminalEquiv, zeroEquiv_eq_equivZero, zeroEquiv_eq_equivZero,
    GlobalTheory.SheafPull.equivZero_pull]
  rfl

theorem cechHZeroEquivH_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y)
    (hV : iSup V = ⊤) (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G') (x : GroundTheory.Arith.SchemeCoh.cechH G.obj V 0) :
    (GroundTheory.Arith.SchemeCoh.cechHZeroEquivH G' U hU : GroundTheory.Arith.SchemeCoh.cechH G'.obj U 0 ≃+ Sheaf.H.{0} G' 0) (cechPullH f φ.hom V U τ hτ 0 x) =
      hPull f φ 0 ((GroundTheory.Arith.SchemeCoh.cechHZeroEquivH G V hV : GroundTheory.Arith.SchemeCoh.cechH G.obj V 0 ≃+ Sheaf.H.{0} G 0) x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  obtain ⟨s, hs⟩ := globalCocycle_surjective G.obj V G.property hV ⟨σ, (mem_cocycles σ).2 hσ⟩
  have hσs : σ = (globalCocycle G.obj V s).1 := (congrArg Subtype.val hs).symm
  apply (Sheaf.H.equiv₀ G' isTerminalTop).injective
  rw [hPull_zero, cechPullH_cls]
  simp only [GroundTheory.Arith.SchemeCoh.cechHZeroEquivH, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [cechHZeroEquiv_cls G.obj V G.property hV s σ hσ hσs]
  refine cechHZeroEquiv_cls G'.obj U G'.property hU _ _ _ ?_
  rw [hσs]
  exact pullCoch_globalCocycle f φ.hom V U τ hτ s

end GlobalTheory.CompanionTheory.CechZero
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechH0PullCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_h0_pull_compat : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G') (x : cechH G.obj V 0),
    (cechHZeroEquivH G' U hU : cechH G'.obj U 0 ≃+ Sheaf.H.{0} G' 0) (cechPullH f φ.hom V U τ hτ 0 x) =
      hPull f φ 0 ((cechHZeroEquivH G V hV : cechH G.obj V 0 ≃+ Sheaf.H.{0} G 0) x) := by
  first | exact @GlobalTheory.CompanionTheory.CechZero.cechHZeroEquivH_pull | exact GlobalTheory.CompanionTheory.CechZero.cechHZeroEquivH_pull | (intros; apply GlobalTheory.CompanionTheory.CechZero.cechHZeroEquivH_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverSystemCechPullNatural
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechLerayPull

theorem cechHEquiv_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) : ∀ (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : GroundTheory.Arith.SchemeCoh.cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : GroundTheory.Arith.SchemeCoh.cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : GroundTheory.Arith.SchemeCoh.cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  intro n
  induction n with
  | zero =>
    intro G G' _ _ φ x
    exact GlobalTheory.T.cech_h0_pull_compat f V hV U hU τ hτ φ x
  | succ n ih =>
    cases n with
    | zero =>
      intro G G' hG hG' φ x
      obtain ⟨α, hα⟩ := GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift f φ
      rw [← hα]
      exact GlobalTheory.T.cech_connecting_pull_natural f V hV U hU τ hτ (S := injectiveSequence G) (S' := injectiveSequence G')
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hCY V hVB G hG)
        (injectiveSequence_cechAcyclic G V) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hCX U hUB G' hG') (injectiveSequence_cechAcyclic G' U) α x
    | succ m =>
      intro G G' hG hG' φ x
      obtain ⟨α, hα⟩ := GlobalTheory.CompanionTheory.CechLift.exists_injectiveSequence_lift f φ
      rw [← hα]
      exact GlobalTheory.T.cech_sheaf_cohomology_pull_compat f V U τ hτ (S := injectiveSequence G) (S' := injectiveSequence G')
        (injectiveSequence_shortExact G) (injectiveSequence_isCechShortExact hCY V hVB G hG)
        (injectiveSequence_cechAcyclic G V) (injectiveSequence_shortExact G')
        (injectiveSequence_isCechShortExact hCX U hUB G' hG') (injectiveSequence_cechAcyclic G' U) α m _ _
        (fun y => ih (injectiveSequence_goodAcyclic hCY G hG)
          (injectiveSequence_goodAcyclic hCX G' hG') α.τ₃ y) x

end GlobalTheory.CompanionTheory.CechLerayPull
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverSystemCechPullNaturalStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_system_cech_pull_natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  first | exact @GlobalTheory.CompanionTheory.CechLerayPull.cechHEquiv_pull | exact GlobalTheory.CompanionTheory.CechLerayPull.cechHEquiv_pull | (intros; apply GlobalTheory.CompanionTheory.CechLerayPull.cechHEquiv_pull <;> assumption)
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem cechOm_pull_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (hV : iSup V = ⊤)
    (hVaff : ∀ (n : ℕ) (i : Fin (n + 1) → κ), IsAffineOpen (⨅ a, V (i a))) (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (a j : ℕ) (x : CO p V a j),
    cechOmAdd q U hU hUaff a j (cechPull hu V U τ hτ a j x) = pullC u hu a j (cechOmAdd p V hV hVaff a j x) := by
  intro K _ X Y q p u hu κ ι V hV hVaff U hU hUaff τ hτ a j x
  have h1 := GlobalTheory.T.cover_system_cech_pull_natural u.base isCoverSystem_isBasicCover isCoverSystem_isBasicCover V hV
    (fun i => by rw [inter_eq_iInf]; exact hVaff _ i) U hU (fun i => by rw [inter_eq_iInf]; exact hUaff _ i) τ hτ j
    (goodAcyclic_modulesAb (GlobalTheory.HodgeCoh.Omega p a)) (goodAcyclic_modulesAb (GlobalTheory.HodgeCoh.Omega q a))
    (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) x
  have h2 := hPull_omega_pf q p u hu a j (cechHAddEquivH V hV hVaff (GlobalTheory.HodgeCoh.Omega p a) j x)
  exact (congrArg (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).symm h1).trans h2

end CrystallineSemistableComparison.Om.Cech
