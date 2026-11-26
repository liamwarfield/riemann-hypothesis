module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RayEv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem smooth_gtCoord_q {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H]
    (c : GtCoord (⊥ : Ideal R) D 0 H) : Smooth c.q.left := by
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  obtain ⟨-, -, -, -, h1, -⟩ := (GlobalTheory.splitTorus_properties (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1))))).1 D.X
  have : Smooth (splitTorus (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) D.X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ D.X) _
  have H' := (GlobalTheory.UnitRigidity.isPullback_act c.i c.q c.isKernel).map (Over.forget _)
  have a1 : Smooth (snd (splitTorus (Spec (CommRingCat.of (R ⧸ (⊥ : Ideal R) ^ (0 + 1)))) D.X)
      (thickObj R ⊥ 0 H)).left :=
    inferInstanceAs (Smooth (pullback.snd (splitTorus _ D.X).hom (thickObj R ⊥ 0 H).hom))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H'.flip ⟨⟨‹_›, ‹_›⟩, (inferInstance : QuasiCompact c.q.left)⟩ a1

theorem Ray.smooth_q {oa : D.OAct O} (Y : Ray oa) : Smooth Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have hc := smooth_gtCoord_q c
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F

  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ

  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]

  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]

  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst D.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

end GlobalTheory.RayEv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqData
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThRead


set_option maxHeartbeats 1000000 in
theorem eW_jW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, ∀ y, Y.mj.eW i (Z.jW i y) = GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ _ i y
  exact (Z.jW_read i y).trans (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _))

theorem eW_injective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, Function.Injective (Y.mj.eW i) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ _ i
  exact GlobalTheory.Mem.LiftForms.inj_of_norm_sq _ (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i)

theorem li_span : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, LinearIndependent ℂ (fun k => Z.jW i (Pi.single k 1)) ∧
    Submodule.span ℂ (Set.range fun k => Z.jW i (Pi.single k 1)) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i
  have he := eW_injective D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  have hc : (Y.mj.eW i ∘ fun k => Z.jW i (Pi.single k 1)) = fun k =>
      GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i (Pi.single k 1) :=
    funext fun k => eW_jW D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i _
  refine ⟨LinearIndependent.of_comp (Y.mj.eW i) ?_, ?_⟩
  · rw [hc]; exact GlobalTheory.Mem.LiftTheta.goodForm_li R.toRealDat F.lv2 hH.prim.unif false i
  · apply Submodule.map_injective_of_injective he
    rw [Submodule.map_top, Submodule.map_span, ← Set.range_comp, hc]
    exact (GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i).trans
      ((hH.aux.levelW false i _).trans (Y.mj.eW_range i).symm)

theorem closure_span_eq {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {V H : Type} [AddCommGroup V]
    [Module (𝓞 K) V] [AddCommGroup H] [Module ℂ H] (f : V →+ H) (hfs : ∀ (b : 𝓞 K) (x : V), f (b • x) = σ (b : K) • f x)
    (X : Set V) :
    AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' X, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' (Submodule.span (𝓞 K) X : Set V), y = σ (a : K) • x} := by
  set C := AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' X, y = σ (a : K) • x}
  have stab : ∀ (b : 𝓞 K), ∀ z ∈ C, σ (b : K) • z ∈ C := by
    intro b z hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨b * a, x, hx, by rw [smul_smul, ← map_mul]; norm_cast⟩
    | zero => rw [smul_zero]; exact C.zero_mem
    | add _ _ _ _ h1 h2 => rw [smul_add]; exact C.add_mem h1 h2
    | neg _ _ h1 => rw [smul_neg]; exact C.neg_mem h1
  have key : ∀ x ∈ Submodule.span (𝓞 K) X, f x ∈ C := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure ⟨1, f x, ⟨x, hx, rfl⟩, by simp⟩
    | zero => rw [map_zero]; exact C.zero_mem
    | add _ _ _ _ h1 h2 => rw [map_add (f := _)]; exact C.add_mem h1 h2
    | smul b x _ h => rw [hfs]; exact stab b _ h
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, _, ⟨x, Submodule.subset_span hx, rfl⟩, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [← hfs]
    exact key _ (Submodule.smul_mem _ a hx)

theorem chiKs_of_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, (R.FW i).ChiKs := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i g
  have hL := hP.char.base.lev
  have h : ((Formalism.IndefR.FWT.chiC R.toRealDat i g : ℂˣ) : ℂ) ∈ (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)).fieldRange := by
    unfold Formalism.IndefR.FWT.chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine GlobalTheory.ChiDetValues.res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy⟩ := hP.keep.valKs i x hx
    exact ⟨y, hy.symm⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, D.what₂.embLL.injective (hy.trans ((Units.coe_prod _ _).trans (hP.char.base.grp.chiW i g).symm))⟩


set_option maxHeartbeats 1000000 in
theorem lat_of : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m,
    OLatTie D.what₂.embLL (D.what₂.MjLat ((i : ℕ) + 1)) (Z.jW i) ((A3.indefDown (s0Of R F)).M i) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i
  have he := eW_injective D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  have hli := (li_span D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i).1
  have hej := eW_jW D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  have hI := hH.aux.integral i
  have hspan := GlobalTheory.GoodLatDescent.span_MK_good (R.FW i) hI.1 (fun g f => (hI.2.2 g f).1)
    (chiKs_of_pins D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i) F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)
    (fun p => ?_) hP.keep.levKs.2
  swap
  · obtain ⟨y, hy⟩ := hP.keep.levKs.1 p
    exact ⟨y⁻¹, by rw [map_inv₀, hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]; rfl⟩
  have hsg : sg0 D A3.A = D.what₂.embLL := RingHom.ext fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have himg : Y.mj.eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier =
      (R.FW i).j (sg0 D A3.A) '' {y | y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy1, hy2, e⟩ := (Y.mj.eW_lat i x).1 hx
      exact ⟨y, ⟨hy1, hy2⟩, e.symm⟩
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hyM : y ∈ (R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) := by
        rw [← hspan]; exact Submodule.subset_span ⟨hy1, hy2⟩
      obtain ⟨c, -, hcy⟩ := (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i _).1 ⟨y, hyM, rfl⟩
      exact ⟨Z.jW i c, (Y.mj.eW_lat i _).2 ⟨y, hy1, hy2, (hej c).trans hcy⟩, (hej c).trans hcy⟩
  refine GlobalTheory.Mem.LiftTheta.oLatTie_of_closure (fun a => ⟨⟨D.what₂.OtoLL a, D.O_int a⟩, rfl⟩) _ (Y.mj.eW i) he (Z.jW i)
    (GlobalTheory.Mem.LiftTheta.semi_injective _ hli) _
    ((R.FW i).j (sg0 D A3.A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) : Set _)) (fun y => ?_) ?_
  · refine (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i y).trans ?_
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).trans h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).symm.trans h⟩⟩
  · rw [himg, ← hspan]
    exact closure_span_eq (σ := D.what₂.embLL) ((R.FW i).j (sg0 D A3.A)).toAddMonoidHom
      (fun b x => by
        rw [← hsg]
        show (R.FW i).j _ (b • x) = _
        rw [← algebraMap_smul D.what₂.LL b x, map_smulₛₗ]
        rfl) _


set_option maxHeartbeats 2000000 in
theorem theta_of (T1 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x))) (T2 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0) : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ (i : Fin D.R.m) (t : T) x,
    D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) =
      Z.jW i (((A3.indefDown (s0Of R F)).θ i t).mulVec ((lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t x
  change Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL at x
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h5 := hR.lifts0.1
  have hr := hR.ratTh
  have hOk := hH.ok.ok2
  apply eW_injective D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  refine (T1 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t x).trans ?_
  refine Eq.trans ?_ (eW_jW D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i _).symm
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hsub : ∀ a b, liftForm A3.A F.P0 F.ψ0 i t (a - b) = liftForm A3.A F.P0 F.ψ0 i t a - liftForm A3.A F.P0 F.ψ0 i t b :=
    fun a b => by unfold liftForm; rw [Matrix.mulVec_sub, map_sub]
  have h1 : R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t
      (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)))) := by
    have h := T2 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
      (x - lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)) (fun z => by rw [map_sub, GlobalTheory.Mem.LiftForms.hform_orth hp, sub_self])
    rwa [hsub, map_sub, map_sub, sub_eq_zero] at h
  rw [h1]
  have h2 := GlobalTheory.Mem.LiftTheta.liftMatrix_computes_lift_rational (R.toCx3 F) F.cr false h5 hr i t
    (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)
  have h3 := GlobalTheory.Mem.LiftTheta.levelFormCoordinateMap_levelZero F.lv2 hOk (A3.fam3.toSub2 (zsOf R F)) i t
    (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)
  have h4 := GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i
    ((R.toCx3 F).liftMat F.cr false i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x))
  have key := h4.symm.trans (h2.trans (by
    show R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) _) = _
    have h3' : F.cr.toL (R.toCx3 F).zs false i t (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x) =
        LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P (A3.A.fam.lvlA F.P0 F.ψ0).ψ
          (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)) :=
      h3.symm
    rw [hP.phs i, one_smul, h3']
    rfl))
  exact (congrArg Tw.out key).symm


set_option maxHeartbeats 1000000 in
theorem thDef3_thTheta : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ThDef3 D A3.A (A3.indefDown (s0Of R F)) Y.tup Y.eMt Z.jW ∧ ∀ (i : Fin D.R.m) (t : T) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) = Z.jW i (((A3.indefDown (s0Of R F)).θ i t).mulVec ((lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  exact ⟨⟨fun i => (li_span D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i).1,
    fun i => (li_span D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i).2, lat_of D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH⟩,
    theta_of GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree GlobalTheory.T.liftLevelForm_orthogonal_killed_by_thetaMap D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH⟩

end GlobalTheory.Mem.ThRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ThDef3 D A3.A (A3.indefDown (s0Of R F)) Y.tup Y.eMt Z.jW ∧ ∀ (i : Fin D.R.m) (t : T) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) = Z.jW i (((A3.indefDown (s0Of R F)).θ i t).mulVec ((lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec x)) := by
  first | exact @GlobalTheory.Mem.ThRead.thDef3_thTheta | exact GlobalTheory.Mem.ThRead.thDef3_thTheta | (intros; apply GlobalTheory.Mem.ThRead.thDef3_thTheta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X} {v : Sp (DualNumber k) ⟶ t.G.left}

theorem preimage_le_of_isTanAtG (hv : IsTanAtG t x v) {V : X.Opens} {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) :
    (specO k (DualNumber k)).hom ⁻¹ᵁ T ≤ v ⁻¹ᵁ W := by
  intro y hy
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero y
  have h₁ : s ∈ (sec (epsZero k) ≫ (specO k (DualNumber k)).hom) ⁻¹ᵁ T := hy
  rw [sec_hom] at h₁
  have h₂ : s ∈ (x ≫ unitSec t.G) ⁻¹ᵁ W := hW (hT h₁)
  rw [← epsZero_comp_of_isTanAtG t hv] at h₂
  exact h₂

theorem tanForm_dUnit (hv : IsTanAtG t x v) {V : X.Opens} {W : t.G.left.Opens}
    (hW : V ≤ unitSec t.G ⁻¹ᵁ W) {T : (Sp k).Opens} (hT : T ≤ x ⁻¹ᵁ V) (f : Γ(t.G.left, W))
    (a b : Γ(Sp k, T))
    (e : (v.appLE W _ (preimage_le_of_isTanAtG t hv hW hT) f :
        Γ((specO k (DualNumber k)).left, (specO k (DualNumber k)).hom ⁻¹ᵁ T)) =
      (specO k (DualNumber k)).hom.appLE T _ le_rfl a +
        (specO k (DualNumber k)).hom.appLE T _ le_rfl b * resG _ le_top (epsFn k)) :
    (tanForm t hv).app T (pullbackSections x (omega t.G) hT (dUnit t.G hW f)) = b := by
  have hV : T ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  have c := baseMap_d (sec_hom (MonObj.one (X := t.G))) (sec_hom (epsZero k)) hv.1
    (epsZero_comp_of_isTanAtG t hv) hW hT hV (preimage_le_of_isTanAtG t hv hW hT) f
  refine (congrArg ((epsIso k).hom.app T) c).trans ?_
  rw [e, map_add (f := _), d_base, zero_add, d_mul, d_base,
    smul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl, GlobalTheory.LB.resG_self, d_resG,
    ← resM_d _ (le_preimage_top _ ⊤) le_top, Scheme.Modules.Hom.app_smul, app_resM, epsIso_d]
  exact (congrArg (b * ·) (map_one (resG (Sp k) (le_top : T ≤ ⊤)))).trans (_root_.mul_one b)

variable {k' : Type} [CommRing k'] (φ : k →+* k')

theorem spMap_dualMap_comp : spMap (Formalism.L2.Pj.dualMap φ) ≫ (specO k (DualNumber k)).hom =
    (specO k' (DualNumber k')).hom ≫ spMap φ := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_dualMap_epsFn :
    (spMap (Formalism.L2.Pj.dualMap φ)).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn k) = epsFn k' := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Formalism.L2.Pj.dualMap φ))) DualNumber.eps).symm.trans ?_
  refine congrArg (Scheme.ΓSpecIso (.of (DualNumber k'))).inv.hom ?_
  change Formalism.L2.Pj.dualMap φ DualNumber.eps = _
  ext <;> simp [Formalism.L2.Pj.dualMap]

theorem tanForm_baseChange {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (hv : IsTanAtG t x v)
    (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V)
    (s : Γ(omega t.G, V)) :
    ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) =
      (spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) : Γ(Sp k, ⊤)) := by
  have := t.semi
  have key (y : (⊤ : (Sp k').Opens)) : ∃ T' : (Sp k').Opens, y.1 ∈ T' ∧
      resG (Sp k') (le_top : T' ≤ ⊤) ((tanForm t hv').app ⊤ (pullbackSections _ (omega t.G) h' s) : Γ(Sp k', ⊤)) =
      resG (Sp k') (le_top : T' ≤ ⊤) ((spMap φ).appLE ⊤ ⊤ (le_preimage_top _ _)
        ((tanForm t hv).app ⊤ (pullbackSections x (omega t.G) h s) : Γ(Sp k, ⊤))) := by
    obtain ⟨U, W, hU, hle, c⟩ := exists_isChart (sec_hom (MonObj.one (X := t.G))) (V := V)
      (x := x (spMap φ y.1)) (h trivial)
    obtain ⟨T, hT, hyT, hTU⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ U) (spMap φ y.1) hU
    obtain ⟨f, hf⟩ := c.d_surjective (sec_hom (MonObj.one (X := t.G))) (resM _ hle s)
    have hf' : dUnit t.G c.le f = resM (omega t.G) hle s := hf
    have hTU' : spMap φ ⁻¹ᵁ T ≤ (spMap φ ≫ x) ⁻¹ᵁ U := (spMap φ).preimage_mono hTU
    obtain ⟨⟨a, b⟩, e⟩ := (bijective_add_mul_epsFn k T hT).2
      (v.appLE W _ (preimage_le_of_isTanAtG t hv c.le hTU) f)
    have e₁ := tanForm_dUnit t hv c.le hTU f a b e.symm
    have kk : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        spMap (Formalism.L2.Pj.dualMap φ) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ T :=
      (le_preimage_of_comp (spMap_dualMap_comp φ)).2 le_rfl
    have kk' : (specO k' (DualNumber k')).hom ⁻¹ᵁ spMap φ ⁻¹ᵁ T ≤
        ((specO k' (DualNumber k')).hom ≫ spMap φ) ⁻¹ᵁ T := le_rfl
    have n (z : Γ(Sp k, T)) : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk
        ((specO k (DualNumber k)).hom.appLE T _ le_rfl z) =
        (specO k' (DualNumber k')).hom.appLE _ _ le_rfl ((spMap φ).appLE T _ le_rfl z) :=
      (appLE_appLE (spMap_dualMap_comp φ) _ _ kk' z).trans (appLE_appLE rfl _ _ kk' z).symm
    have n' : (spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk (resG _ le_top (epsFn k)) =
        resG _ le_top (epsFn k') :=
      (appLE_resG _ _ _ _).trans ((resG_appLE _ le_top (le_preimage_top _ _) _).symm.trans
        (congrArg _ (spMap_dualMap_epsFn φ)))
    have e₂ := tanForm_dUnit t hv' c.le hTU' f ((spMap φ).appLE T _ le_rfl a)
      ((spMap φ).appLE T _ le_rfl b) (by
        refine (appLE_appLE rfl (preimage_le_of_isTanAtG t hv c.le hTU) kk _ f).symm.trans ?_
        refine (congrArg ((spMap (Formalism.L2.Pj.dualMap φ)).appLE _ _ kk) e.symm).trans ?_
        refine (map_add _ _ _).trans ?_
        exact congrArg₂ (· + ·) (n a) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (n b) n')))
    rw [hf', QCoh.pullbackSections_res] at e₁ e₂
    refine ⟨spMap φ ⁻¹ᵁ T, hyT, ?_⟩
    refine (app_resM (tanForm t hv') le_top _).symm.trans ?_
    rw [QCoh.res_pullbackSections, e₂, ← e₁]
    refine .trans ?_ ((appLE_resG (spMap φ) (le_top : T ≤ ⊤) le_rfl _).trans
      (resG_appLE (spMap φ) le_top (le_preimage_top _ _) _).symm)
    refine congrArg _ ?_
    refine .trans ?_ (app_resM (tanForm t hv) le_top _)
    rw [QCoh.res_pullbackSections]
  choose T hT hs using key
  exact LB.fun_ext_of_cover T (fun _ => le_top) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hT _⟩) hs

theorem tanEv_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (v : Sp (DualNumber k) ⟶ t.G.left) (hv : IsTanAtG t x v) (k' : Type) [CommRing k'] (φ : k →+* k') (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) (s : Γ(GlobalTheory.LieVB.omega t.G, V)), tanEv t hv' h' s = φ (tanEv t hv h s) := by
  intro E _ _ _ H X t k _ x V h v hv k' _ φ hv' h' s
  refine (congrArg (Scheme.ΓSpecIso (.of k')).hom (tanForm_baseChange t φ h hv hv' h' s)).trans ?_
  refine (congrArg (Scheme.ΓSpecIso (.of k')).hom (appLE_top (spMap φ) _)).trans ?_
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) _)

end GlobalTheory.LocM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open CategoryTheory.Limits

set_option autoImplicit false

theorem GlobalTheory.ShFam.chart_lift_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (d g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (ch : AlgChart (genStr Z) σ d) (y₀ : FrPt Xo c (Formalism.L2.Pj.CAt σ)), cxPt Z y₀ ∈ ch.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ ch.e (cxPt Z y₀) ∈ B ∧ B ⊆ ch.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∀ y : FrPt Xo c (Formalism.L2.Pj.CAt σ), ch.e.symm b = cxPt Z y → Fu.u i (P b) = y.x := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ d g ty Fu ch y₀ hy₀
  have := Z.jQ_open
  let L := EuclideanSpace.equiv (Fin d) ℂ
  have hsy := GlobalTheory.TrueCx.TorHolo.isHolTo_symm ch
  have hB₀ := (hsy Z.jQ.opensRange 0).1
  set B₀ := {b ∈ ch.e.target | ⊤ ≤ (ch.e.symm b).1 ⁻¹ᵁ Z.jQ.opensRange} with hB₀def
  have hb₀ : ch.e (cxPt Z y₀) ∈ B₀ := by
    refine ⟨ch.e.map_source hy₀, ?_⟩
    rw [ch.e.left_inv hy₀]
    intro s _
    exact ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀ s, (Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀) Z.jQ s).symm⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀⟩
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ Z.jQ = (ch.e.symm b).1 := fun b hb =>
    ⟨IsOpenImmersion.lift Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion Z.jQ
    (LocLift.isHolTo_congr (LocLift.isHolTo_mono hsy hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← Z.jQ_over, ← Category.assoc, hw b hb]
    exact (ch.e.symm b).2
  have hB₁ : IsOpen (L.symm ⁻¹' B₀) := hB₀.preimage L.symm.continuous
  obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := Fu.lift d (L.symm ⁻¹' B₀) (fun x => w (L.symm x) ≫ pullback.fst _ _) hB₁
    (fun x hx => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl)
    (LocLift.isHolTo_comp hyh hB₁ L.symm.differentiableOn fun x hx => hx) (L (ch.e (cxPt Z y₀)))
    (by simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hb₀)
  refine ⟨i, L ⁻¹' B', fun v => P (L v), hB'.preimage L.continuous, hb', fun v hv => ?_, fun v hv => hP.1 _ hv,
    fun x => (hP.2 x).comp L.differentiableOn fun v hv => hv, fun b hb y hy => ?_⟩
  · have := hsub hv
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
    exact this.1
  · have hb1 := hsub hb
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at hb1
    have h1 : w b = GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y :=
      (cancel_mono Z.jQ).1 ((hw b hb1).trans (congrArg Subtype.val hy))
    have h2 := hu _ hb
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h2
    rw [h2, h1]
    exact GlobalTheory.ShFam.ptF_fst y
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.Spread

open GlobalTheory.LieLocFrame (res res_sum res_res)
open GlobalTheory.LieMet (tan_ext)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_germs {X : Scheme.{0}} (y : X) {W : X.Opens} (hW : y ∈ W) {κ : Type} [Finite κ]
    (a : κ → X.presheaf.stalk y) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (hy : y ∈ U) (s : κ → Γ(X, U)), U ≤ W ∧
      ∀ i, X.presheaf.germ U y hy (s i) = a i := by
  choose V hV s hs using fun i => X.presheaf.exists_germ_eq (a i)
  have ho : IsOpen ((W : Set X) ∩ ⋂ i, (V i : Set X)) :=
    W.isOpen.inter (isOpen_iInter_of_finite fun i => (V i).isOpen)
  obtain ⟨U, hU, hy, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⟨_, ho⟩) (x := y)
    ⟨hW, Set.mem_iInter.2 hV⟩
  have hl : ∀ i, U ≤ V i := fun i z hz => Set.mem_iInter.1 (hle hz).2 i
  exact ⟨U, hU, hy, fun i => X.presheaf.map (homOfLE (hl i)).op (s i), fun z hz => (hle hz).1,
    fun i => (X.presheaf.germ_res_apply (homOfLE (hl i)) y hy (s i)).trans (hs i)⟩

theorem spMap_germ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U) :
    spMap (X.presheaf.germ U y hy).hom ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec) =
      (show Sp (X.presheaf.stalk y) ⟶ X from X.fromSpecStalk y) :=
  hU.fromSpecStalk_eq_fromSpecStalk hy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem exists_bc {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* S) {φ' : c.F →+* S}
    {x' : Sp S ⟶ Z.X} (hφ : ψ.comp φ = φ') (hx : spMap ψ ≫ x = x') :
    ∃ g : EigFrame Z φ' x', ∀ τ i, g.vec τ i = res ψ hx (f.vec τ i) := by
  subst hφ hx
  have h : ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x),
      ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i :=
    GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z R S φ x f ψ
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun τ i => tan_ext (hg τ i)⟩

theorem exists_coord {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f g : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ A B : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, B * A = 1 ∧ ∀ i, g.vec τ i = ∑ k, A i k • f.vec τ k := by
  choose A hA _ using fun i => f.existsUnique_sum τ (g.vec τ i) (g.act_vec τ i)
  choose B hB _ using fun i => g.existsUnique_sum τ (f.vec τ i) (f.act_vec τ i)
  refine ⟨Matrix.of A, Matrix.of B, Matrix.ext fun i => congrFun ?_, hA⟩
  refine (f.existsUnique_sum τ (f.vec τ i) (f.act_vec τ i)).unique ?_ ?_
  · refine (hB i).trans ?_
    simp only [show ∀ i, g.vec τ i = ∑ k, A i k • f.vec τ k from hA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
    exact Finset.sum_comm
  · simp only [Matrix.one_apply, ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      zero_smul R]

theorem exists_change {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (A B : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) (h : ∀ τ, B τ * A τ = 1) :
    ∃ g : EigFrame Z φ x, ∀ τ i, g.vec τ i = ∑ k, A τ i k • f.vec τ k := by
  have hs : ∀ τ (a : Fin (Dw.mult τ) → R), ∑ i, a i • ∑ k, A τ i k • f.vec τ k =
      ∑ k, (Matrix.vecMul a (A τ)) k • f.vec τ k := fun τ a => by
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  refine ⟨EigFrame.ofVec (fun τ i => ∑ k, A τ i k • f.vec τ k) (fun τ i a => ?_) fun τ w hw => ?_,
    fun τ i => tan_ext rfl⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, f.act_vec, Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · obtain ⟨a, ha, hu⟩ := f.existsUnique_sum τ w hw
    refine ⟨Matrix.vecMul a (B τ), ?_, fun b hb => ?_⟩
    · show w = _
      rw [hs, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
      exact ha
    · rw [← hu _ (hb.trans (hs τ b)), Matrix.vecMul_vecMul, mul_eq_one_comm.1 (h τ), Matrix.vecMul_one]

end GlobalTheory.ShFam.Spread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.LieVB GlobalTheory.Conormal
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

theorem cotMap_list_prod {S : Scheme.{0}} {T G : Over S} [GrpObj G] [QuasiSeparated G.hom] {s : 𝟙_ (Over S) ⟶ T} :
    ∀ {m : ℕ} (z : Fin m → (T ⟶ G)) (hz : ∀ i, s ≫ z i = η) (h : s ≫ (List.ofFn z).prod = η),
      cotMap (List.ofFn z).prod h = ∑ i, cotMap (z i) (hz i)
  | 0, z, hz, h => by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact cotMap_eq_zero (by rw [List.ofFn_zero, List.prod_nil, Hom.one_def]) _
  | m + 1, z, hz, h => by
    have e : (List.ofFn z).prod = z 0 * (List.ofFn fun i : Fin m => z i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    have h₁ : (η : 𝟙_ (Over S) ⟶ G) = 1 := by rw [Hom.one_def]; simp
    have h' : s ≫ (List.ofFn fun i : Fin m => z i.succ).prod = η := by
      have := h
      rw [e, MonObj.comp_mul, hz 0, h₁, _root_.one_mul] at this
      exact this.trans h₁.symm
    rw [Fin.sum_univ_succ, ← cotMap_list_prod (fun i : Fin m => z i.succ) (fun i => hz _) h',
      ← cotMap_mul (hz 0) h' (e ▸ h)]
    congr 1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
variable {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X}
variable {G' : Over (Sp k)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}

theorem exists_fibre_vector (hp : IsGrpPullback G' t.G x φ) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ y : specO k (DualNumber k) ⟶ G', epsZero k ≫ y = η ∧ y.left ≫ φ = v := by
  refine ⟨Over.homMk (hp.1.lift v _ hv.1) (hp.1.lift_snd _ _ _), Over.OverMorphism.ext (hp.1.hom_ext ?_ ?_),
    hp.1.lift_fst _ _ _⟩
  · refine (Category.assoc _ _ _).trans ((congrArg (sec (epsZero k) ≫ ·) (hp.1.lift_fst _ _ _)).trans ?_)
    exact (epsZero_comp_of_isTanAtG t hv).trans (unitSec_comp hp).symm
  · exact (Over.w _).trans (Over.w _).symm

theorem tanForm_eq_fibre (hp : IsGrpPullback G' t.G x φ) {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v)
    {y : specO k (DualNumber k) ⟶ G'} (hy : epsZero k ≫ y = η) (e : y.left ≫ φ = v) :
    tanForm t hv = omegaBase hp ≫ cotMap y hy ≫ (epsIso k).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso k).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_
  have k₁ := le_of_sq (unitSec_comp hp) (le_refl (unitSec t.G ⁻¹ᵁ W)) le_rfl
  have k₂ := le_of_sq (epsZero_comp_of_isTanAtG t hv) (le_refl (unitSec t.G ⁻¹ᵁ W)) le_rfl
  have k₃ := (le_preimage_of_comp e).2 (le_refl (v ⁻¹ᵁ W))
  refine (baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero k)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl
    k₂ le_rfl a).trans (Eq.symm ?_)
  refine (congrArg ((cotMap y hy).app _) (omegaBase_dUnit hp le_rfl le_rfl k₁ le_rfl a)).trans ?_
  exact (cotMap_d y hy k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE e _ _ _ a))

theorem tanEv_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V),
    ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i)) (cf : Fin m → k)
      (w : Sp (DualNumber k) ⟶ t.G.left) (hw : IsTanAtG t x w), IsCombAtG t x v cf w →
      ∀ s : Γ(GlobalTheory.LieVB.omega t.G, V), tanEv t hw h s = ∑ i, cf i * tanEv t (hv i) h s := by
  rintro E _ _ _ H X t k _ x V h m v hv cf w hw ⟨u, hu, hw'⟩ s
  have hp := isGrpPullback_pullback t.G x
  have := t.semi
  have : QuasiSeparated ((Over.pullback x).obj t.G).hom := MorphismProperty.of_isPullback hp.1 inferInstance
  choose y hy ey using fun i => exists_fibre_vector t hp (hv i)
  obtain ⟨yw, hyw, eyw⟩ := exists_fibre_vector t hp hw
  let z := fun i => ptMap (dualScale (cf i)) ≫ y i
  have hz (i : Fin m) : epsZero k ≫ z i = η := by
    rw [← Category.assoc, epsZero_dualScale, hy]
  have hu' : u = fun i => pushHom hp _ (z i) := funext fun i => Over.OverMorphism.ext <| by
    refine (hu i).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    rw [ey]
    rfl
  have hprod : yw = (List.ofFn z).prod := by
    refine Over.OverMorphism.ext (hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    refine eyw.trans (hw'.symm.trans ?_)
    rw [hu']
    exact (congrArg (fun q => q.left) ((map_list_prod (pushHom hp (specO k (DualNumber k))) (List.ofFn z)).trans
      (congrArg List.prod List.map_ofFn))).symm
  subst hprod
  let σ := (omegaBase hp).app ⊤ (pullbackSections x (omega t.G) h s)
  let F : (conormal (unitSec ((Over.pullback x).obj t.G)) ⟶ conormal (sec (epsZero k))) →+ k :=
    AddMonoidHom.mk' (fun α => (Scheme.ΓSpecIso (.of k)).hom ((epsIso k).hom.app ⊤ (α.app ⊤ σ))) fun α β =>
      (congrArg (Scheme.ΓSpecIso (.of k)).hom (map_add ((epsIso k).hom.app ⊤).hom (α.app ⊤ σ) (β.app ⊤ σ))).trans
        (map_add _ _ _)
  have hF {v' : Sp (DualNumber k) ⟶ t.G.left} (hv' : IsTanAtG t x v') {y'} (hy' : epsZero k ≫ y' = η)
      (e : y'.left ≫ pullback.fst t.G.hom x = v') : tanEv t hv' h s = F (cotMap y' hy') := by
    rw [tanEv, tanForm_eq_fibre t hp hv' hy' e]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hF hw hyw eyw, cotMap_list_prod z hz, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := cotMap_comp (hy i) (epsZero_dualScale (cf i)) rfl (hz i)
  rw [cotMap_dualScale] at e
  rw [hF (hv i) (hy i) (ey i), ← e]
  refine (congrArg (Scheme.ΓSpecIso (.of k)).hom
    ((epsIso k).hom.app_smul (cst k (cf i)) ((cotMap (y i) (hy i)).app ⊤ σ))).trans ?_
  refine (map_mul _ _ _).trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

end GlobalTheory.LocM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframe
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem exists_matches : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : A →+* ℂ), x ≫ genStr Z = spMap φ → ψ.comp φ = σ → (∀ s, (spMap ψ ≫ x) s ∉ genBd Z) → ∃ y : FrPt Xo c (CAt σ), Matches fr ψ y := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ hx hψ hb
  subst hψ
  have := Z.jQ_open
  have : IsLocalRing (CAt (ψ.comp φ)) := inferInstanceAs (IsLocalRing ℂ)
  let ψ' : A →+* CAt (ψ.comp φ) := ψ
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.EigFrame.exists_baseChange E H Dw l Xo c O β Z A (CAt (ψ.comp φ)) φ (x ≫ genι Z) fr ψ'
  have hr : Set.range (spMap ψ' ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨s, rfl⟩
    exact not_not.1 (hb s)
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = spMap ψ' ≫ x := IsOpenImmersion.lift_fac _ _ _
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (CAt (ψ.comp φ))) := by
    rw [← Z.jQ_over, ← Category.assoc, hxF, Category.assoc]
    exact (congrArg (spMap ψ' ≫ ·) hx).trans (OpenReg.spMap_comp _ _)
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (R := CAt (ψ.comp φ)) xF hs
    (x := spMap ψ' ≫ x ≫ genι Z) (by rw [← Category.assoc, hxF, Category.assoc]) g
  have hp : GlobalTheory.AllWt.ptF y = xF := by
    apply pullback.hom_ext
    · rw [← hy]; exact pullback.lift_fst _ _ _
    · rw [hs]; exact pullback.lift_snd _ _ _
  refine ⟨y, by rw [hp]; exact hxF, fun τ i => ⟨w τ i, by rw [hp]; exact (hw τ i).1, (hw τ i).2.1, ?_⟩⟩
  exact (hw τ i).2.2.trans (hg τ i)

end GlobalTheory.ShFam.BdArc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpace
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.LineOfMap

open GlobalTheory.ProjSpace GlobalTheory.FlagMod

variable {Z : Scheme.{0}} {S : Type} [CommRing S]

theorem resG_refl {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  show (X.presheaf.map (homOfLE h).op).hom a = a
  rw [show (homOfLE h).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem fnOn_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U)) :
    fnOn ⊤ (ev z U h a) = (z.appLE U ⊤ h).hom a := by
  refine (resG_refl (X := Sp S) le_top _).trans ?_
  exact (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply _

theorem mem_basicOpen_of_isUnit_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U))
    (hu : IsUnit (ev z U h a)) (p : Sp S) : z p ∈ Z.basicOpen a := by
  have h1 := Scheme.basicOpen_of_isUnit _ (hu.map (fnOn ⊤))
  rw [fnOn_ev] at h1
  exact (((Scheme.basicOpen_appLE z ⊤ U h a).symm.trans h1).ge (Set.mem_univ p)).2

variable {O : Type} [CommRing O] {N : ℕ}

end GlobalTheory.DRFlag.LineOfMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.Proof.frame_combination_coeff_unique

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem pairwise_letters (Dw : Datum H) :
    (letters Dw).Pairwise fun x y : GlobalTheory.ShFam.Pad.Letter Dw => x.1 = y.1 → (x.2 : ℕ) < y.2 := by
  refine List.pairwise_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_finRange _).imp ?_
    exact fun h _ => h
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hx y hy h
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hy
    exact absurd ((Fintype.equivFin (E →+* ℂ)).symm.injective h) hab

theorem get_bijective (Dw : Datum H) : Function.Bijective (letters Dw).get :=
  ⟨List.nodup_iff_injective_get.1 (LetterConjugation.nodup_letters Dw), fun x => List.get_of_mem (LetterConjugation.mem_letters Dw x)⟩

variable {X : Scheme.{0}} {t : SAB H X} {k : Type} [CommRing k] {x : Sp k ⟶ X}

theorem comb_iff {m : ℕ} (u : Fin m → TanM x t.G) (a : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i => (tv (u i)).left) a w ↔ w = (tv (∑ i, a i • u i)).left := by
  have h0 := (GlobalTheory.LieMet.isComb_iff u a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨q, hq, hq'⟩ := h0
  obtain rfl : p = q := funext fun i => Over.OverMorphism.ext ((hp i).trans (hq i).symm)
  exact hq'

end

theorem concat_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] (f : c.F →+* k) (x : Sp k ⟶ X) (u : Vecs Dw t k), GlobalTheory.LocM.IsFrame t f x u → (∀ cf cf' w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf w → IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf' w → cf = cf') ∧ ∀ (j : Fin (letters Dw).length) (cf : Fin (Dw.mult ((letters Dw).get j).1) → k) w, (∀ m, ((letters Dw).get j).2 < m → cf m = 0) → IsCombAtG t x (u ((letters Dw).get j).1) cf w → ∃ cg : Fin (letters Dw).length → k, (∀ m, j < m → cg m = 0) ∧ cg j = cf ((letters Dw).get j).2 ∧ IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cg w := by
  intro E _ _ _ H Dw l c X t k _ f x u hu
  classical
  let _ : Algebra c.F k := f.toAlgebra
  let U : (y : GlobalTheory.ShFam.Pad.Letter Dw) → TanM x t.G := fun y => GlobalTheory.LieMet.tanOf (hu.1 y.1 y.2).1
  let e := Equiv.ofBijective _ (get_bijective Dw)
  have hc : ∀ cf w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
      cf w ↔ w = (tv (∑ y, cf (e.symm y) • U y)).left := fun cf w => by
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    exact comb_iff (fun i => U (e i)) cf w
  have hτ : ∀ τ cf w, IsCombAtG t x (u τ) cf w ↔ w = (tv (∑ i, cf i • U ⟨τ, i⟩)).left := fun τ cf w =>
    comb_iff (fun i => U ⟨τ, i⟩) cf w
  refine ⟨fun cf cf' w h h' => ?_, fun j cf w h0 h => ?_⟩
  · have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
    obtain ⟨α, hinj, -, -⟩ :=
      exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
    let ρ := actR (x0 := x) (S := k) t.act
    have hE : ∀ τ (v : TanM x t.G), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) v ↔ ∀ a : 𝓞 E,
        (tv v).left ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ (tv v).left := fun τ v =>
      forall_congr' fun a => ⟨fun h => congrArg (fun z => (tv z).left) h, fun h => GlobalTheory.LieMet.tan_ext h⟩
    have hS : ∀ τ (a : Fin (Dw.mult τ) → k), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) (∑ i, a i • U ⟨τ, i⟩) := fun τ a s => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hE τ (U ⟨τ, i⟩)).2 (hu.1 τ i).2 s, smul_comm]
    have h1 := GlobalTheory.LieMet.tan_ext (((hc cf w).1 h).symm.trans ((hc cf' w).1 h'))
    rw [Fintype.sum_sigma, Fintype.sum_sigma] at h1
    funext i
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective i
    have h2 := congrArg (proj ρ (embK c) α τ) h1
    rw [proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _), proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _)] at h2
    have h3 := hu.2 τ _ (GlobalTheory.LieMet.isTan_tv _) ((hE τ _).1 (hS τ fun i => cf (e.symm ⟨τ, i⟩)))
    exact congrFun (h3.unique ((hτ τ _ _).2 rfl) ((hτ τ _ _).2 (congrArg (fun z => (tv z).left) h2))) i
  · let B : GlobalTheory.ShFam.Pad.Letter Dw → k := fun y => if h : y.1 = ((letters Dw).get j).1 then cf (h ▸ y.2) else 0
    refine ⟨fun m => B ((letters Dw).get m), fun m hm => ?_, by simp [B], ?_⟩
    · have hp := List.pairwise_iff_get.1 (pairwise_letters Dw) j m hm
      show B ((letters Dw).get m) = 0
      revert hp
      generalize (letters Dw).get m = y
      obtain ⟨τ, i⟩ := y
      intro hp
      by_cases hy : τ = ((letters Dw).get j).1
      · subst hy
        exact (dif_pos rfl).trans (h0 _ (hp rfl))
      · exact dif_neg hy
    · rw [hc, (hτ _ _ _).1 h]
      congr 2
      have : ∀ y, (letters Dw).get (e.symm y) = y := e.apply_symm_apply
      simp only [this]
      rw [Fintype.sum_sigma, Finset.sum_eq_single ((letters Dw).get j).1]
      · exact Finset.sum_congr rfl fun i _ => by simp [B]
      · intro σ _ hσ
        exact Finset.sum_eq_zero fun i _ => by rw [show B ⟨σ, i⟩ = 0 from dif_neg hσ, zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.Proof.frame_combination_coeff_unique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAdaptedOfIntStep
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.AdaptedOfStep

theorem eq_zero_of_dense {X : Scheme.{0}} [IsReduced X] {D : Set X} (hD : Dense D) {U : X.Opens} (f : Γ(X, U))
    (h : ∀ (K : Type) [Field K] (w : Sp K ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ U), w (IsLocalRing.closedPoint K) ∈ D →
      ev w U hw f = 0) : f = 0 := by
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen f).isOpen
    (((X.basicOpen f).ne_bot_iff_nonempty).1 hne)
  let w : Sp (X.residueField x) ⟶ X := X.fromSpecResidueField x
  have hr : ∀ p, w p = x := fun p => Scheme.fromSpecResidueField_apply x p
  have hb : ⊤ ≤ w ⁻¹ᵁ X.basicOpen f := fun p _ => show w p ∈ X.basicOpen f by rw [hr]; exact hx
  have hw : ⊤ ≤ w ⁻¹ᵁ U := le_preimage_mono (X.basicOpen_le f) hb
  have h0 := h _ w hw ((hr _).symm ▸ hxD)
  have hu : IsUnit (resG X (X.basicOpen_le f) f) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace f
  have := hu.map (ev w _ hb)
  rw [ev_res w _ hb hw, h0] at this
  exact not_isUnit_zero this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {σ : E →+* ℂ} {k : ℕ}

variable {U U' : X.Opens} {hU : IsAffineOpen U} {hU' : IsAffineOpen U'} {m m' : ℕ}
  {b : Module.Basis (Fin k ⊕ Fin m) Γ(X, U) (TanM (tau hU ≫ π) M.t.G)}
  {b' : Module.Basis (Fin k ⊕ Fin m') Γ(X, U') (TanM (tau hU' ≫ π) M.t.G)}


end GlobalTheory.DRFlag.AdaptedOfStep
end
end
