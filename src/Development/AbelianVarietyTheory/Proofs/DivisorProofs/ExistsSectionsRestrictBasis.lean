module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsLiftSectionOfAmplePowFromClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsLiftSectionOfAmplePowFromClosed
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftClosed
open GlobalTheory.QCoh GlobalTheory.Twist

theorem res_eq {X : Scheme.{0}} (I : X.IdealSheafData) {V W : X.Opens} (h : W ≤ V)
    (x : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V)) :
    structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W)
      (resM ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) h
        ((structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ V)).symm x)) =
      (I.subscheme.presheaf.map (homOfLE (fun _ hz => h hz :
        I.subschemeι ⁻¹ᵁ W ≤ I.subschemeι ⁻¹ᵁ V)).op).hom x := rfl

theorem smul_eq {X : Scheme.{0}} (I : X.IdealSheafData) {W : X.Opens} (r : Γ(X, W))
    (m : Γ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme), W)) :
    structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W) (r • m) =
      (I.subschemeι.app W).hom r * structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ W) m := rfl

theorem epi_toSubscheme {X : Scheme.{0}} (I : X.IdealSheafData) : Epi (toSubscheme I) := by
  rw [epi_iff_forall_affine]
  intro U hU y
  obtain ⟨f, hf⟩ := I.subschemeι_app_surjective ⟨U, hU⟩ ((structureModuleSectionsEquiv _) y)
  refine ⟨(structureModuleSectionsEquiv U).symm f, ?_⟩
  apply (structureModuleSectionsEquiv _).injective
  rw [← hf]
  rfl

theorem exists_twistSec_of_sec {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (σ : (M.pull I.subschemeι).Sec) :
    ∃ b : Γ(twist ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) M, ⊤),
    ∀ i, structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) (coord b i) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)) := by
  refine ⟨mkSec (fun i => (structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i))).symm
    ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))) ?_,
    fun i => ?_⟩
  · intro i j
    apply (structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j))).injective
    dsimp only
    rw [smul_eq, res_eq, res_eq]
    have hi : ∀ z ∈ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j), z ∈ (M.pull I.subschemeι).U (fun _ => i) :=
      fun z hz => (mem_pull (F := I.subschemeι)).2 hz.1.2
    have hj : ∀ z ∈ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j), z ∈ (M.pull I.subschemeι).U (fun _ => j) :=
      fun z hz => (mem_pull (F := I.subschemeι)).2 hz.2
    refine fn_ext fun z hz => ?_
    have e1 := gs_res (𝟙 I.subscheme) z (fun _ hz => hz.1 : I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j) ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) hz
      ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))
    have e1' := gs_res (𝟙 I.subscheme) z (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i)) hz.1 (σ.f (fun _ => i))
    have e2 := gs_res (𝟙 I.subscheme) z (fun _ hz => ⟨hz.1.1, hz.2⟩ : I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i ⊓ M.U j) ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j)) hz
      ((I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => j)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j) ≤ (M.pull I.subschemeι).U (fun _ => j))).op).hom (σ.f (fun _ => j)))
    have e2' := gs_res (𝟙 I.subscheme) z (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => j)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U j) ≤ (M.pull I.subschemeι).U (fun _ => j)) ⟨hz.1.1, hz.2⟩ (σ.f (fun _ => j))
    have hz' : I.subschemeι z ∈ M.U i ⊓ M.U j := ⟨hz.1.2, hz.2⟩
    have e3 := gs_pull (𝟙 I.subscheme) I.subschemeι z (⊤ ⊓ M.U i ⊓ M.U j) hz (resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (M.g i j : Γ(X, M.U i ⊓ M.U j)))
    have e4 := gs_res (𝟙 I.subscheme ≫ I.subschemeι) z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ⊤ ⊓ M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j) hz (M.g i j : Γ(X, M.U i ⊓ M.U j))
    have e5 := gs_unit (𝟙 I.subscheme ≫ I.subschemeι) z _ hz' (M.g i j)
    have e6 := gs_compat σ (𝟙 _) z (hi z hz) (hj z hz)
    have e7 := gm_pull_g M I.subschemeι (𝟙 _) z (fun _ => i) (fun _ => j) (hi z hz) (hj z hz)
    rw [gs_mul _ z _ hz]
    erw [e1, e1', e2, e2', e3, e4, e5, e6, e7]
  · exact LinearEquiv.apply_symm_apply _ _

theorem secPull_secOfTwist_eq {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (σ : (M.pull I.subschemeι).Sec)
    (b : Γ(twist ((Scheme.Modules.pushforward I.subschemeι).obj (QCoh.structureModule I.subscheme)) M, ⊤))
    (hb : ∀ i, structureModuleSectionsEquiv (X := I.subscheme) (I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i)) (coord b i) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f (fun _ => i)))
    (a : Γ(twist (QCoh.structureModule X) M, ⊤)) (ha : (Twist.map M (toSubscheme I)).app ⊤ a = b) :
    GlobalTheory.secPull (Twist.secOfTwist (𝟙 _) a) I.subschemeι = σ := by
  refine DVR.SecOps.sec_ext fun J => ?_
  have h1 := hb (J PUnit.unit)
  rw [← ha, coord_map_app] at h1
  change (I.subschemeι.appLE _ _ _).hom (resG X _ (structureModuleSectionsEquiv _ (coord a (J PUnit.unit)))) = _

  set i := J PUnit.unit
  have h2 : (I.subschemeι.app (⊤ ⊓ M.U i)).hom (structureModuleSectionsEquiv _ (coord a i)) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => (mem_pull (F := I.subschemeι) (J := fun _ => i)).2 hz.2 :
        I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i) ≤ (M.pull I.subschemeι).U (fun _ => i))).op).hom (σ.f J) := h1
  have e3 : ∀ y : Γ(X, ⊤ ⊓ M.U i), (I.subschemeι.appLE (M.U i) ((M.pull I.subschemeι).U J)
      (fun z hz => (mem_pull (F := I.subschemeι)).1 hz)).hom (resG X (le_inf le_top le_rfl) y) =
      (I.subscheme.presheaf.map (homOfLE (fun z hz => ⟨trivial, (mem_pull (F := I.subschemeι)).1 hz⟩ :
        (M.pull I.subschemeι).U J ≤ I.subschemeι ⁻¹ᵁ (⊤ ⊓ M.U i))).op).hom ((I.subschemeι.app _).hom y) := by
    intro y
    rw [← CommRingCat.comp_apply]
    erw [Scheme.Hom.map_appLE]
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  refine (e3 _).trans ?_
  rw [h2, ← CommRingCat.comp_apply, ← Functor.map_comp]
  exact (congrArg (fun q => (I.subscheme.presheaf.map q).hom (σ.f J)) (Subsingleton.elim _ (𝟙 _))).trans
    (by rw [CategoryTheory.Functor.map_id]; rfl)

theorem exists_secPull_eq_of_subsingleton {X : Scheme.{0}} (I : X.IdealSheafData) (M : LB X) (hM : M.IsLB)
    (h : Subsingleton (coh (twist (idealModule I) M) 1)) (σ : (M.pull I.subschemeι).Sec) :
    ∃ s : M.Sec, GlobalTheory.secPull s I.subschemeι = σ := by
  haveI := epi_toSubscheme I
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (idealModuleι I) (toSubscheme I) (Limits.kernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hsurj := cohOn.app_surjective (Twist.shortExact_map hM hS) ⊤ h
  obtain ⟨b, hb⟩ := exists_twistSec_of_sec I M σ
  obtain ⟨a, ha⟩ := hsurj b
  exact ⟨_, secPull_secOfTwist_eq I M σ b hb a ha⟩

theorem eventually_exists_secPull_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∀ σ : ((lbPow N l).pull (redι Z)).Sec, ∃ s : (lbPow N l).Sec, GlobalTheory.secPull s (redι Z) = σ := by
  intro X _ _ p hp N Z hN
  letI := algebraΓOfHom p
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  refine (hN.eventually_subsingleton_coh_twist (f := p) (fun _ => rfl)
    (idealModule (Scheme.IdealSheafData.vanishingIdeal Z))).mono fun l hl σ => ?_
  exact exists_secPull_eq_of_subsingleton _ _ (isLB_lbPow hN.isLB l) (hl 1 one_pos) σ

end GlobalTheory.LiftClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsLiftSectionOfAmplePowFromClosedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_exists_lift_section_of_ample_pow_from_closed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∀ σ : ((lbPow N l).pull (redι Z)).Sec, ∃ s : (lbPow N l).Sec, GlobalTheory.secPull s (redι Z) = σ := by
  first | exact @GlobalTheory.LiftClosed.eventually_exists_secPull_eq | exact GlobalTheory.LiftClosed.eventually_exists_secPull_eq | (intros; apply GlobalTheory.LiftClosed.eventually_exists_secPull_eq <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem presents_lbPow_toLB {X : Scheme.{0}} [IsIntegral X] (A : CartierDiv X) (l : ℕ) :
    Presents (l • A) (lbPow (toLB A) l) fun j => (j PUnit.unit).1.2 ^ l := by
  refine ⟨isLB_lbPow (isLB_toLB A) l, fun i j h => ?_, fun i x hx => ?_⟩
  · simp only [show (lbPow (toLB A) l).g i j = _ from lbPow_g _ l i j, Units.val_pow_eq_pow_val,
      val_res, map_pow, fnOf_resG, fnOf_toLB_g]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Units.ne_zero _))]
  · exact ((i PUnit.unit).2.2 x ((lbPow_U _ l i).le hx)).nsmul l

theorem secPull_add' {X Y : Scheme.{0}} {L : LB X} (s t : L.Sec) (f : Y ⟶ X) :
    GlobalTheory.secPull (s + t) f = GlobalTheory.secPull s f + GlobalTheory.secPull t f :=
  LB.f_injective (funext fun i => by
    simp only [GlobalTheory.secPull, GlobalTheory.chartSec_f, LB.add_f, map_add (f := _)])

theorem secPull_smul' {X Y : Scheme.{0}} {L : LB X} (c : Γ(X, ⊤)) (s : L.Sec) (f : Y ⟶ X) :
    GlobalTheory.secPull (c • s) f = f.appTop c • GlobalTheory.secPull s f :=
  LB.f_injective (funext fun i => by
    simp only [GlobalTheory.secPull, GlobalTheory.chartSec_f, LB.smul_f, map_mul]
    congr 1
    change ((X.presheaf.map _ ≫ f.appLE _ _ _).hom c) = ((f.appTop ≫ Y.presheaf.map _).hom c)
    rw [Scheme.Hom.map_appLE]
    rfl)

theorem algX_top_eq {X : Scheme.{0}} (p : X ⟶ Sp ℂ) (a : ℂ) :
    algX p ⊤ a = p.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv a) := by
  simp only [algX, RingHom.comp_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem redι_closure_genericPoint {X : Scheme.{0}} (z : X)
    [IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme] :
    redι (Closeds.closure ({z} : Set X)) (genericPoint _) = z := by
  have hcl : closure ({redι (Closeds.closure ({z} : Set X)) (genericPoint _)} : Set X) = closure {z} := by
    rw [← Set.image_singleton, (redι _).isClosedEmbedding.closure_image_eq,
      (genericPoint_spec _).def, Set.image_univ, range_redι]
    rfl
  exact (inseparable_iff_closure_eq.2 hcl).eq

end GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sections_restrict_basis :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p →
      ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l →
        ∃ (r : ℕ) (f : Fin r → X.functionField), (∀ i, f i ∈ (l • A).sections) ∧
          r = (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
            lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X))))) ∧
          ∀ a : Fin r → ℂ, a ≠ 0 → (l • A).GeneratesAt z (∑ i, Cartier.constFn p (a i) * f i) := by
  intro X _ _ p hp A z hA
  haveI hYi : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  obtain ⟨l₁, hl₁⟩ := eventually_atTop.1 (GlobalTheory.T.eventually_exists_lift_section_of_ample_pow_from_closed X p hp (toLB A) (Closeds.closure ({z} : Set X)) hA)
  refine ⟨l₁, fun l hl => ?_⟩
  letI : Algebra ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) :=
    algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p)
  letI : Module ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
    Module.compHom _ (algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤))
  haveI : IsScalarTower ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤)
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
    ⟨fun a g s => by
      show (algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) a * g) • s =
        algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) a • (g • s)
      rw [mul_smul]⟩
  have hP := presents_lbPow_toLB A l
  have hr : Module.finrank ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec =
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) := by
    rw [← lineBundleGlobalSectionsDim_eq_finrank]
    exact lineBundleGlobalSectionsDim_congr_picardClass (pull_isLB hP.isLB _) (pull_isLB (isLB_toLB _) _)
      (by rw [cls_pull hP.isLB, cls_pull (isLB_toLB _), ← hP.toPic_eq, toPic_apply])
  obtain ⟨v, hv⟩ : ∃ v : Fin (Module.finrank ℂ
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec) →
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec, LinearIndependent ℂ v := by
    by_cases hf : Module.Finite ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec
    · exact ⟨_, (Module.finBasis ℂ _).linearIndependent⟩
    · rw [Module.finrank_of_not_finite hf]
      exact ⟨Fin.elim0, linearIndependent_empty_type⟩
  choose s hs using fun i => hl₁ l hl (v i)
  refine ⟨_, fun i => hP.rat (s i), fun i => hP.rat_mem _, hr, fun a ha => ?_⟩
  have e₁ : ∑ i, Cartier.constFn p (a i) * hP.rat (s i) = hP.rat (∑ i, algX p ⊤ (a i) • s i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, Algebra.smul_def, CartierDiv.algebraMap_top]
    rfl
  have e₂ : GlobalTheory.secPull (∑ i, algX p ⊤ (a i) • s i) (redι (Closeds.closure ({z} : Set X))) = ∑ i, a i • v i := by
    let F : (lbPow (toLB A) l).Sec →+ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
      { toFun := fun t => GlobalTheory.secPull t _
        map_zero' := by
          have := secPull_smul' (0 : Γ(X, ⊤)) (0 : (lbPow (toLB A) l).Sec) (redι (Closeds.closure ({z} : Set X)))
          rwa [zero_smul, map_zero, zero_smul] at this
        map_add' := fun t t' => secPull_add' t t' _ }
    change F _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change GlobalTheory.secPull _ _ = _
    rw [secPull_smul', hs i, algX_top_eq]
    rfl
  have hne : ∑ i, a i • v i ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    exact hi (Fintype.linearIndependent_iff.1 hv a h0 i)
  rw [← e₂] at hne
  have hgen := (sec_ne_zero_iff _).1 hne
  rw [GlobalTheory.nonzeroLocus_secPull] at hgen
  have hgen' : redι (Closeds.closure ({z} : Set X)) (genericPoint _) ∈
      nonzeroLocus (∑ i, algX p ⊤ (a i) • s i) := hgen
  have key : ∀ y : X, y = redι (Closeds.closure ({z} : Set X)) (genericPoint _) →
      y ∈ nonzeroLocus (∑ i, algX p ⊤ (a i) • s i) := fun y hy => hy ▸ hgen'
  have hz := key z (redι_closure_genericPoint z).symm
  rw [e₁]
  exact (hP.generatesAt_rat_iff _).2 hz

end GlobalTheory.PairStep
