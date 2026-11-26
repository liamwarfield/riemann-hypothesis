module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PfPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.HodgeCechComparison
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.CechHStepPull

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.FormCochPullPf
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem formCoch_pull_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (U : ι → X.Opens)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (hle : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Pb.capO U i ≤ u ⁻¹ᵁ Pb.capO V (τ ∘ i)) (a n : ℕ)
    (c : (Glob.formCos p V a).X n),
    pullCoch u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom V U τ hτ n (formCoch p V a n c) =
      formCoch q U a n (fun i => GlobalTheory.HodgeCoh.formRes q (hle i) a
        (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i)))) := by
  intro K _ X Y q p u hu κ ι V U τ hτ hle a n c
  funext i
  have key : ∀ (W : Y.Opens) (x : GlobalTheory.CechDR.OmU p W a),
      (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom.app (op W) (toOm p a W x) =
        toOm q a (u ⁻¹ᵁ W) (GlobalTheory.HodgeCoh.formPull hu W a x) :=
    fun W x => GlobalTheory.HodgeCoh.omegaPull_toOmega hu a W x
  change res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_map u.base V U τ hτ i) ((GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom.app _
      (res (modulesAb (GlobalTheory.HodgeCoh.Omega p a)).obj (inter_le_capO V (τ ∘ i)) (toOm p a (Pb.capO V (τ ∘ i)) (c (τ ∘ i))))) =
    res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_capO U i) (toOm q a (Pb.capO U i)
      (GlobalTheory.HodgeCoh.formRes q (hle i) a (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i)))))
  have e1 := app_res_map u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom (inter_le_capO V (τ ∘ i))
    (toOm p a (Pb.capO V (τ ∘ i)) (c (τ ∘ i)))
  have e2 := key (Pb.capO V (τ ∘ i)) (c (τ ∘ i))
  have e3 := toOm_formRes q a (hle i) (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i)))
  refine (congrArg (res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_map u.base V U τ hτ i))
    (e1.trans (congrArg (res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj _) e2))).trans
      (Eq.trans ?_ (congrArg (res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_capO U i)) e3).symm)
  exact (res_res _ _ _ _).trans (res_res _ _ _ _).symm

end CrystallineSemistableComparison.Om.Cech
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.InjectiveSequenceLift
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem cechOmAdd_smul (h : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j), cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x) : type_of% @h := @h

theorem cechOm_pull (h : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (hV : iSup V = ⊤)
    (hVaff : ∀ (n : ℕ) (i : Fin (n + 1) → κ), IsAffineOpen (⨅ a, V (i a))) (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (a j : ℕ) (x : CO p V a j),
    cechOmAdd q U hU hUaff a j (cechPull hu V U τ hτ a j x) = pullC u hu a j (cechOmAdd p V hV hVaff a j x)) : type_of% @h := @h

theorem formToCO_bijective (h : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ),
    Function.Bijective (formToCO q U a j)) : type_of% @h := @h

theorem formToCO_smul (h : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (a j : ℕ) (r : K) (x : (Glob.formCos q U a).cx.H j),
    formToCO q U a j (r • x) = r • formToCO q U a j x) : type_of% @h := @h

theorem formCoch_pull (h : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (U : ι → X.Opens)
    (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (hle : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Pb.capO U i ≤ u ⁻¹ᵁ Pb.capO V (τ ∘ i)) (a n : ℕ)
    (c : (Glob.formCos p V a).X n),
    pullCoch u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom V U τ hτ n (formCoch p V a n c) =
      formCoch q U a n (fun i => GlobalTheory.HodgeCoh.formRes q (hle i) a
        (GlobalTheory.HodgeCoh.formPull hu (Pb.capO V (τ ∘ i)) a (c (τ ∘ i))))) : type_of% @h := @h

end CrystallineSemistableComparison.Om.Cech
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechFormsAddSmul
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechFormsAddSmul
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCech

theorem cechOmAdd_smul {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j) :
    cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x := by
  letI := GlobalTheory.HodgeCoh.algΓ q
  apply (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).injective
  have h1 : ∀ z : CO q U a j, GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j (cechOmAdd q U hU hUaff a j z) =
      cechHAddEquivH.{0} U hU hUaff (GlobalTheory.HodgeCoh.Omega q a) j z :=
    fun z => (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).apply_symm_apply _
  have h2 := cechHAddEquivH_naturality.{0} U hU hUaff
    (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j x
  have h3 := GlobalTheory.coh.toH_map K (smulHom (GlobalTheory.HodgeCoh.Omega q a) (algebraMap K Γ(X, ⊤) r)) j
    (cechOmAdd q U hU hUaff a j x)
  rw [h1] at h3 ⊢
  exact h2.trans h3.symm

end GlobalTheory.CompanionTheory.OmCech
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechFormsAddSmulStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_forms_add_smul : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hU : iSup U = ⊤) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a)))
    (a j : ℕ) (r : K) (x : CO q U a j), cechOmAdd q U hU hUaff a j (r • x) = r • cechOmAdd q U hU hUaff a j x := by
  first | exact @GlobalTheory.CompanionTheory.OmCech.cechOmAdd_smul | exact GlobalTheory.CompanionTheory.OmCech.cechOmAdd_smul | (intros; apply GlobalTheory.CompanionTheory.OmCech.cechOmAdd_smul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechBijective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechBijective
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.OmCech

theorem res_bijective_of_le {T : TopCat.{0}} (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{0}) {V W : Opens T}
    (h : V ≤ W) (h' : W ≤ V) : Function.Bijective (res P h) :=
  Function.bijective_iff_has_inverse.2
    ⟨res P h', fun x => by rw [res_res, res_refl], fun x => by rw [res_res, res_refl]⟩

theorem formCoch_bijective {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {ι : Type} (U : ι → X.Opens)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a n : ℕ) :
    Function.Bijective (formCoch q U a n) := by
  have hb : ∀ i : Fin (n + 1) → ι, Function.Bijective
      (fun x => res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj (inter_le_capO U i)
        (toOm q a (Pb.capO U i) x)) := fun i =>
    (res_bijective_of_le _ (inter_le_capO U i) (le_of_eq (inter_eq_iInf U i).symm)).comp
      (GlobalTheory.HodgeCoh.toOm_bijective q a (hUaff n i))
  refine ⟨fun c c' h => funext fun i => (hb i).1 (congrFun h i), fun σ => ?_⟩
  choose c hc using fun i => (hb i).2 (σ i)
  exact ⟨c, funext hc⟩

theorem formToCO_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ),
    Function.Bijective (formToCO q U a j) := by
  intro K _ X q ι U hUaff a j
  have hB := formCoch_bijective q U hUaff a
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hc' : (Glob.formCos q U a).cx.d j c = 0 := hc
    have hx' : formToCO q U a j ((Glob.formCos q U a).cx.cls c hc') = 0 := hx
    rw [formToCO_cls, GroundTheory.Arith.SchemeCoh.cls_eq_zero_iff] at hx'
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change c ∈ (Glob.formCos q U a).cx.B j
    cases j with
    | zero =>
      rw [coboundaries_zero, AddSubgroup.mem_bot] at hx'
      exact (hB 0).1 (hx'.trans (map_zero _).symm)
    | succ n =>
      rw [coboundaries_succ] at hx'
      obtain ⟨τ, hτ⟩ := hx'
      obtain ⟨b, rfl⟩ := (hB n).2 τ
      exact ⟨b, (hB (n + 1)).1 ((formCoch_d q U a n b).trans hτ)⟩
  · intro y
    obtain ⟨σ, hσ, rfl⟩ := exists_cls (P := (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj) (U := U) (n := j) y
    obtain ⟨c, rfl⟩ := (hB j).2 σ
    have hc : (Glob.formCos q U a).cx.d j c = 0 :=
      (hB (j + 1)).1 (((formCoch_d q U a j c).trans hσ).trans (map_zero _).symm)
    exact ⟨(Glob.formCos q U a).cx.cls c hc, formToCO_cls q U a c hc⟩

end GlobalTheory.CompanionTheory.OmCech
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechBijectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_to_cech_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type}
    (U : ι → X.Opens) (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ),
    Function.Bijective (formToCO q U a j) := by
  first | exact @GlobalTheory.CompanionTheory.OmCech.formToCO_bijective | exact GlobalTheory.CompanionTheory.OmCech.formToCO_bijective | (intros; apply GlobalTheory.CompanionTheory.OmCech.formToCO_bijective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechSmul
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechSmul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.CompanionTheory.OmBridge

open GlobalTheory.HodgeCoh GlobalTheory.CechDR

variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem algebraMap_sec (W : X.Opens) (r : K) :
    letI := algΓ q
    algebraMap K (Sec q W) r = restrictTop W (algebraMap K Γ(X, ⊤) r) := by
  letI := algΓ q
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appLE ⊤ W le_top).hom r =
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop) ≫ X.presheaf.map (homOfLE le_top).op).hom r
  congr 2

theorem toOm_smul (a : ℕ) (W : X.Opens) (r : K) (x : OmU q W a) :
    letI := algΓ q
    CrystallineSemistableComparison.Om.Cech.toOm q a W (r • x) =
      (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).asHom.hom.app (op W)
        (CrystallineSemistableComparison.Om.Cech.toOm q a W x) := by
  letI := algΓ q
  rw [← algebraMap_smul (Sec q W) r x]
  have h := ((toOmega q a).app (op W)).hom.map_smul (algebraMap K (Sec q W) r) x
  refine h.trans ?_
  rw [algebraMap_sec q W r]
  rfl

variable {ι : Type} (U : ι → X.Opens) (a : ℕ)

theorem formCoch_smul (n : ℕ) (r : K) (c : (Glob.formCos q U a).X n) :
    letI := algΓ q
    formCoch q U a n (r • c) =
      GroundTheory.Arith.SchemeCoh.push U
        (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).asHom.hom n (formCoch q U a n c) := by
  letI := algΓ q
  funext i
  change res _ (inter_le_capO U i) (CrystallineSemistableComparison.Om.Cech.toOm q a (Pb.capO U i) (r • c i)) =
    (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).asHom.hom.app (op (inter U i))
      (res _ (inter_le_capO U i) (CrystallineSemistableComparison.Om.Cech.toOm q a (Pb.capO U i) (c i)))
  rw [toOm_smul]
  exact (ConcreteCategory.congr_hom
    ((smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).asHom.hom.naturality
      (homOfLE (inter_le_capO U i)).op) _).symm

theorem formToCO_smul (j : ℕ) (r : K) (x : (Glob.formCos q U a).cx.H j) :
    formToCO q U a j (r • x) = r • formToCO q U a j x := by
  letI := algΓ q
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc' : (Glob.formCos q U a).cx.d j c = 0 := hc
  have hrc : (Glob.formCos q U a).cx.d j (r • c) = 0 := by rw [map_smul, hc', smul_zero]
  change formToCO q U a j ((Glob.formCos q U a).cx.cls (r • c) hrc) =
    r • formToCO q U a j ((Glob.formCos q U a).cx.cls c hc')
  rw [formToCO_cls, formToCO_cls]
  have hd : d (modulesAb (Omega q a)).obj U j (formCoch q U a j c) = 0 := by
    rw [← formCoch_d]
    exact (congrArg _ hc').trans (map_zero _)
  change _ = GroundTheory.Arith.SchemeCoh.cechHMap U (smulAbRingHom (Omega q a) (algebraMap K Γ(X, ⊤) r)).asHom.hom j
    (GroundTheory.Arith.SchemeCoh.cls (formCoch q U a j c) hd)
  rw [GroundTheory.Arith.SchemeCoh.cechHMap_cls]
  exact GroundTheory.Arith.SchemeCoh.cls_congr U (formCoch_smul q U a j r c) _ _

end GlobalTheory.CompanionTheory.OmBridge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormsToCechSmulStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_to_cech_smul :
    type_of% @GlobalTheory.CompanionTheory.OmBridge.formToCO_smul :=
  @GlobalTheory.CompanionTheory.OmBridge.formToCO_smul
end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovOfLocal
theorem UpperTheory.Reformulated.B.Qm13.cov_of_local :
    ∀ {O : Type} [inst : CommRing O] {X : AlgebraicGeometry.Scheme} (Q : X.Opens → Prop)
    (q : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of O)) [AlgebraicGeometry.IsSeparated q]
    [AlgebraicGeometry.QuasiCompact q],
    (∀ (x : ↥X), ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ Q V ∧ Nonempty (CrystallineSemistableComparison.Pb.Coord q V d)) →
      ∃ (U : CrystallineSemistableComparison.Pb.Cov q),
        ∀ (α : U.ι),
          Q
            (U.U
              α) := by
  intro O _ X Q q _ _ h
  choose V d hx hQ hc using h
  have : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace q
  have : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from q]; infer_instance⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨⟨s, fun a => V a, fun a => d a, fun a => (hc a).some, ?_, fun S hS => ?_⟩, fun a => hQ _⟩
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  · exact AlgebraicGeometry.IsAffineOpen.biInf (S : Set s) S.finite_toSet hS
      fun a _ => (hc a).some.affine
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.FormToCOBijectiveI
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.BridgeLApply
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.NeedPf
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.CovRefine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Om.Nt2

def CovRefine : Prop :=
  ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsSeparated q] [QuasiCompact q]
    {κ : Type} (V : κ → X.Opens), iSup V = ⊤ → ∃ U : Pb.Cov q, ∀ α, ∃ k, U.U α ≤ V k

def PullHId : Prop :=
  ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (h : 𝟙 X ≫ q = q) (a n : ℕ)
    (x : HT.Hdg q a n), HT.pullH (𝟙 X) h a n x = x

def PullCId : Prop :=
  ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (h : 𝟙 X ≫ q = q) (a j : ℕ)
    (x : HodgeC q a j), pullC (𝟙 X) h a j x = x

end CrystallineSemistableComparison.Om.Nt2
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Om.Nt2

theorem cov_of_local' {O : Type} [CommRing O] {X : Scheme.{0}} (Q : X.Opens → Prop) (q : X ⟶ Spec (CommRingCat.of O))
    [IsSeparated q] [QuasiCompact q] (h : ∀ x : X, ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ Q V ∧ Nonempty (Pb.Coord q V d)) :
    ∃ U : Pb.Cov q, ∀ α, Q (U.U α) :=
  _root_.UpperTheory.Reformulated.B.Qm13.cov_of_local Q q h

theorem cov_refine : CovRefine := by
  intro K _ X q _ _ _ κ V hV
  refine cov_of_local' (fun W => ∃ k, W ≤ V k) q fun x => ?_
  have hx : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨W, hW, hxW, hWk⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := V k) (x := x) hk
  have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ W le_top).hom :=
    RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hW le_top)
  obtain ⟨f, hf, hst⟩ :=
    GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth RingHom.isStandardSmooth_respectsIso q hW h hxW
  obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
  exact ⟨_, n, hf, ⟨k, fun y hy => hWk (X.basicOpen_le f hy)⟩, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hW f g hg he⟩

theorem pullH_id : PullHId := fun q h a n x => GlobalTheory.CompanionTheory.HodgePull.pullH_id _ _ q a n x

theorem pullC_id : PullCId := fun q h a j x => GlobalTheory.HodgeCoh.hodgePull_id q a j x

end CrystallineSemistableComparison.Om.Nt2
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.Nt2

open CrystallineSemistableComparison.Om.Glob CrystallineSemistableComparison.Om.Cech

theorem cov_aff {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (U : Pb.Cov q)
    (n : ℕ) (i : Fin (n + 1) → U.ι) : IsAffineOpen (⨅ a, U.U (i a)) := by
  classical
  have h := U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ 0)⟩
  have e : (⨅ α ∈ Finset.univ.image i, U.U α) = ⨅ a, U.U (i a) := by
    refine le_antisymm (le_iInf fun a => iInf₂_le (i a) (Finset.mem_image_of_mem i (Finset.mem_univ a))) ?_
    refine le_iInf₂ fun α hα => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
    exact iInf_le (fun a => U.U (i a)) a
  rw [e] at h
  exact h

theorem cls_eq {X : TopCat.{0}} {P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {ι : Type}
    {U : ι → TopologicalSpace.Opens X} {n : ℕ} {σ σ' : GroundTheory.Arith.SchemeCoh.Cochain P U n} (e : σ = σ')
    (h : GroundTheory.Arith.SchemeCoh.d P U n σ = 0) (h' : GroundTheory.Arith.SchemeCoh.d P U n σ' = 0) :
    GroundTheory.Arith.SchemeCoh.cls σ h = GroundTheory.Arith.SchemeCoh.cls σ' h' := by
  subst e
  rfl

theorem capO_pre {X Y : Scheme.{0}} (u : X ⟶ Y) {ι κ : Type} (U : ι → X.Opens) (W : κ → Y.Opens) (τ : ι → κ)
    (hτ : ∀ α, U α ≤ u ⁻¹ᵁ W (τ α)) {n : ℕ} (i : Fin n → ι) : Pb.capO U i ≤ u ⁻¹ᵁ Pb.capO W (τ ∘ i) := by
  intro x hx
  rw [← SetLike.mem_coe, Pb.capO, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter] at hx
  change u.base x ∈ Pb.capO W (τ ∘ i)
  rw [← SetLike.mem_coe, Pb.capO, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  exact fun k => hτ (i k) (hx k)

def covX {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsProper q] : Pb.Cov q :=
  Classical.choice ((Pb.cov_ex q).1 inferInstance)

end CrystallineSemistableComparison.Om.Nt2
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.Nt2F

open CrystallineSemistableComparison.Om.Glob CrystallineSemistableComparison.Om.Cech CrystallineSemistableComparison.Om.Nt2

def bridgeI (hB : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _)) (hS : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _))
    {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Pb.Cov q) (a j : ℕ) :
    (formCos q U.U a).cx.H j ≃ₗ[K] CO q U.U a j :=
  LinearEquiv.ofBijective
    { toFun := formToCO q U.U a j
      map_add' := (formToCO q U.U a j).map_add'
      map_smul' := hS q U.U a j }
    (hB q U.U (cov_aff U) a j)

theorem bridgeI_apply (hB : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _)) (hS : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _))
    {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Pb.Cov q) (a j : ℕ)
    (y : (formCos q U.U a).cx.H j) : bridgeI hB hS q U a j y = formToCO q U.U a j y := rfl

def lerayI (hA : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _)) {K : Type} [Field K] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (U : Pb.Cov q) (a j : ℕ) : CO q U.U a j ≃ₗ[K] HodgeC q a j :=
  (cechOmAdd q U.U U.cover (cov_aff U) a j).toLinearEquiv (hA q U.U U.cover (cov_aff U) a j)

theorem lerayI_apply (hA : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _)) {K : Type} [Field K] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (U : Pb.Cov q) (a j : ℕ) (y : CO q U.U a j) :
    lerayI hA q U a j y = cechOmAdd q U.U U.cover (cov_aff U) a j y := rfl

def isoI (hG : type_of% (@CrystallineSemistableComparison.Om.Glob.glob_iso _)) (hB : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _))
    (hS : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _)) (hA : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _))
    {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Pb.Cov q)
    (a j : ℕ) : HT.Hdg q a (a + j) ≃ₗ[K] HodgeC q a j :=
  ((Classical.choose (hG K) q U a j).trans (bridgeI hB hS q U a j)).trans (lerayI hA q U a j)


set_option maxHeartbeats 2000000 in
theorem isoI_nat (hG : type_of% (@CrystallineSemistableComparison.Om.Glob.glob_iso _)) (hB : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _))
    (hS : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _)) (hA : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _))
    (hP : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOm_pull _)) (hC : type_of% (@CrystallineSemistableComparison.Om.Cech.formCoch_pull _))
    {K : Type} [Field K] [CharZero K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (U : Pb.Cov q) (W : Pb.Cov p)
    (τ : U.ι → W.ι) (hτ : ∀ α, U.U α ≤ u ⁻¹ᵁ W.U (τ α)) (a j : ℕ) (x : HT.Hdg p a (a + j)) :
    isoI hG hB hS hA q U a j (HT.pullH u hu a (a + j) x) = pullC u hu a j (isoI hG hB hS hA p W a j x) := by
  have hτ' : ∀ n (i : Fin (n + 1) → U.ι), Pb.capO U.U i ≤ u ⁻¹ᵁ Pb.capO W.U (τ ∘ i) :=
    fun n i => capO_pre u U.U W.U τ hτ i
  obtain ⟨c, hc, rfl⟩ : ∃ (c : (formCos p W.U a).X j) (h0 : (formCos p W.U a).cx.d j c = 0),
      (Classical.choose (hG K) p W a j).symm ((formCos p W.U a).cx.cls c h0) = x := by
    obtain ⟨⟨c, h0⟩, hx⟩ := Submodule.Quotient.mk_surjective _ (Classical.choose (hG K) p W a j x)
    exact ⟨c, h0, by rw [LinearEquiv.symm_apply_eq]; exact hx⟩
  set c' : (formCos q U.U a).X j := fun i => formRes q (hτ' j i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a (c (τ ∘ i)))
    with hc'
  have hd : (formCos q U.U a).cx.d j c' = fun i =>
      formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a ((formCos p W.U a).cx.d j c (τ ∘ i))) := by
    funext i
    change (Cos.d (formCos q U.U a) j c') i =
      formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a (Cos.d (formCos p W.U a) j c (τ ∘ i)))
    let evU : (formCos q U.U a).X (j + 1) →+ OmU q (Pb.capO U.U i) a :=
      { toFun := fun f => f i, map_zero' := rfl, map_add' := fun _ _ => rfl }
    let evW : (formCos p W.U a).X (j + 1) →+ OmU p (Pb.capO W.U (τ ∘ i)) a :=
      { toFun := fun f => f (τ ∘ i), map_zero' := rfl, map_add' := fun _ _ => rfl }
    change evU (Cos.d (formCos q U.U a) j c') =
      formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a (evW (Cos.d (formCos p W.U a) j c)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Cos.d_apply, Cos.d_apply, map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, map_zsmul, map_zsmul, map_zsmul]
    congr 1
    change formRes q (Pb.capO_comp U.U i k.succAbove) a (formRes q (hτ' j (i ∘ k.succAbove)) a
        (formPull hu (Pb.capO W.U (τ ∘ (i ∘ k.succAbove))) a (c (τ ∘ (i ∘ k.succAbove))))) =
      formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a
        (formRes p (Pb.capO_comp W.U (τ ∘ i) k.succAbove) a (c ((τ ∘ i) ∘ k.succAbove))))
    rw [← formRes_formPull, formRes_formRes, formRes_formRes]
    rfl
  have h1 : (formCos q U.U a).cx.d j c' = 0 := by
    rw [hd]
    funext i
    have h0 : (formCos p W.U a).cx.d j c (τ ∘ i) = 0 := congrFun hc (τ ∘ i)
    refine (congrArg (fun y => formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a y)) h0).trans ?_
    change formRes q (hτ' (j + 1) i) a (formPull hu (Pb.capO W.U (τ ∘ i)) a 0) = 0
    exact (congrArg (formRes q (hτ' (j + 1) i) a) (map_zero _)).trans (map_zero _)
  have key := Classical.choose_spec (hG K) q p u hu U W τ hτ' a j c hc h1
  have hb : bridgeI hB hS q U a j ((formCos q U.U a).cx.cls c' h1) =
      cechPull hu W.U U.U τ hτ a j (bridgeI hB hS p W a j ((formCos p W.U a).cx.cls c hc)) := by
    rw [bridgeI_apply, bridgeI_apply, formToCO_cls, formToCO_cls]
    exact (cls_eq (hC hu W.U U.U τ hτ (fun i => hτ' _ i) a j c).symm _ _).trans
      (cechPullH_cls u.base (GlobalTheory.toAbSheafPush (omegaPull hu a)).hom W.U U.U τ hτ (formCoch p W.U a j c) _).symm
  simp only [isoI, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [key, LinearEquiv.apply_symm_apply, hb, lerayI_apply, lerayI_apply]
  exact hP q p u hu W.U W.cover (cov_aff W) U.U U.cover (cov_aff U) τ hτ a j _

theorem hdg_iso_of_ing (hG : type_of% (@CrystallineSemistableComparison.Om.Glob.glob_iso _)) (hB : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _))
    (hS : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _)) (hA : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _))
    (hP : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOm_pull _)) (hC : type_of% (@CrystallineSemistableComparison.Om.Cech.formCoch_pull _))
    (hR : CovRefine) (hH : PullHId) (hCi : PullCId) : type_of% (@CrystallineSemistableComparison.Om.hdg_iso _) := by
  intro K _ _
  refine ⟨fun {X} q _ _ a j => isoI hG hB hS hA q (covX q) a j, ?_⟩
  intro X Y q p _ _ _ _ u hu a j x
  dsimp only
  obtain ⟨U', hU'⟩ := hR q (fun k : (covX q).ι × (covX p).ι => (covX q).U k.1 ⊓ u ⁻¹ᵁ (covX p).U k.2) (by
    refine eq_top_iff.2 fun z _ => ?_
    have hz : z ∈ (⨆ α, (covX q).U α) := by rw [(covX q).cover]; trivial
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    have hy : u.base z ∈ (⨆ β, (covX p).U β) := by rw [(covX p).cover]; trivial
    obtain ⟨β, hβ⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(α, β), ⟨hα, hβ⟩⟩)
  choose k hk using hU'
  have hid : 𝟙 X ≫ q = q := Category.id_comp q
  have e1 : ∀ z : HT.Hdg q a (a + j), isoI hG hB hS hA q U' a j z = isoI hG hB hS hA q (covX q) a j z := by
    intro z
    have := isoI_nat hG hB hS hA hP hC q q (𝟙 X) hid U' (covX q) (fun α => (k α).1) (fun α y hy => ((hk α) hy).1) a j z
    rwa [hH, hCi] at this
  rw [← e1]
  exact isoI_nat hG hB hS hA hP hC q p u hu U' (covX p) (fun α => (k α).2) (fun α => (hk α).trans inf_le_right) a j x

theorem formToCO_bijective_i : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_bijective _) := GlobalTheory.T.forms_to_cech_bijective
theorem formToCO_smul_i : type_of% (@CrystallineSemistableComparison.Om.Cech.formToCO_smul _) := GlobalTheory.T.forms_to_cech_smul
theorem cechOmAdd_smul_i : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOmAdd_smul _) := GlobalTheory.T.cech_forms_add_smul
theorem formCoch_pull_i : type_of% (@CrystallineSemistableComparison.Om.Cech.formCoch_pull _) := CrystallineSemistableComparison.Om.Cech.formCoch_pull_pf

end CrystallineSemistableComparison.Om.Nt2F
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.PfPullC
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.LerayClean
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.ZeroOne
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Nt2

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison.Om.Cech

theorem top_le_map {X Y : TopCat.{0}} (f : X ⟶ Y) : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤ := le_top

theorem zeroEquiv_eq_equivZero {X : TopCat.{0}} (F : AbSheaf X) (W : Opens X) (x : Sheaf.H'.{0} F 0 W) :
    GlobalTheory.SiteCoh.zeroEquiv F W x = GlobalTheory.SheafLES.equivZero.{0} F W x := by
  obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective _ F).surjective x
  rw [GlobalTheory.SheafLES.equivZero_mk₀]
  exact GlobalTheory.SiteCoh.zeroEquiv_mk₀ F W g

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G')
    (s : G.obj.obj (op ⊤)) :
    hPull f φ 0 ((Sheaf.H.equiv₀ G isTerminalTop).symm s) =
      (Sheaf.H.equiv₀ G' isTerminalTop).symm (GroundTheory.Arith.SchemeCoh.res G'.obj (top_le_map f) (φ.hom.app (op ⊤) s)) := by
  rw [AddEquiv.eq_symm_apply]
  simp only [hPull, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [GlobalTheory.SiteCoh.equiv₀_terminalEquiv, zeroEquiv_eq_equivZero, GlobalTheory.SheafPull.equivZero_sitePull,
    ← zeroEquiv_eq_equivZero, ← GlobalTheory.SiteCoh.equiv₀_terminalEquiv, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q) {κ ι : Type} (V : κ → Opens Y)
    (U : ι → Opens X) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (GroundTheory.Arith.SchemeCoh.res Q (top_le_map f) (φ.app (op ⊤) s))).1 := by
  funext j
  change GroundTheory.Arith.SchemeCoh.res Q _ (φ.app _ (GroundTheory.Arith.SchemeCoh.res P _ s)) =
    GroundTheory.Arith.SchemeCoh.res Q _ (GroundTheory.Arith.SchemeCoh.res Q _ (φ.app (op ⊤) s))
  rw [app_res_map, GroundTheory.Arith.SchemeCoh.res_res, GroundTheory.Arith.SchemeCoh.res_res]

theorem cechHZeroEquiv_mk {X : TopCat.{0}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) {ι : Type} (U : ι → Opens X)
    (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P) (hU : iSup U = ⊤) (s : P.obj (op ⊤)) :
    cechHZeroEquiv P U hP hU (QuotientAddGroup.mk (globalCocycle P U s)) = s := by
  change (globalCocycleEquiv P U hP hU).symm (globalCocycle P U s) = s
  exact (globalCocycleEquiv P U hP hU).symm_apply_apply s

theorem cechHZero_pull' : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G') (x : cechH G.obj V 0),
    (cechHZeroEquivH G' U hU : cechH G'.obj U 0 ≃+ Sheaf.H.{0} G' 0) (cechPullH f φ.hom V U τ hτ 0 x) =
      hPull f φ 0 ((cechHZeroEquivH G V hV : cechH G.obj V 0 ≃+ Sheaf.H.{0} G 0) x) := by
  intro X Y f κ ι V hV U hU τ hτ G G' φ x
  obtain ⟨s, rfl⟩ := (cechHZeroEquiv G.obj V G.property hV).symm.surjective x
  have h1 : (cechHZeroEquiv G.obj V G.property hV).symm s = QuotientAddGroup.mk (globalCocycle G.obj V s) := by
    rw [AddEquiv.symm_apply_eq, cechHZeroEquiv_mk]
  have h3 : (⟨pullCoch f φ.hom V U τ hτ 0 (globalCocycle G.obj V s).1,
      pullCoch_mem_cocycles f φ.hom V U τ hτ (globalCocycle G.obj V s).2⟩ : cocycles G'.obj U 0) =
      globalCocycle G'.obj U (GroundTheory.Arith.SchemeCoh.res G'.obj (top_le_map f) (φ.hom.app (op ⊤) s)) :=
    Subtype.ext (pullCoch_globalCocycle f φ.hom V U τ hτ s)
  have h2 : cechPullH f φ.hom V U τ hτ 0 (QuotientAddGroup.mk (globalCocycle G.obj V s)) =
      QuotientAddGroup.mk (globalCocycle G'.obj U
        (GroundTheory.Arith.SchemeCoh.res G'.obj (top_le_map f) (φ.hom.app (op ⊤) s))) := by
    rw [← h3]
    rfl
  simp only [cechHZeroEquivH, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [h1, h2, cechHZeroEquiv_mk, hPull_zero]

theorem cechHOne_pull' : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj V) (hS' : S'.ShortExact) [Injective S'.X₂]
    (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : CechAcyclic S'.X₂.obj U) (α : S ⟶ S'.map (push f))
    (x : cechH S.X₁.obj V 1),
    (cechHOneEquiv U hU hS' hC' hI' : cechH S'.X₁.obj U 1 ≃+ Sheaf.H.{0} S'.X₁ 1) (cechPullH f α.τ₁.hom V U τ hτ 1 x) =
      hPull f α.τ₁ 1 ((cechHOneEquiv V hV hS hC hI : cechH S.X₁.obj V 1 ≃+ Sheaf.H.{0} S.X₁ 1) x) := by
  intro X Y f κ ι V hV U hU τ hτ S S' hS _ hC hI hS' _ hC' hI' α x
  have h₁₂ : ∀ (W : (Opens Y)ᵒᵖ) (z : S.X₁.obj.obj W),
      α.τ₂.hom.app W (S.f.hom.app W z) = S'.f.hom.app _ (α.τ₁.hom.app W z) := fun W z => by
    have h := congrArg (fun g : S.X₁ ⟶ (S'.map (push f)).X₂ => g.hom.app W z) α.comm₁₂
    exact h.symm
  have h₂₃ : ∀ (W : (Opens Y)ᵒᵖ) (z : S.X₂.obj.obj W),
      α.τ₃.hom.app W (S.g.hom.app W z) = S'.g.hom.app _ (α.τ₂.hom.app W z) := fun W z => by
    have h := congrArg (fun g : S.X₂ ⟶ (S'.map (push f)).X₃ => g.hom.app W z) α.comm₂₃
    exact h.symm
  obtain ⟨s, rfl⟩ := cechOneProj_surjective V hV hC hI x
  have hL : cechPullH f α.τ₁.hom V U τ hτ 1 (cechOneProj V hC s) =
      cechOneProj U hC' (GroundTheory.Arith.SchemeCoh.res S'.X₃.obj (top_le_map f) (α.τ₃.hom.app (op ⊤) s)) := by
    change cechPullH f α.τ₁.hom V U τ hτ (0 + 1) (hC.delta 0 (globalCocycle S.X₃.obj V s)) =
      hC'.delta 0 (globalCocycle S'.X₃.obj U _)
    refine (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ 0
      (globalCocycle S.X₃.obj V s)).trans ?_
    congr 1
    exact Subtype.ext (pullCoch_globalCocycle f α.τ₃.hom V U τ hτ s)
  rw [hL, cechHOneEquiv_cechOneProj, cechHOneEquiv_cechOneProj]
  change H.δ hS' 0 1 rfl ((Sheaf.H.equiv₀ S'.X₃ isTerminalTop).symm _) =
    hPull f α.τ₁ 1 (H.δ hS 0 1 rfl ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s))
  rw [GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α 0, hPull_zero]
  rfl

end CrystallineSemistableComparison.Om.Nt2
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Nt2

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison.Om.Cech

theorem cechHEquiv_pull_compat {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) :
    ∀ (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro G G' hG hG' φ x
    exact CrystallineSemistableComparison.Om.Nt2.cechHZero_pull' f V hV U hU τ hτ φ x
  | one =>
    intro G G' hG hG' φ x
    obtain ⟨α, rfl⟩ := GlobalTheory.T.injective_resolution_lift_pushforward f φ
    exact CrystallineSemistableComparison.Om.Nt2.cechHOne_pull' f V hV U hU τ hτ (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact hCY V hVB G hG) (injectiveSequence_cechAcyclic G V)
      (injectiveSequence_shortExact G') (injectiveSequence_isCechShortExact hCX U hUB G' hG')
      (injectiveSequence_cechAcyclic G' U) α x
  | more m _ ih =>
    intro G G' hG hG' φ x
    obtain ⟨α, rfl⟩ := GlobalTheory.T.injective_resolution_lift_pushforward f φ
    exact CrystallineSemistableComparison.Om.Nt2.cechHStep_pull' f V U τ hτ (injectiveSequence_shortExact G)
      (injectiveSequence_isCechShortExact hCY V hVB G hG) (injectiveSequence_cechAcyclic G V)
      (injectiveSequence_shortExact G') (injectiveSequence_isCechShortExact hCX U hUB G' hG')
      (injectiveSequence_cechAcyclic G' U) α m _ _
      (fun y => ih
        (injectiveSequence_goodAcyclic hCY G hG) (injectiveSequence_goodAcyclic hCX G' hG') α.τ₃ y) x

theorem cechHEquiv_pullC : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  intro X Y f BY GoodY BX GoodX hCY hCX κ ι V hV hVB U hU hUB τ hτ n G G' hG hG' φ x
  exact cechHEquiv_pull_compat f hCY hCX V hV hVB U hU hUB τ hτ n hG hG' φ x

end CrystallineSemistableComparison.Om.Nt2
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech.CechFormPull

open CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull

theorem cechOm_pull_pf : ∀ {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q) {κ ι : Type} (V : κ → Y.Opens) (hV : iSup V = ⊤)
    (hVaff : ∀ (n : ℕ) (i : Fin (n + 1) → κ), IsAffineOpen (⨅ a, V (i a))) (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i))
    (a j : ℕ) (x : CO p V a j),
    cechOmAdd q U hU hUaff a j (cechPull hu V U τ hτ a j x) = pullC u hu a j (cechOmAdd p V hV hVaff a j x) := by
  intro K _ X Y q p u hu κ ι V hV hVaff U hU hUaff τ hτ a j x
  have h1 := CrystallineSemistableComparison.Om.Nt2.cechHEquiv_pullC u.base isCoverSystem_isBasicCover isCoverSystem_isBasicCover V hV
    (fun i => by rw [inter_eq_iInf]; exact hVaff _ i) U hU (fun i => by rw [inter_eq_iInf]; exact hUaff _ i) τ hτ j
    (goodAcyclic_modulesAb (GlobalTheory.HodgeCoh.Omega p a)) (goodAcyclic_modulesAb (GlobalTheory.HodgeCoh.Omega q a))
    (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)) x
  have h2 := hPull_omega_pf q p u hu a j (cechHAddEquivH V hV hVaff (GlobalTheory.HodgeCoh.Omega p a) j x)
  exact (congrArg (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).symm h1).trans h2

end CrystallineSemistableComparison.Om.Cech.CechFormPull
end
end

open CategoryTheory AlgebraicGeometry GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.Nt2F

open CrystallineSemistableComparison.Om.Glob CrystallineSemistableComparison.Om.Cech CrystallineSemistableComparison.Om.Nt2

theorem glob_iso_c : type_of% (@CrystallineSemistableComparison.Om.Glob.glob_iso _) := CrystallineSemistableComparison.Om.GlobPf2.glob_iso
theorem cechOm_pull_c : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOm_pull _) := CrystallineSemistableComparison.Om.Cech.CechFormPull.cechOm_pull_pf

theorem hodge_iso_natural_cech : type_of% (@CrystallineSemistableComparison.Om.hdg_iso _) :=
  hdg_iso_of_ing glob_iso_c formToCO_bijective_i formToCO_smul_i cechOmAdd_smul_i cechOm_pull_c formCoch_pull_i
    cov_refine pullH_id pullC_id

end CrystallineSemistableComparison.Om.Nt2F
