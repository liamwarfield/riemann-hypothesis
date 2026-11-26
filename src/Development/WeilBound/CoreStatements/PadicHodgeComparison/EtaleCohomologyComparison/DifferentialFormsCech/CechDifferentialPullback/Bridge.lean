module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh

section Ref

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
  {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
  {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
  (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))


include hτ in
theorem inter_le_map {n : ℕ} (t : Fin n → ι) : inter U t ≤ (Opens.map f).obj (inter V (τ ∘ t)) := by
  intro x hx
  rw [mem_inter_iff] at hx
  change f x ∈ inter V (τ ∘ t)
  rw [mem_inter_iff]
  exact fun a => hτ (t a) (hx a)

def pullCoch (n : ℕ) : Cochain P V n →+ Cochain Q U n where
  toFun σ t := res Q (inter_le_map f V U τ hτ t) (φ.app (op (inter V (τ ∘ t))) (σ (τ ∘ t)))
  map_zero' := by funext t; simp
  map_add' σ σ' := by funext t; simp

omit hτ in
theorem app_res_map {A B : Opens Y} (h : A ≤ B) (x : P.obj (op B)) :
    φ.app (op A) (res P h x) = res Q ((Opens.map f).monotone h) (φ.app (op B) x) := by
  simp only [res, ← ConcreteCategory.comp_apply, φ.naturality]
  rfl

theorem pullCoch_d (n : ℕ) (σ : Cochain P V n) :
    pullCoch f φ V U τ hτ (n + 1) (d P V n σ) = d Q U n (pullCoch f φ V U τ hτ n σ) := by
  funext t
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pullCoch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, d_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [app_res_map, res_res, res_res]
  rfl

theorem pullCoch_mem_cocycles {n : ℕ} {σ : Cochain P V n} (hσ : σ ∈ cocycles P V n) :
    pullCoch f φ V U τ hτ n σ ∈ cocycles Q U n := by
  rw [mem_cocycles] at hσ ⊢
  rw [← pullCoch_d, hσ, map_zero]

theorem pullCoch_mem_coboundaries {n : ℕ} {σ : Cochain P V n} (hσ : σ ∈ coboundaries P V n) :
    pullCoch f φ V U τ hτ n σ ∈ coboundaries Q U n := by
  cases n with
  | zero =>
    rw [coboundaries_zero, AddSubgroup.mem_bot] at hσ ⊢
    rw [hσ, map_zero]
  | succ n =>
    rw [coboundaries_succ] at hσ ⊢
    obtain ⟨ρ, rfl⟩ := hσ
    exact ⟨pullCoch f φ V U τ hτ n ρ, (pullCoch_d f φ V U τ hτ n ρ).symm⟩

def cechPullH (n : ℕ) : cechH P V n →+ cechH Q U n :=
  QuotientAddGroup.map _ _ (AddMonoidHom.codRestrict ((pullCoch f φ V U τ hτ n).comp (cocycles P V n).subtype)
    (cocycles Q U n) fun σ => pullCoch_mem_cocycles f φ V U τ hτ σ.2) fun σ hσ => by
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
      exact pullCoch_mem_coboundaries f φ V U τ hτ (AddSubgroup.mem_addSubgroupOf.1 hσ)

theorem cechPullH_cls {n : ℕ} (σ : Cochain P V n) (hσ : d P V n σ = 0) :
    cechPullH f φ V U τ hτ n (cls σ hσ) =
      cls (pullCoch f φ V U τ hτ n σ) (by rw [← pullCoch_d, hσ, map_zero]) := rfl

end Ref

section Pull

open GlobalTheory.SheafPull

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}

def hPull (φ : G ⟶ (push f).obj G') (n : ℕ) : Sheaf.H.{0} G n →+ Sheaf.H.{0} G' n :=
  (GlobalTheory.SiteCoh.terminalEquiv G' n isTerminalTop).toAddMonoidHom.comp
    ((pull.{0, 0} f φ n (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤)).comp
      (GlobalTheory.SiteCoh.terminalEquiv G n isTerminalTop).symm.toAddMonoidHom)

end Pull

section Forms

variable {K : Type} [Field K] {X Y : Scheme.{0}}

def CO (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens) (a j : ℕ) : Type :=
  cechH (X := X.toTopCat) (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U j

instance (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens) (a j : ℕ) :
    AddCommGroup (CO q U a j) :=
  inferInstanceAs (AddCommGroup (cechH (X := X.toTopCat) (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U j))

instance (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens) (a j : ℕ) :
    Module K (CO q U a j) :=
  letI := GlobalTheory.HodgeCoh.algΓ q
  inferInstanceAs (Module K (cechH (X := X.toTopCat) (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U j))

def cechPull {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)} {u : X ⟶ Y} (hu : u ≫ p = q)
    {κ ι : Type} (V : κ → Y.Opens) (U : ι → X.Opens) (τ : ι → κ) (hτ : ∀ i, U i ≤ u ⁻¹ᵁ V (τ i)) (a j : ℕ) :
    CO p V a j →+ CO q U a j :=
  cechPullH u.base (GlobalTheory.toAbSheafPush (GlobalTheory.HodgeCoh.omegaPull hu a)).hom V U τ hτ j

def cechOmAdd (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hUaff : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (i a))) (a j : ℕ) :
    CO q U a j ≃+ HodgeC q a j :=
  (cechHAddEquivH.{0} U hU hUaff (GlobalTheory.HodgeCoh.Omega q a) j).trans (GlobalTheory.coh.toH (GlobalTheory.HodgeCoh.Omega q a) j).symm

end Forms

end CrystallineSemistableComparison.Om.Cech
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace CrystallineSemistableComparison.Om.Cech

open GroundTheory.Arith.SchemeCoh

variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {ι : Type} (U : ι → X.Opens) (a : ℕ)

def toOm (W : X.Opens) : GlobalTheory.CechDR.OmU q W a →+ (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj.obj (op W) where
  toFun x := (GlobalTheory.HodgeCoh.toOmega q a).app (op W) x
  map_zero' := map_zero _
  map_add' x y := map_add _ x y

theorem toOm_formRes {W W' : X.Opens} (h : W' ≤ W) (x : GlobalTheory.CechDR.OmU q W a) :
    toOm q a W' (GlobalTheory.HodgeCoh.formRes q h a x) = res (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj h (toOm q a W x) :=
  PresheafOfModules.naturality_apply (GlobalTheory.HodgeCoh.toOmega q a) (homOfLE h).op x

theorem inter_le_capO {n : ℕ} (i : Fin n → ι) : inter U i ≤ Pb.capO U i := by
  intro x hx
  rw [mem_inter_iff] at hx
  unfold Pb.capO
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact hx

def formCoch (n : ℕ) : (Glob.formCos q U a).X n →+ Cochain (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n where
  toFun c i := res _ (inter_le_capO U i) (toOm q a (Pb.capO U i) (c i))
  map_zero' := by
    funext i
    rw [show (0 : (Glob.formCos q U a).X n) i = 0 from rfl, map_zero, map_zero]
    rfl
  map_add' c c' := by
    funext i
    rw [show (c + c') i = c i + c' i from rfl, map_add (f := _), map_add (f := _)]
    rfl

theorem formCoch_d (n : ℕ) (c : (Glob.formCos q U a).X n) :
    formCoch q U a (n + 1) (CrystallineSemistableComparison.Cos.d (Glob.formCos q U a) n c) =
      d (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n (formCoch q U a n c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CrystallineSemistableComparison.Cos.d_apply, map_sum]
  funext i
  rw [GroundTheory.Arith.SchemeCoh.d_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Pi.smul_apply]
  congr 1
  change res _ (inter_le_capO U i) (toOm q a (Pb.capO U i)
      (GlobalTheory.HodgeCoh.formRes q (Pb.capO_comp U i k.succAbove) a (c (i ∘ k.succAbove)))) =
    res _ (inter_le_comp U i k.succAbove) (res _ (inter_le_capO U (i ∘ k.succAbove))
      (toOm q a (Pb.capO U (i ∘ k.succAbove)) (c (i ∘ k.succAbove))))
  rw [toOm_formRes, res_res, res_res]

def formZ (n : ℕ) : (Glob.formCos q U a).cx.Z n →+ cocycles (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n :=
  AddMonoidHom.codRestrict ((formCoch q U a n).comp ((Glob.formCos q U a).cx.Z n).subtype.toAddMonoidHom) _
    fun z => by
      rw [mem_cocycles]
      change d (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n (formCoch q U a n z.1) = 0
      rw [← formCoch_d]
      change formCoch q U a (n + 1) ((Glob.formCos q U a).cx.d n z.1) = 0
      rw [z.2, map_zero]

def formToCO (n : ℕ) : (Glob.formCos q U a).cx.H n →+ CO q U a n :=
  QuotientAddGroup.lift (((Glob.formCos q U a).cx.B n).submoduleOf ((Glob.formCos q U a).cx.Z n)).toAddSubgroup
    ((QuotientAddGroup.mk' _).comp (formZ q U a n)) fun z hz => by
      change (QuotientAddGroup.mk' ((coboundaries (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n).addSubgroupOf
        (cocycles (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n)) (formZ q U a n z) : cechH _ U n) = 0
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      have hz' : z.1 ∈ (Glob.formCos q U a).cx.B n := hz
      change formCoch q U a n z.1 ∈ coboundaries (modulesAb (GlobalTheory.HodgeCoh.Omega q a)).obj U n
      cases n with
      | zero =>
        have h0 : z.1 = 0 := hz'
        rw [h0, map_zero]
        exact zero_mem _
      | succ n =>
        obtain ⟨c, hc⟩ := hz'
        rw [coboundaries_succ, ← hc]
        exact ⟨formCoch q U a n c, (formCoch_d q U a n c).symm⟩

theorem formToCO_cls {n : ℕ} (c : (Glob.formCos q U a).X n) (hc : (Glob.formCos q U a).cx.d n c = 0) :
    formToCO q U a n ((Glob.formCos q U a).cx.cls c hc) =
      cls (formCoch q U a n c) (by rw [← formCoch_d]; exact (congrArg _ hc).trans (map_zero _)) := rfl

end CrystallineSemistableComparison.Om.Cech
