module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CohomologyPresheafFunctorMapAppApply
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PresheafCubeExactAtSuccOfSurjective
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe w v u

noncomputable section

namespace GlobalTheory

section Presheaf

variable {T : TopCat.{w}} {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  (hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W), Function.Surjective (presheafRes P h))

include hP hs

end Presheaf

section Ab

variable {T : TopCat.{w}} {ι : Type}

variable [LinearOrder ι] [Finite ι] (F : TopCat.Sheaf AddCommGrpCat.{w} T) [F.IsFlasque]

variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] in
private theorem cubeComplex_exactAt_one_of_hom_surj_empty_inj_nonempty {A B : _root_.GlobalTheory.Cube ι R} (φ : A ⟶ B)
    (hsurj : ∀ s : Finset ι, s = ∅ → Function.Surjective (φ.app s))
    (hinj : ∀ s : Finset ι, s.Nonempty → Function.Injective (φ.app s))
    (hB : (_root_.GlobalTheory.cubeComplex B).ExactAt 1) : (_root_.GlobalTheory.cubeComplex A).ExactAt 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, _root_.GlobalTheory.cubeComplex_exactAt_succ_iff] at hB ⊢
  have comm : ∀ p (x : A.Term p), (_root_.GlobalTheory.cubeComplexMap φ).f (p + 1) (A.d p x) =
      B.d p ((_root_.GlobalTheory.cubeComplexMap φ).f p x) := by
    intro p x
    have := congrArg (fun f => f.hom x) ((_root_.GlobalTheory.cubeComplexMap φ).comm p (p + 1))
    simp only [_root_.GlobalTheory.cubeComplex, CochainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.coe_comp, Function.comp_apply] at this
    exact this.symm
  have dd : ∀ y : A.Term 0, A.d 1 (A.d 0 y) = 0 := by
    intro y
    have := congrArg (fun f => f.hom y) ((_root_.GlobalTheory.cubeComplex A).d_comp_d 0 1 2)
    simpa [_root_.GlobalTheory.cubeComplex, LinearMap.comp_apply] using this
  have inj1 : Function.Injective ((_root_.GlobalTheory.cubeComplexMap φ).f 1) := by
    intro x y hxy
    funext s
    apply hinj s.1 (Finset.card_pos.mp (by rw [s.2]; norm_num))
    exact congrFun hxy s
  have surj0 : Function.Surjective ((_root_.GlobalTheory.cubeComplexMap φ).f 0) := by
    intro y
    refine ⟨fun s => (hsurj s.1 (Finset.card_eq_zero.mp s.2) (y s)).choose, ?_⟩
    funext s
    exact (hsurj s.1 (Finset.card_eq_zero.mp s.2) (y s)).choose_spec
  intro x
  constructor
  · intro hx
    have h1 : B.d 1 ((_root_.GlobalTheory.cubeComplexMap φ).f 1 x) = 0 := by
      rw [← comm 1 x]
      change (_root_.GlobalTheory.cubeComplexMap φ).f 2 (A.d 1 x) = 0
      rw [show A.d 1 x = 0 from hx]
      exact map_zero _
    obtain ⟨y, hy⟩ := (hB ((_root_.GlobalTheory.cubeComplexMap φ).f 1 x)).1 h1
    obtain ⟨z, rfl⟩ := surj0 y
    exact ⟨z, inj1 ((comm 0 z).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact dd y

variable {T : TopCat.{w}} {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  (hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W), Function.Surjective (_root_.GlobalTheory.presheafRes P h)) in
include hP hs in
private theorem cubeComplex_presheafCube_exactAt_one (V : Opens T) (U : ι → Opens T) :
    (_root_.GlobalTheory.cubeComplex (_root_.GlobalTheory.presheafCube P V U)).ExactAt 1 := by
  have h : ∀ s, _root_.GlobalTheory.cechOpen (V ⊓ ⨆ i, U i) U s ≤ _root_.GlobalTheory.cechOpen V U s :=
    fun s => _root_.GlobalTheory.cechOpen_mono (V := V) (U := U) (hV := inf_le_left)
      (hU := fun _ => le_rfl) s
  refine cubeComplex_exactAt_one_of_hom_surj_empty_inj_nonempty (_root_.GlobalTheory.presheafCubeRes P h) ?_ ?_
    (_root_.GlobalTheory.presheafCube_exactAt_zero_one hP (V := V ⊓ ⨆ i, U i) (U := U) inf_le_right).2
  · rintro s rfl
    exact hs (h ∅)
  · intro s hs' x y hxy
    have h' : _root_.GlobalTheory.cechOpen V U s ≤ _root_.GlobalTheory.cechOpen (V ⊓ ⨆ i, U i) U s := by
      intro z hz
      rw [_root_.GlobalTheory.mem_cechOpen] at hz ⊢
      obtain ⟨j, hj⟩ := hs'
      exact ⟨⟨hz.1, Opens.mem_iSup.mpr ⟨j, hz.2 j hj⟩⟩, hz.2⟩
    have back : ∀ (O O' : Opens T) (h₁ : O' ≤ O) (h₂ : O ≤ O') (w : P.obj (op O)),
        P.map (homOfLE h₂).op (P.map (homOfLE h₁).op w) = w := by
      intro O O' h₁ h₂ w
      rw [← ConcreteCategory.comp_apply, ← P.map_comp,
        show (homOfLE h₁).op ≫ (homOfLE h₂).op = 𝟙 _ from Subsingleton.elim _ _]
      simp
    have key : ∀ w, P.map (homOfLE h').op ((_root_.GlobalTheory.presheafCubeRes P h).app s w) = w :=
      fun w => back _ _ (h s) h' w
    rw [← key x, ← key y, hxy]

variable {T : TopCat.{w}} {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  (hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W), Function.Surjective (_root_.GlobalTheory.presheafRes P h)) in
include hP hs in
private theorem cubeComplex_presheafCube_exactAt_add_one_of_card (n : ℕ) :
    ∀ {α : Type} [LinearOrder α] [Fintype α], Fintype.card α = n →
      ∀ (V : Opens T) (U : α → Opens T) (p : ℕ),
        (_root_.GlobalTheory.cubeComplex (_root_.GlobalTheory.presheafCube P V U)).ExactAt (p + 1) := by
  induction n with
  | zero =>
    intro α _ _ hcard V U p
    rw [_root_.GlobalTheory.cubeComplex_exactAt_succ_iff]
    have : Subsingleton ((_root_.GlobalTheory.presheafCube P V U).Term (p + 1)) :=
      _root_.GlobalTheory.Cube.subsingleton_term _ (by omega)
    have : Subsingleton ((_root_.GlobalTheory.presheafCube P V U).Term (p + 1 + 1)) :=
      _root_.GlobalTheory.Cube.subsingleton_term _ (by omega)
    intro x
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  | succ n ih =>
    intro α _ _ hcard V U p
    cases p with
    | zero => exact cubeComplex_presheafCube_exactAt_one hP hs V U
    | succ p =>
      obtain ⟨i⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
      let e : {j : α // j ≠ i} ↪o α := OrderEmbedding.subtype _
      have he : Set.range e = {i}ᶜ := by
        ext j
        simp [e]
      have hcard' : Fintype.card {j : α // j ≠ i} = n := by
        simp [Fintype.card_subtype_compl, hcard]
      apply _root_.GlobalTheory.cubeComplex_exactAt_succ_of_faces he
      · exact (ih hcard' V (fun k => U (e k)) (p + 1)).of_iso
          ((_root_.GlobalTheory.cubeFunctor _ R).mapIso (_root_.GlobalTheory.presheafCubeLowerFaceIso P V U e)).symm
      · exact (ih hcard' (V ⊓ U i) (fun k => U (e k)) p).of_iso
          ((_root_.GlobalTheory.cubeFunctor _ R).mapIso (_root_.GlobalTheory.presheafCubeUpperFaceIso P V U e i)).symm

theorem _root_.GlobalTheory.subsingleton_cechAbH_succ_of_isFlasque (V : Opens T) (U : ι → Opens T) (p : ℕ) :
    Subsingleton (_root_.GlobalTheory.cechAbH F.obj V U (p + 1)) := by
  have := Fintype.ofFinite ι
  have hP := _root_.GlobalTheory.isSheaf_comp_abToIntModule F.property
  have hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W),
      Function.Surjective (_root_.GlobalTheory.presheafRes (F.obj ⋙ _root_.GlobalTheory.abToIntModule) h) := by
    intro W W' h
    have : Epi (F.obj.map (homOfLE h).op) := TopCat.Presheaf.IsFlasque.epi _
    exact (AddCommGrpCat.epi_iff_surjective _).mp this
  have hex := cubeComplex_presheafCube_exactAt_add_one_of_card hP hs _ rfl V U (p + 1)
  have hcech := (_root_.GlobalTheory.cechComplex_exactAt_succ_iff_cube _ p).mpr hex
  exact ModuleCat.subsingleton_of_isZero hcech.isZero_homology

end Ab

section Modules

variable {X : Scheme.{u}} {ι : Type} (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  (F : X.Modules) [hF : TopCat.Presheaf.IsFlasque (X := X.toPresheafedSpace.carrier) F.presheaf]

include hF

variable [LinearOrder ι] [Finite ι]

end Modules

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
namespace GlobalTheory.AddEquivOfSurjectiveKernel

universe u_1 u_2 u_3

theorem exists_addEquiv_of_surjective_of_ker_iff {A : Type u_1} {B : Type u_2} {C : Type u_3}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : A →+ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a : A, f a = 0 ↔ g a = 0) :
    ∃ e : B ≃+ C, ∀ a : A, e (f a) = g a := by
  have key : ∀ a b : A, f a = f b ↔ g a = g b := by
    intro a b
    rw [← sub_eq_zero, ← map_sub, h, map_sub, sub_eq_zero]
  choose s hs using hf
  choose t ht using hg
  have h1 : ∀ a, g (s (f a)) = g a := fun a => (key _ _).1 (hs _)
  have h2 : ∀ a, f (t (g a)) = f a := fun a => (key _ _).2 (ht _)
  refine ⟨{ toFun := fun b => g (s b)
            invFun := fun c => f (t c)
            left_inv := fun b => by
              show f (t (g (s b))) = b
              rw [h2, hs]
            right_inv := fun c => by
              show g (s (f (t c))) = c
              rw [h1, ht]
            map_add' := fun x y => by
              show g (s (x + y)) = g (s x) + g (s y)
              rw [← map_add (f := _), ← key, map_add (f := _), hs, hs, hs] }, fun a => h1 a⟩

end GlobalTheory.AddEquivOfSurjectiveKernel
end

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe v u

noncomputable section

namespace GlobalTheory

theorem exists_addEquiv_of_surjective_of_ker {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : A →+ C) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : ∀ a, f a = 0 ↔ g a = 0) :
    ∃ e : B ≃+ C, ∀ a, e (f a) = g a := by
  first
  | exact @_root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff
  | exact _root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff
  | (apply _root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff ..)

section Cube

variable {ι : Type} [LinearOrder ι] {R : Type v} [Ring R]

theorem δ_cechClass {S : ShortComplex (Cube.{u} ι R)}
    (hS : (S.map (cechFunctor ι R)).ShortExact) (p : ℕ)
    (x₃ : LinearMap.ker (Cube.d S.X₃ (p + 1))) (x₂ : Cube.Term S.X₂ (p + 1))
    (x₁ : LinearMap.ker (Cube.d S.X₁ (p + 1 + 1)))
    (h₂ : Cube.termMap S.g (p + 1) x₂ = x₃.1)
    (h₁ : Cube.termMap S.f (p + 1 + 1) x₁.1 = Cube.d S.X₂ (p + 1) x₂) :
    (hS.δ p (p + 1) rfl).hom (cechClass S.X₃ p x₃) = cechClass S.X₁ (p + 1) x₁ := by
  have hx₃ : (forget₂ (ModuleCat.{u} R) Ab).map ((S.map (cechFunctor ι R)).X₃.d p (p + 1)) x₃.1
      = 0 := by
    change ((cechComplex S.X₃).d p (p + 1)).hom x₃.1 = 0
    rw [cechComplex_d]
    exact x₃.2
  have hx₁ : (forget₂ (ModuleCat.{u} R) Ab).map ((S.map (cechFunctor ι R)).f.f (p + 1)) x₁.1 =
      (forget₂ (ModuleCat.{u} R) Ab).map ((S.map (cechFunctor ι R)).X₂.d p (p + 1)) x₂ := by
    change _ = ((cechComplex S.X₂).d p (p + 1)).hom x₂
    rw [cechComplex_d]
    exact h₁
  have key := hS.δ_apply p (p + 1) rfl x₃.1 hx₃ x₂ h₂ x₁.1 hx₁ (p + 1 + 1) (by simp)
  have aux (A : Cube.{u} ι R) (q j : ℕ) (x : LinearMap.ker (Cube.d A (q + 1)))
      (hj : (ComplexShape.up ℕ).next q = j)
      (hx : (forget₂ (ModuleCat.{u} R) Ab).map ((cechComplex A).d q j) x.1 = 0) :
      (forget₂ (ModuleCat.{u} R) Ab).map ((cechComplex A).homologyπ q)
        ((cechComplex A).cyclesMk x.1 j hj hx) = cechClass A q x := by
    refine congrArg ((cechComplex A).homologyπ q).hom
      (?_ : _ = (cechCyclesIso A q).inv.hom x)
    apply (ModuleCat.mono_iff_injective ((cechComplex A).iCycles q)).1 inferInstance
    exact ((cechComplex A).i_cyclesMk x.1 j hj hx).trans (iCycles_cechCyclesIso_inv A q x).symm
  exact (congrArg (hS.δ p (p + 1) rfl).hom (aux S.X₃ p _ x₃ _ _).symm).trans
    (key.trans (aux S.X₁ (p + 1) _ x₁ _ _))

theorem exists_lift_cechCocycle {S : ShortComplex (Cube.{u} ι R)}
    (hS : (S.map (cechFunctor ι R)).ShortExact) (p : ℕ)
    (x₃ : LinearMap.ker (Cube.d S.X₃ (p + 1))) :
    ∃ (x₂ : Cube.Term S.X₂ (p + 1)) (x₁ : LinearMap.ker (Cube.d S.X₁ (p + 1 + 1))),
      Cube.termMap S.g (p + 1) x₂ = x₃.1 ∧
      Cube.termMap S.f (p + 1 + 1) x₁.1 = Cube.d S.X₂ (p + 1) x₂ := by
  have h q := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hS q
  have hg : Function.Surjective (Cube.termMap S.g (p + 1)) :=
    (ModuleCat.epi_iff_surjective _).1 (h p).epi_g
  have hf : Function.Injective (Cube.termMap S.f (p + 1 + 1 + 1)) :=
    (ModuleCat.mono_iff_injective _).1 (h (p + 1 + 1)).mono_f
  have he : Function.Exact (Cube.termMap S.f (p + 1 + 1)) (Cube.termMap S.g (p + 1 + 1)) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (h (p + 1)).exact
  obtain ⟨x₂, h₂⟩ := hg x₃.1
  obtain ⟨x₁, h₁⟩ := (he (Cube.d S.X₂ (p + 1) x₂)).1 (by rw [Cube.termMap_d, h₂]; exact x₃.2)
  refine ⟨x₂, ⟨x₁, hf ?_⟩, h₂, h₁⟩
  rw [Cube.termMap_d, h₁, Cube.d_d, map_zero]

theorem Cube.SemiHom.homology_δ {R' : Type*} [Ring R'] {σ : R →+* R'}
    {S : ShortComplex (Cube.{u} ι R)} {S' : ShortComplex (Cube.{u} ι R')}
    (hS : (S.map (cechFunctor ι R)).ShortExact) (hS' : (S'.map (cechFunctor ι R')).ShortExact)
    (ψ₁ : Cube.SemiHom σ S.X₁ S'.X₁) (ψ₂ : Cube.SemiHom σ S.X₂ S'.X₂)
    (ψ₃ : Cube.SemiHom σ S.X₃ S'.X₃)
    (hf : ∀ s x, ψ₂.app s ((S.f.app s).hom x) = (S'.f.app s).hom (ψ₁.app s x))
    (hg : ∀ s x, ψ₃.app s ((S.g.app s).hom x) = (S'.g.app s).hom (ψ₂.app s x))
    (p : ℕ) (x : (cechComplex S.X₃).homology p) :
    ψ₁.homology (p + 1) ((hS.δ p (p + 1) rfl).hom x) =
      (hS'.δ p (p + 1) rfl).hom (ψ₃.homology p x) := by
  obtain ⟨x₃, rfl⟩ := cechClass_surjective S.X₃ p x
  obtain ⟨x₂, x₁, h₂, h₁⟩ := exists_lift_cechCocycle hS p x₃
  rw [δ_cechClass hS p x₃ x₂ x₁ h₂ h₁, homology_cechClass, homology_cechClass]
  refine (δ_cechClass hS' p _ (ψ₂.term _ x₂) _ ?_ ?_).symm
  · rw [coe_cocycle, ← h₂]
    exact funext fun s => (hg s.1 _).symm
  · rw [coe_cocycle, ← term_d, ← h₁]
    exact funext fun s => (hf s.1 _).symm

end Cube

section Ab

variable {T : TopCat.{u}} {ι : Type}

def CechAcyclic (V : Opens T) (U : ι → Opens T)
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) : Prop :=
  ∀ s : Finset ι, s.Nonempty → ∀ q, Subsingleton (Sheaf.H'.{u} F (q + 1) (cechOpen V U s))

variable {V : Opens T} {U : ι → Opens T}

theorem cechAcyclic_of_injective (I : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    [Injective I] : CechAcyclic V U I := fun _ _ q => Flasque.subsingleton_H'_of_injective I q _

theorem CechAcyclic.of_shortExact₃
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (h₁ : CechAcyclic V U S.X₁) (h₂ : CechAcyclic V U S.X₂) : CechAcyclic V U S.X₃ :=
  fun s hs q => SheafLES.subsingleton₃ hS _ _ (h₂ s hs q) (h₁ s hs (q + 1))

theorem sections_shortExact_of_subsingleton
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (W : Opens T) (h : Subsingleton (Sheaf.H'.{u} S.X₁ 1 W)) :
    Function.Injective (S.f.hom.app (op W)) ∧
      Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W)) ∧
      Function.Surjective (S.g.hom.app (op W)) := by
  refine ⟨fun x y hxy => ?_, fun x => ?_, SheafLES.sections_surjective_of_subsingleton hS W h⟩
  · obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{u} S.X₁ W).surjective x
    obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{u} S.X₁ W).surjective y
    rw [← SheafLES.equivZero_map, ← SheafLES.equivZero_map] at hxy
    rw [SheafLES.injective_zero hS W ((SheafLES.equivZero.{u} S.X₂ W).injective hxy)]
  · obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{u} S.X₂ W).surjective x
    rw [← SheafLES.equivZero_map, AddEquiv.map_eq_zero_iff, SheafLES.exact₂ hS 0 W x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (SheafLES.equivZero_map S.f W y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{u} S.X₁ W).surjective y
      exact ⟨y, (SheafLES.equivZero.{u} S.X₂ W).injective
        ((SheafLES.equivZero_map S.f W y).trans hy)⟩

variable [LinearOrder ι]

variable (V U) in
abbrev cechAbSheafFunctor : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⥤
    CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  sheafToPresheaf _ _ ⋙ cechAbFunctor V U

section Delta

variable {S S' : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})}
  (hS : S.ShortExact) (h₁ : CechAcyclic V U S.X₁)

include hS h₁ in
theorem cechAbSheafFunctor_shortExact : (S.map (cechAbSheafFunctor V U)).ShortExact :=
  cechAbFunctor_shortExact V U (S.map (sheafToPresheaf _ _)) fun s hs =>
    sections_shortExact_of_subsingleton hS _ (h₁ s hs 0)

def cechAbδ (n : ℕ) : cechAbH S.X₃.obj V U n →ₗ[ℤ] cechAbH S.X₁.obj V U (n + 1) :=
  ((cechAbSheafFunctor_shortExact hS h₁).δ n (n + 1) rfl).hom

theorem cechAbδ_exact₃ (n : ℕ) :
    Function.Exact (cechAbHMap V U S.g.hom n).hom (cechAbδ hS h₁ n) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((cechAbSheafFunctor_shortExact hS h₁).homology_exact₃ n (n + 1) rfl)

theorem cechAbδ_exact₁ (n : ℕ) :
    Function.Exact (cechAbδ hS h₁ n) (cechAbHMap V U S.f.hom (n + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    ((cechAbSheafFunctor_shortExact hS h₁).homology_exact₁ n (n + 1) rfl)

theorem cechAbδ_naturality (hS' : S'.ShortExact) (h₁' : CechAcyclic V U S'.X₁) (φ : S ⟶ S')
    (n : ℕ) (x : cechAbH S.X₃.obj V U n) :
    (cechAbHMap V U φ.τ₁.hom (n + 1)).hom (cechAbδ hS h₁ n x) =
      cechAbδ hS' h₁' n ((cechAbHMap V U φ.τ₃.hom n).hom x) :=
  congr(($(HomologicalComplex.HomologySequence.δ_naturality
    ((cechAbSheafFunctor V U).mapShortComplex.map φ) (cechAbSheafFunctor_shortExact hS h₁)
    (cechAbSheafFunctor_shortExact hS' h₁') n (n + 1) rfl)).hom x)

theorem cechAbδ_surjective [Finite ι] [Injective S.X₂] (n : ℕ) :
    Function.Surjective (cechAbδ hS h₁ n) := fun x =>
  haveI := Flasque.isFlasque_of_injective (X := T) S.X₂ (hI := ‹_›)
  (cechAbδ_exact₁ hS h₁ n x).1
    (@Subsingleton.elim _ (subsingleton_cechAbH_succ_of_isFlasque (T := T) S.X₂ V U n) _ _)

end Delta

variable (V U) in
def CechComparison (n : ℕ) : Type (u + 1) :=
  {e : ∀ F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}, CechAcyclic V U F →
      (cechAbH F.obj V U n ≃+ Sheaf.H'.{u} F n V) //
    ∀ (F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (hF : CechAcyclic V U F)
      (hG : CechAcyclic V U G) (φ : F ⟶ G) (x : cechAbH F.obj V U n),
      e G hG ((cechAbHMap V U φ.hom n).hom x) = SheafLES.map φ n V (e F hF x)}

def CechComparison.zero (hc : V ≤ ⨆ i, U i) : CechComparison V U 0 :=
  ⟨fun F _ => (cechAbHZeroEquiv F.property hc).toAddEquiv.trans (SheafLES.equivZero F V).symm,
    fun F G _ _ φ x => by
      refine Eq.trans ?_ (SheafLES.map_equivZero_symm φ V _).symm
      exact congrArg (SheafLES.equivZero G V).symm
        (cechAbHZeroEquiv_map F.property G.property hc φ.hom x)⟩

theorem CechComparison.exists_succ [Finite ι] {n : ℕ} (e : CechComparison V U n) :
    ∃ e' : CechComparison V U (n + 1),
      ∀ (S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}))
        (hS : S.ShortExact) (h₁ : CechAcyclic V U S.X₁) (h₃ : CechAcyclic V U S.X₃) x,
        e'.1 S.X₁ h₁ (cechAbδ hS h₁ n x) = SheafLES.δ hS n V (e.1 S.X₃ h₃ x) := by
  obtain ⟨e, he⟩ := e
  let I (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :=
    Flasque.injectiveShortComplex F
  have hI F : (I F).ShortExact := Flasque.injectiveShortComplex_shortExact F
  have inj F : Injective (I F).X₂ := inferInstanceAs (Injective (Injective.under F))
  have a₂ F : CechAcyclic V U (I F).X₂ := cechAcyclic_of_injective _
  have a₃ F (hF : CechAcyclic V U F) : CechAcyclic V U (I F).X₃ :=
    CechAcyclic.of_shortExact₃ (hI F) hF (a₂ F)
  have ex F (hF : CechAcyclic V U F) : ∃ e' : cechAbH F.obj V U (n + 1) ≃+ Sheaf.H'.{u} F (n + 1) V,
      ∀ x, e' (cechAbδ (hI F) hF n x) = SheafLES.δ (hI F) n V (e _ (a₃ F hF) x) := by
    refine exists_addEquiv_of_surjective_of_ker (cechAbδ (hI F) hF n).toAddMonoidHom
      ((SheafLES.δ (hI F) n V).comp (e _ (a₃ F hF)).toAddMonoidHom)
      (cechAbδ_surjective (hI F) hF n)
      ((SheafLES.δ_surjective_of_subsingleton (hI F) n V
        (Flasque.subsingleton_H'_of_injective _ n V)).comp (e _ (a₃ F hF)).surjective)
      fun x => ((cechAbδ_exact₃ (hI F) hF n x).trans ?_).trans
        (SheafLES.exact₃ (hI F) n V (e _ (a₃ F hF) x)).symm
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (he _ _ (a₂ F) _ _ y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (e _ (a₂ F)).surjective y
      exact ⟨y, (e _ (a₃ F hF)).injective ((he _ _ (a₂ F) _ _ y).trans hy)⟩
  choose e' he' using ex
  have key (S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}))
      (hS : S.ShortExact) (h₁ : CechAcyclic V U S.X₁) (h₃ : CechAcyclic V U S.X₃) G hG
      (f : S.X₁ ⟶ G) (x : cechAbH S.X₃.obj V U n) :
      e' G hG ((cechAbHMap V U f.hom (n + 1)).hom (cechAbδ hS h₁ n x)) =
        SheafLES.map f (n + 1) V (SheafLES.δ hS n V (e S.X₃ h₃ x)) := by
    obtain ⟨φ, hφ⟩ := Flasque.exists_hom_τ₁_eq (T := I G) hS f
    have e₁ := cechAbδ_naturality hS h₁ (hI G) hG φ n x
    have e₂ := SheafLES.δ_naturality hS (hI G) φ n V (e S.X₃ h₃ x)
    rw [hφ] at e₁ e₂
    refine (congrArg (e' G hG) e₁).trans ((he' G hG _).trans (Eq.trans ?_ e₂.symm))
    exact congrArg _ (he _ _ h₃ _ φ.τ₃ x)
  refine ⟨⟨e', fun F G hF hG φ x => ?_⟩, fun S hS h₁ h₃ x => ?_⟩
  · obtain ⟨x, rfl⟩ := cechAbδ_surjective (hI F) hF n x
    exact (key (I F) (hI F) hF (a₃ F hF) G hG φ x).trans (congrArg _ (he' F hF x).symm)
  · have := key S hS h₁ h₃ S.X₁ h₁ (𝟙 _) x
    rw [SheafLES.map_id] at this
    refine Eq.trans (congrArg _ ?_) this
    exact (congr(($(cechAbHMap_id S.X₁.obj V U (n + 1))).hom (cechAbδ hS h₁ n x))).symm

variable [Finite ι] (hc : V ≤ ⨆ i, U i)

def cechComparisonOfCover (n : ℕ) : CechComparison V U n :=
  Nat.rec (motive := fun n => CechComparison V U n) (CechComparison.zero hc)
    (fun _ e => e.exists_succ.choose) n

variable {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}}

def cechAbHEquivH' (hF : CechAcyclic V U F) (n : ℕ) :
    cechAbH F.obj V U n ≃+ Sheaf.H'.{u} F n V :=
  (cechComparisonOfCover hc n).1 F hF

theorem cechAbHEquivH'_toCechAbH (hF : CechAcyclic V U F) (x : F.obj.obj (op V)) :
    cechAbHEquivH' hc hF 0 (toCechAbH F.obj V U x) = (SheafLES.equivZero F V).symm x :=
  congrArg (SheafLES.equivZero F V).symm
    ((cechAbHZeroEquiv F.property hc).apply_symm_apply x)

theorem cechAbHEquivH'_map (hF : CechAcyclic V U F) (hG : CechAcyclic V U G) (φ : F ⟶ G) (n : ℕ)
    (x : cechAbH F.obj V U n) :
    cechAbHEquivH' hc hG n ((cechAbHMap V U φ.hom n).hom x) =
      SheafLES.map φ n V (cechAbHEquivH' hc hF n x) :=
  (cechComparisonOfCover hc n).2 F G hF hG φ x

theorem cechAbHEquivH'_δ
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (h₁ : CechAcyclic V U S.X₁) (h₃ : CechAcyclic V U S.X₃) (n : ℕ) (x : cechAbH S.X₃.obj V U n) :
    cechAbHEquivH' hc h₁ (n + 1) (cechAbδ hS h₁ n x) =
      SheafLES.δ hS n V (cechAbHEquivH' hc h₃ n x) :=
  (cechComparisonOfCover hc n).exists_succ.choose_spec S hS h₁ h₃ x

end Ab

section Modules

variable {X : Scheme.{u}} {ι : Type}

def CechAcyclicMod (V : X.Opens) (U : ι → X.Opens) (F : X.Modules) : Prop :=
  ∀ s : Finset ι, s.Nonempty → ∀ q, Subsingleton (cohOn F (cechOpen V U s) (q + 1))

variable {V : X.Opens} {U : ι → X.Opens} {F G : X.Modules}

theorem cechAcyclicMod_iff : CechAcyclicMod V U F ↔
    CechAcyclic (T := X.toPresheafedSpace.carrier) V U ((toAbSheaf (X := X)).obj F) := Iff.rfl

theorem cechAcyclicMod_iff_of_le (h : ∀ i, U i ≤ V) : CechAcyclicMod V U F ↔
    ∀ s : Finset ι, s.Nonempty → ∀ q, 0 < q → Subsingleton (cohOn F (⨅ i ∈ s, U i) q) := by
  refine forall₂_congr fun s hs => ?_
  rw [cechOpen_of_nonempty h hs]
  exact ⟨fun H q hq => by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq.ne'
    exact H q, fun H q => H _ q.succ_pos⟩

variable [LinearOrder ι] (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

section Delta

variable {S S' : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : CechAcyclicMod V U S.X₁)

include hS h₁ in
theorem cechModulesFunctor_shortExact_of_acyclic :
    (S.map (cechModulesFunctor R V U)).ShortExact :=
  cechModulesFunctor_shortExact R V U S fun s hs =>
    sections_shortExact_of_subsingleton (T := X.toPresheafedSpace.carrier)
      (shortExact_toAbSheaf hS) _ (h₁ s hs 0)

def cechδ (n : ℕ) : cechH R S.X₃ V U n →ₗ[R] cechH R S.X₁ V U (n + 1) :=
  ((cechModulesFunctor_shortExact_of_acyclic R hS h₁).δ n (n + 1) rfl).hom

theorem cechAbHEquiv_δ (n : ℕ) (x : cechAbH S.X₃.presheaf V U n) :
    cechAbHEquiv R S.X₁ V U (n + 1) (cechAbδ (T := X.toPresheafedSpace.carrier)
        (shortExact_toAbSheaf hS) (cechAcyclicMod_iff.1 h₁) n x) =
      cechδ R hS h₁ n (cechAbHEquiv R S.X₃ V U n x) :=
  Cube.SemiHom.homology_δ
    (S := (S.map (toAbSheaf (X := X))).map (sheafToPresheaf _ _ ⋙ cechAbCubeFunctor V U))
    (S' := S.map (cechCubeFunctor R V U))
    (cechAbSheafFunctor_shortExact (T := X.toPresheafedSpace.carrier)
      (shortExact_toAbSheaf hS) (cechAcyclicMod_iff.1 h₁))
    (cechModulesFunctor_shortExact_of_acyclic R hS h₁)
    (cechAbCubeToCube R S.X₁ V U) (cechAbCubeToCube R S.X₂ V U) (cechAbCubeToCube R S.X₃ V U)
    (fun _ _ => rfl) (fun _ _ => rfl) n x

end Delta

variable [Finite ι] (hc : V ≤ ⨆ i, U i)

def cechHAddEquivCohOn (hF : CechAcyclicMod V U F) (n : ℕ) : cechH R F V U n ≃+ cohOn F V n :=
  ((cechAbHEquiv R F V U n).symm.trans
    (cechAbHEquivH' (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF) n)).trans
    (cohOn.toH' F V n).symm

theorem toH'_cechHAddEquivCohOn (hF : CechAcyclicMod V U F) (n : ℕ)
    (x : cechAbH F.presheaf V U n) :
    cohOn.toH' F V n (cechHAddEquivCohOn R hc hF n (cechAbHEquiv R F V U n x)) =
      cechAbHEquivH' (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF) n x :=
  congrArg (cechAbHEquivH' (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF) n)
    ((cechAbHEquiv R F V U n).symm_apply_apply x)

theorem cechHAddEquivCohOn_map (hF : CechAcyclicMod V U F) (hG : CechAcyclicMod V U G)
    (φ : F ⟶ G) (n : ℕ) (x : cechH R F V U n) :
    cechHAddEquivCohOn R hc hG n ((cechHMap R V U φ n).hom x) =
      cohOn.map R φ V n (cechHAddEquivCohOn R hc hF n x) := by
  obtain ⟨y, rfl⟩ := (cechAbHEquiv R F V U n).surjective x
  apply (cohOn.toH' G V n).injective
  rw [← cechAbHEquiv_map, toH'_cechHAddEquivCohOn, cohOn.toH'_map, toH'_cechHAddEquivCohOn]
  exact cechAbHEquivH'_map (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF)
    (cechAcyclicMod_iff.1 hG) ((toAbSheaf (X := X)).map φ) n y

def cechHEquivCohOn (hF : CechAcyclicMod V U F) (n : ℕ) : cechH R F V U n ≃ₗ[R] cohOn F V n :=
  { cechHAddEquivCohOn R hc hF n with
    map_smul' := fun r x =>
      (congrArg (cechHAddEquivCohOn R hc hF n) (cechHMap_smulHom_apply R F V U r n x).symm).trans
        (cechHAddEquivCohOn_map R hc hF hF _ n x) }

theorem toH'_cechHEquivCohOn (hF : CechAcyclicMod V U F) (n : ℕ) (x : cechAbH F.presheaf V U n) :
    cohOn.toH' F V n (cechHEquivCohOn R hc hF n (cechAbHEquiv R F V U n x)) =
      cechAbHEquivH' (T := X.toPresheafedSpace.carrier) hc (cechAcyclicMod_iff.1 hF) n x :=
  toH'_cechHAddEquivCohOn R hc hF n x

theorem cechHEquivCohOn_map (hF : CechAcyclicMod V U F) (hG : CechAcyclicMod V U G)
    (φ : F ⟶ G) (n : ℕ) (x : cechH R F V U n) :
    cechHEquivCohOn R hc hG n ((cechHMap R V U φ n).hom x) =
      cohOn.map R φ V n (cechHEquivCohOn R hc hF n x) :=
  cechHAddEquivCohOn_map R hc hF hG φ n x

theorem cechHEquivCohOn_δ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : CechAcyclicMod V U S.X₁) (h₃ : CechAcyclicMod V U S.X₃) (n : ℕ)
    (x : cechH R S.X₃ V U n) :
    cechHEquivCohOn R hc h₁ (n + 1) (cechδ R hS h₁ n x) =
      cohOn.δ R hS V n (cechHEquivCohOn R hc h₃ n x) := by
  obtain ⟨y, rfl⟩ := (cechAbHEquiv R S.X₃ V U n).surjective x
  apply (cohOn.toH' S.X₁ V (n + 1)).injective
  rw [← cechAbHEquiv_δ, cohOn.toH'_δ, toH'_cechHEquivCohOn]
  exact (toH'_cechHEquivCohOn R hc h₁ (n + 1) _).trans
    (cechAbHEquivH'_δ (T := X.toPresheafedSpace.carrier) hc (shortExact_toAbSheaf hS)
      (cechAcyclicMod_iff.1 h₁) (cechAcyclicMod_iff.1 h₃) n y)

theorem cechHEquivCohOn_zero (hF : CechAcyclicMod V U F) :
    cechHEquivCohOn R hc hF 0 = cechHZeroEquivCohOn R F hc := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (toCechH_bijective R F hc).2 x
  apply (cohOn.toH' F V 0).injective
  refine (congrArg (fun z => cohOn.toH' F V 0 (cechHEquivCohOn R hc hF 0 z))
    (cechAbHEquiv_toCechAbH R F V U y).symm).trans ((toH'_cechHEquivCohOn R hc hF 0 _).trans
      ((cechAbHEquivH'_toCechAbH (T := X.toPresheafedSpace.carrier) hc
        (cechAcyclicMod_iff.1 hF) _).trans ?_))
  rw [cechHZeroEquivCohOn, LinearEquiv.trans_apply, cechHZeroEquiv_toCechH]
  rfl

omit [LinearOrder ι] [Finite ι] in
include hc in
theorem subsingleton_cohOn_of_cechAcyclic [Fintype ι] (hF : CechAcyclicMod V U F) {n : ℕ}
    (hn : Fintype.card ι ≤ n) : Subsingleton (cohOn F V n) :=
  letI : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
  haveI := subsingleton_cechH ℤ F V U hn
  (cechHEquivCohOn ℤ hc hF n).symm.injective.subsingleton

end Modules

end GlobalTheory
