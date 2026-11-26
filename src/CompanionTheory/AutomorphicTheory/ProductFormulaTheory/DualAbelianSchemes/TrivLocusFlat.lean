module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechFlatComplex
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpecMapAppFromSpec
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RigDescent
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeQuotientSchemeHolds
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientByFiniteFlatOfFreeQuotient
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KTrivModelOfTrivLocus
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AppTopCompApply
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOutsideFiniteSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FewEquationsStatement
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.AbelianDeRham.FreeAbelianDeRham.H1StructureDimLe

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FewEquationsStatementStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FewEquationsStatement : FewEqSt := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.fewEq | exact GlobalTheory.CompanionTheory.FewEq.fewEq | (intros; apply GlobalTheory.CompanionTheory.FewEq.fewEq <;> assumption)
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PreDualOfIsPerfect
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.DualScheme

theorem preDual_of_isPerfect {S : Scheme.{0}} [IsLocallyNoetherian S] {A B : Over S} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (h : IsPerfect A B P) :
    PreDual A B P := by
  refine ⟨h.isLB, ?_, ?_, h.ker_right, ?_⟩
  · exact CubeNoeth.isAdditive_of_triv_axes hA hB h.isLB h.zero_left h.zero_right
  · exact CubeNoeth.isAdditive_swap_of_triv_axes hA hB h.isLB h.zero_left h.zero_right
  · intro k _ _ t
    exact (Set.finite_singleton (1 : Over.mk t ⟶ A)).subset fun x hx ↦ h.ker_left _ x hx

theorem pull_lam_of_left {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (c : Pic G.left) (u : T'.left ⟶ T.left)
    {a b : T ⟶ G} {a' b' : T' ⟶ G} (ha : u ≫ a.left = a'.left) (hb : u ≫ b.left = b'.left) :
    CechPic.pull u (lam c a b) = lam c a' b' := by
  have hT : u ≫ T.hom = T'.hom := by
    rw [← Over.w a, ← Category.assoc, ha, Over.w a']
  have hab : u ≫ (a * b).left = (a' * b').left := by
    rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, GlobalTheory.AbDual.lift_left_fst, GlobalTheory.AbDual.lift_left_fst, ha]
    · rw [Category.assoc, GlobalTheory.AbDual.lift_left_snd, GlobalTheory.AbDual.lift_left_snd, hb]
  have hu : ∀ X : Over S, (toUnit X).left = X.hom := fun X => by
    simpa using Over.w (toUnit X)
  have h1 : u ≫ (1 : T ⟶ G).left = (1 : T' ⟶ G).left := by
    rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, ← Category.assoc, hu, hu, hT]
  simp only [GlobalTheory.CechPic.lam, map_add (f := _), map_sub, ← GlobalTheory.CechPic.pull_comp, hab, h1, ha, hb]

theorem pull_lam_sq {S S' : Scheme.{0}} {b : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G b φ) (c : Pic G.left) {l : (G' ⊗ G').left ⟶ (G ⊗ G).left}
    (l₁ : l ≫ (fst G G).left = (fst G' G').left ≫ φ) (l₂ : l ≫ (snd G G).left = (snd G' G').left ≫ φ) :
    CechPic.pull l (lam c (fst G G) (snd G G)) = lam (CechPic.pull φ c) (fst G' G') (snd G' G') := by
  rw [GlobalTheory.CechPic.lam_pull_of_isGrpPullback hp c (fst G' G') (snd G' G')]
  exact pull_lam_of_left (T := G ⊗ G) (T' := Over.mk ((G' ⊗ G').hom ≫ b)) (a := fst G G)
    (b := snd G G) (a' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp _ (fst G' G'))
    (b' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp _ (snd G' G')) c l (by rw [l₁]; rfl) (by rw [l₂]; rfl)

theorem ktrivDual : KTrivModel → FinDual → KTrivDual := by
  intro hM hF R _ A _ g hA hg L hL hK
  obtain ⟨R₀, _, σ, A₀, _, φ, L₀, _, hA₀, hg₀, hp, hL₀, hK₀, hiso⟩ := hM R A g hA hg L hL hK
  haveI := hA₀.comm
  have hperf : IsPerfect A₀ A₀ (abelian₂ A₀ L₀) := isPerfect_lam hL₀ hK₀
  have hd : IsDual A₀ A₀ (abelian₂ A₀ L₀) :=
    hF R₀ A₀ A₀ g hA₀ hA₀ hg₀ hg₀ _ (preDual_of_isPerfect hA₀ hA₀ hperf)
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback hp hp
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine IsDual.baseChange hp hp l₁ l₂ hP ?_ hd
  refine (cls_eq_iff (pull_isLB hperf.isLB l) hP).1 ?_
  rw [cls_pull hperf.isLB,
    show cls _ hperf.isLB = lam (cls L₀ hL₀) (fst A₀ A₀) (snd A₀ A₀) from cls_cube_two hL₀ _ _ hperf.isLB,
    show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP,
    (cls_eq_iff hL (pull_isLB hL₀ φ)).2 hiso, cls_pull hL₀]
  exact pull_lam_sq hp _ l₁ l₂

end GlobalTheory.CompanionTheory.DualScheme
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PicardGroupOfFieldTrivial
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PicardGroupOfFieldTrivial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PicField

theorem pic_eq_zero (k : Type) [Field k] (c : Pic (Sp k)) : c = 0 := by
  obtain ⟨p⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨V, hV, hc⟩ := GlobalTheory.AbDual.exists_pull_eq_zero c p
  have hV' : V = ⊤ := by
    have hs : Subsingleton (Sp k) := by
      unfold Sp; infer_instance
    ext x
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact (Subsingleton.elim x p) ▸ hV
  subst hV'
  have : IsIso (⊤ : (Sp k).Opens).ι := (Sp k).topIso.isIso_hom
  have e : c = CechPic.pull (inv (⊤ : (Sp k).Opens).ι) (CechPic.pull (⊤ : (Sp k).Opens).ι c) := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [e, hc, map_zero]

end GlobalTheory.CompanionTheory.PicField
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PicardGroupOfFieldTrivialStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picard_group_of_field_trivial : ∀ (k : Type) [Field k] (c : Pic (Sp k)), c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PicField.pic_eq_zero | exact GlobalTheory.CompanionTheory.PicField.pic_eq_zero | (intros; apply GlobalTheory.CompanionTheory.PicField.pic_eq_zero <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPointOfIsAffine
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.DualAb

section Unique

variable {S : Scheme.{0}} {A B T : Over S} [GrpObj B]

theorem point_ext {P : LB (A ⊗ B).left} (hP : P.IsLB) (a₂ : IsAdditive (swap P)) (r : RightZero A B P)
    {x x' : T ⟶ B} (e : evc hP (fst A T) (snd A T ≫ x) = evc hP (fst A T) (snd A T ≫ x')) : x = x' := by
  have e₁ := (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂ _ (fst A T) (snd A T ≫ (x * x'⁻¹)) (snd A T ≫ x')
  rw [← MonObj.comp_mul, inv_mul_cancel_right, e] at e₁
  exact mul_inv_eq_one.1 (r T _ ((triv_ev_iff hP _ _).2 (right_eq_add.1 e₁)))

end Unique

section Level

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

theorem exists_level [IsNoetherianRing R] (hA : IsAbelianScheme A) {C : Type} [CommRing C] (t : Sp C ⟶ Sp R)
    {M : LB (A ⊗ Over.mk t).left} (hM : M.IsLB) :
    ∃ (D : Type) (_ : CommRing D) (i : D →+* C) (tD : Sp D ⟶ Sp R) (N : LB (A ⊗ Over.mk tD).left)
      (hN : N.IsLB) (w : spMap i ≫ tD = t), IsNoetherianRing D ∧
      cls M hM = evc hN (fst A _) (snd A _ ≫ (Over.homMk (spMap i) w : Over.mk t ⟶ Over.mk tD)) := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ : R →+* C, spMap ψ = t := ⟨(Spec.preimage t).hom, by simp [spMap]⟩
  letI := ψ.toAlgebra
  haveI := hA.proper
  have H : IsPullback (fst A (Over.mk (spMap ψ))).left (snd A (Over.mk (spMap ψ))).left A.hom
      (spMap (algebraMap R C)) := IsPullback.of_hasPullback _ _
  obtain ⟨D, hD, N, hN, h⟩ := GlobalTheory.CompanionTheory.Ar.Approx.lb_descends_fg R C A.left _ A.hom _ _ inferInstance inferInstance H M hM
  have w : spMap D.val.toRingHom ≫ spMap (algebraMap R D) = spMap ψ := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  haveI : Algebra.FiniteType R D := (Subalgebra.fg_iff_finiteType D).1 hD
  refine ⟨D, inferInstance, D.val.toRingHom, spMap (algebraMap R D), N, hN, w,
    Algebra.FiniteType.isNoetherianRing R D, ?_⟩
  refine (cls_eq_iff hM (pull_isLB hN _)).2 (h _ ?_ ?_)
  · exact lift_left_fst _ _
  · exact lift_left_snd _ _ |>.trans rfl

end Level

section Universal

variable {S : Scheme.{0}} {A T₀ Y : Over S} [GrpObj A]

abbrev uniE (N : LB (A ⊗ T₀).left) : LB (A ⊗ (A ⊗ T₀)).left :=
  ev N (fst A (A ⊗ T₀) * (snd A (A ⊗ T₀) ≫ fst A T₀)) (snd A (A ⊗ T₀) ≫ snd A T₀)

abbrev uniF (N : LB (A ⊗ T₀).left) : LB (A ⊗ (A ⊗ T₀)).left :=
  tens (ev N (fst A (A ⊗ T₀)) (snd A (A ⊗ T₀) ≫ snd A T₀))
    (ev N (snd A (A ⊗ T₀) ≫ fst A T₀) (snd A (A ⊗ T₀) ≫ snd A T₀))

theorem lbIso_uni_iff {N : LB (A ⊗ T₀).left} (hN : N.IsLB) (y : Y ⟶ A ⊗ (A ⊗ T₀)) :
    LBIso ((uniE N).pull y.left) ((uniF N).pull y.left) ↔
      evc hN ((y ≫ fst A _) * (y ≫ snd A _ ≫ fst A T₀)) (y ≫ snd A _ ≫ snd A T₀) =
        evc hN (y ≫ fst A _) (y ≫ snd A _ ≫ snd A T₀) +
          evc hN (y ≫ snd A _ ≫ fst A T₀) (y ≫ snd A _ ≫ snd A T₀) := by
  have hE : (uniE N).IsLB := pull_isLB hN _
  have h₁ := pull_isLB hN (lift (fst A (A ⊗ T₀)) (snd A (A ⊗ T₀) ≫ snd A T₀)).left
  have h₂ := pull_isLB hN (lift (snd A (A ⊗ T₀) ≫ fst A T₀) (snd A (A ⊗ T₀) ≫ snd A T₀)).left
  have hF : (uniF N).IsLB := isLB_tens h₁ h₂
  rw [← cls_eq_iff (pull_isLB hE _) (pull_isLB hF _), cls_pull hE, cls_pull hF, cls_tens h₁ h₂, cls_ev hN, cls_ev hN,
    cls_ev hN, map_add, pull_evc, pull_evc, pull_evc, MonObj.comp_mul]

end Universal

section Spread

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

theorem exists_additive_level (hA : IsAbelianScheme A) {C D : Type} [CommRing C] [CommRing D] [IsNoetherianRing D]
    (i : D →+* C) (tD : Sp D ⟶ Sp R) {M : LB (A ⊗ Over.mk (spMap i ≫ tD)).left} (hM : M.IsLB) (hadd : IsAdditive M)
    {N : LB (A ⊗ Over.mk tD).left} (hN : N.IsLB)
    (e : cls M hM = evc hN (fst A _)
      (snd A _ ≫ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ tD) ⟶ Over.mk tD))) :
    ∃ (D₁ : Type) (_ : CommRing D₁) (j : D →+* D₁) (i₁ : D₁ →+* C), IsNoetherianRing D₁ ∧ i₁.comp j = i ∧
      IsAdditive (ev N (fst A (Over.mk (spMap j ≫ tD)))
        (snd A _ ≫ (Over.homMk (spMap j) rfl : Over.mk (spMap j ≫ tD) ⟶ Over.mk tD))) := by
  letI := i.toAlgebra
  haveI := hA.proper
  let T₀ : Over (Sp R) := Over.mk tD
  let u : Over.mk (spMap i ≫ tD) ⟶ T₀ := Over.homMk (spMap i) rfl
  let τ : A ⊗ (A ⊗ T₀) ⟶ T₀ := snd A _ ≫ snd A T₀
  let pB : (A ⊗ (A ⊗ T₀)).left ⟶ Sp D := τ.left
  have q₁ : ∀ T : Over (Sp R), QuasiCompact (snd A T).left := fun T ↦
    inferInstanceAs (QuasiCompact (pullback.snd A.hom T.hom))
  have q₂ : ∀ T : Over (Sp R), QuasiSeparated (snd A T).left := fun T ↦
    inferInstanceAs (QuasiSeparated (pullback.snd A.hom T.hom))
  haveI : QuasiCompact pB := by
    have := q₁ T₀
    have := q₁ (A ⊗ T₀)
    exact inferInstanceAs (QuasiCompact ((snd A (A ⊗ T₀)).left ≫ (snd A T₀).left))
  haveI : QuasiSeparated pB := by
    have := q₂ T₀
    have := q₂ (A ⊗ T₀)
    exact inferInstanceAs (QuasiSeparated ((snd A (A ⊗ T₀)).left ≫ (snd A T₀).left))
  have hE : (uniE N).IsLB := pull_isLB hN _
  have hF : (uniF N).IsLB := isLB_tens (pull_isLB hN _) (pull_isLB hN _)
  let fC := pullback.fst pB (spMap (algebraMap D C))
  let c : Over.mk (fC ≫ (A ⊗ (A ⊗ T₀)).hom) ⟶ A ⊗ (A ⊗ T₀) := Over.homMk fC rfl
  have wτ : pB ≫ tD = (A ⊗ (A ⊗ T₀)).hom := Over.w τ
  let τc : Over.mk (fC ≫ (A ⊗ (A ⊗ T₀)).hom) ⟶ Over.mk (spMap i ≫ tD) :=
    Over.homMk (pullback.snd pB _) (by
      show pullback.snd pB (spMap (algebraMap D C)) ≫ spMap i ≫ tD = fC ≫ (A ⊗ (A ⊗ T₀)).hom
      rw [← wτ, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ tD) (pullback.condition (f := pB) (g := spMap (algebraMap D C))).symm)
  have hc : c ≫ τ = τc ≫ u := Over.OverMorphism.ext (pullback.condition (f := pB) (g := spMap (algebraMap D C)))
  have H := (lbIso_uni_iff hN c).2 (by
    have hc' : c ≫ snd A _ ≫ snd A T₀ = τc ≫ u := hc
    rw [hc', ← GlobalTheory.BirigidLift.evc_of_cls hN hM e, ← GlobalTheory.BirigidLift.evc_of_cls hN hM e,
      ← GlobalTheory.BirigidLift.evc_of_cls hN hM e]
    exact (isAdditive_iff hM).1 hadd _ _ _ _)
  obtain ⟨s, H₁⟩ := GlobalTheory.exists_finset_lbIso_adjoin pB _ _ hE hF H
  let D₁ := Algebra.adjoin D (s : Set C)
  let j : D →+* D₁ := algebraMap D D₁
  haveI : Algebra.FiniteType D D₁ := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)
  refine ⟨D₁, inferInstance, j, D₁.val.toRingHom, Algebra.FiniteType.isNoetherianRing D _,
    RingHom.ext fun x ↦ rfl, ?_⟩
  let f₁ := pullback.fst pB (spMap (algebraMap D D₁))
  let c₁ : Over.mk (f₁ ≫ (A ⊗ (A ⊗ T₀)).hom) ⟶ A ⊗ (A ⊗ T₀) := Over.homMk f₁ rfl
  have K := (lbIso_uni_iff hN c₁).1 H₁
  let v : Over.mk (spMap j ≫ tD) ⟶ T₀ := Over.homMk (spMap j) rfl
  have hN₁ : (ev N (fst A (Over.mk (spMap j ≫ tD))) (snd A _ ≫ v)).IsLB := pull_isLB hN _
  refine (isAdditive_iff hN₁).2 fun Y a a' t ↦ ?_
  rw [GlobalTheory.BirigidLift.evc_of_cls hN hN₁ rfl, GlobalTheory.BirigidLift.evc_of_cls hN hN₁ rfl,
    GlobalTheory.BirigidLift.evc_of_cls hN hN₁ rfl]
  obtain ⟨y, hy⟩ : ∃ y : Y ⟶ A ⊗ (A ⊗ T₀), y = lift a (lift a' (t ≫ v)) := ⟨_, rfl⟩
  have y₁ : y ≫ fst A _ = a := by rw [hy, lift_fst]
  have y₂ : y ≫ snd A _ ≫ fst A T₀ = a' := by rw [hy, lift_snd_assoc, lift_fst]
  have y₃ : y ≫ snd A _ ≫ snd A T₀ = t ≫ v := by rw [hy, lift_snd_assoc, lift_snd]
  have w : y.left ≫ pB = t.left ≫ spMap (algebraMap D D₁) := congrArg (fun q ↦ q.left) y₃
  let g : Y ⟶ Over.mk (f₁ ≫ (A ⊗ (A ⊗ T₀)).hom) := Over.homMk (pullback.lift y.left t.left w) (by
    show pullback.lift y.left t.left w ≫ f₁ ≫ (A ⊗ (A ⊗ T₀)).hom = Y.hom
    rw [pullback.lift_fst_assoc]
    exact Over.w y)
  have hg : g ≫ c₁ = y := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  have K' := congrArg (CechPic.pull g.left) K
  rw [map_add (f := _), pull_evc, pull_evc, pull_evc, MonObj.comp_mul, ← Category.assoc g, ← Category.assoc g,
    ← Category.assoc g, hg, y₁, y₂, y₃] at K'
  exact K'

end Spread

section Affine

variable {R : Type} [CommRing R] [IsNoetherianRing R] {A B : Over (Sp R)} [GrpObj A]

theorem exists_point_spec (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (hP : P.IsLB) (U : UnivNoeth A B P)
    {C : Type} [CommRing C] (t : Sp C ⟶ Sp R) {M : LB (A ⊗ Over.mk t).left} (hM : M.IsLB) (hadd : IsAdditive M) :
    ∃ x : Over.mk t ⟶ B, cls M hM = evc hP (fst A _) (snd A _ ≫ x) := by
  obtain ⟨D, _, i, tD, N, hN, rfl, _, e⟩ := exists_level hA t hM
  obtain ⟨D₁, _, j, i₁, _, rfl, ha⟩ := exists_additive_level hA i tD hM hadd hN e
  have hN₁ := pull_isLB hN (lift (fst A (Over.mk (spMap j ≫ tD)))
    (snd A _ ≫ (Over.homMk (spMap j) rfl : Over.mk (spMap j ≫ tD) ⟶ Over.mk tD))).left
  obtain ⟨x₁, hx₁⟩ := U D₁ (spMap j ≫ tD) _ hN₁ ha
  have hcomp : spMap (i₁.comp j) = spMap i₁ ≫ spMap j := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let v : Over.mk (spMap j ≫ tD) ⟶ Over.mk tD := Over.homMk (spMap j) rfl
  let u₁ : Over.mk (spMap (i₁.comp j) ≫ tD) ⟶ Over.mk (spMap j ≫ tD) := Over.homMk (spMap i₁) (by
    show spMap i₁ ≫ spMap j ≫ tD = spMap (i₁.comp j) ≫ tD
    rw [hcomp, Category.assoc])
  have hv : (Over.homMk (spMap (i₁.comp j)) rfl : Over.mk (spMap (i₁.comp j) ≫ tD) ⟶ Over.mk tD) = u₁ ≫ v :=
    Over.OverMorphism.ext hcomp
  refine ⟨u₁ ≫ x₁, ?_⟩
  rw [e, hv, ← Category.assoc, ← GlobalTheory.BirigidLift.evc_of_cls hN hN₁ rfl,
    GlobalTheory.BirigidLift.evc_of_cls hP hN₁ ((cls_eq_iff hN₁ (pull_isLB hP _)).2 hx₁), Category.assoc]

end Affine

section Pull

variable {S : Scheme.{0}} {A T T' : Over S} [GrpObj A]

theorem cls_eq_evc {M : LB (A ⊗ T).left} (hM : M.IsLB) : cls M hM = evc hM (fst A T) (snd A T) := by
  rw [evc, lift_fst_snd, Over.id_left, pull_id]

theorem isAdditive_ev {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (v : T' ⟶ T) :
    IsAdditive (ev M (fst A T') (snd A T' ≫ v)) := by
  have hN : (ev M (fst A T') (snd A T' ≫ v)).IsLB := pull_isLB hM _
  refine (isAdditive_iff hN).2 fun Y a a' t ↦ ?_
  rw [GlobalTheory.BirigidLift.evc_of_cls hM hN rfl, GlobalTheory.BirigidLift.evc_of_cls hM hN rfl,
    GlobalTheory.BirigidLift.evc_of_cls hM hN rfl]
  exact (isAdditive_iff hM).1 h _ _ _ _

theorem surjective_snd (hA : IsAbelianScheme A) (V : T.left.Opens) :
    Function.Surjective ((snd A T).left ∣_ V).appTop.hom := by
  have hG := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA (isGrpPullback_pullback A T.hom)
  have hV := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG (isGrpPullback_pullback _ V.ι)
  have h1 : Function.Surjective (pullback.snd (pullback.snd A.hom T.hom) V.ι).appTop.hom :=
    (GlobalTheory.globalFns_holds _ _ hV).2
  have e : (snd A T).left ∣_ V =
      (pullbackRestrictIsoRestrict (pullback.snd A.hom T.hom) V).inv ≫ pullback.snd (pullback.snd A.hom T.hom) V.ι := rfl
  have h2 := (ConcreteCategory.bijective_of_isIso
    ((pullbackRestrictIsoRestrict (pullback.snd A.hom T.hom) V).inv.app ⊤)).2.comp h1
  rw [e, Scheme.Hom.comp_appTop]
  exact h2

end Pull

section Global

variable {R : Type} [CommRing R] [IsNoetherianRing R] {A B : Over (Sp R)} [GrpObj A]

theorem exists_point_of_isAffine (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (hP : P.IsLB)
    (U : UnivNoeth A B P) {T : Over (Sp R)} [IsAffine T.left] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (hadd : IsAdditive M) : ∃ x : T ⟶ B, cls M hM = evc hP (fst A T) (snd A T ≫ x) := by
  let e := T.left.isoSpec
  let t : Sp Γ(T.left, ⊤) ⟶ Sp R := e.inv ≫ T.hom
  let i : Over.mk t ⟶ T := Over.homMk e.inv rfl
  let i' : T ⟶ Over.mk t := Over.homMk e.hom (by
    show e.hom ≫ e.inv ≫ T.hom = T.hom
    rw [e.hom_inv_id_assoc])
  have hii : i' ≫ i = 𝟙 T := Over.OverMorphism.ext e.hom_inv_id
  have hN : (ev M (fst A (Over.mk t)) (snd A _ ≫ i)).IsLB := pull_isLB hM _
  obtain ⟨x, hx⟩ := exists_point_spec hA hP U t hN (isAdditive_ev hM hadd i)
  refine ⟨i' ≫ x, ?_⟩
  have k := GlobalTheory.BirigidLift.evc_of_cls hP hN hx (fst A T) (snd A T ≫ i')
  rw [GlobalTheory.BirigidLift.evc_of_cls hM hN rfl, Category.assoc, Category.assoc, hii, Category.comp_id] at k
  rw [cls_eq_evc hM]
  exact k

end Global

section Glue

variable {R : Type} [CommRing R] [IsNoetherianRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem exists_point (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (hP : P.IsLB) (a₁ : IsAdditive P)
    (a₂ : IsAdditive (swap P)) (r : RightZero A B P) (U : UnivNoeth A B P) {T : Over (Sp R)}
    {M : LB (A ⊗ T).left} (hM : M.IsLB) (hadd : IsAdditive M) :
    ∃ x : T ⟶ B, cls M hM = evc hP (fst A T) (snd A T ≫ x) := by
  let 𝒰 := T.left.affineCover
  let Ti : ∀ i, Over (Sp R) := fun i ↦ Over.mk (𝒰.f i ≫ T.hom)
  let j : ∀ i, Ti i ⟶ T := fun i ↦ Over.homMk (𝒰.f i) rfl
  have hN : ∀ i, (ev M (fst A (Ti i)) (snd A _ ≫ j i)).IsLB := fun i ↦ pull_isLB hM _
  have loc : ∀ i, ∃ x : Ti i ⟶ B, cls _ (hN i) = evc hP (fst A _) (snd A _ ≫ x) := fun i ↦ by
    haveI : IsAffine (Ti i).left := inferInstanceAs (IsAffine (𝒰.X i))
    exact exists_point_of_isAffine hA hP U (hN i) (isAdditive_ev hM hadd _)
  choose x hx using loc
  have val : ∀ i {Y : Over (Sp R)} (a : Y ⟶ A) (t : Y ⟶ Ti i), evc hM a (t ≫ j i) = evc hP a (t ≫ x i) :=
    fun i Y a t ↦ (GlobalTheory.BirigidLift.evc_of_cls hM (hN i) rfl a t).symm.trans
      (GlobalTheory.BirigidLift.evc_of_cls hP (hN i) (hx i) a t)
  have ov : ∀ i i', pullback.fst (𝒰.f i) (𝒰.f i') ≫ (x i).left = pullback.snd (𝒰.f i) (𝒰.f i') ≫ (x i').left := by
    intro i i'
    let W : Over (Sp R) := Over.mk (pullback.fst (𝒰.f i) (𝒰.f i') ≫ 𝒰.f i ≫ T.hom)
    let a : W ⟶ Ti i := Over.homMk (pullback.fst _ _) rfl
    let b : W ⟶ Ti i' := Over.homMk (pullback.snd _ _) (by
      show pullback.snd (𝒰.f i) (𝒰.f i') ≫ 𝒰.f i' ≫ T.hom = pullback.fst (𝒰.f i) (𝒰.f i') ≫ 𝒰.f i ≫ T.hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc])
    have hab : a ≫ j i = b ≫ j i' := Over.OverMorphism.ext pullback.condition
    have e := point_ext hP a₂ r (x := a ≫ x i) (x' := b ≫ x i') (by
      rw [← Category.assoc, ← Category.assoc, ← val, ← val, Category.assoc, Category.assoc, hab])
    exact congrArg (fun q ↦ q.left) e
  let x₀ : T.left ⟶ B.left := 𝒰.glueMorphisms (fun i ↦ (x i).left) ov
  have hx₀ : ∀ i, 𝒰.f i ≫ x₀ = (x i).left := fun i ↦ 𝒰.ι_glueMorphisms _ ov i
  let X : T ⟶ B := Over.homMk x₀ (𝒰.hom_ext _ _ fun i ↦ by
    show 𝒰.f i ≫ x₀ ≫ B.hom = 𝒰.f i ≫ T.hom
    rw [reassoc_of% hx₀ i]
    exact Over.w (x i))
  have hX : ∀ i, j i ≫ X = x i := fun i ↦ Over.OverMorphism.ext (hx₀ i)
  refine ⟨X, ?_⟩
  obtain ⟨L, hL, hd⟩ := cls_surj (cls M hM - evc hP (fst A T) (snd A T ≫ X))
  have h0 : Triv L := by
    refine GlobalTheory.CubeGlue.triv_of_locally_triv hL (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left
      ((lift_left_snd _ _).trans (Over.id_left _)) (surjective_snd hA) ?_ ?_
    · refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
      rw [cls_pull hL, hd, map_sub, cls_eq_evc hM, pull_evc, pull_evc, lift_fst,
        lift_snd_assoc, lift_snd, hadd.evc_one hM, a₁.evc_one hP, sub_zero]
    · intro z
      let i := 𝒰.idx z
      let V := (𝒰.f i).opensRange
      refine ⟨V, 𝒰.covers z, ?_⟩
      let W := (snd A T).left ⁻¹ᵁ V
      have hl : Set.range (W.ι ≫ (snd A T).left) ⊆ Set.range (𝒰.f i) := by
        rintro _ ⟨y, rfl⟩
        exact y.2
      let l := IsOpenImmersion.lift (𝒰.f i) (W.ι ≫ (snd A T).left) hl
      have hfac : l ≫ 𝒰.f i = W.ι ≫ (snd A T).left := IsOpenImmersion.lift_fac _ _ _
      let Wo : Over (Sp R) := Over.mk (W.ι ≫ (A ⊗ T).hom)
      let w : Wo ⟶ A ⊗ T := Over.homMk W.ι rfl
      let t₀ : Wo ⟶ Ti i := Over.homMk l (by
        show l ≫ 𝒰.f i ≫ T.hom = W.ι ≫ (A ⊗ T).hom
        rw [← Category.assoc, hfac, Category.assoc]
        exact congrArg (W.ι ≫ ·) (Over.w (snd A T)))
      have ht : t₀ ≫ j i = w ≫ snd A T := Over.OverMorphism.ext hfac
      refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
      rw [cls_pull hL, hd]
      show CechPic.pull w.left _ = 0
      rw [map_sub, cls_eq_evc hM, pull_evc, pull_evc, ← Category.assoc w, ← ht, Category.assoc, hX, val, sub_self]
  rw [← sub_eq_zero, ← hd]
  exact (cls_eq_zero_iff hL).2 h0

end Glue

theorem finDual_of_univNoeth : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, PreDual A B P → UnivNoeth A B P) → FinDual := by
  intro H R _ _ A B _ _ g hA hB gA gB P hD
  have U := H R A B g hA hB gA gB P hD
  refine ⟨hD.isLB, hD.add₁, GlobalTheory.BirigidLift.triv_right hD.isLB hD.add₂, fun T M hM ha ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_point hA hD.isLB hD.add₁ hD.add₂ hD.right U hM ha
  refine ⟨x, (cls_eq_iff hM (pull_isLB hD.isLB _)).1 hx, fun y hy ↦ ?_⟩
  exact point_ext hD.isLB hD.add₂ hD.right (((cls_eq_iff hM (pull_isLB hD.isLB _)).2 hy).symm.trans hx)

end GlobalTheory.CompanionTheory.DualAb
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechComplexTrivialLineBundleNotAcyclic
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechComplexTrivialLineBundleNotAcyclic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity

theorem not_acyclic_cechLB_of_triv {R : Type} [CommRing R] {X : Scheme.{0}} [Nonempty X]
    (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X)
    (hN : N.IsLB) (hT : Triv N) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens)
    (hc : ⨆ i, D i = ⊤) : ¬ (cechLB f N D).Acyclic := by
  intro hac
  obtain ⟨t, ht⟩ := hT
  let σ : LB.Sec N := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  have h0 := hac 0
  rw [cochainComplex_exactAt_zero_iff, cechLB_d _ _ _ 0] at h0
  let x : (secCube f N D).obj ∅ := SecOnR.of f N _ (GlobalTheory.LB.ofSec σ _)
  have hx : Cube.aug (secCube f N D) x = 0 := h0 ((Cube.d_aug _ _).trans (map_zero _).symm)
  obtain ⟨p⟩ := ‹Nonempty X›
  obtain ⟨i, hi⟩ : ∃ i, p ∈ D i := by
    have hp : p ∈ ⨆ i, D i := by rw [hc]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hp
  obtain ⟨c, hcp⟩ : ∃ c, p ∈ N.U c := by
    have hp : p ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hp
  have e := congrFun hx ⟨{i}, Finset.card_singleton i⟩
  have e₂ := congrArg (fun y : SecOnR f N (⨅ j ∈ ({i} : Finset κ), D j) => SecOnR.coord y c) e
  have hpW : p ∈ (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c := by
    refine ⟨?_, hcp⟩
    simpa using hi
  have hu : IsUnit (rs X (inf_le_right : (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c ≤ N.U c)
      (t.s c).val) := (t.s c).isUnit.map (rs X inf_le_right)
  have e₃ : rs X (inf_le_right : (⨅ j ∈ ({i} : Finset κ), D j) ⊓ N.U c ≤ N.U c) (t.s c).val = 0 := by
    let y : SecOnR f N (⨅ j ∈ (∅ : Finset κ), D j) := x
    have e₄ : rs X (inf_le_inf_right _ (iInf_le_iInf_of_subset D (Finset.empty_subset {i})))
        (SecOnR.coord y c) = 0 := e₂
    have e₅ : SecOnR.coord y c = rs X inf_le_right (t.s c).val := GlobalTheory.LB.coord_ofSec _ _ _
    rw [e₅, rs_rs] at e₄
    exact e₄
  rw [e₃] at hu
  have hu' := hu.map (X.presheaf.germ _ p hpW).hom
  rw [map_zero] at hu'
  exact not_isUnit_zero hu'

end GlobalTheory.CompanionTheory.PointSurjectivity
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechComplexTrivialLineBundleNotAcyclicStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_complex_trivial_line_bundle_not_acyclic : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} [Nonempty X] (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X)
    (hN : N.IsLB) (hT : Triv N) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hc : ⨆ i, D i = ⊤), ¬ (cechLB f N D).Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv | exact GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv <;> assumption)
end
end

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.FewEqBridge
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
open GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

theorem fewEquations_of_fewEqSt (hF : FewEqSt) (hLe : H1StructureDimLe) : FewEquations := by
  intro R _ _ _ A _ g hab hsm M hM I hI hJ
  refine hF R A.left A.hom g hab.smooth hab.proper ?_ M hM I hI hJ
  intro X' s' φ hP
  obtain ⟨_, hab', hsm'⟩ := GlobalTheory.CompanionTheory.Hodge.FormBC.exists_grp A g hab hsm s' φ hP
  exact hLe _ (Over.mk s') g hab' hsm'

theorem fewEquations_pf : H1StructureDimLe → FewEquations := fun hLe => fewEquations_of_fewEqSt GlobalTheory.T.FewEquationsStatement hLe

end CompanionTheory.PfDual
end
end

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.PointSurj
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
open GlobalTheory.CompanionTheory.PointSurjectivity
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

section Lemmas

variable {k : Type} [Field k] {A T : Over (Sp k)} {M : LB (A ⊗ T).left}

theorem pull_evc_const (hM : M.IsLB) (t₀ : 𝟙_ (Over (Sp k)) ⟶ T) {Y : Over (Sp k)} (a : Y ⟶ A) :
    GlobalTheory.CechPic.pull a.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) = evc hM a (toUnit Y ≫ t₀) := by
  rw [pull_evc, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem pull_mul_evc_const [GrpObj A] (hM : M.IsLB) (hadd : IsAdditive M) (t₀ : 𝟙_ (Over (Sp k)) ⟶ T)
    {Y : Over (Sp k)} (a a' : Y ⟶ A) :
    GlobalTheory.CechPic.pull (a * a').left (evc hM (𝟙 A) (toUnit A ≫ t₀)) =
      GlobalTheory.CechPic.pull a.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) +
        GlobalTheory.CechPic.pull a'.left (evc hM (𝟙 A) (toUnit A ≫ t₀)) := by
  rw [pull_evc_const, pull_evc_const, pull_evc_const]
  exact (isAdditive_iff hM).1 hadd Y a a' _

end Lemmas


set_option maxHeartbeats 2000000 in
theorem pointSurj_pf : (∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, ∀ hM : M.IsLB, (∀ (Y : Over (Sp k)) (a a' : Y ⟶ A), GlobalTheory.CechPic.pull (a * a').left (cls M hM) = GlobalTheory.CechPic.pull a.left (cls M hM) + GlobalTheory.CechPic.pull a'.left (cls M hM)) → ¬ Triv M → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB A.hom M D).Acyclic) → PointSurj := by
  intro hAA k _ _ A B _ _ hA hB P hP hadd hadd' hfin M hM haddM
  by_contra hno
  push Not at hno
  have : IsCommMonObj A := hA.comm
  have : IsCommMonObj B := hB.comm
  have hpA : IsProjBy A.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k A hA
  have hpB : IsProjBy B.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have hpq : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback _ _
  have hsw : (swap P).IsLB := pull_isLB hP _
  obtain ⟨G, hG, eG⟩ := cls_surj
    (GlobalTheory.CechPic.pull (lift (fst A B) (toUnit (A ⊗ B))).left (cls M hM) - cls P hP)
  have cst : ∀ {X : Over (Sp k)} (x : 𝟙_ (Over (Sp k)) ⟶ X) (Y : Over (Sp k)),
      (toUnit Y ≫ x).left = Y.hom ≫ x.left := fun x Y =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit Y)))

  have sl₁ : ∀ y' : 𝟙_ (Over (Sp k)) ⟶ B, cls _ (pull_isLB hG (lift (𝟙 A) (toUnit A ≫ y')).left) =
      evc hM (𝟙 A) (toUnit A ≫ 𝟙 _) - evc hP (𝟙 A) (toUnit A ≫ y') := fun y' => by
    rw [cls_pull hG, eG, map_sub, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, comp_toUnit,
      Category.comp_id]
    rfl

  have sl₂ : ∀ x' : 𝟙_ (Over (Sp k)) ⟶ A, cls _ (pull_isLB hG (lift (toUnit B ≫ x') (𝟙 B)).left) =
      - evc hsw (𝟙 B) (toUnit B ≫ x') := fun x' => by
    rw [cls_pull hG, eG, map_sub, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, comp_toUnit]
    have e₁ : GlobalTheory.CechPic.pull (lift (toUnit B ≫ x') (toUnit B)).left (cls M hM) = 0 := by
      have e := pull_evc hM (toUnit B) x' (𝟙 _)
      rw [Category.comp_id, GlobalTheory.T.picard_group_of_field_trivial k (evc hM x' (𝟙 _)), map_zero] at e
      exact e.symm
    rw [e₁, zero_sub, evc_swap hP hsw]
    rfl
  have fibB : ∀ (y : Sp k ⟶ B.left) (σ : A.left ⟶ (A ⊗ B).left), y ≫ B.hom = 𝟙 _ →
      σ ≫ (fst A B).left = 𝟙 _ → σ ≫ (snd A B).left = A.hom ≫ y → FibAc A.hom (G.pull σ) := by
    intro y σ hy h₁ h₂
    let y' : 𝟙_ (Over (Sp k)) ⟶ B := Over.homMk y hy
    have hσ : σ = (lift (𝟙 A) (toUnit A ≫ y')).left := by
      refine hpq.hom_ext ?_ ?_
      · rw [h₁, ← Over.comp_left, lift_fst]
        rfl
      · rw [h₂, ← Over.comp_left, lift_snd, cst]
        rfl
    subst hσ
    intro κ _ _ D hD hc
    refine hAA k A hA _ (pull_isLB hG _) (fun Y a a' => ?_) (fun ht => ?_) κ D hD hc
    · rw [sl₁ y', map_sub, map_sub, map_sub, pull_mul_evc_const hM haddM, pull_mul_evc_const hP hadd]
      abel
    · have h0 := (cls_eq_zero_iff (pull_isLB hG _)).2 ht
      rw [sl₁ y', sub_eq_zero] at h0
      refine hno y' ((cls_eq_iff hM (pull_isLB hP _)).1 ?_)
      have e := congrArg (GlobalTheory.CechPic.pull (fst A (𝟙_ (Over (Sp k)))).left) h0
      rw [pull_evc, pull_evc, Category.comp_id, Category.comp_id,
        ← Category.assoc (fst A _) (toUnit A) y',
        toUnit_unique (fst A (𝟙_ (Over (Sp k))) ≫ toUnit A) (snd A _)] at e
      refine Eq.trans ?_ (e.trans (cls_ev hP _ _ _).symm)
      rw [evc, lift_fst_snd, Over.id_left, pull_id]
  have htot : FibAc ((fst A B).left ≫ A.hom) G :=
    GlobalTheory.T.fibre_acyclicity_of_sections A.hom B.hom (fst A B).left (snd A B).left hpq hpA G hG fibB
  let F' : Set (Sp k ⟶ A.left) :=
    (fun x : 𝟙_ (Over (Sp k)) ⟶ A => x.left) '' {x | Triv (ev P (toUnit B ≫ x) (𝟙 B))}
  have fibA : ∀ (y : Sp k ⟶ A.left) (σ : B.left ⟶ (A ⊗ B).left), y ≫ A.hom = 𝟙 _ →
      σ ≫ (snd A B).left = 𝟙 _ → σ ≫ (fst A B).left = B.hom ≫ y → y ∉ F' → FibAc B.hom (G.pull σ) := by
    intro y σ hy h₁ h₂ hyF
    let x' : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk y hy
    have hσ : σ = (lift (toUnit B ≫ x') (𝟙 B)).left := by
      refine hpq.hom_ext ?_ ?_
      · rw [h₂, ← Over.comp_left, lift_fst, cst]
        rfl
      · rw [h₁, ← Over.comp_left, lift_snd]
        rfl
    subst hσ
    intro κ _ _ D hD hc
    refine hAA k B hB _ (pull_isLB hG _) (fun Y a a' => ?_) (fun ht => ?_) κ D hD hc
    · rw [sl₂ x', map_neg, map_neg, map_neg, pull_mul_evc_const hsw hadd']
      abel
    · have h0 := (cls_eq_zero_iff (pull_isLB hG _)).2 ht
      rw [sl₂ x', neg_eq_zero, evc_swap hP hsw] at h0
      exact hyF ⟨x', (triv_ev_iff hP _ _).2 h0, rfl⟩
  have htot' : FibAc ((snd A B).left ≫ B.hom) G := hpq.w ▸ htot
  have hη : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
  obtain ⟨m, D, hD, hc, hac⟩ := GlobalTheory.T.exists_affine_cover_cech_acyclic_of_fibAc_off_finite B.hom A.hom (snd A B).left (fst A B).left hpq.flip hpB G hG F'
    (hfin.image _) fibA htot' η[A].left (lift (toUnit B ≫ η[A]) (𝟙 B)).left hη
    (by rw [← Over.comp_left, lift_snd]; rfl) (by rw [← Over.comp_left, lift_fst, cst])
  have : Nonempty B.left := ⟨η[B].left (IsLocalRing.closedPoint k)⟩
  refine GlobalTheory.T.cech_complex_trivial_line_bundle_not_acyclic B.hom _ (pull_isLB hG _) ?_ (Fin m) D hc hac
  refine (cls_eq_zero_iff (pull_isLB hG _)).1 ?_
  rw [sl₂, evc_swap hP hsw, ← Hom.one_def, IsAdditive.evc_one hP hadd, neg_zero]

end CompanionTheory.PfDual
end

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocus
section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusB
section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusA
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace CompanionTheory.PfDual


open GlobalTheory.TrivRep in
theorem exists_ideal_locTriv_noeth : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → ∀ F : LB B.left, F.IsLB → ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) → ((∀ p : Spec (CommRingCat.of R'), ∃ U : (Spec (CommRingCat.of R')).Opens, p ∈ U ∧ Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔ I ≤ RingHom.ker g) := by
  intro R _ _ B _ hB F hF
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  haveI := hB.proper
  haveI := hB.geomConnected
  haveI : Smooth B.hom := hB.smooth
  have hP : Nonempty (Perf B.hom F) := GlobalTheory.ProperFinite.nonempty_perf_of_isProper B.hom hF
  have hFInv : (pw F (-1)).IsLB := by
    refine ⟨hF.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ (-1 : ℤ)) (hF.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ (-1 : ℤ)) (hF.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have hQ : Nonempty (Perf B.hom (pw F (-1))) :=
    GlobalTheory.ProperFinite.nonempty_perf_of_isProper B.hom hFInv
  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper
    (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)
  obtain ⟨I, hI⟩ := GlobalTheory.TrivRep.exists_ideal
    (GlobalTheory.TrivRep.TrivOn B.hom F) (GlobalTheory.TrivRep.TrivOn.comp B.hom F) (fun p => by
    by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
        IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}
    · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩ := hp
      obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀
        h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht
      exact ⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩
    · obtain ⟨_, ⟨r, rfl⟩, hr, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_compl hp) hC.isOpen_compl
      refine ⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩
      · rcases subsingleton_or_nontrivial S with _ | _
        · exact fun a _ => Subsingleton.elim _ _
        obtain ⟨m, hm⟩ := Ideal.exists_maximal S
        letI := Ideal.Quotient.field m
        let g' := (Ideal.Quotient.mk m).comp g
        refine (hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim
        exact ⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩
      · haveI : Subsingleton S := subsingleton_of_zero_eq_one
          ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))
        exact GlobalTheory.TrivRep.trivOn_of_subsingleton B.hom F S g)
  refine ⟨I, fun S _ g X' π f' h => ?_⟩
  rw [← hI S g]
  exact forall_congr' fun q => GlobalTheory.TrivRep.loc_iff B.hom F h q

end CompanionTheory.PfDual
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace CompanionTheory.PfDual


open GlobalTheory.TrivSubscheme in
theorem exists_closed_locTriv_noeth : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → IsLocallyNoetherian Y.left → ∀ F : LB (A ⊗ Y).left, F.IsLB → ∃ (H : Over S) (j : H ⟶ Y), IsClosedImmersion j.left ∧ ∀ (T' : Over S) (x : T' ⟶ Y), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (A ◁ x).left).pull ((snd A T').left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  intro S A Y _ hB hY F hF
  have h₀ : IsPullback (pullback.fst A.hom Y.hom) (snd A Y).left A.hom Y.hom :=
    IsPullback.of_hasPullback A.hom Y.hom
  obtain ⟨I, hI⟩ := GlobalTheory.TrivSubscheme.exists_idealSheaf
    (GlobalTheory.TrivSubscheme.LocTrivOver (snd A Y).left F)
    GlobalTheory.TrivSubscheme.LocTrivOver.comp GlobalTheory.TrivSubscheme.locTrivOver_of_affine
    (fun U => by
      haveI : IsNoetherianRing Γ(Y.left, U) := IsLocallyNoetherian.component_noetherian U
      let t : Spec (CommRingCat.of Γ(Y.left, U)) ⟶ S := U.2.fromSpec ≫ Y.hom
      have h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ Y.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd A.hom t) (snd A Y).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := exists_ideal_locTriv_noeth Γ(Y.left, U) ((Over.pullback t).obj A)
        (CubeGen.isAb_baseChange hB t) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun S g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)
      rw [← hI S g.hom _ _ _ h₃,
        GlobalTheory.TrivSubscheme.locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _).trans
        (GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ Y.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun T' x => ?_⟩
  have h₄ : IsPullback (A ◁ x).left (snd A T').left (snd A Y).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerLeft_left_snd x) h₀
    rw [Over.whiskerLeft_left_fst, Over.w x]
    exact IsPullback.of_hasPullback A.hom T'.hom
  simp only [GlobalTheory.TrivSubscheme.triv_pull_iff]
  rw [← GlobalTheory.TrivSubscheme.locTrivOver_iff h₄, hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ x.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι x.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w x)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨y, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp y.left I.subschemeι)

end CompanionTheory.PfDual
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

theorem trivLocus_pf : CompanionTheory.ObstructionTrivialLocus.TrivLocus := by
  intro S A Y _ hA hY N hN h0
  obtain ⟨Z, i, hi, hZ⟩ := exists_closed_locTriv_noeth S A Y hA hY N hN
  refine ⟨Z, i, hi, fun T y => ?_⟩
  have e : lift (fst A T) (snd A T ≫ y) = A ◁ y := by ext <;> simp
  rw [← hZ T y, ev, e]
  constructor
  · intro ht p
    exact ⟨⊤, trivial, CubeOpen.triv_pull_pull _ _ (CubeOpen.triv_comp _ rfl ht)⟩
  · intro hloc
    have hpb : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
      IsPullback.of_hasPullback _ _
    have e' : y ≫ lift (1 : Y ⟶ A) (𝟙 Y) = lift (1 : T ⟶ A) (𝟙 T) ≫ A ◁ y := by ext <;> simp
    have hsec : Triv ((N.pull (A ◁ y).left).pull (lift (1 : T ⟶ A) (𝟙 T)).left) :=
      CubeOpen.triv_pull_pull _ _ (CubeOpen.triv_comp y.left (congrArg (·.left) e') h0)
    exact GlobalTheory.exists_gen_of_local_of_section (A ⊗ T).left T.left (snd A T).left (lift (1 : T ⟶ A) (𝟙 T)).left
      (N.pull (A ◁ y).left) (pull_isLB hN _) (congrArg (·.left) (lift_snd (1 : T ⟶ A) (𝟙 T)))
      (GlobalTheory.BaseChangeFns.app_surjective GlobalTheory.globalFns_holds S A hA _ _ T.hom _ _ hpb) hloc hsec

end CompanionTheory.PfDual
end
end

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.AddAcyclic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual


set_option maxHeartbeats 1000000 in
theorem addAcyclic_pf : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, ∀ hM : M.IsLB, (∀ (Y : Over (Sp k)) (a a' : Y ⟶ A), GlobalTheory.CechPic.pull (a * a').left (cls M hM) = GlobalTheory.CechPic.pull a.left (cls M hM) + GlobalTheory.CechPic.pull a'.left (cls M hM)) → ¬ Triv M → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB A.hom M D).Acyclic := by
  intro k _ _ A _ hA M hM hadd hn κ _ _ D hD hc
  have : IsCommMonObj A := hA.comm
  have hp : IsProjBy A.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k A hA
  refine GlobalTheory.T.cechComplex_acyclic_primitive_nontrivial_algClosed k A hA hp M hM ?_ hn κ D hD hc
  have hlam : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  refine (GlobalTheory.CechPic.cls_eq_zero_iff hlam).1 ?_
  refine (GlobalTheory.CechPic.cls_cube_two hM (fst A A) (snd A A) hlam).trans ?_
  have h1 := hadd (A ⊗ A) (fst A A) (snd A A)
  have h0 := hadd (A ⊗ A) 1 1
  rw [_root_.mul_one] at h0
  have h0' : GlobalTheory.CechPic.pull (1 : A ⊗ A ⟶ A).left (cls M hM) = 0 := by
    exact add_left_cancel (h0.symm.trans (add_zero _).symm)
  simp only [GlobalTheory.CechPic.lam, h1, h0']
  abel

end CompanionTheory.PfDual
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

theorem h1Le : H1StructureDimLe := MainStatements.Hodge.Free.h1Le

theorem trivLocus : TrivLocus := trivLocus_pf

theorem fewEquations : FewEquations := fewEquations_pf h1Le

theorem ciFlat : CIFlat := GlobalTheory.T.CechFlatComplex

theorem trivLocusFlat : TrivLocusFlat := @GlobalTheory.CompanionTheory.TrivFlat.trivLocusFlat fewEquations ciFlat

theorem pointSurj : PointSurj := pointSurj_pf addAcyclic_pf

theorem finDual : FinDual := @GlobalTheory.CompanionTheory.DualAb.finDual_of_univNoeth (@GlobalTheory.CompanionTheory.DualUniv.univNoeth trivLocus trivLocusFlat pointSurj)

theorem kTrivModel : KTrivModel := @GlobalTheory.CompanionTheory.KTrivSpread.kTrivModel_of_trivLocus trivLocus

theorem kTrivDual : KTrivDual := @GlobalTheory.CompanionTheory.DualScheme.ktrivDual kTrivModel finDual

end CompanionTheory.PfDual
