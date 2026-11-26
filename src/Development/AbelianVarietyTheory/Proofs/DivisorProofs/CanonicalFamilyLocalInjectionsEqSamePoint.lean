module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseInjectionsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalCoordsEqOfMatchingData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointTransportFieldMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalInjectionsAgreeCanonicalFamilyCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfMumfordBundleTorsionPresentations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfMumfordBundleTorsionPresentations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PresRigid

open GlobalTheory.CechPic GlobalTheory.SiegLev GlobalTheory.SiegRigid GlobalTheory.ZM

theorem eq_of_field_of_ample {S : Scheme.{0}} {A : Over S} [GrpObj A] (c : CechPic.Pic A.left)
    {K : Type} [Field K] [IsAlgClosed K] {A' : Over (Sp K)} [GrpObj A'] (hA' : IsAbelianScheme A') {z : Sp K ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A z φ) (h' : IsGrpPullback A' A z φ')
    {M : LB A'.left} (hM : M.IsLB) (hamp : Out.RelAmple A' M) (hMc : cls M hM = pull φ' c)
    (hc : pull φ c = pull φ' c) {N : ℕ} (hN : 3 ≤ N) (hNK : (N : K) ≠ 0)
    (hfix : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A'), x ^ N = 1 →
      x.left ≫ φ = x.left ≫ φ') : φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut h h'
  have := hA'.comm
  have key := serreAmple K A' hA' M hM hamp N hN hNK σ hσ
    (by rw [hMc, ← pull_comp, e, hc]) fun Ω _ _ t x hx => by
      apply Over.OverMorphism.ext
      apply h'.1.hom_ext
      · rw [Over.comp_left, Category.assoc, e]
        exact hfix Ω t x hx
      · rw [Over.w, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

theorem cls_diag_lam_pull {S S' : Scheme.{0}} {G : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj H]
    [IsCommMonObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left} (hp : IsGrpPullback H G f φ) {L : LB G.left} (hL : L.IsLB)
    (h₁ : ((abelian₂ G L).pull (lift (𝟙 G) (𝟙 G)).left).IsLB)
    (h₂ : ((abelian₂ H (L.pull φ)).pull (lift (𝟙 H) (𝟙 H)).left).IsLB) : cls _ h₂ = pull φ (cls _ h₁) := by
  have hL' := pull_isLB hL φ
  have hΛ : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hΛ' : (abelian₂ H (L.pull φ)).IsLB := LB.isLB_linComb hL' _ _
  have c₁ : cls _ hΛ = lam (cls L hL) (fst G G) (snd G G) := cls_cube_two hL _ _ hΛ
  have c₂ : cls _ hΛ' = lam (cls _ hL') (fst H H) (snd H H) := cls_cube_two hL' _ _ hΛ'
  have c₃ : lam (cls L hL) (pushHom hp H (𝟙 H)) (pushHom hp H (𝟙 H)) = lam (pull φ (cls L hL)) (𝟙 H) (𝟙 H) := by
    simp only [lam, ← map_mul, ← map_one (pushHom hp H)]
    simp only [← pull_comp]
    rfl
  have c₄ : pull (pushHom hp H (𝟙 H)).left (lam (cls L hL) (𝟙 G) (𝟙 G)) =
      lam (cls L hL) (pushHom hp H (𝟙 H)) (pushHom hp H (𝟙 H)) := by
    rw [pull_lam, Category.comp_id]
  have c₅ : (pushHom hp H (𝟙 H)).left = φ := Category.id_comp φ
  rw [cls_pull hΛ, cls_pull hΛ', c₁, c₂, pull_lam, pull_lam, lift_fst, lift_snd, lift_fst, lift_snd, cls_pull hL,
    ← c₃, ← c₄]
  exact congrArg (fun q => pull q _) c₅

theorem diag_square {S S' : Scheme.{0}} {A : Over S'} {B : Over S} {φ : A.left ⟶ B.left}
    {φ₂ : (A ⊗ A).left ⟶ (B ⊗ B).left} (hs : IsSquare φ φ₂) :
    (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 B) (𝟙 B)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 B) (𝟙 B))
  have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 B) (𝟙 B))
  have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A) (𝟙 A))
  have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A) (𝟙 A))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply pullback.hom_ext
  · show (_ ≫ _) ≫ (fst B B).left = (_ ≫ _) ≫ (fst B B).left
    rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
  · show (_ ≫ _) ≫ (snd B B).left = (_ ≫ _) ≫ (snd B B).left
    rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp

theorem eq_of_lam_of_torsion : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (D : DegPre V) {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (P : LB (G2 B).left), P.IsLB → ∀ (t : Sp V ⟶ S) (a₁ a₂ : D.P.A.left ⟶ B.left) (aa₁ aa₂ : (G2 D.P.A).left ⟶ (G2 B).left), IsGrpPullback D.P.A B t a₁ → IsGrpPullback D.P.A B t a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₁) → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₂) → ∀ n : ℕ, 3 ≤ n → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], (∀ x : TF (R := V) F ⟶ D.P.A, x ^ n = 1 → x.left ≫ a₁ = x.left ≫ a₂) → a₁ = a₂ := by
  intro V _ _ _ D S B _ _ P hP t a₁ a₂ aa₁ aa₂ g₁ g₂ s₁ s₂ w₁ w₂ n hn F _ _ _ hfix
  have hab := D.P.isAb
  have hL := D.P.isLB
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := LB.isLB_linComb hL _ _
  have hN := pull_isLB hΛ (lift (𝟙 D.P.A) (𝟙 D.P.A)).left
  have hcls : ∀ (a : D.P.A.left ⟶ B.left) (aa : (G2 D.P.A).left ⟶ (G2 B).left), IsSquare a aa →
      LBIso (abelian₂ D.P.A D.P.L) (P.pull aa) →
      cls _ hN = pull a (pull (lift (𝟙 B) (𝟙 B)).left (cls P hP)) := by
    intro a aa s w
    rw [cls_pull hΛ, (cls_eq_iff hΛ (pull_isLB hP aa)).2 w, cls_pull hP, ← pull_comp, ← pull_comp, diag_square s]
  let ψ : D.P.A.left ⟶ D.P.A.left := g₂.1.lift a₁ D.P.A.hom g₁.1.w
  have e₁ : ψ ≫ a₂ = a₁ := g₂.1.lift_fst _ _ _
  have e₂ : ψ ≫ D.P.A.hom = D.P.A.hom := g₂.1.lift_snd _ _ _
  have hψ : IsGrpPullback D.P.A D.P.A (𝟙 _) ψ :=
    IsGrpPullback.cancel g₂ (by rw [Category.id_comp, e₁]; exact g₁) (by rw [e₂, Category.comp_id])
  have hψc : pull ψ (cls _ hN) = cls _ hN := by
    refine Eq.trans ?_ (hcls a₁ aa₁ s₁ w₁).symm
    rw [hcls a₂ aa₂ s₂ w₂, ← pull_comp, e₁]
  let j : Sp F ⟶ Sp V := DegPre.jFR (R := V) F
  have hp := isGrpPullback_pullback D.P.A j
  have := hab.smooth
  have := hab.proper
  have := hab.geomConnected
  have habF : IsAbelianScheme ((Over.pullback j).obj D.P.A) :=
    { comm := Functor.isCommMonObj_obj
      smooth := by change Smooth (pullback.snd D.P.A.hom j); infer_instance
      proper := by change IsProper (pullback.snd D.P.A.hom j); infer_instance
      geomConnected := by change GeometricallyConnected (pullback.snd D.P.A.hom j); infer_instance }
  have : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing V) F).injective
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e' : pullback.fst D.P.A.hom j ≫ ψ = pullback.fst D.P.A.hom j := by
    have := habF.comm
    have hL' := pull_isLB hL (pullback.fst D.P.A.hom j)
    obtain ⟨w, hw⟩ := (cls_eq_iff hL' hL').1 rfl
    have ha' : Out.RelAmple ((Over.pullback j).obj D.P.A) (D.P.L.pull (pullback.fst D.P.A.hom j)) :=
      relAmple_pull hp.1 hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) D.P.ample
    have hamp := GlobalTheory.EighthPowerFactor.relAmple_diag_lam habF hL'
      (exists_gen_theta_of_isAbelianScheme F _ habF _ hL') ha'
    have hM := pull_isLB (LB.isLB_linComb hL' _ _ : (abelian₂ ((Over.pullback j).obj D.P.A) _).IsLB)
      (lift (𝟙 ((Over.pullback j).obj D.P.A)) (𝟙 ((Over.pullback j).obj D.P.A))).left
    refine eq_of_field_of_ample (cls _ hN) habF ((hp.comp hψ).congr (Category.comp_id _) rfl) hp hM hamp
      (cls_diag_lam_pull hp hL hN hM) (by rw [pull_comp, hψc]) hn hnF fun Ω _ _ x y hy => ?_
    obtain ⟨e, rfl⟩ : ∃ e : F →+* Ω, x = spMap e := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
    obtain ⟨y₀, hy₀⟩ := GlobalTheory.TorsRat.torsion_point_rational F Ω e _ habF n (IsUnit.mk0 _ hnF) y hy
    have : Epi (spMap e) := Flat.epi_of_flat_of_surjective (spMap e)
    have hw₀ : y₀ ≫ ((Over.pullback j).obj D.P.A).hom = 𝟙 _ := by
      rw [← cancel_epi (spMap e), ← Category.assoc, ← hy₀, Over.w y, Category.comp_id]
      rfl
    let y₁ : Over.mk (𝟙 (Sp F)) ⟶ (Over.pullback j).obj D.P.A := Over.homMk y₀ hw₀
    let u : Over.mk (spMap e) ⟶ Over.mk (𝟙 (Sp F)) := Over.homMk (spMap e) (Category.comp_id _)
    have hyu : y = u ≫ y₁ := Over.OverMorphism.ext hy₀
    have hy₁ : y₁ ^ n = 1 := by
      apply Over.OverMorphism.ext
      have h1 : u ≫ y₁ ^ n = u ≫ 1 := by rw [MonObj.comp_pow, ← hyu, hy, MonObj.comp_one]
      exact (cancel_epi (spMap e)).1 (congrArg (fun q => q.left) h1)
    have hy₂ : pushHom hp (Over.mk (𝟙 (Sp F))) y₁ ^ n = 1 := by rw [← map_pow, hy₁, map_one]
    let v : TF (R := V) F ⟶ Over.mk ((Over.mk (𝟙 (Sp F))).hom ≫ j) := Over.homMk (𝟙 _) (by simp [j])
    have hx := hfix (v ≫ pushHom hp (Over.mk (𝟙 (Sp F))) y₁) (by rw [← MonObj.comp_pow, hy₂, MonObj.comp_one])
    have hxl : (v ≫ pushHom hp (Over.mk (𝟙 (Sp F))) y₁).left = y₀ ≫ pullback.fst D.P.A.hom j := Category.id_comp _
    rw [hxl] at hx
    rw [hy₀, Category.assoc, Category.assoc]
    congr 1
    apply g₂.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, ← Category.assoc, hx]
    · rw [Category.assoc, Category.assoc, e₂, Category.assoc]
  have hd := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
  have : IsDominant (pullback.fst D.P.A.hom j) := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Pullback.range_fst]
    exact hd.denseRange.preimage D.P.A.hom.isOpenMap
  have : IsReduced D.P.A.left := GlobalTheory.isReduced_of_smooth_of_isReduced D.P.A.hom
  have key : ψ = 𝟙 _ :=
    ext_of_isDominant_of_isSeparated D.P.A.hom (e₂.trans (Category.id_comp _).symm) (pullback.fst D.P.A.hom j)
      (e'.trans (Category.comp_id _).symm)
  rw [← e₁, key, Category.id_comp]

end GlobalTheory.PresRigid

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfMumfordBundleTorsionPresentationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_mumfordBundle_torsion_presentations : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (D : DegPre V) {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (P : LB (G2 B).left), P.IsLB → ∀ (t : Sp V ⟶ S) (a₁ a₂ : D.P.A.left ⟶ B.left) (aa₁ aa₂ : (G2 D.P.A).left ⟶ (G2 B).left), IsGrpPullback D.P.A B t a₁ → IsGrpPullback D.P.A B t a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₁) → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₂) → ∀ n : ℕ, 3 ≤ n → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], (∀ x : TF (R := V) F ⟶ D.P.A, x ^ n = 1 → x.left ≫ a₁ = x.left ≫ a₂) → a₁ = a₂ := by
  first | exact @GlobalTheory.PresRigid.eq_of_lam_of_torsion | exact GlobalTheory.PresRigid.eq_of_lam_of_torsion | (intros; apply GlobalTheory.PresRigid.eq_of_lam_of_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowEqBalancedFormsBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowEqBalancedFormsBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalMono

theorem coords_eq_zero {O : Type} [CommRing O] [StarRing O] [IsDedekindDomain O]
    [Module.Finite ℤ O] [Module.Free ℤ O] {w : O} (hw : w + star w = 1)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {J : Type} [Fintype J] (ε : Module.Basis J ℤ (PolFan.balForms (star : O → O) X))
    {B : Type} [AddCommGroup B] (c : J → B)
    (hc : ∀ a b, ∑ k, (ε k : LinearMap.BilinForm ℤ X) a b • c k = 0) (k : J) : c k = 0 := by
  classical
  have := Forms.projective_of_int O X
  have := Forms.finite_balTensor (O := O) (X := X)
  have := Forms.free_balTensor (X := X) hw
  let e := Module.Free.chooseBasis ℤ ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X))
  have hm := Forms.balTensorMk_mem_balForms O X
  let β : _ → PolFan.balForms (star : O → O) X := fun j =>
    ⟨(Forms.balTensorMk O).compr₂ (e.coord j),
      fun y x => congrArg (e.coord j) (hm.1 y x), fun a y x => congrArg (e.coord j) (hm.2 a y x)⟩
  let L : J → ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X)) →+ ℤ := fun i =>
    Forms.balTensorLift (O := O) ⟨(ε i : LinearMap.BilinForm ℤ X), (ε i).2.1, (ε i).2.2⟩
  have hL (i a b) : L i (Forms.balTensorMk O a b) = (ε i : LinearMap.BilinForm ℤ X) a b := rfl
  let Φ : ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X)) →+ B :=
    ∑ i, (zmultiplesHom B (c i)).comp (L i)
  have hΦa (t) : Φ t = ∑ i, L i t • c i := by
    simp [Φ, AddMonoidHom.finsetSum_apply]
  have hΦ : Φ = 0 := Forms.balTensor_hom_ext fun a b => by
    rw [hΦa]
    exact hc a b
  have hε (i) : ε i = ∑ j, L i (e j) • β j := by
    apply Subtype.ext
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hL, ← e.sum_repr (Forms.balTensorMk O a b), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_eq_mul, _root_.mul_comm]
    rfl
  have hδ (i) : L i (∑ j, ε.repr (β j) k • e j) = ε.repr (ε i) k := by
    have h1 := congrArg (ε.coord k) (hε i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← ε.coord_apply, h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, _root_.mul_comm, ε.coord_apply]
  have h := hΦa (∑ j, ε.repr (β j) k • e j)
  simp only [hδ, hΦ, AddMonoidHom.zero_apply] at h
  simpa [Finsupp.single_apply] using h.symm

theorem eq_of_prod_zpow_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F] (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms H.bar X)) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ X) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ X) a b) → x = y := by
  intro E _ _ _ H X _ _ _ _ F _ I _ ε x y hx hy h
  letI : StarRing (𝓞 E) :=
    { star := H.bar
      star_involutive := fun a => by
        apply Subtype.ext
        change ((H.bar (H.bar a) : 𝓞 E) : E) = a
        rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
      star_mul := fun a b => by rw [map_mul, _root_.mul_comm]
      star_add := fun a b => map_add H.bar a b }
  have hw : H.w0 + H.bar H.w0 = 1 := PullbackSections.CVA.cmHostUnit_add_conj_eq_one H
  let u : I → Fˣ := fun i => Units.mk0 (x i) (hx i)
  let v : I → Fˣ := fun i => Units.mk0 (y i) (hy i)
  have huv : ∀ a b, ∏ i, (u i / v i) ^ ((ε i : LinearMap.BilinForm ℤ X) a b) = 1 := by
    intro a b
    rw [Finset.prod_congr rfl (fun i _ => div_zpow _ _ _), Finset.prod_div_distrib, div_eq_one]
    apply Units.ext
    simpa [u, v, Units.coe_prod] using h a b
  funext k
  have hk := coords_eq_zero (O := 𝓞 E) hw ε (fun i => Additive.ofMul (u i / v i))
    (fun a b => by
      apply Additive.toMul.injective
      simp only [toMul_sum, toMul_zsmul, toMul_ofMul, toMul_zero]
      exact huv a b) k
  have hk' : u k / v k = 1 := hk
  simpa [u, v] using congrArg Units.val (div_eq_one.1 hk')

end GlobalTheory.BalMono
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowEqBalancedFormsBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_prod_zpow_eq_balancedForms_basis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F] (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms H.bar X)) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ X) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ X) a b) → x = y := by
  first | exact @GlobalTheory.BalMono.eq_of_prod_zpow_eq | exact GlobalTheory.BalMono.eq_of_prod_zpow_eq | (intros; apply GlobalTheory.BalMono.eq_of_prod_zpow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalInjectionsAgreeCanonicalFamilyCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.UInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lattice_id {O : Type} [CommRing O] {bar : O → O} {ψ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : ℕ} {δ : Fin m → LinearMap.BilinForm ℤ X} (hδ : IsCone bar ψ δ)
    (hdef : ∀ x, x ≠ 0 → ∃ k, 0 < δ k x x) (ga : X ≃ₗ[O] X) (c c' : Fin m → ℕ) (hc : ∀ k, 0 < c k) (hc' : ∀ k, 0 < c' k)
    (he : ∑ k, c k • δ k = ∑ k, c' k • pull ga.toLinearMap (δ k)) {n : ℕ} (hn : 3 ≤ n)
    (hcong : ∀ x, GlobalTheory.Poinc.CongMod n (ga x) x) (x : X) : ga x = x := by
  classical
  have hδ' := hδ.pull_equiv ga
  set δ' := fun k => pull ga.toLinearMap (δ k) with hd
  have h1 : ∀ k, ∃ j, δ k = δ' j := cone_gen_mem_of_common hδ hδ' c c' hc he
  have h2 : ∀ j, ∃ k, δ' j = δ k := cone_gen_mem_of_common hδ' hδ c' c hc' he.symm
  have himg : Finset.univ.image δ = Finset.univ.image δ' := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨by rintro ⟨k, rfl⟩; exact (h1 k).imp fun _ => Eq.symm, by rintro ⟨j, rfl⟩; exact (h2 j).imp fun _ => Eq.symm⟩
  have e1 : ∑ x ∈ Finset.univ.image δ, x = ∑ k, δ k := Finset.sum_image fun a _ b _ h => hδ.injective h
  have e2 : ∑ x ∈ Finset.univ.image δ', x = ∑ k, δ' k := Finset.sum_image fun a _ b _ h => hδ'.injective h
  have hS : ∑ k, δ k = ∑ k, δ' k := by rw [← e1, ← e2, himg]
  have hk : ∀ x y, (∑ k, δ k) (ga x) (ga y) = (∑ k, δ k) x y := by
    intro x y
    have h := LinearMap.congr_fun₂ hS x y
    simp only [LinearMap.sum_apply, hd, pull_apply, LinearEquiv.coe_coe] at h ⊢
    exact h.symm
  have hpos : ∀ x, x ≠ 0 → 0 < (∑ k, δ k) x x := by
    intro x hx
    obtain ⟨k, hk⟩ := hdef x hx
    simp only [LinearMap.sum_apply]
    exact Finset.sum_pos' (fun i _ => hδ.nonneg i x) ⟨k, Finset.mem_univ _, hk⟩
  exact DFunLike.congr_fun (GlobalTheory.Poinc.eq_refl_of_isometry_congMod X _ hpos ga.toAddEquiv.toIntLinearEquiv hk n hn hcong) x

theorem tors_sec {D' : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {bs : Geo.Tor.Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o : Obj D' l bs s) {G : Over S} [GrpObj G] {φ : o.t.G.left ⟶ G.left}
    (h : IsGrpPullback o.t.G G (𝟙 S) φ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (p : Over.mk x ⟶ G)
    (hp : p ^ l.A = 1) : ∃ σ : 𝟙_ (Over S) ⟶ G, σ ^ l.A = 1 ∧ p.left = x ≫ σ.left := by
  have : IsMonHom (Iso.refl G).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_of_iso (Iso.refl G))
  obtain ⟨-, I, -, hI, -⟩ := o.geom K x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage _).symm
  obtain ⟨a, ha⟩ := (I.onto l.A l.A_pos (p ≫ e.inv)).1 (by rw [← MonObj.pow_comp, hp, MonObj.one_comp])
  have h0 : o.etaA 0 = 1 := by simpa using o.etaA_ker 0
  have hpow : ∀ n : ℕ, o.etaA (n • a) = o.etaA a ^ n := fun n => by
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [succ_nsmul, o.etaA_add, ih, pow_succ]
  refine ⟨o.etaA a ≫ e.hom, by rw [← MonObj.pow_comp, ← hpow, o.etaA_ker, MonObj.one_comp], ?_⟩
  have : p = toUnit _ ≫ o.etaA a ≫ e.hom := by
    rw [← Category.assoc, hI, ha, Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [this]
  rfl

theorem second_diff {X Y K I : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] [Field K]
    [Fintype I] (e : X ≃ₗ[𝓞 E] Y) (s : I → K) (hs : ∀ k, s k ≠ 0) (ε : I → LinearMap.BilinForm ℤ Y)
    (hε : ∀ k, ε k ∈ balForms H.bar Y) (n : ℤ) (g : X → Kˣ)
    (hg : ∀ y, (((g y)⁻¹ : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e y) (H.w0 • e y))) (a a' : X) :
    (((g (a + a'))⁻¹ * g a * g a' : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e a) (e a')) := by
  have hw : H.w0 + H.bar H.w0 = 1 := GlobalTheory.PelPrim.cmHostUnit_add_conj_eq_one H
  have hg' : ∀ y, (g y : K) = (∏ k, s k ^ (n * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg, Units.val_inv_eq_inv_val, inv_inv]
  rw [Units.val_mul, Units.val_mul, hg, hg', hg', ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hs k), ← zpow_add₀ (hs k)]
  congr 1
  have h1 : ε k (e a') (H.w0 • e a) = ε k (e a) (H.bar H.w0 • e a') := by rw [(hε k).1, (hε k).2]
  have h2 : ε k (e a) (H.w0 • e a') + ε k (e a) (H.bar H.w0 • e a') = ε k (e a) (e a') := by
    rw [← map_add (f := _), ← add_smul, hw, one_smul]
  simp only [map_add (f := _), smul_add, LinearMap.add_apply, h1]
  rw [← h2]
  ring

theorem monomials_eq {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F] : 1 ≤ n → D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → b.left ≫ β₂ = β₁ → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ c a : Fin T.r → ℤ, ∏ i, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (s₁ i)) ^ ε i c a = ∏ i, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (s₂ i)) ^ ε i c a := by
  intro hn hD₁ hD₂ hF₁ hF₂ hM he hb H c a
  obtain ⟨hbm, -, -, hu, -⟩ := hM
  obtain ⟨p₁, p₂, hy₁, ht₁, hy₂, ht₂, p', hy', hA, hE⟩ := H a
  have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ hD₂ F n hn p' p₂ (by
    rw [hy', hy₁, hy₂]; apply e₂.injective; rw [he, e₁.apply_symm_apply, e₂.apply_symm_apply]) hE
  rw [hg] at hA
  have hχ : e₁ (φ.symm (e₂.symm c)) = e₂ (e₂.symm c) := by rw [← he, φ.apply_symm_apply]
  obtain ⟨u, hun⟩ := hu (e₂.symm c)
  obtain ⟨k₁, hk₁, hv₁⟩ := ht₁.2 (φ.symm (e₂.symm c))
  obtain ⟨k₂, hk₂, hv₂⟩ := ht₂.2 (e₂.symm c)
  let z : (TF (R := V) F).left := (⊥ : PrimeSpectrum F)
  obtain ⟨J, hJ, -⟩ := exists_good (JN D₁ D₂) (jn_isLB D₁ D₂) z (K := Empty) Empty.elim Empty.elim
    (fun a => a.elim) (fun k => k.elim)
  obtain ⟨J₀, hJ₀, -⟩ := exists_good T.M.L T.M.isLB z (K := Empty) Empty.elim Empty.elim
    (fun a => a.elim) (fun k => k.elim)
  have a₁ := hv₁ z J₀ (rl J) hJ₀ ((isPart_inl D₁.P.L D₂.P.L).good hJ)
  have a₂ := hv₂ z J₀ (rr J) hJ₀ ((isPart_inr D₁.P.L D₂.P.L).good hJ)
  have a₃ := hA.2 (e₂.symm c) u hun z J hJ
  have a₄ := GlobalTheory.T.mumfordBundleIso_comparison_normalisedGenerator T ε n V ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hD₁ hD₂ hF₁ hF₂ hbm hb
    (φ.symm (e₂.symm c)) (e₂.symm c) hχ u hun (TF (R := V) F) p₁.g.b z J J₀ hJ hJ₀
  rw [← hA.1] at a₄
  rw [hχ] at a₁
  have hk : k₁ = k₂ := by
    apply gm_unitOn_inj z
    exact cancel_four a₁ a₂ a₃ a₄
  have := congrArg Units.val hk
  rw [hk₁, hk₂, hχ, e₂.apply_symm_apply] at this
  exact this

theorem torsion_fixed {W R V : Type} [CommRing W] [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {B : Over (Sp W)} [GrpObj B]
    {n : ℕ} (hn : 1 ≤ n) (hB : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp W) (p : Over.mk x ⟶ B), p ^ n = 1 →
      ∃ σ : 𝟙_ (Over (Sp W)) ⟶ B, σ ^ n = 1 ∧ p.left = x ≫ σ.left)
    {D₀ : DegPre R} {D₁ D₂ : DegPre V} (h₀ : D₀.TauBimult) (h₂ : D₂.TauBimult) {ω : W →+* R} {β : D₀.P.A.left ⟶ B.left}
    (hβ : IsGrpPullback D₀.P.A B (spMap ω) β) {f₁ f₂ : R →+* V} (hf : f₁.comp ω = f₂.comp ω) (hD₁ : IsPullDeg f₁ D₀ D₁)
    (hD₂ : IsPullDeg f₂ D₀ D₂) {F₀ F : Type} [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] [Field F]
    [IsAlgClosed F] [Algebra (FractionRing V) F] {j₁ j₂ : F₀ →+* F} {b : D₁.P.A ⟶ D₂.P.A} {φ : D₁.X ≃+ D₂.X}
    (hj₁ : Ext f₁ j₁) (hj₂ : Ext f₂ j₂)
    (hβ₁ : IsGrpPullback D₁.P.A B (spMap (f₁.comp ω)) ((hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁)) ≫ β))
    (HP : ∀ p₀ : QkPt D₀ F₀ n, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧
      p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂)
    (x : TF (R := V) F ⟶ D₁.P.A) (hx : x ^ n = 1) :
    x.left ≫ (hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁)) ≫ β =
      x.left ≫ b.left ≫ (hD₂.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₂)) ≫ β := by
  obtain ⟨σ, hσ, hxσ⟩ := hB F ((TF (R := V) F).hom ≫ spMap (f₁.comp ω)) (pushHom hβ₁ _ x) (by rw [← map_pow, hx, map_one])
  have hxσ' : x.left ≫ (hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁)) ≫ β =
      ((TF (R := V) F).hom ≫ spMap (f₁.comp ω)) ≫ σ.left := hxσ
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.SiegelPull.push_surjective hβ (TF (R := R) F₀) (toUnit _ ≫ σ)
  have hb₀' : b₀.left ≫ β = (TF (R := R) F₀).hom ≫ spMap ω ≫ σ.left := by
    have e := congrArg (fun z => z.left) hb₀
    simp only [pushHom, pushPt, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left] at e
    rw [e]
    simp
  have hpow : b₀ ^ n = 1 := by
    apply GlobalTheory.SiegelPull.push_injective hβ
    rw [map_pow, hb₀, ← MonObj.comp_pow, hσ, MonObj.comp_one, map_one]
  obtain ⟨p₀, hp₀y, hp₀b⟩ := GlobalTheory.TInj.exists_qk_zero_over R D₀ h₀ F₀ n hn b₀ hpow
  obtain ⟨p₁, p₂, h1y, htr1, h2y, htr2, p', hp'y, hact, heqv⟩ := HP p₀
  have hg₀ : p₀.g.b.left ≫ β = (TF (R := R) F₀).hom ≫ (spMap ω ≫ σ.left) := by rw [hp₀b, hb₀']
  have hsp : ∀ f : R →+* V, spMap (f.comp ω) = spMap f ≫ spMap ω := fun f => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have e₁ := tr_base hj₁ htr1 _ _ hg₀
  have e₂ := tr_base hj₂ htr2 _ _ hg₀
  rw [← Category.assoc (spMap _), ← hsp] at e₁ e₂
  have hg : p'.g = p₂.g := GlobalTheory.T.torsionPoint_torusPart_eq_of_equiv_same_lattice V D₂ h₂ F n hn p' p₂ (by rw [hp'y, h1y, h2y, hp₀y, map_zero, map_zero, map_zero]) heqv
  have hx₁ : x.left = p₁.g.b.left := by
    apply hβ₁.1.hom_ext
    · rw [hxσ', e₁, Category.assoc]
    · rw [Over.w, Over.w]
  rw [hx₁, e₁, hf, ← e₂, ← hg, hact.1, Over.comp_left, Category.assoc]


set_option maxHeartbeats 1000000 in
theorem coords_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∀ k, θ₁ (Cn.ψ (MvPolynomial.X k)) = θ₂ (Cn.ψ (MvPolynomial.X k)) := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn R' _ _ _ hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have hW := GlobalTheory.T.canonicalFamily_base_injections_agree Xo c φ hpq hφ hns R hR C Cn R' hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ hκ₁ hκ₂ hy
  letI := H.starRing
  have hn : 3 ≤ l.M' := l.three_le.trans (Nat.le_of_dvd (level_pos l) (Nat.dvd_lcm_left _ _))
  have hn1 : 1 ≤ l.M' := by omega
  set iw := Cn.ψ.comp MvPolynomial.C with hiwd
  have hiw : Function.Injective iw := by
    have hfl : iw.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) Cn.compl.2.2.1
    letI := iw.toAlgebra
    have : Module.Flat Cn.L.W R := hfl
    have : IsLocalHom (algebraMap Cn.L.W R) := Cn.ψ_loc
    have : Module.FaithfullyFlat Cn.L.W R := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective Cn.L.W R
  let s : Fin C.m ⊕ Fin Cn.N → R := fun k => Cn.ψ (MvPolynomial.X k)
  have hs0 : ∀ k, s k ≠ 0 := by
    rintro (k | k)
    · exact (Cn.bd k).trans_ne (C.s_ne_zero k)
    · exact (Cn.tor k).ne_zero
  obtain ⟨hev, hbi, hgen, -⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨T, ib, β₀, ββ₀, w₀, hF₀⟩ := GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData Cn.L.b Cn.L.D Cn.L.bimult Cn.L.gen l.M'
  obtain ⟨g, hD, hg, hxe, -⟩ := Cn.data
  let ε : Fin C.m ⊕ Fin Cn.N → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X).compl₁₂ ib.symm.toIntLinearEquiv.toLinearMap ib.symm.toIntLinearEquiv.toLinearMap
  have hε : ∀ k a b, ε k (ib a) (ib b) = (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) a b := fun k a b =>
    congrArg₂ (fun x y => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) x y) (ib.symm_apply_apply a) (ib.symm_apply_apply b)
  let e : C.P.D.toPre.X ≃+ (Fin T.r → ℤ) := Cn.e.toAddEquiv.trans ib
  have he : ∀ y, e y = ib (Cn.e y) := fun _ => rfl
  obtain ⟨β, ββ, w, hF⟩ := GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial T l.M' (mulDeg Cn.L.D l.M') hev hbi hgen ib β₀ ββ₀ w₀ hF₀ R iw hiw C.P.D.toPre g hD
    s ε e (fun y => congrArg ib (hxe y).symm) (fun a a' => by
      simp only [he, hε]
      exact second_diff Cn.e _ (fun k => (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (hs0 k)) _
        (fun k => (Cn.ε k).2) _ g hg a a')
  have hT : IsGrpPullback Cn.L.o.t.G T.B (𝟙 _) (Cn.L.φB ≫ β₀) :=
    (Cn.L.ab.1.comp hF₀.1).congr ((Category.id_comp _).trans (Spec.map_id _)) rfl
  obtain ⟨V, _, _, _, _, η', f₁, f₂, hV, hη, hf₁, hf₂, lf₁, lf₂, c₁, c₂⟩ :=
    exists_cDvr_two_embeddings R R R' (RingHom.id R) Function.injective_id (RingHom.Finite.id R)
      ⟨hR'.1.1, hR'.1.2.2.1, hR'.1.2.2.2, hR'.2⟩ θ₁ θ₂ i₁ i₂ l₁ l₂
  rw [RingHom.comp_id] at c₁ c₂
  obtain ⟨k₀, hk₀⟩ := exists_genericMap hη
  have hk : ∀ (θ : R →+* R') (κ : Sp (FractionRing R') ⟶ Sp (FractionRing R)), κ ≫ jK R = jK R' ≫ spMap θ →
      (k₀ ≫ κ) ≫ jK R = jK V ≫ spMap (η'.comp θ) := fun θ κ hκ => by
    rw [Category.assoc, hκ, ← Category.assoc, hk₀, Category.assoc, GlobalTheory.GenericBundleDescent.sp_comp]
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, ph, hE₁, hE₂, hM, hlin, hpairs, -⟩ := pair_match Xo c φ R hR C.toFam V hV f₁ f₂ hf₁ hf₂
    lf₁ lf₂ (k₀ ≫ κ₁) (k₀ ≫ κ₂) (c₁ ▸ hk θ₁ κ₁ hκ₁) (c₂ ▸ hk θ₂ κ₂ hκ₂) (by rw [Category.assoc, hy, Category.assoc])
  obtain ⟨ββ₁, w₁, hF₁⟩ := from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₁ D₁.toPre hD₁ hf₁ hF
  obtain ⟨ββ₂, w₂, hF₂⟩ := from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₂ D₂.toPre hD₂ hf₂ hF
  have htaut : ∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M')
      (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'),
      p₁.y = (hD₁.xe.trans e).symm a ∧ TautPt T (f₁.comp iw) (fun k => f₁ (s k)) ε l.M' D₁.toPre (hD₁.xe.trans e)
        ((hD₁.e.hom.left ≫ pullback.fst C.P.D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁ (AlgebraicClosure (FractionRing V)) a p₁.g ∧
      p₂.y = (hD₂.xe.trans e).symm a ∧ TautPt T (f₂.comp iw) (fun k => f₂ (s k)) ε l.M' D₂.toPre (hD₂.xe.trans e)
        ((hD₂.e.hom.left ≫ pullback.fst C.P.D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ (AlgebraicClosure (FractionRing V)) a p₂.g ∧
      QImg b ph p₁ p₂ := by
    intro a
    obtain ⟨p₀, hp₀y, hp₀⟩ := GlobalTheory.T.periodPart_mem_tautologicalPoint_torsion T ε l.M' R C.P.D.toPre iw s e β ββ w C.P.D.tau_bimult hF hs0
      (AlgebraicClosure (FractionRing R)) a
    obtain ⟨p₁, p₂, hp₁y, hTr₁, hp₂y, hTr₂, hQ⟩ := hpairs p₀
    exact ⟨p₁, p₂, by rw [hp₁y, hp₀y]; rfl,
      GlobalTheory.T.tautologicalPoint_transport_fieldMap T ε l.M' R V _ C.P.D iw s e β ββ w f₁ D₁.toPre hD₁ ββ₁ w₁ hf₁ D₁.tau_bimult hF hF₁ _ _ j₁ hE₁ a _ _ hp₀ hTr₁,
      by rw [hp₂y, hp₀y]; rfl,
      GlobalTheory.T.tautologicalPoint_transport_fieldMap T ε l.M' R V _ C.P.D iw s e β ββ w f₂ D₂.toPre hD₂ ββ₂ w₂ hf₂ D₂.tau_bimult hF hF₂ _ _ j₂ hE₂ a _ _ hp₀ hTr₂,
      hQ⟩

  let ga : C.P.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X :=
    { (hD₁.xe.symm.trans ph).trans hD₂.xe with map_smul' := hlin }
  have hga : ∀ y, ga y = hD₂.xe (ph (hD₁.xe.symm y)) := fun _ => rfl
  have hbd : ∀ f : R →+* V, Function.Injective f → IsLocalHom f → ∀ k, f (s (.inl k)) ∈ maximalIdeal V ∧ f (s (.inl k)) ≠ 0 :=
    fun f hf hl k => ⟨map_nonunit f _ (show Cn.ψ _ ∈ maximalIdeal R from (Cn.bd k).symm ▸ C.s_mem k),
      (map_ne_zero_iff f hf).2 (hs0 _)⟩
  have hpu := GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit T ε l.M' V D₁.toPre D₂.toPre _ _ _ _ ββ₁ w₁ _ _ _ _ ββ₂ w₂ b ph _ D₁.tau_bimult D₂.tau_bimult hF₁ hF₂ hM
  obtain ⟨d₁, d₂, hd₁, hd₂, hsum⟩ := GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination V T.r C.m Cn.N l.M' hn1 ε (fun k => f₁ (s k)) (fun k => f₂ (s k))
    ((e.symm.trans ga.toAddEquiv).trans e).toIntLinearEquiv (hbd f₁ hf₁ lf₁) (fun k => (Cn.tor k).map f₁) (hbd f₂ hf₂ lf₂)
    (fun k => (Cn.tor k).map f₂) (fun a a' => by
      obtain ⟨u, hu⟩ := hpu (hD₁.xe.symm (e.symm a)) (hD₁.xe.symm (e.symm a'))
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply] at hu
      exact ⟨u, hu⟩)
  have hδ : ∀ k a a', C.δ k a a' = ε (.inl k) (e a) (e a') := fun k a a' => by rw [he, he, hε, Cn.cone]; rfl
  have hid := lattice_id C.cone (fun x hx => by
      obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hx
      exact ⟨i, (mul_pos_iff_of_pos_left (show (0 : ℤ) < l.M' by exact_mod_cast level_pos l)).1 hi⟩) ga d₁ d₂ hd₁ hd₂
    (LinearMap.ext₂ fun a a' => by
      have h := LinearMap.congr_fun₂ hsum (e a) (e a')
      simpa [LinearMap.sum_apply, hδ] using h) hn (fun x => by
      obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := htaut (e x)
      have h : hD₂.xe p₂.y = hD₂.xe (ph p₁.y) + l.M' • hD₂.xe z := by rw [hz, map_add (f := _), hp', map_nsmul]
      rw [hy₂, hy₁] at h
      refine ⟨-(hD₂.xe z), ?_⟩
      rw [smul_neg, eq_add_neg_iff_add_eq, hga]
      simpa using h.symm)
  have hlat : ∀ y, (hD₂.xe.trans e) (ph y) = (hD₁.xe.trans e) y := fun y => by
    have := hid (hD₁.xe y)
    rw [hga, AddEquiv.symm_apply_apply] at this
    exact congrArg e this

  have hω : f₁.comp iw = f₂.comp iw := by rw [c₁, c₂, RingHom.comp_assoc, RingHom.comp_assoc, hW]
  rw [← hω] at hF₂ htaut
  haveI := hM.2.1
  haveI : IsMonHom (asIso b).hom := hM.1
  have hbsq : IsSquare b.left (lift (fst D₁.toPre.P.A D₁.toPre.P.A ≫ b) (snd D₁.toPre.P.A D₁.toPre.P.A ≫ b) :
      G2 D₁.toPre.P.A ⟶ G2 D₂.toPre.P.A).left :=
    ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
  have hLam : ∀ D : DegPre V, (abelian₂ D.P.A D.P.L).IsLB := fun D => LB.isLB_linComb D.P.isLB _ _
  have hLamT : (abelian₂ T.B T.M.L).IsLB := LB.isLB_linComb T.M.isLB _ _
  have hb := GlobalTheory.T.eq_of_mumfordBundle_torsion_presentations V D₁.toPre T.B _ hLamT _ _ _ _ _ hF₁.1
    (((isGrpPullback_of_iso (asIso b)).comp hF₂.1).congr (Category.id_comp _) rfl) hF₁.2.1 (isSquare_comp hbsq hF₂.2.1)
    ⟨w₁, hF₁.2.2.1⟩ (LBIso.trans (hLam _) (pull_isLB (hLam _) _) (pull_isLB hLamT _) hM.2.2.1
      (lbIso_pull_comp ⟨w₂, hF₂.2.2.1⟩ _ rfl)) l.M' hn (AlgebraicClosure (FractionRing V))
    (torsion_fixed hn1 (tors_sec Cn.L.o hT) C.P.D.tau_bimult D₂.tau_bimult hF.1 hω hD₁ hD₂ hE₁ hE₂ hF₁.1 hpairs)
  have key := monomials_eq T ε l.M' V _ D₁.toPre D₂.toPre _ _ _ ββ₁ w₁ _ _ _ ββ₂ w₂ b ph _ hn1 D₁.tau_bimult D₂.tau_bimult
    hF₁ hF₂ hM hlat hb.symm htaut
  let f : V →+* AlgebraicClosure (FractionRing V) := (algebraMap (FractionRing V) _).comp (algebraMap V (FractionRing V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing V) _).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hx := GlobalTheory.T.eq_of_prod_zpow_eq_balancedForms_basis H Cn.L.D.X _ _ Cn.ε (fun k => f (f₁ (s k))) (fun k => f (f₂ (s k)))
    (fun k => (map_ne_zero_iff _ hf).2 ((map_ne_zero_iff _ hf₁).2 (hs0 k)))
    (fun k => (map_ne_zero_iff _ hf).2 ((map_ne_zero_iff _ hf₂).2 (hs0 k)))
    (fun a a' => by
      have := key (ib a) (ib a')
      simp only [hε] at this
      exact this)
  intro k
  have h1 := hf (congrFun hx k)
  rw [c₁, c₂] at h1
  exact hη h1

end GlobalTheory.UInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalInjectionsAgreeCanonicalFamilyCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localInjections_agree_canonicalFamily_coordinates : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∀ k, θ₁ (Cn.ψ (MvPolynomial.X k)) = θ₂ (Cn.ψ (MvPolynomial.X k)) := by
  first | exact @GlobalTheory.UInj.coords_eq | exact GlobalTheory.UInj.coords_eq | (intros; apply GlobalTheory.UInj.coords_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLocalInjectionsEqSamePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.inj_of_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R), Canon C → Inj C := by
  intro E _ _ _ H Dw l Xo c φ h₁ h₂ h₃ R _ _ _ hR C Cn R' _ _ _ hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ e₁ e₂ e
  have : IsNoetherianRing R' := hR'.1.1
  refine GlobalTheory.TChart.cuniq _ R R' Cn.ψ Cn.compl θ₁ θ₂ l₁ l₂ (MvPolynomial.ringHom_ext (fun w => ?_) (fun k => ?_))
  · exact RingHom.congr_fun
      (GlobalTheory.T.canonicalFamily_base_injections_agree Xo c φ h₁ h₂ h₃ R hR C Cn R' hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ e₁ e₂ e) w
  · exact GlobalTheory.T.localInjections_agree_canonicalFamily_coordinates Xo c φ h₁ h₂ h₃ R hR C Cn R' hR' θ₁ θ₂ i₁ i₂ l₁ l₂ κ₁ κ₂ e₁ e₂ e k
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLocalInjectionsEqSamePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_localInjections_eq_same_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R), Canon C → Inj C := by
  first | exact @GlobalTheory.UCanon.inj_of_canon | exact GlobalTheory.UCanon.inj_of_canon | (intros; apply GlobalTheory.UCanon.inj_of_canon <;> assumption)
end
