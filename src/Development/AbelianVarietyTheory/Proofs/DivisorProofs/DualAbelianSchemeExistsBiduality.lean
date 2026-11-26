module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualRepresentableAffineBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleDescendsQuotientFiniteSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialAdditiveFamilyKilledByIsogenyStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemePoincare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingAdditiveFamiliesIsDualComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingAdditiveFamiliesIsDualComm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}}

def addCls (A : Over S) [GrpObj A] (T : Over S) : AddSubgroup (Pic (A ⊗ T).left) where
  carrier := {c | ∀ (Y : Over S) (a a' : Y ⟶ A) (t : Y ⟶ T),
    CechPic.pull (lift (a * a') t).left c = CechPic.pull (lift a t).left c + CechPic.pull (lift a' t).left c}
  add_mem' {c d} hc hd Y a a' t := by
    simp only [map_add (f := _)]
    rw [hc Y a a' t, hd Y a a' t]
    abel
  zero_mem' Y a a' t := by simp only [map_zero, add_zero]
  neg_mem' {c} hc Y a a' t := by
    simp only [map_neg]
    rw [hc Y a a' t]
    abel

variable {A : Over S} [GrpObj A]

theorem fam_iff_mem {T : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) : Fam A N ↔ cls N hN ∈ addCls A T :=
  ⟨fun h ↦ (isAdditive_iff hN).1 h.add, fun h ↦ ⟨hN, (isAdditive_iff hN).2 h⟩⟩

def resCls {T' T : Over S} (u : T' ⟶ T) : addCls A T →+ addCls A T' :=
  ((CechPic.pull (lift (fst A T') (snd A T' ≫ u)).left).comp (addCls A T).subtype).codRestrict _
    fun c Y a a' t ↦ by
      simp only [AddMonoidHom.coe_comp, AddSubgroup.coe_subtype, Function.comp_apply, ← CechPic.pull_comp,
        ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
      exact c.2 Y a a' (t ≫ u)


variable (A) in
def famFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{1} where
  obj T := CommGrpCat.of (Multiplicative (addCls A T.unop))
  map g := CommGrpCat.ofHom (AddMonoidHom.toMultiplicative (resCls (A := A) g.unop))
  map_id T := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun c ↦ ?_)
    refine Subtype.ext ?_
    change CechPic.pull (lift (fst A T.unop) (snd A T.unop ≫ 𝟙 _)).left _ = _
    rw [Category.comp_id, lift_fst_snd, Over.id_left, CechPic.pull_id]
    rfl
  map_comp {T T' T''} g g' := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun c ↦ ?_)
    refine Subtype.ext ?_
    change CechPic.pull (lift (fst A T''.unop) (snd A T''.unop ≫ g'.unop ≫ g.unop)).left _ =
      CechPic.pull (lift (fst A T''.unop) (snd A T''.unop ≫ g'.unop)).left
        (CechPic.pull (lift (fst A T'.unop) (snd A T'.unop ≫ g.unop)).left _)
    rw [← CechPic.pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]

section Rep

variable {B : Over S} {P : LB (A ⊗ B).left} (h : Rep A (toUnit B) P)

include h

def ptCls (T : Over S) (x : T ⟶ B) : addCls A T :=
  ⟨evc h.fam.isLB (fst A T) (snd A T ≫ x), (fam_iff_mem (pull_isLB h.fam.isLB _)).1
    ⟨pull_isLB h.fam.isLB _, fun Y a a' t ↦ by
      refine (cls_eq_iff (pull_isLB (pull_isLB h.fam.isLB _) _)
        (isLB_tens (pull_isLB (pull_isLB h.fam.isLB _) _) (pull_isLB (pull_isLB h.fam.isLB _) _))).1 ?_
      rw [cls_tens (pull_isLB (pull_isLB h.fam.isLB _) _) (pull_isLB (pull_isLB h.fam.isLB _) _)]
      rw [cls_ev (pull_isLB h.fam.isLB _), cls_ev (pull_isLB h.fam.isLB _), cls_ev (pull_isLB h.fam.isLB _)]
      rw [evc_ev h.fam.isLB, evc_ev h.fam.isLB, evc_ev h.fam.isLB]
      simp only [lift_fst, lift_snd_assoc]
      exact (isAdditive_iff h.fam.isLB).1 h.fam.add Y _ _ _⟩⟩

theorem ptCls_bij (T : Over S) : Function.Bijective (ptCls h T) := by
  have hP := h.fam.isLB
  constructor
  · intro x x' e
    have hN : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hP _
    have fN : Fam A (ev P (fst A T) (snd A T ≫ x)) := (fam_iff_mem hN).2 (ptCls h T x).2
    refine (h.univ T (toUnit T) _ fN).unique ⟨toUnit_unique _ _, (cls_eq_iff hN hN).1 rfl⟩
      ⟨toUnit_unique _ _, (cls_eq_iff hN (pull_isLB hP _)).1 (congrArg Subtype.val e)⟩
  · intro c
    obtain ⟨N, hN, hc⟩ := cls_surj (c : Pic (A ⊗ T).left)
    have fN : Fam A N := (fam_iff_mem hN).2 (hc ▸ c.2)
    obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ T (toUnit T) N fN
    exact ⟨x, Subtype.ext (((cls_eq_iff hN (pull_isLB hP _)).2 hx).symm.trans hc)⟩

theorem ptCls_comp {T' T : Over S} (g : T' ⟶ T) (x : T ⟶ B) :
    ptCls h T' (g ≫ x) = resCls g (ptCls h T x) := by
  refine Subtype.ext ?_
  change evc h.fam.isLB (fst A T') (snd A T' ≫ g ≫ x) =
    CechPic.pull (lift (fst A T') (snd A T' ≫ g)).left (evc h.fam.isLB (fst A T) (snd A T ≫ x))
  rw [pull_evc, lift_fst, lift_snd_assoc, Category.assoc]

def famRep : (famFunctor A ⋙ forget CommGrpCat.{1}).RepresentableBy B where
  homEquiv {T} := (Equiv.ofBijective _ (ptCls_bij h T)).trans Multiplicative.ofAdd
  homEquiv_comp g x := ptCls_comp h g x

end Rep

end GlobalTheory.DualCon

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S} {P : LB (A ⊗ B).left}

theorem evc_eq_pull_ptCls (h : Rep A (toUnit B) P) {Y : Over S} (a : Y ⟶ A) (x : Y ⟶ B) :
    evc h.fam.isLB a x = CechPic.pull (lift a (𝟙 Y)).left (ptCls h Y x : Pic (A ⊗ Y).left) := by
  change _ = CechPic.pull (lift a (𝟙 Y)).left (evc h.fam.isLB (fst A Y) (snd A Y ≫ x))
  rw [pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]

theorem rep_isDual : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left),
    Rep A (toUnit B) P → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsDual A B P ∧ IsAdditive (swap P) := by
  intro S A B _ P h
  have hP := h.fam.isLB
  letI inst : CommGrpObj B := CommGrpObj.ofRepresentableBy B _ (famRep h)
  have hmul : ∀ (Y : Over S) (x y : Y ⟶ B), ptCls h Y (x * y) = ptCls h Y x + ptCls h Y y := by
    have hμ : ptCls h (B ⊗ B) μ[B] = ptCls h _ (fst B B) + ptCls h _ (snd B B) :=
      Equiv.ofBijective_apply_symm_apply (ptCls h (B ⊗ B)) (ptCls_bij h _) _
    intro Y x y
    rw [Hom.mul_def, ptCls_comp, hμ, map_add (f := _), ← ptCls_comp, ← ptCls_comp, lift_fst, lift_snd]
  have hone : ∀ (Y : Over S), ptCls h Y (1 : Y ⟶ B) = 0 := by
    have hη : ptCls h (𝟙_ (Over S)) η[B] = 0 :=
      Equiv.ofBijective_apply_symm_apply (ptCls h _) (ptCls_bij h _) 0
    intro Y
    rw [Hom.one_def, ptCls_comp, hη, map_zero]
  refine ⟨inferInstance, inferInstance, ⟨hP, h.fam.add, ?_, fun T M hM hA ↦ ?_⟩, ?_⟩
  · rw [triv_ev_iff hP, evc_eq_pull_ptCls h, hone, ZeroMemClass.coe_zero, map_zero]
  · obtain ⟨x, ⟨-, hx⟩, hu⟩ := h.univ T (toUnit T) M ⟨hM, hA⟩
    exact ⟨x, hx, fun y hy ↦ hu y ⟨toUnit_unique _ _, hy⟩⟩
  · have hs : (swap P).IsLB := pull_isLB hP _
    refine (isAdditive_iff hs).2 fun Y b b' a ↦ ?_
    rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs, evc_eq_pull_ptCls h, evc_eq_pull_ptCls h,
      evc_eq_pull_ptCls h, hmul, AddSubgroup.coe_add, map_add]

end GlobalTheory.DualCon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingAdditiveFamiliesIsDualCommStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representing_additiveFamilies_isDual_comm : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left), Rep A (toUnit B) P → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsDual A B P ∧ IsAdditive (swap P) := by
  first | exact @GlobalTheory.DualCon.rep_isDual | exact GlobalTheory.DualCon.rep_isDual | (intros; apply GlobalTheory.DualCon.rep_isDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLocallyConstantRelDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLocallyConstantRelDim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem abelianScheme_locally_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S,
    ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  intro S A _ hA s
  have := hA.smooth
  have := hA.geomConnected
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n :=
    (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have hsec : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  have he : ∀ t : S, A.hom (η[A].left t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, hsec]; rfl
  have fib : ∀ x, n x = n (η[A].left (A.hom x)) := fun x => by
    have hconn : _root_.IsPreconnected (A.hom ⁻¹' {A.hom x}) := by
      rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
      exact isPreconnected_univ.image _ (A.hom.fiberι _).continuous.continuousOn
    exact hc.apply_eq_of_isPreconnected hconn rfl (he (A.hom x))
  let x₀ : A.left := η[A].left s
  let U : S.Opens := η[A].left ⁻¹ᵁ W x₀
  have hsU : s ∈ U := hW x₀
  obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hsU
  refine ⟨V, n x₀, hV, hsV, ?_⟩
  have dimy : ∀ y, n (pullback.fst A.hom V.ι y) = n x₀ := fun y => by
    have h1 : A.hom (pullback.fst A.hom V.ι y) ∈ V := by
      have := congrArg (fun g => g y) (pullback.condition (f := A.hom) (g := V.ι))
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact (pullback.snd A.hom V.ι y).2
    rw [fib, loc _ _ (hVU h1)]
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀))
    (fun y => pullback.fst A.hom V.ι ⁻¹ᵁ W (pullback.fst A.hom V.ι y))
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW _⟩) fun y => ?_
  rw [← dimy y]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    ((isPullback_morphismRestrict (pullback.fst A.hom V.ι) (W _)).paste_vert (IsPullback.of_hasPullback _ _))
    (hd (pullback.fst A.hom V.ι y))

end GlobalTheory.DualCon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLocallyConstantRelDimStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_locally_constant_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S, ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  first | exact @GlobalTheory.DualCon.abelianScheme_locally_relDim | exact GlobalTheory.DualCon.abelianScheme_locally_relDim | (intros; apply GlobalTheory.DualCon.abelianScheme_locally_relDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimPreservedOfEqualLocalRelDims
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimPreservedOfEqualLocalRelDims
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

instance isZariskiLocalAtTarget_smoothDim (n : ℕ) : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension n) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))

theorem smoothDim_restrict_pullback {S T X : Scheme.{0}} (b : X ⟶ S) (t : T ⟶ S) (U : S.Opens) {n : ℕ}
    (h : SmoothOfRelativeDimension n (pullback.snd b U.ι)) :
    SmoothOfRelativeDimension n (pullback.snd b t ∣_ (t ⁻¹ᵁ U)) := by
  have big := (isPullback_morphismRestrict (pullback.snd b t) (t ⁻¹ᵁ U)).flip.paste_horiz
    (IsPullback.of_hasPullback b t)
  rw [← morphismRestrict_ι t U] at big
  have hc : ((pullback.snd b t ⁻¹ᵁ (t ⁻¹ᵁ U)).ι ≫ pullback.fst b t) ≫ b =
      (pullback.snd b t ∣_ (t ⁻¹ᵁ U) ≫ t ∣_ U) ≫ U.ι := by
    simp only [Category.assoc, pullback.condition, morphismRestrict_ι, morphismRestrict_ι_assoc]
  have sq := IsPullback.of_right (h₁₁ := pullback.lift _ _ hc) (by rw [pullback.lift_fst]; exact big)
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback b U.ι)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback sq h

theorem dimLe_of_local : ∀ (S : Scheme.{0}) (A B : Over S), Surjective A.hom → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd A.hom (V i).ι)) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd B.hom (V i).ι)) → DimLe A B := by
  intro S A B hs Ix V g hV hA hB n T t hn
  have hcov : iSup (fun i => t ⁻¹ᵁ V i) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, hi⟩ := hV (t y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) _ hcov fun i => ?_
  by_cases hne : ∃ y, y ∈ t ⁻¹ᵁ V i
  · obtain ⟨y, hy⟩ := hne
    have : Surjective (pullback.snd A.hom t) := by haveI := hs; infer_instance
    obtain ⟨x, hx⟩ := (pullback.snd A.hom t).surjective y
    have h1 : SmoothOfRelativeDimension n (pullback.snd A.hom t ∣_ (t ⁻¹ᵁ V i)) :=
      IsZariskiLocalAtTarget.restrict hn _
    have h2 := smoothDim_restrict_pullback A.hom t (V i) (hA i)
    have e : n = g i := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2
      ⟨x, by rw [Scheme.Hom.mem_preimage, hx]; exact hy⟩
    rw [e]
    exact smoothDim_restrict_pullback B.hom t (V i) (hB i)
  · push_neg at hne
    exact ⟨fun x => (hne _ x.2).elim⟩

end GlobalTheory.DualCon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimPreservedOfEqualLocalRelDimsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relDimPreserved_of_equal_local_relDims : ∀ (S : Scheme.{0}) (A B : Over S), Surjective A.hom → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd A.hom (V i).ι)) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd B.hom (V i).ι)) → DimLe A B := by
  first | exact @GlobalTheory.DualCon.dimLe_of_local | exact GlobalTheory.DualCon.dimLe_of_local | (intros; apply GlobalTheory.DualCon.dimLe_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemePoincare
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualExist

theorem hasRep_of_iso {S : Scheme.{0}} {A : Over S} [GrpObj A] {g : ℕ} {S₁ S₂ : Over S} (e : S₁ ≅ S₂)
    (h : HasRep A g S₁) : HasRep A g S₂ := by
  obtain ⟨B, b, P, hR, hG⟩ := h
  refine ⟨B, b ≫ e.hom, P, ⟨hR.fam, fun T t N hN => ?_⟩, ?_⟩
  · obtain ⟨x, ⟨hx, hxN⟩, hu⟩ := hR.univ T (t ≫ e.inv) N hN
    refine ⟨x, ⟨by rw [← Category.assoc, hx, Category.assoc, e.inv_hom_id, Category.comp_id], hxN⟩,
      fun y ⟨hy, hyN⟩ => hu y ⟨?_, hyN⟩⟩
    rw [← hy, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
  · have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).mapIso e).inv)
    have sq : IsPullback (𝟙 B.left) (b.left ≫ e.hom.left) b.left e.inv.left :=
      IsPullback.of_horiz_isIso ⟨by
        rw [Category.id_comp, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.comp_id]⟩
    have hp := hG.proper
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    rw [Over.comp_left]
    exact ⟨MorphismProperty.of_isPullback (P := @IsProper) sq hp, MorphismProperty.of_isPullback sq hG.smooth,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq hG.conn⟩

theorem hasRep_affineOpen {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {V : S.Opens}
    (hV : IsAffineOpen V) (g : ℕ) (hg : SmoothOfRelativeDimension g (pullback.snd A.hom V.ι)) :
    HasRep A g (Over.mk V.ι) := by
  let A' : Over (Sp Γ(S, V)) := (Over.pullback hV.fromSpec).obj A
  letI : GrpObj A' := Functor.grpObjObj
  have hpb : IsGrpPullback A' A hV.fromSpec (pullback.fst A.hom hV.fromSpec) :=
    isGrpPullback_pullback A hV.fromSpec
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb
  have hg' : SmoothOfRelativeDimension g A'.hom := by
    have sq : IsPullback (pullback.lift (pullback.fst A.hom hV.fromSpec)
        (pullback.snd A.hom hV.fromSpec ≫ hV.isoSpec.inv)
        (by rw [pullback.condition, Category.assoc, IsAffineOpen.isoSpec_inv_ι]))
        (pullback.snd A.hom hV.fromSpec) (pullback.snd A.hom V.ι) hV.isoSpec.inv :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact IsPullback.of_hasPullback A.hom hV.fromSpec)
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback A.hom V.ι)
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback sq hg
  have h1 := ((GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ hV.fromSpec A A' _ hpb g (𝟙_ _)).1).1 (GlobalTheory.T.abelianScheme_dual_representable_affine_base _ A' g hA' hg')
  refine hasRep_of_iso (Over.isoMk hV.isoSpec.symm ?_) h1
  show hV.isoSpec.inv ≫ V.ι = 𝟙 _ ≫ hV.fromSpec
  rw [Category.id_comp, IsAffineOpen.isoSpec_inv_ι]

theorem exists_dual : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧ DimLe A B ∧ IsDual A B P := by
  intro S A _ hA
  choose V g hV hsV hgV using GlobalTheory.T.abelianScheme_locally_constant_relDim S A hA
  have cov : ∀ s : S, ∃ i, s ∈ V i := fun s => ⟨s, hsV s⟩
  obtain ⟨B, P, hR, hGood⟩ :=
    GlobalTheory.T.exists_additiveFamily_representative_zariski_glue S A hA S V g cov (fun i => hasRep_affineOpen A hA (hV i) (g i) (hgV i))
  obtain ⟨inst, hcomm, hD, -⟩ := GlobalTheory.T.representing_additiveFamilies_isDual_comm S A B P hR
  refine ⟨B, inst, P, ?_, ?_, hD⟩
  · have hU : iSup V = ⊤ := eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsV s⟩
    have : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
      rw [GeometricallyConnected.eq_geometrically]; infer_instance
    have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
    have sq := fun i => IsPullback.of_hasPullback B.hom (V i).ι
    exact
      { comm := hcomm
        smooth := GlobalTheory.CoverGlue.of_isPullback_cover @Smooth hU sq fun i => by
          haveI := (hGood i).smooth; exact SmoothOfRelativeDimension.smooth (g i) _
        proper := GlobalTheory.CoverGlue.of_isPullback_cover @IsProper hU sq fun i => (hGood i).proper
        geomConnected := GlobalTheory.CoverGlue.of_isPullback_cover @GeometricallyConnected hU sq fun i => (hGood i).conn }
  · have : GeometricallyConnected A.hom := hA.geomConnected
    exact GlobalTheory.T.relDimPreserved_of_equal_local_relDims S A B inferInstance S V g cov hgV fun i => (hGood i).smooth

end GlobalTheory.DualExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemePoincareStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_abelianScheme_poincare : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧ DimLe A B ∧ IsDual A B P := by
  first | exact @GlobalTheory.DualExist.exists_dual | exact GlobalTheory.DualExist.exists_dual | (intros; apply GlobalTheory.DualExist.exists_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualAbelianSchemePoincareSwap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPoincareLeftKernelTrivialAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyTrivialOfQuotientPullbackTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyTrivialOfQuotientPullbackTrivial
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualInjPull

theorem smooth_of_dimLe {S : Scheme.{0}} {A C : Over S} (h : DimLe A C) {g : ℕ}
    (hA : SmoothOfRelativeDimension g A.hom) : SmoothOfRelativeDimension g C.hom := by
  have h1 : SmoothOfRelativeDimension g (pullback.snd A.hom (𝟙 S)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom (𝟙 S)) hA
  have h2 := h g S (𝟙 S) h1
  have sq : IsPullback (inv (pullback.fst C.hom (𝟙 S))) C.hom (pullback.snd C.hom (𝟙 S)) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [IsIso.inv_comp_eq, Category.comp_id, pullback.condition, Category.comp_id]⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback sq h2

theorem isIso_of_mono' {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B)
    (hB' : IsAbelianScheme B') {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    (hg' : SmoothOfRelativeDimension g B'.hom) (x : B ⟶ B') [Mono x] : IsIso x := by
  have := hB.proper
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : IsIso x.left :=
    GlobalTheory.AbMonoIsoAny.isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) le_rfl
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

theorem evc_of_iso {S : Scheme.{0}} {A T X U Y : Over S} {M : LB (A ⊗ T).left} {N : LB (X ⊗ U).left}
    (hM : M.IsLB) (hN : N.IsLB) (f : A ⊗ T ⟶ X) (g : A ⊗ T ⟶ U) (e : LBIso M (ev N f g))
    (a : Y ⟶ A) (t : Y ⟶ T) : evc hM a t = evc hN (lift a t ≫ f) (lift a t ≫ g) := by
  have c : cls M hM = cls _ (pull_isLB hN _) := (cls_eq_iff hM (pull_isLB hN _)).2 e
  rw [← evc_ev hN f g (pull_isLB hN _) a t, evc, evc, c]

theorem triv_of_triv_pull : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left) (P' : LB (A' ⊗ B).left) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → IsMonHom q → P'.IsLB → IsAdditive P' → LBIso (ev P' (fst A B ≫ q) (snd A B)) P → ∀ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB → IsAdditive M → Triv (ev M (fst A T ≫ q) (snd A T)) → Triv M := by
  intro K _ _ A A' B _ _ _ g P P' q hA hA' hB hgA' hgB hD hq hP' haP' eP T M hM haM hT
  obtain ⟨C, _, Q, hC, hdim, hQ⟩ := GlobalTheory.T.exists_dual_abelianScheme_poincare _ A' hA'
  have hgC : SmoothOfRelativeDimension g C.hom := smooth_of_dimLe hdim hgA'
  have hP := hD.isLB
  have hQl := hQ.isLB
  have hR : (ev Q (fst A C ≫ q) (snd A C)).IsLB := pull_isLB hQl _
  have haR : IsAdditive (ev Q (fst A C ≫ q) (snd A C)) := by
    refine (isAdditive_iff hR).2 fun Y a a' t ↦ ?_
    rw [evc_ev hQl, evc_ev hQl, evc_ev hQl]
    simp only [lift_fst_assoc, lift_snd, MonObj.mul_comp]
    exact (isAdditive_iff hQl).1 hQ.additive Y _ _ t
  obtain ⟨s, hs, -⟩ := hQ.univ B P' hP' haP'
  obtain ⟨r, hr, -⟩ := hD.univ C _ hR haR
  have hsr : s ≫ r = 𝟙 B := by
    refine GlobalTheory.AbDual.IsDual.eq_of_evc hD ?_
    have e1 := evc_of_iso hR hP _ _ hr (fst A B) (snd A B ≫ s)
    have e1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A B) (snd A B ≫ s)
    have e2 := evc_of_iso hP' hQl _ _ hs (fst A B ≫ q) (snd A B)
    have e3 : evc hP' (fst A B ≫ q) (snd A B) = evc hP (fst A B) (snd A B) := by
      rw [← cls_ev hP' _ _ (pull_isLB hP' _), (cls_eq_iff _ hP).2 eP, evc, lift_fst_snd, Over.id_left, pull_id]
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at e1 e1' e2
    rw [Category.comp_id, ← e3, e2, ← e1', e1]
  obtain ⟨c, hc, -⟩ := hQ.univ T M hM haM
  have hcr : c ≫ r = 1 := hD.eq_one _ ((triv_ev_iff hP _ _).2 (by
    have f1 := evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ c)
    have f1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ c)
    have f2 := evc_of_iso hM hQl _ _ hc (fst A T ≫ q) (snd A T)
    have f3 := (triv_ev_iff hM _ _).1 hT
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1' f2
    rw [← f1, f1', ← f2, f3]))
  have h1r : (1 : T ⟶ C) ≫ r = 1 := hD.eq_one _ ((triv_ev_iff hP _ _).2 (by
    have f1 := evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ (1 : T ⟶ C))
    have f1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ (1 : T ⟶ C))
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1'
    rw [← f1, f1', MonObj.comp_one, evc_one_right hQl hQ.zero]))
  haveI : IsSplitMono s := IsSplitMono.mk' ⟨r, hsr⟩
  haveI : IsIso s := isIso_of_mono' hB hC hgB hgC s
  have hrinv : r = inv s := (IsIso.inv_eq_of_hom_inv_id hsr).symm
  haveI : IsIso r := by rw [hrinv]; infer_instance
  have hc1 : c = 1 := (cancel_mono r).1 (hcr.trans h1r.symm)
  refine (cls_eq_zero_iff hM).1 ?_
  rw [(cls_eq_iff hM (pull_isLB hQl _)).2 hc, cls_ev hQl, hc1, MonObj.comp_one, evc_one_right hQl hQ.zero]
end GlobalTheory.DualInjPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyTrivialOfQuotientPullbackTrivialStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveFamily_trivial_of_quotient_pullback_trivial : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left) (P' : LB (A' ⊗ B).left) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → IsMonHom q → P'.IsLB → IsAdditive P' → LBIso (ev P' (fst A B ≫ q) (snd A B)) P → ∀ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB → IsAdditive M → Triv (ev M (fst A T ≫ q) (snd A T)) → Triv M := by
  first | exact @GlobalTheory.DualInjPull.triv_of_triv_pull | exact GlobalTheory.DualInjPull.triv_of_triv_pull | (intros; apply GlobalTheory.DualInjPull.triv_of_triv_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubgroupSchemePoincareLeftKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubgroupSchemePoincareLeftKernel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualKernel

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem evc_ker_iff {P : LB (A ⊗ B).left} (hP : P.IsLB) {T : Over S} (x : T ⟶ A) :
    evc hP (fst T B ≫ x) (snd T B) = 0 ↔ evc hP (snd B T ≫ x) (fst B T) = 0 := by
  constructor
  · intro h
    have e := congrArg (CechPic.pull (lift (snd B T) (fst B T)).left) h
    rwa [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e
  · intro h
    have e := congrArg (CechPic.pull (lift (snd T B) (fst T B)).left) h
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e

theorem evc_ker_mul {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) {T : Over S} (x y : T ⟶ A)
    (hx : evc hP (fst T B ≫ x) (snd T B) = 0) (hy : evc hP (fst T B ≫ y) (snd T B) = 0) :
    evc hP (fst T B ≫ (x * y)) (snd T B) = 0 := by
  rw [MonObj.comp_mul, (isAdditive_iff hP).1 hA, hx, hy, add_zero]

theorem evc_ker_one {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) (T : Over S) :
    evc hP (fst T B ≫ (1 : T ⟶ A)) (snd T B) = 0 := by
  rw [MonObj.comp_one]
  exact hA.evc_one hP _

theorem evc_ker_inv {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) {T : Over S} (x : T ⟶ A)
    (hx : evc hP (fst T B ≫ x) (snd T B) = 0) : evc hP (fst T B ≫ x⁻¹) (snd T B) = 0 := by
  have e := evc_ker_one hP hA T
  rw [← mul_inv_cancel x, MonObj.comp_mul, (isAdditive_iff hP).1 hA, hx, zero_add] at e
  exact e

end GlobalTheory.DualKernel

namespace GlobalTheory.DualKernel

theorem exists_closed_subgroup_ker : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P →
    ∃ (N : Over (Sp K)) (_ : GrpObj N) (i : N ⟶ A), IsMonHom i ∧ IsClosedImmersion i.left ∧
      Triv (ev P (fst N B ≫ i) (snd N B)) ∧
      ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → ∃ z : T ⟶ N, z ≫ i = x := by
  intro K _ _ A B _ _ P hA hB hD
  have hP := hD.isLB
  have hs : (swap P).IsLB := pull_isLB hP _
  have ht : (LB.triv (B ⊗ A).left).IsLB := LB.isLB_triv _
  have h0 : ∀ (Y : Over (Sp K)) (b : Y ⟶ B) (a : Y ⟶ A), evc ht b a = 0 := fun _ _ _ ↦ map_zero _
  have hN : Fam B (swap P) := ⟨hs, isDual_isAdditive_swap _ A B P hB hD⟩
  have hN' : Fam B (LB.triv (B ⊗ A).left) :=
    ⟨ht, (isAdditive_iff ht).2 fun _ _ _ _ ↦ by simp only [h0, add_zero]⟩
  haveI := hA.smooth
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨N, i, hi, hG⟩ := GlobalTheory.DualLocus.exists_closed_same (Sp K) B A hB (swap P) _ hN hN'
  have key : ∀ (T : Over (Sp K)) (x : T ⟶ A),
      evc hP (fst T B ≫ x) (snd T B) = 0 ↔ ∃ z : T ⟶ N, z ≫ i = x := fun T x ↦ by
    rw [← hG, same_iff hs ht, h0, evc_swap hP hs, evc_ker_iff]
  have hK : ∀ (T : Over (Sp K)) (z : T ⟶ N), evc hP (fst T B ≫ z ≫ i) (snd T B) = 0 :=
    fun T z ↦ (key T _).2 ⟨z, rfl⟩
  haveI : Mono i.left := inferInstance
  haveI : Mono i := Over.mono_of_mono_left i
  have hl : ∀ {T : Over (Sp K)} (x : T ⟶ A), evc hP (fst T B ≫ x) (snd T B) = 0 →
      ∃ z : T ⟶ N, z ≫ i = x := fun x h ↦ (key _ x).1 h
  obtain ⟨o, ho⟩ := hl (η[A] : 𝟙_ (Over (Sp K)) ⟶ A) (by
    have e := evc_ker_one hP hD.additive (𝟙_ (Over (Sp K)))
    rwa [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp] at e)
  obtain ⟨m, hm⟩ := hl ((i ⊗ₘ i) ≫ μ[A]) (by
    have e := evc_ker_mul hP hD.additive (fst N N ≫ i) (snd N N ≫ i) (hK _ _) (hK _ _)
    rwa [Hom.mul_def, ← lift_map_assoc, lift_fst_snd, Category.id_comp] at e)
  obtain ⟨n, hn⟩ := hl (i ≫ GrpObj.inv) (by
    have e := evc_ker_inv hP hD.additive i (by simpa using hK N (𝟙 N))
    rwa [Hom.inv_def] at e)
  obtain ⟨g, hg⟩ := GlobalTheory.exists_grpObj_of_mono i o m n ho hm hn
  refine ⟨N, g, i, hg, hi, (triv_ev_iff hP _ _).2 (by simpa using hK N (𝟙 N)), fun T x hx ↦ ?_⟩
  exact (key T x).1 ((triv_ev_iff hP _ _).1 hx)

end GlobalTheory.DualKernel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubgroupSchemePoincareLeftKernelStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubgroupScheme_poincare_left_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → ∃ (N : Over (Sp K)) (_ : GrpObj N) (i : N ⟶ A), IsMonHom i ∧ IsClosedImmersion i.left ∧ Triv (ev P (fst N B ≫ i) (snd N B)) ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → ∃ z : T ⟶ N, z ≫ i = x := by
  first | exact @GlobalTheory.DualKernel.exists_closed_subgroup_ker | exact GlobalTheory.DualKernel.exists_closed_subgroup_ker | (intros; apply GlobalTheory.DualKernel.exists_closed_subgroup_ker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfLineBundleOfDualPairLeftTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfLineBundleOfDualPairLeftTrivial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbDual

theorem memKL_of_triv_ev_left : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left) (L : LB A.left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → L.IsLB →
    ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → GlobalTheory.MemKL A L x := by
  intro K _ _ A B _ _ P L hA _ hD hL T x hx
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have hadd := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  obtain ⟨φ, hφ, -⟩ := hD.univ A (abelian₂ A L) hP hadd
  have hc : cls _ hP = evc hD.isLB (fst A A) (snd A A ≫ φ) :=
    (cls_eq_iff hP (pull_isLB hD.isLB _)).2 hφ
  have hx0 : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
    have e₁ := congrArg (CechPic.pull (lift (fst T A) (snd T A ≫ φ)).left) ((triv_ev_iff hD.isLB _ _).1 hx)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e₁
    rw [← e, evc, hc, pull_evc, lift_fst, lift_snd_assoc]
    exact e₁
  have hD' : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfLineBundleOfDualPairLeftTrivialStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_kernelOfLineBundle_of_dualPair_left_trivial : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (L : LB A.left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → L.IsLB → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → GlobalTheory.MemKL A L x := by
  first | exact @GlobalTheory.AbDual.memKL_of_triv_ev_left | exact GlobalTheory.AbDual.memKL_of_triv_ev_left | (intros; apply GlobalTheory.AbDual.memKL_of_triv_ev_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionFiniteSurjectiveAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionFiniteSurjectiveAbelian
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjDimField

theorem smoothOfRelativeDimension_of_finite_surjective : ∀ (K : Type) [Field K] [IsAlgClosed K]
    (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (g : ℕ) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' →
    IsFinite q.left → Surjective q.left → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g A'.hom := by
  intro K _ _ A A' _ _ g q hA hA' hfin hsurj hg
  have := hA.geomConnected
  have := hA'.geomConnected
  have := hA'.smooth
  have : ConnectedSpace A.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A.hom) (𝟙 _) (𝟙 _) A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have : ConnectedSpace A'.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A'.hom) (𝟙 _) (𝟙 _) A'.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected A'.hom (Classical.arbitrary A'.left)
  have hw : q.left ≫ A'.hom = A.hom := Over.w q
  have hg' : SmoothOfRelativeDimension g (q.left ≫ A'.hom) := by rw [hw]; exact hg
  have e := GlobalTheory.FiniteSurjDim.eq_of_finite_surjective (k := K) q.left A'.hom hg' hm
  subst e
  exact hm

end GlobalTheory.FiniteSurjDimField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionFiniteSurjectiveAbelianStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_finite_surjective_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (g : ℕ) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsFinite q.left → Surjective q.left → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A'.hom := by
  first | exact @GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective | exact GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective | (intros; apply GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPoincareLeftKernelTrivialAlgClosed
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualKer

theorem finite_of_factor {K : Type} [Field K] {N A H : Over (Sp K)} (i : N ⟶ A) (j : H ⟶ A) (z : N ⟶ H)
    (hz : z ≫ j = i) (hi : IsClosedImmersion i.left) (hj : IsClosedImmersion j.left) (hH : IsFinite H.hom) :
    IsFinite N.hom := by
  have e : z.left ≫ j.left = i.left := by rw [← Over.comp_left, hz]
  haveI : IsClosedImmersion (z.left ≫ j.left) := e ▸ hi
  haveI : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left j.left
  have : N.hom = z.left ≫ H.hom := (Over.w z).symm
  rw [this]; infer_instance

theorem leftKer_eq_one : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → x = 1 := by
  intro K _ _ A B _ _ g P hA hB hgA hgB hP T x hx
  obtain ⟨N, _, i, hi, hci, hNt, hfac⟩ := GlobalTheory.T.exists_closedSubgroupScheme_poincare_left_kernel K A B P hA hB hP
  obtain ⟨L, H, _, j, hL, -, -, -, hcj, hH, hKL⟩ := GlobalTheory.T.exists_ample_kernel_finite_subgroupScheme K A hA
  obtain ⟨z, hz⟩ := (hKL N i).1 (GlobalTheory.T.mem_kernelOfLineBundle_of_dualPair_left_trivial K A B P L hA hB hP hL N i hNt)
  have hfin : IsFinite N.hom := finite_of_factor i j z hz hci hcj hH
  haveI : Mono i.left := inferInstance
  have hmono : Mono i := (Over.forget _).mono_of_mono_map (by simpa using (inferInstance : Mono i.left))
  obtain ⟨A', _, hA', q, hq, hqf, hqfl, hqs, hpb⟩ := GlobalTheory.T.exists_quotient_abelianVariety_finite_subgroupScheme K A hA N i hi hmono hfin
  have hgA' := GlobalTheory.T.smoothOfRelativeDimension_finite_surjective_abelianVariety K A A' g q hA hA' hqf hqs hgA
  obtain ⟨P', hP', hP'a, hP'i⟩ := GlobalTheory.T.poincareBundle_descends_quotient_finiteSubgroup K A A' B N P i q hA hA' hB hP hi hq hqf hqfl hqs hpb hNt
  have hi1 : i = 1 := by
    by_contra hne
    obtain ⟨T', M, hM, hMa, hMq, hMn⟩ := GlobalTheory.T.exists_nontrivial_additive_family_killed_by_isogeny K A A' N i q hA hA' hi hq hfin hqf hqfl hqs hpb hne
    exact hMn (GlobalTheory.T.additiveFamily_trivial_of_quotient_pullback_trivial K A A' B g P P' q hA hA' hB hgA' hgB hP hq hP' hP'a hP'i T' M hM hMa hMq)
  obtain ⟨w, rfl⟩ := hfac T x hx
  rw [hi1, MonObj.comp_one]

end GlobalTheory.DualKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPoincareLeftKernelTrivialAlgClosedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualPoincare_left_kernel_trivial_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → x = 1 := by
  first | exact @GlobalTheory.DualKer.leftKer_eq_one | exact GlobalTheory.DualKer.leftKer_eq_one | (intros; apply GlobalTheory.DualKer.leftKer_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualAbelianSchemePoincareSwap
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BidualAbelian

theorem isAdditive_swap_swap {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left}
    (hP : P.IsLB) (h : IsAdditive P) : IsAdditive (swap (swap P)) := by
  have hs : (swap P).IsLB := pull_isLB hP _
  have hss : (swap (swap P)).IsLB := pull_isLB hs _
  refine (isAdditive_iff hss).2 fun Y a a' t ↦ ?_
  rw [evc_swap hs hss, evc_swap hs hss, evc_swap hs hss, evc_swap hP hs, evc_swap hP hs, evc_swap hP hs]
  exact (isAdditive_iff hP).1 h Y a a' t

set_option synthInstance.maxHeartbeats 400000 in
theorem fibre_isIso : ∀ (S : Scheme.{0}) (A B C : Over S) [GrpObj A] [GrpObj B] [GrpObj C] (P : LB (A ⊗ B).left)
    (Q : LB (B ⊗ C).left) (κ : A ⟶ C), IsAbelianScheme A → IsAbelianScheme B → IsAbelianScheme C → DimLe A B →
    DimLe B C → IsDual A B P → IsDual B C Q → IsMonHom κ → LBIso (swap P) (ev Q (fst B A) (snd B A ≫ κ)) →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso ((Over.pullback t).map κ) := by
  intro S A B C _ _ _ P Q κ hA hB hC hAB hBC hd hQ hm e Ω _ _ t
  have hA' := GlobalTheory.IsoOverField.isAbelianScheme_pullback t A hA
  have hB' := GlobalTheory.IsoOverField.isAbelianScheme_pullback t B hB
  have hC' := GlobalTheory.IsoOverField.isAbelianScheme_pullback t C hC
  obtain ⟨g, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim Ω ((Over.pullback t).obj A) hA'
  have hgB : SmoothOfRelativeDimension g ((Over.pullback t).obj B).hom := hAB g (Sp Ω) t hgA
  have hgC : SmoothOfRelativeDimension g ((Over.pullback t).obj C).hom := hBC g (Sp Ω) t hgB
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback t).map a).left ≫ pullback.fst Y.hom t = pullback.fst X.hom t ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback t).obj A ⊗ (Over.pullback t).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback t) A B).left ≫ pullback.fst (A ⊗ B).hom t
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback t).obj A) ((Over.pullback t).obj B)).left ≫
      pullback.fst A.hom t := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback t) A B ≫ (Over.pullback t).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback t).obj A) ((Over.pullback t).obj B)).left ≫
      pullback.fst B.hom t := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback t) A B ≫ (Over.pullback t).map (snd A B) = snd _ _ by simp]
  have hP' : (P.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual _ _ (P.pull h) := IsDual.baseChange (isGrpPullback_pullback A t) (isGrpPullback_pullback B t)
    h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have ker := GlobalTheory.T.dualPoincare_left_kernel_trivial_algClosed Ω _ _ g (P.pull h) hA' hB' hgA hgB hd'
  have hs : (swap P).IsLB := pull_isLB hd.isLB _
  have hE : (ev Q (fst B A) (snd B A ≫ κ)).IsLB := pull_isLB hQ.isLB _
  have ce : cls _ hs = cls _ hE := (cls_eq_iff hs hE).2 e
  have mono : Mono ((Over.pullback t).map κ) := by
    constructor
    intro T x y hxy
    have z1 : (x * y⁻¹) ≫ (Over.pullback t).map κ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
    have tr : Triv (ev (P.pull h) (fst T ((Over.pullback t).obj B) ≫ (x * y⁻¹)) (snd T ((Over.pullback t).obj B))) := by
      refine (triv_ev_iff hP' _ _).2 ?_
      let a : Over.mk (T ⊗ (Over.pullback t).obj B).hom ⟶ (Over.pullback t).obj A :=
        fst T ((Over.pullback t).obj B) ≫ (x * y⁻¹)
      let b : Over.mk (T ⊗ (Over.pullback t).obj B).hom ⟶ (Over.pullback t).obj B := snd T _
      let a₀ := pushP (isGrpPullback_pullback A t) (s₀ := (T ⊗ (Over.pullback t).obj B).hom ≫ t) rfl a
      let b₀ := pushP (isGrpPullback_pullback B t) (s₀ := (T ⊗ (Over.pullback t).obj B).hom ≫ t) rfl b
      have e1 : evc hP' a b = evc hd.isLB a₀ b₀ := evc_eq h₁ h₂ hd.isLB hP' ((cls_eq_iff hP' hP').1 rfl) a b a₀ b₀ rfl rfl
      refine e1.trans ?_
      have one : a₀ ≫ κ = 1 := by
        apply Over.OverMorphism.ext
        rw [Over.comp_left]
        show (a.left ≫ pullback.fst A.hom t) ≫ κ.left = _
        rw [Category.assoc, ← key, ← Category.assoc, ← Over.comp_left]
        show (fst T ((Over.pullback t).obj B) ≫ (x * y⁻¹) ≫ (Over.pullback t).map κ).left ≫ _ = _
        rw [z1, MonObj.comp_one]
        exact one_left_comp (isGrpPullback_pullback C t) rfl
      have e2 : evc hs b₀ a₀ = evc hE b₀ a₀ := by unfold evc; rw [ce]
      rw [← evc_swap hd.isLB hs, e2, evc_ev hQ.isLB, lift_fst, lift_snd_assoc, one, evc_one_right hQ.isLB hQ.zero]
    have hz := ker T (x * y⁻¹) tr
    calc x = x * y⁻¹ * y := (inv_mul_cancel_right x y).symm
      _ = y := by rw [hz, _root_.one_mul]
  exact GlobalTheory.AbMonoIso.isIso_of_mono (Sp Ω) _ _ hA' hC' g g hgA hgC le_rfl _ inferInstance mono

theorem isDual_swap : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left),
    IsAbelianScheme A → IsAbelianScheme B → DimLe A B → IsDual A B P → IsDual B A (swap P) := by
  intro S A B _ _ P hA hB hAB hd
  obtain ⟨C, _, Q, hC, hBC, hQ⟩ := GlobalTheory.T.exists_dual_abelianScheme_poincare S B hB
  have hs : (swap P).IsLB := pull_isLB hd.isLB _
  have ha : IsAdditive (swap P) := isDual_isAdditive_swap S A B P hB hd
  obtain ⟨κ, e, -⟩ := hQ.univ A (swap P) hs ha
  have hm : IsMonHom κ := isMonHom_of_classifying S B A C (swap P) Q hQ
    (isDual_isAdditive_swap S B C Q hC hQ) hs (isAdditive_swap_swap hd.isLB hd.additive) κ e
  have hi : IsIso κ := isIso_of_isIso_pullback hA hC κ fun Ω _ _ t ↦
    fibre_isIso S A B C P Q κ hA hB hC hAB hBC hd hQ hm e Ω t
  exact transport S B A C (swap P) Q hQ hs κ hi hm e

end GlobalTheory.BidualAbelian
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualAbelianSchemePoincareSwapStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDualAbelianSchemePoincare_swap : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → DimLe A B → IsDual A B P → IsDual B A (swap P) := by
  first | exact @GlobalTheory.BidualAbelian.isDual_swap | exact GlobalTheory.BidualAbelian.isDual_swap | (intros; apply GlobalTheory.BidualAbelian.isDual_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smoothOfRelDim_of_pullback_snd_identity {S : Scheme.{0}} (X : Over S) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd X.hom (𝟙 S))) : SmoothOfRelativeDimension g X.hom := by
  have e : X.hom = inv (pullback.fst X.hom (𝟙 S)) ≫ pullback.snd X.hom (𝟙 S) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  have := smoothOfRelativeDimension_comp (n := 0) (m := g) (inv (pullback.fst X.hom (𝟙 S))) (pullback.snd X.hom (𝟙 S))
  simpa using this

theorem smoothOfRelDim_pullback_snd_identity {S : Scheme.{0}} (X : Over S) (g : ℕ)
    (h : SmoothOfRelativeDimension g X.hom) : SmoothOfRelativeDimension g (pullback.snd X.hom (𝟙 S)) := by
  have e : pullback.snd X.hom (𝟙 S) = pullback.fst X.hom (𝟙 S) ≫ X.hom := by
    rw [pullback.condition, Category.comp_id]
  rw [e]
  have := smoothOfRelativeDimension_comp (n := 0) (m := g) (pullback.fst X.hom (𝟙 S)) X.hom
  simpa using this

theorem dualAbelianScheme : GlobalTheory.Published.DualAbelianScheme := by
  intro S A _ hA
  obtain ⟨B, _, P, hB, hdim, hdual⟩ := GlobalTheory.T.exists_dual_abelianScheme_poincare S A hA
  refine ⟨B, inferInstance, P, hB, fun g hg => ?_, hdual, GlobalTheory.T.isDualAbelianSchemePoincare_swap S A B P hA hB hdim hdual⟩
  exact smoothOfRelDim_of_pullback_snd_identity B g (hdim g S (𝟙 S) (smoothOfRelDim_pullback_snd_identity A g hg))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBidualityStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualAbelianScheme_exists_biduality : GlobalTheory.Published.DualAbelianScheme := by
  first | exact @GlobalTheory.dualAbelianScheme | exact GlobalTheory.dualAbelianScheme | (intros; apply GlobalTheory.dualAbelianScheme <;> assumption)
end
