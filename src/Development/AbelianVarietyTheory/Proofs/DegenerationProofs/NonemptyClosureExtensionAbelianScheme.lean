module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMulRegularAndUnitAlongTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByWeightZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyClosureExtensionAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyClosureExtensionAbelianScheme
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosureLifting

theorem exists_lift {Z Y : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (j : Y ⟶ Z) [IsOpenImmersion j] [Nonempty Y] :
    ∃ x : Sp K ⟶ Y, x ≫ j = gp := by
  have hr : Set.range gp ⊆ Set.range j := by
    rw [hgp, Set.singleton_subset_iff]
    exact (genericPoint_specializes (j (Classical.arbitrary Y))).mem_open
      j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  exact ⟨_, IsOpenImmersion.lift_fac j gp hr⟩

theorem flat_of_charZero {Z : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] [CharZero K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (π : Z ⟶ Sp ℤ) : Flat π := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) Z.affineOpenCover.openCover fun i => ?_
  let R := Z.affineOpenCover.X i
  let j : Spec R ⟶ Z := Z.affineOpenCover.f i
  have : IsOpenImmersion j := Z.affineOpenCover.map_prop i
  change Flat (j ≫ π)
  rcases isEmpty_or_nonempty (Spec R) with h | h
  · infer_instance
  obtain ⟨x, -⟩ := exists_lift gp hgp j
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 this
  have : CharZero R := (Spec.preimage x).hom.charZero
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Flat)]
  have e : φ.hom = algebraMap ℤ R := RingHom.ext_int _ _
  rw [e, RingHom.flat_algebraMap_iff]
  infer_instance

theorem exists_section_of_local {Z G : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (q : G ⟶ Z) [IsSeparated q] (ξ : Sp K ⟶ G)
    (H : ∀ z : Z, ∃ (W : Z.Opens) (h : W.toScheme ⟶ G), z ∈ W ∧ h ≫ q = W.ι ∧
      ∀ x : Sp K ⟶ W.toScheme, x ≫ W.ι = gp → x ≫ h = ξ) :
    ∃ e : Z ⟶ G, e ≫ q = 𝟙 Z ∧ gp ≫ e = ξ := by
  choose W h hz hq hξ using H
  have hd : IsDominant gp := ⟨by
    rw [DenseRange, hgp, dense_iff_closure_eq]
    exact genericPoint_spec Z⟩
  have hx : ∀ z, ∃ x : Sp K ⟶ (W z).toScheme, x ≫ (W z).ι = gp := fun z =>
    have : Nonempty (W z).toScheme := ⟨⟨z, hz z⟩⟩
    exists_lift gp hgp _
  choose x hx using hx
  have hW : TopologicalSpace.IsOpenCover W :=
    top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hz z⟩
  let 𝒰 := Z.openCoverOfIsOpenCover W hW
  have hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ h a = pullback.snd (W a).ι (W b).ι ≫ h b := by
    intro a b
    let m : Sp K ⟶ pullback (W a).ι (W b).ι := pullback.lift (x a) (x b) ((hx a).trans (hx b).symm)
    have e : m ≫ pullback.fst _ _ ≫ (W a).ι = gp := by rw [pullback.lift_fst_assoc, hx]
    have : IsDominant (m ≫ pullback.fst _ _ ≫ (W a).ι) := e ▸ hd
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ (W a).ι)
    have : IsReduced (pullback (W a).ι (W b).ι) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)
    refine ext_of_isDominant_of_isSeparated q ?_ m ?_
    · rw [Category.assoc, Category.assoc, hq, hq, pullback.condition]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hξ _ _ (hx a), hξ _ _ (hx b)]
  have he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms h hc = h a := fun a => 𝒰.ι_glueMorphisms h hc a
  refine ⟨𝒰.glueMorphisms h hc, 𝒰.hom_ext _ _ fun (a : Z) => ?_, ?_⟩
  · change (W a).ι ≫ _ = (W a).ι ≫ _
    rw [← Category.assoc, he, hq, Category.comp_id]
  · rw [← hx (genericPoint Z), Category.assoc, he, hξ _ _ (hx _)]

theorem eSec_fst {B B' : Scheme.{0}} (u : B' ⟶ B) (A : Over B) [GrpObj A] :
    eSec ((Over.pullback u).obj A) ≫ pullback.fst A.hom u = u ≫ eSec A := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem proj_zero_of_eq_bot {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

theorem exists_crd_ne_zero [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (ρ : S.Real) {K : Type} [Field K]
    (y : Sp K ⟶ ρ.P.A.left) : ∃ v i, ρ.Crd y v ∧ v i ≠ 0 := by
  let y' : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left :=
    pullback.lift (f := (baseOver (Sp S.R)).hom) (g := ρ.P.A.hom) (y ≫ ρ.P.A.hom) y (Category.comp_id _)
  have hM : (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).IsLB := LB.isLB_linComb ρ.P.isLB _ _
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists hM ρ.s y'
  have hm : y' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (ρ.s i) := by
    rw [(ThetaSys.Real.immBy_basis hL o Ω S ρ).1]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  exact ⟨v, i, ⟨y', pullback.lift_snd _ _ _, hv⟩,
    ((CrdCalc.crd_isUnit_iff i hv).2 ((CrdCalc.top_le_iff y' _).2 hi)).ne_zero⟩

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem range_subset [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) :
    Set.range Q.a₀ ⊆ Set.range Q.G.ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨K, _, x, rfl⟩ : ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ pullback ρ.P.A.hom Q.u₀),
      x (IsLocalRing.closedPoint K) = w :=
    ⟨_, inferInstance, Scheme.fromSpecResidueField _ w, Scheme.fromSpecResidueField_apply w _⟩
  obtain ⟨v, i, hv, hi⟩ := exists_crd_ne_zero hL ρ (x ≫ pullback.fst _ _)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((x ≫ Q.a₀) ≫ Q.P.hom ≫ M.s)
  have hz : ∀ s, ((x ≫ Q.a₀) ≫ Q.P.hom) s ∈ U₀ := fun s => by
    rw [Category.assoc, Q.cart.w, ← Category.assoc]
    exact ((x ≫ pullback.snd _ _) s).2
  have key := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q K (x ≫ Q.a₀) _ ψ.hom v
    Set.range_unique (Or.inr (hz _)) hψ.symm (Q.crd K x v hv)).2 ⟨i, by
      rw [proj_zero_of_eq_bot (hB.gen _ (hz _)),
        Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne hj, map_zero, zero_mul]) (by simp)]
      simpa using hi⟩
  exact key (Set.mem_univ (IsLocalRing.closedPoint K))

theorem nonempty_ext : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), Nonempty Q.Ext := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q
  have := ArithBase.char (o := o) (Ω := Ω)
  have := M.sep
  have := M.lft
  have := M.qc
  have := Q.proper
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.2 (ArithBase.ft (o := o) (Ω := Ω)))
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h1 : (ρ.pt 0).left = eSec ρ.P.A := by
    have e : toUnit (baseOver (Sp S.R)) = 𝟙 (𝟙_ (Over (Sp S.R))) := toUnit_unique _ _
    rw [h0, Hom.one_def, e]
    exact congrArg CommaMorphism.left (Category.id_comp _)
  let a : pullback ρ.P.A.hom Q.u₀ ⟶ Q.G.toScheme := IsOpenImmersion.lift Q.G.ι Q.a₀ (range_subset hL hB Q)
  have ha : a ≫ Q.G.ι = Q.a₀ := IsOpenImmersion.lift_fac _ _ _
  let ε : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ := eSec ((Over.pullback Q.u₀).obj ρ.P.A)
  have hε₁ : ε ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A := eSec_fst Q.u₀ ρ.P.A
  have hε₂ : ε ≫ pullback.snd _ _ = 𝟙 _ := Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]
  have : Nonempty U₀.toScheme := hB.ov.ne.to_subtype
  obtain ⟨t, ht⟩ := exists_lift M.pt M.gen U₀.ι
  obtain ⟨e, he, he'⟩ := exists_section_of_local M.pt M.gen (Q.G.ι ≫ Q.P.hom) (t ≫ ε ≫ a) fun z => by
    obtain ⟨W, h, hz, hh, H⟩ := GlobalTheory.T.exists_section_extending_torsionPoints_support hL o Ω S ρ M U₀ EE hB Q z 0 (zero_mem _)
    refine ⟨W, h, hz, hh, fun x hx => ?_⟩
    rw [← cancel_mono Q.G.ι, Category.assoc, H Ω x (t ≫ ε) ?_ ?_]
    · simp only [Category.assoc, ha]
    · rw [Category.assoc, reassoc_of% hε₂, hx, ht]
    · rw [Category.assoc, Category.assoc, reassoc_of% hε₂, hε₁, h1]
  have : IsDominant (t ≫ U₀.ι) := ht ▸ M.isDominant_pt
  have : IsDominant t := .of_comp_of_isOpenImmersion t U₀.ι
  refine ⟨{
    π := M.s ≫ spMap (algebraMap ℤ o)
    flat := flat_of_charZero M.pt M.gen _
    lft := inferInstance
    qc := inferInstance
    sep := inferInstance
    normal := hB.ov.normal
    ne := hB.ov.ne
    ab := TLinPf.isAb_pullback _ _ ρ.P.isAb
    dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      (ρ.g_eq ▸ ρ.P.smoothDim)
    a := a
    a_eq := ha
    e := e
    e_sec := he
    e_zero := ?_ }⟩
  change U₀.ι ≫ e = ε ≫ a
  refine ext_of_isDominant_of_isSeparated (Q.G.ι ≫ Q.P.hom) ?_ t ?_
  · rw [Category.assoc, he, Category.assoc, reassoc_of% ha, Q.cart.w, reassoc_of% hε₂, Category.comp_id]
  · rw [← Category.assoc, ht, he']

end GlobalTheory.ZH.ClosureLifting
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyClosureExtensionAbelianSchemeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_closureExtension_abelianScheme : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), Nonempty Q.Ext := by
  first | exact @GlobalTheory.ZH.ClosureLifting.nonempty_ext | exact GlobalTheory.ZH.ClosureLifting.nonempty_ext | (intros; apply GlobalTheory.ZH.ClosureLifting.nonempty_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiCmpOfSecCmp
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiCmpOfSecCmp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory.PsiBaseChange

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R} {D' : DegPre V}
  {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)} {xe : D'.X ≃+ D.X}

theorem secCmp_val {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α} (h : SecCmp D D' β v xe f f')
    (α : D'.X) {T : Over (Spec (CommRingCat.of V))} (y : T ⟶ D'.P.A) (r : T.left ⟶ (𝟙_ _ ⊗ D.P.A).left)
    (hr : r ≫ (snd _ D.P.A).left = y.left ≫ β) (z : T.left) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (Ω : (T.left ⟶ D'.P.A.left) → (T.left.presheaf.stalk z)ˣ) (hΩ : ∀ q, Ω q = gw v q z (J (q ≫ β)) (J' q)) :
    sval (f (xe α)) r z J = (Ω (y * cT D' T α).left * (Ω (cT D' T α).left)⁻¹ * Ω (1 : T ⟶ D'.P.A).left).val *
      sval (f' α) (lift (toUnit T) y).left z J' := by
  have a : (lift (toUnit T) y).left ≫ (snd _ D'.P.A).left = y.left := congrArg (fun q => q.left) (lift_snd (toUnit T) y)
  refine (h α _ (lift (toUnit T) y).left r (by rw [hr, ← Category.assoc, a]) z J J' hJ hJ').trans ?_
  refine congrArg (fun u : (T.left.presheaf.stalk z)ˣ => u.val * sval (f' α) (lift (toUnit T) y).left z J') ?_
  simp only [← Category.assoc, ← hΩ, PsiExists.comp_famφT, lift_snd]
  simp [Fin.prod_univ_four, DegPre.famε]

theorem val_psi (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β)
    (hc : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) (hrig : RigCmp φ D D' β v)
    {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α} (hf : SecCmp D D' β v xe f f')
    (h : PsiRel D (𝟙_ _) f) (h' : PsiRel D' (𝟙_ _) f') {gam : (TK V).left ⟶ (TK R).left}
    (hg : gam ≫ jK R = jK V ≫ spMap φ) (x : D'.X) {T : Over (Spec (CommRingCat.of V))} [IsIntegral T.left]
    (κ : T ⟶ TK V) (p : T ⟶ D'.P.A) (z : T.left) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J')
    (ne : sval (f' 0) (lift (toUnit T) p).left z J' ≠ 0) :
    val (D.psi (xe x)) (κ.left ≫ gam) z J =
      (gw v (κ.left ≫ D'.xK x) z (J ((κ.left ≫ D'.xK x) ≫ β)) (J' (κ.left ≫ D'.xK x)))⁻¹ *
        val (D'.psi x) κ.left z J' := by
  let T₀ : Over (Spec (CommRingCat.of R)) := Over.mk (T.hom ≫ spMap φ)
  let κ₀ : T₀ ⟶ TK R := Over.homMk (κ.left ≫ gam) (by
    have w : κ.left ≫ jK V = T.hom := Over.w κ
    show (κ.left ≫ gam) ≫ jK R = T.hom ≫ spMap φ
    rw [Category.assoc, hg, ← Category.assoc, w])
  let b : (T ⟶ D'.P.A) →* (T₀ ⟶ D.P.A) := pushHom gp T
  have bc : b (cT D' T x) = cT D T₀ (xe x) := Over.OverMorphism.ext (by
    show (T.hom ≫ (D'.c x).left) ≫ β = (T.hom ≫ spMap φ) ≫ (D.c (xe x)).left
    rw [Category.assoc, hc, Category.assoc])
  let Ω : (T.left ⟶ D'.P.A.left) → (T.left.presheaf.stalk z)ˣ := fun q => gw v q z (J (q ≫ β)) (J' q)
  let y : T ⟶ D'.P.A := p * (cT D' T x)⁻¹
  have hy : y * cT D' T x = p := inv_mul_cancel_right _ _
  have hyb : b y * cT D T₀ (xe x) = b p := by rw [← bc, ← map_mul, hy]
  have sn : ∀ q : T ⟶ D'.P.A, (lift (toUnit T₀) (b q)).left ≫ (snd _ D.P.A).left = q.left ≫ β := fun q =>
    congrArg (fun q => q.left) (lift_snd (toUnit T₀) (b q))
  have e₁ := h (xe x) T₀ (toUnit _) κ₀ (b y) z J hJ
  have e₂ := h' x T (toUnit _) κ y z J' hJ'
  have e₃ := secCmp_val hf x y _ (sn y) z hJ hJ' Ω fun _ => rfl
  have e₄ := secCmp_val hf 0 p _ (sn p) z hJ hJ' Ω fun _ => rfl
  have e₀ : ∀ α : D.X, α = 0 → sval (f α) (lift (toUnit T₀) (b p)).left z J =
      sval (f 0) (lift (toUnit T₀) (b p)).left z J := by
    rintro _ rfl; rfl
  rw [PsiExists.cT_zero, _root_.mul_one, inv_mul_cancel_right] at e₄
  rw [hy] at e₂ e₃
  rw [hyb] at e₁
  have e₅ : @id (T.left.presheaf.stalk z)ˣ (rigV D (T := T₀) z J) = Ω (1 : T ⟶ D'.P.A).left * rigV D' z J' := by
    have := CubTransport.val_pmaps (fun _ => (cubeMapOf gp).e_comm) hrig T.hom hJ hJ'
    rw [Fintype.prod_unique, zpow_one] at this
    exact this
  have e₆ : κ.left ≫ D'.xK x = (cT D' T x).left :=
    congrArg (fun q => q.left) (show κ ≫ cT D' _ x = cT D' _ x by rw [← Category.assoc, comp_toUnit])
  have e₇ := e₃.symm.trans (e₁.trans (congrArg₂ (· * ·)
    (congrArg (fun u : (T.left.presheaf.stalk z)ˣ => (val (D.psi (xe x)) (κ.left ≫ gam) z J * u).val) e₅)
    ((e₀ _ (map_zero xe)).symm.trans e₄)))
  rw [e₂] at e₇
  rw [e₆]
  refine PsiCompare.unit_cancel (a := Ω p.left) (c := Ω (1 : T ⟶ D'.P.A).left) (q := rigV D' z J') ne ?_
  rw [mul_comm (sval _ _ _ _)]
  exact e₇.trans (mul_comm _ _)

end GlobalTheory.PsiBaseChange

namespace GlobalTheory


open PsiBaseChange in
theorem psiCmp_of_secCmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ (f : ∀ α, SecBT D (𝟙_ _) 1 α) (f' : ∀ α, SecBT D' (𝟙_ _) 1 α), SecCmp D D' β v xe f f' → PsiRel D (𝟙_ _) f → PsiRel D' (𝟙_ _) f' → (∃ j, (f' 0).f j ≠ 0) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam := by
  intro R V _ _ _ _ φ D D' β v xe gp hv hc hrig f f' hf h h' hne gam hg x
  have hL := D.P.isLB
  have hL' := D'.P.isLB
  have pg := (isGen_iff v).1 hv
  have := D'.P.isAb.smooth
  have := D'.P.isAb.geomConnected
  have : IsIntegral (TF (R := V) (FractionRing V)).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of _)))
  have : IsIntegral (DegPre.BF D' (FractionRing V)).left :=
    isIntegral_tensor_left_of_smooth_grpObj _ D'.P.A (TF (R := V) (FractionRing V))
  have hx : D'.xK x ≫ β = gam ≫ D.xK (xe x) := by
    show (jK V ≫ (D'.c x).left) ≫ β = gam ≫ jK R ≫ (D.c (xe x)).left
    rw [Category.assoc, hc, ← Category.assoc gam, hg, Category.assoc]
  let T := DegPre.BF D' (FractionRing V)
  let π : T.left ⟶ (TK V).left := (fst (TF (R := V) (FractionRing V)) D'.P.A).left ≫ jFK (R := V) (FractionRing V)
  let κ : T ⟶ TK V := Over.homMk π
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := V) (FractionRing V)) D'.P.A)))
  obtain ⟨s, hs⟩ := PsiExists.exists_pullB D' (FractionRing V) (toUnit _) 1 f'
  have hs0 := (pullB_ne_zero_iff V D' _ 1 f' s hs 0).2 hne
  have wl : toUnit (TF (R := V) (FractionRing V)) ▷ D'.P.A = lift (toUnit T) (snd _ D'.P.A) :=
    CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ((whiskerRight_snd _ _).trans (lift_snd _ _).symm)
  have key : ∀ (z : T.left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (π ≫ gam) z J =
        (gw v (π ≫ D'.xK x) z (J ((π ≫ D'.xK x) ≫ β)) (J' (π ≫ D'.xK x)))⁻¹ * val (D'.psi x) π z J' :=
    fun z J J' hJ hJ' => val_psi gp hc hrig hf h h' hg x κ (snd _ D'.P.A) z hJ hJ' (by
      rw [← wl, ← hs 0 z J' hJ']
      exact (exists_ne_zero_iff_sval_ne_zero _ hJ').1 hs0)
  obtain ⟨t, ht, hv⟩ := exists_up pg hL hL' (φ' := fun _ : PUnit => D'.xK x) (D'.psi x) (D'.psi_gen x)
  have hcorr : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi (xe x)) (π ≫ gam))
      (LB.pullGen D.P.L _ _ t π) :=
    corr_of_val hL fun z J hJ => by
      choose J' hJ' using fun ψ : T.left ⟶ D'.P.A.left => exists_chart hL' (ψ z)
      rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, key z J J' hJ hJ']
      refine Eq.trans ?_ (hv _ π z _ _ (Good.mem hJ _ π) (Good.mem hJ' _ π)).symm
      rw [pw, Fintype.prod_unique, zpow_neg_one, Category.assoc]; rfl
  have hz : (DegPre.zF D' (FractionRing V)).left ≫ π = 𝟙 (TK V).left := PsiCompare.zF_fst D'
  refine EvenPull.pmaps_of_section pg hL hL' gam (fun _ => hx) _ (D'.psi_gen x) _ (D.psi_gen _) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (by rw [Scheme.Hom.id_appTop]; exact Function.surjective_id) fun y J J' hJ hJ' => ?_
  have := val_corr hJ hcorr (DegPre.zF D' (FractionRing V)).left
  rw [val_pull hJ, val_pull hJ, ← Category.assoc, hz] at this
  refine this.trans ((hv _ (𝟙 _) y _ _ (Good.mem hJ _ _) (Good.mem hJ' _ _)).trans ?_)
  refine congrArg₂ (· * ·) ?_ rfl
  rw [pw, Fintype.prod_unique, Fintype.prod_unique, Category.assoc]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiCmpOfSecCmpStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiCmp_of_secCmp' : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ (f : ∀ α, SecBT D (𝟙_ _) 1 α) (f' : ∀ α, SecBT D' (𝟙_ _) 1 α), SecCmp D D' β v xe f f' → PsiRel D (𝟙_ _) f → PsiRel D' (𝟙_ _) f' → (∃ j, (f' 0).f j ≠ 0) → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam := by
  first | exact @GlobalTheory.psiCmp_of_secCmp | exact GlobalTheory.psiCmp_of_secCmp | (intros; apply GlobalTheory.psiCmp_of_secCmp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section

namespace GlobalTheory.SquareLevel

open GlobalTheory.ThetaCoord

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

theorem halves_inl (g : ℕ) (i : Fin g) : (halves g (.inl i) : ℕ) = i := rfl

theorem halves_inr (g : ℕ) (i : Fin g) : (halves g (.inr i) : ℕ) = g + i := rfl

theorem labelSymp_eq (g M : ℕ) (a b : Fin g ⊕ Fin g → ZMod M) :
    labelSymp (a ∘ (halves g).symm) (b ∘ (halves g).symm) = eStd g M a b := by
  have h₁ : ∀ i j : Fin g, stdSymp g (halves g (.inl i)) (halves g (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inl, if_neg (by omega), if_neg (by omega)]
  have h₂ : ∀ i j : Fin g, stdSymp g (halves g (.inl i)) (halves g (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inr]
    by_cases h : i = j
    · rw [if_pos h, if_pos (by subst h; omega)]
    · have : (i : ℕ) ≠ j := fun q => h (Fin.ext q)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  have h₃ : ∀ i j : Fin g, stdSymp g (halves g (.inr i)) (halves g (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inl, halves_inr]
    by_cases h : i = j
    · rw [if_pos h, if_neg (by omega), if_pos (by subst h; omega)]
    · have : (i : ℕ) ≠ j := fun q => h (Fin.ext q)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  have h₄ : ∀ i j : Fin g, stdSymp g (halves g (.inr i)) (halves g (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    rw [stdSymp, halves_inr, halves_inr, if_neg (by omega), if_neg (by omega)]
  rw [labelSymp, ← (halves g).sum_comp]
  simp_rw [← (halves g).sum_comp]
  simp [Fintype.sum_sum_type, h₁, h₂, h₃, h₄, eStd, sub_eq_add_neg, Finset.sum_add_distrib, add_comm]

variable {S : Scheme.{0}}

theorem linComb_pow_left {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (c : Fin n → ℕ) (M : ℕ) : linComb (fun i => y i ^ M) c = linComb y (fun i => M * c i) := by
  simp only [linComb, pow_mul]

theorem linComb_pow_right {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A))
    (c : Fin n → ℕ) (M : ℕ) : linComb y c ^ M = linComb y (fun i => M * c i) := by
  simp only [linComb, List.prod_ofFn, ← Finset.prod_pow, ← pow_mul, Nat.mul_comm]

theorem comp_linComb {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (y : Fin n → (T ⟶ A)) (c : Fin n → ℕ) : h ≫ linComb y c = linComb (fun i => h ≫ y i) c := by
  let F : (T ⟶ A) →* (T' ⟶ A) := MonoidHom.mk' (h ≫ ·) (fun a b => MonObj.comp_mul _ _ _)
  simp only [linComb, List.prod_ofFn]
  exact (map_prod F _ _).trans (Finset.prod_congr rfl fun i _ => map_pow F _ _)

theorem existsUnique_lab {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n M : ℕ} [NeZero M]
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ (M ^ 2) = 1)
    (ind : ∀ c c' : Fin n → Fin (M ^ 2), linComb y (fun i => (c i : ℕ)) = linComb y (fun i => (c' i : ℕ)) → c = c')
    (z : T ⟶ A) (hz : z ^ M = 1) (sp : ∃ c : Fin n → Fin (M ^ 2), linComb y (fun i => (c i : ℕ)) = z) :
    ∃! a : Fin n → ZMod M, lab (fun i => y i ^ M) a = z := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have lt : ∀ a : ZMod M, M * a.val < M ^ 2 := fun a => by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) hM
  refine existsUnique_of_exists_of_unique ?_ fun a b ha hb => ?_
  · obtain ⟨c, hc⟩ := sp
    have h₀ := ind (fun i => ⟨(M * c i) % M ^ 2, Nat.mod_lt _ (pow_pos hM 2)⟩) (fun _ => ⟨0, pow_pos hM 2⟩) (by
      have e : linComb y (fun i => (M * c i) % M ^ 2) = linComb y (fun i => M * c i) := by
        simp only [linComb]
        exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => (pow_eq_pow_mod _ (hy i)).symm)
      refine e.trans ?_
      rw [← linComb_pow_right, hc, hz]
      simp [linComb])
    have h₁ : ∀ i, M ∣ (c i : ℕ) := fun i => by
      have q : (M * c i) % M ^ 2 = 0 := congrArg Fin.val (congrFun h₀ i)
      exact Nat.dvd_of_mul_dvd_mul_left hM (sq M ▸ Nat.dvd_of_mod_eq_zero q)
    refine ⟨fun i => ((c i : ℕ) / M : ℕ), (linComb_pow_left _ _ _).trans
      ((congrArg (linComb y) (funext fun i => ?_)).trans hc)⟩
    rw [ZMod.val_cast_of_lt (Nat.div_lt_of_lt_mul (sq M ▸ (c i).2)), Nat.mul_div_cancel' (h₁ i)]
  · have h := ind (fun i => ⟨_, lt (a i)⟩) (fun i => ⟨_, lt (b i)⟩)
      ((linComb_pow_left _ _ _).symm.trans ((ha.trans hb.symm).trans (linComb_pow_left _ _ _)))
    funext i
    exact ZMod.val_injective M (Nat.eq_of_mul_eq_mul_left hM (congrArg Fin.val (congrFun h i)))

theorem weilIs_pow_pow (hW : WeilSt) [IsLocallyNoetherian S] (P : PolAV S) {M : ℕ} {T : Over S}
    (hu : IsUnit (M : Γ(T.left, ⊤))) {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hM : 1 ≤ M) (hx : x ^ (M ^ 2) = 1)
    (hy : y ^ (M ^ 2) = 1) (H : WeilIs P.A P.L (M ^ 2 : ℕ) x y c) :
    WeilIs P.A P.L M (x ^ M) (y ^ M) (c ^ M) := by
  have H' := CommPairing.weilIs_symm P.isLB H
  have k : ∀ n, WeilIs P.A P.L (M ^ 2 : ℕ) (y ^ (n + 1)) x (c⁻¹ ^ (n + 1)) := fun n => by
    induction n with
    | zero => simpa using H'
    | succ n ih => rw [pow_succ y, pow_succ c⁻¹]; exact (hW S P _ T).2.1 _ _ _ _ _ ih H'
  have k' := CommPairing.weilIs_symm P.isLB (k (M - 1))
  rw [Nat.sub_add_cancel hM, inv_pow, inv_inv] at k'
  refine ((hW S P M T).2.2.2 M x _ _ (by rw [Nat.cast_mul]; exact hu.mul hu) (by rw [← sq, hx])
    (by rw [← pow_mul, ← sq, hy])).1 ?_
  rwa [← Nat.cast_mul, ← sq]

end GlobalTheory.SquareLevel

namespace GlobalTheory


open SquareLevel ThetaCoord in
theorem exists_torsionPoints_of_squareLevel : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), 1 ≤ M → IsUnit (M : Γ(S, ⊤)) → ∀ lev : Out.Level P (M ^ 2) ze, ∃ pt : (Fin P.g ⊕ Fin P.g → ZMod M) → (baseOver S ⟶ P.A), (∀ a b, pt (a + b) = pt a * pt b) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ pt a = z) ∧ (∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd P.g M a b).val))) ∧ (∀ a, ∃ y : baseOver S ⟶ P.A, y ^ (M ^ 2) = 1 ∧ y ^ M = pt a) ∧ ∀ (i : Fin P.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → pt (Pi.single (.inl i) 1) = lev.pt i₁ ^ M ∧ pt (Pi.single (.inr i) 1) = lev.pt i₂ ^ M := by
  intro hL S _ P M ze hM hu lev
  have : NeZero M := ⟨by omega⟩
  have hq : ∀ i, (lev.pt i ^ M) ^ M = 1 := fun i => by rw [← pow_mul, ← sq, lev.torsion]
  refine ⟨fun a => lab (fun i => lev.pt i ^ M) (a ∘ (halves P.g).symm), fun a b => lab_add hq _ _,
    fun K _ _ x z hz => ?_, fun a b => ?_, fun a => ?_, fun i i₁ i₂ h₁ h₂ => ?_⟩
  · have H := existsUnique_lab (M := M)
      (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ lev.pt i)
      (fun i => by rw [← MonObj.comp_pow, lev.torsion, MonObj.comp_one]) (lev.indep K x) z hz
      (lev.span K x z (by rw [sq, pow_mul, hz, one_pow]))
    refine ((Equiv.arrowCongr (halves P.g) (Equiv.refl (ZMod M))).existsUnique_congr fun a => ?_).2 H
    rw [lab, comp_linComb]
    simp only [MonObj.comp_pow]
    rfl
  · have hze : (ze ^ M) ^ M = 1 := by rw [← pow_mul, ← sq, lev.prim.pow_eq_one]
    have := weilIs_lab hL.globalFns P (T := baseOver S) hq (ze := ze ^ M) hze (fun i j => by
      have := weilIs_pow_pow hL.weil P (T := baseOver S) hu hM (lev.torsion i) (lev.torsion j) (lev.pairing i j)
      convert this using 1
      show (ze ^ M) ^ stdSymp P.g i j = (ze ^ stdSymp P.g i j) ^ M
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm])
      (fun a b => ((hL.weil S P M _).1 _ _ (lab_pow hq a) (lab_pow hq b)).exists)
      (a ∘ (halves P.g).symm) (b ∘ (halves P.g).symm)
    rw [labelSymp_eq] at this
    rw [pow_mul]
    exact this
  · refine ⟨linComb lev.pt fun i => (a ((halves P.g).symm i)).val, ?_, ?_⟩
    · simp only [linComb, List.prod_ofFn, ← Finset.prod_pow]
      exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, Nat.mul_comm, pow_mul, lev.torsion, one_pow]
    exact (linComb_pow_right _ _ _).trans (linComb_pow_left _ _ _).symm
  · have k : ∀ s, lab (fun i => lev.pt i ^ M) ((Pi.single s (1 : ZMod M) : _ → ZMod M) ∘ (halves P.g).symm) =
        lev.pt (halves P.g s) ^ M := fun s => by
      rw [← lab_single (M := M) hq (halves P.g s)]
      congr 1
      funext j
      simp [Pi.single_apply, Equiv.symm_apply_eq]
    have e₁ : i₁ = halves P.g (.inl i) := Fin.ext h₁
    have e₂ : i₂ = halves P.g (.inr i) := Fin.ext (h₂.trans (Nat.add_comm _ _))
    rw [e₁, e₂]
    exact ⟨k _, k _⟩

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointsOfSquareLevelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPoints_of_squareLevel_alt : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), 1 ≤ M → IsUnit (M : Γ(S, ⊤)) → ∀ lev : Out.Level P (M ^ 2) ze, ∃ pt : (Fin P.g ⊕ Fin P.g → ZMod M) → (baseOver S ⟶ P.A), (∀ a b, pt (a + b) = pt a * pt b) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃! a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ pt a = z) ∧ (∀ a b, WeilIs P.A P.L (M : ℕ) (pt a) (pt b) (ze ^ (M * (eStd P.g M a b).val))) ∧ (∀ a, ∃ y : baseOver S ⟶ P.A, y ^ (M ^ 2) = 1 ∧ y ^ M = pt a) ∧ ∀ (i : Fin P.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → pt (Pi.single (.inl i) 1) = lev.pt i₁ ^ M ∧ pt (Pi.single (.inr i) 1) = lev.pt i₂ ^ M := by
  first | exact @GlobalTheory.exists_torsionPoints_of_squareLevel | exact GlobalTheory.exists_torsionPoints_of_squareLevel | (intros; apply GlobalTheory.exists_torsionPoints_of_squareLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestModelMapsIntoOpenPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestModelMapsIntoOpenPart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestInOpen

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem proj_bot {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_crd_ne_zero (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {K : Type} [Field K]
    (x : Sp K ⟶ Q.P.left) {z : M.Z} (hz : Set.range (x ≫ Q.P.hom) = {z}) (hc : z ∈ U₀) :
    ∃ v, Crd Q.O1 Q.st x v ∧ v ≠ 0 := by
  have hxz : ∀ s, Q.P.hom (x s) = z := fun s => by
    have : (x ≫ Q.P.hom) s ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  obtain ⟨l, hl⟩ : ∃ l, z ∈ Q.W l := TopologicalSpace.Opens.mem_iSup.1 (by rw [Q.cover]; trivial)
  have hr : Set.range x ⊆ Set.range (Q.P.hom ⁻¹ᵁ Q.W l).ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    change Q.P.hom (x s) ∈ Q.W l
    rwa [hxz]
  obtain ⟨x', rfl⟩ : ∃ x', x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x :=
    ⟨_, IsOpenImmersion.lift_fac _ x hr⟩
  have hcov := (Q.imm l).1
  have hm : x' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (Q.σ l i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  obtain ⟨w, hw⟩ : ∃ w, Crd _ (Q.σ l) x' w :=
    ⟨_, m, 1, (CrdCalc.top_le_iff x' _).2 (Scheme.basicOpen_le _ _ hm), fun _ => rfl⟩
  have hwi := ((CrdCalc.crd_isUnit_iff i hw).2 ((CrdCalc.top_le_iff x' _).2 hi)).ne_zero
  refine ⟨_, Q.rel l K x' _ hw, fun h0 => hwi ?_⟩
  have hBm : ∀ a b, Q.B l a b ∈ M.O z := fun a => (RatModel.Lat.mem_const_iff M).1 (by
    rw [RatModel.Lat.const_E, ← hB.ee.1 z hc, Q.basis l z hl]
    exact Submodule.subset_span ⟨a, rfl⟩)
  let B' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, hBm a b⟩
  let C' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, RatModel.valF_mem_O hl (Q.c l a b)⟩
  have h1 : C' * B' = 1 := by
    apply Matrix.map_injective (f := (M.O z).val.toRingHom) Subtype.val_injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Q.c_inv l
  have h2 := congrArg (fun A => A.map (RatModel.valHom _ z hz)) (mul_eq_one_comm.1 h1)
  beta_reduce at h2
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  have h3 : C'.map (RatModel.valHom _ z hz) =
      (Q.c l).map (valR (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) := by
    ext a b
    rw [← Category.assoc]
    exact RatModel.val_valF (by rw [hz]; exact Set.singleton_subset_iff.2 hl) _
  have h4 : w = 0 := by
    rw [← Matrix.one_mulVec w, ← h2, ← Matrix.mulVec_mulVec, h3, h0, Matrix.mulVec_zero]
  rw [h4]; rfl

theorem mem_G_of_mem [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (w : Q.P.left)
    (hc : Q.P.hom w ∈ U₀) : w ∈ Q.G := by
  let x : Sp (Q.P.left.residueField w) ⟶ Q.P.left := Q.P.left.fromSpecResidueField w
  have hx : ∀ s, x s = w := fun s => Scheme.fromSpecResidueField_apply w s
  have hz : Set.range (x ≫ Q.P.hom) = {Q.P.hom w} := by
    rw [RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    exact congrArg (fun a => {Q.P.hom a}) (hx _)
  obtain ⟨v, hv, hv0⟩ := exists_crd_ne_zero hB Q x hz hc
  have h := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ x _
    (Spec.preimage (x ≫ Q.P.hom ≫ M.s)).hom v hz (Or.inr hc) (Spec.map_preimage _).symm hv).2 (by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
      refine ⟨i, ?_⟩
      rw [proj_bot (hB.gen _ hc), Finset.sum_eq_single i]
      · simpa using hi
      · intro j _ hj
        simp [hj]
      · simp)
  rw [← hx (IsLocalRing.closedPoint _)]
  exact (CrdCalc.top_le_iff x _).1 h

theorem big_of_big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  rw [ρ.N_eq]
  nlinarith

variable {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}

theorem isLocalHom_j (u : ρ.UTest p y₀) : IsLocalHom u.j := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hb' : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ a) * b = 1 := congrArg Subtype.val hb
  have h0 : algebraMap u.V (FractionRing u.V) a ≠ 0 := fun h => by simp [h] at hb'
  obtain ⟨c, hc⟩ := (u.norm_le (algebraMap u.V _ a)⁻¹).1 (by
    rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hb']
    exact (mem_OO_iff _).1 b.2)
  refine IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hc, mul_inv_cancel₀ h0, map_one]

theorem mem_range_or (u : ρ.UTest p y₀) (s : Sp u.V) :
    s ∈ Set.range (jK u.V) ∨ s ∈ Set.range (rPt p ≫ spMap u.j) := by
  by_cases h : s.asIdeal = ⊥
  · refine Or.inl ⟨(⊥ : PrimeSpectrum (FractionRing u.V)), PrimeSpectrum.ext ?_⟩
    rw [h]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective u.V (FractionRing u.V))
  · have := isLocalHom_j u
    refine Or.inr ⟨IsLocalRing.closedPoint (kb p), ?_⟩
    have e₁ : rPt p (IsLocalRing.closedPoint (kb p)) = cPt p :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
    have e₂ : spMap u.j (cPt p) = IsLocalRing.closedPoint u.V := IsLocalRing.comap_closedPoint u.j
    refine ((congrArg (spMap u.j) e₁).trans e₂).trans ?_
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime h s.isPrime)).symm

theorem top_le_preimage_G : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ⊤ ≤ (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS x _
  rcases mem_range_or t.u (t.u.G.hom x) with ⟨s, hs⟩ | ⟨s, hs⟩
  · refine mem_G_of_mem hB Q _ ?_
    have e₁ : Q.P.hom ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) x) = c.yV (t.u.G.hom x) := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, tm.f_over, Scheme.Hom.comp_apply]
    have e₂ : c.yV (jK t.u.V s) = U₀.ι (c.yK s) := by
      rw [← Scheme.Hom.comp_apply, ← c.yK_fac, Scheme.Hom.comp_apply]
    show Q.P.hom ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) x) ∈ U₀
    rw [e₁, ← hs, e₂]
    exact (c.yK s).2
  · haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
    have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
    obtain ⟨x', rfl, -⟩ := Scheme.exists_preimage_of_isPullback pb x s hs.symm
    have hsm : SmoothOfRelativeDimension S.g t.mod.Φ.G.hom :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback pb t.mod.smooth
    have : Smooth t.mod.Φ.G.hom := SmoothOfRelativeDimension.smooth S.g _
    have : JacobsonSpace t.mod.Φ.G.left := LocallyOfFiniteType.jacobsonSpace t.mod.Φ.G.hom
    have hcov := (GlobalTheory.T.immBy_weight_zero' hL.1 hL.2.1 (kb p) t.mod.Φ S.g S.N _ _ S.J _ t.mod.F t.mod.pol (big_of_big ρ hS)
      t.mod.good t.mod.dim).1
    let U : t.mod.Φ.G.left.Opens := t.mod.r ⁻¹ᵁ ((tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G)
    by_contra hx
    obtain ⟨a, haU, ha⟩ := nonempty_inter_closedPoints (Z := (U : Set t.mod.Φ.G.left)ᶜ) ⟨x', hx⟩
      U.isOpen.isClosed_compl.isLocallyClosed
    let x₀ := pointOfClosedPoint (K := kb p) t.mod.Φ.G.hom a ha
    have h₂ : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _ := pointOfClosedPoint_comp _ a ha
    have h₃ : x₀ (IsLocalRing.closedPoint (kb p)) = a := pointOfClosedPoint_apply _ a ha _
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (R := kb p) (t.mod.Φ.H_isLB 1) t.mod.F x₀
    have hmem : x₀ (IsLocalRing.closedPoint (kb p)) ∈
        ⨆ i ∈ {i | t.mod.xe.symm (t.cls i) = 0}, Out.nonzeroLocus (t.mod.F i) := by
      rw [hcov]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hmem
    obtain ⟨i, hi, hm⟩ := hmem
    have h₄ := ((CrdCalc.crd_isUnit_iff i hv).2 ((CrdCalc.top_le_iff _ _).2 hm)).ne_zero
    have h₁ : (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j := by
      rw [Category.assoc, pb.w, ← Category.assoc, h₂]
      exact Category.id_comp _
    have hcr := tm.crd (kb p) ((IsLocalRing.residue (OO p)).comp t.u.j) _ v
      (h₁.trans (Spec.map_comp _ _).symm) (t.mod.red (Over.homMk x₀ h₂) v hv)
    have hov : ((x₀ ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
      rw [Category.assoc, tm.f_over, ← Category.assoc, h₁, Category.assoc, c.fac]
    have key := (GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS _ v hov hcr).2
      ⟨i, t.mod.xe.symm.map_eq_zero_iff.1 hi, h₄⟩
    refine haU ?_
    rw [← h₃]
    exact key (x := IsLocalRing.closedPoint (kb p)) trivial

end GlobalTheory.ZH.TestInOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestModelMapsIntoOpenPartStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testModel_maps_into_openPart : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ⊤ ≤ (tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) ⁻¹ᵁ Q.G := by
  first | exact @GlobalTheory.ZH.TestInOpen.top_le_preimage_G | exact GlobalTheory.ZH.TestInOpen.top_le_preimage_G | (intros; apply GlobalTheory.ZH.TestInOpen.top_le_preimage_G <;> assumption)
end
end
