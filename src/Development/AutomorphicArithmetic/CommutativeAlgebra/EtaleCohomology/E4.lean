module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.LeafLocalizationOfInjectiveSliceOfRestrictionInj
public import Development.AutomorphicArithmetic.CommutativeAlgebra.CurvePicardOfSelmerPicardOfModelCurve
public import Development.AutomorphicArithmetic.CommutativeAlgebra.CurveEtaleDescent
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOneIffTwistEquiv
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleCohomologyDegreeZeroSurjectiveLimit
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleCohomologyClassKilledOnNeighborhood
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CurveCohomologyKilledByFiniteCover
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleStalkCohomologyStrictHenselianContinuity
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GeometricFibreCohomologyConstant
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TwistedSectionsOfNegativeDegreeVanishing
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsOpenImmersionInclusionOfPiecewise
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FreeEtaleSheafLiftExists
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PullbackIsLimitOverFgSubalgebras
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SepClosedPointFilteredEtaleColimit
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExtensionByZeroOfZariskiQuasiFiniteFactorization
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.DescentMapFactorsThroughStage
public import Development.EtaleCohomology.EtaleSheaves.IterCompPf
public import Development.EtaleCohomology.EtaleSheaves.ReducedOfSmooth
public import Development.EtaleCohomology.EtaleSheaves.LeafRelDimOnePf
public import Development.EtaleCohomology.EtaleSheaves.LeafCompGeomPf
public import Development.EtaleCohomology.EtaleSheaves.LeafConsPfC
public import Development.EtaleCohomology.EtaleSheaves.ColimHensPf
public import Development.EtaleCohomology.EtaleSheaves.LeafLimFPPf
public import Development.EtaleCohomology.EtaleSheaves.DescentPf
public import Development.EtaleCohomology.EtaleSheaves.LeafQCQSInductPf
public import Development.EtaleCohomology.EtaleSheaves.H0Lifting
public import Development.EtaleCohomology.EtaleSheaves.LeafObjAffPf
public import Development.EtaleCohomology.EtaleSheaves.LeafProjModelPfImm
public import Development.EtaleCohomology.EtaleSheaves.QuasiFiniteAtOfIsOpenFiber
public import Development.EtaleCohomology.EtaleSheaves.LeafStalkValuationPf
public import Development.EtaleCohomology.EtaleSheaves.ResZeroOfRange
public import Development.EtaleCohomology.EtaleSheaves.LZHensFinitePf
public import Development.EtaleCohomology.EtaleSheaves.LeafTwistIsoPf
public import Development.EtaleCohomology.EtaleSheaves.CurveUnitsOrderAtInfinity
public import Development.EtaleCohomology.EtaleSheaves.LeafVanWPf
public import Development.EtaleCohomology.KummerTheory.ForgetInjPf
public import Development.EtaleCohomology.EtaleSheaves.RTEqZeroOfPtA

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTrdegDimPf
namespace LateralTheory.E.LeafTrdegDimPf

open Algebra

theorem trdeg_le_card (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (h : Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F) :
    Algebra.trdeg k F ≤ (s.card : Cardinal) := by
  have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set F)) F :=
    ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.1 (h.isAlgebraic x)⟩
  obtain ⟨t, hts, hb⟩ := exists_isTranscendenceBasis_subset (R := k) (A := F) (s : Set F)
  rw [← hb.cardinalMk_eq_trdeg]
  calc Cardinal.mk t ≤ Cardinal.mk (s : Set F) := Cardinal.mk_le_mk_of_subset hts
    _ = (s.card : Cardinal) := by simp

theorem LeafTrdegDim_of : LateralTheory.E.LeafCurveVCut.LeafTrdegDim := by
  intro k F Ω _ _ _ _ _ _ _ _ n s hs hF R hR
  have hFT : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨d, hd1, hd2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k R
  have h1 : Algebra.trdeg k R ≤ Algebra.trdeg k Ω :=
    trdeg_le_of_injective R.val Subtype.val_injective
  have h2 : Algebra.trdeg k Ω = Algebra.trdeg k F := GlobalTheory.trdeg_eq_of_isAlgebraic_top k F Ω
  have h3 := trdeg_le_card k F s hF
  have hdn : (d : Cardinal) ≤ (n : Cardinal) := by
    rw [← hd2]
    exact h1.trans (h2 ▸ h3.trans (by exact_mod_cast hs))
  have : d ≤ n := by exact_mod_cast hdn
  rw [hd1]
  exact_mod_cast this

end LateralTheory.E.LeafTrdegDimPf
end

section -- merged from Development.EtaleCohomology.KummerTheory.FinInjSlice
namespace LateralTheory.Fin.InjSlice
theorem etale_forget_preservesInjectiveObjects : LateralTheory.KummerTheory.ForgetInj := by
  apply LateralTheory.KummerTheory.ForgetInj_of
theorem etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a : LateralTheory.KummerTheory.InjSlice := by
  apply LateralTheory.KummerTheory.InjSlice_of <;> first | exact etale_forget_preservesInjectiveObjects
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.InjSlice := etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a
end LateralTheory.Fin.InjSlice
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RestrictionInjectiveOfAcyclic
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb

open LateralTheory.EWeil.AcycPf

private lemma exact_filtered (R : Type) [CommRing R] (J : Type 1) [Category.{0} J] [IsFiltered J] :
    HasExactColimitsOfShape J (ModuleCat.{1} (ULift.{1} R)) := by
  let e : J ≌ ULiftHom.{1} J := ULiftHom.equiv
  haveI : IsFiltered (ULiftHom.{1} J) := IsFiltered.of_equivalence e
  exact HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{1} (ULift.{1} R)) e.symm

private lemma mono_of_isColimit {J : Type 1} [Category.{0} J] {A : Type 2} [Category.{1} A] [Abelian A]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] {K L : J ⥤ A} (τ : K ⟶ L) [Mono τ]
    {c : Cocone K} {d : Cocone L} (hc : IsColimit c) (hd : IsColimit d) (m : c.pt ⟶ d.pt)
    (hm : ∀ j, c.ι.app j ≫ m = τ.app j ≫ d.ι.app j) : Mono m := by
  have key : m = (hc.coconePointUniqueUpToIso (colimit.isColimit K)).hom ≫ colimMap τ ≫
      (hd.coconePointUniqueUpToIso (colimit.isColimit L)).inv := by
    refine hc.hom_ext fun j => ?_
    simp [hm]
  have hτ : Mono (colim.map τ) := inferInstance
  have hτ' : Mono (colimMap τ) := hτ
  rw [key]
  infer_instance

private lemma lan_mono {C D : Type 1} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) [RepresentablyFlat G]
    {A : Type 2} [Category.{1} A] [Abelian A]
    [∀ X, HasColimitsOfShape (CostructuredArrow G.op X) A]
    (hA : ∀ (J : Type 1) [Category.{0} J] [IsFiltered J] [HasColimitsOfShape J A], HasExactColimitsOfShape J A)
    {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) [Mono φ] : Mono ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ) := by
  have hφ : ∀ c, Mono (φ.app c) := fun c => inferInstance
  have key : ∀ X, Mono (((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X) := by
    intro X
    haveI : IsFiltered (CostructuredArrow G.op X) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence G (unop X))
    haveI := hA (CostructuredArrow G.op X)
    haveI : ∀ j, Mono ((Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ).app j) :=
      fun j => hφ _
    haveI : Mono (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ) :=
      NatTrans.mono_of_mono_app _
    refine mono_of_isColimit (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ)
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op P X)
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op Q X) _ ?_
    intro j
    have h₂ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app (G.op.obj j.left) =
        φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left :=
      (congr_app (G.op.lanUnit.naturality φ) j.left).symm
    have h₃ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj P).map j.hom ≫
        ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X =
        φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj Q).map j.hom := by
      rw [NatTrans.naturality, reassoc_of% h₂]
    first
      | exact (Category.assoc _ _ _).trans h₃
      | (dsimp only [Functor.LeftExtension.coconeAt_ι_app, Functor.whiskerLeft_app]
         simpa only [Category.assoc] using h₃)
  exact NatTrans.mono_of_mono_app _

set_option backward.isDefEq.respectTransparency false in
private lemma incl_flat (S : Scheme.{0}) : RepresentablyFlat (incl S) := by
  have : PreservesFiniteLimits (incl S) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Etale.forget S))
  exact flat_of_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency false in
private lemma incl_cont (S : Scheme.{0}) :
    (incl S).IsContinuous S.smallEtaleTopology (Scheme.etaleTopology.over S) := by
  have := incl_flat S
  haveI : (incl S).Full := inferInstanceAs (Scheme.Etale.forget S).Full
  haveI : (incl S).Faithful := inferInstanceAs (Scheme.Etale.forget S).Faithful
  haveI : (incl S).LocallyCoverDense (Scheme.etaleTopology.over S) :=
    Scheme.locallyCoverDense_of_le (P := @Etale) S le_rfl
  rw [Functor.isContinuous_iff_coverPreserving]
  exact Functor.coverPreserving_restrictedTopology (incl S) (Scheme.etaleTopology.over S)

private lemma restr_inj : RestrInj := by
  intro R _ S G _
  haveI := incl_cont S
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (incl S)
    (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology (Scheme.etaleTopology.over S)
  haveI : (Functor.sheafPullbackConstruction.sheafPullback (incl S) (ModuleCat.{1} (ULift.{1} R))
      S.smallEtaleTopology (Scheme.etaleTopology.over S)).PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    haveI := incl_flat S
    haveI : Mono ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f) :=
      inferInstance
    haveI : Mono (((incl S).op.lan : _ ⥤ (Over S)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)).map
        ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f)) :=
      lan_mono (incl S) (fun J _ _ _ => exact_filtered R J) _
    exact (presheafToSheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R))).map_mono _
  exact ⟨(((incl S).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology
    (Scheme.etaleTopology.over S)).obj G).property, adj.map_injective G inferInstance⟩

end UpperTheory.Cb

theorem UpperTheory.Cb.restrInj : LateralTheory.EWeil.AcycPf.RestrInj := UpperTheory.Cb.restr_inj
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafBdryPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Set Order TopologicalSpace Topology

namespace LateralTheory.E.LeafBdryPf

def univIC (Y : Type*) [TopologicalSpace Y] [IrreducibleSpace Y] : IrreducibleCloseds Y where
  carrier := univ
  isIrreducible' := IrreducibleSpace.isIrreducible_univ Y
  isClosed' := isClosed_univ

lemma withBot_lt_of_add_one_le {a b : WithBot ℕ∞} (h : a + 1 ≤ b) (hb : b < ⊤) (ha : a ≠ ⊥) : a < b := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl ha
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe b =>
      have hb' : b < ⊤ := by
        rw [← WithBot.coe_top] at hb
        exact WithBot.coe_lt_coe.mp hb
      have h' : a + 1 ≤ b := by exact_mod_cast h
      have ha' : a ≠ ⊤ := (lt_of_le_of_lt (le_self_add.trans h') hb').ne
      exact WithBot.coe_lt_coe.mpr ((ENat.add_one_le_iff ha').mp h')

theorem dim_lt_of_closedEmbedding {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [IrreducibleSpace Y]
    (f : Z → Y) (hf : IsClosedEmbedding f) (hfin : topologicalKrullDim Y < ⊤) (hne : (range f)ᶜ.Nonempty) :
    topologicalKrullDim Z < topologicalKrullDim Y := by
  have hY : Nonempty (IrreducibleCloseds Y) := ⟨univIC Y⟩
  by_cases hZ : Nonempty (IrreducibleCloseds Z)
  · have hlt : ∀ c : IrreducibleCloseds Z, IrreducibleCloseds.map f hf.continuous c < univIC Y := by
      intro c
      refine lt_of_le_of_ne (fun x _ => trivial) ?_
      intro heq
      obtain ⟨y, hy⟩ := hne
      have h1 : (IrreducibleCloseds.map f hf.continuous c : Set Y) ⊆ range f := by
        rw [IrreducibleCloseds.coe_map]
        exact closure_minimal (image_subset_range _ _) hf.isClosed_range
      apply hy
      apply h1
      rw [heq]
      trivial
    let g : WithTop (IrreducibleCloseds Z) → IrreducibleCloseds Y :=
      fun o => WithTop.recTopCoe (univIC Y) (IrreducibleCloseds.map f hf.continuous) o
    have hg : StrictMono g := by
      intro a b hab
      induction a using WithTop.recTopCoe with
      | top => exact absurd hab (by simp)
      | coe a =>
        induction b using WithTop.recTopCoe with
        | top => exact hlt a
        | coe b =>
          exact IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing (WithTop.coe_lt_coe.mp hab)
    have h := krullDim_le_of_strictMono g hg
    rw [krullDim_WithTop] at h
    exact withBot_lt_of_add_one_le h hfin (bot_lt_krullDim).ne'
  · rw [not_nonempty_iff] at hZ
    have : topologicalKrullDim Z = ⊥ := krullDim_eq_bot
    rw [this]
    exact bot_lt_krullDim

theorem LeafBdry_of : LateralTheory.E.LeafGeoCut.LeafBdry := by
  intro Y B W p ι hι hirr hfin hne
  have : IsClosedImmersion (pullback.fst p ι) := inferInstance
  refine dim_lt_of_closedEmbedding _ (pullback.fst p ι).isClosedEmbedding hfin ?_
  rw [Scheme.Pullback.range_fst, ← preimage_compl]
  exact hne

end LateralTheory.E.LeafBdryPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafClosedPf
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LeafClosedPf

theorem LeafClosed_of : LateralTheory.E.LeafGeoCut.LeafClosed := by
  intro B V
  let Z : TopologicalSpace.Closeds B := ⟨(V : Set B)ᶜ, V.isOpen.isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  simp [Z]

end LateralTheory.E.LeafClosedPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSelPicPf
noncomputable section
open nonZeroDivisors IsDedekindDomain

namespace LateralTheory.E.LeafSelPicPf
open LateralTheory.E.LeafPicCut

lemma units_torsionFree {B : Type} [CommRing B] [IsDedekindDomain B] {q : ℕ} (hq : q ≠ 0)
    (x : (FractionalIdeal B⁰ (FractionRing B))ˣ) (h : x ^ q = 1) : x = 1 := by
  have hx0 : (x : FractionalIdeal B⁰ (FractionRing B)) ≠ 0 := x.ne_zero
  have hc : ∀ v : HeightOneSpectrum B,
      FractionalIdeal.count (FractionRing B) v (x : FractionalIdeal B⁰ (FractionRing B)) = 0 := by
    intro v
    have h1 := FractionalIdeal.count_pow (FractionRing B) v q (x : FractionalIdeal B⁰ (FractionRing B))
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one, FractionalIdeal.count_one] at h1
    have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    exact (mul_eq_zero.mp h1.symm).resolve_left hq'
  ext1
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (FractionRing B) hx0]
  simp [hc]

lemma exists_rep {B : Type} [CommRing B] [IsDedekindDomain B] (q : ℕ) (c : ClassGroup B) (hc : c ^ q = 1) :
    ∃ (I : (FractionalIdeal B⁰ (FractionRing B))ˣ) (f : (FractionRing B)ˣ),
      ClassGroup.mk (FractionRing B) I = c ∧ toPrincipalIdeal B (FractionRing B) f = I ^ q := by
  revert hc
  refine ClassGroup.induction (R := B) (FractionRing B) (fun I hc => ?_) c
  · refine ⟨I, ?_⟩
    have h1 : ClassGroup.mk (FractionRing B) (I ^ q) = ClassGroup.mk (FractionRing B) 1 := by
      rw [map_pow, hc, map_one]
    obtain ⟨x, hx⟩ := ClassGroup.mk_eq_mk.mp h1
    refine ⟨x⁻¹, rfl, ?_⟩
    rw [map_inv, inv_eq_iff_mul_eq_one, mul_comm, hx]

theorem LeafSelPic_of : LeafSelPic := by
  intro B _ _ q _ hfin
  classical
  have hex := fun c : {c : ClassGroup B // c ^ q = 1} => exists_rep q c.1 c.2
  choose I f hI hf using hex
  have hsel : ∀ c, f c ∈ sel B q := fun c => by
    simp only [sel, Subgroup.mem_comap, MonoidHom.mem_range]
    exact ⟨I c, by rw [hf c]; rfl⟩
  let φ : {c : ClassGroup B // c ^ q = 1} → selQ B q := fun c => QuotientGroup.mk ⟨f c, hsel c⟩
  refine Finite.of_injective φ ?_
  intro c d hcd
  have h1 := QuotientGroup.eq.mp hcd
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at h1
  obtain ⟨u, hu⟩ := h1
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hu
  have hx : ((I c)⁻¹ * I d * (toPrincipalIdeal B (FractionRing B) u)⁻¹) ^ q = 1 := by
    rw [mul_pow, mul_pow, inv_pow, inv_pow, ← map_pow, hu, ← hf c, ← hf d, map_mul, map_inv]
    group
  have h2 := units_torsionFree (NeZero.ne q) _ hx
  apply Subtype.ext
  rw [← hI c, ← hI d]
  refine ClassGroup.mk_eq_mk.mpr ⟨u, ?_⟩
  rw [mul_inv_eq_one, inv_mul_eq_iff_eq_mul] at h2
  exact h2.symm

end LateralTheory.E.LeafSelPicPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTermsPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafTermsPf

variable {R : Type} [CommRing R]

theorem HKpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem HKpull_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem finite_of_retract {K L : Cx R} (s : K ⟶ L) (t : L ⟶ K) (h : s ≫ t = 𝟙 K) (F : Shv R) (n : ℤ)
    (hL : Finite (HK R L F n)) : Finite (HK R K F n) :=
  Finite.of_surjective (HK.pull R s F n) (fun x =>
    ⟨HK.pull R t F n x, by rw [← HKpull_comp, h, HKpull_id]⟩)

theorem finite_of_iso {A B : Shv R} (e : A ≅ B) (F : Shv R) (n : ℤ)
    (hB : Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj B) F n)) :
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj A) F n) :=
  finite_of_retract _ _ (((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).mapIso e).hom_inv_id) F n hB

theorem d_const_zero (P : PSh) : ((chains R).obj (disc.obj P)).d (-1) 0 = 0 := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat
    (i := 1) (j := 0) (i' := -1) (j' := 0) rfl rfl
  change (((chainsN R).obj (disc.obj P)).extend ComplexShape.embeddingDownNat).d (-1) 0 = 0
  rw [h]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    simp [chainsN, Fin.sum_univ_two, SimplicialObject.δ, disc]
    all_goals first
      | (erw [neg_one_smul, one_smul, add_neg_cancel])
      | (simp only [one_smul, neg_smul]; exact add_neg_cancel _)
      | abel
    all_goals rfl
  rw [this]; simp

def proj0 (P : PSh) : (chains R).obj (disc.obj P) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (((chains R).obj (disc.obj P)).X 0) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi => by
    have : i = -1 := by simp at hi; omega
    subst this; rw [d_const_zero]; simp)

theorem etale_chain_complex_degree_zero_incl_proj_eq_id (P : PSh) : LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (disc.obj P)) ≫ proj0 P = 𝟙 _ := by
  apply HomologicalComplex.to_single_hom_ext
  simp [LateralTheory.E.LeafSSCut.incl0, proj0]

theorem finite_single_of_H (Z : Scheme.{0}) (F : Shv R) (m : ℤ) (h : Finite (H R (sch.obj Z) F m)) :
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj (yoneda.obj Z))) F m) :=
  finite_of_iso (chainsXIso R (disc.obj (yoneda.obj Z)) 0).symm F m
    (finite_of_retract _ _ (etale_chain_complex_degree_zero_incl_proj_eq_id (R := R) (yoneda.obj Z)) F m h)

section Geo
variable {Y X : Scheme.{0}} (f : Y ⟶ X)

abbrev W (n : ℕ) : Scheme.{0} := widePullback X (fun _ : Fin n => Y) (fun _ => f)

def toPb (n : ℕ) : W f (n + 1) ⟶ pullback (WidePullback.base (fun _ : Fin n => f)) f :=
  pullback.lift (WidePullback.lift (WidePullback.base _) (fun j => WidePullback.π _ j.succ) (by simp))
    (WidePullback.π _ 0) (by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc])

def ofPb (n : ℕ) : pullback (WidePullback.base (fun _ : Fin n => f)) f ⟶ W f (n + 1) :=
  WidePullback.lift (pullback.snd _ _ ≫ f)
    (Fin.cases (pullback.snd _ _) (fun j => pullback.fst _ _ ≫ WidePullback.π _ j))
    (by intro j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [pullback.condition, WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc])

theorem toPb_ofPb (n : ℕ) : toPb f n ≫ ofPb f n = 𝟙 _ := by
  apply WidePullback.hom_ext
  · intro j
    simp only [Category.assoc, Category.id_comp]
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [ofPb, WidePullback.lift_π]; simp only [Fin.cases_zero]; rw [toPb, pullback.lift_snd]
    · rw [ofPb, WidePullback.lift_π]; simp only [Fin.cases_succ]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_π]
  · simp only [Category.assoc, Category.id_comp]
    rw [ofPb, WidePullback.lift_base, toPb, pullback.lift_snd_assoc, WidePullback.π_arrow]

theorem ofPb_toPb (n : ℕ) : ofPb f n ≫ toPb f n = 𝟙 _ := by
  apply pullback.hom_ext
  · apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, Category.id_comp]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_π, ofPb, WidePullback.lift_π]
      simp only [Fin.cases_succ]
    · simp only [Category.assoc, Category.id_comp]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_base, ofPb, WidePullback.lift_base, pullback.condition]
  · simp only [Category.assoc, Category.id_comp]
    rw [toPb, pullback.lift_snd, ofPb, WidePullback.lift_π]
    simp only [Fin.cases_zero]

theorem base_zero_iso : IsIso (WidePullback.base (fun _ : Fin 0 => f)) :=
  ⟨⟨WidePullback.lift (𝟙 X) (fun j => j.elim0) (fun j => j.elim0), by
    refine ⟨WidePullback.hom_ext _ _ _ (fun j => j.elim0) (by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]), by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]⟩⟩⟩

theorem base_proper [IsProper f] : ∀ n : ℕ, IsProper (WidePullback.base (fun _ : Fin n => f))
  | 0 => by
    have := base_zero_iso f
    first | infer_instance | exact MorphismProperty.of_isIso (P := @IsProper) _
  | n + 1 => by
    have := base_proper n
    have hi : IsIso (toPb f n) := ⟨⟨ofPb f n, toPb_ofPb f n, ofPb_toPb f n⟩⟩
    have : WidePullback.base (fun _ : Fin (n + 1) => f) = toPb f n ≫ pullback.fst _ _ ≫ WidePullback.base _ := by
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_base]
    rw [this]
    infer_instance

def eIso (n : ℕ) : yoneda.obj (W f n) ≅ widePullback (yoneda.obj X) (fun _ : Fin n => yoneda.obj Y) (fun _ => yoneda.map f) :=
  preservesLimitIso yoneda _ ≪≫ HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

end Geo

theorem LeafTerms_of : LateralTheory.E.LeafSSCut.LeafTerms := by
  intro _ R _ F Y X f _ r m hZ
  refine finite_of_iso ((chainsXIso R (cech f) r) ≪≫ (free R).mapIso (eIso f (r + 1)).symm) F m ?_
  exact finite_single_of_H _ F m (hZ _ _ (base_proper f (r + 1)))

end LateralTheory.E.LeafTermsPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafFiltPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.LeafFiltPf

abbrev Sg {R : Type} [CommRing R] (X : Shv R) : Cx R := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj X

variable {R : Type} [CommRing R] (K : Cx R) (F : Shv R) (n : ℤ)

theorem coe_sub' {K L : Cx R} {m : ℤ} (a b : Cocycle K L m) :
    ((a - b : Cocycle K L m) : Cochain K L m) = (a : Cochain K L m) - (b : Cochain K L m) := rfl

theorem coe_zero' {K L : Cx R} {m : ℤ} : ((0 : Cocycle K L m) : Cochain K L m) = 0 := rfl

theorem res_zero (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) := by
  have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 q (by omega)

def V (s : ℤ) (z : Cocycle K (res R F) n) : Prop := ∀ p q (h : p + n = q), s < p → z.1.v p q h = 0

def S (s : ℤ) : Set (HK R K F n) := {x | ∃ z : Cocycle K (res R F) n, CohomologyClass.mk z = x ∧ V K F n s z}

theorem memS {s : ℤ} {x : HK R K F n} (h : x ∈ S K F n s) :
    ∃ z : Cocycle K (res R F) n, CohomologyClass.mk z = x ∧ V K F n s z := h

theorem cocyc (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    z.1.v s d hd ≫ (res R F).d d (d + 1) = 0 := by
  have h0 := Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) s (d + 1) (by omega)
  rw [δ_v n (n + 1) rfl _ s (d + 1) _ d (s + 1) (by omega) rfl, hz (s + 1) (d + 1) (by omega) (by omega)] at h0
  simpa using h0

def clsC (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    Cocycle (Sg (K.X s)) (res R F) d :=
  Cocycle.fromSingleMk (z.1.v s d hd) (zero_add d) (d + 1) rfl (cocyc K F n s d hd z hz)

theorem clsC_v (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    (clsC K F n s d hd z hz).1.v 0 d (zero_add d) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).hom ≫ z.1.v s d hd :=
  Cochain.fromSingleMk_v _ _

theorem CB (X : Shv R) (d : ℤ) (c : Cocycle (Sg X) (res R F) d) (hc : CohomologyClass.mk c = 0) (e : ℤ)
    (he : e + 1 = d) : ∃ β : Cochain (Sg X) (res R F) e,
      β.v 0 e (zero_add e) ≫ (res R F).d e d = c.1.v 0 d (zero_add d) := by
  obtain ⟨m, hm, β, hβ⟩ := (CohomologyClass.mk_eq_zero_iff c).1 hc
  obtain rfl : e = m := by omega
  refine ⟨β, ?_⟩
  have := Cochain.congr_v hβ 0 d (zero_add d)
  rw [δ_v e d hm β 0 d _ e 1 (by omega) rfl] at this
  have hz1 : IsZero ((Sg X).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
  rw [hz1.eq_of_tgt ((Sg X).d 0 1) 0] at this
  simpa using this

theorem KL (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) (e : ℤ) (he : e + 1 = d)
    (β : Cochain (Sg (K.X s)) (res R F) e)
    (hβ : β.v 0 e (zero_add e) ≫ (res R F).d e d =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).hom ≫ z.1.v s d hd) :
    ∃ w : Cocycle K (res R F) n, CohomologyClass.mk w = CohomologyClass.mk z ∧ V K F n (s - 1) w := by
  let g : K.X s ⟶ (res R F).X e :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).inv ≫ β.v 0 e (zero_add e)
  let hh : Cochain K (res R F) (n - 1) := Cochain.single g (n - 1)
  let D : Cocycle K (res R F) n := Cocycle.mk (δ (n - 1) n hh) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - D, ?_, ?_⟩
  · have hD : CohomologyClass.mk D = 0 := (CohomologyClass.mk_eq_zero_iff D).2 ⟨n - 1, by omega, hh, rfl⟩
    rw [CohomologyClass.mk_sub, hD, sub_zero]
  · intro p q hpq hp
    have hDv : D.1.v p q hpq = (δ (n - 1) n hh).v p q hpq := rfl
    simp only [coe_sub', Cochain.sub_v, hDv]
    rw [δ_v (n - 1) n (by omega) hh p q hpq (q - 1) (p + 1) rfl rfl]
    rcases lt_or_eq_of_le (show s ≤ p by omega) with h | h
    · rw [hz p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
        Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp
    · subst h
      obtain rfl : q = d := by omega
      obtain rfl : e = q - 1 := by omega
      rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp only [g, Category.assoc, hβ, Iso.inv_hom_id_assoc, comp_zero, smul_zero, add_zero, sub_self]

theorem step (s d : ℤ) (hd : s + n = d) [Finite (HK R (Sg (K.X s)) F d)] (hS : (S K F n (s - 1)).Finite) :
    (S K F n s).Finite := by
  classical
  let φ : HK R K F n → HK R (Sg (K.X s)) F d := fun x =>
    if h : x ∈ S K F n s then CohomologyClass.mk (clsC K F n s d hd (memS K F n h).choose (memS K F n h).choose_spec.2) else 0
  have key : ∀ x ∈ S K F n s, ∀ x' ∈ S K F n s, φ x = φ x' → x - x' ∈ S K F n (s - 1) := by
    intro x hx x' hx' he
    simp only [φ, dif_pos hx, dif_pos hx'] at he
    have hz := (memS K F n hx).choose_spec
    have hz' := (memS K F n hx').choose_spec
    have h0 : CohomologyClass.mk (clsC K F n s d hd (memS K F n hx).choose hz.2 -
        clsC K F n s d hd (memS K F n hx').choose hz'.2) = 0 := by
      rw [CohomologyClass.mk_sub, he, sub_self]
    obtain ⟨β, hβ⟩ := CB F (K.X s) d _ h0 (d - 1) (by omega)
    have hV : V K F n s ((memS K F n hx).choose - (memS K F n hx').choose) := by
      intro p q h hp
      simp [Cochain.sub_v, hz.2 p q h hp, hz'.2 p q h hp]
    obtain ⟨w, hw, hwV⟩ := KL K F n s d hd _ hV (d - 1) (by omega) β (by
      rw [hβ]
      simp only [coe_sub', Cochain.sub_v, clsC_v, Preadditive.comp_sub])
    exact ⟨w, by rw [hw, CohomologyClass.mk_sub, hz.1, hz'.1], hwV⟩
  let g : HK R (Sg (K.X s)) F d → HK R K F n := fun t =>
    if h : ∃ x ∈ S K F n s, φ x = t then h.choose else 0
  refine ((Set.finite_univ.prod hS).image (fun p => g p.1 + p.2)).subset ?_
  intro x hx
  have h : ∃ y ∈ S K F n s, φ y = φ x := ⟨x, hx, rfl⟩
  refine ⟨(φ x, x - g (φ x)), ⟨trivial, ?_⟩, ?_⟩
  · have hg : g (φ x) = h.choose := by simp only [g, dif_pos h]
    rw [hg]
    exact key x hx _ h.choose_spec.1 h.choose_spec.2.symm
  · simp

theorem base (s : ℤ) (hs : s + n < 0) : S K F n s ⊆ {0} := by
  rintro x ⟨z, rfl, hz⟩
  have : z = 0 := by
    refine Cocycle.ext (Cochain.ext _ _ (fun p q hpq => ?_))
    rw [coe_zero', Cochain.zero_v]
    rcases lt_or_ge s p with h | h
    · exact hz p q hpq h
    · exact (res_zero F q (by omega)).eq_of_tgt (z.1.v p q hpq) 0
  simp [this]

theorem LeafFilt_of : LateralTheory.E.LeafSSCut.LeafFilt := by
  intro _ R _ K _ F n hfin
  have ind : ∀ k : ℕ, ∀ r : ℕ, 1 ≤ r → n < r + k → (S K F n (-(r : ℤ))).Finite := by
    intro k
    induction k with
    | zero => intro r _ hr; exact (Set.finite_singleton 0).subset (base K F n _ (by push_cast at hr; omega))
    | succ k ih =>
      intro r hr1 hr
      by_cases hk : n < r + k
      · exact ih r hr1 hk
      · have : Finite (HK R (Sg (K.X (-(r : ℤ)))) F (n - r)) := hfin r (by omega) (by push_cast at hr; omega)
        have h2 := ih (r + 1) (by omega) (by push_cast at hr ⊢; omega)
        have e : (-((r + 1 : ℕ) : ℤ)) = -(r : ℤ) - 1 := by push_cast; ring
        rw [e] at h2
        exact step K F n (-(r : ℤ)) (n - r) (by omega) h2
  have hS := ind n.toNat 1 le_rfl (by omega)
  have e : (-((1 : ℕ) : ℤ)) = (0 : ℤ) - 1 := by norm_num
  rw [e] at hS
  have hsub : ((HK.pull R (LateralTheory.E.LeafSSCut.incl0 K) F n).ker : Set (HK R K F n)) ⊆ S K F n (0 - 1) := by
    intro x hx
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    have hz : V K F n 0 z := fun p q hpq hp =>
      (CochainComplex.isZero_of_isStrictlyLE K 0 p hp).eq_of_src _ _
    have hc : CohomologyClass.mk (zcomp (Cocycle.ofHom (LateralTheory.E.LeafSSCut.incl0 K)) z (zero_add n)) = 0 := hx
    obtain ⟨β, hβ⟩ := CB F (K.X 0) n _ hc (n - 1) (by omega)
    obtain ⟨w, hw, hwV⟩ := KL K F n 0 n (zero_add n) z hz (n - 1) (by omega) β (by
      rw [hβ]
      change ((Cochain.ofHom (LateralTheory.E.LeafSSCut.incl0 K)).comp z.1 (zero_add n)).v 0 n (zero_add n) = _
      rw [Cochain.comp_v _ _ (zero_add n) 0 0 n (by omega) (by omega), Cochain.ofHom_v]
      simp [LateralTheory.E.LeafSSCut.incl0, HomologicalComplex.mkHomFromSingle_f])
    exact ⟨w, hw, hwV⟩
  exact (hS.subset hsub).to_subtype

end LateralTheory.E.LeafFiltPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DiagonalComparison
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.DiagonalComparison

theorem hkpull_comp {R : Type} [CommRing R] {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (a ≫ b) F n x = HK.pull R a F n (HK.pull R b F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre, zcomp, Cochain.ofHom_comp]

def diag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality := by
    intro a b g
    apply WidePullback.hom_ext
    · intro j
      dsimp [sch, cech]
      simp only [Category.id_comp, Category.assoc]
      erw [WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
    · dsimp [sch, cech]
      simp only [Category.id_comp, Category.assoc]
      erw [WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]

theorem diag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : diag f ≫ cechAug f = sch.map f := by
  apply NatTrans.ext; funext n
  erw [NatTrans.comp_app]
  simp only [cechAug, Arrow.augmentedCechNerve_hom_app]
  erw [WidePullback.lift_base]
  rfl

theorem lift_iso {C : Type*} [Category C] {B A : C} (h : A ⟶ B)
    [HasWidePullback B (fun _ : Fin 1 => A) (fun _ => h)] :
    IsIso (WidePullback.lift h (fun _ : Fin 1 => 𝟙 A) (fun _ => Category.id_comp _) :
      A ⟶ widePullback B (fun _ : Fin 1 => A) (fun _ => h)) := by
  refine ⟨⟨WidePullback.π _ 0, ?_, ?_⟩⟩
  · rw [WidePullback.lift_π]
  apply WidePullback.hom_ext
  · intro j
    obtain rfl := Fin.fin_one_eq_zero j
    rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, WidePullback.lift_base, Category.id_comp, WidePullback.π_arrow]

instance isIso_cech_nerve_diagonal_app_degree_zero {Y X : Scheme.{0}} (f : Y ⟶ X) : IsIso ((diag f).app (op (SimplexCategory.mk 0))) :=
  lift_iso (C := PSh) (yoneda.map f)

instance isIso_etale_chains_map_cech_diagonal_degree_zero {R : Type} [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) :
    IsIso (((chains R).map (diag f)).f 0) := by
  change IsIso ((HomologicalComplex.extendMap ((chainsN R).map (diag f)) ComplexShape.embeddingDownNat).f 0)
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by simp)]
  have : IsIso (((chainsN R).map (diag f)).f 0) := by
    change IsIso ((free R).map ((diag f).app (op (SimplexCategory.mk 0))))
    infer_instance
  infer_instance

theorem etale_chains_degree_zero_inclusion_factors_through_cech_diagonal {R : Type} [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map (inv (((chains R).map (diag f)).f 0)) ≫
      LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (sch.obj Y)) ≫ (chains R).map (diag f) =
    LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (cech f)) := by
  apply HomologicalComplex.from_single_hom_ext
  simp [LateralTheory.E.LeafSSCut.incl0, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self]

theorem LeafCompare_of : LateralTheory.E.LeafSSCut.LeafCompare := by
  intro _ R _ F Y X f n hE _
  have key : ∀ x, pull R (sch.map f) F n x = 0 →
      HK.pull R (LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (cech f))) F n (pull R (cechAug f) F n x) = 0 := by
    intro x hx
    rw [← etale_chains_degree_zero_inclusion_factors_through_cech_diagonal f, hkpull_comp, hkpull_comp]
    have h0 : HK.pull R ((chains R).map (diag f)) F n (pull R (cechAug f) F n x) = 0 := by
      rw [← hx, ← diag_aug f, pull_comp]; rfl
    rw [h0, map_zero, map_zero]
  let φ : (pull R (sch.map f) F n).ker →
      (HK.pull R (LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (cech f))) F n).ker :=
    fun x => ⟨pull R (cechAug f) F n x.1, AddMonoidHom.mem_ker.2 (key x.1 (AddMonoidHom.mem_ker.1 x.2))⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact (hE n).1 (congrArg Subtype.val hxy)
  exact Finite.of_injective φ hφ

end LateralTheory.E.DiagonalComparison
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafPtPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

theorem eq_generic_of_dim {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) (x : X) :
    x = genericPoint X := by
  have hmax := (Order.krullDim_nonpos_iff_forall_isMax).1 hd
  let S : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hST : S ≤ T := fun _ _ => Set.mem_univ _
  have hTS : T ≤ S := hmax S hST
  have h1 : genericPoint X ⤳ x := genericPoint_specializes x
  have h2 : x ⤳ genericPoint X := by
    rw [specializes_iff_mem_closure]
    exact hTS (Set.mem_univ (genericPoint X))
  exact (h2.antisymm h1).eq

theorem subsingleton_of_dim {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) : Subsingleton X :=
  ⟨fun x y => (eq_generic_of_dim hd x).trans (eq_generic_of_dim hd y).symm⟩

theorem leafPtIso (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    (hd : topologicalKrullDim X ≤ 0) : IsIso p := by
  haveI := subsingleton_of_dim hd
  haveI : IsAffine X := inferInstance
  let F : CommRingCat.of k ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso _).inv ≫ p.appTop
  have hfin : p.appTop.hom.Finite := finite_appTop_of_universallyClosed k p
  have hFfin : F.hom.Finite := by
    simp only [F, CommRingCat.hom_comp]
    exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective)
  letI : Algebra k Γ(X, ⊤) := F.hom.toAlgebra
  haveI : Algebra.IsIntegral k Γ(X, ⊤) := ⟨fun a => hFfin.to_isIntegral a⟩
  have hb : Function.Bijective F.hom := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))
  haveI : IsIso F := (ConcreteCategory.isIso_iff_bijective F).2 hb
  haveI : IsIso p.appTop := by
    have : p.appTop = (Scheme.ΓSpecIso _).hom ≫ F := by simp [F]
    rw [this]; infer_instance
  have e : p = X.isoSpec.hom ≫ Spec.map p.appTop ≫ (Sp k).isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]; infer_instance

theorem sh_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k] : SH k := by
  refine ⟨inferInstance, ?_⟩
  have hb : Function.Bijective (IsLocalRing.residue k) := by
    exact ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField k) := IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hb)
  infer_instance

theorem finite_sp (hH : Hyps) (h0 : H0TwistOverClosedField) (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k))
    (n i : ℤ) : Finite (Ht q (sch.obj (Sp k)) n i) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (hH.2.2.2.2.2.2.2.1 (ZMod q) (tw q i)).1 (sch.obj (Sp k)) n hn
    exact Finite.of_subsingleton
  · exact (h0 hH q k hq i).1
  · haveI := hH.2.2.2.2.2.2.2.2.2.2.2.1 (ZMod q) k (sh_of_isAlgClosed k) (tw q i) n hn
    exact Finite.of_subsingleton

theorem LeafPt_of (h0 : H0TwistOverClosedField) : LeafPt := by
  intro hH q _ k _ _ hq X _ p _ hd n i
  have := leafPtIso k p hd
  haveI := finite_sp hH h0 q k hq n i
  refine Finite.of_injective (pull (ZMod q) (sch.map (inv p)) (tw q i) n) ?_
  intro x y hxy
  have key : ∀ z : Ht q (sch.obj X) n i,
      pull (ZMod q) (sch.map p) (tw q i) n (pull (ZMod q) (sch.map (inv p)) (tw q i) n z) = z := by
    intro z
    rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [← key x, ← key y, hxy]

end LateralTheory.E.E4
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleTopology
namespace UpperTheory.Et.EtaleTopology

variable (hB6 : GlobalTheory.EtC.DivisorPicardCompatibility)
include hB6

theorem top : LateralTheory.E.EtaleChapterEFour := by
  have a0 : LateralTheory.E.E4.H0TwistOverClosedField := UpperTheory.leafH0_holds
  have a1 : LateralTheory.E.E4.LeafPt := LateralTheory.E.E4.LeafPt_of a0
  have a2 : LateralTheory.E.E4.LeafCoprod := LateralTheory.E.LeafCoprodPf.LeafCoprod_of
  have a3 : LateralTheory.E.E4.LeafCompGeom := LateralTheory.E.E4.leafCompGeom
  have a4 : LateralTheory.E.E4.LeafComp := LateralTheory.E.E4.LeafComp_of a2 a3
  have a5 : LateralTheory.E.E4.LeafDesc := UpperTheory.curve_etale_descent
  have a6 : LateralTheory.E.LeafSSCut.LeafFilt := LateralTheory.E.LeafFiltPf.LeafFilt_of
  have a7 : LateralTheory.E.LeafSSCut.LeafCompare := LateralTheory.E.DiagonalComparison.LeafCompare_of
  have a8 : LateralTheory.E.LeafSSCut.LeafTerms := LateralTheory.E.LeafTermsPf.LeafTerms_of
  have a9 : LateralTheory.E.E4.LeafSS := LateralTheory.E.LeafSSCut.goal_of a6 a7 a8
  have a10 : LateralTheory.E.E4.LeafUnits := LateralTheory.E.CurveUnitsOrderAtInfinity.LeafUnits_of
  have a11 : LateralTheory.E.LeafPicCut.LeafSelPic := LateralTheory.E.LeafSelPicPf.LeafSelPic_of
  have a12 : LateralTheory.E.LeafIntClosureAlgPf.LeafIntClFinite := UpperTheory.integralClosure_finite_of_finiteType_domain
  have a13 : LateralTheory.E.LeafNormalModelPf.LeafIntClosureAlg := LateralTheory.E.LeafIntClosureAlgPf.LeafIntClosureAlg_of a12
  have a14 : LateralTheory.E.LeafGlueProperPf.LeafGlueExists := LateralTheory.E.GluingExistence.LeafGlueExists_of
  have a15 : LateralTheory.E.LeafGlueProperPf.LeafGlueIntegral := LateralTheory.E.LeafGlueProperPf.glued_affine_curve_is_integral_scheme
  have a16 : LateralTheory.E.LeafGlueProperPf.LeafGlueNormal := LateralTheory.E.LeafGlueProperPf.glued_affine_curve_stalks_integrally_closed
  have a17 : LateralTheory.E.LeafGlueProperPf.LeafGlueDim := LateralTheory.E.LeafGlueDimPf.LeafGlueDim_of
  have a18 : LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep := LateralTheory.E.GluedCurveSeparated.LeafGlueSep_of
  have a19 : LateralTheory.E.LeafGlueIsProperPf.LeafGlueExistence := UpperTheory.Cb.properGluing_existence
  have a20 : LateralTheory.E.LeafGlueProperPf.LeafGlueIsProper := LateralTheory.E.LeafGlueIsProperPf.LeafGlueIsProper_of a18 a19
  have a21 : LateralTheory.E.LeafGlueProperPf.LeafGlueGeneric := LateralTheory.E.LeafGlueGenericPf.glued_curve_generic_point_maps_to_function_field
  have a22 : LateralTheory.E.LeafNormalModelPf.LeafGlueProper := LateralTheory.E.LeafGlueProperPf.LeafGlueProper_of a14 a15 a16 a17 a20 a21
  have a23 : LateralTheory.E.LeafModelCurveCut.ExistsNormalProperCurveModel := LateralTheory.E.LeafNormalModelPf.LeafNormalModel_of a13 a22
  have a24 : LateralTheory.E.LeafSmoothOfNormalPf.LeafStalkSmoothClosed := LateralTheory.E.LeafStalkSmoothClosedPf.LeafStalkSmoothClosed_of
  have a25 : LateralTheory.E.LeafSmoothOfNormalPf.LeafRelDimOne := LateralTheory.E.LeafRelDimOnePf.LeafRelDimOne_of
  have a26 : LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := LateralTheory.E.LeafSmoothOfNormalPf.LeafSmoothOfNormal_of a24 a25
  have a27 : LateralTheory.E.LeafCurveVCut.LeafModelCurve := LateralTheory.E.LeafModelCurveCut.goal_of a23 a26
  have a28 : LateralTheory.E.E4.LeafPic := UpperTheory.curve_picard_of_selmerPicard_of_modelCurve a11 a27
  have a29 : LateralTheory.E.LeafTwistPf.LeafLoc := LateralTheory.E.LeafTwistIsoPf.leafLoc
  have a30 : LateralTheory.E.LeafTwistPf.LeafTwSec := LateralTheory.E.LeafTwistIsoPf.leafTwSec
  have a31 : LateralTheory.E.LeafKumCut.LeafTwist := LateralTheory.E.LeafTwistPf.LeafTwist_of a29 a30
  have a32 : LateralTheory.E.LeafKumCut.EtaleFirstCohomologyMultiplicativeGroupPicard := (fun _ => hB6)
  have a33 : LateralTheory.E.LeafKumCut.LeafKumSeq := LateralTheory.E.LeafKumFieldPf.kumSeq
  have a34 : LateralTheory.E.E4.LeafKum := LateralTheory.E.LeafKumCut.goal_of a31 a32 a33
  have a35 : LateralTheory.E.E4.LeafCurve := UpperTheory.leafCurve_of_leafH0 a0
  have a36 : LateralTheory.E.LeafKillCut.LeafOne := UpperTheory.Cb.curve_cohomology_killed_by_finite_cover a0
  have a37 : LateralTheory.E.E4.LeafKill := LateralTheory.E.LeafKillCut.goal_of a36
  have a38 : LateralTheory.E.LeafCurveVCut.LeafFibreField := LateralTheory.E.LeafFibreFieldPf.LeafFibreField_of
  have a39 : LateralTheory.E.LeafCurveVCut.LeafTrdegDim := LateralTheory.E.LeafTrdegDimPf.LeafTrdegDim_of
  have a40 : LateralTheory.E.LeafCurveVCut.LeafBaseChangeField := LateralTheory.E.LeafBaseChangeFieldPf.LeafBaseChangeField_of
  have a41 : LateralTheory.E.LeafExtendCut.LeafStalkValuation := LateralTheory.E.LeafStalkValuationPf.LeafStalkValuation_of
  have a42 : LateralTheory.E.LeafExtendCut.LeafLocalExtend := LateralTheory.E.LeafLocalExtendPf.LeafLocalExtend_of
  have a43 : LateralTheory.E.LeafExtendCut.LeafGlueExtend := LateralTheory.E.LeafGlueExtendPf.LeafGlueExtend_of
  have a44 : LateralTheory.E.LeafCurveVCut.LeafExtend := LateralTheory.E.LeafExtendCut.goal_of a41 a42 a43
  have a45 : LateralTheory.E.LeafGeoVCut.LeafCurveV := LateralTheory.E.LeafCurveVCut.goal_of a38 a39 a40 a27 a44
  have a46 : LateralTheory.E.LeafDescendVCut.LeafDimBound := LateralTheory.E.LeafDimBoundPf.LeafDimBound_of
  have a47 : LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall := LateralTheory.E.CurveKrullDim.LeafCurveSmall_of a46
  have a48 : LateralTheory.E.QuotientFieldNonconstantLift.LeafLiftNonconst := LateralTheory.E.NonconstantLift.LeafLiftNonconst_of
  have a49 : LateralTheory.E.QuasiFiniteDescent.LeafQFOmega := LateralTheory.E.QuotientFieldNonconstantLift.LeafQFOmega_of a47 a48
  have a50 : LateralTheory.E.LeafObjFPPf.LeafObjAff := LateralTheory.E.LeafObjAffPf.LeafObjAff_of
  have a51 : LateralTheory.E.LeafObjGluePf.LeafGlueTwo := LateralTheory.E.LeafGlueTwoPfQS.LeafGlueTwo_of
  have a52 : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct := LateralTheory.E.LeafQCQSInductPf.LeafQCQSInduct_of
  have a53 : LateralTheory.E.LeafInclPiecePf.LeafInclMap := UpperTheory.Cb.pullback_isLimit_over_fg_subalgebras
  have a54 : LateralTheory.E.LeafInclPiecePf.LeafInclOpen := UpperTheory.Cb.isOpenImmersion_inclusion_of_piecewise
  have a55 : LateralTheory.E.LeafInclDescendPf.LeafInclPiece := LateralTheory.E.LeafInclPiecePf.LeafInclPiece_of a53 a54
  have a56 : LateralTheory.E.LeafMapFPPf.LeafLimFP := LateralTheory.E.LeafLimFPPf.isLimit_pullback_finitelyGenerated
  have a57 : LateralTheory.E.LeafPairRelPf.LeafFactorStage := UpperTheory.Cb.descent_map_factors_through_stage
  have a58 : LateralTheory.E.QuasiFiniteDescent.LeafDescendPreMap := LateralTheory.E.DiagramDescent.LeafDescendPreMap_of a50 a51 a52 a55 a56 a57
  have a59 : LateralTheory.E.LeafSpreadSeparatedPf.LeafClosedImmSpread := LateralTheory.E.LeafClosedImmSpreadPf.LeafClosedImmSpread_of
  have a60 : LateralTheory.E.LeafSpreadSeparatedPf.LeafDiagBC := LateralTheory.E.LeafSpreadSeparatedPf.separated_base_change_iff_diagonal_closed_immersion_holds
  have a61 : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated := LateralTheory.E.LeafSpreadSeparatedPf.of_two a59 a60
  have a62 : LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadRelDim := LateralTheory.E.LeafSpreadRelDimPf.LeafSpreadRelDim_of
  have a63 : LateralTheory.E.SpreadingOutSmoothness.LeafStalkOfAlg := LateralTheory.E.StalkOfAlgebra.LeafStalkOfAlg_of
  have a64 : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1 := LateralTheory.E.SpreadingOutSmoothness.LeafSpreadSmooth1_of a62 a63
  have a65 : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafQFAtDescend := LateralTheory.E.QuasiFiniteAtDescent.LeafQFAtDescend_of
  have a66 : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafOpenSpread := LateralTheory.E.OpenSpreadingOut.etale_open_spreading_out_over_finitely_generated_subalgebra
  have a67 : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap := LateralTheory.E.LeafSpreadLQFMap_vtuPfG.LeafSpreadLQFMap_of a65 a66
  have a68 : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph := LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut.LeafSpreadLQFGraph_of a67
  have a69 : LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF := LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange.LeafSpreadQF_of a61 a64 a68 a67
  have a70 : LateralTheory.E.LeafDescendVCut.LeafIrred := LateralTheory.E.LeafIrredPf.LeafIrred_of
  have a71 : LateralTheory.E.QuasiFiniteDescent.LeafReducedSmooth := LateralTheory.E.ReducedOfSmooth.LeafReducedSmooth_of
  have a72 : LateralTheory.E.LeafGeoVV2Cut.LeafDescendQF := LateralTheory.E.QuasiFiniteDescent.goal_of a49 a58 a69 a70 a71 a46
  have a73 : LateralTheory.E.LeafCloseBCut.LeafProjModel := LateralTheory.E.LeafProjModelPfImm.LeafProjModel_of
  have a74 : LateralTheory.E.LeafCloseBCut.LeafDimOpen := LateralTheory.E.LeafDimOpenPf.LeafDimOpen_of
  have a75 : LateralTheory.E.LeafSpreadVCut.LeafCloseB := LateralTheory.E.LeafCloseBCut.goal_of a73 a74
  have a76 : LateralTheory.E.LeafGeoVV2Cut.LeafExtendZMT := UpperTheory.Cb.extension_by_zero_of_zariski_quasi_finite_factorization
  have a77 : LateralTheory.E.LeafGeoVV2Cut.CurveThroughGenericPointSpreadsToSmoothProperFamily := LateralTheory.E.LeafGeoVV2Cut.spread_of a72 a75 a76
  have a78 : LateralTheory.E.LeafGeoCut.LeafGeoV := LateralTheory.E.LeafGeoVV2Cut.geoV_of a45 a77
  have a79 : LateralTheory.E.LeafGeoCut.LeafClosed := LateralTheory.E.LeafClosedPf.LeafClosed_of
  have a80 : LateralTheory.E.LeafGeoCut.LeafBdry := LateralTheory.E.LeafBdryPf.LeafBdry_of
  have a81 : LateralTheory.E.E4.LeafGeo := LateralTheory.E.LeafGeoCut.goal_of a78 a79 a80
  have a82 : LateralTheory.E.E4.LeafSpec := UpperTheory.Cb.geometric_fibre_cohomology_constant
  have a83 : LateralTheory.E.LeafGhostCut.LeafRelExact := LateralTheory.E.LeafGhostCut.relExact
  have a84 : LateralTheory.E.LeafGhostCut.LeafRelNat := LateralTheory.E.LeafInj0WPf.leafRelNat
  have a85 : LateralTheory.E.LeafGhostRelCut.LeafTrunc := LateralTheory.E.LeafGhostRelCut.LeafTrunc_of
  have a86 : LateralTheory.KummerTheory.InjSlice := LateralTheory.Fin.InjSlice.intersectionNumber_baseChange
  have a87 : LateralTheory.EWeil.AcycPf.RestrInj := UpperTheory.Cb.restrInj
  have a88 : LateralTheory.E.LeafConsPf.LeafLoc := UpperTheory.leafLocalization_of_injective_slice_of_restriction_injective a86 a87
  have a89 : LateralTheory.E.EtaleTopologySheaves.LeafCons := LateralTheory.E.LeafConsPfC.LeafCons_of a88
  have a90 : LateralTheory.E.LeafDegCut.LeafNeg := LateralTheory.E.LeafNegPf.LeafNeg_of
  have a91 : LateralTheory.E.LeafShMapZeroPf.EtaleLift' := UpperTheory.Cb.free_etale_sheaf_lift_exists
  have a92 : LateralTheory.E.LeafShMapZeroPf.Gen.EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators := LateralTheory.E.DegreeZeroGenerators.free_etale_sheaf_zmod_representable_generates
  have a93 : LateralTheory.E.LeafDegCut.LeafShMapZero := LateralTheory.E.LeafShMapZeroPf.Glue.LeafShMapZero_of a91 a92
  have a94 : LateralTheory.E.LeafShIsoPf.EtaleDerivedDegreeZeroHomologyLocallyLifts := LateralTheory.E.H0Lifting.etale_sheaf_epi_lifts_degree_zero_derived_maps_locally
  have a95 : LateralTheory.E.LeafShIsoPf.EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes := LateralTheory.E.H0Kernel.etale_sheaf_zeroth_cohomology_kernel_exact
  have a96 : LateralTheory.E.LeafShIsoPf.Sh.LeafSecRep := LateralTheory.E.LeafSecRepPf.LeafSecRep_of
  have a97 : LateralTheory.E.LeafDegCut.LeafShIso := LateralTheory.E.LeafShIsoPf.Glue.LeafShIso_of a94 a95 a96
  have a98 : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd := UpperTheory.Cb.etale_cohomology_class_killed_on_neighborhood
  have a99 : LateralTheory.E.LeafVan0Pf.LeafVanStalk := LateralTheory.E.StalkVanishing.goal_of a98
  have a100 : LateralTheory.E.LeafVan0Pf.LeafVanW := LateralTheory.E.LeafVanWPf.LeafVanW_of
  have a101 : LateralTheory.E.LeafVan0Pf.LeafVanV := LateralTheory.E.LeafVanVPf.LeafVanV_of
  have a102 : LateralTheory.E.LeafDegCut.LeafVan0 := LateralTheory.E.LeafVan0Pf.LeafVan0_of a99 a100 a101
  have a103 : LateralTheory.E.SecondDegreeKilling.LeafPtW := LateralTheory.E.PointEvaluationWitness.LeafPtW_of
  have a104 : LateralTheory.E.SecondDegreeKilling.LeafPtV := LateralTheory.E.LeafPtVPf.LeafPtV_of
  have a105 : LateralTheory.E.LeafDegCut.LeafKill2 := LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKill2_of a98 a103 a104
  have a106 : LateralTheory.E.LeafDegCut.LeafKill1 := LateralTheory.E.LeafKill1V2Cut.goal_of' a98 a103 a104
  have a107 : LateralTheory.E.LeafSHSysPf.LeafRingSys := UpperTheory.Cb.sepClosed_point_filtered_etale_colimit
  have a108 : LateralTheory.E.LeafSHSysPf.LeafNSysGlue := LateralTheory.E.NeighbourhoodSystemGluing.LeafNSysGlue_of a107
  have a109 : LateralTheory.E.LeafVanBStalkPf.LeafSHSys := LateralTheory.E.LeafSHSysPf.LeafSHSys_of_glue a107 a108
  have a110 : LateralTheory.E.LeafVanBStalkPf.LeafSHCont := UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity
  have a111 : LateralTheory.E.LeafVanBStalkPf.LeafStalkPt := LateralTheory.E.LeafVanBStalkPf.stalkPt_of a109 a110
  have a112 : LateralTheory.E.LeafVanBPf.LeafVanBStalk := LateralTheory.E.LeafVanBStalkPf.LeafVanBStalk_of_pt a111
  have a113 : LateralTheory.E.LeafVanBPf.LeafClosedSHPos := LateralTheory.E.LeafClosedSHPosPf.LeafClosedSHPos_of
  have a114 : LateralTheory.E.LeafClosedSH0Pf.LeafSHSieve := LateralTheory.E.LeafSHSievePf.LeafSHSieve_of
  have a115 : LateralTheory.E.LeafVanBPf.LeafClosedSH0 := LateralTheory.E.LeafClosedSH0PfCut.LeafClosedSH0_of a114
  have a116 : LateralTheory.E.LeafDegCut.LeafVanB := LateralTheory.E.LeafVanBPf.LeafVanB_of a112 a113 a115
  have a117 : LateralTheory.E.LeafInj0WPf.LeafSecTw := UpperTheory.Cb.twistedSections_of_negativeDegreeVanishing a90
  have a118 : LateralTheory.E.LeafInj0Pf.LeafInj0W := LateralTheory.E.LeafInj0WPf.LeafInj0W_of a117
  have a119 : LateralTheory.E.StrictHenselianNeighbourhood.LeafSHNbSys := LateralTheory.E.EtaleNeighbourhoodSystem.LeafSHNbSys_of
  have a120 : LateralTheory.E.StrictHenselianNeighbourhood.LeafSHLoc := LateralTheory.E.StrictHenselianLocalization.LeafSHLoc_of
  have a121 : LateralTheory.E.StrictHenselianNeighbourhood.LeafSHHens := UpperTheory.Cb.strictlyHenselianLocal_of_negligibleDegree a90
  have a122 : LateralTheory.E.LeafSHPtPf.LeafSHNb := LateralTheory.E.StrictHenselianNeighbourhood.LeafSHNb_of a119 a120 a121
  have a123 : LateralTheory.E.LeafInj0VPf.LeafSHPt := LateralTheory.E.StrictHenselianPoint.LeafSHPt_of a122
  have a124 : LateralTheory.E.LeafInj0Pf.LeafInj0V := LateralTheory.E.LeafInj0VPf.LeafInj0V_of a123
  have a125 : LateralTheory.E.LeafDegCut.LeafInj0 := LateralTheory.E.LeafInj0Pf.LeafInj0_of a118 a124
  have a126 : LateralTheory.E.LeafSurj0Pf.LeafSurj0W := LateralTheory.E.LeafSurj0WPf.LeafSurj0W_of
  have a127 : LateralTheory.E.LeafSurj0Pf.LeafSurj0V := UpperTheory.Cb.etale_cohomology_degree_zero_surjective_limit
  have a128 : LateralTheory.E.LeafDegCut.LeafSurj0 := LateralTheory.E.LeafSurj0Pf.LeafSurj0_of a126 a127
  have a129 : LateralTheory.E.EtaleTopologySheaves.LeafDeg := LateralTheory.E.LeafDegCut.goal_of a90 a93 a97 a102 a105 a106 a116 a125 a128
  have a130 : LateralTheory.E.LeafGhostRelCut.LeafRep := LateralTheory.E.EtaleTopologySheaves.goal_of a89 a129
  have a131 : LateralTheory.E.LeafGhostCut.LeafGhostRel := LateralTheory.E.LeafGhostRelCut.goal_of a85 a130
  have a132 : LateralTheory.E.E4.LeafGhost := LateralTheory.E.LeafGhostCut.goal_of_all a83 a84 a131
  have a133 : LateralTheory.E.EtaleChapterEFour := LateralTheory.E.E4.goal_of a0 a1 a4 a5 a9 a10 a28 a34 a35 a37 a81 a82 a132
  exact a133

end UpperTheory.Et.EtaleTopology
end

theorem UpperTheory.Et.e4 : LateralTheory.E.EtaleChapterEFour := UpperTheory.Et.EtaleTopology.top GlobalTheory.T.etale_descent_picard_group
