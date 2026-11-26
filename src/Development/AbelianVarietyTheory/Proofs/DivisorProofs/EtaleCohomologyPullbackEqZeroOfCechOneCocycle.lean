module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharOfIsPrimitiveRoot

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

def cechDiag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (arrows := fun _ : Fin (n.unop.len + 1) => yoneda.map f) (yoneda.map f)
    (fun _ => 𝟙 (yoneda.obj Y)) (fun _ => Category.id_comp _)
  naturality m n g := by
    apply WidePullback.hom_ext
    · intro j
      simp only [cech, Arrow.cechNerve]
      erw [Category.assoc, Category.assoc, WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
      rfl
    · simp only [cech, Arrow.cechNerve]
      erw [Category.assoc, Category.assoc, WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]
      rfl

theorem cechDiag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : cechDiag f ≫ GlobalTheory.EtC.cechAug f = sch.map f := by
  ext n : 1
  simp only [cechDiag, GlobalTheory.EtC.cechAug]
  erw [NatTrans.comp_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]
  rfl

theorem isCls_zero_deg_one (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    IsCls (R := R) (E := E) (n := 1) (0 : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F)
      (0 : H R E F ((1 : ℕ) : ℤ)) := by
  refine ⟨0, ?_, ?_⟩ <;> simp

theorem cechDiag_δ {Y X : Scheme.{0}} (f : Y ⟶ X) (i : Fin 3) :
    (cechDiag f).app (op ⦋2⦌) ≫ SimplicialObject.δ (cech f) i = (cechDiag f).app (op ⦋1⦌) := by
  rw [SimplicialObject.δ, ← NatTrans.naturality]
  simp [sch, disc]

theorem pull_sch_eq_zero (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X)
    (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F)
    (hs : cobd (R := R) (E := cech f) (n := 1) s = 0)
    (x : H R (sch.obj X) F ((1 : ℕ) : ℤ))
    (hx : IsCls (R := R) (E := cech f) (n := 1) s (pull R (GlobalTheory.EtC.cechAug f) F ((1 : ℕ) : ℤ) x)) :
    pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  have hc := congrArg (fun t => (free R).map ((cechDiag f).app (op ⦋2⦌)) ≫ t) hs
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul, ← Functor.map_comp_assoc, cechDiag_δ,
    comp_zero] at hc
  have hc' : ((free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s : (free R).obj ((sch.obj Y).obj (op ⦋2⦌)) ⟶ F) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hd : (free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s = 0 := hc'
  have h0 : pull R (cechDiag f) F ((1 : ℕ) : ℤ) (pull R (GlobalTheory.EtC.cechAug f) F ((1 : ℕ) : ℤ) x) = 0 := by
    obtain ⟨z, hzClass, hz⟩ := hx
    rw [← hzClass]
    simp only [pull, HK.pull, HK.pre, cpre_mk]
    rw [← CohomologyClass.mk_zero]
    apply congrArg CohomologyClass.mk
    apply Cocycle.ext
    change (Cochain.ofHom ((chains R).map (cechDiag f))).comp z.1 (zero_add _) = 0
    rw [hz, ClsBasic.ofHom_comp_single]
    simp only [← Category.assoc, ClsBasic.chainsXIso_nat]
    simp [Category.assoc, hd]
  rw [← cechDiag_aug f, pull_comp]
  exact h0

end GlobalTheory.CechOne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle :
    ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X)
      (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F),
      cobd (R := R) (E := cech f) (n := 1) s = 0 →
      ∀ x : H R (sch.obj X) F ((1 : ℕ) : ℤ),
        IsCls (R := R) (E := cech f) (n := 1) s (pull R (GlobalTheory.EtC.cechAug f) F ((1 : ℕ) : ℤ) x) →
        pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  intro R _ F Y X f s hs x hx
  have hc := congrArg (fun t => (free R).map ((cechDiag f).app (op ⦋2⦌)) ≫ t) hs
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul, ← Functor.map_comp_assoc,
    cechDiag_δ, comp_zero] at hc
  have hc' : ((free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s :
      (free R).obj ((sch.obj Y).obj (op ⦋2⦌)) ⟶ F) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hd : (free R).map ((cechDiag f).app (op ⦋1⦌)) ≫ s = 0 := hc'
  obtain ⟨z, hzClass, hz⟩ := hx
  rw [← cechDiag_aug f, pull_comp, ← hzClass]
  simp only [pull, HK.pull, HK.pre, cpre_mk]
  rw [← CohomologyClass.mk_zero]
  apply congrArg CohomologyClass.mk
  apply Cocycle.ext
  change (Cochain.ofHom ((chains R).map (cechDiag f))).comp z.1 (zero_add _) = 0
  rw [hz, ClsBasic.ofHom_comp_single]
  simp only [← Category.assoc, ClsBasic.chainsXIso_nat]
  simp [Category.assoc, hd]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsLimitWidePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsLimitWidePullback
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem specAdj_symm_comp_specMap (T : Scheme.{0}) {R S : CommRingCat.{0}}
    (f : T ⟶ Spec S) (φ : R ⟶ S) :
    ((ΓSpec.adjunction.homEquiv T (op R)).symm (f ≫ Spec.map φ)).unop =
      φ ≫ ((ΓSpec.adjunction.homEquiv T (op S)).symm f).unop := by
  have h := ΓSpec.adjunction.homEquiv_naturality_right_symm (X := T) (Y := op S) (Y' := op R)
    f φ.op
  exact congrArg Quiver.Hom.unop h

theorem spec_widePushout_isLimit : ∀ (n : ℕ) (C D A : Type) [CommRing C] [CommRing D] [CommRing A] (a : C →+* D) (b : C →+* A) (l : Fin n → (D →+* A)) (hl : ∀ i, (l i).comp a = b), (∀ (B : Type) [CommRing B] (g : Fin n → (D →+* B)) (c : C →+* B), (∀ i, (g i).comp a = c) → ∃! u : A →+* B, u.comp b = c ∧ ∀ i, u.comp (l i) = g i) → Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) (fun i => Spec.map (CommRingCat.ofHom (l i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i]))) := by
  intro n C D A _ _ _ a b l hl H
  classical
  let adj := ΓSpec.adjunction
  let e : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}), (op Γ(T, ⊤) ⟶ op R) ≃ (T ⟶ Spec R) :=
    fun T R => adj.homEquiv T (op R)
  have hcomp : ∀ (T : Scheme.{0}) {R S : CommRingCat.{0}} (f : T ⟶ Spec S) (φ : R ⟶ S),
      ((e T R).symm (f ≫ Spec.map φ)).unop = φ ≫ ((e T S).symm f).unop :=
    fun T R S f φ => specAdj_symm_comp_specMap T f φ
  have hse : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}) (ψ : R ⟶ Γ(T, ⊤)),
      ((e T R).symm (e T R ψ.op)).unop = ψ := fun T R ψ => by
    rw [Equiv.symm_apply_apply]; rfl
  have hinj : ∀ (T : Scheme.{0}) (R : CommRingCat.{0}) (f g : T ⟶ Spec R),
      ((e T R).symm f).unop = ((e T R).symm g).unop → f = g :=
    fun T R f g h => (e T R).symm.injective (Quiver.Hom.unop_inj h)

  let gOf : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))),
      Fin n → (D →+* Γ(t.pt, ⊤)) :=
    fun t i => ((e t.pt (CommRingCat.of D)).symm (t.π i)).unop.hom
  let cOf : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))),
      C →+* Γ(t.pt, ⊤) :=
    fun t => ((e t.pt (CommRingCat.of C)).symm t.base).unop.hom
  have hgc : ∀ t i, (gOf t i).comp a = cOf t := by
    intro t i
    have h1 := hcomp t.pt (t.π i) (CommRingCat.ofHom a)
    rw [t.condition i] at h1
    have h2 := congrArg CommRingCat.Hom.hom h1
    simpa [gOf, cOf] using h2.symm
  let uOf : ∀ t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a)), A →+* Γ(t.pt, ⊤) := fun t => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose
  have huOf : ∀ t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a)), (uOf t).comp b = cOf t ∧ ∀ i, (uOf t).comp (l i) = gOf t i :=
    fun t => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose_spec.1
  have huniq : ∀ (t : WidePullbackCone (fun _ : Fin n => Spec.map (CommRingCat.ofHom a))) (u : A →+* Γ(t.pt, ⊤)), u.comp b = cOf t → (∀ i, u.comp (l i) = gOf t i) →
      u = uOf t :=
    fun t u h1 h2 => (H Γ(t.pt, ⊤) (gOf t) (cOf t) (hgc t)).choose_spec.2 u ⟨h1, h2⟩
  refine ⟨WidePullbackCone.IsLimit.mk _
    (fun t => e t.pt (CommRingCat.of A) (CommRingCat.ofHom (uOf t)).op) ?_ ?_ ?_⟩
  · intro t
    rw [WidePullbackCone.mk_base]
    apply hinj
    erw [hcomp, hse]
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact (huOf t).1
  · intro t i
    rw [WidePullbackCone.mk_π]
    apply hinj
    erw [hcomp, hse]
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact (huOf t).2 i
  · intro t m hb hπ
    rw [WidePullbackCone.mk_base] at hb
    simp only [WidePullbackCone.mk_π] at hπ
    have hu : ((e t.pt (CommRingCat.of A)).symm m).unop.hom = uOf t := by
      apply huniq
      · have hb' : m ≫ Spec.map (CommRingCat.ofHom b) = t.base := hb
        have h1 : ((e t.pt (CommRingCat.of C)).symm t.base).unop =
            CommRingCat.ofHom b ≫ ((e t.pt (CommRingCat.of A)).symm m).unop := by
          rw [← hb']; exact hcomp t.pt m (CommRingCat.ofHom b)
        have h2 := congrArg CommRingCat.Hom.hom h1
        rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
        exact h2.symm
      · intro i
        have hπ' : m ≫ Spec.map (CommRingCat.ofHom (l i)) = t.π i := hπ i
        have h1 : ((e t.pt (CommRingCat.of D)).symm (t.π i)).unop =
            CommRingCat.ofHom (l i) ≫ ((e t.pt (CommRingCat.of A)).symm m).unop := by
          rw [← hπ']; exact hcomp t.pt m (CommRingCat.ofHom (l i))
        have h2 := congrArg CommRingCat.Hom.hom h1
        rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h2
        exact h2.symm
    apply hinj
    rw [hse, ← hu]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsLimitWidePullbackStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_widePushout_isLimit_widePullback : ∀ (n : ℕ) (C D A : Type) [CommRing C] [CommRing D] [CommRing A] (a : C →+* D) (b : C →+* A) (l : Fin n → (D →+* A)) (hl : ∀ i, (l i).comp a = b), (∀ (B : Type) [CommRing B] (g : Fin n → (D →+* B)) (c : C →+* B), (∀ i, (g i).comp a = c) → ∃! u : A →+* B, u.comp b = c ∧ ∀ i, u.comp (l i) = g i) → Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) (fun i => Spec.map (CommRingCat.ofHom (l i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i]))) := by
  first | exact @GlobalTheory.spec_widePushout_isLimit | exact GlobalTheory.spec_widePushout_isLimit | (intros; apply GlobalTheory.spec_widePushout_isLimit; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceIsDVRAndResidueEqGround
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceIsDVRAndResidueEqGround
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem isDiscreteValuationRing_functionFieldPlace_ring {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) :
    IsDiscreteValuationRing v.O := by
  haveI hn : Nontrivial (MonoidWithZeroHom.valueGroup ((v.1 : F →*₀ WithZero (Multiplicative ℤ)))) := by
    obtain ⟨z, hz⟩ := v.2.1 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    let u : (WithZero (Multiplicative ℤ))ˣ :=
      Units.mk0 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) WithZero.coe_ne_zero
    refine ⟨⟨1, ⟨u, MonoidWithZeroHom.mem_valueGroup _ ⟨z, hz⟩⟩, ?_⟩⟩
    intro h
    have := congrArg (fun u => ((u : _ ˣ) : WithZero (Multiplicative ℤ))) (congrArg Subtype.val h)
    have h2 : (Multiplicative.ofAdd (1:ℤ)) = 1 := WithZero.coe_injective (by simpa [u] using this.symm)
    simp at h2
  exact Valuation.valuationSubring_isDiscreteValuationRing v.1

theorem place_le_one_const {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) (c : k) :
    v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

theorem functionFieldPlace_exists_const_sub_lt_one {k F : Type} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    (hF : IsFF k F) (v : Place k F) (x : F) (hx : v.1 x ≤ 1) :
    ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  by_contra hne
  push_neg at hne
  have h1 : ∀ c : k, v.1 (x - algebraMap k F c) = 1 := fun c =>
    le_antisymm ((v.1.map_sub _ _).trans (max_le hx (place_le_one_const v c))) (hne c)
  have hq : ∀ q : k[X], q ≠ 0 → v.1 (Polynomial.aeval x q) = 1 := by
    intro q hq0
    have hs := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := q) IsAlgClosed.card_roots_eq_natDegree
    rw [← hs, map_mul, map_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod]
    simp only [Polynomial.aeval_C, Function.comp_def, map_sub, Polynomial.aeval_X, Multiset.map_map]
    rw [(v.2.2 _ (Polynomial.leadingCoeff_ne_zero.mpr hq0)), one_mul]
    simp [h1]
  have htr : Transcendental k x := by
    rintro ⟨q, hq0, hqx⟩
    have := hq q hq0
    rw [hqx, map_zero] at this
    exact zero_ne_one this
  haveI hfin : FiniteDimensional k⟮x⟯ F := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).1 x htr
  have hK : ∀ y ∈ k⟮x⟯, v.1 y ≤ 1 := by
    intro y hy
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k y).1 hy
    have hle : ∀ q : k[X], v.1 (Polynomial.aeval x q) ≤ 1 := fun q => by
      by_cases h0 : q = 0
      · simp [h0]
      · exact (hq q h0).le
    by_cases hs0 : s = 0
    · simp [hs0]
    · rw [map_div₀, hq s hs0, div_one]
      exact hle r
  have hint : ∀ y : F, v.1 y ≤ 1 := by
    intro y
    obtain ⟨f, hm, hf⟩ := Algebra.IsIntegral.isIntegral (R := k⟮x⟯) y
    have hc : ∀ i, v.1 (algebraMap k⟮x⟯ F (f.coeff i)) ≤ 1 := fun i => hK _ (f.coeff i).2
    by_cases hn : f.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hn
      obtain ⟨c, rfl⟩ := hn
      simp [hm.ne_zero_of_C] at hf
    simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
      one_mul, add_eq_zero_iff_eq_neg] at hf
    apply_fun v.1 at hf
    rw [Valuation.map_neg, Valuation.map_pow] at hf
    contrapose! hf
    refine ne_of_lt (v.1.map_sum_lt ?_ ?_)
    · simp [hn, (hf.trans' (zero_lt_one)).ne']
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Valuation.map_mul, Valuation.map_pow]
      exact mul_lt_of_le_one_of_lt (hc _) <| pow_lt_pow_right₀ hf hi
  obtain ⟨z, hz⟩ := v.2.1 ((Multiplicative.ofAdd (1:ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have := hint z
  rw [hz] at this
  exact absurd this (by decide)

theorem place_isDVR_residue : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ v : Place k F, IsDiscreteValuationRing v.O ∧ ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  intro k F _ _ _ _ _ hF v
  exact ⟨isDiscreteValuationRing_functionFieldPlace_ring v, fun x hx => functionFieldPlace_exists_const_sub_lt_one hF v x hx⟩

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceIsDVRAndResidueEqGroundStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ v : Place k F, IsDiscreteValuationRing v.O ∧ ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1 := by
  first | exact @GlobalTheory.Nef.place_isDVR_residue | exact GlobalTheory.Nef.place_isDVR_residue | (intros; apply GlobalTheory.Nef.place_isDVR_residue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraEqRangeExteriorPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraEqRangeExteriorPower
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem smul_mem_omB_regForms {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ)
    {b : K} (hb : b ∈ B) {y : DR k K} (hy : y ∈ omB k K B q) : b • y ∈ omB k K B q := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨b * c, B.mul_mem hb hc, v, hv, ?_⟩
    rw [smul_smul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | smul r y _ h => rw [smul_comm]; exact Submodule.smul_mem _ r h

theorem ιMulti_D_mem_omB_regForms {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ)
    (w : Fin q → B) : (ExteriorAlgebra.ιMulti K q fun j => D k K (w j : K)) ∈ omB k K B q := by
  apply Submodule.subset_span
  exact ⟨1, B.one_mem, fun j => (w j : K), fun j => (w j).2, (one_smul K _).symm⟩

theorem omB_eq_range_exteriorPower : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K)
    [IsFractionRing B K] [Algebra.Smooth k B] (q : ℕ), ∃ e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K,
    Function.Injective e ∧ (∀ y, y ∈ omB k K B q ↔ ∃ z, e z = y) ∧
    ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
  intro k K _ _ _ B _ _ q
  haveI : Algebra.FormallyEtale B K := .of_isLocalization (nonZeroDivisors B)
  let φ : Ω[B⁄k] →ₗ[B] Ω[K⁄k] := KaehlerDifferential.map k k B K
  have hD : ∀ x : B, φ (D k B x) = D k K (x : K) := fun x => KaehlerDifferential.map_D k k B K x
  have hφ : IsBaseChange K φ := IsBaseChange.of_equiv (tensorKaehlerEquivOfFormallyEtale k B K) fun x => by
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul]
    rfl
  let E := GlobalTheory.exteriorPowerMapOver K q φ
  have hE : IsLocalizedModule (nonZeroDivisors B) E :=
    (isLocalizedModule_iff_isBaseChange _ K E).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ q)
  haveI : Module.Projective B (⋀[B]^q Ω[B⁄k]) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective B Ω[B⁄k])
    exact Module.Projective.of_split (exteriorPower.map q s)
      (exteriorPower.map q (Finsupp.linearCombination B id))
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  haveI : Module.Flat B (⋀[B]^q Ω[B⁄k]) := inferInstance
  haveI : Module.IsTorsionFree B (⋀[B]^q Ω[B⁄k]) := Module.Flat.isTorsionFree
  have hEinj : Function.Injective E := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors B) hxy
    exact (Module.IsTorsionFree.isSMulRegular (M := ⋀[B]^q Ω[B⁄k])
      (IsRegular.of_ne_zero (nonZeroDivisors.coe_ne_zero c))) hc
  let e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K := ((⋀[K]^q Ω[K⁄k]).subtype.restrictScalars B) ∘ₗ E
  have hι : ∀ a : Fin q → Ω[B⁄k], e (exteriorPower.ιMulti B q a) =
      ExteriorAlgebra.ιMulti K q fun j => φ (a j) := by
    intro a
    change ((E (exteriorPower.ιMulti B q a) : ⋀[K]^q Ω[K⁄k]) : DR k K) = _
    rw [GlobalTheory.exteriorPowerMapOver_ιMulti, exteriorPower.ιMulti_apply_coe]
  have hιD : ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
    intro v
    rw [hι]
    simp only [hD]
  have hB : ∀ (b : B) (y : DR k K), b • y = (b : K) • y := fun b y => (algebraMap_smul K b y).symm
  refine ⟨e, Subtype.val_injective.comp hEinj, fun y => ⟨fun hy => ?_, ?_⟩, hιD⟩
  · have : omB k K B q ≤ LinearMap.range (e.restrictScalars k) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, v, hv, rfl⟩
      refine ⟨(⟨b, hb⟩ : B) • exteriorPower.ιMulti B q (fun j => D k B ⟨v j, hv j⟩), ?_⟩
      rw [LinearMap.restrictScalars_apply, map_smul, hιD, hB]
    obtain ⟨z, hz⟩ := this hy
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    have htop := exteriorPower.ιMulti_span_of_span B q Ω[B⁄k] (span_range_derivation k B)
    have hz : z ∈ Submodule.span B
        (⇑(exteriorPower.ιMulti B q) '' {a | Set.range a ⊆ Set.range (D k B)}) := by
      rw [htop]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      choose w hw using fun j => ha ⟨j, rfl⟩
      have ha' : a = fun j => D k B (w j) := funext fun j => (hw j).symm
      subst ha'
      rw [hιD]
      exact ιMulti_D_mem_omB_regForms B q w
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | smul b z _ h => rw [map_smul, hB]; exact smul_mem_omB_regForms B q b.2 h

end GlobalTheory.PD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraEqRangeExteriorPowerStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_eq_range_exteriorPower : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (q : ℕ), ∃ e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K, Function.Injective e ∧ (∀ y, y ∈ omB k K B q ↔ ∃ z, e z = y) ∧ ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) = ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
  first | (exact @GlobalTheory.PD.omB_eq_range_exteriorPower) | (exact GlobalTheory.PD.omB_eq_range_exteriorPower) | (intros; apply GlobalTheory.PD.omB_eq_range_exteriorPower  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughExtendScalarsZmod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughExtendScalarsZmod
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

namespace FactorExt

theorem intCast_surj (Q : ℕ) : Function.Surjective (Int.cast : ℤ → ULift.{1} (ZMod Q)) := by
  intro r
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective r.down
  exact ⟨z, ULift.ext (by simp [hz])⟩

theorem map_smul_of_add {A B M N : Type*} [Ring A] [Ring B] (f : A →+* B)
    (hA : Function.Surjective (Int.cast : ℤ → A)) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (g : M →+ N) (r : A) (m : M) : g (r • m) = f r • g m := by
  obtain ⟨z, rfl⟩ := hA r
  rw [Int.cast_smul_eq_zsmul, map_zsmul, map_intCast, Int.cast_smul_eq_zsmul]

variable {R S : Type} [CommRing R] [CommRing S]

theorem extSh_hom_ext (φ : R →+* S) {F : Shv R} {G : Shv S} (f g : (extSh φ).obj F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (a : Sec F U), Sec.map f (extSh.sec φ F U a) = Sec.map g (extSh.sec φ F U a)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))
    f.hom g.hom G.property ?_
  ext U : 2
  apply (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext a
  exact h (unop U) a

end FactorExt

end GlobalTheory.EtC

end

noncomputable section

namespace GlobalTheory.EtC

namespace FactorExt

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
  (hR : Function.Surjective (Int.cast : ℤ → ULift.{1} R)) {I : Cx R} {K : Cx S} (ρ : SemiMap I K)
include hR

def lin (s : ℤ) (U : Scheme.{0}) :
    (I.X s).obj.obj (op U) ⟶ (ModuleCat.restrictScalars (uliftHom φ)).obj ((K.X s).obj.obj (op U)) :=
  ModuleCat.ofHom (X := (I.X s).obj.obj (op U))
    (Y := (ModuleCat.restrictScalars (uliftHom φ)).obj ((K.X s).obj.obj (op U)))
    { toFun := ρ.app U s
      map_add' := map_add _
      map_smul' := fun r a => by
        exact map_smul_of_add (uliftHom φ) hR (ρ.app U s) r a }

def pre (s : ℤ) : (I.X s).obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ) ⟶ (K.X s).obj where
  app U := ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _).symm (lin φ hR ρ s (unop U))
  naturality {U V} g := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    ext a
    exact (ρ.nat g.unop s a).symm

def term (s : ℤ) : (extCx φ I).X s ⟶ K.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} S))).homEquiv _ _).symm (pre φ hR ρ s)

theorem term_sec (s : ℤ) (U : Scheme.{0}) (a : Sec (I.X s) U) :
    Sec.map (term φ hR ρ s) (extSh.sec φ (I.X s) U a) = ρ.app U s a := by
  have h1 : toSheafify Scheme.etaleTopology.{0} ((I.X s).obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)) ≫
      (term φ hR ρ s).hom = pre φ hR ρ s := by
    have := Adjunction.homEquiv_unit (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} S)))
      _ _ (term φ hR ρ s)
    rw [sheafificationAdjunction_unit_app] at this
    exact this.symm.trans (Equiv.apply_symm_apply _ _)
  have h2 := Adjunction.homEquiv_unit (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)) _ _
    ((pre φ hR ρ s).app (op U))
  have e1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (NatTrans.congr_app h1 (op U)))
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app ((I.X s).obj.obj (op U))).hom a)
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h2) a
  simp only [pre, Equiv.apply_symm_apply] at e2
  exact e1.trans e2.symm

def hom : extCx φ I ⟶ K where
  f s := term φ hR ρ s
  comm' s t _ := by
    apply FactorExt.extSh_hom_ext φ
    intro U a
    show Sec.map (K.d s t) (Sec.map (term φ hR ρ s) (extSh.sec φ (I.X s) U a)) =
      Sec.map (term φ hR ρ t) (Sec.map ((extSh φ).map (I.d s t)) (extSh.sec φ (I.X s) U a))
    rw [term_sec, extSh.sec_map, term_sec, ρ.comm]

end FactorExt

theorem SemiMap.factor_extCx : ∀ (Q q : ℕ) (hq : q ∣ Q) (I : Cx (ZMod Q)) (K : Cx (ZMod q)) (ρ : SemiMap I K),
    ∃ u : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U),
      ρ.app U s a = Sec.map (u.f s) ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a) :=
  fun Q _ hq _ _ ρ => ⟨FactorExt.hom _ (FactorExt.intCast_surj Q) ρ,
    fun U s a => (FactorExt.term_sec (ZMod.castHom hq _) (FactorExt.intCast_surj Q) ρ s U a).symm⟩

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughExtendScalarsZmodStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_extendScalars_zmod : ∀ (Q q : ℕ) (hq : q ∣ Q) (I : Cx (ZMod Q)) (K : Cx (ZMod q)) (ρ : SemiMap I K), ∃ u : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ.app U s a = Sec.map (u.f s) ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a) := by
  first | exact @GlobalTheory.EtC.SemiMap.factor_extCx | exact GlobalTheory.EtC.SemiMap.factor_extCx | (intros; apply GlobalTheory.EtC.SemiMap.factor_extCx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentConstantTermFormFunctionField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentConstantTermFormFunctionField
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in
private theorem linearIndependent_laurentMonomials {k F ι : Type} [Field k] [Field F] [Algebra k F]
    [Fintype ι] (y : ι → F) (hy : AlgebraicIndependent k y) (hy0 : ∀ i, y i ≠ 0) :
    LinearIndependent k (fun n : ι → ℤ => ∏ i, y i ^ n i) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg n hn
  set B : ℤ := ∑ m ∈ s, ∑ i, |m i| with hBdef
  have hB : ∀ m ∈ s, ∀ i, 0 ≤ m i + B := by
    intro m hm i
    have h1 : |m i| ≤ ∑ i, |m i| :=
      Finset.single_le_sum (f := fun i => |m i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i, |m i| ≤ B :=
      Finset.single_le_sum (f := fun m : ι → ℤ => ∑ i, |m i|)
        (fun m _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hm
    linarith [neg_abs_le (m i)]
  let e : (ι → ℤ) → (ι →₀ ℕ) := fun m => Finsupp.equivFunOnFinite.symm (fun i => (m i + B).toNat)
  have he : Set.InjOn e s := by
    intro m hm m' hm' h
    funext i
    have h' := congrArg (fun f : ι →₀ ℕ => f i) h
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h'
    have := Int.toNat_of_nonneg (hB m hm i)
    have := Int.toNat_of_nonneg (hB m' hm' i)
    omega
  set P : F := ∏ i, y i ^ B with hPdef
  have hkey : ∀ m ∈ s, MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k)) =
      P * ∏ i, y i ^ m i := by
    intro m hm
    rw [MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), hPdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_add₀ (hy0 i), ← zpow_natCast]
    congr 1
    simp only [e, Finsupp.coe_equivFunOnFinite_symm]
    rw [Int.toNat_of_nonneg (hB m hm i)]
    ring
  have hw : LinearIndependent k (fun a : ι →₀ ℕ => MvPolynomial.aeval y (MvPolynomial.monomial a (1 : k))) := by
    have := (MvPolynomial.basisMonomials ι k).linearIndependent.map'
      (MvPolynomial.aeval y).toLinearMap (LinearMap.ker_eq_bot.mpr hy)
    simpa only [MvPolynomial.coe_basisMonomials, Function.comp_def, AlgHom.toLinearMap_apply] using this
  have hws : LinearIndependent k
      (fun m : s => MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k))) :=
    hw.comp (fun m : s => e m) (fun a b h => Subtype.ext (he a.2 b.2 h))
  rw [Fintype.linearIndependent_iff] at hws
  refine hws (fun m => g m) ?_ ⟨n, hn⟩
  calc ∑ m : s, g m • MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k))
      = ∑ m : s, P * (g m • ∏ i, y i ^ (m : ι → ℤ) i) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hkey m m.2, mul_smul_comm]
    _ = P * ∑ m ∈ s, g m • ∏ i, y i ^ m i := by
        rw [← Finset.mul_sum, Finset.sum_coe_sort s (fun m => g m • ∏ i, y i ^ m i)]
    _ = 0 := by rw [hg, mul_zero]

open KaehlerDifferential in
private theorem prod_zpow_eq_prod_div_zpow_of_sum_eq_zero {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → F)
    (hx : ∀ i, x i ≠ 0) (m : Fin (d + 1) → ℤ) (hm : ∑ j, m j = 0) :
    ∏ j, x j ^ m j = ∏ i : Fin d, (x i.succ / x 0) ^ m i.succ := by
  have h0 : m 0 = -∑ i : Fin d, m i.succ := by
    rw [Fin.sum_univ_succ] at hm
    linarith
  have hpow : ∀ s : Finset (Fin d), ∏ i ∈ s, x 0 ^ m i.succ = x 0 ^ ∑ i ∈ s, m i.succ := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (hx 0)]
  rw [Fin.prod_univ_succ, h0]
  simp_rw [div_zpow]
  rw [Finset.prod_div_distrib, hpow, zpow_neg, div_eq_mul_inv, mul_comm]


open KaehlerDifferential in
theorem _root_.GlobalTheory.exists_isRes : ∀ (k : Type) [Field k] (F : Type) [Field F]
    [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F),
    _root_.GlobalTheory.PD.IsPd k x → ∃ ρ : F →ₗ[k] k, _root_.GlobalTheory.PD.IsRes k x ρ := by
  intro k _ F _ _ d x hx
  classical
  let v : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} → F := fun m => ∏ j, x j ^ m.1 j
  have hv : LinearIndependent k v := by
    have hL := linearIndependent_laurentMonomials (k := k) (fun i : Fin d => x i.succ / x 0)
      hx.indep
      (fun i => div_ne_zero (hx.ne _) (hx.ne 0))
    have hinj : Function.Injective
        (fun m : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} => fun i : Fin d => m.1 i.succ) := by
      intro a b h
      apply Subtype.ext
      have hs : ∀ i : Fin d, a.1 i.succ = b.1 i.succ := fun i => congrFun h i
      have ha := a.2
      have hb := b.2
      rw [Fin.sum_univ_succ] at ha hb
      have hsum : ∑ i : Fin d, a.1 i.succ = ∑ i : Fin d, b.1 i.succ :=
        Finset.sum_congr rfl fun i _ => hs i
      funext j
      refine Fin.cases ?_ (fun i => hs i) j
      linarith
    have := hL.comp _ hinj
    convert this using 1
    funext m
    exact prod_zpow_eq_prod_div_zpow_of_sum_eq_zero x hx.ne m.1 m.2
  let z₀ : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} := ⟨0, by simp⟩
  have h1 : v z₀ = 1 := by simp [v, z₀]
  have hnot := hv.notMem_span_image (s := {z | z ≠ z₀}) (x := z₀) (by simp)
  rw [h1] at hnot
  obtain ⟨f, hf1, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨(f 1)⁻¹ • f, ?_⟩
  delta _root_.GlobalTheory.PD.IsRes
  refine ⟨?_, ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf1]
  · intro m hm hm0
    have hmem : ∏ j, x j ^ m j ∈ Submodule.span k (v '' {z | z ≠ z₀}) :=
      Submodule.subset_span ⟨⟨m, hm⟩, fun h => hm0 (congrArg Subtype.val h), rfl⟩
    have hzero : f (∏ j, x j ^ m j) = 0 := by
      exact LinearMap.mem_ker.mp ((LinearMap.le_ker_iff_map.mpr hf) hmem)
    rw [LinearMap.smul_apply, hzero, smul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentConstantTermFormFunctionFieldStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laurentConstantTermForm_functionField : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∃ ρ : F →ₗ[k] k, IsRes k x ρ := by
  first | (exact @GlobalTheory.exists_isRes) | (exact GlobalTheory.exists_isRes) | (intros; apply GlobalTheory.exists_isRes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringInValuationSubring
open Polynomial

namespace GlobalTheory

theorem finiteDimensional_top_subfield (L : Type*) [Field L] :
    FiniteDimensional (⊤ : Subfield L) L := by
  refine ⟨⟨{1}, eq_top_iff.mpr fun l _ => ?_⟩⟩
  rw [Finset.coe_singleton, Submodule.mem_span_singleton]
  exact ⟨⟨l, Subfield.mem_top l⟩, mul_one l⟩

theorem exists_normal_finiteType_subring_of_valuationSubring : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := by
  intro K L _ _ φ c hfin V hc t ht hgen
  classical
  letI : Algebra ℂ K := c.toAlgebra
  letI : Algebra K L := φ.toAlgebra
  letI : Algebra ℂ L := (φ.comp c).toAlgebra
  haveI : IsScalarTower ℂ K L := .of_algebraMap_eq fun _ => rfl
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℂ L).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  have ht' : ∀ x : t, ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0 :=
    fun x => (ht x x.2).2
  choose p hpm hpc hpx using ht'
  let T : Set K := ⋃ x : t, ((p x).coeffs : Set K)
  have hT : T.Finite := Set.finite_iUnion fun x => (p x).coeffs.finite_toSet
  let A : Subalgebra ℂ K := Algebra.adjoin ℂ T
  haveI : Algebra.FiniteType ℂ A := .adjoin_of_finite hT
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hcoefA : ∀ x : t, ∀ n, (p x).coeff n ∈ A := fun x n => by
    by_cases h : (p x).coeff n = 0
    · rw [h]; exact A.zero_mem
    · exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨x, Polynomial.coeff_mem_coeffs h⟩)
  have hAE : ∀ y ∈ A, y ∈ V.comap φ := fun y hy => by
    let E' : Subalgebra ℂ K := { (V.comap φ).toSubring with algebraMap_mem' := fun a => hc a }
    have : A ≤ E' := Algebra.adjoin_le (by
      intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      exact hpc x i)
    exact this hy
  haveI : IsScalarTower A K L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ A L := .of_algebraMap_eq fun _ => rfl
  have hint : ∀ x : t, IsIntegral A (x : L) := fun x => by
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap A K)
      ((lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, hcoefA x n⟩, rfl⟩) (hpm x)
    refine ⟨q, hqm, ?_⟩
    rw [← hpx x, ← hq, eval₂_map]
    rfl

  have hsub : Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)) ≤ (integralClosure A L).toSubring :=
    Subring.closure_le.mpr (Set.union_subset
      (by
        rintro _ ⟨a, rfl⟩
        exact isIntegral_algebraMap (R := A) (x := (⟨c a, A.algebraMap_mem a⟩ : A)))
      (fun x hx => hint ⟨x, hx⟩))
  have hall : ∀ l : L, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)),
      ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)), (l = b / d ∨ l⁻¹ = b / d) := by
    intro l
    rcases V.mem_or_inv_mem l with h | h
    · obtain ⟨b, hb, d, hd, -, -, he⟩ := hgen l h
      exact ⟨b, hb, d, hd, Or.inl he⟩
    · obtain ⟨b, hb, d, hd, -, -, he⟩ := hgen _ h
      exact ⟨b, hb, d, hd, Or.inr he⟩
  haveI : Algebra.IsAlgebraic A L := ⟨fun l => by
    obtain ⟨b, hb, d, hd, h⟩ := hall l
    have hb' : IsAlgebraic A b := (hsub hb : IsIntegral A b).isAlgebraic
    have hd' : IsAlgebraic A d := (hsub hd : IsIntegral A d).isAlgebraic
    have hbd : IsAlgebraic A (b / d) := by rw [div_eq_mul_inv]; exact hb'.mul hd'.inv
    rcases h with h | h
    · rw [h]; exact hbd
    · rw [← inv_inv l, h]; exact hbd.inv⟩
  haveI : Algebra.IsAlgebraic A K := ⟨fun k =>
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom A K L) φ.injective).mp
      (Algebra.IsAlgebraic.isAlgebraic (φ k))⟩
  have htop : Subfield.closure (Set.range (algebraMap ℂ L) ∪ (t : Set L)) = ⊤ := by
    refine eq_top_iff.mpr fun l _ => ?_
    have hle : Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)) ≤
        (Subfield.closure (Set.range (algebraMap ℂ L) ∪ (t : Set L))).toSubring :=
      Subring.closure_le.mpr Subfield.subset_closure
    obtain ⟨b, hb, d, hd, h⟩ := hall l
    have hbd := Subfield.div_mem _ (hle hb) (hle hd)
    rcases h with h | h
    · rw [h]; exact hbd
    · rw [← inv_inv l, h]; exact Subfield.inv_mem _ hbd
  haveI : Algebra.EssFiniteType ℂ L := by
    refine essFiniteType_of_finiteDimensional_subfield_closure t.finite_toSet ?_
    rw [htop]
    exact finiteDimensional_top_subfield L
  haveI : Algebra.EssFiniteType A L := .of_comp ℂ A L
  haveI : Module.Finite A (integralClosure A L) :=
    GlobalTheory.finite_integralClosure_of_essFiniteType_field ℂ A L
  let S := integralClosure A K
  let f : S →ₐ[A] integralClosure A L :=
    ((IsScalarTower.toAlgHom A K L).comp S.val).codRestrict _ fun z =>
      (z.2.map (IsScalarTower.toAlgHom A K L) : IsIntegral A _)
  haveI : Module.Finite A S := Module.Finite.of_injective f.toLinearMap fun z w h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h : _))
  set_option synthInstance.maxHeartbeats 200000 in
    haveI : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
    haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
    haveI : IsFractionRing S K := integralClosure.isFractionRing_of_algebraic fun x hx => Subtype.ext hx
    haveI : IsIntegrallyClosed S := (isIntegrallyClosed_iff K).mpr fun {x} hx =>
      ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩

    have hcR : ∀ a, c a ∈ S.toSubring := fun a => S.algebraMap_mem (⟨c a, A.algebraMap_mem a⟩ : A)
    refine ⟨S.toSubring, hcR, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ S)
    · intro x hx
      obtain ⟨q, hqm, hq⟩ := (hx : IsIntegral A x)
      let ι : A →+* V.comap φ :=
        { toFun := fun a => ⟨a, hAE a a.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hE : IsIntegral (V.comap φ) x := by
        refine ⟨q.map ι, hqm.map ι, ?_⟩
        rw [eval₂_map]
        exact hq
      obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hE
      exact y.2
    · exact (inferInstance : IsNoetherianRing S)
    · exact (inferInstance : IsIntegrallyClosed S)
    · exact (inferInstance : IsFractionRing S K)
    · intro x hx
      obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := S.toSubring.subtype)
        ((lifts_iff_coeff_lifts _).mpr fun n =>
          ⟨⟨_, S.algebraMap_mem (⟨_, hcoefA ⟨x, hx⟩ n⟩ : A)⟩, rfl⟩) (hpm ⟨x, hx⟩)
      refine ⟨q, hqm, ?_⟩
      rw [← eval₂_map, hq]
      exact hpx ⟨x, hx⟩

end GlobalTheory
end
