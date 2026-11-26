module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainExistsFromNaturalSections
section -- merged from Development.EtaleCohomology.TateTwists.EtaleSchemeGlobalSectionCohomologyClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSchemeGlobalSectionCohomologyClass : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ), m + 1 = n → n + 1 = k →
    (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
      (∀ (U : Scheme.{0}) (x : U ⟶ X), ev (R := R) α.1 0 n (by simp) U x = Sec.res x z) ∧
      ∀ (p : ℕ) s h U x, ev (R := R) α.1 (p + 1) s h U x = 0) ∧
    ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n,
      Sec.map (I.d n k) (ev (R := R) α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
      (CohomologyClass.mk α = 0 ↔ ∃ y : Sec (I.X m) X,
        Sec.map (I.d m n) y = ev (R := R) α.1 0 n (by simp) X (𝟙 X))
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSimplicialCochainExistsFromNaturalSections : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U), (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) → ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def EtaleSimplicialCochainEvaluationDifferentialFormula : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

def EtaleSimplicialCochainEvaluationProperties : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n : ℤ), m + 1 = n → ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, ev α.1 0 n (by simp) X (𝟙 X) = 0 → ∃ β : Cochain ((chains R).obj (sch.obj X)) I m, δ m n β = α.1

def a0 {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U
  | 0, s, h, U, x => (show n = s by omega) ▸ Sec.res (x : U ⟶ X) z
  | _ + 1, _, _, _, _ => 0

lemma etaleSimplicialCochain_scheme_section_extension_degree_zero {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) (h : -((0:ℕ) : ℤ) + n = n)
    (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) : a0 X I n z 0 n h U x = Sec.res (x : U ⟶ X) z := rfl

lemma res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp [Sec.res, op_comp, Functor.map_comp]

lemma res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (z : Sec F U) : Sec.res (𝟙 U) z = z := by
  simp [Sec.res]

lemma map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.map φ (Sec.res g z) = Sec.res g (Sec.map φ z) := by
  simp only [Sec.map, Sec.res]
  exact congrArg (fun f => ModuleCat.Hom.hom f z) (φ.hom.naturality g.op)

lemma etaleSimplicialCochain_scheme_section_extension_naturality {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) :
    ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (a0 X I n z p s h U x) = a0 X I n z p s h V (x.res g) := by
  intro p s h V U g x
  cases p with
  | zero =>
    obtain rfl : s = n := by omega
    exact res_res g x z
  | succ q => simp [a0, Sec.res]

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialCochain_scheme_class_of_evaluation_properties (hmk : EtaleSimplicialCochainExistsFromNaturalSections) (hdl : EtaleSimplicialCochainEvaluationDifferentialFormula)
    (hb : EtaleSimplicialCochainEvaluationProperties) (hcob : EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary) : EtaleSchemeGlobalSectionCohomologyClass := by
  intro R _ X I m n k hmn hnk

  have v0 : ∀ {q : ℤ} (β : Cochain ((chains R).obj (sch.obj X)) I q) (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U),
      ev β 0 q (by simp) U x = Sec.res (x : U ⟶ X) (ev β 0 q (by simp) X (𝟙 X)) := by
    intro q β U x
    rw [(hb R).2.1 β 0 q (by simp) U X x (𝟙 X)]
    rfl
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨α, hα⟩ := hmk R (a0 X I n z) (etaleSimplicialCochain_scheme_section_extension_naturality X I n z)
    have hδ : δ n k α = 0 := by
      apply (hb R).2.2.1
      intro p s h U x
      rw [((hb R).1 (δ n k α) (δ n k α) p s h U x).2.2.1]
      cases p with
      | zero =>
        obtain rfl : s = k := by omega
        rw [(hdl R hnk α U).1 x, hα, etaleSimplicialCochain_scheme_section_extension_degree_zero]
        exact (map_res (I.d n s) (x : U ⟶ X) z).trans (by rw [hz]; simp [Sec.res])
      | succ p =>
        rw [(hdl R hnk α U).2 p (-((p + 1 : ℕ) : ℤ) + n) s rfl h x]
        simp only [hα]
        cases p with
        | zero =>
          obtain rfl : s = n := by omega
          simp [a0, Fin.sum_univ_two]
          rw [show x.face 0 = x from rfl, show x.face 1 = x from rfl]
          exact add_neg_cancel _
        | succ p => simp [a0]
    refine ⟨Cocycle.mk α k hnk hδ, ?_, ?_⟩
    · intro U x; exact hα 0 n (by simp) U x
    · intro p s h U x; rw [show (Cocycle.mk α k hnk hδ).1 = α from rfl, hα]; rfl
  · intro α
    have hd0 : Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 := by
      rw [← (hdl R hnk α.1 X).1 (𝟙 X), Cocycle.δ_eq_zero]
      exact ((hb R (E := sch.obj X) (I := I) (n := k)).1 0 0 0 k (by simp) X (𝟙 X)).2.2.1
    refine ⟨hd0, ?_⟩
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α m hmn]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 m (by simp) X (𝟙 X), ?_⟩
      rw [← (hdl R hmn β X).1 (𝟙 X), hβ]
    · rintro ⟨y, hy⟩
      obtain ⟨γ, hγ⟩ := hmk R (a0 X I m y) (etaleSimplicialCochain_scheme_section_extension_naturality X I m y)
      have hc : δ n k (α.1 - δ m n γ) = 0 := by
        rw [δ_sub, Cocycle.δ_eq_zero, δ_δ, sub_zero]
      obtain ⟨β, hβ⟩ := hcob R X I m n hmn (Cocycle.mk (α.1 - δ m n γ) k hnk hc) (by
        have e := ((hb R).1 (α : Cochain ((chains R).obj (sch.obj X)) I n) (δ m n γ) 0 n (by simp) X (𝟙 X)).2.1
        have e2 : ev (δ m n γ) 0 n (by simp) X (𝟙 X) = Sec.map (I.d m n) y := by
          rw [(hdl R hmn γ X).1 (𝟙 X)]
          exact congrArg (Sec.map (I.d m n)) ((hγ 0 m (by simp) X (𝟙 X)).trans (res_id y))
        exact e.trans ((congrArg (ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n (by simp) X (𝟙 X) - ·) e2).trans
          (sub_eq_zero.mpr hy.symm)))
      refine ⟨β + γ, ?_⟩
      rw [δ_add, hβ]
      show α.1 - δ m n γ + δ m n γ = α.1
      abel
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorHomDescendsAlongTensorPairing
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorComplexDescendsNaturalFamily
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorComplexDescendsNaturalFamily : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x)) → ∃ φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧ ∀ U x, φ U (τ.lift U w x) = b U x
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensFam

theorem res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res h (Sec.res g y) = Sec.res (h ≫ g) y := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h1⟩ := hP
  obtain ⟨T, hT, h2⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT, fun V g hg => ⟨h1 V g hg.1, h2 V g hg.2⟩⟩

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem sep {S : Type} [CommRing S] (M : Shv S) {U : Scheme.{0}} (s s' : Sec M U)
    (h : Loc U fun V g => Sec.res g s = Sec.res g s') : s = s' := by
  obtain ⟨T, hT, h1⟩ := h
  have hM := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology M.obj (forget _)).mp M.2)
  exact (hM T hT).isSeparatedFor.ext fun V g hg => h1 V g hg

theorem glue {S : Type} [CommRing S] (M : Shv S) {U : Scheme.{0}} (T : Sieve U) (hT : T ∈ Scheme.etaleTopology U)
    (t : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V)
    (ht : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : T.arrows g),
      t W (k ≫ g) (T.downward_closed hg k) = Sec.res k (t V g hg)) :
    ∃ s : Sec M U, ∀ V g (hg : T.arrows g), Sec.res g s = t V g hg := by
  have hM := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology M.obj (forget _)).mp M.2)
  let x : Presieve.FamilyOfElements (M.obj ⋙ forget _) T.arrows := fun V g hg => t V g hg
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    exact ht V W g k hg
  exact ⟨(hM T hT).amalgamate x hx, fun V g hg => (hM T hT).valid_glue hx g hg⟩

theorem lift_res {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (x : Tens I J U w) : Sec.res g (τ.lift U w x) = τ.lift V w (Tens.res g w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [Sec.res, map_add (f := _)] at *; rw [ha, hb]
  | of i z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [Sec.res, map_add (f := _)] at *; rw [ha, hb]
    | tmul a c =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [Pair.lift, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.lift.tmul, TensorProduct.map_tmul]
      exact τ.nat g _ _ w _ a c

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a c : Sec F U) :
    Sec.res g (a + c) = Sec.res g a + Sec.res g c := map_add _ _ _

section Main
variable {R S : Type} [CommRing R] [CommRing S] {I J K : Cx R}

def Good (τ : Pair I J K) (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U)
    (U : Scheme.{0}) (y : Sec (K.X w) U) (s : Sec M U) : Prop :=
  Loc U fun V g => ∃ x, τ.lift V w x = Sec.res g y ∧ Sec.res g s = b V x

variable (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x))
include hτ hb

theorem key {U : Scheme.{0}} (x1 x2 : Tens I J U w) (h : τ.lift U w x1 = τ.lift U w x2) : b U x1 = b U x2 := by
  have h0 : τ.lift U w (x1 - x2) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨T, hT, hT'⟩ := hτ.2 U w _ h0
  apply sep M
  refine ⟨T, hT, fun V g hg => ?_⟩
  have h1 : Tens.res g w (x1 - x2) = 0 := hT' V g hg
  rw [map_sub, sub_eq_zero] at h1
  show Sec.res g (b U x1) = Sec.res g (b U x2)
  rw [hb, hb, h1]

theorem uniq {U : Scheme.{0}} {y : Sec (K.X w) U} {s s' : Sec M U}
    (h1 : Good τ w M b U y s) (h2 : Good τ w M b U y s') : s = s' := by
  apply sep M
  obtain ⟨T, hT, h⟩ := loc_and h1 h2
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨⟨x, hx, hs⟩, ⟨x', hx', hs'⟩⟩ := h V g hg
  rw [hs, hs']
  exact key τ hτ w M b hb x x' (hx.trans hx'.symm)

theorem good_exists (U : Scheme.{0}) (y : Sec (K.X w) U) : ∃ s, Good τ w M b U y s := by
  obtain ⟨T, hT, hc⟩ := hτ.1 U w y
  let t : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V := fun V g hg => b V (hc V g hg).choose
  obtain ⟨s, hs⟩ := glue M T hT t (by
    intro V W g k hg
    simp only [t]
    rw [hb]
    apply key τ hτ w M b hb
    rw [(hc W (k ≫ g) (T.downward_closed hg k)).choose_spec, ← lift_res, (hc V g hg).choose_spec, res_res])
  exact ⟨s, T, hT, fun V g hg => ⟨(hc V g hg).choose, (hc V g hg).choose_spec, hs V g hg⟩⟩

omit hτ in
theorem good_add {U : Scheme.{0}} {y1 y2 : Sec (K.X w) U} {s1 s2 : Sec M U}
    (h1 : Good τ w M b U y1 s1) (h2 : Good τ w M b U y2 s2) : Good τ w M b U (y1 + y2) (s1 + s2) := by
  obtain ⟨T, hT, h⟩ := loc_and h1 h2
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨⟨x, hx, hs⟩, ⟨x', hx', hs'⟩⟩ := h V g hg
  exact ⟨x + x', by rw [map_add (f := _), hx, hx', res_add], by rw [res_add, hs, hs', map_add (f := _)]⟩

omit hτ hb in
theorem good_zero (U : Scheme.{0}) : Good τ w M b U 0 0 :=
  loc_top fun V g => ⟨0, by simp, by simp⟩

omit hτ in
theorem good_nat {V U : Scheme.{0}} (g : V ⟶ U) {y : Sec (K.X w) U} {s : Sec M U}
    (h : Good τ w M b U y s) : Good τ w M b V (Sec.res g y) (Sec.res g s) := by
  obtain ⟨T, hT, h1⟩ := h
  refine ⟨T.pullback g, (Scheme.etaleTopology).pullback_stable g hT, fun W k hk => ?_⟩
  obtain ⟨x, hx, hs⟩ := h1 W (k ≫ g) hk
  exact ⟨x, by rw [res_res, hx], by rw [res_res, hs]⟩

omit hτ in
theorem good_lift (U : Scheme.{0}) (x : Tens I J U w) : Good τ w M b U (τ.lift U w x) (b U x) :=
  loc_top fun V g => ⟨Tens.res g w x, (lift_res τ g w x).symm, hb V U g x⟩

end Main

end LateralTheory.EtaleFoundations.TensFam

open LateralTheory.EtaleFoundations.TensFam in
theorem LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing : LateralTheory.EtaleFoundations.EtaleTensorComplexDescendsNaturalFamily := by
  intro R S _ _ I J K τ hτ w M b hb
  have ex := good_exists τ hτ w M b hb
  let φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U := fun U =>
    { toFun := fun y => (ex U y).choose
      map_zero' := uniq τ hτ w M b hb (ex U 0).choose_spec (good_zero τ w M b U)
      map_add' := fun y1 y2 => uniq τ hτ w M b hb (ex U _).choose_spec
        (good_add τ w M b hb (ex U y1).choose_spec (ex U y2).choose_spec) }
  refine ⟨φ, fun V U g y => ?_, fun U x => ?_⟩
  · exact uniq τ hτ w M b hb (good_nat τ w M b hb g (ex U y).choose_spec) (ex V _).choose_spec
  · exact uniq τ hτ w M b hb (ex U _).choose_spec (good_lift τ w M b hb U x)
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCupProductFlipExistsOfComponents
section -- merged from Development.EtaleCohomology.TateTwists.IsTensorFlip
section -- merged from Development.EtaleCohomology.TateTwists.EtaleComplexPairingFlipExists
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧ (μ.IsTensor → ν.IsTensor)
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.FlipPf
open GlobalTheory.EtC

variable {R : Type} [CommRing R]

lemma negOnePow_smul_smul {M : Type*} [AddCommGroup M] (n : ℤ) (x : M) :
    ((n.negOnePow : ℤ) • ((n.negOnePow : ℤ) • x)) = x := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

lemma coef1 (s t : ℤ) : ((t * s).negOnePow : ℤ) * (t.negOnePow : ℤ) = ((t * (s + 1)).negOnePow : ℤ) := by
  rw [mul_add, mul_one, Int.negOnePow_add, Units.val_mul]

lemma coef2 (s t : ℤ) : (s.negOnePow : ℤ) * (((t + 1) * s).negOnePow : ℤ) = ((t * s).negOnePow : ℤ) := by
  rw [add_mul, one_mul, Int.negOnePow_add, Units.val_mul, mul_left_comm, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, mul_one]

def flipPair {I J K : Cx R} (μ : Pair I J K) : Pair J I K where
  mul U s t w h := ((t * s).negOnePow : ℤ) • (μ.mul U t s w (by omega)).flip
  nat := by
    intro V U g s t w h b a
    simp only [LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul, μ.nat]
  leibniz := by
    intro U s t w h b a
    have hl := μ.leibniz U t s w (by omega) a b
    simp only [LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul]
    dsimp only [Sec.map] at hl ⊢
    rw [hl, smul_add]
    simp only [Units.smul_def, smul_smul, coef1, coef2]
    exact add_comm _ _

def swIx {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) : {p : ℤ × ℤ // p.1 + p.2 = w} :=
  ⟨(p.1.2, p.1.1), by have := p.2; simp only at this ⊢; omega⟩

def sw (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens J I U w :=
  DirectSum.toModule _ _ _ fun p =>
    ((p.1.1 * p.1.2).negOnePow : ℤ) •
      ((DirectSum.lof (ULift.{1} R) _
        (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIx p)) ∘ₗ
        (TensorProduct.comm (ULift.{1} R) _ _).toLinearMap)

lemma sw_lof (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    sw I J U w (DirectSum.lof (ULift.{1} R) _
      (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p (a ⊗ₜ b)) =
    ((p.1.1 * p.1.2).negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) _
      (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIx p) (b ⊗ₜ a) := by
  unfold sw
  erw [DirectSum.toModule_lof]
  rfl

lemma lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _
      (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p (a ⊗ₜ b)) =
    μ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift
  erw [DirectSum.toModule_lof]
  rfl

lemma lift_sw {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    (flipPair μ).lift U w (sw I J U w x) = μ.lift U w x := by
  have key : (flipPair μ).lift U w ∘ₗ sw I J U w = μ.lift U w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply]
    rw [sw_lof, map_zsmul, lift_lof]
    erw [lift_lof (flipPair μ) U w (swIx p) b a]
    simp only [flipPair, LinearMap.smul_apply, LinearMap.flip_apply]
    exact negOnePow_smul_smul _ _
  exact LinearMap.congr_fun key x

lemma sw_sw (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    sw J I U w (sw I J U w x) = x := by
  have key : sw J I U w ∘ₗ sw I J U w = LinearMap.id := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [sw_lof, map_zsmul]
    erw [sw_lof J I U w (swIx p) b a]
    show ((p.1.1 * p.1.2).negOnePow : ℤ) • ((p.1.2 * p.1.1).negOnePow : ℤ) • _ = _
    rw [mul_comm p.1.2 p.1.1]
    exact negOnePow_smul_smul _ _
  exact LinearMap.congr_fun key x

lemma res_sw (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Tens.res g w (sw I J U w x) = sw I J V w (Tens.res g w x) := by
  have key : Tens.res g w ∘ₗ sw I J U w = sw I J V w ∘ₗ Tens.res g w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply]
    rw [sw_lof, map_zsmul]
    unfold Tens.res
    erw [DirectSum.lmap_lof, DirectSum.lmap_lof, TensorProduct.map_tmul, TensorProduct.map_tmul, sw_lof]
    rfl
  exact LinearMap.congr_fun key x

lemma lift_sw' {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (x : Tens J I U w) :
    μ.lift U w (sw J I U w x) = (flipPair μ).lift U w x := by
  conv_rhs => rw [← sw_sw J I U w x]
  rw [lift_sw]

lemma isTensor_flip {I J K : Cx R} (μ : Pair I J K) (hμ : μ.IsTensor) : (flipPair μ).IsTensor := by
  obtain ⟨hs, hi⟩ := hμ
  constructor
  · intro U w y
    obtain ⟨S, hS, hP⟩ := hs U w y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    exact ⟨sw I J V w x, by rw [lift_sw, hx]⟩
  · intro U w x hx
    have h0 : μ.lift U w (sw J I U w x) = 0 := by rw [lift_sw', hx]
    obtain ⟨S, hS, hP⟩ := hi U w _ h0
    refine ⟨S, hS, fun V g hg => ?_⟩
    have h1 : Tens.res g w (sw J I U w x) = 0 := hP V g hg
    show Tens.res g w x = 0
    rw [← sw_sw J I U w x, res_sw, h1, map_zero]

end LateralTheory.EtaleFoundations.FlipPf

theorem LateralTheory.EtaleFoundations.etale_complex_pairing_flip_exists : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := by
  intro R _ I J K μ
  refine ⟨LateralTheory.EtaleFoundations.FlipPf.flipPair μ, ?_, ?_, LateralTheory.EtaleFoundations.FlipPf.isTensor_flip μ⟩
  · intro U s t w h a b
    simp only [LateralTheory.EtaleFoundations.FlipPf.flipPair, LinearMap.smul_apply, LinearMap.flip_apply, Units.smul_def]
  · intro U s t w h b a
    simp only [LateralTheory.EtaleFoundations.FlipPf.flipPair, LinearMap.smul_apply, LinearMap.flip_apply, Units.smul_def]
    rw [mul_comm s t]
    exact (LateralTheory.EtaleFoundations.FlipPf.negOnePow_smul_smul _ _).symm
end
end

namespace LateralTheory.Fin.EtaleComplexPairingFlipExists
theorem etale_cup_product_flip_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := by
  apply LateralTheory.EtaleFoundations.etale_complex_pairing_flip_exists
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexPairingFlipExists := etale_cup_product_flip_exists_of_components
end LateralTheory.Fin.EtaleComplexPairingFlipExists
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleRootsOfUnityTwistFlatOfLocalFree
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsFlatOfQuotientIso
section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistSheafFlat
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i)
end

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable {q : ℕ} {A : Type} [CommRing A]

theorem prim_pow_q (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
  exact sub_eq_zero.1 h

theorem pow_mod_q (ζ : Prim q A) (n : ℕ) : ζ.1 ^ (n % q) = ζ.1 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, prim_pow_q, one_pow, one_mul]

theorem pow_val_one (ζ : Prim q A) : ζ.1 ^ (1 : ZMod q).val = ζ.1 := by
  rw [ZMod.val_one_eq_one_mod, pow_mod_q, pow_one]

theorem pow_val_mul (ζ : Prim q A) (a b : ZMod q) : ζ.1 ^ (a * b).val = (ζ.1 ^ a.val) ^ b.val := by
  rw [ZMod.val_mul, pow_mod_q, pow_mul]

theorem val_inj [NeZero q] [Nontrivial A] (ζ : Prim q A) (a b : ZMod q) (h : ζ.1 ^ a.val = ζ.1 ^ b.val) : a = b := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let π : A →+* A ⧸ m := Ideal.Quotient.mk m
  have : NeZero ((q : ℕ) : A ⧸ m) := ⟨by
    have hu := ζ.2.1.map π
    rw [map_natCast] at hu
    exact hu.ne_zero⟩
  have hr : IsRoot (cyclotomic q (A ⧸ m)) (π ζ.1) := by
    have h2 := aeval_algHom_apply π.toIntAlgHom ζ.1 (cyclotomic q ℤ)
    rw [ζ.2.2, map_zero] at h2
    rw [IsRoot, ← map_cyclotomic q (algebraMap ℤ (A ⧸ m)), eval_map_algebraMap]
    exact h2
  have hp : IsPrimitiveRoot (π ζ.1) q := (isRoot_cyclotomic_iff).1 hr
  have h3 : (π ζ.1) ^ a.val = (π ζ.1) ^ b.val := by rw [← map_pow, ← map_pow, h]
  exact ZMod.val_injective q (hp.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h3)

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable (q : ℕ) [NeZero q] (A : Type) [CommRing A]

def Rel (ζ ξ : Prim q A) : Prop := ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val

def St : Setoid (Prim q A) where
  r := Rel q A
  iseqv := by
    refine ⟨fun ζ => ⟨1, by rw [Units.val_one, pow_val_one]⟩, ?_, ?_⟩
    · rintro ζ ξ ⟨a, h⟩
      refine ⟨a⁻¹, ?_⟩
      rw [h, ← pow_val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, pow_val_one]
    · rintro ζ ξ η ⟨a, h⟩ ⟨b, h'⟩
      exact ⟨a * b, by rw [h', h, Units.val_mul, pow_val_mul]⟩

variable {q A}

def rep (ξ : Prim q A) : Prim q A := (Quotient.mk (St q A) ξ).out

theorem rep_rel (ξ : Prim q A) : Rel q A (rep ξ) ξ := Quotient.mk_out (s := St q A) ξ

def cc (ξ : Prim q A) : (ZMod q)ˣ := (rep_rel ξ).choose

theorem cc_spec (ξ : Prim q A) : ξ.1 = (rep ξ).1 ^ (cc ξ : ZMod q).val := (rep_rel ξ).choose_spec

theorem rep_eq {ζ ξ : Prim q A} (h : Rel q A ζ ξ) : rep ζ = rep ξ := by
  unfold rep; rw [Quotient.sound (s := St q A) h]

theorem cc_mul [Nontrivial A] {ζ ξ : Prim q A} (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    cc ξ = cc ζ * a := by
  apply Units.ext
  apply val_inj (rep ξ)
  rw [← cc_spec ξ, Units.val_mul, pow_val_mul, ← rep_eq ⟨a, h⟩, ← cc_spec ζ, h]

theorem cc_out [Nontrivial A] (o : Quotient (St q A)) : cc o.out = 1 := by
  have hr : rep o.out = o.out := by
    show (Quotient.mk (St q A) o.out).out = o.out
    rw [Quotient.out_eq]
  apply Units.ext
  apply val_inj o.out
  have h := cc_spec o.out
  rw [hr] at h
  rw [← h, Units.val_one, pow_val_one]

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open GlobalTheory.EtC

variable {q : ℕ} [NeZero q] {A : Type} [CommRing A]

def wt (i : ℤ) (ξ : Prim q A) : ULift.{1} (ZMod q) := ULift.up (((cc ξ ^ i : (ZMod q)ˣ)) : ZMod q)

def psi0 (i : ℤ) : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] (Quotient (St q A) →₀ ULift.{1} (ZMod q)) :=
  Finsupp.linearCombination _ fun ξ => Finsupp.single (Quotient.mk (St q A) ξ) (wt i ξ)

theorem primitive_roots_twisted_weight_map_single (i : ℤ) (ξ : Prim q A) (r : ULift.{1} (ZMod q)) :
    psi0 i (Finsupp.single ξ r) = Finsupp.single (Quotient.mk (St q A) ξ) (r * wt i ξ) := by
  rw [psi0, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul]

theorem rel_le [Nontrivial A] (i : ℤ) : twRel q i A ≤ LinearMap.ker (psi0 i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, primitive_roots_twisted_weight_map_single]
  rw [sub_eq_zero, Quotient.sound (s := St q A) (⟨a, h⟩ : Rel q A ζ ξ)]
  congr 1
  apply ULift.ext
  simp only [wt, ULift.mul_down, cc_mul a h, mul_zpow, Units.val_mul, one_mul]
  ring

def phi [Nontrivial A] (i : ℤ) : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)]
    (Quotient (St q A) →₀ ULift.{1} (ZMod q)) := (twRel q i A).liftQ (psi0 i) (rel_le i)

def theta (i : ℤ) : (Quotient (St q A) →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)]
    ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  (twRel q i A).mkQ ∘ₗ Finsupp.lmapDomain _ _ (fun o : Quotient (St q A) => o.out)

theorem phi_theta [Nontrivial A] (i : ℤ) : phi i ∘ₗ theta (q := q) (A := A) i = LinearMap.id := by
  refine Finsupp.lhom_ext fun o r => ?_
  simp only [theta, phi, LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Submodule.mkQ_apply, Submodule.liftQ_apply, primitive_roots_twisted_weight_map_single, LinearMap.id_apply]
  rw [Quotient.out_eq]
  congr 1
  rw [wt, cc_out, one_zpow, Units.val_one]
  apply ULift.ext
  simp

theorem theta_phi [Nontrivial A] (i : ℤ) : theta i ∘ₗ phi (q := q) (A := A) i = LinearMap.id := by
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ξ r => ?_)
  simp only [theta, phi, LinearMap.coe_comp, Function.comp_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Submodule.mkQ_apply, Submodule.liftQ_apply, primitive_roots_twisted_weight_map_single, LinearMap.id_apply]
  refine (Submodule.Quotient.eq _).2 ?_
  have hm : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single (rep ξ) (ULift.up ((cc ξ ^ i : (ZMod q)ˣ) : ZMod q))
      ∈ twRel q i A := Submodule.subset_span ⟨rep ξ, ξ, cc ξ, cc_spec ξ, rfl⟩
  have h2 := Submodule.smul_mem _ r hm
  rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one] at h2
  rw [← neg_mem_iff, neg_sub]
  exact h2

theorem flat_of_nontrivial [Nontrivial A] (i : ℤ) :
    Module.Flat (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  Module.Flat.of_linearEquiv (LinearEquiv.ofLinearMap (phi i) (theta i) (phi_theta i) (theta_phi i))

end LateralTheory.EtaleFoundations.TwFlat

namespace LateralTheory.EtaleFoundations.TwFlat
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem shf_loc (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U),
      Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 →
      Loc U fun _ g => (P.map g.op).hom x = 0) := by
  constructor
  · intro U y
    refine ⟨Presheaf.imageSieve (toSheafify Scheme.etaleTopology P) y,
      Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩
    rintro V g ⟨t, ht⟩
    exact ⟨t, ht⟩
  · intro U x hx
    have h : (toSheafify Scheme.etaleTopology P).app (op U) x = (toSheafify Scheme.etaleTopology P).app (op U) 0 := by
      change ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0
      rw [hx, map_zero]
    refine ⟨Presheaf.equalizerSieve (F := P) (X := op U) x 0,
      Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩
    intro V g hg
    have hg' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    rw [hg', map_zero]

end LateralTheory.EtaleFoundations.TwFlat


open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_sections_flat_of_quotient_iso : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := by
  intro q _ i
  obtain ⟨h1, h2⟩ := LateralTheory.EtaleFoundations.TwFlat.shf_loc (ZMod q) (Scheme.Γ ⋙ twF q i)
  refine ⟨Scheme.Γ ⋙ twF q i, toSheafify Scheme.etaleTopology _, h1, h2, fun U hU => ?_⟩
  have : Nonempty (⊤ : U.Opens) := ⟨⟨hU.some, trivial⟩⟩
  exact LateralTheory.EtaleFoundations.TwFlat.flat_of_nontrivial (A := Γ(U, ⊤)) i
end
end

namespace LateralTheory.Fin.EtaleTateTwistSheafFlat
theorem etale_roots_of_unity_twist_flat_of_local_free : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := by
  apply LateralTheory.EtaleFoundations.etale_tate_twist_sections_flat_of_quotient_iso
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat := etale_roots_of_unity_twist_flat_of_local_free
end LateralTheory.Fin.EtaleTateTwistSheafFlat
end
