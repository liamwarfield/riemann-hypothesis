module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwist
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplitting
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUnitEqMultiplicativeGroupSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EqOfUnitGlobalSectionEq
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.GmInj
open Polynomial

private noncomputable def evalT {A : Type} [CommRing A] (a : A) : ℤ[X] →+* A :=
  Polynomial.eval₂RingHom (Int.castRingHom A) a

private noncomputable abbrev Line : Scheme.{0} := Spec (CommRingCat.of ℤ[X])

private noncomputable def toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) : V ⟶ Line :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalT a))

private noncomputable def coord {V : Scheme.{0}} (f : V ⟶ Line) : Γ(V, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

private lemma line_sheaf : Presieve.IsSheaf Scheme.etaleTopology (yoneda.obj Line) :=
  Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end UpperTheory.GmInj

private theorem gmInj_coord_toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) :
    UpperTheory.GmInj.coord (UpperTheory.GmInj.toLine a) = a := by
  unfold UpperTheory.GmInj.coord UpperTheory.GmInj.toLine
  rw [Scheme.Hom.comp_appTop]
  simp [UpperTheory.GmInj.evalT]

private theorem comp_gmInj_toLine {V W : Scheme.{0}} (f : W ⟶ V) (a : Γ(V, ⊤)) :
    f ≫ UpperTheory.GmInj.toLine a = UpperTheory.GmInj.toLine (f.appTop.hom a) := by
  unfold UpperTheory.GmInj.toLine
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  apply Polynomial.ringHom_ext
  · intro n
    simp [UpperTheory.GmInj.evalT]
  · simp [UpperTheory.GmInj.evalT]

theorem UpperTheory.eq_of_unitGlobalSection_eq :
    ∀ (U : Scheme.{0}) (u v : (Γ(U, ⊤))ˣ), unitSec u = unitSec v → u = v := by
  intro U u v h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op U)
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v)) h
  have key : UpperTheory.GmInj.toLine (u : Γ(U, ⊤)) = UpperTheory.GmInj.toLine (v : Γ(U, ⊤)) := by
    refine (UpperTheory.GmInj.line_sheaf _ hS).isSeparatedFor
      (fun W f _ => f ≫ UpperTheory.GmInj.toLine (u : Γ(U, ⊤)))
      _ _ (fun W f hf => rfl) (fun W f hf => ?_)
    show f ≫ UpperTheory.GmInj.toLine _ = f ≫ UpperTheory.GmInj.toLine _
    rw [comp_gmInj_toLine, comp_gmInj_toLine]
    have h2 := congrArg (fun z : ULift (Additive (Scheme.Γ.obj (op W))ˣ) =>
      ((Additive.toMul z.down : (Scheme.Γ.obj (op W))ˣ) : Scheme.Γ.obj (op W))) hf
    have h3 : f.appTop.hom (u : Γ(U, ⊤)) = f.appTop.hom v := h2
    rw [h3]
  have h4 := congrArg UpperTheory.GmInj.coord key
  rw [gmInj_coord_toLine, gmInj_coord_toLine] at h4
  exact Units.ext h4
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.KumSExact
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Deg2

abbrev T (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def kap (q : ℕ) [NeZero q] : T q ⟶ Gm := (GlobalTheory.T.kummer_sequence_etale_tateTwist q).choose

theorem kap_spec (q : ℕ) [NeZero q] : Mono (kap q) ∧ kap q ≫ ((q : ℤ) • 𝟙 Gm) = 0 ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map (kap q) (show Sec (T q) U from twGen 1 ζ) = unitSec u) ∧ (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map (kap q) a = b) ∧ ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b :=
  (GlobalTheory.T.kummer_sequence_etale_tateTwist q).choose_spec

section MV
variable (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)

end MV

section Shrink
variable (R : Type) [CommRing R] (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B)

end Shrink

end UpperTheory.Deg2
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.KummerClassAddOfUnitSecAdd
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

private theorem prim_pow (q : ℕ) {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

private theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom x) h

private theorem sec_res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U)
    (x y : Sec F U) : Sec.res g (x + y) = Sec.res g x + Sec.res g y :=
  map_add (F.obj.map g.op).hom x y

private theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

private theorem sec_map_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ)
    (x : Sec F U) : Sec.map φ (c • x) = c • Sec.map φ x :=
  map_nsmul (φ.hom.app (op U)).hom c x

private theorem unitSec_pow_mul {W : Scheme.{0}} (u w : (Γ(W, ⊤))ˣ) (c : ℕ) :
    unitSec (u ^ c * w) = unitSec w + c • unitSec u := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ', mul_assoc, UpperTheory.PicD.unitSec_mul, ih, succ_nsmul]
    abel

private theorem kumT_pow_mul (q : ℕ) [NeZero q] (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (u w : (Γ(W, ⊤))ˣ)
    (hu : (u : Γ(W, ⊤)) = ζ.1) (c : ℕ) :
    kumT q W (u ^ c * w) = kumT q W w + c • resGen 1 ζ := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 W ζ (u ^ c * w) (u ^ (c + 1) * w)
      (by rw [pow_succ', mul_assoc, Units.val_mul, hu])
    rw [h, ih, succ_nsmul, add_assoc]

theorem UpperTheory.kummer_class_add_of_unitSec_add :
    ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}), IsUnit (q : Γ(V, ⊤)) → ∀ (v v' : (Γ(V, ⊤))ˣ) (a : Sec (tw q 1) V), unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) (show Sec (UpperTheory.Deg2.T q) V from a) → kumT q V v' = kumT q V v + Sec.map (resι _ (tw q 1)) a := by
  intro q _ V hq v v' a h
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) _ V).1 _ _ ?_
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).1 V a
  refine ⟨S, hS, fun W g hg => ?_⟩
  show Sec.res g (kumT q V v') = Sec.res g (kumT q V v + Sec.map (resι _ (tw q 1)) a)
  have hK := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V g
  let b : Sec (UpperTheory.Deg2.T q) V := a
  let bW : Sec (UpperTheory.Deg2.T q) W := Sec.res g a
  have hb : Sec.res g (Sec.map (UpperTheory.Deg2.kap q) b) = Sec.map (UpperTheory.Deg2.kap q) bW :=
    (sec_map_res (UpperTheory.Deg2.kap q) g b).symm
  have h' : unitSec (Units.map g.appTop.hom.toMonoidHom v') = unitSec (Units.map g.appTop.hom.toMonoidHom v) +
      Sec.map (UpperTheory.Deg2.kap q) bW := by
    have h0 : unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) b := h
    have h1 := congrArg (Sec.res g) h0
    rw [sec_res_add, UpperTheory.PicD.unitSec_res, UpperTheory.PicD.unitSec_res, hb] at h1
    exact h1
  rw [sec_res_add, hK v hq, hK v' hq, ← sec_map_res]
  rcases hP W g hg with h0 | ⟨ζ, c, hc⟩
  · have h2 : Sec.map (UpperTheory.Deg2.kap q) bW = 0 := by
      have : bW = 0 := h0
      rw [this]
      exact sec_map_zero _
    rw [h0, sec_map_zero, add_zero]
    rw [h2, add_zero] at h'
    rw [UpperTheory.eq_of_unitGlobalSection_eq _ _ _ h']
  · have hun : IsUnit ζ.1 := isUnit_iff_exists_inv.2 ⟨ζ.1 ^ (q - 1), by
      rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q)]
      exact prim_pow q ζ⟩
    obtain ⟨u, hu⟩ := hun
    have h2 : Sec.map (UpperTheory.Deg2.kap q) bW = c • unitSec u := by
      have : bW = c • (show Sec (UpperTheory.Deg2.T q) W from twGen 1 ζ) := hc
      rw [this, sec_map_nsmul, (UpperTheory.Deg2.kap_spec q).2.2.1 W ζ u hu]
    rw [h2, ← unitSec_pow_mul] at h'
    rw [UpperTheory.eq_of_unitGlobalSection_eq _ _ _ h', kumT_pow_mul q W ζ u _ hu c, hc, sec_map_nsmul]
    rfl
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.KumRoot

private lemma map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (ModuleCat.Hom.hom (φ.hom.app (op V))) ((ModuleCat.Hom.hom (F.obj.map g.op)) x) =
    (ModuleCat.Hom.hom (G.obj.map g.op)) ((ModuleCat.Hom.hom (φ.hom.app (op U))) x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private lemma res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res k (Sec.res g x) = Sec.res (k ≫ g) x := by
  show (ModuleCat.Hom.hom (F.obj.map k.op)) ((ModuleCat.Hom.hom (F.obj.map g.op)) x) =
    (ModuleCat.Hom.hom (F.obj.map (k ≫ g).op)) x
  rw [← ModuleCat.comp_apply, ← F.obj.map_comp]
  rfl

private lemma sec_map_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := by
  exact map_add _ a b

private lemma sec_map_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := by
  exact map_sub _ a b

private lemma sec_res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := by
  exact map_add _ a b

private lemma sec_res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (a : Sec F U) :
    Sec.res g (n • a) = n • Sec.res g a := by
  exact map_nsmul _ n a

private lemma map_smul_int {V : Scheme.{0}} (b : Sec Gm V) (n : ℤ) : Sec.map (n • 𝟙 Gm) b = n • b := by
  rfl

private lemma unitSec_pow {U : Scheme.{0}} (v : (Γ(U, ⊤))ˣ) (n : ℕ) : unitSec (v ^ n) = n • unitSec v := by
  induction n with
  | zero => simp [UpperTheory.PicD.unitSec_one]
  | succ n ih => rw [pow_succ, UpperTheory.PicD.unitSec_mul, ih, succ_nsmul]

private lemma units_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : (Γ(U, ⊤))ˣ) :
    Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom w) =
      Units.map (k ≫ g).appTop.hom.toMonoidHom w := by
  ext
  simp [Scheme.Hom.appTop, Scheme.Hom.app]
  rfl

private lemma ker_res {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (z : Sec ((res R F).X 0) U)
    (hz : Sec.map ((res R F).d 0 1) z = 0) : ∃ s : Sec F U, Sec.map (resι R F) s = z := by
  obtain ⟨α, hα0, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R U (res R F) (-1) 0 1 (by norm_num) (by norm_num)).1 z hz
  obtain ⟨s, hs⟩ := (GlobalTheory.T.degreeZeroSectionClass_properties R F U).2.1.2 (CohomologyClass.mk α)
  refine ⟨s, ?_⟩
  have h1 := ((GlobalTheory.T.degreeZeroSectionClass_properties R F U).1 s α).2 hs.symm
  rw [← h1, hα0]
  show (ModuleCat.Hom.hom (((res R F).X 0).obj.map (𝟙 U).op)) z = z
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma resι_inj {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Sec.map (resι R F) a = Sec.map (resι R F) b) : a = b := by
  obtain ⟨α, hα⟩ := CohomologyClass.mk_surjective (secClass F a)
  have h1 := ((GlobalTheory.T.degreeZeroSectionClass_properties R F U).1 a α).2 hα
  have h2 := ((GlobalTheory.T.degreeZeroSectionClass_properties R F U).1 b α).1 (h1.trans h)
  exact (GlobalTheory.T.degreeZeroSectionClass_properties R F U).2.1.1 (hα.symm.trans h2)

variable (q : ℕ) [NeZero q]

private noncomputable def kp {V : Scheme.{0}} (s : Sec (tw q 1) V) : Sec Gm V :=
  Sec.map (UpperTheory.Deg2.kap q) (show Sec (UpperTheory.Deg2.T q) V from s)

private lemma kp_add {V : Scheme.{0}} (s t : Sec (tw q 1) V) : kp q (s + t) = kp q s + kp q t := by
  unfold kp
  exact sec_map_add _ _ _

private lemma kp_res {W V : Scheme.{0}} (k : W ⟶ V) (s : Sec (tw q 1) V) :
    Sec.res k (kp q s) = kp q (Sec.res k s) := by
  unfold kp
  exact (map_res _ _ _).symm

private lemma kp_nsmul {V : Scheme.{0}} (s : Sec (tw q 1) V) : q • kp q s = 0 := by
  unfold kp
  have h0 := (UpperTheory.Deg2.kap_spec q).2.1
  have h1 : Sec.map ((q : ℤ) • 𝟙 Gm) (Sec.map (UpperTheory.Deg2.kap q) (show Sec (UpperTheory.Deg2.T q) V from s)) =
      Sec.map (UpperTheory.Deg2.kap q ≫ ((q : ℤ) • 𝟙 Gm)) (show Sec (UpperTheory.Deg2.T q) V from s) := rfl
  rw [← natCast_zsmul, ← map_smul_int, h1, h0]
  rfl

private lemma unique_datum {V : Scheme.{0}} (hq : IsUnit (q : Γ(V, ⊤))) (v v' : (Γ(V, ⊤))ˣ)
    (s s' : Sec (tw q 1) V) (hv : v ^ q = v' ^ q)
    (h : kumT q V v + Sec.map (resι _ (tw q 1)) s = kumT q V v' + Sec.map (resι _ (tw q 1)) s') :
    unitSec v + kp q s = unitSec v' + kp q s' := by
  have hx : Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec (v⁻¹ * v')) = 0 := by
    rw [map_smul_int, natCast_zsmul, ← unitSec_pow, mul_pow, ← hv, inv_pow, inv_mul_cancel,
      UpperTheory.PicD.unitSec_one]
  obtain ⟨a, ha⟩ := (UpperTheory.Deg2.kap_spec q).2.2.2.1 V hq (unitSec (v⁻¹ * v')) hx
  have e1 : unitSec v' = unitSec v + Sec.map (UpperTheory.Deg2.kap q) a := by
    rw [ha, ← UpperTheory.PicD.unitSec_mul, mul_inv_cancel_left]
  have e2 := UpperTheory.kummer_class_add_of_unitSec_add q V hq v v' a e1
  rw [e2, add_assoc] at h
  have h3 : Sec.map (resι _ (tw q 1)) s = Sec.map (resι _ (tw q 1)) ((show Sec (tw q 1) V from a) + s') := by
    rw [sec_map_add]
    exact add_left_cancel h
  have hs := resι_inj _ _ _ _ h3
  rw [hs, kp_add, e1, add_assoc]
  rfl

end UpperTheory.KumRoot

open UpperTheory.KumRoot in
theorem UpperTheory.exists_root_of_kummer_class_eq_zero :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (w : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q w = 0 → ∃ v : (Γ(X, ⊤))ˣ, v ^ q = w := by
  intro q _ X w hq hw
  obtain ⟨γ, hγ, -, hγ2⟩ := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).1 X w hq
  rw [hw] at hγ
  obtain ⟨y, hy⟩ := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff (ZMod q) X (res (ZMod q) (tw q 1)) 0 1 2 (by norm_num) (by norm_num)).2 γ).2.1 hγ
  have hqV : ∀ {V : Scheme.{0}} (g : V ⟶ X), IsUnit (q : Γ(V, ⊤)) := by
    intro V g
    have := hq.map g.appTop.hom
    simpa using this
  let D : (V : Scheme.{0}) → (V ⟶ X) → Sec Gm V → Prop := fun V g b =>
    ∃ (v : (Γ(V, ⊤))ˣ) (s : Sec (tw q 1) V),
      v ^ q = Units.map ↑(CommRingCat.Hom.hom (Scheme.Hom.appTop g)) w ∧
      Sec.res g y = kumT q V v + Sec.map (resι _ (tw q 1)) s ∧ b = unitSec v + kp q s
  have hA : ∀ {V : Scheme.{0}} (g : V ⟶ X) (v : (Γ(V, ⊤))ˣ),
      v ^ q = Units.map ↑(CommRingCat.Hom.hom (Scheme.Hom.appTop g)) w → ∃ b, D V g b := by
    intro V g v hv
    have e := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q) (E := sch.obj X) (I := res (ZMod q) (tw q 1)) (n := 1)).2.1
      (γ : Cochain _ _ 1) 0 1 (by norm_num) V X g (𝟙 X)
    have hd : Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (Sec.res g y - kumT q V v) = 0 := by
      rw [sec_map_sub, map_res, hy, sub_eq_zero]
      refine e.trans ?_
      exact hγ2 V g v hv
    obtain ⟨s, hs⟩ := ker_res _ V _ hd
    exact ⟨_, v, s, hv, by rw [hs]; abel, rfl⟩
  have hB : ∀ {V : Scheme.{0}} (g : V ⟶ X) (b b' : Sec Gm V), D V g b → D V g b' → b = b' := by
    intro V g b b' ⟨v, s, hv, hs, hb⟩ ⟨v', s', hv', hs', hb'⟩
    rw [hb, hb']
    exact unique_datum q (hqV g) v v' s s' (hv.trans hv'.symm) (hs.symm.trans hs')
  have hC : ∀ {V W : Scheme.{0}} (g : V ⟶ X) (k : W ⟶ V) (b : Sec Gm V), D V g b → D W (k ≫ g) (Sec.res k b) := by
    intro V W g k b ⟨v, s, hv, hs, hb⟩
    refine ⟨Units.map ↑(CommRingCat.Hom.hom (Scheme.Hom.appTop k)) v, Sec.res k s, ?_, ?_, ?_⟩
    · rw [← map_pow, hv]
      exact units_comp k g w
    · rw [← res_comp, hs, KumRoot.sec_res_add, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 W V k v (hqV g), map_res]
      rfl
    · rw [hb, KumRoot.sec_res_add, UpperTheory.PicD.unitSec_res, kp_res]
      rfl
  have hloc : Loc X fun V g => ∃ b, D V g b :=
    GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 X _ _ ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q X).2.2.2 hq w) (fun V g ⟨v, hv⟩ => hA g v hv)
  obtain ⟨S, hS, hSP⟩ := hloc
  obtain ⟨b0, hb0⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ Gm X).2 S hS (fun V g hg => Classical.choose (hSP V g hg))
    (fun V W g k hg => hB (k ≫ g) _ _ (hC g k _ (Classical.choose_spec (hSP V g hg)))
      (Classical.choose_spec (hSP W (k ≫ g) (S.downward_closed hg k))))
  obtain ⟨u, hu⟩ := UpperTheory.exists_unit_eq_multiplicativeGroup_section X b0
  refine ⟨u, UpperTheory.eq_of_unitGlobalSection_eq X _ _ ?_⟩
  rw [unitSec_pow, hu]
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ Gm X).1
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨v, s, hv, -, hb⟩ := Classical.choose_spec (hSP V g hg)
  rw [sec_res_nsmul, hb0 V g hg, hb, nsmul_add, kp_nsmul, add_zero, ← unitSec_pow, hv,
    UpperTheory.PicD.unitSec_res]
  rfl
