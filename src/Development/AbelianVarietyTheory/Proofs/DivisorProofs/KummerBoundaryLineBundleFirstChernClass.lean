module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.KumPic

abbrev twZ (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def dv (q : ℕ) (φ : Gm ⟶ (res ℤ (twZ q)).X 0) (U : Scheme.{0}) (v : (Γ(U, ⊤))ˣ) : Sec ((res ℤ (twZ q)).X 0) U :=
  Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v)

end GlobalTheory.EtC.KumPic

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectEqOfPowEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectEqOfPowEq
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

noncomputable section

namespace GlobalTheory.EtC.KumPic

section
variable (q : ℕ) [NeZero q]

theorem prim_pow_eq_one {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨r, hr⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hr
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, ζ.2.2, zero_mul] at h
  exact sub_eq_zero.mp h

def primUnit {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  Units.ofPowEqOne ζ.1 q (prim_pow_eq_one q ζ) (NeZero.ne q)

theorem primUnit_val {A : Type} [CommRing A] (ζ : Prim q A) : ((primUnit q ζ : Aˣ) : A) = ζ.1 :=
  Units.val_ofPowEqOne _ _ _ _

theorem dv_res (φ : Gm ⟶ (res ℤ (twZ q)).X 0) {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤)))
    (v : (Γ(U, ⊤))ˣ) : Sec.res g (dv q φ U v) = dv q φ V (Units.map g.appTop.hom.toMonoidHom v) := by
  unfold dv
  rw [show ∀ a b : Sec ((res ℤ (twZ q)).X 0) U, Sec.res g (a - b) = Sec.res g a - Sec.res g b from
    fun a b => LinearMap.map_sub _ a b, PicSpec.sec_map_res, PicSpec.unitSec_res, (restrMap _ _).nat, (kumT_spec q).1 V U g v hq]

variable (κ : twZ q ⟶ Gm)
  (hκ : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
    Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u)
  (φ : Gm ⟶ (res ℤ (twZ q)).X 0) (hφ : κ ≫ φ = resι ℤ (twZ q))
include hκ hφ

theorem dv_mul_prim {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ) (h : (w : Γ(U, ⊤)) = ζ.1 * v) :
    dv q φ U w = dv q φ U v := by
  have hu := primUnit_val q ζ
  have hw : w = primUnit q ζ * v := Units.ext (by rw [Units.val_mul, hu, h])
  have hk := (kumT_spec q).2 U ζ v w h
  have h1 : Sec.map φ (unitSec (primUnit q ζ)) =
      Sec.map (resι ℤ (twZ q)) (show Sec (twZ q) U from twGen 1 ζ) := by
    rw [← hκ U ζ _ hu, PicSpec.sec_map_comp, hφ]
  have h2 : (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (resGen 1 ζ) =
      Sec.map (resι ℤ (twZ q)) (show Sec (twZ q) U from twGen 1 ζ) :=
    restrMap_spec _ _ U _
  unfold dv
  rw [hk, map_add (f := _), h2, hw, PicSpec.unitSec_mul, PicSpec.sec_map_add, h1]
  abel

theorem dv_mul_prim_pow {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : ℕ) :
    ∀ v w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v → dv q φ U w = dv q φ U v := by
  induction a with
  | zero =>
    intro v w h
    rw [pow_zero, one_mul] at h
    rw [Units.ext h]
  | succ a ih =>
    intro v w h
    have h1 : ((primUnit q ζ ^ a * v : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ζ.1 ^ a * v := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, primUnit_val]
    rw [dv_mul_prim q κ hκ φ hφ ζ (primUnit q ζ ^ a * v) w (by rw [h, h1, pow_succ', mul_assoc]), ih v (primUnit q ζ ^ a * v) h1]

end

theorem dv_eq_of_pow_eq : ∀ (q : ℕ) [NeZero q] (κ : twZ q ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u) → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), κ ≫ φ = resι ℤ (twZ q) → ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v' := by
  intro q _ κ hκ φ hφ U hq v v' hvv
  have sep := fun W : Scheme.{0} => (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ ((res ℤ (twZ q)).X 0) W).1
  apply sep U
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map g.appTop.hom
  rw [dv_res q φ g hq, dv_res q φ g hq]
  set x := Units.map g.appTop.hom.toMonoidHom v
  set x' := Units.map g.appTop.hom.toMonoidHom v'
  have hx : x ^ q = x' ^ q := by simp only [x, x', ← map_pow, hvv]
  apply sep V
  have hω : ((x' * x⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hx, inv_pow, mul_inv_cancel, Units.val_one]
  obtain ⟨S₂, hS₂, hP₂⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ _ hω
  refine ⟨S₂, hS₂, fun W h hh => ?_⟩
  obtain ⟨a, ha⟩ := hP₂ W h hh
  rw [dv_res q φ h hqV, dv_res q φ h hqV]
  symm
  apply dv_mul_prim_pow q κ hκ φ hφ (ζ.map h.appTop.hom) a
  change h.appTop.hom (x' : Γ(V, ⊤)) = (h.appTop.hom ζ.1) ^ a * h.appTop.hom (x : Γ(V, ⊤))
  rw [← ha, ← map_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]

end GlobalTheory.EtC.KumPic

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectEqOfPowEqStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerSplittingDefect_eq_of_pow_eq : ∀ (q : ℕ) [NeZero q] (κ : twZ q ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u) → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), κ ≫ φ = resι ℤ (twZ q) → ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v' := by
  first
  | exact @GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq
  | exact GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq
  | (intros; apply GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCocycleSubChernClassCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCocycleSubChernClassCoboundary
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

namespace GlobalTheory.EtC.KumPic.Cobd

theorem res_zero {F : Shv ℤ} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem res_id {F : Shv ℤ} {U : Scheme.{0}} (s : Sec F U) : Sec.res (𝟙 U) s = s := by simp [Sec.res]

theorem res_res {F : Shv ℤ} {W V U : Scheme.{0}} (g : V ⟶ U) (g' : W ⟶ V) (s : Sec F U) :
    Sec.res g' (Sec.res g s) = Sec.res (g' ≫ g) s := by simp [Sec.res]

theorem umap_id {U : Scheme.{0}} (b : (Γ(U, ⊤))ˣ) : Units.map (𝟙 U : U ⟶ U).appTop.hom.toMonoidHom b = b := by
  ext; simp

theorem umap_comp {W V U : Scheme.{0}} (g : V ⟶ U) (g' : W ⟶ V) (b : (Γ(U, ⊤))ˣ) :
    Units.map (g' ≫ g).appTop.hom.toMonoidHom b =
      Units.map g'.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom b) := by
  ext; simp; rfl

theorem ev_sub {E : Spc} {I : Cx ℤ} {n : ℤ} (a b : Cochain ((chains ℤ).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (a - b) p s h U x = ev a p s h U x - ev b p s h U x := map_sub (CupSpec.evHom I n p s h U x) a b

theorem ev_comp {E : Spc} {L M : Cx ℤ} {n₁ n₂ n : ℤ} (a : Cochain ((chains ℤ).obj E) L n₁) (b : Cochain L M n₂)
    (hn : n₁ + n₂ = n) (p : ℕ) (t s : ℤ) (ht : -(p : ℤ) + n₁ = t) (hs : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (a.comp b hn) p s hs U x = Sec.map (b.v t s (by omega)) (ev a p t ht U x) := by
  rw [CupSpec.ev_def, CupSpec.ev_def, Cochain.comp_v a b hn (-(p : ℤ)) t s ht (by omega)]
  rfl

theorem sglZ (C : Shv ℤ) (k : ℤ) (hk : k ≠ 0) : IsZero ((sgl C).X k) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 C k hk

theorem face_two {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  have e : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
      SimplexCategory.subinterval 0 1 (by omega) :=
    CupSpec.hom_ext_val _ _ fun v => by
      rw [CupSpec.δ_val, CupSpec.sub_val]; have := v.2; simp; omega
  show (E.map (SimplexCategory.δ (2 : Fin 3)).op).app (op U) x = _
  rw [e]; rfl

theorem face_zero {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  have e : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
      SimplexCategory.subinterval 1 1 (by omega) :=
    CupSpec.hom_ext_val _ _ fun v => by
      rw [CupSpec.δ_val, CupSpec.sub_val]; simp
  show (E.map (SimplexCategory.δ (0 : Fin 3)).op).app (op U) x = _
  rw [e]; rfl

theorem mkiff {E : Spc} {I : Cx ℤ} (a b : Cocycle ((chains ℤ).obj E) I 2) :
    CohomologyClass.mk a = CohomologyClass.mk b ↔ ∃ w : Cochain _ I 1, δ 1 2 w = a.1 - b.1 := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  rfl

theorem sep_zero {F : Shv ℤ} {U : Scheme.{0}} (s : Sec F U) (h : Loc U fun _ g => Sec.res g s = 0) : s = 0 := by
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ F U).1 s 0 ?_
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => (hP V g hg).trans (res_zero g).symm⟩

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem isUnit_of_sx {q : ℕ} {E : Spc} (hE : Inv q E) {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    IsUnit (q : Γ(U, ⊤)) :=
  hE U ⟨x.sub 0 0 (by omega)⟩

theorem eta_unique (q : ℕ) [NeZero q] (φ : Gm ⟶ (res ℤ (twZ q)).X 0) {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤)))
    (b : (Γ(U, ⊤))ˣ) (η η' : Sec ((res ℤ (twZ q)).X 0) U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b →
      Sec.res g η = dv q φ V v)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b →
      Sec.res g η' = dv q φ V v) : η = η' :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ _ U).1 η η' (loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 hq b)
    fun V g ⟨v, hv⟩ => (h V g v hv).trans (h' V g v hv).symm)

def thF (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res ℤ (twZ q)).X s) U
  | 1, s, h, U, x => Sec.map ((res ℤ (twZ q)).XIsoOfEq (show (0 : ℤ) = s by omega)).hom (η U x)
  | _, _, _, _, _ => 0

theorem thF_zero (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U) (s : ℤ)
    (h : -((0 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E 0 U) : thF q η 0 s h U x = 0 := rfl

theorem thF_two (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U) (p : ℕ) (s : ℤ)
    (h : -((p + 2 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E (p + 2) U) : thF q η (p + 2) s h U x = 0 := rfl

theorem thF_one (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E 1 U) : thF q η 1 0 h U x = η U x := by
  simp [thF, Sec.map]

theorem thF_nat (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (hη : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (η U x) = η V (x.res g)) :
    ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (thF q η p s h U x) = thF q η p s h V (x.res g) := by
  intro p s h V U g x
  match p with
  | 0 => rw [thF_zero, thF_zero, res_zero]
  | 1 =>
    obtain rfl : s = 0 := by omega
    rw [thF_one, thF_one, hη]
  | p + 2 => rw [thF_two, thF_two, res_zero]

theorem thF_one' (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (h : -((0 + 1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E (0 + 1) U) : thF q η (0 + 1) 0 h U x = η U x :=
  thF_one q η h U x

theorem thF_two' (q : ℕ) {E : Spc} (η : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res ℤ (twZ q)).X 0) U)
    (h : -((1 + 1 : ℕ) : ℤ) + 1 = -1) (U : Scheme.{0}) (x : Sx E (1 + 1) U) : thF q η (1 + 1) (-1) h U x = 0 := rfl

theorem smap_sub {F G : Shv ℤ} (f : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map f (a - b) = Sec.map f a - Sec.map f b := map_sub _ _ _

theorem cobd : ∀ (q : ℕ) [NeZero q] (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v) → ∀ (C : Shv ℤ) (a : Cocycle ((chains ℤ).obj E) (sgl C) 1) (w : Cocycle (sgl C) (res ℤ (twZ q)) 1), (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → Sec.map (w.1.v 0 1 (zero_add 1)) (ev a.1 1 0 (by simp) U x) = Sec.map ((res ℤ (twZ q)).d 0 1) (Sec.map φ (unitSec v))) → CohomologyClass.mk (zcomp a w rfl) = restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  intro q _ E L hE φ hφ C a w hw
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hE
  obtain ⟨β, hβ⟩ := SemiMap.image_exists (restrMap (Int.castRingHom (ZMod q)) (tw q 1)) E 2 γ
  have hβc : restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) = CohomologyClass.mk β := by
    rw [← hγ]; exact SemiMap.op_spec _ E 2 γ β hβ
  rw [hβc]
  have h2 : (1 : ℤ) + 1 = 2 := by norm_num
  change CohomologyClass.mk (zcomp a w h2) = _
  choose η hη using fun (U : Scheme.{0}) (x : Sx E 1 U) => hφ U (lineUnit L x) (isUnit_of_sx hE x)
  have ηnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (η U x) = η V (x.res g) := by
    intro V U g x
    refine eta_unique q φ (isUnit_of_sx hE (x.res g)) (lineUnit L (x.res g)) _ _ (fun V' g' v hv => ?_)
      (hη V (x.res g))
    rw [res_res]
    exact hη U x V' (g' ≫ g) v (by rw [umap_comp, ← PicSpec.lineUnit_res]; exact hv)
  have ηroot : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → η U x = dv q φ U v := by
    intro U x v hv
    have := hη U x U (𝟙 U) v (by rw [umap_id]; exact hv)
    rwa [res_id] at this
  obtain ⟨θ, hθ⟩ := CupSpec.ev_exists (E := E) (I := res ℤ (twZ q)) (n := 1) (thF q η) (thF_nat q η ηnat)
  have hzc : (zcomp a w h2).1 = a.1.comp w.1 h2 := rfl
  have key1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (δ 1 2 θ - ((zcomp a w h2).1 - β.1)) 1 1 (by simp) U x = 0 := by
    intro U x v hv
    rw [ev_sub, ev_sub, CupSpec.ev_δ_succ (by norm_num) θ U 0 0 1 (by simp) (by simp) x, hzc,
      ev_comp a.1 w.1 h2 1 0 1 (by simp) (by simp) U x, hw U x v hv, hβ, hγ1 U x v hv,
      ← (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).comm]
    simp only [hθ, thF_zero, thF_one', ηroot U x v hv, dv, smap_sub, smul_zero, Finset.sum_const_zero, add_zero]
    abel
  have key2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v u : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      u ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (δ 1 2 θ - ((zcomp a w h2).1 - β.1)) 2 0 (by simp) U x = 0 := by
    intro U x v u hv hu
    rw [ev_sub, ev_sub, CupSpec.ev_δ_succ (by norm_num) θ U 1 (-1) 0 (by simp) (by simp) x, hzc,
      ev_comp a.1 w.1 h2 2 (-1) 0 (by simp) (by simp) U x,
      PicSpec.sec_eq_zero (sglZ C (-1) (by omega)) (ev a.1 2 (-1) _ U x), PicSpec.sec_map_zero, hβ,
      hγ2 U x v u hv hu, Fin.sum_univ_three]
    simp only [hθ, thF_two', thF_one, PicSpec.sec_map_zero]
    have e2 : η U (x.face 2) = dv q φ U v := ηroot U _ v (by rw [face_two]; exact hv)
    have e0 : η U (x.face 0) = dv q φ U u := ηroot U _ u (by rw [face_zero]; exact hu)
    have e1 : η U (x.face 1) = dv q φ U (v * u) := ηroot U _ (v * u) (by
      rw [PicSpec.lineUnit_face, face_two, face_zero, mul_pow, hv, hu, mul_comm])
    rw [e0, e1, e2]
    have hn2 : (2 : ℤ).negOnePow = 1 := by decide
    simp only [dv, PicSpec.unitSec_mul, PicSpec.sec_map_add, smap_sub, map_add (f := _), map_sub, hn2, one_smul, Fin.val_zero,
      Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, neg_smul]
    abel
  refine (mkiff _ _).2 ⟨θ, sub_eq_zero.mp (CupSpec.ev_ext _ _ fun p s h U x => ?_)⟩
  rw [CupSpec.ev_zero]
  match p with
  | 0 =>
    obtain rfl : s = 2 := by omega
    rw [ev_sub, ev_sub, CupSpec.ev_δ_zero (by norm_num) θ U 1 2 (by simp) h x, hθ, thF_zero, PicSpec.sec_map_zero, hzc,
      ev_comp a.1 w.1 h2 0 1 2 (by simp) h U x, PicSpec.sec_eq_zero (sglZ C 1 (by omega)) (ev a.1 0 1 _ U x),
      PicSpec.sec_map_zero, hβ, hγ0, map_zero]
    simp
  | 1 =>
    obtain rfl : s = 1 := by omega
    apply sep_zero
    refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 (isUnit_of_sx hE x) (lineUnit L x)) fun V g ⟨v, hv⟩ => ?_
    rw [CupSpec.ev_res]
    exact key1 V (x.res g) v (by rw [PicSpec.lineUnit_res]; exact hv)
  | 2 =>
    obtain rfl : s = 0 := by omega
    apply sep_zero
    refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 (isUnit_of_sx hE x) (lineUnit L (x.sub 0 1 (by omega))))
      fun V g ⟨v, hv⟩ => ?_
    rw [CupSpec.ev_res]
    apply sep_zero
    refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.2 (isUnit_of_sx hE (x.res g)) (lineUnit L ((x.res g).sub 1 1 (by omega))))
      fun V' g' ⟨u, hu⟩ => ?_
    rw [CupSpec.ev_res]
    refine key2 V' ((x.res g).res g') (Units.map g'.appTop.hom.toMonoidHom v) u ?_ ?_
    · rw [CupSpec.sub_res, CupSpec.sub_res, PicSpec.lineUnit_res, PicSpec.lineUnit_res, ← hv, map_pow]
    · rw [CupSpec.sub_res, PicSpec.lineUnit_res]; exact hu
  | p + 3 =>
    exact PicSpec.sec_eq_zero (PicSpec.res_isZero _ s (by omega)) _

end GlobalTheory.EtC.KumPic.Cobd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerCocycleSubChernClassCoboundaryStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCocycle_sub_chernClass_coboundary : ∀ (q : ℕ) [NeZero q] (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v) → ∀ (C : Shv ℤ) (a : Cocycle ((chains ℤ).obj E) (sgl C) 1) (w : Cocycle (sgl C) (res ℤ (twZ q)) 1), (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → Sec.map (w.1.v 0 1 (zero_add 1)) (ev a.1 1 0 (by simp) U x) = Sec.map ((res ℤ (twZ q)).d 0 1) (Sec.map φ (unitSec v))) → CohomologyClass.mk (zcomp a w rfl) = restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  first
  | exact @GlobalTheory.EtC.KumPic.Cobd.cobd
  | exact GlobalTheory.EtC.KumPic.Cobd.cobd
  | (intros; apply GlobalTheory.EtC.KumPic.Cobd.cobd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectGlueQthRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectGlueQthRoots
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

noncomputable section
namespace GlobalTheory.EtC.KumPic.DvGlue

private theorem unitsMap_comp_appTop {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) := by
  ext
  simp [Scheme.Hom.comp_appTop]
  rfl

private theorem isUnit_natCast_appTop {V U : Scheme.{0}} (g : V ⟶ U) (q : ℕ) (h : IsUnit (q : Γ(U, ⊤))) :
    IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem dv_res (q : ℕ) (φ : Gm ⟶ (res ℤ (twZ q)).X 0) {V U : Scheme.{0}} (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ)
    (hq : IsUnit (q : Γ(U, ⊤))) :
    Sec.res g (dv q φ U v) = dv q φ V (Units.map g.appTop.hom.toMonoidHom v) := by
  unfold dv
  rw [show ∀ a b : Sec ((res ℤ (twZ q)).X 0) U, Sec.res g (a - b) = Sec.res g a - Sec.res g b from
    fun a b => map_sub _ a b]
  rw [PicSpec.sec_map_res, PicSpec.unitSec_res, SemiMap.nat, (kumT_spec q).1 V U g v hq]

theorem glue : ∀ (q : ℕ) [NeZero q] (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v') → ∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v := by
  intro q _ φ hdv U b hq
  let S : Sieve U :=
    { arrows := fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom b
      downward_closed := by
        rintro V W g ⟨v, hv⟩ k
        refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
        rw [← map_pow, hv, unitsMap_comp_appTop] }
  have hS : S ∈ Scheme.etaleTopology U := by
    obtain ⟨S₀, hS₀, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 hq b
    exact GrothendieckTopology.superset_covering _ (fun V g hg => hP V g hg) hS₀
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res ℤ (twZ q)).X 0) V :=
    fun V g hg => dv q φ V hg.choose
  have hcompat : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k) := by
    intro V W g k hg
    have hqV : IsUnit (q : Γ(V, ⊤)) := isUnit_natCast_appTop g q hq
    have hqW : IsUnit (q : Γ(W, ⊤)) := isUnit_natCast_appTop k q hqV
    change Sec.res k (dv q φ V hg.choose) = dv q φ W (S.downward_closed hg k).choose
    rw [dv_res q φ k hg.choose hqV]
    refine hdv W hqW _ _ ?_
    rw [(S.downward_closed hg k).choose_spec, ← map_pow, hg.choose_spec, unitsMap_comp_appTop]
  obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).2 S hS s hcompat
  refine ⟨a, fun V g v hv => ?_⟩
  have hg : S.arrows g := ⟨v, hv⟩
  rw [ha V g hg]
  exact hdv V (isUnit_natCast_appTop g q hq) _ _ (hg.choose_spec.trans hv.symm)

end GlobalTheory.EtC.KumPic.DvGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectGlueQthRootsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerSplittingDefect_glue_qthRoots : ∀ (q : ℕ) [NeZero q] (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v') → ∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v := by
  first
  | exact @GlobalTheory.EtC.KumPic.DvGlue.glue
  | exact GlobalTheory.EtC.KumPic.DvGlue.glue
  | (intros; apply GlobalTheory.EtC.KumPic.DvGlue.glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerLiftedCocycleImageEqPicardClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerLiftedCocycleImageEqPicardClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.KumPic.PostVal

theorem ev_comp_ofHom {E : Spc} {I J : Cx ℤ} {n : ℤ} (α : Cochain ((chains ℤ).obj E) I n) (m : I ⟶ J)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  unfold ev
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

theorem sglι_resAug (C : Shv ℤ) : sglι C ≫ (resAug C).f 0 = resι ℤ C := rfl

theorem resι_resMap {C G : Shv ℤ} (φ : C ⟶ G) : resι ℤ C ≫ (resMap ℤ φ).f 0 = φ ≫ resι ℤ G := by
  unfold resι resMap res
  rw [InjectiveResolution.ι'_f_zero, InjectiveResolution.ι'_f_zero,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) (by simp)]
  simp [InjectiveResolution.cochainComplexXIso]

theorem post_eq_picClass (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1))
    (a : Cocycle ((chains ℤ).obj E) (sgl C) 1)
    (ha : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧
      ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c) :
    HK.post ℤ _ qb 1 (CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))) = picClass L := by
  let β := zcomp (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))
    (Cocycle.ofHom (resMap ℤ qb)) (add_zero 1)
  change CohomologyClass.mk β = picClass L
  have hβ₀ (U : Scheme.{0}) (x : Sx E 0 U) : ev β.1 0 1 (by simp) U x = 0 := by
    change ev ((a.1.comp (Cochain.ofHom (resAug C)) (add_zero 1)).comp
      (Cochain.ofHom (resMap ℤ qb)) (add_zero 1))
      0 1 _ U x = 0
    rw [ev_comp_ofHom, ev_comp_ofHom,
      GlobalTheory.EtC.PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)) (ev a.1 0 1 _ U x),
      GlobalTheory.EtC.PicSpec.sec_map_zero, GlobalTheory.EtC.PicSpec.sec_map_zero]
  have hβ₁ (U : Scheme.{0}) (x : Sx E 1 U) :
      ev β.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
    obtain ⟨c, hc, hv⟩ := ha U x
    change ev ((a.1.comp (Cochain.ofHom (resAug C)) (add_zero 1)).comp
      (Cochain.ofHom (resMap ℤ qb)) (add_zero 1))
      1 0 _ U x = _
    rw [ev_comp_ofHom, ev_comp_ofHom, hv, GlobalTheory.EtC.PicSpec.sec_map_comp, GlobalTheory.EtC.PicSpec.sec_map_comp, ← hc,
      GlobalTheory.EtC.PicSpec.sec_map_comp, ← Category.assoc, sglι_resAug, resι_resMap]
  let P (c : H ℤ E Gm 1) : Prop :=
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = c ∧
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U),
        ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x))
  have hspec : P (picClass L) := by
    change P (pick P)
    exact pick_spec ⟨_, β, rfl, hβ₀, hβ₁⟩
  obtain ⟨γ, hγ, hγ₀, hγ₁⟩ := hspec
  have hEq : β = γ := by
    refine Cocycle.ext (CupSpec.ev_ext β.1 γ.1 fun p s h U x => ?_)
    match p with
    | 0 =>
      obtain rfl : s = 1 := by omega
      exact (hβ₀ U x).trans (hγ₀ U x).symm
    | 1 =>
      obtain rfl : s = 0 := by omega
      exact (hβ₁ U x).trans (hγ₁ U x).symm
    | p + 2 =>
      have hZ := GlobalTheory.EtC.PicSpec.res_isZero Gm s (by omega)
      exact (GlobalTheory.EtC.PicSpec.sec_eq_zero hZ _).trans
        (GlobalTheory.EtC.PicSpec.sec_eq_zero hZ _).symm
  rw [hEq, hγ]

end GlobalTheory.EtC.KumPic.PostVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerLiftedCocycleImageEqPicardClassStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerLiftedCocycle_image_eq_picardClass : ∀ (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)) (a : Cocycle ((chains ℤ).obj E) (sgl C) 1), (∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c) → HK.post ℤ _ qb 1 (CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))) = picClass L := by
  first | (exact @GlobalTheory.EtC.KumPic.PostVal.post_eq_picClass) | (exact GlobalTheory.EtC.KumPic.PostVal.post_eq_picClass) | (intros; apply GlobalTheory.EtC.KumPic.PostVal.post_eq_picClass  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleLiftingLineBundleTransitionUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleLiftingLineBundleTransitionUnits
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.KumPic

def liftSec {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 1 U) : Sec C U :=
  Function.surjInv (hb U (hE U ⟨x.face 0⟩)).2 (unitSec (lineUnit L x))

theorem liftSec_spec {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 1 U) : Sec.map qb (liftSec qb L hE hb U x) = unitSec (lineUnit L x) :=
  Function.surjInv_eq _ _

theorem liftSec_res {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    Sec.res g (liftSec qb L hE hb U x) = liftSec qb L hE hb V (x.res g) := by
  apply (hb V (hE V ⟨(x.res g).face 0⟩)).1
  rw [← CupSpec.map_res, liftSec_spec, liftSec_spec, PicSpec.unitSec_res, PicSpec.lineUnit_res]

theorem liftSec_face {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 2 U) :
    liftSec qb L hE hb U (x.face 1) = liftSec qb L hE hb U (x.face 0) + liftSec qb L hE hb U (x.face 2) := by
  apply (hb U (hE U ⟨(x.face 0).face 0⟩)).1
  rw [PicSpec.sec_map_add, liftSec_spec, liftSec_spec, liftSec_spec, PicSpec.lineUnit_face, PicSpec.unitSec_mul]

def liftFam {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((sgl C).X s) U
  | 1, s, h, U, x => Sec.map ((sgl C).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (Sec.map (sglι C) (liftSec qb L hE hb U x))
  | _, _, _, _, _ => 0

theorem liftFam_nat {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (liftFam qb L hE hb p s h U x) = liftFam qb L hE hb p s h V (x.res g) := by
  match p with
  | 0 => exact map_zero _
  | 1 =>
    simp only [liftFam]
    rw [CupSpec.map_res, CupSpec.map_res, liftSec_res]
  | p + 2 => exact map_zero _

end GlobalTheory.EtC.KumPic

namespace GlobalTheory.EtC.KumPic

theorem liftFam_one {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E 1 U) :
    liftFam qb L hE hb 1 0 h U x = Sec.map (sglι C) (liftSec qb L hE hb U x) := by
  simp [liftFam, Sec.map]

theorem liftFam_cocycle {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (α : Cochain ((chains ℤ).obj E) (sgl C) 1)
    (hα : ∀ p s h U x, ev α p s h U x = liftFam qb L hE hb p s h U x) : δ 1 2 α = 0 := by
  apply CupSpec.ev_ext
  intro p t ht U x
  rw [CupSpec.ev_zero]
  by_cases h0 : t = 0
  · subst h0
    obtain rfl : p = 2 := by omega
    rw [CupSpec.ev_δ_succ (by norm_num) α U 1 (-1) 0 (by simp) ht x]
    simp only [hα]
    rw [show liftFam qb L hE hb 2 (-1) (by simp) U x = 0 from rfl, PicSpec.sec_map_zero, zero_add, Fin.sum_univ_three]
    simp only [liftFam_one]
    rw [liftSec_face, PicSpec.sec_map_add]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    simp
  · exact PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ h0) _

theorem lift_cocycle : ∀ (q : ℕ) (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) → ∃ a : Cocycle ((chains ℤ).obj E) (sgl C) 1, ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c := by
  intro q C qb E L hE hb
  obtain ⟨α, hα⟩ := CupSpec.ev_exists (liftFam qb L hE hb) (liftFam_nat qb L hE hb)
  refine ⟨Cocycle.mk α 2 (by norm_num) (liftFam_cocycle qb L hE hb α hα), fun U x => ⟨liftSec qb L hE hb U x,
    liftSec_spec qb L hE hb U x, ?_⟩⟩
  refine (hα 1 0 _ U x).trans ?_
  exact liftFam_one qb L hE hb _ U x

end GlobalTheory.EtC.KumPic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleLiftingLineBundleTransitionUnitsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_lifting_lineBundle_transition_units : ∀ (q : ℕ) (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) → ∃ a : Cocycle ((chains ℤ).obj E) (sgl C) 1, ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c := by
  intro q C qb E L hE hb
  obtain ⟨α, hα⟩ := CupSpec.ev_exists (liftFam qb L hE hb) (liftFam_nat qb L hE hb)
  have hδα : δ 1 2 α = 0 := by
    apply CupSpec.ev_ext
    intro p t ht U x
    rw [CupSpec.ev_zero]
    by_cases h0 : t = 0
    · subst h0
      obtain rfl : p = 2 := by omega
      rw [CupSpec.ev_δ_succ (by norm_num) α U 1 (-1) 0 (by simp) ht x]
      simp only [hα]
      rw [show liftFam qb L hE hb 2 (-1) (by simp) U x = 0 from rfl,
        PicSpec.sec_map_zero, zero_add, Fin.sum_univ_three]
      simp only [liftFam_one]
      rw [liftSec_face, PicSpec.sec_map_add]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
      simp
    · exact PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ h0) _
  refine ⟨Cocycle.mk α 2 (by norm_num) hδα, fun U x =>
    ⟨liftSec qb L hE hb U x, liftSec_spec qb L hE hb U x, ?_⟩⟩
  exact (hα 1 0 _ U x).trans (liftFam_one qb L hE hb _ U x)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleOfMapToDegreeOneTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleOfMapToDegreeOneTerm
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_cocycle_of_map_to_X_one :
    ∀ (C : Shv ℤ) (I : Cx ℤ) (ψ : C ⟶ I.X 1), ψ ≫ I.d 1 2 = 0 →
      ∃ w : Cocycle (sgl C) I 1, sglι C ≫ w.1.v 0 1 (zero_add 1) = ψ := by
  intro C I ψ hψ
  refine ⟨Cocycle.fromSingleMk ψ (zero_add 1) 2 (by norm_num) hψ, ?_⟩
  rw [Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v]
  exact (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 C).inv_hom_id_assoc ψ

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleOfMapToDegreeOneTermStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_of_map_to_degreeOne_term : ∀ (C : Shv ℤ) (I : Cx ℤ) (ψ : C ⟶ I.X 1), ψ ≫ I.d 1 2 = 0 → ∃ w : Cocycle (sgl C) I 1, sglι C ≫ w.1.v 0 1 (zero_add 1) = ψ := by
  first | (exact @GlobalTheory.EtC.exists_cocycle_of_map_to_X_one) | (exact GlobalTheory.EtC.exists_cocycle_of_map_to_X_one) | (intros; apply GlobalTheory.EtC.exists_cocycle_of_map_to_X_one  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerBoundaryLineBundleFirstChernClass
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.KumPic

theorem kummer_boundary_picClass : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0), Mono κ →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U))) →
  ∀ (z : Cocycle (res ℤ (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1) (s : ℤˣ),
  (∀ (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (ψ : cokernel κ ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 1),
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) → cokernel.π κ ≫ ψ = φ ≫ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).d 0 1 →
      ∀ w : Cocycle (sgl (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1, sglι (cokernel κ) ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug (cokernel κ))) z (zero_add 1)) = s • CohomologyClass.mk w) →
  ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ y : H ℤ E (cokernel κ) 1,
    HK.post ℤ _ (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) 1 y = picClass L →
    HK.ext ℤ _ z 1 (1 + 1) rfl y = s • restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  intro q _ κ h0 _ h2 _ _ h5 z s hz E L hE y hy
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_cocycle_lifting_lineBundle_transition_units q (cokernel κ) _ E L hE h5
  have hy' : y = CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 1)) :=
    (GlobalTheory.T.etaleCohomology_bijective_of_support_bijective ℤ E _ (fun U hU => h5 U (hE U hU)) 1).1 (hy.trans (GlobalTheory.T.kummerLiftedCocycle_image_eq_picardClass _ _ E L a ha).symm)
  haveI : Injective ((res ℤ (twZ q)).X 0) :=
    inferInstanceAs (Injective ((injectiveResolution (twZ q)).cochainComplex.X 0))
  let φ : Gm ⟶ (res ℤ (twZ q)).X 0 := Injective.factorThru (resι ℤ (twZ q)) κ
  have hφ : κ ≫ φ = resι ℤ (twZ q) := Injective.comp_factorThru _ _
  have hd : κ ≫ (φ ≫ (res ℤ (twZ q)).d 0 1) = 0 := by
    rw [← Category.assoc, hφ, PicSpec.resι_d]
  let ψ : cokernel κ ⟶ (res ℤ (twZ q)).X 1 := cokernel.desc κ (φ ≫ (res ℤ (twZ q)).d 0 1) hd
  have hψ : cokernel.π κ ≫ ψ = φ ≫ (res ℤ (twZ q)).d 0 1 := cokernel.π_desc _ _ _
  have hψd : ψ ≫ (res ℤ (twZ q)).d 1 2 = 0 := by
    rw [← cancel_epi (cokernel.π κ), ← Category.assoc, hψ, Category.assoc, HomologicalComplex.d_comp_d,
      comp_zero, comp_zero]
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_cocycle_of_map_to_degreeOne_term (cokernel κ) (res ℤ (twZ q)) ψ hψd
  have hzw := hz φ ψ hφ hψ w hw
  have hext : HK.ext ℤ _ z 1 (1 + 1) rfl y = s • CohomologyClass.mk (zcomp a w rfl) := by
    rw [hy']
    change CohomologyClass.mk (zcomp (zcomp a (Cocycle.ofHom (resAug _)) (add_zero 1)) z rfl) = _
    have hc : zcomp (zcomp a (Cocycle.ofHom (resAug (cokernel κ))) (add_zero 1)) z rfl =
        zcomp a (zcomp (Cocycle.ofHom (resAug _)) z (zero_add 1)) rfl :=
      Cocycle.ext (Cochain.comp_assoc _ _ _ (add_zero 1) (zero_add 1) (by omega))
    rw [hc, ← cpre_mk, hzw]
    rw [Units.smul_def, Units.smul_def, map_zsmul]
    rfl
  rw [hext]
  congr 1
  refine GlobalTheory.T.kummerCocycle_sub_chernClass_coboundary q E L hE φ (GlobalTheory.T.kummerSplittingDefect_glue_qthRoots q φ (GlobalTheory.T.kummerSplittingDefect_eq_of_pow_eq q κ h2 φ hφ)) (cokernel κ) a w (fun U x v hv => ?_)
  obtain ⟨c, hc, hac⟩ := ha U x
  have hU : IsUnit (q : Γ(U, ⊤)) := hE U ⟨x.face 0⟩
  have hpow : ∀ n : ℕ, unitSec (v ^ n) = (n : ℤ) • unitSec v := by
    intro n
    induction n with
    | zero =>
      have := PicSpec.unitSec_mul (1 : (Γ(U, ⊤))ˣ) 1
      rw [mul_one] at this
      simpa using this
    | succ n ih => rw [pow_succ, PicSpec.unitSec_mul, ih]; push_cast; rw [add_smul, one_smul]
  have hcv : c = Sec.map (cokernel.π κ) (unitSec v) := by
    refine (h5 U hU).1 (hc.trans ?_)
    rw [PicSpec.sec_map_comp, cokernel.π_desc, ← hv, hpow]
    exact (map_zsmul (CupSpec.mapHom Gm Gm (unitSec v)) (q : ℤ) (𝟙 Gm)).symm
  rw [hac, PicSpec.sec_map_comp, hw, hcv, PicSpec.sec_map_comp, hψ]
  rfl

end GlobalTheory.EtC.KumPic

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerBoundaryLineBundleFirstChernClassStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerBoundary_lineBundle_firstChernClass : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm) (h0 : κ ≫ ((q : ℤ) • 𝟙 Gm) = 0), Mono κ →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
  (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) (U := U))) →
  ∀ (z : Cocycle (res ℤ (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1) (s : ℤˣ),
  (∀ (φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0) (ψ : cokernel κ ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 1),
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) → cokernel.π κ ≫ ψ = φ ≫ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).d 0 1 →
      ∀ w : Cocycle (sgl (cokernel κ)) (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))) 1, sglι (cokernel κ) ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug (cokernel κ))) z (zero_add 1)) = s • CohomologyClass.mk w) →
  ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ y : H ℤ E (cokernel κ) 1,
    HK.post ℤ _ (cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0) 1 y = picClass L →
    HK.ext ℤ _ z 1 (1 + 1) rfl y = s • restrH (Int.castRingHom (ZMod q)) E (tw q 1) (1 + 1) (c1 q L) := by
  first
  | exact @GlobalTheory.EtC.KumPic.kummer_boundary_picClass
  | exact GlobalTheory.EtC.KumPic.kummer_boundary_picClass
  | (intros; apply GlobalTheory.EtC.KumPic.kummer_boundary_picClass <;> assumption)
end
