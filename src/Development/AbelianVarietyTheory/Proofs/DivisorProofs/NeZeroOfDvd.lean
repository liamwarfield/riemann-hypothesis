module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplitting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

def defect (Q q : ℕ) (U : Scheme.{0}) (v : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  (redMap Q q 1).app U 0 (kumT Q U v) - kumT q U (v ^ (Q / q))

def defectSec (Q q : ℕ) (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  pick fun s => ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u →
    Sec.res g s = defect Q q V v

def corrFam (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X s) U
  | 1, s, h, U, x => Sec.map ((res _ (tw q 1)).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (defectSec Q q U (lineUnit L x))
  | _, _, _, _, _ => 0

theorem corrFam_zero (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (s : ℤ) (h : -((0 : ℕ) : ℤ) + 1 = s)
    (U : Scheme.{0}) (x : Sx E 0 U) : corrFam Q q L 0 s h U x = 0 := rfl

theorem corrFam_add_two (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -((p + 2 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E (p + 2) U) : corrFam Q q L (p + 2) s h U x = 0 := rfl

theorem corrFam_one (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0})
    (x : Sx E 1 U) : corrFam Q q L 1 0 h U x = defectSec Q q U (lineUnit L x) := by
  simp [corrFam, Sec.map]

end GlobalTheory.EtC.RedChern
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestriction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestriction
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem res_defect : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ),
    IsUnit (Q : Γ(U, ⊤)) → Sec.res g (GlobalTheory.EtC.RedChern.defect Q q U v) =
      GlobalTheory.EtC.RedChern.defect Q q V (Units.map g.appTop.hom.toMonoidHom v) := by
  intro Q q _ hqQ V U g v hQ
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (zero_dvd_iff.mp hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hqU : IsUnit (q : Γ(U, ⊤)) := by
    obtain ⟨k, hk⟩ := hqQ
    rw [hk, Nat.cast_mul] at hQ
    exact isUnit_of_mul_isUnit_left hQ
  unfold defect
  rw [Sec.res, map_sub]
  change Sec.res g _ - Sec.res g _ = _
  rw [(redMap Q q 1).nat g 0, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting Q).1 V U g v hQ, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g _ hqU, map_pow]

end GlobalTheory.EtC.RedChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_restriction : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → Sec.res g (GlobalTheory.EtC.RedChern.defect Q q U v) = GlobalTheory.EtC.RedChern.defect Q q V (Units.map g.appTop.hom.toMonoidHom v) := by
  first
  | exact @GlobalTheory.EtC.RedChern.res_defect
  | exact GlobalTheory.EtC.RedChern.res_defect
  | (intros; apply GlobalTheory.EtC.RedChern.res_defect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistAltI
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP0⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hP0 V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : Loc U P') :
    Loc U fun V g => P V g ∧ P' V g := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hP'⟩ := h'
  exact ⟨S ⊓ S', Scheme.etaleTopology.intersection_covering hS hS', fun V g hg => ⟨hP V g hg.1, hP' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  classical
  obtain ⟨S, hS, hP0⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => hP V g (hP0 V g hg)
  refine ⟨Sieve.bind S.arrows fun V g hg => T V g hg, Scheme.etaleTopology.bind_covering hS fun V g hg => hT V g hg, ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hT' V g hg W k hk

end GlobalTheory.EtC.RedChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrict
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectEqOfPowEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectEqOfPowEq
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defect_mul_prim (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (v w : (Γ(U, ⊤))ˣ) (h : (w : Γ(U, ⊤)) = ζ.1 * v) : defect Q q U w = defect Q q U v := by
  have hq0 : q ≠ 0 := fun h0 => NeZero.ne Q (Nat.eq_zero_of_zero_dvd (h0 ▸ hqQ))
  haveI : NeZero q := ⟨hq0⟩
  obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
  have h1 : kumT Q U w = kumT Q U v + resGen 1 ζ := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting Q).2 U ζ v w h
  have h2 : (redMap Q q 1).app U 0 (resGen 1 ζ) = resGen 1 ξ := GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ 1 U ζ ξ hξ
  have h3 : ((w ^ (Q / q) : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ξ.1 * ((v ^ (Q / q) : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) := by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h, hξ, mul_pow]
  have h4 : kumT q U (w ^ (Q / q)) = kumT q U (v ^ (Q / q)) + resGen 1 ξ :=
    (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 U ξ _ _ h3
  unfold defect
  rw [h1, h4, map_add (f := _), h2]
  abel

theorem defect_mul_prim_pow (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (v : (Γ(U, ⊤))ˣ) (a : ℕ) : ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v →
      defect Q q U w = defect Q q U v := by
  have hζ : IsUnit ζ.1 := IsUnit.of_pow_eq_one ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).1 ζ) (NeZero.ne Q)
  induction a with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    exact congrArg (defect Q q U) (Units.ext hw)
  | succ a ih =>
    intro w hw
    have e : ((hζ.unit ^ a * v : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ζ.1 ^ a * v := by simp
    rw [defect_mul_prim Q q hqQ U ζ (hζ.unit ^ a * v) w (by rw [hw, e, pow_succ]; ring)]
    exact ih _ e

end GlobalTheory.EtC.RedChern

namespace GlobalTheory.EtC.RedChern

theorem defect_eq_of_pow_eq (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ)
    (hQ : IsUnit (Q : Γ(U, ⊤))) (hvw : v ^ Q = w ^ Q) : defect Q q U v = defect Q q U w := by
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue (ZMod q) ((res _ (tw q 1)).X 0) U).1 _ _ ?_
  refine loc_bind ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).1 hQ) fun V g hV => ?_
  obtain ⟨ζ⟩ := hV
  set v' : (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom v
  set w' : (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom w
  have hx : (((w' * v'⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤))) ^ Q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ← map_pow, ← map_pow, ← hvw, mul_inv_cancel, Units.val_one]
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.1 ζ _ hx) fun W k ⟨a, ha⟩ => ?_
  rw [GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W U (k ≫ g) v hQ, GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W U (k ≫ g) w hQ]
  symm
  refine defect_mul_prim_pow Q q hqQ W (ζ.map k.appTop.hom) _ a _ ?_
  have e1 : ∀ u : (Γ(U, ⊤))ˣ, ((Units.map (k ≫ g).appTop.hom.toMonoidHom u : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      k.appTop.hom ((Units.map g.appTop.hom.toMonoidHom u : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) := fun u => rfl
  rw [e1, e1]
  change k.appTop.hom (w' : Γ(V, ⊤)) = (k.appTop.hom ζ.1) ^ a * k.appTop.hom (v' : Γ(V, ⊤))
  rw [← ha, ← map_mul, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end GlobalTheory.EtC.RedChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectEqOfPowEqStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → v ^ Q = w ^ Q → GlobalTheory.EtC.RedChern.defect Q q U v = GlobalTheory.EtC.RedChern.defect Q q U w := by
  first
  | exact @GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq
  | exact GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq
  | (intros; apply GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrict
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

private theorem unitsMap_comp_appTop {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) := by
  ext
  simp [Scheme.Hom.comp_appTop]
  rfl

private theorem isUnit_natCast_appTop {V U : Scheme.{0}} (g : V ⟶ U) (Q : ℕ) (h : IsUnit (Q : Γ(U, ⊤))) :
    IsUnit (Q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem res_defectSec : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) →
    ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u →
      Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defect Q q V v := by
  intro Q q _ hqQ U u hQ

  let S : Sieve U :=
    { arrows := fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ Q = Units.map g.appTop.hom.toMonoidHom u
      downward_closed := by
        rintro V W g ⟨v, hv⟩ k
        refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
        rw [← map_pow, hv, unitsMap_comp_appTop] }
  have hS : S ∈ Scheme.etaleTopology U := by
    obtain ⟨S₀, hS₀, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u
    exact GrothendieckTopology.superset_covering _ (fun V g hg => hP V g hg) hS₀
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res _ (tw q 1)).X 0) V :=
    fun V g hg => defect Q q V hg.choose
  have hcompat : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k) := by
    intro V W g k hg
    have hQV : IsUnit (Q : Γ(V, ⊤)) := isUnit_natCast_appTop g Q hQ
    have hQW : IsUnit (Q : Γ(W, ⊤)) := isUnit_natCast_appTop k Q hQV
    change Sec.res k (defect Q q V hg.choose) = defect Q q W (S.downward_closed hg k).choose
    rw [GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W V k hg.choose hQV]
    refine GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq Q q hqQ W _ _ hQW ?_
    rw [(S.downward_closed hg k).choose_spec, ← map_pow, hg.choose_spec, unitsMap_comp_appTop]
  obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).2 S hS s hcompat
  have hex : ∃ a : Sec ((res _ (tw q 1)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ),
      v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = defect Q q V v := by
    refine ⟨a, fun V g v hv => ?_⟩
    have hg : S.arrows g := ⟨v, hv⟩
    rw [ha V g hg]
    exact GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq Q q hqQ V _ _ (isUnit_natCast_appTop g Q hQ) (hg.choose_spec.trans hv.symm)
  intro V g v hv
  exact pick_spec hex V g v hv

end GlobalTheory.EtC.RedChern
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_restrict : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defect Q q V v := by
  first
  | exact @GlobalTheory.EtC.RedChern.res_defectSec
  | exact GlobalTheory.EtC.RedChern.res_defectSec
  | (intros; apply GlobalTheory.EtC.RedChern.res_defectSec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegOneSubEqDifferential
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegOneSubEqDifferential
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

private theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem sec_res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x - y) = Sec.res g x - Sec.res g y := map_sub _ x y

private theorem sec_map_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub _ x y

theorem red_chern_deg_one : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 1) U) (b : Sec ((res _ (tw q 1)).X 1) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = Sec.map ((res _ (tw Q 1)).d 0 1) (kumT Q V v)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (w : (Γ(V, ⊤))ˣ), w ^ q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g b = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w)) → (redMap Q q 1).app U 1 a - b = Sec.map ((res _ (tw q 1)).d 0 1) (GlobalTheory.EtC.RedChern.defectSec Q q U u) := by
  intro Q q _ hqQ U u hQ a b ha hb
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1 _ _ ?_
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u) ?_
  rintro V g ⟨v, hv⟩
  have hw : (v ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hv]
  rw [sec_res_sub, (redMap Q q 1).nat, ha V g v hv, hb V g _ hw, ← (redMap Q q 1).comm, sec_res_map,
    GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ V g v hv, defect, sec_map_sub]

end GlobalTheory.EtC.RedChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegOneSubEqDifferentialStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 1) U) (b : Sec ((res _ (tw q 1)).X 1) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = Sec.map ((res _ (tw Q 1)).d 0 1) (kumT Q V v)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (w : (Γ(V, ⊤))ˣ), w ^ q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g b = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w)) → (redMap Q q 1).app U 1 a - b = Sec.map ((res _ (tw q 1)).d 0 1) (GlobalTheory.EtC.RedChern.defectSec Q q U u) := by
  first
  | exact @GlobalTheory.EtC.RedChern.red_chern_deg_one
  | exact GlobalTheory.EtC.RedChern.red_chern_deg_one
  | (intros; apply GlobalTheory.EtC.RedChern.red_chern_deg_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegTwoSubEqDefects
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegTwoSubEqDefects
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  intro Q q _ hqQ U u₁ u₂ hQ a b ha hb
  refine (GlobalTheory.T.etaleSheafSections_ext_and_glue _ ((res _ (tw q 1)).X 0) U).1 _ _ ?_
  have h1 := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u₁
  have h2 := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u₂
  refine GlobalTheory.EtC.RedChern.loc_mono (GlobalTheory.EtC.RedChern.loc_and h1 h2) ?_
  rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  have hvq : (v ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u₁ := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hv]
  have hwq : (w ^ (Q / q)) ^ q = Units.map g.appTop.hom.toMonoidHom u₂ := by
    rw [← pow_mul, Nat.div_mul_cancel hqQ, hw]
  have hvw : (v * w) ^ Q = Units.map g.appTop.hom.toMonoidHom (u₁ * u₂) := by
    rw [mul_pow, hv, hw, map_mul]
  have ea := ha V g v w hv hw
  have eb := hb V g _ _ hvq hwq
  have d1 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u₁ hQ V g v hv
  have d2 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u₂ hQ V g w hw
  have d3 := GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U (u₁ * u₂) hQ V g (v * w) hvw
  have en := (redMap Q q 1).nat g 0 a
  have hsub : ∀ x y : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (x - y) = Sec.res g x - Sec.res g y := fun x y => map_sub _ x y
  have hadd : ∀ x y : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (x + y) = Sec.res g x + Sec.res g y := fun x y => map_add _ x y
  rw [hsub, hadd, hsub, en, ea, eb, d1, d2, d3]
  simp only [GlobalTheory.EtC.RedChern.defect, map_sub, map_add (f := _), mul_pow]
  abel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegTwoSubEqDefectsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  first
  | exact @GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
  | exact GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
  | (intros; apply GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectSectionRes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectSectionRes
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defectSec_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  intro Q q _ hqQ U u hQ V g
  have hQV : IsUnit (Q : Γ(V, ⊤)) := by
    have := hQ.map g.appTop.hom
    simpa using this
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ V).1
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.2 hQV (Units.map g.appTop.hom.toMonoidHom u)) ?_
  rintro W h ⟨v, hv⟩
  have hres : Sec.res h (Sec.res g (defectSec Q q U u)) = Sec.res (h ≫ g) (defectSec Q q U u) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hres, GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ V _ hQV W h v hv]
  refine GlobalTheory.T.kummerReductionChernDefect_restrict Q q hqQ U u hQ W (h ≫ g) v ?_
  rw [hv]
  ext
  simp [Scheme.Hom.comp_appTop] <;> rfl

end GlobalTheory.EtC.RedChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectSectionResStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefectSection_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  first
  | exact @GlobalTheory.EtC.RedChern.defectSec_res
  | exact GlobalTheory.EtC.RedChern.defectSec_res
  | (intros; apply GlobalTheory.EtC.RedChern.defectSec_res <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwist
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

set_option backward.isDefEq.respectTransparency false

theorem delta_two_eq : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 0 1 (by omega) := by
  ext i; fin_cases i <;> rfl

theorem delta_zero_eq : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 1 1 (by omega) := by
  ext i; fin_cases i <;> rfl

theorem face_two {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_two_eq]

theorem face_zero {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [delta_zero_eq]

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

open GlobalTheory.EtC.PicSpec

theorem corrFam_nat (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) {E : Spc} (hE : Inv Q E) (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (corrFam Q q L p s h U x) = corrFam Q q L p s h V (x.res g) := by
  match p with
  | 0 =>
    rw [corrFam_zero, corrFam_zero]
    exact map_zero (((res _ (tw q 1)).X s).obj.map g.op).hom
  | 1 =>
    obtain rfl : s = 0 := by omega
    rw [corrFam_one, corrFam_one, lineUnit_res,
      GlobalTheory.T.kummerReductionChernDefectSection_res Q q hqQ U _ (hE U ⟨x.face 0⟩) V g]
  | p + 2 =>
    rw [corrFam_add_two, corrFam_add_two]
    exact map_zero (((res _ (tw q 1)).X s).obj.map g.op).hom

theorem coefficientReduction_firstChernClass_tateTwist : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1),
    red Q q E 2 1 (c1 Q L) = c1 q L := by
  intro Q q _ hqQ E hE L
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hUnit : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive Q).1 L hE
  obtain ⟨γ', hγ', hγ0', hγ1', hγ2'⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hUnit
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).1 E 2 γ
  have hred : red Q q E 2 1 (c1 Q L) = CohomologyClass.mk β := by
    rw [← hγ]
    exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 1)).2 E 2 γ β hβ
  rw [hred, ← hγ']
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (corrFam Q q L) (corrFam_nat Q q hqQ hE L)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  refine ⟨α, ?_⟩
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1
  intro p t ht U x
  rw [Cocycle.coe_sub, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1, hβ]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).1 x, hα, corrFam_zero, sec_map_zero, hγ0, hγ0', map_zero, sub_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_zero, smul_zero, Finset.sum_const_zero, add_zero, corrFam_one]
    refine (GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential Q q hqQ U (lineUnit L x) (hE U ⟨x.face 0⟩) _ _ (fun V g v hv => ?_) (fun V g w hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 1 1 _ V U g x]
      exact hγ1 V (x.res g) v (by simpa only [lineUnit_res] using hv)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 1 1 _ V U g x]
      exact hγ1' V (x.res g) w (by simpa only [lineUnit_res] using hw)
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) α U).2 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, corrFam_one]
    rw [show corrFam Q q L (1 + 1) (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three,
      lineUnit_face, face_zero, face_two]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]
    rw [Int.negOnePow_even 2 (by decide), one_smul, mul_comm (lineUnit L _) (lineUnit L _), ← sub_eq_add_neg]
    norm_num
    refine (GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects Q q hqQ U _ _ (hE U ⟨(x.face 0).face 0⟩) _ _ (fun V g v w hv hw => ?_) (fun V g v w hv hw => ?_)).symm
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod Q)).2.1 γ.1 2 0 _ V U g x]
      exact hγ2 V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
    · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ'.1 2 0 _ V U g x]
      exact hγ2' V (x.res g) v w (by rw [sub_res, lineUnit_res]; exact hv) (by rw [sub_res, lineUnit_res]; exact hw)
  | p + 3 =>
    have hZ := res_isZero (tw q 1) t (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.RedChern
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.red_c1_eq_c1_of_dvd : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → ∀ L : E ⟶ ofCat (glCat 1), red Q q E 2 1 (c1 Q L) = c1 q L := by
  first
  | exact @GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | exact GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist
  | (intros; apply GlobalTheory.EtC.RedChern.coefficientReduction_firstChernClass_tateTwist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionUnitClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionUnitClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUnit

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have := congrArg (fun f => f.hom y) (φ.hom.naturality g.op)
  exact this.symm

theorem res_resGen {q : ℕ} [NeZero q] (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  unfold resGen
  rw [res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ]

theorem val_one_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (y : M) :
    (1 : ZMod q).val • y = y := by
  by_cases hq : q = 1
  · subst hq
    have : Subsingleton M := Module.subsingleton (ULift.{1} (ZMod 1)) M
    exact Subsingleton.elim _ _
  · haveI : Fact (1 < q) := ⟨by have := NeZero.ne q; omega⟩
    rw [ZMod.val_one, one_smul]

theorem resGen_zero_eq {q : ℕ} [NeZero q] {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) : resGen 0 ζ = resGen 0 ξ := by
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.1 ζ ξ
  refine ⟨S, hS, fun W h hh => ?_⟩
  obtain ⟨a, ha⟩ := hP W h hh
  rw [res_resGen, res_resGen]
  have := (GlobalTheory.T.tateTwist_sections_locally_generated q 0).2.2.2.2.1 W (ζ.map h.appTop.hom) (ξ.map h.appTop.hom) a ha
  unfold resGen
  rw [this, zpow_zero, Units.val_one, val_one_smul]

end GlobalTheory.EtC.RedUnit

theorem GlobalTheory.EtC.red_one : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  intro Q q _ hqQ E hE
  haveI : NeZero q := ⟨fun h => by subst h; exact NeZero.ne Q (Nat.eq_zero_of_zero_dvd hqQ)⟩
  have hEq : Inv q E := fun U hU => by
    obtain ⟨k, hk⟩ := hqQ
    have := hE U hU
    rw [hk, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨α, hα1, hα2⟩ := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec Q).1 E hE
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).1 E 0 α
  have hred : red Q q E 0 0 (one Q E) = CohomologyClass.mk β := by
    rw [← hα1]; exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap _ _ (redMap Q q 0)).2 E 0 α β hβ
  rw [hred]
  refine (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.1 E hEq β fun U x ξ => ?_
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).1
  obtain ⟨S, hS, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).1 (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  obtain ⟨ξ', hξ'⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(V, ⊤)).2.2.2.2.2 q hqQ ζ
  rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 β.1 0 0 _ V U g x, hβ 0 0 _ V (x.res g), hα2 V (x.res g) ζ,
    GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ 0 V ζ ξ' hξ', RedUnit.res_resGen]
  exact RedUnit.resGen_zero_eq _ _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionUnitClassStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCoefficientReduction_unitClass : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  first
  | exact @GlobalTheory.EtC.red_one
  | exact GlobalTheory.EtC.red_one
  | (intros; apply GlobalTheory.EtC.red_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionCohomologyMapUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsTateTwistResolutionHomExtAugmentati
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsTateTwistResolutionHomExtAugmentati
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

theorem secMap_res' {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.hom.naturality g.op)) x).symm

theorem secMap_nsmul' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map f (c • x) = c • Sec.map f x :=
  map_nsmul (f.hom.app (op U)).hom c x

theorem secMap_zero' {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} :
    Sec.map f (0 : Sec F U) = 0 :=
  map_zero (f.hom.app (op U)).hom

theorem extSh_hom_ext (φ : R →+* S) {F : Shv R} {M : Shv S} (a b : (extSh φ).obj F ⟶ M)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map a (extSh.sec φ F U y) = Sec.map b (extSh.sec φ F U y)) : a = b := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))
    a.hom b.hom M.property ?_
  ext U : 2
  apply ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext y
  exact h (unop U) y

end

theorem extAug_comp_ext : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ) (K : Cx (ZMod q))
    (u u' : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K),
    (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
      Sec.map (u.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ)) =
        Sec.map (u'.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ))) →
    extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u = extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u' := by
  intro Q q _ hq i K u u' h
  have e : ∀ (v : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K) (V : Scheme.{0}) (z : Sec (tw Q i) V),
      Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ v.f 0)
          (extSh.sec (ZMod.castHom hq (ZMod q)) (tw Q i) V z) =
        Sec.map (v.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app V 0 (Sec.map (resι _ (tw Q i)) z)) := by
    intro v V z
    change Sec.map (v.f 0) (Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i))) _) = _
    rw [extSh.sec_map]
    rfl
  have key : (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ u.f 0 =
      (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ u'.f 0 := by
    apply extSh_hom_ext
    intro U y
    apply (GlobalTheory.T.etaleSheafSections_ext_and_glue _ (K.X 0) U).1
    obtain ⟨S, hS, hy⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated Q i).1 U y
    refine ⟨S, hS, fun V g hg => ?_⟩
    dsimp only
    rw [secMap_res', secMap_res', extSh.sec_res, e, e]
    rcases hy V g hg with h0 | ⟨ζ, c, hc⟩
    · rw [h0, secMap_zero', map_zero, secMap_zero', secMap_zero']
    · rw [hc, secMap_nsmul', map_nsmul, secMap_nsmul', secMap_nsmul']
      exact congrArg (c • ·) (h V ζ)
  have hv : ∀ v : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K, (extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ v).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
        (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) ≫ v.f 0 := by
    intro v
    have hs := HomologicalComplex.singleMapHomologicalComplex_inv_app_self (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0 (tw Q i)
    change (((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0)) ≫
        v.f 0 = _
    have hs' : ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
        (ComplexShape.up ℤ) 0).inv.app (tw Q i)).f 0 ≫ (extSh (ZMod.castHom hq (ZMod q))).map ((resAug (tw Q i)).f 0) =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((extSh (ZMod.castHom hq (ZMod q))).obj (tw Q i))).hom ≫
          (extSh (ZMod.castHom hq (ZMod q))).map (resι _ (tw Q i)) := by
      rw [hs]
      exact (Category.assoc _ _ _).trans (congrArg _ (Functor.map_comp _ _ _).symm)
    exact (congrArg (· ≫ v.f 0) hs').trans (Category.assoc _ _ _)
  apply HomologicalComplex.from_single_hom_ext
  rw [hv, hv, key]

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsTateTwistResolutionHomExtAugmentatiStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendScalars_tateTwistResolution_hom_ext_augmentation : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ) (K : Cx (ZMod q)) (u u' : extCx (ZMod.castHom hq (ZMod q)) (res _ (tw Q i)) ⟶ K), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map (u.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ)) = Sec.map (u'.f 0) ((extπ (ZMod.castHom hq (ZMod q)) _).app U 0 (resGen i ζ))) → extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u = extAug (ZMod.castHom hq (ZMod q)) (tw Q i) ≫ u' := by
  first | (exact @GlobalTheory.EtC.extAug_comp_ext) | (exact GlobalTheory.EtC.extAug_comp_ext) | (intros; apply GlobalTheory.EtC.extAug_comp_ext  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionCohomologyMapUnique
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUniq

theorem op_eq : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (ρ ρ' : SemiMap (res _ (tw Q i)) (res _ (tw q i))),
    (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), ρ.app U 0 (resGen i ζ) = ρ'.app U 0 (resGen i ζ)) →
    ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i), ρ.op.app E n x = ρ'.op.app E n x := by
  intro Q q _ hq i ρ ρ' h E n x
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_factor_through_extendScalars_zmod Q q hq _ _ ρ
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_factor_through_extendScalars_zmod Q q hq _ _ ρ'
  have e1 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective _ _ (extπ (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) ρ u hu).1 E n x
  have e2 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective _ _ (extπ (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) ρ' u' hu').1 E n x
  have hε := GlobalTheory.T.extendScalars_tateTwistResolution_hom_ext_augmentation Q q hq i _ u u' (fun U ζ => by rw [← hu, ← hu', h])
  haveI := GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation Q q hq i
  haveI : (res (ZMod q) (tw q i)).IsKInjective :=
    inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsKInjective)
  haveI : (res (ZMod q) (tw q i)).IsStrictlyGE 0 :=
    inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsStrictlyGE 0)
  obtain ⟨H⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) _ _ (res _ (tw q i)) (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).2 u u' hε
  have e3 := ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)).2.2.2.2 u u' ⟨H⟩ ((chains (ZMod q)).obj E) n).2
  rw [e1, e2, e3]

end GlobalTheory.EtC.RedUniq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionCohomologyMapUniqueStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistReduction_cohomology_map_unique : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (ρ ρ' : SemiMap (res _ (tw Q i)) (res _ (tw q i))), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), ρ.app U 0 (resGen i ζ) = ρ'.app U 0 (resGen i ζ)) → ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i), ρ.op.app E n x = ρ'.op.app E n x := by
  first
  | exact @GlobalTheory.EtC.RedUniq.op_eq
  | exact GlobalTheory.EtC.RedUniq.op_eq
  | (intros; apply GlobalTheory.EtC.RedUniq.op_eq <;> assumption)
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.RedCoef

variable {S R T : Type} [CommRing S] [CommRing R] [CommRing T]

def semiId (I : Cx S) : SemiMap I I where
  app _ _ := AddMonoidHom.id _
  nat _ _ _ := rfl
  comm _ _ _ _ := rfl

def semiComp {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (σ.app _ s (ρ.app _ s a)) = σ.app _ s (ρ.app _ s (Sec.res g a))
    rw [σ.nat, ρ.nat]
  comm U s t a := by
    change Sec.map (K.d s t) (σ.app U s (ρ.app U s a)) = σ.app U t (ρ.app U t (Sec.map (I.d s t) a))
    rw [σ.comm, ρ.comm]

theorem semiId_op (I : Cx S) (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (semiId I).op.app E n x = x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S S (semiId I)).2 E n α α (fun _ _ _ _ _ => rfl)

theorem semiComp_op {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (semiComp ρ σ).op.app E n x = σ.op.app E n (ρ.op.app E n x) := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n α
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R T σ).1 E n β
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n α β hβ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R T σ).2 E n β γ hγ]
  exact (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S T (semiComp ρ σ)).2 E n α γ (fun p s h U y => by
    rw [hγ p s h U y, hβ p s h U y]; rfl)

theorem neZero_of_dvd {q Q : ℕ} [NeZero Q] (h : q ∣ Q) : NeZero q :=
  ⟨by rintro rfl; exact NeZero.ne Q (zero_dvd_iff.mp h)⟩

theorem div_mul_div {Q q r : ℕ} [NeZero Q] (hq : q ∣ Q) (hr : r ∣ q) : Q / q * (q / r) = Q / r := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨l, rfl⟩ := hr
  have hQ := NeZero.ne (r * l * k)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hQ
  have hl0 : l ≠ 0 := by rintro rfl; simp at hQ
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero hr0 hl0)),
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0), mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr0),
    mul_comm]

end GlobalTheory.EtC.RedCoef

namespace GlobalTheory.EtC.RedCoef

theorem a11 : GlobalTheory.EtC.A11 := by
  intro Q q _ hqQ E
  haveI : NeZero q := neZero_of_dvd hqQ
  refine ⟨fun a b => GlobalTheory.T.tateTwistCoefficientReduction_cup Q q hqQ E a b, fun hE => ⟨GlobalTheory.T.tateTwistCoefficientReduction_unitClass Q q hqQ E hE, fun L => GlobalTheory.T.red_c1_eq_c1_of_dvd Q q hqQ E hE L⟩,
    fun n i a => ?_, fun r hr n i a => ?_⟩
  · have hgen : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
        (redMap Q Q i).app U 0 (resGen i ζ) = (semiId (res _ (tw Q i))).app U 0 (resGen i ζ) := by
      intro U ζ
      refine GlobalTheory.T.tateTwistReductionResolutionMap_generator Q Q dvd_rfl i U ζ ζ ?_
      rw [Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne Q)), pow_one]
    exact (GlobalTheory.T.tateTwistReduction_cohomology_map_unique Q Q dvd_rfl i _ _ hgen E n a).trans (semiId_op _ E n a)
  · haveI : NeZero r := neZero_of_dvd hr
    have hrQ : r ∣ Q := hr.trans hqQ
    have hgen : ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)),
        (semiComp (redMap Q q i) (redMap q r i)).app U 0 (resGen i ζ) = (redMap Q r i).app U 0 (resGen i ζ) := by
      intro U ζ
      obtain ⟨η, hη⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
      obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q Γ(U, ⊤)).2.2.2.2.2 r hr η
      change (redMap q r i).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) = _
      rw [GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ i U ζ η hη, GlobalTheory.T.tateTwistReductionResolutionMap_generator q r hr i U η ξ hξ,
        GlobalTheory.T.tateTwistReductionResolutionMap_generator Q r hrQ i U ζ ξ (by rw [hξ, hη, ← pow_mul, div_mul_div hqQ hr])]
    exact (semiComp_op _ _ E n a).symm.trans (GlobalTheory.T.tateTwistReduction_cohomology_map_unique Q r hrQ i _ _ hgen E n a)

end GlobalTheory.EtC.RedCoef
