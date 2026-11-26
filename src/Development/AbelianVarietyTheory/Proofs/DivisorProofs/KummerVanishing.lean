module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicFaithfullyFlatDescentUnitCocycles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.MuTw
variable (q : ℕ) [NeZero q]

instance muModule (A : Type) [CommRing A] : Module (ZMod q) (Additive (rootsOfUnity q A)) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      exact (mem_rootsOfUnity q _).1 (Additive.toMul x).2))

theorem smul_eq (A : Type) [CommRing A] (c : ZMod q) (x : Additive (rootsOfUnity q A)) : c • x = c.val • x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul]

def muMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    ULift.{1} (Additive (rootsOfUnity q A)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (Additive (rootsOfUnity q B)) where
  toFun x := ⟨Additive.ofMul (restrictRootsOfUnity f q (Additive.toMul x.down))⟩
  map_add' x y := congrArg ULift.up (congrArg Additive.ofMul (map_mul (restrictRootsOfUnity f q) _ _))
  map_smul' c x := by
    apply ULift.ext
    change Additive.ofMul (restrictRootsOfUnity f q (Additive.toMul (c.down • x.down))) =
      c.down • Additive.ofMul (restrictRootsOfUnity f q (Additive.toMul x.down))
    rw [smul_eq, smul_eq, toMul_nsmul, map_pow, ofMul_pow]

theorem muMap_coe {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : ULift.{1} (Additive (rootsOfUnity q A))) :
    (((Additive.toMul (muMap q f x).down : rootsOfUnity q B) : Bˣ) : B) = f (((Additive.toMul x.down : rootsOfUnity q A) : Aˣ) : A) :=
  restrictRootsOfUnity_coe_apply f _

def muF : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj A := ModuleCat.of _ (ULift.{1} (Additive (rootsOfUnity q A)))
  map f := ModuleCat.ofHom (muMap q f.hom)
  map_id A := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact muMap_coe q _ x
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact muMap_coe q _ x

theorem prim_pow {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one] at h
  exact sub_eq_zero.1 h

def root {A : Type} [CommRing A] (ζ : Prim q A) : rootsOfUnity q A := rootsOfUnity.mkOfPowEq ζ.1 (prim_pow q ζ)

theorem root_coe {A : Type} [CommRing A] (ζ : Prim q A) : (((root q ζ : rootsOfUnity q A) : Aˣ) : A) = ζ.1 := rfl

def etaLin (A : Type) [CommRing A] : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (Additive (rootsOfUnity q A)) :=
  Finsupp.lift _ _ _ (fun ζ => ⟨Additive.ofMul (root q ζ)⟩)

theorem etaLin_single (A : Type) [CommRing A] (ζ : Prim q A) (c : ULift.{1} (ZMod q)) :
    etaLin q A (Finsupp.single ζ c) = ⟨c.down • Additive.ofMul (root q ζ)⟩ := by
  rw [etaLin, Finsupp.lift_apply, Finsupp.sum_single_index]
  · rfl
  · exact zero_smul _ _

theorem root_pow_coe {A : Type} [CommRing A] (ζ : Prim q A) (n : ℕ) :
    ((((root q ζ) ^ n : rootsOfUnity q A) : Aˣ) : A) = ζ.1 ^ n := by
  simp [root_coe]

theorem twRel_le_ker (A : Type) [CommRing A] : twRel q 1 A ≤ LinearMap.ker (etaLin q A) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, etaLin_single]
  rw [sub_eq_zero]
  apply ULift.ext
  change (1 : ZMod q) • Additive.ofMul (root q ξ) = ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q) • Additive.ofMul (root q ζ)
  rw [one_smul, zpow_one, smul_eq, ← ofMul_pow]
  congr 1
  apply Subtype.ext; apply Units.ext
  rw [root_pow_coe, root_coe, h]

def eta : twF q 1 ⟶ muF q where
  app A := ModuleCat.ofHom (Submodule.liftQ _ (etaLin q A) (twRel_le_ker q A))
  naturality A B f := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ c => ?_))
    change etaLin q B (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ c)) = muMap q f.hom (etaLin q A (Finsupp.single ζ c))
    rw [Finsupp.mapDomain_single, etaLin_single, etaLin_single]
    apply ULift.ext
    change c.down • Additive.ofMul (root q (Prim.map f.hom ζ)) =
      (muMap q f.hom (c • ⟨Additive.ofMul (root q ζ)⟩)).down
    rw [map_smul]
    change _ = c.down • (muMap q f.hom ⟨Additive.ofMul (root q ζ)⟩).down
    congr 1
    apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact (muMap_coe q f.hom ⟨Additive.ofMul (root q ζ)⟩).symm

theorem eta_mk (A : CommRingCat.{0}) (ζ : Prim q A) (c : ULift.{1} (ZMod q)) :
    ((eta q).app A).hom (Submodule.Quotient.mk (Finsupp.single ζ c)) = ⟨c.down • Additive.ofMul (root q ζ)⟩ :=
  etaLin_single q A ζ c

abbrev rval {V : Scheme.{0}} (t : ((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj (op V)) : Γ(V, ⊤)ˣ :=
  ((Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(V, ⊤))) t) : rootsOfUnity q Γ(V, ⊤)) : Γ(V, ⊤)ˣ)

theorem rval_map {V W : Scheme.{0}} (g : W ⟶ V) (t : ((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj (op V)) :
    ((rval q (((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).map g.op t) : Γ(W, ⊤)ˣ) : Γ(W, ⊤)) =
      (Scheme.Γ ⋙ forget CommRingCat).map g.op ((rval q t : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) := muMap_coe q _ _

theorem isSheaf : Presheaf.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ muF q) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))), isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  have hG := GmSec.isSheaf_gamma S hS
  let v : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => ((rval q (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  have hv : v.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    have := congrArg (fun t => ((rval q t : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤))) (hx g₁ g₂ h₁ h₂ e)
    simp only [rval_map] at this
    exact this
  obtain ⟨a, ha, -⟩ := hG v hv
  have hq : a ^ q = 1 := by
    refine hG.isSeparatedFor.ext (fun V f hf => ?_)
    change (Scheme.Γ.map f.op).hom (a ^ q) = (Scheme.Γ.map f.op).hom 1
    rw [map_pow, map_one]
    have h1 := ha f hf
    change (Scheme.Γ.map f.op).hom a = _ at h1
    rw [h1]
    change ((rval q (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) ^ q = 1
    have hr : rval q (x f hf) ^ q = 1 :=
      (mem_rootsOfUnity q _).1 (Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(V, ⊤))) (x f hf))).2
    rw [← Units.val_pow_eq_pow_val, hr, Units.val_one]
  refine ⟨(ULift.up (Additive.ofMul (rootsOfUnity.mkOfPowEq a hq)) :
    ((Scheme.Γ ⋙ muF q) ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj (op U)), ?_, ?_⟩
  · intro V f hf
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    exact (rval_map q f _).trans (ha f hf)
  · intro y hy
    apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    refine hG.isSeparatedFor.ext (fun V f hf => ?_)
    have e1 := congrArg (fun t => ((rval q t : Γ(V, ⊤)ˣ) : Γ(V, ⊤))) (hy f hf)
    simp only [rval_map] at e1
    exact e1.trans (ha f hf).symm

def muS : Shv (ZMod q) := ⟨Scheme.Γ ⋙ muF q, isSheaf q⟩

def etaS : tw q 1 ⟶ muS q := ⟨sheafifyLift Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ (eta q)) (isSheaf q)⟩

theorem etaS_sec (U : Scheme.{0}) (m : (twF q 1).obj Γ(U, ⊤)) :
    Sec.map (etaS q) (ofRings.sec (twF q 1) U m) = ((eta q).app Γ(U, ⊤)).hom m := by
  have h := toSheafify_sheafifyLift Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ (eta q)) (isSheaf q)
  exact congrArg (fun φ => (φ.app (op U)).hom m) h

theorem etaS_res {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 1) U) :
    Sec.map (etaS q) (Sec.res g x) = Sec.res g (Sec.map (etaS q) x) :=
  congrArg (fun φ => φ.hom x) ((etaS q).hom.naturality g.op)

abbrev muVal {U : Scheme.{0}} (y : Sec (muS q) U) : Γ(U, ⊤) :=
  (((Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(U, ⊤))) y) : rootsOfUnity q Γ(U, ⊤)) : Γ(U, ⊤)ˣ) : Γ(U, ⊤))

theorem muVal_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec (muS q) U) : muVal q (Sec.res g y) = g.appTop.hom (muVal q y) :=
  muMap_coe q _ _

theorem muVal_injective (U : Scheme.{0}) : Function.Injective (muVal q (U := U)) := fun y y' h => by
  apply ULift.ext; apply Additive.toMul.injective; apply Subtype.ext; exact Units.ext h

end GlobalTheory.EtC.MuTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsInjective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

noncomputable section
namespace GlobalTheory.EtC.MuTw.Inj

variable (q : ℕ) [NeZero q]

theorem comp_appTop_apply' {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (a : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom a = g.appTop.hom (h.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem eq_zero_of_pow_eq_one {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (C : ZMod q)
    (h : ζ.1 ^ C.val = 1) : C = 0 := by
  by_contra hC
  have hne : ¬ C.val ≡ 0 [MOD q] := by
    intro hm
    apply hC
    rw [← ZMod.val_eq_zero]
    unfold Nat.ModEq at hm
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt C), Nat.zero_mod] at hm
  have hu := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).2.2.1 ζ C.val 0 hne
  rw [h, pow_zero, sub_self] at hu
  exact not_isUnit_zero hu

theorem mk_single_eq {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (c : ULift.{1} (ZMod q)) :
    (twRel q 1 A).mkQ (Finsupp.single ξ c) = (twRel q 1 A).mkQ (Finsupp.single ζ (c * ULift.up (a : ZMod q))) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  have hmem : Finsupp.single ξ 1 - Finsupp.single ζ (ULift.up ((a ^ (1 : ℤ) : (ZMod q)ˣ) : ZMod q)) ∈ twRel q 1 A :=
    Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have := (twRel q 1 A).smul_mem c hmem
  convert this using 1
  rw [smul_sub, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, zpow_one]

theorem mk_eq_single {A : Type} [CommRing A] (ζ : Prim q A) (f : Prim q A →₀ ULift.{1} (ZMod q))
    (h : ∀ ξ ∈ f.support, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ∃ C : ULift.{1} (ZMod q), (twRel q 1 A).mkQ f = (twRel q 1 A).mkQ (Finsupp.single ζ C) := by
  classical
  choose! a ha using h
  refine ⟨∑ ξ ∈ f.support, f ξ * ULift.up (a ξ : ZMod q), ?_⟩
  conv_lhs => rw [← Finsupp.sum_single f]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum, Finsupp.single_finsetSum, map_sum]
  exact Finset.sum_congr rfl fun ξ hξ => mk_single_eq q ζ ξ (a ξ) (ha ξ hξ) (f ξ)

end GlobalTheory.EtC.MuTw.Inj

namespace GlobalTheory.EtC.MuTw.Inj
variable (q : ℕ) [NeZero q]

theorem local_zero (V : Scheme.{0}) [IsAffine V] (m : (twF q 1).obj Γ(V, ⊤))
    (hm : ((eta q).app Γ(V, ⊤)).hom m = 0) (v : V) :
    ∃ (W : Scheme.{0}) (k : W ⟶ V), IsAffine W ∧ Etale k ∧ v ∈ Set.range k ∧ ((twF q 1).map k.appTop).hom m = 0 := by
  classical
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (twRel q 1 Γ(V, ⊤)) m
  by_cases hf : f = 0
  · refine ⟨V, 𝟙 V, inferInstance, inferInstance, ⟨v, rfl⟩, ?_⟩
    have h0 : ((twRel q 1 Γ(V, ⊤)).mkQ f : (twF q 1).obj Γ(V, ⊤)) = 0 := by rw [hf, map_zero]
    rw [h0]
    exact map_zero _
  obtain ⟨ζ₀, hζ₀⟩ := Finsupp.support_nonempty_iff.2 hf
  let P : f.support → ∀ W : Scheme.{0}, (W ⟶ V) → Prop := fun ξ W k =>
    ∃ a : (ZMod q)ˣ, k.appTop.hom ξ.1.1 = k.appTop.hom ζ₀.1 ^ (a : ZMod q).val
  have hL : Loc V fun W k => ∀ ξ, P ξ W k :=
    (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.2.1 V f.support P fun ξ => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 ζ₀ ξ.1
  have hst : ∀ (W W' : Scheme.{0}) (g : W ⟶ V) (k : W' ⟶ W), (∀ ξ, P ξ W g) → ∀ ξ, P ξ W' (k ≫ g) := by
    intro W W' g k h ξ
    obtain ⟨a, ha⟩ := h ξ
    refine ⟨a, ?_⟩
    rw [comp_appTop_apply', comp_appTop_apply', ha, map_pow]
  obtain ⟨W, k, hWa, hk, ⟨w, hw⟩, hP⟩ := ((GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover V _ hst).1 hL) v
  refine ⟨W, k, hWa, hk, ⟨w, hw⟩, ?_⟩
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨w, trivial⟩⟩
  haveI : Nontrivial Γ(W, ⊤) := Scheme.component_nontrivial W ⊤
  let φ := k.appTop.hom
  let ζ₁ : Prim q Γ(W, ⊤) := Prim.map φ ζ₀
  have hmap : ((twF q 1).map k.appTop).hom ((twRel q 1 Γ(V, ⊤)).mkQ f) =
      (twRel q 1 Γ(W, ⊤)).mkQ (Finsupp.mapDomain (Prim.map φ) f) := rfl
  obtain ⟨C, hC⟩ := mk_eq_single q ζ₁ (Finsupp.mapDomain (Prim.map φ) f) (by
    intro ξ' hξ'
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hξ')
    obtain ⟨a, ha⟩ := hP ⟨ξ, hξ⟩
    exact ⟨a, ha⟩)
  rw [hmap, hC]
  have he : ((eta q).app Γ(W, ⊤)).hom ((twF q 1).map k.appTop |>.hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) = 0 := by
    have := congrArg (fun g => g.hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) ((eta q).naturality k.appTop)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at this
    refine this.trans ?_
    change ((muF q).map k.appTop).hom (((eta q).app Γ(V, ⊤)).hom ((twRel q 1 Γ(V, ⊤)).mkQ f)) = 0
    rw [hm, map_zero]
  rw [hmap, hC, Submodule.mkQ_apply, eta_mk] at he
  have h1 : ζ₁.1 ^ C.down.val = 1 := by
    have := congrArg (fun y : ULift.{1} (Additive (rootsOfUnity q Γ(W, ⊤))) =>
      (((Additive.toMul y.down : rootsOfUnity q Γ(W, ⊤)) : Γ(W, ⊤)ˣ) : Γ(W, ⊤))) he
    simp only [smul_eq, toMul_nsmul, toMul_ofMul] at this
    rw [root_pow_coe] at this
    exact this.trans rfl
  have hC0 : C = 0 := ULift.ext (eq_zero_of_pow_eq_one q ζ₁ C.down h1)
  rw [hC0, Finsupp.single_zero, map_zero]
  rfl

end GlobalTheory.EtC.MuTw.Inj

namespace GlobalTheory.EtC.MuTw.Inj

theorem res_comp {q : ℕ} {V W U : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (x : Sec (tw q 1) U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  change ((tw q 1).obj.map (k ≫ g).op).hom x = ((tw q 1).obj.map k.op).hom (((tw q 1).obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem etaS_injective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Function.Injective ((etaS q).hom.app (op U)).hom := by
  intro q _ U _
  refine (injective_iff_map_eq_zero ((etaS q).hom.app (op U)).hom).2 fun x hx => ?_
  have hst : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), Sec.res g x = 0 → Sec.res (k ≫ g) x = 0 := by
    intro V W g k h
    rw [res_comp, h]
    exact map_zero _
  have hloc : Loc U fun W g => Sec.res g x = 0 := by
    rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ hst]
    intro u
    obtain ⟨V, j, v, m, hVa, hj, hjv, hm⟩ := (GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective (ZMod q) (twF q 1) U).1 x u
    have hem : ((eta q).app Γ(V, ⊤)).hom m = 0 := by
      have hm' : (ofRings.sec (twF q 1) V m : Sec (tw q 1) V) = Sec.res (F := tw q 1) j x := hm
      rw [← etaS_sec, hm', etaS_res]
      change Sec.res j (((etaS q).hom.app (op U)).hom x) = 0
      rw [hx]
      exact map_zero _
    obtain ⟨W, k, hWa, hk, ⟨w, hw⟩, hmW⟩ := local_zero q V m hem v
    refine ⟨W, k ≫ j, hWa, inferInstance, ⟨w, ?_⟩, ?_⟩
    · rw [Scheme.Hom.comp_apply, hw, hjv]
    · have hm' : Sec.res (F := tw q 1) j x = (ofRings.sec (twF q 1) V m : Sec (tw q 1) V) := hm.symm
      rw [res_comp, hm']
      refine ((GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective (ZMod q) (twF q 1) V).2.2 W k m).trans ?_
      rw [hmW]
      exact map_zero _
  obtain ⟨S, hS, hSP⟩ := hloc
  have hF := (tw q 1).property
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hF
  refine (hF S hS).isSeparatedFor.ext fun V g hg => ?_
  have h1 := hSP V g hg
  change Sec.res g x = Sec.res g 0
  rw [h1]
  exact (map_zero _).symm

end GlobalTheory.EtC.MuTw.Inj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsInjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Injective ((etaS q).hom.app (op U)).hom := by
  first | (exact @GlobalTheory.EtC.MuTw.Inj.etaS_injective) | (exact GlobalTheory.EtC.MuTw.Inj.etaS_injective) | (intros; apply GlobalTheory.EtC.MuTw.Inj.etaS_injective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneSectionsEqRootsOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsSurjective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

noncomputable section
namespace GlobalTheory.EtC.MuTw

theorem appTop_comp_apply' {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Γ(U, ⊤)) :
    (k ≫ g).appTop.hom a = k.appTop.hom (g.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem isUnit_natCast_of_hom {V U : Scheme.{0}} (g : V ⟶ U) (q : ℕ) (hq : IsUnit (q : Γ(U, ⊤))) :
    IsUnit (q : Γ(V, ⊤)) := by
  have := hq.map g.appTop.hom
  rwa [map_natCast] at this

theorem muVal_pow (q : ℕ) [NeZero q] {U : Scheme.{0}} (y : Sec (muS q) U) : muVal q y ^ q = 1 := by
  have hr := (mem_rootsOfUnity q _).1 (Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(U, ⊤))) y)).2
  change (( _ : Γ(U, ⊤)ˣ) : Γ(U, ⊤)) ^ q = 1
  rw [← Units.val_pow_eq_pow_val, hr, Units.val_one]

theorem etaS_lift_pow (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (z : Sec (muS q) V) (a : ℕ)
    (h : muVal q z = ζ.1 ^ a) :
    Sec.map (etaS q) (ofRings.sec (twF q 1) V
      (Submodule.Quotient.mk (Finsupp.single ζ (ULift.up (a : ZMod q))))) = z := by
  refine (etaS_sec q V _).trans ((eta_mk q Γ(V, ⊤) ζ _).trans ?_)
  apply muVal_injective q V
  rw [h]
  change (((Additive.toMul (((a : ZMod q)) • Additive.ofMul (root q ζ)) : rootsOfUnity q Γ(V, ⊤)) :
    Γ(V, ⊤)ˣ) : Γ(V, ⊤)) = _
  rw [smul_eq, toMul_nsmul, toMul_ofMul, root_pow_coe, ZMod.val_natCast]
  exact (pow_eq_pow_mod a (prim_pow q ζ)).symm

end GlobalTheory.EtC.MuTw

namespace GlobalTheory.EtC.MuTw

theorem etaS_surjective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Function.Surjective ((etaS q).hom.app (op U)).hom := by
  intro q _ U hq y
  have hloc : Loc U fun V g => ∃ s : Sec (tw q 1) V, Sec.map (etaS q) s = Sec.res g y := by
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.1 U _ ?_
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq) ?_
    rintro V g ⟨ζ⟩
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _
      ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ (muVal q (Sec.res g y)) (muVal_pow q _)) ?_
    rintro W k ⟨a, ha⟩
    refine ⟨_, etaS_lift_pow q W (Prim.map k.appTop.hom ζ) (Sec.res (k ≫ g) y) a ?_⟩
    rw [muVal_res, appTop_comp_apply', ← muVal_res, ha]
    rfl
  obtain ⟨S, hS, hSy⟩ := hloc
  choose s hs using hSy
  have hsh := (tw q 1).property
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hsh
  let fam : Presieve.FamilyOfElements ((tw q 1).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows :=
    fun V g hg => s V g hg
  have hfam : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    apply GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective q Z (isUnit_natCast_of_hom (g₁ ≫ f₁) q hq)
    change Sec.map (etaS q) (Sec.res g₁ (s _ f₁ h₁)) = Sec.map (etaS q) (Sec.res g₂ (s _ f₂ h₂))
    rw [etaS_res, etaS_res, hs, hs]
    apply muVal_injective q Z
    simp only [muVal_res]
    rw [← appTop_comp_apply', ← appTop_comp_apply', e]
  obtain ⟨x, hx, -⟩ := hsh S hS fam hfam
  refine ⟨x, ?_⟩
  have hsep := (muS q).property
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hsep
  refine (hsep S hS).isSeparatedFor.ext (fun V g hg => ?_)
  change Sec.res g (Sec.map (etaS q) x) = Sec.res g y
  rw [← etaS_res]
  have h1 : Sec.res g x = s V g hg := hx g hg
  rw [h1, hs]

end GlobalTheory.EtC.MuTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsSurjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_surjective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Surjective ((etaS q).hom.app (op U)).hom := by
  first | (exact @GlobalTheory.EtC.MuTw.etaS_surjective) | (exact GlobalTheory.EtC.MuTw.etaS_surjective) | (intros; apply GlobalTheory.EtC.MuTw.etaS_surjective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneSectionsEqRootsOfUnity
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC


open GlobalTheory.EtC.MuTw in
theorem GlobalTheory.EtC.tw_one_mu : ∀ (q : ℕ) [NeZero q], ∃ e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C), ∀ (C D : Type) [CommRing C] [CommRing D] (φ : C →+* D) (hC : IsUnit (q : C)) (hD : IsUnit (q : D)) (x : (onRings (tw q 1)).obj (CommRingCat.of C)), ((Additive.toMul (e D hD (((onRings (tw q 1)).map (CommRingCat.ofHom φ)).hom x)) : rootsOfUnity q D) : Dˣ) = Units.map φ.toMonoidHom ((Additive.toMul (e C hC x) : rootsOfUnity q C) : Cˣ) := by
  intro q _
  have hunit : ∀ (C : Type) [CommRing C], IsUnit (q : C) → IsUnit (q : Γ(Spec (CommRingCat.of C), ⊤)) := by
    intro C _ hC
    have := hC.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
    simpa using this
  let e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C) :=
    fun C _ hC =>
      ((AddEquiv.ofBijective ((etaS q).hom.app (op (Spec (CommRingCat.of C)))).hom.toAddMonoidHom
        ⟨GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective q _ (hunit C hC), GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_surjective q _ (hunit C hC)⟩).trans AddEquiv.ulift).trans
        (MulEquiv.restrictRootsOfUnity (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.toMulEquiv q).toAdditive
  refine ⟨e, ?_⟩
  intro C D _ _ φ hC hD x
  apply Units.ext
  have h1 := etaS_res q (Spec.map (CommRingCat.ofHom φ)) x
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (muVal q (Sec.map (etaS q) (Sec.res (Spec.map (CommRingCat.ofHom φ)) x))) = φ ((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (muVal q (Sec.map (etaS q) x)))
  rw [h1, muVal_res]
  exact congrArg (fun f => f.hom (muVal q (Sec.map (etaS q) x))) h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneSectionsEqRootsOfUnityStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity : ∀ (q : ℕ) [NeZero q], ∃ e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C), ∀ (C D : Type) [CommRing C] [CommRing D] (φ : C →+* D) (hC : IsUnit (q : C)) (hD : IsUnit (q : D)) (x : (onRings (tw q 1)).obj (CommRingCat.of C)), ((Additive.toMul (e D hD (((onRings (tw q 1)).map (CommRingCat.ofHom φ)).hom x)) : rootsOfUnity q D) : Dˣ) = Units.map φ.toMonoidHom ((Additive.toMul (e C hC x) : rootsOfUnity q C) : Cˣ) := by
  first | (exact @GlobalTheory.EtC.tw_one_mu) | (exact GlobalTheory.EtC.tw_one_mu) | (intros; apply GlobalTheory.EtC.tw_one_mu  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerVanishing
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem uCoc_one (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : UCoc A B 1 := by
  unfold UCoc
  simp [Algebra.TensorProduct.one_def]

theorem uCoc_mul {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {u v : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) (hv : UCoc A B v) : UCoc A B (u * v) := by
  unfold UCoc at *
  simp only [Units.val_mul, map_mul, hu, hv]
  ring

theorem uCoc_pow {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {u : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) (n : ℕ) : UCoc A B (u ^ n) := by
  induction n with
  | zero => simpa using uCoc_one A B
  | succ n ih => rw [pow_succ]; exact uCoc_mul ih hu

theorem kummer_vanishing : B6h1 := by
  intro q _ A _ hq hu hp
  suffices h : ∀ x : Ht q (sp A) 1 1, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨Y, f, hfe, hfs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover (ZMod q) (Spec (CommRingCat.of A)) (tw q 1) 1 one_pos x
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of A) Y f hfe hfs
  letI : Algebra A B := g.hom.toAlgebra
  haveI : Algebra.Etale A B := hg.1
  haveI : Module.FaithfullyFlat A B := hg.2
  have hxB : pull (ZMod q) (spMap (algebraMap A B)) (tw q 1) 1 x = 0 := by
    have : spMap (algebraMap A B) = sch.map h ≫ sch.map f := by
      rw [← sch.map_comp, hhf]; rfl
    rw [this, pull_comp, hx, map_zero]
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.etale_cocycle_coboundary_iff (ZMod q) (tw q 1) A
  obtain ⟨hγ0, hγs, -, -⟩ := hγ B
  obtain ⟨u, rfl⟩ := hγs x hxB
  rw [hγ0]

  obtain ⟨e, he⟩ := GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity q
  have hqB : IsUnit (q : (B : Type)) := by simpa using hq.map (algebraMap A B)
  have hqBB : IsUnit (q : B ⊗[A] B) := by simpa using hq.map (algebraMap A (B ⊗[A] B))
  have hqBBB : IsUnit (q : B ⊗[A] (B ⊗[A] B)) := by simpa using hq.map (algebraMap A (B ⊗[A] (B ⊗[A] B)))
  have hUq : ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) ^ q = 1 :=
    (mem_rootsOfUnity _ _).1 (Additive.toMul (e _ hqBB u.1)).2
  have hUc : UCoc A B ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) := by
    have h2 := u.2
    change _ = _ at h2
    have h3 := congrArg (fun y => ((Additive.toMul (e _ hqBBB y) : rootsOfUnity q _) : (B ⊗[A] (B ⊗[A] B))ˣ)) h2
    simp only [AddMonoidHom.add_apply, map_add (f := _), toMul_add, Subgroup.coe_mul, LinearMap.toAddMonoidHom_coe] at h3
    rw [he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB] at h3
    have h4 := congrArg Units.val h3
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.coe_toRingHom] at h4
    exact h4

  set U := ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) with hUdef
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A
  obtain ⟨hmul, hone, -, -, -⟩ := hδ B
  have hδ1 : δ B 1 = 1 := by
    have := hmul 1 1 (uCoc_one A B) (uCoc_one A B)
    rw [mul_one] at this
    simpa using this
  have hδpow : ∀ n : ℕ, δ B (U ^ n) = δ B U ^ n := by
    intro n
    induction n with
    | zero => simpa using hδ1
    | succ n ih => rw [pow_succ, hmul _ _ (uCoc_pow hUc n) hUc, ih, pow_succ]
  have hδU : δ B U = 1 := hp _ (by rw [← hδpow, hUq, hδ1])
  obtain ⟨w, hw⟩ := (hone U hUc).1 hδU
  let iL : (B : Type) →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let iR : (B : Type) →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  have hwU : U * Units.map iR.toRingHom.toMonoidHom w = Units.map iL.toRingHom.toMonoidHom w :=
    Units.ext (by simpa [iL, iR] using hw)
  have hWq : Units.map iL.toRingHom.toMonoidHom (w ^ q) = Units.map iR.toRingHom.toMonoidHom (w ^ q) := by
    rw [map_pow, map_pow, ← hwU, mul_pow, hUq, one_mul]
  have hWq' : Units.map iL.toRingHom.toMonoidHom (w ^ q)⁻¹ = Units.map iR.toRingHom.toMonoidHom (w ^ q)⁻¹ := by
    rw [map_inv, map_inv, hWq]
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B ((w ^ q : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq)
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B (((w ^ q)⁻¹ : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq')
  have haa : a * a' = 1 :=
    FaithfulSMul.algebraMap_injective A B (by rw [map_mul, ha, ha', Units.mul_inv, map_one])
  obtain ⟨v, hv⟩ := hu ⟨a, a', haa, by rw [mul_comm, haa]⟩
  let vB : (B : Type)ˣ := Units.map (algebraMap A B).toMonoidHom v
  have hvB : vB ^ q = w ^ q := by
    apply Units.ext
    rw [← map_pow, ← hv, Units.coe_map]
    exact ha
  have hT : (vB * w⁻¹) ^ q = 1 := by rw [mul_pow, hvB, inv_pow, mul_inv_cancel]
  let Tr : rootsOfUnity q (B : Type) := ⟨vB * w⁻¹, (mem_rootsOfUnity _ _).2 hT⟩
  have hV : Units.map iR.toRingHom.toMonoidHom vB = Units.map iL.toRingHom.toMonoidHom vB := by
    apply Units.ext
    simp [vB, iL, iR]
  refine ⟨(e _ hqB).symm (Additive.ofMul Tr), ?_⟩
  apply (e _ hqBB).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [map_sub, toMul_sub, SubgroupClass.coe_div, he _ _ _ hqB hqBB, he _ _ _ hqB hqBB, AddEquiv.apply_symm_apply]
  change U = Units.map iR.toRingHom.toMonoidHom (vB * w⁻¹) / Units.map iL.toRingHom.toMonoidHom (vB * w⁻¹)
  rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq, map_mul, map_mul, map_inv, map_inv, hV, ← hwU]
  rw [mul_inv_rev, mul_left_comm, ← mul_assoc U, mul_comm U, mul_assoc, mul_inv_cancel, mul_one]
end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerVanishingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_etale_vanishing : GlobalTheory.EtC.B6h1 := by
  first | (exact @GlobalTheory.EtC.kummer_vanishing) | (exact GlobalTheory.EtC.kummer_vanishing) | (intros; apply GlobalTheory.EtC.kummer_vanishing  <;> assumption)
end
