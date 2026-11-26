module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianFirstCoordsMeasurePreserving
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CoeffLgPcurveTop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.GeomSumRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateInCell
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateInCellStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairing
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.res_lof {I J : _root_.GlobalTheory.EtC.Cx R} {V U : Scheme.{0}}
    (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U) (b : _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U) :
    _root_.GlobalTheory.EtC.Tens.res g w
      (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U)
        p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) V ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) V) p
        (_root_.GlobalTheory.EtC.Sec.res g a ⊗ₜ _root_.GlobalTheory.EtC.Sec.res g b) := by
  unfold _root_.GlobalTheory.EtC.Tens.res
  rw [DirectSum.lmap_lof, TensorProduct.map_tmul]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.sres_id {F : _root_.GlobalTheory.EtC.Shv R} {U : Scheme.{0}}
    (a : _root_.GlobalTheory.EtC.Sec F U) : _root_.GlobalTheory.EtC.Sec.res (𝟙 U) a = a := by
  unfold _root_.GlobalTheory.EtC.Sec.res
  simp

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.sres_comp {F : _root_.GlobalTheory.EtC.Shv R} {W V U : Scheme.{0}}
    (g : W ⟶ V) (f : V ⟶ U) (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res (g ≫ f) a =
      _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.res f a) := by
  unfold _root_.GlobalTheory.EtC.Sec.res
  simp

def pre (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_)
    simp [res_lof, sres_id]
  map_comp f g := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_)
    simp [res_lof, sres_comp]

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.smap_res {F G : _root_.GlobalTheory.EtC.Shv R} (φ : F ⟶ G)
    {V U : Scheme.{0}} (g : V ⟶ U) (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.map φ a) =
      _root_.GlobalTheory.EtC.Sec.map φ (_root_.GlobalTheory.EtC.Sec.res g a) := by
  unfold _root_.GlobalTheory.EtC.Sec.res _root_.GlobalTheory.EtC.Sec.map
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp; omega⟩ ∘ₗ
      TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id) +
    ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.dT_lof {I J : _root_.GlobalTheory.EtC.Cx R} (U : Scheme.{0})
    (s t w : ℤ) (h : s + t = w) (a : _root_.GlobalTheory.EtC.Sec (I.X s) U)
    (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.TensEx.dT I J U w (DirectSum.lof (ULift.{1} R) _
      (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U)
        ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
        ⟨(s + 1, t), by simp; omega⟩
        (_root_.GlobalTheory.EtC.Sec.map (I.d s (s + 1)) a ⊗ₜ b) +
    (s.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
        ⟨(s, t + 1), by simp; omega⟩
        (a ⊗ₜ _root_.GlobalTheory.EtC.Sec.map (J.d t (t + 1)) b) := by
  unfold _root_.GlobalTheory.EtC.TensEx.dT
  rw [DirectSum.toModule_lof]
  rfl

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

def D (I J : Cx R) (w : ℤ) : pre I J w ⟶ pre I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_)
    simp only [pre, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    rw [res_lof, dT_lof, dT_lof, map_add (f := _), map_zsmul, res_lof, res_lof, smap_res, smap_res]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem sec_map_d_map_d_eq_zero (K : _root_.GlobalTheory.EtC.Cx R) {U : Scheme.{0}}
    (i j k : ℤ) (a : _root_.GlobalTheory.EtC.Sec (K.X i) U) :
    _root_.GlobalTheory.EtC.Sec.map (K.d j k) (_root_.GlobalTheory.EtC.Sec.map (K.d i j) a) = 0 := by
  have key := congrArg (fun f : K.X i ⟶ K.X k => (f.hom.app (op U)).hom a) (K.d_comp_d i j k)
  exact key

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.D_comp (I J : _root_.GlobalTheory.EtC.Cx R) (w : ℤ) :
    _root_.GlobalTheory.EtC.TensEx.D I J w ≫
      _root_.GlobalTheory.EtC.TensEx.D I J (w + 1) = 0 := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (DirectSum.linearMap_ext _
    fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  show _root_.GlobalTheory.EtC.TensEx.dT I J U.unop (w + 1) (_root_.GlobalTheory.EtC.TensEx.dT I J U.unop w
    (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U.unop ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U.unop)
      ⟨(s, t), h⟩ (a ⊗ₜ b))) = 0
  rw [_root_.GlobalTheory.EtC.TensEx.dT_lof, map_add (f := _), map_zsmul, _root_.GlobalTheory.EtC.TensEx.dT_lof,
    _root_.GlobalTheory.EtC.TensEx.dT_lof, sec_map_d_map_d_eq_zero, sec_map_d_map_d_eq_zero,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, map_zero]
  simp [Int.negOnePow_succ, smul_add]

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

def cx (I J : Cx R) : Cx R :=
  CochainComplex.of (fun w => (presheafToSheaf Scheme.etaleTopology _).obj (pre I J w))
    (fun w => (presheafToSheaf Scheme.etaleTopology _).map (D I J w))
    (fun w => by rw [← Functor.map_comp, D_comp, Functor.map_zero])

def toS (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((cx I J).X w) U :=
  ((toSheafify Scheme.etaleTopology (pre I J w)).app (op U)).hom

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.toS_res (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}}
    (g : V ⟶ U) (w : ℤ) (x : _root_.GlobalTheory.EtC.Tens I J U w) :
    _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.TensEx.toS I J U w x) =
      _root_.GlobalTheory.EtC.TensEx.toS I J V w (_root_.GlobalTheory.EtC.Tens.res g w x) := by
  have key := congrArg (fun f => ModuleCat.Hom.hom f x)
    ((toSheafify Scheme.etaleTopology (_root_.GlobalTheory.EtC.TensEx.pre I J w)).naturality g.op)
  exact key.symm

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.d_toS (I J : _root_.GlobalTheory.EtC.Cx R)
    (U : Scheme.{0}) (w : ℤ) (x : _root_.GlobalTheory.EtC.Tens I J U w) :
    _root_.GlobalTheory.EtC.Sec.map ((_root_.GlobalTheory.EtC.TensEx.cx I J).d w (w + 1))
        (_root_.GlobalTheory.EtC.TensEx.toS I J U w x) =
      _root_.GlobalTheory.EtC.TensEx.toS I J U (w + 1) (_root_.GlobalTheory.EtC.TensEx.dT I J U w x) := by
  have hd : (_root_.GlobalTheory.EtC.TensEx.cx I J).d w (w + 1) = (presheafToSheaf Scheme.etaleTopology _).map
      (_root_.GlobalTheory.EtC.TensEx.D I J w) := by
    unfold _root_.GlobalTheory.EtC.TensEx.cx
    simp
  have key := congrArg (fun f => ModuleCat.Hom.hom (f.app (op U)) x)
    (toSheafify_naturality Scheme.etaleTopology (_root_.GlobalTheory.EtC.TensEx.D I J w))
  rw [hd]
  exact key.symm

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

def pair (I J : Cx R) : Pair I J (cx I J) where
  mul U s t w h := (TensorProduct.mk (ULift.{1} R) _ _).compr₂ (toS I J U w ∘ₗ
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [toS_res, res_lof]
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [d_toS, dT_lof, map_add (f := _), map_zsmul, Units.smul_def]

end GlobalTheory.EtC.TensEx


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
theorem _root_.GlobalTheory.EtC.tensor_exists :
    ∀ (R : Type) [CommRing R] (I J : _root_.GlobalTheory.EtC.Cx R),
      ∃ (K : _root_.GlobalTheory.EtC.Cx R) (τ : _root_.GlobalTheory.EtC.Pair I J K), τ.IsTensor := by
  intro R _ I J
  refine ⟨_root_.GlobalTheory.EtC.TensEx.cx I J, _root_.GlobalTheory.EtC.TensEx.pair I J, ?_⟩
  have hlift : ∀ (U : Scheme.{0}) (w : ℤ),
      (_root_.GlobalTheory.EtC.TensEx.pair I J).lift U w =
        _root_.GlobalTheory.EtC.TensEx.toS I J U w := by
    intro U w
    refine DirectSum.linearMap_ext _ fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_
    unfold _root_.GlobalTheory.EtC.Pair.lift
    rw [LinearMap.comp_apply, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    rfl
  unfold _root_.GlobalTheory.EtC.Pair.IsTensor
  simp only [hlift]
  exact ⟨fun U w y =>
      (_root_.GlobalTheory.EtC.toSheafify_loc_bij_lift R (_root_.GlobalTheory.EtC.TensEx.pre I J w)).1 U y,
    fun U w x hx =>
      (_root_.GlobalTheory.EtC.toSheafify_loc_bij_lift R (_root_.GlobalTheory.EtC.TensEx.pre I J w)).2.1 U x hx⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing : ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor := by
  first | (exact @GlobalTheory.EtC.tensor_exists) | (exact GlobalTheory.EtC.tensor_exists) | (intros; apply GlobalTheory.EtC.tensor_exists  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombination
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etaleLocally_weaken_freeSheafSections {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem free_sec_lin_sum {S X M : Type*} [Semiring S] [AddCommMonoid M] [Module S M]
    (φ : (X →₀ S) →ₗ[S] M) (x : X →₀ S) :
    (x.sum fun a r => r • φ (Finsupp.single a 1)) = φ x := by
  calc (x.sum fun a r => r • φ (Finsupp.single a 1))
      = x.sum fun a r => φ (Finsupp.single a r) := by
        refine Finsupp.sum_congr fun a _ => ?_
        rw [← map_smul, Finsupp.smul_single_one]
    _ = φ x := by rw [← map_finsuppSum, Finsupp.sum_single]

theorem free_sec_sum_eq (R : Type) [CommRing R] (P : PSh) (V : Scheme.{0})
    (x : ULift.{1} (P.obj (op V)) →₀ ULift.{1} R) :
    ((Finsupp.mapDomain ULift.down x).sum fun a r => r • freeGen R P V a) =
      ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom x := by
  rw [Finsupp.sum_mapDomain_index_inj ULift.down_injective]
  exact free_sec_lin_sum ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom x

theorem free_sec_loc : ∀ (R : Type) [CommRing R] (P : PSh) (U : Scheme.{0}), (∀ y : Sec ((free R).obj P) U, Loc U fun V g => ∃ c : P.obj (op V) →₀ ULift.{1} R, Sec.res g y = c.sum fun x r => r • freeGen R P V x) ∧ ∀ c : P.obj (op U) →₀ ULift.{1} R, (c.sum fun x r => r • freeGen R P U x) = 0 → Loc U fun _ g => Finsupp.mapDomain (P.map g.op) c = 0 := by
  intro R _ P U
  have base := GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R ((freeP R).obj P)
  refine ⟨fun y => ?_, fun c hc => ?_⟩
  · refine etaleLocally_weaken_freeSheafSections (base.1 U y) ?_
    rintro V g ⟨x, hx⟩
    exact ⟨_, ((free_sec_sum_eq R P V x).trans hx).symm⟩
  · have hdu : Finsupp.mapDomain ULift.down (Finsupp.mapDomain ULift.up c) = c := by
      rw [← Finsupp.mapDomain_comp]
      exact Finsupp.mapDomain_id
    have h2 : ((Finsupp.mapDomain ULift.down (Finsupp.mapDomain ULift.up c)).sum
        fun a r => r • freeGen R P U a) = 0 := by
      rw [hdu]
      exact hc
    have hx := (free_sec_sum_eq R P U _).symm.trans h2
    refine etaleLocally_weaken_freeSheafSections (base.2.1 U _ hx) ?_
    intro V g hg
    have key : Finsupp.mapDomain ULift.down ((((freeP R).obj P).map g.op).hom
        (Finsupp.mapDomain ULift.up c)) = Finsupp.mapDomain (P.map g.op) c := by
      have e1 : (((freeP R).obj P).map g.op).hom (Finsupp.mapDomain ULift.up c) =
          Finsupp.mapDomain (fun a : ULift.{1} (P.obj (op U)) =>
            (ULift.up (P.map g.op a.down) : ULift.{1} (P.obj (op V)))) (Finsupp.mapDomain ULift.up c) := rfl
      rw [e1, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
      rfl
    rw [← key]
    exact (congrArg (Finsupp.mapDomain ULift.down) hg).trans Finsupp.mapDomain_zero

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombinationStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination : ∀ (R : Type) [CommRing R] (P : PSh) (U : Scheme.{0}), (∀ y : Sec ((free R).obj P) U, Loc U fun V g => ∃ c : P.obj (op V) →₀ ULift.{1} R, Sec.res g y = c.sum fun x r => r • freeGen R P V x) ∧ ∀ c : P.obj (op U) →₀ ULift.{1} R, (c.sum fun x r => r • freeGen R P U x) = 0 → Loc U fun _ g => Finsupp.mapDomain (P.map g.op) c = 0 := by
  first | (exact @GlobalTheory.EtC.free_sec_loc) | (exact GlobalTheory.EtC.free_sec_loc) | (intros; apply GlobalTheory.EtC.free_sec_loc  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EveryElementIsNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianFrobeniusLift
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem exists_isNorm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F'), ∃ γ : GL (Fin n) F, IsNorm s δ γ := by
  intro F F' _ _ _ _ s hs n δ₀
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI : Finite (GL (Fin n) F) := inferInstance
  haveI : Finite (GL (Fin n) F') := inferInstance
  letI := Fintype.ofFinite (GL (Fin n) F)
  letI := Fintype.ofFinite (GL (Fin n) F')
  have hfib := GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL F F' s hs n
  have hnd := GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion F F' n
  let cl : GL (Fin n) F → ℕ := fun γ => Nat.card {γ' : GL (Fin n) F // IsConj γ γ'}
  have hcl_pos : ∀ γ, 0 < cl γ := fun γ => Nat.card_pos_iff.2 ⟨⟨⟨γ, IsConj.refl γ⟩⟩, inferInstance⟩
  have hcl_eq : ∀ γ, (cl γ : ℚ) = ((Finset.univ.filter fun γ' => IsConj γ γ').card : ℚ) := by
    intro γ
    simp only [cl, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard : ∀ γ, Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ}
      = (Finset.univ.filter fun δ => IsNorm s δ γ).card := by
    intro γ
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let f : GL (Fin n) F' → GL (Fin n) F → ℚ := fun δ γ => if IsNorm s δ γ then ((cl γ : ℚ))⁻¹ else 0
  have h1 : ∀ δ, ∑ γ, f δ γ = if ∃ γ, IsNorm s δ γ then 1 else 0 := by
    intro δ
    by_cases h : ∃ γ, IsNorm s δ γ
    · obtain ⟨γ₀, h₀⟩ := h
      rw [if_pos ⟨γ₀, h₀⟩]
      have hiff : ∀ γ, IsNorm s δ γ ↔ IsConj γ₀ γ := by
        intro γ
        constructor
        · intro hγ
          exact hnd γ₀ γ (h₀.trans hγ.symm)
        · intro hγ
          exact (isConj_iff.2 (by
            obtain ⟨c, hc⟩ := isConj_iff.1 hγ
            exact ⟨incl F F' n c, by rw [← hc]; simp [map_mul, map_inv]⟩)).symm.trans h₀
      have hcl' : ∀ γ, IsConj γ₀ γ → cl γ = cl γ₀ := by
        intro γ hγ
        exact Nat.card_congr (Equiv.subtypeEquivRight fun γ' => ⟨fun h => hγ.trans h, fun h => hγ.symm.trans h⟩)
      have : ∀ γ, f δ γ = if IsConj γ₀ γ then ((cl γ₀ : ℚ))⁻¹ else 0 := by
        intro γ
        simp only [f, hiff γ]
        split_ifs with hh
        · rw [hcl' γ hh]
        · rfl
      simp only [this]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcl_eq]
      exact mul_inv_cancel₀ (by exact_mod_cast (hcl_pos γ₀).ne')
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro γ _
      simp only [f]
      rw [if_neg (fun hh => h ⟨γ, hh⟩)]
  have h2 : ∀ γ, ∑ δ, f δ γ = (Nat.card (GL (Fin n) F') : ℚ) / Nat.card (GL (Fin n) F) := by
    intro γ
    simp only [f]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hcard]
    have hG : (0 : ℚ) < Nat.card (GL (Fin n) F) := by exact_mod_cast Nat.card_pos
    have hc : (0 : ℚ) < cl γ := by exact_mod_cast hcl_pos γ
    have hq : (Nat.card {δ : GL (Fin n) F' // IsNorm s δ γ} : ℚ) * Nat.card (GL (Fin n) F)
        = cl γ * Nat.card (GL (Fin n) F') := by exact_mod_cast hfib γ
    field_simp
    linarith [hq]
  have hsum : ∑ δ : GL (Fin n) F', (if ∃ γ, IsNorm s δ γ then (1 : ℚ) else 0) = ∑ δ : GL (Fin n) F', (1 : ℚ) := by
    simp only [← h1]
    rw [Finset.sum_comm]
    simp only [h2]
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have hG : (0 : ℚ) < Nat.card (GL (Fin n) F) := by exact_mod_cast Nat.card_pos
    field_simp
  have hle : ∀ δ ∈ (Finset.univ : Finset (GL (Fin n) F')),
      (if ∃ γ, IsNorm s δ γ then (1 : ℚ) else 0) ≤ 1 := by
    intro δ _
    split_ifs <;> norm_num
  have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum δ₀ (Finset.mem_univ _)
  by_contra hno
  rw [if_neg hno] at this
  norm_num at this

end GlobalTheory.Shin
end

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_element_is_norm : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (δ : GL (Fin n) F'), ∃ γ : GL (Fin n) F, IsNorm s δ γ := by
  first | (exact @GlobalTheory.Shin.exists_isNorm) | (exact GlobalTheory.Shin.exists_isNorm) | (intros; apply GlobalTheory.Shin.exists_isNorm  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEtAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEtAtPrime
open CategoryTheory Limits
open scoped TensorProduct

namespace GlobalTheory.IndEtFactorLoc

def constColim (R : Type) [CommRing R] :
    IsColimit (Cocone.mk (CommRingCat.of R)
      (𝟙 ((Functor.const (Discrete PUnit.{1})).obj (CommRingCat.of R)))) where
  desc c := c.ι.app ⟨⟨⟩⟩
  fac c j := by rcases j with ⟨⟨⟩⟩; simp
  uniq c m hm := by simpa using hm ⟨⟨⟩⟩

theorem exists_etale_factor_of_indEt_atPrime : ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (P : Ideal R) [P.IsPrime]
    (φ : Localization.AtPrime P →+* O), φ.comp (algebraMap R _) = algebraMap R O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
      (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g := by
  intro R O _ _ _ P _ φ hφ hind Z _ _ _ g
  let L := Localization.AtPrime P
  letI : Algebra L O := φ.toAlgebra
  haveI : IsScalarTower R L O :=
    IsScalarTower.of_algebraMap_eq (fun r => (congrArg (fun f => f r) hφ).symm)
  let g1 : L ⊗[R] Z →ₐ[L] O :=
    Algebra.TensorProduct.lift (Algebra.ofId L O) g (fun _ _ => Commute.all _ _)
  obtain ⟨C, _, _, _, ψ, χ, hψχ⟩ := GlobalTheory.EtC.exists_etale_factor_of_indEt L O hind (L ⊗[R] Z) g1
  let M := P.primeCompl
  let D0 := (Functor.const (Discrete PUnit.{1})).obj (CommRingCat.of R)
  let s0 : D0 ⟶ (Functor.const _).obj (CommRingCat.of R) := 𝟙 _
  have hs0 : IsColimit (Cocone.mk _ s0) := constColim R
  obtain ⟨j, Aj, _, instA, hAj, ⟨e⟩⟩ := GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit
    (GlobalTheory.IndEtaleLoc.Idx D0 s0 M) (GlobalTheory.IndEtaleLoc.diag D0 s0 M)
    (Cocone.mk _ (GlobalTheory.IndEtaleLoc.toLoc (s := s0) (M := M) L))
    (GlobalTheory.IndEtaleLoc.isColimitToLoc L hs0) C

  let Re : Type := Localization.Away j.e
  letI : Algebra R Re := (inferInstance : Algebra (D0.obj j.j) (Localization.Away j.e))
  letI : Algebra Re L := (GlobalTheory.IndEtaleLoc.leg L j).toAlgebra
  letI : Algebra Re Aj := instA
  haveI : Algebra.Etale Re Aj := hAj
  let e0 : R := j.e
  have he0 : e0 ∈ M := j.mem
  haveI : IsLocalization (Submonoid.powers e0) Re :=
    (inferInstance : IsLocalization (Submonoid.powers j.e) (Localization.Away j.e))
  haveI : IsScalarTower R Re L := IsScalarTower.of_algebraMap_eq (fun r =>
    (GlobalTheory.IndEtaleLoc.leg_algebraMap (s := s0) (M := M) L j r).symm)
  haveI hLoc : IsLocalization (M.map (algebraMap R Re)) L :=
    IsLocalization.isLocalization_of_submonoid_le Re L (Submonoid.powers e0) M
      (Submonoid.powers_le.2 he0)
  let e' : L ⊗[Re] Aj ≃ₐ[L] C := e
  letI rA : Algebra Aj (L ⊗[Re] Aj) := Algebra.TensorProduct.rightAlgebra
  haveI hT : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re)))
      (L ⊗[Re] Aj) := IsLocalization.tensorRight _ _
  letI : Algebra Aj C := (e'.toRingHom.comp (algebraMap Aj (L ⊗[Re] Aj))).toAlgebra
  let eA : L ⊗[Re] Aj ≃ₐ[Aj] C := AlgEquiv.ofRingEquiv (f := e'.toRingEquiv) (fun _ => rfl)
  haveI hCloc : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) C :=
    IsLocalization.isLocalization_of_algEquiv _ eA
  letI : Algebra R Aj := ((algebraMap Re Aj).comp (algebraMap R Re)).toAlgebra
  haveI : IsScalarTower R Re Aj := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale R Re :=
    (Algebra.Etale.of_isLocalizationAway j.e : Algebra.Etale (D0.obj j.j) (Localization.Away j.e))
  haveI : Algebra.Etale R Aj := Algebra.Etale.comp R Re Aj
  letI : Algebra R C := ((algebraMap L C).comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R Aj C := IsScalarTower.of_algebraMap_eq (fun r => by
    have key : ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r)) =
        algebraMap L (L ⊗[Re] Aj) (algebraMap R L r) := by
      rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply R Re L]
      generalize algebraMap R Re r = c
      rw [Algebra.algebraMap_eq_smul_one (A := Aj) c, Algebra.algebraMap_eq_smul_one (A := L) c,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rfl
    show algebraMap L C (algebraMap R L r) = e' ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r))
    rw [key, AlgEquiv.commutes])
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R C) :=
    GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization R Aj C
      (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) (GlobalTheory.EtC.indEt_of_etale R Aj)
  let ψ' : Z →ₐ[R] C := (ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight
  obtain ⟨W, _, _, _, u, v', huv⟩ := GlobalTheory.EtC.exists_etale_factor_of_indEt R C hC Z ψ'
  refine ⟨W, inferInstance, inferInstance, inferInstance, u, (χ.restrictScalars R).comp v', ?_⟩
  ext z
  have h1 := DFunLike.congr_fun huv z
  have h2 := DFunLike.congr_fun hψχ ((1 : L) ⊗ₜ[R] z)
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', ψ',
    Algebra.TensorProduct.includeRight_apply] at h1 h2 ⊢
  rw [h1, h2]
  simp [g1]

end GlobalTheory.IndEtFactorLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEtAtPrimeStatement
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_factorization_of_isIndEtale : ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (P : Ideal R) [P.IsPrime]
    (φ : Localization.AtPrime P →+* O), φ.comp (algebraMap R _) = algebraMap R O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
      (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g := by
  first | exact @GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime | exact GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime | (intros; apply GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFunctionalVanishesOnOmegaForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdZpowAdd
namespace GlobalTheory.ProductZpowAdd

theorem prod_zpow_add {F : Type} [inst : Field F] {d : ℕ} (x : Fin (d + 1) → F)
    (hx : ∀ i : Fin (d + 1), x i ≠ 0) (m n : Fin (d + 1) → ℤ) :
    ∏ j : Fin (d + 1), x j ^ (m j + n j)
      = (∏ j : Fin (d + 1), x j ^ m j) * ∏ j : Fin (d + 1), x j ^ n j := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => zpow_add₀ (hx j) _ _

end GlobalTheory.ProductZpowAdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFunctionalVanishesOnOmegaForms
set_option autoImplicit false
noncomputable section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.ResVan

variable {F : Type} [Field F] {d : ℕ}

theorem prod_zpow_add (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (m n : Fin (d + 1) → ℤ) :
    ∏ j, x j ^ (m j + n j) = (∏ j, x j ^ m j) * ∏ j, x j ^ n j := by
  first
  | exact @_root_.GlobalTheory.ProductZpowAdd.prod_zpow_add
  | exact _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add
  | (apply _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add ..)

def monoA (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (I : Finset (Fin (d + 1))) : Submonoid F where
  carrier := {f | ∃ m : Fin (d + 1) → ℤ, ∑ j, m j = 0 ∧ (∀ j ∉ I, 0 ≤ m j) ∧ f = ∏ j, x j ^ m j}
  one_mem' := ⟨0, by simp, fun _ _ => le_rfl, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨m, hm, hm', rfl⟩ ⟨n, hn, hn', rfl⟩
    refine ⟨m + n, ?_, fun j hj => add_nonneg (hm' j hj) (hn' j hj), ?_⟩
    · simp [Finset.sum_add_distrib, hm, hn]
    · simp only [Pi.add_apply]; exact (prod_zpow_add x hx m n).symm

theorem prod_single_sub (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (i j : Fin (d + 1)) :
    ∏ l, x l ^ ((Pi.single j 1 : Fin (d + 1) → ℤ) l - (Pi.single i 1 : Fin (d + 1) → ℤ) l) = x j / x i := by
  simp_rw [zpow_sub₀ (hx _)]
  rw [Finset.prod_div_distrib]
  congr 1
  · rw [Fintype.prod_eq_single j (fun l hl => by simp [Pi.single_apply, hl])]; simp
  · rw [Fintype.prod_eq_single i (fun l hl => by simp [Pi.single_apply, hl])]; simp

theorem prod_exp (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (i0 : Fin (d + 1)) :
    (∏ j, x j ^ ((1 : ℤ) - if j = i0 then ((d : ℤ) + 1) else 0)) * ∏ j, x i0 / x j = 1 := by
  simp_rw [zpow_sub₀ (hx _), zpow_one]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  have hq : ∏ j, x j ^ (if j = i0 then ((d : ℤ) + 1) else 0) = x i0 ^ (d + 1) := by
    rw [Fintype.prod_eq_single i0 (fun l hl => by simp [hl])]
    rw [if_pos rfl, show ((d : ℤ) + 1) = ((d + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hq]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h0 : ∏ j, x j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hx j
  have h1 := hx i0
  field_simp

theorem resvan : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x →
    ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∀ (i : Fin (d + 1)) (I : Finset (Fin (d + 1))), I.Nonempty → i ∉ I →
    ∀ y ∈ omA k x I, ρ y = 0 := by
  intro k _ F _ _ d x hx ρ hρ i I hI hi y hy
  obtain ⟨i0, hi0⟩ := hI
  have hne := hx.ne
  have hii0 : i ≠ i0 := fun h => hi (h ▸ hi0)
  have h1 : (∏ j, x i0 / x j) * y ∈ rA k x I := by
    have h2 := (Submodule.mem_iInf _).1 hy i0
    have h3 := (Submodule.mem_iInf _).1 h2 hi0
    simpa using h3
  have hz : (∏ j, x i0 / x j) * y ∈ Submodule.span k (monoA x hne I : Set F) := by
    rw [rA, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at h1
    refine Submodule.span_mono (Submonoid.closure_le.2 ?_) h1
    rintro _ ⟨i', hi', j, rfl⟩
    refine ⟨(Pi.single j 1 : Fin (d + 1) → ℤ) - Pi.single i' 1, by simp, fun l hl => ?_,
      (prod_single_sub x hne i' j).symm⟩
    have hl' : l ≠ i' := fun h => hl (h ▸ hi')
    simp only [Pi.sub_apply, Pi.single_apply, hl', if_false, sub_zero]
    split_ifs <;> omega
  have hP := prod_exp x hne i0
  have hy' : y = (∏ j, x j ^ ((1 : ℤ) - if j = i0 then ((d : ℤ) + 1) else 0)) * ((∏ j, x i0 / x j) * y) := by
    rw [← mul_assoc, hP, one_mul]
  rw [hy']
  generalize (∏ j, x i0 / x j) * y = z at hz
  induction hz using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m, hm, hm', rfl⟩ := hf
    rw [← prod_zpow_add x hne]
    refine hρ.2 _ ?_ ?_
    · rw [Finset.sum_add_distrib, hm, add_zero, Finset.sum_sub_distrib]
      simp
    · intro h0
      have := congrFun h0 i
      simp only [hii0, if_false, Pi.zero_apply] at this
      have := hm' i hi
      omega
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, map_add (f := _), ha, hb, add_zero]
  | smul c a _ ha => rw [mul_smul_comm, map_smul, ha, smul_zero]

end GlobalTheory.PD.ResVan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFunctionalVanishesOnOmegaFormsStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_functional_vanishes_on_omega_forms : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∀ (i : Fin (d + 1)) (I : Finset (Fin (d + 1))), I.Nonempty → i ∉ I → ∀ y ∈ omA k x I, ρ y = 0 := by
  first | (exact @GlobalTheory.PD.ResVan.resvan) | (exact GlobalTheory.PD.ResVan.resvan) | (intros; apply GlobalTheory.PD.ResVan.resvan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCofilteredLimitAffineEtaleOfIsStalk
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_cofiltered_limit_affine_etale_of_isStalk : ∀ (S : Scheme.{0}) (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → ∃ (I : Type) (_ : SmallCategory I) (_ : IsCofiltered I) (G : I ⥤ Over S) (π : (Functor.const I).obj (Over.mk s) ⟶ G), Nonempty (IsLimit (Cone.mk _ π)) ∧ ∀ i, IsAffine (G.obj i).left ∧ Etale (G.obj i).hom := by
  intro S O _ s hs
  obtain ⟨_, A, _, _, j, hj, hind, rfl⟩ := hs
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, het⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt A O hind
  let G : Jᵒᵖ ⥤ Over S :=
    { obj := fun k => Over.mk (Spec.map (D.obj k.unop).hom ≫ j)
      map := fun {k l} f => Over.homMk (Spec.map (D.map f.unop).right) (by
        dsimp
        rw [← Category.assoc, ← Spec.map_comp, Under.w])
      map_id := fun k => by ext1; simp
      map_comp := fun f g => by ext1; simp [Spec.map_comp] }
  let π : (Functor.const Jᵒᵖ).obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ j)) ⟶ G :=
    { app := fun k => Over.homMk (Spec.map (ι.app k.unop).right) (by
        dsimp [G]
        rw [← Category.assoc, ← Spec.map_comp, Under.w (ι.app k.unop)]
        rfl)
      naturality := fun k l f => by
        ext1
        change (𝟙 _ ≫ Spec.map (ι.app l.unop).right) = Spec.map (ι.app k.unop).right ≫ Spec.map (D.map f.unop).right
        rw [Category.id_comp, ← Spec.map_comp]
        congr 1
        have := congrArg (fun m => Under.Hom.right m) (ι.naturality f.unop)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Under.comp_right] at this
        exact this.symm }
  haveI : IsConnected J := IsFiltered.isConnected J
  haveI : IsConnected Jᵒᵖ := IsCofiltered.isConnected Jᵒᵖ
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, G, π, ⟨?_⟩, fun k => ⟨?_, ?_⟩⟩
  · apply isLimitOfReflects (Over.forget S)
    have h1 := isColimitOfPreserves (Under.forget (CommRingCat.of A)) hc
    have h2 := isLimitOfPreserves Scheme.Spec h1.op
    exact h2
  · dsimp [G]; infer_instance
  · dsimp [G]
    have : Etale (Spec.map (D.obj k.unop).hom) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 (het k.unop)
    infer_instance

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAt0EqSumOfSubset
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem derivAt0_eq_sum_of_subset {C : Type} [Field C] {σ : Type} (P : MvPolynomial σ C)
    (g : MvPowerSeries σ C) {s : Finset (σ →₀ ℕ)} (hs : P.support ⊆ s) :
    derivAt0 P g = ∑ α ∈ s, P.coeff α * mfact α * coeff α g := by
  unfold derivAt0
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.mp hα]
  simp

theorem derivAt0_linear (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (σ : Type) (P Q : MvPolynomial σ C) (g g' : MvPowerSeries σ C) (a : C) :
    derivAt0 P (g + g') = derivAt0 P g + derivAt0 P g' ∧
      derivAt0 P (a • g) = a * derivAt0 P g ∧
      derivAt0 (P + Q) g = derivAt0 P g + derivAt0 Q g ∧
      derivAt0 (a • P) g = a * derivAt0 P g ∧
      ((∀ α ∈ P.support, coeff α g = coeff α g') → derivAt0 P g = derivAt0 P g') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold derivAt0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_add (f := _), mul_add]
  · unfold derivAt0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_smul, smul_eq_mul]
    ring
  · classical
    rw [derivAt0_eq_sum_of_subset (P + Q) g (MvPolynomial.support_add (p := P) (q := Q)),
      derivAt0_eq_sum_of_subset P g (Finset.subset_union_left (s₂ := Q.support)),
      derivAt0_eq_sum_of_subset Q g (Finset.subset_union_right (s₁ := P.support)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_add]
    ring
  · rw [derivAt0_eq_sum_of_subset (a • P) g (MvPolynomial.support_smul (a := a) (f := P)),
      derivAt0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    ring
  · intro h
    unfold derivAt0
    exact Finset.sum_congr rfl fun α hα => by rw [h α hα]

end GlobalTheory.FGDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquiv
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.HInvIso

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  exact CategoryTheory.Functor.map_id _ _

theorem pull_spMap_bij {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : ∀ x, pull R (spMap (e : A →+* B)) F n (pull R (spMap (e.symm : B →+* A)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp']
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext a; simp
    rw [this, spMap_id', pull_id]
  have h2 : ∀ x, pull R (spMap (e.symm : B →+* A)) F n (pull R (spMap (e : A →+* B)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp']
    have : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by ext a; simp
    rw [this, spMap_id', pull_id]
  exact ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩

end GlobalTheory.EtC.HInvIso

namespace GlobalTheory.EtC


open HInvIso in
theorem hInv_of_ringEquiv : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B], (A ≃+* B) → HInv q A → HInv q B := by
  intro q _ A B _ _ e hA i n
  have hsq : (Polynomial.C : B →+* Polynomial B).comp (e : A →+* B) =
      ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B).comp Polynomial.C := by
    ext a; simp
  have hpull : ∀ x, pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n x) =
      pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n
        (pull (ZMod q) (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n x) := by
    intro x
    rw [← pull_comp, ← pull_comp, ← spMap_comp', ← spMap_comp', hsq]
  have hc : Function.Bijective ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) := by
    have : ((pull (ZMod q) (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
      (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)) =
      (pull (ZMod q) (spMap ((Polynomial.mapEquiv e : Polynomial A ≃+* Polynomial B) : Polynomial A →+* Polynomial B)) (tw q i) n) ∘
        (pull (ZMod q) (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n) := funext hpull
    rw [this]
    exact (pull_spMap_bij _ _ n).comp (hA i n)
  exact (Function.Bijective.of_comp_iff _ (pull_spMap_bij e _ n)).1 hc

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquivStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B], (A ≃+* B) → HInv q A → HInv q B := by
  first | exact @GlobalTheory.EtC.hInv_of_ringEquiv | exact GlobalTheory.EtC.hInv_of_ringEquiv | (intros; apply GlobalTheory.EtC.hInv_of_ringEquiv; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicWeylElementGenerateUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicWeylElementGenerateUnitary
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem mem_of_inCell {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (hP : sieg c ν ≤ U) (hw : weyl c ν ∈ U) {g : UG c (stdJ ν E)} (hg : InCell c g) : g ∈ U := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hg
  exact U.mul_mem (U.mul_mem (hP hp) hw) (hP hq)

theorem sieg_weyl_generate : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))),
    sieg c ν ≤ U → weyl c ν ∈ U → U = ⊤ := by
  intro F _ _ E _ _ c δ hE ν _ _ U hP hw
  classical
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_translate_inCell' F E c δ hE ν {1, g}
  have h1 : u ∈ U := by
    simpa using mem_of_inCell c U hP hw (hu 1 (by simp))
  have h2 : g * u ∈ U := mem_of_inCell c U hP hw (hu g (by simp))
  simpa using U.mul_mem h2 (U.inv_mem h1)

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicWeylElementGenerateUnitaryStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelParabolic_weylElement_generate_unitary : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))), sieg c ν ≤ U → weyl c ν ∈ U → U = ⊤ := by
  first | exact @GlobalTheory.KSp.sieg_weyl_generate | exact GlobalTheory.KSp.sieg_weyl_generate | (intros; apply GlobalTheory.KSp.sieg_weyl_generate <;> assumption)
end
end
