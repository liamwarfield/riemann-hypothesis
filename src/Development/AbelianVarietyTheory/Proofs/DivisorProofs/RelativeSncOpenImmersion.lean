module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeSncOpenImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenPullOpenImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenPullOpenImmersion
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPair

theorem isEtCoord_openImmersion (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X)
    [IsOpenImmersion e] (U : X.Opens) (W : Y.Opens) (h : W ≤ e ⁻¹ᵁ U) (d : ℕ) (t : Fin d → Γ(X, U)) :
    IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t →
      IsEtCoord (e ≫ f) W (fun a => (e.appLE U W h).hom (t a)) := by
  intro hU hW ht
  have hφ : (e.appLE U W h).hom.Etale := e.etale_appLE hU hW h
  have hc : (e.appLE U W h).hom.comp (cstOn f U) = cstOn (e ≫ f) W := by
    have e₁ : f.appLE ⊤ U le_top ≫ e.appLE U W h = (e ≫ f).appLE ⊤ W le_top :=
      Scheme.Hom.appLE_comp_appLE e f ⊤ U W le_top h
    have e₂ : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) ≫ e.appLE U W h =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (e ≫ f).appLE ⊤ W le_top := by
      rw [Category.assoc, e₁]
    exact congrArg CommRingCat.Hom.hom e₂
  unfold IsEtCoord
  rw [← hc, ← MvPolynomial.comp_eval₂Hom]
  exact RingHom.Etale.stableUnderComposition _ _ ht hφ

end GlobalTheory.LogPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenPullOpenImmersionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_pull_openImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X) [IsOpenImmersion e] (U : X.Opens) (W : Y.Opens) (h : W ≤ e ⁻¹ᵁ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord (e ≫ f) W (fun a => (e.appLE U W h).hom (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_openImmersion | exact GlobalTheory.LogPair.isEtCoord_openImmersion | (intros; apply GlobalTheory.LogPair.isEtCoord_openImmersion <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem relSnc_pull_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), RelSnc f d L σ → RelSnc (e ≫ f) d (fun i => (L i).pull e) (fun i => Cartier.secPull (σ i) e) := by
  intro R _ X Y f e _ d s L σ h
  refine ⟨fun i => LB.isLB_pull (h.isLB i) e, fun y => ?_⟩
  obtain ⟨C, hC⟩ := h.chart (e y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := y) (u := (e ⁻¹ᵁ C.U : Y.Opens)) hC
      (e ⁻¹ᵁ C.U).isOpen
  have hle : W ≤ e ⁻¹ᵁ C.U := hWV
  have hap : ∀ a : Γ(X, C.U), (e.appLE C.U W hle).hom a = resG Y hle ((e.app C.U).hom a) :=
    fun _ => rfl
  refine ⟨{ U := W
            affine := hW
            t := fun a => (e.appLE C.U W hle).hom (C.t a)
            etale := GlobalTheory.T.isEtaleCoordinatesOnOpen_pull_openImmersion R X Y f e C.U W hle d C.t C.affine hW C.etale
            c := fun i _ => C.c i
            le := fun i => (hle.trans (e.preimage_mono (C.le i))).trans
              (Cartier.pull_U (L i) e (fun _ => C.c i)).ge
            e := C.e
            inj := C.inj
            u := fun i => Units.map (e.appLE C.U W hle).hom.toMonoidHom (C.u i)
            eq := fun i => ?_ }, hyW⟩
  have h1 := congrArg (e.appLE C.U W hle).hom (C.eq i)
  rw [map_mul, hap, Cartier.app_resG, Cartier.resG_resG] at h1
  refine (Cartier.resG_resG _ _ _).trans (h1.trans ?_)
  congr 1
  cases C.e i with
  | none => exact map_one _
  | some a => rfl

end GlobalTheory.LogPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldCoordinatesDlog
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtCoordBasis

open KaehlerDifferential

theorem kaehler_map_bijective (p : ℕ) (L : Type) [CommRing L] [Algebra (ZMod p) L] :
    Function.Bijective (KaehlerDifferential.map ℤ (ZMod p) L L) := by
  refine ⟨?_, KaehlerDifferential.map_surjective ℤ (ZMod p) L⟩
  have hsurj : Function.Surjective (algebraMap ℤ (ZMod p)) := by
    intro x
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨m, by simp⟩
  have hs : Subsingleton Ω[ZMod p⁄ℤ] := KaehlerDifferential.subsingleton_of_surjective ℤ (ZMod p) hsurj
  have hex := KaehlerDifferential.exact_mapBaseChange_map ℤ (ZMod p) L
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hex x).1 hx
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Subsingleton.elim b 0]
  | add y z hy hz => rw [map_add (f := _), hy, hz, add_zero]

theorem etale_coords_basis : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (ht : ∀ j, algebraMap A L (t j) ≠ 0), IsCoord (fun j => Units.mk0 (algebraMap A L (t j)) (ht j)) ∧ ∀ f : A, ∃ c : Fin n → A, KaehlerDifferential.D ℤ L (algebraMap A L f) = ∑ j, algebraMap A L (c j) • KaehlerDifferential.D ℤ L (algebraMap A L (t j)) := by
  intro p _ A _ _ _ n t het L _ _ _ ht
  classical
  let P := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra P A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : IsScalarTower (ZMod p) P A :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval t).commutes r).symm
  haveI : Algebra.Etale P A := het
  letI : Algebra (ZMod p) L := ((algebraMap A L).comp (algebraMap (ZMod p) A)).toAlgebra
  haveI : IsScalarTower (ZMod p) A L := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors A)
  let bA : Module.Basis (Fin n) A Ω[A⁄ZMod p] :=
    ((mvPolynomialBasis (ZMod p) (Fin n)).baseChange A).map
      (tensorKaehlerEquivOfFormallyEtale (ZMod p) P A)
  have hbA : ∀ j, bA j = D (ZMod p) A (t j) := by
    intro j
    simp only [bA, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]
    have h : algebraMap P A (MvPolynomial.X j) = t j := by
      change MvPolynomial.aeval t (MvPolynomial.X j) = t j
      exact MvPolynomial.aeval_X t j
    rw [← h, ← map_D (ZMod p) (ZMod p) P A]
    exact (mapBaseChange_tmul (ZMod p) P A 1 _).trans (one_smul _ _)
  let bL : Module.Basis (Fin n) L Ω[L⁄ZMod p] :=
    (bA.baseChange L).map (tensorKaehlerEquivOfFormallyEtale (ZMod p) A L)
  have hbL : ∀ j, bL j = D (ZMod p) L (algebraMap A L (t j)) := by
    intro j
    simp only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, hbA, map_D]
  let e : Ω[L⁄ℤ] ≃ₗ[L] Ω[L⁄ZMod p] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map ℤ (ZMod p) L L) (kaehler_map_bijective p L)
  have he : ∀ x : L, e.symm (D (ZMod p) L x) = D ℤ L x := by
    intro x
    rw [LinearEquiv.symm_apply_eq]
    exact (KaehlerDifferential.map_D ℤ (ZMod p) L L x).symm
  let b : Module.Basis (Fin n) L Ω[L⁄ℤ] := bL.map e.symm
  have hb : ∀ j, b j = D ℤ L (algebraMap A L (t j)) := by
    intro j
    simp only [b, Module.Basis.map_apply, hbL, he]
  have hfun : (fun i => dK ((Units.mk0 (algebraMap A L (t i)) (ht i) : Lˣ) : L)) = ⇑b := by
    funext i
    simp [hb, dK]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hfun]; exact b.linearIndependent
  · rw [hfun]; exact b.span_eq
  · intro f
    refine ⟨bA.repr (D (ZMod p) A f), ?_⟩
    have h1 := bA.sum_repr (D (ZMod p) A f)
    rw [← he, ← map_D (ZMod p) (ZMod p) A L]
    conv_lhs => rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, hbA, map_D, ← algebraMap_smul L (bA.repr (D (ZMod p) A f) j), LinearEquiv.map_smul, he]

end GlobalTheory.EtCoordBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelOfPresents
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.Presents

variable {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ}

def genChart (h : Presents D L r) : L.ι := (exists_chart h.isLB (genericPoint X)).choose

theorem gen_mem_genChart (h : Presents D L r) : genericPoint X ∈ L.U h.genChart :=
  (exists_chart h.isLB (genericPoint X)).choose_spec

def secVal (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) : Γ(LB.toMod L, U) →+ X.functionField :=
  AddMonoidHom.mk' (fun s => fnOf _ (memInf hU h.gen_mem_genChart) (LB.coord s h.genChart) /
      (r h.genChart : X.functionField)) fun s t => by
    rw [LB.coord_add, map_add (f := _), add_div]

theorem secVal_apply (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(LB.toMod L, U)) :
    h.secVal U hU s = fnOf _ (memInf hU h.gen_mem_genChart) (LB.coord s h.genChart) /
      (r h.genChart : X.functionField) := rfl

theorem secVal_mul (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(LB.toMod L, U))
    (i : L.ι) (hi : genericPoint X ∈ U ⊓ L.U i) :
    h.secVal U hU s * r i = fnOf _ hi (LB.coord s i) := by
  have h₀ := h.gen_mem_genChart
  have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U h.genChart := ⟨hi, h₀⟩
  have e := congrArg (fnOf _ hW) (LB.coord_rel s i h.genChart
    (inf_le_left : U ⊓ L.U i ⊓ L.U h.genChart ≤ U ⊓ L.U i)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG] at e
  rw [e, secVal_apply, h.isRatSec i h.genChart (memInf hi.2 h₀), mul_left_comm]
  exact congrArg _ (div_mul_cancel₀ _ (Units.ne_zero _))

theorem secVal_injective (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) :
    Function.Injective (h.secVal U hU) := fun s t e =>
  LB.sec_ext fun i => fn_ext fun hi => by rw [← h.secVal_mul U hU s i hi, ← h.secVal_mul U hU t i hi, e]

theorem mem_range_secVal (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (f : X.functionField) :
    f ∈ (h.secVal U hU).range ↔ ∀ y ∈ U, D.RegularAt y f := by
  constructor
  · rintro ⟨s, rfl⟩ y hy
    obtain ⟨i, hi⟩ := exists_chart h.isLB y
    have hyi : y ∈ U ⊓ L.U i := ⟨hy, hi⟩
    refine (h.isEqn i y hi).regularAt_iff.2 ?_
    rw [h.secVal_mul U hU s i (gen_mem hyi)]
    exact regAt_fnOf hyi _ _
  · intro hf
    have key (i : L.ι) : ∃ a : Γ(X, U ⊓ L.U i), ∀ hi, fnOf _ hi a = f * r i := by
      by_cases hi : genericPoint X ∈ U ⊓ L.U i
      · obtain ⟨a, ha⟩ := exists_fnOf_eq hi fun x hx =>
          (h.isEqn i x hx.2).regularAt_iff.1 (hf x hx.1)
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h' => (hi h').elim⟩
    choose a ha using key
    have hmem : a ∈ secOn L U := fun i j => fn_ext fun hij => by
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, ha, ha,
        h.isRatSec i j (memInf hij.1.2 hij.2), mul_left_comm]
    refine ⟨LB.mkSec a hmem, ?_⟩
    rw [secVal_apply, LB.coord_mkSec, ha]
    exact mul_div_cancel_right₀ _ (Units.ne_zero _)

def latModel (h : Presents D L r) :
    LatModel (V := X.functionField) (fun y => (D.secOn {y}).toAddSubgroup) (LB.toMod L) where
  val := h.secVal
  inj := h.secVal_injective
  range U hU := by
    ext f
    rw [h.mem_range_secVal U hU f]
    simp only [latSec, AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, CartierDiv.mem_secOn,
      Set.mem_singleton_iff, forall_eq]
  res U W e hW s := by
    rw [secVal_apply, secVal_apply, LB.coord_map, fnOf_resG]
  smul U hU a s := by
    rw [secVal_apply, secVal_apply, LB.coord_smul, map_mul, fnOf_resG, smul_eq_mul, mul_div_assoc]

end GlobalTheory.Cartier.Presents

theorem GlobalTheory.Cartier.nonempty_latModel_of_presents : ∀ (X : Scheme.{0}) [IsIntegral X] (D : CartierDiv X) (L : LB X)
    (r : L.ι → X.functionFieldˣ), Presents D L r →
    Nonempty (LatModel (V := X.functionField) (fun y => (D.secOn {y}).toAddSubgroup) (LB.toMod L)) :=
  fun _ _ _ _ _ h => ⟨h.latModel⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelUniqueInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

variable {X : Scheme.{0}} [IsIntegral X]

theorem latSec_map {V V' : Type} [AddCommGroup V] [AddCommGroup V'] (M : X → AddSubgroup V)
    (φ : V →+ V') (hφ : Function.Injective φ) (U : X.Opens) (h : genericPoint X ∈ U) :
    (latSec M U).map φ = latSec (fun y => (M y).map φ) U := by
  ext w
  simp only [latSec, AddSubgroup.mem_map, AddSubgroup.mem_iInf]
  constructor
  · rintro ⟨v, hv, rfl⟩ y hy
    exact ⟨v, hv y hy, rfl⟩
  · intro hw
    obtain ⟨v, -, hv⟩ := hw _ h
    refine ⟨v, fun y hy => ?_, hv⟩
    obtain ⟨u, hu, hu'⟩ := hw y hy
    rwa [hφ (hu'.trans hv.symm)] at hu

def LatModel.mapLin {V V' : Type} [AddCommGroup V] [Module X.functionField V] [AddCommGroup V']
    [Module X.functionField V'] {M : X → AddSubgroup V} {F : X.Modules} (L : LatModel M F)
    (φ : V →ₗ[X.functionField] V') (hφ : Function.Injective φ) :
    LatModel (fun y => (M y).map φ.toAddMonoidHom) F where
  val U h := φ.toAddMonoidHom.comp (L.val U h)
  inj U h := hφ.comp (L.inj U h)
  range U h := by
    rw [AddMonoidHom.range_comp, L.range U h]
    exact latSec_map M φ.toAddMonoidHom hφ U h
  res U W e h s := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, L.res U W e h s]
  smul U h r s := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, L.smul U h r s, LinearMap.toAddMonoidHom_coe,
      LinearMap.map_smul]

def LatModel.transfer {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) (h : genericPoint X ∈ U)
    (s : Γ(F, U)) : Γ(F', U) :=
  Classical.choose (show L.val U h s ∈ (L'.val U h).range by
    rw [L'.range U h, ← L.range U h]; exact ⟨s, rfl⟩)

theorem LatModel.val_transfer {V : Type} [AddCommGroup V] [Module X.functionField V]
    {M : X → AddSubgroup V} {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(F, U)) : L'.val U h (L.transfer L' U h s) = L.val U h s :=
  Classical.choose_spec (show L.val U h s ∈ (L'.val U h).range by
    rw [L'.range U h, ← L.range U h]; exact ⟨s, rfl⟩)

def LatModel.secEquiv {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) (h : genericPoint X ∈ U) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F', U) where
  toFun := L.transfer L' U h
  map_add' s t := L'.inj U h (by simp only [map_add (f := _), LatModel.val_transfer])
  map_smul' r s := L'.inj U h (by
    simp only [RingHom.id_apply, LatModel.val_transfer, L'.smul U h, L.smul U h])
  invFun := L'.transfer L U h
  left_inv s := L.inj U h (by simp only [LatModel.val_transfer])
  right_inv s := L'.inj U h (by simp only [LatModel.val_transfer])

theorem LatModel.val_secEquiv {V : Type} [AddCommGroup V] [Module X.functionField V]
    {M : X → AddSubgroup V} {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(F, U)) : L'.val U h (L.secEquiv L' U h s) = L.val U h s :=
  L.val_transfer L' U h s

theorem subsingleton_sec_of_not_gen (F : X.Modules) {U : X.Opens} (hU : genericPoint X ∉ U) :
    Subsingleton Γ(F, U) := by
  haveI : Subsingleton Γ(X, U) := ⟨fun a b => fn_ext fun h => absurd h hU⟩
  exact Module.subsingleton Γ(X, U) Γ(F, U)


open Classical in
def LatModel.secEquiv' {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') (U : X.Opens) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F', U) :=
  if h : genericPoint X ∈ U then L.secEquiv L' U h else
    haveI := subsingleton_sec_of_not_gen F h
    haveI := subsingleton_sec_of_not_gen F' h
    LinearEquiv.ofSubsingleton _ _

def LatModel.iso {V : Type} [AddCommGroup V] [Module X.functionField V] {M : X → AddSubgroup V}
    {F F' : X.Modules} (L : LatModel M F) (L' : LatModel M F') : F ≅ F' :=
  GlobalTheory.LB.isoOfLinear (L.secEquiv' L') fun {U W} e s => by
    by_cases hW : genericPoint X ∈ W
    · have hU : genericPoint X ∈ U := e hW
      apply L'.inj W hW
      simp only [LatModel.secEquiv', dif_pos hW, dif_pos hU]
      rw [L.val_secEquiv L' W hW, L'.res U W e hW, L.res U W e hW, L.val_secEquiv L' U hU]
    · haveI := subsingleton_sec_of_not_gen F' hW
      exact Subsingleton.elim _ _

theorem latModel_map_and_unique : ∀ (X : Scheme.{0}) [IsIntegral X] {V V' : Type} [AddCommGroup V] [Module X.functionField V] [AddCommGroup V'] [Module X.functionField V'] (M : X → AddSubgroup V) (F F' : X.Modules) (φ : V →ₗ[X.functionField] V'), Function.Injective φ → LatModel M F → (Nonempty (LatModel (fun y => (M y).map φ.toAddMonoidHom) F)) ∧ (LatModel M F' → Nonempty (F ≅ F')) := by
  intro X _ V V' _ _ _ _ M F F' φ hφ L
  exact ⟨⟨L.mapLin φ hφ⟩, fun L' => ⟨L.iso L'⟩⟩

end GlobalTheory.LogDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalBundleOpenRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace CanonLB

open TopForm LB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {R : Type} [CommRing R] {X Y : Scheme.{0}} {f : X ⟶ Sp R} (e : Y ⟶ X) [IsOpenImmersion e]
  {d : ℕ} [SmoothOfRelativeDimension d f]

theorem comp_spMap_id (f : X ⟶ Sp R) : e ≫ f = (e ≫ f) ≫ spMap (RingHom.id R) := by
  simp [spMap]

theorem isFrame_pullForm_openImm {U : X.Opens} {ω : FormsOn f d U} (hω : IsFrame ω)
    {W : Y.Opens} (hW : IsAffineOpen W) (h : W ≤ e ⁻¹ᵁ U) :
    IsFrame (pullForm (comp_spMap_id e f) h ω) := by
  have hle : e ''ᵁ W ≤ U := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h hy
  have h' : W ≤ e ⁻¹ᵁ (e ''ᵁ W) := (e.preimage_image_eq W).ge
  have hω' : IsFrame (resForm hle ω) := hω.res (hW.image_of_isOpenImmersion e) hle
  have key : pullForm (comp_spMap_id e f) h ω = pullForm (comp_spMap_id e f) h' (resForm hle ω) := by
    rw [pullForm_resForm]
  rw [key]
  have hiso : IsIso (e.appLE (e ''ᵁ W) W h') := by
    have : e.appLE (e ''ᵁ W) W h' = (e.appIso W).hom := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]
      rfl
    rw [this]
    infer_instance
  have sq := appLE_comp_algX (comp_spMap_id e f) h'
  haveI : IsIso (CommRingCat.ofHom (e.appLE (e ''ᵁ W) W h').hom) := by
    simpa using hiso
  haveI : IsIso (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id]
    infer_instance
  have H : IsPushout (CommRingCat.ofHom (algX f (e ''ᵁ W))) (CommRingCat.ofHom (RingHom.id R))
      (CommRingCat.ofHom (e.appLE (e ''ᵁ W) W h').hom) (CommRingCat.ofHom (algX (e ≫ f) W)) := by
    refine IsPushout.of_vert_isIso ⟨?_⟩
    ext x
    exact RingHom.congr_fun sq x
  exact ⟨hW, hω'.gen.formMapSq (RingHom.id R) (e.appLE (e ''ᵁ W) W h').hom sq H⟩

abbrev OIdx (e : Y ⟶ X) (K : CanonLB f d) : Type :=
  Σ i : K.bundle.ι, {W : Y.Opens // IsAffineOpen W ∧ W ≤ e ⁻¹ᵁ K.bundle.U i}

def oBundle (e : Y ⟶ X) (K : CanonLB f d) : LB Y :=
  ZH.UFib.refinePull K.bundle e (fun a : OIdx e K => a.2.1) (fun a => a.1) (fun a => a.2.2.2)

theorem resG_oBundle_g (K : CanonLB f d) (a b : OIdx e K)
    {W : Y.Opens} (h : W ≤ (oBundle e K).U a ⊓ (oBundle e K).U b) :
    resG Y h ((oBundle e K).g a b : Γ(Y, (oBundle e K).U a ⊓ (oBundle e K).U b)) =
      (e.appLE (K.bundle.U a.1 ⊓ K.bundle.U b.1) W
        (h.trans (fun _ hy => ⟨a.2.2.2 hy.1, b.2.2.2 hy.2⟩))).hom
          ((K.bundle.g a.1 b.1 : Γ(X, K.bundle.U a.1 ⊓ K.bundle.U b.1))) := by
  simp only [oBundle, ZH.UFib.refinePull, res, pullU, Units.coe_map, MonoidHom.coe_coe]
  erw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  simp only [Scheme.Hom.appLE, Category.assoc, resG]
  rw [← Functor.map_comp]
  rfl

theorem iSup_oIdx (K : CanonLB f d) : ⨆ a : OIdx e K, a.2.1 = ⊤ :=
  eq_top_iff.2 fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart K.isLB (e y)
    obtain ⟨W, hW, hy, hsub⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := e ⁻¹ᵁ K.bundle.U i) hi
    exact Opens.mem_iSup.2 ⟨⟨i, W, hW, fun z hz => hsub hz⟩, hy⟩

def oChartPull (K : CanonLB f d) : ChartPull (oBundle e K) K.bundle e where
  idx a := a.1
  le a := a.2.2.2
  g y a b h h' := ZH.UFib.gm_refinePull K.bundle e (fun a : OIdx e K => a.2.1) (fun a => a.1)
    (fun a => a.2.2.2) y a b h h'

variable [SmoothOfRelativeDimension d (e ≫ f)]

theorem resForm_pullForm_om (K : CanonLB f d) (a b : OIdx e K) {W : Y.Opens} (hW : IsAffineOpen W)
    (ha : W ≤ a.2.1) (hb : W ≤ b.2.1) (h : W ≤ e ⁻¹ᵁ (K.bundle.U a.1 ⊓ K.bundle.U b.1)) :
    resForm hb (pullForm (comp_spMap_id e f) b.2.2.2 (K.om b.1)) =
      (e.appLE (K.bundle.U a.1 ⊓ K.bundle.U b.1) W h).hom
          ((K.bundle.g a.1 b.1 : Γ(X, K.bundle.U a.1 ⊓ K.bundle.U b.1))) •
        resForm ha (pullForm (comp_spMap_id e f) a.2.2.2 (K.om a.1)) := by
  have hfa := isFrame_pullForm_openImm e (K.isFrame a.1) a.2.2.1 a.2.2.2
  have h₁ := (K.isFrame a.1).coeff_pullForm (comp_spMap_id e f) a.2.2.2 hfa inf_le_left ha h
    (resForm inf_le_right (K.om b.1))
  rw [pullForm_resForm] at h₁
  rw [g_eq_ratio, resForm_pullForm]
  exact (hfa.coeff_smul_resForm hW ha _).symm.trans (congrArg (· • _) h₁)

def openImm (K : CanonLB f d) : CanonLB (e ≫ f) d where
  bundle := oBundle e K
  isLB := ZH.UFib.refinePull_isLB K.bundle K.isLB e _ _ _ (iSup_oIdx e K)
  affine a := a.2.2.1
  om a := pullForm (comp_spMap_id e f) a.2.2.2 (K.om a.1)
  gen a := (isFrame_pullForm_openImm e (K.isFrame a.1) a.2.2.1 a.2.2.2).gen
  trans a b W hW ha hb := by
    have h : W ≤ e ⁻¹ᵁ (K.bundle.U a.1 ⊓ K.bundle.U b.1) :=
      le_inf (ha.trans a.2.2.2) (hb.trans b.2.2.2)
    exact (resForm_pullForm_om e K a b hW ha hb h).trans
      (congrArg (· • _) (resG_oBundle_g e K a b (le_inf ha hb)).symm)

end CanonLB

theorem cls_canonLB_openImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R)
    (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) [SmoothOfRelativeDimension d f]
    [SmoothOfRelativeDimension d (e ≫ f)] (K : CanonLB f d) (K' : CanonLB (e ≫ f) d),
    cls K'.bundle K'.isLB = CechPic.pull e (cls K.bundle K.isLB) := by
  intro R _ X Y f e _ d _ _ K K'
  have hp : (K.bundle.pull e).IsLB := Semi.LB.isLB_linComb K.isLB _ _
  calc cls K'.bundle K'.isLB = cls (K.openImm e).bundle (K.openImm e).isLB :=
        (cls_eq_iff _ _).2 (K'.lbIso (K.openImm e))
    _ = cls (K.bundle.pull e) hp :=
        (cls_eq_iff _ _).2 (LBIso.chartPull (K.oChartPull e)
          (Geo.Tor.chartPullPull K.bundle e e rfl) (K.lbIso K))
    _ = CechPic.pull e (cls K.bundle K.isLB) := cls_pull K.isLB e hp

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentFrameFormsBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentFrameFormsBaseChange
set_option autoImplicit false

noncomputable section

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative

namespace GlobalTheory.BaseChangeIndep

theorem indep_pi {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {L : Type} [Field L] (emb : O →+* L)
    (hemb : Function.Injective emb) {M V : Type} [AddCommGroup M] [Module O M] [AddCommGroup V] [Module L V]
    (b : M →ₛₗ[emb] V) (hbinj : Function.Injective b)
    (hb : ∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent L fun a => b (x a))
    {T : Type} [Finite T] (n : ℕ) (y : Fin n → T → M) (hy : LinearIndependent O y) :
    LinearIndependent L fun a t => b (y a t) := by
  classical
  haveI : Fintype T := Fintype.ofFinite T

  haveI : Module.IsTorsionFree O M := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r m h
    have h1 : emb r • b m = 0 := by rw [← LinearMap.map_smulₛₗ, h, map_zero]
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (hemb (by rw [h2, map_zero]))
    · exact Or.inr (hbinj (by rw [h2, map_zero]))

  let P : Submodule O M := Submodule.span O (Set.range fun p : Fin n × T => y p.1 p.2)
  haveI : Module.Finite O P := Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range _))
  haveI : Module.Free O P := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis O P
  let k := Module.finrank O P
  have hmem : ∀ a t, y a t ∈ P := fun a t => Submodule.subset_span ⟨(a, t), rfl⟩
  have he : LinearIndependent O fun i => ((e i : P) : M) :=
    e.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hbe : LinearIndependent L fun i => b (e i : M) := by
    have := hb k (fun i => (e i : M)) he
    exact this

  let Y : Fin n → T × Fin k → O := fun a p => e.repr ⟨y a p.1, hmem a p.1⟩ p.2
  let Φ : (T × Fin k → O) →ₗ[O] (T → M) :=
    { toFun := fun Z t => ∑ i, Z (t, i) • ((e i : P) : M)
      map_add' := by
        intro Z Z'; funext t; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c Z; funext t; simp [smul_smul, Finset.smul_sum] }
  have hΦ : ∀ a, Φ (Y a) = y a := by
    intro a; funext t
    have h2 : ((∑ i, e.repr ⟨y a t, hmem a t⟩ i • e i : P) : M) = y a t := by rw [e.sum_repr]
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    change ∑ i, Y a (t, i) • ((e i : P) : M) = y a t
    exact h2
  have hY : LinearIndependent O Y := by
    apply LinearIndependent.of_comp Φ
    have : (Φ ∘ Y) = y := funext hΦ
    rw [this]; exact hy
  letI : Algebra O L := emb.toAlgebra
  haveI : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 hemb
  have hY' : LinearIndependent L fun a => algebraMap O L ∘ Y a :=
    linearIndependent_algebraMap_comp_iff.2 hY
  let Ψ : (T × Fin k → L) →ₗ[L] (T → V) :=
    { toFun := fun Z t => ∑ i, Z (t, i) • b (e i : M)
      map_add' := by
        intro Z Z'; funext t; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c Z; funext t; simp [smul_smul, Finset.smul_sum] }
  have hΨ : LinearMap.ker Ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro Z hZ
    funext p
    have h1 : ∑ i, Z (p.1, i) • b (e i : M) = 0 := congrFun hZ p.1
    have := (Fintype.linearIndependent_iff.1 hbe) (fun i => Z (p.1, i)) h1 p.2
    simpa using this
  have key := hY'.map' Ψ hΨ
  have hfam : (Ψ ∘ fun a => algebraMap O L ∘ Y a) = fun a t => b (y a t) := by
    funext a t
    change ∑ i, (algebraMap O L (Y a (t, i))) • b (e i : M) = b (y a t)
    rw [← hΦ a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sum, LinearMap.map_smulₛₗ]
    rfl
  rw [hfam] at key
  exact key

end GlobalTheory.BaseChangeIndep

namespace GlobalTheory.BaseChangeIndep

theorem forms_indep : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ)
    (jK : F.K →* alg F.O N mu) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu), Function.Injective b → F.Ok →
    (∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a)) →
    ∀ (n : ℕ) (x : Fin n → Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)), LinearIndependent F.O x →
      LinearIndependent (PadicAlgCl l) fun a => (fun g => b ((x a : F.G → NablaT F.O N mu) g)) := by
  intro l _ ι _ _ N F mu jK b hbinj hOk hb n x hx
  obtain ⟨S, hS⟩ := hOk.classes
  let R : Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu) →ₗ[F.O] (S → NablaT F.O N mu) :=
    { toFun := fun f s => (f : F.G → NablaT F.O N mu) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : LinearMap.ker R = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf0
    apply Subtype.ext
    funext g
    obtain ⟨γ, hγ, s, hs, κ, hκ, rfl⟩ := hS g
    have hf : ∀ (γ : F.Γ) (g : F.G) (κ : F.K), (f : F.G → NablaT F.O N mu) ((γ : F.G) * g * κ) =
        repOf F.O (A := alg F.O N mu) jK (NablaT F.O N mu) κ⁻¹ ((f : F.G → NablaT F.O N mu) g) := f.2
    have h0 : (f : F.G → NablaT F.O N mu) s = 0 := congrFun hf0 ⟨s, hs⟩
    have h1 := hf ⟨γ, hγ⟩ s ⟨κ, hκ⟩
    rw [h1, h0, map_zero]
    rfl
  have hx' : LinearIndependent F.O (R ∘ x) := hx.map' R hR
  have hOk1 := hOk.ring.1
  have key := indep_pi F.emb hOk1 b hbinj hb n (R ∘ x) hx'
  let R' : (F.G → NablaT (PadicAlgCl l) N mu) →ₗ[PadicAlgCl l] (S → NablaT (PadicAlgCl l) N mu) :=
    { toFun := fun f s => f s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply LinearIndependent.of_comp R'
  exact key

end GlobalTheory.BaseChangeIndep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentFrameFormsBaseChangeStatement
open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_frameForms_baseChange : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu) (b : NablaT F.O N mu →ₛₗ[F.emb] NablaT (PadicAlgCl l) N mu), Function.Injective b → F.Ok → (∀ (n : ℕ) (x : Fin n → NablaT F.O N mu), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => b (x a)) → ∀ (n : ℕ) (x : Fin n → Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)), LinearIndependent F.O x → LinearIndependent (PadicAlgCl l) fun a => (fun g => b ((x a : F.G → NablaT F.O N mu) g)) := by
  first | exact @GlobalTheory.BaseChangeIndep.forms_indep | exact GlobalTheory.BaseChangeIndep.forms_indep | (intros; apply GlobalTheory.BaseChangeIndep.forms_indep <;> assumption)
end
end
