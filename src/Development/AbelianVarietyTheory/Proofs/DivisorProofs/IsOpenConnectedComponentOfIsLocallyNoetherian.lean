module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.ConnOpen

theorem isOpen_connectedComponent_noetherian {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y] (y : Y) :
    IsOpen (connectedComponent y) := by
  set C := connectedComponent y
  have key : ∀ t, t ∉ C → irreducibleComponent t ⊆ Cᶜ := by
    intro t ht s hs hsC
    have h1 : irreducibleComponent t ⊆ connectedComponent s :=
      _root_.IsPreconnected.subset_connectedComponent
        (isIrreducible_irreducibleComponent (x := t)).isConnected.isPreconnected hs
    rw [← connectedComponent_eq hsC] at h1
    exact ht (h1 mem_irreducibleComponent)
  have hC : Cᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents Y | Z ⊆ Cᶜ}, Z := by
    ext t
    refine ⟨fun ht => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents t, key t ht⟩
      mem_irreducibleComponent, fun ht => ?_⟩
    obtain ⟨Z, ⟨-, hZ⟩, htZ⟩ := Set.mem_iUnion₂.1 ht
    exact hZ htZ
  have hcl : IsClosed Cᶜ := by
    rw [hC]
    exact (NoetherianSpace.finite_irreducibleComponents.subset (by exact fun _ h => h.1)).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  exact isClosed_compl_iff.1 hcl

end GlobalTheory.ConnOpen

theorem GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian :
    ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by
  intro X hX x
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := y) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let y' : (U : Set X) := ⟨y, hyU⟩
  refine ⟨Subtype.val '' connectedComponent y', ?_,
    U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ (GlobalTheory.ConnOpen.isOpen_connectedComponent_noetherian y'),
    ⟨y', mem_connectedComponent, rfl⟩⟩
  have hc : _root_.IsPreconnected (Subtype.val '' connectedComponent y' : Set X) :=
    isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have := hc.subset_connectedComponent ⟨y', mem_connectedComponent, rfl⟩
  rwa [← connectedComponent_eq hy] at this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem exists_idempotent_basicOpen_eq_of_isClopen :
    ∀ (X : Scheme.{0}) (U : Set X), IsClopen U →
      ∃ e : Γ(X, ⊤), e * e = e ∧ ((X.basicOpen e : X.Opens) : Set X) = U := by
  intro X U hU
  let O : Bool → X.Opens := fun i => bif i then ⟨U, hU.isOpen⟩ else ⟨Uᶜ, hU.isClosed.isOpen_compl⟩
  have hd : O true ⊓ O false = ⊥ := by
    ext x
    simp [O]
  have hcov : (⊤ : X.Opens) ≤ ⨆ i, O i := fun x _ => by
    by_cases hx : x ∈ U
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, hx⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, hx⟩
  let sf : ∀ i, Γ(X, O i) := fun i => bif i then 1 else 0
  have sub : ∀ T : X.Opens, T = ⊥ → Subsingleton Γ(X, T) := fun T hT => by
    subst hT; infer_instance
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 O sf := by
    intro i j
    cases i <;> cases j
    · exact (map_zero _).trans (map_zero _).symm
    · exact (sub _ ((inf_comm _ _).trans hd)).elim _ _
    · exact (sub _ hd).elim _ _
    · exact (map_one _).trans (map_one _).symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' O ⊤ (fun i => homOfLE le_top) hcov sf hcompat
  obtain ⟨t, hs'⟩ : ∃ t : Γ(X, ⊤), ∀ i, X.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op t = sf i :=
    ⟨s, hs⟩
  clear hs s
  refine ⟨t, ?_, ?_⟩
  · refine X.sheaf.eq_of_locally_eq' O ⊤ (fun i => homOfLE le_top) hcov (t * t) t fun i => ?_
    have e1 : X.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op (t * t) = sf i * sf i := by
      rw [map_mul, hs' i]
    refine e1.trans (Eq.trans ?_ (hs' i).symm)
    cases i
    · exact mul_zero _
    · exact mul_one _
  · have h1 : O true ⊓ X.basicOpen t = O true := by
      rw [← Scheme.basicOpen_res, hs' true]
      exact X.basicOpen_of_isUnit isUnit_one
    have h0 : O false ⊓ X.basicOpen t = ⊥ := by
      rw [← Scheme.basicOpen_res, hs' false]
      exact X.basicOpen_zero _
    ext x
    constructor
    · intro hx
      by_contra hxU
      have : x ∈ O false ⊓ X.basicOpen t := ⟨hxU, hx⟩
      rw [h0] at this
      exact this
    · intro hx
      have : x ∈ O true := hx
      rw [← h1] at this
      exact this.2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
noncomputable section

namespace GlobalTheory.HTRho

variable {k H O C : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

def mSub (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H) : Submodule k H :=
  Submodule.span k {z | ∃ c : C, ∃ x ∈ X, z = σ (algebraMap C O c) x - χ c • x}

def jSub {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H) : Submodule k H :=
  Submodule.span k {z | ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → C) (x : H), x ∈ X ∧
    (∀ i, ∑ l, lam l * χ i (c l) = 0) ∧ z = ∑ l, lam l • σ (algebraMap C O (c l)) x}

def homO {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) : Submodule k (X →ₗ[k] Y) where
  carrier := {T | ∀ a, T ∘ₗ σX a = σY a ∘ₗ T}
  zero_mem' a := by simp
  add_mem' {S T} hS hT a := by rw [LinearMap.add_comp, LinearMap.comp_add, hS a, hT a]
  smul_mem' c T hT a := by rw [LinearMap.smul_comp, LinearMap.comp_smul, hT a]

theorem mem_homO {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) (T : X →ₗ[k] Y) :
    T ∈ homO σX σY ↔ ∀ a x, T (σX a x) = σY a (T x) := by
  simp only [homO, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    LinearMap.ext_iff, LinearMap.comp_apply]

def rAct (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X) :
    O →+* Module.End k X where
  toFun a := (σ a).restrict (h a)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def qAct (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X) :
    O →+* Module.End k (H ⧸ X) where
  toFun a := X.mapQ X (σ a) (fun x hx => h a x hx)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem qAct_mk (σ : O →+* Module.End k H) (X : Submodule k H) (h : ∀ a, ∀ x ∈ X, σ a x ∈ X)
    (a : O) (x : H) : qAct σ X h a (X.mkQ x) = X.mkQ (σ a x) := rfl

theorem mSub_stable (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : ∀ a, ∀ x ∈ mSub σ χ X, σ a x ∈ mSub σ χ X := by
  intro a x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, y, hy, rfl⟩ := hz
    refine Submodule.subset_span ⟨c, σ a y, hX a y hy, ?_⟩
    rw [map_sub, map_smul, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul,
      Algebra.commutes]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem jSub_stable {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : ∀ a, ∀ x ∈ jSub σ χ X, σ a x ∈ jSub σ χ X := by
  intro a x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, lam, c, y, hy, hc, rfl⟩ := hz
    refine Submodule.subset_span ⟨r, lam, c, σ a y, hX a y hy, hc, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, Algebra.commutes]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem qAct_mSub_algebraMap (σ : O →+* Module.End k H) (χ : C →+* k) (c : C) :
    qAct σ (mSub σ χ ⊤) (mSub_stable σ χ ⊤ (fun _ _ _ => trivial)) (algebraMap C O c) = χ c • 1 := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  change (mSub σ χ ⊤).mkQ (σ (algebraMap C O c) x) = χ c • (mSub σ χ ⊤).mkQ x
  rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨c, x, trivial, rfl⟩

end GlobalTheory.HTRho
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
noncomputable section

open Matrix

namespace GlobalTheory.HeisLatVac


open Classical in
def vacFn {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K) : (κ → K) → ℂ := by
  classical
  exact fun x => if h : ∃ u ∈ Λ, x = x₀ + u.1 then
    χ h.choose * ψ₀ (-(x₀ ⬝ᵥ h.choose.2) - ⅟(2 : K) * (h.choose.1 ⬝ᵥ h.choose.2)) else 0

end GlobalTheory.HeisLatVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
noncomputable section
open scoped TensorProduct

namespace GlobalTheory.LKInvGood

def locOrder (ℓ : ℕ) [Fact ℓ.Prime] {B : Type} [Ring B] [Algebra ℚ B] (OB : Subring B) :
    Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) :=
  Algebra.adjoin ℤ_[ℓ] ((fun b : B => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' (OB : Set B))

def cenOrder (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [NumberField F] :
    Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) :=
  Algebra.adjoin ℤ_[ℓ] (Set.range fun a : NumberField.RingOfIntegers F => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F))

def cenMap (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] : ℚ_[ℓ] ⊗[ℚ] F →ₐ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] B :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) ((Algebra.ofId F B).restrictScalars ℚ)

def CentreCompat (ℓ : ℕ) [Fact ℓ.Prime] {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (OB : Subring B) {n : ℕ}
    (ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F)) : Prop :=
  ∀ a : cenOrder ℓ F, ∃ h : cenMap ℓ F B (a : ℚ_[ℓ] ⊗[ℚ] F) ∈ locOrder ℓ OB,
    ψ ⟨_, h⟩ = Matrix.scalar (Fin n) a

end GlobalTheory.LKInvGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBound
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.DimCodim

section

attribute [local instance low] specializationOrder

theorem dim_add_le_of_le_coheight {S W : Type*} [TopologicalSpace S] [TopologicalSpace W]
    [QuasiSober S] [T0Space S] [QuasiSober W] [T0Space W] {j : W → S} (hj : Continuous j)
    (hi : Function.Injective j) (c : ℕ∞) (h : ∀ w, c ≤ Order.coheight (j w)) :
    topologicalKrullDim W + c ≤ topologicalKrullDim S := by
  have hmono : StrictMono j := by
    intro x y hxy
    refine lt_of_le_of_ne ?_ (fun hxy' => hxy.ne (hi hxy'))
    exact (show y ⤳ x from hxy.le).map hj
  rw [topologicalKrullDim, topologicalKrullDim,
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := W)),
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := S))]
  rcases isEmpty_or_nonempty W with hW | hW
  · rw [Order.krullDim_eq_bot]
    simp
  · have : Nonempty S := ⟨j hW.some⟩
    rw [Order.krullDim_eq_iSup_height_of_nonempty,
      Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add,
      WithBot.coe_le_coe, ENat.iSup_add]
    refine iSup_le fun w => le_trans ?_
      (le_iSup (fun a : S => Order.height a + Order.coheight a) (j w))
    exact add_le_add (Order.height_le_height_apply_of_strictMono j hmono w) (h w)

end

end GlobalTheory.DimCodim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDualAndRangeDualMapBaseChange
open TensorProduct

namespace GlobalTheory.DualFibreRank

section
variable {O : Type} [CommRing O] (A : Type) [CommRing A] [Algebra O A]

noncomputable def cmp (M : Type) [AddCommGroup M] [Module O M] :
    A ⊗[O] Module.Dual O M →ₗ[A] Module.Dual A (A ⊗[O] M) :=
  LinearMap.liftBaseChange A (Module.Dual.baseChange A)

variable {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]

theorem cmp_natural (f : M →ₗ[O] N) :
    cmp A M ∘ₗ f.dualMap.baseChange A = (f.baseChange A).dualMap ∘ₗ cmp A N := by
  ext g x
  simp [cmp]

theorem cmp_natural_apply (f : M →ₗ[O] N) (x : A ⊗[O] Module.Dual O N) :
    cmp A M (f.dualMap.baseChange A x) = (f.baseChange A).dualMap (cmp A N x) :=
  LinearMap.congr_fun (cmp_natural A f) x

theorem cmp_bijective_of_free [Module.Free O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by
  have h := (TensorProduct.isBaseChange O M A)
  have : cmp A M (O := O) = h.toDualBaseChange.toLinearMap := by
    ext g x
    have := h.toDualBaseChange_tmul 1 g x
    simp only [TensorProduct.mk_apply] at this
    simp [cmp, this, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact h.toDualBaseChange.bijective

theorem cmp_bijective [Module.Projective O M] [Module.Finite O M] :
    Function.Bijective (cmp A M (O := O)) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective O M
  have hF := cmp_bijective_of_free A (O := O) (M := Fin n → O)
  have h1 : ∀ x, i.dualMap.baseChange A (p.dualMap.baseChange A x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.dualMap_comp_dualMap, hpi]
    simp [LinearMap.dualMap_id]
  have h2 : ∀ y, (i.baseChange A).dualMap ((p.baseChange A).dualMap y) = y := by
    intro y
    rw [← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, ← LinearMap.baseChange_comp, hpi]
    simp [LinearMap.dualMap_id]
  constructor
  · intro x y hxy
    rw [← h1 x, ← h1 y]
    congr 1
    apply hF.1
    rw [cmp_natural_apply, cmp_natural_apply, hxy]
  · intro y
    obtain ⟨z, hz⟩ := hF.2 ((p.baseChange A).dualMap y)
    exact ⟨i.dualMap.baseChange A z, by rw [cmp_natural_apply, hz, h2]⟩

end

theorem finrank_dual_and_range_dualMap_baseChange :
    ∀ (O M N κ : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
      [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]
      [Field κ] [Algebra O κ] (f : M →ₗ[O] N),
      Module.finrank κ (TensorProduct O κ (Module.Dual O M)) =
          Module.finrank κ (TensorProduct O κ M) ∧
        Module.finrank κ (LinearMap.range (f.dualMap.baseChange κ)) =
          Module.finrank κ (LinearMap.range (f.baseChange κ)) := by
  intro O M N κ _ _ _ _ _ _ _ _ _ _ _ f
  let eM := LinearEquiv.ofBijective (cmp κ M (O := O)) (cmp_bijective κ)
  refine ⟨by rw [eM.finrank_eq, Subspace.dual_finrank_eq], ?_⟩
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range (f.baseChange κ),
    ← LinearEquiv.finrank_map_eq eM]
  have : (LinearMap.range (f.dualMap.baseChange κ)).map (eM : _ →ₗ[κ] _) =
      LinearMap.range (f.baseChange κ).dualMap := by
    rw [← LinearMap.range_comp]
    change LinearMap.range (cmp κ M ∘ₗ f.dualMap.baseChange κ) = _
    rw [cmp_natural, LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.2 (cmp_bijective κ).2
  rw [this]

end GlobalTheory.DualFibreRank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

abbrev str : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

def Good (r : ℕ) {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) : Prop :=
  IsFinite (I.subschemeι ≫ pullback.snd _ g) ∧ Flat (I.subschemeι ≫ pullback.snd _ g) ∧
    ∀ y, (I.subschemeι ≫ pullback.snd _ g).finrank y = r

abbrev bc {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) :
    pullback (str A B) (a ≫ g) ⟶ pullback (str A B) g :=
  pullback.map _ _ _ _ (𝟙 _) a (𝟙 _) (by simp) (by simp)

theorem isPullback_bc {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) :
    IsPullback (bc A B g a) (pullback.snd _ (a ≫ g)) (pullback.snd _ g) a :=
  by
    have h : bc A B g a ≫ pullback.fst (str A B) g = pullback.fst _ _ :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [h]
    exact IsPullback.of_hasPullback (str A B) (a ≫ g)

theorem good_comap (r : ℕ) {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T)
    (I : (pullback (str A B) g).IdealSheafData) (hI : Good A B r g I) :
    Good A B r (a ≫ g) (I.comap (bc A B g a)) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have H : IsPullback (pullback.snd (bc A B g a) I.subschemeι)
      (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) I.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have e : (I.comap (bc A B g a)).subschemeι ≫ pullback.snd _ (a ≫ g) =
      (I.comapIso (bc A B g a)).hom ≫ (pullback.fst (bc A B g a) I.subschemeι ≫
        pullback.snd _ (a ≫ g)) := by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have f1 : IsFinite (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H h1
  have f2 : Flat (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @Flat) H h2
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [e]; infer_instance
  · rw [e]; infer_instance
  · rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ H y, h3]

theorem sigma_eq (r : ℕ) {T : Scheme.{0}} {g₀ g : T ⟶ Spec (CommRingCat.of A)} (h : g₀ = g)
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I : (pullback (str A B) g).IdealSheafData}
    (hI : I₀ = I.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])))
    (h₀ : Good A B r g₀ I₀) (h₁ : Good A B r g I) :
    (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g, ⟨I, h₁⟩⟩ := by
  subst h
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id] at hI
  subst hI
  rfl

theorem comap_bc_comp {T T' T'' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T)
    (b : T'' ⟶ T') (I : (pullback (str A B) g).IdealSheafData) :
    I.comap (bc A B g (b ≫ a)) = ((I.comap (bc A B g a)).comap (bc A B (a ≫ g) b)).comap
      (pullback.map (str A B) ((b ≫ a) ≫ g) (str A B) (b ≫ a ≫ g) (𝟙 _) (𝟙 _) (𝟙 _)
        (by simp) (by simp)) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  apply pullback.hom_ext <;>
    simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]

def functor (r : ℕ) : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := Σ g : T.unop ⟶ Spec (CommRingCat.of A),
    {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}
  map {_ _} a := TypeCat.ofHom fun x => ⟨a.unop ≫ x.1, ⟨x.2.1.comap (bc A B x.1 a.unop),
    good_comap A B r x.1 a.unop x.2.1 x.2.2⟩⟩
  map_id T := by
    ext x : 3
    exact sigma_eq A B r (Category.id_comp _) rfl _ _
  map_comp {T T' T''} a b := by
    ext x : 3
    exact sigma_eq A B r (Category.assoc _ _ _) (comap_bc_comp A B x.1 a.unop b.unop x.2.1) _ _

theorem functor_map (r : ℕ) {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    (functor A B r).map a.op y =
      ⟨a ≫ y.1, ⟨y.2.1.comap (bc A B y.1 a), good_comap A B r y.1 a y.2.1 y.2.2⟩⟩ := rfl

def Basic {r N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : Prop :=
  ∀ U : T.affineOpens, Function.Bijective fun c : Fin r → Γ(T, U) =>
    ∑ k, ((y.2.1.subschemeι ≫ pullback.snd _ y.1).app U).hom (c k) *
      ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤
        ((y.2.1.subschemeι ≫ pullback.snd _ y.1) ⁻¹ᵁ U) (by simp)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (e (σ k)))

end GlobalTheory.HilbAff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjection
namespace GlobalTheory.OrbitAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)

def stab (x : V) : Subgroup L where
  carrier := {l | π (l : G) x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Subgroup.coe_inv] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_stab {x : V} {l : L} : l ∈ stab π L x ↔ π (l : G) x = x := Iff.rfl

noncomputable def cv (H : Subgroup L) (x : V) (q : L ⧸ H) : V := π ((q.out : L) : G) x

theorem cv_mk {H : Subgroup L} {x : V} (hH : H ≤ stab π L x) (a : L) :
    cv π L H x (QuotientGroup.mk a) = π (a : G) x := by
  unfold cv
  set b : L := (QuotientGroup.mk a : L ⧸ H).out with hb
  have h1 : (QuotientGroup.mk b : L ⧸ H) = QuotientGroup.mk a := QuotientGroup.out_eq' _
  have h2 : b⁻¹ * a ∈ H := QuotientGroup.eq.mp h1
  have h3 := (mem_stab π L).mp (hH h2)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply] at h3
  calc π (b : G) x = π (b : G) (π (b : G)⁻¹ (π (a : G) x)) := by rw [h3]
    _ = π (a : G) x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

noncomputable def avgH (H : Subgroup L) (x : V) : V :=
  ((H.index : ℂ))⁻¹ • ∑ᶠ q : L ⧸ H, cv π L H x q

theorem avgH_refine {H H' : Subgroup L} {x : V} (hle : H' ≤ H) (hH : H ≤ stab π L x)
    [H'.FiniteIndex] : avgH π L H' x = avgH π L H x := by
  classical
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hrel := Subgroup.relIndex_mul_index hle
  haveI : (H'.subgroupOf H).FiniteIndex := by
    refine ⟨?_⟩
    intro h0
    have h4 : H'.index = 0 := by rw [← hrel]; simp [Subgroup.relIndex, h0]
    exact Subgroup.FiniteIndex.index_ne_zero h4
  haveI := Fintype.ofFinite (L ⧸ H)
  haveI := Fintype.ofFinite (L ⧸ H')
  haveI := Fintype.ofFinite (H ⧸ H'.subgroupOf H)
  unfold avgH
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let e := Subgroup.quotientEquivProdOfLE hle
  have hcv : ∀ q : L ⧸ H', cv π L H' x q = cv π L H x (e q).1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cv_mk π L (le_trans hle hH), show (e (QuotientGroup.mk a)).1 = QuotientGroup.mk a from rfl,
        cv_mk π L hH]
  have hsum : ∑ q : L ⧸ H', cv π L H' x q =
      (Fintype.card (H ⧸ H'.subgroupOf H) : ℂ) • ∑ q : L ⧸ H, cv π L H x q := by
    simp_rw [hcv]
    rw [Equiv.sum_comp e (fun p => cv π L H x p.1), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [Finset.smul_sum]
    simp [Nat.cast_smul_eq_nsmul]
  have hc : Fintype.card (H ⧸ H'.subgroupOf H) = H'.relIndex H := by
    rw [Fintype.card_eq_nat_card]; rfl
  rw [hsum, hc, ← hrel, smul_smul]
  congr 1
  have h5 : (H'.relIndex H : ℂ) ≠ 0 := by
    have := Subgroup.FiniteIndex.index_ne_zero (H := H'.subgroupOf H)
    exact_mod_cast this
  push_cast
  field_simp

theorem stab_le_add (x y : V) : stab π L x ⊓ stab π L y ≤ stab π L (x + y) := by
  intro l hl
  rw [mem_stab, map_add (f := _), (mem_stab π L).mp hl.1, (mem_stab π L).mp hl.2]

theorem stab_le_smul (c : ℂ) (x : V) : stab π L x ≤ stab π L (c • x) := by
  intro l hl
  rw [mem_stab, map_smul, (mem_stab π L).mp hl]

theorem avgH_add (H : Subgroup L) [H.FiniteIndex] (x y : V) :
    avgH π L H (x + y) = avgH π L H x + avgH π L H y := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH cv
  simp only [finsum_eq_sum_of_fintype, map_add (f := _), Finset.sum_add_distrib, smul_add]

theorem avgH_smul (H : Subgroup L) [H.FiniteIndex] (c : ℂ) (x : V) :
    avgH π L H (c • x) = c • avgH π L H x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ H)
  unfold avgH cv
  simp only [finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum, smul_comm c]

noncomputable def avg (x : V) : V := avgH π L (stab π L x) x

theorem avg_eq {H : Subgroup L} {x : V} [H.FiniteIndex] (hH : H ≤ stab π L x) :
    avg π L x = avgH π L H x := (avgH_refine π L hH le_rfl).symm

theorem avg_fixed {x : V} (hx : (stab π L x).FiniteIndex) (hfix : ∀ l ∈ L, π l x = x) :
    avg π L x = x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ stab π L x)
  unfold avg avgH
  have : ∀ q : L ⧸ stab π L x, cv π L (stab π L x) x q = x := fun q => hfix _ (q.out).2
  simp only [finsum_eq_sum_of_fintype, this, Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_eq_nat_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h0 : ((stab π L x).index : ℂ) ≠ 0 := by exact_mod_cast hx.index_ne_zero
  rw [show Nat.card (L ⧸ stab π L x) = (stab π L x).index from rfl, inv_mul_cancel₀ h0, one_smul]

theorem avg_invariant {x : V} (hx : (stab π L x).FiniteIndex) (l : L) :
    π (l : G) (avg π L x) = avg π L x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ stab π L x)
  unfold avg avgH
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_fintype, map_smul, map_sum]
  congr 1
  have h : ∀ q : L ⧸ stab π L x, π (l : G) (cv π L (stab π L x) x q) =
      cv π L (stab π L x) x (l • q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cv_mk π L le_rfl, MulAction.Quotient.smul_mk, cv_mk π L le_rfl, smul_eq_mul, Subgroup.coe_mul, map_mul,
        Module.End.mul_apply]
  simp_rw [h]
  exact Equiv.sum_comp (MulAction.toPerm l) (cv π L (stab π L x) x)

theorem avg_add {x y : V} (hx : (stab π L x).FiniteIndex) (hy : (stab π L y).FiniteIndex) :
    avg π L (x + y) = avg π L x + avg π L y := by
  haveI : (stab π L x ⊓ stab π L y).FiniteIndex := inferInstance
  rw [avg_eq π L (stab_le_add π L x y), avg_eq π L (inf_le_left : stab π L x ⊓ stab π L y ≤ stab π L x),
    avg_eq π L (inf_le_right : stab π L x ⊓ stab π L y ≤ stab π L y), avgH_add]

theorem avg_smul {x : V} (hx : (stab π L x).FiniteIndex) (c : ℂ) :
    avg π L (c • x) = c • avg π L x := by
  rw [avg_eq π L (stab_le_smul π L c x), avgH_smul]
  rfl

end GlobalTheory.OrbitAvg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixOneParameterGroupEqExpOfContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtOneParameter
noncomputable section

open Filter Topology MeasureTheory

namespace GlobalTheory.LocWeil.DerComm

theorem _root_.GlobalTheory.LocWeil.DerComm.differentiableAt_oneParameter {A : Type} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (φ : ℝ → A) (hc : Continuous φ) (h0 : φ 0 = 1)
    (hm : ∀ s t : ℝ, φ (s + t) = φ s * φ t) : DifferentiableAt ℝ φ 0 := by
  have hφ := hc
  have hadd := hm
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > (0 : ℝ), ∀ s : ℝ, |s| ≤ δ → ‖1 - φ s‖ ≤ 1 / 2 := by
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.mp hφ.continuousAt (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun s hs => ?_⟩
    have hs' : dist s 0 < ε := by
      rw [Real.dist_eq, sub_zero]; linarith
    have := h hs'
    rw [dist_eq_norm, h0, norm_sub_rev] at this
    exact this.le
  set E : A := δ⁻¹ • ∫ s in (0 : ℝ)..δ, (1 - φ s) with hE
  have hEn : ‖E‖ < 1 := by
    have hI : ‖∫ s in (0 : ℝ)..δ, (1 - φ s)‖ ≤ 1 / 2 * |δ - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le hδ.le] at hs
      apply hball
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    rw [sub_zero, abs_of_pos hδ] at hI
    rw [hE, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ]
    calc δ⁻¹ * ‖∫ s in (0 : ℝ)..δ, (1 - φ s)‖ ≤ δ⁻¹ * (1 / 2 * δ) := by gcongr
      _ < 1 := by field_simp; norm_num
  set G : ℝ → A := fun x => ∫ s in (0 : ℝ)..x, φ s with hG
  have hint : ∀ t : ℝ, φ t * (1 - E) = δ⁻¹ • (G (t + δ) - G t) := by
    intro t
    have hC : 1 - E = δ⁻¹ • ∫ s in (0 : ℝ)..δ, φ s := by
      rw [hE, intervalIntegral.integral_sub intervalIntegrable_const (hφ.intervalIntegrable _ _),
        intervalIntegral.integral_const, smul_sub, sub_zero, smul_smul, inv_mul_cancel₀ hδ.ne',
        one_smul, sub_sub_cancel]
    rw [hC, mul_smul_comm, hG,
      intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
        (hφ.intervalIntegrable _ _)]
    congr 1
    have key := (ContinuousLinearMap.mul ℝ A (φ t)).intervalIntegral_comp_comm
      (hφ.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at key
    rw [← key]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun s => φ s) t]
    simp [add_comm]
  set u : Aˣ := Units.oneSub E hEn with hu
  have hrep : φ = fun t => (δ⁻¹ • (G (t + δ) - G t)) * ↑u⁻¹ := by
    funext t
    rw [← hint t]
    have : (1 - E : A) = ↑u := by rw [hu, Units.val_oneSub]
    rw [this, Units.mul_inv_cancel_right]
  have hGd : ∀ x : ℝ, DifferentiableAt ℝ G x := fun x =>
    (hφ.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
  rw [hrep]
  have h1 : DifferentiableAt ℝ (fun t => G (t + δ)) 0 :=
    (hGd (0 + δ)).comp (0 : ℝ) (differentiableAt_id.add_const δ)
  have h2 : DifferentiableAt ℝ (fun t => δ⁻¹ • (G (t + δ) - G t)) 0 :=
    by
      have h3 := (h1.sub (hGd 0)).const_smul δ⁻¹
      exact h3
  exact h2.mul_const _

section Alg

variable {S U : Type} [AddCommGroup S] [Module ℂ S]

variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

variable (β : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) {ι : Type} [Fintype ι] (b b' : ι → U)

variable {β b b'}

variable {d : U →ₗ[ℝ] Module.End ℂ S} {κ : ℂ} {Y : U →ₗ[ℝ] U}

section Main

variable {Γ I : Type} [Group Γ] (ω : Γ →* Module.End ℂ S) (G : Γ →* (U →L[ℝ] U)) (ev : I → S →ₗ[ℂ] ℂ) {f : S}
  {N : Submodule ℂ S}
  (hβ : ∀ x, (∀ y, β x y = 0) → x = 0) (hs : ∀ x y, β y x = -β x y) (hκ : κ ≠ 0)
  (hd : ∀ u v, d u * d v - d v * d u = (κ * (β u v : ℝ)) • (1 : Module.End ℂ S))
  (hω : ∀ q u, ω q * d u = d (G q u) * ω q) (hG : ∀ q x y, β (G q x) (G q y) = β x y)
  (hN : ∀ Φ, Φ ∈ N ↔ ∃ a ∈ Algebra.adjoin ℂ (Set.range d), a f = Φ)
  (hvac : ∀ B ∈ Algebra.adjoin ℂ (Set.range d), (∀ u, B (d u f) = d u (B f)) → ∃ c : ℂ, B f = c • f)
  (hev : ∀ Φ Ψ, (∀ w, ev w Φ = ev w Ψ) → Φ = Ψ)
  (hline : ∀ w u, ∃ ℓ : ℝ → S →ₗ[ℂ] ℂ, ℓ 0 = ev w ∧ (∀ Ψ s, HasDerivAt (fun s => ℓ s Ψ) (ℓ s (d u Ψ)) s) ∧
    ∀ s, ∃ (c : ℂ) (w' : I), ∀ Ψ, ℓ s Ψ = c * ev w' Ψ)

end Main

end Alg

end GlobalTheory.LocWeil.DerComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixOneParameterGroupEqExpOfContinuous
open Filter Topology

namespace GlobalTheory.OneParamMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem eq_exp_of_continuous_oneParameter {n : Type} [Fintype n] [DecidableEq n]
    (N : ℝ → Matrix n n ℂ) (hc : Continuous N) (h0 : N 0 = 1)
    (hm : ∀ s t, N (s + t) = N s * N t) :
    ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) := by
  have hd := GlobalTheory.LocWeil.DerComm.differentiableAt_oneParameter N hc h0 hm
  set Y := deriv N 0 with hY
  have hN : ∀ t, HasDerivAt N (N t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => N t * N (s - t)) (N t * Y) t := by
      have h2 : HasDerivAt (fun s => N (s - t)) Y t := by
        have hd' : HasDerivAt N Y (t - t) := by rw [sub_self]; exact hd.hasDerivAt
        exact hd'.comp_sub_const t t
      exact h2.const_mul (N t)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only
    rw [← hm]; congr 1; ring
  refine ⟨Y, fun t => ?_⟩
  set f : ℝ → Matrix n n ℂ := fun s => N s * NormedSpace.exp ((-s) • Y) with hf
  have hfd : ∀ s, HasDerivAt f 0 s := by
    intro s
    have he : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Y))) (NormedSpace.exp (s • (-Y)) * (-Y)) s :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Y) s
    have he' : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • Y))
        (NormedSpace.exp ((-s) • Y) * (-Y)) s := by
      simpa [smul_neg, neg_smul] using he
    have := (hN s).mul he'
    refine this.congr_deriv ?_
    have hcomm : Y * NormedSpace.exp ((-s) • Y) = NormedSpace.exp ((-s) • Y) * Y :=
      ((Commute.refl Y).smul_right (-s)).exp_right.eq
    rw [mul_assoc, hcomm]
    simp [mul_neg]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hfd s).differentiableAt)
    (fun s => (hfd s).deriv) t 0
  have hf0 : f 0 = 1 := by simp [hf, h0]
  rw [hf0] at hconst
  have hinv : NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]
    simp
  calc N t = N t * (NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y)) := by rw [hinv, mul_one]
    _ = f t * NormedSpace.exp (t • Y) := by simp only [hf, mul_assoc]
    _ = NormedSpace.exp (t • Y) := by rw [hconst, one_mul]

end GlobalTheory.OneParamMatrix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixOneParameterGroupEqExpOfContinuousStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_oneParameterGroup_eq_exp_of_continuous : ∀ {n : Type} [Fintype n] [DecidableEq n] (N : ℝ → Matrix n n ℂ), Continuous N → N 0 = 1 → (∀ s t, N (s + t) = N s * N t) → ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) := by
  first | exact @GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter | exact GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter | (intros; apply GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsProportional
open Matrix

namespace GlobalTheory

theorem det_mul_det_toBlocks₂₂_of_mul_eq_one {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X Y : Matrix (m ⊕ n) (m ⊕ n) K) (h : X * Y = 1) :
    X.det * Y.toBlocks₂₂.det = X.toBlocks₁₁.det := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, X = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks X).symm⟩
  obtain ⟨A', B', C', D', rfl⟩ : ∃ A B C D, Y = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks Y).symm⟩
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
  obtain ⟨-, h12, -, h22⟩ := h
  have key : fromBlocks A B C D * fromBlocks (1 : Matrix m m K) B' 0 D' = fromBlocks A 0 C 1 := by
    rw [fromBlocks_multiply, h12, h22]
    simp
  have := congrArg Matrix.det key
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at this
  simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
noncomputable section

namespace GlobalTheory.AffineCurveNbhd

def IsNbhd (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) : Prop :=
  (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) ∧
  (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f})

theorem awayHom_isUnit {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    (φ : A' →ₐ[A] A'') (f : A) :
    IsUnit (((algebraMap A'' (Localization.Away (algebraMap A A'' f))).comp φ.toRingHom) (algebraMap A A' f)) := by
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  exact IsLocalization.Away.algebraMap_isUnit _

def awayHom {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    (φ : A' →ₐ[A] A'') (f : A) : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A'' f) :=
  Localization.awayLift ((algebraMap A'' _).comp φ.toRingHom) _ (awayHom_isUnit φ f)

theorem awayHom_comp_algebraMap {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) :
    (awayHom φ f).comp (algebraMap A' _) = (algebraMap A'' _).comp φ.toRingHom :=
  IsLocalization.Away.lift_comp _ (awayHom_isUnit φ f)

end GlobalTheory.AffineCurveNbhd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitution
namespace GlobalTheory


open MvPolynomial in
theorem _root_.GlobalTheory.etale_mvPolynomial_map_of_etale {B A N : Type} [CommRing B] [CommRing A] (g : B →+* A)
    (hg : g.Etale) : (MvPolynomial.map (σ := N) g).Etale := by
  letI := g.toAlgebra
  letI : Algebra (MvPolynomial N B) (MvPolynomial N A) := MvPolynomial.algebraMvPolynomial
  exact RingHom.Etale.isStableUnderBaseChange B A (MvPolynomial N B) (MvPolynomial N A) hg

end GlobalTheory
end
