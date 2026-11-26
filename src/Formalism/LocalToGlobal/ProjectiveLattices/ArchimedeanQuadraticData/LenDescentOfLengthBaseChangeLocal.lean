module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreSt
public import Formalism.FilteredPoleLength.LocalDescentLevels.LengthBaseChange

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.TieLDB
namespace Formalism.L2.Pj.QAt.TieLDB

open Module

variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]

theorem smul_comm' (s : A) (o : Localization.AtPrime p) (v : V) : s • (o • v) = o • (s • v) := by
  rw [← smul_assoc, Algebra.smul_def, mul_comm, mul_smul, algebraMap_smul]

theorem exists_smul_mem (G : Submodule A V) {x : V}
    (hx : x ∈ Submodule.span (Localization.AtPrime p) (G : Set V)) :
    ∃ s ∈ p.primeCompl, s • x ∈ G := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, p.primeCompl.one_mem, by rw [smul_zero]; exact G.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, p.primeCompl.mul_mem hs ht, ?_⟩
    have e1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    have e2 : (s * t) • y = s • (t • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact add_mem (G.smul_mem t hsx) (G.smul_mem s hty)
  | smul o x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨a, s'⟩, hos⟩ := IsLocalization.mk'_surjective p.primeCompl o
    refine ⟨s' * s, p.primeCompl.mul_mem s'.2 hs, ?_⟩
    have h1 : (s' : A) • o = algebraMap A (Localization.AtPrime p) a := by
      rw [← hos, Algebra.smul_def, mul_comm, IsLocalization.mk'_spec]
    rw [mul_smul, smul_comm' p s o x, ← smul_assoc, h1, algebraMap_smul]
    exact G.smul_mem a hsx

theorem span_inf_eq (M : Submodule A V) (W : Submodule (Localization.AtPrime p) V) :
    Submodule.span (Localization.AtPrime p) ((M ⊓ W.restrictScalars A : Submodule A V) : Set V) =
      Submodule.span (Localization.AtPrime p) (M : Set V) ⊓ W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact ⟨Submodule.subset_span hx.1, hx.2⟩
  · rintro x ⟨hxM, hxW⟩
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p M hxM
    have hu := IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
    have hmem : s • x ∈ Submodule.span (Localization.AtPrime p)
        ((M ⊓ W.restrictScalars A : Submodule A V) : Set V) :=
      Submodule.subset_span ⟨hsx, W.smul_of_tower_mem s hxW⟩
    have hx : x = hu.unit⁻¹ • (s • x) := by
      rw [← algebraMap_smul (Localization.AtPrime p) s x]
      change x = hu.unit⁻¹ • (hu.unit • x)
      rw [inv_smul_smul]
    rw [hx]
    exact Submodule.smul_of_tower_mem _ _ hmem

variable (H G : Submodule A V)

def inc : H →ₗ[A] Submodule.span (Localization.AtPrime p) (H : Set V) where
  toFun h := ⟨h, Submodule.subset_span h.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def locMap :
    H ⧸ G.comap H.subtype →ₗ[A] ↥(Submodule.span (Localization.AtPrime p) (H : Set V)) ⧸
      (Submodule.span (Localization.AtPrime p) (G : Set V)).comap
        (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype :=
  (G.comap H.subtype).liftQ
    (((((Submodule.span (Localization.AtPrime p) (G : Set V)).comap
      (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype).mkQ).restrictScalars A) ∘ₗ
        inc p H) (by
      intro h hh
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span hh)

theorem locMap_mk (h : H) :
    locMap p H G (Submodule.Quotient.mk h) = Submodule.Quotient.mk (inc p H h) := rfl

theorem isLocalizedModule : IsLocalizedModule p.primeCompl (locMap p H G) := by
  constructor
  · intro s
    rw [Module.End.isUnit_iff]
    have hu := IsLocalization.map_units (Localization.AtPrime p) s
    constructor
    · intro z1 z2 h
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        ← algebraMap_smul (Localization.AtPrime p) (s : A) z1,
        ← algebraMap_smul (Localization.AtPrime p) (s : A) z2] at h
      exact hu.smul_left_cancel.1 h
    · intro z
      refine ⟨hu.unit⁻¹ • z, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul (Localization.AtPrime p) (s : A)]
      change hu.unit • hu.unit⁻¹ • z = z
      rw [smul_inv_smul]
  · intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p H hx
    refine ⟨(Submodule.Quotient.mk ⟨s • x, hsx⟩, ⟨s, hs⟩), ?_⟩
    rw [locMap_mk]
    rfl
  · intro x₁ x₂ h
    obtain ⟨h1, rfl⟩ := Submodule.Quotient.mk_surjective _ x₁
    obtain ⟨h2, rfl⟩ := Submodule.Quotient.mk_surjective _ x₂
    rw [locMap_mk, locMap_mk, Submodule.Quotient.eq] at h
    have h' : (h1 : V) - h2 ∈ Submodule.span (Localization.AtPrime p) (G : Set V) := h
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p G h'
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    change (s • (h1 : V)) - s • (h2 : V) ∈ G
    rw [← smul_sub]
    exact hsx

theorem length_localized_eq {P : Type*} [AddCommGroup P] [Module A P]
    (e : P ≃ₗ[A] H ⧸ G.comap H.subtype) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl P) =
      Module.length (Localization.AtPrime p)
        (↥(Submodule.span (Localization.AtPrime p) (H : Set V)) ⧸
          (Submodule.span (Localization.AtPrime p) (G : Set V)).comap
            (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype) := by
  have := isLocalizedModule p H G
  have : IsLocalizedModule p.primeCompl (locMap p H G ∘ₗ e.toLinearMap) := inferInstance
  exact ((IsLocalizedModule.iso p.primeCompl (locMap p H G ∘ₗ e.toLinearMap)).extendScalarsOfIsLocalization
    p.primeCompl (Localization.AtPrime p)).length_eq

end Formalism.L2.Pj.QAt.TieLDB
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.TieLDA
namespace Formalism.L2.Pj.QAt.TieLDA

open TensorProduct Module

def tm (K K₁ : Type*) [Field K] [Field K₁] [Algebra K K₁] {U : Type*} [AddCommGroup U]
    [Module K U] (u : U) : K₁ ⊗[K] U :=
  (1 : K₁) ⊗ₜ[K] u

section Base

variable {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]

abbrev modT (T : Subring K₁) (U : Type*) [AddCommGroup U] [Module K U] :
    Module T (K₁ ⊗[K] U) :=
  Module.compHom _ T.subtype

attribute [local instance] modT

abbrev modR (R : Type*) [CommRing R] [Algebra R K] (U : Type*) [AddCommGroup U] [Module K U] :
    Module R (K₁ ⊗[K] U) :=
  Module.compHom _ (algebraMap R K)

attribute [local instance] modR

variable {U : Type*} [AddCommGroup U] [Module K U]

theorem smulT_def (T : Subring K₁) (t : T) (l : K₁ ⊗[K] U) : t • l = (t : K₁) • l := rfl

theorem smulK_eq (k : K) (l : K₁ ⊗[K] U) : k • l = algebraMap K K₁ k • l := by
  induction l using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def]
    rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

section R

variable {R : Type*} [CommRing R] [Algebra R K] [Module R U] [IsScalarTower R K U]

theorem smulR_def (r : R) (l : K₁ ⊗[K] U) : r • l = algebraMap R K r • l := rfl

def tmR : U →ₗ[R] K₁ ⊗[K] U where
  toFun u := tm K K₁ u
  map_add' x y := tmul_add _ _ _
  map_smul' r u := by
    change (1 : K₁) ⊗ₜ[K] (r • u) = algebraMap R K r • ((1 : K₁) ⊗ₜ[K] u)
    rw [← algebraMap_smul K r u, tmul_smul]

variable (T : Subring K₁) [Algebra R T]
  (hRT : ∀ r : R, ((algebraMap R T r : T) : K₁) = algebraMap K K₁ (algebraMap R K r))

include hRT in
theorem tower : IsScalarTower R T (K₁ ⊗[K] U) := by
  constructor
  intro r t l
  show ((r • t : T) : K₁) • l = algebraMap R K r • ((t : K₁) • l)
  rw [smulK_eq, smul_smul, Algebra.smul_def r t, Subring.coe_mul, hRT]

include hRT in
theorem tm_smul (r : R) (u : U) : tm K K₁ (r • u) = algebraMap R T r • tm K K₁ u := by
  have h := (tmR (K₁ := K₁) (K := K) (U := U) (R := R)).map_smul r u
  change tm K K₁ (r • u) = r • tm K K₁ u at h
  rw [h, smulR_def, smulT_def, hRT, smulK_eq]

noncomputable def Phi (X : Submodule R U) : T ⊗[R] X →ₗ[T] K₁ ⊗[K] U :=
  @LinearMap.liftBaseChange R X (K₁ ⊗[K] U) T _ _ _ _ _ _ _ _ (tower (U := U) T hRT)
    ((tmR (K₁ := K₁) (K := K) (U := U)).comp X.subtype)

theorem Phi_tmul (X : Submodule R U) (t : T) (x : X) :
    Phi T hRT X (t ⊗ₜ x) = (t : K₁) • tm K K₁ (x : U) := by
  unfold Phi
  erw [LinearMap.liftBaseChange_tmul]
  rfl

theorem Phi_range (X : Submodule R U) :
    LinearMap.range (Phi T hRT X) = Submodule.span T (tm K K₁ '' (X : Set U)) := by
  unfold Phi
  erw [LinearMap.range_liftBaseChange]
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

include hRT in
theorem span_tm_span (G : Set U) :
    Submodule.span T (tm K K₁ '' (Submodule.span R G : Set U)) = Submodule.span T (tm K K₁ '' G) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      show (1 : K₁) ⊗ₜ[K] (0 : U) ∈ _
      rw [tmul_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _
      rw [tmul_add]
      exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [tm_smul T hRT]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]

include K in
theorem isTorsionFree_sub (X : Submodule R U) : Module.IsTorsionFree R X := by
  constructor
  intro r hr x y hxy
  have hr0 : r ≠ 0 := hr.ne_zero
  have hK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0
  apply Subtype.ext
  have h1 : r • (x : U) = r • (y : U) := congrArg Subtype.val hxy
  rw [← algebraMap_smul K r (x : U), ← algebraMap_smul K r (y : U)] at h1
  exact smul_right_injective U hK h1

theorem Phi_injective (X : Submodule R U) (hX : X.FG) : Function.Injective (Phi T hRT X) := by
  classical
  haveI : Module.Finite R X := Module.Finite.iff_fg.2 hX
  haveI : Module.IsTorsionFree R X := isTorsionFree_sub (K := K) X
  haveI : Module.Free R X := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R X
  let v : Module.Free.ChooseBasisIndex R X → K₁ ⊗[K] U := fun i => tm K K₁ ((b i : X) : U)
  have hR : LinearIndependent R (fun i => ((b i : X) : U)) :=
    b.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
  have hK : LinearIndependent K (fun i => ((b i : X) : U)) := (LinearIndependent.iff_fractionRing R K).1 hR
  have hK₁ : LinearIndependent K₁ v := Module.Flat.linearIndependent_one_tmul hK
  have hT : LinearIndependent T v := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h1 := (linearIndependent_iff'.1 hK₁) s (fun j => (g j : K₁)) (by exact hg) i hi
    exact Subtype.ext h1
  let b' := b.baseChange T
  have hcomp : (Phi T hRT X) ∘ₗ b'.repr.symm.toLinearMap = Finsupp.linearCombination T v := by
    refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
    simp [b', v, Basis.baseChange_apply, Phi_tmul]
    first
      | exact (one_smul _ _).symm
      | (rw [smulT_def]; simp)
  have key : ∀ z, Finsupp.linearCombination T v (b'.repr z) = Phi T hRT X z := by
    intro z
    rw [← hcomp]
    simp
  intro z w hzw
  apply b'.repr.injective
  exact hT (by rw [key, key, hzw])

include hRT in
theorem length_quot_eq (X Y : Submodule R U) (hX : X.FG) (hYX : Y ≤ X) :
    Module.length T (↥(Submodule.span T (tm K K₁ '' (X : Set U))) ⧸
        (Submodule.span T (tm K K₁ '' (Y : Set U))).comap
          (Submodule.span T (tm K K₁ '' (X : Set U))).subtype) =
      Module.length T (T ⊗[R] (X ⧸ Y.comap X.subtype)) := by
  classical
  let Y' := Y.comap X.subtype
  let Ψ : T ⊗[R] X →ₗ[T] T ⊗[R] (X ⧸ Y') := Y'.mkQ.baseChange T
  have h1 : (Ψ : T ⊗[R] X → T ⊗[R] (X ⧸ Y')) = Y'.mkQ.lTensor T := LinearMap.baseChange_eq_ltensor _
  have hΨ : Function.Surjective Ψ := by
    rw [h1]
    exact LinearMap.lTensor_surjective T (Submodule.mkQ_surjective Y')
  let ι' : T ⊗[R] Y' →ₗ[T] T ⊗[R] X := Y'.subtype.baseChange T
  have h2 : (ι' : T ⊗[R] Y' → T ⊗[R] X) = Y'.subtype.lTensor T := LinearMap.baseChange_eq_ltensor _
  have hker : LinearMap.ker Ψ = LinearMap.range ι' := by
    ext z
    have hex := lTensor_exact T (LinearMap.exact_subtype_mkQ Y') (Submodule.mkQ_surjective Y') z
    rw [LinearMap.mem_ker, LinearMap.mem_range, h1, hex, Set.mem_range, h2]
  let e1 : T ⊗[R] X ≃ₗ[T] Submodule.span T (tm K K₁ '' (X : Set U)) :=
    (LinearEquiv.ofInjective (Phi T hRT X) (Phi_injective T hRT X hX)).trans
      (LinearEquiv.ofEq _ _ (Phi_range T hRT X))
  have he1 : ∀ z, ((e1 z : Submodule.span T (tm K K₁ '' (X : Set U))) : K₁ ⊗[K] U) = Phi T hRT X z := by
    intro z
    rfl
  have hY : ∀ z, Phi T hRT X z ∈ Submodule.span T (tm K K₁ '' (Y : Set U)) ↔ z ∈ LinearMap.range ι' := by
    intro z
    constructor
    · intro hz
      have hle : Submodule.span T (tm K K₁ '' (Y : Set U)) ≤ (LinearMap.range ι').map (Phi T hRT X) := by
        rw [Submodule.span_le]
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨ι' ((1 : T) ⊗ₜ ⟨⟨y, hYX hy⟩, hy⟩), ⟨_, rfl⟩, ?_⟩
        show Phi T hRT X ((1 : T) ⊗ₜ ⟨y, hYX hy⟩) = tm K K₁ y
        rw [Phi_tmul]
        simp
      obtain ⟨w, hw, hwz⟩ := hle hz
      rw [← Phi_injective T hRT X hX hwz]
      exact hw
    · rintro ⟨w, rfl⟩
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul t y =>
        show Phi T hRT X (t ⊗ₜ (y : X)) ∈ _
        rw [Phi_tmul]
        exact Submodule.smul_mem _ t (Submodule.subset_span ⟨(y : X), y.2, rfl⟩)
      | add a c ha hc =>
        rw [map_add (f := _), map_add (f := _)]
        exact Submodule.add_mem _ ha hc
  have hmap : ((Submodule.span T (tm K K₁ '' (Y : Set U))).comap
      (Submodule.span T (tm K K₁ '' (X : Set U))).subtype).map (e1.symm : _ →ₗ[T] _) = LinearMap.range ι' := by
    ext z
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_comap, Submodule.subtype_apply, he1]
    exact hY z
  exact ((Submodule.Quotient.equiv _ _ e1.symm hmap).trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (Ψ.quotKerEquivOfSurjective hΨ))).length_eq

include hRT in
theorem span_inf_eq (X : Submodule R U) (hX : X.FG) (W : Submodule K U) :
    Submodule.span T (Submodule.span K₁ (tm K K₁ '' (W : Set U)) : Set (K₁ ⊗[K] U)) ⊓
        Submodule.span T (tm K K₁ '' (X : Set U)) =
      Submodule.span T (tm K K₁ '' ((X ⊓ W.restrictScalars R : Submodule R U) : Set U)) := by
  classical
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hzW, hzX⟩ := hz
    let fR : U →ₗ[R] U ⧸ W := W.mkQ.restrictScalars R
    let Xb : Submodule R (U ⧸ W) := X.map fR
    let g : X →ₗ[R] Xb := fR.submoduleMap X
    have hg : Function.Surjective g := LinearMap.submoduleMap_surjective fR X
    have hz0 : W.mkQ.baseChange K₁ z = 0 := by
      refine Submodule.span_induction (p := fun z _ => W.mkQ.baseChange K₁ z = 0) ?_ ?_ ?_ ?_ hzW
      · intro y hy
        refine Submodule.span_induction (p := fun y _ => W.mkQ.baseChange K₁ y = 0) ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨w, hw, rfl⟩
          show W.mkQ.baseChange K₁ ((1 : K₁) ⊗ₜ[K] w) = 0
          rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hw,
            TensorProduct.tmul_zero]
        · simp
        · intro a b _ _ ha hb
          rw [map_add (f := _), ha, hb, add_zero]
        · intro c a _ ha
          rw [map_smul, ha, smul_zero]
      · simp
      · intro a b _ _ ha hb
        rw [map_add (f := _), ha, hb, add_zero]
      · intro t a _ ha
        show W.mkQ.baseChange K₁ ((t : K₁) • a) = 0
        rw [map_smul, ha, smul_zero]
    have hzR : z ∈ LinearMap.range (Phi T hRT X) := by
      rw [Phi_range]
      exact hzX
    obtain ⟨w, rfl⟩ := hzR
    have hsq : ∀ w, Phi T hRT Xb (g.baseChange T w) = W.mkQ.baseChange K₁ (Phi T hRT X w) := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul t x =>
        rw [LinearMap.baseChange_tmul, Phi_tmul, Phi_tmul]
        show (t : K₁) • tm K K₁ ((g x : Xb) : U ⧸ W) = W.mkQ.baseChange K₁ ((t : K₁) • (1 : K₁) ⊗ₜ[K] (x : U))
        rw [map_smul, LinearMap.baseChange_tmul]
        rfl
      | add a c ha hc =>
        rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hc]
    have hw0 : g.baseChange T w = 0 := by
      apply Phi_injective T hRT Xb (hX.map _)
      rw [hsq, map_zero]
      exact hz0
    have hex : Function.Exact (LinearMap.ker g).subtype g :=
      LinearMap.exact_iff.2 (Submodule.range_subtype _).symm
    have hw0' : g.lTensor T w = 0 := by
      rw [← congrFun (LinearMap.baseChange_eq_ltensor (A := T) g) w]
      exact hw0
    obtain ⟨v, rfl⟩ := (lTensor_exact T hex hg w).1 hw0'
    clear hzW hzX hz0 hw0 hw0'
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul t y =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, Phi_tmul]
      have hyW : ((y : X) : U) ∈ W := by
        have hy : g (y : X) = 0 := y.2
        have h' : W.mkQ ((y : X) : U) = 0 := congrArg Subtype.val hy
        exact (Submodule.Quotient.mk_eq_zero W).1 h'
      exact Submodule.smul_mem _ t (Submodule.subset_span ⟨(y : X), ⟨(y : X).2, hyW⟩, rfl⟩)
    | add a c ha hc =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ ha hc
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxX, hxW⟩, rfl⟩
    refine ⟨?_, Submodule.subset_span ⟨x, hxX, rfl⟩⟩
    exact Submodule.subset_span (Submodule.subset_span ⟨x, hxW, rfl⟩)

end R

end Base

section DVR

theorem length_self_eq_top (T : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] :
    Module.length T T = ⊤ := by
  by_contra h
  have hfin := Module.length_ne_top_iff.mp h
  have hart : IsArtinianRing T := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  exact IsDiscreteValuationRing.not_isField T (IsArtinianRing.isField_of_isDomain T)

theorem length_quot_span_pow {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {p : R} (hp : Irreducible p) (e : ℕ) : Module.length R (R ⧸ R ∙ p ^ e) = e := by
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {p} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer p).1 hp
  have h := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R e
  rw [hm, Ideal.span_singleton_pow] at h
  exact h

theorem length_tensor_eq_top {R T : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra R T]
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N] (h : Module.length R N = ⊤) :
    Module.length T (T ⊗[R] N) = ⊤ := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum R N
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exfalso
    subst hn
    have h1 := f.length_eq
    rw [h, Module.length_prod, (DirectSum.linearEquivFunOnFintype R ι (fun i => R ⧸ R ∙ p i ^ e i)).length_eq,
      Module.length_pi_of_fintype] at h1
    have h0 : Module.length R (Fin 0 →₀ R) = 0 := by
      first
        | exact Module.length_eq_zero_iff.2 inferInstance
        | exact Module.length_eq_zero
    rw [h0, zero_add] at h1
    have h2 : ∑ i, Module.length R (R ⧸ R ∙ p i ^ e i) = ((∑ i, e i : ℕ) : ℕ∞) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun i _ => length_quot_span_pow (hp i) (e i)
    rw [h2] at h1
    exact ENat.coe_ne_top _ h1.symm
  · let g : N →ₗ[R] R := (Finsupp.lapply ⟨0, hn⟩) ∘ₗ (LinearMap.fst R _ _) ∘ₗ f.toLinearMap
    have hg : Function.Surjective g := by
      intro r
      refine ⟨f.symm (Finsupp.single ⟨0, hn⟩ r, 0), ?_⟩
      simp [g]
    let φ : T ⊗[R] N →ₗ[T] T := (TensorProduct.AlgebraTensorModule.rid R T T).toLinearMap ∘ₗ g.baseChange T
    have hφ : Function.Surjective φ := by
      have hb : Function.Surjective (g.baseChange T) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective T hg
      exact (TensorProduct.AlgebraTensorModule.rid R T T).surjective.comp hb
    have hle := Module.length_le_of_surjective φ hφ
    rw [length_self_eq_top] at hle
    exact top_le_iff.1 hle

end DVR

end Formalism.L2.Pj.QAt.TieLDA
end

namespace Formalism.L2.Pj.QAt

namespace TieLD

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

attribute [local instance] TieLDA.modT TieLDA.modR

theorem pow_maximalIdeal_inj {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    {a b : ℕ} (h : IsLocalRing.maximalIdeal T ^ a = IsLocalRing.maximalIdeal T ^ b) : a = b := by
  have h0 : IsLocalRing.maximalIdeal T ≠ ⊥ := IsDiscreteValuationRing.not_a_field T
  have h1 : IsLocalRing.maximalIdeal T ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal T).ne_top
  exact (Ideal.pow_right_strictAnti _ h0 h1).injective h

variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

noncomputable abbrev Tw (w : HeightOneSpectrum (𝓞 K₁)) : Subring K₁ := (w.valuationSubringAtPrime K₁).toSubring

noncomputable abbrev algCT (w : HeightOneSpectrum (𝓞 K₁)) : Algebra (𝓞 K₁) (Tw w) :=
  inferInstanceAs (Algebra (𝓞 K₁) (w.valuationSubringAtPrime K₁))

attribute [local instance] algCT

theorem locT (w : HeightOneSpectrum (𝓞 K₁)) : IsLocalization w.asIdeal.primeCompl (Tw w) :=
  inferInstanceAs (IsLocalization w.asIdeal.primeCompl (w.valuationSubringAtPrime K₁))

attribute [local instance] locT

theorem dvrT (w : HeightOneSpectrum (𝓞 K₁)) : IsDiscreteValuationRing (Tw w) := by
  first
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K₁) (NumberField.RingOfIntegers.not_isField K₁) w.ne_bot (Tw w)
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain w.ne_bot (Tw w)
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K₁) w.ne_bot (Tw w)

attribute [local instance] dvrT

theorem dvrLa (la : HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (Localization.AtPrime la.asIdeal) := by
  first
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) (NumberField.RingOfIntegers.not_isField K) la.ne_bot _
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain la.ne_bot _
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) la.ne_bot _

attribute [local instance] dvrLa

noncomputable abbrev algLaK (la : HeightOneSpectrum (𝓞 K)) :
    Algebra (Localization.AtPrime la.asIdeal) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ K la.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K)) la.asIdeal.primeCompl_le_nonZeroDivisors

attribute [local instance] algLaK

theorem towerLaK (la : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (Localization.AtPrime la.asIdeal) K := by
  first
    | exact IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _
    | exact IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.AtPrime la.asIdeal) K _ _ la.asIdeal.primeCompl_le_nonZeroDivisors
    | (apply IsScalarTower.of_algebraMap_eq; intro x; exact (IsLocalization.map_eq _ x).symm)

attribute [local instance] towerLaK

theorem fracLaK (la : HeightOneSpectrum (𝓞 K)) :
    IsFractionRing (Localization.AtPrime la.asIdeal) K := by
  first
    | exact IsFractionRing.isFractionRing_of_isLocalization la.asIdeal.primeCompl _ _ la.asIdeal.primeCompl_le_nonZeroDivisors
    | exact IsLocalization.isFractionRing_of_isDomain_of_isLocalization la.asIdeal.primeCompl _ _
    | exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization la.asIdeal.primeCompl _ _

attribute [local instance] fracLaK

theorem primeCompl_le (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) :
    la.asIdeal.primeCompl ≤ w.asIdeal.primeCompl.comap (algebraMap (𝓞 K) (𝓞 K₁)) := by
  intro x hx
  unfold LiesOver at hw
  rw [Submonoid.mem_comap, Ideal.mem_primeCompl_iff]
  rw [Ideal.mem_primeCompl_iff] at hx
  intro hxw
  apply hx
  rw [← hw]
  exact Ideal.mem_comap.mpr hxw

noncomputable def mapLaT (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) : Localization.AtPrime la.asIdeal →+* Tw w :=
  IsLocalization.map (M := la.asIdeal.primeCompl) (S := Localization.AtPrime la.asIdeal) (Tw w)
    (algebraMap (𝓞 K) (𝓞 K₁)) (T := w.asIdeal.primeCompl) (primeCompl_le la w hw)

theorem mapLaT_coe (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) (r : Localization.AtPrime la.asIdeal) :
    ((mapLaT la w hw r : Tw w) : K₁) =
      algebraMap K K₁ (algebraMap (Localization.AtPrime la.asIdeal) K r) := by
  have key : (Tw w).subtype.comp (mapLaT la w hw) =
      (algebraMap K K₁).comp (algebraMap (Localization.AtPrime la.asIdeal) K) := by
    apply IsLocalization.ringHom_ext la.asIdeal.primeCompl
    ext x
    simp only [RingHom.comp_apply, mapLaT, IsLocalization.map_eq]
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (Localization.AtPrime la.asIdeal) K]
    first
      | rfl
      | simp
      | (norm_cast; simp)
      | exact (trivial : True)
  exact RingHom.congr_fun key r

theorem ramificationIdx_ne_zero' (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := by
  unfold LiesOver at hw
  have hlo : w.asIdeal.LiesOver la.asIdeal := ⟨hw.symm⟩
  rw [← Ideal.ramificationIdx_eq_ramificationIdx' la.asIdeal w.asIdeal la.ne_bot]
  apply Ideal.IsDedekindDomain.ramificationIdx'_ne_zero <;>
    first
          | exact la.ne_bot
          | exact w.ne_bot
          | exact hlo
          | exact w.isPrime
          | infer_instance
          | exact Ideal.map_le_iff_le_comap.mpr hw.ge
          | exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 K₁))).not.mpr la.ne_bot
          | exact (Ideal.map_eq_bot_iff_of_injective (NoZeroSMulDivisors.algebraMap_injective (𝓞 K) (𝓞 K₁))).not.mpr la.ne_bot
          | exact Ideal.map_ne_bot_of_ne_bot la.ne_bot
          | exact (trivial : True)

theorem exists_rel (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) :
    ∃ (ϖ : Localization.AtPrime la.asIdeal) (ϖ₁ : Tw w) (u : (Tw w)ˣ), Irreducible ϖ ∧
      Irreducible ϖ₁ ∧ mapLaT la w hw ϖ = u * ϖ₁ ^ (w.asIdeal.ramificationIdx (𝓞 K)) := by
  have : w.asIdeal.LiesOver la.asIdeal := ⟨hw.symm⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime la.asIdeal)
  obtain ⟨ϖ₁, hϖ₁⟩ := IsDiscreteValuationRing.exists_irreducible (Tw w)
  have hinj : Function.Injective (mapLaT la w hw) := by
    intro x y hxy
    have h := congrArg (fun t : Tw w => (t : K₁)) hxy
    simp only [mapLaT_coe] at h
    exact IsFractionRing.injective (Localization.AtPrime la.asIdeal) K
      ((algebraMap K K₁).injective h)
  have h0 : mapLaT la w hw ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ₁
  have hmap0 : la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot la.ne_bot
  obtain ⟨Q, hQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hmap0 w.asIdeal
  generalize hc : Multiset.count w.asIdeal
    (UniqueFactorizationMonoid.normalizedFactors (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁)))) = c
    at hfac
  have hQw : ¬ Q ≤ w.asIdeal := fun hle => by
    rw [sup_eq_left.2 hle] at hQ
    exact w.isPrime.ne_top hQ
  have h1 : (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁))).map (algebraMap (𝓞 K₁) (Tw w)) =
      IsLocalRing.maximalIdeal (Tw w) ^ c := by
    rw [hfac, Ideal.map_mul, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_maximalIdeal (p := w.asIdeal) (Rₚ := Tw w),
      IsLocalization.AtPrime.map_eq_top_of_not_le (S := Tw w) hQw, Ideal.mul_top]
  have hcomp : (mapLaT la w hw).comp (algebraMap (𝓞 K) (Localization.AtPrime la.asIdeal)) =
      (algebraMap (𝓞 K₁) (Tw w)).comp (algebraMap (𝓞 K) (𝓞 K₁)) :=
    IsLocalization.map_comp _
  have h2 : (la.asIdeal.map (algebraMap (𝓞 K) (𝓞 K₁))).map (algebraMap (𝓞 K₁) (Tw w)) =
      Ideal.span {mapLaT la w hw ϖ} := by
    rw [Ideal.map_map, ← hcomp, ← Ideal.map_map,
      IsLocalization.AtPrime.map_eq_maximalIdeal (p := la.asIdeal)
        (Rₚ := Localization.AtPrime la.asIdeal),
      hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have h3 : Ideal.span {mapLaT la w hw ϖ} = IsLocalRing.maximalIdeal (Tw w) ^ n := by
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ₁.maximalIdeal_eq]
  have hn : n = c := pow_maximalIdeal_inj (h3.symm.trans (h2.symm.trans h1))
  have he : n = w.asIdeal.ramificationIdx (𝓞 K) := by
    rw [hn, ← hc, ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0
      w.isPrime w.ne_bot, Ideal.ramificationIdx'_eq_ramificationIdx la.asIdeal w.asIdeal la.ne_bot]
  exact ⟨ϖ, ϖ₁, u, hϖ, hϖ₁, by rw [hu, he]⟩

theorem main_eq (hL : Formalism.LatticeBaseChangeAlt.LengthBaseChangeLocal)
    {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (M : Submodule (𝓞 K) V) (hMfg : M.FG) (W : Submodule K V) {ρ : ℕ} (θ : Fin ρ → M)
    (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁)) (hw : LiesOver w la) :
    lenW w M W θ = (w.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) *
      lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
        (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) := by
  let _ : Algebra (Localization.AtPrime la.asIdeal) (Tw w) := (mapLaT la w hw).toAlgebra
  have hRT : ∀ r : Localization.AtPrime la.asIdeal,
      ((algebraMap (Localization.AtPrime la.asIdeal) (Tw w) r : Tw w) : K₁) =
        algebraMap K K₁ (algebraMap (Localization.AtPrime la.asIdeal) K r) := mapLaT_coe la w hw
  let _ : Module (Localization.AtPrime la.asIdeal) V :=
    Module.compHom V (algebraMap (Localization.AtPrime la.asIdeal) K)
  have : IsScalarTower (Localization.AtPrime la.asIdeal) K V := ⟨fun o k v => by
    change (o • k) • v = algebraMap _ K o • (k • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower (𝓞 K) (Localization.AtPrime la.asIdeal) V := ⟨fun a o v => by
    change algebraMap _ K (a • o) • v = a • (algebraMap _ K o • v)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul]⟩

  let θ' : Fin ρ → V := fun j => (θ j : V)
  let S : Set V := ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) ∪ Set.range θ'
  have hSM : S ⊆ (M : Set V) := by
    rintro x (hx | ⟨j, rfl⟩)
    · exact hx.1
    · exact (θ j).2
  let G : Submodule (𝓞 K) V := Submodule.span (𝓞 K) S
  have hGM : G ≤ M := Submodule.span_le.2 hSM
  let X : Submodule (Localization.AtPrime la.asIdeal) V :=
    Submodule.span (Localization.AtPrime la.asIdeal) (M : Set V)
  let Y : Submodule (Localization.AtPrime la.asIdeal) V :=
    Submodule.span (Localization.AtPrime la.asIdeal) S
  have hYG : Y = Submodule.span (Localization.AtPrime la.asIdeal) (G : Set V) := by
    show _ = Submodule.span _ (Submodule.span (𝓞 K) S : Set V)
    rw [Submodule.span_span_of_tower]

  let S₁ : Submodule (𝓞 K) M := (W.restrictScalars (𝓞 K)).comap M.subtype
  have hS₂ : G.comap M.subtype = S₁ ⊔ Submodule.span (𝓞 K) (Set.range θ) := by
    apply Submodule.map_injective_of_injective M.injective_subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hGM, Submodule.map_sup,
      Submodule.map_comap_subtype, Submodule.map_span, ← Set.range_comp]
    show Submodule.span (𝓞 K) S = _
    rw [Submodule.span_union, Submodule.span_eq]
    rfl
  have hmapQ : (G.comap M.subtype).map S₁.mkQ =
      Submodule.span (𝓞 K) (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W)) := by
    rw [hS₂, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span,
      ← Set.range_comp]
    rfl
  have hle : S₁ ≤ G.comap M.subtype := by rw [hS₂]; exact le_sup_left
  let e1 : (QuotMW M W ⧸ Submodule.span (𝓞 K)
      (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) ≃ₗ[𝓞 K]
      M ⧸ G.comap M.subtype :=
    (Submodule.quotEquivOfEq _ _ hmapQ.symm).trans
      (Submodule.quotientQuotientEquivQuotient S₁ (G.comap M.subtype) hle)
  have hA : lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
      (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))) =
      Module.length (Localization.AtPrime la.asIdeal) (X ⧸ Y.comap X.subtype) := by
    rw [hYG]
    exact TieLDB.length_localized_eq la.asIdeal M G e1

  have hXfg : X.FG := by
    obtain ⟨s, hs⟩ := hMfg
    refine ⟨s, ?_⟩
    show Submodule.span _ (s : Set V) = Submodule.span _ (M : Set V)
    rw [← hs, Submodule.span_span_of_tower]
  have hYX : Y ≤ X := Submodule.span_mono hSM
  have hMw : Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V)) =
      Submodule.span (Tw w) (TieLDA.tm K K₁ '' (X : Set V)) :=
    (TieLDA.span_tm_span (Tw w) hRT (M : Set V)).symm
  have hNw : (Submodule.span (Tw w)
        (Submodule.span K₁ (TieLDA.tm K K₁ '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓
        Submodule.span (Tw w) (TieLDA.tm K K₁ '' (X : Set V))) ⊔
      Submodule.span (Tw w) (Set.range fun j => TieLDA.tm K K₁ (θ' j)) =
      Submodule.span (Tw w) (TieLDA.tm K K₁ '' (Y : Set V)) := by
    rw [TieLDA.span_inf_eq (Tw w) hRT X hXfg W]
    have h1 : X ⊓ W.restrictScalars (Localization.AtPrime la.asIdeal) =
        Submodule.span (Localization.AtPrime la.asIdeal)
          ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) :=
      (TieLDB.span_inf_eq la.asIdeal M (W.restrictScalars (Localization.AtPrime la.asIdeal))).symm
    rw [h1, TieLDA.span_tm_span (Tw w) hRT]
    show _ = Submodule.span (Tw w) (TieLDA.tm K K₁ ''
      (Submodule.span (Localization.AtPrime la.asIdeal) S : Set V))
    rw [TieLDA.span_tm_span (Tw w) hRT, Set.image_union, Submodule.span_union, ← Set.range_comp]
    rfl
  have hW : lenW w M W θ = Module.length (Tw w)
      (↥(Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))) ⧸
        ((Submodule.span (Tw w)
          (Submodule.span K₁ (TieLDA.tm K K₁ '' (W : Set V)) : Set (K₁ ⊗[K] V)) ⊓
          Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))) ⊔
          Submodule.span (Tw w) (Set.range fun j => TieLDA.tm K K₁ (θ' j))).comap
          (Submodule.span (Tw w) (TieLDA.tm K K₁ '' (M : Set V))).subtype) := rfl
  rw [hW, hMw, hNw, TieLDA.length_quot_eq (Tw w) hRT X Y hXfg hYX, hA]

  have hfinX : Module.Finite (Localization.AtPrime la.asIdeal) X := Module.Finite.iff_fg.2 hXfg
  by_cases hN : Module.length (Localization.AtPrime la.asIdeal) (X ⧸ Y.comap X.subtype) = ⊤
  · have he : ((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : ℕ∞) ≠ 0 := by
      exact_mod_cast ramificationIdx_ne_zero' la w hw
    rw [TieLDA.length_tensor_eq_top (T := Tw w) _ hN, hN, ENat.mul_top he]
  · obtain ⟨ϖ, ϖ₁, u, hϖ, hϖ₁, hrel⟩ := exists_rel la w hw
    exact hL (Localization.AtPrime la.asIdeal) (Tw w) (X ⧸ Y.comap X.subtype) ϖ ϖ₁ u _ hϖ hϖ₁
      hrel hN

end TieLD

open TieLD in
theorem lenDescent_of_lengthBaseChangeLocal (h : Formalism.LatticeBaseChangeAlt.LengthBaseChangeLocal) :
    ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LenDescentStatement := by
  unfold ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LenDescentStatement
  intro K K₁ V _ _ _ _ _ _ _ _ _ _ M hMfg _ W ρ θ la w hw
  exact TieLD.main_eq h M hMfg W θ la w hw

theorem lenDescent_holds : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LenDescentStatement :=
  lenDescent_of_lengthBaseChangeLocal Formalism.LatticeBaseChangeAlt.lengthBaseChangeLocal

end Formalism.L2.Pj.QAt
