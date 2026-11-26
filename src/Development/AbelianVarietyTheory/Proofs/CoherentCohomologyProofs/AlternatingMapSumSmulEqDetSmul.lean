module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AlternatingMapSumSmulEqDetSmul
namespace GlobalTheory

open scoped BigOperators

section JetWedge

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {D : ℕ}

noncomputable def jetWedge (ω : M [⋀^Fin D]→ₗ[A] N) : (A × M) [⋀^Fin (D + 1)]→ₗ[A] N :=
  AlternatingMap.alternatizeUncurryFin
    ((LinearMap.fst A A M).smulRight (ω.compLinearMap (LinearMap.snd A A M)))

theorem jetWedge_apply (ω : M [⋀^Fin D]→ₗ[A] N) (v : Fin (D + 1) → A × M) :
    jetWedge ω v =
      ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * (v i).1) • ω (fun k => (v (i.succAbove k)).2) := by
  rw [jetWedge, AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul, ← Int.cast_smul_eq_zsmul A]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  rfl

theorem jetWedge_shear (ω : M [⋀^Fin D]→ₗ[A] N) (h : A) (u : M) (v : Fin (D + 1) → A × M) :
    jetWedge ω (fun i => (h * (v i).1, h • (v i).2 + (v i).1 • u)) = h ^ (D + 1) • jetWedge ω v := by
  classical
  let φ : (A × M) →ₗ[A] (A × M) :=
    (h • LinearMap.fst A A M).prod (h • LinearMap.snd A A M + (LinearMap.fst A A M).smulRight u)
  let g : Option M → A × M := fun o => o.elim (1, 0) (fun m => (0, m))
  have hg : Submodule.span A (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, m⟩ -
    have : ((a, m) : A × M) = a • g none + g (some m) := by simp [g]
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩))
      (Submodule.subset_span ⟨some m, rfl⟩)
  have key : ((jetWedge ω).compLinearMap φ).toMultilinearMap
      = (h ^ (D + 1) • jetWedge ω).toMultilinearMap := by
    refine MultilinearMap.ext_of_span_eq_top (g := fun _ => g) (fun _ => hg) fun j => ?_
    change jetWedge ω (fun i => φ (g (j i))) = h ^ (D + 1) • jetWedge ω (fun i => g (j i))
    by_cases hj : ∃ a b, a ≠ b ∧ j a = j b
    · obtain ⟨a, b, hab, hjab⟩ := hj
      rw [(jetWedge ω).map_eq_zero_of_eq _ (i := a) (j := b) (by simp only [hjab]) hab,
        (jetWedge ω).map_eq_zero_of_eq _ (i := a) (j := b) (by simp only [hjab]) hab, smul_zero]
    · push Not at hj
      rw [jetWedge_apply, jetWedge_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases hi : j i with
      | some m => simp [φ, g]
      | none =>
        have hk : ∀ k : Fin D, (g (j (i.succAbove k))).1 = 0 := by
          intro k
          cases hk : j (i.succAbove k) with
          | some m => simp [g]
          | none => exact absurd (hk.trans hi.symm) (hj _ _ (Fin.succAbove_ne i k))
        have : (fun k : Fin D => (φ (g (j (i.succAbove k)))).2)
            = fun k : Fin D => h • (g (j (i.succAbove k))).2 := by
          funext k
          simp [φ, hk k]
        rw [this, ω.map_smul_univ (fun _ => h)]
        simp only [φ, g, smul_smul]
        congr 1
        simp
        ring
  exact congrArg (fun F => F v) key

theorem alternating_map_sum_smul_eq_det_smul {n : ℕ} (ω : M [⋀^Fin n]→ₗ[A] N)
    (a : Matrix (Fin n) (Fin n) A) (w : Fin n → M) :
    ω (fun i => ∑ k, a i k • w k) = a.det • ω w := by
  classical
  let φ : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A w
  have key : ω.compLinearMap φ
      = ((LinearMap.toSpanSingleton A N (ω w)).compAlternatingMap Matrix.detRowAlternating) := by
    refine Module.Basis.ext_alternating (Pi.basisFun A (Fin n)) fun v hv => ?_
    have hb : Function.Bijective v := Finite.injective_iff_bijective.mp hv
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v hb
    have e1 : (fun i => (Pi.basisFun A (Fin n)) (v i)) = (Pi.basisFun A (Fin n)) ∘ σ := rfl
    rw [e1, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e2 : (Matrix.detRowAlternating : (Fin n → A) [⋀^Fin n]→ₗ[A] A) (Pi.basisFun A (Fin n))
        = 1 := by
      rw [← Matrix.det_one (n := Fin n)]
      change Matrix.det _ = _
      congr 1
      ext i j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simp only [LinearMap.compAlternatingMap_apply, e2, LinearMap.toSpanSingleton_apply, one_smul,
      AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp [φ]
  have := congrArg (fun F : (Fin n → A) [⋀^Fin n]→ₗ[A] N => F a) key
  have e3 : (fun i => ∑ k, a i k • w k) = fun i => φ (a i) := by
    funext i
    exact (Fintype.linearCombination_apply A w (a i)).symm
  rw [e3]
  exact this

theorem alternating_sub_mem_smul_top (ω : M [⋀^Fin D]→ₗ[A] N) (I : Ideal A) (v w : Fin D → M)
    (hvw : ∀ k, v k - w k ∈ I • (⊤ : Submodule A M)) :
    ω v - ω w ∈ I • (⊤ : Submodule A N) := by
  classical
  have key : ∀ s : Finset (Fin D), ω (s.piecewise v w) - ω w ∈ I • (⊤ : Submodule A N) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      have h1 : s.piecewise v w = Function.update (s.piecewise v w) i (w i) := by
        rw [eq_comm, Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hi]
      have h2 : ω ((insert i s).piecewise v w) - ω (s.piecewise v w)
          = ω.toMultilinearMap.toLinearMap (s.piecewise v w) i (v i - w i) := by
        rw [map_sub, Finset.piecewise_insert]
        conv_lhs => rw [h1]
        simp
      have h3 : ω ((insert i s).piecewise v w) - ω (s.piecewise v w)
          ∈ I • (⊤ : Submodule A N) := by
        rw [h2]
        have := Submodule.mem_map_of_mem
          (f := ω.toMultilinearMap.toLinearMap (s.piecewise v w) i) (hvw i)
        rw [Submodule.map_smul''] at this
        exact Submodule.smul_mono le_rfl le_top this
      simpa using add_mem h3 ih
  simpa using key Finset.univ

end JetWedge

section JacForm

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [AddCommGroup N] [Module A N] {D : ℕ}

noncomputable def jacForm (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)
    (f : Fin (D + 1) → A) : N :=
  ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * f i) • ω (fun k => d (f (i.succAbove k)))

variable (d : Derivation R A M) (ω : M [⋀^Fin D]→ₗ[A] N)

theorem jacForm_eq_jetWedge (f : Fin (D + 1) → A) :
    jacForm d ω f = jetWedge ω (fun i => (f i, d (f i))) := by
  rw [jetWedge_apply, jacForm]

theorem jacForm_mul (h : A) (f : Fin (D + 1) → A) :
    jacForm d ω (fun i => h * f i) = h ^ (D + 1) • jacForm d ω f := by
  rw [jacForm_eq_jetWedge, jacForm_eq_jetWedge, ← jetWedge_shear ω h (d h)]
  simp only [Derivation.leibniz]

theorem form_d_mul_sub_mem (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    ω (fun k => d (h * g k)) - h ^ D • ω (fun k => d (g k)) ∈ I • (⊤ : Submodule A N) := by
  have : h ^ D • ω (fun k => d (g k)) = ω (fun k => h • d (g k)) := by
    rw [ω.map_smul_univ (fun _ => h)]
    simp
  rw [this]
  refine alternating_sub_mem_smul_top ω I _ _ fun k => ?_
  rw [Derivation.leibniz, add_sub_cancel_left]
  exact Submodule.smul_mem_smul (hg k) Submodule.mem_top

variable [Module R N] [IsScalarTower R A N] [IsScalarTower R A M]

end JacForm

section RestrictScalars

variable (A : Type*) {B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {D : ℕ}

def altRestrictScalars (ω : M [⋀^Fin D]→ₗ[B] N) : M [⋀^Fin D]→ₗ[A] N where
  toMultilinearMap := ω.toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' v _ _ hv hij := ω.map_eq_zero_of_eq v hv hij

variable {A} {L : Type*} [AddCommGroup L] [Module A L]

variable (B D) in
noncomputable def exteriorPowerMapOver (φ : L →ₗ[A] M) : (⋀[A]^D L) →ₗ[A] (⋀[B]^D M) :=
  exteriorPower.alternatingMapLinearEquiv
    ((altRestrictScalars A (exteriorPower.ιMulti B D (M := M))).compLinearMap φ)

@[simp] theorem exteriorPowerMapOver_ιMulti (φ : L →ₗ[A] M) (v : Fin D → L) :
    exteriorPowerMapOver B D φ (exteriorPower.ιMulti A D v)
      = exteriorPower.ιMulti B D (fun k => φ (v k)) := by
  simp only [exteriorPowerMapOver,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

end RestrictScalars

section Jac

variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}

open KaehlerDifferential

noncomputable def dWedge (g : Fin D → A) : ⋀[A]^D Ω[A⁄R] :=
  exteriorPower.ιMulti A D (fun k => KaehlerDifferential.D R A (g k))

noncomputable def jac (f : Fin (D + 1) → A) : ⋀[A]^D Ω[A⁄R] :=
  ∑ i : Fin (D + 1), ((-1 : A) ^ (i : ℕ) * f i) • dWedge R (fun k => f (i.succAbove k))

theorem jac_mul (h : A) (f : Fin (D + 1) → A) :
    jac R (fun i => h * f i) = h ^ (D + 1) • jac R f :=
  jacForm_mul _ _ h f

theorem dWedge_mul_sub_mem (I : Ideal A) (h : A) (g : Fin D → A) (hg : ∀ k, g k ∈ I) :
    dWedge R (fun k => h * g k) - h ^ D • dWedge R g ∈ I • (⊤ : Submodule A (⋀[A]^D Ω[A⁄R])) :=
  form_d_mul_sub_mem _ _ I h g hg


variable {R}

theorem map_jac (S B : Type*) [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [IsScalarTower R S B] [SMulCommClass S A B]
    (f : Fin (D + 1) → A) :
    exteriorPowerMapOver B D (KaehlerDifferential.map R S A B) (jac R f)
      = jac S (fun i => algebraMap A B (f i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [jac, jac, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, dWedge, exteriorPowerMapOver_ιMulti, ← algebraMap_smul B]
  simp [dWedge]

end Jac

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBaseChangeQuotientOfMapMaximalIdeal
open IsLocalRing TensorProduct

namespace GlobalTheory

section Local

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

theorem nonempty_baseChange_subquotient_equiv [Module.Flat R S] {X : Type*} [AddCommGroup X]
    [Module R X] (A B : Submodule R X) :
    Nonempty ((S ⊗[R] (A ⧸ B.submoduleOf A)) ≃ₗ[S]
      (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S))) := by
  let h : S ⊗[R] A →ₗ[S] S ⊗[R] (A ⧸ B.submoduleOf A) := (B.submoduleOf A).mkQ.baseChange S
  let g : S ⊗[R] A →ₗ[S] (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) :=
    ((B.baseChange S).submoduleOf (A.baseChange S)).mkQ ∘ₗ A.toBaseChange S
  have hh : Function.Surjective h :=
    LinearMap.lTensor_surjective S (B.submoduleOf A).mkQ_surjective
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (A.toBaseChange_surjective S)
  have e₁ : Function.Exact ((B.submoduleOf A).subtype.lTensor S)
      ((B.submoduleOf A).mkQ.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ _)
  have e₂ : Function.Exact ((B.submoduleOf A).subtype.lTensor S)
      ((B.mkQ ∘ₗ A.subtype).lTensor S) := by
    apply Module.Flat.lTensor_exact S
    rw [LinearMap.exact_iff, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype]
    rfl
  have e₃ : Function.Exact (B.subtype.lTensor S) (B.mkQ.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ _)
  have hker : LinearMap.ker h = LinearMap.ker g := by
    ext x
    have h1 : x ∈ LinearMap.ker h ↔ (B.submoduleOf A).mkQ.lTensor S x = 0 := Iff.rfl
    have h2 : x ∈ LinearMap.ker g ↔ A.subtype.lTensor S x ∈ B.baseChange S := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      rfl
    rw [h1, h2, e₁ x, ← e₂ x, LinearMap.lTensor_comp, LinearMap.comp_apply, e₃]
    rfl
  exact ⟨(h.quotKerEquivOfSurjective hh).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    g.quotKerEquivOfSurjective hg⟩

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
  (X : Type*) [AddCommGroup X] [Module R X]

theorem length_baseChange_flat :
    Module.length S (S ⊗[R] X) =
      Module.length R X * Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
  IsLocalRing.length_baseChange R S X


variable {X} in
theorem length_baseChange_subquotient_flat (A B : Submodule R X) :
    Module.length S (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) =
      Module.length R (A ⧸ B.submoduleOf A) *
        Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  rw [← length_baseChange_flat]
  exact (nonempty_baseChange_subquotient_equiv R S A B).some.length_eq.symm

variable {R S}

end Local

section DVR

open IsDiscreteValuationRing hiding maximalIdeal

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]

theorem length_quotient_span_singleton_eq_addVal {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (x : S) :
    Module.length S (S ⧸ Ideal.span {x}) = addVal S x := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  rcases eq_or_ne x 0 with rfl | hx
  · rw [addVal_zero, Ideal.span_singleton_zero,
      (Submodule.quotEquivOfEqBot (⊥ : Ideal S) rfl).length_eq]
    by_contra h
    have h' := Module.length_ne_top_iff.mp h
    rw [← isArtinianRing_iff_isFiniteLength] at h'
    exact not_isField S (IsArtinianRing.isField_of_isDomain S)
  · obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
    rw [addVal_def' u hπ, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq, length_quotient_pow_maximalIdeal]

variable [IsLocalHom (algebraMap R S)]

theorem map_maximalIdeal_eq_pow_ramificationIdx :
    (maximalIdeal R).map (algebraMap R S) =
      maximalIdeal S ^ ((maximalIdeal S).ramificationIdx R) := by
  have hp : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hpS : (maximalIdeal R).map (algebraMap R S) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  obtain ⟨π, hπ⟩ := exists_irreducible S
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible hpS hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at hn
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal S) hp,
    Ideal.ramificationIdx'_spec (n := n) hn.le, hn]
  rw [hn]
  exact (Ideal.pow_succ_lt_pow (IsDiscreteValuationRing.not_a_field S) n).not_ge

theorem length_fibre_eq_ramificationIdx :
    Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) =
      ((maximalIdeal S).ramificationIdx R : ℕ) := by
  conv_lhs => rw [map_maximalIdeal_eq_pow_ramificationIdx]
  exact length_quotient_pow_maximalIdeal S _

theorem ramificationIdx_maximalIdeal_pos : 0 < (maximalIdeal S).ramificationIdx R := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have := map_maximalIdeal_eq_pow_ramificationIdx R S
  rw [h, pow_zero, Ideal.one_eq_top] at this
  exact (map_maximalIdeal_lt_top (algebraMap R S)).ne this


variable {R} in
theorem addVal_algebraMap_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) :
    addVal S (algebraMap R S ϖ) = ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [← length_fibre_eq_ramificationIdx, ← length_quotient_span_singleton_eq_addVal,
    hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]


variable {R} in
theorem addVal_algebraMap (x : R) :
    addVal S (algebraMap R S x) = addVal R x * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, addVal_zero, addVal_zero, ENat.top_mul]
    exact_mod_cast (ramificationIdx_maximalIdeal_pos R S).ne'
  · obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
    rw [addVal_def' u hϖ, map_mul, map_pow, addVal_mul, addVal_pow,
      addVal_algebraMap_uniformizer S hϖ,
      addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap R S)), zero_add, nsmul_eq_mul]

variable (X : Type*) [AddCommGroup X] [Module R X]

theorem length_baseChange_dvr :
    Module.length S (S ⊗[R] X) =
      Module.length R X * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [length_baseChange_flat, length_fibre_eq_ramificationIdx]


variable {X} in
theorem length_baseChange_subquotient_dvr (A B : Submodule R X) :
    Module.length S (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) =
      Module.length R (A ⧸ B.submoduleOf A) * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [length_baseChange_subquotient_flat, length_fibre_eq_ramificationIdx]

end DVR

section Uniformizer

open IsDiscreteValuationRing hiding maximalIdeal

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]

end Uniformizer

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
namespace GlobalTheory.InnerAutomorphism

section Inner

variable {A : Type*} (R : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

def innerAut (u : Aˣ) : A ≃ₐ[R] A where
  toFun x := (u : A) * x * ((u⁻¹ : Aˣ) : A)
  invFun x := ((u⁻¹ : Aˣ) : A) * x * (u : A)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

end Inner

section Bounded

variable {K n : Type*} [NormedField K]

def EntriesBounded (M : Matrix n n K) (c : ℝ) : Prop :=
  ∀ i j, ‖M i j‖ ≤ c

end Bounded

section DropLast

variable (K : Type*) [Semiring K] (d : ℕ)

def dropLast : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) where
  toFun x i := x i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end DropLast

section Split

variable {ι : Type*} [DecidableEq ι] (F : ι → Type*)

def sigmaSplit (j : ι) : (Σ i, F i) ≃ F j ⊕ (Σ i : {i // i ≠ j}, F i.1) where
  toFun p := if h : p.1 = j then Sum.inl (h ▸ p.2) else Sum.inr ⟨⟨p.1, h⟩, p.2⟩
  invFun s := Sum.elim (fun x => ⟨j, x⟩) (fun q => ⟨q.1.1, q.2⟩) s
  left_inv := by
    rintro ⟨i, x⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  right_inv := by
    rintro (x | ⟨⟨i, hi⟩, x⟩)
    · simp
    · simp [show ¬ i = j from hi]

theorem sigmaSplit_self (j : ι) (x : F j) : sigmaSplit F j ⟨j, x⟩ = Sum.inl x :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

theorem sigmaSplit_of_ne {i j : ι} (h : i ≠ j) (x : F i) :
    sigmaSplit F j ⟨i, x⟩ = Sum.inr ⟨⟨i, h⟩, x⟩ :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

end Split

end GlobalTheory.InnerAutomorphism
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanSingletonEqTopIffIsUnitOfIsBaseChange
open TensorProduct

namespace GlobalTheory

namespace Descent

section Algebra

variable {A : Type*} (A' : Type*) [CommRing A] [CommRing A'] [Algebra A A']
  [Module.FaithfullyFlat A A'] {M : Type*} [AddCommGroup M] [Module A M]

theorem finite [Module.Finite A' (A' ⊗[A] M)] : Module.Finite A M :=
  Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A'

theorem flat [Module.Flat A' (A' ⊗[A] M)] : Module.Flat A M :=
  Module.Flat.of_flat_tensorProduct A M A'

theorem fg_of_baseChange {N : Submodule A M} (h : (N.baseChange A').FG) : N.FG := by
  have hinj : Function.Injective (N.subtype.baseChange A') :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := A') N.subtype N.injective_subtype
  have e : A' ⊗[A] N ≃ₗ[A'] N.baseChange A' := LinearEquiv.ofInjective _ hinj
  have : Module.Finite A' (N.baseChange A') := Module.Finite.iff_fg.mpr h
  have : Module.Finite A' (A' ⊗[A] N) := Module.Finite.equiv e.symm
  exact Module.Finite.iff_fg.mp (finite A')

theorem finitePresentation [Module.FinitePresentation A' (A' ⊗[A] M)] :
    Module.FinitePresentation A M := by
  have : Module.Finite A M := finite A'
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  refine Module.finitePresentation_of_free_of_surjective f hf (fg_of_baseChange A' ?_)
  have hf' : Function.Surjective (f.baseChange A') := LinearMap.lTensor_surjective A' hf
  have hker : (LinearMap.ker f).baseChange A' = LinearMap.ker (f.baseChange A') := by
    have hex : Function.Exact ((LinearMap.ker f).subtype.baseChange A') (f.baseChange A') :=
      lTensor_exact A' (LinearMap.exact_subtype_ker_map f) hf
    exact (LinearMap.exact_iff.mp hex).symm
  rw [hker]
  exact Module.FinitePresentation.fg_ker _ hf'

theorem projective [Module.Finite A' (A' ⊗[A] M)] [Module.Projective A' (A' ⊗[A] M)] :
    Module.Projective A M := by
  have : Module.FinitePresentation A' (A' ⊗[A] M) := Module.finitePresentation_of_projective _ _
  have : Module.FinitePresentation A M := finitePresentation A'
  have : Module.Flat A M := flat A'
  exact Module.Flat.projective_of_finitePresentation

end Algebra

section IsBaseChange

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [Module.FaithfullyFlat A A']
  {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module A' M']
  [IsScalarTower A A' M'] {f : M →ₗ[A] M'} (hf : IsBaseChange A' f)

include hf

theorem finite_of_isBaseChange [Module.Finite A' M'] : Module.Finite A M :=
  have := Module.Finite.equiv hf.equiv.symm
  finite A'

theorem projective_of_isBaseChange [Module.Finite A' M'] [Module.Projective A' M'] :
    Module.Projective A M :=
  have := Module.Finite.equiv hf.equiv.symm
  have := Module.Projective.of_equiv hf.equiv.symm
  projective A'

end IsBaseChange

section Scheme

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}} (F : X.Modules)

noncomputable instance stalkModule (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x

theorem germ_smul (U : X.Opens) (x : X) (hx : x ∈ U) (r : Γ(X, U)) (m : Γ(F, U)) :
    F.presheaf.germ U x hx (r • m) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx m :=
  PresheafOfModules.germ_smul (R := X.presheaf) F.val x U hx r m

variable {F} {U : X.Opens} {s : Γ(F, U)}

theorem injective_smul_of_stalk {V : X.Opens} (hV : V ≤ U)
    (h : ∀ (x : X) (hx : x ∈ V), Function.Injective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x (hV hx) s) :
    Function.Injective fun a : Γ(X, V) ↦ a • F.presheaf.map (homOfLE hV).op s := by
  intro a b hab
  apply TopCat.Presheaf.section_ext X.sheaf V a b
  intro x hx
  apply h x hx
  have := congrArg (F.presheaf.germ V x hx) hab
  simp only [germ_smul, TopCat.Presheaf.germ_res_apply] at this
  exact this

theorem bijective_smul_of_stalk
    (h : ∀ (x : X) (hx : x ∈ U), Function.Bijective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s)
    {V : X.Opens} (hV : V ≤ U) :
    Function.Bijective fun a : Γ(X, V) ↦ a • F.presheaf.map (homOfLE hV).op s := by
  refine ⟨injective_smul_of_stalk hV fun x hx ↦ (h x (hV hx)).1, fun t ↦ ?_⟩
  have hloc : ∀ x : V, ∃ (W : X.Opens) (_ : x.1 ∈ W) (hW : W ≤ V) (a : Γ(X, W)),
      a • F.presheaf.map (homOfLE (hW.trans hV)).op s = F.presheaf.map (homOfLE hW).op t := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := (h x (hV hx)).2 (F.presheaf.germ V x hx t)
    obtain ⟨W, hWV, hxW, a, rfl⟩ := X.presheaf.exists_le_germ_eq a hx
    have h₁ : F.presheaf.germ W x hxW (a • F.presheaf.map (homOfLE (hWV.trans hV)).op s) =
        F.presheaf.germ V x hx t := by
      rw [germ_smul, TopCat.Presheaf.germ_res_apply]
      exact ha
    obtain ⟨W', hxW', i₁, i₂, e⟩ := F.presheaf.germ_eq x hxW hx _ _ h₁
    refine ⟨W', hxW', i₂.le, X.presheaf.map i₁.op a, ?_⟩
    rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp] at e
    exact e
  choose W hxW hWV a ha using hloc
  have hcover : V ≤ iSup W := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf W a := by
    intro i j
    have hij : W i ⊓ W j ≤ U := inf_le_left.trans ((hWV i).trans hV)
    apply injective_smul_of_stalk (s := s) hij fun x hx ↦ (h x (hij hx)).1
    have e₁ := congrArg (F.presheaf.map (Opens.infLELeft (W i) (W j)).op) (ha i)
    have e₂ := congrArg (F.presheaf.map (Opens.infLERight (W i) (W j)).op) (ha j)
    rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp,
      ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp] at e₁ e₂
    exact e₁.trans e₂.symm
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i ↦ homOfLE (hWV i)) hcover a hcomp
  refine ⟨b, ?_⟩
  change Γ(X, V) at b
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) W V
    (fun i ↦ homOfLE (hWV i)) hcover
  intro i
  have hb' : X.presheaf.map (homOfLE (hWV i)).op b = a i := hb i
  change F.presheaf.map (homOfLE (hWV i)).op (b • F.presheaf.map (homOfLE hV).op s) =
    F.presheaf.map (homOfLE (hWV i)).op t
  rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp, hb', ← ha i]
  rfl

theorem bijective_smul_stalk
    (h : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective fun a : Γ(X, V) ↦ a • F.presheaf.map (homOfLE hV).op s)
    (x : X) (hx : x ∈ U) :
    Function.Bijective fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s := by
  constructor
  · intro a b hab
    obtain ⟨V, hVU, hxV, a, rfl⟩ := X.presheaf.exists_le_germ_eq a hx
    obtain ⟨W, hWV, hxW, b, rfl⟩ := X.presheaf.exists_le_germ_eq b hxV
    have h₁ : F.presheaf.germ V x hxV (a • F.presheaf.map (homOfLE hVU).op s) =
        F.presheaf.germ W x hxW (b • F.presheaf.map (homOfLE (hWV.trans hVU)).op s) := by
      rw [germ_smul, germ_smul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
      exact hab
    obtain ⟨W', hxW', i₁, i₂, e⟩ := F.presheaf.germ_eq x hxV hxW _ _ h₁
    rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp,
      Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp] at e
    exact X.presheaf.germ_ext W' hxW' i₁ i₂ ((h W' (i₁.le.trans hVU)).1 e)
  · intro t
    obtain ⟨V, hVU, hxV, t, rfl⟩ := F.presheaf.exists_le_germ_eq t hx
    obtain ⟨a, rfl⟩ := (h V hVU).2 t
    refine ⟨X.presheaf.germ V x hxV a, ?_⟩
    simp only [germ_smul, TopCat.Presheaf.germ_res_apply]


variable (s) in
noncomputable def sectionHom :
    @Quiver.Hom (U : Scheme.{u}).Modules _ (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)
      (F.restrict U.ι) :=
  (SheafOfModules.unitHomEquiv (F.restrict U.ι)).symm
    (PresheafOfModules.sectionsMk
      (fun W ↦ F.presheaf.map (homOfLE (U.ι_image_le W.unop)).op s)
      (fun W W' i ↦ by
        change F.presheaf.map _ (F.presheaf.map _ s) = _
        rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
        rfl))


variable (s) in
theorem sectionHom_app (W : (U : Scheme.{u}).Opens) (a : Γ(X, U.ι ''ᵁ W)) :
    ((sectionHom (s := s)).app W a : Γ(F, U.ι ''ᵁ W)) =
      a • F.presheaf.map (homOfLE (U.ι_image_le W)).op s := by
  have h1 : (sectionHom (s := s)).app W (1 : Γ((U : Scheme.{u}), W)) =
      F.presheaf.map (homOfLE (U.ι_image_le W)).op s := by
    have := SheafOfModules.unitHomEquiv_apply_coe (F.restrict U.ι) (sectionHom (s := s)) (op W)
    rw [sectionHom, Equiv.apply_symm_apply] at this
    exact this.symm
  have h2 := Scheme.Modules.Hom.app_smul (sectionHom (s := s)) (U := W) a
    (1 : Γ((U : Scheme.{u}), W))
  have h3 : a = a * 1 := (mul_one a).symm
  refine (congrArg ((sectionHom (s := s)).app W) h3).trans (h2.trans ?_)
  rw [h1]
  change ((U.ι.appIso W).inv a) • F.presheaf.map (homOfLE (U.ι_image_le W)).op s = _
  rw [Scheme.Opens.ι_appIso]
  rfl

theorem isIso_sectionHom_iff :
    IsIso (sectionHom (s := s)) ↔ ∀ (x : X) (hx : x ∈ U), Function.Bijective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.trans ?_
  have key (W : (U : Scheme.{u}).Opens) : IsIso ((sectionHom (s := s)).app W) ↔ Function.Bijective
      fun a : Γ(X, U.ι ''ᵁ W) ↦ a • F.presheaf.map (homOfLE (U.ι_image_le W)).op s := by
    rw [ConcreteCategory.isIso_iff_bijective, ← funext (sectionHom_app (s := s) W)]
    rfl
  simp_rw [key]
  refine ⟨fun h ↦ bijective_smul_stalk fun V hV ↦ ?_, fun h W ↦ bijective_smul_of_stalk h _⟩
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hV]
  obtain ⟨W, rfl⟩ : ∃ W, U.ι ''ᵁ W = V := ⟨_, e⟩
  exact h W

noncomputable def freeIso
    (h : ∀ (x : X) (hx : x ∈ U), Function.Bijective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s) :
    @Iso (U : Scheme.{u}).Modules _ (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)
      (F.restrict U.ι) :=
  @asIso _ _ _ _ (sectionHom (s := s)) (isIso_sectionHom_iff.mpr h)

end Scheme

end Descent

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DoubleCosetSetoidRelIffMem
namespace GlobalTheory.DoubleCosetSetoid

section Rep

variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]

def repStabilizer (ρ : Representation k G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]

end Rep

section Cont

variable {𝕜 G E : Type*} [NontriviallyNormedField 𝕜] [Group G] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]

def clmStabilizer (π : G →* (E →L[𝕜] E)) (v : E) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ContinuousLinearMap.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply]

end Cont

section DoubleCoset

variable {G : Type*} [Group G]

def doubleCosetSetoid (H K : Subgroup G) : Setoid G where
  r x y := ∃ h ∈ H, ∃ k ∈ K, y = h * x * k
  iseqv :=
    { refl := fun x => ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      symm := by
        rintro x y ⟨h, hh, k, hk, rfl⟩
        exact ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, by group⟩
      trans := by
        rintro x y z ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        exact ⟨h' * h, H.mul_mem hh' hh, k * k', K.mul_mem hk hk', by group⟩ }

end DoubleCoset

end GlobalTheory.DoubleCosetSetoid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ContractMultilinearApply
open scoped TensorProduct BigOperators

namespace GlobalTheory.MultilinearContraction

section

variable {ι : Type*} [Fintype ι] [dι : DecidableEq ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

omit [Fintype ι] dι in
private theorem apply_update (φ : ∀ i, X i →ₗ[R] R) [inst : DecidableEq ι] (x : ∀ i, X i) (k : ι)
    (y : X k) (i : ι) :
    φ i (Function.update x k y i) = Function.update (fun i => φ i (x i)) k (φ k y) i := by
  by_cases h : i = k
  · subst h
    simp
  · simp [Function.update_of_ne h]

def contractMultilinear (φ : ∀ i, X i →ₗ[R] R) (j : ι) : (Π i, X i) →ₘₗ[R] X j where
  toFun x := (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j
  map_update_add' := by
    intro inst x k y z
    have h₁ : j ∉ @Finset.erase ι dι Finset.univ j := @Finset.notMem_erase ι dι j Finset.univ
    have h₂ : k ≠ j → k ∈ @Finset.erase ι dι Finset.univ j := fun h =>
      (@Finset.mem_erase ι dι _ _ _).2 ⟨h, Finset.mem_univ _⟩
    generalize @Finset.erase ι dι Finset.univ j = S at h₁ h₂ ⊢
    simp only [apply_update]
    by_cases h : k = j
    · subst h
      simp only [Finset.prod_update_of_notMem h₁,
        Function.update_self, smul_add]
    · have hk := h₂ h
      simp only [Finset.prod_update_of_mem hk, Function.update_of_ne (Ne.symm h), map_add (f := _),
        add_mul, add_smul]
  map_update_smul' := by
    intro inst x k c y
    have h₁ : j ∉ @Finset.erase ι dι Finset.univ j := @Finset.notMem_erase ι dι j Finset.univ
    have h₂ : k ≠ j → k ∈ @Finset.erase ι dι Finset.univ j := fun h =>
      (@Finset.mem_erase ι dι _ _ _).2 ⟨h, Finset.mem_univ _⟩
    generalize @Finset.erase ι dι Finset.univ j = S at h₁ h₂ ⊢
    simp only [apply_update]
    by_cases h : k = j
    · subst h
      simp only [Finset.prod_update_of_notMem h₁, Function.update_self, RingHom.id_apply]
      exact smul_comm _ _ _
    · have hk := h₂ h
      simp only [Finset.prod_update_of_mem hk, Function.update_of_ne (Ne.symm h), map_smul,
        RingHom.id_apply, smul_eq_mul, mul_assoc, mul_smul]

@[simp] theorem contractMultilinear_apply (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contractMultilinear φ j x = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := rfl

noncomputable def contract (φ : ∀ i, X i →ₗ[R] R) (j : ι) : (⨂[R] i, X i) →ₗ[R] X j :=
  PiTensorProduct.lift (contractMultilinear φ j)

theorem contract_def (φ : ∀ i, X i →ₗ[R] R) (j : ι) :
    contract φ j = PiTensorProduct.lift (contractMultilinear φ j) := rfl

@[simp] theorem contract_tprod (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contract φ j (⨂ₜ[R] i, x i) = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := by
  rw [contract_def, PiTensorProduct.lift.tprod, contractMultilinear_apply]

end

section

variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

def prodMultilinear (φ : ∀ i, X i →ₗ[R] R) : (Π i, X i) →ₘₗ[R] R :=
  (MultilinearMap.mkPiAlgebra R ι R).compLinearMap φ

@[simp] theorem prodMultilinear_apply (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodMultilinear φ x = ∏ i, φ i (x i) := rfl

noncomputable def prodForm (φ : ∀ i, X i →ₗ[R] R) : (⨂[R] i, X i) →ₗ[R] R :=
  PiTensorProduct.lift (prodMultilinear φ)

theorem prodForm_def (φ : ∀ i, X i →ₗ[R] R) :
    prodForm φ = PiTensorProduct.lift (prodMultilinear φ) := rfl

@[simp] theorem prodForm_tprod (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodForm φ (⨂ₜ[R] i, x i) = ∏ i, φ i (x i) := by
  rw [prodForm_def, PiTensorProduct.lift.tprod, prodMultilinear_apply]

end

end GlobalTheory.MultilinearContraction
end
