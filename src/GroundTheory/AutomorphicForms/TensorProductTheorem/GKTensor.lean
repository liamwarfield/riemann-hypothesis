module

public import GroundTheory.AutomorphicForms.TensorProductTheorem.KProjApplyEqSelfIff
public import GroundTheory.AutomorphicForms.TensorProductTheorem.TwoFactorUnique

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.TensorProductTheorem.CoeToRepresentationApply
noncomputable section

namespace GroundTheory.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Set Module

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G} {V : Type*} [AddCommGroup V] [Module ℂ V]

def GKModule.rep (M : h.GKModule K V) :
    Representation ℂ (FreeMonoid (h.lieSubalgebra ⊕ K)) V :=
  FreeMonoid.lift (Sum.elim (fun X => M.ρ X) fun k => M.σ k)

@[simp] theorem GKModule.rep_of_inl (M : h.GKModule K V) (X : h.lieSubalgebra) :
    M.rep (FreeMonoid.of (Sum.inl X)) = M.ρ X :=
  rfl

@[simp] theorem GKModule.rep_of_inr (M : h.GKModule K V) (k : K) :
    M.rep (FreeMonoid.of (Sum.inr k)) = M.σ k :=
  rfl

def GKModule.IsIrreducible (M : h.GKModule K V) : Prop := M.rep.IsIrreducible

theorem GKModule.rep_comm (M : h.GKModule K V) {T : End ℂ V} (hρ : ∀ X, M.ρ X * T = T * M.ρ X)
    (hσ : ∀ k, M.σ k * T = T * M.σ k) (a : FreeMonoid (h.lieSubalgebra ⊕ K)) :
    M.rep a * T = T * M.rep a := by
  induction a using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul x a ih =>
    rw [map_mul, mul_assoc, ih, ← mul_assoc, ← mul_assoc]
    congr 1
    rcases x with X | k
    · exact hρ X
    · exact hσ k

theorem GKModule.apply_σ_mem (M : h.GKModule K V) (Y : Subrepresentation M.rep) (k : K) {y : V}
    (hy : y ∈ Y.toSubmodule) : M.σ k y ∈ Y.toSubmodule :=
  Y.apply_mem_toSubmodule (FreeMonoid.of (Sum.inr k)) hy

section SubQuot

variable (M : h.GKModule K V) (U : Subrepresentation M.rep) (U₀ : Submodule ℂ U.toSubmodule)
  (hU₀ : ∀ a, U₀ ≤ U₀.comap (U.toRepresentation a))

abbrev quotRep : Representation ℂ (FreeMonoid (h.lieSubalgebra ⊕ K)) (U.toSubmodule ⧸ U₀) :=
  U.toRepresentation.quotient U₀ hU₀

theorem quotRep_mk (a : FreeMonoid (h.lieSubalgebra ⊕ K)) (u : U.toSubmodule) :
    quotRep M U U₀ hU₀ a (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (U.toRepresentation a u) :=
  rfl

theorem exists_form_extend (φ : Dual ℂ (U.toSubmodule ⧸ U₀)) :
    ∃ ψ : Dual ℂ V, ∀ u : U.toSubmodule, φ (Submodule.Quotient.mk u) = ψ u := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (φ ∘ₗ U₀.mkQ)
  exact ⟨ψ, fun u => (LinearMap.congr_fun hψ u).symm⟩

theorem coe_toRepresentation_apply (a : FreeMonoid (h.lieSubalgebra ⊕ K)) (u : U.toSubmodule) :
    ((U.toRepresentation a u : U.toSubmodule) : V) = M.rep a u :=
  rfl

def subQuotρ : h.lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ (U.toSubmodule ⧸ U₀) where
  toFun X := quotRep M U U₀ hU₀ (FreeMonoid.of (Sum.inl X))
  map_add' X Y := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, LinearMap.add_apply,
      ← Submodule.Quotient.mk_add]
    congr 1
    refine Subtype.ext ?_
    simp only [Submodule.coe_add, coe_toRepresentation_apply, GKModule.rep_of_inl, map_add (f := _),
      LinearMap.add_apply]
  map_smul' r X := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, LinearMap.smul_apply,
      RingHom.id_apply]
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    refine Subtype.ext ?_
    rw [Submodule.coe_smul_of_tower]
    simp only [coe_toRepresentation_apply, GKModule.rep_of_inl, map_smul, LinearMap.smul_apply]
  map_lie' {X Y} := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk,
      LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      ← Submodule.Quotient.mk_sub]
    congr 1
    refine Subtype.ext ?_
    simp only [Submodule.coe_sub, coe_toRepresentation_apply, GKModule.rep_of_inl, LieHom.map_lie,
      LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply]

def subQuotσ : Representation ℂ K (U.toSubmodule ⧸ U₀) where
  toFun k := quotRep M U U₀ hU₀ (FreeMonoid.of (Sum.inr k))
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, Module.End.one_apply]
    congr 1
    refine Subtype.ext ?_
    simp only [coe_toRepresentation_apply, GKModule.rep_of_inr, map_one, Module.End.one_apply]
  map_mul' k₁ k₂ := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, Module.End.mul_apply]
    congr 1
    refine Subtype.ext ?_
    simp only [coe_toRepresentation_apply, GKModule.rep_of_inr, map_mul, Module.End.mul_apply]

theorem subQuotρ_mk (X : h.lieSubalgebra) (u : U.toSubmodule) :
    subQuotρ M U U₀ hU₀ X (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (U.toRepresentation (FreeMonoid.of (Sum.inl X)) u) :=
  rfl

theorem subQuotσ_mk (k : K) (u : U.toSubmodule) :
    subQuotσ M U U₀ hU₀ k (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (U.toRepresentation (FreeMonoid.of (Sum.inr k)) u) :=
  rfl

theorem subQuot_locallyFinite (q : U.toSubmodule ⧸ U₀) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K => subQuotσ M U U₀ hU₀ k q)) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hfin := M.locallyFinite u
  set S : Submodule ℂ U.toSubmodule :=
    Submodule.span ℂ (range fun k : K => U.toRepresentation (FreeMonoid.of (Sum.inr k)) u)
  have hS : FiniteDimensional ℂ S := by
    have hle : S.map U.toSubmodule.subtype ≤ Submodule.span ℂ (range fun k : K => M.σ k u) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨k, rfl⟩
    have : FiniteDimensional ℂ (S.map U.toSubmodule.subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ U.toSubmodule.injective_subtype S).symm
  have hle : Submodule.span ℂ (range fun k : K =>
      subQuotσ M U U₀ hU₀ k (Submodule.Quotient.mk u)) ≤ S.map U₀.mkQ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem subQuot_hasContinuousCoeff : Representation.HasContinuousCoeff (subQuotσ M U U₀ hU₀) := by
  intro φ q
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨ψ, hψ⟩ := exists_form_extend M U U₀ φ
  have : (fun k : K => φ (subQuotσ M U U₀ hU₀ k (Submodule.Quotient.mk u))) =
      fun k => ψ (M.σ k u) := by
    funext k
    rw [subQuotσ_mk, hψ]
    rfl
  rw [this]
  exact M.hasContinuousCoeff ψ u

theorem subQuot_hasDerivAt (X : 𝔤) (hX : ∀ t : ℝ, h.expG (t • X) ∈ K)
    (φ : Dual ℂ (U.toSubmodule ⧸ U₀)) (q : U.toSubmodule ⧸ U₀) :
    HasDerivAt (fun t : ℝ => φ (subQuotσ M U U₀ hU₀ ⟨h.expG (t • X), hX t⟩ q))
      (φ (subQuotρ M U U₀ hU₀ (h.toLie X) q)) 0 := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨ψ, hψ⟩ := exists_form_extend M U U₀ φ
  have h1 : (fun t : ℝ => φ (subQuotσ M U U₀ hU₀ ⟨h.expG (t • X), hX t⟩
      (Submodule.Quotient.mk u))) = fun t => ψ (M.σ ⟨h.expG (t • X), hX t⟩ u) := by
    funext t
    rw [subQuotσ_mk, hψ]
    rfl
  have h2 : φ (subQuotρ M U U₀ hU₀ (h.toLie X) (Submodule.Quotient.mk u)) =
      ψ (M.ρ (h.toLie X) u) := by
    rw [subQuotρ_mk, hψ]
    rfl
  rw [h1, h2]
  exact M.hasDerivAt_coeff X hX ψ u

theorem subQuot_map_ρ (k : K) (X : 𝔤) (q : U.toSubmodule ⧸ U₀) :
    subQuotσ M U U₀ hU₀ k (subQuotρ M U U₀ hU₀ (h.toLie X) q) =
      subQuotρ M U U₀ hU₀ (h.toLie (h.Ad k X)) (subQuotσ M U U₀ hU₀ k q) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [subQuotρ_mk, subQuotσ_mk, subQuotσ_mk, subQuotρ_mk]
  congr 1
  exact Subtype.ext (M.map_ρ k X u)

def GKModule.subQuot : h.GKModule K (U.toSubmodule ⧸ U₀) where
  ρ := subQuotρ M U U₀ hU₀
  σ := subQuotσ M U U₀ hU₀
  locallyFinite := subQuot_locallyFinite M U U₀ hU₀
  hasContinuousCoeff := subQuot_hasContinuousCoeff M U U₀ hU₀
  hasDerivAt_coeff := subQuot_hasDerivAt M U U₀ hU₀
  map_ρ := subQuot_map_ρ M U U₀ hU₀

theorem GKModule.subQuot_rep : (M.subQuot U U₀ hU₀).rep = quotRep M U U₀ hU₀ :=
  FreeMonoid.hom_eq fun x => by
    rcases x with X | k <;> rfl

end SubQuot

end IsExpLieAlgebra

end GroundTheory.Automorphic
end
end

noncomputable section

universe u

namespace GroundTheory.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Set Module RestrictedTensor CompactRep

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace GKTensor

section FixedEnd

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {τ : Representation ℂ L V} (hτ : IsSmooth τ)
  {H : Subgroup L} (hHc : IsCompact (H : Set L)) (hHo : IsOpen (H : Set L))

def fixedEnd : End ℂ V := (fixedVectors τ H).subtype ∘ₗ fixedProj τ hτ hHc hHo

theorem fixedEnd_apply_of_mem {v : V} (hv : v ∈ fixedVectors τ H) :
    fixedEnd hτ hHc hHo v = v :=
  fixedProj_apply_of_mem hτ hHc hHo hv

theorem fixedEnd_mem (v : V) : fixedEnd hτ hHc hHo v ∈ fixedVectors τ H :=
  (fixedProj τ hτ hHc hHo v).2

theorem fixedEnd_comm {T : End ℂ V} (hT : ∀ g, T * τ g = τ g * T) (v : V) :
    fixedEnd hτ hHc hHo (T v) = T (fixedEnd hτ hHc hHo v) := by
  let f : Representation.IntertwiningMap τ τ := ⟨T, hT⟩
  have := fixedProj_map hHc hHo hτ hτ f v
  exact congrArg Subtype.val this

theorem isWinProj_fixedEnd : IsWinProj τ (fixedEnd hτ hHc hHo) :=
  ⟨fun v => fixedEnd_apply_of_mem hτ hHc hHo (fixedEnd_mem hτ hHc hHo v),
    fun Y _ hy => fixedProj_mem hτ hHc hHo Y hy⟩

theorem range_fixedEnd : LinearMap.range (fixedEnd hτ hHc hHo) = fixedVectors τ H := by
  refine le_antisymm ?_ fun v hv => ⟨v, fixedEnd_apply_of_mem hτ hHc hHo hv⟩
  rintro _ ⟨v, rfl⟩
  exact fixedEnd_mem hτ hHc hHo v

end FixedEnd

variable {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G} [CompactSpace K]

theorem _root_.GroundTheory.Automorphic.IsExpLieAlgebra.GKModule.isKFinite {V : Type*} [AddCommGroup V]
    [Module ℂ V] (M : h.GKModule K V) : IsKFinite M.σ :=
  ⟨M.locallyFinite, M.hasContinuousCoeff⟩


variable (h K) in
structure GKLModule (L : Type*) [Group L] (V : Type*) [AddCommGroup V] [Module ℂ V] where

  gk : h.GKModule K V

  τ : Representation ℂ L V
  comm_ρ : ∀ X g, gk.ρ X * τ g = τ g * gk.ρ X
  comm_σ : ∀ k g, gk.σ k * τ g = τ g * gk.σ k

namespace GKLModule

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type u} [AddCommGroup V] [Module ℂ V]
  (Mx : GKLModule h K L V)

theorem rep_comm (a : FreeMonoid (h.lieSubalgebra ⊕ K)) (g : L) :
    Mx.gk.rep a * Mx.τ g = Mx.τ g * Mx.gk.rep a :=
  Mx.gk.rep_comm (fun X => Mx.comm_ρ X g) (fun k => Mx.comm_σ k g) a

def fullRep : Representation ℂ (FreeMonoid (h.lieSubalgebra ⊕ K) × L) V :=
  prodRep Mx.gk.rep Mx.τ Mx.rep_comm

def IsIrreducible : Prop := Mx.fullRep.IsIrreducible

def IsAdmissible : Prop :=
  IsSmooth Mx.τ ∧ ∀ (H : Subgroup L), IsCompact (H : Set L) → IsOpen (H : Set L) →
    ∀ (c : Submodule (MonoidAlgebra ℂ K) Mx.gk.σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) Mx.gk.σ.asModule),
      FiniteDimensional ℂ (LinearMap.range (kProj Mx.gk.isKFinite hc ∘ₗ (fixedVectors Mx.τ H).subtype))


set_option maxHeartbeats 2000000 in
theorem exists_equiv_outerTensor_gkl (hirr : Mx.IsIrreducible) (hadm : Mx.IsAdmissible) :
    ∃ (H : Subgroup L) (hHc : IsCompact (H : Set L)) (hHo : IsOpen (H : Set L))
      (c : Submodule (MonoidAlgebra ℂ K) Mx.gk.σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) Mx.gk.σ.asModule) (N₁ N₂ : Submodule ℂ V),
      N₁ ≤ fixedVectors Mx.τ H ∧ N₂ ≤ fixedVectors Mx.τ H ∧
      N₂ ≤ LinearMap.range (kProj Mx.gk.isKFinite hc) ∧ N₁ ≠ ⊥ ∧ N₂ ≠ ⊥ ∧
      (∀ b, ∀ n ∈ N₂, fixedEnd hadm.1 hHc hHo (Mx.τ b n) ∈ N₂) ∧
      (mGenQuotRep Mx.gk.rep (kProj Mx.gk.isKFinite hc) N₁).IsIrreducible ∧
      (mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂).IsIrreducible ∧
      ((∀ T : End ℂ ((mGenSubrep Mx.τ N₂).toSubmodule ⧸ mGenKernel Mx.τ (fixedEnd hadm.1 hHc hHo) N₂),
          (∀ b, T * mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂ b =
            mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂ b * T) → ∃ c : ℂ, T = c • 1) →
        Nonempty (Mx.fullRep.Equiv
          (outerTensor (mGenQuotRep Mx.gk.rep (kProj Mx.gk.isKFinite hc) N₁)
            (mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂)))) := by
  classical
  have hτ := hadm.1
  have hσK := Mx.gk.isKFinite
  have hVnt := nontrivial_of_irreducible hirr
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨H', hH'c, hH'sub⟩ := exists_openSubgroup_isCompact_subset
    ((hτ x₀).mem_nhds (stabilizerOf Mx.τ x₀).one_mem)
  set H : Subgroup L := H'.toSubgroup
  have hHc : IsCompact (H : Set L) := hH'c
  have hHo : IsOpen (H : Set L) := H'.isOpen
  have hx₀H : x₀ ∈ fixedVectors Mx.τ H := fun g hg => hH'sub hg

  have hVHK : ∀ k, ∀ y ∈ fixedVectors Mx.τ H, Mx.gk.σ k y ∈ fixedVectors Mx.τ H := by
    intro k y hy g hg
    rw [← Module.End.mul_apply, ← Mx.comm_σ, Module.End.mul_apply, hy g hg]
  have hVH0 : fixedVectors Mx.τ H ≠ ⊥ := fun hb => hx₀ (by
    have : x₀ ∈ (⊥ : Submodule ℂ V) := hb ▸ hx₀H
    simpa using this)
  obtain ⟨c, hc, y, hyH, hy0, hyc⟩ := exists_kProj_eq_self hσK hVHK hVH0
  set e₁ := kProj hσK hc
  set e₂ := fixedEnd hτ hHc hHo
  have he₁ : IsWinProj Mx.gk.rep e₁ :=
    isWinProj_kProj hσK hc fun Y k y hy => Mx.gk.apply_σ_mem Y k hy
  have he₂ : IsWinProj Mx.τ e₂ := isWinProj_fixedEnd hτ hHc hHo
  have he₁₂ : ∀ g, e₁ * Mx.τ g = Mx.τ g * e₁ := fun g => LinearMap.ext fun v =>
    kProj_comm hσK hc (fun k => (Mx.comm_σ k g).symm) v
  have he₂₁ : ∀ a, e₂ * Mx.gk.rep a = Mx.gk.rep a * e₂ := fun a => LinearMap.ext fun v =>
    fixedEnd_comm hτ hHc hHo (fun g => Mx.rep_comm a g) v
  have hee : e₁ * e₂ = e₂ * e₁ := LinearMap.ext fun v =>
    (kProj_comm hσK hc (T := e₂) (fun k => LinearMap.ext fun w =>
      fixedEnd_comm hτ hHc hHo (fun g => Mx.comm_σ k g) w) v)
  have hW : LinearMap.range (e₁ * e₂) ≤
      LinearMap.range (kProj hσK hc ∘ₗ (fixedVectors Mx.τ H).subtype) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨fixedProj Mx.τ hτ hHc hHo v, rfl⟩
  have hfin : FiniteDimensional ℂ (LinearMap.range (e₁ * e₂)) := by
    have := hadm.2 H hHc hHo c hc
    exact Submodule.finiteDimensional_of_le hW
  have hne : LinearMap.range (e₁ * e₂) ≠ ⊥ := by
    intro hb
    have : y ∈ LinearMap.range (e₁ * e₂) := ⟨y, by
      show e₁ (e₂ y) = y
      rw [fixedEnd_apply_of_mem hτ hHc hHo hyH, hyc]⟩
    rw [hb, Submodule.mem_bot] at this
    exact hy0 this
  obtain ⟨N₁, N₂, hN₁W, hN₂W, hN₁0, hN₂0, -, hN₂st, hπ₁, hπ₂, hequiv⟩ :=
    exists_equiv_outerTensor (hcomm := Mx.rep_comm) hirr he₁ he₂ he₁₂ he₂₁ hee hne
  have hWH : LinearMap.range (e₁ * e₂) ≤ fixedVectors Mx.τ H := by
    rintro _ ⟨v, rfl⟩
    show e₁ (e₂ v) ∈ fixedVectors Mx.τ H
    exact kProj_mem hσK hc hVHK (fixedEnd_mem hτ hHc hHo v)
  have hWc : LinearMap.range (e₁ * e₂) ≤ LinearMap.range (kProj hσK hc) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨e₂ v, rfl⟩
  exact ⟨H, hHc, hHo, c, hc, N₁, N₂, hN₁W.trans hWH, hN₂W.trans hWH, hN₂W.trans hWc, hN₁0, hN₂0,
    hN₂st, hπ₁, hπ₂, hequiv⟩

end GKLModule

end GKTensor

end GroundTheory.Automorphic
