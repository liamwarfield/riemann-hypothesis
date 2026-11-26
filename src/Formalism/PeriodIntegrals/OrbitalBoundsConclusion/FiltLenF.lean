module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF
section -- merged from Formalism.PeriodIntegrals.FiltLenF
namespace PI

def FiltLenF : Prop :=
  ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (F : ℕ → Submodule R W) (a : ℕ),
    Antitone F → F 0 = ⊤ → F a = ⊥ →
    ∀ (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module R (V k)] (φ : ∀ k, ↥(F k) →ₗ[R] V k),
      (∀ k, ∀ x : ↥(F k), φ k x = 0 → (x : W) ∈ F (k + 1)) →
      ∀ (M N : Submodule R W) (P Q : ∀ k, Submodule R (V k)), N ≤ M →
        (∀ k < a, (M.comap (F k).subtype).map (φ k) ≤ P k) →
        (∀ k < a, Q k ≤ (N.comap (F k).subtype).map (φ k)) →
        Module.length R (↥M ⧸ N.comap M.subtype) ≤
          ∑ k ∈ Finset.range a, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype)

end PI
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiltrationLength.FiltLenFMain
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiltrationLength.LengthQuotLeOfKerLe
namespace PI.FiltrationLength

open Submodule

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

noncomputable def ell (B A : Submodule R W) : ℕ∞ :=
  Module.length R (↥B ⧸ A.comap B.subtype)

theorem ell_add {A B C : Submodule R W} (hAC : A ≤ C) (hCB : C ≤ B) :
    ell B A = ell C A + ell B C := by
  unfold ell
  let f : (↥C ⧸ A.comap C.subtype) →ₗ[R] (↥B ⧸ A.comap B.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hCB) (fun x hx => by simpa using hx)
  let g : (↥B ⧸ A.comap B.subtype) →ₗ[R] (↥B ⧸ C.comap B.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => by simpa using hAC hx)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      rw [LinearMap.mem_ker] at hy
      simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.coe_subtype, Submodule.coe_inclusion] at hy
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hy
  have hg : Function.Surjective g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ b => exact ⟨Submodule.Quotient.mk b, by simp [g]⟩
  have H : Function.Exact f g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ b =>
      constructor
      · intro hb
        simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
          Submodule.mem_comap, Submodule.coe_subtype] at hb
        exact ⟨Submodule.Quotient.mk ⟨b, hb⟩, by simp [f]; rfl⟩
      · rintro ⟨z, hz⟩
        induction z using Submodule.Quotient.induction_on with
        | _ c =>
          simp only [f, Submodule.mapQ_apply] at hz
          rw [Submodule.Quotient.eq] at hz
          simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
            Submodule.coe_inclusion] at hz
          simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
            Submodule.mem_comap, Submodule.coe_subtype]
          have h1 : (c : W) ∈ C := c.2
          have h2 : (c : W) - (b : W) ∈ C := hAC hz
          have := C.sub_mem h1 h2
          simpa using this
  exact Module.length_eq_add_of_exact f g hf hg H

theorem ell_sup_le {A C D : Submodule R W} (hDA : D ≤ A) :
    ell (A ⊔ C) A ≤ ell C D := by
  unfold ell
  refine Module.length_le_of_surjective
    (Submodule.mapQ (D.comap C.subtype) (A.comap (A ⊔ C).subtype)
      (Submodule.inclusion (le_sup_right : C ≤ A ⊔ C)) (fun x hx => by simpa using hDA hx)) ?_
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ z =>
    obtain ⟨a, ha, c, hc, hz⟩ := Submodule.mem_sup.mp z.2
    refine ⟨Submodule.Quotient.mk ⟨c, hc⟩, ?_⟩
    simp only [Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      Submodule.coe_inclusion]
    have : (c : W) - (z : W) = -a := by rw [← hz]; abel
    rw [this]
    exact A.neg_mem ha

end PI.FiltrationLength
end

namespace PI.FiltrationLength

open Submodule

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem ell_stepF {V : Type} [AddCommGroup V] [Module R V]
    (M N Fk Fk1 : Submodule R W) (ψ : ↥Fk →ₗ[R] V) (P Q : Submodule R V) (hNM : N ≤ M)
    (hinj : ∀ x : ↥Fk, ψ x = 0 → (x : W) ∈ Fk1)
    (hP : (M.comap Fk.subtype).map ψ ≤ P) (hQ : Q ≤ (N.comap Fk.subtype).map ψ) :
    ell (M ⊓ Fk) ((N ⊓ Fk) ⊔ (M ⊓ Fk1)) ≤ Module.length R (↥P ⧸ Q.comap P.subtype) := by
  have hgP : ∀ x : ↥(M ⊓ Fk), ψ (Submodule.inclusion inf_le_right x) ∈ P := fun x =>
    hP (Submodule.mem_map_of_mem (show Submodule.inclusion inf_le_right x ∈ M.comap Fk.subtype from x.2.1))
  let g : ↥(M ⊓ Fk) →ₗ[R] ↥P :=
    LinearMap.codRestrict P (ψ ∘ₗ Submodule.inclusion (inf_le_right : M ⊓ Fk ≤ Fk)) hgP
  let f : ↥(M ⊓ Fk) →ₗ[R] ↥P ⧸ Q.comap P.subtype := (Q.comap P.subtype).mkQ ∘ₗ g
  have hker : LinearMap.ker f ≤ ((N ⊓ Fk) ⊔ (M ⊓ Fk1)).comap (M ⊓ Fk).subtype := by
    intro x hx
    have hxQ : ψ (Submodule.inclusion inf_le_right x) ∈ Q := by
      have h1 : g x ∈ Q.comap P.subtype := (Submodule.Quotient.mk_eq_zero _).1 hx
      exact h1
    obtain ⟨y, hyN, hyx⟩ := hQ hxQ
    have hdiff : ψ (Submodule.inclusion inf_le_right x - y) = 0 := by rw [map_sub, hyx, sub_self]
    have hF1 := hinj _ hdiff
    have hxM : (x : W) ∈ M := x.2.1
    have hyM : (y : W) ∈ M := hNM hyN
    show (x : W) ∈ (N ⊓ Fk) ⊔ (M ⊓ Fk1)
    have hsplit : (x : W) = (y : W) + ((x : W) - (y : W)) := by abel
    rw [hsplit]
    refine Submodule.add_mem_sup ⟨hyN, y.2⟩ ⟨M.sub_mem hxM hyM, ?_⟩
    simpa using hF1
  unfold ell
  have hsurj : Function.Surjective (Submodule.factor hker) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  calc Module.length R (↥(M ⊓ Fk) ⧸ ((N ⊓ Fk) ⊔ (M ⊓ Fk1)).comap (M ⊓ Fk).subtype)
      ≤ Module.length R (↥(M ⊓ Fk) ⧸ LinearMap.ker f) := Module.length_le_of_surjective _ hsurj
    _ ≤ Module.length R (↥P ⧸ Q.comap P.subtype) :=
      Module.length_le_of_injective _
        (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ f le_rfl le_rfl))

theorem filtLenF_main : PI.FiltLenF := by
  intro R W _ _ _ F a hanti h0 ha V _ _ φ hinj M N P Q hNM hP hQ
  set X : ℕ → Submodule R W := fun k => N ⊔ (M ⊓ F k) with hX
  have hXmono : ∀ k, X (k + 1) ≤ X k := fun k =>
    sup_le_sup_left (inf_le_inf_left _ (hanti (Nat.le_succ k))) _
  have hX0 : X 0 = M := by simp [hX, h0, sup_eq_right.2 hNM]
  have hXa : X a = N := by simp [hX, ha]
  have hXle0 : ∀ k, X k ≤ X 0 := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hXmono k).trans ih
  have hstep : ∀ k < a, ell (X k) (X (k + 1)) ≤
      Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype) := by
    intro k hk
    have hD : (N ⊓ F k) ⊔ (M ⊓ F (k + 1)) ≤ X (k + 1) :=
      sup_le (inf_le_left.trans le_sup_left) le_sup_right
    have heq : X (k + 1) ⊔ (M ⊓ F k) = X k := by
      simp only [hX]
      apply le_antisymm
      · exact sup_le (sup_le le_sup_left
          (le_sup_of_le_right (inf_le_inf_left _ (hanti (Nat.le_succ k))))) le_sup_right
      · exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
    have h1 : ell (X k) (X (k + 1)) ≤ ell (M ⊓ F k) ((N ⊓ F k) ⊔ (M ⊓ F (k + 1))) := by
      calc ell (X k) (X (k + 1)) = ell (X (k + 1) ⊔ (M ⊓ F k)) (X (k + 1)) := by rw [heq]
        _ ≤ _ := ell_sup_le hD
    exact h1.trans (ell_stepF M N (F k) (F (k + 1)) (φ k) (P k) (Q k) hNM (hinj k) (hP k hk) (hQ k hk))
  have hsum : ∀ j ≤ a, ell (X 0) (X j) ≤
      ∑ k ∈ Finset.range j, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype) := by
    intro j
    induction j with
    | zero => intro _; simp [ell, Submodule.comap_subtype_self]
    | succ j ih =>
      intro hj
      rw [ell_add (hXmono j) (hXle0 j), Finset.sum_range_succ, add_comm]
      exact add_le_add (ih (Nat.le_of_succ_le hj)) (hstep j hj)
  have hfin := hsum a le_rfl
  rw [hX0, hXa] at hfin
  exact hfin

end PI.FiltrationLength
end

theorem filtration_length_bound : PI.FiltLenF := PI.FiltrationLength.filtLenF_main
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhConvProj
section -- merged from Formalism.PeriodIntegrals.PhConvProj
noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace PI.PhConvProj

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURep (ρ : G → (H →L[ℂ] H)) : Prop :=
  ρ 1 = 1 ∧ (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) ∧ (∀ g v, ‖ρ g v‖ = ‖v‖) ∧
    ∀ v, Continuous fun g => ρ g v

def IsOpInt {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (μ : Measure G)
    (π : G → (K →L[ℂ] K)) (ph : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  ∀ x y : K, ⟪x, T y⟫_ℂ = ∫ g, ph g * ⟪x, π g y⟫_ℂ ∂μ

def IsRowProj {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (π : G → (K →L[ℂ] K)) (m : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  (∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) ∧ T.comp T = T ∧ ∀ a, T.comp ((π a).comp T) = m a • T

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def ConvProj : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → IsRowProj π m T

end PI.PhConvProj
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.ConvProjOf
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhConvProj.Defs

open PI.PhConvProj

def SelfAdjStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → ∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ

def SandStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → ∀ a, T.comp ((π a).comp T) = m a • T

theorem convProj_of (h1 : SelfAdjStep) (h2 : SandStep) : ConvProj := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m hph hci K _ _ π T hπ hT
  have hsa := h1 G μ ph m hph hci K π T hπ hT
  have hsw := h2 G μ ph m hph hci K π T hπ hT
  obtain ⟨hπ1, -⟩ := hπ
  obtain ⟨hm1, -⟩ := hci
  refine ⟨hsa, ?_, hsw⟩
  have h := hsw 1
  rw [hπ1, hm1, one_smul, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] at h
  exact h

end PI.UnitaryGroupMassFormula.PhConvProj.Defs
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.SelfAdj
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj

open PI.PhConvProj

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem inner_map_map {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (x y : K) :
    ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let f : K →ₗᵢ[ℂ] K := ⟨(π g).toLinearMap, fun v => hπ.2.2.1 g v⟩
  exact f.inner_map_map x y

theorem map_inv_map {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (y : K) :
    π g (π g⁻¹ y) = y := by
  have h := congrArg (fun A : K →L[ℂ] K => A y) (hπ.2.1 g g⁻¹)
  simp only [mul_inv_cancel, hπ.1, ContinuousLinearMap.coe_comp, Function.comp_apply] at h
  rw [← h]
  rfl

theorem inner_map_left {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (x y : K) :
    ⟪π g x, y⟫_ℂ = ⟪x, π g⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← (map_inv_map hπ) g y]
  exact (inner_map_map hπ) g x (π g⁻¹ y)

theorem inner_symm [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant] (ph : G → ℂ) (hph : ∀ g, ph g⁻¹ = star (ph g))
    {π : G → (K →L[ℂ] K)} (hπ : IsURep π) {T : K →L[ℂ] K} (hT : IsOpInt μ π ph T) (x y : K) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have h1 : ⟪T x, y⟫_ℂ = ∫ g, ph g⁻¹ * ⟪x, π g⁻¹ y⟫_ℂ ∂μ := by
    rw [← inner_conj_symm, hT y x, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, inner_conj_symm, hph g]
    rw [(inner_map_left hπ)]
    rfl
  rw [h1, hT x y]
  exact integral_inv_eq_self (fun g => ph g * ⟪x, π g y⟫_ℂ) μ

theorem selfAdj : Defs.SelfAdjStep := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m _ hidem K _ _ π T hπ hT x y
  exact inner_symm μ ph hidem.2.1 hπ hT x y

end PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.UrepMulApply
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhConvProj.Sand

open PI.PhConvProj

section

variable {G : Type} [Group G] [TopologicalSpace G] {K : Type} [NormedAddCommGroup K]
  [InnerProductSpace ℂ K]

theorem urep_inner {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (k : G) (u v : K) :
    ⟪π k u, π k v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let f : K →ₗᵢ[ℂ] K := { toLinearMap := (π k : K →ₗ[ℂ] K), norm_map' := hπ.2.2.1 k }
  exact f.inner_map_map u v

theorem urep_mul_apply {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (a b : G) (v : K) :
    π (a * b) v = π a (π b v) := by
  rw [hπ.2.1 a b]
  rfl

theorem urep_adj {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (k : G) (u v : K) :
    ⟪π k u, v⟫_ℂ = ⟪u, π k⁻¹ v⟫_ℂ := by
  have h1 : π k (π k⁻¹ v) = v := by
    rw [← urep_mul_apply hπ, mul_inv_cancel, hπ.1, ContinuousLinearMap.one_apply]
  calc ⟪π k u, v⟫_ℂ = ⟪π k u, π k (π k⁻¹ v)⟫_ℂ := by rw [h1]
    _ = ⟪u, π k⁻¹ v⟫_ℂ := urep_inner hπ k u _

end

theorem sand : Defs.SandStep := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m hph hconv K _ _ π T hπ hT a
  ext y
  refine ext_inner_left ℂ (fun x => ?_)
  let F : G → ℂ := fun k => ⟪x, π k y⟫_ℂ
  have hFc : Continuous F := continuous_const.inner (hπ.2.2.2 y)
  have hFb : ∀ k, ‖F k‖ ≤ ‖x‖ * ‖y‖ := fun k =>
    (norm_inner_le_norm x (π k y)).trans_eq (by rw [hπ.2.2.1])
  have step1 : ∀ g, ⟪x, π g (π a (T y))⟫_ℂ = ∫ h, ph h * F (g * (a * h)) ∂μ := by
    intro g
    rw [← urep_mul_apply hπ, ← inv_inv (g * a), ← urep_adj hπ, hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [F]
    rw [urep_adj hπ, inv_inv, ← urep_mul_apply hπ, mul_assoc]
  let A : G × G → ℂ := fun z => ph z.1 * ph z.2 * F (z.1 * (a * z.2))
  have hA : Integrable A (μ.prod μ) := by
    have h1 : Integrable (fun z : G × G => ph z.1 * ph z.2) (μ.prod μ) := hph.mul_prod hph
    have hm : AEStronglyMeasurable (fun z : G × G => F (z.1 * (a * z.2))) (μ.prod μ) :=
      (hFc.comp (continuous_fst.mul (continuous_const.mul continuous_snd))).aestronglyMeasurable
    exact h1.mul_bdd hm (Filter.Eventually.of_forall fun z => hFb _)
  have e1 : ∫ g, ph g * ∫ h, ph h * F (g * (a * h)) ∂μ ∂μ = ∫ z, A z ∂(μ.prod μ) := by
    rw [integral_prod _ hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [A]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    ring
  let Ψ : G × G → G × G := fun z => (z.1, z.1 * (a * z.2))
  have hΨ : MeasurePreserving Ψ (μ.prod μ) (μ.prod μ) :=
    (measurePreserving_prod_mul μ μ).comp ((MeasurePreserving.id μ).prod (measurePreserving_mul_left μ a))
  have hΨe : MeasurableEmbedding Ψ :=
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl G) (MeasurableEquiv.mulLeft a)).trans
      (MeasurableEquiv.shearMulRight G)).measurableEmbedding
  let B : G × G → ℂ := fun z => ph z.1 * ph (a⁻¹ * z.1⁻¹ * z.2) * F z.2
  have hBA : B ∘ Ψ = A := by
    funext z
    simp only [B, Ψ, A, Function.comp]
    have : a⁻¹ * z.1⁻¹ * (z.1 * (a * z.2)) = z.2 := by group
    rw [this]
  have hB : Integrable B (μ.prod μ) := (hΨ.integrable_comp_emb hΨe).1 (hBA ▸ hA)
  have e2 : ∫ z, A z ∂(μ.prod μ) = ∫ z, B z ∂(μ.prod μ) := by
    rw [← hBA]
    exact hΨ.integral_comp hΨe B
  show ⟪x, T (π a (T y))⟫_ℂ = ⟪x, (m a • T) y⟫_ℂ
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, hT x (π a (T y)), hT x y]
  simp_rw [step1]
  rw [e1, e2, integral_prod_symm B hB, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [B, F]
  rw [integral_mul_const, (hconv.2.2 a h).2]
  ring

end PI.UnitaryGroupMassFormula.PhConvProj.Sand
end
end

theorem convolution_projection : PI.PhConvProj.ConvProj :=
  PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.selfAdj PI.UnitaryGroupMassFormula.PhConvProj.Sand.sand
end
