module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.EntriesOfMemUnipRad
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.GoodColUInv
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.MulRowOfGood
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.ColUSingleOfGe
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.ExistsAvgNotMem
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DualSumEqZero
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.ExistsBallMem
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.MulMemBall
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ball (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := by
    intro a b ha hb
    simp only [cball, Set.mem_setOf_eq] at ha hb ⊢
    exact Valuation.map_add_le _ ha hb
  neg_mem' := by
    intro a ha
    simp only [cball, Set.mem_setOf_eq] at ha ⊢
    rwa [Valuation.map_neg]

theorem mem_ball {s : kˣ} {a : k} : a ∈ ball s ↔ valuation k a ≤ valuation k (s : k) := Iff.rfl

theorem ball_mono {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) {a : k} (ha : a ∈ ball s) :
    a ∈ ball t := mem_ball.2 (le_trans (mem_ball.1 ha) h)

theorem mul_mem_ball {s t : kˣ} {a b : k} (ha : a ∈ ball s) (hb : b ∈ ball t) : a * b ∈ ball (s * t) := by
  rw [mem_ball, map_mul, Units.val_mul, map_mul]
  exact mul_le_mul' ha hb

theorem isOpen_ball (s : kˣ) : IsOpen ((ball s : AddSubgroup k) : Set k) := isOpen_cball s

abbrev Q (s t : kˣ) : Type := ↥(ball t) ⧸ (ball s).addSubgroupOf (ball t)

instance finite_Q (s t : kˣ) : Finite (Q (k := k) s t) := by
  haveI : CompactSpace ↥(ball t) := isCompact_iff_compactSpace.mp (isCompact_cball t)
  refine AddSubgroup.quotient_finite_of_isOpen _ ?_
  rw [AddSubgroup.coe_addSubgroupOf]
  exact (isOpen_ball s).preimage continuous_subtype_val

noncomputable instance (s t : kˣ) : Fintype (Q (k := k) s t) := Fintype.ofFinite _

theorem out_eq_add {s t : kˣ} (x : ↥(ball t)) (q : Q s t) (hq : q = QuotientAddGroup.mk x) :
    ∃ h ∈ ball s, ((Quotient.out q : ↥(ball t)) : k) = (x : k) + h := by
  have h1 : (QuotientAddGroup.mk (Quotient.out q) : Q s t) = QuotientAddGroup.mk x := by
    rw [← hq]; exact QuotientAddGroup.out_eq' q
  rw [QuotientAddGroup.eq] at h1
  refine ⟨((Quotient.out q : ↥(ball t)) : k) - x, ?_, by ring⟩
  have h2 := AddSubgroup.mem_addSubgroupOf.1 (neg_mem h1)
  convert h2 using 1
  push_cast
  ring

theorem apply_out {M : Type} {s t : kˣ} (g : k → M) (hg : ∀ b, ∀ h ∈ ball s, g (b + h) = g b)
    (x : ↥(ball t)) (q : Q s t) (hq : q = QuotientAddGroup.mk x) :
    g ((Quotient.out q : ↥(ball t)) : k) = g x := by
  obtain ⟨h, hh, he⟩ := out_eq_add x q hq
  rw [he, hg _ _ hh]

theorem out_mem {s t : kˣ} (q : Q s t) : ((Quotient.out q : ↥(ball t)) : k) ∈ ball t := (Quotient.out q).2

theorem out_zero_mem {s t : kˣ} : ((Quotient.out (0 : Q s t) : ↥(ball t)) : k) ∈ ball s := by
  obtain ⟨h, hh, he⟩ := out_eq_add (s := s) (0 : ↥(ball t)) 0 rfl
  rw [he]; simpa using hh

theorem out_mem_iff {s t : kˣ} (q : Q s t) : ((Quotient.out q : ↥(ball t)) : k) ∈ ball s ↔ q = 0 := by
  constructor
  · intro h
    rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_addSubgroupOf.2 h
  · rintro rfl; exact out_zero_mem

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def avg (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (s t : kˣ) (ξ : k) : V →ₗ[ℂ] V :=
  ∑ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) • σ ((Quotient.out q : ↥(ball t)) : k)

theorem ch_add (ψ : AddChar k Circle) (a b : k) : ((ψ (a + b) : Circle) : ℂ) = (ψ a : ℂ) * (ψ b : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

theorem ch_neg_mul (ψ : AddChar k Circle) (a : k) : ((ψ (-a) : Circle) : ℂ) * (ψ a : ℂ) = 1 := by
  rw [← ch_add ψ, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

section Avg

variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (hadd : ∀ a b, σ (a + b) = σ a * σ b)
include hadd

theorem comm (a b : k) : σ a * σ b = σ b * σ a := by rw [← hadd, ← hadd, add_comm]

theorem avg_comm (s t : kˣ) (ξ : k) (b : k) : avg ψ σ s t ξ * σ b = σ b * avg ψ σ s t ξ := by
  simp only [avg, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, comm σ hadd]

theorem avg_comm_avg (s t s' t' : kˣ) (ξ ξ' : k) :
    avg ψ σ s t ξ * avg ψ σ s' t' ξ' = avg ψ σ s' t' ξ' * avg ψ σ s t ξ := by
  rw [avg, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, avg_comm ψ σ hadd]

omit hadd in
theorem avg_mem (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W) (s t : kˣ) (ξ : k) {w : V} (hw : w ∈ W) :
    avg ψ σ s t ξ w ∈ W := by
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply]
  exact W.sum_mem fun q _ => W.smul_mem _ (hW _ _ hw)

theorem avg_eigen {s t : kˣ} {ξ : k} (hξ : ∀ h ∈ ball s, ψ (ξ * h) = 1) {y : V} (hy : ∀ h ∈ ball s, σ h y = y)
    {a : k} (ha : a ∈ ball t) : σ a (avg ψ σ s t ξ y) = ((ψ (ξ * a) : Circle) : ℂ) • avg ψ σ s t ξ y := by
  rw [← Module.End.mul_apply, ← avg_comm ψ σ hadd, Module.End.mul_apply]
  let g : k → V := fun b => ((ψ (-(ξ * b)) : Circle) : ℂ) • σ b y
  have hg : ∀ b, ∀ h ∈ ball s, g (b + h) = g b := by
    intro b h hh
    simp only [g, hadd, Module.End.mul_apply, hy h hh, mul_add, neg_add, ch_add ψ, hξ h hh]
    have : ((ψ (-(ξ * h)) : Circle) : ℂ) = 1 := by
      have := ch_neg_mul ψ (ξ * h); rwa [hξ h hh, Circle.coe_one, mul_one] at this
    rw [this, mul_one]
  let a' : ↥(ball t) := ⟨a, ha⟩
  have key : ∀ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) •
      σ ((Quotient.out q : ↥(ball t)) : k) (σ a y) =
      ((ψ (ξ * a) : Circle) : ℂ) • g ((Quotient.out (q + QuotientAddGroup.mk a') : ↥(ball t)) : k) := by
    intro q
    rw [apply_out g hg (Quotient.out q + a') _ (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq'])]
    simp only [g, AddSubgroup.coe_add, a', ← Module.End.mul_apply, ← hadd, smul_smul]
    congr 1
    rw [mul_add, neg_add, ch_add ψ, ← mul_assoc, mul_comm ((ψ (ξ * a) : Circle) : ℂ), mul_assoc]
    rw [mul_comm ((ψ (ξ * a) : Circle) : ℂ), ch_neg_mul, mul_one]
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply, key, ← Finset.smul_sum]
  congr 1
  exact (Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk a' : Q s t)) (fun q => g ((Quotient.out q : ↥(ball t)) : k)))

end Avg

end DiscreteGroups.sglob.LConvGenF
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem psi_triv {ψ : AddChar k Circle} {c : kˣ} (hc : HasConductor ψ c) {s : kˣ} {ξ : k}
    (hξ : ξ ∈ ball (c * s⁻¹)) : ∀ h ∈ ball s, ψ (ξ * h) = 1 := by
  intro h hh
  have := mul_mem_ball hξ hh
  rw [inv_mul_cancel_right] at this
  exact hc.eq_one this

theorem psi_neg_triv {ψ : AddChar k Circle} {c : kˣ} (hc : HasConductor ψ c) {s : kˣ} {ξ : k}
    (hξ : ξ ∈ ball (c * s⁻¹)) {h : k} (hh : h ∈ ball s) : ψ (-(ξ * h)) = 1 := by
  have := mul_mem_ball hξ hh
  rw [inv_mul_cancel_right] at this
  exact hc.eq_one (neg_mem this)

theorem card_ne_zero (s t : kˣ) : ((Fintype.card (Q (k := k) s t) : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem exists_ball_mem (a : k) : ∃ t : kˣ, a ∈ ball t := by
  by_cases h : a = 0
  · exact ⟨1, by rw [h]; exact (ball 1).zero_mem⟩
  · exact ⟨Units.mk0 a h, mem_ball.2 le_rfl⟩

theorem exists_min (s1 s2 : kˣ) : ∃ s : kˣ, valuation k (s : k) ≤ valuation k (s1 : k) ∧
    valuation k (s : k) ≤ valuation k (s2 : k) := by
  rcases le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h
  · exact ⟨s1, le_rfl, h⟩
  · exact ⟨s2, h, le_rfl⟩

theorem exists_max (s1 s2 : kˣ) : ∃ s : kˣ, valuation k (s1 : k) ≤ valuation k (s : k) ∧
    valuation k (s2 : k) ≤ valuation k (s : k) := by
  rcases le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h
  · exact ⟨s2, h, le_rfl⟩
  · exact ⟨s1, le_rfl, h⟩

section Fourier

variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (hadd : ∀ a b, σ (a + b) = σ a * σ b)

theorem avg_of_eigen {s t : kˣ} {ξ : k} {z : V}
    (hz : ∀ b ∈ ball t, σ b z = ((ψ (ξ * b) : Circle) : ℂ) • z) :
    avg ψ σ s t ξ z = ((Fintype.card (Q s t) : ℕ) : ℂ) • z := by
  have h1 : ∀ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) •
      σ ((Quotient.out q : ↥(ball t)) : k) z = z := fun q => by
    rw [hz _ (out_mem q), smul_smul, ch_neg_mul, one_smul]
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply, h1, Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

include hadd

theorem avg_level {s s0 t : kˣ} {ξ : k} (hss0 : valuation k (s : k) ≤ valuation k (s0 : k))
    (hξ : ∀ h ∈ ball s0, ψ (ξ * h) = 1) {x : V} (hx : ∀ h ∈ ball s0, σ h x = x) :
    ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x := by
  have hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1 := fun h hh => hξ h (ball_mono hss0 hh)
  have hxs : ∀ h ∈ ball s, σ h x = x := fun h hh => hx h (ball_mono hss0 hh)
  have e1 : avg ψ σ s0 t ξ (avg ψ σ s t ξ x) = ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξs hxs hb)
  have e2 : avg ψ σ s t ξ (avg ψ σ s0 t ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx hb)
  rw [← e1, ← e2, ← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]

theorem avg_mono_mem (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W) {s t t' : kˣ}
    (htt' : valuation k (t : k) ≤ valuation k (t' : k)) {ξ : k} (hξ : ∀ h ∈ ball s, ψ (ξ * h) = 1)
    {x : V} (hx : ∀ h ∈ ball s, σ h x = x) (h : avg ψ σ s t ξ x ∈ W) : avg ψ σ s t' ξ x ∈ W := by
  have e : avg ψ σ s t ξ (avg ψ σ s t' ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s t' ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx (ball_mono htt' hb))
  have hm : avg ψ σ s t ξ (avg ψ σ s t' ξ x) ∈ W := by
    rw [← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]
    exact avg_mem ψ σ W hW _ _ _ h
  rw [e] at hm
  exact (W.smul_mem_iff (card_ne_zero s t)).1 hm

end Fourier

end DiscreteGroups.sglob.LConvGenF
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) {c : kˣ} (hc : HasConductor ψ c)


include hc in
theorem dual_sum_eq_zero {s t : kˣ} {b : k} (hbt : b ∈ ball t) (hbs : b ∉ ball s) :
    ∑ f : Q (c * t⁻¹) (c * s⁻¹), ((ψ (-(((Quotient.out f : ↥(ball (c * s⁻¹))) : k) * b)) : Circle) : ℂ) = 0 := by
  obtain ⟨ξ0, hξ0, hne⟩ := hc.exists_ne_one (c * s⁻¹) (x := b)
    (by rw [show c * (c * s⁻¹)⁻¹ = s by rw [mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]]; exact hbs)
  let φ : k → ℂ := fun ξ => ((ψ (-(ξ * b)) : Circle) : ℂ)
  have hφ : ∀ ξ, ∀ h ∈ ball (c * t⁻¹), φ (ξ + h) = φ ξ := by
    intro ξ h hh
    show ((ψ (-((ξ + h) * b)) : Circle) : ℂ) = ψ (-(ξ * b))
    rw [add_mul, neg_add, ch_add ψ, psi_neg_triv hc hh hbt, Circle.coe_one, mul_one]
  let ξ0' : ↥(ball (c * s⁻¹)) := ⟨ξ0, hξ0⟩
  have shift : ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) =
      φ ξ0 * ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) := by
    rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ξ0' : Q (c * t⁻¹) (c * s⁻¹)))]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Equiv.coe_addRight, apply_out φ hφ (Quotient.out f + ξ0') _
      (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq'])]
    simp only [φ, AddSubgroup.coe_add, ξ0']
    rw [add_mul, neg_add, ch_add ψ, mul_comm]
  have hne' : φ ξ0 ≠ 1 := by
    intro h1
    apply hne
    have := ch_neg_mul ψ (ξ0 * b)
    simp only [φ] at h1
    rw [h1, one_mul] at this
    exact Circle.coe_eq_one.1 this
  have h2 : (1 - φ ξ0) * ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) = 0 := by
    rw [sub_mul, one_mul, ← shift, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne'.symm)


include hc in
theorem sum_avg {s t : kˣ} {x : V} (hx : ∀ h ∈ ball s, σ h x = x) :
    ∑ f : Q (c * t⁻¹) (c * s⁻¹), avg ψ σ s t ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) x =
      ((Fintype.card (Q (c * t⁻¹) (c * s⁻¹)) : ℕ) : ℂ) • x := by
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single (0 : Q s t)]
  · rw [hx _ out_zero_mem]
    congr 1
    have h1 : ∀ f : Q (c * t⁻¹) (c * s⁻¹), ((ψ (-(((Quotient.out f : ↥(ball (c * s⁻¹))) : k) *
        ((Quotient.out (0 : Q s t) : ↥(ball t)) : k))) : Circle) : ℂ) = 1 := fun f => by
      rw [psi_neg_triv hc (out_mem f) out_zero_mem, Circle.coe_one]
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · intro q _ hq
    rw [dual_sum_eq_zero ψ hc (out_mem q) (fun h => hq ((out_mem_iff q).1 h)), zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

end DiscreteGroups.sglob.LConvGenF
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) {c : kˣ} (hc : HasConductor ψ c)

include hc in
theorem exists_avg_notMem (W : Submodule ℂ V) {s t : kˣ} {x : V} (hx : ∀ h ∈ ball s, σ h x = x)
    (hxW : x ∉ W) : ∃ ξ ∈ ball (c * s⁻¹), avg ψ σ s t ξ x ∉ W := by
  by_contra hall
  push Not at hall
  apply hxW
  have hsum := sum_avg ψ σ (c := c) hc (t := t) hx
  have hm : ((Fintype.card (Q (c * t⁻¹) (c * s⁻¹)) : ℕ) : ℂ) • x ∈ W := by
    rw [← hsum]
    exact W.sum_mem fun f _ => hall _ (out_mem f)
  exact (W.smul_mem_iff (card_ne_zero _ _)).1 hm

include hc in
theorem avg_shift {s t : kˣ} {ξ h : k} (hh : h ∈ ball (c * t⁻¹)) : avg ψ σ s t (ξ + h) = avg ψ σ s t ξ := by
  simp only [avg]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [add_mul, neg_add, ch_add ψ, psi_neg_triv hc hh (out_mem q), Circle.coe_one, mul_one]

include hc in
theorem isClosed_notMem (W : Submodule ℂ V) (s t : kˣ) (x : V) :
    IsClosed {ξ : k | avg ψ σ s t ξ x ∉ W} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro ξ hξ
  have hU : (fun η => η - ξ) ⁻¹' ((ball (c * t⁻¹) : AddSubgroup k) : Set k) ∈ nhds ξ :=
    ((isOpen_ball _).preimage (continuous_sub_right ξ)).mem_nhds (by simp [(ball _).zero_mem])
  refine Filter.mem_of_superset hU fun η hη => ?_
  have : η = ξ + (η - ξ) := by ring
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hξ ⊢
  rw [this, avg_shift ψ σ hc hη]
  exact hξ

variable (hadd : ∀ a b, σ (a + b) = σ a * σ b)

include hadd in
theorem key_step (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W)
    (hsm : ∀ v : V, ∃ s : kˣ, ∀ h ∈ ball s, σ h v = v) {s : kˣ} {x : V} (hs : ∀ h ∈ ball s, σ h x = x) {ξ : k}
    (hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1)
    (hx : x ∈ W ⊔ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y}) :
    ∃ t' : kˣ, valuation k (s : k) ≤ valuation k (t' : k) ∧ avg ψ σ s t' ξ x ∈ W := by
  let P : V → Prop := fun z => ∃ s' t' : kˣ, valuation k (s' : k) ≤ valuation k (s : k) ∧
    valuation k (s : k) ≤ valuation k (t' : k) ∧ ∀ s'' t'' : kˣ, valuation k (s'' : k) ≤ valuation k (s' : k) →
      valuation k (t' : k) ≤ valuation k (t'' : k) → avg ψ σ s'' t'' ξ z ∈ W
  have Padd : ∀ z1 z2, P z1 → P z2 → P (z1 + z2) := by
    rintro z1 z2 ⟨s1, t1, hs1, ht1, h1⟩ ⟨s2, t2, hs2, ht2, h2⟩
    obtain ⟨s', a1, a2⟩ := exists_min s1 s2
    obtain ⟨t', b1, b2⟩ := exists_max t1 t2
    refine ⟨s', t', a1.trans hs1, ht1.trans b1, fun s'' t'' h1' h2' => ?_⟩
    rw [map_add (f := _)]
    exact W.add_mem (h1 _ _ (h1'.trans a1) (b1.trans h2')) (h2 _ _ (h1'.trans a2) (b2.trans h2'))
  have PW : ∀ w ∈ W, P w := fun w hw => ⟨s, s, le_rfl, le_rfl, fun _ _ _ _ => avg_mem ψ σ W hW _ _ _ hw⟩
  have Pspan : ∀ z ∈ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y},
      P z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, y, rfl⟩ := hz
      obtain ⟨sy, hsy⟩ := hsm y
      obtain ⟨ta, hta⟩ := exists_ball_mem a
      obtain ⟨s', a1, a2⟩ := exists_min s sy
      obtain ⟨t', b1, b2⟩ := exists_max s ta
      refine ⟨s', t', a1, b1, fun s'' t'' h1 h2 => ?_⟩
      have hy'' : ∀ h ∈ ball s'', σ h y = y := fun h hh => hsy h (ball_mono (h1.trans a2) hh)
      have hξ'' : ∀ h ∈ ball s'', ψ (ξ * h) = 1 := fun h hh => hξs h (ball_mono (h1.trans a1) hh)
      have ha : a ∈ ball t'' := ball_mono (b2.trans h2) hta
      rw [map_sub, map_smul, ← Module.End.mul_apply, avg_comm ψ σ hadd, Module.End.mul_apply,
        avg_eigen ψ σ hadd hξ'' hy'' ha, sub_self]
      exact W.zero_mem
    | zero => exact PW 0 W.zero_mem
    | add z1 z2 _ _ h1 h2 => exact Padd z1 z2 h1 h2
    | smul r z _ h =>
      obtain ⟨s', t', a1, b1, hz⟩ := h
      exact ⟨s', t', a1, b1, fun s'' t'' h1 h2 => by rw [map_smul]; exact W.smul_mem r (hz _ _ h1 h2)⟩
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s', t', hs', ht', h⟩ := Padd w y (PW w hw) (Pspan y hy)
  refine ⟨t', ht', ?_⟩
  have h1 := h s' t' le_rfl le_rfl
  have e := avg_level ψ σ hadd (t := t') hs' hξs hs
  have hm : ((Fintype.card (Q s' t') : ℕ) : ℂ) • avg ψ σ s t' ξ (w + y) ∈ W := by
    rw [← e]; exact W.smul_mem _ h1
  exact (W.smul_mem_iff (card_ne_zero _ _)).1 hm


include hc hadd in
theorem exists_character_sup_ne_top (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W)
    (hsm : ∀ v : V, ∃ s : kˣ, ∀ h ∈ ball s, σ h v = v) (hne : W ≠ ⊤) :
    ∃ ξ : k, W ⊔ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y} ≠ ⊤ := by
  obtain ⟨x, hxW⟩ : ∃ x, x ∉ W := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨s, hs⟩ := hsm x
  let ι := {t : kˣ // valuation k (s : k) ≤ valuation k (t : k)}
  haveI : Nonempty ι := ⟨⟨s, le_rfl⟩⟩
  let C : ι → Set k := fun t => ((ball (c * s⁻¹) : AddSubgroup k) : Set k) ∩ {ξ | avg ψ σ s t.1 ξ x ∉ W}
  have hdir : Directed (· ⊇ ·) C := by
    intro t1 t2
    rcases le_total (valuation k (t1.1 : k)) (valuation k (t2.1 : k)) with h | h
    · exact ⟨t2, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩,
        le_rfl⟩
    · exact ⟨t1, le_rfl, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩⟩
  have hnon : ∀ t, (C t).Nonempty := fun t => by
    obtain ⟨ξ, h1, h2⟩ := exists_avg_notMem ψ σ hc W (t := t.1) hs hxW
    exact ⟨ξ, h1, h2⟩
  have hcl : ∀ t, IsClosed (C t) := fun t =>
    ((ball _).isClosed_of_isOpen (isOpen_ball _)).inter (isClosed_notMem ψ σ hc W s t.1 x)
  have hcpt : ∀ t, IsCompact (C t) := fun t => (isCompact_cball _).inter_right (isClosed_notMem ψ σ hc W s t.1 x)
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hnon hcpt hcl
  rw [Set.mem_iInter] at hξ
  have hξs := psi_triv hc (hξ ⟨s, le_rfl⟩).1
  refine ⟨ξ, fun htop => ?_⟩
  obtain ⟨t', ht', hm⟩ := key_step ψ σ hadd W hW hsm hs hξs (x := x) (by rw [htop]; exact Submodule.mem_top)
  exact (hξ ⟨t', ht'⟩).2 hm

end DiscreteGroups.sglob.LConvGenF
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

def colM (j : ℕ) (c : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i l => if i.val < j ∧ l.val = j then c i else 0

theorem colM_apply (j : ℕ) (c : Fin n → k) (i l : Fin n) :
    colM j c i l = if i.val < j ∧ l.val = j then c i else 0 := rfl

theorem colM_mul (j : ℕ) (c d : Fin n → k) : colM j c * colM j d = 0 := by
  ext i l
  simp only [Matrix.mul_apply, colM_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases h1 : i.val < j ∧ a.val = j
  · by_cases h2 : a.val < j ∧ l.val = j
    · exact absurd h2.1 (by omega)
    · simp [h2]
  · simp [h1]

theorem colM_add (j : ℕ) (c d : Fin n → k) : colM j (c + d) = colM j c + colM j d := by
  ext i l
  simp only [colM_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

def colU (j : ℕ) (c : Fin n → k) : GL (Fin n) k :=
  ⟨1 + colM j c, 1 - colM j c, by rw [add_mul, one_mul, mul_sub, mul_one, colM_mul]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, colM_mul]; abel⟩

theorem val_colU (j : ℕ) (c : Fin n → k) : (colU j c : Matrix (Fin n) (Fin n) k) = 1 + colM j c := rfl

theorem colU_add (j : ℕ) (c d : Fin n → k) : colU j (c + d) = colU j c * colU j d := by
  ext : 1
  rw [Units.val_mul, val_colU, val_colU, val_colU, colM_add, add_mul, one_mul, mul_add, mul_one, colM_mul]
  abel

theorem colU_zero (j : ℕ) : colU j (0 : Fin n → k) = 1 := by
  ext : 1
  rw [val_colU, Units.val_one]
  have : colM j (0 : Fin n → k) = 0 := by ext i l; simp [colM_apply]
  rw [this, add_zero]

theorem colU_inv (j : ℕ) (c : Fin n → k) : (colU j c)⁻¹ = colU j (-c) := by
  refine (inv_eq_of_mul_eq_one_right ?_)
  rw [← colU_add, add_neg_cancel, colU_zero]

theorem colU_mul_apply (j : ℕ) (hj : j < n) (c : Fin n → k) (M : Matrix (Fin n) (Fin n) k) (i l : Fin n) :
    ((colU j c : Matrix (Fin n) (Fin n) k) * M) i l = M i l + (if i.val < j then c i * M ⟨j, hj⟩ l else 0) := by
  rw [val_colU, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
  · simp only [colM_apply, and_true]
    split_ifs <;> simp
  · intro a _ ha
    have : ¬ (a.val = j) := fun h => ha (Fin.ext h)
    simp [colM_apply, this]
  · simp

theorem colU_single_of_lt (j : ℕ) (hj : j < n) {r : Fin n} (hr : r.val < j) (a : k) :
    colU j (Pi.single r a) = GlobalTheory.RootUp.elem (i := r) (j := ⟨j, hj⟩) (fun h => by
      have := congrArg Fin.val h; simp at this; omega) a := by
  ext i l
  rw [val_colU, GlobalTheory.RootUp.val_elem, Matrix.add_apply, Matrix.add_apply]
  congr 1
  rw [colM_apply, Matrix.single_apply]
  by_cases hi : i = r
  · subst hi
    by_cases hl : l.val = j
    · have : (⟨j, hj⟩ : Fin n) = l := Fin.ext hl.symm
      simp [hr, hl, this]
    · have : (⟨j, hj⟩ : Fin n) ≠ l := fun h => hl (by rw [← h])
      simp [hl, this]
  · have : r ≠ i := Ne.symm hi
    simp [Pi.single_apply, hi, this]

theorem colU_single_of_ge (j : ℕ) {r : Fin n} (hr : j ≤ r.val) (a : k) : colU j (Pi.single r a) = 1 := by
  ext i l
  rw [val_colU, Units.val_one, Matrix.add_apply, colM_apply]
  by_cases hi : i = r
  · subst hi; simp [show ¬ i.val < j by omega]
  · simp [Pi.single_apply, hi]

end DiscreteGroups.sglob.LConvGenM
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

def Nset (m : ℕ) : Set (GL (Fin n) k) :=
  {g | ∀ i l : Fin n, (l ≤ i ∨ l.val < m) → (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l}

def sdS (m : ℕ) (M : Matrix (Fin n) (Fin n) k) : k :=
  ∑ i : Fin n, ∑ l : Fin n, if l.val = i.val + 1 ∧ m ≤ l.val then M i l else 0

def Good (j : ℕ) (x : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i l : Fin n, (j ≤ i.val ∨ j + 1 ≤ l.val) → x i l = (1 : Matrix (Fin n) (Fin n) k) i l

theorem mul_col_of_good {j : ℕ} {Y : Matrix (Fin n) (Fin n) k} (hY : Good j Y) (M : Matrix (Fin n) (Fin n) k)
    {i l : Fin n} (hl : j + 1 ≤ l.val) : (M * Y) i l = M i l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · rw [hY l l (Or.inr hl), one_apply_eq, mul_one]
  · intro b _ hb; rw [hY b l (Or.inr hl), one_apply_ne hb, mul_zero]
  · simp

theorem mul_row_of_good {j : ℕ} {X : Matrix (Fin n) (Fin n) k} (hX : Good j X) (M : Matrix (Fin n) (Fin n) k)
    {i l : Fin n} (hi : j ≤ i.val) : (X * M) i l = M i l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hX i i (Or.inl hi), one_apply_eq, one_mul]
  · intro b _ hb; rw [hX i b (Or.inl hi), one_apply_ne (Ne.symm hb), zero_mul]
  · simp

theorem good_conj {j : ℕ} (x : GL (Fin n) k) (hx : Good j (x : Matrix (Fin n) (Fin n) k))
    (hy : Good j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Nset (j + 1)) :
    x * g * x⁻¹ ∈ Nset (j + 1) ∧ sdS (j + 1) ((x * g * x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      sdS (j + 1) (g : Matrix (Fin n) (Fin n) k) := by
  set X := (x : Matrix (Fin n) (Fin n) k)
  set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  set G := (g : Matrix (Fin n) (Fin n) k)
  have hXY : X * Y = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hval : ((x * g * x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = X * G * Y := by
    simp only [Units.val_mul, X, Y, G]

  have hA : ∀ i l : Fin n, l.val < j + 1 → (X * G * Y) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
    intro i l hl
    have hGY : ∀ a, (G * Y) a l = Y a l := by
      intro a
      rw [Matrix.mul_apply, ← one_mul Y, Matrix.mul_apply, one_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b.val < j + 1
      · exact congrArg (· * Y b l) (hg a b (Or.inr hb))
      · have h1 : Y b l = 0 := by
          rw [hy b l (Or.inl (by omega)), one_apply_ne]; intro h; rw [h] at hb; omega
        rw [h1, mul_zero, mul_zero]
    rw [Matrix.mul_assoc, Matrix.mul_apply, ← hXY, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [hGY]

  have hB : ∀ i l : Fin n, j ≤ i.val → j + 1 ≤ l.val → (X * G * Y) i l = G i l := by
    intro i l hi hl
    rw [mul_col_of_good hy _ hl, mul_row_of_good hx _ hi]
  refine ⟨fun i l hil => ?_, ?_⟩
  · rw [hval]
    by_cases hl : l.val < j + 1
    · exact hA i l hl
    · have hli : l ≤ i := hil.resolve_right hl
      rw [hB i l (by rw [Fin.le_iff_val_le_val] at hli; omega) (by omega)]
      exact hg i l (Or.inl hli)
  · rw [hval, sdS, sdS]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs with h
    · exact hB i l (by omega) h.2
    · rfl

end DiscreteGroups.sglob.LConvGenM
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem good_colU (j : ℕ) (c : Fin n → k) : Good j ((colU j c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  rw [val_colU, Matrix.add_apply, colM_apply, if_neg (by omega), add_zero]

theorem good_colU_inv (j : ℕ) (c : Fin n → k) :
    Good j (((colU j c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [colU_inv]; exact good_colU j _

theorem peel_apply (j : ℕ) (hj : j < n) (g : GL (Fin n) k) (i l : Fin n) :
    ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l =
      (g : Matrix (Fin n) (Fin n) k) i l + (if i.val < j then
        -(g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ * (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l else 0) := by
  rw [Units.val_mul, colU_mul_apply j hj]
  rfl

theorem peel_N (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) {g : GL (Fin n) k} (hg : g ∈ Nset j) :
    colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g ∈ Nset (j + 1) ∧
    sdS j (g : Matrix (Fin n) (Fin n) k) =
      sdS (j + 1) ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) + (g : Matrix (Fin n) (Fin n) k) ⟨j - 1, by omega⟩ ⟨j, hj⟩ := by
  have hg' : ∀ i l : Fin n, (l ≤ i ∨ l.val < j) → (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := hg
  have hjj : (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ ⟨j, hj⟩ = 1 := by rw [hg' _ _ (Or.inl le_rfl), one_apply_eq]
  have hrow : ∀ l : Fin n, l.val < j → (g : Matrix (Fin n) (Fin n) k) ⟨j, hj⟩ l = 0 := fun l hl => by
    rw [hg' _ _ (Or.inr hl), one_apply_ne]; intro h; rw [← h] at hl; simp at hl
  have hhi : ∀ i l : Fin n, j ≤ i.val → ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k) i l = (g : Matrix (Fin n) (Fin n) k) i l := fun i l hi => by
    rw [peel_apply, if_neg (by omega), add_zero]
  refine ⟨fun i l hil => ?_, ?_⟩
  · rw [peel_apply]
    by_cases hl : l.val < j
    · rw [hg' i l (Or.inr hl), hrow l hl]; simp
    · by_cases hlj : l.val = j
      · have hl' : l = ⟨j, hj⟩ := Fin.ext hlj
        subst hl'
        by_cases hi : i.val < j
        · rw [if_pos hi, hjj, mul_one, add_neg_cancel, one_apply_ne]
          intro h; rw [h] at hi; simp at hi
        · rw [if_neg hi, add_zero]
          exact hg' i _ (Or.inl (by rw [Fin.le_iff_val_le_val]; simp; omega))
      · have hli : l ≤ i := hil.resolve_right (by omega)
        rw [if_neg (by rw [Fin.le_iff_val_le_val] at hli; omega), add_zero]
        exact hg' i l (Or.inl hli)
  · have key : ∀ i l : Fin n, (if l.val = i.val + 1 ∧ j ≤ l.val then (g : Matrix (Fin n) (Fin n) k) i l else 0) =
        (if l.val = i.val + 1 ∧ j + 1 ≤ l.val then ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
          Matrix (Fin n) (Fin n) k) i l else 0) +
        (if i = (⟨j - 1, by omega⟩ : Fin n) then (if l = (⟨j, hj⟩ : Fin n) then (g : Matrix (Fin n) (Fin n) k) i l else 0) else 0) := by
      intro i l
      by_cases h2 : l.val = i.val + 1 ∧ j + 1 ≤ l.val
      · rw [if_pos ⟨h2.1, by omega⟩, if_pos h2, hhi i l (by omega),
          if_neg (fun h => by rw [Fin.ext_iff] at h; simp at h; omega), add_zero]
      · rw [if_neg h2, zero_add]
        by_cases h1 : l.val = i.val + 1 ∧ j ≤ l.val
        · have e1 : i = ⟨j - 1, by omega⟩ := Fin.ext (by simp; omega)
          have e2 : l = ⟨j, hj⟩ := Fin.ext (by simp; omega)
          rw [if_pos h1, if_pos e1, if_pos e2]
        · rw [if_neg h1]
          by_cases e1 : i = ⟨j - 1, by omega⟩
          · by_cases e2 : l = ⟨j, hj⟩
            · exfalso; apply h1; rw [e1, e2]; simp; omega
            · rw [if_pos e1, if_neg e2]
          · rw [if_neg e1]
    rw [sdS, sdS]
    simp only [key, Finset.sum_add_distrib]
    congr 1
    simp

end DiscreteGroups.sglob.LConvGenM
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem entries_of_mem_unipRad (j : ℕ) (h : ∑ i, ![j, n - j] i = n) {g : GL (Fin n) k}
    (hg : g ∈ unipRad k (stdBlocks ![j, n - j] h)) (i l : Fin n) (hil : ¬ (i.val < j ∧ j ≤ l.val)) :
    (g : Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
  refine GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 hg i l ?_
  rw [GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two]
  by_cases hi : i.val < j
  · have hl : l.val < j := by omega
    simp [hi, hl]
  · simp only [hi, if_false]
    split_ifs <;> decide

theorem peel_rad (j : ℕ) (hj : j < n) (h : ∑ i, ![j, n - j] i = n) {g : GL (Fin n) k}
    (hg : g ∈ unipRad k (stdBlocks ![j, n - j] h)) :
    colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g ∈ Nset (j + 1) ∧
    sdS (j + 1) ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = 0 := by
  have hent := entries_of_mem_unipRad j h hg
  have key : ∀ i l : Fin n, ¬ (i.val < j ∧ j + 1 ≤ l.val) →
      ((colU j (-(fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩)) * g : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) i l = (1 : Matrix (Fin n) (Fin n) k) i l := by
    intro i l hil
    rw [peel_apply]
    by_cases hi : i.val < j
    · rw [if_pos hi, hent ⟨j, hj⟩ l (by simp)]
      by_cases hlj : l.val = j
      · have hl' : l = ⟨j, hj⟩ := Fin.ext hlj
        subst hl'
        rw [one_apply_eq, mul_one, add_neg_cancel, one_apply_ne]
        intro e; rw [e] at hi; simp at hi
      · have hne : (⟨j, hj⟩ : Fin n) ≠ l := fun e => hlj (by rw [← e])
        rw [one_apply_ne hne, mul_zero, add_zero, hent i l (by omega)]
    · rw [if_neg hi, add_zero, hent i l (by omega)]
  refine ⟨fun i l hil => key i l (by
    rcases hil with hil | hil
    · rw [Fin.le_iff_val_le_val] at hil; omega
    · omega), ?_⟩
  rw [sdS]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
  split_ifs with hh
  · rw [key i l (by omega), one_apply_ne]
    intro e; rw [e] at hh; omega
  · rfl

def TopLeft (j : ℕ) (x : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i l : Fin n, (j ≤ i.val ∨ j ≤ l.val) → x i l = (1 : Matrix (Fin n) (Fin n) k) i l

theorem TopLeft.good {j : ℕ} {x : Matrix (Fin n) (Fin n) k} (hx : TopLeft j x) : Good j x :=
  fun i l h => hx i l (by omega)

def dotj (j : ℕ) (ξ c : Fin n → k) : k := ∑ i : Fin n, if i.val < j then ξ i * c i else 0

def rowMul (j : ℕ) (ξ : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) : Fin n → k :=
  fun a => ∑ i : Fin n, if i.val < j then ξ i * Y i a else 0

def colMul (j : ℕ) (Y : Matrix (Fin n) (Fin n) k) (c : Fin n → k) : Fin n → k :=
  fun i => ∑ a : Fin n, if a.val < j then Y i a * c a else 0

theorem dotj_colMul (j : ℕ) (ξ c : Fin n → k) (Y : Matrix (Fin n) (Fin n) k) :
    dotj j ξ (colMul j Y c) = dotj j (rowMul j ξ Y) c := by
  let F : Fin n → Fin n → k := fun i a => if i.val < j ∧ a.val < j then ξ i * Y i a * c a else 0
  have hL : dotj j ξ (colMul j Y c) = ∑ i : Fin n, ∑ a : Fin n, F i a := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val < j
    · rw [if_pos hi, colMul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by by_cases ha : a.val < j <;> simp [F, hi, ha, mul_assoc]
    · rw [if_neg hi]; simp [F, hi]
  have hR : dotj j (rowMul j ξ Y) c = ∑ a : Fin n, ∑ i : Fin n, F i a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a.val < j
    · rw [if_pos ha, rowMul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by by_cases hi : i.val < j <;> simp [F, hi, ha]
    · rw [if_neg ha]; simp [F, ha]
  rw [hL, hR, Finset.sum_comm]

end DiscreteGroups.sglob.LConvGenM
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

theorem conj_colU (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (c : Fin n → k) :
    x⁻¹ * colU j c * x = colU j (colMul j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c) := by
  set X := (x : Matrix (Fin n) (Fin n) k)
  set Y := ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  have hYX : Y * X = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYC : Y * colM j c = colM j (colMul j Y c) := by
    ext i b
    rw [Matrix.mul_apply, colM_apply]
    by_cases hb : b.val = j
    · simp only [colM_apply, hb, and_true]
      by_cases hi : i.val < j
      · rw [if_pos hi, colMul]
        exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun a _ => ?_
        split_ifs with ha
        · rw [hy i a (Or.inl (by omega)), one_apply_ne (by intro e; rw [e] at hi; omega), zero_mul]
        · rw [mul_zero]
    · simp [colM_apply, hb]
  have hCX : ∀ d : Fin n → k, colM j d * X = colM j d := by
    intro d
    ext i l
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · rw [hx _ l (Or.inl le_rfl)]
      by_cases hl : (⟨j, hj⟩ : Fin n) = l
      · rw [← hl, one_apply_eq, mul_one]
      · rw [one_apply_ne hl, mul_zero, colM_apply, if_neg (fun h => hl (Fin.ext h.2.symm))]
    · intro b _ hb
      rw [colM_apply, if_neg (fun h => hb (Fin.ext h.2)), zero_mul]
    · simp
  ext : 1
  rw [Units.val_mul, Units.val_mul, val_colU, val_colU, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hYX, hYC, hCX]

def i0 (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) : Fin n := ⟨j - 1, by omega⟩

section RankOne

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (ξ : Fin n → k)

def vrow : Fin n → k := fun l => if l.val < j then ξ l - (if l = i0 j hj hj1 then 1 else 0) else 0

def R1 : Matrix (Fin n) (Fin n) k := Matrix.of fun i l => if i = i0 j hj hj1 then vrow j hj hj1 ξ l else 0

theorem rankOne_mul_self : R1 j hj hj1 ξ * R1 j hj hj1 ξ = (vrow j hj hj1 ξ (i0 j hj hj1)) • R1 j hj hj1 ξ := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (i0 j hj hj1)]
  · simp only [R1, of_apply, Matrix.smul_apply, smul_eq_mul, if_true]
    split_ifs <;> ring
  · intro b _ hb; simp [R1, hb]
  · simp

theorem rowVector_at_index : vrow j hj hj1 ξ (i0 j hj hj1) = ξ (i0 j hj hj1) - 1 := by
  simp [vrow, i0, show j - 1 < j by omega]

theorem rankOne_top_left_zero : ∀ i l : Fin n, (j ≤ i.val ∨ j ≤ l.val) → R1 j hj hj1 ξ i l = 0 := by
  intro i l h
  simp only [R1, of_apply]
  split_ifs with hi
  · have : ¬ l.val < j := by rw [hi] at h; simp [i0] at h; omega
    simp [vrow, this]
  · rfl

end RankOne

end DiscreteGroups.sglob.LConvGenM
