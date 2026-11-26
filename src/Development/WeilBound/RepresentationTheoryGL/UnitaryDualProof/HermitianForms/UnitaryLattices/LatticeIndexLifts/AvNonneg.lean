module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.SmoothCol

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.KerOpen
namespace PositivityTheory.RgUd.Form.U.Lift2.KerOpen

open Filter Topology

theorem isOpen_ker {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (φ : AddChar k Circle) (hφ : Continuous φ) :
    IsOpen {x : k | φ x = 1} := by

  let K : AddSubgroup k :=
    { carrier := {x | φ x = 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [AddChar.map_add_eq_mul, ha, hb, one_mul]
      zero_mem' := AddChar.map_zero_eq_one φ
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [AddChar.map_neg_eq_inv, ha, inv_one] }

  have h1 : (1 : Circle) ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  have hU : φ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : k) := by
    apply hφ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact (Circle.isOpen_centeredArc _).mem_nhds h1

  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hU
  let B : AddSubgroup k := (ValuativeRel.valuation k).ltAddSubgroup (Units.mk0 γ hγ)
  have hB : (B : Set k) = {x | ValuativeRel.valuation k x < γ} := rfl

  have hBK : (B : Set k) ⊆ K := by
    intro x hx
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    rw [← AddChar.map_nsmul_eq_pow]
    apply hsub
    rw [← hB]
    exact B.nsmul_mem hx n
  have hBn : (B : Set k) ∈ 𝓝 (0 : k) := by
    rw [hB]
    exact (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ
  exact AddSubgroup.isOpen_of_mem_nhds K (Filter.mem_of_superset hBn hBK)

end PositivityTheory.RgUd.Form.U.Lift2.KerOpen
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.BesselAbs
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.SummandInv
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.SumCharEqZero
noncomputable section

open Matrix
open scoped Topology

namespace PositivityTheory.RgUd.Form.U.Lift2.AvA

section Grp

variable {G : Type*} [AddCommGroup G]

theorem sum_transl {M : Type*} [AddCommMonoid M] (A H : AddSubgroup G) (_hHA : H ≤ A) (T : Finset G)
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (f : G → M) (hf : ∀ x, ∀ h ∈ H, f (x + h) = f x) (a : G) (ha : a ∈ A) :
    ∑ t ∈ T, f (t + a) = ∑ t ∈ T, f t := by
  classical
  have hex : ∀ x ∈ A, ∃ t, t ∈ T ∧ x - t ∈ H := fun x hx => (hu x hx).exists
  let r : G → G := fun x => if hx : x ∈ A then (hex x hx).choose else x
  have hr : ∀ x ∈ A, r x ∈ T ∧ x - r x ∈ H := by
    intro x hx
    simp only [r, dif_pos hx]
    exact (hex x hx).choose_spec
  have huniq : ∀ x ∈ A, ∀ t ∈ T, x - t ∈ H → r x = t := fun x hx t ht hxt =>
    (hu x hx).unique (hr x hx) ⟨ht, hxt⟩
  have hfr : ∀ x ∈ A, f x = f (r x) := by
    intro x hx
    have := hf (r x) (x - r x) (hr x hx).2
    rw [add_sub_cancel] at this
    exact this
  refine Finset.sum_nbij' (fun t => r (t + a)) (fun t => r (t - a)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact (hr _ (A.add_mem (hT t ht) ha)).1
  · intro t ht
    exact (hr _ (A.sub_mem (hT t ht) ha)).1
  · intro t ht
    have h1 := hr (t + a) (A.add_mem (hT t ht) ha)
    apply huniq _ (A.sub_mem (hT _ h1.1) ha) t ht
    have : r (t + a) - a - t = -((t + a) - r (t + a)) := by abel
    rw [this]
    exact H.neg_mem h1.2
  · intro t ht
    have h1 := hr (t - a) (A.sub_mem (hT t ht) ha)
    apply huniq _ (A.add_mem (hT _ h1.1) ha) t ht
    have : r (t - a) + a - t = -((t - a) - r (t - a)) := by abel
    rw [this]
    exact H.neg_mem h1.2
  · intro t ht
    exact hfr _ (A.add_mem (hT t ht) ha)

theorem card_ne_zero (A H : AddSubgroup G) (T : Finset G) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) :
    (T.card : ℂ) ≠ 0 := by
  obtain ⟨t, ⟨ht, -⟩, -⟩ := hu 0 A.zero_mem
  exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨t, ht⟩)

theorem sum_char_eq_zero (A H : AddSubgroup G) (hHA : H ≤ A) (T : Finset G)
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (χ : G → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hH : ∀ h ∈ H, χ h = 1)
    (a : G) (ha : a ∈ A) (hne : χ a ≠ 1) : ∑ t ∈ T, χ t = 0 := by
  have h := sum_transl A H hHA T hT hu χ (fun x h hh => by rw [hχ, hH h hh, mul_one]) a ha
  simp_rw [hχ] at h
  rw [← Finset.sum_mul] at h
  have : (∑ t ∈ T, χ t) * (χ a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact h1
  · exact absurd (sub_eq_zero.1 h1) hne

theorem avg_indep {M : Type*} [AddCommGroup M] [Module ℂ M] (A H K : AddSubgroup G) (hHA : H ≤ A)
    (hKA : K ≤ A) (S R : Finset G)
    (hS : ∀ t ∈ S, t ∈ A) (huS : ∀ a ∈ A, ∃! t, t ∈ S ∧ a - t ∈ H)
    (hR : ∀ t ∈ R, t ∈ A) (huR : ∀ a ∈ A, ∃! t, t ∈ R ∧ a - t ∈ K)
    (f : G → M) (hfH : ∀ x, ∀ h ∈ H, f (x + h) = f x) (hfK : ∀ x, ∀ h ∈ K, f (x + h) = f x) :
    ((S.card : ℂ)⁻¹) • ∑ t ∈ S, f t = ((R.card : ℂ)⁻¹) • ∑ t ∈ R, f t := by
  have e1 : ∑ r ∈ R, ∑ t ∈ S, f (t + r) = (R.card : ℂ) • ∑ t ∈ S, f t := by
    rw [Finset.sum_congr rfl (fun r hr => sum_transl A H hHA S hS huS f hfH r (hR r hr))]
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have e2 : ∑ t ∈ S, ∑ r ∈ R, f (r + t) = (S.card : ℂ) • ∑ t ∈ R, f t := by
    rw [Finset.sum_congr rfl (fun t ht => sum_transl A K hKA R hR huR f hfK t (hS t ht))]
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have key : (R.card : ℂ) • ∑ t ∈ S, f t = (S.card : ℂ) • ∑ t ∈ R, f t := by
    rw [← e1, ← e2, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [add_comm]
  have hSp := card_ne_zero A H S huS
  have hRp := card_ne_zero A K R huR
  have hX : (∑ t ∈ S, f t) = (R.card : ℂ)⁻¹ • ((S.card : ℂ) • ∑ t ∈ R, f t) := by
    rw [← key, smul_smul, inv_mul_cancel₀ hRp, one_smul]
  rw [hX, smul_smul, smul_smul, mul_comm ((S.card : ℂ)⁻¹) ((R.card : ℂ)⁻¹), mul_assoc,
    inv_mul_cancel₀ hSp, mul_one]

theorem sum_circ_eq_zero (A H : AddSubgroup G) (hHA : H ≤ A) (T : Finset G)
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (χ : G → Circle) (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hH : ∀ h ∈ H, χ h = 1)
    (a : G) (ha : a ∈ A) (hne : χ a ≠ 1) : ∑ t ∈ T, ((χ t : Circle) : ℂ) = 0 :=
  sum_char_eq_zero A H hHA T hT hu (fun x => (χ x : ℂ)) (fun x y => by rw [hχ, Circle.coe_mul])
    (fun h hh => by rw [hH h hh, Circle.coe_one]) a ha (fun h => hne (Circle.coe_eq_one.1 h))

theorem exists_tr [TopologicalSpace G] [IsTopologicalAddGroup G] (A H : AddSubgroup G)
    (hAc : IsCompact (A : Set G)) (hH : IsOpen (H : Set G)) (hHA : H ≤ A) :
    ∃ T : Finset G, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  classical
  obtain ⟨F, hF⟩ := hAc.elim_finite_subcover (fun a : A => (fun x => x - (a : G)) ⁻¹' (H : Set G))
    (fun a => hH.preimage (continuous_sub_right _))
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simp [H.zero_mem]⟩)
  let r : G → G := fun x => Quotient.out (QuotientAddGroup.mk x : G ⧸ H)
  have hr : ∀ x, r x - x ∈ H := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add H x
    simp only [r]
    rw [hh, add_sub_cancel_left]
    exact h.2
  have hrr : ∀ x y, x - y ∈ H → r x = r y := fun x y hxy => by
    simp only [r]
    congr 1
    refine QuotientAddGroup.eq.2 ?_
    have : -x + y = -(x - y) := by abel
    rw [this]
    exact H.neg_mem hxy
  have hrA : ∀ x ∈ A, r x ∈ A := fun x hx => by
    have : r x = x + (r x - x) := by abel
    rw [this]
    exact A.add_mem hx (hHA (hr x))
  refine ⟨F.image (fun a : A => r a), ?_, ?_⟩
  · intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 ht
    exact hrA a a.2
  · intro a ha
    obtain ⟨i, hi, hai⟩ := Set.mem_iUnion₂.1 (hF ha)
    refine ⟨r i, ⟨Finset.mem_image.2 ⟨i, hi, rfl⟩, ?_⟩, ?_⟩
    · have : a - r i = (a - i) - (r i - i) := by abel
      rw [this]
      exact H.sub_mem hai (hr i)
    · rintro t ⟨ht, hat⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
      have h1 : r (r j) = r j := hrr _ _ (hr j)
      have h2 : r (r i) = r i := hrr _ _ (hr i)
      have h3 : r j - r i ∈ H := by
        have : r j - r i = (a - r i) - (a - r j) := by abel
        rw [this]
        have : a - r i = (a - i) - (r i - i) := by abel
        rw [this]
        exact H.sub_mem (H.sub_mem hai (hr i)) hat
      rw [← h1, ← h2]
      exact hrr _ _ h3

end Grp

theorem isOpen_ker {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : AddChar k Circle) (hφ : Continuous φ) : IsOpen {x : k | φ x = 1} :=
  PositivityTheory.RgUd.Form.U.Lift2.KerOpen.isOpen_ker φ hφ

end PositivityTheory.RgUd.Form.U.Lift2.AvA
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix
open scoped Topology

namespace PositivityTheory.RgUd.Form.U.Lift2.AvA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def stab (col : (Fin n → k) → V →ₗ[ℂ] V) (hc0 : ∀ v, col 0 v = v)
    (hca : ∀ x y v, col (x + y) v = col x (col y v)) (v : V) : AddSubgroup (Fin n → k) where
  carrier := {x | col x v = v}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [hca, hy, hx]
  zero_mem' := hc0 v
  neg_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    calc col (-x) v = col (-x) (col x v) := by rw [hx]
      _ = col (-x + x) v := (hca _ _ _).symm
      _ = v := by rw [neg_add_cancel, hc0]

def kers (φ : AddChar k Circle) (s : Finset (Fin n → k)) : AddSubgroup (Fin n → k) where
  carrier := {x | ∀ ξ ∈ s, φ (ξ ⬝ᵥ x) = 1}
  add_mem' := by
    intro x y hx hy ξ hξ
    rw [dotProduct_add, AddChar.map_add_eq_mul, hx ξ hξ, hy ξ hξ, one_mul]
  zero_mem' := by
    intro ξ _
    simp
  neg_mem' := by
    intro x hx ξ hξ
    rw [dotProduct_neg, AddChar.map_neg_eq_inv, hx ξ hξ, inv_one]

theorem isOpen_kers (φ : AddChar k Circle) (hφ : Continuous φ) (s : Finset (Fin n → k)) :
    IsOpen (kers φ s : Set (Fin n → k)) := by
  have : (kers φ s : Set (Fin n → k)) = ⋂ ξ ∈ s, {x | φ (ξ ⬝ᵥ x) = 1} := by
    ext x
    simp [kers]
  rw [this]
  refine isOpen_biInter_finset fun ξ _ => ?_
  exact (isOpen_ker φ hφ).preimage (by fun_prop)

theorem exists_AD (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (hsm : ∀ v, IsOpen {x | col x v = v})
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (s : Finset (Fin n → k)) (v : V) :
    ∃ p : AddSubgroup (Fin n → k) × Finset (Fin n → k), ∀ ξ ∈ s, AD φ col ξ A v p := by
  let H := A ⊓ stab col hc0 hca v ⊓ kers φ s
  have hHo : IsOpen (H : Set (Fin n → k)) := by
    simp only [H, AddSubgroup.coe_inf]
    exact (hA.2.inter (hsm v)).inter (isOpen_kers φ hφ s)
  have hHA : H ≤ A := fun x hx => hx.1.1
  obtain ⟨T, hT, hu⟩ := exists_tr A H hA.1 hHo hHA
  exact ⟨(H, T), fun ξ hξ => ⟨hHA, hHo, fun a ha => ha.1.2, fun a ha => ha.2 ξ hξ, hT, hu⟩⟩

theorem summand_inv (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hca : ∀ x y v, col (x + y) v = col x (col y v)) (ξ : Fin n → k) (v : V) (H : AddSubgroup (Fin n → k))
    (h3 : ∀ a ∈ H, col a v = v) (h4 : ∀ a ∈ H, φ (ξ ⬝ᵥ a) = 1) :
    ∀ x, ∀ h ∈ H, (fun t => (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v) (x + h) =
      (fun t => (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v) x := by
  intro x h hh
  simp only [dotProduct_add, AddChar.map_add_eq_mul, h4 h hh, mul_one, hca, h3 h hh]

theorem av_eq' (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (A : AddSubgroup (Fin n → k)) (ξ : Fin n → k) (v : V) (p : AddSubgroup (Fin n → k) × Finset (Fin n → k))
    (hp : AD φ col ξ A v p) :
    av φ col ξ A v = ((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v := by
  have hd : ∃ p, AD φ col ξ A v p := ⟨p, hp⟩
  unfold av
  rw [dite_eq_left hd]
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hd.choose_spec
  obtain ⟨g1, -, g3, g4, g5, g6⟩ := hp
  exact avg_indep A _ _ h1 g1 _ _ h5 h6 g5 g6 _ (summand_inv φ col hca ξ v _ h3 h4)
    (summand_inv φ col hca ξ v _ g3 g4)

theorem circ_char (φ ψ : AddChar k Circle) (ξ η : Fin n → k) (x y : Fin n → k) :
    (φ (ξ ⬝ᵥ (x + y)))⁻¹ * ψ (η ⬝ᵥ (x + y)) = ((φ (ξ ⬝ᵥ x))⁻¹ * ψ (η ⬝ᵥ x)) * ((φ (ξ ⬝ᵥ y))⁻¹ * ψ (η ⬝ᵥ y)) := by
  rw [dotProduct_add, dotProduct_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

open Classical in
theorem av_eigen' (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (E : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (ψ : AddChar k Circle) (η : Fin n → k)
    (hE : ∀ x u w, E (col x u) w = ((ψ (η ⬝ᵥ x) : Circle) : ℂ) * E u w)
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (ξ : Fin n → k) (v w : V) :
    E (av φ col ξ A v) w = if ∀ a ∈ A, ψ (η ⬝ᵥ a) = φ (ξ ⬝ᵥ a) then E v w else 0 := by
  obtain ⟨p, hp⟩ := exists_AD φ hφ col hc0 hca hsm A hA {ξ} v
  have hp' := hp ξ (Finset.mem_singleton_self ξ)
  rw [av_eq' φ col hca A ξ v p hp']
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hp'
  let χ : (Fin n → k) → Circle := fun t => (φ (ξ ⬝ᵥ t))⁻¹ * ψ (η ⬝ᵥ t)
  have hexp : E (((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2, (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v) w
      = ((p.2.card : ℂ)⁻¹ * ∑ t ∈ p.2, ((χ t : Circle) : ℂ)) * E v w := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, hE]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [χ, Circle.coe_mul, Circle.coe_inv_eq_conj]
    ring
  rw [hexp]
  by_cases hEv : E v w = 0
  · rw [hEv, mul_zero]
    split_ifs <;> rfl
  have hψ : ∀ a ∈ p.1, ψ (η ⬝ᵥ a) = 1 := by
    intro a ha
    have h := hE a v w
    rw [h3 a ha] at h
    have h' : (((ψ (η ⬝ᵥ a) : Circle) : ℂ) - 1) * E v w = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    exact Circle.coe_eq_one.1 (sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hEv))
  have hχH : ∀ a ∈ p.1, χ a = 1 := by
    intro a ha
    simp only [χ, h4 a ha, hψ a ha, inv_one, mul_one]
  have hN := card_ne_zero A p.1 p.2 h6
  split_ifs with hc
  · have : ∑ t ∈ p.2, ((χ t : Circle) : ℂ) = p.2.card := by
      rw [Finset.sum_congr rfl (fun t ht => by
        simp only [χ, hc t (h5 t ht), inv_mul_cancel, Circle.coe_one] : ∀ t ∈ p.2, ((χ t : Circle) : ℂ) = 1)]
      simp
    rw [this, inv_mul_cancel₀ hN, one_mul]
  · simp only [not_forall] at hc
    obtain ⟨a, ha, hne⟩ := hc
    have hχa : χ a ≠ 1 := by
      intro h
      apply hne
      have := congrArg (fun z => φ (ξ ⬝ᵥ a) * z) h
      simpa [χ] using this
    rw [sum_circ_eq_zero A p.1 h1 p.2 h5 h6 χ (circ_char φ ψ ξ η) hχH a ha hχa, mul_zero, zero_mul]

theorem mulVec_ginv (g : GL (Fin n) k) (x : Fin n → k) :
    ((g : Matrix (Fin n) (Fin n) k)) *ᵥ (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem ginv_mulVec (g : GL (Fin n) k) (x : Fin n → k) :
    (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem mem_gmap (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (x : Fin n → k) :
    x ∈ gmap g A ↔ (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ x ∈ A := by
  simp only [gmap, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [ginv_mulVec]
  · intro h
    exact ⟨_, h, mulVec_ginv g x⟩

theorem isOpen_gmap (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : IsOpen (A : Set (Fin n → k))) :
    IsOpen (gmap g A : Set (Fin n → k)) := by
  have : (gmap g A : Set (Fin n → k)) =
      (fun x => (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ x) ⁻¹' (A : Set (Fin n → k)) := by
    ext x
    exact mem_gmap g A x
  rw [this]
  exact hA.preimage (continuous_const.matrix_mulVec continuous_id)

theorem lat_gmap' (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) : Lat (gmap g A) := by
  refine ⟨?_, isOpen_gmap g A hA.2⟩
  have : (gmap g A : Set (Fin n → k)) = (fun x => (g : Matrix (Fin n) (Fin n) k) *ᵥ x) '' (A : Set (Fin n → k)) := by
    simp only [gmap, AddSubgroup.coe_map]
    rfl
  rw [this]
  exact hA.1.image (continuous_const.matrix_mulVec continuous_id)

theorem dot_g (g : GL (Fin n) k) (ξ x : Fin n → k) :
    (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ⬝ᵥ x =
      ξ ⬝ᵥ ((((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ x) := by
  rw [dotProduct_mulVec]

theorem av_conj' (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (gl : GL (Fin n) k →* (V →ₗ[ℂ] V))
    (hconj : ∀ g x v, gl g (col x v) = col ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) (gl g v))
    (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) (ξ : Fin n → k) (v : V) :
    gl g (av φ col ξ A v) = av φ col (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (gmap g A) (gl g v) := by
  classical
  obtain ⟨p, hp⟩ := exists_AD φ hφ col hc0 hca hsm A hA {ξ} v
  have hp' := hp ξ (Finset.mem_singleton_self ξ)
  rw [av_eq' φ col hca A ξ v p hp']
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp'
  have hinj : Function.Injective (fun t : Fin n → k => (g : Matrix (Fin n) (Fin n) k) *ᵥ t) := by
    intro x y hxy
    have := congrArg (fun z => (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ z) hxy
    simpa only [ginv_mulVec] using this
  let q : AddSubgroup (Fin n → k) × Finset (Fin n → k) :=
    (gmap g p.1, p.2.image (fun t => (g : Matrix (Fin n) (Fin n) k) *ᵥ t))
  have hsub : ∀ a t, (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ (a - (g : Matrix (Fin n) (Fin n) k) *ᵥ t)
      = (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *ᵥ a - t := by
    intro a t
    rw [Matrix.mulVec_sub, ginv_mulVec]
  have hq : AD φ col (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (gmap g A) (gl g v) q := by
    refine ⟨AddSubgroup.map_mono h1, isOpen_gmap g p.1 h2, ?_, ?_, ?_, ?_⟩
    · intro a ha
      rw [mem_gmap] at ha
      rw [← mulVec_ginv g a, ← hconj, h3 _ ha]
    · intro a ha
      rw [mem_gmap] at ha
      rw [dot_g]
      exact h4 _ ha
    · intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 ht
      rw [mem_gmap, ginv_mulVec]
      exact h5 t₀ ht₀
    · intro a ha
      rw [mem_gmap] at ha
      obtain ⟨t₀, ⟨ht₀, hb⟩, huq⟩ := h6 _ ha
      refine ⟨(g : Matrix (Fin n) (Fin n) k) *ᵥ t₀, ⟨Finset.mem_image.2 ⟨t₀, ht₀, rfl⟩, ?_⟩, ?_⟩
      · rw [mem_gmap, hsub]
        exact hb
      · rintro t ⟨ht, hat⟩
        obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.1 ht
        rw [mem_gmap, hsub] at hat
        rw [huq t₁ ⟨ht₁, hat⟩]
  rw [av_eq' φ col hca (gmap g A) _ (gl g v) q hq]
  simp only [q]
  rw [Finset.card_image_of_injective _ hinj, Finset.sum_image (fun x _ y _ h => hinj h)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, hconj, dot_g, ginv_mulVec]

end PositivityTheory.RgUd.Form.U.Lift2.AvA
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace PositivityTheory.RgUd.Form.U.Lift2.AvA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

theorem B_u (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : (Fin n → k) → ℂ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (T : Finset (Fin n → k)) (v w : V) :
    B (∑ t ∈ T, c t • col t v) w = ∑ t ∈ T, c t * B (col t v) w := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem gram (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A H : AddSubgroup (Fin n → k)) (hHA : H ≤ A) (T : Finset (Fin n → k))
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (v : V) (hv : ∀ a ∈ H, col a v = v) (ξ ζ : Fin n → k) (hξ : ∀ a ∈ H, φ (ξ ⬝ᵥ a) = 1) :
    B (∑ t ∈ T, (starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ)) • col t v)
        (∑ r ∈ T, (starRingEnd ℂ ((φ (ζ ⬝ᵥ r) : Circle) : ℂ)) • col r v)
      = (∑ r ∈ T, ((((φ (ξ ⬝ᵥ r))⁻¹ * φ (ζ ⬝ᵥ r) : Circle)) : ℂ)) *
          ∑ t ∈ T, starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ) * B (col t v) v := by
  classical
  set f : (Fin n → k) → ℂ := fun x => starRingEnd ℂ ((φ (ξ ⬝ᵥ x) : Circle) : ℂ) * B (col x v) v with hf
  have hfH : ∀ x h, h ∈ H → f (x + h) = f x := by
    intro x h hh
    simp only [hf, dotProduct_add, AddChar.map_add_eq_mul, hξ h hh, mul_one, hca, hv h hh]
  have hsh : ∀ r ∈ T, ∑ t ∈ T, f (t + -r) = ∑ t ∈ T, f t := fun r hr =>
    sum_transl A H hHA T hT hu f hfH (-r) (A.neg_mem (hT r hr))
  have key : ∀ t r, B (col t v) (col r v) = B (col (t - r) v) v := by
    intro t r
    have h1 : col t v = col r (col (t - r) v) := by rw [← hca, add_sub_cancel]
    rw [h1, hBc]
  have hsplit : ∀ t r, starRingEnd ℂ ((φ (ξ ⬝ᵥ t) : Circle) : ℂ) =
      starRingEnd ℂ ((φ (ξ ⬝ᵥ (t + -r)) : Circle) : ℂ) * starRingEnd ℂ ((φ (ξ ⬝ᵥ r) : Circle) : ℂ) := by
    intro t r
    rw [← map_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← dotProduct_add, neg_add_cancel_right]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs =>
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_self_apply, RingHom.id_apply, key, Finset.mul_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [← hsh r hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hsplit t r]
  simp only [hf, Circle.coe_mul, Circle.coe_inv_eq_conj, sub_eq_add_neg]
  ring

theorem gram_av (φ : AddChar k Circle) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v))
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A : AddSubgroup (Fin n → k)) (ξ ζ : Fin n → k) (v : V)
    (p : AddSubgroup (Fin n → k) × Finset (Fin n → k)) (hpξ : AD φ col ξ A v p) (hpζ : AD φ col ζ A v p) :
    B (av φ col ξ A v) (av φ col ζ A v) =
      ((p.2.card : ℂ)⁻¹ * ∑ r ∈ p.2, ((((φ (ξ ⬝ᵥ r))⁻¹ * φ (ζ ⬝ᵥ r) : Circle)) : ℂ)) *
        B (av φ col ξ A v) v := by
  have av_eq_local (η : Fin n → k) (hp : AD φ col η A v p) :
      av φ col η A v = ((p.2.card : ℂ)⁻¹) • ∑ t ∈ p.2,
        (starRingEnd ℂ ((φ (η ⬝ᵥ t) : Circle) : ℂ)) • col t v := by
    have hd : ∃ q, AD φ col η A v q := ⟨p, hp⟩
    unfold av
    rw [dite_eq_left hd]
    obtain ⟨h1, -, h3, h4, h5, h6⟩ := hd.choose_spec
    obtain ⟨g1, -, g3, g4, g5, g6⟩ := hp
    exact avg_indep A _ _ h1 g1 _ _ h5 h6 g5 g6 _
      (summand_inv φ col hca η v _ h3 h4) (summand_inv φ col hca η v _ g3 g4)
  rw [av_eq_local ξ hpξ, av_eq_local ζ hpζ]
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := hpξ
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    gram φ col hc0 hca B hBc A p.1 h1 p.2 h5 h6 v h3 ξ ζ h4, LinearMap.smul_apply, B_u]
  simp only [smul_eq_mul, map_inv₀, map_natCast]
  ring

theorem bessel_abs (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : Psd B) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → V) (v : V)
    (hw : ∀ i ∈ s, ∀ j ∈ s, B (w i) (w j) = if i = j then B (w i) v else 0) :
    ∑ i ∈ s, (B (w i) v).re ≤ (B v v).re := by
  classical
  have hWW : B (∑ i ∈ s, w i) (∑ i ∈ s, w i) = ∑ i ∈ s, B (w i) v := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_congr rfl fun d hd => hw d hd i hi]
    simp [hi]
  have hWv : B (∑ i ∈ s, w i) v = ∑ i ∈ s, B (w i) v := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply]
  have hvW : B v (∑ i ∈ s, w i) = starRingEnd ℂ (∑ i ∈ s, B (w i) v) := by
    rw [hB.1 (∑ i ∈ s, w i) v, hWv]
  have h0 := hB.2 (v - ∑ i ∈ s, w i)
  simp only [map_sub, LinearMap.sub_apply, hWW, hWv, hvW, Complex.sub_re, Complex.conj_re] at h0
  rw [← Complex.re_sum]
  linarith

theorem av_bessel' (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (s : Finset (Fin n → k))
    (hs : ∀ ξ ∈ s, ∀ ξ' ∈ s, ξ - ξ' ∈ perp φ A → ξ = ξ') (v : V) :
    ∑ ξ ∈ s, (B (av φ col ξ A v) v).re ≤ (B v v).re := by
  classical
  obtain ⟨p, hp⟩ := exists_AD φ hφ col hc0 hca hsm A hA s v
  refine bessel_abs B hB s (fun ξ => av φ col ξ A v) v ?_
  intro ξ hξ ξ' hξ'
  show B (av φ col ξ A v) (av φ col ξ' A v) = if ξ = ξ' then B (av φ col ξ A v) v else 0
  rw [gram_av φ col hc0 hca B hBc A ξ ξ' v p (hp ξ hξ) (hp ξ' hξ')]
  have hcard := card_ne_zero A p.1 p.2 (hp ξ hξ).2.2.2.2.2
  split_ifs with hxx
  · subst hxx
    simp only [inv_mul_cancel, Circle.coe_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ hcard, one_mul]
  · have hz : ∑ r ∈ p.2, ((((φ (ξ ⬝ᵥ r))⁻¹ * φ (ξ' ⬝ᵥ r) : Circle)) : ℂ) = 0 := by
      obtain ⟨h1, -, -, h4, h5, h6⟩ := hp ξ hξ
      obtain ⟨-, -, -, h4', -, -⟩ := hp ξ' hξ'
      by_contra hne
      apply hxx
      apply hs ξ hξ ξ' hξ'
      show ∀ a ∈ A, φ ((ξ - ξ') ⬝ᵥ a) = 1
      intro a ha
      by_contra hna
      apply hne
      refine sum_circ_eq_zero A p.1 h1 p.2 h5 h6 (fun r => (φ (ξ ⬝ᵥ r))⁻¹ * φ (ξ' ⬝ᵥ r))
        (fun x y => circ_char φ φ ξ ξ' x y) (fun h hh => by simp [h4 h hh, h4' h hh]) a ha ?_
      intro hχ
      apply hna
      have e : φ (ξ ⬝ᵥ a) = φ (ξ' ⬝ᵥ a) := inv_mul_eq_one.mp hχ
      rw [sub_dotProduct, AddChar.map_sub_eq_div, e, div_self']
    rw [hz, mul_zero, zero_mul]

end PositivityTheory.RgUd.Form.U.Lift2.AvA
end
end

noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.BZMir
open scoped Topology

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

theorem lat_gmap (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) : Lat (gmap g A) :=
  AvA.lat_gmap' g A hA

theorem av_conj (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (gl : GL (Fin n) k →* (V →ₗ[ℂ] V))
    (hconj : ∀ g x v, gl g (col x v) = col ((g : Matrix (Fin n) (Fin n) k) *ᵥ x) (gl g v))
    (g : GL (Fin n) k) (A : AddSubgroup (Fin n → k)) (hA : Lat A) (ξ : Fin n → k) (v : V) :
    gl g (av φ col ξ A v) = av φ col (ξ ᵥ* ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (gmap g A) (gl g v) :=
  AvA.av_conj' φ hφ col hc0 hca hsm gl hconj g A hA ξ v

theorem av_bessel (φ : AddChar k Circle) (hφ : Continuous φ) (col : (Fin n → k) → V →ₗ[ℂ] V)
    (hc0 : ∀ v, col 0 v = v) (hca : ∀ x y v, col (x + y) v = col x (col y v)) (hsm : ∀ v, IsOpen {x | col x v = v})
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
    (A : AddSubgroup (Fin n → k)) (hA : Lat A) (s : Finset (Fin n → k))
    (hs : ∀ ξ ∈ s, ∀ ξ' ∈ s, ξ - ξ' ∈ perp φ A → ξ = ξ') (v : V) :
    ∑ ξ ∈ s, (B (av φ col ξ A v) v).re ≤ (B v v).re :=
  AvA.av_bessel' φ hφ col hc0 hca hsm B hB hBc A hA s hs v

end PositivityTheory.RgUd.Form.U.Lift2
