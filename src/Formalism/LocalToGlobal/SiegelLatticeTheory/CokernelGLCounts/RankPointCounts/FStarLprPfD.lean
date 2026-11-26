module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLocInB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfH

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfC
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfB
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfA
noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.LprU

open Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

def GramInvE {ι : Type} [Fintype ι] [DecidableEq ι] (H : HermSp M V) (v : ι → V) : Prop :=
  ∃ N : Matrix ι ι E, N * H.gram v = 1

theorem eqz {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInvE H v) {z : V}
    (hz : z ∈ Submodule.span E (Set.range v)) (h0 : ∀ i, H.h z (v i) = 0) : z = 0 := by
  obtain ⟨N, hN⟩ := hN
  have hz0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V),
      H.h (∑ a ∈ s, c a • v a) y = ∑ a ∈ s, c a * H.h (v a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [hz0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hz
  have hg : H.gram v *ᵥ c = 0 := by
    funext i
    rw [Pi.zero_apply, ← h0 i, hsum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc : c = 0 := by
    have h2 := congrArg (fun u => N *ᵥ u) hg
    simp only [Matrix.mulVec_mulVec, hN, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2
  simp [hc]

theorem decompE {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInvE H v) (x : V) :
    ∃ c : ι → E, ∀ i, H.h (x - ∑ j, c j • v j) (v i) = 0 := by
  obtain ⟨N, hN⟩ := hN
  have hN' : H.gram v * N = 1 := mul_eq_one_comm.mp hN
  have h0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V),
      H.h (∑ a ∈ s, c a • v a) y = ∑ a ∈ s, c a * H.h (v a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  let w : ι → E := fun i => H.h x (v i)
  refine ⟨N *ᵥ w, fun i => ?_⟩
  have hsub : ∀ y z : V, H.h (y - z) (v i) = H.h y (v i) - H.h z (v i) := fun y z => by
    rw [sub_eq_add_neg, H.h_add_left, ← neg_one_smul E z, H.h_smul_left]
    ring
  rw [hsub, hsum]
  have e : ∑ j, (N *ᵥ w) j * H.h (v j) (v i) = (H.gram v *ᵥ (N *ᵥ w)) i :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e, Matrix.mulVec_mulVec, hN', Matrix.one_mulVec, sub_self]

theorem y_eq_om {r : ℕ} (f f' : Fin (r + 1) → V) (α : Fin (r + 1) → E)
    (hy : ∀ b, b ≠ Fin.last r → H.h (∑ a, α a • f a) (f' b) = 0) :
    M.L.cj (H.Zhat f f').det • ∑ a, α a • f a = H.h (∑ a, α a • f a) (f' (Fin.last r)) • H.om f f' := by
  have h0 : ∀ y, H.h 0 y = 0 := fun y => by
    have h1 := H.h_add_left 0 0 y
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hsum : ∀ (s : Finset (Fin (r + 1))) (c : (Fin (r + 1)) → E) (y : V),
      H.h (∑ a ∈ s, c a • f a) y = ∑ a ∈ s, c a * H.h (f a) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
  set Z := H.Zhat f f' with hZ
  set W := Z.map M.L.cj with hW
  set β : Fin (r + 1) → E := fun b => H.h (∑ a, α a • f a) (f' b) with hβdef

  have hβ : β = Wᵀ *ᵥ α := by
    funext b
    simp only [hβdef]
    rw [hsum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [H.h_herm (f' b) (f a)]
      exact mul_comm _ _

  have hcr : W.det • α = W.adjugateᵀ *ᵥ β := by
    rw [hβ, Matrix.mulVec_mulVec, Matrix.adjugate_transpose, Matrix.adjugate_mul, Matrix.det_transpose]
    first
      | rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
      | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      | (ext a; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])
  have hdet : W.det = M.L.cj Z.det := by
    first
      | exact (RingHom.map_det M.L.cj Z).symm
      | exact (RingHom.map_det (M.L.cj : E →+* E) Z).symm
  have hadj : W.adjugate = Z.adjugate.map M.L.cj := by
    first
      | (have h := RingHom.map_adjugate (M.L.cj : E →+* E) Z
         simp only [RingHom.mapMatrix_apply, RingHom.coe_coe] at h
         exact h.symm)
  have hcomp : ∀ a, M.L.cj Z.det * α a = β (Fin.last r) * M.L.cj (Z.adjugate (Fin.last r) a) := by
    intro a
    have h1 := congrFun hcr a
    rw [Pi.smul_apply, smul_eq_mul, hdet] at h1
    rw [h1, Matrix.mulVec, dotProduct, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.transpose_apply, hadj, Matrix.map_apply]
      ring
    · intro b _ hb
      have hb0 : β b = 0 := hy b hb
      rw [hb0, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold Formalism.MainNotions.S.Loc.HermSp.om
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, smul_smul, hcomp a]

end Formalism.MainNotions.S.Loc.HermSp.LprU
end
end

noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.LprU

open Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem dl_full {r : ℕ} (f f' : Fin (r + 1) → V) : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dite_eq_left le_rfl]
  simp [Fin.castLE_rfl]

def Iso' {r : ℕ} (H : HermSp M V) (f' : Fin (r + 1) → V) : Prop :=
  ∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f' a) (f' b) = 0

theorem mem_perp_X {r : ℕ} (f' : Fin (r + 1) → V) {x : V} (hx : ∀ i : Fin r, H.h x (f' i.castSucc) = 0) :
    x ∈ H.perp (H.X f') := fun y hy => h_right_zero hx hy

theorem X_le_perp {r : ℕ} {f' : Fin (r + 1) → V} (hK : Iso' H f') : H.X f' ≤ H.perp (H.X f') := by
  unfold HermSp.X
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact mem_perp_X f' (fun i => hK _ _ (Or.inl (Fin.castSucc_lt_last a).ne))

theorem z_mem_perp {r : ℕ} {f' : Fin (r + 1) → V} (hK : Iso' H f') : f' (Fin.last r) ∈ H.perp (H.X f') := mem_perp_X f' (fun i => hK _ _ (Or.inr (Fin.castSucc_lt_last i).ne))

theorem om_mem_perp {r : ℕ} (f f' : Fin (r + 1) → V) : H.om f f' ∈ H.perp (H.X f') := by
  apply mem_perp_X
  intro i
  unfold HermSp.om
  rw [Formalism.L2.SG.CntLocal.h_sum_left]
  have e : ∀ a, H.h (M.L.cj ((H.Zhat f f').adjugate (Fin.last r) a) • f a) (f' i.castSucc) =
      M.L.cj ((H.Zhat f f').adjugate (Fin.last r) a * (H.Zhat f f') a i.castSucc) := by
    intro a
    rw [H.h_smul_left, H.h_herm (f' i.castSucc) (f a), map_mul]
    rfl
  simp only [e]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  have h2 : ∑ a, (H.Zhat f f').adjugate (Fin.last r) a * (H.Zhat f f') a i.castSucc =
      ((H.Zhat f f').adjugate * H.Zhat f f') (Fin.last r) i.castSucc := (Matrix.mul_apply ..).symm
  rw [h2, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne',
    smul_zero, map_zero]

theorem w_zero_le_perp_first {r : ℕ} (f f' : Fin (r + 1) → V) : H.W0 f f' ≤ H.perp (H.X f) := by
  intro v hv x hx
  exact hv x (Submodule.mem_sup_left (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, rfl⟩) hx))

theorem w_zero_le_perp_second {r : ℕ} (f f' : Fin (r + 1) → V) : H.W0 f f' ≤ H.perp (H.X f') := by
  intro v hv x hx
  exact hv x (Submodule.mem_sup_right (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, rfl⟩) hx))

theorem Xp_le_span {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Xp f ⊔ H.Xp f' ≤ Submodule.span E (Set.range (Sum.elim f f')) := by
  apply sup_le
  · apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨Sum.inl a, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    exact ⟨Sum.inr a, rfl⟩

theorem X_le_span {r : ℕ} (f f' : Fin (r + 1) → V) : H.X f ≤ Submodule.span E (Set.range (Sum.elim f f')) := by
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact ⟨Sum.inl a.castSucc, rfl⟩

theorem decomp_perp {r : ℕ} (t : Term V M r) (hN : GramInvE H (Sum.elim t.f t.f'))
    (hD : IsUnit (H.Zhat t.f t.f').det) (hK : Iso' H t.f') {x : V} (hx : x ∈ H.perp (H.X t.f')) :
    ∃ (w : V) (μ c : E) (xX : V), w ∈ H.W0 t.f t.f' ∧ xX ∈ H.X t.f' ∧
      x = w + μ • H.om t.f t.f' + xX + c • t.f' (Fin.last r) := by
  obtain ⟨c, hc⟩ := decompE hN x
  set w := x - ∑ k, c k • Sum.elim t.f t.f' k with hwdef
  have hwW : w ∈ H.W0 t.f t.f' := fun y hy => h_right_zero hc (Xp_le_span t.f t.f' hy)
  set y : V := ∑ a, c (Sum.inl a) • t.f a with hy
  set xX : V := ∑ i : Fin r, c (Sum.inr i.castSucc) • t.f' i.castSucc with hxX
  have hxXm : xX ∈ H.X t.f' :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsplit : ∑ k, c k • Sum.elim t.f t.f' k = y + xX + c (Sum.inr (Fin.last r)) • t.f' (Fin.last r) := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Fin.sum_univ_castSucc (fun b => c (Sum.inr b) • t.f' b)]
    abel
  have hx' : x = w + y + xX + c (Sum.inr (Fin.last r)) • t.f' (Fin.last r) := by
    rw [hwdef, hsplit]; abel
  have hyo : ∀ b, b ≠ Fin.last r → H.h y (t.f' b) = 0 := by
    intro b hb
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hb
    have hyv : y = x - w - xX - c (Sum.inr (Fin.last r)) • t.f' (Fin.last r) := by rw [hx']; abel
    have e1 : H.h x (t.f' i.castSucc) = 0 := hx _ (Submodule.subset_span ⟨i, rfl⟩)
    have e2 : H.h w (t.f' i.castSucc) = 0 := hc (Sum.inr i.castSucc)
    have e3 : H.h xX (t.f' i.castSucc) = 0 := X_le_perp hK hxXm _ (Submodule.subset_span ⟨i, rfl⟩)
    have e4 : H.h (t.f' (Fin.last r)) (t.f' i.castSucc) = 0 := hK _ _ (Or.inr (Fin.castSucc_ne_last i))
    rw [hyv, ← hL_apply]
    simp only [map_sub, map_smul, hL_apply, e1, e2, e3, e4, smul_zero, sub_zero]
  have hyom := y_eq_om t.f t.f' (fun a => c (Sum.inl a)) hyo
  have hu : IsUnit (M.L.cj (H.Zhat t.f t.f').det) := hD.map M.L.cj
  refine ⟨w, ((hu.unit⁻¹ : Eˣ) : E) * H.h y (t.f' (Fin.last r)), c (Sum.inr (Fin.last r)), xX, hwW, hxXm, ?_⟩
  have hy2 : y = (((hu.unit⁻¹ : Eˣ) : E) * H.h y (t.f' (Fin.last r))) • H.om t.f t.f' := by
    rw [mul_smul, ← hyom, smul_smul, hu.val_inv_mul, one_smul]
  rw [hx', ← hy2]

theorem psi_unique {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (ψ ψ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (hN1 : GramInvE H (Sum.elim t₁.f t₁.f')) (hN2 : GramInvE H (Sum.elim t₂.f t₂.f'))
    (hD1 : IsUnit (H.Zhat t₁.f t₁.f').det) (hD2 : IsUnit (H.Zhat t₂.f t₂.f').det)
    (hK1 : Iso' H t₁.f') (hK2 : Iso' H t₂.f')
    (hI : H.Ident t₁ t₂ φ ψ) (hI' : H.Ident t₁ t₂ φ ψ')
    (hz : H.SendsTo ψ.toLinearMap 1 1 (t₁.f' (Fin.last r)) (t₂.f' (Fin.last r)))
    (hz' : H.SendsTo ψ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (t₂.f' (Fin.last r))) : ψ = ψ' := by

  have gW : ∀ (w : V) (hw : w ∈ H.W0 t₁.f t₁.f'),
      ψ (H.mkW t₁.f' ⟨w, w_zero_le_perp_second _ _ hw⟩) = ψ' (H.mkW t₁.f' ⟨w, w_zero_le_perp_second _ _ hw⟩) := by
    intro w hw
    obtain ⟨w₂, hw₂, hφ1, hψ1⟩ := hI.2.2.1 w hw
    obtain ⟨w₂', hw₂', hφ2, hψ2⟩ := hI'.2.2.1 w hw
    have e1 := hφ1 ⟨w, w_zero_le_perp_first _ _ hw⟩ ⟨w₂, w_zero_le_perp_first _ _ hw₂⟩ rfl rfl
    have e2 := hφ2 ⟨w, w_zero_le_perp_first _ _ hw⟩ ⟨w₂', w_zero_le_perp_first _ _ hw₂'⟩ rfl rfl
    rw [one_smul, one_smul] at e1 e2
    have e12 : H.mkW t₂.f ⟨w₂, w_zero_le_perp_first _ _ hw₂⟩ = H.mkW t₂.f ⟨w₂', w_zero_le_perp_first _ _ hw₂'⟩ := by
      rw [← e1, ← e2]
    have hsub : w₂ - w₂' ∈ H.X t₂.f := by
      have h := (Submodule.Quotient.eq _).1 e12
      simpa using h
    have hz0 : w₂ - w₂' = 0 := by
      refine eqz hN2 (X_le_span _ _ hsub) fun k => ?_
      have hk : Sum.elim t₂.f t₂.f' k ∈ H.Xp t₂.f ⊔ H.Xp t₂.f' := by
        cases k with
        | inl a => exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
        | inr b => exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, rfl⟩)
      exact (H.W0 t₂.f t₂.f').sub_mem hw₂ hw₂' _ hk
    have hww : w₂ = w₂' := sub_eq_zero.1 hz0
    have f1 := hψ1 ⟨w, w_zero_le_perp_second _ _ hw⟩ ⟨w₂, w_zero_le_perp_second _ _ hw₂⟩ rfl rfl
    have f2 := hψ2 ⟨w, w_zero_le_perp_second _ _ hw⟩ ⟨w₂', w_zero_le_perp_second _ _ hw₂'⟩ rfl rfl
    rw [one_smul, one_smul] at f1 f2
    subst hww
    exact f1.trans f2.symm

  have gom : ψ (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) = ψ' (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := by
    have e1 := hI.2.2.2.2.1 ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩ ⟨H.om t₂.f t₂.f', om_mem_perp _ _⟩ rfl rfl
    have e2 := hI'.2.2.2.2.1 ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩ ⟨H.om t₂.f t₂.f', om_mem_perp _ _⟩ rfl rfl
    have hu : IsUnit (M.L.cj (H.Dl t₂.f t₂.f' (r + 1))) := by rw [dl_full]; exact hD2.map M.L.cj
    have e3 : M.L.cj (H.Dl t₂.f t₂.f' (r + 1)) • ψ (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) =
        M.L.cj (H.Dl t₂.f t₂.f' (r + 1)) • ψ' (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := by
      have a1 : ψ.toLinearMap (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) =
          ψ (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := rfl
      have a2 : ψ'.toLinearMap (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) =
          ψ' (H.mkW t₁.f' ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩) := rfl
      rw [← a1, ← a2, e1, e2]
    have e4 := congrArg (fun q => ((hu.unit⁻¹ : Eˣ) : E) • q) e3
    simp only [smul_smul] at e4
    rwa [hu.val_inv_mul, one_smul, one_smul] at e4

  have gz : ψ (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩) =
      ψ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩) := by
    have e1 := hz ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩ ⟨t₂.f' (Fin.last r), z_mem_perp hK2⟩ rfl rfl
    have e2 := hz' ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩ ⟨t₂.f' (Fin.last r), z_mem_perp hK2⟩ rfl rfl
    rw [one_smul, one_smul] at e1 e2
    exact e1.trans e2.symm
  apply LinearEquiv.ext
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨w, μ, c, xX, hw, hxX, hdec⟩ := decomp_perp t₁ hN1 hD1 hK1 hx
  have hq : (⟨x, hx⟩ : H.perp (H.X t₁.f')) = ⟨w, w_zero_le_perp_second _ _ hw⟩ + μ • ⟨H.om t₁.f t₁.f', om_mem_perp _ _⟩ +
      ⟨xX, X_le_perp hK1 hxX⟩ + c • ⟨t₁.f' (Fin.last r), z_mem_perp hK1⟩ := Subtype.ext hdec
  have h0 : H.mkW t₁.f' ⟨xX, X_le_perp hK1 hxX⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hxX
  show ψ (H.mkW t₁.f' ⟨x, hx⟩) = ψ' (H.mkW t₁.f' ⟨x, hx⟩)
  rw [hq, map_add (f := _), map_add (f := _), map_add (f := _), map_smul, map_smul, h0, add_zero]
  simp only [map_add (f := _), map_smul]
  rw [gW w hw, gom, gz]

end Formalism.MainNotions.S.Loc.HermSp.LprU
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.S.Loc.HermSp.LprU

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def LprExist : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ p : PlF D,
      ∃ ψ₀ : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'),
        (locH Zd p).Ident (tLoc Zd p γ) ⟨⊥, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩
          (LinearEquiv.refl _ _) ψ₀ ∧
        (locH Zd p).SendsTo ψ₀.toLinearMap 1 1 ((tLoc Zd p γ).f' (Fin.last _)) (locF' Zd p F' (Fin.last _)) ∧
        ψ₀ '' (locH Zd p).Lset (tLoc Zd p γ).abelian₂ (tLoc Zd p γ).f' =
          (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F') ∧
        ∀ g, (Zd.M p).split = some g →
          Prod.map ψ₀ (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
            (locH Zd p).iotaGraph g (tLoc Zd p γ) =
            (locH Zd p).iotaGraph g
              ⟨lattice₂ D Zd.M p γ.lam, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩

def LprNondeg : Prop :=
  IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ F', IsPartner γ Z F' → ∀ p : PlF D,
      GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (tLoc Zd p γ).f') ∧
      GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (locF' Zd p F')) ∧
      IsUnit ((locH Zd p).Zhat (tLoc Zd p γ).f (tLoc Zd p γ).f').det ∧
      IsUnit ((locH Zd p).Zhat (tLoc Zd p γ).f (locF' Zd p F')).det ∧
      Iso' (locH Zd p) (tLoc Zd p γ).f' ∧ Iso' (locH Zd p) (locF' Zd p F')

variable {u u' F0 what₂}


set_option maxHeartbeats 800000 in
theorem lprPart_of (hE : LprExist Zd u u' F0 what₂) (hN : LprNondeg Zd u u' F0 what₂) : LprPart Zd u u' F0 what₂ := by
  intro hrows γ Z hC F' hP p ψ hI hz
  obtain ⟨ψ₀, hI₀, hz₀, hL, hι⟩ := hE hrows γ Z hC F' hP p
  obtain ⟨n1, n2, d1, d2, k1, k2⟩ := hN hrows γ Z hC F' hP p
  have h : ψ = ψ₀ := psi_unique (H := locH Zd p) (tLoc Zd p γ)
    ⟨⊥, (tLoc Zd p γ).f, locF' Zd p F', (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩ (LinearEquiv.refl _ _) ψ ψ₀
    n1 n2 d1 d2 k1 k2 hI hI₀ hz hz₀
  rw [h]
  exact ⟨hL, hι⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.S.Loc.HermSp.LprU

namespace LprND

variable {D : Formalism.BasicNotions.D7}

def gramW {ι : Type} (w : ι → (VS D).V) : Matrix ι ι D.host.E := Matrix.of fun i j => brS (VS D) (w j) (w i)

theorem gramW_det_ne {r : ℕ} {U : Submodule D.host.E (VS D).V} (hdim : Module.finrank D.host.E U = 2 * r + 2)
    (hnd : U ⊓ orth (VS D) U = ⊥) (w : Fin (r + 1) ⊕ Fin (r + 1) → (VS D).V)
    (hw : Submodule.span D.host.E (Set.range w) = U) : (gramW w).det ≠ 0 := by
  have hli : LinearIndependent D.host.E w := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show _ = Module.finrank D.host.E (Submodule.span D.host.E (Set.range w))
    rw [hw, hdim, Fintype.card_sum, Fintype.card_fin]
    ring
  intro h0
  obtain ⟨c, hc0, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set x := ∑ k, c k • w k with hx
  have hx2 : ∀ i, (VS D).hT (w i) x = 0 := by
    intro i
    have h := congrFun hMc i
    simp only [Matrix.mulVec, dotProduct, gramW, Matrix.of_apply, brS, Pi.zero_apply] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hx1 : x ∈ U := by
    rw [← hw, hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hx3 : x ∈ orth (VS D) U := by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro y hy
    rw [← hw] at hy
    have hk : Submodule.span D.host.E (Set.range w) ≤ LinearMap.ker ((VS D).hT.flip x) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show (VS D).hT.flip x (w i) = 0
      rw [LinearMap.flip_apply]
      exact hx2 i
    have h := hk hy
    rw [LinearMap.mem_ker, LinearMap.flip_apply] at h
    exact h
  have hx0 : x = 0 := by
    have h : x ∈ U ⊓ orth (VS D) U := ⟨hx1, hx3⟩
    rw [hnd] at h
    exact (Submodule.mem_bot _).1 h
  apply hc0
  funext k
  exact Fintype.linearIndependent_iff.1 hli c (hx ▸ hx0) k

theorem gram_pair_ne {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F'' : LFlag (D.sp.Y 0) D.R.rS T') (hG : Gflag F.fl F''.fl ≠ 0)
    (w : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V)
    (hw : Submodule.span D.host.E (Set.range w) =
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F''.fl.fvec))) : (gramW w).det ≠ 0 := by
  set v := Sum.elim F.fl.fvec F''.fl.fvec with hv
  set Λ' : Submodule (𝓞 D.host.E) (VS D).V := Λ ⊔ Submodule.span (𝓞 D.host.E) (Set.range v) with hΛ'
  have hmem : ∀ k, v k ∈ Λ' := fun k => Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩)
  let F1 : LFlag (D.sp.Y 0) D.R.rS T := ⟨F.fl, F.fl.z⟩
  let F2 : LFlag (D.sp.Y 0) D.R.rS T' := ⟨F''.fl, F''.fl.z⟩
  have hX1 : Xsp F1 ≤ spanE (VS D) (XLam Λ' F1) := by
    show Submodule.span D.host.E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span ⟨?_, Submodule.subset_span ⟨a, rfl⟩⟩
    have h := hmem (Sum.inl a.castSucc)
    simpa [hv, PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc] using h
  have hX2 : Xsp F2 ≤ spanE (VS D) (XLam Λ' F2) := by
    show Submodule.span D.host.E (Set.range F''.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span ⟨?_, Submodule.subset_span ⟨a, rfl⟩⟩
    have h := hmem (Sum.inr a.castSucc)
    simpa [hv, PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc] using h
  have hU : UUE Λ' F1 F2 = Submodule.span D.host.E (Set.range v) :=
    PI.ScalarPairDr.W.UUE_eq Λ' F1 F2 rfl rfl hX1 hX2
  have n := PI.UnitaryGroupMassFormula.BetaLUniq.gram_matrix_nondegenerate_of_span_eq Λ' F1 F2 hU hG
  exact gramW_det_ne n.1 n.2 w (hw.trans hU.symm)

theorem span_frameAct {r : ℕ} (u v : Fin (r + 1) → (VS D).V) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    Submodule.span D.host.E (Set.range (Sum.elim u (frameAct v ξ⁻¹))) =
      Submodule.span D.host.E (Set.range (Sum.elim u v)) := by
  have hdet : IsUnit ξ.det := by
    have hbt : ξ.BlockTriangular id := fun i j hij => h1 i j hij
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [h2]
  have hinv : ξ⁻¹ * ξ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hv : v = frameAct (frameAct v ξ⁻¹) ξ := by
    funext b
    simp only [frameAct, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have e : ∀ a, ∑ c, ((ξ⁻¹ a c : 𝓞 D.host.E) : D.host.E) * ((ξ c b : 𝓞 D.host.E) : D.host.E) =
        (((ξ⁻¹ * ξ) a b : 𝓞 D.host.E) : D.host.E) := by
      intro a; rw [Matrix.mul_apply]; push_cast; rfl
    simp_rw [← Finset.sum_smul]
    have e2 : ∀ a, (∑ c, ((ξ c b : 𝓞 D.host.E) : D.host.E) * ((ξ⁻¹ a c : 𝓞 D.host.E) : D.host.E)) =
        (((ξ⁻¹ * ξ) a b : 𝓞 D.host.E) : D.host.E) := by
      intro a; rw [← e a]; exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    simp only [e2, hinv, Matrix.one_apply]
    simp
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    cases k with
    | inl a => exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    | inr b =>
      show frameAct v ξ⁻¹ b ∈ _
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    cases k with
    | inl a => exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    | inr b =>
      show v b ∈ _
      have hb : v b = frameAct (frameAct v ξ⁻¹) ξ b := congrFun hv b
      rw [hb]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr a, rfl⟩)

variable (Zd : LocDat D) (p : PlF D)

theorem gram_loc {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → (VS D).V) (s : ι → (D.s.atP p).Ep) :
    (locH Zd p).gram (fun k => s k • baseChange₂ D p (w k)) =
      Matrix.diagonal (fun k => (Zd.M p).L.cj (s k)) * (gramW w).map (D.s.atP p).ιE * Matrix.diagonal s := by
  ext i j
  simp only [Formalism.MainNotions.S.Loc.HermSp.gram, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply,
    gramW]
  rw [Formalism.L2.SG.Pf.ScalarFramePf.h_bcP]
  ring

theorem gramInvE_loc {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → (VS D).V) (s : ι → (D.s.atP p).Ep)
    (hs : ∀ k, IsUnit (s k)) (hdet : (gramW w).det ≠ 0) :
    GramInvE (locH Zd p) (fun k => s k • baseChange₂ D p (w k)) := by
  set M := gramW w with hMdef
  set ι' := (D.s.atP p).ιE with hι
  set si : ι → (D.s.atP p).Ep := fun k => (((hs k).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) with hsi
  refine ⟨Matrix.diagonal si * M⁻¹.map ι' * Matrix.diagonal (fun k => (Zd.M p).L.cj (si k)), ?_⟩
  rw [gram_loc]
  have hM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
  have hmap : M⁻¹.map ι' * M.map ι' = 1 := by
    rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero ι') (map_one ι')]
  have hs1 : (fun k => si k * s k) = fun _ => 1 := funext fun k => (hs k).val_inv_mul
  have hc1 : (fun k => (Zd.M p).L.cj (si k) * (Zd.M p).L.cj (s k)) = fun _ => 1 := by
    funext k; rw [← map_mul, (hs k).val_inv_mul, map_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal fun k => (Zd.M p).L.cj (si k)), Matrix.diagonal_mul_diagonal, hc1,
    Matrix.diagonal_one, Matrix.one_mul, ← Matrix.mul_assoc (M⁻¹.map ι'), hmap, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal, hs1, Matrix.diagonal_one]

end LprND

open LprND

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem genLoc_rows (hrows : IsRowReps D F0 what₂) (γ : TermDef.Term D u u' F0 what₂)
    (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w) (p : PlF D) : (locH Zd p).IsGeneric (tLoc Zd p γ) := by
  have hR : IsRowLat D F0 γ.lam := hrows.1 γ.lam γ.mem
  obtain ⟨hgen, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  obtain ⟨F', ⟨h1, h1e⟩, hF'⟩ := hgen
  have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
    (h1e.trans h2e.symm)
  have hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ) := by
    obtain ⟨-, ⟨-, -, hFl, hFc⟩, -⟩ := hR
    exact (PI.TermAttrConst.UnitaryGroupMassFormula.genFun_gen γ.lam (lf D F0) _ (gS D)
      hFl hFc (fun x hx => ⟨hx.1, hx.2.1, hx.2.2.1⟩) ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  have hGv : Gval (lf D F0) (repF γ) ≠ 0 := by
    have heq := Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2
    change Gval (lf D F0) (repF γ) = Gval (lf D F0) (Quot.out γ.cls).val at heq
    rw [heq]; exact hG
  exact (Formalism.L2.SG.Pf.frameGenLoc_holds D Zd F0 γ.lam (repF γ) hR h2
    (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) hGv).1 hgenR p

theorem gval_repF (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (hγ : EligAt γ w) :
    Gval (lf D F0) (repF γ) ≠ 0 := by
  obtain ⟨-, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  have heq := Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2
  change Gval (lf D F0) (repF γ) = Gval (lf D F0) (Quot.out γ.cls).val at heq
  rw [heq]; exact hG

theorem iso_locF' (p : PlF D) {T' : D.host.E} (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Iso' (locH Zd p) (locF' Zd p F') := by
  intro a b hab
  show (locH Zd p).h ((TermLoc.sgnP' D p a * frFac Zd.δ p a) • baseChange₂ D p (frame F' a))
    ((TermLoc.sgnP' D p b * frFac Zd.δ p b) • baseChange₂ D p (frame F' b)) = 0
  rw [Formalism.L2.SG.Pf.ScalarFramePf.h_bcP]
  have h0 : brS (VS D) (frame F' a) (frame F' b) = 0 := by
    unfold brS
    rcases hab with ha | hb
    · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 ha
      rw [PI.ScalarPairDr.W.hT_swap]
      have e : (VS D).hT (frame F' i.castSucc) (frame F' b) = 0 := by
        show (VS D).hT (F'.fl.fvec i.castSucc) (F'.fl.fvec b) = 0
        rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc]
        refine Fin.lastCases ?_ (fun j => ?_) b
        · rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_last]; exact F'.fl.z_orth i
        · rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc]; exact F'.fl.e_iso i j
      rw [e, star_zero]
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hb
      show (VS D).hT (F'.fl.fvec j.castSucc) (F'.fl.fvec a) = 0
      rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc]
      refine Fin.lastCases ?_ (fun i => ?_) a
      · rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_last]; exact F'.fl.z_orth j
      · rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc]; exact F'.fl.e_iso j i
  rw [h0, map_zero, mul_zero]

theorem lprNondeg_holds : LprNondeg Zd u u' F0 what₂ := by
  intro hrows γ Z hC F' hP p
  obtain ⟨w, hγ, -, -, -, -⟩ := id hC
  have hgen := genLoc_rows Zd hrows γ w hγ p
  have hZ : ZhatL (lf D F0) F' = Z := hP.1.2.2.2.2
  have hdet : Z.det ≠ 0 := (starMinors_holds u u' F0 what₂ γ Z hC).1
  have hsK : ∀ k, IsUnit (Sum.elim (fun a => sgnP D p a * frFac Zd.δ p a)
      (fun b => sgnP' D p b * frFac Zd.δ p b) k) := by
    intro k
    cases k with
    | inl a => exact Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p a
    | inr b => exact Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p b

  have n1 : GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (tLoc Zd p γ).f') := by
    have e : Sum.elim (tLoc Zd p γ).f (tLoc Zd p γ).f' = fun k => Sum.elim (fun a => sgnP D p a * frFac Zd.δ p a)
        (fun b => sgnP' D p b * frFac Zd.δ p b) k • baseChange₂ D p (Sum.elim (frame (lf D F0)) (starFrame γ) k) := by
      funext k; cases k <;> rfl
    rw [e]
    refine gramInvE_loc Zd p _ _ hsK (gram_pair_ne γ.lam (lf D F0) (repF γ) (gval_repF γ w hγ) _ ?_)
    have hu := admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)
    exact span_frameAct _ _ _ hu.1 hu.2
  have n2 : GramInvE (locH Zd p) (Sum.elim (tLoc Zd p γ).f (locF' Zd p F')) := by
    have e : Sum.elim (tLoc Zd p γ).f (locF' Zd p F') = fun k => Sum.elim (fun a => sgnP D p a * frFac Zd.δ p a)
        (fun b => sgnP' D p b * frFac Zd.δ p b) k • baseChange₂ D p (Sum.elim (frame (lf D F0)) (frame F') k) := by
      funext k; cases k <;> rfl
    rw [e]
    exact gramInvE_loc Zd p _ _ hsK (gram_pair_ne γ.lam (lf D F0) F' hP.1.1.2.2 _ rfl)
  refine ⟨n1, n2, ?_, ?_, hgen.1.2.2.1.2.1, iso_locF' Zd p F'⟩
  · rw [← dl_full]; exact hgen.1.2.2.2.1
  · rw [← dl_full]; exact local_discriminant_unit_of_det Zd p γ Z F' hZ hdet

theorem lprPart_of' (hE : LprExist Zd u u' F0 what₂) : LprPart Zd u u' F0 what₂ :=
  lprPart_of Zd hE (lprNondeg_holds Zd)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
