module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PKey

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.TkFcPzTop
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.EvFinsetSum
noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

theorem ev_finset_sum {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (F : (Fin (m + 1) → Y) → ℝ) (y : Y) {ι : Type} (s : Finset ι) (z : ι → Chn G m) :
    ev ρ F y (∑ i ∈ s, z i) = ∑ i ∈ s, ev ρ F y (z i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ev_eq, map_sum]

theorem inv_dC {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (E : (Fin (m + 1) → Y) → ℝ) (hE : Inv ρ E) : Inv ρ (dC E) := by
  intro g y
  simp only [dC]
  exact Finset.sum_congr rfl fun i _ => by rw [hE g (fun j => y (i.succAbove j))]

theorem pEvDC : PEvDC := by
  intro G H Y _ _ _ ρ m E hE y z
  refine Finsupp.induction_linear z ?_ ?_ ?_
  · simp [ev_zero]
  · intro a b ha hb
    rw [ev_add, map_add (f := _), ev_add, ha, hb]
  · intro g a
    have hbd : bd G m (Finsupp.single g a) = a • bd G m (Finsupp.single g 1) := by
      rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hbd, ev_smul, ev_single]
    congr 1
    simp only [bd, Finsupp.linearCombination_single, one_smul]
    rw [ev_add, ev_single, one_mul, ev_finset_sum]
    simp only [ev_smul, ev_single, one_mul]
    simp only [dC]
    rw [Fin.sum_univ_succ]
    congr 1
    · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      have : (fun j : Fin (m + 1) => ρ (Fin.partialProd g j.succ) • y) =
          fun j => ρ (g 0) • (ρ (Fin.partialProd (fun i : Fin m => g i.succ) j) • y) := by
        funext j
        rw [Fin.partialProd_succ', map_mul, mul_smul]
        rfl
      rw [this, hE (g 0)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.partialProd_contractNth]
      simp [Fin.val_succ]

theorem pCob : PCob := by
  intro G _ m F hF hz
  let φ : Chn G (m + 1) →ₗ[ℝ] ℝ :=
    Finsupp.linearCombination ℝ (fun g : Fin (m + 1) → G => F fun j => Fin.partialProd g j)
  have hφ : ∀ z, φ z = ev (MonoidHom.id G) F 1 z := fun z => by
    rw [ev_eq]; simp [φ]
  have hker : LinearMap.ker (bd G m) ≤ LinearMap.ker φ := fun z hz' => by
    rw [LinearMap.mem_ker] at hz' ⊢; rw [hφ]; exact hz z hz'
  let ψ₀ : LinearMap.range (bd G m) →ₗ[ℝ] ℝ :=
    (LinearMap.ker (bd G m)).liftQ φ hker ∘ₗ (bd G m).quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend ψ₀
  have hψbd : ∀ z, ψ (bd G m z) = φ z := fun z => by
    have h1 := LinearMap.congr_fun hψ ⟨bd G m z, LinearMap.mem_range_self _ z⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    simp [ψ₀, LinearMap.quotKerEquivRange_symm_apply_image]
  let E : (Fin (m + 1) → G) → ℝ := fun y =>
    ψ (Finsupp.single (fun j : Fin m => (y j.castSucc)⁻¹ * y j.succ) 1)
  have hEinv : Inv (MonoidHom.id G) E := by
    intro g y
    simp only [E, MonoidHom.id_apply, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hevE : ∀ w : Chn G m, ev (MonoidHom.id G) E 1 w = ψ w := by
    intro w
    refine Finsupp.induction_linear w ?_ ?_ ?_
    · simp [ev_zero]
    · intro a b ha hb; rw [ev_add, ha, hb, map_add (f := _)]
    · intro g a
      rw [ev_single]
      simp only [E, MonoidHom.id_apply, smul_eq_mul, mul_one, Fin.partialProd_right_inv]
      rw [← smul_eq_mul, ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine ⟨E, hEinv, ?_⟩
  funext y
  set g' : Fin (m + 1) → G := fun i => (y i.castSucc)⁻¹ * y i.succ
  have hy : y = fun j => y 0 * Fin.partialProd g' j := by
    have := Fin.partialProd_left_inv y
    funext j
    exact (congrFun this j).symm
  have h1 : dC E y = dC E (fun j => Fin.partialProd g' j) := by
    conv_lhs => rw [hy]
    exact inv_dC (MonoidHom.id G) E hEinv (y 0) _
  have h2 : F y = F (fun j => Fin.partialProd g' j) := by
    conv_lhs => rw [hy]
    exact hF (y 0) _
  rw [h1, h2]
  have h3 := pEvDC G G G (MonoidHom.id G) m E hEinv 1 (Finsupp.single g' 1)
  rw [ev_single, hevE, hψbd, hφ, ev_single] at h3
  simpa using h3

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section Seq

variable {Y : Type}

def tk (n : ℕ) (f : ℕ → Y) : Fin n → Y := fun j => f j

def fc (l : ℕ) (f : ℕ → Y) : ℕ → Y := fun j => if j < l then f j else f (j + 1)

def pz (v : Y → Y) (i : ℕ) (f : ℕ → Y) : ℕ → Y := fun j => if j ≤ i then f j else v (f (j - 1))

def ext {m : ℕ} (y : Fin (m + 1) → Y) : ℕ → Y := fun j => y ⟨min j m, by omega⟩

theorem tk_ext {m : ℕ} (y : Fin (m + 1) → Y) : tk (m + 1) (ext y) = y := by
  funext j
  simp only [tk, ext]
  congr 1
  ext
  simp only
  omega

theorem dC_tk {n : ℕ} (F : (Fin (n + 1) → Y) → ℝ) (f : ℕ → Y) :
    dC F (tk (n + 2) f) = ∑ l ∈ Finset.range (n + 2), (-1 : ℝ) ^ l * F (tk (n + 1) (fc l f)) := by
  rw [Finset.sum_range]
  unfold dC
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j
  simp only [tk, fc]
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    try rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]
    try rfl

variable (v : Y → Y) (f : ℕ → Y)

theorem fc_pz_lt {l i : ℕ} (h : l < i) : fc l (pz v i f) = pz v (i - 1) (fc l f) := by
  funext j
  simp only [fc, pz]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | (congr 2; omega)

theorem fc_pz_gt {l i : ℕ} (h : i + 1 < l) : fc l (pz v i f) = pz v i (fc (l - 1) f) := by
  funext j
  simp only [fc, pz]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | (congr 2; omega)

theorem fc_pz_diag (i : ℕ) : fc (i + 1) (pz v i f) = fc (i + 1) (pz v (i + 1) f) := by
  funext j
  simp only [fc, pz]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | (congr 2; omega)

theorem fc_pz_zero : fc 0 (pz v 0 f) = fun j => v (f j) := by
  funext j
  simp only [fc, pz]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | (congr 2; omega)

theorem tk_fc_pz_top (m : ℕ) : tk (m + 2) (fc (m + 2) (pz v (m + 2) f)) = tk (m + 2) f := by
  funext j
  simp only [tk, fc, pz]
  have := j.isLt
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | (congr 2; omega)

theorem tk_pz_ext (m : ℕ) {i : ℕ} (hi : i ≤ m) (g : ℕ → Y) :
    tk (m + 2) (pz v i (ext (tk (m + 1) g))) = tk (m + 2) (pz v i g) := by
  funext j
  simp only [tk, pz, ext]
  have := j.isLt
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | (congr 2; omega)

end Seq

def prismH {Y : Type} (v : Y → Y) (m : ℕ) (F : (Fin (m + 2) → Y) → ℝ) (y : Fin (m + 1) → Y) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i * F (tk (m + 2) (pz v i (ext y)))

private theorem signed_double_sum_prism_identity (A T : ℕ → ℕ → ℝ) (D : ℕ → ℝ)
    (h1 : ∀ i l, l < i → T i l = A (i - 1) l) (h2 : ∀ i, T i i = D i)
    (h3 : ∀ i, T i (i + 1) = D (i + 1)) (h4 : ∀ i l, i + 1 < l → T i l = A i (l - 1)) (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), (-1 : ℝ) ^ i * ∑ l ∈ Finset.range (M + 2), (-1 : ℝ) ^ l * T i l
      = D 0 - D (M + 1) - ∑ l ∈ Finset.range (M + 1), (-1 : ℝ) ^ l * ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * A i l := by
  induction M with
  | zero =>
    have e := h3 0
    simp only [zero_add] at e
    simp [Finset.sum_range_succ, h2, e]
    ring
  | succ M ih =>
    have hs : ((-1 : ℝ) ^ M) * (-1) ^ M = 1 := by rw [← mul_pow]; norm_num
    have hA : ∑ i ∈ Finset.range (M + 1), (-1 : ℝ) ^ i * ∑ l ∈ Finset.range (M + 1 + 2), (-1 : ℝ) ^ l * T i l
        = ∑ i ∈ Finset.range (M + 1), (-1 : ℝ) ^ i * ∑ l ∈ Finset.range (M + 2), (-1 : ℝ) ^ l * T i l
          + (-1 : ℝ) ^ M * ∑ i ∈ Finset.range (M + 1), (-1 : ℝ) ^ i * A i (M + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [show M + 1 + 2 = M + 2 + 1 by omega, Finset.sum_range_succ, h4 i (M + 2) (by omega),
        show M + 2 - 1 = M + 1 by omega]
      ring
    have hB : ∑ l ∈ Finset.range (M + 1 + 2), (-1 : ℝ) ^ l * T (M + 1) l
        = ∑ l ∈ Finset.range (M + 1), (-1 : ℝ) ^ l * A M l - (-1 : ℝ) ^ M * D (M + 1)
          + (-1 : ℝ) ^ M * D (M + 1 + 1) := by
      rw [show M + 1 + 2 = M + 1 + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
        h2 (M + 1), h3 (M + 1)]
      have e : ∑ l ∈ Finset.range (M + 1), (-1 : ℝ) ^ l * T (M + 1) l
          = ∑ l ∈ Finset.range (M + 1), (-1 : ℝ) ^ l * A M l :=
        Finset.sum_congr rfl fun l hl => by
          rw [Finset.mem_range] at hl
          rw [h1 (M + 1) l (by omega), Nat.add_sub_cancel]
      rw [e]
      ring
    have hC : ∑ l ∈ Finset.range (M + 1 + 1), (-1 : ℝ) ^ l * ∑ i ∈ Finset.range (M + 1), (-1 : ℝ) ^ i * A i l
        = ∑ l ∈ Finset.range (M + 1), (-1 : ℝ) ^ l * ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * A i l
          - (-1 : ℝ) ^ M * ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * A i (M + 1)
          + (-1 : ℝ) ^ M * ∑ l ∈ Finset.range (M + 1), (-1 : ℝ) ^ l * A M l - A M (M + 1) := by
      have inner : ∀ l, ∑ i ∈ Finset.range (M + 1), (-1 : ℝ) ^ i * A i l
          = ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * A i l + (-1 : ℝ) ^ M * A M l :=
        fun l => Finset.sum_range_succ _ _
      simp only [inner, mul_add, Finset.sum_add_distrib]
      rw [Finset.sum_range_succ _ (M + 1), Finset.sum_range_succ _ (M + 1)]
      have e : ∑ l ∈ Finset.range (M + 1), (-1 : ℝ) ^ l * ((-1 : ℝ) ^ M * A M l)
          = (-1 : ℝ) ^ M * ∑ l ∈ Finset.range (M + 1), (-1 : ℝ) ^ l * A M l := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [e]
      linear_combination (-(A M (M + 1))) * hs
    have hD : ∑ i ∈ Finset.range (M + 1), (-1 : ℝ) ^ i * A i (M + 1)
        = ∑ i ∈ Finset.range M, (-1 : ℝ) ^ i * A i (M + 1) + (-1 : ℝ) ^ M * A M (M + 1) :=
      Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ _ (M + 1), hA, hB, ih, hC, hD]
    linear_combination (A M (M + 1) + D (M + 1) - D (M + 1 + 1)) * hs

theorem dC_prismH {Y : Type} (v : Y → Y) (m : ℕ) (F : (Fin (m + 2) → Y) → ℝ) (hF : dC F = 0)
    (f : ℕ → Y) : dC (prismH v m F) (tk (m + 2) f) = F (tk (m + 2) fun j => v (f j)) - F (tk (m + 2) f) := by
  have hz : ∀ i, ∑ l ∈ Finset.range (m + 1 + 2), (-1 : ℝ) ^ l * F (tk (m + 2) (fc l (pz v i f))) = 0 := by
    intro i
    have e := dC_tk (n := m + 1) F (pz v i f)
    rw [hF] at e
    exact e.symm.trans rfl
  have key := signed_double_sum_prism_identity (fun i l => F (tk (m + 2) (pz v i (fc l f))))
    (fun i l => F (tk (m + 2) (fc l (pz v i f)))) (fun i => F (tk (m + 2) (fc i (pz v i f))))
    (fun i l h => by simp only [fc_pz_lt v f h]) (fun i => rfl)
    (fun i => by simp only [fc_pz_diag v f i]) (fun i l h => by simp only [fc_pz_gt v f h]) (m + 1)
  beta_reduce at key
  simp only [hz, mul_zero, Finset.sum_const_zero] at key
  rw [fc_pz_zero v f] at key
  have e7 : F (tk (m + 2) (fc (m + 1 + 1) (pz v (m + 1 + 1) f))) = F (tk (m + 2) f) :=
    congrArg F (tk_fc_pz_top v f m)
  rw [e7] at key
  have hP : ∀ l, prismH v m F (tk (m + 1) (fc l f))
      = ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i * F (tk (m + 2) (pz v i (fc l f))) := by
    intro l
    unfold prismH
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [tk_pz_ext v m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  rw [dC_tk]
  simp only [hP]
  linarith

theorem dC_neg {Y : Type} {m : ℕ} (P : (Fin (m + 1) → Y) → ℝ) (y : Fin (m + 2) → Y) :
    dC (fun x => -P x) y = -dC P y := by
  simp only [dC, mul_neg, Finset.sum_neg_distrib]

theorem dC_add {Y : Type} {m : ℕ} (P Q : (Fin (m + 1) → Y) → ℝ) :
    dC (fun x => P x + Q x) = fun y => dC P y + dC Q y := by
  funext y
  simp only [dC, mul_add, Finset.sum_add_distrib]

theorem pPrism : PPrism := by
  intro H Y _ _ v hv m F hFi hF
  refine ⟨fun y => -prismH v m F y, ?_, ?_⟩
  · intro h y
    simp only [prismH, neg_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← hFi h (tk (m + 2) (pz v i (ext y)))]
    congr 1
    funext j
    simp only [tk, pz, ext]
    split_ifs <;> simp [hv]
  · intro y
    rw [dC_neg]
    have e := dC_prismH v m F hF (ext y)
    rw [tk_ext] at e
    have e2 : tk (m + 2) (fun j => v (ext y j)) = v ∘ y := by
      funext j
      exact congrArg v (congrFun (tk_ext y) j)
    rw [e, e2]
    ring

theorem pCobSub : PCobSub := by
  intro Γ _ H m Φ hΦ hd hc
  obtain ⟨ρ, hρ1, hρ2⟩ : ∃ ρ : Γ → Γ, (∀ γ, γ * (ρ γ)⁻¹ ∈ H) ∧ ∀ (h : H) (γ : Γ), ρ (↑h * γ) = ρ γ := by
    refine ⟨fun γ => (Quotient.mk (QuotientGroup.rightRel H) γ).out, fun γ => ?_, fun h γ => ?_⟩
    · exact QuotientGroup.rightRel_apply.mp (Quotient.mk_out (s := QuotientGroup.rightRel H) γ)
    · show (Quotient.mk _ _).out = (Quotient.mk _ _).out
      congr 1
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      rw [mul_inv_rev, mul_inv_cancel_left]
      exact H.inv_mem h.2
  obtain ⟨v, hvH, hv⟩ : ∃ v : Γ → Γ, (∀ γ, v γ ∈ H) ∧ ∀ (h : H) (γ : Γ), v (h • γ) = h • v γ := by
    refine ⟨fun γ => γ * (ρ γ)⁻¹, hρ1, fun h γ => ?_⟩
    simp only [Subgroup.smul_def, smul_eq_mul, hρ2, mul_assoc]
  obtain ⟨Ψ₁, hΨ₁i, hΨ₁⟩ := pPrism H Γ v hv m Φ (by intro h y; exact hΦ h y) hd
  obtain ⟨E, hEi, hE⟩ := pCob H m (fun z => Φ (fun j => (z j : Γ)))
    (by intro g z; exact hΦ g (fun j => (z j : Γ))) (by intro w hw; exact hc w hw)
  refine ⟨fun y => Ψ₁ y + E (fun j => ⟨v (y j), hvH (y j)⟩), ?_, ?_⟩
  · intro g y
    show Ψ₁ (fun j => H.subtype g • y j) + E (fun j => ⟨v (H.subtype g • y j), hvH _⟩)
      = Ψ₁ y + E (fun j => ⟨v (y j), hvH (y j)⟩)
    have e1 : Ψ₁ (fun j => H.subtype g • y j) = Ψ₁ y := hΨ₁i g y
    have e2 : (fun j => (⟨v (H.subtype g • y j), hvH _⟩ : H))
        = fun j => MonoidHom.id H g • (⟨v (y j), hvH (y j)⟩ : H) := by
      funext j
      apply Subtype.ext
      exact hv g (y j)
    rw [e1, e2]
    congr 1
    exact hEi g _
  · rw [dC_add]
    funext y
    rw [hΨ₁ y]
    have e3 : dC (fun x : Fin (m + 1) → Γ => E (fun j => ⟨v (x j), hvH (x j)⟩)) y
        = dC E (fun j => ⟨v (y j), hvH (y j)⟩) := rfl
    rw [e3, hE]
    simp [Function.comp_def]

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.Transfer
noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

theorem dC_translate {Γ : Type} [Group Γ] {m : ℕ} (F : (Fin (m + 1) → Γ) → ℝ) (g : Γ) (y : Fin (m + 2) → Γ) :
    dC (fun y : Fin (m + 1) → Γ => F fun j => g * y j) y = dC F (fun j => g * y j) := rfl

theorem pTransfer (hC : PCobSub) (hE : PEvDC) : PTransfer := by
  intro Γ X _ _ act h1 hm m Φ hΦ hd hcyc z hz
  classical
  haveI : Fintype X := Fintype.ofFinite X
  have hinv : ∀ x, Inv (stabR act h1 hm x).subtype (Φ x) := by
    intro x g y
    have hg : act x (g : Γ) = x := g.2
    show (Φ x fun j => (g : Γ) * y j) = Φ x y
    rw [← hΦ x g y, hg]
  have hex : ∀ x, ∃ Ψ : (Fin (m + 1) → Γ) → ℝ, Inv (stabR act h1 hm x).subtype Ψ ∧ dC Ψ = Φ x :=
    fun x => hC Γ (stabR act h1 hm x) m (Φ x) (hinv x) (hd x) (hcyc x)
  choose Ψ hΨi hΨd using hex
  obtain ⟨rep, hrep1, hrep2⟩ : ∃ rep : X → X, (∀ x h, rep (act x h) = rep x) ∧
      ∀ x, ∃ g, act (rep x) g = x := by
    letI S : Setoid X := ⟨fun a b => ∃ g, act a g = b, ⟨fun a => ⟨1, h1 a⟩,
      fun ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg, ← hm, mul_inv_cancel, h1]⟩,
      fun ⟨g, hg⟩ ⟨k, hk⟩ => ⟨g * k, by rw [hm, hg, hk]⟩⟩⟩
    refine ⟨fun x => (Quotient.mk S x).out, fun x h => ?_, fun x => ?_⟩
    · exact congrArg Quotient.out (@Quotient.sound _ S _ _ ⟨h⁻¹, by rw [← hm, mul_inv_cancel, h1]⟩)
    · exact @Quotient.mk_out _ S x
  obtain ⟨gs, hgs⟩ : ∃ gs : X → Γ, ∀ x, act (rep x) (gs x) = x :=
    ⟨fun x => (hrep2 x).choose, fun x => (hrep2 x).choose_spec⟩
  have hshift : ∀ x h (y : Fin (m + 1) → Γ),
      Ψ (rep x) (fun j => gs x * (h * y j)) = Ψ (rep (act x h)) (fun j => gs (act x h) * y j) := by
    intro x h y
    have e2 := hgs (act x h)
    rw [hrep1] at e2 ⊢
    have hk : act (rep x) (gs x * h * (gs (act x h))⁻¹) = rep x := by
      have t : act (act (rep x) (gs (act x h))) (gs (act x h))⁻¹ = rep x := by
        rw [← hm, mul_inv_cancel, h1]
      rw [e2] at t
      rw [hm, hm, hgs x, t]
    have := hΨi (rep x) ⟨gs x * h * (gs (act x h))⁻¹, hk⟩ (fun j => gs (act x h) * y j)
    rw [← this]
    congr 1
    funext j
    show gs x * (h * y j) = (gs x * h * (gs (act x h))⁻¹) * (gs (act x h) * y j)
    group
  have hEinv : Inv (MonoidHom.id Γ) (fun y : Fin (m + 1) → Γ => ∑ x, Ψ (rep x) fun j => gs x * y j) := by
    intro g y
    show ∑ x, Ψ (rep x) (fun j => gs x * (g * y j)) = ∑ x, Ψ (rep x) fun j => gs x * y j
    rw [Finset.sum_congr rfl (fun x _ => hshift x g y)]
    exact Fintype.sum_equiv ⟨fun x => act x g, fun x => act x g⁻¹,
      fun x => by simp only; rw [← hm, mul_inv_cancel, h1],
      fun x => by simp only; rw [← hm, inv_mul_cancel, h1]⟩ _ _
      (fun x => rfl)
  have hdE : dC (fun y : Fin (m + 1) → Γ => ∑ x, Ψ (rep x) fun j => gs x * y j)
      = fun y => ∑ x, Φ x y := by
    funext y
    have hx : ∀ x, Φ x y = dC (fun y' : Fin (m + 1) → Γ => Ψ (rep x) fun j => gs x * y' j) y := by
      intro x
      rw [dC_translate (Ψ (rep x)) (gs x) y, hΨd (rep x), ← hΦ (rep x) (gs x) y, hgs x]
    simp only [hx, dC, Finset.mul_sum]
    exact Finset.sum_comm
  have key := hE Γ Γ Γ (MonoidHom.id Γ) m
    (fun y : Fin (m + 1) → Γ => ∑ x, Ψ (rep x) fun j => gs x * y j) hEinv 1 z
  rw [hdE] at key
  have hz' : bd Γ m z = 0 := hz
  rw [hz'] at key
  simp only [finsum_eq_sum_of_fintype]
  rw [key]
  simp [ev]

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

namespace PositivityTheory.KB

open AffineStabilizerVanishing

theorem sHecke_of (_hCh : SChain) (_hEv : SEv) (_hSep : SSep) (_hSt : SStab) (_hFin : SFin) (_hAff : SAff) :
    SHecke :=
  assemble _hCh _hEv _hSt _hFin _hAff (pKey (pTransfer pCobSub pEvDC)) pHeckeFormal
    (pHeckeKer (pTransfer pCobSub pEvDC) pEvDC) pIndex pStabK

end PositivityTheory.KB
