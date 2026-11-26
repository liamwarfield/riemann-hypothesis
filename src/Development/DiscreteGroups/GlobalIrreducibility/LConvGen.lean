module

public import Development.DiscreteGroups.GlobalIrreducibility.RankOneTopLeftZero

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.ExistsColChar
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DotjUpdate
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.NeTopOfConj
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.KUSStable
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.TopLeftElemInv
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.TopLeftXAInv
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

section RankOne

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (ξ : Fin n → k) (hξ : ξ (i0 j hj hj1) ≠ 0)
include hξ

theorem coef_eq : (ξ (i0 j hj hj1))⁻¹ * (ξ (i0 j hj hj1) - 1) = 1 - (ξ (i0 j hj hj1))⁻¹ := by
  field_simp

def xA : GL (Fin n) k :=
  ⟨1 + R1 j hj hj1 ξ, 1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ,
    by rw [add_mul, one_mul, mul_sub, mul_one, Matrix.mul_smul, rankOne_mul_self, smul_smul, rowVector_at_index, coef_eq j hj hj1 ξ hξ,
      sub_smul, one_smul]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, rankOne_mul_self, smul_smul, rowVector_at_index, coef_eq j hj hj1 ξ hξ,
      sub_smul, one_smul]; abel⟩

theorem topLeft_xA : TopLeft j ((xA j hj hj1 ξ hξ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 + R1 j hj hj1 ξ) i l = _
  rw [Matrix.add_apply, rankOne_top_left_zero j hj hj1 ξ i l h, add_zero]

theorem topLeft_xA_inv : TopLeft j (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ) i l = _
  rw [Matrix.sub_apply, Matrix.smul_apply, rankOne_top_left_zero j hj hj1 ξ i l h, smul_zero, sub_zero]

theorem rowMul_xA_inv (a : Fin n) (ha : a.val < j) :
    rowMul j ξ (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a =
      if a = i0 j hj hj1 then 1 else 0 := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  have key : ∀ i : Fin n, (if i.val < j then ξ i *
      (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i a else 0) =
      (if i = a then ξ a else 0) - (if i = i0 j hj hj1 then vrow j hj hj1 ξ a else 0) := by
    intro i
    show (if i.val < j then ξ i * (1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ) i a else 0) = _
    by_cases hi : i.val < j
    · rw [if_pos hi]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, R1, of_apply, one_apply]
      by_cases hia : i = a <;> by_cases hii : i = i0 j hj hj1
      · subst hia; subst hii; simp; field_simp
      · subst hia; simp [hii]
      · subst hii; simp [hia]; field_simp
      · simp [hia, hii]
    · rw [if_neg hi, if_neg (fun e => hi (by rw [e]; exact ha)), if_neg (fun e => hi (by rw [e]; exact hi0))]
      ring
  rw [rowMul, Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  simp only [vrow, if_pos ha]
  ring

theorem dotj_xA_inv (c : Fin n → k) :
    dotj j (rowMul j ξ (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) c = c (i0 j hj hj1) := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  rw [dotj, Finset.sum_congr rfl fun a _ => (?_ : _ = if a = i0 j hj hj1 then c a else 0), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _)]
  by_cases ha : a.val < j
  · rw [if_pos ha, rowMul_xA_inv j hj hj1 ξ hξ a ha]
    split_ifs <;> simp
  · rw [if_neg ha, if_neg (fun e => ha (by rw [e]; exact hi0))]

end RankOne

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

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) {p : Fin n} (hp : p.val < j) (hne : p ≠ i0 j hj hj1)
include hp

theorem topLeft_single (y : k) (i l : Fin n) (h : j ≤ i.val ∨ j ≤ l.val) :
    Matrix.single p (i0 j hj hj1) y i l = 0 := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  omega

theorem topLeft_elem (y : k) : TopLeft j ((GlobalTheory.RootUp.elem hne y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  rw [GlobalTheory.RootUp.val_elem, Matrix.add_apply, topLeft_single j hj hj1 hp y i l h, add_zero]

theorem topLeft_elem_inv (y : k) :
    TopLeft j (((GlobalTheory.RootUp.elem hne y)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 - Matrix.single p (i0 j hj hj1) y) i l = _
  rw [Matrix.sub_apply, topLeft_single j hj hj1 hp y i l h, sub_zero]

theorem rowMul_elem_inv (ξ : Fin n → k) :
    rowMul j ξ (((GlobalTheory.RootUp.elem hne (-1 : k))⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (i0 j hj hj1) =
      ξ (i0 j hj hj1) + ξ p := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  have key : ∀ i : Fin n, (if i.val < j then ξ i *
      (((GlobalTheory.RootUp.elem hne (-1 : k))⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i (i0 j hj hj1) else 0) =
      (if i = i0 j hj hj1 then ξ (i0 j hj hj1) else 0) + (if i = p then ξ p else 0) := by
    intro i
    show (if i.val < j then ξ i * (1 - Matrix.single p (i0 j hj hj1) (-1 : k)) i (i0 j hj hj1) else 0) = _
    rw [Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
    by_cases hi : i.val < j
    · rw [if_pos hi]
      by_cases h1 : i = i0 j hj hj1
      · subst h1
        have : ¬ (p = i0 j hj hj1) := hne
        simp [this, Ne.symm hne]
      · by_cases h2 : i = p
        · subst h2; simp [h1]
        · simp [h1, h2, Ne.symm h2]
    · rw [if_neg hi, if_neg (fun e => hi (by rw [e]; exact hi0)), if_neg (fun e => hi (by rw [e]; exact hp)),
        add_zero]
  rw [rowMul, Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]

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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

def chM (m : ℕ) (g : GL (Fin n) k) : ℂ := ((ψ (sdS m (g : Matrix (Fin n) (Fin n) k)) : Circle) : ℂ)

def KN (m : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ g ∈ Nset m, ∃ v : V, w = π g v - chM ψ m g • v}

def KUS (j : ℕ) (S : Finset (Fin n)) (ξ : Fin n → k) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ c : Fin n → k, (∀ r ∉ S, c r = 0) ∧ ∃ v : V,
    w = π (colU j c) v - ((ψ (dotj j ξ c) : Circle) : ℂ) • v}

theorem conj_apply (x g : GL (Fin n) k) (v : V) : π x (π g v) = π (x * g * x⁻¹) (π x v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

theorem KN_stable (j : ℕ) (x : GL (Fin n) k) (hx : Good j (x : Matrix (Fin n) (Fin n) k))
    (hy : Good j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) {w : V} (hw : w ∈ KN π ψ (j + 1)) :
    π x w ∈ KN π ψ (j + 1) := by
  refine (Submodule.span_le.2 ?_ : KN π ψ (j + 1) ≤ (KN π ψ (j + 1)).comap (π x)) hw
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨h1, h2⟩ := good_conj x hx hy hg
  refine Submodule.subset_span ⟨x * g * x⁻¹, h1, π x v, ?_⟩
  rw [map_sub, map_smul, conj_apply, chM, chM, h2]

theorem colU_comm (j : ℕ) (c d : Fin n → k) : colU j c * colU j d = colU j d * colU j c := by
  rw [← colU_add, ← colU_add, add_comm]

theorem KUS_stable (j : ℕ) (S : Finset (Fin n)) (ξ d : Fin n → k) {w : V} (hw : w ∈ KUS π ψ j S ξ) :
    π (colU j d) w ∈ KUS π ψ j S ξ := by
  refine (Submodule.span_le.2 ?_ : KUS π ψ j S ξ ≤ (KUS π ψ j S ξ).comap (π (colU j d))) hw
  rintro _ ⟨c, hc, v, rfl⟩
  refine Submodule.subset_span ⟨c, hc, π (colU j d) v, ?_⟩
  rw [map_sub, map_smul, ← Module.End.mul_apply, ← map_mul, colU_comm, map_mul, Module.End.mul_apply]

theorem W_stable (j : ℕ) (S : Finset (Fin n)) (ξ d : Fin n → k) {w : V}
    (hw : w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ) : π (colU j d) w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j d) (good_colU_inv j d) ha)
    (KUS_stable π ψ j S ξ d hb)

theorem KN_top (m : ℕ) (hm : n ≤ m) : KN π ψ m = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨g, hg, v, rfl⟩
  have hg1 : g = 1 := by
    ext i l
    rw [hg i l (Or.inr (by omega)), Units.val_one]
  have hs : sdS m ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg (by omega)]
  rw [hg1, chM, hs, AddChar.map_zero_eq_one, Circle.coe_one, one_smul, map_one, Module.End.one_apply, sub_self]

end DiscreteGroups.sglob.LConvGenR
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem univ_supp (c : Fin n → k) : ∀ r ∉ (Finset.univ : Finset (Fin n)), c r = 0 :=
  fun r hr => absurd (Finset.mem_univ r) hr

theorem conj_S (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (ξ : Fin n → k) {w : V}
    (hw : w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) :
    π x⁻¹ w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add (f := _)]
  refine Submodule.add_mem_sup (KN_stable π ψ j _ hy.good (by rw [inv_inv]; exact hx.good) ha) ?_
  refine (Submodule.span_le.2 ?_ : KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    ≤ (KUS π ψ j Finset.univ ξ).comap (π x⁻¹)) hb
  rintro _ ⟨c, -, v, rfl⟩
  refine Submodule.subset_span ⟨colMul j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) c, univ_supp _, π x⁻¹ v, ?_⟩
  rw [map_sub, map_smul, conj_apply, inv_inv, conj_colU j hj x hx hy, dotj_colMul]

theorem ne_top_of_conj (j : ℕ) (hj : j < n) (x : GL (Fin n) k) (hx : TopLeft j (x : Matrix (Fin n) (Fin n) k))
    (hy : TopLeft j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (ξ : Fin n → k)
    (h : KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ ≠ ⊤) :
    KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ (rowMul j ξ ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ≠ ⊤ := by
  intro htop
  apply h
  refine eq_top_iff.2 fun v _ => ?_
  have := conj_S π ψ j hj x hx hy ξ (w := π x v) (by rw [htop]; exact Submodule.mem_top)
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this

theorem KN_le (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (η : Fin n → k) (hη : ∀ c, dotj j η c = c (i0 j hj hj1)) :
    KN π ψ j ≤ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ η := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨h1, h2⟩ := peel_N j hj hj1 hg
  set c : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ with hc
  set n' := colU j (-c) * g with hn'
  have hg' : g = colU j c * n' := by rw [hn', ← mul_assoc, ← colU_add, add_neg_cancel, colU_zero, one_mul]
  have hch : chM ψ j g = chM ψ (j + 1) n' * ((ψ (c (i0 j hj hj1)) : Circle) : ℂ) := by
    rw [chM, chM, h2, AddChar.map_add_eq_mul, Circle.coe_mul]; rfl
  have e : π g v - chM ψ j g • v = π (colU j c) (π n' v - chM ψ (j + 1) n' • v) +
      chM ψ (j + 1) n' • (π (colU j c) v - ((ψ (dotj j η c) : Circle) : ℂ) • v) := by
    rw [hη, hch, map_sub, map_smul, smul_sub, smul_smul]
    conv_lhs => rw [hg', map_mul, Module.End.mul_apply]
    abel
  show _ ∈ _
  rw [e]
  refine Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j c) (good_colU_inv j c)
    (Submodule.subset_span ⟨n', h1, v, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, univ_supp c, v, rfl⟩))

theorem twKer_le (j : ℕ) (hj : j < n) (h : ∑ i, ![j, n - j] i = n) (ξ : Fin n → k) (hz : ∀ i : Fin n, i.val < j → ξ i = 0) :
    twKer π (unipRad k (stdBlocks ![j, n - j] h)) 1 ≤ KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g, hg⟩, v, rfl⟩
  obtain ⟨h1, h2⟩ := peel_rad j hj h hg
  set c : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i ⟨j, hj⟩ with hc
  set n' := colU j (-c) * g with hn'
  have hg' : g = colU j c * n' := by rw [hn', ← mul_assoc, ← colU_add, add_neg_cancel, colU_zero, one_mul]
  have hch : chM ψ (j + 1) n' = 1 := by rw [chM, h2, AddChar.map_zero_eq_one, Circle.coe_one]
  have hd : dotj j ξ c = 0 := Finset.sum_eq_zero fun i _ => by
    by_cases hi : i.val < j
    · rw [if_pos hi, hz i hi, zero_mul]
    · rw [if_neg hi]
  have e : π g v - (((1 : ↥(unipRad k (stdBlocks ![j, n - j] h)) →* ℂˣ) ⟨g, hg⟩ : ℂˣ) : ℂ) • v =
      π (colU j c) (π n' v - chM ψ (j + 1) n' • v) + (π (colU j c) v - ((ψ (dotj j ξ c) : Circle) : ℂ) • v) := by
    rw [hch, hd, AddChar.map_zero_eq_one, Circle.coe_one, MonoidHom.one_apply, Units.val_one, one_smul,
      map_sub]
    conv_lhs => rw [hg', map_mul, Module.End.mul_apply]
    abel
  show _ ∈ _
  rw [e]
  exact Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j c) (good_colU_inv j c)
    (Submodule.subset_span ⟨n', h1, v, rfl⟩)) (Submodule.subset_span ⟨c, univ_supp c, v, rfl⟩)

end DiscreteGroups.sglob.LConvGenR
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

section Dot

variable {k : Type} [Field k] {n : ℕ}

theorem dotj_add (j : ℕ) (ξ c d : Fin n → k) : dotj j ξ (c + d) = dotj j ξ c + dotj j ξ d := by
  simp only [dotj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_add]

theorem dotj_single (j : ℕ) (ξ : Fin n → k) (a : Fin n) (x : k) :
    dotj j ξ (Pi.single a x) = if a.val < j then ξ a * x else 0 := by
  rw [dotj, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem dotj_update (j : ℕ) (ξ c : Fin n → k) (a : Fin n) (x : k) (hc : c a = 0) :
    dotj j (Function.update ξ a x) c = dotj j ξ c := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = a
  · subst hi; simp [hc]
  · rw [Function.update_of_ne hi]

end Dot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem KUS_empty (j : ℕ) (ξ : Fin n → k) : KUS π ψ j ∅ ξ = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨c, hc, v, rfl⟩
  have : c = 0 := funext fun r => hc r (Finset.notMem_empty r)
  subst this
  have h0 : dotj j ξ (0 : Fin n → k) = 0 := Finset.sum_eq_zero fun i _ => by split_ifs <;> simp
  rw [colU_zero, h0, AddChar.map_zero_eq_one, Circle.coe_one, one_smul, map_one, Module.End.one_apply, sub_self]

theorem smooth_col (hs : IsSmooth π) (j : ℕ) (hj : j < n) (a : Fin n) (v : V) :
    ∃ s : kˣ, ∀ h ∈ ball s, π (colU j (Pi.single a h)) v = v := by
  by_cases ha : a.val < j
  · have hne : a ≠ (⟨j, hj⟩ : Fin n) := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    have hU : {g : GL (Fin n) k | π g v = v} ∈ nhds (1 : GL (Fin n) k) := (hs v).mem_nhds (by simp)
    have h0 : GlobalTheory.RootUp.elem hne (0 : k) = 1 := Units.ext (by simp [GlobalTheory.RootUp.val_elem])
    have hpre : (GlobalTheory.RootUp.elem hne) ⁻¹' {g : GL (Fin n) k | π g v = v} ∈ nhds (0 : k) :=
      (GlobalTheory.RootUp.continuous_elem hne).continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
    obtain ⟨s, hs'⟩ := exists_cball_subset hpre
    refine ⟨s, fun h hh => ?_⟩
    rw [colU_single_of_lt j hj ha]
    exact hs' hh
  · exact ⟨1, fun h _ => by rw [colU_single_of_ge j (by omega), map_one, Module.End.one_apply]⟩

end DiscreteGroups.sglob.LConvGenR
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem exists_col_char {c : kˣ} (hc : HasConductor ψ c) (hs : IsSmooth π) (j : ℕ) (hj : j < n)
    (h0 : KN π ψ (j + 1) ≠ ⊤) (S : Finset (Fin n)) : ∃ ξ : Fin n → k, KN π ψ (j + 1) ⊔ KUS π ψ j S ξ ≠ ⊤ := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by rw [KUS_empty, sup_bot_eq]; exact h0⟩
  | insert a S ha ih =>
    obtain ⟨ξ, hξ⟩ := ih
    let σ : k → V →ₗ[ℂ] V := fun t => π (colU j (Pi.single a t))
    have hadd : ∀ s t, σ (s + t) = σ s * σ t := fun s t => by
      simp only [σ]; rw [Pi.single_add, colU_add, map_mul]
    have hW : ∀ t, ∀ w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ, σ t w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ :=
      fun t w hw => W_stable π ψ j S ξ _ hw
    obtain ⟨ξa, hξa⟩ := exists_character_sup_ne_top ψ σ hc hadd _ hW (fun v => smooth_col π hs j hj a v) hξ
    refine ⟨Function.update ξ a ξa, fun htop => hξa (eq_top_iff.2 ?_)⟩
    rw [← htop]
    refine sup_le (le_sup_left.trans le_sup_left) (Submodule.span_le.2 ?_)
    rintro _ ⟨c, hcS, v, rfl⟩
    set cS := Function.update c a 0 with hcS'
    have hcS0 : ∀ r ∉ S, cS r = 0 := by
      intro r hr
      by_cases hra : r = a
      · subst hra; simp [cS]
      · rw [hcS', Function.update_of_ne hra]; exact hcS r (by simp [hra, hr])
    have hsplit : c = Pi.single a (c a) + cS := by
      funext r
      by_cases hra : r = a
      · subst hra; simp [cS]
      · simp [cS, hra, Pi.single_apply]
    have hdot : dotj j (Function.update ξ a ξa) c =
        dotj j (Function.update ξ a ξa) (Pi.single a (c a)) + dotj j ξ cS := by
      conv_lhs => rw [hsplit]
      rw [dotj_add, dotj_update j ξ cS a ξa (by simp [cS])]
    have e : π (colU j c) v - ((ψ (dotj j (Function.update ξ a ξa) c) : Circle) : ℂ) • v =
        σ (c a) (π (colU j cS) v - ((ψ (dotj j ξ cS) : Circle) : ℂ) • v) +
        ((ψ (dotj j ξ cS) : Circle) : ℂ) • (σ (c a) v -
          ((ψ (dotj j (Function.update ξ a ξa) (Pi.single a (c a))) : Circle) : ℂ) • v) := by
      have hcol : π (colU j c) v = σ (c a) (π (colU j cS) v) := by
        conv_lhs => rw [hsplit]
        rw [colU_add, map_mul, Module.End.mul_apply]
      rw [hcol, hdot, AddChar.map_add_eq_mul, Circle.coe_mul, map_sub, map_smul, smul_sub, smul_smul,
        mul_comm ((ψ (dotj j (Function.update ξ a ξa) (Pi.single a (c a))) : Circle) : ℂ)]
      abel
    show _ ∈ _
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hW _ _ (Submodule.mem_sup_right
      (Submodule.subset_span ⟨cS, hcS0, v, rfl⟩)))) (Submodule.smul_mem _ _ ?_)
    rw [dotj_single]
    by_cases haj : a.val < j
    · rw [if_pos haj, Function.update_self]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨c a, v, rfl⟩)
    · rw [if_neg haj, AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
      simp only [σ]
      rw [colU_single_of_ge j (by omega), map_one, Module.End.one_apply, sub_self]
      exact Submodule.zero_mem _

end DiscreteGroups.sglob.LConvGenR
end
end

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem step {c : kˣ} (hc : HasConductor ψ c) (hcusp : IsCuspidal π) (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j)
    (h0 : KN π ψ (j + 1) ≠ ⊤) : KN π ψ j ≠ ⊤ := by
  obtain ⟨ξ, hξ⟩ := exists_col_char π ψ hc hcusp.1 j hj h0 Finset.univ
  by_cases hz : ∀ i : Fin n, i.val < j → ξ i = 0
  · exfalso
    have h : ∑ i, ![j, n - j] i = n := by simp [Fin.sum_univ_two]; omega
    have htw : twKer π (unipRad k (stdBlocks ![j, n - j] h)) 1 = ⊤ :=
      Submodule.Quotient.subsingleton_iff.1 (hcusp.2 2 ![j, n - j] (stdBlocks ![j, n - j] h)
        (GlobalTheory.T.unipRad_stdBlocks_two_ne_bot' k n j (n - j) h hj1 (by omega)))
    exact hξ (eq_top_iff.2 (by rw [← htw]; exact twKer_le π ψ j hj h ξ hz))
  · push Not at hz
    obtain ⟨p, hp, hpξ⟩ := hz
    obtain ⟨ξ1, h1, hξ1⟩ : ∃ ξ1 : Fin n → k, ξ1 (i0 j hj hj1) ≠ 0 ∧
        KN π ψ (j + 1) ⊔ KUS π ψ j Finset.univ ξ1 ≠ ⊤ := by
      by_cases hi0 : ξ (i0 j hj hj1) = 0
      · have hne : p ≠ i0 j hj hj1 := fun e => hpξ (by rw [e]; exact hi0)
        refine ⟨_, ?_, ne_top_of_conj π ψ j hj (GlobalTheory.RootUp.elem hne (-1 : k))
          (topLeft_elem j hj hj1 hp hne _) (topLeft_elem_inv j hj hj1 hp hne _) ξ hξ⟩
        rw [rowMul_elem_inv j hj hj1 hp hne ξ, hi0, zero_add]
        exact hpξ
      · exact ⟨ξ, hi0, hξ⟩
    have h2 := ne_top_of_conj π ψ j hj (xA j hj hj1 ξ1 h1) (topLeft_xA j hj hj1 ξ1 h1)
      (topLeft_xA_inv j hj hj1 ξ1 h1) ξ1 hξ1
    exact fun htop => h2 (eq_top_iff.2 (by rw [← htop]; exact KN_le π ψ j hj hj1 _ (dotj_xA_inv j hj hj1 ξ1 h1)))

theorem KN_one_ne_top [Nontrivial V] {c : kˣ} (hc : HasConductor ψ c) (hcusp : IsCuspidal π) :
    KN π ψ 1 ≠ ⊤ := by
  have hbase : ∀ m, n ≤ m → KN π ψ m ≠ ⊤ := fun m hm => by rw [KN_top π ψ m hm]; exact bot_ne_top
  have key : ∀ d, d + 1 ≤ n → KN π ψ (n - d) ≠ ⊤ := by
    intro d
    induction d with
    | zero => intro _; exact hbase _ (by omega)
    | succ d ih =>
      intro hd
      refine step π ψ hc hcusp (n - (d + 1)) (by omega) (by omega) ?_
      rw [show n - (d + 1) + 1 = n - d by omega]
      exact ih (by omega)
  by_cases hn : n ≤ 1
  · exact hbase 1 hn
  · have := key (n - 1) (by omega)
    rwa [show n - (n - 1) = 1 by omega] at this

theorem sdS_one (M : Matrix (Fin n) (Fin n) k) : sdS 1 M = ∑ i : Fin n, ∑ l : Fin n with l.val = i.val + 1, M i l := by
  simp only [sdS, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem mem_Nset_one {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n)) : u ∈ Nset 1 := by
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hu
  intro i l hil
  have hli : l ≤ i := hil.elim id (fun h => by rw [Fin.le_iff_val_le_val]; omega)
  rcases hli.lt_or_eq with hlt | heq
  · rw [h1 i l hlt, one_apply_ne (ne_of_gt hlt)]
  · rw [heq, h2 i, one_apply_eq]

end DiscreteGroups.sglob.LConvGenR

namespace DiscreteGroups.sglob.LConv

open DiscreteGroups.sglob.LConvGenR

theorem cuspGen : CuspGen := by
  intro k _ _ _ _ ψ hψ hψ1 n V _ _ π hV hcusp
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ hψ1
  have hne := KN_one_ne_top π ψ hc hcusp
  obtain ⟨x, hx⟩ : ∃ x, x ∉ KN π ψ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨f, hfx, hker⟩ := Submodule.exists_le_ker_of_notMem hx
  refine ⟨f, fun h0 => hfx (by rw [h0]; rfl), fun u hu v => ?_⟩
  have hmem : π u v - chM ψ 1 u • v ∈ KN π ψ 1 := Submodule.subset_span ⟨u, mem_Nset_one hu, v, rfl⟩
  have h1 := hker hmem
  rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at h1
  rw [h1, smul_eq_mul, chM, sdS_one]
  rfl

end DiscreteGroups.sglob.LConv
