module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvBigD
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvBigC
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvBigB
section -- merged from Development.DiscreteGroups.GlobalIrreducibility.LConvBigA
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Filter Topology

namespace DiscreteGroups.sglob.LConv

section Matrices

variable {k : Type} [Field k] {m : ℕ}

def tv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) : GL (Fin n) k :=
  ⟨Matrix.transvection i j c, Matrix.transvection i j (-c),
    by rw [Matrix.transvection_mul_transvection_same _ _ h, add_neg_cancel, Matrix.transvection_zero],
    by rw [Matrix.transvection_mul_transvection_same _ _ h, neg_add_cancel, Matrix.transvection_zero]⟩

theorem val_tv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) :
    ((tv i j h c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.transvection i j c := rfl

theorem val_tv_inv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) :
    (((tv i j h c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.transvection i j (-c) := rfl

theorem tv_zero {n : ℕ} (i j : Fin n) (h : i ≠ j) : tv i j h (0 : k) = 1 :=
  Units.ext (by rw [val_tv, Matrix.transvection_zero, Units.val_one])

theorem continuous_tv [TopologicalSpace k] [IsTopologicalAddGroup k] {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    Continuous fun c : k => tv i j h c := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun c : k => Matrix.transvection i j c
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · show Continuous fun c : k => Matrix.transvection i j (-c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

theorem stdSum_symm_castSucc (i : Fin m) : (stdSum (rfl : m + 1 = m + 1)).symm i.castSucc = Sum.inl i := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by simp)

theorem stdSum_symm_last : (stdSum (rfl : m + 1 = m + 1)).symm (Fin.last m) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by simp)

theorem corner_cs_cs (g : GL (Fin m) k) (i j : Fin m) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.castSucc j.castSucc = (g : Matrix (Fin m) (Fin m) k) i j := by
  simp [corner, emb₂, leviEmb, leviTwo, two, stdSum_symm_castSucc]

theorem corner_last (g : GL (Fin m) k) (j : Fin (m + 1)) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [corner, emb₂, leviEmb, leviTwo, two, stdSum_symm_last]
  · simp [corner, emb₂, leviEmb, leviTwo, two, Matrix.blockDiagonal', stdSum_symm_castSucc, stdSum_symm_last,
      (Fin.castSucc_lt_last j).ne']

theorem corner_one : corner (1 : GL (Fin m) k) = 1 :=
  map_one (emb₂ k (stdSum (rfl : m + 1 = m + 1)))

theorem longElt_inv (n : ℕ) : (longElt n k)⁻¹ = longElt n k := Units.ext rfl

theorem longElt_last (j : Fin (m + 1)) :
    (longElt (m + 1) k : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = if j = 0 then 1 else 0 := by
  simp [longElt]

end Matrices

section Small

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_small {U : Set k} (hU : U ∈ 𝓝 (0 : k)) (a : k) : ∃ t : k, t ≠ 0 ∧ t ∈ U ∧ a * t ∈ U := by
  let := GroundTheory.LocalField.nontriviallyNormedField k
  have hU' : U ∩ (fun t => a * t) ⁻¹' U ∈ 𝓝 (0 : k) :=
    inter_mem hU ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU'
  obtain ⟨t, ht0, htε⟩ := NormedField.exists_norm_lt k hε
  have ht : t ∈ U ∩ (fun t => a * t) ⁻¹' U := hball (by simpa using htε)
  exact ⟨t, norm_pos_iff.1 ht0, ht.1, ht.2⟩

end Small

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] {m : ℕ}

def cornerHom : GL (Fin m) k →* GL (Fin (m + 1)) k :=
  (emb₂ k (stdSum (rfl : m + 1 = m + 1))).comp (MonoidHom.inl _ _)

theorem cornerHom_apply (g : GL (Fin m) k) : cornerHom g = corner g := rfl

def IsP (p : GL (Fin (m + 1)) k) : Prop :=
  ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j

theorem mul_apply_last_of_isMirabolic {a b : GL (Fin (m + 1)) k} (ha : IsP a) (j : Fin (m + 1)) :
    ((a * b : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := by
  rw [Units.val_mul, Matrix.mul_apply]
  calc ∑ c, (a : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c * (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c j
      = ∑ c, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c * (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c j :=
        Finset.sum_congr rfl fun c _ => by rw [ha c]
    _ = _ := by rw [← Matrix.mul_apply, Matrix.one_mul]

theorem isMirabolic_mul {a b : GL (Fin (m + 1)) k} (ha : IsP a) (hb : IsP b) : IsP (a * b) := fun j =>
  (mul_apply_last_of_isMirabolic ha j).trans (hb j)

theorem isMirabolic_corner (g : GL (Fin m) k) : IsP (corner g) := corner_last g

theorem exists_eq_mul_corner {p : GL (Fin (m + 1)) k} (hp : IsP p) :
    ∃ u ∈ unipB k (Fin (m + 1)), ∃ h : GL (Fin m) k, p = u * corner h := by
  have hne : ∀ j : Fin m, Fin.last m ≠ j.castSucc := fun j => (Fin.castSucc_lt_last j).ne'
  set A : Matrix (Fin m) (Fin m) k := (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k).submatrix Fin.castSucc Fin.castSucc
  have he : ((-1 : k) ^ (m + m)) = 1 := by rw [← two_mul, pow_mul]; simp
  have hdet : (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k).det = A.det := by
    have hp' : ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := hp
    rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
    simp [hp', Matrix.one_apply, hne, Fin.succAbove_last, A, he]
  have hA : A.det ≠ 0 := by
    rw [← hdet]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 p.isUnit).ne_zero
  set h : GL (Fin m) k := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
  have hh : (h : Matrix (Fin m) (Fin m) k) = A := rfl
  refine ⟨p * corner h⁻¹, ?_, h, ?_⟩
  swap
  · rw [mul_assoc, ← cornerHom_apply, ← cornerHom_apply, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hL : ∀ j, ((p * corner h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := fun j =>
    (mul_apply_last_of_isMirabolic hp j).trans (corner_last _ j)
  have hB : ∀ i j : Fin m, ((p * corner h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
      i.castSucc j.castSucc = (1 : Matrix (Fin m) (Fin m) k) i j := by
    intro i j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, corner_last, Matrix.one_apply_ne (hne j)]
    simp only [corner_cs_cs, mul_zero, add_zero]
    rw [← h.mul_inv, Matrix.mul_apply, hh]
    rfl
  refine (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · induction i using Fin.lastCases with
    | last => rw [hL, Matrix.one_apply_ne hij.ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)
      | cast j =>
        rw [hB, Matrix.one_apply_ne]
        intro e; subst e; exact lt_irrefl _ hij
  · induction i using Fin.lastCases with
    | last => rw [hL, Matrix.one_apply_eq]
    | cast i => rw [hB, Matrix.one_apply_eq]

section Agree

variable {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁} {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂}
  {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem agree_of_isP (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) {p : GL (Fin (m + 1)) k}
    (hp : IsP p) : l₁ (π₁ p v₁) = l₂ (π₂ p v₂) := by
  obtain ⟨u, hu, h, rfl⟩ := exists_eq_mul_corner hp
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hl₁ u hu, hl₂ u hu, hX h]

theorem agree_translate (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) {p : GL (Fin (m + 1)) k}
    (hp : IsP p) (g : GL (Fin m) k) : l₁ (π₁ (corner g) (π₁ p v₁)) = l₂ (π₂ (corner g) (π₂ p v₂)) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  exact agree_of_isP hl₁ hl₂ hX (isMirabolic_mul (isMirabolic_corner g) hp)

end Agree

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] {m : ℕ} {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁}
  {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂} {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem agree_of_entry_one (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k)
    (hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 1) :
    l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
  set r : Fin (m + 1) → k := fun j => ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
    Matrix.of fun i j => if i = 0 then r j else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j
  have hMtri : ∀ i j : Fin (m + 1), j < i → M i j = 0 := by
    intro i j hij
    have hi : i ≠ 0 := fun e => by subst e; exact (Fin.not_lt_zero j) hij
    simp [M, hi, Matrix.one_apply_ne hij.ne']
  have hMdiag : ∀ i, M i i = 1 := by
    intro i
    by_cases hi : i = 0
    · subst hi; simpa [M, r] using hg
    · simp [M, hi]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hMtri i j hij)]
    simp [hMdiag]
  set n : GL (Fin (m + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero)
  have hnv : (n : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = M := rfl
  have hn : n ∈ unipB k (Fin (m + 1)) := (mem_unipB k).2 ⟨fun i j hij => by rw [hnv]; exact hMtri i j hij,
    fun i => by rw [hnv]; exact hMdiag i⟩
  have hwn : ∀ b, ((longElt (m + 1) k : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * (n : Matrix (Fin (m + 1)) (Fin (m + 1)) k))
      (Fin.last m) b = r b := by
    intro b
    rw [hnv, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (m + 1))]
    · rw [longElt_last, if_pos rfl, one_mul]
      simp [M, r]
    · intro a _ ha
      rw [longElt_last, if_neg ha, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set p : GL (Fin (m + 1)) k := longElt (m + 1) k * n * g
  have hP : IsP p := by
    intro j
    show ((longElt (m + 1) k * n * g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = _
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply]
    calc _ = ∑ b, r b * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) b j :=
          Finset.sum_congr rfl fun b _ => by rw [hwn b]
      _ = _ := by
        simp only [r]
        rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg' : g = n⁻¹ * (longElt (m + 1) k)⁻¹ * p := by
    simp only [p, mul_assoc, inv_mul_cancel_left]
  rw [hg', longElt_inv]
  simp only [map_mul, Module.End.mul_apply]
  rw [hl₁ _ (inv_mem hn), hl₂ _ (inv_mem hn), hW _ _ (agree_translate hl₁ hl₂ hX hP)]

theorem val_scalar (z : kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      Matrix.diagonal fun _ => (z : k) := by
  first
  | rfl
  | (ext i j; simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply])

theorem agree_scalar {ω₁ ω₂ : kˣ →* ℂˣ} (h₁ : HasCentralChar π₁ ω₁) (h₂ : HasCentralChar π₂ ω₂)
    (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k) (u : kˣ)
    (hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = u) :
    (ω₁ u : ℂ) * l₁ (π₁ g v₁) = (ω₂ u : ℂ) * l₂ (π₂ g v₂) := by
  have hent : (((Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u * g)⁻¹ : GL (Fin (m + 1)) k) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 1 := by
    rw [mul_inv_rev, ← map_inv, Units.val_mul, val_scalar, Matrix.mul_diagonal, hg, Units.mul_inv]
  have := agree_of_entry_one hl₁ hl₂ hW hX _ hent
  rwa [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₁, h₂, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul] at this

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Filter Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁}
  {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂} {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem small_fix (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) (v₁ : V₁) (v₂ : V₂) (i j : Fin (m + 1)) (h : i ≠ j) :
    {t : k | π₁ (tv i j h (-t)) v₁ = v₁ ∧ π₂ (tv i j h (-t)) v₂ = v₂} ∈ 𝓝 (0 : k) := by
  have hc : Continuous fun t : k => tv i j h (-t) := (continuous_tv i j h).comp continuous_neg
  refine IsOpen.mem_nhds (((hs₁ v₁).preimage hc).inter ((hs₂ v₂).preimage hc)) ?_
  simp [tv_zero]

theorem last_ne_zero (hm : 0 < m) : Fin.last m ≠ (0 : Fin (m + 1)) := fun e => by
  have := congrArg Fin.val e
  simp at this
  omega

theorem transvection_apply_same (i j : Fin (m + 1)) (h : i ≠ j) (t : k) : Matrix.transvection i j t i j = t := by
  simp [Matrix.transvection, Matrix.one_apply_ne h]

theorem centralChar_eq (hm : 0 < m) (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) {ω₁ ω₂ : kˣ →* ℂˣ}
    (h₁ : HasCentralChar π₁ ω₁) (h₂ : HasCentralChar π₂ ω₂) (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (h0 : l₁ v₁ ≠ 0) : ω₁ = ω₂ := by
  have hc : l₁ v₁ = l₂ v₂ := by
    have := hX 1
    rwa [corner_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply] at this
  have hL := last_ne_zero hm
  have hO := small_fix hs₁ hs₂ v₁ v₂ _ _ hL
  have key : ∀ t : k, ∀ ht : t ≠ 0, t ∈ {t : k | π₁ (tv _ _ hL (-t)) v₁ = v₁ ∧ π₂ (tv _ _ hL (-t)) v₂ = v₂} →
      ω₁ (Units.mk0 t ht) = ω₂ (Units.mk0 t ht) := by
    intro t ht hmem
    have hent : (((tv _ _ hL (-t))⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 =
        (Units.mk0 t ht : k) := by
      rw [val_tv_inv, neg_neg, transvection_apply_same _ _ hL, Units.val_mk0]
    have := agree_scalar h₁ h₂ hl₁ hl₂ hW hX _ _ hent
    rw [hmem.1, hmem.2, ← hc] at this
    exact Units.ext (mul_right_cancel₀ h0 this)
  refine MonoidHom.ext fun a => ?_
  obtain ⟨t, ht, htO, hatO⟩ := exists_small hO (a : k)
  have hat : (a : k) * t ≠ 0 := mul_ne_zero a.ne_zero ht
  have e : Units.mk0 ((a : k) * t) hat = a * Units.mk0 t ht := Units.ext (by simp)
  have h1 := key _ hat hatO
  rw [e, map_mul, map_mul, key _ ht htO] at h1
  exact mul_right_cancel h1

theorem agree_all (hm : 0 < m) (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) {ω : kˣ →* ℂˣ}
    (h₁ : HasCentralChar π₁ ω) (h₂ : HasCentralChar π₂ ω) (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k) :
    l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
  have step : ∀ g : GL (Fin (m + 1)) k,
      ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 ≠ 0 →
      l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
    intro g hg
    have := agree_scalar h₁ h₂ hl₁ hl₂ hW hX g (Units.mk0 _ hg) rfl
    exact mul_left_cancel₀ (ω (Units.mk0 _ hg)).ne_zero this
  by_cases hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 0
  swap
  · exact step g hg
  obtain ⟨j, hj⟩ : ∃ j, ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) j 0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h1 := congrFun (congrFun g.mul_inv 0) 0
    rw [Matrix.mul_apply] at h1
    simp [hall] at h1
  have hjL : Fin.last m ≠ j := fun e => hj (e ▸ hg)
  obtain ⟨t, ht, htO, -⟩ := exists_small (small_fix hs₁ hs₂ v₁ v₂ _ _ hjL) 1
  have hent : (((g * tv _ _ hjL (-t))⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
      (Fin.last m) 0 ≠ 0 := by
    rw [mul_inv_rev, Units.val_mul, val_tv_inv, neg_neg, Matrix.transvection_mul_apply_same, hg, zero_add]
    exact mul_ne_zero ht hj
  have := step _ hent
  rwa [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, htO.1, htO.2] at this

end DiscreteGroups.sglob.LConv

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

section Irr

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem irr_mem [ρ.IsIrreducible] (S : Submodule ℂ V) (hS : ∀ g, ∀ ⦃x⦄, x ∈ S → ρ g x ∈ S) {v : V} (hv0 : v ≠ 0)
    (hv : v ∈ S) (w : V) : w ∈ S := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation ρ) with h | h
  · exfalso
    apply hv0
    have : v ∈ (⟨S, hS⟩ : Subrepresentation ρ) := hv
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · have : w ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← h] at this
    exact this

theorem eq_zero_of_forall [ρ.IsIrreducible] (l : Module.Dual ℂ V) {v₀ : V} (hv₀ : l v₀ ≠ 0) {b : V}
    (hb : ∀ g, l (ρ g b) = 0) : b = 0 := by
  by_contra hb0
  let S : Submodule ℂ V :=
    { carrier := {x | ∀ g, l (ρ g x) = 0}
      add_mem' := fun {x y} hx hy g => by rw [map_add (f := _), map_add (f := _), hx g, hy g, add_zero]
      zero_mem' := fun g => by rw [map_zero, map_zero]
      smul_mem' := fun c x hx g => by rw [map_smul, map_smul, hx g, smul_zero] }
  have hS : ∀ h, ∀ ⦃x⦄, x ∈ S → ρ h x ∈ S := fun h x hx g => by
    rw [← Module.End.mul_apply, ← map_mul]
    exact hx (g * h)
  have := irr_mem S hS hb0 hb v₀ 1
  rw [map_one, Module.End.one_apply] at this
  exact hv₀ this

end Irr

theorem bigCell : BigCell := by
  intro k _ _ _ _ ψ m hm π₁ π₂ l₁ l₂ hl₁ hl₂ hW ⟨v₁, v₂, hX, h0⟩
  have := π₁.irr
  have := π₂.irr
  obtain ⟨ω₁, -, h₁⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar π₁.smooth π₁.irr
  obtain ⟨ω₂, -, h₂⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar π₂.smooth π₂.irr
  obtain rfl := centralChar_eq hm π₁.smooth π₂.smooth h₁ h₂ hl₁ hl₂ hW hX h0
  have hall : ∀ (a : π₁.V) (b : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) a) = l₂ (π₂.ρ (corner g) b)) →
      ∀ g, l₁ (π₁.ρ g a) = l₂ (π₂.ρ g b) := fun a b hab g =>
    agree_all hm π₁.smooth π₂.smooth h₁ h₂ hl₁ hl₂ hW hab g
  let Y : Submodule ℂ (π₁.V × π₂.V) :=
    { carrier := {x | ∀ g, l₁ (π₁.ρ g x.1) = l₂ (π₂.ρ g x.2)}
      add_mem' := fun {x y} hx hy g => by
        rw [Prod.fst_add, Prod.snd_add, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx g, hy g]
      zero_mem' := fun g => by simp
      smul_mem' := fun c x hx g => by
        rw [Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, map_smul, map_smul, hx g] }
  have hY : ∀ h (x : π₁.V × π₂.V), x ∈ Y → (π₁.ρ h x.1, π₂.ρ h x.2) ∈ Y := fun h x hx g => by
    show l₁ (π₁.ρ g (π₁.ρ h x.1)) = l₂ (π₂.ρ g (π₂.ρ h x.2))
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    exact hx (g * h)
  have hv : (v₁, v₂) ∈ Y := hall v₁ v₂ hX
  have h0' : l₂ v₂ ≠ 0 := by
    have := hv 1
    rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply] at this
    rwa [← this]
  have hv₁ : v₁ ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have hv₂ : v₂ ≠ 0 := fun e => h0' (by rw [e, map_zero])

  let f₁ : Y →ₗ[ℂ] π₁.V := (LinearMap.fst ℂ π₁.V π₂.V).comp Y.subtype
  let f₂ : Y →ₗ[ℂ] π₂.V := (LinearMap.snd ℂ π₁.V π₂.V).comp Y.subtype
  have inj₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero f₁).2 fun y hy => ?_
    have hy1 : (y : π₁.V × π₂.V).1 = 0 := hy
    have hy2 : (y : π₁.V × π₂.V).2 = 0 := eq_zero_of_forall (ρ := π₂.ρ) l₂ h0' fun g => by
      rw [← y.2 g, hy1, map_zero, map_zero]
    exact Subtype.ext (Prod.ext hy1 hy2)
  have inj₂ : Function.Injective f₂ := by
    refine (injective_iff_map_eq_zero f₂).2 fun y hy => ?_
    have hy2 : (y : π₁.V × π₂.V).2 = 0 := hy
    have hy1 : (y : π₁.V × π₂.V).1 = 0 := eq_zero_of_forall (ρ := π₁.ρ) l₁ h0 fun g => by
      rw [y.2 g, hy2, map_zero, map_zero]
    exact Subtype.ext (Prod.ext hy1 hy2)
  have surj₁ : Function.Surjective f₁ := fun a => by
    have := irr_mem (ρ := π₁.ρ) (LinearMap.range f₁) (fun h x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨⟨_, hY h _ y.2⟩, rfl⟩) hv₁ ⟨⟨_, hv⟩, rfl⟩ a
    exact this
  have surj₂ : Function.Surjective f₂ := fun b => by
    have := irr_mem (ρ := π₂.ρ) (LinearMap.range f₂) (fun h x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨⟨_, hY h _ y.2⟩, rfl⟩) hv₂ ⟨⟨_, hv⟩, rfl⟩ b
    exact this
  let e₁ := LinearEquiv.ofBijective f₁ ⟨inj₁, surj₁⟩
  let e₂ := LinearEquiv.ofBijective f₂ ⟨inj₂, surj₂⟩
  let T : π₁.V ≃ₗ[ℂ] π₂.V := e₁.symm.trans e₂
  have hT : ∀ a, (a, T a) ∈ Y := fun a => by
    have h1 : ((e₁.symm a : Y) : π₁.V × π₂.V).1 = a := e₁.apply_symm_apply a
    have := (e₁.symm a).2
    rw [← Prod.mk.eta (p := ((e₁.symm a : Y) : π₁.V × π₂.V)), h1] at this
    exact this
  have hint : ∀ g a, T (π₁.ρ g a) = π₂.ρ g (T a) := fun g a => by
    have h1 : e₁.symm (π₁.ρ g a) = ⟨_, hY g _ (hT a)⟩ := e₁.injective (by rw [e₁.apply_symm_apply]; rfl)
    show e₂ (e₁.symm (π₁.ρ g a)) = _
    rw [h1]
    rfl
  let Tint : Representation.IntertwiningMap π₁.ρ π₂.ρ :=
    { toLinearMap := T.toLinearMap
      isIntertwining' := fun g => LinearMap.ext fun a => hint g a }
  exact ⟨Tint.ofBijective T.bijective⟩

end DiscreteGroups.sglob.LConv

end
