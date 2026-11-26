module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnMixed
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.Imports
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.RealPowerProductEqOne
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.IsCompactSupport
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.MemBallMSelf
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.ValLeOneOfLc
public import Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.MeasurableSetBallM
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguez
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ImportsAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.MingZel
section -- merged from Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.RepInvApply
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Rg.Ming

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem idem_eq_eMat (r t : ℕ) : idem k r (r + t) r = GlobalTheory.GodementJacquet.eMat k r t := by
  ext i l
  simp [idem, GlobalTheory.GodementJacquet.eMat]

theorem rank_eq_of_ne {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : SB (Matrix (Fin (r + t)) (Fin r) k))
    (hΦ : ∀ x : Matrix (Fin (r + t)) (Fin r) k, x.rank < r → Φ.1 x = 0)
    (x : Matrix (Fin (r + t)) (Fin r) k) (hx : Φ.1 x ≠ 0) : x.rank = r := by
  have h1 : x.rank ≤ r := by
    simpa using Matrix.rank_le_width x
  have h2 : ¬ x.rank < r := fun h => hx (hΦ x h)
  omega

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rep_inv_apply {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin n) k) W) (h : GL (Fin n) k) (w : W) : π h (π h⁻¹ w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

end PositivityTheory.Rg.Ming

namespace PositivityTheory.Rg.Ming

theorem nz : BallSt → LocSt → NfSt → NzSt := by
  intro hball hloc hnf k _ _ _ _ _ _ ν hν r t μ V _ _ W _ _ σ π B hEq hG Φ hΦ
  ext w
  show B Φ w = 0
  set e := GlobalTheory.GodementJacquet.eMat k r t with he
  have key := hloc k (r + t) r (LinearMap.ker (B.flip w)) Φ
  have hmem := key ?_
  · simpa using hmem
  intro x hx
  have hrk := rank_eq_of_ne (V := V) (W := W) Φ hΦ x hx
  obtain ⟨⟨H, G, hxHG⟩, -⟩ := hnf k (r + t) r r x hrk
  rw [idem_eq_eMat] at hxHG
  obtain ⟨c, hc⟩ := hG (π H⁻¹ w)
  let f : Matrix (Fin (r + t)) (Fin r) k → Matrix (Fin (r + t)) (Fin r) k :=
    fun z => (H⁻¹ : GL (Fin (r + t)) k).val * z * (G⁻¹ : GL (Fin r) k).val
  have hf : Continuous f := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine ⟨f ⁻¹' ballM c e, ((hball k (r + t) r).1 c e).1.preimage hf, ?_, ?_⟩
  · show f x ∈ ballM c e
    have : f x = e := by
      simp only [f, hxHG, ← Matrix.mul_assoc]
      rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [this]
    exact fun i l => by simp
  · intro Ψ hΨ
    obtain ⟨Ψ', hΨ'def⟩ : ∃ Ψ' : SB (Matrix (Fin (r + t)) (Fin r) k),
        Ψ'.1 = om μ G H⁻¹ Ψ.1 :=
      ⟨⟨_, om_mem_SB μ _ _ Ψ.2⟩, rfl⟩
    have hΨΨ' : (Ψ : Matrix (Fin (r + t)) (Fin r) k → ℂ) = om μ G⁻¹ H Ψ'.1 := by
      show Ψ.1 = _
      rw [hΨ'def, ← om_mul, inv_mul_cancel, mul_inv_cancel, om_one]
    have hsupp : ∀ y, Ψ'.1 y ≠ 0 → y ∈ ballM c e := by
      intro y hy
      rw [hΨ'def] at hy
      simp only [om, inv_inv] at hy
      have h2 := (hΨ _ (right_ne_zero_of_mul hy)).1
      have h3 : f (H.val * y * G.val) = y := by
        simp only [f, ← Matrix.mul_assoc]
        rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      simpa [Set.mem_preimage, h3] using h2
    have h1 := hEq G⁻¹ H Ψ' Ψ hΨΨ' (π H⁻¹ w)
    rw [rep_inv_apply] at h1
    show B Ψ w = 0
    rw [h1, hc Ψ' hsupp, smul_zero, map_zero]

end PositivityTheory.Rg.Ming
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.ExtBasis
open ValuativeRel Matrix GlobalTheory.SplitWeil PositivityTheory.Tls2.Ming3

noncomputable section

namespace PositivityTheory.Rg.Ming.NfX

def E (R : Type*) [Semiring R] (a b j : ℕ) : Matrix (Fin a) (Fin b) R :=
  Matrix.of fun i l => if (i : ℕ) = l ∧ (l : ℕ) < j then 1 else 0

theorem E_apply {R : Type*} [Semiring R] {a b j : ℕ} (i : Fin a) (l : Fin b) :
    E R a b j i l = if (i : ℕ) = l ∧ (l : ℕ) < j then 1 else 0 := rfl

theorem E_mul {R : Type*} [Semiring R] {a b c j : ℕ} (hb : j ≤ b) :
    E R a b j * E R b c j = E R a c j := by
  ext i l
  simp only [Matrix.mul_apply, E_apply]
  by_cases h : (i : ℕ) = l ∧ (l : ℕ) < j
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := h
    have hi : (i : ℕ) < j := h1 ▸ h2
    rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin b)]
    · simp [hi, h1, h2]
    · intro m _ hm
      have hne : ¬ ((i : ℕ) = m ∧ (m : ℕ) < j) := fun e => hm (Fin.ext e.1.symm)
      rw [if_neg hne, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases h1 : (i : ℕ) = m ∧ (m : ℕ) < j
    · have h2 : ¬ ((m : ℕ) = l ∧ (l : ℕ) < j) := fun h2 => h ⟨h1.1.trans h2.1, h2.2⟩
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

theorem E_diag {R : Type*} [Semiring R] {a j : ℕ} :
    E R a a j = diagonal fun i : Fin a => if (i : ℕ) < j then 1 else 0 := by
  ext i l
  simp only [E_apply, diagonal_apply]
  by_cases h : i = l
  · subst h; simp
  · have : (i : ℕ) ≠ l := fun e => h (Fin.ext e)
    simp [h, this]

theorem rank_E {k : Type*} [Field k] {a j : ℕ} (hj : j ≤ a) : (E k a a j).rank = j := by
  classical
  rw [E_diag, rank_diagonal]
  refine (Fintype.card_congr ?_).trans (Fintype.card_fin j)
  exact
    { toFun := fun i => ⟨i.1, by
        have := i.2
        by_contra hlt
        simp [hlt] at this⟩
      invFun := fun l => ⟨Fin.castLE hj l, by simp [l.2]⟩
      left_inv := fun i => Subtype.ext (Fin.ext rfl)
      right_inv := fun l => Fin.ext rfl }

theorem what₂ {k : Type*} [Field k] {n r j : ℕ} (hj : j ≤ n) (y : Matrix (Fin n) (Fin r) k) (hy : y.rank ≤ j)
    (hc : LinearMap.range (E k n n j).mulVecLin ≤ LinearMap.range y.mulVecLin) : E k n n j * y = y := by
  classical
  have hE : (E k n n j).rank = j := rank_E hj
  have heq : LinearMap.range (E k n n j).mulVecLin = LinearMap.range y.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le hc
    exact (hy.trans hE.ge : y.rank ≤ (E k n n j).rank)
  have hEE : E k n n j * E k n n j = E k n n j := E_mul hj
  ext i l
  have hcol : y.mulVecLin (Pi.single l 1) ∈ LinearMap.range (E k n n j).mulVecLin := by
    rw [heq]
    exact LinearMap.mem_range_self _ _
  obtain ⟨v, hv⟩ := hcol
  have hv' : (E k n n j).mulVec v = y.mulVec (Pi.single l 1) := hv
  have key : (E k n n j * y).mulVec (Pi.single l 1) = y.mulVec (Pi.single l 1) := by
    rw [← Matrix.mulVec_mulVec, ← hv', Matrix.mulVec_mulVec, hEE]
  have := congrFun key i
  simpa [Matrix.mulVec_single_one] using this

theorem ext_basis {k : Type*} [Field k] {a j : ℕ} (hj : j ≤ a) (v : Fin j → (Fin a → k))
    (hv : LinearIndependent k v) : ∃ H : GL (Fin a) k, ∀ i (l : Fin j), H.val i (Fin.castLE hj l) = v l i := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range v))
  have hfin : Module.finrank k C = a - j := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 : Module.finrank k (Submodule.span k (Set.range v)) = j := by
      rw [finrank_span_eq_card hv, Fintype.card_fin]
    have h3 : Module.finrank k (Fin a → k) = a := Module.finrank_fin_fun k
    omega
  obtain ⟨bC, -⟩ : ∃ bC : Module.Basis (Fin (a - j)) k C, True :=
    ⟨Module.finBasisOfFinrankEq k C hfin, trivial⟩
  have hw : LinearIndependent k (C.subtype ∘ bC) :=
    bC.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
  have hdisj : Disjoint (Submodule.span k (Set.range v)) (Submodule.span k (Set.range (C.subtype ∘ bC))) := by
    have hle : Submodule.span k (Set.range (C.subtype ∘ bC)) ≤ C := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact (bC m).2
    exact hC.disjoint.mono_right hle
  have hvw := hv.sum_type hw hdisj
  obtain ⟨e, he⟩ : ∃ e : Fin a ≃ Fin j ⊕ Fin (a - j),
      e = (finCongr (by omega : a = j + (a - j))).trans finSumFinEquiv.symm := ⟨_, rfl⟩
  have hf := hvw.comp e e.injective
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin a) (Fin a) k, M = Matrix.of fun i m => (Sum.elim v (C.subtype ∘ bC) (e m)) i :=
    ⟨_, rfl⟩
  have hcolM : M.col = Sum.elim v (C.subtype ∘ bC) ∘ e := by
    ext m i
    simp [hM, Matrix.col]
  have hMu : IsUnit M := by
    rw [← linearIndependent_cols_iff_isUnit, hcolM]
    exact hf
  refine ⟨hMu.unit, fun i l => ?_⟩
  have hel : e (Fin.castLE hj l) = Sum.inl l := by
    rw [he, Equiv.trans_apply, Equiv.symm_apply_eq]
    apply Fin.ext
    simp
  show M i (Fin.castLE hj l) = v l i
  rw [hM, Matrix.of_apply, hel]
  rfl

private theorem E_mul_apply_eq_dite_lt {R : Type*} [Semiring R] {a b c j : ℕ} (hb : j ≤ b)
    (M : Matrix (Fin b) (Fin c) R) (i : Fin a) (m : Fin c) :
    (E R a b j * M) i m = if h : (i : ℕ) < j then M ⟨i, by omega⟩ m else 0 := by
  rw [Matrix.mul_apply]
  simp only [E_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin b)]
    · simp [h]
    · intro t _ ht
      have hne : ¬ ((i : ℕ) = t ∧ (t : ℕ) < j) := fun e => ht (Fin.ext e.1.symm)
      rw [if_neg hne, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun t _ => ?_
    have hne : ¬ ((i : ℕ) = t ∧ (t : ℕ) < j) := fun e => h (by rw [e.1]; exact e.2)
    rw [if_neg hne, zero_mul]

set_option maxHeartbeats 1000000 in
theorem nf1 {k : Type*} [Field k] {n r j : ℕ} (x : Matrix (Fin n) (Fin r) k) (hx : x.rank = j) :
    ∃ (H : GL (Fin n) k) (G : GL (Fin r) k), x = H.val * E k n r j * G.val := by
  classical
  have hn : j ≤ n := hx ▸ (by simpa using x.rank_le_card_height)
  have hr : j ≤ r := hx ▸ (by simpa using x.rank_le_card_width)
  obtain ⟨bb, -⟩ : ∃ bb : Module.Basis (Fin j) k (LinearMap.range x.mulVecLin), True :=
    ⟨Module.finBasisOfFinrankEq k _ hx, trivial⟩
  obtain ⟨H, hH⟩ := ext_basis hn ((LinearMap.range x.mulVecLin).subtype ∘ bb)
    (bb.linearIndependent.map' _ (Submodule.ker_subtype _))
  have hcol : LinearMap.range (H.val * E k n n j).mulVecLin ≤ LinearMap.range x.mulVecLin := by
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    by_cases hm : (m : ℕ) < j
    · have hc : (H.val * E k n n j).col m = (bb ⟨m, hm⟩ : Fin n → k) := by
        ext i
        show (H.val * E k n n j) i m = _
        simp only [E_diag, mul_diagonal, hm, if_true, mul_one]
        exact hH i ⟨m, hm⟩
      rw [hc]
      exact (bb ⟨m, hm⟩).2
    · have hc : (H.val * E k n n j).col m = 0 := by
        ext i
        show (H.val * E k n n j) i m = 0
        simp [E_diag, mul_diagonal, hm]
      rw [hc]
      exact zero_mem _
  obtain ⟨y, hy⟩ : ∃ y, y = (H⁻¹).val * x := ⟨_, rfl⟩
  have hcr : LinearMap.range (E k n n j).mulVecLin ≤ LinearMap.range y.mulVecLin := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, hu⟩ := hcol (LinearMap.mem_range_self _ w)
    refine ⟨u, ?_⟩
    have hu' : x.mulVec u = (H.val * E k n n j).mulVec w := hu
    show y.mulVec u = (E k n n j).mulVec w
    rw [hy, ← Matrix.mulVec_mulVec, hu', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul,
      Matrix.one_mul]
  have hyr : y.rank = j := by
    rw [hy, rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 (H⁻¹).isUnit), hx]
  have hrows : E k n n j * y = y := what₂ hn y hyr.le hcr
  have hzero : ∀ i : Fin n, ¬ (i : ℕ) < j → y i = 0 := by
    intro i hi
    ext m
    rw [← hrows, E_mul_apply_eq_dite_lt hn, dite_eq_right hi]
    rfl
  obtain ⟨z, hzd⟩ : ∃ z : Fin j → (Fin r → k), z = fun l => y (Fin.castLE hn l) := ⟨_, rfl⟩
  have hz : LinearIndependent k z := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    apply le_antisymm
    · have h1 : Submodule.span k (Set.range y) ≤ Submodule.span k (Set.range z) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        by_cases hi : (i : ℕ) < j
        · exact Submodule.subset_span ⟨⟨i, hi⟩, by rw [hzd]; rfl⟩
        · rw [hzero i hi]
          exact zero_mem _
      have h2 := Submodule.finrank_mono h1
      have h3 : y.rank = Module.finrank k (Submodule.span k (Set.range y)) := rank_eq_finrank_span_row y
      rw [← h3, hyr] at h2
      exact h2
    · simpa using finrank_range_le_card (R := k) (b := z)
  obtain ⟨G', hG'⟩ := ext_basis hr z hz
  have hT : IsUnit (G'.val)ᵀ := by
    rw [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det]
    exact G'.isUnit
  refine ⟨H, hT.unit, ?_⟩
  have hEG : E k n r j * hT.unit.val = y := by
    ext i m
    rw [E_mul_apply_eq_dite_lt hr]
    split_ifs with hi
    · have := hG' m ⟨i, hi⟩
      rw [hzd] at this
      exact this
    · rw [hzero i hi]
      rfl
  rw [Matrix.mul_assoc, hEG, hy, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Bd {a b : ℕ} (γ : ValueGroupWithZero k) (M : Matrix (Fin a) (Fin b) k) : Prop :=
  ∀ i l, valuation k (M i l) ≤ γ

theorem bd_mul {a b d : ℕ} {γ δ : ValueGroupWithZero k} {P : Matrix (Fin a) (Fin b) k}
    {Q : Matrix (Fin b) (Fin d) k} (hP : Bd γ P) (hQ : Bd δ Q) : Bd (γ * δ) (P * Q) := fun i m => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun l _ => by rw [map_mul]; exact mul_le_mul' (hP i l) (hQ l m)

theorem bd_sub {a b : ℕ} {γ : ValueGroupWithZero k} {P Q : Matrix (Fin a) (Fin b) k}
    (hP : Bd γ P) (hQ : Bd γ Q) : Bd γ (P - Q) := by
  intro i l
  rw [Matrix.sub_apply]
  exact (Valuation.map_sub _ _ _).trans (max_le (hP i l) (hQ i l))

theorem bd_E {a b j : ℕ} : Bd (1 : ValueGroupWithZero k) (E k a b j) := fun i l => by
  rw [E_apply]; split_ifs <;> simp

theorem bd_one {a : ℕ} : Bd (1 : ValueGroupWithZero k) (1 : Matrix (Fin a) (Fin a) k) := by
  intro i l
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem bd_KO {a : ℕ} {H : GL (Fin a) k} (hH : H ∈ KO k (Fin a)) : Bd (1 : ValueGroupWithZero k) H.val := by
  obtain ⟨u, rfl⟩ := hH
  intro i l
  show valuation k (algebraMap 𝒪[k] k (u.val i l)) ≤ 1
  exact (u.val i l).2

theorem mem_KO {a : ℕ} {γ : ValueGroupWithZero k} (hc : γ < 1) (A : Matrix (Fin a) (Fin a) k)
    (hA : Bd γ (A - 1)) : ∃ H ∈ KO k (Fin a), H.val = A := by
  classical
  have hint : ∀ i l, valuation k (A i l) ≤ 1 := by
    intro i l
    have h1 : A i l = (A - 1) i l + (1 : Matrix (Fin a) (Fin a) k) i l := by simp
    rw [h1]
    refine (Valuation.map_add _ _ _).trans (max_le ((hA i l).trans hc.le) ?_)
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hI : (valuation k).Integers 𝒪[k] := Valuation.integer.integers (valuation k)
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin a) (Fin a) 𝒪[k], B = Matrix.of fun i l => ⟨A i l, hint i l⟩ :=
    ⟨_, rfl⟩
  have hsmall : ∀ x : 𝒪[k], valuation k (x : k) < 1 → x ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
    exact hx.ne
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix B = 1 := by
    ext i l
    have hm : B i l - (1 : Matrix (Fin a) (Fin a) 𝒪[k]) i l ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      apply hsmall
      have e : ((B i l - (1 : Matrix (Fin a) (Fin a) 𝒪[k]) i l : 𝒪[k]) : k) = (A - 1) i l := by
        rw [Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply, hB]
        split_ifs <;> simp
      rw [e]
      exact lt_of_le_of_lt (hA i l) hc
    have h0 := (IsLocalRing.residue_eq_zero_iff _).2 hm
    rw [map_sub, sub_eq_zero] at h0
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit B.det := by
    by_contra hnu
    have hm : B.det ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have h0 := (IsLocalRing.residue_eq_zero_iff _).2 hm
    rw [RingHom.map_det, hres, det_one] at h0
    exact one_ne_zero h0
  have hBu : IsUnit B := (isUnit_iff_isUnit_det B).2 hdet
  refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[k] k) hBu.unit, ⟨hBu.unit, rfl⟩, ?_⟩
  subst hB
  rfl

theorem nf2 {n r j : ℕ} (x : Matrix (Fin n) (Fin r) k) (hx : x.rank = j) (c : kˣ)
    (hc : valuation k (c : k) < 1) (hb : ∀ i l, valuation k (x i l - E k n r j i l) ≤ valuation k (c : k)) :
    ∃ h ∈ KO k (Fin n), ∃ g ∈ KO k (Fin r), x = h.val * E k n r j * g.val := by
  have hn : j ≤ n := hx ▸ (by simpa using x.rank_le_card_height)
  have hr : j ≤ r := hx ▸ (by simpa using x.rank_le_card_width)
  have Enr_rn : E k n r j * E k r n j = E k n n j := E_mul hr
  have Ern_nr : E k r n j * E k n r j = E k r r j := E_mul hn
  have Enn_nr : E k n n j * E k n r j = E k n r j := E_mul hn
  have Enr_rr : E k n r j * E k r r j = E k n r j := E_mul hr
  have Err_rn : E k r r j * E k r n j = E k r n j := E_mul hr
  have hE1 : ∀ {a b : ℕ}, Bd (1 : ValueGroupWithZero k) (E k a b j) := fun {a b} => bd_E
  have hx' : Bd (valuation k (c : k)) (x - E k n r j) := fun i l => by
    rw [Matrix.sub_apply]
    exact hb i l
  have hh1 : x * E k r n j + (1 - E k n n j) - 1 = (x - E k n r j) * E k r n j := by
    rw [Matrix.sub_mul, Enr_rn]
    abel
  obtain ⟨H, hHK, hH⟩ := mem_KO hc (x * E k r n j + (1 - E k n n j)) (by
    rw [hh1]
    simpa using bd_mul hx' hE1)
  have hxE : x * E k r r j = H.val * E k n r j := by
    rw [hH, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Ern_nr, Enn_nr,
      sub_self, add_zero]
  obtain ⟨y, hy⟩ : ∃ y, y = (H⁻¹).val * x := ⟨_, rfl⟩
  have hyE : y * E k r r j = E k n r j := by
    rw [hy, Matrix.mul_assoc, hxE, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hyEn : y * E k r n j = E k n n j := by
    rw [← Err_rn, ← Matrix.mul_assoc, hyE, Enr_rn]
  have hcr : LinearMap.range (E k n n j).mulVecLin ≤ LinearMap.range y.mulVecLin := by
    rw [← hyEn, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hyr : y.rank ≤ j := by
    rw [hy]
    exact (rank_mul_le_right _ _).trans hx.le
  have hrows : E k n n j * y = y := what₂ hn y hyr hcr
  have hsplit : (x - E k n r j) * (1 - E k r r j) = x - x * E k r r j := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_one, Enr_rr]
    abel
  have hyd : y - E k n r j = (H⁻¹).val * ((x - E k n r j) * (1 - E k r r j)) := by
    rw [hsplit, Matrix.mul_sub, ← Matrix.mul_assoc, ← hy, hyE]
  have hinv : H⁻¹ ∈ KO k (Fin n) := (KO k (Fin n)).inv_mem hHK
  have hyb : Bd (valuation k (c : k)) (y - E k n r j) := by
    rw [hyd]
    simpa using bd_mul (bd_KO hinv) (bd_mul hx' (bd_sub bd_one hE1))
  have hg1 : E k r n j * y + (1 - E k r r j) - 1 = E k r n j * (y - E k n r j) := by
    rw [Matrix.mul_sub, Ern_nr]
    abel
  obtain ⟨G, hGK, hG⟩ := mem_KO hc (E k r n j * y + (1 - E k r r j)) (by
    rw [hg1]
    simpa using bd_mul hE1 hyb)
  refine ⟨H, hHK, G, hGK, ?_⟩
  calc x = H.val * y := by rw [hy, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    _ = H.val * (E k n r j * G.val) := by
      rw [hG, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Enr_rn, hrows,
        Enr_rr, sub_self, add_zero]
    _ = H.val * E k n r j * G.val := (Matrix.mul_assoc _ _ _).symm

end PositivityTheory.Rg.Ming.NfX

namespace PositivityTheory.Rg.Ming

theorem nf : NfSt := by
  intro k _ _ _ _ n r j x hx
  exact ⟨NfX.nf1 x hx, fun c hc hb => NfX.nf2 x hx c hc hb⟩

end PositivityTheory.Rg.Ming

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.IsCompactSupportSB
open MeasureTheory GlobalTheory.SplitWeil ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Rg.Ming

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n r : ℕ}

theorem ballM_mono_loc {c c' : kˣ} (h : valuation k (c : k) ≤ valuation k (c' : k))
    (x : Matrix (Fin n) (Fin r) k) : ballM c x ⊆ ballM c' x :=
  fun _ hy i l => (hy i l).trans h

theorem mem_ballM_self_loc (c : kˣ) (x : Matrix (Fin n) (Fin r) k) : x ∈ ballM c x := by
  intro i l
  simp

theorem isCompact_support_SB (Φ : SB (Matrix (Fin n) (Fin r) k)) :
    IsCompact (Function.support Φ.1) := by
  obtain ⟨hlc, hcs⟩ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  refine IsCompact.of_isClosed_subset hcs ?_ (subset_tsupport _)
  have h := (hlc.isClopen_fiber 0).isOpen
  rw [← isOpen_compl_iff]
  convert h using 1
  ext x
  simp [Function.mem_support]

theorem loc (hB : BallSt) : LocSt := by
  intro k _ _ _ _ n r P Φ hΦ
  obtain ⟨hball, hsmall, hdec⟩ := hB k n r
  have hpick : ∀ x : {x // (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0}, ∃ c : kˣ,
      ∀ Ψ : SB (Matrix (Fin n) (Fin r) k),
        (∀ y, (Ψ : Matrix (Fin n) (Fin r) k → ℂ) y ≠ 0 →
          y ∈ ballM c x.1 ∧ (Φ : Matrix (Fin n) (Fin r) k → ℂ) y ≠ 0) → Ψ ∈ P := by
    intro x
    obtain ⟨U, hU, hxU, hP⟩ := hΦ x.1 x.2
    obtain ⟨c, -, hc⟩ := hsmall x.1 U (hU.mem_nhds hxU)
    exact ⟨c, fun Ψ hΨ => hP Ψ fun y hy => ⟨hc (hΨ y hy).1, (hΨ y hy).2⟩⟩
  choose cs hcs using hpick
  obtain ⟨t, ht⟩ := (isCompact_support_SB Φ).elim_finite_subcover
    (fun x => ballM (cs x) x.1) (fun x => (hball (cs x) x.1).1)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, mem_ballM_self_loc _ _⟩)
  obtain ⟨c₀, hc₀⟩ := hdec Φ
  have hmin : ∀ s : Finset {x // (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0}, ∃ c : kˣ,
      valuation k (c : k) ≤ valuation k (c₀ : k) ∧
        ∀ i ∈ s, valuation k (c : k) ≤ valuation k (cs i : k) := by
    intro s
    classical
    refine Finset.induction_on s ⟨c₀, le_rfl, by simp⟩ ?_
    intro a s _ ih
    obtain ⟨c, hc1, hc2⟩ := ih
    rcases le_total (valuation k (c : k)) (valuation k (cs a : k)) with h | h
    · refine ⟨c, hc1, ?_⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h
      · exact hc2 i hi
    · refine ⟨cs a, h.trans hc1, ?_⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_rfl
      · exact h.trans (hc2 i hi)
  obtain ⟨c, hcc₀, hcci⟩ := hmin t
  obtain ⟨S, hS, hsum⟩ := hc₀ c hcc₀
  have hind : ∀ x, ((ballM c x).indicator fun _ => (1 : ℂ)) ∈ SB (Matrix (Fin n) (Fin r) k) :=
    fun x => (hball c x).2.2.1
  have hterm : ∀ x ∈ S, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x •
      (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) ∈ P := by
    intro x hx
    have hx0 : (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0 := (hS x hx x (mem_ballM_self_loc c x)).2
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht (show x ∈ Function.support (Φ : Matrix (Fin n) (Fin r) k → ℂ) from hx0))
    have hsub : ballM c x ⊆ ballM (cs i) i.1 := by
      rw [← (hball (cs i) i.1).2.2.2.1 x hxi]
      exact ballM_mono_loc (hcci i hi) x
    apply P.smul_mem
    apply hcs i
    intro y hy
    have hy' : y ∈ ballM c x := by
      by_contra hn
      exact hy (by simp [Set.indicator, hn])
    exact ⟨hsub hy', by rw [(hS x hx y hy').1]; exact hx0⟩
  have hΦeq : Φ = ∑ x ∈ S, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x •
      (⟨_, hind x⟩ : SB (Matrix (Fin n) (Fin r) k)) := by
    apply Subtype.ext
    refine hsum.trans ?_
    simp [Submodule.coe_sum, Submodule.coe_smul]
  rw [hΦeq]
  exact P.sum_mem hterm

end PositivityTheory.Rg.Ming
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.PointAveraging.MinkowskiBalls.GermUnique
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3
open scoped Topology Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.Rg.Ming.UniqX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valSet_eq (a : k) (c : kˣ) :
    {y : k | valuation k (y - a) ≤ valuation k (c : k)} = (fun y => -a + y) ⁻¹' (c • (𝒪[k] : Set k)) := by
  ext y
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]; simp
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, Valuation.mem_integer_iff, Units.smul_def,
    Units.val_inv_eq_inv_val, smul_eq_mul, map_mul, map_inv₀, neg_add_eq_sub, inv_mul_le_one₀ hc]

theorem isOpen_valSet (a : k) (c : kˣ) : IsOpen {y : k | valuation k (y - a) ≤ valuation k (c : k)} := by
  rw [valSet_eq]
  exact (Valuation.isOpen_integer.smul c).preimage (continuous_const.add continuous_id)

theorem vol_valSet [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (a : k) (c : kˣ) :
    ν {y : k | valuation k (y - a) ≤ valuation k (c : k)} = ENNReal.ofReal (nabs k c) := by
  obtain ⟨hH, h1⟩ := hν
  haveI := hH
  haveI : SecondCountableTopology k := by exact secondCountable k
  rw [valSet_eq, measure_preimage_add, ← distribHaarChar_mul, h1, mul_one, nabs, ENNReal.ofReal_coe_nnreal]

variable {n r : ℕ}

theorem ballM_eq_pi (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    (ballM c x₀ : Set (Matrix (Fin n) (Fin r) k)) =
      (Set.univ.pi fun i => Set.univ.pi fun l => {y : k | valuation k (y - x₀ i l) ≤ valuation k (c : k)} :
        Set (Fin n → Fin r → k)) := by
  ext x
  simp only [ballM, Set.mem_setOf_eq]
  constructor
  · intro h i _ l _
    exact h i l
  · intro h i l
    exact h i (Set.mem_univ _) l (Set.mem_univ _)

theorem measurableSet_ballM [MeasurableSpace k] [BorelSpace k] (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    MeasurableSet (ballM c x₀) := by
  rw [ballM_eq_pi]
  exact MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun l => (isOpen_valSet _ c).measurableSet

theorem volM_ballM [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) :
    volM ν (Fin n) (Fin r) (ballM c x₀) = ∏ _i : Fin n, ∏ _l : Fin r, ENNReal.ofReal (nabs k c) := by
  obtain ⟨hH, h1⟩ := hν
  haveI := hH
  haveI : SecondCountableTopology k := by exact secondCountable k
  rw [volM, ballM_eq_pi]
  erw [Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.pi_pi]
  exact Finset.prod_congr rfl fun l _ => vol_valSet ν ⟨hH, h1⟩ (x₀ i l) c

theorem volM_ballM_ne_zero [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) : (volM ν (Fin n) (Fin r) (ballM c x₀)).toReal ≠ 0 := by
  have hpos : 0 < nabs k c := by
    unfold nabs
    have h : distribHaarChar k c * distribHaarChar k c⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hne : distribHaarChar k c ≠ 0 := left_ne_zero_of_mul_eq_one h
    exact_mod_cast pos_iff_ne_zero.2 hne
  rw [volM_ballM ν hν, ENNReal.toReal_prod]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [ENNReal.toReal_prod]
  refine Finset.prod_ne_zero_iff.2 fun l _ => ?_
  rw [ENNReal.toReal_ofReal hpos.le]
  exact hpos.ne'

theorem integral_ind [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    ∫ x, (ballM c x₀).indicator (fun _ => (1 : ℂ)) x ∂volM ν (Fin n) (Fin r) =
      ((volM ν (Fin n) (Fin r) (ballM c x₀)).toReal : ℂ) :=
  PositivityTheory.Rg.Ming.GermX.integral_ind ν c x₀

theorem ballM_mono {c c' : kˣ} (hle : valuation k (c : k) ≤ valuation k (c' : k))
    {x₀ : Matrix (Fin n) (Fin r) k} : ballM c x₀ ⊆ ballM c' x₀ :=
  fun _ hx i l => (hx i l).trans hle

theorem exists_le_both (c₁ c₂ : kˣ) :
    ∃ c : kˣ, valuation k (c : k) ≤ valuation k (c₁ : k) ∧ valuation k (c : k) ≤ valuation k (c₂ : k) := by
  rcases le_total (valuation k (c₁ : k)) (valuation k (c₂ : k)) with h | h
  · exact ⟨c₁, le_rfl, h⟩
  · exact ⟨c₂, h, le_rfl⟩

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem germ_zero [MeasurableSpace k] (ν : Measure k) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V)
    (x₀ : Matrix (Fin n) (Fin r) k) : IsGerm ν B x₀ 0 0 :=
  ⟨1, fun Φ _ => by simp⟩

theorem germ_comb [MeasurableSpace k] (ν : Measure k) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V)
    (x₀ : Matrix (Fin n) (Fin r) k) (a : ℂ) {w₁ w₂ : W} {v₁ v₂ : V}
    (h₁ : IsGerm ν B x₀ w₁ v₁) (h₂ : IsGerm ν B x₀ w₂ v₂) : IsGerm ν B x₀ (a • w₁ + w₂) (a • v₁ + v₂) := by
  obtain ⟨c₁, e₁⟩ := h₁
  obtain ⟨c₂, e₂⟩ := h₂
  obtain ⟨c, hc₁, hc₂⟩ := exists_le_both c₁ c₂
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [map_add (f := _), map_smul, e₁ Φ (fun x hx => ballM_mono hc₁ (hΦ x hx)),
    e₂ Φ (fun x hx => ballM_mono hc₂ (hΦ x hx)), smul_add, smul_comm a]

theorem germ_unique (hb : BallSt) [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν)
    (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) (x₀ : Matrix (Fin n) (Fin r) k) {w : W} {v₁ v₂ : V}
    (h₁ : IsGerm ν B x₀ w v₁) (h₂ : IsGerm ν B x₀ w v₂) : v₁ = v₂ := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  obtain ⟨c, hle₁, hle₂⟩ := exists_le_both c₁ c₂
  let Φ : SB (Matrix (Fin n) (Fin r) k) :=
    ⟨(ballM c x₀).indicator fun _ => (1 : ℂ), ((hb k n r).1 c x₀).2.2.1⟩
  have hsupp : ∀ x, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0 → x ∈ ballM c x₀ := by
    intro x hx
    by_contra h
    exact hx (by simp [Φ, Set.indicator, h])
  have e₁ := hc₁ Φ fun x hx => ballM_mono hle₁ (hsupp x hx)
  have e₂ := hc₂ Φ fun x hx => ballM_mono hle₂ (hsupp x hx)
  have hI : (∫ x, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ∂volM ν (Fin n) (Fin r)) ≠ 0 := by
    change (∫ x, (ballM c x₀).indicator (fun _ => (1 : ℂ)) x ∂volM ν (Fin n) (Fin r)) ≠ 0
    rw [integral_ind]
    exact Complex.ofReal_ne_zero.2 (volM_ballM_ne_zero ν hν c x₀)
  exact smul_right_injective V hI (e₁.symm.trans e₂)

end PositivityTheory.Rg.Ming.UniqX

namespace PositivityTheory.Rg.Ming

open PositivityTheory.Rg.Ming.UniqX in
theorem uniq : BallSt → UniqSt := by
  intro hb
  unfold UniqSt
  intro k _ _ _ _ _ _ ν hν n r V _ _ W _ _ B x₀ hex
  choose f hf using hex
  have hadd : ∀ w₁ w₂ : W, f (w₁ + w₂) = f w₁ + f w₂ := by
    intro w₁ w₂
    have h := germ_comb ν B x₀ 1 (hf w₁) (hf w₂)
    rw [one_smul, one_smul] at h
    exact germ_unique hb ν hν B x₀ (hf (w₁ + w₂)) h
  have hsmul : ∀ (a : ℂ) (w : W), f (a • w) = a • f w := by
    intro a w
    have h := germ_comb ν B x₀ a (hf w) (germ_zero ν B x₀)
    rw [add_zero, add_zero] at h
    exact germ_unique hb ν hν B x₀ (hf (a • w)) h
  refine ⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul }, fun w v => ?_⟩
  constructor
  · intro h
    exact germ_unique hb ν hν B x₀ h (hf w)
  · rintro rfl
    exact hf w

end PositivityTheory.Rg.Ming

end
end

open MeasureTheory GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel PositivityTheory.Tls2.Ming3 PositivityTheory.Rg.Ming
open scoped TensorProduct

namespace UpperTheory.Lit.HoweDuality

theorem lift_of_irr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ)
    (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W) (hrt : r < t)
    (hμs : IsSmoothChar μ) (hμu : IsUnitaryChar μ) (hσu : IsUnitarisable σ) (hπs : IsSmooth π) (hπi : π.IsIrreducible)
    (hIi : (prod₂ σ (detRep (Fin t) μ)).IsIrreducible) (hθ : ThetaPair μ σ π) :
    Nonempty (π.Equiv (prod₂ σ (detRep (Fin t) μ))) := by
  have hstep := step ball (loc ball) nf rk (core ball rk)
  have hgerm := germ ball
  have huniq := uniq ball
  have hnz := nz ball (loc ball) nf
  have hlaw := law ball cov
  obtain ⟨B, hB0, hE⟩ := hθ
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.Model.exists_isUnitVol (k := k)
  have down : ∀ j, j ≤ r → VanRk B j → VanRk B 0 := fun j => by
    induction j with
    | zero => exact fun _ h => h
    | succ j ih => exact fun hj h => ih (by omega) (hstep k (r + t) r μ V W σ π B j (by omega) (by omega) hμu hσu hE h)
  obtain ⟨ev, hev⟩ := huniq k ν hν (r + t) r V W B _ (hgerm k ν hν r t μ V W σ π B hμs hπs hE)
  have hev0 : ev ≠ 0 := fun e => hB0 (LinearMap.ext fun Φ => down r le_rfl
    (hnz k ν hν r t μ V W σ π B hE fun w => (hev w 0).2 (by rw [e]; rfl)) Φ fun _ h => absurd h (Nat.not_lt_zero _))
  obtain ⟨f, hf⟩ := frob k r t μ V W σ π ev hπs hev0 (hlaw k ν hν r t μ V W σ π B hE ev hev)
  haveI := hπi
  haveI := hIi
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with h | h
  · exact ⟨.mk (LinearEquiv.ofBijective f.toLinearMap h) f.isIntertwining'⟩
  · exact absurd (by rw [h]; rfl) hf

end UpperTheory.Lit.HoweDuality
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGeneralLinearStatement
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct
namespace GlobalTheory.ThetaLiftGL
abbrev _root_.GlobalTheory.ThetaLiftGL.ThetaLiftGeneralLinearStatement : Prop :=  BernsteinZelevinskyFiniteness → BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ)
    (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W), r < t →
    IsSmoothChar μ → IsUnitaryChar μ → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmooth π →
    π.IsIrreducible → ThetaPair μ σ π → Nonempty (π.Equiv (prod₂ σ (detRep (Fin t) μ)))
end GlobalTheory.ThetaLiftGL
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlThetaLiftIsClosed
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGlOfZelevinskyClassification
section
open MeasureTheory GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published ValuativeRel PositivityTheory.Tls2.Ming3 PositivityTheory.Rg.Ming
open scoped TensorProduct
namespace UpperTheory.Lit.HoweDuality
theorem thetaLift_gl_of_zelevinsky_classification (hZ : ZelevinskyPolynomialRing) : _root_.GlobalTheory.ThetaLiftGL.ThetaLiftGeneralLinearStatement :=
  fun hBZ _ k _ _ _ _ r t μ V _ _ W _ _ σ π hrt hμs hμu hσs hσi hσu hπs hπi hθ =>
    lift_of_irr k r t μ V W σ π hrt hμs hμu hσu hπs hπi
      (UpperTheory.Lit.Mix.top (GlobalTheory.geometricLemma_of_filtration hBZ GlobalTheory.geometricLemmaFiltration_unconditional) hBZ hZ
        k r t V σ μ hrt hσs hσi hσu hμs hμu) hθ
end UpperTheory.Lit.HoweDuality
end
end

section
namespace UpperTheory.Lit.Mix
theorem gl_thetaLift_isClosed : _root_.GlobalTheory.ThetaLiftGL.ThetaLiftGeneralLinearStatement := _root_.UpperTheory.Lit.HoweDuality.thetaLift_gl_of_zelevinsky_classification polynomialRing
end UpperTheory.Lit.Mix
end
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_general_linear : BernsteinZelevinskyFiniteness → BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W), r < t → IsSmoothChar μ → IsUnitaryChar μ → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmooth π → π.IsIrreducible → ThetaPair μ σ π → Nonempty (π.Equiv (prod₂ σ (detRep (Fin t) μ))) := by
  first | exact @_root_.UpperTheory.Lit.Mix.gl_thetaLift_isClosed | exact _root_.UpperTheory.Lit.Mix.gl_thetaLift_isClosed | (intros; apply _root_.UpperTheory.Lit.Mix.gl_thetaLift_isClosed <;> assumption)
end
