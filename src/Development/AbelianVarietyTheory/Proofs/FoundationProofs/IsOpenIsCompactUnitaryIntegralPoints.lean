module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivationProdPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.IntPtsUnitary

section General
variable {L : Type} [Field L] [TopologicalSpace L] [IsTopologicalRing L] {n : Type} [Fintype n] [DecidableEq n]

omit [TopologicalSpace L] [IsTopologicalRing L] in
theorem coe_GLint (O : Subring L) : (GLint n O : Set (GL n L)) =
    {g : GL n L | ∀ i j, (g : Matrix n n L) i j ∈ O} ∩ {g : GL n L | ∀ i j, ((g⁻¹ : GL n L) : Matrix n n L) i j ∈ O} :=
  Set.ext fun g => ⟨fun h => ⟨P.cartan_entries_of_mem O g h, P.cartan_entries_of_mem O _ (inv_mem h)⟩,
    fun h => P.cartan_mem_of_entries O g h.1 h.2⟩

theorem isOpen_GLint (O : Subring L) (hO : IsOpen (O : Set L)) : IsOpen (GLint n O : Set (GL n L)) := by
  rw [coe_GLint]
  simp only [Set.ofPred_forall]
  refine IsOpen.inter ?_ ?_
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (Units.continuous_val.matrix_elem i j)
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (Units.continuous_coe_inv.matrix_elem i j)

theorem isCompact_GLint [T2Space L] (O : Subring L) (hO : IsCompact (O : Set L)) :
    IsCompact (GLint n O : Set (GL n L)) := by
  have hM : IsCompact {A : Matrix n n L | ∀ i j, A i j ∈ O} := by
    have := isCompact_univ_pi fun _ : n => isCompact_univ_pi fun _ : n => hO
    have e : {A : Matrix n n L | ∀ i j, A i j ∈ O} =
        Set.univ.pi fun _ : n => Set.univ.pi fun _ : n => (O : Set L) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ this
  have := (Units.isClosedEmbedding_embedProduct (α := Matrix n n L)).isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))
  convert this using 1
  rw [coe_GLint]
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL n L) : Matrix n n L) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

end General

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isCompact_intL [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    IsCompact (intL L : Set L) := by
  obtain ⟨-, -, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  exact isCompact_iff_compactSpace.2 hp

theorem coe_KU (σ : L →+* L) (n : ℕ) :
    (KU σ n : Set (GU σ n)) = Subtype.val ⁻¹' (GLint (Fin n) (intL L) : Set (GL (Fin n) L)) := by
  ext g
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem isOpen_isCompact_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q →
      IsOpen (KU σ n : Set (GU σ n)) ∧ IsCompact (KU σ n : Set (GU σ n)) := by
  intro L _ _ _ ϖ σ q n h
  rw [coe_KU]
  refine ⟨(isOpen_GLint _ (Valued.isOpen_integer L)).preimage continuous_subtype_val, ?_⟩
  have hc : IsClosed (GU σ n : Set (GL (Fin n) L)) :=
    isClosed_eq (((Units.continuous_val.matrix_map (GlobalTheory.LGrp.continuous_of_unramInv h)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul Units.continuous_val) continuous_const
  exact hc.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_GLint _ (isCompact_intL h))

end GlobalTheory.LFun.IntPtsUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPointsStatement
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → IsOpen (KU σ n : Set (GU σ n)) ∧ IsCompact (KU σ n : Set (GU σ n)) := by
  first | exact @GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU | exact GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU | (intros; apply GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaMemHighestWeightSecond
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaMemHighestWeightSecond
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm GlobalTheory.JointHarm.Minor

namespace GlobalTheory.DeltaHighest

def ext0 {l : ℕ} (a : Fin l → ℕ) (i : ℕ) : ℕ := if h : i < l then a ⟨i, h⟩ else 0

theorem partitionExtendByZero_antitone {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) : Antitone (ext0 a) := by
  intro i j hij
  unfold ext0
  split_ifs with h h'
  · exact ha (by simpa using hij)
  · omega
  · omega
  · omega

def leadProd {σ : Type} {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) (z : Fin n × Fin l → σ) :
    MvPolynomial σ ℂ :=
  ∏ i : Fin l, lead z (n := i.1 + 1) (le_trans i.2 h) i.2 ^ (ext0 a i - ext0 a (i + 1))

theorem partition_row_difference_eq_extendByZero_difference {l : ℕ} (a : Fin l → ℕ) (i : Fin l) :
    a i - nextRow a i = ext0 a i - ext0 a (i + 1) := by
  simp [ext0, nextRow]

theorem leadProd_rows {σ : Type} {n l : ℕ} (h : l ≤ n) {a : Fin l → ℕ} (ha : Antitone a)
    (z : Fin n × Fin l → σ) (hz : Function.Injective z) :
    (∀ c d : Fin n, c < d → rowDer z c d (leadProd h a z) = 0) ∧
      ∀ c : Fin n, rowDer z c c (leadProd h a z) = (ext0 a c : ℂ) • leadProd h a z := by
  have := what₂ z hz (ext0 a) (partitionExtendByZero_antitone ha) l (fun i hi => dif_neg (by omega))
    (fun i => le_trans i.2 h) (fun i => i.2)
  simpa only [rowOp_eq_rowDer, leadProd] using this

theorem leadProd_kill {σ : Type} {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) (z : Fin n × Fin l → σ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (hD : ∀ w, D (X (z w)) = 0) :
    D (leadProd h a z) = 0 := by
  rw [leadProd, derivation_prod_pow D _ _ _ (fun _ => 0)]
  · simp
  · intro i
    rw [zero_smul, lead, derivation_det]
    refine Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [Matrix.updateRow_self]
    exact hD _

theorem rowDer_X_other {σ : Type} {n l : ℕ} (z : Fin n × Fin l → σ) (c d : Fin n) (v : σ)
    (hv : ∀ w, z w ≠ v) : rowDer z c d (X v) = 0 := by
  classical
  rw [← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pderiv_X_of_ne (hv _).symm, mul_zero]

variable (p q n : ℕ)

def vp : Fin n × Fin p → Ln p q n 0 := fun w => (Sum.inl w.2, Sum.inl w.1)

def vm : Fin n × Fin q → Ln p q n 0 := fun w => (Sum.inr w.2, Sum.inl w.1.rev)

theorem vp_inj : Function.Injective (vp p q n) := fun u w h => by
  simpa [vp, Prod.ext_iff, and_comm] using h

theorem vm_inj : Function.Injective (vm p q n) := fun u w h => by
  simpa [vm, Prod.ext_iff, and_comm] using h

theorem top_eq (h : p ≤ n) (a : Fin p → ℕ) :
    minorProd a (zPlus p q n) (topRows h) = leadProd h a (vp p q n) := by
  unfold minorProd leadProd
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [partition_row_difference_eq_extendByZero_difference]
  rfl

theorem bot_eq (h : q ≤ n) (a : Fin q → ℕ) :
    ∃ u : ℂ, minorProd a (zMinus p q n) (botRows h) = u • leadProd h a (vm p q n) := by
  refine ⟨∏ i : Fin q, ((Equiv.Perm.sign (Fin.revPerm (n := i.1 + 1)) : ℤ) : ℂ) ^
    (ext0 a i - ext0 a (i + 1)), ?_⟩
  unfold minorProd leadProd
  rw [Algebra.smul_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [partition_row_difference_eq_extendByZero_difference, map_pow, ← mul_pow, map_intCast, lead, ← Matrix.det_permute]
  congr 2
  ext1 c b
  simp only [zMinus, vm, Matrix.submatrix_apply, Matrix.of_apply, id]
  congr 3
  apply Fin.ext
  have := i.2
  have := c.2
  simp [botRows, Fin.revPerm, Fin.val_rev]
  omega

theorem act_eq (c d : Fin n) (P : Pol p q n 0) :
    fockAct2 p q n 0 (Eab (.inl c) (.inl d)) P =
      rowDer (vp p q n) c d P - rowDer (vm p q n) d.rev c.rev P +
        (if c = d then ((p : ℂ) - q) / 2 else 0) • P := by
  rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, ← rowOp_eq_rowDer,
    ← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply, GlobalTheory.Capelli.rowOp_apply]
  simp only [omE_pos_pos (l := (.inl _, .inl c)) (l' := (.inl _, .inl d)) rfl rfl,
    omE_neg_neg (l := (.inr _, .inl c)) (l' := (.inr _, .inl d)) rfl rfl, vp, vm, Fin.rev_rev,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_smul]
  by_cases h : c = d <;> simp [h] <;> module

theorem delta_mem_hwSub : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ),
    Antitone ap → Antitone am → delta hn ap am ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) := by
  intro p q n hn ap am hp hm
  have h1 : p ≤ n := by omega
  have h2 : q ≤ n := by omega
  obtain ⟨u, hu⟩ := bot_eq p q n h2 am
  have e : delta hn ap am = u • (leadProd h1 ap (vp p q n) * leadProd h2 am (vm p q n)) := by
    rw [delta, top_eq, hu, mul_smul_comm]
  rw [e]
  refine Submodule.smul_mem _ _ ?_
  have a1 := leadProd_rows h1 hp _ (vp_inj p q n)
  have a2 := leadProd_rows h2 hm _ (vm_inj p q n)
  have k1 : ∀ c d, rowDer (vp p q n) c d (leadProd h2 am (vm p q n)) = 0 := fun c d =>
    leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]
  have k2 : ∀ c d, rowDer (vm p q n) c d (leadProd h1 ap (vp p q n)) = 0 := fun c d =>
    leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, Sum.forall,
    posC, IsEmpty.forall_iff, implies_true, and_true, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, act_eq, Derivation.leibniz, k1, k2, a1.2, a2.2, if_true]
  refine ⟨fun c => ?_, fun c d hcd => ?_⟩
  · have hw : ((wtH n ap am (.inl c) : ℚ) : ℂ) =
        (ext0 ap c : ℂ) - (ext0 am c.rev : ℂ) + ((p : ℂ) - q) / 2 := by
      have := c.2
      have hr := c.val_rev
      simp only [wtH, ext0]
      split_ifs with h h' h'
      · omega
      all_goals simp
    rw [hw]
    generalize leadProd h1 ap (vp p q n) = A
    generalize leadProd h2 am (vm p q n) = B
    simp only [mul_zero, zero_add, add_zero, smul_eq_mul, mul_smul_comm, mul_comm B A]
    module
  · rw [a1.1 c d hcd, a2.1 _ _ (Fin.rev_lt_rev.2 hcd), if_neg hcd.ne]
    simp

end GlobalTheory.DeltaHighest

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaMemHighestWeightSecondStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicMinorProductDelta_mem_highestWeight_second : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) := by
  first | exact @GlobalTheory.DeltaHighest.delta_mem_hwSub | exact GlobalTheory.DeltaHighest.delta_mem_hwSub | (intros; apply GlobalTheory.DeltaHighest.delta_mem_hwSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaExtremalFirstMember
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaExtremalFirstMember
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockMinorExtremal

open MvPolynomial GlobalTheory.JointHarm GlobalTheory.JointHarm.Minor GlobalTheory.Capelli

section General

variable {A : Type} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A) {n l : ℕ}
  (y : Matrix (Fin n) (Fin l) A)

theorem der_minor {a b : Fin l} (hab : a ≤ b) (hD : ∀ c k, D (y c k) = if k = b then y c a else 0)
    {m : ℕ} (row : Fin m → Fin n) (h : m ≤ l) :
    D (y.submatrix row (Fin.castLE h)).det =
      (if a = b then (if a.1 < m then (1 : ℂ) else 0) else 0) • (y.submatrix row (Fin.castLE h)).det := by
  rw [← Matrix.det_transpose, derivation_det]
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, hD]
  by_cases hb : b.1 < m
  · rw [Finset.sum_eq_single (⟨b.1, hb⟩ : Fin m)]
    · have e : Fin.castLE h ⟨b.1, hb⟩ = b := rfl
      simp only [e, if_true]
      split_ifs with h1 h2
      · subst h1
        rw [one_smul]
        congr 1
        exact Matrix.updateRow_eq_self _ _
      · exact absurd (h1 ▸ hb) h2
      · have hlt : a.1 < b.1 := lt_of_le_of_ne hab fun e => h1 (Fin.ext e)
        have hne : (⟨a.1, hlt.trans hb⟩ : Fin m) ≠ ⟨b.1, hb⟩ := fun e => by
          rw [Fin.ext_iff] at e; simp at e; omega
        rw [zero_smul]
        refine Matrix.det_zero_of_row_eq hne ?_
        rw [Matrix.updateRow_self, Matrix.updateRow_ne hne]
        rfl
    · intro i _ hi
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      rw [Matrix.updateRow_self, if_neg fun e : Fin.castLE h i = b => hi (Fin.ext (congrArg Fin.val e :))]
    · simp
  · have h0 : (if a = b then (if a.1 < m then (1 : ℂ) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exact absurd (h1 ▸ h2) hb
      · rfl
      · rfl
    rw [h0, zero_smul]
    refine Finset.sum_eq_zero fun i _ => Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [Matrix.updateRow_self, if_neg fun e : Fin.castLE h i = b => hb (e ▸ i.2)]

theorem sum_rows (α : Fin l → ℕ) (hα : Antitone α) (a : Fin l) :
    ∑ i : Fin l, ((α i - nextRow α i : ℕ) : ℂ) * (if a.1 < i.1 + 1 then 1 else 0) = α a := by
  let f : ℕ → ℕ := fun i => if h : i < l then α ⟨i, h⟩ else 0
  have hf : Antitone f := by
    refine antitone_nat_of_succ_le fun i => ?_
    simp only [f]
    split_ifs with h1 h2 h2
    · exact hα (by simp [Fin.le_def])
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have h := telescope f hf a l
  have hl : f l = 0 := by simp [f]
  rw [if_pos a.2.le, hl, ← Fin.sum_univ_eq_sum_range
    (fun i => ((f i - f (i + 1) : ℕ) : ℂ) * (if a.1 < i + 1 then 1 else 0))] at h
  have e1 : ∀ i : Fin l, f i = α i := fun i => by simp [f, i.2]
  have e2 : ∀ i : Fin l, f (i + 1) = nextRow α i := fun i => rfl
  simpa only [e1, e2, Nat.cast_zero, sub_zero] using h

theorem der_minorProd (α : Fin l → ℕ) (hα : Antitone α) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n)
    {a b : Fin l} (hab : a ≤ b) (hD : ∀ c k, D (y c k) = if k = b then y c a else 0) :
    D (minorProd α y row) = (if a = b then (α a : ℂ) else 0) • minorProd α y row := by
  rw [minorProd, derivation_prod_pow D _ _ _ _ fun i => der_minor D y hab hD (row i) i.2]
  congr 1
  split_ifs with h
  · exact sum_rows α hα a
  · simp

theorem der_minorProd_zero (α : Fin l → ℕ) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n)
    (hD : ∀ i c k, D (y (row i c) k) = 0) : D (minorProd α y row) = 0 := by
  rw [minorProd, derivation_prod_pow D _ _ _ (fun _ => 0) fun i => ?_]
  · simp
  · rw [zero_smul, derivation_det]
    refine Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [Matrix.updateRow_self, Matrix.submatrix_apply, hD]

end General

theorem minorProd_ne_zero {σ : Type} {n l : ℕ} (z : Fin n × Fin l → σ) (hz : Function.Injective z)
    (α : Fin l → ℕ) (row : ∀ i : Fin l, Fin (i.1 + 1) → Fin n) (hrow : ∀ i, Function.Injective (row i)) :
    minorProd α (Matrix.of fun c k => (X (z (c, k)) : MvPolynomial σ ℂ)) row ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _
    (lead_ne_zero (fun w : Fin (i.1 + 1) × Fin l => z (row i w.1, w.2))
      (hz.comp ((hrow i).prodMap Function.injective_id)) le_rfl i.2)

variable {p q n : ℕ}

def vPlus (p q n : ℕ) : Fin p × Fin n → Ln p q n 0 := fun w => (.inl w.1, .inl w.2)

def vMinus (p q n : ℕ) : Fin q × Fin n → Ln p q n 0 := fun w => (.inr w.1, .inl w.2)

theorem vPlus_inj : Function.Injective (vPlus p q n) := fun u w h => by
  simpa [vPlus, Prod.ext_iff] using h

theorem vMinus_inj : Function.Injective (vMinus p q n) := fun u w h => by
  simpa [vMinus, Prod.ext_iff] using h

theorem act_plus (i j : Fin p) (P : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (.inl i) (.inl j)) P =
      rowDer (vPlus p q n) i j P + (if i = j then (n : ℂ) / 2 else 0) • P := by
  rw [isSide_one.1, mixedOp_apply, ← rowOp_eq_rowDer, rowOp_apply]
  simp [zA, vPlus, cPair]

theorem act_minus (i j : Fin q) (P : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (.inr j) (.inr i)) P =
      -rowDer (vMinus p q n) i j P - (if i = j then (n : ℂ) / 2 else 0) • P := by
  rw [isSide_one.2, mixedOp_apply, ← rowOp_eq_rowDer, rowOp_apply]
  simp [zD, vMinus, cPair, eq_comm]

theorem der_plus (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (hp : Antitone ap) {i j : Fin p}
    (hij : i ≤ j) :
    rowDer (vPlus p q n) i j (delta hn ap am) = (if i = j then (ap i : ℂ) else 0) • delta hn ap am := by
  rw [delta, Derivation.leibniz, der_minorProd _ (zPlus p q n) ap hp _ hij
    fun c k => rowDer_X _ vPlus_inj i j k c, der_minorProd_zero _ (zMinus p q n) am _ fun _ c k => ?_]
  · simp [mul_comm]
  · rw [← rowOp_eq_rowDer, rowOp_apply]
    simp [zMinus, vPlus, pderiv_X, Pi.single_apply]

theorem der_minus (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (hm : Antitone am) {i j : Fin q}
    (hij : i ≤ j) :
    rowDer (vMinus p q n) i j (delta hn ap am) = (if i = j then (am i : ℂ) else 0) • delta hn ap am := by
  rw [delta, Derivation.leibniz, der_minorProd _ (zMinus p q n) am hm _ hij
    fun c k => rowDer_X _ vMinus_inj i j k c, der_minorProd_zero _ (zPlus p q n) ap _ fun _ c k => ?_]
  · simp
  · rw [← rowOp_eq_rowDer, rowOp_apply]
    simp [zPlus, vMinus, pderiv_X, Pi.single_apply]

theorem lower (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) :
    KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  intro a b
  rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero, GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.lowerOp]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h1 : pderiv ((.inr b, .inl c) : Ln p q n 0) (minorProd ap (zPlus p q n) (topRows (by omega))) = 0 :=
    der_minorProd_zero _ _ _ _ fun _ _ _ => pderiv_X_of_ne (by simp)
  have h2 : pderiv ((.inl a, .inl c) : Ln p q n 0) (minorProd am (zMinus p q n) (botRows (by omega))) = 0 :=
    der_minorProd_zero _ _ _ _ fun _ _ _ => pderiv_X_of_ne (by simp)
  rw [delta, Derivation.leibniz, h1, smul_zero, add_zero, smul_eq_mul, Derivation.leibniz, pderiv_swap, h2,
    map_zero, smul_zero, zero_add, smul_eq_mul]
  by_cases hc : c.1 < p
  · rw [der_minorProd_zero (pderiv ((.inr b, .inl c) : Ln p q n 0)) (zMinus p q n) am (botRows (by omega))
      fun i d _ => pderiv_X_of_ne ?_,
      zero_mul]
    have := i.2
    simp only [botRows, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega
  · rw [der_minorProd_zero (pderiv ((.inl a, .inl c) : Ln p q n 0)) (zPlus p q n) ap (topRows (by omega))
      fun i d _ => pderiv_X_of_ne ?_,
      mul_zero]
    have := i.2
    have := d.2
    simp only [topRows, ne_eq, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
    omega

theorem delta_extremal : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ≠ 0 ∧ delta hn ap am ∈ wtSub (fockAct1 p q n 0) (wtExt n ap am) ∧ (∀ i j : Fin p, i < j → fockAct1 p q n 0 (Eab (Sum.inl i) (Sum.inl j)) (delta hn ap am) = 0) ∧ (∀ i j : Fin q, i < j → fockAct1 p q n 0 (Eab (Sum.inr j) (Sum.inr i)) (delta hn ap am) = 0) ∧ KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  intro p q n hn ap am hp hm
  refine ⟨mul_ne_zero ?_ ?_, ?_, fun i j h => ?_, fun i j h => ?_, lower hn ap am⟩
  · exact minorProd_ne_zero (fun w => vPlus p q n w.swap) (vPlus_inj.comp Prod.swap_injective) ap _
      fun i c d h => by simpa [topRows, Fin.ext_iff] using h
  · exact minorProd_ne_zero (fun w => vMinus p q n w.swap) (vMinus_inj.comp Prod.swap_injective) am _
      fun i c d h => by simpa [botRows, Fin.ext_iff] using h
  · simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Sum.forall, sub_eq_zero]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [act_plus, der_plus hn ap am hp le_rfl]
      simp [wtExt, add_smul]
    · rw [act_minus, der_minus hn ap am hm le_rfl]
      simp [wtExt, sub_smul]
  · rw [act_plus, der_plus hn ap am hp h.le]
    simp [h.ne]
  · rw [act_minus, der_minus hn ap am hm h.le]
    simp [h.ne]

end GlobalTheory.FockMinorExtremal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaExtremalFirstMemberStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicMinorProductDelta_extremal_first_member : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ≠ 0 ∧ delta hn ap am ∈ wtSub (fockAct1 p q n 0) (wtExt n ap am) ∧ (∀ i j : Fin p, i < j → fockAct1 p q n 0 (Eab (Sum.inl i) (Sum.inl j)) (delta hn ap am) = 0) ∧ (∀ i j : Fin q, i < j → fockAct1 p q n 0 (Eab (Sum.inr j) (Sum.inr i)) (delta hn ap am) = 0) ∧ KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  first | exact @GlobalTheory.FockMinorExtremal.delta_extremal | exact GlobalTheory.FockMinorExtremal.delta_extremal | (intros; apply GlobalTheory.FockMinorExtremal.delta_extremal <;> assumption)
end
end
