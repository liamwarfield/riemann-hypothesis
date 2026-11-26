module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqRankOneFactorSL2OfGeometricOnShells
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTri
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedOfHasGoodReduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingTermCoefEqResidueCardZpow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThreeRankOneSphericalVectorCellValue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningLastEven
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem chiDeltaU_congr {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n m : ℕ}
    (q : ℕ) (α : Fin m → ℂ) (b c : GU σ n)
    (h : ∀ i, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) :
    chiDeltaU q α b = chiDeltaU q α c := by
  unfold chiDeltaU
  simp only [h]

end GlobalTheory.WeylCell.RankOneUnitary

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem ordL_of_v_eq {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (x : L) (z : ℤ)
    (hx : Valued.v x = ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) : ordL x = -z := by
  unfold ordL
  have h0 : Valued.v x ≠ 0 := by rw [hx]; exact WithZero.coe_ne_zero
  rw [dite_eq_right h0]
  have : WithZero.unzero h0 = Multiplicative.ofAdd z := by
    apply WithZero.coe_injective; rw [WithZero.coe_unzero, hx]
  rw [this]; rfl

end GlobalTheory.WeylCell.RankOneUnitary

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylSimpleReflectionRevCommSqEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylSimpleReflectionRevCommSqEqOne
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory

theorem simpleU_rev_and_sq : ∀ (n : ℕ) (k : Fin (n / 2)), (∀ i, simpleU k i.rev = (simpleU k i).rev) ∧ simpleU k * simpleU k = 1 := by
  intro n k
  have hk := k.isLt
  have hn : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  unfold simpleU partnerU
  split_ifs with h
  · refine ⟨fun i => ?_, ?_⟩
    · have hi := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs at * <;> simp only [Fin.ext_iff, Fin.val_rev, lo, Fin.coe_castLE] at * <;> omega
    · have hnd : [lo k, lo (⟨k.val + 1, h⟩ : Fin (n / 2)), (lo k).rev,
          (lo (⟨k.val + 1, h⟩ : Fin (n / 2))).rev].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
          and_true, Fin.ext_iff, Fin.val_rev, lo, Fin.coe_castLE, not_false_eq_true]
        omega
      have hc := (Equiv.Perm.disjoint_swap_swap hnd).commute
      rw [hc.symm.mul_mul_mul_comm, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  · refine ⟨fun i => ?_, Equiv.swap_mul_self _ _⟩
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, lo] <;> omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylSimpleReflectionRevCommSqEqOneStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryWeylSimpleReflection_rev_comm_sq_eq_one : ∀ (n : ℕ) (k : Fin (n / 2)), (∀ i, simpleU k i.rev = (simpleU k i).rev) ∧ simpleU k * simpleU k = 1 := by
  first | exact @GlobalTheory.simpleU_rev_and_sq | exact GlobalTheory.simpleU_rev_and_sq | (intros; apply GlobalTheory.simpleU_rev_and_sq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShellMeasure
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.InvStep

open GlobalTheory.ShellU GlobalTheory.GKConjScale GlobalTheory.UnipShiftU

private theorem weylRep_inv_mul_diag_local {L : Type} [Field L] {n : ℕ}
    {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (p : Fin n) :
    (Units.val x⁻¹) p (w p) * (Units.val x) (w p) p = 1 := by
  have h : (Units.val (x⁻¹ * x)) p p = (Units.val (1 : GL (Fin n) L)) p p := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)] at h

private theorem weylRep_inv_local {L : Type} [Field L] {n : ℕ}
    {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) :
    IsWeylRep w⁻¹ x⁻¹ := by
  intro p a hpa
  have hne : (Units.val x) a (w⁻¹ a) ≠ 0 := by
    intro h0
    have h : (Units.val (x * x⁻¹)) a a = (Units.val (1 : GL (Fin n) L)) a a := by rw [mul_inv_cancel]
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
    rw [Finset.sum_eq_single (w⁻¹ a) (fun b _ hb => by
      rw [hx a b (fun e => hb (w.injective (by simpa using e)).symm), zero_mul]) (by simp),
      h0, zero_mul] at h
    exact zero_ne_one h
  have h : (Units.val (x⁻¹ * x)) p (w⁻¹ a) = (Units.val (1 : GL (Fin n) L)) p (w⁻¹ a) := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa] at h
  rw [Finset.sum_eq_single a (fun b _ hb => by
      rw [hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)] at h
  exact (mul_eq_zero.1 h).resolve_right hne

private theorem weylRep_conj_apply_local {L : Type} [Field L] {n : ℕ}
    {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (u : GL (Fin n) L)
    (p q : Fin n) : (Units.val (x⁻¹ * u * x)) p q =
      (Units.val x⁻¹) p (w p) * (Units.val u) (w p) (w q) * (Units.val x) (w q) q := by
  have hi := weylRep_inv_local hx
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q)
    (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply,
    Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]

theorem shell_measure' : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 →
    Even n → ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
    μ ((KU σ n).subgroupOf (cellU y)) = 1 → ∀ (j : ℤ),
    MeasurableSet {u : cellU y | Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤
        ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ))} ∧
    μ {u : cellU y | Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤
        ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ))} = (q : ENNReal) ^ j := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hyK hy _ _ μ _ hμ j
  have hidx := relIndex_antiBall hU
  obtain ⟨-, -, -, hv, -, hq2, -⟩ := hU
  have haa : lo k ≠ (lo k).rev := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev, Fin.val_castLE] at this
    have := k.2
    omega
  have hshape := cellU_rankOne_shape L σ n k hk hn y hy
  set a := lo k with ha
  let M : cellU y → Matrix (Fin n) (Fin n) L := fun u => (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  let c : cellU y → L := fun u => M u a a.rev
  have hstr : ∀ u : cellU y, M u = 1 + Matrix.single a a.rev (c u) := by
    intro u
    ext i l
    rw [Matrix.add_apply, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.one_apply_ne haa, zero_add]
    · rw [add_zero]
      exact (hshape u).1 u.2 i l (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)
  have hprod : ∀ b d : L, (1 + Matrix.single a a.rev b) * (1 + Matrix.single a a.rev d) =
      1 + Matrix.single a a.rev (b + d) := by
    intro b d
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.single_mul_single_of_ne _ _ _ _ haa.symm,
      Matrix.single_add]
    simp only [Matrix.one_mul, Matrix.mul_one, add_zero]
    abel
  have hent : ∀ b : L, (1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) a a.rev = b := by
    intro b
    rw [Matrix.add_apply, Matrix.one_apply_ne haa, Matrix.single_apply_same, zero_add]
  have hM : ∀ u w : cellU y, M (u * w) = M u * M w := fun u w => rfl
  have hmul : ∀ u w : cellU y, c (u * w) = c u + c w := by
    intro u w
    show M (u * w) a a.rev = c u + c w
    rw [hM, hstr u, hstr w, hprod, hent]
  have hone : c 1 = 0 := Matrix.one_apply_ne haa
  have hinv : ∀ u, c u⁻¹ = -c u := fun u => by
    have := hmul u⁻¹ u
    rw [inv_mul_cancel, hone] at this
    linear_combination -this
  have hanti : ∀ u, σ (c u) = -c u := fun u => by
    have := (LGrp.mem_GU_iff σ n _).1 (u : GU σ n).2 a a.rev
    rw [Fin.rev_rev] at this
    rw [← hinv]
    exact this.symm
  have hsurj : ∀ b : L, σ b = -b → ∃ u : cellU y, c u = b := by
    intro b hb
    let g : GL (Fin n) L := ⟨1 + Matrix.single a a.rev b, 1 + Matrix.single a a.rev (-b),
      by rw [hprod]; simp, by rw [hprod]; simp⟩
    have hg : g ∈ GU σ n := by
      rw [LGrp.mem_GU_iff]
      intro i l
      show (1 + Matrix.single a a.rev (-b) : Matrix (Fin n) (Fin n) L) i l =
        σ ((1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) l.rev i.rev)
      rw [Matrix.add_apply, Matrix.add_apply, map_add (f := _), Matrix.one_apply, Matrix.one_apply, Matrix.single_apply,
        Matrix.single_apply, apply_ite σ, apply_ite σ, map_one, map_zero, hb]
      congr 1
      · exact if_congr (by rw [Fin.rev_inj, eq_comm]) rfl rfl
      · refine if_congr ?_ rfl rfl
        rw [Fin.rev_inj, and_comm, Fin.rev_eq_iff]
    refine ⟨⟨⟨g, hg⟩, (hshape _).2 fun i l h => ?_⟩, hent b⟩
    show (1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) i l = _
    rw [Matrix.add_apply, Matrix.single_apply, ite_eq_right (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), add_zero]
  let φ : cellU y →* Multiplicative L :=
    { toFun := fun u => Multiplicative.ofAdd (c u)
      map_one' := by simp only [hone]; rfl
      map_mul' := fun u w => by simp only [hmul]; rfl }
  let H : ℤ → Subgroup (cellU y) := fun j => (AddSubgroup.toSubgroup (antiBall σ j)).comap φ
  have memH : ∀ j (u : cellU y), u ∈ H j ↔ Valued.v (c u) ≤ WithZero.exp j := by
    intro j u
    show (c u) ∈ antiBall σ j ↔ _
    rw [mem_antiBall]
    exact ⟨fun h => h.2, fun h => ⟨hanti u, h⟩⟩
  have hset : ∀ j, (H j : Set (cellU y)) = c ⁻¹' {x : L | Valued.v x ≤ WithZero.exp j} :=
    fun j => Set.ext (memH j)
  have hc : Continuous c :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem a a.rev
  have hm : ∀ j, MeasurableSet (H j : Set (cellU y)) := fun j => by
    rw [hset]
    exact ((isOpen_ball hv j).preimage hc).measurableSet
  have hle : ∀ j, H j ≤ H (j + 1) := fun j u hu =>
    (memH _ _).2 (((memH _ _).1 hu).trans (WithZero.exp_le_exp.2 (by omega)))
  have hi : ∀ j, (H j).relIndex (H (j + 1)) = q := fun j => by
    show ((AddSubgroup.toSubgroup (antiBall σ j)).comap φ).relIndex
      ((AddSubgroup.toSubgroup (antiBall σ (j + 1))).comap φ) = q
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self, AddSubgroup.relIndex_toSubgroup, hidx]
    intro b hb
    obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd b) hb.1
    exact ⟨u, congrArg Multiplicative.ofAdd hu⟩
  have hint : ∀ u : cellU y, Valued.v (c u) ≤ 1 → ∀ i l, M u i l ∈ intL L := by
    intro u hu i l
    rw [hstr u, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    refine add_mem ?_ ?_ <;> split_ifs
    · exact one_mem _
    · exact zero_mem _
    · exact hu
    · exact zero_mem _
  have hH0 : H 0 = (KU σ n).subgroupOf (cellU y) := by
    ext u
    rw [memH, WithZero.exp_zero, Subgroup.mem_subgroupOf, ← SetLike.mem_coe, LFun.IntPtsUnitary.coe_KU,
      LFun.IntPtsUnitary.coe_GLint]
    constructor
    · intro h
      exact ⟨hint u h, hint u⁻¹ (by rwa [hinv, Valuation.map_neg])⟩
    · intro h
      exact h.1 a a.rev
  have hfin := measure_chain μ H (q := q) (by omega) hm hle hi (by rw [hH0]; exact hμ) j
  have hmj := hm j
  rw [hset] at hfin hmj
  exact ⟨hmj, hfin⟩

theorem conjScale' : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 →
    Even n → ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
    μ ((KU σ n).subgroupOf (cellU y)) = 1 → ∀ (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    (∀ F : GU σ n → ℂ, ∫ u : cellU y, F (t⁻¹ * u * t) ∂μ =
        (q : ℂ) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) *
          ∫ u : cellU y, F u ∂μ) ∧
    ∀ F : GU σ n → ENNReal, ∫⁻ u : cellU y, F (t⁻¹ * u * t) ∂μ =
        (q : ENNReal) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) *
          ∫⁻ u : cellU y, F u ∂μ := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hyK hy _ _ μ _ hμ t ht
  haveI : SecondCountableTopology L := (GlobalTheory.LineUMod.locCompact_secondCountable hU).2
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) L) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → L))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) L)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) L)).symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) L) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (GU σ n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (cellU y) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU
  haveI : LocallyCompactSpace (cellU y) := by
    have hN : IsClosed (cellU y : Set (GU σ n)) := (isClosed_cell _).preimage continuous_subtype_val
    have h1 : IsOpen ((KU σ n).subgroupOf (cellU y) : Set (cellU y)) := hKo.preimage continuous_subtype_val
    have h2 : IsCompact ((KU σ n).subgroupOf (cellU y) : Set (cellU y)) :=
      hN.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
    exact h2.locallyCompactSpace_of_mem_nhds_of_group (h1.mem_nhds (one_mem _))
  have htinv := inv_offdiag t ht
  have hdc := (GlobalTheory.WeylCell.diagConjU L σ n y _ hy t ht).2
  have hdc' := (GlobalTheory.WeylCell.diagConjU L σ n y _ hy t⁻¹ htinv).2
  let c : cellU y ≃* cellU y :=
    { toFun := fun u => ⟨t⁻¹ * u * t, hdc u u.2⟩
      invFun := fun u => ⟨t * u * t⁻¹, by simpa using hdc' u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hc : Continuous c :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hc' : Continuous c.symm :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  haveI : (μ.map c).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ c hc hc'
  have hE : MeasurableEmbedding c := (Homeomorph.mk c.toEquiv hc hc').measurableEmbedding

  set T : Matrix (Fin n) (Fin n) L := ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTd
  set a : Fin n := lo k with ha
  set r : ℤ := ordL (T a a) with hr
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  have hprod : σ (T a.rev a.rev) * T a a = 1 := by
    have hu := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 a a
    have h := congrFun (congrFun (Units.inv_mul (t : GL (Fin n) L)) a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h
    · rw [← hu, h, Matrix.one_apply_eq]
    · intro b _ hb; exact mul_eq_zero_of_right _ (ht b a hb)
    · simp
  have ha0 : T a a ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hva : Valued.v (T a a) = ((Multiplicative.ofAdd (-r) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    v_eq_ofAdd_ordL ha0
  have hva' : Valued.v (T a.rev a.rev) = ((Multiplicative.ofAdd r : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    have h := congrArg Valued.v hprod
    rw [map_mul, hσv, map_one, hva] at h
    rw [eq_inv_of_mul_eq_one_left h, ← WithZero.coe_inv, ← ofAdd_neg, neg_neg]

  let S : ℤ → Set (cellU y) := fun j => {u : cellU y |
    Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a.rev) ≤
      ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ))}
  have hsh : ∀ j : ℤ, MeasurableSet (S j) ∧ μ (S j) = (q : ENNReal) ^ j := shell_measure' L ϖ σ q hU n k hk hn y hyK hy μ hμ
  have hpre : c ⁻¹' S 0 = S (-2 * r) := by
    ext u
    simp only [S, Set.mem_preimage, Set.mem_ofPred_eq]
    show Valued.v (((((t : GL (Fin n) L))⁻¹ * ((u : GU σ n) : GL (Fin n) L) * (t : GL (Fin n) L) : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) a a.rev) ≤ _ ↔ _
    rw [gl_conj_apply_of_offdiag ht, map_mul, map_mul, map_inv₀, ← hTd, hva, hva', ← WithZero.coe_inv,
      mul_right_comm, ← WithZero.coe_mul, coe_mul_le_iff]
    have e : ((Multiplicative.ofAdd (-r))⁻¹ * Multiplicative.ofAdd r)⁻¹ * Multiplicative.ofAdd (0 : ℤ) =
        (Multiplicative.ofAdd (-2 * r) : Multiplicative ℤ) := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
      ring
    rw [e]
  have hq0 : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  set Q : ℝ≥0 := (q : ℝ≥0) ^ (-2 * r) with hQd
  have hQ : (Q : ℝ≥0∞) = (q : ℝ≥0∞) ^ (-2 * r) := by
    rw [hQd, ENNReal.coe_zpow (by exact_mod_cast hq0)]
    simp
  have hmap : μ.map c (S 0) = (q : ℝ≥0∞) ^ (-2 * r) := by
    rw [Measure.map_apply hE.measurable (hsh 0).1, hpre, (hsh _).2]
  have hS0 : μ (S 0) = 1 := by rw [(hsh 0).2, zpow_zero]
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map c) μ
  have hfac : Measure.haarScalarFactor (μ.map c) μ = Q := by
    have h := congrArg (fun ν : Measure (cellU y) => ν (S 0)) e
    simp only [smul_apply, hS0, hmap, ENNReal.smul_def, smul_eq_mul, mul_one] at h
    exact ENNReal.coe_injective (h.symm.trans hQ.symm)
  have hmu : μ.map c = Q • μ := e.trans (by rw [hfac])
  refine ⟨fun F => ?_, fun F => ?_⟩
  · refine (hE.integral_map (fun v : cellU y => F v)).symm.trans ?_
    rw [hmu, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    congr 1
    rw [hQd]
    push_cast
    rfl
  · refine (hE.lintegral_map (fun v : cellU y => F v)).symm.trans ?_
    rw [hmu, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, hQ]

theorem shiftCore (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (q : ℕ) (n : ℕ)
    (a a' : Fin n) (hrev : a.rev = a') (haa : a'.val = a.val + 1) {m : ℕ} (α : Fin m → ℂ) (φ : GU σ n → ℂ)
    (hφ : ∀ b g : GU σ n, IsBorelU b → φ (b * g) = chiDeltaU q α b * φ g) (y : GU σ n) (hy : IsWeylRep (Equiv.swap a a') (y : GL (Fin n) L))
    (ν : GU σ n) (hν : IsUnipU ν) :
    ∃ u' ∈ cellU y, ∀ u ∈ cellU y, ∀ g : GU σ n, φ (y⁻¹ * u * ν * g) = φ (y⁻¹ * (u' * u) * g) := by
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  have hlt : a < a' := by rw [Fin.lt_def]; omega
  have hrev' : a'.rev = a := by rw [← hrev, Fin.rev_rev]
  have hνB : (ν : GL (Fin n) L) ∈ unipB L (Fin n) := (mem_unipB L).2 ⟨hν.1, hν.2⟩
  set c : L := ((ν : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' with hc
  have hσc : σ c = -c := by
    have h := (GlobalTheory.LGrp.mem_GU_iff σ n (ν : GL (Fin n) L)).1 ν.2 a a'
    rw [hrev', hrev, unipB_inv_apply_succ hνB haa] at h
    exact h.symm
  let T : GL (Fin n) L := ⟨Matrix.transvection a a' c, Matrix.transvection a a' (-c),
    (Matrix.transvection_mul_transvection_same a a' hne c (-c)).trans (by rw [add_neg_cancel, Matrix.transvection_zero]),
    (Matrix.transvection_mul_transvection_same a a' hne (-c) c).trans (by rw [neg_add_cancel, Matrix.transvection_zero])⟩
  have hTapp : ∀ (d : L) (i j : Fin n), Matrix.transvection a a' d i j =
      (if i = j then 1 else 0) + (if i = a ∧ j = a' then d else 0) := by
    intro d i j
    exact transvection_apply' a a' d i j
  have hT : ∀ i j, (T : Matrix (Fin n) (Fin n) L) i j =
      (if i = j then 1 else 0) + (if i = a ∧ j = a' then c else 0) := hTapp c
  have hTi : ∀ i j, ((T⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      (if i = j then 1 else 0) + (if i = a ∧ j = a' then -c else 0) := hTapp (-c)
  have hTG : T ∈ GU σ n := by
    rw [GlobalTheory.LGrp.mem_GU_iff]
    intro i j
    rw [hTi, hT]
    have e1 : j.rev = i.rev ↔ i = j := by rw [Fin.rev_inj]; exact eq_comm
    have e2 : (j.rev = a ∧ i.rev = a') ↔ (i = a ∧ j = a') := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [← Fin.rev_rev i, h2, hrev'], by rw [← Fin.rev_rev j, h1, hrev]⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨hrev', hrev⟩
    simp only [e1, e2]
    split_ifs with h1 h2 <;> simp_all
  have hTB : T ∈ unipB L (Fin n) := by
    refine (mem_unipB L).2 ⟨fun i j h => ?_, fun i => ?_⟩
    · rw [hT, ite_eq_right (ne_of_lt h).symm, ite_eq_right (fun e => by obtain ⟨rfl, rfl⟩ := e; exact absurd h (not_lt.2 hlt.le)), add_zero]
    · rw [hT, ite_eq_left rfl, ite_eq_right (fun h => hne (h.1.symm.trans h.2)), add_zero]
  have hback : ∀ i j, Equiv.swap a a' i = a → Equiv.swap a a' j = a' → i = a' ∧ j = a := by
    intro i j h1 h2
    exact ⟨by rw [← Equiv.swap_apply_self a a' i, h1, Equiv.swap_apply_left],
      by rw [← Equiv.swap_apply_self a a' j, h2, Equiv.swap_apply_right]⟩
  refine ⟨⟨T, hTG⟩, ?_, ?_⟩
  · show T ∈ cell (y : GL (Fin n) L)
    rw [mem_cell]
    refine ⟨hTB, mem_unipBLower.2 ⟨fun i j hij => ?_, fun i => ?_⟩⟩
    · rw [Units.val_mul, Units.val_mul, conj_apply hy, hT,
        ite_eq_right (fun e => (ne_of_lt hij) ((Equiv.injective _) e)),
        ite_eq_right (fun e => by
          obtain ⟨h1, h2⟩ := hback i j e.1 e.2
          rw [h1, h2] at hij
          exact absurd hij (not_lt.2 hlt.le))]
      simp
    · rw [Units.val_mul, Units.val_mul, conj_apply hy, hT, ite_eq_left rfl,
        ite_eq_right (fun h => hne (h.1.symm.trans h.2)), add_zero, mul_one, inv_mul_diag hy]
  · intro u hu g
    have huB : (u : GL (Fin n) L) ∈ unipB L (Fin n) := (mem_cell.1 hu).1
    set N : GL (Fin n) L := (u : GL (Fin n) L) * ν * (u : GL (Fin n) L)⁻¹ * T⁻¹ with hN
    have hNB : N ∈ unipB L (Fin n) :=
      mul_mem (mul_mem (mul_mem huB hνB) (inv_mem huB)) (inv_mem hTB)
    have hNa : (N : Matrix (Fin n) (Fin n) L) a a' = 0 := by
      rw [hN, unipB_mul_apply_succ (mul_mem (mul_mem huB hνB) (inv_mem huB)) (inv_mem hTB) haa,
        unipB_mul_apply_succ (mul_mem huB hνB) (inv_mem huB) haa, unipB_mul_apply_succ huB hνB haa,
        unipB_inv_apply_succ hTB haa, unipB_inv_apply_succ huB haa, hT, ite_eq_right hne, ite_eq_left ⟨rfl, rfl⟩]
      ring
    let b : GU σ n := y⁻¹ * u * ν * u⁻¹ * (⟨T, hTG⟩ : GU σ n)⁻¹ * y
    have hbG : (b : GL (Fin n) L) = (y : GL (Fin n) L)⁻¹ * N * y := by
      simp only [b, hN, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hbv : ∀ i j, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
        ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (Equiv.swap a a' i) *
          (N : Matrix (Fin n) (Fin n) L) (Equiv.swap a a' i) (Equiv.swap a a' j) *
          ((y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (Equiv.swap a a' j) j := by
      intro i j
      rw [hbG, Units.val_mul, Units.val_mul, conj_apply hy]
    have hbB : IsBorelU b := by
      intro i j hji
      rw [hbv]
      suffices h0 : (N : Matrix (Fin n) (Fin n) L) (Equiv.swap a a' i) (Equiv.swap a a' j) = 0 by
        rw [h0, mul_zero, zero_mul]
      rcases lt_trichotomy (Equiv.swap a a' i) (Equiv.swap a a' j) with h | h | h
      · obtain ⟨h1, h2⟩ := swap_inversion haa h (by rwa [Equiv.swap_apply_self, Equiv.swap_apply_self])
        rw [h1, h2]
        exact hNa
      · exact absurd ((Equiv.injective _) h) (ne_of_lt hji).symm
      · exact ((mem_unipB L).1 hNB).1 _ _ h
    have hbd : ∀ i, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
      intro i
      rw [hbv, ((mem_unipB L).1 hNB).2, mul_one, inv_mul_diag hy]
    have hchi : chiDeltaU q α b = 1 := by
      unfold chiDeltaU
      apply Finset.prod_eq_one
      intro i _
      split_ifs
      · rw [hbd, ordL_one]
        simp
      · rfl
    have e : ∀ w : GU σ n, y⁻¹ * u * ν * g = (y⁻¹ * u * ν * u⁻¹ * w⁻¹ * y) * (y⁻¹ * (w * u) * g) :=
      fun w => by group
    have key := hφ b (y⁻¹ * (⟨T, hTG⟩ * u) * g) hbB
    rw [hchi, one_mul] at key
    rw [e ⟨T, hTG⟩]
    exact key

theorem shiftEven (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (q : ℕ) (n : ℕ)
    (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (hn : Even n) {m : ℕ} (α : Fin m → ℂ) (φ : GU σ n → ℂ)
    (hφ : ∀ b g : GU σ n, IsBorelU b → φ (b * g) = chiDeltaU q α b * φ g) (y : GU σ n)
    (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) (ν : GU σ n) (hν : IsUnipU ν) :
    ∃ u' ∈ cellU y, ∀ u ∈ cellU y, ∀ g : GU σ n, φ (y⁻¹ * u * ν * g) = φ (y⁻¹ * (u' * u) * g) := by
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp only [simpleU, ite_eq_right hk]
  rw [hs] at hy
  have haa : ((lo k).rev).val = (lo k).val + 1 := by
    obtain ⟨m, hm⟩ := hn
    have := k.2
    simp only [Fin.val_rev, lo, Fin.val_castLE]
    omega
  exact shiftCore L σ q n (lo k) (lo k).rev rfl haa α φ hφ y hy ν hν

theorem shiftOdd : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), (∀ b g : GU σ n, IsBorelU b → φ (b * g) = chiDeltaU q α b * φ g) →
    ∀ n' : GU σ n, IsUnipU n' → ∃ p : cellU y, ∀ (u : cellU y) (x : GU σ n),
      φ (y⁻¹ * (u : GU σ n) * n' * x) = φ (y⁻¹ * ((u * p : cellU y) : GU σ n) * x) := by
  intro L _ _ _ ϖ σ q hq n k hk hn y hyK hy α φ hφ n' hn'
  have hcell := mem_cellU_last_iff L ϖ σ q hq n k hk hn y hyK hy
  have hw : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hA := val_rev_lo_of_last k hk hn
  have hnB : (n' : GL (Fin n) L) ∈ unipB L (Fin n) := (mem_unipB L).2 hn'
  let p₀ : GU σ n := ⟨blockKeepGL (lo k) (lo k).rev _ hnB, blockKeepGL_mem_GU _ _ hnB n'.2⟩
  have hp₀ : ((p₀ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockKeep (lo k) (lo k).rev ((n' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := rfl
  have hp : p₀ ∈ cellU y := by
    refine (hcell p₀).2 ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij hor => ?_⟩
    · rw [hp₀]; unfold blockKeep
      split_ifs
      · exact hn'.1 i j hij
      · exact Matrix.one_apply_ne hij.ne'
    · rw [hp₀]; unfold blockKeep
      split_ifs
      · exact hn'.2 i
      · exact Matrix.one_apply_eq i
    · rw [hp₀]; unfold blockKeep
      rw [ite_eq_right, Matrix.one_apply_ne hij.ne]
      rintro ⟨⟨h1, -⟩, -, h2⟩
      rcases hor with h | h
      · exact absurd h1 (not_le.2 h)
      · exact absurd h2 (not_le.2 h)
  refine ⟨⟨p₀, hp⟩, fun u x => ?_⟩
  have hkeep : ∀ v : GU σ n, v ∈ cellU y →
      blockKeep (lo k) (lo k).rev ((v : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        ((v : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := fun v hv =>
    blockKeep_eq_self _ _ _ ((hcell v).1 hv).1.1 ((hcell v).1 hv).1.2 ((hcell v).1 hv).2
  have hB : ∀ v : GU σ n, v ∈ cellU y → (v : GL (Fin n) L) ∈ unipB L (Fin n) := fun v hv =>
    (mem_unipB L).2 ((hcell v).1 hv).1
  set c : GU σ n := (u : GU σ n) * p₀ with hc
  have hcc : c ∈ cellU y := mul_mem u.2 hp
  set M : GU σ n := (u : GU σ n) * n' * c⁻¹ with hM
  have hMB : (M : GL (Fin n) L) ∈ unipB L (Fin n) :=
    mul_mem (mul_mem (hB _ u.2) hnB) (hB _ (inv_mem hcc))
  have hM1 : blockKeep (lo k) (lo k).rev ((M : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    have e1 : ((M : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (((u : GU σ n) : GL (Fin n) L) * (n' : GL (Fin n) L) : GL (Fin n) L) *
          (((c⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := rfl
    rw [e1, blockKeep_mul _ _ _ _ ((mem_unipB L).1 (mul_mem (hB _ u.2) hnB)).1
      ((mem_unipB L).1 (hB _ (inv_mem hcc))).1, Units.val_mul,
      blockKeep_mul _ _ _ _ ((mem_unipB L).1 (hB _ u.2)).1 hn'.1, hkeep _ u.2, hkeep _ (inv_mem hcc), ← hp₀,
      ← Units.val_mul, ← Units.val_mul]
    have e2 : ((u : GU σ n) : GL (Fin n) L) * (p₀ : GL (Fin n) L) * ((c⁻¹ : GU σ n) : GL (Fin n) L) =
        ((c * c⁻¹ : GU σ n) : GL (Fin n) L) := rfl
    rw [e2, mul_inv_cancel]
    rfl
  set g : GU σ n := y⁻¹ * M * y with hg
  have hgv : (g : GL (Fin n) L) = (y : GL (Fin n) L)⁻¹ * (M : GL (Fin n) L) * (y : GL (Fin n) L) := rfl
  have hgB : IsBorelU g := by
    intro i j hij
    rw [hgv, weylRep_conj_apply_local hy]
    have hz : ((M : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (simpleU k i) (simpleU k j) = 0 := by
      rcases lt_or_gt_of_ne (fun e : simpleU k i = simpleU k j => hij.ne' ((simpleU k).injective e)) with hl | hl
      · have hno := (swap_lt_swap_iff_of_add_two (lo k) (lo k).rev _ _ hA hl).not.1 (by
          rw [hw, Equiv.swap_apply_self, Equiv.swap_apply_self]; exact not_lt.2 hij.le)
        rw [not_or, not_lt, not_lt] at hno
        have := congrFun (congrFun hM1 (simpleU k i)) (simpleU k j)
        unfold blockKeep at this
        rw [ite_eq_left ⟨⟨hno.1, hl.le.trans hno.2⟩, hno.1.trans hl.le, hno.2⟩, Matrix.one_apply_ne hl.ne] at this
        exact this
      · exact ((mem_unipB L).1 hMB).1 _ _ hl
    rw [hz, mul_zero, zero_mul]
  have hgd : ∀ i, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
    intro i
    rw [hgv, weylRep_conj_apply_local hy, ((mem_unipB L).1 hMB).2, mul_one, weylRep_inv_mul_diag_local hy]
  have ho : ordL (1 : L) = 0 := by
    unfold ordL
    split_ifs with h
    · rfl
    · have : WithZero.unzero h = 1 := by
        apply WithZero.coe_injective
        rw [WithZero.coe_unzero, map_one]; rfl
      rw [this]; simp
  have hchi : chiDeltaU q α g = 1 := by
    unfold chiDeltaU
    refine Finset.prod_eq_one fun i _ => ?_
    split_ifs
    · rw [hgd, ho]; simp
    · rfl
  have h := hφ g (y⁻¹ * c * x) hgB
  rw [hchi, one_mul] at h
  have e : y⁻¹ * (u : GU σ n) * n' * x = g * (y⁻¹ * c * x) := by
    rw [hg, hM]; group
  rw [e, h]
  rfl

end GlobalTheory.CompanionTheory.InvStep

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReduction
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.CompanionTheory.InvStep

section Cell

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q n : ℕ}

theorem spherical_even (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (hn : Even n) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂˣ) (hαk : ‖(α k : ℂ)‖ < 1) (φ : GU σ n → ℂ) (hφ : IsSphericalU q (fun i => (α i : ℂ)) φ)
    (hφ1 : φ 1 = 1) :
    Integrable (fun u : cellU y => φ (y⁻¹ * u)) μ ∧ ∫ u : cellU y, φ (y⁻¹ * u) ∂μ = cSimpleU q k α := by
  have hq2 : 2 ≤ q := h.2.2.2.2.2.1
  let H : ℕ → Set (cellU y) := fun j => {u : cellU y |
    Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤
      ((Multiplicative.ofAdd (j : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))}
  have hHm : ∀ j, MeasurableSet (H j) := fun j => (shell_measure' L ϖ σ q h n k hk hn y hyK hy μ hμ j).1
  have hHμ : ∀ j, μ (H j) = (q : ENNReal) ^ j := fun j => by
    have := (shell_measure' L ϖ σ q h n k hk hn y hyK hy μ hμ j).2
    rw [zpow_natCast] at this; exact this
  have hmono : Monotone H := by
    intro i j hij u hu
    simp only [H, Set.mem_setOf_eq] at hu ⊢
    exact le_trans hu (WithZero.coe_le_coe.2 (Multiplicative.ofAdd_le.2 (by exact_mod_cast hij)))
  have hcov : ⋃ j, H j = Set.univ := by
    refine Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ?_
    show ∃ j : ℕ, Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ _
    induction Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)
      using WithZero.recZeroCoe with
    | zero => exact ⟨0, zero_le'⟩
    | coe a =>
      refine ⟨(Multiplicative.toAdd a).toNat, WithZero.coe_le_coe.2 ?_⟩
      show Multiplicative.toAdd a ≤ ((Multiplicative.toAdd a).toNat : ℤ)
      exact Int.self_le_toNat _
  have hshape : ∀ u : cellU y, ∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((((u : GU σ n)) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j :=
    fun u => (GlobalTheory.T.mem_weylCellUnitaryGroup_longSimpleReflection_iff L σ n k hk hn y hy u).1 u.2
  have hval := fun u : cellU y =>
    GlobalTheory.T.sphericalVector_value_unitaryRankOne_gindikinKarpelevich L ϖ σ q h n k hk hn (fun i => (α i : ℂ)) φ hφ hφ1 y hyK hy u (hshape u)
  have hF0 : ∀ x ∈ H 0, φ (y⁻¹ * x) = 1 := by
    intro x hx
    rw [hval x, if_pos]
    simpa [H] using hx
  have hF : ∀ j x, x ∈ H (j + 1) → x ∉ H j → φ (y⁻¹ * x) = ((α k : ℂ) / q) ^ (j + 1) := by
    intro j x hx1 hx0
    have hv : Valued.v ((((x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) =
        ((Multiplicative.ofAdd (((j + 1 : ℕ)) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simp only [H, Set.mem_setOf_eq, not_le] at hx1 hx0
      revert hx1 hx0
      induction Valued.v ((((x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev)
        using WithZero.recZeroCoe with
      | zero => intro _ h0; exact absurd h0 (not_lt.2 zero_le')
      | coe a =>
        intro h1 h0
        have h1' : Multiplicative.toAdd a ≤ ((j + 1 : ℕ) : ℤ) := WithZero.coe_le_coe.1 h1
        have h0' : (j : ℤ) < Multiplicative.toAdd a := WithZero.coe_lt_coe.1 h0
        congr 1
        apply Multiplicative.toAdd.injective
        simp only [toAdd_ofAdd]
        push_cast at h1' ⊢
        omega
    have hord := GlobalTheory.WeylCell.RankOneUnitary.ordL_of_v_eq _ _ hv
    have hnot : ¬ Valued.v ((((x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤ 1 := by
      rw [hv, ← WithZero.coe_one, WithZero.coe_le_coe]
      show ¬ (((j + 1 : ℕ) : ℤ) ≤ 0)
      omega
    rw [hval x, if_neg hnot, hord, neg_neg, zpow_natCast, zpow_neg, zpow_natCast, div_pow, div_eq_mul_inv]
  obtain ⟨hInt1, hI1, -⟩ := GlobalTheory.T.integral_eq_rankOneFactorSL2_of_geometric_on_shells μ q hq2 (α k : ℂ) hαk H hHm hmono hcov hHμ (fun x => φ (y⁻¹ * x)) hF0 hF
  refine ⟨hInt1, ?_⟩
  rw [hI1]
  simp [cSimpleU, hk, hn]

theorem spherical_cell (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂˣ) (hαk : ‖(α k : ℂ)‖ < 1) (φ : GU σ n → ℂ) (hφ : IsSphericalU q (fun i => (α i : ℂ)) φ)
    (hφ1 : φ 1 = 1) :
    Integrable (fun u : cellU y => φ (y⁻¹ * u)) μ ∧ ∫ u : cellU y, φ (y⁻¹ * u) ∂μ = cSimpleU q k α := by
  by_cases hn : Even n
  · exact spherical_even h k hk hn y hyK hy μ hμ α hαk φ hφ hφ1
  · have hA := GlobalTheory.T.integral_depth_power_lastSimpleReflectionCell L ϖ σ q h n k hk hn y hyK hy μ hμ (α k) hαk
    have hpt : ∀ u : cellU y, φ (y⁻¹ * (u : GU σ n)) = ((α k : ℂ) / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) :=
      GlobalTheory.T.unitaryThreeRankOne_sphericalVector_cell_value L ϖ σ q h n k hk hn y hyK hy (fun i => (α i : ℂ)) φ hφ hφ1
    simp_rw [hpt]
    refine ⟨hA.1, ?_⟩
    rw [hA.2.1]
    simp [cSimpleU, hk, hn]

theorem cSimpleU_ne_zero (hq : 2 ≤ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (α : Fin (n / 2) → ℂˣ)
    (hαk : ‖(α k : ℂ)‖ < 1) : cSimpleU q k α ≠ 0 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hnq : ‖(q : ℂ)‖ = q := by simp
  set z : ℂ := ((α k : ℂˣ) : ℂ) with hz
  have key : ∀ (w : ℂ), ‖w‖ < 1 → 1 - w ≠ 0 := fun w hw e => by
    have : w = 1 := (sub_eq_zero.1 e).symm
    rw [this] at hw
    simp at hw
  have hqi : ‖(q : ℂ)⁻¹‖ < 1 := by
    rw [norm_inv, hnq]
    exact inv_lt_one_of_one_lt₀ hq1
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hαk two_ne_zero
  have hmul : ∀ a : ℂ, ‖a‖ ≤ 1 → ‖a * z‖ < 1 := fun a ha => by
    rw [norm_mul]
    calc ‖a‖ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < 1 := by simpa using hαk
  have hqn : ‖(q : ℂ)⁻¹‖ ≤ 1 := hqi.le
  have hq2n : ‖((q : ℂ) ^ 2)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, hnq]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hq1.le)
  simp only [cSimpleU, dif_neg hk]
  split_ifs with hn
  · exact div_ne_zero (key _ (hmul _ hqn)) (key _ hαk)
  · refine div_ne_zero (mul_ne_zero (key _ (hmul _ hq2n)) ?_) (key _ hz2)
    have := key (-((q : ℂ)⁻¹ * z)) (by rw [norm_neg]; exact hmul _ hqn)
    simpa using this

theorem scale_cell (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂˣ) (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) :
    ∃ s : ℂ, (∀ F : GU σ n → ℂ, ∫ u : cellU y, F (t⁻¹ * u * t) ∂μ = s * ∫ u : cellU y, F u ∂μ) ∧
      chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) * s = chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
  by_cases hn : Even n
  · exact ⟨_, (conjScale' L ϖ σ q h n k hk hn y hyK hy μ hμ t ht).1, GlobalTheory.T.chiDeltaU_conj_longSimpleReflection_unitary L ϖ σ q h n k hk hn y hy α t ht⟩
  · refine ⟨_, (GlobalTheory.T.integral_diagonal_conj_lastSimpleReflectionCell L ϖ σ q h n k hk hn y hyK hy μ hμ t ht).1, ?_⟩
    obtain ⟨Φ, hΦ, hΦ1, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) h (by omega) (by omega)
      (fun i => (α i : ℂ)) fun i => (α i).ne_zero
    have e := GlobalTheory.T.unitaryRankOne_sphericalIntegrand_diagonal_torus_factor L ϖ σ q h n k hk hn y hyK hy α Φ hΦ t ht 1 y
    have hB := (GlobalTheory.WeylCell.diagConjU L σ n y _ hy t ht).1
    have e2 : Φ (y⁻¹ * t * 1 * y) = chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) := by
      have := hΦ (y⁻¹ * t * y) 1 1 hB (one_mem _)
      simpa [hΦ1, mul_assoc] using this
    rw [e2] at e
    simpa [hΦ1] using e

theorem shift_cell (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂ) (ψ : GU σ n → ℂ) (hψ : ∀ b g : GU σ n, IsBorelU b → ψ (b * g) = chiDeltaU q α b * ψ g)
    (ν : GU σ n) (hν : IsUnipU ν) :
    ∫ u : cellU y, ψ (y⁻¹ * u * ν) ∂μ = ∫ u : cellU y, ψ (y⁻¹ * u) ∂μ := by
  by_cases hn : Even n
  · obtain ⟨u', hu', hsh⟩ := shiftEven L σ q n k hk hn α ψ hψ y hy ν hν
    have e : ∀ u : cellU y, ψ (y⁻¹ * u * ν) = ψ (y⁻¹ * (((⟨u', hu'⟩ : cellU y) * u : cellU y) : GU σ n)) := by
      intro u
      simpa using hsh u u.2 1
    simp_rw [e]
    exact integral_mul_left_eq_self (fun v : cellU y => ψ (y⁻¹ * (v : GU σ n))) (⟨u', hu'⟩ : cellU y)
  · obtain ⟨p, hp⟩ := shiftOdd L ϖ σ q h n k hk hn y hyK hy α ψ hψ ν hν
    have e : ∀ u : cellU y, ψ (y⁻¹ * u * ν) = ψ (y⁻¹ * ((u * p : cellU y) : GU σ n)) := by
      intro u
      simpa using hp u 1
    simp_rw [e]
    exact (GlobalTheory.T.unitaryWeylCell_haar_rightTranslate_invariant L ϖ σ q h n k hk hn y hyK hy μ hμ p).1 fun w => ψ (y⁻¹ * w)

theorem integral_law (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂˣ) (ψ : GU σ n → ℂ)
    (hψ : ∀ b g : GU σ n, IsBorelU b → ψ (b * g) = chiDeltaU q (fun i => (α i : ℂ)) b * ψ g)
    (β : GU σ n) (hβ : IsBorelU β) :
    ∫ u : cellU y, ψ (y⁻¹ * u * β) ∂μ =
      chiDeltaU q (fun i => (actU k α i : ℂ)) β * ∫ u : cellU y, ψ (y⁻¹ * u) ∂μ := by
  obtain ⟨t, ν, rfl, hν, htd, htdiag⟩ := GlobalTheory.T.unitaryBorel_eq_diagonal_mul_unipotent L σ n β hβ
  have hBt := (GlobalTheory.WeylCell.diagConjU L σ n y _ hy t htd).1
  obtain ⟨s, hs, hchi⟩ := scale_cell h k hk y hyK hy μ hμ α t htd
  have hχ : chiDeltaU q (fun i => (actU k α i : ℂ)) (t * ν) = chiDeltaU q (fun i => (actU k α i : ℂ)) t :=
    (GlobalTheory.WeylCell.RankOneUnitary.chiDeltaU_congr q _ t (t * ν) htdiag).symm
  have hpt : ∀ u : cellU y, ψ (y⁻¹ * u * (t * ν)) =
      chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) * ψ (y⁻¹ * (t⁻¹ * u * t) * ν) := by
    intro u
    rw [← hψ _ _ hBt]
    congr 1
    group
  simp_rw [hpt]
  rw [integral_const_mul, hs (fun v => ψ (y⁻¹ * v * ν)), ← mul_assoc, hchi, hχ,
    shift_cell h k hk y hyK hy μ hμ _ ψ hψ ν hν]

theorem integrable_cell (h : IsUnramInv ϖ σ q) (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (y : GU σ n)
    (hyK : y ∈ KU σ n) (hy : IsWeylRep (simpleU k) (y : GL (Fin n) L)) [MeasurableSpace (cellU y)]
    [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure] (hμ : μ ((KU σ n).subgroupOf (cellU y)) = 1)
    (α : Fin (n / 2) → ℂˣ) (hαk : ‖(α k : ℂ)‖ < 1) (ψ : GU σ n → ℂ)
    (hψ : ∀ b g : GU σ n, IsBorelU b → ψ (b * g) = chiDeltaU q (fun i => (α i : ℂ)) b * ψ g)
    (S : Set (GU σ n)) (hS : IsOpen S) (h1 : (1 : GU σ n) ∈ S) (hinv : ∀ g ∈ S, ∀ x, ψ (x * g) = ψ x) :
    Integrable (fun u : cellU y => ψ (y⁻¹ * u)) μ := by
  have hcont : Continuous ψ := continuous_iff_continuousAt.2 fun g => by
    have hO : IsOpen ((fun x => g⁻¹ * x) ⁻¹' S) := hS.preimage (continuous_const.mul continuous_id)
    have hg : g ∈ (fun x => g⁻¹ * x) ⁻¹' S := by simpa using h1
    refine (tendsto_const_nhds (x := ψ g)).congr' (Filter.eventually_of_mem (hO.mem_nhds hg) fun x hx => ?_)
    have := hinv _ hx g
    rw [mul_inv_cancel_left] at this
    exact this.symm
  obtain ⟨-, hKc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨Φ, hΦ, hΦ1, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) h (by omega) (by omega)
    (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  obtain ⟨hI, -⟩ := spherical_cell h k hk y hyK hy μ hμ α hαk Φ hΦ hΦ1
  have hb : ∀ g, ‖ψ g‖ ≤ max C 0 * ‖Φ g‖ := by
    intro g
    obtain ⟨b, κ, hb, hκ, rfl⟩ := Formalism.UG.P.fIwasawa_iwasawa σ h.1 h.2.1 g
    have e2 := hΦ b 1 κ hb hκ
    rw [mul_one, hΦ1, mul_one] at e2
    rw [hψ b κ hb, e2, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hC κ hκ).trans (le_max_left _ _)) (norm_nonneg _)
  refine (hI.norm.const_mul (max C 0)).mono'
    (hcont.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => hb _)

end Cell

theorem invStepU : PositivityTheory.SphericalProduct.InvStepU := by
  intro L _ _ _ ϖ σ q n h V _ _ ρ hadm hirr hsph χ j hj hχ f hf hfe
  have hk : ¬ j.val + 1 < n / 2 := by omega
  have hq2 : 2 ≤ q := h.2.2.2.2.2.1
  have hact : actU j χ = Function.update χ j (χ j)⁻¹ := by simp [actU, hk]
  rw [← hact]
  obtain ⟨-, ⟨y, hyK, hyw⟩, hμex⟩ := exists_data_U h n χ (simpleU j) (GlobalTheory.T.unitaryWeylSimpleReflection_rev_comm_sq_eq_one n j).1
  letI : MeasurableSpace (cellU y) := borel _
  haveI : BorelSpace (cellU y) := ⟨rfl⟩
  obtain ⟨μ, hμH, hμ⟩ := hμex y
  haveI := hμH
  have hlaw : ∀ (v : V) (b g : GU σ n), IsBorelU b →
      (f v).1 (b * g) = chiDeltaU q (fun i => (χ i : ℂ)) b * (f v).1 g := fun v b g hb => (f v).2 b g hb
  have htr : ∀ (g : GU σ n) (v : V) (x : GU σ n), (f (ρ g v)).1 x = (f v).1 (x * g) := fun g v x => by
    rw [hfe]
    rfl
  have hint : ∀ v : V, Integrable (fun u : cellU y => (f v).1 (y⁻¹ * u)) μ := fun v =>
    integrable_cell h j hk y hyK hyw μ hμ χ hχ _ (hlaw v) {g | ρ g v = v} (hadm.1 v) (by simp)
      fun g hg x => by rw [← htr, show ρ g v = v from hg]
  let lam : V →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ u : cellU y, (f v).1 (y⁻¹ * u) ∂μ
      map_add' := fun a b => by
        simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c a => by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  have hlam : ∀ v, lam v = ∫ u : cellU y, (f v).1 (y⁻¹ * u) ∂μ := fun _ => rfl
  have hlamB : ∀ (b : GU σ n) (v : V), IsBorelU b →
      lam (ρ b v) = chiDeltaU q (fun i => (actU j χ i : ℂ)) b * lam v := by
    intro b v hb
    rw [hlam, hlam, ← integral_law h j hk y hyK hyw μ hμ χ _ (hlaw v) b hb]
    simp_rw [htr]
  let F : V →ₗ[ℂ] psSpaceU σ q (actU j χ) :=
    { toFun := fun v => ⟨fun g => lam (ρ g v), fun b g hb => by
        show lam (ρ (b * g) v) = _
        rw [map_mul, Module.End.mul_apply, hlamB b _ hb]⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by
        show lam (ρ g (a + b)) = lam (ρ g a) + lam (ρ g b)
        simp)
      map_smul' := fun c a => Subtype.ext (funext fun g => by
        show lam (ρ g (c • a)) = c * lam (ρ g a)
        simp) }
  have hFe : ∀ (g : GU σ n) (v : V), F (ρ g v) = psFunU σ q (actU j χ) g (F v) := fun g v =>
    Subtype.ext (funext fun x => by
      show lam (ρ x (ρ g v)) = lam (ρ (x * g) v)
      rw [map_mul, Module.End.mul_apply])

  obtain ⟨v₀, hv₀, hv₀0⟩ := (Submodule.ne_bot_iff _).1 hsph
  obtain ⟨Φ, hΦ, hΦ1, huniq⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) h (by omega) (by omega)
    (fun i => (χ i : ℂ)) fun i => (χ i).ne_zero
  have hsv : IsSphericalU q (fun i => (χ i : ℂ)) (f v₀).1 := by
    intro b g κ hb hκ
    rw [mul_assoc, hlaw v₀ b _ hb, ← htr, GlobalTheory.LGrp.mem_fixed.1 hv₀ κ hκ]
  have he := huniq _ hsv
  have hf0 : (f v₀).1 1 ≠ 0 := by
    intro h0
    apply hv₀0
    apply hf
    rw [map_zero]
    refine Subtype.ext ?_
    rw [he, h0]
    funext g
    simp
  have hlam0 : lam v₀ ≠ 0 := by
    have e : lam v₀ = (f v₀).1 1 * cSimpleU q j χ := by
      rw [hlam, ← (spherical_cell h j hk y hyK hyw μ hμ χ hχ Φ hΦ hΦ1).2, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun u => congrFun he _)
    rw [e]
    exact mul_ne_zero hf0 (cSimpleU_ne_zero hq2 j hk χ hχ)
  let W : Subrepresentation ρ := ⟨LinearMap.ker F, fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hFe, hv, map_zero]⟩
  have hW : W = ⊥ := by
    refine (hirr.eq_bot_or_eq_top W).resolve_right fun hT => ?_
    have h1 : v₀ ∈ W.toSubmodule := by
      rw [hT]
      trivial
    have h2 : F v₀ = 0 := h1
    have h3 := congrFun (congrArg Subtype.val h2) 1
    apply hlam0
    have h4 : lam (ρ 1 v₀) = 0 := h3
    simpa using h4
  refine ⟨F, ?_, hFe⟩
  rw [← LinearMap.ker_eq_bot]
  have := congrArg Subrepresentation.toSubmodule hW
  exact this

end GlobalTheory.CompanionTheory.InvStep

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReductionStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_inverse_reduction : PositivityTheory.SphericalProduct.InvStepU := by
  first | exact @GlobalTheory.CompanionTheory.InvStep.invStepU | exact GlobalTheory.CompanionTheory.InvStep.invStepU | (intros; apply GlobalTheory.CompanionTheory.InvStep.invStepU <;> assumption)
end
