module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmIndCoinvariants
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatSupportedNhdsIntegralOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatSupportedNhdsIntegralOne
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx

private theorem isLocallyConstant_indicator_const_of_isClopen {X : Type} [TopologicalSpace X] {B : Set X}
    (hB : IsClopen B) (c : ℂ) : IsLocallyConstant (B.indicator fun _ => c) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨B, hB.isOpen, hx, fun y hy => ?_⟩
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · refine ⟨Bᶜ, hB.isClosed.isOpen_compl, hx, fun y hy => ?_⟩
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem sigmaCompactSpace_of_isNonarchimedeanLocalField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ValueGroupWithZero k)ˣ)
  refine SigmaCompactSpace.of_countable
    (Set.range fun m : ℤ => {x : k | valuation k x ≤ ((g ^ m : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨m, rfl⟩
    exact IsNonarchimedeanLocalField.isCompact_closedBall k _
  · refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x = 0
    · subst hx
      refine Set.mem_sUnion.mpr ⟨_, ⟨0, rfl⟩, ?_⟩
      rw [Set.mem_ofPred_eq, map_zero]
      exact zero_le
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
        (hg (Units.mk0 (valuation k x) ((map_ne_zero (valuation k)).mpr hx)))
      refine Set.mem_sUnion.mpr ⟨_, ⟨m, rfl⟩, ?_⟩
      rw [Set.mem_ofPred_eq, hm, Units.val_mk0]


open GlobalTheory.SplitWeil.FourierPi in
theorem exists_SB_supported_integral_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (U : Set (n → k)) (_ : U ∈ nhds (0 : n → k)), ∃ Ψ : SB (n → k), (∀ y, y ∉ U → Ψ.1 y = 0) ∧ ∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν) = 1 := by
  intro k _ _ _ _ _ _ n _ _ ν _ U hU
  have := sigmaCompactSpace_of_isNonarchimedeanLocalField k
  obtain ⟨s, hsU⟩ := exists_box_subset (k := k) (n := n) hU
  have hBo : IsOpen (box (k := k) n s) := isOpen_box s
  have hBc : IsCompact (box (k := k) n s) := isCompact_box s
  have hBcl : IsClosed (box (k := k) n s) := isClosed_set_pi fun _ _ =>
    AddSubgroup.isClosed_of_isOpen
      { carrier := cball s
        zero_mem' := by
          show valuation k (0 : k) ≤ valuation k (s : k)
          rw [map_zero]
          exact zero_le
        add_mem' := add_mem_cball
        neg_mem' := neg_mem_cball } (isOpen_cball s)
  have hBm : MeasurableSet (box (k := k) n s) :=
    MeasurableSet.univ_pi fun _ => (isOpen_cball s).measurableSet
  have h0 : (0 : n → k) ∈ box (k := k) n s := by
    intro i _
    show valuation k (0 : k) ≤ valuation k (s : k)
    rw [map_zero]
    exact zero_le
  have hpos : 0 < (Measure.pi fun _ : n => ν) (box n s) := hBo.measure_pos _ ⟨0, h0⟩
  have hfin : (Measure.pi fun _ : n => ν) (box n s) < ⊤ := hBc.measure_lt_top
  have hreal : (Measure.pi fun _ : n => ν).real (box n s) ≠ 0 :=
    (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  set c : ℂ := (((Measure.pi fun _ : n => ν).real (box n s) : ℝ) : ℂ)⁻¹ with hc
  refine ⟨⟨(box (k := k) n s).indicator fun _ => c,
    isLocallyConstant_indicator_const_of_isClopen ⟨hBcl, hBo⟩ c,
    HasCompactSupport.intro' hBc hBcl fun y hy => Set.indicator_of_notMem hy _⟩, ?_, ?_⟩
  · intro y hy
    show (box (k := k) n s).indicator (fun _ => c) y = 0
    exact Set.indicator_of_notMem (fun hb => hy (hsU hb)) _
  · show ∫ y, (box (k := k) n s).indicator (fun _ => c) y ∂(Measure.pi fun _ => ν) = 1
    rw [integral_indicator_const c hBm, Complex.real_smul, hc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hreal)]

end GlobalTheory.RootEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatSupportedNhdsIntegralOneStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (U : Set (n → k)) (_ : U ∈ nhds (0 : n → k)), ∃ Ψ : SB (n → k), (∀ y, y ∉ U → Ψ.1 y = 0) ∧ ∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν) = 1 := by
  first | exact @GlobalTheory.RootEx.exists_SB_supported_integral_one | exact GlobalTheory.RootEx.exists_SB_supported_integral_one | (intros; apply GlobalTheory.RootEx.exists_SB_supported_integral_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeOperatorWeilRowUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeOperatorWeilRowUnipotent
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.RootEx.RowSign
open GlobalTheory.RootEx.Exchange

theorem mat_add_gRow {k : Type} [Field k] {n n' : Type} [DecidableEq n] {c : ℕ} (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (y : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k) :
    mat x₀ (y + gRow q u) = mat x₀ y + rowM n c (q.val + 1) u := by
  ext r s
  rcases r with r | l <;> rcases s with s | i <;>
    simp [mat, gRow, rowM, Fin.ext_iff, add_assoc]

private theorem ch_affPt_add_sRow {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    ch (affPt (q.val + 1) x₀ (e + sRow q u e)) = ch (affPt (q.val + 1) x₀ e) := by
  unfold ch
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [affPt, sRow]

theorem opE_om_rowE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (u : n' → k) (x₀ : Matrix n n' k), opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ.1) x₀ = opE ψ ν p (fun x => Φ.1 (x + rowM n c p u)) x₀ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψ ν _ μ Φ u x₀
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨q, rfl⟩ : ∃ q : Fin c, q.val + 1 = p := ⟨⟨p - 1, by omega⟩, by show p - 1 + 1 = p; omega⟩
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  have hA : Continuous fun e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k =>
      affPt (q.val + 1) x₀ e :=
    ((continuous_mat x₀).comp (continuous_wittExtendByZero _)).congr fun e => (affPt_eq _ x₀ e).symm
  have hch : Continuous fun x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => ch x :=
    continuous_finsetSum _ fun i _ => continuous_id.matrix_elem _ _
  set f : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) → ℂ := fun e =>
    Φ.1 (affPt (q.val + 1) x₀ e + rowM n c (q.val + 1) u) * (ψ (-ch (affPt (q.val + 1) x₀ e)) : ℂ) with hf_def
  have hf : Continuous f := by
    refine (hΦ.1.continuous.comp (hA.add continuous_const)).mul ?_
    exact continuous_subtype_val.comp (hψ.comp (hch.comp hA).neg)
  have hS : Continuous (sRow (n := n) (n' := n') q u) := by
    refine continuous_pi fun i => ?_
    rcases i with ⟨⟨r, s | s⟩, hi⟩
    · exact ((continuous_apply _).comp (continuous_wittExtendByZero _)).mul continuous_const
    · exact continuous_const
  have h0 : ∀ e (i : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs}),
      ¬ (∃ s, i.1.2 = Sum.inl s) → sRow q u e i = 0 := by
    rintro e ⟨⟨r, s | s⟩, hi⟩ h
    · exact absurd ⟨s, rfl⟩ h
    · rfl
  have h1 : ∀ e e' : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k,
      (∀ i, ¬ (∃ s, i.1.2 = Sum.inl s) → e i = e' i) → sRow q u e = sRow q u e' := by
    intro e e' he
    funext i
    rcases i with ⟨⟨r, s | s⟩, hi⟩
    · simp only [sRow, Sum.elim_inl]
      congr 1
      simp only [ext0]
      split_ifs with h
      · exact he _ (by simp)
      · rfl
    · rfl
  have hL : ∀ e, om μ (rowE (c + 1) (q.val + 1) u) 1 Φ.1 (affPt (q.val + 1) x₀ e) *
      (ψ (-ch (affPt (q.val + 1) x₀ e)) : ℂ) = f (e + sRow q u e) := by
    intro e
    rw [om_rowE, affPt_mul_rowE, mat_add_gRow, ← affPt_eq]
    simp only [hf_def, ch_affPt_add_sRow]
  unfold opE
  simp_rw [hL]
  exact integral_shear ν (fun i => ∃ s, i.1.2 = Sum.inl s) (sRow q u) hS h0 h1 f hf

end GlobalTheory.RootEx.RowSign
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeOperatorWeilRowUnipotentStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (u : n' → k) (x₀ : Matrix n n' k), opE ψ ν p (om μ (rowE (c + 1) p u) 1 Φ.1) x₀ = opE ψ ν p (fun x => Φ.1 (x + rowM n c p u)) x₀ := by
  first | exact @GlobalTheory.RootEx.RowSign.opE_om_rowE | exact GlobalTheory.RootEx.RowSign.opE_om_rowE | (intros; apply GlobalTheory.RootEx.RowSign.opE_om_rowE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeHeisenbergVariableSign
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeHeisenbergVariableSign
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.RootEx.HeisenbergSign

theorem colE_inv_eq {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    ((colE c p β)⁻¹ : GL (n ⊕ Fin c) k).val = 1 - ((colE c p β).val - 1) := by
  rw [ExchangeSupport.colE_inv_val, ExchangeSupport.colE_val]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

theorem mat_add_gCol {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (q : Fin c) (ξ : n → k) (x₀ : Matrix n n' k) (y : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k) :
    Exchange.mat x₀ (y + Exchange.gCol q ξ) = Exchange.mat x₀ y + colM c (q.val + 1) ξ := by
  ext r s
  rcases r with r | l <;> rcases s with s | i <;>
    simp [Exchange.mat, Exchange.gCol, colM, add_assoc, Fin.ext_iff]

theorem sign : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) (β : n → k) (r : n) (i : Fin (c + 1)), i.val + 1 = ρ + 1 → ((1 - ((colE c (ρ + 1) β).val - 1)) * affPt (ρ + 1) x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (Sum.inl r) (Sum.inr i) = -β r) ∧ ∀ (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (β : n → k), (∀ x, om μ 1 (colE c (ρ + 1) β) Φ.1 x = Φ.1 ((1 - ((colE c (ρ + 1) β).val - 1)) * x)) ∧ ∀ x₀, fl ψ ν μ ρ Φ.1 x₀ β = opE ψ ν (ρ + 1) (fun x => Φ.1 (x + colM c (ρ + 1) (-β))) x₀ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ρ _ hρc
  refine ⟨fun x₀ e β r i hi => ?_, fun ψ ν _ hψ μ Φ β => ⟨fun x => ?_, fun x₀ => ?_⟩⟩
  ·
    have hi' : i = Fin.castSucc (⟨ρ, hρc⟩ : Fin c) := Fin.ext (by simp; omega)
    subst hi'
    have h := congrFun (Exchange.col_colE_inv_mul (n' := n') (⟨ρ, hρc⟩ : Fin c) β x₀ e) r
    simp only at h
    rw [← colE_inv_eq]
    exact neg_eq_iff_eq_neg.mp h
  · rw [Exchange.om_colE, colE_inv_eq]
  ·
    have hch : ∀ (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (p : ℕ) (ξ : n → k),
        ch (y + colM c p ξ) = ch y := by
      intro y p ξ
      simp [ch, colM]
    have hmem : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
    have key := Exchange.opE_colE hψ ν μ (⟨ρ, hρc⟩ : Fin c) (⟨ρ, hρc⟩ : Fin c)
      (χ := fun _ => (1 : ℂ)) continuous_const hmem.1.continuous x₀ β
    dsimp only at key
    refine Eq.trans ?_ (key.trans ?_)
    · simp [fl]
    · rw [opE]
      congr 1
      funext e
      rw [mat_add_gCol, ← Exchange.affPt_eq]
      simp only [Exchange.big, one_mul, hch]

end GlobalTheory.RootEx.HeisenbergSign
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeHeisenbergVariableSignStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchange_heisenbergVariable_sign : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) (β : n → k) (r : n) (i : Fin (c + 1)), i.val + 1 = ρ + 1 → ((1 - ((colE c (ρ + 1) β).val - 1)) * affPt (ρ + 1) x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (Sum.inl r) (Sum.inr i) = -β r) ∧ ∀ (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (β : n → k), (∀ x, om μ 1 (colE c (ρ + 1) β) Φ.1 x = Φ.1 ((1 - ((colE c (ρ + 1) β).val - 1)) * x)) ∧ ∀ x₀, fl ψ ν μ ρ Φ.1 x₀ β = opE ψ ν (ρ + 1) (fun x => Φ.1 (x + colM c (ρ + 1) (-β))) x₀ := by
  first | exact @GlobalTheory.RootEx.HeisenbergSign.sign | exact GlobalTheory.RootEx.HeisenbergSign.sign | (intros; apply GlobalTheory.RootEx.HeisenbergSign.sign <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumSmulOfLocallyConstantCompactSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumSmulOfLocallyConstantCompactSupport
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.LocConstTensor

theorem exists_sum (Z : Type) [TopologicalSpace Z] [T2Space Z] (V : Type) [AddCommGroup V]
    [Module ℂ V] (T : Z → V) (hT : IsLocallyConstant T) (K : Set Z) (hK : IsCompact K)
    (h0 : ∀ y, y ∉ K → T y = 0) :
    ∃ (m : ℕ) (v : Fin m → V) (Φ : Fin m → SB Z), ∀ y, T y = ∑ i, (Φ i).1 y • v i := by
  classical
  have hfin : (T '' K).Finite := by
    letI : TopologicalSpace V := ⊥
    haveI : DiscreteTopology V := ⟨rfl⟩
    exact (hK.image hT.continuous).finite_of_discrete
  let S : Finset V := hfin.toFinset.erase 0
  let e : Fin S.card ≃ S := S.equivFin.symm
  have hmem : ∀ w : V, w ≠ 0 → (fun y => if T y = w then (1 : ℂ) else 0) ∈ SB Z := by
    intro w hw
    refine ⟨hT.comp (fun u => if u = w then (1 : ℂ) else 0), ?_⟩
    refine HasCompactSupport.intro hK ?_
    intro y hy
    rw [h0 y hy, if_neg (Ne.symm hw)]
  refine ⟨S.card, fun i => (e i : V),
    fun i => ⟨_, hmem (e i) (Finset.ne_of_mem_erase (e i).2)⟩, fun y => ?_⟩
  have h1 : ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)
      = ∑ w ∈ S, (if T y = w then (1 : ℂ) else 0) • w := by
    rw [← Finset.sum_coe_sort S]
    exact Equiv.sum_comp e (fun w : S => (if T y = (w : V) then (1 : ℂ) else 0) • (w : V))
  change T y = ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)
  rw [h1]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    refine Finset.mem_erase.2 ⟨hne, hfin.mem_toFinset.2 ⟨y, ?_, rfl⟩⟩
    by_contra hy
    exact hne (h0 y hy)

end GlobalTheory.LocConstTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumSmulOfLocallyConstantCompactSupportStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport : ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] (V : Type) [AddCommGroup V] [Module ℂ V] (T : Z → V) (_ : IsLocallyConstant T) (K : Set Z) (_ : IsCompact K) (_ : ∀ y, y ∉ K → T y = 0), ∃ (m : ℕ) (v : Fin m → V) (Φ : Fin m → SB Z), ∀ y, T y = ∑ i, (Φ i).1 y • v i := by
  first | exact @GlobalTheory.LocConstTensor.exists_sum | exact GlobalTheory.LocConstTensor.exists_sum | (intros; apply GlobalTheory.LocConstTensor.exists_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergSubgroupFourierJacobiCommutator
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergSubgroupFourierJacobiCommutator
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.RootEx.HeisenbergSubgroup

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

def zM (c p : ℕ) (t : k) : Matrix (Fin c) (Fin c) k :=
  Matrix.of fun l i => if l.val + 1 = p ∧ i.val + 1 = p + 1 then t else 0

def hM (c p : ℕ) (u β : n → k) (t : k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  fromBlocks 1 (ExchangeSupport.colM c (p + 1) β) (ExchangeSupport.rowM c p u) (1 + zM c p t)

theorem zM_add (s t : k) : zM c p (s + t) = zM c p s + zM c p t := by
  ext l i
  simp only [zM, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem zM_zero : zM c p (0 : k) = 0 := by
  ext l i
  simp [zM]

theorem zM_mul (s t : k) : zM c p s * zM c p t = 0 := by
  ext l i
  simp only [Matrix.mul_apply, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [Fintype n] [DecidableEq n] in
theorem col_mul_zM (β : n → k) (t : k) : ExchangeSupport.colM c (p + 1) β * zM c p t = 0 := by
  ext r i
  simp only [Matrix.mul_apply, ExchangeSupport.colM, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [Fintype n] [DecidableEq n] in
theorem zM_mul_row (u : n → k) (t : k) : zM c p t * ExchangeSupport.rowM c p u = 0 := by
  ext l s
  simp only [Matrix.mul_apply, ExchangeSupport.rowM, zM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h₁ h₂ <;> first | (exfalso; omega) | simp

omit [DecidableEq n] in
theorem row_mul_col (u β : n → k) :
    ExchangeSupport.rowM c p u * ExchangeSupport.colM c (p + 1) β = zM c p (u ⬝ᵥ β) := by
  ext l i
  simp only [Matrix.mul_apply, ExchangeSupport.rowM, ExchangeSupport.colM, zM, Matrix.of_apply]
  by_cases hl : l.val + 1 = p <;> by_cases hi : i.val + 1 = p + 1 <;> simp [hl, hi, dotProduct]

omit [Fintype n] [DecidableEq n] in
theorem row_add (u w : n → k) : ExchangeSupport.rowM c p (u + w) =
    ExchangeSupport.rowM c p u + ExchangeSupport.rowM c p w := by
  ext l s
  simp only [ExchangeSupport.rowM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
theorem col_add (u w : n → k) : ExchangeSupport.colM c p (u + w) =
    ExchangeSupport.colM c p u + ExchangeSupport.colM c p w := by
  ext r i
  simp only [ExchangeSupport.colM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
theorem row_zero : ExchangeSupport.rowM c p (0 : n → k) = 0 := by
  ext l s
  simp [ExchangeSupport.rowM]

omit [Fintype n] [DecidableEq n] in
theorem col_zero : ExchangeSupport.colM c p (0 : n → k) = 0 := by
  ext r i
  simp [ExchangeSupport.colM]

theorem hM_mul (u β u' β' : n → k) (t t' : k) :
    hM c p u β t * hM c p u' β' t' = hM c p (u + u') (β + β') (t + t' + u ⬝ᵥ β') := by
  simp only [hM, Matrix.fromBlocks_multiply]
  congr 1
  · rw [ExchangeSupport.colM_mul_rowM, Matrix.one_mul, add_zero]
  · rw [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, col_mul_zM, add_zero, col_add]
    abel
  · rw [Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, zM_mul_row, add_zero, row_add]
  · rw [row_mul_col]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, zM_mul, zM_add]
    abel

omit [Fintype n] in
theorem hM_zero : hM c p (0 : n → k) 0 0 = 1 := by
  rw [hM, row_zero, col_zero, zM_zero, add_zero, Matrix.fromBlocks_one]

theorem rowE_eq (u : n → k) : (rowE c p u).val = hM c p u 0 0 := by
  rw [ExchangeSupport.rowE_val, hM, col_zero, zM_zero, add_zero]

theorem colE_eq (β : n → k) : (colE c (p + 1) β).val = hM c p 0 β 0 := by
  rw [ExchangeSupport.colE_val, hM, row_zero, zM_zero, add_zero]

theorem cenM_eq (t : k) : cenM n c p t = hM c p 0 0 t := by
  rw [hM, row_zero, col_zero]
  rfl

theorem prod_eq (u β : n → k) (t : k) :
    (rowE c p u).val * (colE c (p + 1) β).val * cenM n c p t = hM c p u β (u ⬝ᵥ β + t) := by
  rw [rowE_eq, colE_eq, cenM_eq, hM_mul, hM_mul]
  simp only [add_zero, zero_add, dotProduct_zero]

def Heisenberg₂ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | ∃ (u β : n → k) (t : k), g.val = hM c p u β t}
  one_mem' := ⟨0, 0, 0, hM_zero.symm⟩
  mul_mem' := by
    rintro g h ⟨u, β, t, hg⟩ ⟨u', β', t', hh⟩
    exact ⟨_, _, _, by rw [Units.val_mul, hg, hh, hM_mul]⟩
  inv_mem' := by
    rintro g ⟨u, β, t, hg⟩
    refine ⟨-u, -β, u ⬝ᵥ β - t, Units.inv_eq_of_mul_eq_one_right ?_⟩
    rw [hg, hM_mul, ← hM_zero (p := p)]
    simp

theorem mem_N_of_val {g : GL (n ⊕ Fin c) k} {β : n → k} {t : k} (hg : g.val = hM c p 0 β t) :
    g ∈ N k n c p := by
  show g ∈ Subgroup.closure {g | InN p g}
  refine Subgroup.subset_closure ?_
  intro r s hrs
  rw [hg, hM, row_zero]
  rcases r with a | l <;> rcases s with b | i
  · simp [Matrix.one_apply]
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₁₂, ExchangeSupport.colM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · simp
  · simp only [lev, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.add_apply, zM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp [Matrix.one_apply]

private theorem eMat_mem_N_succ (u : n → k) : rowE c p u ∈ N k n c (p + 1) := by
  show rowE c p u ∈ Subgroup.closure {g | InN (p + 1) g}
  refine Subgroup.subset_closure ?_
  intro r s hrs
  rw [ExchangeSupport.rowE_val]
  rcases r with a | l <;> rcases s with b | i
  · simp [Matrix.one_apply]
  · simp
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₂₁, ExchangeSupport.rowM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · simp [Matrix.one_apply]

theorem heis_le : Heisenberg₂ k n c p ≤ NFJ k n c p := by
  rintro g ⟨u, β, t, hg⟩
  have hinv : rowE c p u * rowE c p (-u) = 1 := by
    rw [← ExchangeSupport.rowE_add, add_neg_cancel, ExchangeSupport.rowE_zero]
  have hsplit : g = rowE c p u * (rowE c p (-u) * g) := by
    rw [← mul_assoc, hinv, one_mul]
  have hrest : rowE c p (-u) * g ∈ N k n c p := by
    refine mem_N_of_val (β := β) (t := t - u ⬝ᵥ β) ?_
    rw [Units.val_mul, hg, rowE_eq, hM_mul]
    simp only [neg_add_cancel, zero_add, neg_dotProduct]
    ring_nf
  rw [hsplit]
  exact Subgroup.mul_mem _ (le_sup_right (a := N k n c p) (eMat_mem_N_succ u))
    (le_sup_left (b := N k n c (p + 1)) hrest)

end

theorem heisenberg_subgroup : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∃ H : Subgroup (GL (n ⊕ Fin c) k), H ≤ NFJ k n c ρ ∧ ∀ g, g ∈ H ↔ ∃ (u β : n → k) (t : k), g.val = (rowE c ρ u).val * (colE c (ρ + 1) β).val * cenM n c ρ t) ∧ ∀ u β₀ : n → k, (rowE c ρ u * colE c (ρ + 1) β₀).val = cenM n c ρ (u ⬝ᵥ β₀) * (colE c (ρ + 1) β₀ * rowE c ρ u).val := by
  intro k _ n _ _ c ρ _ _
  refine ⟨⟨Heisenberg₂ k n c ρ, heis_le, fun g => ?_⟩, fun u β₀ => ?_⟩
  · constructor
    · rintro ⟨u, β, t, hg⟩
      refine ⟨u, β, t - u ⬝ᵥ β, ?_⟩
      rw [prod_eq, hg]
      congr 1
      ring
    · rintro ⟨u, β, t, hg⟩
      exact ⟨u, β, u ⬝ᵥ β + t, by rw [hg, prod_eq]⟩
  · rw [Units.val_mul, Units.val_mul, rowE_eq, colE_eq, cenM_eq, hM_mul, hM_mul, hM_mul]
    simp only [add_zero, zero_add, dotProduct_zero, zero_dotProduct]

end GlobalTheory.RootEx.HeisenbergSubgroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergSubgroupFourierJacobiCommutatorStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergSubgroup_fourierJacobi_commutator : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∃ H : Subgroup (GL (n ⊕ Fin c) k), H ≤ NFJ k n c ρ ∧ ∀ g, g ∈ H ↔ ∃ (u β : n → k) (t : k), g.val = (rowE c ρ u).val * (colE c (ρ + 1) β).val * cenM n c ρ t) ∧ ∀ u β₀ : n → k, (rowE c ρ u * colE c (ρ + 1) β₀).val = cenM n c ρ (u ⬝ᵥ β₀) * (colE c (ρ + 1) β₀ * rowE c ρ u).val := by
  first | exact @GlobalTheory.RootEx.HeisenbergSubgroup.heisenberg_subgroup | exact GlobalTheory.RootEx.HeisenbergSubgroup.heisenberg_subgroup | (intros; apply GlobalTheory.RootEx.HeisenbergSubgroup.heisenberg_subgroup <;> assumption)
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx.FourierJacobi
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL ev)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem heisenberg : Heisenberg k := by
  intro n _ _ c ρ h1 hc
  have h2 : ρ < c := by omega
  refine ⟨(GlobalTheory.T.fourierJacobiUnipotent_eq_prod_rootExchange k n c ρ h1 h2).1, (GlobalTheory.T.exists_heisenbergSubgroup_fourierJacobi_commutator k n c ρ h1 h2).1, (GlobalTheory.T.exists_heisenbergSubgroup_fourierJacobi_commutator k n c ρ h1 h2).2, ?_⟩
  intro ψ hψ _ u β₀ Φ₀
  refine ⟨⟨Φ₀.2.1.comp_continuous (continuous_add_const β₀),
    Φ₀.2.2.comp_homeomorph (Homeomorph.addRight β₀)⟩,
    ⟨(((GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField k).2 ψ hψ).comp_continuous (f := fun β : n → k => u ⬝ᵥ β) (by fun_prop)).mul Φ₀.2.1,
      Φ₀.2.2.mul_left⟩, ?_⟩
  funext β
  simp only [schM, schT, Pi.smul_apply, smul_eq_mul, dotProduct_add, ← mul_assoc, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul]
  congr 3
  ring

section Bessel
variable {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} {ψ : AddChar k Circle} {ν : Measure k}
  {P A : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
  {σ : Representation ℂ (GL (n ⊕ Fin c) k) A}
  {fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ} {b b₀ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ}

omit [DecidableEq n] in
theorem sb_int [ν.IsAddHaarMeasure] {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    Integrable f (Measure.pi fun _ => ν) := by
  have := secondCountable k
  have := t2Space k
  exact hf.1.continuous.integrable_of_hasCompactSupport hf.2

def stab (ρ : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (v : A) : Set (n → k) :=
  {β | σ (colE c (ρ + 1) β) v = v}

omit [MeasurableSpace k] [BorelSpace k] in
theorem stab_nhds (hσ : IsSmoothRep σ) (v : A) : stab ρ σ v ∈ 𝓝 (0 : n → k) :=
  ((hσ v).preimage ExchangeSupport.continuous_colE).mem_nhds (by simp [ExchangeSupport.colE_zero])

theorem fj_conv [ν.IsAddHaarMeasure] (hfj : IsFJ ψ ρ σ fj) (Φ Ψ : SB (n → k)) :
    ∃ w : SB (n → k), (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧
      (∀ x, w.1 x = ∫ y, Ψ.1 y * Φ.1 (x - y) ∂(Measure.pi fun _ => ν)) ∧
      ∀ φ v, fj φ v w = ∫ y, Φ.1 y * fj φ (σ (colE c (ρ + 1) y) v) Ψ ∂(Measure.pi fun _ => ν) := by
  obtain ⟨T, w, hT, h1, h2, h3⟩ := GlobalTheory.T.exists_schwartzBruhat_convolution_localFieldPower k n ν Φ Ψ
  refine ⟨w, h1, h2, fun φ v => ?_⟩
  rw [h3]
  congr 1; funext y
  rw [hfj.1 φ v y (T y) Ψ (by funext β; simp [schT, hT])]

omit [DecidableEq n] [BorelSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [Field k] in
theorem integral_mul_of_support {U : Set (n → k)} {Ψ f : (n → k) → ℂ} {z : ℂ} (h0 : ∀ y, y ∉ U → Ψ y = 0)
    (h1 : ∀ y ∈ U, f y = z) :
    ∫ y, Ψ y * f y ∂(Measure.pi fun _ => ν) = (∫ y, Ψ y ∂(Measure.pi fun _ => ν)) * z := by
  rw [← integral_mul_const]
  congr 1; funext y
  by_cases hy : y ∈ U
  · rw [h1 y hy]
  · simp [h0 y hy]

theorem fj_indep [ν.IsAddHaarMeasure] (hfj : IsFJ ψ ρ σ fj) (φ : P) (v : A) (Φ Ψ : SB (n → k))
    (hΦ : ∀ y, y ∉ stab ρ σ v → Φ.1 y = 0) (hΦ1 : ∫ y, Φ.1 y ∂(Measure.pi fun _ => ν) = 1)
    (hΨ : ∀ y, y ∉ stab ρ σ v → Ψ.1 y = 0) (hΨ1 : ∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν) = 1) :
    fj φ v Φ = fj φ v Ψ := by
  obtain ⟨w, h1, -, h3⟩ := fj_conv (ν := ν) hfj Φ Ψ
  obtain ⟨w', -, h2', h3'⟩ := fj_conv (ν := ν) hfj Ψ Φ
  have e : w = w' := Subtype.ext (funext fun x => (h1 x).trans (h2' x).symm)
  have a := h3 φ v
  have a' := h3' φ v
  rw [integral_mul_of_support (z := fj φ v Ψ) hΦ (fun y hy => by rw [show σ _ v = v from hy]), hΦ1, one_mul] at a
  rw [integral_mul_of_support (z := fj φ v Φ) hΨ (fun y hy => by rw [show σ _ v = v from hy]), hΨ1, one_mul] at a'
  rw [← a, ← a', e]

theorem exists_represents [ν.IsAddHaarMeasure] (h1 : 1 ≤ ρ) (h2 : ρ < c) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hσ : IsSmoothRep σ) (hfj : IsFJ ψ ρ σ fj) : ∃ b, Represents ψ ν ρ σ fj b := by
  choose Ψ hΨ hΨ1 using fun v : A => GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν _ (stab_nhds (ρ := ρ) hσ v)
  have key : ∀ U ∈ 𝓝 (0 : n → k), ∃ Φ : SB (n → k), (∀ y, y ∉ U → Φ.1 y = 0) ∧
      ∫ y, Φ.1 y ∂(Measure.pi fun _ => ν) = 1 ∧ ∀ φ v, U ⊆ stab ρ σ v → fj φ v (Ψ v) = fj φ v Φ := by
    intro U hU
    obtain ⟨Φ, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν U hU
    exact ⟨Φ, a, a1, fun φ v hv => fj_indep hfj φ v _ _ (hΨ v) (hΨ1 v) (fun y hy => a y fun h => hy (hv h)) a1⟩
  let b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun φ v => fj φ v (Ψ v)) (by intros; simp) (by intros; simp)
    (by
      intro φ v w
      obtain ⟨Φ, -, -, h⟩ := key _ (inter_mem (stab_nhds (ρ := ρ) hσ v) (stab_nhds (ρ := ρ) hσ w))
      rw [h φ v Set.inter_subset_left, h φ w Set.inter_subset_right, h φ (v + w)]
      · simp
      · intro y hy
        change σ _ _ = _
        rw [map_add (f := _), show σ _ v = v from hy.1, show σ _ w = w from hy.2])
    (by
      intro z φ v
      obtain ⟨Φ, -, -, h⟩ := key _ (stab_nhds (ρ := ρ) hσ v)
      rw [h φ v subset_rfl, h φ (z • v)]
      · simp
      · intro y hy
        change σ _ _ = _
        rw [map_smul, show σ _ v = v from hy])
  have hb : ∀ φ v, b φ v = fj φ v (Ψ v) := fun _ _ => rfl
  have hN : ∀ φ, IsNEquiv ψ (ρ + 1) σ (b φ) := by
    intro φ g hg v
    obtain ⟨g₁, hg₁, u, rfl⟩ := RadicalDecomp.succ_decomp k n c ρ g hg
    obtain ⟨-, hs, -, -, -, -, hr, -⟩ := Radical.unipotent_radical_basic k n c (ρ + 1)
    have hu : {β : n → k | (ψ ((-u) ⬝ᵥ β) : ℂ) = 1} ∈ 𝓝 (0 : n → k) :=
      ((((GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField k).2 ψ hψ).comp_continuous (f := fun β : n → k => (-u) ⬝ᵥ β)
        (by fun_prop)).isOpen_fiber 1).mem_nhds (by simp)
    obtain ⟨Φ, a, -, h⟩ := key _ (inter_mem (inter_mem (stab_nhds (ρ := ρ) hσ v)
      (stab_nhds (ρ := ρ) hσ (σ (g₁ * rowE c ρ u) v))) hu)
    rw [hb, hb, h φ v fun y hy => hy.1.1, h φ _ fun y hy => hy.1.2, map_mul, Module.End.mul_apply,
      hfj.2.2 φ _ Φ g₁ hg₁, hs _ hg₁.2 _ (hr ρ u (by omega)).1, (hr ρ u (by omega)).2, add_zero,
      hfj.2.1 φ v u Φ Φ]
    funext β
    by_cases hβ : (ψ ((-u) ⬝ᵥ β) : ℂ) = 1
    · rw [schM, hβ, one_mul]
    · rw [schM, a β fun h => hβ h.2, mul_zero]
  refine ⟨b, hN, fun φ v Φ₀ => ⟨?_, ?_⟩⟩
  · have := ((ExchangeSupport.exchange_support k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ (b φ) v).2 (hN φ)).1
    exact sb_int ⟨Φ₀.2.1.mul this.1, Φ₀.2.2.mul_right⟩
  · obtain ⟨K, hK, hKi⟩ := GlobalTheory.QuotInt.exists_open_stab (G := Multiplicative (n → k))
      (F := fun x => Φ₀.1 x.toAdd) Φ₀.2
    have hK' : {y : n → k | Multiplicative.ofAdd y ∈ K} ∈ 𝓝 (0 : n → k) := hK.mem_nhds K.one_mem
    obtain ⟨Φ, a, a1, h⟩ := key _ (inter_mem (stab_nhds (ρ := ρ) hσ v) hK')
    obtain ⟨w, -, e2, e3⟩ := fj_conv (ν := ν) hfj Φ₀ Φ
    have e : w = Φ₀ := by
      refine Subtype.ext (funext fun x => ?_)
      rw [e2, integral_mul_of_support (z := Φ₀.1 x) a, a1, one_mul]
      intro y hy
      rw [sub_eq_add_neg]
      exact hKi (Multiplicative.ofAdd x) _ (K.inv_mem hy.2)
    rw [← e, e3, e]
    congr 1; funext y
    rw [hb, h]
    intro β hβ
    change σ _ _ = _
    rw [← Module.End.mul_apply, ← map_mul, ← ExchangeSupport.colE_add, add_comm β y, ExchangeSupport.colE_add,
      map_mul, Module.End.mul_apply, show σ _ v = v from hβ.1]

theorem represents_eval (hb : Represents ψ ν ρ σ fj b) (φ : P) (v : A) (Ψ : SB (n → k))
    (hΨ : ∀ y, y ∉ stab ρ σ v → Ψ.1 y = 0) :
    fj φ v Ψ = (∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν)) * b φ v := by
  rw [(hb.2 φ v Ψ).2, integral_mul_of_support hΨ (fun y hy => by rw [show σ _ v = v from hy])]

theorem exchanges_eq (h1 : 1 ≤ ρ) (h2 : ρ < c) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hν : IsSelfDual ψ ν)
    (hσ : IsSmoothRep σ) (h : ExchangesTo ψ ν ρ σ b₀ b) (φ : P) (v : A) : b₀ φ v = exDown ν ρ σ (b φ) v := by
  rw [← (exDown_exUp_and_exUp_exDown k n c ρ h1 h2 ψ hψ hψ1 ν hν A σ hσ (b₀ φ) v).1 (h.1 φ)]
  congr 1
  funext w
  exact (h.2 φ w).2.symm

theorem uniqueBessel : UniqueBessel k := by
  intro n _ _ c ρ h1 hc ψ ν hψ hψ1 hν P A _ _ _ _ σ hσ fj hfj
  have h2 : ρ < c := by omega
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hS := ExchangeSupport.exchange_support k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ
  refine ⟨existsUnique_of_exists_of_unique (exists_represents h1 h2 hψ hψ1 hσ hfj) fun b b' hb hb' => ?_,
    fun b hb => ⟨existsUnique_of_exists_of_unique ?_ fun b₀ b₁ h h' => ?_, fun b₀ h φ v Φ₀ => ?_⟩⟩
  · ext φ v
    obtain ⟨Ψ, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν _ (stab_nhds (ρ := ρ) hσ v)
    have e := represents_eval hb φ v Ψ a
    rw [represents_eval hb' φ v Ψ a, a1, one_mul, one_mul] at e
    exact e.symm
  · choose L hL hL' using fun φ =>
      (Exchange.exchange_isPos k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ).2.1 (b φ) (hb.1 φ)
    refine ⟨⟨⟨L, fun φ φ' => ?_⟩, fun z φ => ?_⟩, hL', fun φ v => ⟨sb_int ((hS _ v).1 (hL' φ)).1, ?_⟩⟩
    · ext v
      simp only [hL, exDown, map_add (f := _), LinearMap.add_apply]
      exact integral_add (sb_int ((hS _ v).2 (hb.1 φ)).1) (sb_int ((hS _ v).2 (hb.1 φ')).1)
    · ext v
      simp only [hL, exDown, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, integral_const_mul]
    · rw [← (exDown_exUp_and_exUp_exDown k n c ρ h1 h2 ψ hψ hψ1 ν hν A σ hσ (b φ) v).2 (hb.1 φ)]
      congr 1
      funext w
      exact (hL φ w).symm
  · ext φ v
    rw [exchanges_eq h1 h2 hψ hψ1 hν hσ h, exchanges_eq h1 h2 hψ hψ1 hν hσ h']
  · obtain ⟨s1, -, s3⟩ := (hS (b₀ φ) v).1 (h.1 φ)
    have hh := (GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n ψ hψ hψ1 ν hν).1 Φ₀
    refine ⟨sb_int ⟨hh.1.mul s1.1, hh.2.mul_right⟩, ?_⟩
    rw [(hb.2 φ v Φ₀).2]
    simp only [(h.2 φ _).2, s3, hat, ← integral_const_mul, ← integral_mul_const]
    rw [integral_integral_swap]
    · congr 1; funext u; congr 1; funext β; ring
    · have := ((sb_int (ν := ν) Φ₀.2).mul_prod (sb_int (ν := ν) s1)).bdd_mul (c := 1)
        (f := fun z : (n → k) × (n → k) => (ψ (z.2 ⬝ᵥ z.1) : ℂ))
        (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => (Circle.norm_coe _).le)
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry]
      ring

theorem exponents : Exponents k := by
  intro n _ _ c ρ h1 hc ψ ν hψ hψ1 hν P A _ _ _ _ π σ _ hσ η _ _ fj b _ hb
  have h2 : ρ < c := by omega
  have := hν.1
  have main : ∀ s e : ℝ, s + e + 1 = 0 → IsFJInv η s π σ fj → ∀ (g : GL n k) φ v,
      b (twist η π g φ) (σ (embX c g) v) =
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ e : ℝ) : ℂ) * b φ v := by
    intro s e hse hinv g φ v
    obtain ⟨Ψ, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν _ (stab_nhds (ρ := ρ) hσ v)
    let T : (n → k) ≃ₜ (n → k) :=
      { toFun := fun β => (g⁻¹ : GL n k).val *ᵥ β
        invFun := fun β => g.val *ᵥ β
        left_inv := fun β => by simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
        right_inv := fun β => by simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let Φ : SB (n → k) := ((η (Matrix.GeneralLinearGroup.det g) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ)) •
        ⟨fun β => Ψ.1 (T β), Ψ.2.1.comp_continuous T.continuous, Ψ.2.2.comp_homeomorph T⟩
    have e1 := hinv g φ v Ψ Φ rfl
    have hpos : 0 < nabs k (Matrix.GeneralLinearGroup.det g) := by
      simp only [nabs]; exact_mod_cast distribHaarChar_pos
    have hinv' : (nabs k (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ = nabs k (Matrix.GeneralLinearGroup.det g) := by
      simp [nabs]
    have e2 : ∫ y, Φ.1 y ∂(Measure.pi fun _ => ν) = (η (Matrix.GeneralLinearGroup.det g) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (s + 1) : ℝ) : ℂ) := by
      have := (linear_change_of_variables k n n ν).1 g⁻¹ Ψ.1
      rw [a1, hinv'] at this
      change ∫ y, _ * Ψ.1 ((g⁻¹ : GL n k).val *ᵥ y) ∂_ = _
      rw [integral_const_mul, this, Real.rpow_add hpos]
      simp [mul_assoc]
    rw [represents_eval hb φ v Ψ a, a1, one_mul, represents_eval hb _ _ Φ, e2] at e1
    · change b ((η (Matrix.GeneralLinearGroup.det g) : ℂ) • π g φ) _ = _
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← e1]
      have : ((nabs k (Matrix.GeneralLinearGroup.det g) ^ e : ℝ) : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (s + 1) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.rpow_add hpos, show e + (s + 1) = 0 by linarith]
        simp
      linear_combination (-(η (Matrix.GeneralLinearGroup.det g) : ℂ) * b (π g φ) (σ (embX c g) v)) * this
    · intro y hy
      change _ * Ψ.1 ((g⁻¹ : GL n k).val *ᵥ y) = 0
      rw [a _ fun h => hy ?_, mul_zero]
      have h' : σ _ v = v := h
      rw [← QuotStep.conj_colE, map_inv, inv_inv] at h'
      change σ _ _ = _
      conv_rhs => rw [← h']
      simp only [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨main, fun hinv => ?_⟩
  have hp : IsPos ψ (ρ + 1) (twist η π) σ b :=
    ⟨hb.1, main _ _ (by rw [hc]; push_cast; ring) hinv⟩
  refine ⟨hp, fun b₀ h => ?_⟩
  obtain ⟨b', e, hb'⟩ := ((Exchange.exchange_isPos k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ).2.2 P _ b).2 hp
  have : b₀ = b' := by
    ext φ v
    rw [e, exchanges_eq h1 h2 hψ hψ1 hν hσ h]
  exact this ▸ hb'

end Bessel

theorem localSign : LocalSign k := by
  intro n n' _ _ _ _ c ρ h1 hc
  have h2 : ρ < c := by omega
  refine ⟨(GlobalTheory.T.mem_fourierJacobiSubgroup_iff_parabolic_mul_column k n c ρ h1 h2).1,
    GlobalTheory.T.isUnimodular_blockUpperTriangular_symmetricLevels k n c _ _ (fun i => ?_) _ ((GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries k n c ρ).2 h1 h2),
    (GlobalTheory.T.rootExchange_heisenbergVariable_sign k n n' c ρ h1 h2).1, fun ψ ν hψ _ hν => ?_⟩
  · have := i.2
    simp only [Fin.val_rev]
    omega
  · have := hν.1
    exact ⟨fun μ _ => (GlobalTheory.T.rootExchange_heisenbergVariable_sign k n n' c ρ h1 h2).2 ψ ν hψ μ,
      fun μX μG _ _ => GlobalTheory.T.weil_formula_rootExchange_parabolic_quotient k n c ρ h1 h2 ν μX μG⟩

theorem target : Target k := by
  intro n n' _ _ _ _ c ρ h1 hc ψ ν hψ hψ1 hν μ hμ μX μG hX hG P A P' A' _ _ _ _ _ _ _ _ π σ π' σ' _ hσ _ _
    ϑ θ _ hθ fj b b' _ hb hp _ φ F
  have h2 : ρ < c := by omega
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hμ' := (GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField k).1 μ hμ
  have main : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ h, Integrable (fun β : n → k => b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β)
          (σ (colE c (ρ + 1) β) (σ h F))) (Measure.pi fun _ => ν)) ∧
      ∀ z : ℂ,
        (IsQuotInt ν μX μG (ρ + 1) (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1) z ↔
          IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k,
            b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
              ∂(Measure.pi fun _ => ν)) z) ∧
        (IsQuotInt ν μX μG (ρ + 1) (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1) z ↔
          IsFJInt ψ ν μX μG μ ρ σ θ fj φ F Φ.1 z) := by
    intro Φ
    have e : ∀ h β, b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F)) =
        rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1 (colE c (ρ + 1) β * h) := by
      intro h β
      have := om_mul μ 1 1 (colE c (ρ + 1) β) h Φ.1
      rw [one_mul] at this
      rw [rInt, this, map_mul]
      rfl
    obtain ⟨z₀, hz₀⟩ := exists_isQuotInt_unfolding k n n' c (ρ + 1) (by omega) h2 ψ hψ hψ1 ν μ hμ' μX μG A σ hσ
      P P' π π' θ hθ b hp φ F Φ (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1) fun h Ψ hΨ => by rw [rInt, ← hΨ, app_coe]
    have W := GlobalTheory.T.weil_formula_rootExchange_parabolic_quotient k n c ρ h1 h2 ν μX μG (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1)
    have val : ∀ h w, HasTensorVal (fun Ψ Φ₀ => fj (θ φ Ψ) (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) w ↔
        w = ∫ β : n → k, b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
          ∂(Measure.pi fun _ => ν) := by
      intro h
      have v1 : ∀ w, HasTensorVal (fun Ψ Φ₀ => fj (θ φ Ψ) (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) w →
          w = ∫ β : n → k, b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
            ∂(Measure.pi fun _ => ν) := by
        rintro w ⟨m, Ψ, Φ₀, hd, rfl⟩
        simp only [(hb.2 _ _ _).2]
        rw [← MeasureTheory.integral_finsetSum _ fun i _ => (hb.2 _ _ _).1]
        congr 1; funext β
        have : (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) = (∑ i, (Φ₀ i).1 β • Ψ i : SB (Matrix n n' k)).1 := by
          funext x₀
          simp [hd, mul_comm]
        rw [this, app_coe]
        simp
      let T : (n → k) → SB (Matrix n n' k) := fun β =>
        opL hψ ν (ρ + 1) (omR μ (1, colE c (ρ + 1) β) (omR μ (1, h) Φ))
      have hT : IsLocallyConstant T :=
        ((orbit_locallyConstant (omR_smooth hμ') (omR μ (1, h) Φ)).comp_continuous
          (continuous_const.prodMk ExchangeSupport.continuous_colE)).comp fun Ψ => opL hψ ν (ρ + 1) Ψ
      obtain ⟨K, hK, HK⟩ := ColumnSupport.opE_colE_eq_zero k n n' c ρ h2 ψ ν μ _ (omR μ (1, h) Φ).2
      obtain ⟨m, Ψ, Φ₀, hd⟩ := GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport (n → k) _ T hT K hK fun β hβ => Subtype.ext (by
        have := HK β hβ fun _ => 1
        simp only [one_mul] at this
        exact this)
      have v2 : HasTensorVal (fun Ψ Φ₀ => fj (θ φ Ψ) (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) _ :=
        ⟨m, Ψ, Φ₀, fun x y => by
          have := congrArg (fun t : SB (Matrix n n' k) => t.1 x) (hd y)
          refine Eq.trans this ?_
          simp [mul_comm], rfl⟩
      exact fun w => ⟨v1 w, fun hw => by rw [hw, ← v1 _ v2]; exact v2⟩
    have i1 : ∀ z, IsQuotInt ν μX μG (ρ + 1) (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1) z ↔
          IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k,
            b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
              ∂(Measure.pi fun _ => ν)) z := by
      intro z
      simp only [e]
      exact ⟨fun hz => (W z hz).2, fun hz => GlobalTheory.T.eq_of_isQuotIntFJ_of_isQuotIntFJ k n c ρ h1 h2 ν μX μG _ _ _ (W z₀ hz₀).2 hz ▸ hz₀⟩
    refine ⟨fun h => ?_, fun z => ⟨i1 z, (i1 z).trans ⟨fun hz => ⟨_, fun h => (val h _).2 rfl, hz⟩, ?_⟩⟩⟩
    · simp only [e]
      exact (W z₀ hz₀).1 h
    · rintro ⟨f, hf, hz⟩
      rwa [show f = _ from funext fun h => (val h _).1 (hf h)] at hz
  refine ⟨fun Φ => ⟨fun h => (opL hψ ν (ρ + 1) (omR μ (1, h) Φ)).2,
    fun h β => (opL hψ ν (ρ + 1) (omR μ (1, colE c (ρ + 1) β) (omR μ (1, h) Φ))).2, main Φ⟩,
    forall_congr' fun Φ => ((main Φ).2 _).2⟩

theorem source : Source k := by
  intro n n' _ _ _ _ c ρ hc ψ ν hψ hψ1 hν μ hμ μX μG hX hG P A P' A' _ _ _ _ _ _ _ _ π σ π' σ' _ _ _ _
    ϑ θ hϑ _ fj' b b' _ _ hfj φ F
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hμ' := (GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField k).1 μ hμ
  have hF := GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n' ψ hψ hψ1 ν hν
  have main : ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Φ₀ : SB (n' → k)),
      ∃ w : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), avg ψ ν μ ρ Φ₀ Φ.1 = w.1 ∧
      (∀ h, opE ψ ν ρ (om μ 1 h w.1) = opEFJ ψ ν ρ Φ₀ (om μ 1 h Φ.1)) ∧ fj' φ (ϑ F Φ) Φ₀ = b' φ (ϑ F w) := by
    intro Φ Φ₀
    have hh := hF.1 Φ₀
    let T : (n' → k) → SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := fun u =>
      hat ψ ν Φ₀.1 u • omR μ (rowE (c + 1) ρ u, 1) Φ
    have hT : IsLocallyConstant T :=
      (hh.1.prodMk ((orbit_locallyConstant (omR_smooth hμ') Φ).comp_continuous
        (ExchangeSupport.continuous_rowE.prodMk continuous_const))).comp fun z => z.1 • z.2
    obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n' → k)
      (Measure.pi fun _ => ν) _ T hT _ hh.2 fun u hu => by
        simp only [T, image_eq_zero_of_notMem_tsupport hu, zero_smul]
    refine ⟨w, funext fun x => (hw (ev x)).symm, fun h => funext fun x₀ => ?_, ?_⟩
    · refine (hw ((ev x₀).comp ((opL hψ ν ρ).comp (omR μ (1, h))))).trans ?_
      rw [opEFJ]
      congr 1; funext u
      simp only [T, LinearMap.comp_apply, map_smul, smul_eq_mul]
      congr 1
      have := GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent k n n' c ρ (by omega) (by omega) ψ hψ ν μ (omR μ (1, h) Φ) u x₀
      rw [← omR_val, omR_mul, one_mul, mul_one] at this
      rw [omR_mul, one_mul, mul_one]
      exact this
    · rw [hfj]
      refine Eq.trans ?_ (hw ((b' φ).comp (ϑ F))).symm
      congr 1; funext u
      have := hϑ (rowE (c + 1) ρ u) 1 F Φ (omR μ (rowE (c + 1) ρ u, 1) Φ) rfl
      rw [map_one, Module.End.one_apply] at this
      simp only [T, LinearMap.comp_apply, map_smul, smul_eq_mul, this]
  refine ⟨GlobalTheory.T.isUnimodular_blockUpperTriangular_symmetricLevels k n c _ _ (fun i => ?_) _ (GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries k n c ρ).1, fun Φ Φ₀ => ?_, fun H Φ => ?_,
    fun H Φ Φ₀ => ?_⟩
  · have := i.2
    simp only [Fin.val_rev]
    omega
  · obtain ⟨w, e1, e2, e3⟩ := main Φ Φ₀
    rw [e1, app_coe]
    exact ⟨w.2, fun h => (opL hψ ν ρ (omR μ (1, h) Φ)).2, fun h => e2 h ▸ (opL hψ ν ρ (omR μ (1, h) w)).2, e2, e3⟩
  · have hU : {u : n' → k | omR μ (rowE (c + 1) ρ u, 1) Φ = Φ} ∈ 𝓝 (0 : n' → k) :=
      ((omR_smooth hμ' Φ).preimage (ExchangeSupport.continuous_rowE.prodMk continuous_const)).mem_nhds (by
        change omR μ (rowE (c + 1) ρ 0, 1) Φ = Φ
        rw [ExchangeSupport.rowE_zero, ← Prod.one_eq_mk, map_one, Module.End.one_apply])
    obtain ⟨g, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n' ν _ hU
    obtain ⟨Φ₀, h0⟩ := hF.2 g
    obtain ⟨w, e1, e2, e3⟩ := main Φ Φ₀
    have e : w = Φ := by
      refine Subtype.ext (e1.symm.trans (funext fun x => ?_))
      rw [avg, h0, integral_mul_of_support (z := Φ.1 x) a, a1, one_mul]
      intro u hu
      exact congrArg (fun t : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) => t.1 x) hu
    have := H Φ Φ₀
    simp only [← e2, e3, e] at this
    exact this
  · obtain ⟨w, -, e2, e3⟩ := main Φ Φ₀
    simp only [← e2, e3]
    exact H w

theorem fourierJacobiBessel : FourierJacobiBessel :=
  fun _ _ _ _ _ _ _ => ⟨heisenberg, uniqueBessel, exponents, localSign, target, source⟩

end GlobalTheory.RootEx.FourierJacobi
