module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiRowAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiRowAdd
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LocFlat

theorem add_right_mem_SB {m m' k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
    {Φ : Matrix m m' k → ℂ} (hΦ : Φ ∈ SB (Matrix m m' k)) (a : Matrix m m' k) :
    (fun z => Φ (z + a)) ∈ SB (Matrix m m' k) :=
  ⟨hΦ.1.comp_continuous (continuous_add_const a), hΦ.2.comp_homeomorph (Homeomorph.addRight a)⟩

theorem flRow_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → GlobalTheory.LocFlat.flRow ψ ν p (Φ₁ + Φ₂) = GlobalTheory.LocFlat.flRow ψ ν p Φ₁ + GlobalTheory.LocFlat.flRow ψ ν p Φ₂ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p Φ₁ Φ₂ h₁ h₂
  funext x
  have H := opE_smul_add p hψ ν (1 : ℂ)
    (add_right_mem_SB h₁ (rowAt n c p (x (Sum.inr ()))))
    (add_right_mem_SB h₂ (rowAt n c p (x (Sum.inr ()))))
  have H' := congrFun H x.toRows₁
  simp only [one_smul, Pi.add_apply] at H'
  simp only [flRow, Pi.add_apply]
  rw [← H']
  rfl

end GlobalTheory.LocFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiRowAddStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMapFourierJacobiRow_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → GlobalTheory.LocFlat.flRow ψ ν p (Φ₁ + Φ₂) = GlobalTheory.LocFlat.flRow ψ ν p Φ₁ + GlobalTheory.LocFlat.flRow ψ ν p Φ₂ := by
  first | exact @GlobalTheory.LocFlat.flRow_add | exact GlobalTheory.LocFlat.flRow_add | (intros; apply GlobalTheory.LocFlat.flRow_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqFlatMapFourierJacobiRow
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqFlatMapFourierJacobiRow
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.RedFlatRow
open GlobalTheory.PartRed GlobalTheory.LocFlat

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_transSet_union_upSet (ρ : ℕ) (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :
    e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) ↔ Free (ρ + 1) e := by
  rcases e with ⟨r | l, s | i⟩ <;> simp only [transSet, upSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] <;> simp [Free] <;> omega

def freeEquiv (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) :
    {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} ≃
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} :=
  Equiv.subtypeEquivRight (mem_transSet_union_upSet ρ)

theorem fill_eq (ρ : ℕ) (lρ : Fin c) (hl : lρ.val = ρ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    fillAt (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) (transSet ρ ∪ upSet ρ) x y =
      affPt (ρ + 1) (fun r s => x (Sum.inl r) (Sum.inl s)) (fun rs => y ((freeEquiv n n' c ρ).symm rs)) +
        rowAt n c (ρ + 1) (fun s => x (Sum.inr lρ) (Sum.inl s)) := by
  ext r q
  simp only [fillAt, affPt, Matrix.add_apply, Matrix.of_apply]
  by_cases hI : (r, q) ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))
  · have hF : Free (ρ + 1) (r, q) := (mem_transSet_union_upSet ρ _).1 hI
    rw [dite_eq_left hI, dite_eq_left hF]
    have h1 : (freeEquiv n n' c ρ).symm ⟨(r, q), hF⟩ = ⟨(r, q), hI⟩ := rfl
    rw [h1]
    rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state
  · have hF : ¬ Free (ρ + 1) (r, q) := fun hF => hI ((mem_transSet_union_upSet ρ _).2 hF)
    rw [dite_eq_right hI, dite_eq_right hF]
    by_cases hE : (r, q) ∈ (fixSet ρ ∪ lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))
    · rw [if_pos hE]
      simp only [fixSet, lowSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hE
      rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF hE ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state
    · rw [if_neg hE]
      simp only [fixSet, lowSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hE
      rcases r with r | l <;> rcases q with s | i <;> simp [basePt, rowAt, Free, Matrix.fromBlocks] at hF hE ⊢ <;> (try split_ifs) <;> first | rfl | (exfalso; omega) | (have hl' : l = lρ := Fin.ext (by omega); subst hl'; simp) | simp | omega | trace_state

theorem ch_add_rowAt (p : ℕ) (A : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (u : n' → k) :
    ch (A + rowAt n c p u) = ch A := by
  simp [ch, rowAt, Matrix.fromBlocks]

theorem piCongrLeft_freeEquiv [MeasurableSpace k] (ρ : ℕ)
    (y : {e // e ∈ (transSet ρ ∪ upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))))} → k) :
    MeasurableEquiv.piCongrLeft (fun _ => k) (freeEquiv n n' c ρ) y =
      fun rs => y ((freeEquiv n n' c ρ).symm rs) := by
  funext rs
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

end GlobalTheory.RedFlatRow


open GlobalTheory.RedFlatRow in
theorem GlobalTheory.RedFlatRow.red_eq_flRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ + 1 → ∀ (lρ : Fin c), lρ.val = ρ → ∀ (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.PartRed.red ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) (GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ) Φ x = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ (Matrix.of fun r s => Sum.elim (fun r => x (Sum.inl r) (Sum.inl s)) (fun _ => x (Sum.inr lρ) (Sum.inl s)) r) := by
  intro k _ _ _ _ _ _ ψ ν hν n n' _ _ _ _ c ρ _ lρ hl Φ x
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  have hmp := MeasureTheory.measurePreserving_piCongrLeft (α := fun _ => k)
    (fun _ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} => ν) (freeEquiv n n' c ρ)
  simp only [GlobalTheory.PartRed.red, GlobalTheory.LocFlat.flRow, opE]
  refine Eq.trans ?_ (hmp.integral_comp' _)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [piCongrLeft_freeEquiv, fill_eq ρ lρ hl x y, GlobalTheory.PartRed.chL_apply, ch_add_rowAt]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqFlatMapFourierJacobiRowStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_eq_flatMapFourierJacobiRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ + 1 → ∀ (lρ : Fin c), lρ.val = ρ → ∀ (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.PartRed.red ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) (GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ) Φ x = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ (Matrix.of fun r s => Sum.elim (fun r => x (Sum.inl r) (Sum.inl s)) (fun _ => x (Sum.inr lρ) (Sum.inl s)) r) := by
  first | exact @GlobalTheory.RedFlatRow.red_eq_flRow | exact GlobalTheory.RedFlatRow.red_eq_flRow | (intros; apply GlobalTheory.RedFlatRow.red_eq_flRow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionIntegrateEntryOfTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionIntegrateEntryOfTranslation
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology

noncomputable section
namespace GlobalTheory.PartRed.IntEntry

theorem fill_entry {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
    (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by
  obtain ⟨r, q⟩ := e
  simp [fillAt, hI, hE]

theorem fill_add_single {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
    (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) (a : k) :
    fillAt β E I (x + Matrix.single e.1 e.2 a) y = fillAt β E I x y + Matrix.single e.1 e.2 a := by
  obtain ⟨r₀, q₀⟩ := e
  ext r q
  by_cases h1 : (r, q) ∈ I
  · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hI h1
    simp [fillAt, h1, Matrix.single_apply, this]
  · by_cases h2 : (r, q) ∈ E
    · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hE h2
      simp [fillAt, h1, h2, Matrix.single_apply, this]
    · simp [fillAt, h1, h2]

theorem measurePreserving_adjoin {ι X : Type} [DecidableEq ι] [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν]
    (I : Finset ι) (e : ι) (he : e ∉ I) :
    MeasurePreserving
      (fun (p : X × (I → X)) (i : ↥(insert e I : Finset ι)) => if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1)
      (ν.prod (Measure.pi fun _ : I => ν)) (Measure.pi fun _ : ↥(insert e I : Finset ι) => ν) := by
  have hm : Measurable
      (fun (p : X × (I → X)) (i : ↥(insert e I : Finset ι)) => if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1) := by
    refine Measurable.of_eval fun i => ?_
    by_cases h : i.1 ∈ I
    · simp only [dif_pos h]; fun_prop
    · simp only [dif_neg h]; fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (p : X × (I → X)) (i : ↥(insert e I : Finset ι)) =>
      if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1) ⁻¹' Set.univ.pi s =
      s ⟨e, Finset.mem_insert_self e I⟩ ×ˢ Set.univ.pi fun i : I => s ⟨i.1, Finset.mem_insert_of_mem i.2⟩ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa [he] using h ⟨e, Finset.mem_insert_self e I⟩, fun i => ?_⟩
      simpa [i.2] using h ⟨i.1, Finset.mem_insert_of_mem i.2⟩
    · rintro ⟨h1, h2⟩ ⟨i, hi⟩
      by_cases h : i ∈ I
      · simpa [h] using h2 ⟨i, h⟩
      · obtain rfl : i = e := (Finset.mem_insert.1 hi).resolve_right h
        simpa [h] using h1
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Finset.univ_eq_attach (insert e I), Finset.attach_insert,
    Finset.prod_insert, Finset.prod_image, Finset.univ_eq_attach]
  · intro a _ b _ hab
    exact Subtype.ext (congrArg (fun z : ↥(insert e I : Finset ι) => z.1) hab)
  · intro h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    have : a.1 = e := congrArg (fun z : ↥(insert e I : Finset ι) => z.1) ha
    exact he (this ▸ a.2)

theorem integrable_red : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ x : Matrix R Q k, Integrable (fun y : I → k => Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ)) (Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν R Q _ _ _ _ w β E I Φ hΦ x
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : (Measure.pi fun _ : I => ν).IsAddHaarMeasure := inferInstance
  have hf : Continuous (fillAt β E I x) := by
    refine continuous_matrix fun r q => ?_
    simp only [fillAt, Matrix.of_apply]
    by_cases h : (r, q) ∈ I
    · simp only [dif_pos h]; fun_prop
    · simp only [dif_neg h]; fun_prop
  have hw : Continuous w := by
    have : (w : Matrix R Q k → k) = fun t => ∑ r, ∑ q, t r q * w (Matrix.single r q 1) := by
      funext t
      conv_lhs => rw [Matrix.matrix_eq_sum_single t]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ => ?_
      rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this]
    fun_prop
  have hc : Continuous fun y : I → k => Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ) :=
    (hΦ.1.continuous.comp hf).mul (continuous_subtype_val.comp (hψ.comp (hw.comp hf).neg))
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (K := Set.univ.pi fun i : I => (fun t : Matrix R Q k => t i.1.1 i.1.2) '' tsupport Φ)
    (isCompact_univ_pi fun i => hΦ.2.image (by fun_prop)) fun y hy => ?_)
  rw [image_eq_zero_of_notMem_tsupport (f := Φ) fun h => hy fun i _ => ⟨_, h, ?_⟩, zero_mul]
  simp [fillAt, i.2]

theorem red_insert : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k), Integrable (fun y : ↥(insert e I : Finset (R × Q)) → k => Φ (fillAt β E (insert e I) x y) * (ψ (-w (fillAt β E (insert e I) x y)) : ℂ)) (Measure.pi fun _ => ν) → red ψ ν w β E (insert e I) Φ x = ∫ s, red ψ ν w β E I Φ (x + Matrix.single e.1 e.2 (s - x e.1 e.2)) ∂ν := by
  intro k _ _ _ _ _ _ ψ ν hψ hν R Q _ _ _ _ w β E I e hE hI Φ x hint
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hmp := measurePreserving_adjoin ν I e hI
  have hfill : ∀ p : k × (I → k), fillAt β E (insert e I) x
      (fun i => if h : i.1 ∈ I then p.2 ⟨i.1, h⟩ else p.1) =
      fillAt β E I (x + Matrix.single e.1 e.2 (p.1 - x e.1 e.2)) p.2 := by
    intro p
    obtain ⟨r₀, q₀⟩ := e
    ext r q
    by_cases h1 : (r, q) ∈ I
    · simp [fillAt, h1]
    · by_cases h2 : (r, q) = (r₀, q₀)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
        simp [fillAt, h1, hE]
      · have h3 : (r, q) ∉ insert (r₀, q₀) I := by
          rw [Finset.mem_insert, not_or]; exact ⟨h2, h1⟩
        have h4 : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact h2 rfl
        simp only [fillAt, Matrix.of_apply, dif_neg h1, dif_neg h3, Matrix.add_apply, Matrix.single_apply,
          if_neg h4, add_zero]
  have h1 := hmp.integrable_comp_of_integrable hint
  unfold red
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hint.1)]
  refine (integral_prod _ h1).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact congrArg (fun t => Φ t * (ψ (-w t) : ℂ)) (hfill (s, y))

theorem exists_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (e : R × Q) (c : k), ∃ U : AddSubgroup k, IsOpen (U : Set k) ∧ IsCompact (U : Set k) ∧ ∀ u ∈ U, ψ (u * c) = 1 ∧ ∀ t, Φ (t + Matrix.single e.1 e.2 u) = Φ t := by
  intro k _ _ _ _ ψ hψ R Q _ _ _ _ Φ hΦ e c
  have hs : Continuous fun u : k => Matrix.single e.1 e.2 u := by
    refine continuous_matrix fun r q => ?_
    simp only [Matrix.single_apply]
    by_cases h : e.1 = r ∧ e.2 = q
    · simp only [if_pos h]; fun_prop
    · simp only [if_neg h]; fun_prop
  have h1 : ∀ᶠ u in 𝓝 (0 : k), ∀ z ∈ tsupport Φ, Φ (z + Matrix.single e.1 e.2 u) = Φ z := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : k × Matrix R Q k => (Φ (q.2 + Matrix.single e.1 e.2 q.1), Φ q.2) :=
      (hΦ.1.comp_continuous (continuous_snd.add (hs.comp continuous_fst))).prodMk
        (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, Matrix.single_zero, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s₀, hs₀⟩ := exists_cball_addChar_eq_one ψ hψ
  have h3 : ∀ᶠ u in 𝓝 (0 : k), ψ (u * c) = 1 := by
    have : (fun u : k => u * c) ⁻¹' cball s₀ ∈ 𝓝 (0 : k) :=
      ((isOpen_cball s₀).preimage (by fun_prop)).mem_nhds (by simp [cball])
    filter_upwards [this] with u hu using hs₀ _ hu
  obtain ⟨s, hUs⟩ := exists_cball_subset (h1.and h3)
  refine ⟨HaarFactor.cballSub s, isOpen_cball s, isCompact_cball s, fun u hu => ⟨(hUs hu).2, fun z => ?_⟩⟩
  by_cases hz : z ∈ tsupport Φ
  · exact (hUs hu).1 z hz
  by_cases hz' : z + Matrix.single e.1 e.2 u ∈ tsupport Φ
  · have := (hUs (neg_mem_cball hu)).1 _ hz'
    rw [add_assoc, ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

theorem exists_representatives : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [Fintype Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (U : AddSubgroup k), IsOpen (U : Set k) → ∀ e : R × Q, ∃ S : Finset k, (∀ a ∈ S, ∀ b ∈ S, a - b ∈ U → a = b) ∧ ∀ t : Matrix R Q k, Φ t ≠ 0 → ∃ a ∈ S, t e.1 e.2 - a ∈ U := by
  intro k _ _ _ _ R Q _ _ Φ hΦ U hU e
  classical
  have hK : IsCompact ((fun t : Matrix R Q k => t e.1 e.2) '' tsupport Φ) := hΦ.2.image (by fun_prop)
  obtain ⟨T, -, hT⟩ := hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set k))
    (fun a _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨T.image fun a : k => (a : k ⧸ U).out, ?_, fun t ht => ?_⟩
  · intro a ha b hb hab
    obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b', -, rfl⟩ := Finset.mem_image.1 hb
    have := QuotientAddGroup.eq_iff_sub_mem.mpr hab
    rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
    rw [this]
  · obtain ⟨a, ha, hta⟩ := Set.mem_iUnion₂.mp (hT ⟨t, subset_tsupport Φ ht, rfl⟩)
    refine ⟨_, Finset.mem_image.mpr ⟨a, ha, rfl⟩, QuotientAddGroup.eq_iff_sub_mem.mp ?_⟩
    rw [QuotientAddGroup.out_eq']
    exact QuotientAddGroup.eq_iff_sub_mem.mpr hta

theorem integral_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (U : AddSubgroup k), IsOpen (U : Set k) → IsCompact (U : Set k) → ∀ (S : Finset k), (∀ a ∈ S, ∀ b ∈ S, a - b ∈ U → a = b) → ∀ h : k → ℂ, (∀ s u, u ∈ U → h (s + u) = h s) → (∀ s, h s ≠ 0 → ∃ a ∈ S, s - a ∈ U) → ∫ s, h s ∂ν = ((ν (U : Set k)).toReal : ℂ) * ∑ a ∈ S, h a := by
  intro k _ _ _ _ _ _ ν hν U hUo hUc S hS h hinv hsupp
  haveI := secondCountable k
  haveI := t2Space k
  have he := HaarFactor.integrable_of_SB ν (HaarFactor.ind_mem hUo hUc)
  have hshift : ∀ c : k, ∫ a, (U : Set k).indicator (fun _ => (1 : ℂ)) (a - c) ∂ν = (ν.real (U : Set k) : ℂ) := by
    intro c
    rw [integral_sub_right_eq_self (fun a => (U : Set k).indicator (fun _ => (1 : ℂ)) a) c,
      integral_indicator_const _ hUo.measurableSet]
    simp
  have hT : ∀ s, h s = ∑ a ∈ S, h a * (U : Set k).indicator (fun _ => (1 : ℂ)) (s - a) := by
    intro s
    have hv : ∀ a, s - a ∈ U → h s = h a := fun a ha => by rw [← hinv a _ ha, add_sub_cancel]
    by_cases hs : h s = 0
    · rw [hs]
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      by_cases ha : s - a ∈ U
      · rw [← hv a ha, hs, zero_mul]
      · rw [Set.indicator_of_notMem (show s - a ∉ (U : Set k) from ha), mul_zero]
    · obtain ⟨a, ha, hsa⟩ := hsupp s hs
      rw [Finset.sum_eq_single a]
      · rw [Set.indicator_of_mem (show s - a ∈ (U : Set k) from hsa), mul_one, hv a hsa]
      · intro b hb hba
        rw [Set.indicator_of_notMem, mul_zero]
        intro hsb
        have hm := U.sub_mem hsa hsb
        rw [sub_sub_sub_cancel_left] at hm
        exact hba (hS b hb a ha hm)
      · exact fun ha' => absurd ha ha'
  rw [integral_congr_ae (Filter.Eventually.of_forall hT),
    MeasureTheory.integral_finsetSum _ fun q _ => (he.comp_sub_right _).const_mul _]
  simp only [integral_const_mul, hshift, ← Finset.sum_mul]
  rw [mul_comm]
  rfl

theorem indicator_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [Fintype Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (U : AddSubgroup k), IsOpen (U : Set k) → ∀ (e : R × Q) (a : k), Set.indicator {t : Matrix R Q k | t e.1 e.2 - a ∈ U} Φ ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ R Q _ _ Φ hΦ U hU e a
  have hc : Continuous fun t : Matrix R Q k => t e.1 e.2 - a := by fun_prop
  have hcl : IsClopen {t : Matrix R Q k | t e.1 e.2 - a ∈ U} :=
    ⟨(U.isClosed_of_isOpen hU).preimage hc, hU.preimage hc⟩
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hΦ.2 fun y hy => ?_⟩
  · by_cases hx : x ∈ {t : Matrix R Q k | t e.1 e.2 - a ∈ U}
    · filter_upwards [hcl.isOpen.mem_nhds hx, hΦ.1.eventually_eq x] with z hz hz'
      exact (Set.indicator_of_mem (s := {t : Matrix R Q k | t e.1 e.2 - a ∈ U}) hz Φ).trans
        (hz'.trans (Set.indicator_of_mem hx Φ).symm)
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz
      exact (Set.indicator_of_notMem (s := {t : Matrix R Q k | t e.1 e.2 - a ∈ U}) hz Φ).trans
        (Set.indicator_of_notMem hx Φ).symm
  · exact Set.indicator_apply_eq_zero.mpr fun _ => image_eq_zero_of_notMem_tsupport hy

theorem red_shift : ∀ (k : Type) [Field k] [TopologicalSpace k] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (u : k), (∀ t, Φ (t + Matrix.single e.1 e.2 u) = Φ t) → ψ (u * w (Matrix.single e.1 e.2 1)) = 1 → ∀ x, red ψ ν w β E I Φ (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ x := by
  intro k _ _ _ ψ ν R Q _ _ _ _ w β E I e hE hI Φ u hΦ hψ x
  have hw : w (Matrix.single e.1 e.2 u) = u * w (Matrix.single e.1 e.2 1) := by
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have h1 : ψ (-w (Matrix.single e.1 e.2 u)) = 1 := by rw [AddChar.map_neg_eq_inv, hw, hψ, inv_one]
  unfold red
  simp only [fill_add_single β E I x _ e hI hE u, hΦ, map_add (f := _), neg_add, AddChar.map_add_eq_mul, h1, mul_one]

theorem red_indicator : ∀ (k : Type) [Field k] [TopologicalSpace k] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (A : Set k) (x : Matrix R Q k), red ψ ν w β E I (Set.indicator {t : Matrix R Q k | t e.1 e.2 ∈ A} Φ) x = Set.indicator {z : Matrix R Q k | z e.1 e.2 ∈ A} (red ψ ν w β E I Φ) x := by
  intro k _ _ _ ψ ν R Q _ _ _ _ w β E I e hE hI Φ A x
  by_cases hx : x e.1 e.2 ∈ A
  · rw [Set.indicator_of_mem (show x ∈ {z : Matrix R Q k | z e.1 e.2 ∈ A} from hx)]
    unfold red
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [Set.indicator_of_mem]
    show fillAt β E I x y e.1 e.2 ∈ A
    rwa [fill_entry β E I x y e hI hE]
  · rw [Set.indicator_of_notMem (show x ∉ {z : Matrix R Q k | z e.1 e.2 ∈ A} from hx)]
    unfold red
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [Set.indicator_of_notMem, zero_mul, Pi.zero_apply]
    show ¬ fillAt β E I x y e.1 e.2 ∈ A
    rwa [fill_entry β E I x y e hI hE]

theorem red_support : ∀ (k : Type) [Field k] [TopologicalSpace k] [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k), red ψ ν w β E I Φ x ≠ 0 → ∃ t, Φ t ≠ 0 ∧ t e.1 e.2 = x e.1 e.2 := by
  intro k _ _ _ ψ ν R Q _ _ _ _ w β E I e hE hI Φ x hx
  by_contra hne
  refine hx (integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_))
  have : Φ (fillAt β E I x y) = 0 := by
    by_contra h
    exact hne ⟨_, h, fill_entry β E I x y e hI hE⟩
  simp [this]

theorem integrate_entry : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.IntLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β E (insert e I) := by
  intro k _ _ _ _ _ _ ψ ν hψ hν R Q _ _ _ _ M _ _ L w β E I e heE hK hInt
  by_cases heI : e ∈ I
  · rwa [Finset.insert_eq_of_mem heI]
  intro Φ hΦ
  obtain ⟨U, hUo, hUc, hU⟩ := exists_subgroup k ψ hψ R Q Φ.1 Φ.2 e (w (Matrix.single e.1 e.2 1))
  obtain ⟨S, hSd, hS⟩ := exists_representatives k R Q Φ.1 Φ.2 U hUo e
  have hsh : ∀ x (u : k), u ∈ U → red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 u) = red ψ ν w β E I Φ.1 x :=
    fun x u hu => red_shift k ψ ν R Q w β E I e heE heI Φ.1 u (hU u hu).2 (hU u hu).1 x
  have hlin : ∀ (f : k → Matrix R Q k → ℂ), (∀ a, f a ∈ SB (Matrix R Q k)) → ∀ x,
      red ψ ν w β E I (∑ a ∈ S, f a) x = ∑ a ∈ S, red ψ ν w β E I (f a) x := by
    intro f hf x
    unfold red
    simp only [Finset.sum_apply, Finset.sum_mul]
    exact MeasureTheory.integral_finsetSum S fun a _ => integrable_red k ψ ν hψ hν R Q w β E I (f a) (hf a) x
  have hsum : ∀ x, ∑ a ∈ S, red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 (a - x e.1 e.2)) = 0 := by
    intro x
    have h0 : red ψ ν w β E (insert e I) Φ.1 x = 0 := congrFun hΦ x
    rw [red_insert k ψ ν hψ hν R Q w β E I e heE heI Φ.1 x
      (integrable_red k ψ ν hψ hν R Q w β E (insert e I) Φ.1 Φ.2 x)] at h0
    rw [integral_cosets k ν hν U hUo hUc S hSd
      (fun s => red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 (s - x e.1 e.2))) ?_ ?_] at h0
    · have h1 : ν (U : Set k) ≠ 0 := hUo.measure_ne_zero ν ⟨0, U.zero_mem⟩
      have h2 : ν (U : Set k) ≠ ⊤ := hUc.measure_lt_top.ne
      have hpos : ((ν (U : Set k)).toReal : ℂ) ≠ 0 := by
        exact_mod_cast (ENNReal.toReal_pos h1 h2).ne'
      exact (mul_eq_zero.1 h0).resolve_left hpos
    · intro s u hu
      rw [show s + u - x e.1 e.2 = (s - x e.1 e.2) + u by ring, Matrix.single_add, ← add_assoc]
      exact hsh _ u hu
    · intro s hs
      obtain ⟨t, ht, hte⟩ := red_support k ψ ν R Q w β E I e heE heI Φ.1 _ hs
      obtain ⟨a, ha, hta⟩ := hS t ht
      refine ⟨a, ha, ?_⟩
      have hxe : (x + Matrix.single e.1 e.2 (s - x e.1 e.2)) e.1 e.2 = s := by
        rw [Matrix.add_apply, Matrix.single_apply_same, add_sub_cancel]
      rw [hte, hxe] at hta
      exact hta
  let Φc : k → SB (Matrix R Q k) := fun a =>
    ⟨Set.indicator {t : Matrix R Q k | t e.1 e.2 - a ∈ U} Φ.1, indicator_mem k R Q Φ.1 Φ.2 U hUo e a⟩
  have hcov : ∑ a ∈ S, Φc a = Φ := by
    apply Subtype.ext
    funext t
    rw [Submodule.coe_sum, Finset.sum_apply]
    by_cases ht : Φ.1 t = 0
    · rw [ht]
      exact Finset.sum_eq_zero fun a _ => Set.indicator_apply_eq_zero.mpr fun _ => ht
    · obtain ⟨a, ha, hta⟩ := hS t ht
      rw [Finset.sum_eq_single a]
      · exact Set.indicator_of_mem (s := {t : Matrix R Q k | t e.1 e.2 - a ∈ U}) hta Φ.1
      · intro b hb hba
        refine Set.indicator_of_notMem (s := {t : Matrix R Q k | t e.1 e.2 - b ∈ U}) ?_ Φ.1
        intro htb
        have hm := U.sub_mem hta htb
        rw [sub_sub_sub_cancel_left] at hm
        exact hba (hSd b hb a ha hm)
      · intro ha'
        exact absurd ha ha'
  choose Φ' hΦ'L hΦ'r using fun a => hInt a (Φc a)
  have hred' : ∀ a x, red ψ ν w β E I (Φ' a).1 x =
      Set.indicator {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)}
        (fun z => red ψ ν w β E I Φ.1 (z + Matrix.single e.1 e.2 (a - z e.1 e.2))) x := by
    intro a x
    rw [hΦ'r a x]
    have h8 := red_indicator k ψ ν R Q w β E I e heE heI Φ.1 {s : k | s - a ∈ U} (x + Matrix.single e.1 e.2 a)
    have hxe : (x + Matrix.single e.1 e.2 a) e.1 e.2 - a = x e.1 e.2 := by
      simp [Matrix.add_apply, Matrix.single_apply]
    change red ψ ν w β E I (Set.indicator {t : Matrix R Q k | t e.1 e.2 ∈ {s : k | s - a ∈ U}} Φ.1) _ = _
    rw [h8]
    by_cases hx : x e.1 e.2 ∈ U
    · rw [Set.indicator_of_mem (show (x + Matrix.single e.1 e.2 a) ∈ {z : Matrix R Q k | z e.1 e.2 ∈ {s : k | s - a ∈ U}} by
          show (x + Matrix.single e.1 e.2 a) e.1 e.2 - a ∈ U
          rw [hxe]; exact hx),
        Set.indicator_of_mem (show x ∈ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx)]
      rw [← hsh (x + Matrix.single e.1 e.2 (a - x e.1 e.2)) (x e.1 e.2) hx, add_assoc, ← Matrix.single_add,
        sub_add_cancel]
    · rw [Set.indicator_of_notMem (show (x + Matrix.single e.1 e.2 a) ∉ {z : Matrix R Q k | z e.1 e.2 ∈ {s : k | s - a ∈ U}} by
          show ¬ ((x + Matrix.single e.1 e.2 a) e.1 e.2 - a ∈ U)
          rw [hxe]; exact hx),
        Set.indicator_of_notMem (show x ∉ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx)]
  have hΞ : red ψ ν w β E I (∑ a ∈ S, Φ' a).1 = 0 := by
    funext x
    rw [Submodule.coe_sum, hlin (fun a => (Φ' a).1) (fun a => (Φ' a).2) x]
    simp only [hred']
    by_cases hx : x e.1 e.2 ∈ U
    · simp only [Set.indicator_of_mem (show x ∈ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx)]
      exact hsum x
    · simp only [Set.indicator_of_notMem (show x ∉ {z : Matrix R Q k | z e.1 e.2 ∈ (U : Set k)} from hx),
        Finset.sum_const_zero, Pi.zero_apply]
  have hL := hK (∑ a ∈ S, Φ' a) hΞ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hcov, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at hL
  rw [← hL]
  exact Finset.sum_congr rfl fun a _ => (hΦ'L a).symm

end GlobalTheory.PartRed.IntEntry
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionIntegrateEntryOfTranslationStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_integrate_entry_of_translation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.IntLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β E (insert e I) := by
  first | exact @GlobalTheory.PartRed.IntEntry.integrate_entry | exact GlobalTheory.PartRed.IntEntry.integrate_entry | (intros; apply GlobalTheory.PartRed.IntEntry.integrate_entry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapLawsFactorFourierJacobiSource
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

section Glue
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] {M : Type} [AddCommGroup M]
  [Module ℂ M]

theorem fillAt_entry (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) : fillAt β E I x y e.1 e.2 = x e.1 e.2 := by
  obtain ⟨r, q⟩ := e
  simp [fillAt, hI, hE]

theorem red_mul_entry (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E) (g : k → ℂ) (Φ : Matrix R Q k → ℂ)
    (x : Matrix R Q k) :
    red ψ ν w β E I (fun t => g (t e.1 e.2) * Φ t) x = g (x e.1 e.2) * red ψ ν w β E I Φ x := by
  unfold red
  simp_rw [fillAt_entry β E I x _ e hI hE, mul_assoc]
  exact integral_const_mul _ _

theorem fillAt_add_single (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) (e : R × Q)
    (hI : e ∉ I) (hE : e ∉ E) (a : k) :
    fillAt β E I x y + Matrix.single e.1 e.2 a = fillAt β E I (x + Matrix.single e.1 e.2 a) y := by
  obtain ⟨r₀, q₀⟩ := e
  ext r q
  by_cases h1 : (r, q) ∈ I
  · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hI h1
    simp [fillAt, h1, Matrix.single_apply, this]
  · by_cases h2 : (r, q) ∈ E
    · have : ¬ (r₀ = r ∧ q₀ = q) := by rintro ⟨rfl, rfl⟩; exact hE h2
      simp [fillAt, h1, h2, Matrix.single_apply, this]
    · simp [fillAt, h1, h2]

theorem circle_neg_mul (ψ : AddChar k Circle) (z : k) : (ψ (-z) : ℂ) * (ψ z : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem evalLaw_direct (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E)
    (h : ∀ (b : k) (Φ Φ' : SB (Matrix R Q k)), (∀ t, Φ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Φ.1 t) →
      L Φ' = L Φ) :
    EvalLaw L ψ ν w β E I e := by
  intro b Φ
  let f : Matrix R Q k →ₗ[k] k :=
    { toFun := fun t => b * t e.1 e.2
      map_add' := fun s t => by simp [mul_add]
      map_smul' := fun a t => by simp; ring }
  have hmem : (fun t => (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Φ.1 t) ∈ SB (Matrix R Q k) := by
    have := GlobalTheory.T.schwartzBruhat_mul_addChar_linearForm k ψ hψ R Q f (-(b * β e.1 e.2)) Φ.1 Φ.2
    convert this using 3 with t
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk]
    ring_nf
  refine ⟨⟨_, hmem⟩, h b Φ ⟨_, hmem⟩ (fun t => rfl), fun x => ?_⟩
  exact red_mul_entry ψ ν w β E I e hI hE (fun s => (ψ (b * (s - β e.1 e.2)) : ℂ)) Φ.1 x

theorem intLaw_direct (ψ : AddChar k Circle) (ν : Measure k) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E)
    (h : ∀ (a : k) (Φ Φ' : SB (Matrix R Q k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single e.1 e.2 a)) →
      L Φ' = (ψ (w (Matrix.single e.1 e.2 a)) : ℂ) • L Φ) :
    IntLaw L ψ ν w β E I e := by
  intro a Φ
  have hmem1 : (fun t => Φ.1 (t + Matrix.single e.1 e.2 a)) ∈ SB (Matrix R Q k) := by
    have := GlobalTheory.T.schwartzBruhat_comp_affine_matrix k R Q 1 (Matrix.single e.1 e.2 a) Φ.1 Φ.2
    simpa using this
  let Φa : SB (Matrix R Q k) := ⟨_, hmem1⟩
  refine ⟨(ψ (-w (Matrix.single e.1 e.2 a)) : ℂ) • Φa, ?_, fun x => ?_⟩
  · rw [map_smul, h a Φ Φa (fun t => rfl), smul_smul, circle_neg_mul, one_smul]
  · unfold red
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Φa]
    congr 1
    funext y
    rw [← fillAt_add_single β E I x y e hI hE a, map_add (f := _), neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring

theorem kills_empty (ψ : AddChar k Circle) (ν : Measure k) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) : Kills L ψ ν w β ∅ ∅ := by
  intro Φ hΦ
  have h0 : Φ = 0 := by
    apply Subtype.ext
    funext x
    have hx := congrFun hΦ x
    unfold red at hx
    have hf : ∀ y : (∅ : Finset (R × Q)) → k, fillAt β ∅ ∅ x y = x := fun y => by ext r q; simp [fillAt]
    simp only [hf] at hx
    rw [integral_const] at hx
    have hv : (Measure.pi fun _ : (∅ : Finset (R × Q)) => ν) Set.univ = 1 := by
      rw [Measure.pi_of_empty]; simp
    have hv' : (Measure.pi fun _ : (∅ : Finset (R × Q)) => ν).real Set.univ = 1 := by
      simp [Measure.real, hv]
    rw [hv', one_smul, Pi.zero_apply] at hx
    rw [Submodule.coe_zero, Pi.zero_apply]
    exact (mul_eq_zero.mp hx).resolve_right (Circle.coe_ne_zero _)
  rw [h0, map_zero]

end Glue
end GlobalTheory.PartRed

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

section Glue2
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] {M : Type} [AddCommGroup M]
  [Module ℂ M]

theorem kills_evals (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hν : ν.IsAddHaarMeasure) (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (I : Finset (R × Q)) (S : Finset (R × Q)) : ∀ E : Finset (R × Q), Disjoint S I → Kills L ψ ν w β E I →
    (∀ e ∈ S, ∀ E' : Finset (R × Q), E ⊆ E' → E' ⊆ E ∪ S → e ∉ E' → EvalLaw L ψ ν w β E' I e) →
    Kills L ψ ν w β (E ∪ S) I := by
  induction S using Finset.induction_on with
  | empty => intro E _ hK _; simpa using hK
  | insert a S ha ih =>
    intro E hdisj hK hlaw
    have hdisj' : Disjoint S I := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisj
    have h1 : Kills L ψ ν w β (E ∪ S) I := ih E hdisj' hK fun e he E' h1 h2 h3 =>
      hlaw e (Finset.mem_insert_of_mem he) E' h1
        (h2.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))) h3
    have haI : a ∉ I := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self _ _)
    have heq : E ∪ insert a S = insert a (E ∪ S) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [heq]
    by_cases haE : a ∈ E ∪ S
    · rwa [Finset.insert_eq_of_mem haE]
    · refine GlobalTheory.T.partialReduction_evaluate_entry_of_mul_law k ψ ν hψ hψ1 hν R Q M L w β (E ∪ S) I a haI h1 ?_
      refine hlaw a (Finset.mem_insert_self _ _) (E ∪ S) Finset.subset_union_left ?_ haE
      exact Finset.union_subset_union_right (Finset.subset_insert _ _)

theorem kills_ints (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ)
    (hν : ν.IsAddHaarMeasure) (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E : Finset (R × Q)) (S : Finset (R × Q)) : ∀ I : Finset (R × Q), Disjoint S E → Kills L ψ ν w β E I →
    (∀ e ∈ S, ∀ I' : Finset (R × Q), I ⊆ I' → I' ⊆ I ∪ S → e ∉ I' → IntLaw L ψ ν w β E I' e) →
    Kills L ψ ν w β E (I ∪ S) := by
  induction S using Finset.induction_on with
  | empty => intro I _ hK _; simpa using hK
  | insert a S ha ih =>
    intro I hdisj hK hlaw
    have hdisj' : Disjoint S E := Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisj
    have h1 : Kills L ψ ν w β E (I ∪ S) := ih I hdisj' hK fun e he I' h1 h2 h3 =>
      hlaw e (Finset.mem_insert_of_mem he) I' h1
        (h2.trans (Finset.union_subset_union_right (Finset.subset_insert _ _))) h3
    have haE : a ∉ E := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self _ _)
    have heq : I ∪ insert a S = insert a (I ∪ S) := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [heq]
    by_cases haI : a ∈ I ∪ S
    · rwa [Finset.insert_eq_of_mem haI]
    · refine GlobalTheory.T.partialReduction_integrate_entry_of_translation k ψ ν hψ hν R Q M L w β E (I ∪ S) a haE h1 ?_
      refine hlaw a (Finset.mem_insert_self _ _) (I ∪ S) Finset.subset_union_left ?_ haI
      exact Finset.union_subset_union_right (Finset.subset_insert _ _)

end Glue2
end GlobalTheory.PartRed

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

section Sets
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem mem_fixSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ fixSet ρ ↔
    ((∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨ (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s)) := by
  simp [fixSet]

theorem mem_transSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ transSet ρ ↔
    (Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val) := by
  simp [transSet]

theorem mem_lowSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ lowSet ρ ↔
    ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val := by
  simp [lowSet]

theorem mem_upSet {ρ : ℕ} {e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} : e ∈ upSet ρ ↔
    ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ l.val < i.val ∧ i.val ≤ ρ := by
  simp [upSet]

theorem disj_trans_fix (ρ : ℕ) :
    Disjoint (transSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (fixSet ρ) := by
  rw [Finset.disjoint_left]
  rintro ⟨r, q⟩ h1 h2
  rw [mem_transSet] at h1
  rw [mem_fixSet] at h2
  rcases h2 with ⟨i, hq, hi, hnf⟩ | ⟨l, s, hr, hl, hq⟩
  · exact hnf h1.1
  · dsimp only at hr hq
    subst hr hq
    have := h1.1
    simp only [Free] at this
    omega

theorem disj_low_trans (ρ : ℕ) :
    Disjoint (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (transSet ρ) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨l, i, rfl, -, hil⟩ := mem_lowSet.mp h1
  have := (mem_transSet.mp h2).1
  simp only [Free] at this
  omega

theorem disj_up_fixlow (ρ : ℕ) :
    Disjoint (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (fixSet ρ ∪ lowSet ρ) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨l, i, rfl, hli, hiρ⟩ := mem_upSet.mp h1
  rcases Finset.mem_union.mp h2 with h | h
  · rcases mem_fixSet.mp h with ⟨i', hq, -, hnf⟩ | ⟨l', s, -, -, hq⟩
    · exact hnf (by simp only [Free]; exact hli)
    · simp at hq
  · obtain ⟨l', i', he, -, hil⟩ := mem_lowSet.mp h
    simp only [Prod.mk.injEq, Sum.inr.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    omega

end Sets

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
  {M : Type} [AddCommGroup M] [Module ℂ M]

theorem kills_low (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hν : ν.IsAddHaarMeasure) (ρ : ℕ) (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hc : c = 2 * ρ + 1)
    (H4 : ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ)
    (K : Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ) (transSet ρ)) :
    ∀ j : ℕ, Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ (lowSet ρ).filter (fun e => colIx e < j))
      (transSet ρ) := by
  intro j
  induction j with
  | zero => simpa using K
  | succ j ih =>
    have hsplit : (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => colIx e < j + 1) =
        (lowSet ρ).filter (fun e => colIx e < j) ∪ (lowSet ρ).filter (fun e => colIx e = j) := by
      ext e
      by_cases h : e ∈ (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) <;> simp [h] <;> omega
    rw [hsplit, ← Finset.union_assoc]
    refine kills_evals ψ ν hψ hψ1 hν L chL _ (transSet ρ) _ _
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (disj_low_trans ρ)) ih ?_
    intro e he E' h1 h2 h3
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨l, i, rfl, hρi, hil⟩ := mem_lowSet.mp he1
    simp only [colIx, Sum.elim_inr] at he2
    refine GlobalTheory.T.partialReduction_lower_entry_multiplication_law k ψ ν hψ hν n n' c ρ M L hc H4 l i hρi hil E'
      (Finset.subset_union_left.trans h1) ?_ ?_ h3
    · intro x hx
      apply h1
      refine Finset.mem_union_right _ ?_
      simpa [he2] using hx
    · refine h2.trans ?_
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter] at hx ⊢
      tauto

theorem kills_up (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ)
    (hν : ν.IsAddHaarMeasure) (ρ : ℕ) (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hc : c = 2 * ρ + 1)
    (H4 : ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ)
    (K : Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) (transSet ρ)) :
    ∀ d j : ℕ, j + d = c + 1 → Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ)
      (transSet ρ ∪ (upSet ρ).filter (fun e => j ≤ colIx e)) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hemp : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => j ≤ colIx e) = ∅ := by
      apply Finset.filter_false_of_mem
      intro e he
      obtain ⟨l, i, rfl, -, -⟩ := mem_upSet.mp he
      simp only [colIx, Sum.elim_inr]
      have := i.isLt
      omega
    rw [hemp, Finset.union_empty]
    exact K
  | succ d ih =>
    intro j hj
    have hsplit : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => j ≤ colIx e) =
        (upSet ρ).filter (fun e => j + 1 ≤ colIx e) ∪ (upSet ρ).filter (fun e => colIx e = j) := by
      ext e
      by_cases h : e ∈ (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) <;> simp [h] <;> omega
    rw [hsplit, ← Finset.union_assoc]
    refine kills_ints ψ ν hψ hν L chL _ (fixSet ρ ∪ lowSet ρ) _ _
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (disj_up_fixlow ρ)) (ih (j + 1) (by omega)) ?_
    intro e he I' h1 h2 h3
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨l, i, rfl, hli, hiρ⟩ := mem_upSet.mp he1
    simp only [colIx, Sum.elim_inr] at he2
    refine GlobalTheory.T.partialReduction_upper_free_entry_translation_law k ψ ν hψ hν n n' c ρ M L hc H4 l i hli hiρ I'
      (Finset.subset_union_left.trans h1) ?_ ?_ h3
    · intro x hx
      apply h1
      refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    · refine h2.trans ?_
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter] at hx ⊢
      tauto

end Main
end GlobalTheory.PartRed

namespace GlobalTheory.PartRed
open GlobalTheory.LocFlat

theorem flRow_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s, r = Sum.inr l ∧ ρ < l.val ∧ q = Sum.inl s) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ < i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν n n' _ _ _ _ c ρ M _ _ L hc H1 H2 H3 H4
  have K0 := kills_empty ψ ν L chL (basePt c (0 : Matrix n n' k))
  have K1 := kills_evals ψ ν hψ hψ1 hν L chL (basePt c (0 : Matrix n n' k)) ∅ (fixSet ρ) ∅
    (Finset.disjoint_empty_right _) K0 (by
      intro e he E' _ _ heE'
      refine evalLaw_direct ψ ν hψ L chL _ E' ∅ e (Finset.notMem_empty _) heE' ?_
      obtain ⟨r, q⟩ := e
      rcases mem_fixSet.mp he with h | h
      · exact H1 r q h
      · exact H2 r q h)
  rw [Finset.empty_union] at K1
  have K2 := kills_ints ψ ν hψ hν L chL (basePt c (0 : Matrix n n' k)) (fixSet ρ) (transSet ρ) ∅
    (disj_trans_fix ρ) K1 (by
      intro e he I' _ _ heI'
      refine intLaw_direct ψ ν L chL _ (fixSet ρ) I' e heI'
        (Finset.disjoint_left.mp (disj_trans_fix ρ) he) ?_
      obtain ⟨r, q⟩ := e
      have h := mem_transSet.mp he
      intro a Φ Φ' hΦ'
      rw [chL_apply]
      exact H3 r q h.1 h.2 a Φ Φ' hΦ')
  rw [Finset.empty_union] at K2
  have K3 := kills_low ψ ν hψ hψ1 hν ρ L hc H4 K2 (c + 1)
  have hlow : (lowSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => colIx e < c + 1) = lowSet ρ := by
    apply Finset.filter_true_of_mem
    intro e he
    obtain ⟨l, i, rfl, -, -⟩ := mem_lowSet.mp he
    simp only [colIx, Sum.elim_inr]
    exact i.isLt
  rw [hlow] at K3
  have K4 := kills_up ψ ν hψ hν ρ L hc H4 K3 (c + 1) 0 (by omega)
  have hup : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => 0 ≤ colIx e) = upSet ρ := by
    apply Finset.filter_true_of_mem
    intro e _
    exact Nat.zero_le _
  rw [hup] at K4
  have hρc : ρ < c := by omega
  let lρ : Fin c := ⟨ρ, hρc⟩
  let F : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (Matrix (n ⊕ Unit) n' k → ℂ) :=
    { toFun := fun Φ => flRow ψ ν (ρ + 1) Φ.1
      map_add' := fun Φ₁ Φ₂ => GlobalTheory.T.flatMapFourierJacobiRow_add k ψ ν hψ hν n n' c (ρ + 1) Φ₁.1 Φ₂.1 Φ₁.2 Φ₂.2
      map_smul' := fun a Φ => by
        funext x
        simp only [flRow, opE, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  have hker : LinearMap.ker F ≤ LinearMap.ker L := by
    intro Φ hΦ
    rw [LinearMap.mem_ker] at hΦ ⊢
    apply K4
    funext x
    rw [GlobalTheory.T.partialReduction_eq_flatMapFourierJacobiRow k ψ ν hν n n' c ρ hc lρ rfl Φ.1 x]
    exact congrFun hΦ _
  let f₀ : LinearMap.range F →ₗ[ℂ] M := (LinearMap.ker F).liftQ L hker ∘ₗ F.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f₀
  refine ⟨g ∘ₗ (SB (Matrix (n ⊕ Unit) n' k)).subtype, fun Φ Ψ hΨ => ?_⟩
  have h1 : g (F Φ) = L Φ := by
    have := LinearMap.congr_fun hg ⟨F Φ, LinearMap.mem_range_self F Φ⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [this]
    simp [f₀, LinearMap.quotKerEquivRange_symm_apply_image]
  rw [LinearMap.comp_apply, Submodule.coe_subtype, hΨ]
  exact h1.symm

end GlobalTheory.PartRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapLawsFactorFourierJacobiSourceStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_laws_factor_fourierJacobi_source : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s, r = Sum.inr l ∧ ρ < l.val ∧ q = Sum.inl s) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ < i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  first | exact @GlobalTheory.PartRed.flRow_factor | exact GlobalTheory.PartRed.flRow_factor | (intros; apply GlobalTheory.PartRed.flRow_factor <;> assumption)
end
