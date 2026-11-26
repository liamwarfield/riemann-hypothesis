module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthNonnegIntegralOperatorIntegralVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomPointsFactorHenselianOfSpecializes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfSteps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionIntegralPointOfSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionIntegralPointOfSteps
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

theorem limPt_of_steps : AddSt → ActSt → ContSt → LimPtSt := by
  intro hAdd hAct hCont
  intro C _ _ v d R _ _ O _ _ B hB σ _ κ _ w hw A a hA
  have hdI : ∀ c e e', IsIntV v (dAct C B c e e') := fun c e _ => hB.2.1 c e _
  have hAI : ∀ b e e', IsIntV v (A b e e') := by
    intro b e e'
    have h0 : IsIntV v (A b e e' - dAct C B (a 0 b) e e') := by
      have := hA 0 b e e'
      simpa [IsIntV] using this
    have : A b e e' = (A b e e' - dAct C B (a 0 b) e e') + dAct C B (a 0 b) e e' := by ring
    rw [this]
    exact (ptIsIntV_iff _).2 (Subring.add_mem _ ((ptIsIntV_iff _).1 h0) ((ptIsIntV_iff _).1 (hdI _ _ _)))
  have hN : ∀ N, IntLog (fglOf hB) (∑ b, mv (dAct C B (a N b)) (w b)) := fun N =>
    Finset.sum_induction _ (IntLog (fglOf hB)) (fun x y hx hy => (hAdd C v d (fglOf hB) σ).2.2 x y hx hy)
      (hAdd C v d (fglOf hB) σ).1 (fun b _ => (hAct C v d R O B hB σ (a N b)).2 _ (hw b))
  have hw0 : ∀ b i, constantCoeff (w b i) = 0 := fun b => (hw b).1
  have key : ∀ (M : κ → Matrix (Fin d) (Fin d) C) (i : Fin d),
      expPt (fglOf hB) (∑ b, mv (M b) (w b)) i =
        subst (fun q => ∑ x : κ × Fin d, M x.1 q x.2 • w x.1 x.2) (expOf (fglOf hB) i) := by
    intro M i
    unfold expPt
    congr 1
    funext q
    rw [Finset.sum_apply, Fintype.sum_prod_type]
    rfl
  refine ⟨fun i => ?_, fun i α => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_apply, map_sum]
      exact Finset.sum_eq_zero fun b _ => cc_mv (A b) (hw0 b) i
  · obtain ⟨N₀, hN₀⟩ := hCont C v (Fin d) σ (κ × Fin d) (expOf (fglOf hB) i) (fun x => w x.1 x.2)
      (fun x => hw0 x.1 x.2) α
    have h1 := hN₀ (fun q x => A x.1 q x.2) (fun q x => dAct C B (a N₀ x.1) q x.2) (fun q x => hAI _ _ _)
      (fun q x => hdI _ _ _) (fun q x => hA N₀ x.1 q x.2)
    have h2 := (hN N₀).2 i α
    rw [key] at h2
    rw [key]
    rw [← sub_add_cancel (coeff α (subst (fun q => ∑ x : κ × Fin d, A x.1 q x.2 • w x.1 x.2)
      (expOf (fglOf hB) i) : MvPowerSeries σ C))
      (coeff α (subst (fun q => ∑ x : κ × Fin d, dAct C B (a N₀ x.1) q x.2 • w x.1 x.2)
      (expOf (fglOf hB) i) : MvPowerSeries σ C))]
    exact (ptIsIntV_iff _).2 (Subring.add_mem _ ((ptIsIntV_iff _).1 h1) ((ptIsIntV_iff _).1 h2))

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionIntegralPointOfStepsStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitActionIntegralPoint_of_steps : AddSt → ActSt → ContSt → LimPtSt := by
  first | exact @GlobalTheory.IsoTriv.limPt_of_steps | exact GlobalTheory.IsoTriv.limPt_of_steps | (intros; apply GlobalTheory.IsoTriv.limPt_of_steps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSeriesExpSumOfActionLinearLogUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSeriesExpSumOfActionLinearLogUnit
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

theorem frame_cc_ev {C : Type} [CommRing C] {d m n : ℕ} (a : Fin m → Pt C n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) {f : PS C m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by
  have h0 : ∀ p : Fin m × Fin d, constantCoeff ((fun p : Fin m × Fin d => a p.1 p.2) p) = 0 := fun p => ha p.1 p.2
  unfold ev
  exact constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin d => a p.1 p.2)
    (hasSubst_of_constantCoeff_zero h0) h0 hf

theorem frame_subst_ev {C : Type} [CommRing C] {d m n : ℕ} {σ : Type} (a : Fin m → Pt C n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) {t : Fin n × Fin d → MvPowerSeries σ C} (ht : HasSubst t)
    (f : PS C m d) :
    subst t (ev a f) = subst (fun p : Fin m × Fin d => subst t (a p.1 p.2)) f := by
  have h0 : ∀ p : Fin m × Fin d, constantCoeff ((fun p : Fin m × Fin d => a p.1 p.2) p) = 0 := fun p => ha p.1 p.2
  unfold ev
  exact subst_comp_subst_apply (a := fun p : Fin m × Fin d => a p.1 p.2) (hasSubst_of_constantCoeff_zero h0) ht f

theorem frame_cc_pt {C : Type} [CommRing C] {d n : ℕ} (b : Fin n) (j : Fin 1) (i : Fin d) :
    constantCoeff ((![pt C d b] : Fin 1 → Pt C n d) j i) = 0 := by
  simp [pt]

theorem frame_subst_ev_pt {C : Type} [CommRing C] {d n : ℕ} {σ : Type} (b : Fin n)
    {t : Fin n × Fin d → MvPowerSeries σ C} (ht : HasSubst t) (f : PS C 1 d) :
    subst t (ev ![pt C d b] f) = subst (fun p : Fin 1 × Fin d => t (b, p.2)) f := by
  rw [frame_subst_ev _ (frame_cc_pt b) ht]
  congr 1
  funext p
  rcases p with ⟨j, i⟩
  fin_cases j
  simpa [pt] using (subst_X (R := C) ht (b, i))

theorem frame_exp_zero {C : Type} [CommRing C] [Algebra ℚ C] {σ : Type} :
    PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C) = 1 := by
  classical
  unfold PowerSeries.subst
  have e : (fun _ : Unit => (0 : MvPowerSeries σ C)) = 0 := rfl
  rw [e, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  ext x
  by_cases hx : x = 0
  · subst hx
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C, if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff,
      map_one]
    exact PowerSeries.constantCoeff_exp (A := C)
  · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C, if_neg hx, MvPowerSeries.coeff_one, if_neg hx, map_zero]

theorem frameSt_of (hAct : ActSt) (hUnit : UnitSt) : FrameSt := by
  intro C _ _ v d R _ _ O _ _ B hB h hh w0 n
  have hc : constantCoeff h = 0 := GlobalTheory.GaugeBaseChange.const_of_axis hh.ax0
  have hact : ∀ i, constantCoeff (B.actK C w0 i) = 0 := fun i => by
    unfold FB.actK
    rw [constantCoeff_map, B.A.const, map_zero]
  have hpair : ∀ j i, constantCoeff
      ((![pt C d 0, comp1 (B.actK C w0) (pt C d 0)] : Fin 2 → Pt C 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · simp [pt]
    · exact frame_cc_ev _ (frame_cc_pt 0) (hact i)
  have hcL : constantCoeff (B.hL C h w0) = 0 := frame_cc_ev _ hpair hc
  have hS : constantCoeff (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => frame_cc_ev _ (frame_cc_pt b) hcL
  obtain ⟨-, -, -, hadd, hone, -⟩ := hUnit C v (Fin n × Fin d)
  refine ⟨hone _ hS, fun k => ?_, fun σ _ y hy => ?_⟩
  · unfold frameSer FB.expS
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, frame_exp_zero]
    | succ k ih =>
      rw [Nat.cast_succ, add_smul, one_smul, hadd _ _ _ hS, ih, pow_succ]
      rw [smul_eq_C_mul, map_mul, hS, mul_zero]
  · have ht : HasSubst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2) :=
      hasSubst_of_constantCoeff_zero fun q => cc_expPt _ (hy q.1) q.2
    have key : subst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2)
        (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) =
        ∑ j, pairSer (fglOf hB) h (y j) (mv (dAct C B w0) (y j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← coe_substAlgHom ht, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hs : HasSubst (fun p : Fin 1 × Fin d => expPt (fglOf hB) (y b) p.2) :=
        hasSubst_of_constantCoeff_zero fun q => cc_expPt _ (hy b) q.2
      rw [coe_substAlgHom, frame_subst_ev_pt b ht]
      unfold FB.hL pairSer
      rw [frame_subst_ev _ hpair hs, (hAct C v d R O B hB σ w0).1 (y b) (hy b)]
      congr 1
      funext ⟨j, i⟩
      fin_cases j
      · exact subst_X hs _
      · exact frame_subst_ev_pt 0 hs _
    rw [← key]
    unfold frameSer FB.expS PowerSeries.subst
    exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => hS) ht _

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSeriesExpSumOfActionLinearLogUnitStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameSeriesExpSum_of_actionLinear_logUnit : ActSt → UnitSt → FrameSt := by
  first | exact @GlobalTheory.IsoTriv.frameSt_of | exact GlobalTheory.IsoTriv.frameSt_of | (intros; apply GlobalTheory.IsoTriv.frameSt_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmSumIntegralAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmSumIntegralAdditive
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

theorem exp_point_zero {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    (σ : Type) : expPt G (0 : Fin d → MvPowerSeries σ C) = 0 := by
  funext i
  have h0 : ∀ j, constantCoeff ((0 : Fin d → MvPowerSeries σ C) j) = 0 := fun _ => by simp
  have hs : HasSubst (0 : Fin d → MvPowerSeries σ C) := hasSubst_of_constantCoeff_zero h0
  ext e
  simp only [expPt, Pi.zero_apply]
  rw [coeff_subst hs, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m = 0
  · subst hm
    simp [coeff_zero_eq_constantCoeff_apply, (isExp_expOf G).1 i]
  · obtain ⟨s, hsm⟩ : ∃ s, m s ≠ 0 := by
      by_contra hc; push_neg at hc; exact hm (Finsupp.ext hc)
    have : (m.prod fun s n => ((0 : Fin d → MvPowerSeries σ C) s) ^ n) = 0 := by
      rw [Finsupp.prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hsm)
      simp [zero_pow hsm]
    rw [this, map_zero, smul_zero]

theorem log_sum_additive_preserves_integrality : AddSt := by
  intro C _ v d G σ _
  have hadd : ∀ w w' : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) →
      (∀ i, constantCoeff (w' i) = 0) →
      expPt G (w + w') = fun i => subst (Sum.elim (expPt G w) (expPt G w')) (G.F i) := by
    intro w w' hw hw'
    set a : Fin d ⊕ Fin d → MvPowerSeries σ C := Sum.elim (expPt G w) (expPt G w') with ha_def
    have ha0 : ∀ s, constantCoeff (a s) = 0 := by
      rintro (b | b)
      · exact cc_expPt G hw b
      · exact cc_expPt G hw' b
    have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
    have hF : HasSubst G.F := hasSubst_of_constantCoeff_zero G.F_const
    set y : Fin d → MvPowerSeries σ C := fun i => subst a (G.F i) with hy_def
    have hy0 : ∀ i, constantCoeff (y i) = 0 := fun i =>
      constantCoeff_subst_eq_zero ha ha0 (G.F_const i)
    have hlg : lgPt G y = w + w' := by
      funext i
      have h1 := subst_comp_subst_apply hF ha (G.lg i)
      have hXl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
        hasSubst_of_constantCoeff_zero (fun b => by simp)
      have hXr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
        hasSubst_of_constantCoeff_zero (fun b => by simp)
      rw [G.lg_F, subst_add ha, subst_comp_subst_apply hXl ha, subst_comp_subst_apply hXr ha] at h1
      have hl : (fun s : Fin d => subst a (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) C)) = expPt G w := by
        funext s; rw [subst_X ha]; rfl
      have hr : (fun s : Fin d => subst a (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) C)) = expPt G w' := by
        funext s; rw [subst_X ha]; rfl
      rw [hl, hr] at h1
      have e1 : subst (expPt G w) (G.lg i) = w i := by
        have := congrFun (lgPt_expPt G hw) i; exact this
      have e2 : subst (expPt G w') (G.lg i) = w' i := by
        have := congrFun (lgPt_expPt G hw') i; exact this
      show subst y (G.lg i) = w i + w' i
      rw [hy_def, ← h1, e1, e2]
    rw [← hlg, expPt_lgPt G hy0]
  refine ⟨⟨fun i => by simp, fun i => ?_⟩, hadd, ?_⟩
  · rw [exp_point_zero G σ]; intro α; simp [IsIntV]
  · intro w w' hw hw'
    refine ⟨fun i => by simp [hw.1 i, hw'.1 i], fun i => ?_⟩
    rw [hadd w w' hw.1 hw'.1]
    refine ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (G.F_int i) ?_ ?_
    · rintro (b | b)
      · exact hw.2 b
      · exact hw'.2 b
    · rintro (b | b)
      · exact cc_expPt G hw.1 b
      · exact cc_expPt G hw'.1 b

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmSumIntegralAdditiveStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logarithm_sum_integral_additive : AddSt := by
  first | exact @GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | exact GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | (intros; apply GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeHermitianCombinationOfSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeHermitianCombinationOfSteps
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.HermRead

open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

section Lin

variable {C : Type} [Field C] {d : ℕ} {σ : Type}

theorem mv_sum (A : Matrix (Fin d) (Fin d) C) {β : Type} (s : Finset β) (x : β → Fin d → MvPowerSeries σ C) :
    mv A (∑ b ∈ s, x b) = ∑ b ∈ s, mv A (x b) := by
  funext e
  simp only [mv, Finset.sum_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem mv_mv (A A' : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) :
    mv A (mv A' w) = mv (A * A') w := by
  funext e
  simp only [mv, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem add_mv (A A' : Matrix (Fin d) (Fin d) C) (w : Fin d → MvPowerSeries σ C) :
    mv (A + A') w = mv A w + mv A' w := by
  funext e
  simp only [mv, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]

end Lin

theorem map_sum_of_additive {M Q : Type} [AddCommMonoid M] [AddCommGroup Q] (p : M → Prop) (h0 : p 0)
    (hp : ∀ x y, p x → p y → p (x + y)) (f : M → Q) (hf : ∀ x y, p x → p y → f (x + y) = f x + f y)
    {β : Type} (s : Finset β) (x : β → M) (hx : ∀ b, p (x b)) :
    p (∑ b ∈ s, x b) ∧ f (∑ b ∈ s, x b) = ∑ b ∈ s, f (x b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using h0, ?_⟩
    have := hf 0 0 h0 h0
    rw [add_zero] at this
    simpa using this
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact ⟨hp _ _ (hx b) ih.1, by rw [hf _ _ (hx b) ih.1, ih.2]⟩

theorem finSt_of (hAdd : AddSt) (hAct : ActSt) (hUnit : UnitSt) (hBi : BiaddSt) : FinSt := by
  intro C _ _ v d R _ _ O _ _ B hB h hg σ _ κ _ w hw w0 n a ι _ e t ht
  obtain ⟨hU0, hUadd, hUneg, -⟩ := hUnit C v σ
  obtain ⟨hI0, -, hIadd⟩ := hAdd C v d (fglOf hB) σ
  have hIact := fun c => (hAct C v d R O B hB σ c).2
  have hbi := hBi C v d R O B hB h hg σ
  let U : AddSubgroup (MvPowerSeries σ C) :=
    { carrier := {s | LogUnit v s}
      add_mem' := fun {s t} hs ht => hUadd s t hs ht
      zero_mem' := hU0
      neg_mem' := fun {s} hs => hUneg s hs }
  let π := QuotientAddGroup.mk' U
  have key : ∀ s, π s = 0 ↔ LogUnit v s := fun s => QuotientAddGroup.eq_zero_iff s
  have h1 : ∀ z, IntLog (fglOf hB) z → ∀ x y, IntLog (fglOf hB) x → IntLog (fglOf hB) y →
      π (pairSer (fglOf hB) h (x + y) z) = π (pairSer (fglOf hB) h x z) + π (pairSer (fglOf hB) h y z) := by
    intro z hz x y hx hy
    have := (key _).2 (hbi x y z hx hy hz).2.1
    rw [map_sub, map_add (f := _), sub_eq_zero] at this
    exact this.symm
  have h2 : ∀ z, IntLog (fglOf hB) z → ∀ x y, IntLog (fglOf hB) x → IntLog (fglOf hB) y →
      π (pairSer (fglOf hB) h z (x + y)) = π (pairSer (fglOf hB) h z x) + π (pairSer (fglOf hB) h z y) := by
    intro z hz x y hx hy
    have := (key _).2 (hbi x y z hx hy hz).2.2.1
    rw [map_sub, map_add (f := _), sub_eq_zero] at this
    exact this.symm
  have h3 : ∀ (c : O) x z, IntLog (fglOf hB) x → IntLog (fglOf hB) z →
      π (pairSer (fglOf hB) h (mv (dAct C B c) x) z) =
        π (pairSer (fglOf hB) h x (mv (dAct C B (star c)) z)) := by
    intro c x z hx hz
    have := (key _).2 ((hbi x x z hx hx hz).2.2.2 c)
    rwa [map_sub, sub_eq_zero] at this
  let F : κ → κ → O →+ MvPowerSeries σ C ⧸ U := fun b b' =>
    AddMonoidHom.mk' (fun c => π (pairSer (fglOf hB) h (w b) (mv (dAct C B c) (w b')))) fun c c' => by
      rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add, add_mv]
      exact h2 _ (hw b) _ _ (hIact _ _ (hw b')) (hIact _ _ (hw b'))
  have hF : ∀ b b' c, F b b' c = π (pairSer (fglOf hB) h (w b) (mv (dAct C B c) (w b'))) := fun _ _ _ => rfl
  have hj : ∀ j, π (pairSer (fglOf hB) h (∑ b, mv (dAct C B (a b j)) (w b))
      (mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b)))) =
        ∑ b, ∑ b', F b b' (star (a b j) * a b' j * w0) := by
    intro j
    have hy : IntLog (fglOf hB) (∑ b, mv (dAct C B (a b j)) (w b)) :=
      (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun _ => (0 : ℤ)) (by simp) Finset.univ _
        fun b => hIact _ _ (hw b)).1
    have hz := hIact w0 _ hy
    generalize hzz : mv (dAct C B w0) (∑ b, mv (dAct C B (a b j)) (w b)) = z at hz
    refine (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun x => π (pairSer (fglOf hB) h x z)) (h1 _ hz)
      Finset.univ _ fun b => hIact (a b j) _ (hw b)).2.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [h3 _ _ _ (hw b) hz, ← hzz, mv_mv, mv_sum, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul]
    refine (map_sum_of_additive (IntLog (fglOf hB)) hI0 hIadd (fun x => π (pairSer (fglOf hB) h (w b) x))
      (h2 _ (hw b)) Finset.univ _ fun b' => hIact _ _ (hIact _ _ (hw b'))).2.trans
      (Finset.sum_congr rfl fun b' _ => ?_)
    rw [hF, mv_mv, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul, mul_right_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← key, map_sub, sub_eq_zero, map_sum, Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← Finset.sum_mul, ht, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul, map_zsmul, hF]

end GlobalTheory.IsoTriv.HermRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeHermitianCombinationOfStepsStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeHermitianCombination_of_steps : AddSt → ActSt → UnitSt → BiaddSt → FinSt := by
  first | exact @GlobalTheory.IsoTriv.HermRead.finSt_of | exact GlobalTheory.IsoTriv.HermRead.finSt_of | (intros; apply GlobalTheory.IsoTriv.HermRead.finSt_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionLieAlgebraOfPrimeIdempotentApprox
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionLieAlgebraOfPrimeIdempotentApprox
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.LimAct

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IsoTriv
open ReciprocityTheory.ChartRestriction.G.TB (dAct)
open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA (dActH)

theorem exists_lim {O : Type} [CommRing O] (q : O) [IsAdicComplete (Ideal.span {q}) O] (g : ℕ → O)
    (hg : ∀ m n, m ≤ n → ∃ w, g n - g m = q ^ m * w) : ∃ L : O, ∀ n, ∃ w, L - g n = q ^ n * w := by
  have key : ∀ m n, m ≤ n → g m ≡ g n [SMOD (Ideal.span {q} ^ m • ⊤ : Submodule O O)] := by
    intro m n hmn
    obtain ⟨w, hw⟩ := hg m n hmn
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨-w, by rw [← neg_sub, hw]; ring⟩
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {q}) g (fun {m n} h => key m n h)
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨-a, by rw [← neg_sub, ← ha]; ring⟩

section Val

variable {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p)

theorem isIntV_alg (o : X.O) : IsIntV (vX_vp X) (algebraMap X.O X.C o) := by
  rw [GlobalTheory.FactorDepth.isIntV_iff]; exact X.ints.map_le_one o

theorem le_v_pow_mul (N : ℕ) (o : X.O) :
    ((N : ℝ) : WithTop ℝ) ≤ vX_vp X ((p : X.C) ^ N * algebraMap X.O X.C o) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, vX_vp_p, nsmul_one]
  have h := isIntV_alg X o
  unfold IsIntV at h
  calc ((N : ℝ) : WithTop ℝ) = (N : WithTop ℝ) := by norm_cast
    _ ≤ (N : WithTop ℝ) + vX_vp X (algebraMap X.O X.C o) := le_add_of_nonneg_right h

theorem eq_zero_of_le_v (x : X.C) (h : ∀ N : ℕ, ((N : ℝ) : WithTop ℝ) ≤ vX_vp X x) : x = 0 := by
  by_contra hx
  obtain ⟨N, hN⟩ := exists_nat_gt ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v x : ℝ))
  have := h N
  rw [vX_vp_apply X hx, WithTop.coe_le_coe] at this
  linarith

end Val

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [inst : StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def dActXH : 𝓞 E →+* Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  dActH X.C Ch.ch.B

theorem dActX_eq (a : 𝓞 E) : dActX Ch X a = dActXH Ch X a := rfl

def entO (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) : X.O :=
  X.ι (coeff (Finsupp.single ((0 : Fin 1), e') 1) (Ch.actT a e))

theorem alg_entO (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) :
    algebraMap X.O X.C (entO Ch X a e e') = dActX Ch X a e e' := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  rw [entO, ← X.comp]
  show _ = coeff _ (Ch.ch.B.actK X.C a e)
  unfold FB.actK
  rw [Ch.gen.1.2.1 a e, coeff_map, coeff_map]
  rfl

theorem dActX_apply (a : 𝓞 E) (e e' : Fin (chD Ch.ch)) :
    dActX Ch X a e e' = X.ιF (letI := io.toAlgebra; dAct T.Fr Ch.ch.B a e e') := by
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  show coeff _ (Ch.ch.B.actK X.C a e) = X.ιF (coeff _ (Ch.ch.B.actK T.Fr a e))
  unfold FB.actK
  rw [coeff_map, coeff_map]
  rfl

theorem dActX_mulVec_lieVec (hst : ∀ a : 𝓞 E, star a = H.bar a) (φ : 𝓞 E →+* T.V) (τ : E →+* ℂ)
    (hφ : ∀ a : 𝓞 E, algebraMap T.V T.Fr (φ a) = io (embK c τ a)) (a : 𝓞 E) (i : Fin (Dw.mult τ)) :
    (dActX Ch X a).mulVec (lieVec Ch X ⟨τ, i⟩) = jX X (φ a) • lieVec Ch X ⟨τ, i⟩ := by
  obtain rfl := GlobalTheory.PowGerm.starSt E H inst hst
  letI := H.starRing
  letI := io.toAlgebra
  have h := GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y Ch a ⟨τ, i⟩
  funext e
  have h3 := congrArg X.ιF (congrFun h e)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h3 ⊢
  simp only [dActX_apply, lieVec, jX, RingHom.comp_apply, hφ, ← Ch.gen.1.2.2.2.2.2.2]
  exact h3

end Chart

theorem cauchy_eps_mul {R V : Type} [CommRing R] [CommRing V] (φ : R →+* V) (q : R) (ε x : ℕ → R) (t : V)
    (hε : ∀ N : ℕ, (∃ z, φ (ε N) = 1 + φ q ^ N * z) ∧
      ∀ M ≤ N, ∀ a : R, (∃ z, φ a = φ q ^ M * z) → ε N * a ∈ Ideal.span {q ^ M})
    (hx : ∀ N : ℕ, ∃ z, φ (x N) = t + φ q ^ N * z) (m n : ℕ) (hmn : m ≤ n) :
    ∃ w, ε n * x n - ε m * x m = q ^ m * w := by
  have hstep : ∀ N, ε (N + 1) * x (N + 1) - ε N * x N ∈ Ideal.span {q ^ N} := by
    intro N
    obtain ⟨z0, hz0⟩ := hx N
    obtain ⟨z1, hz1⟩ := hx (N + 1)
    obtain ⟨u0, hu0⟩ := (hε N).1
    obtain ⟨u1, hu1⟩ := (hε (N + 1)).1
    have ha : ε N * (x (N + 1) - x N) ∈ Ideal.span {q ^ N} :=
      (hε N).2 N le_rfl _ ⟨φ q * z1 - z0, by rw [map_sub, hz0, hz1]; ring⟩
    have hb : ε (N + 1) * (1 - ε N) ∈ Ideal.span {q ^ N} :=
      (hε (N + 1)).2 N (Nat.le_succ N) _ ⟨-u0, by rw [map_sub, map_one, hu0]; ring⟩
    have hc : ε N * (1 - ε (N + 1)) ∈ Ideal.span {q ^ N} :=
      (hε N).2 N le_rfl _ ⟨-(φ q * u1), by rw [map_sub, map_one, hu1]; ring⟩
    have e : ε (N + 1) * x (N + 1) - ε N * x N =
        ε N * (x (N + 1) - x N) + (ε (N + 1) * (1 - ε N) - ε N * (1 - ε (N + 1))) * x (N + 1) := by ring
    rw [e]
    exact Ideal.add_mem _ ha (Ideal.mul_mem_right _ _ (Ideal.sub_mem _ hb hc))
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨0, by ring⟩
  | succ n hmn ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1 (hstep n)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact ⟨w + q ^ k * w', by linear_combination hw - hw'⟩

end GlobalTheory.IsoTriv.LimAct

namespace GlobalTheory.IsoTriv

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IsoTriv.LimAct

theorem limActSt_of_epsSt (hε : EpsSt) : LimActSt := by
  intro E _ _ _ H Dw l Xo c inst hst T io y Ch p _ X τ
  obtain ⟨φ, hφ⟩ := GlobalTheory.IsoCols.exists_lift T (io.comp (embK c τ))
  have hP : φ (p : 𝓞 E) = (p : T.V) := map_natCast φ p
  have hp0 : φ (p : 𝓞 E) ≠ 0 := by rw [hP]; exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpu : ¬ IsUnit (φ (p : 𝓞 E)) := by rw [hP]; exact not_isUnit_p X
  obtain ⟨ε, hεN⟩ := hε (𝓞 E) T.V φ (p : 𝓞 E) hp0 hpu
  refine ⟨ε, fun t x hx => ?_⟩
  have hxN : ∀ N : ℕ, ∃ z, φ (x N) = t + φ (p : 𝓞 E) ^ N * z := fun N => by
    obtain ⟨z, hz⟩ := hx N
    exact ⟨z, by rw [hP]; exact IsFractionRing.injective T.V T.Fr ((hφ (x N)).trans hz)⟩
  have hcau := cauchy_eps_mul φ (p : 𝓞 E) ε x t hεN hxN
  have hent : ∀ e e', ∃ L : X.O, ∀ N, ∃ w, L - entO Ch X (ε N * x N) e e' = (p : X.O) ^ N * w := by
    intro e e'
    refine exists_lim (p : X.O) (fun N => entO Ch X (ε N * x N) e e') fun m n hmn => ?_
    obtain ⟨w, hw⟩ := hcau m n hmn
    refine ⟨entO Ch X w e e', X.ints.hom_inj ?_⟩
    rw [map_sub, map_mul, map_pow, map_natCast, alg_entO, alg_entO, alg_entO, dActX_eq, dActX_eq, dActX_eq,
      ← Matrix.sub_apply, ← map_sub, hw, ← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul, Matrix.smul_apply, nsmul_eq_mul,
      Nat.cast_pow]
  choose L W hW using hent
  have hA : ∀ N e e', algebraMap X.O X.C (L e e') =
      dActX Ch X (ε N * x N) e e' + (p : X.C) ^ N * algebraMap X.O X.C (W e e' N) := by
    intro N e e'
    have h := congrArg (algebraMap X.O X.C) (hW e e' N)
    rw [RingHom.map_sub, map_mul, map_pow, map_natCast, alg_entO] at h
    linear_combination h
  refine ⟨Matrix.of fun e e' => algebraMap X.O X.C (L e e'), fun N e e' => ?_, fun i => ?_⟩
  · rw [Matrix.of_apply, hA N, add_sub_cancel_left]
    exact le_v_pow_mul X N _
  · funext e
    rw [← sub_eq_zero]
    refine eq_zero_of_le_v X _ fun N => ?_
    obtain ⟨z0, hz0⟩ := hxN N
    obtain ⟨u, hu⟩ := (hεN N).1
    obtain ⟨z, hz⟩ : ∃ z, φ (ε N * x N) = t + (p : T.V) ^ N * z :=
      ⟨z0 + u * t + (p : T.V) ^ N * u * z0, by rw [map_mul, hu, hz0, hP]; ring⟩
    have hj : ∀ r : T.V, jX X r = algebraMap X.O X.C (X.ι r) := fun r => X.comp r
    have he := congrFun (dActX_mulVec_lieVec Ch X hst φ τ (fun a => hφ a) (ε N * x N) i) e
    rw [hz, map_add (f := _), map_mul, map_pow, map_natCast] at he
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.of_apply] at he ⊢
    have key : ∑ e', algebraMap X.O X.C (L e e') * lieVec Ch X ⟨τ, i⟩ e' - jX X t * lieVec Ch X ⟨τ, i⟩ e =
        (p : X.C) ^ N * algebraMap X.O X.C
          (∑ e', W e e' N * X.ι (Ch.uvecT ⟨τ, i⟩ e') + X.ι z * X.ι (Ch.uvecT ⟨τ, i⟩ e)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hA N, add_mul, Finset.sum_add_distrib, he, map_add (f := _), map_sum, map_mul, ← hj, mul_add, Finset.mul_sum,
        mul_assoc]
      simp only [lieVec]
      ring
    rw [key]
    exact le_v_pow_mul X N _

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionLieAlgebraOfPrimeIdempotentApproxStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitActionLieAlgebra_of_primeIdempotentApprox : EpsSt → LimActSt := by
  first | exact @GlobalTheory.IsoTriv.limActSt_of_epsSt | exact GlobalTheory.IsoTriv.limActSt_of_epsSt | (intros; apply GlobalTheory.IsoTriv.limActSt_of_epsSt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIntegralUnitsSubgroupExpHomProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIntegralUnitsSubgroupExpHomProof
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh

section Unit

variable {C : Type} [Field C] [CharZero C] {σ : Type}

theorem expU_add (s t : MvPowerSeries σ C) (hs : constantCoeff s = 0) (ht : constantCoeff t = 0) :
    PowerSeries.subst (s + t) (PowerSeries.exp C) =
      PowerSeries.subst s (PowerSeries.exp C) * PowerSeries.subst t (PowerSeries.exp C) := by
  have hst : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hs, ht])
  have comp : ∀ p : MvPowerSeries (Fin 2) C, constantCoeff p = 0 →
      MvPowerSeries.subst ![s, t] (PowerSeries.subst p (PowerSeries.exp C)) =
        PowerSeries.subst (MvPowerSeries.subst ![s, t] p) (PowerSeries.exp C) := by
    intro p hp
    unfold PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hp).const hst]
  have H := congrArg (MvPowerSeries.subst ![s, t]) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_subst_add_two_vars C)
  rw [MvPowerSeries.subst_mul hst, comp _ (by simp), comp _ (by simp), comp _ (by simp),
    MvPowerSeries.subst_add hst, MvPowerSeries.subst_X hst, MvPowerSeries.subst_X hst] at H
  simpa using H

theorem cc_expU (s : MvPowerSeries σ C) (hs : constantCoeff s = 0) :
    constantCoeff (PowerSeries.subst s (PowerSeries.exp C)) = 1 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [map_pow, hs, zero_pow he]

theorem expU_zero : PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C) = 1 := by
  have h := expU_add (0 : MvPowerSeries σ C) 0 (by simp) (by simp)
  rw [add_zero] at h
  have hu : IsUnit (PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, cc_expU _ (by simp)]
    exact isUnit_one
  exact hu.mul_left_cancel (by rw [mul_one]; exact h.symm)

omit [CharZero C] in
theorem inv_int (v : AddValuation C (WithTop ℝ)) (U : MvPowerSeries σ C) (hU : MvIsInt v U)
    (h1 : constantCoeff U = 1) : ∃ U', MvIsInt v U' ∧ U * U' = 1 := by
  set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v
  let U' : MvPowerSeries σ S := fun α => ⟨coeff α U, hU α⟩
  have hU' : map S.subtype U' = U := by ext α; rfl
  have hc : constantCoeff U' = ((1 : Sˣ) : S) := by
    apply Subtype.ext
    change coeff 0 U = 1
    rw [coeff_zero_eq_constantCoeff_apply, h1]
  refine ⟨map S.subtype (invOfUnit U' 1), fun α => ?_, ?_⟩
  · rw [coeff_map]; exact (coeff α (invOfUnit U' 1)).2
  · rw [← hU', ← map_mul, mul_invOfUnit U' 1 hc, map_one]

theorem unitSt : UnitSt := by
  intro C _ _ v σ _
  have hexp0 := expU_zero (C := C) (σ := σ)
  refine ⟨⟨by simp, ?_⟩, ?_, ?_, fun s t hs ht => expU_add s t hs ht, fun s hs => cc_expU s hs,
    fun U hU h1 => inv_int v U hU h1⟩
  · rw [hexp0]; exact Subring.one_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer v σ)
  · rintro s t ⟨hs0, hs⟩ ⟨ht0, ht⟩
    refine ⟨by simp [hs0, ht0], ?_⟩
    rw [expU_add s t hs0 ht0]
    exact Subring.mul_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer v σ) hs ht
  · rintro s ⟨hs0, hs⟩
    have hn0 : constantCoeff (-s) = 0 := by simp [hs0]
    refine ⟨hn0, ?_⟩
    obtain ⟨U', hU', hm⟩ := inv_int v _ hs (cc_expU s hs0)
    have e : PowerSeries.subst (-s) (PowerSeries.exp C) * PowerSeries.subst s (PowerSeries.exp C) = 1 := by
      rw [← expU_add _ _ hn0 hs0, neg_add_cancel, hexp0]
    have : PowerSeries.subst (-s) (PowerSeries.exp C) = U' := by
      calc PowerSeries.subst (-s) (PowerSeries.exp C)
          = PowerSeries.subst (-s) (PowerSeries.exp C) * (PowerSeries.subst s (PowerSeries.exp C) * U') := by
            rw [hm, mul_one]
        _ = U' := by rw [← mul_assoc, e, one_mul]
    rw [this]; exact hU'

end Unit

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIntegralUnitsSubgroupExpHomProofStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logIntegralUnitsSubgroupExpHom_proof : UnitSt := by
  first | exact @GlobalTheory.IsoTriv.unitSt | exact GlobalTheory.IsoTriv.unitSt | (intros; apply GlobalTheory.IsoTriv.unitSt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeIdempotentApproximationsDVRProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeIdempotentApproximationsDVRProof
open GlobalTheory.IsoTriv

namespace GlobalTheory.IsoTriv.PrimeIdempotent

theorem mem_pow_of_map_dvd {R V : Type} [CommRing R] [IsDedekindDomain R] [CommRing V]
    [IsDomain V] [IsDiscreteValuationRing V] (φ : R →+* V) (b a : R) (hb : φ b ≠ 0) (n : ℕ)
    (hw : (Ideal.comap φ (IsLocalRing.maximalIdeal V)).IsMaximal)
    (hbn : b ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n) (z : V) (hz : φ a = φ b * z) :
    a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal V) ^ n := by
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  by_cases ha : a = 0
  · rw [ha]; exact Ideal.zero_mem _
  have hspan : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = i
    at hfac
  by_cases hi : n ≤ i
  · have h1 : a ∈ w ^ i * J := hfac ▸ Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_pow_right hi (Ideal.mul_le_inf h1).1
  exfalso
  have hJw : ¬ J ≤ w := fun h => hw.ne_top (by rw [← hJ, sup_eq_left.mpr h])
  obtain ⟨s, hsJ, hsw⟩ := Set.not_subset.mp hJw
  have hb1 : b ∈ w ^ (i + 1) := Ideal.pow_le_pow_right (by omega) hbn
  have h2 : b * s ∈ Ideal.span {a} * w := by
    rw [hfac, mul_right_comm, ← pow_succ]
    exact Ideal.mul_mem_mul hb1 hsJ
  obtain ⟨m, hm, hm'⟩ := Ideal.mem_span_singleton_mul.mp h2
  apply hsw
  have h3 : φ s = z * φ m := by
    apply mul_left_cancel₀ hb
    rw [← map_mul, ← hm', map_mul, hz, mul_assoc]
  change φ s ∈ IsLocalRing.maximalIdeal V
  rw [h3]
  exact Ideal.mul_mem_left _ _ hm

theorem epsSt : EpsSt := by
  intro R V _ _ _ _ _ φ q hq hu
  set w := Ideal.comap φ (IsLocalRing.maximalIdeal V) with hwdef
  have hq0 : q ≠ 0 := fun h => hq (by rw [h, map_zero])
  have hqw : q ∈ w := (IsLocalRing.mem_maximalIdeal _).mpr hu
  have hwp : w.IsPrime := Ideal.comap_isPrime φ _
  have hw0 : w ≠ ⊥ := fun h => hq0 (by rw [h] at hqw; exact hqw)
  have hw : w.IsMaximal := hwp.isMaximal hw0
  have hspan : Ideal.span {q} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨J, hJ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hspan w
  generalize Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {q})) = e
    at hfac
  have hpow : ∀ M : ℕ, Ideal.span {q ^ M} = w ^ (e * M) * J ^ M := fun M => by
    rw [← Ideal.span_singleton_pow, hfac, mul_pow, pow_mul]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ N : ℕ, ∃ y ∈ J ^ N, ∃ z, φ y = 1 + φ q ^ N * z := by
    intro N
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero N hq) hϖ
    have hco : w ^ k ⊔ J ^ N = ⊤ := Ideal.pow_sup_pow_eq_top hJ
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hco)
    have h1 : φ x ∈ Ideal.span {φ q ^ N} := by
      have h2 : φ x ∈ (Ideal.map φ w) ^ k := by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem φ hx
      have h3 : φ x ∈ IsLocalRing.maximalIdeal V ^ k :=
        Ideal.pow_right_mono Ideal.map_comap_le k h2
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h3
      rwa [Ideal.span_singleton_eq_span_singleton.mpr hk]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h1
    refine ⟨y, hy, -c, ?_⟩
    have h4 : φ x + φ y = 1 := by rw [← map_add (f := _), hxy, map_one]
    rw [← h4, hc]; ring
  choose ε hεJ hε using key
  refine ⟨ε, fun N => ⟨hε N, fun M hM a ⟨z, hz⟩ => ?_⟩⟩
  have hqM : q ^ M ∈ w ^ (e * M) := by
    have h1 : q ^ M ∈ w ^ (e * M) * J ^ M := hpow M ▸ Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf h1).1
  have ha : a ∈ w ^ (e * M) :=
    mem_pow_of_map_dvd φ (q ^ M) a (by rw [map_pow]; exact pow_ne_zero M hq) _ hw hqM z
      (by rw [map_pow]; exact hz)
  rw [hpow M, mul_comm (ε N)]
  exact Ideal.mul_mem_mul ha (Ideal.pow_le_pow_right hM (hεJ N))

end GlobalTheory.IsoTriv.PrimeIdempotent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeIdempotentApproximationsDVRProofStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeIdempotentApproximationsDVR_proof : EpsSt := by
  first | exact @GlobalTheory.IsoTriv.PrimeIdempotent.epsSt | exact GlobalTheory.IsoTriv.PrimeIdempotent.epsSt | (intros; apply GlobalTheory.IsoTriv.PrimeIdempotent.epsSt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnCopiesSameValue
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ColumnGerm

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns GlobalTheory.IsoTriv

theorem mvIsInt_pow {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {σ : Type} {g : MvPowerSeries σ C}
    (hg : MvIsInt v g) (k : ℕ) : MvIsInt v (g ^ k) := by
  classical
  induction k with
  | zero =>
    intro α
    unfold IsIntV
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih => rw [pow_succ]; exact GlobalTheory.DepthNonneg.mvIsInt_mul ih hg

theorem exists_nabX_eq (hN : NabSt) (hI : InclSt) (hR : RetrSt) (hU : UnitSt) (hF : FrameSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y)
    {p : ℕ} [Fact p.Prime] (X : ValExt T p) (cx : Lt1 Dw → ℕ) {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V)
    (hB : IsCols c T io p cx B) (k : ℕ) (f : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C)
    (hf : MvIsInt (vX_vp X) f) :
    ∃ g : PS X.C n (chD Ch.ch), MvIsInt (vX_vp X) g ∧
      nabX Ch X cx B k g = derivAt0 (polyH X.C cx) (subst (expH Ch X cx) f) := by
  obtain ⟨ψ, ψ0, -, ψe, ψU⟩ := hI E H Dw l Xo c hs T io y Ch p X cx n B hB
  obtain ⟨ρ, ρ0, ρi, ρe⟩ := hR E H Dw l Xo c hs T io y Ch p X cx n B hB
  have hψ : HasSubst ψ := hasSubst_of_constantCoeff_zero ψ0
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero ρ0
  have e0 : ∀ q, constantCoeff (expH Ch X cx q) = 0 := fun q =>
    cc_expPt (fgl Ch X) (fun e => by simp) q.2
  have c0 : ∀ q, constantCoeff (colPt Ch X cx B q) = 0 := fun q =>
    cc_expPt (fgl Ch X) (fun e => by simp) q.2
  have he : HasSubst (expH Ch X cx) := hasSubst_of_constantCoeff_zero e0
  have hc : HasSubst (colPt Ch X cx B) := hasSubst_of_constantCoeff_zero c0
  have fr1 : constantCoeff (frameX Ch X n) = 1 := by
    letI := io.toAlgebra
    letI : Algebra T.Fr X.C := X.ιF.toAlgebra
    exact (hF X.C (vX_vp X) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (gauge_chart Ch X) H.w0 n).1
  have U1 : constantCoeff (subst ψ (frameX Ch X n) : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) = 1 := by
    have h := constantCoeff_subst_eq_zero hψ ψ0 (f := frameX Ch X n - 1) (by rw [map_sub, fr1, map_one, sub_self])
    rw [← coe_substAlgHom hψ, map_sub, map_one, map_sub, map_one, sub_eq_zero, coe_substAlgHom] at h
    exact h
  obtain ⟨U', U'i, hU'⟩ := (hU X.C (vX_vp X) _).2.2.2.2.2 _ ψU U1
  refine ⟨subst ρ (f * U' ^ k), ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst _
    (GlobalTheory.DepthNonneg.mvIsInt_mul hf (mvIsInt_pow U'i k)) ρi ρ0, ?_⟩
  rw [hN E H Dw l Xo c T io y Ch p X cx n B k]
  congr 1
  have h1 : subst (colPt Ch X cx B) (subst ρ (f * U' ^ k) : PS X.C n (chD Ch.ch)) =
      subst (expH Ch X cx) (f * U' ^ k) := by
    rw [subst_comp_subst_apply hρ hc, funext ρe]
  have h2 : subst (colPt Ch X cx B) (frameX Ch X n) = subst (expH Ch X cx)
      (subst ψ (frameX Ch X n) : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) := by
    rw [subst_comp_subst_apply hψ he, funext ψe]
  rw [subst_mul hc, subst_pow hc, h1, h2, ← subst_pow he, ← subst_mul he, mul_assoc, ← mul_pow, mul_comm U', hU',
    one_pow, mul_one]

end GlobalTheory.ColumnGerm

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ColumnGerm

theorem exists_germ_on_copies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C), MvIsInt (vX_vp X) f → ∃ g : PS X.C n (chD Ch.ch), MvIsInt (vX_vp X) g ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e _ y Ch X cx n B hB N k f hf
  have hadd := GlobalTheory.T.logarithm_sum_integral_additive
  have hact := GlobalTheory.T.action_linear_logCoordinates_integral
  have hunit := GlobalTheory.T.logIntegralUnitsSubgroupExpHom_proof
  have hcont := GlobalTheory.T.seriesCoeffUniformlyContinuousInCoeffs_proof
  have hbi := GlobalTheory.T.canonGaugeBiadditive_of_logSum_actionLinear hadd hact
  have hfr := GlobalTheory.T.frameSeriesExpSum_of_actionLinear_logUnit hact hunit
  have hfin := GlobalTheory.T.gaugeHermitianCombination_of_steps hadd hact hunit hbi
  have hla := GlobalTheory.T.limitActionLieAlgebra_of_primeIdempotentApprox GlobalTheory.T.primeIdempotentApproximationsDVR_proof
  have hlp := GlobalTheory.T.limitActionIntegralPoint_of_steps hadd hact hcont
  have hlf := GlobalTheory.T.limitIsotropicFrameIntegral_of_steps hadd hact hunit hbi hfr hfin hcont
  obtain ⟨g, hg, h⟩ := exists_nabX_eq (GlobalTheory.T.nablaOperatorFrameSeries_of_steps GlobalTheory.T.invariantDerivationEqPartialLogCoords_proof GlobalTheory.T.constCoeffOperatorLinearSubstitution_proof hfr) (GlobalTheory.T.columnInclusionIntegral_of_limitSteps hla hlp hlf)
    (GlobalTheory.T.columnInclusionRetraction_of_limitSteps hla hlp GlobalTheory.IsoTriv.limitEntriesMatrixInverseClosed_proof) hunit hfr (fun _ => rfl) Ch X cx B hB k f hf
  refine ⟨g, hg, ?_⟩
  rw [h, sub_self, AddValuation.map_zero]
  exact le_top

end GlobalTheory.ColumnGerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnCopiesSameValueStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_germ_on_copies_same_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C), MvIsInt (vX_vp X) f → ∃ g : PS X.C n (chD Ch.ch), MvIsInt (vX_vp X) g ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  first | exact @GlobalTheory.ColumnGerm.exists_germ_on_copies | exact GlobalTheory.ColumnGerm.exists_germ_on_copies | (intros; apply GlobalTheory.ColumnGerm.exists_germ_on_copies <;> assumption)
end
