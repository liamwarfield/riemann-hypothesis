module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalI
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementJ
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Th0FromPhPrime

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Th0TwoAnalyticOf
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B.An2

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.G (unitBall)
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)
open Formalism.L2.Th1.E (Unif ptW inW px py IntCurve OneUnit)
open Formalism.L2.Th1.A (fgl iSer logSer expSer wpReg g₂ g₃ IntModel xS)

theorem norm_transport (ι : ℂ ≃+* ℂ_[2]) (α : ℂ) (n : ℕ) (h : ((n : ℝ) + 1) = Complex.normSq α) :
    ι α * ι (conj α) = (n : ℂ_[2]) + 1 := by
  rw [← map_mul, Complex.mul_conj, ← h]
  push_cast
  rw [map_add (f := _), map_natCast, map_one]

theorem Th0TwoAnalytic_of (hE : HalfFibreExists) (hF : FibreZInstance) (hH : HalfShiftSeries)
    (hM : FibreMap) : ThetaZeroTwoAnalytic := by
  intro L ι W hU hW α ω₀ b b' hα hmul hω hω2 hb hb' hnb hnb' hno hxT hxQ
  obtain ⟨Sq, hSq⟩ := hE L α ω₀ hα hmul hω hno
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L α hα hmul
  obtain ⟨hcard, hfib⟩ := hF L α ω₀ S Sq hα hmul hS hω hω2 hSq
  rw [hH L ω₀ hω hω2] at hfib
  have hfib' := hM ℂ ℂ_[2] (ι : ℂ →+* ℂ_[2]) _ _ Sq _ _ _ _ _ hfib
  have hP := Formalism.L2.Th1.E.weierstrass_series_eq_transported 2 L ι W hU

  have hpx : px W (ptW 2 L ι W (ω₀ / 2)) = ι (L.weierstrassP (ω₀ / 2)) - W.b₂ / 12 :=
    Formalism.L2.Th1.E.AnaSysW.px_ptW hU _ hω2
  have he : px W (ptW 2 L ι W (ω₀ / 2)) + W.b₂ / 12 = ι (L.weierstrassP (ω₀ / 2)) := by
    rw [hpx]; ring
  have hEq : W.toAffine.Equation (px W (ptW 2 L ι W (ω₀ / 2)))
      (Formalism.L2.Th1.E.AnaSysW.yc 2 L ι W (ω₀ / 2)) := by
    rw [hpx]
    exact (Formalism.L2.Th1.E.AnaSysW.nonsing hU _ hω2).1
  have hd : L.derivWeierstrassP (ω₀ / 2) = 0 :=
    (Formalism.L2.Th1.F.pDerivZero L _ hω2).2 (by
      have : 2 * (ω₀ / 2) = ω₀ := by ring
      rw [this]; exact hω)
  have h2 : 2 * Formalism.L2.Th1.E.AnaSysW.yc 2 L ι W (ω₀ / 2) + W.a₁ * px W (ptW 2 L ι W (ω₀ / 2)) + W.a₃
      = 0 := by
    rw [hpx]
    unfold Formalism.L2.Th1.E.AnaSysW.yc
    rw [hd, map_zero]
    ring
  have hy : ‖Formalism.L2.Th1.E.AnaSysW.yc 2 L ι W (ω₀ / 2)‖ ≤ 1 :=
    ((Formalism.L2.Th1.A.bridgeTwoMore ℂ_[2] W _ _ hEq h2).2.2 hW hxT).1

  obtain ⟨hLaw, hi, -⟩ := Formalism.L2.Th1.A.bridgeLaw ℂ_[2] W hW
  have hlp := Crv2.logPair W
  obtain ⟨hEnd, hcl, h0, hne, h1, hb1, hb2⟩ :=
    twoAdicScalars ℂ_[2] (fgl W) (logSer W) (expSer W) b b' hLaw hlp hnb hnb'

  have hQn : ∀ Q : Sq, (Q : ℂ) ∉ L.lattice := by
    intro Q hQ
    apply (hSq.1 Q Q.2).2
    rw [two_mul]
    exact add_mem hQ hQ
  have hcQ : ∀ Q : Sq, px W (ptW 2 L ι W (Q : ℂ)) + W.b₂ / 12 = ι (L.weierstrassP (Q : ℂ)) := by
    intro Q
    rw [Formalism.L2.Th1.E.AnaSysW.px_ptW hU _ (hQn Q)]
    ring
  have hk : (ι : ℂ →+* ℂ_[2]) (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4) =
      3 * ι (L.weierstrassP (ω₀ / 2)) ^ 2 - ι L.g₂ / 4 := by
    simp only [RingEquiv.coe_toRingHom, map_sub, map_mul, map_pow, map_div₀, map_ofNat]
  rw [map_add (f := _), map_mul, PowerSeries.map_C, PowerSeries.map_C, Map.map_wOf, hk, ← hP] at hfib'
  have hZ : IsFibreZ (wpReg W)
      (PowerSeries.C (px W (ptW 2 L ι W (ω₀ / 2)) + W.b₂ / 12) +
        PowerSeries.C (3 * (px W (ptW 2 L ι W (ω₀ / 2)) + W.b₂ / 12) ^ 2 - g₂ W / 4) *
          wOf (px W (ptW 2 L ι W (ω₀ / 2)) + W.b₂ / 12) (wpReg W))
      (fun Q : Sq => px W (ptW 2 L ι W (Q : ℂ)) + W.b₂ / 12)
      (fun Q : Sq => PowerSeries.map (ι : ℂ →+* ℂ_[2]) (taylor0 fun z => L.weierstrassP (z + (Q : ℂ))))
      (fun Q : Sq => PowerSeries.map (ι : ℂ →+* ℂ_[2]) (taylor0 fun z => L.weierstrassP (z - (Q : ℂ))))
      (ι α)
      (ι (∑ P ∈ S, L.weierstrassP P)) := by
    rw [he, hU.1]
    simp only [hcQ]
    exact hfib'
  have hN : ι α * ι (conj α) = 2 * (Fintype.card Sq : ℂ_[2]) := by
    rw [norm_transport ι α S.card (Formalism.L2.Th1.F.kerRepsCard L α S hα hmul hS), Fintype.card_coe]
    exact_mod_cast hcard.symm
  have hS2 : ι α * (ι α - ι (conj α)) * ι (Formalism.L2.Th1.F.s2 L) = ι (∑ P ∈ S, L.weierstrassP P) := by
    rw [← Formalism.L2.Th1.F.quasiPeriodConstIsogeny L α S hα hmul hS, ← Complex.mul_conj, ← map_sub, ← map_mul,
      ← map_mul]
    congr 1
    ring
  have hal : algebraMap ℚ_[2] ℂ_[2] (b : ℚ_[2]) = ι α := hb.symm
  have halb : algebraMap ℚ_[2] ℂ_[2] (b' : ℚ_[2]) = ι (conj α) := hb'.symm
  simp only [hal, halb] at hEnd hcl h0 hne h1 hb1 hb2
  have hV := (th0Vanish ℂ_[2] (g₂ W) (g₃ W) (ι (Formalism.L2.Th1.F.s2 L)) (W.b₂ / 12) W.a₁ W.a₃
    (px W (ptW 2 L ι W (ω₀ / 2))) (Formalism.L2.Th1.E.AnaSysW.yc 2 L ι W (ω₀ / 2)) (ι α) (ι (conj α))
    (ι (∑ P ∈ S, L.weierstrassP P)) (wpReg W) (logSer W) (expSer W) (iSer W) (xS W) (fgl W) Sq
    (fun Q : Sq => px W (ptW 2 L ι W (Q : ℂ))) _ _ (Formalism.L2.Th1.A.bridgeWp ℂ_[2] W) hLaw hi hlp
    (Formalism.L2.Th1.A.bridgeCurve ℂ_[2] W hW) (Formalism.L2.Th1.A.bridgeCurve3 ℂ_[2] W hW)
    (Crv2.twoHyp W _ _ hW hEq h2 hxT hy) (fun Q => hxQ _ (hSq.1 Q Q.2).1) hZ hN hS2 hEnd hcl h0 hne
    h1 hb1 hb2).1
  have hV' : Simeq (ι := Unit)
      (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 := hV
  refine ⟨hV', ?_⟩
  rw [Formalism.L2.Th1.E.inWTh0 2 L ι W hU ω₀ hω hω2]
  exact Formalism.L2.Th1.E.Two.oneUnit_fExp_neg hV'

end Formalism.L2.Th1.B.An2
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormXLeOneOfNotInKernel
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Half

open Formalism.L2.Th1.F (MulStable IsKerReps)
open Formalism.L2.Th1.E (Unif ptW px IntCurve)
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv)
open Formalism.ELL (InFormalGroupPoints)

theorem exists_transversal (M : Submodule ℤ ℂ) (A : Finset ℂ) :
    ∃ Sq : Finset ℂ, Sq ⊆ A ∧
      (∀ Q ∈ Sq, ∀ Q' ∈ Sq, (Q - Q' ∈ M ∨ Q + Q' ∈ M) → Q = Q') ∧
      (∀ c ∈ A, ∃ Q ∈ Sq, c - Q ∈ M ∨ c + Q ∈ M) := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert a A _ ih =>
    obtain ⟨Sq, h0, h1, h2⟩ := ih
    by_cases ha : ∃ Q ∈ Sq, a - Q ∈ M ∨ a + Q ∈ M
    · refine ⟨Sq, h0.trans (Finset.subset_insert _ _), h1, ?_⟩
      intro c hc
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ha
      · exact h2 c hc
    · refine ⟨insert a Sq, Finset.insert_subset_insert _ h0, ?_, ?_⟩
      · intro Q hQ Q' hQ' h
        rcases Finset.mem_insert.1 hQ with rfl | hQs
        · rcases Finset.mem_insert.1 hQ' with rfl | hQ'
          · rfl
          · exact absurd ⟨Q', hQ', h⟩ ha
        · rcases Finset.mem_insert.1 hQ' with rfl | hQ'
          · refine absurd ⟨Q, hQs, ?_⟩ ha
            rcases h with h | h
            · left
              have := M.neg_mem h
              rwa [neg_sub] at this
            · right
              rwa [add_comm] at h
          · exact h1 Q hQs Q' hQ' h
      · intro c hc
        rcases Finset.mem_insert.1 hc with rfl | hc
        · exact ⟨c, Finset.mem_insert_self _ _, Or.inl (by simp)⟩
        · obtain ⟨Q, hQ, h⟩ := h2 c hc
          exact ⟨Q, Finset.mem_insert_of_mem hQ, h⟩

theorem half_fibre_exists_holds : HalfFibreExists := by
  classical
  intro L α ω₀ hα hst _ hno
  obtain ⟨S, hS1, _, hS3⟩ := Formalism.L2.Th1.F.kerRepsExist L α hα hst
  set Q0 : ℂ := (ω₀ / 2) / α with hQ0
  have hαQ0 : α * Q0 = ω₀ / 2 := by rw [hQ0]; field_simp
  obtain ⟨Sq, h0, h1, h2⟩ :=
    exists_transversal L.lattice (insert Q0 (S.image (fun P => Q0 + P)))
  have hfib : ∀ c ∈ insert Q0 (S.image (fun P => Q0 + P)), α * c - ω₀ / 2 ∈ L.lattice := by
    intro c hc
    rcases Finset.mem_insert.1 hc with rfl | hc
    · rw [hαQ0, sub_self]; exact L.lattice.zero_mem
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hc
      have : α * (Q0 + P) - ω₀ / 2 = α * P := by rw [mul_add, hαQ0]; ring
      rw [this]; exact (hS1 P hP).1
  refine ⟨Sq, ?_, h1, ?_⟩
  · intro Q hQ
    exact ⟨hfib Q (h0 hQ), hno Q (hfib Q (h0 hQ))⟩
  · intro z hz
    have hker : α * (z - Q0) ∈ L.lattice := by
      have : α * (z - Q0) = α * z - ω₀ / 2 := by rw [mul_sub, hαQ0]
      rw [this]; exact hz
    obtain ⟨c, hc, hzc⟩ : ∃ c ∈ insert Q0 (S.image (fun P => Q0 + P)), z - c ∈ L.lattice := by
      by_cases hz0 : z - Q0 ∈ L.lattice
      · exact ⟨Q0, Finset.mem_insert_self _ _, hz0⟩
      · obtain ⟨P, hP, h⟩ := hS3 (z - Q0) hker hz0
        refine ⟨Q0 + P, Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨P, hP, rfl⟩), ?_⟩
        have : z - (Q0 + P) = z - Q0 - P := by ring
        rw [this]; exact h
    obtain ⟨Q, hQ, h⟩ := h2 c hc
    refine ⟨Q, hQ, ?_⟩
    rcases h with h | h
    · left
      have : z - Q = (z - c) + (c - Q) := by ring
      rw [this]; exact L.lattice.add_mem hzc h
    · right
      have : z + Q = (z - c) + (c + Q) := by ring
      rw [this]; exact L.lattice.add_mem hzc h

section Alg

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem map_derivative (f : PowerSeries K) :
    PowerSeries.map φ (PowerSeries.derivative (R := K) f) =
      PowerSeries.derivative (R := K') (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_derivative]

theorem map_rescale (a : K) (f : PowerSeries K) :
    PowerSeries.map φ (PowerSeries.rescale a f) =
      PowerSeries.rescale (φ a) (PowerSeries.map φ f) := by
  ext n
  simp [PowerSeries.coeff_rescale]

theorem map_wpShift (e : PowerSeries K) (c : K) :
    PowerSeries.map φ (wpShift e c) = wpShift (PowerSeries.map φ e) (φ c) := by
  unfold wpShift
  simp

theorem second_log_derivative_map {f g : PowerSeries K} (h : HasSecondLogDeriv f g) :
    HasSecondLogDeriv (PowerSeries.map φ f) (PowerSeries.map φ g) := by
  unfold HasSecondLogDeriv at h ⊢
  have := congrArg (PowerSeries.map φ) h
  simpa [map_derivative] using this

end Alg

theorem fibre_map_holds : FibreMap := by
  intro K K' _ _ _ _ j P tr ι _ c wp wm al S h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro Q
    have := second_log_derivative_map j (h1 Q)
    have e2 : PowerSeries.map j (2 : PowerSeries K) = 2 := map_ofNat _ 2
    rw [map_wpShift] at this
    simpa [e2] using this
  · have := congrArg (PowerSeries.map j) h2
    simpa [map_rescale] using this

theorem norm_x_le_one_of_not_in_kernel {K : Type} [NormedField K] {W : WeierstrassCurve K}
    (P : W.toAffine.Point) (h : ¬ InFormalGroupPoints P) : ‖px W P‖ ≤ 1 := by
  cases P with
  | zero => exact absurd trivial h
  | some x y hxy => exact not_lt.1 h


end Formalism.L2.Th1.B.Half
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.FibreIntegerInstanceHolds
noncomputable section
open scoped BigOperators
open Filter Topology

namespace Formalism.L2.Th1.B.Fib

open PowerSeries
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries taylor_ring isogenyP halfShift)
open Formalism.L2.Th1.F.TaylorWp
open Formalism.L2.Th1.F.EndoZ

theorem sum_reps {ι κ M : Type} [AddCommMonoid M] (L : PeriodPair) (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ)
    (hA : ∀ i ∈ s, ∀ i' ∈ s, a i - a i' ∈ L.lattice → i = i')
    (hB : ∀ j ∈ t, ∀ j' ∈ t, b j - b j' ∈ L.lattice → j = j')
    (hAB : ∀ i ∈ s, ∃ j ∈ t, a i - b j ∈ L.lattice)
    (hBA : ∀ j ∈ t, ∃ i ∈ s, b j - a i ∈ L.lattice)
    (f : ℂ → M) (hf : ∀ x y, x - y ∈ L.lattice → f x = f y) :
    ∑ i ∈ s, f (a i) = ∑ j ∈ t, f (b j) := by
  choose φ hφ using hAB
  refine Finset.sum_bij φ (fun i hi => (hφ i hi).1) ?_ ?_ (fun i hi => hf _ _ (hφ i hi).2)
  · intro i hi i' hi' h
    apply hA i hi i' hi'
    have h1 := L.lattice.sub_mem (hφ i hi).2 (hφ i' hi').2
    rw [h] at h1
    have e : a i - b (φ i' hi') - (a i' - b (φ i' hi')) = a i - a i' := by ring
    rwa [e] at h1
  · intro j hj
    obtain ⟨i, hi, h⟩ := hBA j hj
    refine ⟨i, hi, ?_⟩
    apply hB _ (hφ i hi).1 j hj
    have h1 := L.lattice.neg_mem (L.lattice.add_mem h (hφ i hi).2)
    have e : -(b j - a i + (a i - b (φ i hi))) = b (φ i hi) - b j := by ring
    rwa [e] at h1

def repA (Q0 : ℂ) : Option ℂ → ℂ := fun o => Q0 + o.elim 0 id

def repB : ℂ ⊕ ℂ → ℂ := Sum.elim id Neg.neg

theorem two_mul_half (ω₀ : ℂ) : 2 * (ω₀ / 2) = ω₀ := by ring

theorem notMem_of_two {L : PeriodPair} {Q : ℂ} (h : 2 * Q ∉ L.lattice) : Q ∉ L.lattice := by
  intro hQ
  apply h
  rw [two_mul]
  exact L.lattice.add_mem hQ hQ

theorem fibre_sum {M : Type} [AddCommMonoid M] (L : PeriodPair) (α ω₀ : ℂ) (S Sq : Finset ℂ)
    (hα : α ≠ 0) (hS : IsKerReps L α S) (hω : ω₀ ∈ L.lattice)
    (hq : IsHalfFibre L α (ω₀ / 2) Sq)
    (f : ℂ → M) (hf : ∀ x y, x - y ∈ L.lattice → f x = f y) :
    f (ω₀ / 2 / α) + ∑ P ∈ S, f (ω₀ / 2 / α + P) = ∑ Q ∈ Sq, f Q + ∑ Q ∈ Sq, f (-Q) := by
  have key := sum_reps L (Finset.insertNone S) (Sq.disjSum Sq) (repA (ω₀ / 2 / α)) repB
    ?_ ?_ ?_ ?_ f hf
  · rw [Finset.sum_insertNone, Finset.sum_disjSum] at key
    simpa [repA, repB] using key
  · intro i hi i' hi' h
    rcases i with _ | P <;> rcases i' with _ | P'
    · rfl
    · exfalso
      have hP' : P' ∈ S := by simpa using hi'
      apply (hS.1 P' hP').2
      have h1 := L.lattice.neg_mem h
      simpa [repA] using h1
    · exfalso
      have hP : P ∈ S := by simpa using hi
      apply (hS.1 P hP).2
      simpa [repA] using h
    · have hP : P ∈ S := by simpa using hi
      have hP' : P' ∈ S := by simpa using hi'
      congr 1
      apply hS.2.1 P hP P' hP'
      simpa [repA] using h
  · intro j hj j' hj' h
    rcases j with Q | Q <;> rcases j' with Q' | Q'
    · have hQ : Q ∈ Sq := by simpa using hj
      have hQ' : Q' ∈ Sq := by simpa using hj'
      congr 1
      exact hq.2.1 Q hQ Q' hQ' (Or.inl (by simpa [repB] using h))
    · exfalso
      have hQ : Q ∈ Sq := by simpa using hj
      have hQ' : Q' ∈ Sq := by simpa using hj'
      have h1 : Q + Q' ∈ L.lattice := by simpa [repB] using h
      have e := hq.2.1 Q hQ Q' hQ' (Or.inr h1)
      subst e
      apply (hq.1 Q hQ).2
      rwa [two_mul]
    · exfalso
      have hQ : Q ∈ Sq := by simpa using hj
      have hQ' : Q' ∈ Sq := by simpa using hj'
      have h1 : Q + Q' ∈ L.lattice := by
        have h2 := L.lattice.neg_mem h
        have e : -(repB (Sum.inr Q) - repB (Sum.inl Q')) = Q + Q' := by simp [repB]; ring
        rwa [e] at h2
      have e := hq.2.1 Q hQ Q' hQ' (Or.inr h1)
      subst e
      apply (hq.1 Q hQ).2
      rwa [two_mul]
    · have hQ : Q ∈ Sq := by simpa using hj
      have hQ' : Q' ∈ Sq := by simpa using hj'
      congr 1
      refine hq.2.1 Q hQ Q' hQ' (Or.inl ?_)
      have h2 := L.lattice.neg_mem h
      have e : -(repB (Sum.inr Q) - repB (Sum.inr Q')) = Q - Q' := by simp [repB]; ring
      rwa [e] at h2
  · intro i hi
    have h1 : α * repA (ω₀ / 2 / α) i - ω₀ / 2 ∈ L.lattice := by
      rcases i with _ | P
      · have e : α * repA (ω₀ / 2 / α) none - ω₀ / 2 = 0 := by
          simp only [repA, Option.elim_none, add_zero]
          field_simp
          ring
        rw [e]
        exact L.lattice.zero_mem
      · have hP : P ∈ S := by simpa using hi
        have e : α * repA (ω₀ / 2 / α) (some P) - ω₀ / 2 = α * P := by
          simp only [repA, Option.elim_some, id]
          field_simp
          ring
        rw [e]
        exact (hS.1 P hP).1
    obtain ⟨Q, hQ, h2 | h2⟩ := hq.2.2 _ h1
    · exact ⟨Sum.inl Q, by simpa using hQ, by simpa [repB] using h2⟩
    · exact ⟨Sum.inr Q, by simpa using hQ, by simpa [repB] using h2⟩
  · intro j hj
    have h1 : α * repB j - ω₀ / 2 ∈ L.lattice := by
      rcases j with Q | Q
      · have hQ : Q ∈ Sq := by simpa using hj
        simpa [repB] using (hq.1 Q hQ).1
      · have hQ : Q ∈ Sq := by simpa using hj
        have h2 := L.lattice.sub_mem (L.lattice.neg_mem (hq.1 Q hQ).1) hω
        have e : -(α * Q - ω₀ / 2) - ω₀ = α * repB (Sum.inr Q) - ω₀ / 2 := by
          simp only [repB, Sum.elim_inr]
          ring
        rwa [e] at h2
    have h3 : α * (repB j - ω₀ / 2 / α) ∈ L.lattice := by
      have e : α * (repB j - ω₀ / 2 / α) = α * repB j - ω₀ / 2 := by
        field_simp
      rwa [e]
    by_cases h4 : repB j - ω₀ / 2 / α ∈ L.lattice
    · exact ⟨none, by simp, by simpa [repA] using h4⟩
    · obtain ⟨P, hP, h5⟩ := hS.2.2 _ h3 h4
      refine ⟨some P, by simpa using hP, ?_⟩
      have e : repB j - repA (ω₀ / 2 / α) (some P) = repB j - ω₀ / 2 / α - P := by
        simp only [repA, Option.elim_some, id]
        ring
      rwa [e]

theorem fibre_card (L : PeriodPair) (α ω₀ : ℂ) (S Sq : Finset ℂ)
    (hα : α ≠ 0) (hS : IsKerReps L α S) (hω : ω₀ ∈ L.lattice)
    (hq : IsHalfFibre L α (ω₀ / 2) Sq) : 2 * Sq.card = S.card + 1 := by
  have h := fibre_sum L α ω₀ S Sq hα hS hω hq (fun _ => (1 : ℕ)) (fun _ _ _ => rfl)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  omega

theorem T_shift_sub (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    T (fun z => L.weierstrassP (z - P)) (taylor0 fun z => L.weierstrassP (z - P)) := by
  have hP' : -P ∉ L.lattice := fun h => hP (by simpa using L.lattice.neg_mem h)
  simpa only [← sub_eq_add_neg] using T_shift L hP'

theorem clause1 (L : PeriodPair) {Q : ℂ} (hQ : Q ∉ L.lattice) :
    Formalism.L2.Th1.C.HasSecondLogDeriv (Formalism.L2.Th1.C.wpShift (pSeries L) (L.weierstrassP Q))
      (2 * pSeries L - taylor0 (fun z => L.weierstrassP (z + Q))
        - taylor0 (fun z => L.weierstrassP (z - Q))) := by
  have h := clause2 L (P := Q) (Q := -Q) hQ (by simp)
  simpa only [← sub_eq_add_neg] using h

theorem ev_mul_shift_notMem (L : PeriodPair) (α : ℂ) {t : ℂ} (ht : t ∉ L.lattice) :
    ∀ᶠ z in 𝓝 (0 : ℂ), α * z + t ∉ L.lattice := by
  have h1 : Tendsto (fun z : ℂ => α * z) (𝓝 0) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => α * z) (𝓝 0) (𝓝 (α * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rwa [mul_zero] at this
  exact h1.eventually (ev_shift_notMem L ht)

theorem clauseSum (L : PeriodPair) (α ω₀ : ℂ) (S Sq : Finset ℂ) (hα : α ≠ 0) (hm : MulStable L α)
    (hS : IsKerReps L α S) (hω : ω₀ ∈ L.lattice) (ht : ω₀ / 2 ∉ L.lattice)
    (hq : IsHalfFibre L α (ω₀ / 2) Sq) :
    C (α ^ 2) * rescale α (taylor0 fun z => L.weierstrassP (z + ω₀ / 2))
      = ∑ Q : Sq, ((taylor0 fun z => L.weierstrassP (z + (Q : ℂ)))
          + taylor0 fun z => L.weierstrassP (z - (Q : ℂ))) - C (∑ P ∈ S, L.weierstrassP P) := by
  have h1 := T.mul taylor_ring (T.const taylor_ring (α ^ 2)) (T.rescale α (T_shift L ht))
  have h2 := T.sub (T.sum (Finset.univ : Finset Sq)
    (fun Q z => L.weierstrassP (z + (Q : ℂ)) + L.weierstrassP (z - (Q : ℂ)))
    (fun Q => (taylor0 fun z => L.weierstrassP (z + (Q : ℂ)))
      + taylor0 fun z => L.weierstrassP (z - (Q : ℂ)))
    (fun Q _ => T.add taylor_ring (T_shift L (notMem_of_two (hq.1 Q Q.2).2))
      (T_shift_sub L (notMem_of_two (hq.1 Q Q.2).2))))
    (T.const taylor_ring (∑ P ∈ S, L.weierstrassP P))
  refine T.unique h1 h2 ?_
  filter_upwards [(ev_mul_shift_notMem L α ht).filter_mono nhdsWithin_le_nhds] with z hz
  have e : α * (z + ω₀ / 2 / α) = α * z + ω₀ / 2 := by field_simp
  have h3 := isogenyP L α S hα hm hS (z + ω₀ / 2 / α) (by rwa [e])
  rw [e, Finset.sum_sub_distrib] at h3
  have h4 := fibre_sum L α ω₀ S Sq hα hS hω hq (fun c => L.weierstrassP (z + c)) (by
    intro x y hxy
    apply wp_congr L
    have e2 : z + x - (z + y) = x - y := by ring
    rwa [e2])
  rw [Finset.sum_coe_sort Sq (fun Q => L.weierstrassP (z + Q) + L.weierstrassP (z - Q)),
    Finset.sum_add_distrib]
  simp only [← sub_eq_add_neg, ← add_assoc] at h4
  linear_combination h3 + h4

theorem fibre_integer_instance_holds : FibreZInstance := by
  intro L α ω₀ S Sq hα hm hS hω ht hq
  refine ⟨fibre_card L α ω₀ S Sq hα hS hω hq, ?_, clauseSum L α ω₀ S Sq hα hm hS hω ht hq⟩
  intro Q
  exact clause1 L (notMem_of_two (hq.1 Q Q.2).2)

theorem half_shift_series_holds : HalfShiftSeries := by
  intro L ω₀ hω ht
  set t : ℂ := ω₀ / 2 with htd
  have h2t : 2 * t ∈ L.lattice := by rw [htd, two_mul_half]; exact hω
  have h1 := T.mul taylor_ring (T.sub (T_shift L ht) (T.const taylor_ring (L.weierstrassP t)))
    (T_fP L t)
  have h2 := T.mul taylor_ring (T.const taylor_ring (3 * L.weierstrassP t ^ 2 - L.g₂ / 4))
    (T.pow taylor_ring (T.id taylor_ring) 2)
  have h3 := T.unique h1 h2 (by
    filter_upwards [ev_notMem L, (ev_shift_notMem L ht).filter_mono nhdsWithin_le_nhds] with z hz hzt
    have hz0 : z ≠ 0 := ne_zero_of_notMem L hz
    rw [fP_eq L t hz0]
    have h := halfShift L t z ht h2t hz hzt
    linear_combination z ^ 2 * h)
  have h4 := GCob.wOf_mul (L.weierstrassP t) (pSeries L)
  have hU : (1 + X ^ 2 * pSeries L - C (L.weierstrassP t) * X ^ 2 : PowerSeries ℂ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  apply mul_right_cancel₀ hU
  unfold Formalism.L2.Th1.C.wpShift at h3
  linear_combination h3 - C (3 * L.weierstrassP t ^ 2 - L.g₂ / 4) * h4

end Formalism.L2.Th1.B.Fib
end
end

namespace Formalism.L2.Th1.B

theorem halfFibreExists : HalfFibreExists := Half.half_fibre_exists_holds
theorem fibreZInstance : FibreZInstance := Fib.fibre_integer_instance_holds
theorem halfShiftSeries : HalfShiftSeries := Fib.half_shift_series_holds
theorem fibreMap : FibreMap := Half.fibre_map_holds
theorem th0TwoAnalytic : ThetaZeroTwoAnalytic :=
  An2.Th0TwoAnalytic_of halfFibreExists fibreZInstance halfShiftSeries fibreMap

end Formalism.L2.Th1.B
