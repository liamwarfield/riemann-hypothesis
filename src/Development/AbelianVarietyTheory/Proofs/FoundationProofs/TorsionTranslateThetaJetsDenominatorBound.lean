module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaFunctionsOverTwoUnitAndIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointLocalHeightEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPadicWeierstrassModelAbscissaTwoTorsionLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOrderParameterSeriesBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOrderParameterSeriesBounded
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter
open scoped Topology

noncomputable section

namespace GlobalTheory.ThetaOrderBdd
open GlobalTheory.ThetaTransl GlobalTheory.ThetaTranslDecomp

variable {Λ : AddSubgroup ℂ}

theorem ratio_add (hΛ : IsLat Λ) {G : ℂ → ℂ} {k : ℕ}
    (hlaw : ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ k = G z * sgStar Λ (z + ω) ^ k)
    (z : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    G (z + l) / sgStar Λ (z + l) ^ k = G z / sgStar Λ z ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hlaw l hl z
  by_cases hz : z ∈ Λ
  · rw [(hΛ.sg_eq_zero z).2 hz, (hΛ.sg_eq_zero _).2 (add_mem hz hl), zero_pow hk.ne']
    simp
  have h0 := (hΛ.sg_eq_zero z).not.2 hz
  have h1 : sgStar Λ (z + l) ≠ 0 := (hΛ.sg_eq_zero _).not.2 (fun h => hz (by simpa using sub_mem h hl))
  rw [div_eq_div_iff (pow_ne_zero _ h1) (pow_ne_zero _ h0)]
  exact hlaw l hl z

theorem exists_decomp_gen : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (k : ℕ) (G : ℂ → ℂ), Differentiable ℂ G →
    (∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ k = G z * sgStar Λ (z + ω) ^ k) →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), k ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - k) * G z =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  intro Λ hΛ k G hG hlaw v hv
  obtain ⟨L, h⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hσ := hΛ.differentiable
  have hS := hΛ.differentiable_sqTh v
  have hT : Continuous (sqThD Λ v) := by
    have h1 := hσ.deriv.continuous
    have h2 := hS.deriv.continuous
    have h3 := hσ.continuous
    have h4 := hS.continuous
    unfold sqThD
    fun_prop
  have hc : ∀ z, z ∉ L.lattice →
      ContinuousAt (fun z => G z / sgStar Λ z ^ k) z := fun z hz =>
    (hG z).continuousAt.div ((hσ z).continuousAt.pow k)
      (pow_ne_zero _ ((hΛ.sg_eq_zero z).not.2 ((h z).not.2 hz)))
  obtain ⟨A, B, hAB⟩ := GlobalTheory.EllipticPoles.no_pole_case L
    (g := fun z => G z / sgStar Λ z ^ k)
    (fun a => (hG.analyticAt a).meromorphicAt.div ((hσ.analyticAt a).meromorphicAt.pow k))
    (fun a ha => ⟨_, (hc a ha).tendsto.mono_left nhdsWithin_le_nhds⟩)
    (fun z l hl => ratio_add hΛ hlaw z ((h l).2 hl))
  have hAB' : ∀ z, z ∉ L.lattice → G z / sgStar Λ z ^ k =
      A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    intro z hz
    have h1 := (L.analyticOnNhd_weierstrassP z hz).continuousAt
    have h2 := (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt
    have h3 : ContinuousAt (fun z => A.eval (L.weierstrassP z) +
        B.eval (L.weierstrassP z) * L.derivWeierstrassP z) z :=
      (A.continuous.continuousAt.comp h1).add ((B.continuous.continuousAt.comp h1).mul h2)
    exact tendsto_nhds_unique_of_eventuallyEq ((hc z hz).tendsto.mono_left nhdsWithin_le_nhds)
      (h3.tendsto.mono_left nhdsWithin_le_nhds) (hAB z)
  set A' := Polynomial.taylor (wpF Λ v) A with hA'
  set B' := Polynomial.taylor (wpF Λ v) B with hB'
  obtain ⟨I, hI⟩ : ∃ I, I = A'.natDegree + B'.natDegree + k := ⟨_, rfl⟩
  refine ⟨I, A'.coeff, B'.coeff, by omega, fun z => ?_⟩
  have h3 := hσ.continuous
  have h4 := hS.continuous
  have h5 := hG.continuous
  refine congrFun (Continuous.ext_on hΛ.dense_compl
    (f := fun z => sgStar Λ z ^ (2 * I + 3 - k) * G z)
    (g := fun z => ∑ i ∈ Finset.range (I + 1),
      A'.coeff i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
      ∑ j ∈ Finset.range (I + 1),
        B'.coeff j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z))
    (by fun_prop) (by fun_prop) fun z hz => ?_) z
  have hz' : z ∉ L.lattice := (h z).not.1 hz
  have h0 := (hΛ.sg_eq_zero z).not.2 hz
  have e := hAB' z hz'
  rw [← Polynomial.taylor_eval_sub (wpF Λ v) A, ← Polynomial.taylor_eval_sub (wpF Λ v) B,
    ← hA', ← hB', Polynomial.eval_eq_sum_range' (n := I + 1) (p := A') (by omega),
    Polynomial.eval_eq_sum_range' (n := I + 1) (p := B') (by omega),
    div_eq_iff (pow_ne_zero _ h0)] at e
  beta_reduce
  rw [e, mul_left_comm, ← pow_add, Nat.sub_add_cancel (by omega), sqThD_eq hΛ L h hv hz,
    hΛ.sqTh_eq hv hz, GlobalTheory.OddTheta.wpF_eq L Λ h z, add_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun i hi => ?_
  all_goals
    obtain ⟨m, rfl⟩ : ∃ m, I = i + m := Nat.exists_eq_add_of_le (by simpa [Nat.lt_succ_iff] using hi)
    rw [Nat.add_sub_cancel_left, mul_pow]
    ring


set_option maxHeartbeats 800000 in
theorem order_bdd : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
    ∀ (k : ℕ) (G : ℂ → ℂ), AlgEnt G →
      (∀ ω ∈ g.abelian₂, ∀ z, G (z + ω) * sgStar g.abelian₂ z ^ k = G z * sgStar g.abelian₂ (z + ω) ^ k) →
      ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU G = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B := by
  intro p _ g hok hlat' h2 h3 hdisc hsg v hv hwv k G hG hlaw
  obtain ⟨hu1, hwq1, -, he0, hsgU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def
  have he : e ≠ 0 := fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0
  have gσ : GoodAt g 1 (sgStar g.abelian₂) :=
    ⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (ThetaTransl.bdd_C ε) bdd_X, by rw [hsgU]; ring⟩
  obtain ⟨hSa, hSe⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg v hv hwv
  have gS : GoodAt g 2 (sqTh g.abelian₂ v) := ⟨hSa, lineSer g.wq⁻¹ (xAt g v),
    bdd_sub ⟨1, hwq1⟩ (bdd_mul (ThetaTransl.bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩
  obtain ⟨hTa, w, hw, hTe⟩ := GlobalTheory.ThetaTransl.CubeSer.sqThD_atU p g hok hlat' h2 h3 hdisc hsg v hv hwv
  have gT : GoodAt g 3 (sqThD g.abelian₂ v) := ⟨hTa, w, hw, hTe⟩
  obtain ⟨I, a, b, hle, hid⟩ := exists_decomp_gen g.abelian₂ hlat' k G hG.1 hlaw v hv
  let φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ := Sum.elim
    (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ v z ^ (i : ℕ))
    (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ v z ^ (j : ℕ) * sqThD g.abelian₂ v z)
  let c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ := Sum.elim (fun i => a i) (fun j => b j)
  have gφ : ∀ k, GoodAt g (2 * I + 3) (φ k) := by
    rintro (i | j)
    · have hi := i.isLt
      exact good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)
    · have hj := j.isLt
      exact good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT)
        (by omega)
  obtain ⟨hEa, hEe⟩ := atU_mul_pow (g := g) hsg hG (2 * I + 3 - k) 1
  have hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - k) * G z ^ 1 = ∑ j, c j * φ j z := by
    intro z
    rw [pow_one, hid z, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
  obtain ⟨a', -, hlin⟩ := GlobalTheory.TranslLin.transl_lin p g _ φ c _ hEa (fun j => (gφ j).1) hEq
  choose B hB hBe using fun j => (gφ j).2
  have hS : BddSer (∑ j, PowerSeries.C (lamC g.lam (a' j)) * B j) :=
    bdd_sum _ _ fun j _ => bdd_mul (ThetaTransl.bdd_C _) (hB j)
  rw [hEe, hsgU, pow_one] at hlin
  simp only [hBe] at hlin
  set Bk : PowerSeries ℂ_[p] := (e ^ k)⁻¹ * g.atU G with hBk
  have hGe : g.atU G = e ^ k * Bk := by
    rw [hBk, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [map_pow, he0, one_pow]; exact one_ne_zero),
      one_mul]
  rw [hGe] at hlin
  set K := 2 * I + 3 - k with hKd
  have hK : K + k = 2 * I + 3 := Nat.sub_add_cancel hle
  have hsum : ∑ j, PowerSeries.C (lamC g.lam (a' j)) * (e ^ (2 * I + 3) * B j) =
      e ^ (2 * I + 3) * ∑ j, PowerSeries.C (lamC g.lam (a' j)) * B j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e ^ k * Bk) =
      e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * Bk)) := by
    rw [← hK, pow_add, map_pow]; ring
  have key := hleft.symm.trans (hlin.trans hsum)
  have key2 := mul_left_cancel₀ (pow_ne_zero _ he) key
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨Bk, ⟨C0, fun n => ?_⟩, hGe⟩
  have h1 := congrArg (PowerSeries.coeff (n + K)) key2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h1
  have h2 := hC0 (n + K)
  rw [← h1, norm_mul, norm_pow, hu1, one_pow, one_mul] at h2
  exact h2

end GlobalTheory.ThetaOrderBdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOrderParameterSeriesBoundedStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOrder_parameterSeries_bounded : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → ∀ (k : ℕ) (G : ℂ → ℂ), AlgEnt G → (∀ ω ∈ g.abelian₂, ∀ z, G (z + ω) * sgStar g.abelian₂ z ^ k = G z * sgStar g.abelian₂ (z + ω) ^ k) → ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU G = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B := by
  first | exact @GlobalTheory.ThetaOrderBdd.order_bdd | exact GlobalTheory.ThetaOrderBdd.order_bdd | (intros; apply GlobalTheory.ThetaOrderBdd.order_bdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateProductSigmaStarPowLatticeLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateProductSigmaStarPowLatticeLaw
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ThetaLaw

open GlobalTheory.ThetaParam

theorem pull_law : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, 2 * t₀ ∈ Λ → ∀ (y : ℂ) (N : ℕ), (N : ℂ) * y ∈ Λ → ∀ ω ∈ Λ, ∀ z : ℂ, (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * (z + ω)) * GL3Theta.th0 Λ t₀ ((N : ℂ) * (z + ω))) * sgStar Λ z ^ (2 * N ^ 2) = (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * z) * GL3Theta.th0 Λ t₀ ((N : ℂ) * z)) * sgStar Λ (z + ω) ^ (2 * N ^ 2) := by
  intro Λ hΛ t₀ ht y N hy ω hω z
  have hlaw : ∀ x ∈ Λ, ∀ v, sgStar Λ (v + x) = (if x / 2 ∈ Λ then 1 else -1) * sgStar Λ v *
      Complex.exp ((Real.pi : ℂ) * v * (starRingEnd ℂ) x / (area Λ : ℂ) +
        (Real.pi : ℂ) * x * (starRingEnd ℂ) x / (2 * (area Λ : ℂ))) := by
    intro x hx v
    have e := hΛ.sg_law hx v
    simp only [U1] at e
    rw [← e, mul_assoc, ← Complex.exp_add]
    ring_nf
    simp
  have hne : ∃ z, sgStar Λ z ≠ 0 := by
    by_contra h
    push_neg at h
    have hd := (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1
    rw [show sgStar Λ = fun _ => 0 from funext h] at hd
    simp at hd
  have hsl : ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z :=
    fun ω hω z => hΛ.sg_law hω z
  have hx : (N : ℂ) * ω ∈ Λ := by simpa [nsmul_eq_mul] using nsmul_mem hω N
  have c1 : cocy Λ ((N : ℂ) * ω) y ^ 2 = 1 := by
    have e := cocy_pow Λ ω y N 1
    have r := cocy_root (m := 1) (n := N) hne hsl (by simpa using hω) hy
    simp only [Nat.cast_one, one_mul, mul_one] at e r
    rw [e, ← pow_mul, r]
  have c2 : cocy Λ ((N : ℂ) * ω) t₀ ^ 4 = 1 := by
    have r := cocy_root (m := 1) (n := 2) hne hsl (a := (N : ℂ) * ω) (b := t₀) (by simpa using hx) (by simpa using ht)
    simpa using r
  have hψ : ∀ x : ℂ, (if x / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 = 1 := by
    intro x; split_ifs <;> norm_num
  have hprod : ∀ v, U1 Λ y (GL3Theta.th0 Λ t₀) v * GL3Theta.th0 Λ t₀ v =
      sgStar Λ (v + y + t₀) * sgStar Λ (v + t₀) *
        (Complex.exp (-(Real.pi : ℂ) * (v + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * v * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * v * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) /
        (U1 Λ t₀ (sgStar Λ) 0) ^ 2 := by
    intro v
    simp only [GL3Theta.th0, U1]
    ring
  have hE : Complex.exp ((Real.pi : ℂ) * ((N : ℂ) * z + y + t₀) * (starRingEnd ℂ) ((N : ℂ) * ω) / (area Λ : ℂ) +
        (Real.pi : ℂ) * ((N : ℂ) * ω) * (starRingEnd ℂ) ((N : ℂ) * ω) / (2 * (area Λ : ℂ))) *
      Complex.exp ((Real.pi : ℂ) * ((N : ℂ) * z + t₀) * (starRingEnd ℂ) ((N : ℂ) * ω) / (area Λ : ℂ) +
        (Real.pi : ℂ) * ((N : ℂ) * ω) * (starRingEnd ℂ) ((N : ℂ) * ω) / (2 * (area Λ : ℂ))) *
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω) + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω)) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω)) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) =
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) *
      Complex.exp ((Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) +
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ))) ^ (2 * N ^ 2) *
      (cocy Λ ((N : ℂ) * ω) y ^ 2 * cocy Λ ((N : ℂ) * ω) t₀ ^ 4) := by
    simp only [cocy, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_add (f := _), map_natCast]
    push_cast
    ring
  rw [c1, c2, mul_one, mul_one] at hE
  rw [hprod, hprod,
    show (N : ℂ) * (z + ω) + y + t₀ = ((N : ℂ) * z + y + t₀) + (N : ℂ) * ω by ring,
    show (N : ℂ) * (z + ω) + t₀ = ((N : ℂ) * z + t₀) + (N : ℂ) * ω by ring,
    hlaw _ hx, hlaw _ hx, hlaw _ hω z, mul_pow, mul_pow, pow_mul (if ω / 2 ∈ Λ then (1 : ℂ) else -1) 2 (N ^ 2), hψ ω, one_pow, one_mul]
  linear_combination (sgStar Λ ((N : ℂ) * z + y + t₀) * sgStar Λ ((N : ℂ) * z + t₀) * sgStar Λ z ^ (2 * N ^ 2) /
      (U1 Λ t₀ (sgStar Λ) 0) ^ 2) * ((if (N : ℂ) * ω / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 * hE +
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) *
      Complex.exp ((Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) +
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ))) ^ (2 * N ^ 2) * hψ ((N : ℂ) * ω))

end GlobalTheory.ThetaLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateProductSigmaStarPowLatticeLawStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslateProduct_sigmaStarPow_lattice_law : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, 2 * t₀ ∈ Λ → ∀ (y : ℂ) (N : ℕ), (N : ℂ) * y ∈ Λ → ∀ ω ∈ Λ, ∀ z : ℂ, (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * (z + ω)) * GL3Theta.th0 Λ t₀ ((N : ℂ) * (z + ω))) * sgStar Λ z ^ (2 * N ^ 2) = (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * z) * GL3Theta.th0 Λ t₀ ((N : ℂ) * z)) * sgStar Λ (z + ω) ^ (2 * N ^ 2) := by
  first | exact @GlobalTheory.ThetaLaw.pull_law | exact GlobalTheory.ThetaLaw.pull_law | (intros; apply GlobalTheory.ThetaLaw.pull_law <;> assumption)
end
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.PullBackSplit
open GlobalTheory.EvenTheta

section
variable {p : ℕ} [Fact p.Prime]

theorem int_mulBy_of_closure (g : GL3Theta.G1 p) (hok : g.Ok) {c : ℂ_[p]}
    (hc : c ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[p]))) :
    IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  refine closure_minimal (t := {c : ℂ_[p] | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])})
    ?_ (GlobalTheory.mulBy_integral_isClosed p g) hc
  rintro _ ⟨n, rfl⟩
  show IntegralMv _
  rw [GlobalTheory.SerTransport.mulBy_X]
  exact intSer_iff.2 ((GlobalTheory.IntDLog.int_dlog p g hok).2.2 n)

theorem neg_one_mem_closure : (-1 : ℂ_[p]) ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[p])) := by
  have h1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h2 := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1).sub_const 1
  rw [zero_sub] at h2
  refine mem_closure_of_tendsto h2 (Filter.Eventually.of_forall fun n => ⟨p ^ n - 1, ?_⟩)
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)]
  simp

theorem int_of_mul_reflect {f m : PowerSeries ℂ_[p]} (hf : BddSer f) (hm : IntSer m)
    (hm0 : PowerSeries.constantCoeff m = 0)
    (hmm : (PowerSeries.subst m (PowerSeries.subst m f : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p]) = f)
    (h : IntSer (f * PowerSeries.subst m f)) : IntSer f := by
  have hS := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.2.2.1
  obtain ⟨B, hB⟩ := hf
  intro n
  by_contra hn
  push Not at hn
  have h1 := GlobalTheory.EvenTheta.sup_norm_mul_padicComplex p f _ 1 ⟨B, hB⟩ ⟨B, hS f m B hB hm hm0⟩ h n
  have h2 := hS (PowerSeries.subst m f) m 1 (fun j => by
    nlinarith [h1 j, norm_nonneg (PowerSeries.coeff j (PowerSeries.subst m f : PowerSeries ℂ_[p]))]) hm hm0 n
  rw [hmm] at h2
  linarith

theorem IntSer.pow {f : PowerSeries ℂ_[p]} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => rw [pow_zero, ← map_one PowerSeries.C]; exact int_C (by simp)
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem translate_sigma_star_neg {Λ : AddSubgroup ℂ} (h : IsLat Λ) (v z : ℂ) :
    U1 Λ v (sgStar Λ) (-z) = -U1 Λ (-v) (sgStar Λ) z := by
  simp only [U1]
  rw [show -z + v = -(z + -v) by ring, h.sg_neg, map_neg, neg_mul]
  congr 3 <;> ring

end

theorem norm_padicWeierstrassModelAbscissa_twoTorsion_le_one (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p)
    (hg : GL3Theta.At D cc δ g) (t0 : ℂ) (ht0 : GL3Theta.IsTwoTorsionPointUnkilled D g.abelian₂ t0) : ‖xAt g t0‖ ≤ 1 := by
  have hg' := hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hnm : t0 ∉ g.abelian₂ := GlobalTheory.PositiveMeans.not_mem_lattice_of_isCMTorsionBasePoint ht0 hst
  by_cases hp : p = 2
  · subst hp
    obtain ⟨a, β, k, ha, hβ, hn, htrc, hN, hb⟩ := GlobalTheory.EvenTheta.exists_int_trace_one_unit_at_two D g.lam
    obtain ⟨hb1, hb2⟩ := hb _ _ ht0
    have hst' : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂ := fun ω hω => ha ▸ hst a ω hω
    have hlat' : IsLat g.abelian₂ := hlat
    have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
      have := hlat'.differentiable
      unfold U1
      fun_prop, huse x hx⟩
    have hint := int_mulBy_of_closure g hok
      (GlobalTheory.TwoAdicFirst.fst_mem_closure_natCast D g.lam _ (subset_closure ⟨a, rfl⟩))
    simp only [GL3Theta.tauK, ha] at hint
    exact (int_th hok hlat' hdisc h2 h3 (fun t h h' => (hwp t h h').1) halg hnm ht0.1 hβ hn hst' htrc hN
      hb1 hb2 hint).2
  · exact GlobalTheory.TorsionAbscissa.norm_xAt_le D p cc δ g hg' t0 ⟨hnm, 2, two_pos,
      (Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hp), by exact_mod_cast ht0.1⟩

theorem pull_back_split : ∀ (D : D7), Inp D → ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D g.abelian₂ t0 → ∀ (y : ℂ) (N : ℕ), 0 < N → (N : ℂ) * y ∈ g.abelian₂ → p ∣ N → SplitIn D p → ∃ h : PowerSeries ℂ_[p], (∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) ∧ g.atU (fun z => U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0) ((N : ℂ) * z)) = h * g.atU (fun z => GL3Theta.th0 g.abelian₂ t0 ((N : ℂ) * z)) := by
  intro D hI p _ cc δ g hg t0 ht0 y N hN hNy _ hsp
  have hθ := intSer_iff.1 ((GlobalTheory.ThetaParam.theta_param_integral D hI p cc δ g hg t0 ht0).2 hsp).1
  have hx0 := norm_padicWeierstrassModelAbscissa_twoTorsion_le_one D p cc δ g hg t0 ht0
  have hht := GlobalTheory.T.torsionPoint_localHeight_eq_one D p cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  have ht0n : t0 ∉ g.abelian₂ := GlobalTheory.PositiveMeans.not_mem_lattice_of_isCMTorsionBasePoint ht0 hst
  have ht2 : ((2 : ℕ) : ℂ) * t0 ∈ g.abelian₂ := by exact_mod_cast ht0.1
  have hq0 : InRationalLattice g.abelian₂ t0 := ⟨2, two_pos, ht2⟩
  have hT := GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt g.abelian₂ hlat' halg t0 ht0n ht0.1
  have hth := GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties g.abelian₂ hlat' t0 ht0n ht0.1
  have hAy : AlgEnt (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0)) := (hT y ⟨N, hN, hNy⟩).1
  have hA0 : AlgEnt (GL3Theta.th0 g.abelian₂ t0) := by
    have h0 := (hT 0 (rational_lattice_point_zero _)).1
    rwa [thetaTranslation_zero] at h0
  have hσ : AlgEnt (sgStar g.abelian₂) := by
    have h0 := halg 0 (rational_lattice_point_zero _)
    rwa [thetaTranslation_zero] at h0
  have hSR := GlobalTheory.EvenTheta.SerRing.series_ring_laws p
  have hTr := GlobalTheory.SerTransport.transport p g
  obtain ⟨hε, hw, hw0, hE, hσU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hd := fun v hv hq => GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hσ v hv (hwp v hq hv).1
  set E := ePhi1 g.lam g.abelian₂ g.C g.wq with hEdef

  have hE2 : IntSer (E ^ 2) := by
    have hf2 : g.atU (GL3Theta.th0 g.abelian₂ t0) ^ 2 = E ^ 2 * lineSer g.wq⁻¹ (xAt g t0) := by
      rw [← (atU_sq g hA0).2, ← (hd t0 ht0n hq0).2]
      exact congrArg _ (funext hth.2.2.2.1)
    have h0 : PowerSeries.constantCoeff (lineSer g.wq⁻¹ (xAt g t0)) = 1 := by
      simp only [lineSer, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, hw0]; simp
    have := hθ.sq.mul (((int_line hw).2 hx0).inv (by rw [h0, norm_one]))
    rwa [hf2, mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [h0]; exact one_ne_zero), mul_one] at this

  obtain ⟨h, hh, hh0, -, htr⟩ := hTr.2.2.2 hok (N : ℂ) (natCast_mem _ N)
  obtain ⟨m, hm, hm0, -, hmr⟩ := hTr.2.2.2 hok (-1 : ℂ) (neg_mem (one_mem _))
  have hhint : IntSer h := by
    refine intSer_iff.1 (hh ▸ int_mulBy_of_closure g hok (subset_closure ⟨N, ?_⟩))
    rw [lamC_coe _ (natCast_mem _ N)]
    exact (map_natCast g.lam N).symm
  have hmint : IntSer m := intSer_iff.1 (hm ▸ int_mulBy_of_closure g hok (by
    rw [lamC_neg_one]; exact neg_one_mem_closure))
  obtain ⟨hF, -⟩ := htr _ hAy
  obtain ⟨hTa, hTe⟩ := htr _ hA0
  set A := U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0) with hA
  set T := g.atU (fun z => GL3Theta.th0 g.abelian₂ t0 ((N : ℂ) * z)) with hTdef
  have hTint : IntSer T := by rw [hTe]; exact hSR.2.2.2.2.2.1 _ h 1 hθ hhint hh0
  have hT0 : PowerSeries.constantCoeff T = 1 := by
    rw [hTdef, (hTr.2.2.1 _ hTa).2, mul_zero, hth.2.1, lamC_one]
  have hTi : T⁻¹ * T = 1 := PowerSeries.inv_mul_cancel _ (by rw [hT0]; exact one_ne_zero)
  have hTinv := hTint.inv (by rw [hT0, norm_one])
  set F := g.atU (fun z => A ((N : ℂ) * z)) with hFdef
  suffices hFint : IntSer F from ⟨F * T⁻¹, hFint.mul hTinv, by rw [mul_assoc, hTi, mul_one]⟩

  have hFb : BddSer F := by
    obtain ⟨h1, h2'⟩ := atU_mul g hF hTa
    obtain ⟨B, hB, hBe⟩ := GlobalTheory.T.thetaOrder_parameterSeries_bounded p g hok hlat' h2 h3 hdisc hσ t0 ht0n (hwp t0 hq0 ht0n).1 (2 * N ^ 2) _ h1
      (GlobalTheory.T.thetaTranslateProduct_sigmaStarPow_lattice_law g.abelian₂ hlat' t0 ht0.1 y N hNy)
    rw [h2', pow_mul] at hBe
    have := ((IntSer.pow hE2 (N ^ 2)).bdd.mul hB).mul hTinv.bdd
    rwa [← hBe, mul_assoc, mul_comm T, hTi, mul_one] at this

  have hAm := (hmr _ hAy).1
  have hG2 : IntSer (g.atU (fun w => A w * A (-1 * w))) := by
    set c := U1 g.abelian₂ t0 (sgStar g.abelian₂) 0 with hc
    have hcQ : c ∈ Qbar := (hTr.2.2.1 _ (halg t0 hq0)).1
    have hcn : ‖lamC g.lam c‖ = 1 := by
      have := hht t0 hq0 ht0n
      rw [max_eq_left hx0, mul_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
    have hr := GlobalTheory.ThetaParam.cocy_root ⟨t0, (hlat'.sg_eq_zero t0).not.2 ht0n⟩
      (fun ω hω => hlat'.sg_law hω) hNy ht2
    have hm' : 0 < N * 2 * 2 := by positivity
    set κ := c⁻¹ * GlobalTheory.ThetaParam.cocy g.abelian₂ y t0 with hκ
    have hκQ : κ ∈ Qbar := mul_mem (inv_mem hcQ) (GlobalTheory.ThetaParam.root_mem hm' hr)
    have hκn : ‖lamC g.lam κ‖ = 1 := by
      rw [hκ, lamC_mul _ (inv_mem hcQ) (GlobalTheory.ThetaParam.root_mem hm' hr), norm_mul,
        GlobalTheory.ThetaParam.norm_lamC_inv _ hcQ hcn, GlobalTheory.ThetaParam.norm_lamC_root _ hm' hr, one_mul]
    have hU : ∀ z, A z = κ * U1 g.abelian₂ (y + t0) (sgStar g.abelian₂) z := by
      intro z
      have hth' : GL3Theta.th0 g.abelian₂ t0 = fun z => c⁻¹ * U1 g.abelian₂ t0 (sgStar g.abelian₂) z := by
        funext z
        rw [GL3Theta.th0, div_eq_inv_mul]
      rw [hA, hth', GlobalTheory.ThetaParam.thetaTranslation_const_mul]
      beta_reduce
      rw [GlobalTheory.ThetaParam.thetaTranslation_comp_eq_cocycle_mul, hκ, mul_assoc]
    have hqv : InRationalLattice g.abelian₂ (y + t0) := by
      refine ⟨N * 2, by positivity, ?_⟩
      have := add_mem (nsmul_mem hNy 2) (nsmul_mem ht2 N)
      convert this using 1
      simp only [nsmul_eq_mul]
      push_cast
      ring
    by_cases hv : y + t0 ∈ g.abelian₂
    · have e : (fun w => A w * A (-1 * w)) = fun w => ((-1) * (κ * κ)) * sgStar g.abelian₂ w ^ 2 := by
        funext w
        rw [hU, hU, hlat'.sg_law hv, hlat'.sg_law hv, neg_one_mul, hlat'.sg_neg]
        split_ifs <;> ring
      have hq := mul_mem (neg_mem (one_mem Qbar)) (mul_mem hκQ hκQ)
      rw [e, (atU_smul g hq (atU_sq g hσ).1).2, (atU_sq g hσ).2, hσU, mul_pow]
      refine (int_C ?_).mul (((int_C hε.le).mul int_X).sq.mul hE2)
      rw [lamC_mul _ (neg_mem (one_mem Qbar)) (mul_mem hκQ hκQ), lamC_mul _ hκQ hκQ, lamC_neg_one]
      simp [hκn]
    · set s := U1 g.abelian₂ (y + t0) (sgStar g.abelian₂) 0 with hs
      have hsQ : s ∈ Qbar := (hTr.2.2.1 _ (halg _ hqv)).1
      have e : (fun w => A w * A (-1 * w)) = fun w => ((κ * s) * (κ * s)) * sqTh g.abelian₂ (y + t0) w := by
        funext w
        have e1 := hlat'.sqTh_mul hv w
        have e2 := translate_sigma_star_neg hlat' (y + t0) 0
        rw [neg_zero] at e2
        rw [hU, hU, neg_one_mul, translate_sigma_star_neg hlat']
        linear_combination κ ^ 2 * e1 - κ ^ 2 * s * sqTh g.abelian₂ (y + t0) w * e2
      have hq := mul_mem hκQ hsQ
      have hh1 := hht _ hqv hv
      have hn : ‖lamC g.lam ((κ * s) * (κ * s))‖ = ‖GlobalTheory.ThetaTransl.cval g (y + t0)‖ ^ 2 := by
        rw [lamC_mul _ hq hq, lamC_mul _ hκQ hsQ, norm_mul, norm_mul, hκn, one_mul, _root_.sq]; rfl
      rw [e, (atU_smul g (mul_mem hq hq) (hd _ hv hqv).1).2, (hd _ hv hqv).2, mul_left_comm, lineSer, mul_sub,
        ← mul_assoc (PowerSeries.C _), ← map_mul]
      have hp := pow_nonneg (norm_nonneg (GlobalTheory.ThetaTransl.cval g (y + t0))) 2
      refine hE2.mul (((int_C ?_).mul hw).sub ((int_C ?_).mul int_X.sq))
      · rw [hn]
        nlinarith [le_max_left 1 ‖xAt g (y + t0)‖]
      · rw [norm_mul, hn]
        nlinarith [le_max_right 1 ‖xAt g (y + t0)‖]
  obtain ⟨hF', hF'e⟩ := hmr _ hF
  refine int_of_mul_reflect hFb hmint hm0 ?_ ?_
  · rw [← hF'e, ← (hmr _ hF').2, hFdef]
    congr 1
    funext z
    congr 1
    ring
  · have := hSR.2.2.2.2.2.1 _ h 1 hG2 hhint hh0
    rw [← (htr _ (atU_mul g hAy hAm).1).2] at this
    rw [← hF'e, hFdef, ← (atU_mul g hF hF').2]
    have e : (fun z : ℂ => A ((N : ℂ) * z) * A ((N : ℂ) * (-1 * z))) =
        fun z : ℂ => A ((N : ℂ) * z) * A (-1 * ((N : ℂ) * z)) := by
      funext z
      rw [mul_left_comm (N : ℂ)]
    rw [e]
    exact this

end GlobalTheory.PullBackSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTranslateThetaJetsDenominatorBound
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TorsionJets

open PowerSeries GlobalTheory.ThetaParam

variable {p : ℕ} [Fact p.Prime]

theorem lamC_natCast (lam : Qbar →+* ℂ_[p]) (n : ℕ) : lamC lam (n : ℂ) = n := by
  have h : (n : ℂ) ∈ Qbar := natCast_mem _ n
  simp only [lamC, dif_pos h]
  rw [← map_natCast lam n]; rfl

theorem iteratedDeriv_scale (G : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => G (c * z)) = fun z => c ^ n * iteratedDeriv n G (c * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext z
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ,
      smul_eq_mul, pow_succ, mul_assoc]

theorem deriv_mem_iff (G : ℂ → ℂ) (n : ℕ) : iteratedDeriv n G 0 ∈ Qbar ↔ coef1 G n ∈ Qbar := by
  have h : ((n.factorial : ℕ) : ℂ) ∈ Qbar := natCast_mem _ _
  have h0 : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  constructor
  · intro hG
    exact div_mem hG h
  · intro hG
    have := mul_mem h hG
    rwa [coef1, mul_div_cancel₀ _ h0] at this

theorem jet_atU (g : GL3Theta.G1 p) (hOk : g.Ok) (G : ℂ → ℂ) (n : ℕ) (hG : iteratedDeriv n G 0 ∈ Qbar) :
    (n.factorial : ℂ_[p]) * coeff n (subst g.ex (g.atU G) : PowerSeries ℂ_[p]) =
      ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ n * lamC g.lam (iteratedDeriv n G 0) := by
  have hex : HasSubst g.ex := HasSubst.of_constantCoeff_zero' hOk.2.2.1
  have harg := HasSubst.of_constantCoeff_zero' (constantCoeff_arg g)
  have e : (subst g.ex (g.atU G) : PowerSeries ℂ_[p]) =
      rescale ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) (GL3Theta.ser1 g.lam G) := by
    rw [GL3Theta.G1.atU, subst_comp_subst_apply harg hex, rescale_eq_subst]
    congr 1
    rw [← Algebra.smul_def, subst_smul hex, hOk.2.2.2]
  have h : ((n.factorial : ℕ) : ℂ) ∈ Qbar := natCast_mem _ _
  have h0 : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [e, coeff_rescale, GL3Theta.ser1, coeff_mk, mul_left_comm, ← lamC_natCast g.lam,
    ← lamC_mul _ h (div_mem hG h), mul_div_cancel₀ _ h0]

theorem norm_jet_atU (g : GL3Theta.G1 p) (hOk : g.Ok) (hu : ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1)
    (G : ℂ → ℂ) (n : ℕ) (hG : iteratedDeriv n G 0 ∈ Qbar) :
    ‖(n.factorial : ℂ_[p]) * coeff n (subst g.ex (g.atU G) : PowerSeries ℂ_[p])‖ =
      ‖lamC g.lam (iteratedDeriv n G 0)‖ := by
  rw [jet_atU g hOk G n hG, norm_mul, norm_pow, Units.val_inv_eq_inv_val, norm_inv, hu]
  simp

theorem norm_jet_atU_scale (g : GL3Theta.G1 p) (hOk : g.Ok) (hu : ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1)
    (G : ℂ → ℂ) (N n : ℕ) (hG : iteratedDeriv n G 0 ∈ Qbar) :
    ‖(n.factorial : ℂ_[p]) * coeff n (subst g.ex (g.atU fun z => G ((N : ℂ) * z)) : PowerSeries ℂ_[p])‖ =
      ‖(N : ℂ_[p])‖ ^ n * ‖lamC g.lam (iteratedDeriv n G 0)‖ := by
  have hN : ((N : ℂ)) ^ n ∈ Qbar := pow_mem (natCast_mem _ _) _
  have e : iteratedDeriv n (fun z => G ((N : ℂ) * z)) 0 = (N : ℂ) ^ n * iteratedDeriv n G 0 := by
    rw [iteratedDeriv_scale]; simp
  rw [norm_jet_atU g hOk hu _ n (e ▸ mul_mem hN hG), e, lamC_mul _ hN hG, ← Nat.cast_pow,
    lamC_natCast, norm_mul, Nat.cast_pow, norm_pow]

theorem expPS_logOf (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 1) : expPS (logOf F) = F := by
  have h0 : constantCoeff (logOf F) = 0 := constantCoeff_logOf hF
  have h1 : constantCoeff (-logOf F) = 0 := by simp [h0]
  have e : expPS (logOf F) * expPS (-logOf F) = 1 := by
    refine derivative.ext ?_ ?_
    · rw [Derivation.leibniz, GlobalTheory.ExpJets.derivative_expPS _ h0,
        GlobalTheory.ExpJets.derivative_expPS _ h1, map_neg, derivative_one]
      simp only [smul_eq_mul]
      ring
    · simp [constantCoeff_expPS]
  have e2 := exp_neg_log_mul F hF
  linear_combination F * e - expPS (logOf F) * e2

theorem subst_expPS {a F : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (hF : constantCoeff F = 0) :
    (subst a (expPS F) : PowerSeries ℂ_[p]) = expPS (subst a F) := by
  rw [GlobalTheory.ExpJets.expPS_eq_subst F hF,
    GlobalTheory.ExpJets.expPS_eq_subst _ (by rw [constantCoeff_subst' ha, hF]),
    subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hF) (HasSubst.of_constantCoeff_zero' ha)]

theorem deriv_translate_mem (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hCrv : Crv D cc δ) (t0 : ℂ) (hT : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (y : ℂ) (N : ℕ) (hN : 0 < N)
    (hy : (N : ℂ) * y ∈ lamOf D cc δ) (n : ℕ) :
    iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0 ∈ Qbar := by
  set L := lamOf D cc δ with hL
  obtain ⟨⟨-, hd, -, hq⟩, -⟩ :=
    GlobalTheory.OddTheta.sgStar_laws L (GlobalTheory.CurveLattice.lattice_of_curve D hI.g1 cc δ hCrv).1
  have halg : ∀ x, InRationalLattice L x → ∀ n, coef1 (U1 L x (sgStar L)) n ∈ Qbar := (hI.use1 cc δ hCrv).1
  have hne : ∃ z, sgStar L z ≠ 0 := by
    by_contra h
    push Not at h
    rw [show sgStar L = fun _ => 0 from funext h] at hd
    simp at hd
  have h2 : ((2 : ℕ) : ℂ) * t0 ∈ L := by simpa using hT.1
  set c := U1 L t0 (sgStar L) 0 with hcdef
  have hcQ : c ∈ Qbar := by
    have := halg t0 ⟨2, two_pos, h2⟩ 0
    simpa [coef1] using this
  have hth : GL3Theta.th0 L t0 = fun z => c⁻¹ * U1 L t0 (sgStar L) z := by
    funext z
    rw [GL3Theta.th0, div_eq_inv_mul]
  have hU : U1 L y (GL3Theta.th0 L t0) =
      fun z => (c⁻¹ * cocy L y t0) * U1 L (y + t0) (sgStar L) z := by
    rw [hth, thetaTranslation_const_mul]
    funext z
    rw [thetaTranslation_comp_eq_cocycle_mul, mul_assoc]
  have hr := cocy_root hne hq hy h2
  have hsum : ((N * 2 : ℕ) : ℂ) * (y + t0) ∈ L := by
    have := add_mem (nsmul_mem hy 2) (nsmul_mem h2 N)
    convert this using 1
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [hU, iteratedDeriv_const_mul_field]
  exact mul_mem (mul_mem (inv_mem hcQ) (root_mem (by positivity) hr))
    ((deriv_mem_iff _ n).2 (halg _ ⟨N * 2, by positivity, hsum⟩ n))

theorem norm_natCast_of_coprime {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have e : (N : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (N : ℚ_[p]) := (map_natCast _ _).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 h

theorem jet_translate_le : ∀ (D : D7), Inp D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (y : ℂ) (Nn : ℕ), 0 < Nn → (Nn : ℂ) * y ∈ (lamOf D cc δ) → (p ∣ Nn → SplitIn D p) → ∀ n : ℕ, iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0 ∈ Qbar ∧ ‖lamC lam (iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0)‖ ≤ (‖(Nn : ℂ_[p])‖⁻¹) ^ n * (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1) := by
  intro D hI p hp lam cc δ hCrv hcop t0 hT y N hN hy hsp n
  have halg := deriv_translate_mem D hI cc δ hCrv t0 hT y N hN hy
  have halg0 : ∀ m, iteratedDeriv m (GL3Theta.th0 (lamOf D cc δ) t0) 0 ∈ Qbar := fun m =>
    (deriv_mem_iff _ m).2 ((hI.use1 cc δ hCrv).2.1 t0 hT m)
  refine ⟨halg n, ?_⟩
  obtain ⟨g, hAt, rfl, hu⟩ := GlobalTheory.GenusOneDatum.exists_genusOne_datum D hI.model p lam cc δ hCrv hcop
  have hL : g.abelian₂ = lamOf D cc δ := hAt.2.2.2.1
  have hOk := hAt.2.2.2.2
  rw [← hL] at hT hy halg halg0 ⊢
  have hex0 : constantCoeff g.ex = 0 := hOk.2.2.1
  have hex : HasSubst g.ex := HasSubst.of_constantCoeff_zero' hex0
  have hD := (GlobalTheory.IntDLog.int_dlog p g hOk).1
  obtain ⟨hodd, hsplit⟩ := theta_param_integral D hI p cc δ g hAt t0 hT
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  have hfac : (1 : ℝ) ≤ (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1) := by
    split_ifs
    · exact Real.one_le_rpow hp1 (by positivity)
    · exact le_rfl
  by_cases hpN : p ∣ N
  · obtain ⟨h, hh, e⟩ := GlobalTheory.PullBackSplit.pull_back_split D hI p cc δ g hAt t0 hT y N hN hy hpN (hsp hpN)
    have h0 := (integral_iff _).1 (hsplit (hsp hpN)).1
    have hN1 : ‖(N : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    have hN0 : 0 < ‖(N : ℂ_[p])‖ := norm_pos_iff.2 (by exact_mod_cast hN.ne')
    have key := norm_jet_atU_scale g hOk hu _ N n (halg n)
    rw [e, subst_mul hex] at key
    have hle := GlobalTheory.ExpJets.norm_jet_mul_le (subst g.ex h)
      (subst g.ex (g.atU fun z => GL3Theta.th0 g.abelian₂ t0 ((N : ℂ) * z))) n 1 zero_le_one fun i j _ => by
        refine mul_le_one₀ (hD h hh i) (norm_nonneg _) ?_
        rw [norm_jet_atU_scale g hOk hu _ N j (halg0 j), ← norm_jet_atU g hOk hu _ j (halg0 j)]
        exact mul_le_one₀ (pow_le_one₀ hN0.le hN1) (norm_nonneg _) (hD _ h0 j)
    rw [key] at hle
    refine le_trans ?_ (le_mul_of_one_le_right (by positivity) hfac)
    rw [inv_pow, ← mul_one (_ ^ n)⁻¹, le_inv_mul_iff₀ (by positivity)]
    exact hle
  · have hc : Nat.Coprime N p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpN).symm
    rw [norm_natCast_of_coprime hpN, inv_one, one_pow, one_mul, ← norm_jet_atU g hOk hu _ n (halg n)]
    by_cases hp2 : p = 2
    · exact (hD _ ((integral_iff _).1 ((hsplit (Or.inl hp2)).2 y N hc hy)) n).trans hfac
    have hf := (integral_iff _).1 ((hodd hp2).2 y N hc hy)
    obtain ⟨⟨-, hd, -, -⟩, -⟩ :=
      GlobalTheory.OddTheta.sgStar_laws g.abelian₂ (hL ▸ (GlobalTheory.CurveLattice.lattice_of_curve D hI.g1 cc δ hCrv).1)
    have he := constantCoeff_ePhi1 g hOk.2.1 hd
    set E := ePhi1 g.lam g.abelian₂ g.C g.wq with hE
    set f := E⁻¹ * g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0)) with hfdef
    have hinv : E * E⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [he]; exact one_ne_zero)
    have hph : -g.ph = logOf E := by
      rw [GL3Theta.G1.ph, neg_neg]
      exact logMv_eq E he
    have hph0 : constantCoeff g.ph = 0 := by
      have := constantCoeff_logOf he
      rw [← hph] at this
      simpa using this
    have e : (subst g.ex (g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0))) : PowerSeries ℂ_[p]) =
        expPS (-(subst g.ex g.ph)) * subst g.ex f := by
      have e1 : (-(subst g.ex g.ph) : PowerSeries ℂ_[p]) = subst g.ex (logOf E) := by
        rw [← hph, ← coe_substAlgHom hex, map_neg]
      rw [e1, ← subst_expPS hex0 (constantCoeff_logOf he), expPS_logOf E he, ← subst_mul hex,
        hfdef, ← mul_assoc, hinv, one_mul]
    obtain ⟨j1, -, j2, j3⟩ := hI.jets p cc δ g hAt hp2
    have hmain := fun (s : ℝ) (hs : 1 ≤ s) h2 =>
      GlobalTheory.ExpJets.norm_jet_exp_neg_mul_le p (subst g.ex g.ph) s hs
        (by rw [constantCoeff_subst' hex0, hph0]) j1 h2 (subst g.ex f) (hD f hf) n
    have hj : g.jetPh 2 = 2 * coeff 2 (subst g.ex g.ph : PowerSeries ℂ_[p]) := by
      simp [GL3Theta.G1.jetPh]
    rw [e]
    split_ifs with hd'
    · have := hmain ((p : ℝ) ^ ((1 : ℝ) / 4)) (Real.one_le_rpow hp1 (by positivity)) (by
        rw [← hj, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        convert j3 hd' using 2
        norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at this
      convert this using 2
      ring
    · have := hmain 1 le_rfl (by rw [← hj, one_pow]; exact j2 hd')
      rwa [one_pow] at this

end GlobalTheory.TorsionJets
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTranslateThetaJetsDenominatorBoundStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionTranslate_theta_jets_denominator_bound : ∀ (D : D7), Inp D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (y : ℂ) (Nn : ℕ), 0 < Nn → (Nn : ℂ) * y ∈ (lamOf D cc δ) → (p ∣ Nn → SplitIn D p) → ∀ n : ℕ, iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0 ∈ Qbar ∧ ‖lamC lam (iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0)‖ ≤ (‖(Nn : ℂ_[p])‖⁻¹) ^ n * (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1) := by
  first | exact @GlobalTheory.TorsionJets.jet_translate_le | exact GlobalTheory.TorsionJets.jet_translate_le | (intros; apply GlobalTheory.TorsionJets.jet_translate_le <;> assumption)
end
