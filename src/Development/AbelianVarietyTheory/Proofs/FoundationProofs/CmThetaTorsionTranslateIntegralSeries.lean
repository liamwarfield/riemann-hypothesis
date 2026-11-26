module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateLogNormParallelogramLaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateSeriesEqConstMulIntegralOneSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneRootCoprimePadic
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneRootCoprimePadic
open scoped BigOperators

noncomputable section
namespace GlobalTheory.RootInt

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem intSer_mul {f g : PowerSeries K} (hf : GlobalTheory.EvenTheta.IntSer f) (hg : GlobalTheory.EvenTheta.IntSer g) :
    GlobalTheory.EvenTheta.IntSer (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem intSer_pow {f : PowerSeries K} (hf : GlobalTheory.EvenTheta.IntSer f) (N : ℕ) :
    GlobalTheory.EvenTheta.IntSer (f ^ N) := by
  induction N with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ N ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_of_pow {N : ℕ} (hN : ‖(N : K)‖ = 1) {s : PowerSeries K}
    (hs0 : PowerSeries.constantCoeff s = 1) (hsN : GlobalTheory.EvenTheta.IntSer (s ^ N)) :
    GlobalTheory.EvenTheta.IntSer s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0, norm_one]
  set a : PowerSeries K := PowerSeries.mk fun k => if k < n then PowerSeries.coeff k s else 0 with ha
  have hca : ∀ k, PowerSeries.coeff k a = if k < n then PowerSeries.coeff k s else 0 := fun k => by
    rw [ha, PowerSeries.coeff_mk]
  have hai : GlobalTheory.EvenTheta.IntSer a := fun k => by
    rw [hca]; split_ifs with h
    · exact ih k h
    · simp
  have hcb : ∀ k, PowerSeries.coeff k (s - a) = if k < n then 0 else PowerSeries.coeff k s := fun k => by
    rw [map_sub, hca]; split_ifs <;> simp
  set G : PowerSeries K := ∑ i ∈ Finset.range N, s ^ i * a ^ (N - 1 - i) with hG
  have hGN : G * (s - a) = s ^ N - a ^ N := geom_sum₂_mul s a N
  have ha0 : PowerSeries.constantCoeff a = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hca, if_pos hn,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0]
  have hG0 : PowerSeries.coeff 0 G = N := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hG, map_sum]
    simp [hs0, ha0]
  have key : PowerSeries.coeff n (G * (s - a)) = (N : K) * PowerSeries.coeff n s := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · rw [hG0, hcb, if_neg (lt_irrefl n)]
    · rintro ⟨i, j⟩ hij hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      have hj : j < n := by
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact absurd (by simp at hij; simp [hij]) hne
        · omega
      simp only
      rw [hcb, if_pos hj, mul_zero]
    · intro h; exact absurd (by simp) h
  have h1 : ‖(N : K) * PowerSeries.coeff n s‖ ≤ 1 := by
    rw [← key, hGN, map_sub]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hsN n) ?_)
    rw [norm_neg]; exact intSer_pow hai N n
  rwa [norm_mul, hN, one_mul] at h1

end GlobalTheory.RootInt

theorem GlobalTheory.RootInt.intSer_root : ∀ (p : ℕ) [Fact p.Prime] (N : ℕ), 0 < N → Nat.Coprime N p →
    ∀ s : PowerSeries ℂ_[p], PowerSeries.constantCoeff s = 1 →
      GlobalTheory.EvenTheta.IntSer (s ^ N) → GlobalTheory.EvenTheta.IntSer s := by
  intro p _ N _ hcop s hs0 hsN
  refine GlobalTheory.RootInt.intSer_of_pow ?_ hs0 hsN
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact hcop.symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneRootCoprimePadicStatement
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesCoeffNormLeOne_root_coprime_padic : ∀ (p : ℕ) [Fact p.Prime] (N : ℕ), 0 < N → Nat.Coprime N p →
    ∀ s : PowerSeries ℂ_[p], PowerSeries.constantCoeff s = 1 →
      GlobalTheory.EvenTheta.IntSer (s ^ N) → GlobalTheory.EvenTheta.IntSer s := by
  first | exact @GlobalTheory.RootInt.intSer_root | exact GlobalTheory.RootInt.intSer_root | (intros; apply GlobalTheory.RootInt.intSer_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateSeriesEqConstMulIntegralOneSeries
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaUnit
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

section
variable {p : ℕ} [Fact p.Prime]

theorem lamC_eq (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) : lamC lam x = lam ⟨x, hx⟩ := dif_pos hx

theorem lamC_mul' (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  rw [lamC_eq lam hx, lamC_eq lam hy, lamC_eq lam (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_ne_zero (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) (h0 : x ≠ 0) : lamC lam x ≠ 0 := by
  rw [lamC_eq lam hx]
  intro h
  apply h0
  have := (map_eq_zero_iff lam lam.injective).1 h
  exact congrArg Subtype.val this

theorem intSer_one : IntSer (1 : PowerSeries ℂ_[p]) := by
  have := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 1).2 norm_one.le
  rwa [map_one] at this

theorem intSer_pow {f : PowerSeries ℂ_[p]} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => simpa using intSer_one (p := p)
  | succ n ih => rw [pow_succ]; exact ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ ih hf).2.2

end

theorem tors_neg' {p : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 p Λ t) : GL3Theta.Tors1 p Λ (-t) := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  exact ⟨by simpa using h0, n, hn, hc, by simpa using h⟩

theorem laQ_of_tors {p : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 p Λ t) : InRationalLattice Λ t :=
  let ⟨_, n, hn, _, h⟩ := h; ⟨n, hn, h⟩

theorem thetaTranslateOperator_zero_eq_self (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

theorem thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice {Λ : AddSubgroup ℂ} (hlat : IsLat Λ) {t : ℂ} (ht : t ∉ Λ) :
    U1 Λ t (sgStar Λ) 0 ≠ 0 := by
  simp only [U1, zero_add]
  exact mul_ne_zero ((hlat.sg_eq_zero t).not.2 ht) (Complex.exp_ne_zero _)

theorem atU_smul' {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) {c : ℂ} (hc : c ∈ Qbar) {F : ℂ → ℂ} (hF : AlgEnt F) :
    AlgEnt (fun z => c * F z) ∧ g.atU (fun z => c * F z) = PowerSeries.C (lamC g.lam c) * g.atU F := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 c hc
  rw [← h2]
  exact ((GlobalTheory.SerTransport.transport p g).1 _ _ h1 hF).1

theorem tau_eq_C_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g t = PowerSeries.C (GlobalTheory.ThetaTransl.cval g t) * w := by
  intro D p _ cc δ g hg hx t ht
  have hA := GlobalTheory.T.thetaTranslatePowerSeries_pow_boundedCoeffs_of_torsion D p cc δ g hg
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
  obtain ⟨-, hw, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hsg : AlgEnt (sgStar g.abelian₂) := by
    have := halg 0 ⟨1, one_pos, by simp⟩
    rwa [thetaTranslateOperator_zero_eq_self] at this
  have hEi : (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hE]; exact one_ne_zero)
  have hcon : ∀ s, InRationalLattice g.abelian₂ s → PowerSeries.constantCoeff (tau g s) = cval g s ∧
      U1 g.abelian₂ s (sgStar g.abelian₂) 0 ∈ Qbar := by
    intro s hs
    obtain ⟨c, d⟩ := (GlobalTheory.SerTransport.transport p g).2.2.1 _ (halg s hs)
    refine ⟨?_, c⟩
    rw [tau, map_mul, PowerSeries.constantCoeff_inv, hE, inv_one, one_mul, d, cval]
  have hq := laQ_of_tors ht
  have hq' := laQ_of_tors (tors_neg' ht)
  obtain ⟨c1, c2⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t ht.1 (hwp t hq ht.1).1
  have a3 := (hcon t hq).2
  have b3 := (hcon (-t) hq').2
  have e := (atU_smul' g (mul_mem a3 b3) c1).2
  rw [funext (hlat'.sqTh_mul ht.1), ((GlobalTheory.SerTransport.transport p g).1 _ _ (halg _ hq) (halg _ hq')).1.2,
    c2, lamC_mul' _ a3 b3] at e
  have hprod : tau g t * tau g (-t) = PowerSeries.C (cval g t * cval g (-t)) *
      lineSer g.wq⁻¹ (xAt g t) := by
    simp only [tau, cval]
    linear_combination ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹) * e +
      PowerSeries.C (lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0) * lamC g.lam (U1 g.abelian₂ (-t) (sgStar g.abelian₂) 0)) *
        lineSer g.wq⁻¹ (xAt g t) * ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq + 1) * hEi

  have hL : IntSer (lineSer g.wq⁻¹ (xAt g t)) := by
    have h1 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 (xAt g t)).2 (hx t ht)
    have h2 := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1
    have h3 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ h2 h2).2.2
    have h4 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ h1 h3).2.2
    have h5 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ hw h4).2.1
    simpa [lineSer, _root_.sq, mul_assoc] using h5
  obtain ⟨n, hn, hcop, hnt⟩ := ht.2
  have hnt' : (n : ℂ) * (-t) ∈ g.abelian₂ := by rw [mul_neg]; exact neg_mem hnt
  have B1 := hA t ht n hn hnt
  have B2 := hA (-t) (tors_neg' ht) n hn hnt'
  set c := cval g t with hc
  set c' := cval g (-t) with hc'
  have hc0 : c ≠ 0 := lamC_ne_zero _ a3 (thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice hlat' ht.1)
  have hc0' : c' ≠ 0 := lamC_ne_zero _ b3 (thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice hlat' (tors_neg' ht).1)
  have hpow : tau g t ^ n * tau g (-t) ^ n = PowerSeries.C ((c * c') ^ n) * lineSer g.wq⁻¹ (xAt g t) ^ n := by
    rw [← mul_pow, hprod, mul_pow, map_pow]
  have hbound : ∀ k, ‖PowerSeries.coeff k (tau g t ^ n * tau g (-t) ^ n)‖ ≤ ‖c * c'‖ ^ n := by
    intro k
    rw [hpow, PowerSeries.coeff_C_mul, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (intSer_pow hL n k)
  have G := GlobalTheory.EvenTheta.sup_norm_mul_padicComplex p _ _ _ B1 B2 hbound
  have h0' : PowerSeries.coeff 0 (tau g (-t) ^ n) = c' ^ n := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, (hcon _ hq').1]
  have hcn : 0 < ‖c'‖ ^ n := pow_pos (norm_pos_iff.2 hc0') n
  have hle : ∀ i, ‖PowerSeries.coeff i (tau g t ^ n)‖ ≤ ‖c‖ ^ n := by
    intro i
    have := G i 0
    rw [h0', norm_pow, norm_mul, mul_pow] at this
    exact le_of_mul_le_mul_right this hcn
  set s := PowerSeries.C c⁻¹ * tau g t with hs
  have hsn : IntSer (s ^ n) := by
    intro k
    rw [hs, mul_pow, ← map_pow, PowerSeries.coeff_C_mul, norm_mul, norm_pow, norm_inv]
    have hcp : 0 < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc0) n
    calc ‖c‖⁻¹ ^ n * ‖PowerSeries.coeff k (tau g t ^ n)‖ ≤ ‖c‖⁻¹ ^ n * ‖c‖ ^ n :=
          mul_le_mul_of_nonneg_left (hle k) (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (norm_ne_zero_iff.2 hc0), one_pow]
  have hs0 : PowerSeries.constantCoeff s = 1 := by
    rw [hs, map_mul, PowerSeries.constantCoeff_C, (hcon t hq).1, inv_mul_cancel₀ hc0]
  refine ⟨s, GlobalTheory.T.powerSeriesCoeffNormLeOne_root_coprime_padic p n hn hcop s hs0 hsn, hs0, ?_⟩
  rw [hs, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

end GlobalTheory.ThetaUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateSeriesEqConstMulIntegralOneSeriesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslateSeries_eq_const_mul_integral_one_series : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g t = PowerSeries.C (GlobalTheory.ThetaTransl.cval g t) * w := by
  first | exact @GlobalTheory.ThetaUnit.tau_eq_C_mul | exact GlobalTheory.ThetaUnit.tau_eq_C_mul | (intros; apply GlobalTheory.ThetaUnit.tau_eq_C_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionParallelogramLawPeriodicVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionParallelogramLawPeriodicVanish
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem GlobalTheory.torsion_parallelogram_vanish : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ (N : ℕ), 0 < N → ∀ M : ℂ → ℝ,
    (∀ t ∈ Λ, M t = 0) → (∀ t ω : ℂ, (N : ℂ) * t ∈ Λ → ω ∈ Λ → M (t + ω) = M t) →
    (∀ P Q : ℂ, (N : ℂ) * P ∈ Λ → (N : ℂ) * Q ∈ Λ → Q ∉ Λ → M (P + Q) + M (P - Q) = 2 * M P + 2 * M Q) →
    ∀ t : ℂ, (N : ℂ) * t ∈ Λ → M t = 0 := by
  intro Λ _ N hN M h0 _ hlaw t ht
  by_cases hQ : t ∈ Λ
  · exact h0 t hQ
  have key : ∀ k : ℕ, M ((k:ℂ) * t) = (k:ℝ)^2 * M t ∧
      M (((k:ℂ)+1) * t) = ((k:ℝ)+1)^2 * M t := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [h0 0 (zero_mem Λ)]
      · simp
    | succ k ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have hmem : (N:ℂ) * (((k:ℂ)+1) * t) ∈ Λ := by
        have e : (N:ℂ) * (((k:ℂ)+1) * t) = (k+1 : ℕ) • ((N:ℂ) * t) := by
          rw [nsmul_eq_mul]; push_cast; ring
        rw [e]; exact AddSubgroup.nsmul_mem Λ ht _
      have h := hlaw (((k:ℂ)+1) * t) t hmem ht hQ
      have e1 : ((k:ℂ)+1) * t + t = ((k:ℂ)+1+1) * t := by ring
      have e2 : ((k:ℂ)+1) * t - t = (k:ℂ) * t := by ring
      rw [e1, e2, ih.1, ih.2] at h
      push_cast
      linear_combination h
  have h1 := (key N).1
  rw [h0 _ ht] at h1
  have hN' : (N:ℝ)^2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp h1.symm).resolve_left hN'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionParallelogramLawPeriodicVanishStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_parallelogramLaw_periodic_vanish : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ (N : ℕ), 0 < N → ∀ M : ℂ → ℝ,
    (∀ t ∈ Λ, M t = 0) → (∀ t ω : ℂ, (N : ℂ) * t ∈ Λ → ω ∈ Λ → M (t + ω) = M t) →
    (∀ P Q : ℂ, (N : ℂ) * P ∈ Λ → (N : ℂ) * Q ∈ Λ → Q ∉ Λ → M (P + Q) + M (P - Q) = 2 * M P + 2 * M Q) →
    ∀ t : ℂ, (N : ℂ) * t ∈ Λ → M t = 0 := by
  first | exact @GlobalTheory.torsion_parallelogram_vanish | exact GlobalTheory.torsion_parallelogram_vanish | (intros; apply GlobalTheory.torsion_parallelogram_vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeries
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTransl

theorem intMv_iff {p : ℕ} [Fact p.Prime] (f : PowerSeries ℂ_[p]) : IntegralMv f ↔ GlobalTheory.EvenTheta.IntSer f := by
  constructor
  · intro h n; exact h (Finsupp.single () n)
  · intro h n
    have := h (n ())
    rwa [PowerSeries.coeff_def (s := n) rfl] at this

theorem transl_holds : ∀ D : D7, GL3Theta.transl D := by
  intro D p _ cc δ g hg t ht
  have hg' := hg
  obtain ⟨hcc, -, hδ, hΛ, -⟩ := hg'
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, -, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  rw [← hΛ] at hlat huse
  have hlat' : GlobalTheory.EvenTheta.IsLat g.abelian₂ := hlat
  have hred := GlobalTheory.T.torsionPoint_padicAbscissa_norm_le_one D p cc δ g hg
  have hun := GlobalTheory.T.thetaTranslateSeries_eq_const_mul_integral_one_series D p cc δ g hg hred
  obtain ⟨n, hn, hnp, hnt⟩ := ht.2
  have hM : logc g t = 0 := by
    refine GlobalTheory.T.torsion_parallelogramLaw_periodic_vanish g.abelian₂ hlat' n hn (logc g) (fun s hs => by simp [logc, hs]) ?_ ?_ t hnt
    · intro s ω hs hω
      by_cases h1 : s ∈ g.abelian₂
      · simp [logc, h1, add_mem h1 hω]
      · have h2 : s + ω ∉ g.abelian₂ := fun h => h1 (by simpa using sub_mem h hω)
        simp only [logc, h1, h2, if_false]
        rw [GlobalTheory.T.norm_thetaTranslateValueAtZeroPadic_periodic D p cc δ g hg s ω ⟨n, hn, hs⟩ hω]
    · intro P Q hP hQ hQ'
      exact GlobalTheory.T.thetaTranslateLogNorm_parallelogram_law D p cc δ g hg hred hun P Q ⟨n, hn, hnp, hP⟩ ⟨hQ', n, hn, hnp, hQ⟩
  have hA : GlobalTheory.EvenTheta.AlgEnt (U1 g.abelian₂ t (sgStar g.abelian₂)) := ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse t ⟨n, hn, hnt⟩⟩
  obtain ⟨hq, hc0⟩ := (GlobalTheory.SerTransport.transport p g).2.2.1 _ hA
  have hne : U1 g.abelian₂ t (sgStar g.abelian₂) 0 ≠ 0 := by
    simp only [U1, zero_add, ne_eq, mul_eq_zero, Complex.exp_ne_zero, or_false]
    exact fun h => ht.1 ((hlat'.sg_eq_zero t).1 h)
  have hcne : cval g t ≠ 0 := by
    unfold cval lamC
    rw [dite_eq_left hq]
    exact (map_ne_zero g.lam).2 fun h => hne (congrArg Subtype.val h)
  have hc1 : ‖cval g t‖ = 1 := by
    simp only [logc, ht.1, if_false] at hM
    rcases Real.log_eq_zero.1 hM with h | h | h
    · exact absurd (norm_eq_zero.1 h) hcne
    · exact h
    · linarith [norm_nonneg (cval g t)]
  obtain ⟨w, hw, -, hτ⟩ := hun t ht
  refine ⟨?_, ?_⟩
  · rw [intMv_iff]
    change GlobalTheory.EvenTheta.IntSer (tau g t)
    intro k
    rw [hτ, PowerSeries.coeff_C_mul, norm_mul, hc1, one_mul]
    exact hw k
  · rw [hc0]; exact hc1

end GlobalTheory.ThetaTransl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeriesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_theta_torsion_translate_integral_series : ∀ D : D7, GL3Theta.transl D := by
  first | exact @GlobalTheory.ThetaTransl.transl_holds | exact GlobalTheory.ThetaTransl.transl_holds | (intros; apply GlobalTheory.ThetaTransl.transl_holds <;> assumption)
end
