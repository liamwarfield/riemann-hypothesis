module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FstMemClosureNatCast
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEntireOfLocallyDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecomposition
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

open Filter
open scoped Topology

noncomputable section

namespace GlobalTheory.ThetaTranslDecomp

variable {Λ : AddSubgroup ℂ}

private lemma u1_apply_eq_mul_u1_one (ω : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω G z = G (z + ω) * U1 Λ ω (fun _ => (1 : ℂ)) z := by
  simp only [U1, one_mul]

private lemma u1_one_ne_zero (ω z : ℂ) : U1 Λ ω (fun _ => (1 : ℂ)) z ≠ 0 := by
  simp only [U1, one_mul]
  exact Complex.exp_ne_zero _

private lemma u1_one_add_mul_comm_cexp (a b z : ℂ) :
    U1 Λ a (fun _ => (1 : ℂ)) (z + b) * U1 Λ b (fun _ => (1 : ℂ)) z =
      U1 Λ a (fun _ => (1 : ℂ)) z * U1 Λ b (fun _ => (1 : ℂ)) (z + a) *
        Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ)) := by
  simp only [U1, one_mul, ← Complex.exp_add]
  congr 1
  ring

private lemma u1_one_add_mul_eq_u1_one_add_mul_cexp (a b z : ℂ) :
    U1 Λ a (fun _ => (1 : ℂ)) (z + b) * U1 Λ b (fun _ => (1 : ℂ)) z =
      U1 Λ (a + b) (fun _ => (1 : ℂ)) z *
        Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) := by
  simp only [U1, one_mul, ← Complex.exp_add, map_add (f := _)]
  congr 1
  ring

private lemma cexp_pi_mul_conj_sub_div_area_eq_one_of_mem (hΛ : IsLat Λ) {a b : ℂ} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ)) = 1 := by
  obtain ⟨z0, hz0⟩ := hΛ.dense_compl.nonempty
  have hs0 : sgStar Λ z0 ≠ 0 := fun h0 => hz0 ((hΛ.sg_eq_zero z0).1 h0)
  have hsq : ∀ c : ℂ, (if c / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 = 1 := by
    intro c
    split_ifs <;> norm_num
  have l1 := hΛ.sg_law (add_mem ha hb) z0
  have l2 := hΛ.sg_law ha (z0 + b)
  have l3 := hΛ.sg_law hb z0
  rw [u1_apply_eq_mul_u1_one] at l1 l2 l3
  have key : (if (a + b) / 2 ∈ Λ then (1 : ℂ) else -1) *
      Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) =
      (if a / 2 ∈ Λ then (1 : ℂ) else -1) * (if b / 2 ∈ Λ then (1 : ℂ) else -1) := by
    apply mul_right_cancel₀ hs0
    calc _ = sgStar Λ (z0 + (a + b)) * U1 Λ (a + b) (fun _ => (1 : ℂ)) z0 *
          Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) := by
          rw [l1]; ring
      _ = sgStar Λ (z0 + b + a) * (U1 Λ a (fun _ => (1 : ℂ)) (z0 + b) * U1 Λ b (fun _ => (1 : ℂ)) z0) := by
          rw [u1_one_add_mul_eq_u1_one_add_mul_cexp, show z0 + b + a = z0 + (a + b) by ring]; ring
      _ = _ := by rw [← mul_assoc, l2, mul_assoc, l3]; ring
  have h2 : Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) /
      (2 * (area Λ : ℂ))) ^ 2 = 1 := by
    have := congrArg (· ^ 2) key
    simp only [mul_pow, hsq, one_mul] at this
    exact this
  rw [show (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ) =
      (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ)) +
      (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ)) by ring,
    Complex.exp_add, ← sq, h2]

theorem ratio_pow_add (hΛ : IsLat Λ) {t : ℂ} {N : ℕ} (hN : 0 < N) (ht : (N : ℂ) * t ∈ Λ)
    (z : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    (U1 Λ t (sgStar Λ) (z + l) / sgStar Λ (z + l)) ^ N = (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N := by
  by_cases hz : z ∈ Λ
  · have h1 : sgStar Λ z = 0 := (hΛ.sg_eq_zero z).2 hz
    have h2 : sgStar Λ (z + l) = 0 := (hΛ.sg_eq_zero _).2 (add_mem hz hl)
    rw [h1, h2, div_zero, div_zero]
  · have hs : sgStar Λ z ≠ 0 := fun h0 => hz ((hΛ.sg_eq_zero z).1 h0)
    have hzl : z + l ∉ Λ := fun h' => hz (by simpa using sub_mem h' hl)
    have hsl : sgStar Λ (z + l) ≠ 0 := fun h0 => hzl ((hΛ.sg_eq_zero _).1 h0)
    have hsn : (if l / 2 ∈ Λ then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
    have la := hΛ.sg_law hl (z + t)
    have lb := hΛ.sg_law hl z
    rw [u1_apply_eq_mul_u1_one] at la lb
    have hK := u1_one_add_mul_comm_cexp (Λ := Λ) t l z
    have e3 := u1_one_ne_zero (Λ := Λ) l z
    have e4 := u1_one_ne_zero (Λ := Λ) l (z + t)
    have hA : sgStar Λ (z + l + t) = (if l / 2 ∈ Λ then (1 : ℂ) else -1) * sgStar Λ (z + t) /
        U1 Λ l (fun _ => (1 : ℂ)) (z + t) := by
      rw [eq_div_iff e4, show z + l + t = z + t + l by ring]
      exact la
    have hB : sgStar Λ (z + l) = (if l / 2 ∈ Λ then (1 : ℂ) else -1) * sgStar Λ z /
        U1 Λ l (fun _ => (1 : ℂ)) z := by
      rw [eq_div_iff e3]
      exact lb
    have hF : U1 Λ t (fun _ => (1 : ℂ)) (z + l) = U1 Λ t (fun _ => (1 : ℂ)) z *
        U1 Λ l (fun _ => (1 : ℂ)) (z + t) *
        Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) /
        U1 Λ l (fun _ => (1 : ℂ)) z := by
      rw [eq_div_iff e3]
      exact hK
    have hbase : U1 Λ t (sgStar Λ) (z + l) / sgStar Λ (z + l) = U1 Λ t (sgStar Λ) z / sgStar Λ z *
        Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) := by
      rw [u1_apply_eq_mul_u1_one, u1_apply_eq_mul_u1_one t (sgStar Λ) z, hA, hF, hB]
      field_simp
    rw [hbase, mul_pow, ← Complex.exp_nat_mul,
      show (N : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) =
        (Real.pi : ℂ) * ((N : ℂ) * t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) ((N : ℂ) * t)) / (area Λ : ℂ) by
        rw [map_mul, map_natCast]; ring,
      cexp_pi_mul_conj_sub_div_area_eq_one_of_mem hΛ ht hl, mul_one]

theorem sqThD_eq (hΛ : IsLat Λ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {v z : ℂ}
    (hv : v ∉ Λ) (hz : z ∉ Λ) : sqThD Λ v z = sgStar Λ z ^ 3 * L.derivWeierstrassP z := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hzL : z ∉ L.lattice := fun hz' => hz ((h z).2 hz')
  have hev : sqTh Λ v =ᶠ[𝓝 z] fun w => sgStar Λ w ^ 2 * (L.weierstrassP w - L.weierstrassP v) := by
    filter_upwards [hU.mem_nhds hzL] with w hw
    have hwΛ : w ∉ Λ := fun h' => hw ((h w).1 h')
    rw [hΛ.sqTh_eq hv hwΛ, GlobalTheory.OddTheta.wpF_eq L Λ h, GlobalTheory.OddTheta.wpF_eq L Λ h]
  have hsg : HasDerivAt (sgStar Λ) (deriv (sgStar Λ) z) z := (hΛ.differentiable z).hasDerivAt
  have hwp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    have hd : DifferentiableAt ℂ L.weierstrassP z :=
      (L.analyticOnNhd_weierstrassP z hzL).differentiableAt
    have := hd.hasDerivAt
    rwa [L.deriv_weierstrassP] at this
  have hD : HasDerivAt (fun w => sgStar Λ w ^ 2 * (L.weierstrassP w - L.weierstrassP v)) _ z :=
    (hsg.pow 2).mul (hwp.sub_const (L.weierstrassP v))
  unfold sqThD
  rw [hev.deriv_eq, hD.deriv, hΛ.sqTh_eq hv hz,
    GlobalTheory.OddTheta.wpF_eq L Λ h, GlobalTheory.OddTheta.wpF_eq L Λ h]
  norm_num
  ring

theorem exists_decomp : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (t : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ Λ →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), N ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  intro Λ hΛ t N hN ht v hv
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hσ : Differentiable ℂ (sgStar Λ) := hΛ.differentiable
  have hσ0 : ∀ w, sgStar Λ w = 0 ↔ w ∈ Λ := hΛ.sg_eq_zero
  have hU : Differentiable ℂ (U1 Λ t (sgStar Λ)) := by
    unfold U1
    fun_prop
  have hmer : Meromorphic (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) := fun x =>
    ((hU.analyticAt x).meromorphicAt.div (hσ.analyticAt x).meromorphicAt).pow N
  have hcont : ∀ a, a ∉ Λ → ContinuousAt (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) a :=
    fun a ha => ((hU a).continuousAt.div (hσ a).continuousAt (fun h0 => ha ((hσ0 a).1 h0))).pow N
  have hd : ∀ a ∉ L.lattice, ∃ c, Tendsto (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) (𝓝[≠] a) (𝓝 c) :=
    fun a ha => ⟨_, (hcont a (fun h' => ha ((hL a).1 h'))).tendsto.mono_left nhdsWithin_le_nhds⟩
  have hp : ∀ z, ∀ l ∈ L.lattice, (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) (z + l) =
      (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) z :=
    fun z l hl => ratio_pow_add hΛ hN ht z ((hL l).2 hl)
  obtain ⟨A, B, hAB⟩ := GlobalTheory.EllipticPoles.no_pole_case L hmer hd hp
  have hpt : ∀ z, z ∉ Λ → (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N =
      A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    intro z hzΛ
    have hz : z ∉ L.lattice := fun h' => hzΛ ((hL z).2 h')
    have t1 := (hcont z hzΛ).tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    have hc2 : ContinuousAt (fun w => A.eval (L.weierstrassP w) + B.eval (L.weierstrassP w) * L.derivWeierstrassP w) z :=
      (A.continuous.continuousAt.comp (L.analyticOnNhd_weierstrassP z hz).continuousAt).add
        ((B.continuous.continuousAt.comp (L.analyticOnNhd_weierstrassP z hz).continuousAt).mul
          (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt)
    exact tendsto_nhds_unique (t1.congr' (hAB z)) (hc2.tendsto.mono_left nhdsWithin_le_nhds)
  have hS : Differentiable ℂ (sqTh Λ v) := hΛ.differentiable_sqTh v
  have hdS : Continuous (deriv (sqTh Λ v)) := (hS.contDiff (n := 1)).continuous_deriv le_rfl
  have hdσ : Continuous (deriv (sgStar Λ)) := (hσ.contDiff (n := 1)).continuous_deriv le_rfl
  have hT : Continuous (sqThD Λ v) := by
    unfold sqThD
    exact (hσ.continuous.mul hdS).sub ((continuous_const.mul hdσ).mul hS.continuous)
  set P := A.comp (Polynomial.X + Polynomial.C (L.weierstrassP v)) with hP
  set Q := B.comp (Polynomial.X + Polynomial.C (L.weierstrassP v)) with hQ
  refine ⟨max (max P.natDegree Q.natDegree) N, fun i => P.coeff i, fun j => Q.coeff j, ?_, ?_⟩
  · have := le_max_right (max P.natDegree Q.natDegree) N
    omega
  have hIP : P.natDegree < max (max P.natDegree Q.natDegree) N + 1 := by
    have := le_max_left (max P.natDegree Q.natDegree) N
    have := le_max_left P.natDegree Q.natDegree
    omega
  have hIQ : Q.natDegree < max (max P.natDegree Q.natDegree) N + 1 := by
    have := le_max_left (max P.natDegree Q.natDegree) N
    have := le_max_right P.natDegree Q.natDegree
    omega
  have hNI : N ≤ 2 * max (max P.natDegree Q.natDegree) N + 3 := by
    have := le_max_right (max P.natDegree Q.natDegree) N
    omega
  generalize max (max P.natDegree Q.natDegree) N = I at hIP hIQ hNI ⊢
  have heq : (fun z => sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N) =
      fun z => ∑ i ∈ Finset.range (I + 1), P.coeff i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), Q.coeff j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
    refine Continuous.ext_on hΛ.dense_compl ((hσ.continuous.pow _).mul (hU.continuous.pow _))
      ((continuous_finsetSum _ fun i _ => continuous_const.mul ((hσ.continuous.pow _).mul (hS.continuous.pow _))).add
        (continuous_finsetSum _ fun j _ =>
          continuous_const.mul (((hσ.continuous.pow _).mul (hS.continuous.pow _)).mul hT))) ?_
    intro z hz
    have hzΛ : z ∉ Λ := hz
    have hs : sgStar Λ z ≠ 0 := fun h0 => hzΛ ((hσ0 z).1 h0)
    have hz' : z ∉ L.lattice := fun h' => hzΛ ((hL z).2 h')
    have hq := hpt z hzΛ
    have hApt : A.eval (L.weierstrassP z) = P.eval (L.weierstrassP z - L.weierstrassP v) := by
      rw [hP, Polynomial.eval_comp]; simp
    have hBpt : B.eval (L.weierstrassP z) = Q.eval (L.weierstrassP z - L.weierstrassP v) := by
      rw [hQ, Polynomial.eval_comp]; simp
    rw [hApt, hBpt, Polynomial.eval_eq_sum_range' hIP, Polynomial.eval_eq_sum_range' hIQ] at hq
    have hUN : U1 Λ t (sgStar Λ) z ^ N = sgStar Λ z ^ N * (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hs)]
    simp only
    rw [hUN, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hNI, hq,
      sqThD_eq hΛ L hL hv hzΛ, hΛ.sqTh_eq hv hzΛ, GlobalTheory.OddTheta.wpF_eq L Λ hL, GlobalTheory.OddTheta.wpF_eq L Λ hL,
      mul_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ I := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_pow, ← pow_mul, show 2 * I + 3 = (2 * (I - i) + 3) + 2 * i by omega]
      ring
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ I := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_pow, ← pow_mul, show 2 * I + 3 = 2 * (I - j) + 2 * j + 3 by omega]
      ring
  intro z
  exact congrFun heq z

end GlobalTheory.ThetaTranslDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RelIndexImageOneSubComplexLinearEquiv
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.ThetaCovIndex

open GlobalTheory.ThetaInter Module

section General

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]


omit [FiniteDimensional ℝ W] in
set_option backward.isDefEq.respectTransparency false in
theorem relIndex_eq_abs_det {ι : Type} [Fintype ι] [DecidableEq ι] (b₁ b₂ : Basis ι ℝ W) {L₁ L₂ : AddSubgroup W}
    (h₁ : (Submodule.span ℤ (Set.range b₁)).toAddSubgroup = L₁)
    (h₂ : (Submodule.span ℤ (Set.range b₂)).toAddSubgroup = L₂) (h : L₁ ≤ L₂) :
    (L₁.relIndex L₂ : ℝ) = |b₂.det b₁| := by
  subst h₁ h₂
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ h (b₁.restrictScalars ℤ) (b₂.restrictScalars ℤ),
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  have := b₂.restrictScalars_repr_apply ℤ
    ⟨b₁.restrictScalars ℤ j, h (Submodule.coe_mem _)⟩ i
  refine this.trans ?_
  simp

theorem exists_basis_finrank {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ W)) ℝ W, (Submodule.span ℤ (Set.range b)).toAddSubgroup = A := by
  have : DiscreteTopology A.toIntSubmodule := hA
  have : IsZLattice ℝ A.toIntSubmodule := ⟨hsp⟩
  let b₀ := Module.finBasisOfFinrankEq ℤ A.toIntSubmodule (ZLattice.rank ℝ A.toIntSubmodule)
  refine ⟨b₀.ofZLatticeBasis ℝ A.toIntSubmodule, ?_⟩
  rw [Basis.ofZLatticeBasis_span]
  rfl

theorem relIndex_map {A B : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (f : W ≃ₗ[ℝ] W) (hB : B ≤ A)
    (hf : B.map (f : W →ₗ[ℝ] W).toAddMonoidHom ≤ A) {m : ℕ} (hm : 0 < m)
    (hx : ∀ x ∈ A, ∃ y ∈ B, m • x = f y) :
    B.relIndex A ≠ 0 ∧ ((B.map (f : W →ₗ[ℝ] W).toAddMonoidHom).relIndex A : ℝ) =
      B.relIndex A * |LinearMap.det (f : W →ₗ[ℝ] W)| := by
  have hBd : DiscreteTopology B := DiscreteTopology.of_subset hA hB
  have hBs : Submodule.span ℝ (B : Set W) = ⊤ := by
    have h1 : (Submodule.span ℝ (B : Set W)).map (f : W →ₗ[ℝ] W) = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      intro x hxA
      obtain ⟨y, hy, e⟩ := hx x hxA
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      refine ⟨(m : ℝ)⁻¹ • y, Submodule.smul_mem _ _ (Submodule.subset_span hy), ?_⟩
      simp only [LinearEquiv.coe_coe, map_smul]
      rw [← e, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, e⟩ := (h1.ge (Submodule.mem_top (x := f x)))
    exact f.injective e ▸ hy
  obtain ⟨a, ha⟩ := exists_basis_finrank hA hsp
  obtain ⟨b, hb⟩ := exists_basis_finrank hBd hBs
  have hb₁ : (Submodule.span ℤ (Set.range (b.map f))).toAddSubgroup =
      B.map (f : W →ₗ[ℝ] W).toAddMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := f.surjective y
    have : f x ∈ B.map (f : W →ₗ[ℝ] W).toAddMonoidHom ↔ x ∈ B :=
      AddSubgroup.mem_map_iff_mem (f := (f : W →ₗ[ℝ] W).toAddMonoidHom) f.injective
    rw [this, ← hb, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
      Module.Basis.mem_span_iff_repr_mem, Module.Basis.mem_span_iff_repr_mem]
    simp
  have e1 := relIndex_eq_abs_det b a hb ha hB
  generalize B.map (f : W →ₗ[ℝ] W).toAddMonoidHom = C at hf hb₁ ⊢
  have e2 := relIndex_eq_abs_det (b.map f) a hb₁ ha hf
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, Nat.cast_zero, eq_comm, abs_eq_zero] at e1
    exact IsUnit.ne_zero (a.isUnit_det b) e1
  · rw [e2, e1, ← abs_mul, mul_comm, ← a.det_comp (f : W →ₗ[ℝ] W) b, Basis.coe_map]
    rfl

end General

theorem relIndex_image_one_sub_complexLinearEquiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {A A₁ : AddSubgroup W} (t₁ : DiscreteTopology A) (s₁ : Submodule.span ℝ (A : Set W) = ⊤)
    (u : W ≃ₗ[ℂ] W) (hA : ∀ x, x ∈ A ↔ u x ∈ A₁)
    (hdet : LinearMap.det (LinearMap.id - (u.symm : W →ₗ[ℂ] W)) ≠ 0) {m : ℕ} (hm : 0 < m)
    (hx : ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) :
    A₁.relIndex A ≠ 0 ∧
      (((A.map (LinearMap.id - (u.symm : W →ₗ[ℂ] W)).toAddMonoidHom).relIndex A : ℕ) : ℝ) =
        (A₁.relIndex A : ℝ) * ‖LinearMap.det (LinearMap.id - (u.symm : W →ₗ[ℂ] W))‖ ^ 2 := by
  set g : W →ₗ[ℂ] W := LinearMap.id - (u.symm : W →ₗ[ℂ] W) with hg
  have hgy : ∀ y, g y = y - u.symm y := fun y => rfl
  let f : W ≃ₗ[ℝ] W := (LinearMap.equivOfDetNeZero g hdet).restrictScalars ℝ
  have hfg : (f : W →ₗ[ℝ] W) = g.restrictScalars ℝ := by
    ext1 y; simp [f]
  have hfy : ∀ y, f y = y - u.symm y := fun y => congrArg (fun φ => φ y) hfg
  have hA' : ∀ y, u.symm y ∈ A ↔ y ∈ A₁ := fun y => by rw [hA, u.apply_symm_apply]
  have hinf : (A₁ ⊓ A).map (f : W →ₗ[ℝ] W).toAddMonoidHom = A.map g.toAddMonoidHom ⊓ A := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy₁, hy⟩, rfl⟩
      refine ⟨⟨y, hy, (hfy y).symm⟩, ?_⟩
      change f y ∈ A
      rw [hfy]
      exact A.sub_mem hy ((hA' y).2 hy₁)
    · rintro ⟨⟨y, hy, rfl⟩, h2⟩
      refine ⟨y, ⟨(hA' y).1 ?_, hy⟩, hfy y⟩
      have h3 : y - u.symm y ∈ A := h2
      simpa using A.sub_mem hy h3
  have key := relIndex_map (B := A₁ ⊓ A) t₁ s₁ f inf_le_right (hinf.le.trans inf_le_right) hm
    fun x hxA => by
      obtain ⟨y, hy, hy', e⟩ := hx x hxA
      exact ⟨y, ⟨(hA' y).1 hy', hy⟩, e.trans (hfy y).symm⟩
  rw [hinf, AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_right, hfg,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity)] at key
  exact key

theorem relIndex_one_sub : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → A₁.relIndex A ≠ 0 ∧ ((((A.map (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')).toAddMonoidHom).relIndex A : ℕ) : ℝ)) = (A₁.relIndex A : ℝ) * ‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ ^ 2 := by
  intro D cc δ hc N N' A A₁ h₁ _ u _ hA hdet ⟨m, hm, hx⟩
  obtain ⟨f₁, s₁, d₁, -⟩ := klat_facts hc h₁
  have t₁ := discrete_of_selfDual (isHerm_sesqOf D (tor0 D cc δ) N N') d₁ f₁
  exact relIndex_image_one_sub_complexLinearEquiv t₁ s₁ u hA hdet hm hx

end GlobalTheory.ThetaCovIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqNegOnePow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqNegOnePow
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TriangleSign

theorem exists_coords {V R ι : Type} [AddCommGroup V] [CommRing R] (P : Ideal R) (A B C : AddSubgroup V)
    (f : (ι → R) →+ V) (hB : ∀ a, f a ∈ B) (hk : ∀ a, f a ∈ A ↔ ∀ i, a i ∈ P)
    (hs : ∀ z ∈ B, ∃ a, z - f a ∈ A ∧ z - f a ∈ C) :
    ∃ (e : (B ⧸ A.addSubgroupOf B) ≃ (ι → R ⧸ P)) (a : (B ⧸ A.addSubgroupOf B) → ι → R),
      ∀ q, (((Quotient.out q : B) : V) - f (a q) ∈ A ∧ ((Quotient.out q : B) : V) - f (a q) ∈ C) ∧
        ∀ i, Ideal.Quotient.mk P (a q i) = e q i := by
  choose g hg using hs
  let a : (B ⧸ A.addSubgroupOf B) → ι → R := fun q => g _ (Quotient.out q : B).2
  have ha : ∀ q, ((Quotient.out q : B) : V) - f (a q) ∈ A ∧ ((Quotient.out q : B) : V) - f (a q) ∈ C :=
    fun q => hg _ _
  let e : (B ⧸ A.addSubgroupOf B) → (ι → R ⧸ P) := fun q i => Ideal.Quotient.mk P (a q i)
  have hinj : Function.Injective e := by
    intro q q' h
    have h1 : f (a q' - a q) ∈ A := (hk _).2 fun i => by
      have := congrFun h i
      exact Ideal.Quotient.eq.1 this.symm
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    have h2 := A.add_mem (A.sub_mem (ha q').1 (ha q).1) h1
    rw [map_sub] at h2
    convert h2 using 1
    push_cast; abel
  have hsurj : Function.Surjective e := by
    intro t
    let b : ι → R := fun i => Quotient.out (t i)
    let q : B ⧸ A.addSubgroupOf B := QuotientAddGroup.mk ⟨f b, hB b⟩
    have h1 : (QuotientAddGroup.mk (Quotient.out q) : B ⧸ A.addSubgroupOf B) = QuotientAddGroup.mk ⟨f b, hB b⟩ :=
      QuotientAddGroup.out_eq' q
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    have h2 : f (b - a q) ∈ A := by
      have := A.add_mem h1 (ha q).1
      rw [map_sub]
      convert this using 1
      push_cast; abel
    refine ⟨q, funext fun i => ?_⟩
    have h3 := Ideal.Quotient.eq.2 ((hk _).1 h2 i)
    rw [← Ideal.Quotient.mk_out (t i)]
    exact h3.symm
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, a, fun q => ⟨ha q, fun i => rfl⟩⟩

def ch (D : D7) (s : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Real.sqrt D.host.d * s.re + s.im : ℝ) : ℂ))

theorem bc_eq (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : bc D T x y = ch D (Hf D T x y) := rfl

theorem ch_add (D : D7) (s t : ℂ) : ch D (s + t) = ch D s * ch D t := by
  rw [ch, ch, ch, ← Complex.exp_add, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

theorem ch_zero (D : D7) : ch D 0 = 1 := by simp [ch]

theorem ch_ne_zero (D : D7) (s : ℂ) : ch D s ≠ 0 := Complex.exp_ne_zero _

theorem bc_sum_left (D : D7) (T : Tor D) {N N' : ℕ} {ι : Type} (s : Finset ι) (x : ι → VC D N N') (y : VC D N N') :
    bc D T (∑ i ∈ s, x i) y = ∏ i ∈ s, bc D T (x i) y := by
  induction s using Finset.induction_on with
  | empty => simp [bc_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, bc_add_left, ih]

theorem bc_sum_right (D : D7) (T : Tor D) {N N' : ℕ} {ι : Type} (s : Finset ι) (x : VC D N N') (y : ι → VC D N N') :
    bc D T x (∑ i ∈ s, y i) = ∏ i ∈ s, bc D T x (y i) := by
  induction s using Finset.induction_on with
  | empty => simp [bc_zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, bc_add_right, ih]

def sumHom {V R ι : Type} [Fintype ι] [AddCommGroup V] [CommRing R] (X : ι → R →+ V) : (ι → R) →+ V where
  toFun a := ∑ i, X i (a i)
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

theorem sumHom_apply {V R ι : Type} [Fintype ι] [AddCommGroup V] [CommRing R] (X : ι → R →+ V) (a : ι → R) :
    sumHom X a = ∑ i, X i (a i) := rfl

theorem sign_of_pow {μ : ℂ} {r : ℕ} {r₀ m : ℝ} (h0 : 0 < r₀) (hm : 0 < m) (h8 : μ ^ 8 = 1)
    (h : μ * (r₀ : ℂ) = (-1) ^ r * (m : ℂ)) : μ = (-1) ^ r := by
  have hr : (r₀ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have h1 : μ = (-1) ^ r * ((m / r₀ : ℝ) : ℂ) := by
    push_cast; field_simp; exact h
  have h2 : (m / r₀) ^ 8 = 1 := by
    rw [h1, mul_pow, ← pow_mul, mul_comm r 8, pow_mul] at h8
    norm_num at h8
    exact_mod_cast h8
  have h3 : m / r₀ = 1 := (pow_eq_one_iff_of_nonneg (div_pos hm h0).le (by norm_num)).1 h2
  rw [h1, h3]; simp

theorem mu_eq_sign : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ),
    Trip D T A₁ A₂ A₃ e μ → ∀ (P : Ideal (𝓞 D.host.E)) (r : ℕ), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) →
    (∃ a, a - sgO D a ∉ P) → TriDat D T A₁ A₂ A₃ P r → μ = (-1) ^ r := by
  intro D T N N' A₁ A₂ A₃ e μ hT P r hP hσ hne hD
  obtain ⟨r₀, hr₀, hμ⟩ := GlobalTheory.TripleConstant.mu_form D T N N' A₁ A₂ A₃ e μ hT
  obtain ⟨n₁, n₂, n₃, -, -, -, -, -, h8, -⟩ := hT
  obtain ⟨X, Y, φ, hH, hm, hp, s₂, s₃, k₁, k₂⟩ := hD
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  have : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  let _ : Fintype (𝓞 D.host.E ⧸ P) := Fintype.ofFinite _
  let χ : Fin r → 𝓞 D.host.E → ℂ := fun i s => ch D (φ i s)
  have χadd : ∀ i a b, χ i (a + b) = χ i a * χ i b := fun i a b => by simp only [χ, map_add (f := _), ch_add]
  have hYX : ∀ i a a', bc D T (Y i a') (X i a) = χ i (a' * sgO D a) := fun i a a' => by
    rw [bc_eq, hH, if_pos rfl]
  have hYX' : ∀ i j a a', i ≠ j → bc D T (Y i a') (X j a) = 1 := fun i j a a' h => by
    rw [bc_eq, hH, if_neg h, ch_zero]
  have hXY' : ∀ i j a a', i ≠ j → bc D T (X j a) (Y i a') = 1 := fun i j a a' h => by
    rw [bc_eq, ← Hf_conj, hH, if_neg h, map_zero, ch_zero]
  have χP : ∀ i, ∀ a ∈ P, χ i a = 1 := fun i a ha => by
    have := hYX i 1 a
    rw [map_one (sgO D), mul_one] at this
    rw [← this]
    exact n₂.2.1 _ (hp i a ha).2.2 _ (hm i 1).1
  have χne : ∀ i, ∃ a, χ i (a + sgO D a) ≠ 1 := fun i => by
    by_contra hc
    push Not at hc
    have c1 : ∀ j a, bc D T (X i 1) (Y j a) = bc D T (Y j a) (X i 1) := fun j a => by
      by_cases h : j = i
      · subst h
        have e1 := n₁.2.1 _ (hm j 1).2.2 _ (hm j a).2.2
        rw [bc_add_left, bc_add_right, bc_add_right, n₂.2.1 _ (hm j 1).1 _ (hm j a).1,
          n₃.2.1 _ (hm j 1).2.1 _ (hm j a).2.1, hYX, one_mul, one_mul, mul_one] at e1
        have e2 := hc a
        rw [χadd] at e2
        rw [hYX, map_one (sgO D), mul_one]
        exact mul_right_cancel₀ (ch_ne_zero D _) (e1.trans e2.symm)
      · rw [hYX' j i _ _ h, hXY' j i _ _ h]
    have c2 : X i 1 ∈ A₃ := n₃.2.2 _ fun y hy => by
      obtain ⟨a, ha⟩ := s₃ y hy
      have hy' : y = (y - ∑ j, Y j (a j)) + ∑ j, Y j (a j) := by abel
      rw [hy', bc_add_left, bc_add_right, n₂.2.1 _ ha.2 _ (hm i 1).1, n₂.2.1 _ (hm i 1).1 _ ha.2,
        bc_sum_left, bc_sum_right]
      simp only [c1]
    obtain ⟨a, ha⟩ := s₃ _ c2
    have c3 : ∑ j, Y j (a j) ∈ A₂ := by
      have := A₂.sub_mem (hm i 1).1 ha.2
      simpa using this
    have c4 : ∑ j, Y j (a j) ∈ A₁ := A₁.sum_mem fun j _ => (hp j _ (k₂ a c3 j)).2.1
    have c5 : X i 1 ∈ A₁ := by
      have := A₁.add_mem ha.1 c4
      simpa using this
    have c6 : ∑ j, X j ((Pi.single i 1 : Fin r → 𝓞 D.host.E) j) = X i 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, map_zero]
      · simp
    have c7 := k₁ (Pi.single i 1) (c6 ▸ c5) i
    rw [Pi.single_eq_same] at c7
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 c7)
  have hG : ∀ i, ∃ m : ℝ, 0 < m ∧
      ∑ᶠ q : 𝓞 D.host.E ⧸ P, χ i (Quotient.out q * sgO D (Quotient.out q)) = -(m : ℂ) := fun i =>
    GlobalTheory.NormGauss.finsum_norm_neg _ (sgO D) P (sgO_sgO D) hσ hne (χ i) (χadd i) (χP i) (χne i)
  choose m hm0 hmG using hG
  have kX : ∀ a, sumHom X a ∈ A₁ ↔ ∀ i, a i ∈ P := fun a =>
    ⟨k₁ a, fun h => by rw [sumHom_apply]; exact A₁.sum_mem fun i _ => (hp i _ (h i)).1.1⟩
  have kY : ∀ a, sumHom Y a ∈ A₂ ↔ ∀ i, a i ∈ P := fun a =>
    ⟨k₂ a, fun h => by rw [sumHom_apply]; exact A₂.sum_mem fun i _ => (hp i _ (h i)).2.2⟩
  have mX : ∀ a, sumHom X a ∈ A₂ := fun a => by
    rw [sumHom_apply]; exact A₂.sum_mem fun i _ => (hm i _).1
  have mY : ∀ a, sumHom Y a ∈ A₃ := fun a => by
    rw [sumHom_apply]; exact A₃.sum_mem fun i _ => (hm i _).2.1
  have mXY : ∀ a, sumHom X a + sumHom Y a ∈ A₁ := fun a => by
    rw [sumHom_apply, sumHom_apply, ← Finset.sum_add_distrib]
    exact A₁.sum_mem fun i _ => (hm i _).2.2
  obtain ⟨e₂, a₂, h₂⟩ := exists_coords P A₁ A₂ A₃ (sumHom X) mX kX
    (fun z hz => (s₂ z hz).imp fun a ha => ⟨ha.1, ha.2⟩)
  obtain ⟨e₃, a₃, h₃⟩ := exists_coords P A₂ A₃ A₁ (sumHom Y) mY kY
    (fun z hz => (s₃ z hz).imp fun a ha => ⟨ha.2, ha.1⟩)
  let F : (Fin r → 𝓞 D.host.E ⧸ P) × (Fin r → 𝓞 D.host.E ⧸ P) → ℂ := fun p =>
    if p.1 = p.2 then ∏ i, χ i (Quotient.out (p.2 i) * sgO D (Quotient.out (p.2 i))) else 0
  have key : ∀ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂),
      (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then
        bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) =
      F (Equiv.prodCongr e₃ e₂ p) := by
    rintro ⟨q₃, q₂⟩
    obtain ⟨⟨u1, u3⟩, u⟩ := h₂ q₂
    obtain ⟨⟨v2, v1⟩, v⟩ := h₃ q₃
    have x2 := (Quotient.out q₂ : A₂).2
    have y3 := (Quotient.out q₃ : A₃).2
    simp only [F, Equiv.prodCongr_apply, Prod.map]
    generalize ((Quotient.out q₂ : A₂) : VC D N N') = x at *
    generalize ((Quotient.out q₃ : A₃) : VC D N N') = y at *
    have hiff : y + x ∈ A₁ ↔ e₃ q₃ = e₂ q₂ := by
      have w : y + x = sumHom X (a₂ q₂ - a₃ q₃) + ((x - sumHom X (a₂ q₂)) + (y - sumHom Y (a₃ q₃)) +
          (sumHom X (a₃ q₃) + sumHom Y (a₃ q₃))) := by rw [map_sub]; abel
      rw [w, A₁.add_mem_cancel_right (A₁.add_mem (A₁.add_mem u1 v1) (mXY _)), kX, funext_iff]
      refine forall_congr' fun i => ?_
      rw [← u, ← v, eq_comm, Ideal.Quotient.eq, Pi.sub_apply]
    by_cases h : e₃ q₃ = e₂ q₂
    · rw [if_pos (hiff.2 h), if_pos h]
      have wx : x = sumHom X (a₂ q₂) + (x - sumHom X (a₂ q₂)) := by abel
      have wy : y = sumHom Y (a₃ q₃) + (y - sumHom Y (a₃ q₃)) := by abel
      rw [wy, bc_add_left, n₂.2.1 _ v2 _ x2, mul_one, wx, bc_add_right, n₃.2.1 _ (mY _) _ u3, mul_one,
        sumHom_apply, sumHom_apply, bc_sum_left]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [bc_sum_right, Finset.prod_eq_single i (fun j _ hj => hYX' i j _ _ hj.symm) (by simp), hYX]
      set t := Quotient.out (e₂ q₂ i) with ht
      have t2 : a₂ q₂ i - t ∈ P := Ideal.Quotient.eq.1 (by rw [u, ht, Ideal.Quotient.mk_out])
      have t3 : a₃ q₃ i - t ∈ P := Ideal.Quotient.eq.1 (by rw [v, h, ht, Ideal.Quotient.mk_out])
      have w : a₃ q₃ i * sgO D (a₂ q₂ i) = t * sgO D t +
          ((a₃ q₃ i - t) * sgO D (a₂ q₂ i) + t * sgO D (a₂ q₂ i - t)) := by rw [map_sub]; ring
      rw [w, χadd, χP i _ (P.add_mem (P.mul_mem_right _ t3) (P.mul_mem_left _ (hσ _ t2))), mul_one]
    · rw [if_neg (mt hiff.1 h), if_neg h]
  rw [finsum_congr key, finsum_comp_equiv (Equiv.prodCongr e₃ e₂) (f := F), finsum_eq_sum_of_fintype,
    Fintype.sum_prod_type_right] at hμ
  simp only [F, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hμ
  simp only [finsum_eq_sum_of_fintype] at hmG
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ)
    (fun i (t : 𝓞 D.host.E ⧸ P) => χ i (Quotient.out t * sgO D (Quotient.out t)))] at hμ
  simp only [hmG] at hμ
  refine sign_of_pow hr₀ (Finset.prod_pos fun i (_ : i ∈ Finset.univ) => hm0 i) h8 ?_
  rw [hμ, Finset.prod_neg]
  simp

end GlobalTheory.TriangleSign
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqNegOnePowStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTripleConstant_eq_neg_one_pow : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → ∀ (P : Ideal (𝓞 D.host.E)) (r : ℕ), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → (∃ a, a - sgO D a ∉ P) → TriDat D T A₁ A₂ A₃ P r → μ = (-1) ^ r := by
  first | exact @GlobalTheory.TriangleSign.mu_eq_sign | exact GlobalTheory.TriangleSign.mu_eq_sign | (intros; apply GlobalTheory.TriangleSign.mu_eq_sign <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDataOfNeighbourTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDataOfNeighbourTriple
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TriangleColumns

def IL (D : D7) (cc : Ideal (𝓞 D.host.K)) {n : ℕ} (L : Lat D n) : Lat D n :=
  Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • y}

theorem smul_mem_IL {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L : Lat D n} {t : D.host.E}
    (ht : t ∈ Iid D cc) {y : Fin n → D.host.E} (hy : y ∈ L) : t • y ∈ IL D cc L :=
  Submodule.subset_span ⟨t, ht, y, hy, rfl⟩

theorem IL_mono {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L L' : Lat D n} (h : L ≤ L') :
    IL D cc L ≤ IL D cc L' :=
  Submodule.span_mono fun _ ⟨t, ht, y, hy, e⟩ => ⟨t, ht, y, h hy, e⟩

theorem hE_osmul_left (D : D7) {n : ℕ} (a : 𝓞 D.host.E) (x y : Fin n → D.host.E) :
    hE D (a • x) y = a • hE D x y := by
  rw [← algebraMap_smul D.host.E a x, hE_smul_left, Algebra.smul_def]

theorem pair_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L : Lat D n} {v w : Fin n → D.host.E}
    (hw : ∀ y ∈ L, IntE D (hE D y w)) (hv : v ∈ IL D cc L) : hE D v w ∈ Iid D cc := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨o, ho⟩ := hw y hy
    rw [hE_smul_left, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ht
  | zero => simp [hE]
  | add u v _ _ hu hv => rw [hE_add_left]; exact add_mem hu hv
  | smul a v _ hv => rw [hE_osmul_left]; exact Submodule.smul_mem _ _ hv

theorem sd_int {D : D7} {n : ℕ} {L : Lat D n} (h : SD D L) {y w : Fin n → D.host.E} (hy : y ∈ L) (hw : w ∈ L) :
    IntE D (hE D y w) := (((sd_iff D L).1 h).2.2 y).1 hy w hw

theorem smul_mem_IL_of_P {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {M : Lat D n} {P : Ideal (𝓞 D.host.E)}
    {b : Fin n → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t : D.host.E} (ht : t ∈ P • Iid D cc) :
    t • b ∈ IL D cc M := by
  refine Submodule.smul_induction_on ht (fun p hp s hs => ?_) (fun u v hu hv => ?_)
  · have : (p • s) • b = s • (p • b) := by rw [smul_assoc, smul_comm]
    rw [this]; exact smul_mem_IL hs (hb p hp)
  · rw [add_smul]; exact add_mem hu hv

theorem decomp {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {M : Lat D n} {P : Ideal (𝓞 D.host.E)}
    {b : Fin n → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {v : Fin n → D.host.E}
    (hv : v ∈ IL D cc (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : 𝓞 D.host.E, v - (a • t₀) • b ∈ IL D cc M := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨a, ha⟩ := hg (o • t) (Submodule.smul_mem _ _ ht)
    refine ⟨a, ?_⟩
    have : t • (m + o • b) - (a • t₀) • b = t • m + (o • t - a • t₀) • b := by
      rw [smul_add, sub_smul, smul_assoc o t b, smul_comm o t b]; abel
    rw [this]
    exact add_mem (smul_mem_IL ht hm) (smul_mem_IL_of_P hb ha)
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨a', ha'⟩ := hv
    refine ⟨a + a', ?_⟩
    have : u + v - ((a + a') • t₀) • b = (u - (a • t₀) • b) + (v - (a' • t₀) • b) := by
      rw [add_smul, add_smul]; abel
    rw [this]; exact add_mem ha ha'
  | smul c v _ hv =>
    obtain ⟨a, ha⟩ := hv
    refine ⟨c * a, ?_⟩
    have : c • v - ((c * a) • t₀) • b = c • (v - (a • t₀) • b) := by
      rw [smul_sub, mul_smul, smul_assoc c]
    rw [this]; exact Submodule.smul_mem _ _ ha

def mat (D : D7) {N N' : ℕ} (t₀ : D.host.E) (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E := fun i j => (a j • t₀) * b i

theorem pt_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z : Matrix (Fin N') (Fin N) D.host.E)
    (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) : pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := rfl

theorem pt_sub (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ w = pt D (tor0 D cc δ) δ (z - w) := by
  funext τ i j
  simp only [Pi.sub_apply, pt_apply, Matrix.sub_apply, map_sub, mul_sub]

theorem pt_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w = pt D (tor0 D cc δ) δ (z + w) := by
  funext τ i j
  simp only [Pi.add_apply, pt_apply, Matrix.add_apply, map_add (f := _), mul_add]

def ptH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E) (b : Fin N' → D.host.E) :
    (Fin N → 𝓞 D.host.E) →+ VC D N N' :=
  AddMonoidHom.mk' (fun a => pt D (tor0 D cc δ) δ (mat D t₀ b a)) fun a a' => by
    rw [pt_add]; congr 1; funext i j
    simp only [mat, Pi.add_apply, Matrix.add_apply, add_smul, add_mul]

theorem ptH_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a = pt D (tor0 D cc δ) δ (mat D t₀ b a) := rfl

def phiH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N' : ℕ} (t₀ : D.host.E) (b x : Fin N' → D.host.E) :
    𝓞 D.host.E →+ ℂ :=
  AddMonoidHom.mk' (fun s => (∑ τ, ∑ i, embT D τ (s : D.host.E) *
      (δ * embT D τ (t₀ * x i) * (starRingEnd ℂ) (δ * embT D τ (t₀ * b i)))) / (area (tor0 D cc δ).abelian₂ : ℂ))
    fun s s' => by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add (f := _), add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_ptH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b x : Fin N' → D.host.E) (c c' : Fin N → 𝓞 D.host.E) :
    Hf D (tor0 D cc δ) (ptH D cc δ N t₀ x c') (ptH D cc δ N t₀ b c) =
      phiH D cc δ t₀ b x (∑ k, c' k * sgO D (c k)) := by
  have h1 : ∀ s : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E (sgO D s) =
      D.host.conj (algebraMap (𝓞 D.host.E) D.host.E s) := fun s => rfl
  rw [phiH, AddMonoidHom.mk'_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, ptH_apply, pt_apply, mat, Algebra.smul_def,
    RingOfIntegers.coe_eq_algebraMap, map_sum, map_mul, h1, embT_conj, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pt_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} (L : Lat D N')
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) (stdL D N) L ↔ ∀ j, (fun i => z i j) ∈ IL D cc L := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.ThetaLatImage.theta_lattice_image D cc δ hδ N N'
  rw [h2]
  constructor
  · rintro ⟨w, hw, e⟩
    rw [h1 e]; exact (h3 L w).1 hw
  · intro h
    exact ⟨z, (h3 L z).2 h, rfl⟩

theorem ptH_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} (L : Lat D N')
    (t₀ : D.host.E) (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a ∈ La D (tor0 D cc δ) (stdL D N) L ↔ ∀ j, (a j • t₀) • b ∈ IL D cc L :=
  pt_mem hδ L _

theorem ptH_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b x : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a + ptH D cc δ N t₀ x a = ptH D cc δ N t₀ (b + x) a := by
  rw [ptH_apply, ptH_apply, ptH_apply, pt_add]; congr 1; funext i j
  simp only [mat, Pi.add_apply, Matrix.add_apply, mul_add]

theorem exists_sub_ptH {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {M : Lat D N'}
    {P : Ideal (𝓞 D.host.E)} {b : Fin N' → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {z : VC D N N'}
    (hz : z ∈ La D (tor0 D cc δ) (stdL D N) (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : Fin N → 𝓞 D.host.E, ∀ L : Lat D N', M ≤ L →
      z - ptH D cc δ N t₀ b a ∈ La D (tor0 D cc δ) (stdL D N) L := by
  obtain ⟨w, -, rfl⟩ := ((GlobalTheory.ThetaLatImage.theta_lattice_image D cc δ hδ N N').2.1 _ _ z).1 hz
  choose a ha using fun j => decomp hb hg ((pt_mem hδ _ w).1 hz j)
  refine ⟨a, fun L hL => ?_⟩
  rw [ptH_apply, pt_sub, pt_mem hδ]
  exact fun j => IL_mono hL (ha j)

theorem triDat_of_tri : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → ∀ A B C : Lat D N', Tri D P A B C → TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) A) (La D (tor0 D cc δ) (stdL D N) B) (La D (tor0 D cc δ) (stdL D N) C) P N := by
  intro D cc δ hcc hδ N N' P hP A B C ⟨hA, hB, hC, M, b, x, eA, eB, eC, hp, hbx⟩
  obtain ⟨t₀, ht₀, hg, hθ⟩ := GlobalTheory.IdealGenerator.exists_generator_Iid D cc hcc P hP
  have MA : M ≤ A := eA ▸ le_sup_left
  have MB : M ≤ B := eB ▸ le_sup_left
  have MC : M ≤ C := eC ▸ le_sup_left
  have bxA : b + x ∈ A := eA ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have bB : b ∈ B := eB ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have xC : x ∈ C := eC ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hsum : ∀ (y : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E),
      ∑ i, ((ptH D cc δ N t₀ y).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i)) (a i) =
        ptH D cc δ N t₀ y a := by
    intro y a
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Finset.univ_sum_single]
  have hin : ∀ (L : Lat D N') (y : Fin N' → D.host.E), y ∈ L → ∀ a : Fin N → 𝓞 D.host.E,
      ptH D cc δ N t₀ y a ∈ La D (tor0 D cc δ) (stdL D N) L := fun L y hy a =>
    (ptH_mem hδ L t₀ y a).2 fun j => smul_mem_IL (Submodule.smul_mem _ _ ht₀) hy
  have hinP : ∀ (L : Lat D N') (y : Fin N' → D.host.E), M ≤ L → (∀ p ∈ P, p • y ∈ M) → ∀ i, ∀ p ∈ P,
      ptH D cc δ N t₀ y (Pi.single i p) ∈ La D (tor0 D cc δ) (stdL D N) L := fun L y hL hy i p hp =>
    (ptH_mem hδ L t₀ y _).2 fun j => IL_mono hL <| smul_mem_IL_of_P hy <| Submodule.smul_mem_smul (by
      by_cases h : j = i
      · subst h; simpa using hp
      · simp [Pi.single_eq_of_ne h]) ht₀
  refine ⟨fun i => (ptH D cc δ N t₀ b).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i),
    fun i => (ptH D cc δ N t₀ x).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i),
    fun _ => phiH D cc δ t₀ b x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j a a'
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
    rw [Hf_ptH, Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_mul]) (by simp)]
    split_ifs with h
    · subst h; simp only [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, map_zero, mul_zero, map_zero]
  · intro i a
    refine ⟨hin B b bB _, hin C x xC _, ?_⟩
    simp only [AddMonoidHom.comp_apply]
    rw [ptH_add]; exact hin A _ bxA _
  · intro i p hpP
    exact ⟨⟨hinP A b MA (fun p h => (hp p h).1) i p hpP, hinP C b MC (fun p h => (hp p h).1) i p hpP⟩,
      ⟨hinP A x MA (fun p h => (hp p h).2) i p hpP, hinP B x MB (fun p h => (hp p h).2) i p hpP⟩⟩
  · intro z hz
    rw [eB] at hz
    obtain ⟨a, ha⟩ := exists_sub_ptH hδ (fun p h => (hp p h).1) hg hz
    exact ⟨a, by rw [hsum]; exact ⟨ha A MA, ha C MC⟩⟩
  · intro z hz
    rw [eC] at hz
    obtain ⟨a, ha⟩ := exists_sub_ptH hδ (fun p h => (hp p h).2) hg hz
    exact ⟨a, by rw [hsum]; exact ⟨ha A MA, ha B MB⟩⟩
  · intro a ha i
    rw [hsum, ptH_mem hδ] at ha
    have h1 := pair_mem (fun y hy => sd_int hA hy bxA) (ha i)
    obtain ⟨o, ho⟩ := sd_int hB bB bB
    refine hθ (hE D b x) hbx (fun p h => ?_) (a i) ?_
    · rw [← hE_osmul_left]; exact sd_int hC (MC (hp p h).1) xC
    · have : a i • (t₀ * hE D b x) = hE D ((a i • t₀) • b) (b + x) - (a i * o) • t₀ := by
        rw [hE_smul_left, hE_add_right, ← ho]
        simp only [Algebra.smul_def, map_mul]; ring
      rw [this]; exact sub_mem h1 (Submodule.smul_mem _ _ ht₀)
  · intro a ha i
    rw [hsum, ptH_mem hδ] at ha
    have h1 := pair_mem (fun y hy => sd_int hB hy bB) (ha i)
    refine hθ (hE D x b) (fun h => hbx (conj_hE D x b ▸ h.conj)) (fun p h => ?_) (a i) ?_
    · rw [← hE_osmul_left]; exact sd_int hB (MB (hp p h).2) bB
    · rwa [hE_smul_left, smul_mul_assoc] at h1

end GlobalTheory.TriangleColumns
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDataOfNeighbourTripleStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTripleData_of_neighbourTriple : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → ∀ A B C : Lat D N', Tri D P A B C → TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) A) (La D (tor0 D cc δ) (stdL D N) B) (La D (tor0 D cc δ) (stdL D N) C) P N := by
  first | exact @GlobalTheory.TriangleColumns.triDat_of_tri | exact GlobalTheory.TriangleColumns.triDat_of_tri | (intros; apply GlobalTheory.TriangleColumns.triDat_of_tri <;> assumption)
end
end
