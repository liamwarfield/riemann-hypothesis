module

public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ProjLineLimit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionSurjectiveAdditiveLinear
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.WeilBound.CoreStatements.HodgeTatePoints.KleimanInputUniverseZero
public import Development.WeilBound.CoreStatements.HodgeTatePoints.KTwins
public import Development.WeilBound.CoreStatements.HodgeTatePoints.SiuKodaira

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankChartLatQMono
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.ChartSections

theorem finrank_chartLatQ_mono : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (b b' : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → b ≤ b' →
    FiniteDimensional ℚ (chartLatQ y b' 1) →
    Module.finrank ℚ (chartLatQ y b 1) ≤ Module.finrank ℚ (chartLatQ y b' 1) := by
  intro K _ ι _ Ω _ _ y b b' hy hb hfd
  choose j hj using hy
  obtain ⟨n, hn⟩ : ∃ n : K → ℕ, ∀ k, (n k : ℤ) = b' k - b k :=
    ⟨fun k => (b' k - b k).toNat, fun k => Int.toNat_of_nonneg (sub_nonneg.2 (hb k))⟩
  have hu0 : (∏ k, y ⟨k, j k⟩ ^ n k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hj k)
  have hmem : ∀ s ∈ chartLatQ y b 1, s * ∏ k, y ⟨k, j k⟩ ^ n k ∈ chartLatQ y b' 1 := by
    intro s hs c hc
    have h1 : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) ∈ chartRingQ y c := hs c hc
    have hq : ∀ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ ∈ chartRingQ y c :=
      fun k => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
    have h2 : ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ n k ∈ chartRingQ y c :=
      prod_mem fun k _ => pow_mem (hq k) _
    have heq : s * (∏ k, y ⟨k, j k⟩ ^ n k) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k))) * ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ n k := by
      rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      have hck := hc k
      have hnk := hn k
      have hz : y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) =
          y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) * (y ⟨k, c k⟩ ^ n k)⁻¹ := by
        rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hck]
        congr 1
        simp only [Nat.cast_one, one_mul]
        omega
      rw [hz, div_pow, div_eq_mul_inv]
      ring
    show s * (∏ k, y ⟨k, j k⟩ ^ n k) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) ∈ chartRingQ y c
    rw [heq]
    exact mul_mem h1 h2
  let f : chartLatQ y b 1 →ₗ[ℚ] chartLatQ y b' 1 :=
    { toFun := fun s => ⟨s.1 * ∏ k, y ⟨k, j k⟩ ^ n k, hmem s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r s => Subtype.ext (smul_mul_assoc _ _ _) }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun s t hst => ?_
  exact Subtype.ext (mul_right_cancel₀ hu0 (congrArg Subtype.val hst))

end GlobalTheory.CompanionTheory.ChartSections
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpper
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpper
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.NefSections

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

theorem eval_le_top_add (P : Polynomial ℚ) (e : ℕ) (hP : P.natDegree ≤ e + 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ((P.eval (n : ℚ) : ℚ) : ℝ) ≤ ((P.coeff (e + 1) : ℚ) : ℝ) * (n : ℝ) ^ (e + 1) + C * (n : ℝ) ^ e := by
  refine ⟨∑ i ∈ Finset.range (e + 1), |((P.coeff i : ℚ) : ℝ)|, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.sum_range_succ]
  push_cast
  rw [add_comm, Finset.sum_mul]
  refine add_le_add le_rfl (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc ((P.coeff i : ℚ) : ℝ) * (n : ℝ) ^ i ≤ |((P.coeff i : ℚ) : ℝ)| * (n : ℝ) ^ i :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |((P.coeff i : ℚ) : ℝ)| * (n : ℝ) ^ e :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn1 hi') (abs_nonneg _)

theorem finrank_secOver_nsmul_le (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (d : ℕ) (ν : K → ℤ)
    (hmod : IsModelWithBase F y k₀)
    (hdim : FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)))
    (hva : VeryAmple F y ν) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (Module.finrank F (secOver F y (n • ν)) : ℝ) ≤
      (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) * (n : ℝ) ^ (d + 1) /
        ((d + 1).factorial : ℝ) + C * (n : ℝ) ^ d := by
  have hpos : 0 < Fintype.card (ι k₀) := by
    obtain ⟨i, -⟩ := hmod.1 k₀
    exact Fintype.card_pos_iff.2 ⟨i⟩
  obtain ⟨N, hN'⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  obtain ⟨e⟩ : Nonempty (ι k₀ ≃ Fin (N + 1)) := ⟨(Fintype.equivFin _).trans (finCongr hN')⟩
  obtain ⟨Q, hQ⟩ := Kleiman.SectionsOverLocalization.BundleOfDeg.full F K ι Ω y k₀ N e hmod ν
  have hsub := (Kleiman.SectionsOverLocalization.ModelDim.proof F K ι Ω y k₀ N e _ rfl hmod (d + 1)).2 hdim
  have hvaQ := (PositivityTheory.HtPt.Ktw.a74 F K ι Ω y k₀ N e _ rfl hmod Q ν hQ).2 hva
  obtain ⟨-, P, hdeg, hlead, hev⟩ := PositivityTheory.HtPt.Ktw.a37 F Ω N _ (d + 1) Q hsub hvaQ
  have hnum := PositivityTheory.HtPt.Ktw.a18 F K ι Ω y k₀ N e _ rfl hmod (d + 1) (fun _ => Q) (fun _ => ν) (fun _ => hQ) hsub
  obtain ⟨C, hC⟩ := eval_le_top_add P d hdeg
  refine ⟨C, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hsec : (Q.toSubSystem.pow n).secs = secOver F y (n • ν) := by
    have h := PositivityTheory.HtPt.Ktw.a66 F K ι Ω y k₀ N e _ rfl hmod Q ν hQ n 0
    rw [Kleiman.twistMul, Kleiman.SubSystem.twist_twistSys_zero] at h
    rw [h]
    simp
  rw [← hsec]
  have h1 : (Module.finrank F (Q.toSubSystem.pow n).secs : ℝ) = ((P.eval (n : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hn
  rw [h1]
  have hfac : ((d + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hco : ((P.coeff (d + 1) : ℚ) : ℝ) =
      (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) / ((d + 1).factorial : ℝ) := by
    have : P.coeff (d + 1) = (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℚ) /
        ((d + 1).factorial : ℚ) := by
      rw [eq_div_iff hfac, hlead, hnum]
    rw [this]; push_cast; rfl
  have := hC n hn1
  rw [hco] at this
  calc _ ≤ _ := this
    _ = _ := by ring

end GlobalTheory.CompanionTheory.NefSections

namespace GlobalTheory.CompanionTheory.NefSections

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

theorem exists_rat_multilinear_le {M : Type} [AddCommGroup M] {n : ℕ}
    (f : (Π _ : Fin n, M) →ₘₗ[ℤ] ℤ) (μ e : M) (ε : ℚ) (hε : 0 < ε) :
    ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t →
      ((f (fun _ => a • μ + m • e) : ℤ) : ℚ) ≤ (a : ℚ) ^ n * (((f fun _ => μ : ℤ) : ℚ) + ε) := by
  let g : ℚ → ℚ := fun t => PositivityTheory.HtPt.Siua.form f μ e (fun _ => 1) (fun _ => 1 * t)
  have hg : Continuous g := PositivityTheory.HtPt.Siua.form_cont f μ e (fun _ => 1) (fun _ => 1)
  have hg0 : g 0 = ((f fun _ => μ : ℤ) : ℚ) := by
    have h1 := PositivityTheory.HtPt.Siua.form_cast f μ e (fun _ => 1) (fun _ => 0)
    simp only [one_smul, zero_smul, add_zero, Int.cast_one, Int.cast_zero] at h1
    simp only [g, mul_zero]
    rw [← h1]
  have hlt : g 0 < ((f fun _ => μ : ℤ) : ℚ) + ε := by rw [hg0]; linarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℚ), g t < ((f fun _ => μ : ℤ) : ℚ) + ε ∧ 0 < t :=
    ((hg.continuousAt.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, hgt, ht⟩ := hev.exists
  refine ⟨t, ht, fun a m ha hm => ?_⟩
  have e2 : (fun _ : Fin n => a • μ + m • e) = fun _ => (a : ℤ) • μ + m • e := by
    funext i; simp
  have h2 := PositivityTheory.HtPt.Siua.form_cast f μ e (fun _ => (a : ℤ)) (fun _ => m)
  have h4 := PositivityTheory.HtPt.Siua.form_smul f μ e (fun _ => 1) (fun _ => 1 * t) a
  have h6 : PositivityTheory.HtPt.Siua.form f μ e (fun _ => (((a : ℤ) : ℤ) : ℚ)) (fun _ => ((m : ℤ) : ℚ)) =
      PositivityTheory.HtPt.Siua.form f μ e (fun _ => (a : ℚ) * 1) (fun _ => (a : ℚ) * (1 * t)) := by
    congr 1 <;> funext i <;> push_cast
    · ring
    · rw [hm]; ring
  have hapos : (0 : ℚ) ≤ (a : ℚ) ^ n := by positivity
  rw [e2, h2, h6, h4]
  exact mul_le_mul_of_nonneg_left hgt.le hapos

theorem secOver_eq_chartLatQ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (β : K → ℤ) : secOver ℚ y β = chartLatQ y β 1 := by
  ext s
  constructor
  · intro hs c hc
    have h1 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hs c) hc
    have h2 : s * ∏ j, y ⟨j, c j⟩ ^ (-β j) ∈ chartRingOver ℚ y c := h1
    have h3 : ∀ j, -(((1 : ℕ) : ℤ) * β j) = -β j := fun j => by simp
    simp only [h3]
    exact h2
  · intro hs
    refine (Submodule.mem_iInf _).2 fun c => (Submodule.mem_iInf _).2 fun hc => ?_
    have h1 := hs c hc
    have h3 : ∀ j, -(((1 : ℕ) : ℤ) * β j) = -β j := fun j => by simp
    simp only [h3] at h1
    exact h1

theorem real_step {X G ε' ε C A nR T fc : ℝ} (d : ℕ) (hfc : 0 < fc) (hG : 0 ≤ G) (hε' : 0 < ε') (hε : 2 * ε' ≤ ε)
    (hA : 1 ≤ A) (hn : 0 ≤ nR) (hAT : A * nR ≤ T) (hX : X ≤ A ^ (d + 1) * (G + ε'))
    (hT : |C| * fc ≤ ε' * T) (h1T : 1 ≤ T) {v : ℝ} (hv : v ≤ X * nR ^ (d + 1) / fc + C * nR ^ d) :
    v ≤ (G + ε) * T ^ (d + 1) / fc := by
  have hT0 : 0 ≤ T := by linarith
  have hnT : nR ≤ T := by nlinarith
  have h1 : X * nR ^ (d + 1) / fc ≤ (G + ε') * T ^ (d + 1) / fc := by
    apply div_le_div_of_nonneg_right _ hfc.le
    calc X * nR ^ (d + 1) ≤ (A ^ (d + 1) * (G + ε')) * nR ^ (d + 1) :=
          mul_le_mul_of_nonneg_right hX (by positivity)
      _ = (G + ε') * (A * nR) ^ (d + 1) := by rw [mul_pow]; ring
      _ ≤ (G + ε') * T ^ (d + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hAT _) (by linarith)
  have h2 : C * nR ^ d ≤ ε' * T ^ (d + 1) / fc := by
    rw [le_div_iff₀ hfc]
    calc C * nR ^ d * fc ≤ |C| * T ^ d * fc := by
          apply mul_le_mul_of_nonneg_right _ hfc.le
          calc C * nR ^ d ≤ |C| * nR ^ d := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
            _ ≤ |C| * T ^ d := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn hnT _) (abs_nonneg _)
      _ = (|C| * fc) * T ^ d := by ring
      _ ≤ (ε' * T) * T ^ d := mul_le_mul_of_nonneg_right hT (by positivity)
      _ = ε' * T ^ (d + 1) := by ring
  have h3 : (G + ε') * T ^ (d + 1) / fc + ε' * T ^ (d + 1) / fc ≤ (G + ε) * T ^ (d + 1) / fc := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hfc.le
    have : 0 ≤ T ^ (d + 1) := by positivity
    nlinarith
  linarith

theorem twist_le {K : Type} [Fintype K] (a b : K → ℤ) (a₀ : ℕ) :
    ∃ B : ℕ, ∀ (τ q : ℕ), 1 ≤ a₀ → 1 ≤ q → B ≤ τ / a₀ →
      (τ : ℤ) • a + b ≤ ((τ / a₀ * a₀ : ℕ) : ℤ) • a + fun _ => ((τ / a₀ * q : ℕ) : ℤ) := by
  refine ⟨∑ k, (a₀ * |a k| + |b k|).toNat, fun τ q ha hq hB k => ?_⟩
  set n := τ / a₀ with hn
  have hτ : τ = n * a₀ + τ % a₀ := by rw [hn]; exact (Nat.div_add_mod' τ a₀).symm
  have hr : τ % a₀ < a₀ := Nat.mod_lt _ ha
  set r := τ % a₀ with hrdef
  have hk : (a₀ * |a k| + |b k|).toNat ≤ n :=
    le_trans (Finset.single_le_sum (f := fun k => (a₀ * |a k| + |b k|).toNat)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)) hB
  have hnn : (0 : ℤ) ≤ a₀ * |a k| + |b k| := by positivity
  have hk' : (a₀ : ℤ) * |a k| + |b k| ≤ n := by
    have : (((a₀ * |a k| + |b k|).toNat : ℕ) : ℤ) ≤ n := by exact_mod_cast hk
    rwa [Int.toNat_of_nonneg hnn] at this
  have hra : (r : ℤ) * a k ≤ a₀ * |a k| := by
    calc (r : ℤ) * a k ≤ r * |a k| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ a₀ * |a k| := mul_le_mul_of_nonneg_right (by exact_mod_cast hr.le) (abs_nonneg _)
  have hbk : b k ≤ |b k| := le_abs_self _
  have hnq : (n : ℤ) ≤ ((n * q : ℕ) : ℤ) := by
    exact_mod_cast Nat.le_mul_of_pos_right n hq
  have hτ' : (τ : ℤ) = n * a₀ + r := by exact_mod_cast hτ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hτ']
  push_cast at hnq ⊢
  nlinarith

end GlobalTheory.CompanionTheory.NefSections

namespace GlobalTheory.CompanionTheory.NefSections

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem finrank_chartLatQ_nsmul_add_le : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ), 1 ≤ D → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) →
    Birational y → NefOnGenericDeg (mCoordIdeal y) a → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1) : ℝ) ≤
        ((genDeg (mCoordIdeal y) D a : ℝ) + ε) * (n : ℝ) ^ D / (D.factorial : ℝ) := by
  intro K _ ι _ Ω _ _ y D a b hD hV _ hN ε hε
  classical
  have : Nonempty K := hV.1
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  have hI : genIdeal y = mIdealOver ℚ y := LiftBirationalNef.genIdeal_eq y
  have hP := isProjVarF_map_of_isArithVar hV
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k =>
    (hV.2.1.2.2 k).imp fun i hi => LiftBirationalNef.coord_ne_zero_of_not_mem hi
  have hdim : FieldNumbers.relDim (mIdealOver ℚ y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    hI ▸ (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (d + 1)).2 hP.2
  have hnef : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.IsNef ℚ y a := fun W hW hle hW1 =>
    NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hN W
      ⟨(Bridge.isMultiProjPrime_iff W).mp hW, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
      (hI.le.trans hle)
  obtain ⟨hNP, hKl, -⟩ := PositivityTheory.HtPt.Ktw.k_twins PositivityTheory.HtPt.Kra.kleiman_input_universe_zero
  have hGdef : genDeg (mCoordIdeal y) (d + 1) a =
      NumbersDVR.intNum ℚ (mIdealOver ℚ y) (fun _ : Fin (d + 1) => a) := by
    rw [← hI]; rfl
  have hG0 : 0 ≤ genDeg (mCoordIdeal y) (d + 1) a := by
    rw [hGdef]; exact hNP ℚ K ι Ω y (d + 1) (fun _ => a) hnz hdim (fun _ => hnef)
  have hmod := (SegreBase.proof ℚ K ι Ω y hnz).1
  have hdim' : FieldNumbers.relDim (mIdealOver ℚ (segreJoin y)) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    (SegreDim.proof ℚ K ι Ω y hnz).trans hdim
  have hnef' : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.IsNef ℚ (segreJoin y) (pullDeg a) :=
    (SegreNef.proof SegreDim.proof SegreNum.proof ℚ K ι Ω y hnz a).2 hnef
  have hPr := isMultiProjPrime_mIdealOver (S := ℚ) (segreJoin y) hmod.1
  obtain ⟨f, hf⟩ := PositivityTheory.HtPt.Siub.exists_multilinear (M := Unit ⊕ K → ℤ) (n := d + 1)
    (fun v => NumbersDVR.intNum ℚ (mIdealOver ℚ (segreJoin y)) v)
    (FieldNumbers.IntNumAdd.full ℚ _ _ (mIdealOver ℚ (segreJoin y)) hPr.multiHomog hPr.relevant (d + 1) hdim')
  have hfa : f (fun _ => pullDeg a) = genDeg (mCoordIdeal y) (d + 1) a := by
    rw [hf, hGdef]
    exact SegreNum.proof ℚ K ι Ω y hnz (d + 1) (fun _ => a)
  obtain ⟨ε', hε'0, hε'⟩ : ∃ ε' : ℚ, 0 < ε' ∧ 2 * (ε' : ℝ) ≤ ε := by
    obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (half_pos hε)
    exact ⟨q, by exact_mod_cast hq0, by linarith⟩
  obtain ⟨t, ht, hbd⟩ := exists_rat_multilinear_le f (pullDeg a) (baseDeg (Sum.inl ())) ε' hε'0
  obtain ⟨a₀, m, ha₀, hm, hva⟩ := hKl (d + 1) ℚ (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) hmod hdim'
    (pullDeg a) hnef' t ht
  have hmpos : 0 < m := by
    have ha' : (0 : ℚ) < a₀ := by exact_mod_cast ha₀
    have : (0 : ℚ) < m := by rw [hm]; exact mul_pos ha' ht
    exact_mod_cast this
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hmpos.le
  have hq : 1 ≤ q := by exact_mod_cast hmpos
  obtain ⟨C, hC⟩ := finrank_secOver_nsmul_le ℚ (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) d _ hmod hdim' hva
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hC
  obtain ⟨B, hB⟩ := twist_le a b a₀
  have hsec : ∀ n : ℕ, secOver ℚ (segreJoin y) (n • (a₀ • pullDeg a + (q : ℤ) • baseDeg (Sum.inl ()))) =
      chartLatQ y (((n * a₀ : ℕ) : ℤ) • a + fun _ => ((n * q : ℕ) : ℤ)) 1 := by
    intro n
    rw [← secOver_eq_chartLatQ, ← SegreTwist.proof ℚ K ι Ω y hnz]
    congr 1
    funext k
    rcases k with k | k <;> simp [pullDeg, baseDeg, Pi.single_apply] <;> ring
  have hfc : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hXq : ((f (fun _ => a₀ • pullDeg a + (q : ℤ) • baseDeg (Sum.inl ())) : ℤ) : ℝ) ≤
      (a₀ : ℝ) ^ (d + 1) * ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) + (ε' : ℝ)) := by
    have h := hbd a₀ q ha₀ hm
    rw [hfa] at h
    exact_mod_cast h
  have hε'R : (0 : ℝ) < ε' := by exact_mod_cast hε'0
  obtain ⟨T₀, hT₀⟩ := exists_nat_ge (|C| * ((d + 1).factorial : ℝ) / (ε' : ℝ))
  filter_upwards [eventually_ge_atTop (a₀ * (max n₀ B + 1)), eventually_ge_atTop T₀] with τ hτ hτ₀
  have hdiv : max n₀ B + 1 ≤ τ / a₀ := (Nat.le_div_iff_mul_le ha₀).2 (by rwa [mul_comm] at hτ)
  have hn₁ : n₀ ≤ τ / a₀ := by omega
  have hB₁ : B ≤ τ / a₀ := by omega
  have h1τ : 1 ≤ τ := by
    have : 1 ≤ τ / a₀ := by omega
    exact le_trans this (Nat.div_le_self _ _)
  have hmono := GlobalTheory.CompanionTheory.ChartSections.finrank_chartLatQ_mono K ι Ω y _ _ hnz (hB τ q ha₀ hq hB₁)
    (GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ K ι Ω y (d + 1) _ hV)
  have hup := hn₀ (τ / a₀) hn₁
  rw [hsec, ← hf] at hup
  have hmonoR : (Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + b) 1) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y (((τ / a₀ * a₀ : ℕ) : ℤ) • a + fun _ => ((τ / a₀ * q : ℕ) : ℤ)) 1) : ℝ) := by
    exact_mod_cast hmono
  refine real_step d hfc (by exact_mod_cast hG0) hε'R hε' (A := (a₀ : ℝ)) (nR := ((τ / a₀ : ℕ) : ℝ)) (T := (τ : ℝ))
    (C := C) (by exact_mod_cast ha₀) (by positivity) ?_ hXq ?_ (by exact_mod_cast h1τ) (hmonoR.trans hup)
  · have : a₀ * (τ / a₀) ≤ τ := Nat.mul_div_le τ a₀
    exact_mod_cast this
  · have h1 : |C| * ((d + 1).factorial : ℝ) / (ε' : ℝ) ≤ τ := hT₀.trans (by exact_mod_cast hτ₀)
    rw [div_le_iff₀ hε'R] at h1
    linarith

end GlobalTheory.CompanionTheory.NefSections
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpperStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_dimension_upper : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ), 1 ≤ D → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnGenericDeg (mCoordIdeal y) a → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1) : ℝ) ≤ ((genDeg (mCoordIdeal y) D a : ℝ) + ε) * (n : ℝ) ^ D / (D.factorial : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le | exact GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le | (intros; apply GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankLeAddOfMem
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.NefLower

open PositivityTheory.HtPt.Siua in
theorem num_lower {M : Type} [AddCommGroup M] (d : ℕ)
    (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (d + 1) => M) ℤ) (μ e : M) (δ : ℚ) (hδ : 0 < δ) :
    ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t →
      ((f (fun _ => μ) : ℚ) - δ) * (a : ℚ) ^ (d + 1) ≤
        (f (fun _ => a • μ + m • e) : ℚ) - ((d + 1 : ℕ) : ℚ) *
          (f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) (m • e)) : ℚ) := by
  let x : Fin (d + 1) → ℤ := Fin.snoc (α := fun _ => ℤ) (fun _ : Fin d => 1) 0
  let g : ℚ → ℚ := fun t => form f μ e (fun _ => 1) (fun _ => 1 * t) -
    ((d + 1 : ℕ) : ℚ) * form f μ e (fun i => x i) (fun _ => 1 * t)
  have hg : Continuous g :=
    (form_cont f μ e (fun _ => 1) (fun _ => 1)).sub (continuous_const.mul (form_cont f μ e _ _))
  have hg0 : (f (fun _ => μ) : ℚ) - δ < g 0 := by
    have h1 := form_cast f μ e (fun _ => 1) (fun _ => 0)
    have h2 := form_cast f μ e x (fun _ => 0)
    have h3 : f (fun i => x i • μ + (0 : ℤ) • e) = 0 :=
      f.map_coord_zero (Fin.last d) (by simp [x])
    rw [h3] at h2
    simp only [one_smul, zero_smul, add_zero, Int.cast_one, Int.cast_zero] at h1 h2
    simp only [g, mul_zero]
    rw [← h1, ← h2, mul_zero, sub_zero]
    linarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℚ), (f (fun _ => μ) : ℚ) - δ < g t ∧ 0 < t :=
    ((hg.continuousAt.eventually (lt_mem_nhds hg0)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, hgt, ht⟩ := hev.exists
  refine ⟨t, ht, fun a m ha hm => ?_⟩
  have e1 : (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) (m • e)) =
      fun i => ((a : ℤ) * x i) • μ + m • e := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [x]
  have e2 : (fun _ : Fin (d + 1) => a • μ + m • e) = fun _ => (a : ℤ) • μ + m • e := by
    funext i; simp
  have h1 := form_cast f μ e (fun i => (a : ℤ) * x i) (fun _ => m)
  have h2 := form_cast f μ e (fun _ => (a : ℤ)) (fun _ => m)
  have h3 := form_smul f μ e (fun i => x i) (fun _ => 1 * t) a
  have h4 := form_smul f μ e (fun _ => 1) (fun _ => 1 * t) a
  have h5 : form f μ e (fun i => (((a : ℤ) * x i : ℤ) : ℚ)) (fun _ => ((m : ℤ) : ℚ)) =
      form f μ e (fun i => (a : ℚ) * x i) (fun _ => (a : ℚ) * (1 * t)) := by
    congr 1 <;> funext i <;> push_cast
    · rfl
    · rw [hm]; ring
  have h6 : form f μ e (fun _ => (((a : ℤ) : ℤ) : ℚ)) (fun _ => ((m : ℤ) : ℚ)) =
      form f μ e (fun _ => (a : ℚ) * 1) (fun _ => (a : ℚ) * (1 * t)) := by
    congr 1 <;> funext i <;> push_cast
    · ring
    · rw [hm]; ring
  have hapos : (0 : ℚ) < (a : ℚ) ^ (d + 1) := pow_pos (by exact_mod_cast ha) _
  have hfin := mul_lt_mul_of_pos_left hgt hapos
  rw [e1, e2, h1, h2, h5, h6, h3, h4]
  simp only [g] at hfin
  push_cast at hfin ⊢
  nlinarith [hfin]

theorem eventually_lower (f : ℕ → ℝ) (A C : ℝ) (hA : 0 ≤ A) (d a₀ L : ℕ) (ha : 1 ≤ a₀)
    (h : ∀ᶠ N : ℕ in atTop, ∃ m : ℕ, a₀ * m ≤ N ∧ N ≤ a₀ * m + L ∧
      A * (a₀ : ℝ) ^ (d + 1) * (m : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (m : ℝ) ^ d ≤ f N)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (A - ε) * (N : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤ f N := by
  have hfac : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast (d + 1).factorial_pos
  set C' : ℝ := max C 0 with hC'
  have hlim : Tendsto (fun N : ℕ => A * (1 - (L : ℝ) / N) ^ (d + 1) -
      ((d + 1).factorial : ℝ) * C' * (1 / (N : ℝ))) atTop (𝓝 (A * (1 - 0) ^ (d + 1) -
        ((d + 1).factorial : ℝ) * C' * 0)) := by
    have h0 : Tendsto (fun N : ℕ => (L : ℝ) / N) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have h1 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    exact (((tendsto_const_nhds.sub h0).pow (d + 1)).const_mul A).sub (h1.const_mul _)
  have hval : A * (1 - 0 : ℝ) ^ (d + 1) - ((d + 1).factorial : ℝ) * C' * 0 = A := by simp
  rw [hval] at hlim
  have hev := hlim.eventually (lt_mem_nhds (show A - ε < A by linarith))
  filter_upwards [h, hev, eventually_gt_atTop L, eventually_gt_atTop 0] with N ⟨m, hm1, hm2, hm3⟩ hN hNL hN0
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hNL' : (L : ℝ) < (N : ℝ) := by exact_mod_cast hNL
  have hfrac : (1 - (L : ℝ) / N) * N = N - L := by field_simp
  have hm1' : ((a₀ : ℝ) * m) ≤ N := by exact_mod_cast hm1
  have hm2' : (N : ℝ) ≤ a₀ * m + L := by exact_mod_cast hm2
  have ha' : (1 : ℝ) ≤ a₀ := by exact_mod_cast ha
  have hmN : (m : ℝ) ≤ N := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith
  have hpow : ((N : ℝ) - L) ^ (d + 1) ≤ ((a₀ : ℝ) * m) ^ (d + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hCm : C * (m : ℝ) ^ d ≤ C' * (N : ℝ) ^ d := by
    have h1 : (m : ℝ) ^ d ≤ (N : ℝ) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hmN _
    have h2 : C ≤ C' := le_max_left _ _
    have h3 : 0 ≤ C' := le_max_right _ _
    have h4 : (0 : ℝ) ≤ (m : ℝ) ^ d := by positivity
    nlinarith
  have hNpow : (0 : ℝ) < (N : ℝ) ^ (d + 1) := pow_pos hN' _
  have key := mul_lt_mul_of_pos_right hN hNpow
  have e1 : (A * (1 - (L : ℝ) / N) ^ (d + 1) - ((d + 1).factorial : ℝ) * C' * (1 / (N : ℝ))) * (N : ℝ) ^ (d + 1) =
      A * ((N : ℝ) - L) ^ (d + 1) - ((d + 1).factorial : ℝ) * C' * (N : ℝ) ^ d := by
    rw [← hfrac, mul_pow, pow_succ (N : ℝ) d]
    field_simp
  rw [e1] at key
  have e2 : A * (a₀ : ℝ) ^ (d + 1) * (m : ℝ) ^ (d + 1) = A * ((a₀ : ℝ) * m) ^ (d + 1) := by
    rw [mul_pow]; ring
  rw [e2] at hm3
  have hAp := mul_le_mul_of_nonneg_left hpow hA
  rw [div_le_iff₀ hfac]
  have hm4 : A * ((a₀ : ℝ) * m) ^ (d + 1) - ((d + 1).factorial : ℝ) * (C * (m : ℝ) ^ d) ≤
      f N * ((d + 1).factorial : ℝ) := by
    have := mul_le_mul_of_nonneg_right hm3 hfac.le
    rw [sub_mul, div_mul_cancel₀ _ hfac.ne'] at this
    linarith
  have hCm' := mul_le_mul_of_nonneg_left hCm hfac.le
  nlinarith

section Sections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem chartLatQ_eq_secOver (y : (Σ k, ι k) → Ω) (β : K → ℤ) :
    chartLatQ y β 1 = KH.secOver ℚ y β := by
  ext s
  simp only [KH.secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h c hc
    have h1 := h c hc
    simp only [Nat.cast_one, one_mul] at h1
    exact h1
  · intro h c hc
    show s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * β k)) ∈ chartRingQ y c
    simp only [Nat.cast_one, one_mul]
    exact h c hc

theorem finrank_le_add_of_mem (y : (Σ k, ι k) → Ω) (β γ : K → ℤ) (e : Ω) (he0 : e ≠ 0)
    (he : e ∈ chartLatQ y γ 1) (hfd : FiniteDimensional ℚ (chartLatQ y (β + γ) 1)) :
    Module.finrank ℚ (chartLatQ y β 1) ≤ Module.finrank ℚ (chartLatQ y (β + γ) 1) := by
  have hmem : ∀ s ∈ chartLatQ y β 1, s * e ∈ chartLatQ y (β + γ) 1 := by
    intro s hs
    rw [chartLatQ_eq_secOver] at hs he ⊢
    exact GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelTwistGenerated.secOver_mul y hs he
  let g : chartLatQ y β 1 →ₗ[ℚ] chartLatQ y (β + γ) 1 :=
    { toFun := fun s => ⟨s.1 * e, hmem s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r s => Subtype.ext (smul_mul_assoc _ _ _) }
  refine LinearMap.finrank_le_finrank_of_injective (f := g) fun s t hst => ?_
  exact Subtype.ext (mul_right_cancel₀ he0 (congrArg Subtype.val hst))

theorem pow_mem_chartLatQ (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (e : Ω) (he : e ∈ chartLatQ y γ 1) (c : ℕ) :
    e ^ c ∈ chartLatQ y ((c : ℤ) • γ) 1 := by
  rw [chartLatQ_eq_secOver] at he ⊢
  exact GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelTwistGenerated.pow_mem_secOver y he c

end Sections


open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization in
theorem count_lower (hK : VeryAmpleNefPlusAmple.Statement) (hS : SectionCount.Statement)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ) (a : K → ℤ) (hV : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1 + 1))
    (hN : NefOnGenericDeg (mCoordIdeal y) a) (δ : ℚ) (hδ : 0 < δ) :
    ∃ (a₀ : ℕ) (C : ℝ), 1 ≤ a₀ ∧ ∀ n : ℕ, 1 ≤ n →
      ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) - (δ : ℝ)) * (a₀ : ℝ) ^ (d + 1) * (n : ℝ) ^ (d + 1) /
          ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤
        (Module.finrank ℚ (chartLatQ y (((n * a₀ : ℕ) : ℤ) • a) 1) : ℝ) := by
  let _ : DecidableEq K := fun x y => Classical.propDecidable (x = y)
  have : Nonempty K := hV.1
  have hI : KH.genIdeal y = KH.mIdealOver ℚ y := LiftBirationalNef.genIdeal_eq y
  have hP := isProjVarF_map_of_isArithVar hV
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k =>
    (hV.2.1.2.2 k).imp fun i hi => LiftBirationalNef.coord_ne_zero_of_not_mem hi
  have hdim : FieldNumbers.relDim (KH.mIdealOver ℚ y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    hI ▸ (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (d + 1)).2 hP.2
  have hnef : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.IsNef ℚ y a := fun W hW hle hW1 =>
    NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hN W
      ⟨(Bridge.isMultiProjPrime_iff W).mp hW, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
      (hI.le.trans hle)
  have hmodel := (SegreBase.proof ℚ K ι Ω y hnz).1
  have hdim' := (SegreDim.proof ℚ K ι Ω y hnz).trans hdim
  have hnef' := (SegreNef.proof SegreDim.proof SegreNum.proof ℚ K ι Ω y hnz a).2 hnef
  have hPr := isMultiProjPrime_mIdealOver (S := ℚ) (segreJoin y) hmodel.1
  obtain ⟨f, hf⟩ := PositivityTheory.HtPt.Siub.exists_multilinear (M := Unit ⊕ K → ℤ) (n := d + 1)
    (fun v => NumbersDVR.intNum ℚ (KH.mIdealOver ℚ (segreJoin y)) v)
    (FieldNumbers.IntNumAdd.full ℚ (Unit ⊕ K) _ (KH.mIdealOver ℚ (segreJoin y)) hPr.multiHomog
      hPr.relevant (d + 1) hdim')
  obtain ⟨t, ht, hlt⟩ := num_lower d f (pullDeg a) (baseDeg (Sum.inl ())) δ hδ
  obtain ⟨a₀, m, ha, hm, hva⟩ := hK (d + 1) ℚ _ _ Ω (segreJoin y) (Sum.inl ()) hmodel hdim'
    (pullDeg a) hnef' t ht
  have hmpos : 0 < m := by
    have ha' : (0 : ℚ) < a₀ := by exact_mod_cast ha
    have : (0 : ℚ) < m := by rw [hm]; exact mul_pos ha' ht
    exact_mod_cast this
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hmpos.le
  have hr : 0 < r := by exact_mod_cast hmpos
  obtain ⟨C, hC⟩ := hS ℚ (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) d
    (a₀ • pullDeg a + (r : ℤ) • baseDeg (Sum.inl ())) r hmodel hdim' hva (by omega)
  refine ⟨a₀, C, ha, fun n hn => ?_⟩
  have h1 := hC n hn
  have e : n • (a₀ • pullDeg (K₁ := Unit) a + (r : ℤ) • baseDeg (Sum.inl ()) - r • baseDeg (Sum.inl ())) =
      pullDeg (K₁ := Unit) (((n * a₀ : ℕ) : ℤ) • a) := by
    funext k
    cases k <;> simp [pullDeg]
    ring
  rw [e, (SegreBase.proof ℚ K ι Ω y hnz).2.1, ← chartLatQ_eq_secOver] at h1
  have hlt' := hlt a₀ (r : ℤ) ha hm
  rw [hf, hf, hf] at hlt'
  have hG : NumbersDVR.intNum ℚ (KH.mIdealOver ℚ (segreJoin y)) (fun _ : Fin (d + 1) => pullDeg a) =
      genDeg (mCoordIdeal y) (d + 1) a := by
    rw [SegreNum.proof ℚ K ι Ω y hnz (d + 1) (fun _ => a), ← hI]
    rfl
  rw [hG] at hlt'
  have hq : ((r : ℤ)) • baseDeg (K := Unit ⊕ K) (Sum.inl ()) = r • baseDeg (Sum.inl ()) := by
    rw [← natCast_zsmul]
  rw [← hq] at h1
  have hR : ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) - (δ : ℝ)) * (a₀ : ℝ) ^ (d + 1) ≤
      (NumbersDVR.intNum ℚ (KH.mIdealOver ℚ (segreJoin y))
        (fun _ : Fin (d + 1) => a₀ • pullDeg a + (r : ℤ) • baseDeg (Sum.inl ())) : ℝ) -
      ((d + 1 : ℕ) : ℝ) * (NumbersDVR.intNum ℚ (KH.mIdealOver ℚ (segreJoin y))
        (Fin.snoc (α := fun _ => Unit ⊕ K → ℤ)
          (fun _ : Fin d => a₀ • pullDeg a + (r : ℤ) • baseDeg (Sum.inl ()))
          ((r : ℤ) • baseDeg (Sum.inl ()))) : ℝ) := by
    exact_mod_cast (Rat.cast_le (K := ℝ)).2 hlt'
  have hfac : (0 : ℝ) ≤ (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by positivity
  have h2 := mul_le_mul_of_nonneg_right hR hfac
  simp only [mul_div_assoc] at h1 ⊢
  linarith


open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 in
theorem lower_of_pos (hK : VeryAmpleNefPlusAmple.Statement) (hS : SectionCount.Statement)
    (hKod : KodairaGeneric.Statement)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ) (a b : K → ℤ) (hV : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1 + 1))
    (hB : Birational y) (hN : NefOnGenericDeg (mCoordIdeal y) a) (ε : ℝ) (hε : 0 < ε)
    (hpos : ε < (genDeg (mCoordIdeal y) (d + 1) a : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) - ε) * (N : ℝ) ^ (d + 1) /
        ((d + 1).factorial : ℝ) ≤ (Module.finrank ℚ (chartLatQ y ((N : ℤ) • a + b) 1) : ℝ) := by
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k =>
    (hV.2.1.2.2 k).imp fun i hi => LiftBirationalNef.coord_ne_zero_of_not_mem hi
  obtain ⟨δ, hδ0, hδ1⟩ := exists_rat_btwn hε
  have hδ0' : 0 < δ := by exact_mod_cast hδ0
  obtain ⟨a₀, C, ha, hcount⟩ := count_lower hK hS K ι Ω y d a hV hN δ hδ0'
  have hGpos : 0 < genDeg (mCoordIdeal y) (d + 1) a := by
    have : (0 : ℝ) < (genDeg (mCoordIdeal y) (d + 1) a : ℝ) := hε.trans hpos
    exact_mod_cast this
  obtain ⟨k, e, hk, he0, he⟩ := hKod K ι Ω y (d + 1) a (by omega) hV hB hN hGpos
  obtain ⟨B, hB'⟩ : ∃ B : ℕ, ∀ r : ℕ, r < a₀ → ∀ κ, -(B : ℤ) ≤ (r : ℤ) * a κ + b κ := by
    refine ⟨∑ κ, (a₀ * (a κ).natAbs + (b κ).natAbs), fun r hr κ => ?_⟩
    have h1 : a₀ * (a κ).natAbs + (b κ).natAbs ≤ ∑ κ, (a₀ * (a κ).natAbs + (b κ).natAbs) :=
      Finset.single_le_sum (f := fun κ => a₀ * (a κ).natAbs + (b κ).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)
    have h1' : (a₀ : ℤ) * |a κ| + |b κ| ≤ ((∑ κ, (a₀ * (a κ).natAbs + (b κ).natAbs) : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
      exact_mod_cast h1
    have h2 : -|b κ| ≤ b κ := neg_abs_le _
    have h3 : -|a κ| ≤ a κ := neg_abs_le _
    have h4 : (r : ℤ) ≤ a₀ := by exact_mod_cast hr.le
    have h5 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
    have h6 : (0 : ℤ) ≤ |a κ| := abs_nonneg _
    nlinarith
  have ha0 : 0 < a₀ := ha
  have hmain := eventually_lower
    (fun N : ℕ => (Module.finrank ℚ (chartLatQ y ((N : ℤ) • a + b) 1) : ℝ))
    ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) - (δ : ℝ)) C (by linarith) d a₀ (a₀ * (B * k) + a₀) ha ?_
    (ε - δ) (by linarith)
  · have e' : (genDeg (mCoordIdeal y) (d + 1) a : ℝ) - (δ : ℝ) - (ε - δ) =
        (genDeg (mCoordIdeal y) (d + 1) a : ℝ) - ε := by ring
    rw [e'] at hmain
    exact hmain
  · filter_upwards [eventually_ge_atTop (a₀ * (B * k + 1))] with N hN1
    have hNr : a₀ * (N / a₀) + N % a₀ = N := Nat.div_add_mod N a₀
    have hr : N % a₀ < a₀ := Nat.mod_lt _ ha0
    have hn : B * k + 1 ≤ N / a₀ := (Nat.le_div_iff_mul_le ha0).2 (by rw [Nat.mul_comm]; exact hN1)
    obtain ⟨m, hm⟩ : ∃ m, N / a₀ = m + B * k := ⟨N / a₀ - B * k, by omega⟩
    have hm1 : 1 ≤ m := by omega
    have hmul : a₀ * (N / a₀) = a₀ * m + a₀ * (B * k) := by rw [hm, Nat.mul_add]
    refine ⟨m, by omega, by omega, ?_⟩
    refine (hcount m hm1).trans ?_
    have hce := pow_mem_chartLatQ y ((k : ℤ) • a - 1) e he (a₀ * B)
    have hfd := fun β => GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ K ι Ω y (d + 1) β hV
    have s1 := finrank_le_add_of_mem y (((m * a₀ : ℕ) : ℤ) • a) (((a₀ * B : ℕ) : ℤ) • ((k : ℤ) • a - 1))
      (e ^ (a₀ * B)) (pow_ne_zero _ he0) hce (hfd _)
    have hle : (((m * a₀ : ℕ) : ℤ) • a + ((a₀ * B : ℕ) : ℤ) • ((k : ℤ) • a - 1)) ≤ (N : ℤ) • a + b := by
      intro κ
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
      have hNz : (N : ℤ) = (a₀ : ℤ) * (m + B * k) + ((N % a₀ : ℕ) : ℤ) := by
        have : N = a₀ * (m + B * k) + N % a₀ := by rw [← hm]; exact hNr.symm
        exact_mod_cast this
      have hb := hB' (N % a₀) hr κ
      have hBB : (B : ℤ) ≤ (a₀ : ℤ) * B := by
        have : B ≤ a₀ * B := Nat.le_mul_of_pos_left _ ha0
        exact_mod_cast this
      have hdiff : (N : ℤ) * a κ + b κ - (((m * a₀ : ℕ) : ℤ) * a κ + ((a₀ * B : ℕ) : ℤ) * ((k : ℤ) * a κ - 1)) =
          ((N % a₀ : ℕ) : ℤ) * a κ + b κ + (a₀ : ℤ) * B := by
        rw [hNz]; push_cast; ring
      linarith
    have s2 := GlobalTheory.CompanionTheory.ChartSections.finrank_chartLatQ_mono K ι Ω y _ ((N : ℤ) • a + b) hnz hle (hfd _)
    exact_mod_cast s1.trans s2

theorem nef_sections_lower : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ), 1 ≤ D → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnGenericDeg (mCoordIdeal y) a → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ((genDeg (mCoordIdeal y) D a : ℝ) - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1) : ℝ) := by
  intro K _ ι _ Ω _ _ y D a b hD hV hB hN ε hε
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  by_cases hG : (genDeg (mCoordIdeal y) (d + 1) a : ℝ) ≤ ε
  · refine Eventually.of_forall fun n => ?_
    have h1 : ((genDeg (mCoordIdeal y) (d + 1) a : ℝ) - ε) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) (by positivity)
    exact h1.trans (Nat.cast_nonneg _)
  · obtain ⟨-, hK, hS⟩ := PositivityTheory.HtPt.Ktw.k_twins PositivityTheory.HtPt.Kra.kleiman_input_universe_zero
    exact lower_of_pos hK hS (PositivityTheory.HtPt.Siua.siu_kodaira hK hS) K ι Ω y d a b hV hB hN ε hε
      (not_le.mp hG)

end GlobalTheory.CompanionTheory.NefLower
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoOfAsymptoticBoundsStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoOfAsymptoticBounds
open Filter Topology

namespace GlobalTheory.CompanionTheory.Analysis

theorem tendsto_factorial_mul_div_pow_of_eps_bounds (f : ℕ → ℝ) (G : ℝ) (D : ℕ)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) :
    Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by
  have hfac : (0 : ℝ) < (D.factorial : ℝ) := by exact_mod_cast D.factorial_pos
  have hev : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hl ((G - a) / 2) (by linarith), hev] with n hn hp
    rw [div_le_iff₀ hfac] at hn
    have key : G - (G - a) / 2 ≤ (D.factorial : ℝ) * f n / (n : ℝ) ^ D := by
      rw [le_div_iff₀ hp]
      linarith
    linarith
  · filter_upwards [hu ((b - G) / 2) (by linarith), hev] with n hn hp
    rw [le_div_iff₀ hfac] at hn
    have key : (D.factorial : ℝ) * f n / (n : ℝ) ^ D ≤ G + (b - G) / 2 := by
      rw [div_le_iff₀ hp]
      linarith
    linarith

end GlobalTheory.CompanionTheory.Analysis
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_of_asymptotic_bounds : ∀ (f : ℕ → ℝ) (G : ℝ) (D : ℕ), (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n) → (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) → Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by
  first | exact @GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds | exact GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds | (intros; apply GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds <;> assumption)
end

namespace PositivityTheory.Tls2.Nef

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem nefRR : GlobalTheory.CompanionTheory.Ar.Pub.NefRR := by
  intro K _ ι _ Ω _ _ y D a hV hB hN
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel.nefRR_dimZero y a hV hB
  obtain ⟨e, c, hc, hmem⟩ := GlobalTheory.T.chart_lattice_span_twist_shift K ι Ω y D hV hB
  have hinj : Function.Injective (LinearMap.mulLeft ℚ c) := mul_right_injective₀ hc
  have hle : ∀ τ : ℕ, (Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c) ≤
      chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
    intro τ
    rintro _ ⟨s, hs, rfl⟩
    exact hmem a τ s hs
  have hfd : ∀ τ : ℕ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := by
    intro τ
    haveI := GlobalTheory.T.finiteDimensional_chart_lattice K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV
    haveI : FiniteDimensional ℚ ((Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c)) :=
      Submodule.finiteDimensional_of_le (hle τ)
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hinj _).symm
  have hup : ∀ τ : ℕ, Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) ≤
      Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1) := by
    intro τ
    haveI := GlobalTheory.T.finiteDimensional_chart_lattice K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV
    rw [(Submodule.equivMapOfInjective _ hinj (Submodule.span ℚ (chartLatNm y a τ : Set Ω))).finrank_eq]
    exact Submodule.finrank_mono (hle τ)
  have hlow : ∀ τ : ℕ, Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + 0) 1) ≤
      Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := by
    intro τ
    haveI := hfd τ
    have hsub : chartLatQ y ((τ : ℤ) • a + 0) 1 ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
      rw [add_zero, ← chartLatQ_eq_smul_one]
      exact GlobalTheory.T.chart_lattice_le_span_norm K ι Ω y a τ
    exact Submodule.finrank_mono hsub
  refine ⟨hfd, ?_⟩
  apply GlobalTheory.T.tendsto_of_asymptotic_bounds (fun τ => (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ)) _ D
  · intro ε hε
    filter_upwards [GlobalTheory.CompanionTheory.NefLower.nef_sections_lower K ι Ω y D a 0 hD hV hB hN ε hε] with n hn
    exact hn.trans (by exact_mod_cast hlow n)
  · intro ε hε
    filter_upwards [GlobalTheory.T.chart_lattice_dimension_upper K ι Ω y D a (fun k => (e k : ℤ)) hD hV hB hN ε hε] with n hn
    exact le_trans (by exact_mod_cast hup n) hn

end PositivityTheory.Tls2.Nef
