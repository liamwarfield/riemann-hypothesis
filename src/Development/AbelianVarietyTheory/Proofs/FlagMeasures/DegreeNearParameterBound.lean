module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BigCellMemUnitary
open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory

namespace BigCellUnitary

def pos (k r : ℕ) : (Fin r ⊕ Fin r) ⊕ Fin (k + 1) → Fin (2 * r + k + 1) :=
  Sum.elim (Sum.elim (eI k r) (esI k r)) (wI k r)

theorem pos_bijective (k r : ℕ) : Function.Bijective (pos k r) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp; omega⟩
  rintro ((a | a) | a) ((b | b) | b) h <;>
    simp only [pos, eI, esI, wI, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    first
      | (exfalso; omega)
      | (have : a = b := Fin.ext (by omega); rw [this])

def posEquiv (k r : ℕ) : (Fin r ⊕ Fin r) ⊕ Fin (k + 1) ≃ Fin (2 * r + k + 1) :=
  Equiv.ofBijective _ (pos_bijective k r)

theorem gram_submatrix (k r : ℕ) :
    (Hpk k r).submatrix (pos k r) (pos k r) =
      fromBlocks (fromBlocks 0 1 1 0) 0 0 (Hb k) := by
  ext ((a | a) | a) ((b | b) | b) <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    simp only [pos, eI, esI, wI, Hpk, Hb, Sum.elim_inl, Sum.elim_inr, submatrix_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.one_apply, diagonal_apply, Fin.ext_iff, Fin.val_last] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | contradiction | (exfalso; simp_all; done) |
      (rename_i h1 h2
       first
        | exact (if_pos h2).trans (by rw [if_pos (by omega), if_pos (by omega)])
        | exact (if_neg h2).trans (by rw [if_pos (by omega), if_neg (by omega)]))

theorem col_e (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin r) :
    bigCell k r c μ i (eI k r b) = if i.val = 2 * r + k - b.val then c b else 0 := by
  have hb : (eI k r b).val < r := b.isLt
  unfold bigCell
  rw [dite_eq_left hb]
  exact if_congr Fin.ext_iff rfl rfl

theorem col_w (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin (k + 1)) :
    bigCell k r c μ i (wI k r b) =
      if hi : r ≤ i.val ∧ i.val ≤ r + k then μ ⟨i.val - r, by omega⟩ b else 0 := by
  have hb := b.isLt
  have hv : (wI k r b).val = r + b.val := rfl
  unfold bigCell
  rw [dif_neg (by omega), dite_eq_left (by omega)]
  split_ifs
  · congr 1
    apply Fin.ext
    show (wI k r b).val - r = b.val
    omega
  · rfl

theorem col_es (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin r) :
    bigCell k r c μ i (esI k r b) = if i.val = b.val then (star (c b))⁻¹ else 0 := by
  have hb := b.isLt
  have hv : (esI k r b).val = 2 * r + k - b.val := rfl
  unfold bigCell
  rw [dif_neg (by omega), dif_neg (by omega)]
  refine if_congr (by omega) ?_ rfl
  congr 3
  apply Fin.ext
  show 2 * r + k - (esI k r b).val = b.val
  omega

theorem bigCell_submatrix (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (bigCell k r c μ).submatrix (pos k r) (pos k r) =
      fromBlocks (fromBlocks 0 (diagonal fun a => (star (c a))⁻¹) (diagonal c) 0) 0 0 μ := by
  ext ((a | a) | a) ((b | b) | b) <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    simp only [pos, Sum.elim_inl, Sum.elim_inr, submatrix_apply, col_e, col_w, col_es,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, diagonal_apply]
  · exact if_neg (by show ¬ a.val = _; omega)
  · have : ((eI k r a).val = b.val) ↔ a = b := (Fin.ext_iff (a := a) (b := b)).symm
    exact (if_congr this rfl rfl).trans (by split_ifs with h <;> simp [h])
  · exact dif_neg (by show ¬ (r ≤ a.val ∧ _); omega)
  · have : ((esI k r a).val = 2 * r + k - b.val) ↔ a = b := by
      rw [Fin.ext_iff]; show 2 * r + k - a.val = _ ↔ _; omega
    exact (if_congr this rfl rfl).trans (by split_ifs with h <;> simp [h])
  · exact if_neg (by show ¬ 2 * r + k - a.val = _; omega)
  · exact dif_neg (by show ¬ (_ ∧ 2 * r + k - a.val ≤ _); omega)
  · exact if_neg (by show ¬ r + a.val = _; omega)
  · exact if_neg (by show ¬ r + a.val = _; omega)
  · rw [dite_eq_left (by show r ≤ r + a.val ∧ r + a.val ≤ _; omega)]
    congr 1
    apply Fin.ext
    show r + a.val - r = a.val
    omega

end BigCellUnitary


open BigCellUnitary in
theorem bigCell_mem_unitary : Formalism.QuantumDeterminants.BigCellMem := by
  intro k r c μ hc hμ
  change (bigCell k r c μ)ᴴ * Hpk k r * bigCell k r c μ = Hpk k r
  let e := BigCellUnitary.posEquiv k r
  have key : ((bigCell k r c μ)ᴴ * Hpk k r * bigCell k r c μ).submatrix e e =
      (Hpk k r).submatrix e e := by
    rw [← submatrix_mul_equiv _ _ _ e, ← submatrix_mul_equiv _ _ _ e,
      ← conjTranspose_submatrix]
    have hp : ⇑e = BigCellUnitary.pos k r := rfl
    rw [hp, BigCellUnitary.gram_submatrix, BigCellUnitary.bigCell_submatrix]
    have h1 : diagonal (fun a => star (c a)) * diagonal (fun a => (star (c a))⁻¹) =
        (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext a
      exact mul_inv_cancel₀ (star_ne_zero.2 (hc a))
    have h2 : diagonal (fun a => star (star (c a))⁻¹) * diagonal c =
        (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext a
      rw [star_inv₀, star_star]
      exact inv_mul_cancel₀ (hc a)
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_zero, diagonal_conjTranspose,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add, hμ]
    rw [show star c = fun a => star (c a) from rfl,
      show star (fun a => (star (c a))⁻¹) = fun a => star (star (c a))⁻¹ from rfl, h1, h2]
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  exact congrFun (congrFun key i) j

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DegreeNearParameterBound
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OpenCellNorm

theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = ‖t‖ ^ 2 * hsNormSq A := by
  have h : hsInner (t • A) (t • A) = ((‖t‖ ^ 2 : ℝ) : ℂ) * hsInner A A := by
    simp only [hsInner, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsNormSq, h, Complex.re_ofReal_mul, hsNormSq]

theorem bigCell_mem_of_weight {k r : ℕ} (hk : 2 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ}
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : IsSection k r z z' μsec) {q : (Fin r → ℂ) × ℂ}
    (hq : bcWeight k r (Tz k r z) (Tz k r z') q ≠ 0) : bigCell k r q.1 (μsec q.2) ∈ UH (Hpk k r) := by
  unfold bcWeight at hq
  split_ifs at hq with h
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hq
    refine GlobalTheory.bigCell_mem_unitary k r _ _ (fun a ha => ?_) (hs.2 _ (lt_of_le_of_ne h fun e => ?_)).1
    · refine Finset.prod_ne_zero_iff.1 h1 a (Finset.mem_univ a) ?_
      rw [ha, norm_zero]
      exact zero_pow (by unfold Mdim; omega)
    · rw [e, sub_self] at h2
      exact h2 (zero_pow (by omega))
  · exact absurd rfl hq

theorem lintegral_weight_smul {k r : ℕ} (hk : 2 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ}
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : IsSection k r z z' μsec)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {J J' : MatKR k r → (Wq →L[ℂ] Wp)} {η : ℂ} (h : ∀ γ ∈ UH (Hpk k r), J γ = η • J' γ) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q *
        hsNormSq (J (bigCell k r q.1 (μsec q.2)))) =
      ENNReal.ofReal (‖η‖ ^ 2) * ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q *
        hsNormSq (J' (bigCell k r q.1 (μsec q.2)))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  by_cases hq : bcWeight k r (Tz k r z) (Tz k r z') q = 0
  · simp [hq]
  · rw [h _ (bigCell_mem_of_weight hk hs hq), hsNormSq_smul, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm]

theorem exists_bessel_scale (hH : Hyps) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)}
    {u : ℕ → ℝ} {c : ℂ} {μW μN μG νq : Measure (Mt k r)} (hc : c ≠ 0) (hS : SideG k r z π u μW μN μG νq)
    {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ} (R : Rep k r) (hR : R.IsDS ε mu)
    (hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ) (hg : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) :
    ∃ l : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l ∧
      ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x) := by
  obtain ⟨t, ht, hN, hz, -⟩ := GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter k r c hc
  obtain ⟨-, hW, hψ⟩ := hz z hS.1
  obtain ⟨hS', hm⟩ := GlobalTheory.T.torus_normaliser_bessel hH k r Wp z π u c μW μN μG νq t ht hN hW hψ hS
  obtain ⟨l₁, hl⟩ := GlobalTheory.exists_normalised_bessel_map hH k r ε mu h R Wp _ _ _ _ _ _ _ hR hg hok hS'
  obtain ⟨h1, h2⟩ := hm R hU
  refine ⟨fun v => l₁ (R.σ t⁻¹ v), (h1 _).2 ?_, h2 l₁ hl⟩
  have e : (fun v => l₁ (R.σ t⁻¹ (R.σ t v))) = l₁ := by
    funext v
    have h3 := hU.1.2 _ (PI.HwUniqW.inv_mem_UH ht) _ ht
    rw [show t⁻¹ * t = 1 from PI.HwUniqW.inv_mul_UH' ht, hU.1.1] at h3
    exact congrArg l₁ (congrArg (fun T : R.H →L[ℂ] R.H => T v) h3).symm
  show IsBes R z π (fun v => l₁ (R.σ t⁻¹ (R.σ t v)))
  rw [e]
  exact hl.1

theorem norm_eq_const_div_deg : Hyps → AmpKF → CellConv → ∀ Cg cb Cu cT CT C0 C1 Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∃ K : ℝ, 0 < K ∧ ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A → MMv D w w' A μsec = ENNReal.ofReal (K / A.deg) := by
  intro hH hKF hCC Cg cb Cu cT CT C0 C1 Cn
  refine ⟨Cn, fun D large₂ C' Cl hCl hBig hcd hZ τ w w' hTT θ hθw W hW μsec hsec => ?_⟩
  by_cases hex : ∃ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A
  swap
  · exact ⟨1, one_pos, fun lam' _ A hA => absurd ⟨lam', A, hA⟩ hex⟩
  obtain ⟨lam₀, A₀, hA₀⟩ := hex
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  have hθ : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos (Real.exp_pos _) _) hθw.1
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv : 0 < D.host.v := by linarith
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hv
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hkg : 0 < D.host.ka / gg D := div_pos hka (mul_pos hg0 hg1)
  have hc : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  have hT : 0 < Tr D w := by unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by unfold Tr; exact_mod_cast hTT.2.1.pos
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hκN : kapN D θ ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨-, -, -, o1, o2⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam₀ A₀ hθ hv hTT hW hA₀
  have n1' : 0 < Module.finrank ℂ W.Wp := by haveI := o1.2.2.1; exact Module.finrank_pos
  have n2' : 0 < Module.finrank ℂ W.Wq := by haveI := o2.2.2.1; exact Module.finrank_pos
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := o1.2.2.2.2.2.2.2.2.1
  obtain ⟨κ, hκ, hdeg⟩ := GlobalTheory.T.formal_degree_proportional hH D τ w w' θ W hcd hW
  obtain ⟨c, hc0, hnorm⟩ := GlobalTheory.T.uniform_bessel_constant hH hKF hCC _ _ (toBessel D τ w w' θ W lam₀ A₀ hW hA₀ hT hT') W.μG μsec hk hc
    hκN ENNReal.ofReal_ne_top hW.2.2.2.2.2.2.1 hsec
  have hW' := hW
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW'
  let sq : (Fin D.R.k → ℝ) → ℕ → ℝ := fun u n => if h : n - 1 < D.R.k then u ⟨n - 1, h⟩ else 0
  have hsq : ∀ u (i : Fin D.R.k), sq u (i.val + 1) = u i := fun u i => by simp [sq]
  have s1 : SideG D.R.k D.R.rS W.z W.π (sq (uS D w τ)) W.μW W.μN W.μG W.νS :=
    ⟨z1, t1 ▸ hT, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z1 (t1 ▸ hT) c1 (hsq _), w1, hNH, hG, q1⟩
  have s2 : SideG D.R.k D.R.rS W.z' W.π' (sq (uS D w' τ)) W.μW' W.μN W.μG W.νS' :=
    ⟨z2, t2 ▸ hT', ⟨_, c2⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z2 (t2 ▸ hT') c2 (hsq _), w2, hNH, hG, q2⟩
  obtain ⟨hNum, hcell, heps⟩ := GlobalTheory.T.momentPieriNumerics_of_sizeHyps D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w _ (hsq _)
  obtain ⟨⟨-, -, -, -, hok⟩, hν⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hNum
  refine ⟨c * κ * (Module.finrank ℂ W.Wp * Module.finrank ℂ W.Wq), by positivity, fun lam' hl A hA => ?_⟩
  obtain ⟨ν, hlam, hn1, -⟩ := GlobalTheory.hcParam_sub_integral _ (lamD D τ) lam' hNum.2.1 hA.1
  have hq : n1 ν ≤ D.R.k * D.R.m ^ 5 := by
    have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
    have h1 : Cn ≤ (D.R.m : ℝ) ^ 2 := by have := hBig.2.2; nlinarith
    have h2 : ((n1 ν : ℕ) : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 5 := by
      rw [hn1]
      calc _ ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 := hl
        _ ≤ (D.R.m : ℝ) ^ 2 * D.R.k * (D.R.m : ℝ) ^ 3 := by gcongr
        _ = _ := by ring
    exact_mod_cast h2
  have hgap : GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) := by
    rw [hlam, ← heps]; exact (hν ν hq).2.2.1
  have hDS : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).IsDS (epsSH D.R) lam' := ⟨hA.1, hA.2.1⟩
  have hU := (GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam' A hθ hv hTT hW hA).1
  obtain ⟨l, b1, e1⟩ := exists_bessel_scale hH hc s1 ⟨A.H, A.σ⟩ hDS hU hgap hok
  obtain ⟨l', b2, e2⟩ := exists_bessel_scale hH hc s2 ⟨A.H, A.σ⟩ hDS hU hgap hok
  obtain ⟨k1, k2, w0, η, hw0, hη, hJ⟩ :=
    GlobalTheory.T.bessel_period_positivity hH D τ w w' θ W lam' A _ l l' hθ hkg hT hT' hW hA hgap hok b1 b2 e1 e2
  have hw0' : w0 ≠ 0 := by
    obtain ⟨P, -, h1, -⟩ := hw0
    rintro rfl
    simp at h1
  obtain ⟨d1, d2⟩ := hdeg lam' A hA w0 hw0'
  have hd : 0 < PI.BesselPeriodGGP.fdegH W.μG A.σ w0 := by
    rw [d1] at d2; exact (mul_pos_iff_of_pos_left hκ).1 d2
  rw [hN] at e1 e2
  have key := hnorm ⟨A.H, A.σ⟩ lam' _ l l' w0 hDS hgap hok hcell e1 e2 k1 k2 hw0
  have h5 := lintegral_weight_smul hk hsec (J := A.J W.μG)
    (J' := amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 W.μG) (η := η) fun γ hγ => hJ W.μG γ hγ hG.2.2.1
  unfold MMv
  rw [← t1, ← t2, h5]
  refine (congrArg _ key).trans ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _), hη, mul_pow, Real.sq_sqrt (by positivity), d1]
  congr 1
  show _ * (c / PI.BesselPeriodGGP.fdegH W.μG A.σ w0 ^ 3) = _
  field_simp

end GlobalTheory.Amp.OpenCellNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DegreeNearParameterBoundStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mmv_eq_const_div_deg_of_near_parameter : Hyps → AmpKF → CellConv → ∀ Cg cb Cu cT CT C0 C1 Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∃ K : ℝ, 0 < K ∧ ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A → MMv D w w' A μsec = ENNReal.ofReal (K / A.deg) := by
  first | exact @GlobalTheory.Amp.OpenCellNorm.norm_eq_const_div_deg | exact GlobalTheory.Amp.OpenCellNorm.norm_eq_const_div_deg | (intros; apply GlobalTheory.Amp.OpenCellNorm.norm_eq_const_div_deg <;> assumption)
end
