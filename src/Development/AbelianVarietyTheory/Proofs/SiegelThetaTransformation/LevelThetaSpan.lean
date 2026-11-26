module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SetIntegralCompOfStable
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernelIdentity
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaLevelDataFormsSystem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSeriesSpanBoundedForms
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatticeOperatorCoefficients
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Coef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem ip_smul_smul {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
    {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) (a b : ℂ) :
    ip (a • φ) (b • ψ) = a * conj b * ip φ ψ := by
  have hc : IsSB fun x => conj (ψ x) :=
    (isSB_algebra_haar_linear K κ ι ψ ψ hψ hψ).2.2.2.1
  have hp : IsSB (φ * fun x => conj (ψ x)) :=
    (isSB_algebra_haar_linear K κ ι φ _ hφ hc).2.2.1
  have hs := (isSB_algebra_haar_linear K κ ι _ _ hp hp).2.2.2.2.2.1 (a * conj b)
  have key : (fun x => (a • φ) x * conj ((b • ψ) x)) =
      (a * conj b) • (φ * fun x => conj (ψ x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul]
    ring
  unfold ip
  rw [key, hs]
  rfl

theorem classSum_eq_sum {M : ℕ} [Fintype (Cls E n M)] (f : Lt E n → ℂ) :
    classSum M f = ∑ c : Cls E n M, (wt M (Quot.out c).1 : ℂ) * f (Quot.out c).1 := by
  unfold classSum
  exact finsum_eq_sum_of_fintype _

theorem exists_mass {M : ℕ} (hM : 0 < M) : ∃ m : ℝ, 0 < m ∧
    (∀ (f : Lt E n → ℂ) (a : ℂ), (∀ Λ ∈ Vset E n M, f Λ = a) → classSum M f = m * a) ∧
    ∀ (f : Lt E n → ℂ) (b : ℝ), (∀ Λ ∈ Vset E n M, ‖f Λ‖ ≤ b) → ‖classSum M f‖ ≤ m * b := by
  classical
  obtain ⟨hfin, hstd, hwt, -, -⟩ := finite_cls_and_stab E n M hM
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  refine ⟨∑ c : Cls E n M, wt M (Quot.out c).1, ?_, ?_, ?_⟩
  · apply Finset.sum_pos
    · intro c _
      exact (hwt _ (Quot.out c).2).2
    · exact ⟨(Quot.mk _ ⟨stdL E n, hstd⟩ : Cls E n M), Finset.mem_univ _⟩
  · intro f a hf
    rw [classSum_eq_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hf _ (Quot.out c).2]
  · intro f b hf
    rw [classSum_eq_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    have hw := (hwt _ (Quot.out c).2).2
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
    exact mul_le_mul_of_nonneg_left (hf _ (Quot.out c).2) hw.le

theorem classSum_mul {M : ℕ} (hM : 0 < M) (f : Lt E n → ℂ) (a : ℂ) :
    classSum M f * a = classSum M fun Λ => f Λ * a := by
  classical
  have := (finite_cls_and_stab E n M hM).1
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  rw [classSum_eq_sum, classSum_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => mul_assoc _ _ _

end GlobalTheory.SW.Coef

namespace GlobalTheory.SW

open Coef

private theorem classSum_congr_of_eqOn_Vset {E : Type} [Field E] [NumberField E] [IsCMField E]
    {n M : ℕ} {f g : Lt E n → ℂ} (h : ∀ Λ ∈ Vset E n M, f Λ = g Λ) :
    classSum M f = classSum M g := by
  unfold classSum
  exact finsum_congr fun c => by rw [h _ (Quot.out c).2]

theorem lattice_operator_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), 0 < M → IsSystem X bas idx M Δ 𝓛 Φ μ → ∃ (a θ : ℝ), 0 < a ∧ θ < 1 ∧ (∀ L ∈ 𝓛, classSum M (fun Λ => ip (Φ L Λ) (Φ L Λ)) = a ∧ Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖) ∧ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖ ≤ θ * a) ∧ ∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, classSum M (fun Λ => ip (Φ (mapL γ L) Λ) (Φ (mapL γ L') Λ)) * μ γ L * conj (μ γ L') = classSum M (fun Λ => ip (Φ L Λ) (Φ L' Λ)) := by
  intro E _ _ _ r X g bas idx n hs hn M Δ 𝓛 Φ μ hM hsys
  obtain ⟨m, hm, hconst, hbd⟩ := Coef.exists_mass (E := E) (n := n) hM
  obtain ⟨a, ha, hdiag, b, θ, hθ, hoff, hbt⟩ := hsys.norm
  have hma : 0 < m * a := mul_pos hm ha
  refine ⟨m * a, θ, hma, hθ, fun L hL => ?_, ?_⟩
  · have hb : ∀ L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L},
        ‖classSum M (fun Λ => ip (Φ L Λ) (Φ L'.1 Λ))‖ ≤ m * a * b L L'.1 := fun L' => by
      rw [mul_assoc]
      exact hbd _ (a * b L L'.1) fun Λ hΛ => hoff L hL L'.1 L'.2.1 Λ hΛ
    have hS : Summable fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => m * a * b L L'.1 :=
      (hbt L hL).1.mul_left (m * a)
    have hT := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hS
    refine ⟨?_, hT, ?_⟩
    · rw [hconst _ (a : ℂ) fun Λ hΛ => hdiag L hL Λ hΛ]
      exact (Complex.ofReal_mul m a).symm
    · calc _ ≤ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, m * a * b L L'.1 :=
            Summable.tsum_le_tsum hb hT hS
        _ = m * a * ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, b L L'.1 := tsum_mul_left
        _ ≤ m * a * θ := mul_le_mul_of_nonneg_left (hbt L hL).2 hma.le
        _ = θ * (m * a) := mul_comm _ _
  · intro γ hγ L hL L' hL'
    have hun := hsys.un γ hγ
    have key : ∀ Λ ∈ Vset E n M, ip (Φ L Λ) (Φ L' Λ) =
        ip (Φ (mapL γ L) Λ) (Φ (mapL γ L') Λ) * (μ γ L * conj (μ γ L')) := by
      intro Λ hΛ
      have hw := wG_laws E r X g bas idx n hs hn γ hun (Φ L Λ) (hsys.sb L hL Λ hΛ)
      rw [← (hw.2.2.1 (Φ L' Λ) (hsys.sb L' hL' Λ hΛ)).1, (hsys.mu γ hγ L hL).2 Λ hΛ,
        (hsys.mu γ hγ L' hL').2 Λ hΛ,
        Coef.ip_smul_smul (hsys.sb _ (hsys.stab γ hγ L hL) Λ hΛ)
          (hsys.sb _ (hsys.stab γ hγ L' hL') Λ hΛ)]
      ring
    rw [mul_assoc, Coef.classSum_mul hM]
    exact classSum_congr_of_eqOn_Vset fun Λ hΛ => (key Λ hΛ).symm

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenFrames
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical Topology

namespace GlobalTheory.SW.Neumann

noncomputable section

theorem diffOn_tsum {H ι : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    {U : Set H} (hU : IsOpen U) {w : H → ℝ} (hw : ContinuousOn w U) {g : ι → H → ℂ}
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) {u : ι → ℝ} (hu : Summable u) (hu0 : ∀ i, 0 ≤ u i)
    (hb : ∀ i, ∀ x ∈ U, ‖g i x‖ ≤ u i * w x) :
    DifferentiableOn ℂ (fun x => ∑' i, g i x) U := by
  refine GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hU hg fun x hx => ?_
  have h1 : ∀ᶠ z in 𝓝 x, w z < w x + 1 :=
    (hw.continuousAt (hU.mem_nhds hx)).eventually (gt_mem_nhds (by linarith))
  refine ⟨_, Filter.inter_mem (hU.mem_nhds hx) h1, fun i => u i * (w x + 1), hu.mul_right _,
    fun i z hz => (hb i z hz.1).trans (mul_le_mul_of_nonneg_left (le_of_lt hz.2) (hu0 i))⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cont_dmin (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  have h : Continuous fun x : Frame X.Ψ r => FD.gram τ.1 X.Gm (mat x τ) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [FD.gram, hermC, FD.col, mat, Matrix.of_apply]
    fun_prop
  exact (h.matrix_submatrix _ _).matrix_det

theorem isOpen_frames : IsOpen X.dom := by
  have h : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x; simp [Data.dom, GG]
  rw [h]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun
      (show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det
      continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp
      (cont_dmin X τ i)))

theorem dmin_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have := (hx τ).2 i
  rw [h] at this
  simp at this

def fac (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)

theorem fac_pos (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 < fac X la x :=
  Finset.prod_pos fun τ _ => Finset.prod_pos fun _ _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _))) _

theorem fac_cont (la : Wt X.Ψ r) : ContinuousOn (fun x => (fac X la x)⁻¹) X.dom := by
  refine ContinuousOn.inv₀ ?_ fun x hx => (fac_pos X la hx).ne'
  refine continuousOn_finsetProd _ fun τ _ => continuousOn_finsetProd _ fun i _ => ?_
  refine ContinuousOn.rpow_const ?_ fun x hx => Or.inl ?_
  · exact (((cont_dmin X τ _).continuousOn).div (cont_dmin X τ _).continuousOn
      fun x hx => dmin_ne X hx τ _).norm
  · exact norm_ne_zero_iff.mpr (div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _))

theorem pnorm_le_iff (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (B : ℝ) : X.pnorm la P x ≤ B ↔ ‖P x‖ ≤ B * (fac X la x)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (fac_pos X la hx)]; rfl

omit [IsCMField E] in
theorem mapL_mul (γ δ : GL (Fin r) E) (L : Lt E r) : mapL (γ * δ) L = mapL γ (mapL δ L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
theorem mapL_one (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  rw [Units.val_one, Matrix.toLin'_one]
  exact Submodule.map_id L

def mapE (γ : GL (Fin r) E) : Lt E r ≃ Lt E r where
  toFun := mapL γ
  invFun := mapL γ⁻¹
  left_inv L := by rw [← mapL_mul, inv_mul_cancel, mapL_one]
  right_inv L := by rw [← mapL_mul, mul_inv_cancel, mapL_one]

def op (𝓛 : Set (Lt E r)) (C : Lt E r → Lt E r → ℂ) (a : ℝ) (G : Lt E r → Frame X.Ψ r → ℂ)
    (L : Lt E r) (x : Frame X.Ψ r) : ℂ :=
  -(a : ℂ)⁻¹ * ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, C L L'.1 * G L'.1 x

variable {X} {Δ : Subgroup (GL (Fin r) E)} {𝓛 : Set (Lt E r)} {μ : GL (Fin r) E → Lt E r → ℂ}
  {la : Wt X.Ψ r} {C : Lt E r → Lt E r → ℂ} {a θ : ℝ}

theorem op_bound (ha : 0 < a)
    (hC : ∀ L ∈ 𝓛, Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧
      ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a)
    {G : Lt E r → Frame X.Ψ r → ℂ} {B : ℝ} (hB : 0 ≤ B) {x : Frame X.Ψ r}
    (hG : ∀ L ∈ 𝓛, ‖G L x‖ ≤ B) {L : Lt E r} (hL : L ∈ 𝓛) :
    ‖op X 𝓛 C a G L x‖ ≤ θ * B := by
  have h1 : ‖∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, C L L'.1 * G L'.1 x‖ ≤
      (∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖) * B := by
    refine tsum_of_norm_bounded ((hC L hL).1.hasSum.mul_right B) fun L' => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hG _ L'.2.1) (norm_nonneg _)
  have h2 := h1.trans (mul_le_mul_of_nonneg_right (hC L hL).2 hB)
  unfold op
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg ha.le,
    inv_mul_le_iff₀ ha]
  linarith

theorem op_form (ha : 0 < a)
    (hμ : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛 ∧ ‖μ γ L‖ = 1)
    (hC : ∀ L ∈ 𝓛, Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧
      ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a)
    (hinv : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛,
      C (mapL γ L) (mapL γ L') * μ γ L * conj (μ γ L') = C L L')
    {G : Lt E r → Frame X.Ψ r → ℂ} (hG : IsForm X Δ 𝓛 μ la G) :
    IsForm X Δ 𝓛 μ la (op X 𝓛 C a G) := by
  obtain ⟨B, hB⟩ := hG.bdd
  have hB' : ∀ L ∈ 𝓛, ∀ x ∈ X.dom, ‖G L x‖ ≤ max B 0 * (fac X la x)⁻¹ := fun L hL x hx =>
    (pnorm_le_iff X la _ hx _).1 ((hB L hL x hx).trans (le_max_left _ _))
  refine ⟨fun L hL => ?_, fun L hL x hx b hb => ?_, fun γ hγ L hL x hx => ?_,
    θ * max B 0, fun L hL x hx => ?_⟩
  · refine DifferentiableOn.const_mul (diffOn_tsum (isOpen_frames X) (fac_cont X la)
      (fun L' => (hG.hol _ L'.2.1).const_mul _) ((hC L hL).1.mul_right (max B 0))
      (fun L' => mul_nonneg (norm_nonneg _) (le_max_right _ _)) fun L' x hx => ?_) _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB' _ L'.2.1 x hx) (norm_nonneg _)
  · unfold op
    rw [mul_left_comm, ← tsum_mul_left (a := bchar la b)]
    congr 1
    refine tsum_congr fun L' => ?_
    rw [hG.bor _ L'.2.1 x hx b hb]; ring
  · have he : ∀ L', (L' ∈ 𝓛 ∧ L' ≠ L) ↔ (mapE γ L' ∈ 𝓛 ∧ mapE γ L' ≠ mapL γ L) := by
      intro L'
      refine and_congr ⟨fun h => (hμ γ hγ L' h).1, fun h => ?_⟩ (mapE γ).injective.ne_iff.symm
      have := (hμ γ⁻¹ (Δ.inv_mem hγ) _ h).1
      rwa [show mapL γ⁻¹ (mapE γ L') = L' from (mapE γ).left_inv L'] at this
    unfold op
    rw [mul_left_comm, ← tsum_mul_left (a := (μ γ L)⁻¹),
      ← ((mapE γ).subtypeEquiv he).tsum_eq]
    congr 1
    refine tsum_congr fun L' => ?_
    change C (mapL γ L) (mapL γ L'.1) * G (mapL γ L'.1) (lact γ x) = _
    rw [hG.aut γ hγ _ L'.2.1 x hx, ← hinv γ hγ L hL _ L'.2.1,
      ← Complex.inv_eq_conj (hμ γ hγ _ L'.2.1).2]
    have h0 : μ γ L ≠ 0 := norm_ne_zero_iff.1 (by rw [(hμ γ hγ L hL).2]; exact one_ne_zero)
    field_simp
  · rw [pnorm_le_iff X la _ hx, mul_assoc]
    exact op_bound ha hC (mul_nonneg (le_max_right _ _) (inv_pos.2 (fac_pos X la hx)).le)
      (fun L hL => hB' L hL x hx) hL

end

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (μ : GL (Fin r) E → Lt E r → ℂ) (la : Wt X.Ψ r) (C : Lt E r → Lt E r → ℂ) (a θ : ℝ), 0 < a → θ < 1 → (∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛 ∧ ‖μ γ L‖ = 1) → (∀ γ ∈ Δ, ∀ x ∈ X.dom, lact γ x ∈ X.dom) → (∀ L ∈ 𝓛, C L L = a ∧ Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧ ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a) → (∀ γ ∈ Δ, ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, C (mapL γ L) (mapL γ L') * μ γ L * conj (μ γ L') = C L L') → ∀ F, IsForm X Δ 𝓛 μ la F → ∃ F', IsForm X Δ 𝓛 μ la F' ∧ ∀ L ∈ 𝓛, ∀ x ∈ X.dom, F L x = ∑' L' : 𝓛, C L L'.1 * F' L'.1 x := by
  intro E _ _ _ r X Δ 𝓛 μ la C a θ₀ ha hθ₀ hμ _ hC₀ hinv F hF
  set θ : ℝ := max θ₀ 0 with hθ
  have hθ0 : 0 ≤ θ := le_max_right _ _
  have hθ1 : θ < 1 := max_lt hθ₀ one_pos
  have hC : ∀ L ∈ 𝓛, Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => ‖C L L'.1‖) ∧
      ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ‖C L L'.1‖ ≤ θ * a := fun L hL =>
    ⟨(hC₀ L hL).2.1, (hC₀ L hL).2.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha.le)⟩
  obtain ⟨G, hG0, hGs⟩ : ∃ G : ℕ → Lt E r → Frame X.Ψ r → ℂ, G 0 = F ∧
      ∀ k, G (k + 1) = op X 𝓛 C a (G k) :=
    ⟨fun k => (op X 𝓛 C a)^[k] F, rfl, fun k => Function.iterate_succ_apply' _ _ _⟩
  have hGf : ∀ k, IsForm X Δ 𝓛 μ la (G k) := by
    intro k
    induction k with
    | zero => rwa [hG0]
    | succ k ih => rw [hGs]; exact op_form ha hμ hC hinv ih
  obtain ⟨B₀, hB₀⟩ := hF.bdd
  set B : ℝ := max B₀ 0 with hBd
  have hB0 : 0 ≤ B := le_max_right _ _
  have hw : ∀ x ∈ X.dom, 0 ≤ (fac X la x)⁻¹ := fun x hx => (inv_pos.2 (fac_pos X la hx)).le
  have hGb : ∀ k, ∀ x ∈ X.dom, ∀ L ∈ 𝓛, ‖G k L x‖ ≤ θ ^ k * B * (fac X la x)⁻¹ := by
    intro k x hx
    induction k with
    | zero =>
      intro L hL
      rw [hG0, pow_zero, one_mul]
      exact (pnorm_le_iff X la _ hx _).1 ((hB₀ L hL x hx).trans (le_max_left _ _))
    | succ k ih =>
      intro L hL
      rw [hGs]
      refine (op_bound ha hC (mul_nonneg (by positivity) (hw x hx)) ih hL).trans (le_of_eq ?_)
      ring
  have hgeo : Summable fun k : ℕ => θ ^ k * B :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_right B
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  refine ⟨fun L x => (a : ℂ)⁻¹ * ∑' k, G k L x, ⟨fun L hL => ?_, fun L hL x hx b hb => ?_,
    fun γ hγ L hL x hx => ?_, ‖(a : ℂ)⁻¹‖ * ∑' k : ℕ, θ ^ k * B, fun L hL x hx => ?_⟩,
    fun L hL x hx => ?_⟩
  · exact (diffOn_tsum (isOpen_frames X) (fac_cont X la) (fun k => (hGf k).hol L hL) hgeo
      (fun k => by positivity) fun k x hx => hGb k x hx L hL).const_mul _
  · rw [mul_left_comm, ← tsum_mul_left (a := bchar la b)]
    congr 1
    exact tsum_congr fun k => (hGf k).bor L hL x hx b hb
  · rw [mul_left_comm, ← tsum_mul_left (a := (μ γ L)⁻¹)]
    congr 1
    exact tsum_congr fun k => (hGf k).aut γ hγ L hL x hx
  · rw [pnorm_le_iff X la _ hx, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (tsum_of_norm_bounded (hgeo.hasSum.mul_right _)
      fun k => hGb k x hx L hL) (norm_nonneg _)
  · have hs : Summable fun k => G k L x :=
      Summable.of_norm_bounded (hgeo.mul_right _) fun k => hGb k x hx L hL
    have hp : Summable fun p : {L' // L' ∈ 𝓛 ∧ L' ≠ L} × ℕ =>
        (a : ℂ)⁻¹ * (C L p.1.1 * G p.2 p.1.1 x) := by
      refine Summable.mul_left _ (Summable.of_norm_bounded
        (Summable.mul_of_nonneg (hC L hL).1 (hgeo.mul_right (fac X la x)⁻¹)
          (fun _ => norm_nonneg _) fun k => mul_nonneg (by positivity) (hw x hx)) fun p => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hGb _ x hx _ p.1.2.1) (norm_nonneg _)
    have hcomm := Summable.tsum_comm (f := fun (L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}) (k : ℕ) =>
      (a : ℂ)⁻¹ * (C L L'.1 * G k L'.1 x)) hp
    have hterm : ∀ L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, ∑' k, (a : ℂ)⁻¹ * (C L L'.1 * G k L'.1 x) =
        C L L'.1 * ((a : ℂ)⁻¹ * ∑' k, G k L'.1 x) := by
      intro L'
      rw [tsum_mul_left, tsum_mul_left]; ring
    have hk : ∀ k, ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L}, (a : ℂ)⁻¹ * (C L L'.1 * G k L'.1 x) =
        -G (k + 1) L x := by
      intro k
      rw [tsum_mul_left, hGs, op]; ring
    have hsum : HasSum (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} =>
        C L L'.1 * ((a : ℂ)⁻¹ * ∑' k, G k L'.1 x)) (-∑' k, G (k + 1) L x) := by
      have h := hp.prod.hasSum
      simp only at h
      rw [← hcomm] at h
      simp only [hterm, hk, tsum_neg] at h
      exact h
    have hall : ∀ s : Set (Lt E r), s = {L} ∪ {L' | L' ∈ 𝓛 ∧ L' ≠ L} →
        HasSum (fun L' : s => C L L'.1 * ((a : ℂ)⁻¹ * ∑' k, G k L'.1 x))
          (C L L * ((a : ℂ)⁻¹ * ∑' k, G k L x) + -∑' k, G (k + 1) L x) := by
      rintro s rfl
      exact HasSum.add_disjoint (f := fun L' => C L L' * ((a : ℂ)⁻¹ * ∑' k, G k L' x))
        (by simp) (hasSum_singleton L fun L' => C L L' * ((a : ℂ)⁻¹ * ∑' k, G k L' x)) hsum
    rw [(hall 𝓛 ?_).tsum_eq, (hC₀ L hL).1, mul_inv_cancel_left₀ hac, hs.tsum_eq_zero_add, hG0]
    · ring
    · ext L'
      by_cases h : L' = L <;> simp [h, hL]

end GlobalTheory.SW.Neumann
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegrableTsumOfSummableIntegralNorm
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

private theorem integrable_tsum_of_summable_integral_norm' {ι Y E : Type} [Countable ι] [MeasurableSpace Y]
    [NormedAddCommGroup E] [CompleteSpace E]
    (μ : Measure Y) (F : ι → Y → E) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ y, ‖F i y‖ ∂μ) :
    Integrable (fun y => ∑' i, F i y) μ ∧ ∀ᵐ y ∂μ, Summable fun i => ‖F i y‖ := by
  have hmeas : ∀ i, AEMeasurable (fun y => ‖F i y‖ₑ) μ := fun i => (hF i).1.enorm

  have htot : ∫⁻ y, ∑' i, ‖F i y‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have h : ∀ i, ∫⁻ y, ‖F i y‖ₑ ∂μ = ENNReal.ofReal (∫ y, ‖F i y‖ ∂μ) := fun i =>
      (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
    simp_rw [h]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun y => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top

  have hsum : ∀ᵐ y ∂μ, Summable fun i => ‖F i y‖ := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) htot] with y hy
    exact tsum_enorm_ne_top_iff_summable_norm.1 hy.ne
  refine ⟨⟨?_, ?_⟩, hsum⟩
  · refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
      (f := fun s y => ∑ i ∈ s, F i y) (fun s => ?_) ?_
    · exact Finset.aestronglyMeasurable_fun_sum s fun i _ => (hF i).1
    · filter_upwards [hsum] with y hy
      exact hy.of_norm.hasSum
  · exact lt_of_le_of_lt (lintegral_mono fun y => enorm_tsum_le_tsum_enorm) htot.lt_top

theorem integrable_tsum_of_summable_integral_norm {ι Y : Type} [Countable ι] [MeasurableSpace Y]
    (μ : Measure Y) (F : ι → Y → ℂ) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ y, ‖F i y‖ ∂μ) :
    Integrable (fun y => ∑' i, F i y) μ ∧ ∫ y, ‖∑' i, F i y‖ ∂μ ≤ ∑' i, ∫ y, ‖F i y‖ ∂μ := by
  obtain ⟨hint, hsum⟩ := integrable_tsum_of_summable_integral_norm' μ F hF hs
  refine ⟨hint, ?_⟩
  have hnorm : ∀ i, Integrable (fun y => ‖F i y‖) μ := fun i => (hF i).norm
  have hs' : Summable fun i => ∫ y, ‖‖F i y‖‖ ∂μ := by simpa only [norm_norm] using hs
  calc ∫ y, ‖∑' i, F i y‖ ∂μ ≤ ∫ y, ∑' i, ‖F i y‖ ∂μ := by
        refine integral_mono_ae hint.norm (integrable_tsum_of_summable_integral_norm' μ _ hnorm hs').1 ?_
        filter_upwards [hsum] with y hy
        exact norm_tsum_le_tsum_norm hy
    _ = ∑' i, ∫ y, ‖F i y‖ ∂μ := (integral_tsum_of_summable_integral_norm hnorm hs').symm

theorem hasSum_setIntegral_of_ae_existsUnique {ι Y E : Type} [Countable ι] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Y) (S : ι → Set Y) (hS : ∀ i, MeasurableSet (S i))
    (hu : ∀ᵐ y ∂μ, ∃! i, y ∈ S i) (f : Y → E) (hf : Integrable f μ) :
    HasSum (fun i => ∫ y in S i, f y ∂μ) (∫ y, f y ∂μ) := by

  have hdisj : Pairwise fun i j => AEDisjoint μ (S i) (S j) := by
    intro i j hij
    refine measure_mono_null (t := {y | ¬ ∃! k, y ∈ S k}) ?_ (ae_iff.1 hu)
    intro y hy h
    exact hij (ExistsUnique.unique h hy.1 hy.2)

  have hcover : (⋃ i, S i : Set Y) =ᵐ[μ] (Set.univ : Set Y) := by
    filter_upwards [hu] with y ⟨i, hi, _⟩
    exact ⟨fun _ => trivial, fun _ => Set.mem_iUnion.2 ⟨i, hi⟩⟩
  have h := hasSum_integral_iUnion_ae (fun i => (hS i).nullMeasurableSet) hdisj hf.integrableOn
  rwa [setIntegral_congr_set hcover, setIntegral_univ] at h

theorem setIntegral_smul_of_measurePreserving {Γ Y E : Type} [Group Γ] [MeasurableSpace Y]
    [MulAction Γ Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure Y)
    (hν : ∀ γ : Γ, MeasurePreserving (fun y : Y => γ • y) ν ν) (γ : Γ) (D : Set Y) (g : Y → E) :
    ∫ y in D, g (γ • y) ∂ν = ∫ y in (fun y : Y => γ⁻¹ • y) ⁻¹' D, g y ∂ν := by
  let φ : Y ≃ᵐ Y :=
    { toEquiv := MulAction.toPerm γ
      measurable_toFun := (hν γ).measurable
      measurable_invFun := (hν γ⁻¹).measurable }
  have hemb : MeasurableEmbedding (fun y : Y => γ • y) := φ.measurableEmbedding
  have hD : D = (fun y : Y => γ • y) ⁻¹' ((fun y : Y => γ⁻¹ • y) ⁻¹' D) := by
    ext y
    simp
  have key := (hν γ).setIntegral_preimage_emb hemb g ((fun y : Y => γ⁻¹ • y) ⁻¹' D)
  rw [← hD] at key
  exact key

theorem unfolding_abstract : ∀ (Γ I Y : Type) [Group Γ] [Countable Γ] [Countable I] [MeasurableSpace Y] [MulAction Γ I] [MulAction Γ Y] (ν : Measure Y) [SFinite ν], (∀ γ : Γ, MeasurePreserving (fun y : Y => γ • y) ν ν) → ∀ D : I → Set Y, (∀ i, MeasurableSet (D i)) → (∀ i, ∀ᵐ y ∂ν, ∃! γ : Γ, γ • y ∈ D (γ • i)) → ∀ f : I → Y → ℂ, (∀ i, Integrable (f i) ν) → Summable (fun i => ∫ y, ‖f i y‖ ∂ν) → (∀ i, IntegrableOn (fun y => ∑' γ : Γ, f (γ • i) (γ • y)) (D i) ν) ∧ Summable (fun i => ∫ y in D i, ‖∑' γ : Γ, f (γ • i) (γ • y)‖ ∂ν) ∧ ∑' i, ∫ y in D i, ∑' γ : Γ, f (γ • i) (γ • y) ∂ν = ∑' i, ∫ y, f i y ∂ν := by
  intro Γ I Y _ _ _ _ _ _ ν _ hν D hD hcov f hf hs

  have hSm : ∀ (j : I) (δ : Γ), MeasurableSet ((fun y : Y => δ • y) ⁻¹' D (δ • j)) :=
    fun j δ => (hν δ).measurable (hD _)
  have hP : ∀ (j : I) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Y → E),
      Integrable g ν →
      HasSum (fun δ : Γ => ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), g y ∂ν) (∫ y, g y ∂ν) :=
    fun j E _ _ g hg => hasSum_setIntegral_of_ae_existsUnique ν
      (fun δ : Γ => (fun y : Y => δ • y) ⁻¹' D (δ • j)) (hSm j) (hcov j) g hg

  have hmove : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (j : I) (δ : Γ) (g : Y → E),
      ∫ y in D (δ • j), g (δ⁻¹ • y) ∂ν = ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), g y ∂ν := by
    intro E _ _ j δ g
    rw [setIntegral_smul_of_measurePreserving ν hν δ⁻¹ (D (δ • j)) g]
    simp only [inv_inv]

  let e : I × Γ ≃ I × Γ :=
    { toFun := fun p => (p.2 • p.1, p.2⁻¹)
      invFun := fun p => (p.2 • p.1, p.2⁻¹)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have he : ∀ p : I × Γ, e p = (p.2 • p.1, p.2⁻¹) := fun p => rfl
  obtain ⟨c, hc⟩ : ∃ c : I × Γ → ℂ,
      ∀ p, c p = ∫ y in D p.1, f (p.2 • p.1) (p.2 • y) ∂ν := ⟨_, fun _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : I × Γ → ℝ,
      ∀ p, a p = ∫ y in D p.1, ‖f (p.2 • p.1) (p.2 • y)‖ ∂ν := ⟨_, fun _ => rfl⟩
  have hce : ∀ p : I × Γ,
      c (e p) = ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), f p.1 y ∂ν := by
    rintro ⟨j, δ⟩
    rw [he, hc]
    dsimp only
    simp only [inv_smul_smul]
    exact hmove j δ (f j)
  have hae : ∀ p : I × Γ,
      a (e p) = ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), ‖f p.1 y‖ ∂ν := by
    rintro ⟨j, δ⟩
    rw [he, ha]
    dsimp only
    simp only [inv_smul_smul]
    exact hmove j δ (fun y => ‖f j y‖)
  have hnorm_int : ∀ j, Integrable (fun y => ‖f j y‖) ν := fun j => (hf j).norm

  have ha0 : 0 ≤ a := fun p => by
    rw [Pi.zero_apply, ha]
    exact integral_nonneg fun _ => norm_nonneg _
  have hb_sum : Summable (a ∘ e) := by
    have h0 : 0 ≤ a ∘ e := fun p => ha0 (e p)
    refine (summable_prod_of_nonneg h0).2 ⟨fun j => ?_, ?_⟩
    · simp only [Function.comp_apply, hae]
      exact (hP j _ (hnorm_int j)).summable
    · simp only [Function.comp_apply, hae]
      have h1 : ∀ j : I, ∑' δ : Γ, ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), ‖f j y‖ ∂ν =
          ∫ y, ‖f j y‖ ∂ν := fun j => (hP j _ (hnorm_int j)).tsum_eq
      simpa only [h1] using hs
  have ha_sum : Summable a := e.summable_iff.1 hb_sum
  have hc_sum : Summable c := ha_sum.of_norm_bounded fun p => by
    rw [hc, ha]
    exact norm_integral_le_integral_norm _

  have hFint : ∀ (i : I) (γ : Γ), Integrable (fun y => f (γ • i) (γ • y)) (ν.restrict (D i)) :=
    fun i γ => ((hν γ).integrable_comp_of_integrable (hf (γ • i))).restrict
  have hFsum : ∀ i, Summable fun γ : Γ => ∫ y in D i, ‖f (γ • i) (γ • y)‖ ∂ν := fun i => by
    simpa only [ha] using ha_sum.prod_factor i
  have hmain := fun i => integrable_tsum_of_summable_integral_norm (ν.restrict (D i))
    (fun (γ : Γ) (y : Y) => f (γ • i) (γ • y)) (hFint i) (hFsum i)
  refine ⟨fun i => (hmain i).1, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun y => norm_nonneg _)
      (fun i => (hmain i).2) ?_
    simpa only [ha] using ((summable_prod_of_nonneg ha0).1 ha_sum).2
  · have hrow : ∀ i, ∫ y in D i, ∑' γ : Γ, f (γ • i) (γ • y) ∂ν = ∑' γ : Γ, c (i, γ) :=
      fun i => (integral_tsum_of_summable_integral_norm (hFint i) (hFsum i)).symm.trans
        (tsum_congr fun γ => (hc (i, γ)).symm)
    have hd : Summable fun p : I × Γ =>
        ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), f p.1 y ∂ν := by
      have h1 := e.summable_iff.2 hc_sum
      simpa only [Function.comp_def, hce] using h1
    calc ∑' i, ∫ y in D i, ∑' γ : Γ, f (γ • i) (γ • y) ∂ν = ∑' i, ∑' γ : Γ, c (i, γ) :=
          tsum_congr hrow
      _ = ∑' p, c p := (hc_sum.tsum_prod' hc_sum.prod_factor).symm
      _ = ∑' p, c (e p) := (e.tsum_eq c).symm
      _ = ∑' p : I × Γ, ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), f p.1 y ∂ν :=
          tsum_congr hce
      _ = ∑' j, ∑' δ : Γ, ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), f j y ∂ν :=
          hd.tsum_prod' hd.prod_factor
      _ = ∑' j, ∫ y, f j y ∂ν := tsum_congr fun j => (hP j (f j) (hf j)).tsum_eq

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableSetIntegralOfSummableNorm
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem summable_setIntegral_of_summable_norm {I Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    (D : I → Set Y) (f : I → Y → ℂ) (h : Summable fun i => ∫ y in D i, ‖f i y‖ ∂ν) :
    Summable fun i => ∫ y in D i, f i y ∂ν := by

  exact Summable.of_norm_bounded h fun i => norm_integral_le_integral_norm _

def finiteRankDomain {I Y : Type} [MeasurableSpace Y] (ν : Measure Y) (D : I → Set Y) {m : ℕ}
    (t : Fin m → I → Y → ℂ) : Submodule ℂ (Fin m → ℂ) where
  carrier := {v | (∀ i, IntegrableOn (fun y => ∑ j, v j * t j i y) (D i) ν) ∧
    Summable fun i => ∫ y in D i, ‖∑ j, v j * t j i y‖ ∂ν}
  zero_mem' := by
    refine ⟨fun i => ?_, ?_⟩
    · simp
    · simp
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    have key : ∀ i y, ∑ j, (v + w) j * t j i y = ∑ j, v j * t j i y + ∑ j, w j * t j i y := by
      intro i y
      simp [add_mul, Finset.sum_add_distrib]
    refine ⟨fun i => ?_, ?_⟩
    · simp only [key]
      exact (hv i).add (hw i)
    · simp only [key]
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun y => norm_nonneg _)
        (fun i => ?_) (hv'.add hw')
      rw [← integral_add (hv i).norm (hw i).norm]
      exact integral_mono ((hv i).add (hw i)).norm ((hv i).norm.add (hw i).norm)
        (fun y => norm_add_le _ _)
  smul_mem' := by
    rintro c v ⟨hv, hv'⟩
    have key : ∀ i y, ∑ j, (c • v) j * t j i y = c * ∑ j, v j * t j i y := by
      intro i y
      simp [Finset.mul_sum, mul_assoc]
    refine ⟨fun i => ?_, ?_⟩
    · simp only [key]
      exact (hv i).const_mul c
    · simp only [key, norm_mul, integral_const_mul]
      exact hv'.mul_left _

noncomputable def finiteRankFunctional {I Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    (D : I → Set Y) {m : ℕ} (t : Fin m → I → Y → ℂ) : finiteRankDomain ν D t →ₗ[ℂ] ℂ where
  toFun v := ∑' i, ∫ y in D i, ∑ j, v.1 j * t j i y ∂ν
  map_add' := by
    rintro ⟨v, hv, hv'⟩ ⟨w, hw, hw'⟩
    have key : ∀ i y, ∑ j, (v + w) j * t j i y = ∑ j, v j * t j i y + ∑ j, w j * t j i y := by
      intro i y
      simp [add_mul, Finset.sum_add_distrib]
    show ∑' i, ∫ y in D i, ∑ j, (v + w) j * t j i y ∂ν
      = ∑' i, ∫ y in D i, ∑ j, v j * t j i y ∂ν + ∑' i, ∫ y in D i, ∑ j, w j * t j i y ∂ν
    rw [← Summable.tsum_add (summable_setIntegral_of_summable_norm ν D _ hv')
      (summable_setIntegral_of_summable_norm ν D _ hw')]
    refine tsum_congr fun i => ?_
    simp only [key]
    exact integral_add (hv i) (hw i)
  map_smul' := by
    rintro c ⟨v, hv⟩
    have key : ∀ i y, ∑ j, (c • v) j * t j i y = c * ∑ j, v j * t j i y := by
      intro i y
      simp [Finset.mul_sum, mul_assoc]
    show ∑' i, ∫ y in D i, ∑ j, (c • v) j * t j i y ∂ν
      = c * ∑' i, ∫ y in D i, ∑ j, v j * t j i y ∂ν
    simp only [key, integral_const_mul]
    exact tsum_mul_left

theorem finiteRank_integral_mem_span : ∀ (A I Y : Type) [Countable I] [MeasurableSpace Y] (ν : Measure Y) (D : I → Set Y) (S : Set A) (m : ℕ) (e : Fin m → A → ℂ) (t : Fin m → I → Y → ℂ), (∀ a ∈ S, (∀ i, IntegrableOn (fun y => ∑ j, e j a * t j i y) (D i) ν) ∧ Summable fun i => ∫ y in D i, ‖∑ j, e j a * t j i y‖ ∂ν) → ∃ b : Fin m → ℂ, ∀ a ∈ S, ∑' i, ∫ y in D i, ∑ j, e j a * t j i y ∂ν = ∑ j, b j * e j a := by
  intro A I Y _ _ ν D S m e t hS

  obtain ⟨g, hg⟩ := LinearMap.exists_extend (finiteRankFunctional ν D t)
  refine ⟨fun j => g (Pi.single j 1), fun a ha => ?_⟩
  have hmem : (fun j => e j a) ∈ finiteRankDomain ν D t := hS a ha
  have h1 : g (fun j => e j a) = ∑' i, ∫ y in D i, ∑ j, e j a * t j i y ∂ν :=
    LinearMap.congr_fun hg ⟨fun j => e j a, hmem⟩
  rw [← h1]
  have hx : (fun j => e j a) = ∑ j, e j a • (Pi.single j (1 : ℂ) : Fin m → ℂ) := by
    ext k
    simp [Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  simp [mul_comm]

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSeriesSpanBoundedForms
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.SpanMain

theorem unfold_span (Γ I Y A J : Type) [Group Γ] [Countable Γ] [Countable I] [MeasurableSpace Y]
    [MulAction Γ I] [MulAction Γ Y] [Fintype J] (ν : Measure Y) [SFinite ν]
    (hν : ∀ γ : Γ, MeasurePreserving (fun y : Y => γ • y) ν ν) (D : I → Set Y)
    (hD : ∀ i, MeasurableSet (D i)) (hD' : ∀ i, ∀ᵐ y ∂ν, ∃! γ : Γ, γ • y ∈ D (γ • i))
    (S : Set A) (f : A → I → Y → ℂ) (hf : ∀ a ∈ S, ∀ i, Integrable (f a i) ν)
    (hs : ∀ a ∈ S, Summable fun i => ∫ y, ‖f a i y‖ ∂ν) (e : J → A → ℂ) (t : J → I → Y → ℂ)
    (hk : ∀ a ∈ S, ∀ i, ∀ᵐ y ∂ν, ∑' γ : Γ, f a (γ • i) (γ • y) = ∑ j, e j a * t j i y) :
    ∃ (m : ℕ) (k : Fin m → J) (b : Fin m → ℂ), ∀ a ∈ S,
      ∑' i, ∫ y, f a i y ∂ν = ∑ j, b j * e (k j) a := by
  let k : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hk' : ∀ a ∈ S, ∀ i, (fun y => ∑' γ : Γ, f a (γ • i) (γ • y)) =ᵐ[ν.restrict (D i)]
      fun y => ∑ j, e (k j) a * t (k j) i y := fun a ha i => by
    refine ae_restrict_of_ae ((hk a ha i).mono fun y hy => ?_)
    exact hy.trans (k.sum_comp fun j => e j a * t j i y).symm
  obtain ⟨b, hb⟩ := finiteRank_integral_mem_span A I Y ν D S _ (fun j => e (k j))
    (fun j => t (k j)) fun a ha => by
      obtain ⟨h1, h2, -⟩ := unfolding_abstract Γ I Y ν hν D hD hD' (f a) (hf a ha) (hs a ha)
      refine ⟨fun i => (h1 i).congr (hk' a ha i), h2.congr fun i => ?_⟩
      exact integral_congr_ae ((hk' a ha i).mono fun y hy => congrArg norm hy)
  refine ⟨_, k, b, fun a ha => ?_⟩
  obtain ⟨-, -, h3⟩ := unfolding_abstract Γ I Y ν hν D hD hD' (f a) (hf a ha) (hs a ha)
  rw [← h3, ← hb a ha]
  exact tsum_congr fun i => integral_congr_ae (hk' a ha i)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem pnorm_of_gram (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X) : X.pnorm la F x = ‖F x‖ := by
  have h : ∀ τ i, ‖dmin X.Gm x τ i‖ = 1 := fun τ i => by
    unfold dmin lminor
    rw [hx τ, sgnM, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal,
      norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [Function.comp_apply, sgn]
    split_ifs <;> simp
  unfold Data.pnorm
  simp [h]


omit [NumberField E] [IsCMField E] in
theorem norm_bchar_le {Ψ : Finset (E →+* ℂ)} (la : Wt Ψ r) (C : ℝ) {b : Frame Ψ r}
    (hb : ∀ τ i, ‖b τ i i‖ ≤ C ∧ ‖(b τ i i)⁻¹‖ ≤ C) :
    ‖bchar la b‖ ≤ ∏ τ, ∏ i, C ^ (la τ i).natAbs := by
  unfold bchar
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (la τ i)
  · rw [hk, zpow_natCast, Int.natAbs_natCast, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb τ i).1 _
  · rw [hk, _root_.zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← inv_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb τ i).2 _

theorem summable_of_ne {α : Type} (𝓛 : Set α) (L : α) (u : α → ℝ)
    (h : Summable fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => u L'.1) : Summable fun L' : 𝓛 => u L'.1 := by
  have h1 : Summable (u ∘ ((↑) : (𝓛 \ {L} : Set α) → α)) := h
  have h2 : Summable (u ∘ ((↑) : (𝓛 ∩ {L} : Set α) → α)) :=
    ((Set.finite_singleton L).subset Set.inter_subset_right).summable u
  rw [summable_subtype_iff_indicator] at h1 h2
  change Summable (u ∘ ((↑) : 𝓛 → α))
  rw [summable_subtype_iff_indicator]
  refine (h2.add h1).congr fun x => ?_
  by_cases hx : x ∈ 𝓛 <;> by_cases hL : x = L <;> simp [Set.indicator, hx, hL]

theorem bound_on (la : Wt X.Ψ r) (S : Set (Frame X.Ψ r)) (K B : ℝ)
    (hd : ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X) → x ∈ X.dom)
    (hK : ∀ x ∈ S, ∃ x' : Frame X.Ψ r, (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x' τ) = sgnM X) ∧
      ∃ b ∈ Bor X.Ψ r, x = rmul x' b ∧ ∀ τ i j, ‖b τ i j‖ ≤ K ∧ ‖(b τ i i)⁻¹‖ ≤ K) :
    ∃ B' : ℝ, ∀ F : Frame X.Ψ r → ℂ,
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, F (rmul x b) = bchar la b * F x) →
      (∀ x ∈ X.dom, X.pnorm la F x ≤ B) → ∀ x ∈ S, ‖F x‖ ≤ B' := by
  refine ⟨(∏ τ, ∏ i, K ^ (la τ i).natAbs) * B, fun F h1 h2 x hx => ?_⟩
  obtain ⟨x', hx', b, hb, rfl, hbK⟩ := hK x hx
  have h3 := norm_bchar_le la K fun τ i => hbK τ i i
  rw [h1 x' (hd _ hx') b hb, norm_mul]
  refine mul_le_mul h3 ?_ (norm_nonneg _) ((norm_nonneg _).trans h3)
  rw [← pnorm_of_gram X la _ hx']
  exact h2 x' (hd _ hx')

@[reducible] noncomputable def frameAct (Δ : Subgroup (GL (Fin r) E)) :
    MulAction Δ (Frame X.Ψ r) where
  smul γ x := lact γ x
  one_smul x := by
    funext τ
    change (1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  mul_smul γ' γ x := by
    funext τ
    change (((γ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
      ((γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)).map τ.1 * mat x τ =
      ((γ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        (((γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
    rw [Matrix.map_mul, Matrix.mul_assoc]


omit [IsCMField E] in
theorem countable_gl : Countable (GL (Fin r) E) := by
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact (Units.val_injective (α := Matrix (Fin r) (Fin r) E)).countable

theorem sFinite_frame : SFinite (volume : Measure (Frame X.Ψ r)) := by
  have : SigmaFinite (volume : Measure (Fin r → ℂ)) := inferInstance
  have : SigmaFinite (volume : Measure (Fin r → Fin r → ℂ)) := inferInstance
  have : SigmaFinite (volume : Measure (X.Ψ → Fin r → Fin r → ℂ)) := inferInstance
  infer_instance

theorem unfold_frames (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (hun : ∀ γ ∈ Δ, IsUn X γ)
    (hlat : ∀ L ∈ 𝓛, L.FG ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤)
    (hstab : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛) (S : Set (Frame X.Ψ r)) (hmeas : MeasurableSet S)
    (hsub : S ⊆ X.dom)
    (hmp : ∀ γ ∈ Δ, MeasurePreserving (lact γ : Frame X.Ψ r → Frame X.Ψ r)
      (volume.restrict S) (volume.restrict S))
    (A J : Type) [Fintype J] (T : Set A) (f : A → Lt E r → Frame X.Ψ r → ℂ)
    (hf : ∀ a ∈ T, ∀ L ∈ 𝓛, Integrable (f a L) (volume.restrict S))
    (hs : ∀ a ∈ T, Summable fun L : 𝓛 => ∫ y in S, ‖f a L y‖)
    (e : J → A → ℂ) (t : J → Lt E r → Frame X.Ψ r → ℂ)
    (hk : ∀ a ∈ T, ∀ L ∈ 𝓛, ∀ y ∈ S,
      ∑' γ : Δ, f a (mapL γ L) (lact γ y) = ∑ j, e j a * t j L y) :
    ∃ (m : ℕ) (k : Fin m → J) (b : Fin m → ℂ), ∀ a ∈ T,
      ∑' L : 𝓛, ∫ y in S, f a L y = ∑ j, b j * e (k j) a := by
  obtain ⟨hcount, hmul, hone, D, hD, hD'⟩ :=
    LatFrame.exists_fundamentalDomain E r X Δ 𝓛 hun hlat hstab
  have : Countable 𝓛 := hcount.to_subtype
  have : Countable (GL (Fin r) E) := countable_gl
  have := sFinite_frame X
  letI : MulAction Δ 𝓛 :=
    { smul := fun γ L => ⟨mapL γ L, hstab γ γ.2 L L.2⟩
      one_smul := fun L => Subtype.ext (hone _)
      mul_smul := fun γ γ' L => Subtype.ext (hmul _ _ _) }
  have hae : ∀ᵐ y ∂(volume.restrict S), y ∈ S := ae_restrict_mem hmeas
  exact @unfold_span Δ 𝓛 (Frame X.Ψ r) A J _ _ _ MeasureSpace.toMeasurableSpace _ (frameAct X Δ) _
    (volume.restrict S) _ (fun γ => hmp γ γ.2) (fun L => D L) (fun L => (hD L).1)
    (fun L => hae.mono fun y hy => hD' L L.2 y (hsub hy)) T (fun a L => f a L)
    (fun a ha L => hf a ha L L.2) hs e (fun j L => t j L)
    (fun a ha L => hae.mono fun y hy => hk a ha L L.2 y hy)


omit [NumberField E] [IsCMField E] in
theorem mp_restrict {Ψ : Finset (E →+* ℂ)} (S : Set (Frame Ψ r)) (hmeas : MeasurableSet S)
    (f : Frame Ψ r → Frame Ψ r) (h3 : MeasurePreserving f volume volume)
    (h4 : ∀ x, f x ∈ S ↔ x ∈ S) : MeasurePreserving f (volume.restrict S) (volume.restrict S) := by
  have h5 := h3.restrict_preimage hmeas
  rwa [show f ⁻¹' S = S from Set.ext h4] at h5

theorem theta_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * r < n → ∀ (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), 0 < M → IsSystem X bas idx M Δ 𝓛 Φ μ → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (F : Lt E r → Frame X.Ψ r → ℂ), IsForm X Δ 𝓛 μ (wtOf X hr c c' n) F → InSpan X hr bas idx M 𝓛 Φ (Harm.rowHighest ℂ c c' : Submodule ℂ (Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))) F := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn hrn M Δ 𝓛 Φ μ hM hS c c' F hF
  obtain ⟨m, P, hP, hP0, hPi⟩ := exists_invFam_rowHighest X.Ψ q0 X.p0 n c c' (by omega)
  obtain ⟨a, θ, ha, hθ, hC1, hC2⟩ := lattice_operator_coefficients E r X g bas idx n hs hn M Δ 𝓛 Φ μ hM hS
  obtain ⟨κ, hκ, hker⟩ := kernel_identity E r X g q0 hr bas idx n hs hn hrn M Δ 𝓛 Φ μ hM hS
  replace hker := hker c c' m P hP hPi
  obtain ⟨C, hC⟩ : ∃ C : Lt E r → Lt E r → ℂ,
      ∀ L L', classSum M (fun Λ => ip (Φ L Λ) (Φ L' Λ)) = C L L' := ⟨_, fun _ _ => rfl⟩
  simp only [hC] at hC1 hC2 hker
  obtain ⟨F', hF', hFF⟩ := Neumann.main E r X Δ 𝓛 μ (wtOf X hr c c' n) C a θ ha hθ
    (fun γ hγ L hL => ⟨hS.stab γ hγ L hL, (hS.mu γ hγ L hL).1⟩)
    (fun γ hγ x hx => (hS.un γ hγ).lact_mem hx) hC1 hC2 F hF
  obtain ⟨δ₀, hδ₀, hslab⟩ := thin_slab E r X
  obtain ⟨δ₁, hδ₁, hint⟩ := kern_integrableOn_slab E r X g q0 hr idx n c c' m P hn hP (by omega)
  obtain ⟨δ₂, hδ₂, hrep⟩ := kern_reproducing E r X g q0 hr idx n c c' m P hn hP (by omega) hP0
  obtain ⟨δ, hδ, h0, h1, h2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ :=
    ⟨min δ₀ (min δ₁ δ₂), by positivity, min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨hopen, hsub, horth, -, hun, ⟨K, hK⟩, -⟩ := hslab δ hδ h0
  replace hint := hint δ hδ h1
  obtain ⟨ρ, hρ, hrep⟩ := hrep δ hδ h2
  have hmeas : MeasurableSet (slab X δ) := hopen.measurableSet
  obtain ⟨B, hB⟩ := hF'.bdd
  obtain ⟨B', hB0⟩ := bound_on X (wtOf X hr c c' n) (slab X δ) K B
    (fun x hx => hsub (horth x hx)) hK
  have hB' : ∀ L ∈ 𝓛, ∀ x ∈ slab X δ, ‖F' L x‖ ≤ B' := fun L hL =>
    hB0 _ (hF'.bor L hL) (hB L hL)
  have : Finite (Cls E n M) := (finite_cls_and_stab E n M hM).1
  letI : Fintype (Cls E n M) := Fintype.ofFinite _
  have hae : ∀ᵐ y ∂(volume.restrict (slab X δ)), y ∈ slab X δ := ae_restrict_mem hmeas
  have hi : ∀ x₁ ∈ X.dom, ∀ L ∈ 𝓛, Integrable (fun y => kern X hr idx P x₁ y * F' L y)
      (volume.restrict (slab X δ)) := fun x₁ hx₁ L hL =>
    Integrable.mul_bdd (c := B') (hint x₁ hx₁).1
      (((hF'.hol L hL).continuousOn.mono hsub).aestronglyMeasurable hmeas)
      (hae.mono fun y hy => hB' L hL y hy)
  have hmp : ∀ γ ∈ Δ, MeasurePreserving (lact γ : Frame X.Ψ r → Frame X.Ψ r)
      (volume.restrict (slab X δ)) (volume.restrict (slab X δ)) := fun γ hγ => by
    have e : (lact γ : Frame X.Ψ r → Frame X.Ψ r) =
        X.lmulC fun τ => (γ : Matrix (Fin r) (Fin r) E).map τ.1 := rfl
    have h3 := hun (fun τ => (γ : Matrix (Fin r) (Fin r) E).map τ.1)
      fun τ v w => by rw [PerMove.hermC_unitary _ _ _ (hS.un γ hγ)]
    rw [e]
    exact mp_restrict _ hmeas _ h3.1 h3.2.1
  generalize kern X hr idx P = Kr at hker hint hrep hi
  have hsum : ∀ p ∈ 𝓛 ×ˢ X.dom,
      Summable fun L : 𝓛 => ∫ y in slab X δ, ‖C p.1 L * (Kr p.2 y * F' L y)‖ := fun p hp => by
    refine Summable.of_nonneg_of_le (fun L => integral_nonneg fun y => norm_nonneg _)
      (fun L => ?_) ((summable_of_ne 𝓛 p.1 (fun L => ‖C p.1 L‖) (hC1 p.1 hp.1).2.1).mul_right
        (∫ y in slab X δ, ‖Kr p.2 y‖ * B'))
    simp only [norm_mul]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left (integral_mono_ae ?_ ((hint p.2 hp.2).1.norm.mul_const _)
      (hae.mono fun y hy => ?_)) (norm_nonneg _)
    · simpa only [norm_mul] using (hi p.2 hp.2 L L.2).norm
    · exact mul_le_mul_of_nonneg_left (hB' L L.2 y hy) (norm_nonneg _)
  obtain ⟨th, hth⟩ : ∃ th : Lt E r → Lt E n → Fin m → Frame X.Ψ r → ℂ,
      ∀ L Λ j x, thP X hr bas idx (Φ L Λ) (P j) x = th L Λ j x := ⟨_, fun _ _ _ _ => rfl⟩
  simp only [hth] at hker
  obtain ⟨N, k, b, hb⟩ := unfold_frames X Δ 𝓛 hS.un hS.lat hS.stab (slab X δ) hmeas hsub hmp
    (Lt E r × Frame X.Ψ r) (Cls E n M × Fin m)
    (𝓛 ×ˢ X.dom) (fun p L y => C p.1 L * (Kr p.2 y * F' L y))
    (fun p hp L hL => (hi p.2 hp.2 L hL).const_mul _) hsum
    (fun j p => th p.1 (Quot.out j.1).1 j.2 p.2)
    (fun j L y => κ⁻¹ * (wt M (Quot.out j.1).1 : ℂ) *
      conj (th L (Quot.out j.1).1 j.2 y) * F' L y)
    (fun p hp L hL y hy => by
      have h3 := ((hker p.1 hp.1 L hL p.2 hp.2 y (hsub hy)).mul_left κ⁻¹).mul_right (F' L y)
      refine Eq.trans (tsum_congr fun γ => ?_) (h3.tsum_eq.trans ?_)
      · rw [hF'.aut γ γ.2 L hL y (hsub hy), Complex.inv_eq_conj (hS.mu γ γ.2 L hL).1]
        field_simp
      · rw [classSum, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
        ring)
  refine ⟨N, fun i => (Quot.out (k i).1).1, fun i => P (k i).2, fun i => (ρ : ℂ)⁻¹ * b i,
    fun i => ⟨(Quot.out (k i).1).2, hP _⟩, fun L hL x hx => ?_⟩
  have h3 := hb (L, x) ⟨hL, hx⟩
  have hρ' : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.2 hρ.ne'
  have h4 : ∀ L' : 𝓛, ∫ y in slab X δ, C L L' * (Kr x y * F' L' y) =
      ρ * (C L L' * F' L' x) := fun L' => by
    rw [integral_const_mul, hrep (F' L') (hF'.hol _ L'.2) (hF'.bor _ L'.2)
      ⟨B, hB _ L'.2⟩ x hx]
    ring
  simp only [h4] at h3
  rw [tsum_mul_left, ← hFF L hL x hx] at h3
  simp only [mul_assoc, hth]
  rw [← Finset.mul_sum, ← h3, inv_mul_cancel_left₀ hρ']

end GlobalTheory.SW.SpanMain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSeriesSpanBoundedFormsStatement
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTheta_series_span_bounded_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * r < n → ∀ (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), 0 < M → IsSystem X bas idx M Δ 𝓛 Φ μ → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (F : Lt E r → Frame X.Ψ r → ℂ), IsForm X Δ 𝓛 μ (wtOf X hr c c' n) F → InSpan X hr bas idx M 𝓛 Φ (Harm.rowHighest ℂ c c' : Submodule ℂ (Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))) F := by
  first | exact @GlobalTheory.SW.SpanMain.theta_span | exact GlobalTheory.SW.SpanMain.theta_span | (intros; apply GlobalTheory.SW.SpanMain.theta_span <;> assumption)
end
end

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem GlobalTheory.SW.level_theta_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ μ : GL (Fin r) E → Lt E r → ℂ, (∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (F : Lt E r → Frame X.Ψ r → ℂ), IsForm X D.grp D.lats μ (wtOf X hr c c' n) F → InSpan X hr bas idx M D.lats (D.phi bas hn v₀) (Harm.rowHighest ℂ c c' : Submodule ℂ (Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))) F := by
  intro E _ _ _ r X g q0 hr bas idx n hS hE hn4 D hn M hM hMD v₀ hv μ hμ c c' F hF

  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hr1 : r ≤ Module.finrank ℚ E * r := Nat.le_mul_of_pos_left r hd
  have h4 : 4 * r < n := by
    generalize Module.finrank ℚ E * r = k at hr1 hn4
    omega

  exact GlobalTheory.T.hermitianTheta_series_span_bounded_forms E r X g q0 hr bas idx n hS hE h4 M D.grp D.lats (D.phi bas hn v₀) μ hM
    (GlobalTheory.T.hermitianThetaLevelData_forms_system E r X g bas idx n hS hE hn4 D hn M hM hMD v₀ hv μ hμ) c c' F hF
