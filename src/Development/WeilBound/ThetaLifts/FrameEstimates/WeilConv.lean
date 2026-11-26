module

public import Development.WeilBound.ThetaLifts.FrameEstimates.IContOf
public import Development.WeilBound.ThetaLifts.FrameEstimates.SiegelAll
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefSum
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefBd
public import Development.WeilBound.ThetaLifts.FrameEstimates.FourierInj
public import Development.WeilBound.ThetaLifts.FrameEstimates.InitialPairs.TriplePairHolds

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LatFull
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem latFull_of : LatTor → Minor → LatFull := by
  intro hT hM F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' m
  obtain ⟨N, hN⟩ := hT F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  refine ⟨N + m * (n + 1), fun C hC => ?_⟩
  obtain ⟨K, hK⟩ := hN C hC
  obtain ⟨c, hc, h⟩ := hM F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC
  refine ⟨((c ^ (m * (n + 1)))⁻¹).toNNReal * K, fun s hs t ht => ?_⟩
  let i : fullRank E n d → (Set.univ : Set (Matrix (Fin n) (Fin d) E)) := fun x => ⟨x.1, trivial⟩
  have hi : Function.Injective i := fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
  let g : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (maj τ C N (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ))
  calc _ ≤ ∑' x, ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := h s hs t ht x.1 x.2
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        unfold maj
        split_ifs with hx
        · have h2 := pow_le_pow_left₀ (by positivity) (h1 hx) (m * (n + 1))
          rw [mul_pow, ← Real.exp_nat_mul,
            show ((m * (n + 1) : ℕ) : ℝ) * (viol s t / (n + 1)) = m * viol s t by push_cast; field_simp] at h2
          rw [pow_add, mul_inv, mul_comm, Real.exp_neg, ← mul_inv (c ^ _)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) h2) (by positivity)
        · simp
    _ ≤ ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) *
          (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * posWt n d s t))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans (hK s hs t ht)
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.coe_mul]
        change _ = ENNReal.ofReal _ * _ * _
        ring

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.SoSemi
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem qht_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {γ : UA σ J} (hγ : γ ∈ ratU σ J) : qht g ≤ ht (γ * g) :=
  ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ J)

theorem psum_self {r : ℕ} (t : Fin r → ℝ) : psum t r = ∑ i, t i :=
  Finset.sum_congr rfl fun j _ => if_pos j.2

theorem psum_le {r : ℕ} {t : Fin r → ℝ} (h : t ∈ Cone r) (i : ℕ) : psum t i ≤ ∑ j, t j :=
  Finset.sum_le_sum fun j _ => by split_ifs; exacts [le_rfl, h.2 j]

theorem soSemiU_of (hT : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hQ : SqSo) (hI : LatInv) (hK : LatCpt) (hL : LatFull)
    (hP : PosWt) : SoSemiU := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp N₀
  have hc := hp.base.cm
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base n X r s (Or.inl hp.herm)
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨fr, hg, -, ⟨Ω, hΩ, hcov⟩, -, ⟨C₀, k₀, hht⟩⟩ := hS F E σ hc n X.J hJ
  obtain ⟨fr', hg', -, ⟨Ω', hΩ', hcov'⟩, -, hht'⟩ := hS F E σ hc d W.J hJ'
  obtain ⟨A, k₁, hA0, hAk⟩ := exp_le_ht hT hc hJ' hht' hΩ'
  obtain ⟨B₀, hB₀⟩ := (hT F E σ hc n X.J hJ).2.2.2.2.2.2.2 Ω hΩ
  set D : ℕ := Module.finrank ℚ E with hD
  set m : ℕ := D * d + 2 * (k₀ * N₀) with hm
  obtain ⟨N, hN⟩ := hL F E σ hc B.emb n d X.J W.J hJ hJ' fr fr' hg hg' m
  refine ⟨k₁ * (m + D * n), fun φ hφ => ?_⟩
  obtain ⟨p, C, hpc, hC, hb⟩ := hQ F E σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc B.emb n d X.J W.J hJ hJ' Ω Ω' hΩ hΩ' C N hC
  obtain ⟨K₂, h₂⟩ := hN C₁ hC₁
  set K : ℝ := (K₁ * K₂ + 1) * (max C₀ 0 * B₀) ^ N₀ * A ^ (m + D * n) with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨NNReal.mk K hK0 • p, (continuous_const.mul hpc : Continuous fun f => K * p f), fun f g h => ?_⟩
  obtain ⟨γ, hγ, s₁, hs, κ, hκ, e⟩ := hcov g
  obtain ⟨δ, hδ, t, ht', κ', hκ', e'⟩ := hcov' h
  have hpf : 0 ≤ p f := apply_nonneg p f
  obtain ⟨hw, hv0, hv⟩ := hP n d fr.r fr'.r s₁ t hs ht'
  set S := ∑ i, s₁ i with hSdef
  set T := ∑ j, t j with hTdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hs.2 i
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => ht'.2 i
  have hST : S ≤ T + viol s₁ t := by
    have := hv fr.r le_rfl
    rw [psum_self] at this
    linarith [psum_le ht' fr.r]
  have e1 := hb f g h
  rw [← hI F E σ hc B.emb n d X.J W.J hJ hJ' C N (fullRank E n d) (by simp) γ hγ δ hδ g h, e, e'] at e1
  have e2 := e1.trans (mul_le_mul_right ((h₁ _ _ _ κ hκ κ' hκ').trans (mul_le_mul_right (h₂ s₁ hs t ht') _)) _)
  set x : ℝ := D * posWt n d s₁ t - m * viol s₁ t with hx
  have e3 : ‖theta om (pureA F f φ) g h‖ ^ 2 ≤ p f ^ 2 * (K₁ * (K₂ * Real.exp x)) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow hpf, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_coe_nnreal (p := K₂), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)] at e2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 e2
  have e4 : ‖theta om (pureA F f φ) g h‖ ≤ p f * ((K₁ * K₂ + 1) * Real.exp (x / 2)) := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine e3.trans ?_
    have h5 : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h6 : (0 : ℝ) ≤ K₁ * K₂ := by positivity
    rw [mul_pow, mul_pow, h5, ← mul_assoc (K₁ : ℝ)]
    gcongr
    nlinarith
  have e5 : (qht g : ℝ) ≤ max C₀ 0 * B₀ * Real.exp (k₀ * S) := by
    have a1 : (qht g : ℝ) ≤ ht (fr.a s₁) * B₀ := by
      have := (qht_le g hγ).trans (e ▸ (ht_mul_le _ _).trans (mul_le_mul_right (hB₀ κ hκ) _))
      exact_mod_cast this
    have a2 : (ht (fr.a s₁) : ℝ) ≤ max C₀ 0 * Real.exp (k₀ * S) :=
      (hht s₁ hs).1.trans (by gcongr; exact le_max_left _ _)
    calc _ ≤ _ := a1
      _ ≤ max C₀ 0 * Real.exp (k₀ * S) * B₀ := by gcongr
      _ = _ := by ring
  have e6 : x / 2 + N₀ * (k₀ * S) ≤ ((m + D * n : ℕ) : ℝ) * T := by
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have b1 : (D : ℝ) * posWt n d s₁ t ≤ D * (d * S + n * T) := mul_le_mul_of_nonneg_left hw hD0
    have hmr : (m : ℝ) = D * d + 2 * (k₀ * N₀) := by rw [hm]; push_cast; ring
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have b2 : (m : ℝ) * S ≤ m * (T + viol s₁ t) := mul_le_mul_of_nonneg_left hST hm0
    have b3 : (0 : ℝ) ≤ m * T := mul_nonneg hm0 hT0
    have b4 : (0 : ℝ) ≤ D * n * T := by positivity
    have b5 : (m : ℝ) * S = D * d * S + 2 * (N₀ * (k₀ * S)) := by rw [hmr]; ring
    rw [hx]
    push_cast
    nlinarith
  have e7 : Real.exp (((m + D * n : ℕ) : ℝ) * T) ≤ A ^ (m + D * n) * (ht h : ℝ) ^ (k₁ * (m + D * n)) := by
    rw [Real.exp_nat_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (hAk h δ hδ t ht' κ' hκ' e') _
  calc ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N₀
      ≤ p f * ((K₁ * K₂ + 1) * Real.exp (x / 2)) * (max C₀ 0 * B₀ * Real.exp (k₀ * S)) ^ N₀ := by gcongr
    _ = p f * ((K₁ * K₂ + 1) * (max C₀ 0 * B₀) ^ N₀) * Real.exp (x / 2 + N₀ * (k₀ * S)) := by
        rw [Real.exp_add, mul_pow _ (Real.exp _), ← Real.exp_nat_mul]; ring
    _ ≤ p f * ((K₁ * K₂ + 1) * (max C₀ 0 * B₀) ^ N₀) * (A ^ (m + D * n) * (ht h : ℝ) ^ (k₁ * (m + D * n))) := by
        gcongr
        exact (Real.exp_le_exp.2 e6).trans e7
    _ = (K * p f) * (ht h : ℝ) ^ (k₁ * (m + D * n)) := by rw [hKdef]; ring

theorem domSoU_of (hE : EpsOf) (hV : FinVolU) (hS : SoSemiU) : DomSoU := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base n X r s (Or.inl hp.herm)
  obtain ⟨k, hk⟩ := hS F E σ B n d X W M χX χW om r s r' s' hp 0
  refine ⟨k, fun φ hφ => ?_⟩
  obtain ⟨p, hpc, hb⟩ := hk φ hφ
  refine ⟨p, fun _ => 1, hpc, measurable_const, ?_, fun f g h => ?_⟩
  · rw [setLIntegral_one]
    exact hV F E σ hp.base.cm n X.J hJ M.μ M.dom hp.good.haar hp.good.dom
  · rw [mul_one, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa using hb f g h)

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.HermitianFormDetNeZero
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.EmbChart (atPlace atPlace_mul_right evFin_atPlace)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace PositivityTheory.ThKEst

namespace W

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (a : AF F) : (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hn a)]

theorem coef_eigen {ψ : AddChar (AF F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure]
    (Φ : (κ → AF F) → ℂ) (u w : (κ → AF F) × (κ → AF F)) (a : AF F) (h : schr ψ u Φ = ψ a • Φ) :
    coef F ψ μ Φ (fun x => Φ (-x)) w = ψ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2 + (a + a)) * coef F ψ μ Φ (fun x => Φ (-x)) w := by
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have key : ∀ y, Φ (y + u.1) = ψ (a - (y ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2))) * Φ y := fun y => by
    have := congrFun h y
    simp only [schr, Pi.smul_apply, smul_eq_mul] at this
    rw [sub_eq_neg_add, AddChar.map_add_eq_mul, mul_assoc, ← this, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  have key' : ∀ x, Φ (-(x + u.1)) = ψ (-(a - ((-(x + u.1)) ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2)))) * Φ (-x) := fun x => by
    have := key (-(x + u.1))
    rw [show -(x + u.1) + u.1 = -x by abel] at this
    rw [this, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  unfold coef
  rw [← integral_const_mul, ← integral_add_right_eq_self _ u.1]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [schr]
  rw [add_right_comm x u.1 w.1, key, key', map_mul, conj_psi hn]
  have e : ∀ p q s t t' : AF F, ∀ A B : ℂ, p + q + s = t + t' → ψ p * (ψ q * A) * (ψ s * B) = ψ t * (ψ t' * A * B) := by
    intro p q s t t' A B e
    have := congrArg ψ e
    simp only [AddChar.map_add_eq_mul] at this
    linear_combination A * B * this
  refine e _ _ _ _ _ _ _ ?_
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  simp only [add_dotProduct, neg_dotProduct]
  linear_combination (-(u.1 ⬝ᵥ u.2)) * h2

variable {v : Pl (F := F)}

theorem indep_of_rest {φ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ} (h : Rest (evFin F v) φ r) : Indep v r :=
  fun x t => h.1 x _ ((at_iff _).2 (funext fun i => (ep_mul _).trans (by rw [evFin_atPlace])))

theorem acts_schr (ψ : AddChar (AF F) ℂ) {w : (κ → AF F) × (κ → AF F)} (hw : ep v • w = w) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (schr ψ w) φ (schr (psv v ψ) (evP v w) φ) := fun r hr => by
  rw [schr_tens ψ w _ (indep_of_rest hr), offP_eq, sub_smul, hw, one_smul, sub_self, schr_zero]

end W

open W

theorem det_X {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact hasSig_det (h.sig w) (by
    rw [show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero])

theorem hermitian_form_det_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact hasSig_det (h.sig w) (by
    rw [det_smul, show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero,
      mul_zero])

theorem soCut_of : SoCut := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ
  classical
  obtain ⟨hφ, ι, hι, hz⟩ := hφ
  have h := hP.base.cm
  haveI := h.1
  have hψ := isCharAF hP.base.std
  generalize B.τ₁ = t at *
  generalize B.v₁ = v at *
  generalize B.ψ = ψ at *
  have hc : Continuous (psv v ψ) := hψ.1.comp cont_at
  obtain ⟨b, hb⟩ := (GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ).1 v
  haveI := nonarch_field (Fv F v)
  haveI : CharZero (Fv F v) := algebraRat.charZero _
  obtain ⟨m, g, hsum, hg⟩ := exists_cut (v.adicCompletionIntegers F)
    (isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v))
    (fun U hU => by
      obtain ⟨a, ha⟩ := GlobalTheory.SplitWeil.exists_cball_subset hU
      exact ⟨a, a.ne_zero, ha (by simp [GlobalTheory.SplitWeil.cball])⟩)
    (psv v ψ) (isLocallyConstant_addChar _ hc) (b := b) hb (hι.bij.mapsTo hφ) hz
  choose χ hχ hχg using fun i => hι.bij.surjOn (hg i).1
  have hu : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E), J.det ≠ 0 → ∃ P : GL (Fin m) (Fv F v), P.1 = J.map t := fun J hJ =>
    ⟨GeneralLinearGroup.mkOfDetNeZero (J.map t) (by
      rw [show (J.map t).det = t J.det from ((t : E →+* Fv F v).map_det J).symm]
      exact (map_ne_zero t).2 hJ), rfl⟩
  obtain ⟨P, hP'⟩ := hu _ (det_X hP.herm)
  obtain ⟨Q, hQ⟩ := hu _ (hermitian_form_det_ne_zero hP.skew)
  have hco : ∀ u, coB σ X W t u = -(P.1 * u.map (piW (t.comp σ)) * Q.1ᵀ) := fun u => by rw [coB, hP', hQ]
  have QQ : (Q⁻¹).1ᵀ * Q.1ᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  have coU : ∀ A Y, coB σ X W t (spM h t A (-((P⁻¹).1 * Y * (Q⁻¹).1ᵀ))) = Y := fun A Y => by
    rw [hco, spM_snd, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul, Matrix.mul_assoc, QQ, Matrix.mul_one]
  have epU : ∀ A A' : Matrix (Fin n) (Fin d) (Fv F v), ep v • spM h t A A' = spM h t A A' := fun A A' => by
    have := spM_off h t A A'
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e1 : ∀ u : Matrix (Fin n) (Fin d) (AE F E), -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * u.map (piW (t.comp σ)) *
      (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) = coB σ X W t u := fun u => by simp [coB]
  have sy : ∀ (U : Matrix (Fin n) (Fin d) (Fv F v)) z, symp (cA σ) (-1) (incM F X.J) (incM F W.J) z
      (spM h t (-U) 0) = atPlace v (trace (coB σ X W t z * Uᵀ)) := fun U z => by
    have := ev_symp h t hP.herm.herm hP.skew.skew z (spM h t (-U) 0)
    rw [spM_fst, neg_neg, hco (spM h t (-U) 0), spM_snd] at this
    simp only [Matrix.mul_zero, Matrix.zero_mul, neg_zero, trace_zero, sub_zero] at this
    rw [← this, ← ep_mul, M.co.form]
    conv_lhs => rw [← epU, map_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul, mul_sub]
  refine ⟨m, χ, hι.bij.injOn hφ (Submodule.sum_mem _ fun i _ => hχ i) ?_, fun i => ⟨⟨hχ i, ι, hι, fun Y hY => ?_⟩, ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, hsum]
      exact Finset.sum_congr rfl fun i _ => (hχg i).symm
  · rw [hχg]
    exact (hg i).2.1 Y (hz Y hY)
  intro r hr μ hμ z hzr
  obtain ⟨Y₀, hY₀⟩ := (hg i).2.2
  obtain ⟨U, hU, hU'⟩ := hY₀ (coB σ X W t z) fun h' => hzr (rank_of_mul _ _ _ (rank_neg_full h'))
  have hw : ep v • M.co.e (spM h t (-U) 0) = M.co.e (spM h t (-U) 0) := by rw [← map_smul, epU]
  have ha := acts_schr ψ hw (χ i)
  have hs := schr_mem_SB hc (evP v (M.co.e (spM h t (-U) 0))) (hχ i)
  have eig : schr (psv v ψ) (evP v (M.co.e (spM h t (-U) 0))) (χ i) = psv v ψ (trace (Y₀ * Uᵀ)) • χ i := by
    refine hι.bij.injOn hs (Submodule.smul_mem _ _ (hχ i)) (funext fun Y => ?_)
    have := hι.mult _ ((at_iff _).2 (epU _ _)) (spM_snd h t _ _) _ (hχ i) _ hs ha
      (spM h t 0 (-((P⁻¹).1 * Y * (Q⁻¹).1ᵀ))) ((at_iff _).2 (epU _ _)) (spM_fst h t _ _)
    simp only [e1] at this
    rw [sy, coU, ← psv_apply] at this
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, hχg]
    by_cases h0 : g i Y = 0
    · simp [h0]
    · rw [hU Y h0]
  have hΦ := ha r hr
  rw [eig] at hΦ
  have := coef_eigen hψ.2.1 μ (tens (evFin F v) (χ i) r) _ (M.co.e z) (atPlace v (trace (Y₀ * Uᵀ)))
    (hΦ.trans (funext fun x => mul_assoc _ _ _))
  rw [← neg_sub, ← M.co.form, sy, ← map_add (f := _), ← map_neg, ← map_add (f := _), ← psv_apply] at this
  by_contra h0
  apply hU'
  have h1 := (mul_eq_right₀ h0).1 this.symm
  rw [← inv_eq_one, ← AddChar.map_neg_eq_inv, ← h1]
  congr 1
  rw [Matrix.sub_mul, Matrix.add_mul, trace_sub, trace_add]
  ring

end PositivityTheory.ThKEst
end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LatInv
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def latInvEquiv {E : Type} [Field E] {n d : ℕ} (a : GL (Fin n) E) (b : GL (Fin d) E) :
    Matrix (Fin n) (Fin d) E ≃ Matrix (Fin n) (Fin d) E where
  toFun x := a.1 * x * b.1ᵀ
  invFun x := (a⁻¹).1 * x * (b⁻¹).1ᵀ
  left_inv x := by
    have h1 : (a⁻¹).1 * a.1 = 1 := a.inv_mul
    have h2 : b.1ᵀ * (b⁻¹).1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show (b⁻¹).1 * b.1 = 1 from b.inv_mul, Matrix.transpose_one]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  right_inv x := by
    have h1 : a.1 * (a⁻¹).1 = 1 := a.mul_inv
    have h2 : (b⁻¹).1ᵀ * b.1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show b.1 * (b⁻¹).1 = 1 from b.mul_inv, Matrix.transpose_one]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem latInvEquiv_rank {E : Type} [Field E] {n d : ℕ} (a : GL (Fin n) E) (b : GL (Fin d) E)
    (x : Matrix (Fin n) (Fin d) E) : (latInvEquiv a b x).rank = x.rank := by
  have ha : IsUnit a.1.det := (Matrix.isUnit_iff_isUnit_det _).1 a.isUnit
  have hb : IsUnit b.1ᵀ.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
  change (a.1 * x * b.1ᵀ).rank = x.rank
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hb, Matrix.rank_mul_eq_right_of_isUnit_det _ _ ha]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem latInv_mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (γ : UA σ J) (hγ : γ ∈ ratU σ J) :
    ∃ a : GL (Fin n) E, ∀ g : UA σ J, mat (γ * g)⁻¹ = mat g⁻¹ * incM F a.1 := by
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 ((ratU σ J).inv_mem hγ)
  refine ⟨a, fun g => ?_⟩
  have h1 : mat γ⁻¹ = incM F a.1 := (congrArg Units.val ha).symm
  rw [mul_inv_rev, ← h1]
  rfl

theorem latInv_incM {n d : ℕ} (a : GL (Fin n) E) (b : GL (Fin d) E) (x : Matrix (Fin n) (Fin d) E) :
    incM F (latInvEquiv a b x) = incM F a.1 * incM F x * (incM F b.1)ᵀ := by
  change incM F (a.1 * x * b.1ᵀ) = _
  simp only [incM, Matrix.map_mul, Matrix.transpose_map]

theorem latInv_of : LatInv := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ C N S hS γ hγ δ hδ g h
  obtain ⟨a, ha⟩ := latInv_mat_inv_mul γ hγ
  obtain ⟨b, hb⟩ := latInv_mat_inv_mul δ hδ
  have hSS : ∀ x, x ∈ S ↔ latInvEquiv a b x ∈ S := by
    intro x
    rcases hS with rfl | rfl
    · simp
    · simp only [fullRank, Set.mem_setOf_eq, latInvEquiv_rank]
  unfold latSum
  rw [← Equiv.tsum_eq ((latInvEquiv a b).subtypeEquiv hSS)
    (fun x : S => ENNReal.ofReal (maj τ C N (mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ)))]
  refine tsum_congr fun x => ?_
  rw [Equiv.subtypeEquiv_apply, ha, hb, latInv_incM, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.CoefReal
section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.CoefRealA
noncomputable section

namespace PositivityTheory.ThKEst.RealFourierCoefficientBounds

open MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def q (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (M N : ℕ) : Seminorm ℂ (SchwartzMap V ℂ) :=
  (Finset.Iic (M, N)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2

theorem q_cont (M N : ℕ) : Continuous (q V M N) := by
  unfold q
  exact Seminorm.continuous_finsetSup (E := SchwartzMap V ℂ) (s := Finset.Iic (M, N))
    fun m _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm m

def H (f₁ f₂ : SchwartzMap V ℂ) (x : V) (u : V) : ℂ := f₁ (u + x) * (starRingEnd ℂ) (f₂ u)

theorem conj_smooth (f : SchwartzMap V ℂ) : ContDiff ℝ ∞ fun u => (starRingEnd ℂ) (f u) :=
  Complex.conjCLE.contDiff.comp (f.smooth ⊤)

theorem shift_smooth (f : SchwartzMap V ℂ) (x : V) : ContDiff ℝ ∞ fun u => f (u + x) :=
  (f.smooth ⊤).comp (contDiff_id.add contDiff_const)

theorem H_smooth (f₁ f₂ : SchwartzMap V ℂ) (x : V) : ContDiff ℝ ∞ (H f₁ f₂ x) :=
  (shift_smooth f₁ x).mul (conj_smooth f₂)

omit [InnerProductSpace ℝ V] in
theorem peetre (x u : V) : 1 + ‖x‖ ≤ (1 + ‖u + x‖) * (1 + ‖u‖) := by
  have h : ‖x‖ ≤ ‖u + x‖ + ‖u‖ := by simpa using norm_sub_le (u + x) u
  nlinarith [norm_nonneg (u + x), norm_nonneg u, mul_nonneg (norm_nonneg (u + x)) (norm_nonneg u)]

theorem H_bound (N D : ℕ) (f₁ f₂ : SchwartzMap V ℂ) (x u : V) {j : ℕ} (hj : j ≤ N) :
    (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D * ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤
      2 ^ N * ((2 ^ (N + D) * q V (N + D) N f₁) * (2 ^ (N + D) * q V (N + D) N f₂)) := by
  set A := 2 ^ (N + D) * q V (N + D) N f₁ with hA
  set B := 2 ^ (N + D) * q V (N + D) N f₂ with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (shift_smooth f₁ x) (conj_smooth f₂) u (n := j)
    (by exact_mod_cast le_top)
  have key : ∀ i ∈ Finset.range (j + 1), (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D *
      ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun u => f₁ (u + x)) u‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖) ≤ (j.choose i : ℝ) * (A * B) := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖ = ‖iteratedFDeriv ℝ (j - i) f₂ u‖ :=
      Complex.conjLIE.norm_iteratedFDeriv_comp_left f₂ u (j - i)
    rw [e1, iteratedFDeriv_comp_add_right (f := f₁)]
    have b1 : (1 + ‖u + x‖) ^ N * ‖iteratedFDeriv ℝ i f₁ (u + x)‖ ≤ A :=
      one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N + D, N)) (by simp) (by simp; omega) f₁ (u + x)
    have b2 : (1 + ‖u‖) ^ (N + D) * ‖iteratedFDeriv ℝ (j - i) f₂ u‖ ≤ B :=
      one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N + D, N)) (by simp) (by simp; omega) f₂ u
    have b3 : (1 + ‖x‖) ^ N ≤ (1 + ‖u + x‖) ^ N * (1 + ‖u‖) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (peetre x u) N
    calc _ ≤ ((1 + ‖u + x‖) ^ N * (1 + ‖u‖) ^ N) * (1 + ‖u‖) ^ D *
          ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f₁ (u + x)‖ * ‖iteratedFDeriv ℝ (j - i) f₂ u‖) := by
          gcongr
      _ = (j.choose i : ℝ) * (((1 + ‖u + x‖) ^ N * ‖iteratedFDeriv ℝ i f₁ (u + x)‖) *
          ((1 + ‖u‖) ^ (N + D) * ‖iteratedFDeriv ℝ (j - i) f₂ u‖)) := by ring
      _ ≤ _ := by gcongr
  calc _ ≤ (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D * ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun u => f₁ (u + x)) u‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A * B) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum key
    _ = 2 ^ j * (A * B) := by
        rw [← Finset.sum_mul]; congr 1; exact_mod_cast Nat.sum_range_choose j
    _ ≤ 2 ^ N * (A * B) := by gcongr; norm_num

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem wt_int : Integrable fun u : V => ((1 + ‖u‖) ^ (Module.finrank ℝ V + 1))⁻¹ := by
  have h := integrable_one_add_norm (E := V) (μ := volume) (r := ((Module.finrank ℝ V + 1 : ℕ) : ℝ))
    (by push_cast; linarith)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem H_int (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x : V) (j : ℕ), j ≤ N →
    Integrable (fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖) ∧
    (1 + ‖x‖) ^ N * ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤
      K * (q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂) := by
  set D := Module.finrank ℝ V + 1 with hD
  refine ⟨2 ^ N * 2 ^ (N + D) * 2 ^ (N + D) * ∫ u : V, ((1 + ‖u‖) ^ D)⁻¹, ?_, fun f₁ f₂ x j hj => ?_⟩
  · have : 0 ≤ ∫ u : V, ((1 + ‖u‖) ^ D)⁻¹ := integral_nonneg fun u => by positivity
    positivity
  set C := 2 ^ N * ((2 ^ (N + D) * q V (N + D) N f₁) * (2 ^ (N + D) * q V (N + D) N f₂)) with hC
  have hb : ∀ u, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤ C * ((1 + ‖u‖) ^ D)⁻¹ := by
    intro u
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have := H_bound N D f₁ f₂ x u hj
    linarith [mul_right_comm ((1 + ‖x‖) ^ N) ((1 + ‖u‖) ^ D) ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖]
  have hw : Integrable fun u : V => C * ((1 + ‖u‖) ^ D)⁻¹ := (wt_int (V := V)).const_mul C
  have hc : Continuous fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ :=
    ((H_smooth f₁ f₂ x).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have hi : Integrable fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ := by
    refine hw.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_norm]
    refine le_trans ?_ (hb u)
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg x]))
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  refine (integral_mono (hi.const_mul _) hw hb).trans (le_of_eq ?_)
  rw [integral_const_mul, hC]; ring

theorem fourier_bound (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x w : V),
    ‖𝓕 (H f₁ f₂ x) w‖ * (1 + ‖x‖ + ‖w‖) ^ N ≤
      K * (q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂) := by
  obtain ⟨K, hK, h⟩ := H_int (V := V) N
  refine ⟨2 ^ N * (2 * (2 ^ N * ((N + 1) * K))), by positivity, fun f₁ f₂ x w => ?_⟩
  set Q := q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have step : ∀ n ≤ N, (1 + ‖x‖) ^ N * (‖w‖ ^ n * ‖𝓕 (H f₁ f₂ x) w‖) ≤ 2 ^ N * ((N + 1) * K) * Q := by
    intro n hn
    have h1 := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := (N : ℕ∞)) (f := H f₁ f₂ x)
      ((H_smooth f₁ f₂ x).of_le (by exact_mod_cast le_top))
      (fun k m hk hm => by
        have hk0 : k = 0 := by simpa using hk
        subst hk0
        simpa using (h f₁ f₂ x m (by exact_mod_cast hm)).1)
      (k := 0) (n := n) (by simp) (by exact_mod_cast hn) w
    simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
      Finset.range_one, Finset.singleton_product, Finset.sum_map, Function.Embedding.sectR_apply] at h1
    calc _ ≤ (1 + ‖x‖) ^ N * (2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), (1 + ‖x‖) ^ N * ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ := by
          rw [← Finset.mul_sum]; ring
      _ ≤ 2 ^ n * ∑ _j ∈ Finset.range (n + 1), K * Q := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (by positivity)
          exact (h f₁ f₂ x j ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hn)).2
      _ = 2 ^ n * ((n + 1) * K) * Q := by simp; ring
      _ ≤ _ := by gcongr; norm_num
  have s0 := step 0 (Nat.zero_le _)
  have sN := step N le_rfl
  have e1 : (1 + ‖x‖ + ‖w‖) ^ N ≤ (1 + ‖x‖) ^ N * (1 + ‖w‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg w)]) N
  have e2 : (1 + ‖w‖) ^ N ≤ 2 ^ N * (1 + ‖w‖ ^ N) := by
    have := add_pow_le (zero_le_one' ℝ) (norm_nonneg w) N
    rw [one_pow] at this
    refine this.trans ?_
    gcongr
    · norm_num
    · omega
  calc _ ≤ ‖𝓕 (H f₁ f₂ x) w‖ * ((1 + ‖x‖) ^ N * (2 ^ N * (1 + ‖w‖ ^ N))) := by
        gcongr
        exact e1.trans (by gcongr)
    _ = 2 ^ N * ((1 + ‖x‖) ^ N * (‖w‖ ^ 0 * ‖𝓕 (H f₁ f₂ x) w‖) +
          (1 + ‖x‖) ^ N * (‖w‖ ^ N * ‖𝓕 (H f₁ f₂ x) w‖)) := by ring
    _ ≤ 2 ^ N * (2 ^ N * ((N + 1) * K) * Q + 2 ^ N * ((N + 1) * K) * Q) := by gcongr
    _ = _ := by ring

theorem main (N : ℕ) : ∃ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x y : V),
    ‖∫ u, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ u y : ℝ)) * f₁ (u + x) * (starRingEnd ℂ) (f₂ u)‖ *
      (1 + ‖x‖ + ‖y‖) ^ N ≤ p f₁ * p f₂ := by
  obtain ⟨K, hK, h⟩ := fourier_bound (V := V) N
  let c : NNReal := ⟨Real.sqrt K, Real.sqrt_nonneg K⟩
  refine ⟨c • q V (N + (Module.finrank ℝ V + 1)) N, ?_, fun f₁ f₂ x y => ?_⟩
  · exact (q_cont _ _).const_smul c
  have e : (∫ u, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ u y : ℝ)) * f₁ (u + x) *
      (starRingEnd ℂ) (f₂ u)) = 𝓕 (H f₁ f₂ x) (-y) := by
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [H, inner_neg_right, smul_eq_mul, mul_assoc]
    congr 2
    push_cast; ring
  have h1 := h f₁ f₂ x (-y)
  rw [norm_neg] at h1
  rw [e]
  refine h1.trans (le_of_eq ?_)
  have hc : (c : ℝ) * c = K := Real.mul_self_sqrt hK
  simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  rw [← hc]; ring

end PositivityTheory.ThKEst.RealFourierCoefficientBounds

end
end

namespace PositivityTheory.ThKEst

theorem coefReal_of : CoefReal := fun _ _ _ _ _ _ N => RealFourierCoefficientBounds.main N

end PositivityTheory.ThKEst
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.OneVar
noncomputable section

namespace PositivityTheory.ThKEst

open scoped NNReal ENNReal
open MeasureTheory Metric

section

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem oneVar_sep (Λ : Submodule ℤ V) [DiscreteTopology Λ] :
    ∃ ε : ℝ, 0 < ε ∧ Pairwise (Function.onFun Disjoint fun x : Λ => ball (x : V) ε) := by
  obtain ⟨δ, hδ, h⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set Λ)) 0 rfl
  refine ⟨δ / 2, by positivity, fun x y hxy => ?_⟩
  apply Metric.ball_disjoint_ball
  by_contra hlt
  push Not at hlt
  apply hxy
  have hm : x - y ∈ ball (0 : Λ) δ := by
    rw [mem_ball_zero_iff]
    have : ‖x - y‖ = dist (x : V) (y : V) := by
      rw [dist_eq_norm]; rfl
    linarith
  exact sub_eq_zero.1 (h hm)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem oneVar_pt {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε) (N : ℕ) {x y : V} (hy : y ∈ ball x ε) :
    ((1 + c * ‖x‖) ^ N)⁻¹ ≤ (1 + ε) ^ N * ((1 + ‖c • (1 : ℝ)‖ * ‖y‖) ^ N)⁻¹ := by
  have hcn : ‖c • (1 : ℝ)‖ = c := by simp [abs_of_pos hc]
  rw [hcn]
  have h1 : ‖y‖ ≤ ‖x‖ + ε := by
    have := mem_ball_iff_norm.1 hy
    have h2 := norm_le_norm_add_norm_sub' y x
    linarith
  have hx := norm_nonneg x
  have hy0 := norm_nonneg y
  have h2 : 1 + c * ‖y‖ ≤ (1 + ε) * (1 + c * ‖x‖) := by
    have : c * ‖y‖ ≤ c * (‖x‖ + ε) := mul_le_mul_of_nonneg_left h1 hc.le
    have h3 : c * ε ≤ ε := by nlinarith
    have h4 : 0 ≤ ε * (c * ‖x‖) := by positivity
    nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h2 N

theorem oneVar_core (Λ : Submodule ℤ V) [DiscreteTopology Λ] (N : ℕ) (hN : Module.finrank ℝ V < N) :
    ∃ K : ℝ≥0, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ K * ENNReal.ofReal ((c ^ Module.finrank ℝ V)⁻¹) := by
  borelize V
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  set μ : Measure V := Measure.addHaar with hμ
  obtain ⟨ε, hε, hd⟩ := oneVar_sep Λ
  set f : V → ℝ≥0∞ := fun y => ENNReal.ofReal (((1 + ‖y‖) ^ N)⁻¹) with hf
  have hfm : Measurable f := by
    rw [hf]; fun_prop
  have hI : ∫⁻ y, f y ∂μ < ⊤ := by
    have := finite_integral_one_add_norm (E := V) (μ := μ) (r := (N : ℝ)) (by exact_mod_cast hN)
    refine lt_of_eq_of_lt (lintegral_congr fun y => ?_) this
    rw [hf, Real.rpow_neg (by positivity), Real.rpow_natCast]
  set b : ℝ≥0∞ := μ (ball (0 : V) ε) with hb
  have hb0 : b ≠ 0 := (measure_ball_pos μ _ hε).ne'
  have hbt : b ≠ ⊤ := measure_ball_lt_top.ne
  set A : ℝ≥0∞ := ENNReal.ofReal ((1 + ε) ^ N) with hA
  have hK : b⁻¹ * A * ∫⁻ y, f y ∂μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hb0) ENNReal.ofReal_ne_top) hI.ne
  refine ⟨(b⁻¹ * A * ∫⁻ y, f y ∂μ).toNNReal, fun c hc hc1 => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  have hsc : ∫⁻ y, f (c • y) ∂μ = ENNReal.ofReal ((c ^ Module.finrank ℝ V)⁻¹) * ∫⁻ y, f y ∂μ := by
    rw [← lintegral_map hfm (measurable_const_smul c), Measure.map_addHaar_smul μ hc.ne', lintegral_smul_measure,
      abs_of_pos (by positivity), smul_eq_mul]
  have hpt : ∀ x : Λ, b * ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ A * ∫⁻ y in ball (x : V) ε, f (c • y) ∂μ := by
    intro x
    have e1 : b = μ (ball (x : V) ε) := (Measure.addHaar_ball_center μ _ _).symm
    rw [e1, mul_comm, ← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
    simp only [hf]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := oneVar_pt hc hc1 hε N hy
    simpa [norm_smul] using this
  have hsum : b * ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ A * ∫⁻ y, f (c • y) ∂μ := by
    rw [← ENNReal.tsum_mul_left]
    refine (ENNReal.tsum_le_tsum hpt).trans ?_
    rw [ENNReal.tsum_mul_left, ← lintegral_iUnion (fun _ => measurableSet_ball) hd]
    gcongr
    exact Measure.restrict_le_self
  calc ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹)
      = b⁻¹ * (b * ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hb0 hbt, one_mul]
    _ ≤ b⁻¹ * (A * ∫⁻ y, f (c • y) ∂μ) := by gcongr
    _ = _ := by rw [hsc]; ring

end

theorem oneVar_of : OneVar := by
  intro V _ _ _ Λ _ N hN
  obtain ⟨K, hK⟩ := oneVar_core Λ N hN
  refine ⟨K, fun l => ?_⟩
  have h := hK (Real.exp (-max 0 l)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by simp))
  rw [← Real.exp_nat_mul, ← Real.exp_neg, mul_neg, neg_neg] at h
  refine le_trans (ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal ?_) h
  have : Real.exp (-max 0 l) ≤ Real.exp (-l) := Real.exp_le_exp.2 (neg_le_neg (le_max_right _ _))
  gcongr

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.FrameBasis
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cm_invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem rId_zero : rId F 0 = 1 := by
  rw [rId, Real.exp_zero, sub_self, realAd, map_zero, map_zero, map_zero]
  exact add_zero (1 : AF F)

def formL (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := form σ J x y
  map_add' a b := by simp [form, add_dotProduct]
  map_smul' c a := by simp [form, smul_dotProduct]

omit [NumberField F] [NumberField E] in
theorem formL_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) : formL σ J y x = form σ J x y := rfl

theorem form_swap (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : EpsHerm σ J) :
    ∃ ε : E, ε * ε = 1 ∧ ∀ x y, form σ J y x = ε * σ (form σ J x y) := by
  have key : ∀ ε : E, (∀ i j, σ (J j i) = ε * J i j) → ε * ε = 1 → ∀ x y, form σ J y x = ε * σ (form σ J x y) := by
    intro ε h1 h2 x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, cm_invol h, h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    linear_combination (-(y j * J j i * σ (x i))) * h2
  rcases hJ.1 with h1 | h1
  · exact ⟨1, by simp, key 1 (by simpa using h1) (by simp)⟩
  · exact ⟨-1, by simp, key (-1) (by simpa using h1) (by simp)⟩

theorem frameBasis_of : FrameBasis := by
  intro F E _ _ _ _ _ σ hσ n J hJ fr hfr
  classical
  obtain ⟨ε, hε, hsw⟩ := form_swap hσ hJ
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have yx : ∀ i j, form σ J (fr.y i) (fr.x j) = if i = j then ε else 0 := by
    intro i j
    rw [hsw, hfr.xy]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  let K : Submodule E (Fin n → E) := ⨅ i, (LinearMap.ker (formL σ J (fr.x i)) ⊓ LinearMap.ker (formL σ J (fr.y i)))
  have hK : ∀ u, u ∈ K ↔ ∀ i, form σ J u (fr.x i) = 0 ∧ form σ J u (fr.y i) = 0 := by
    intro u
    simp [K, Submodule.mem_iInf, formL_apply]
  let bK := Module.finBasis E K
  let v : (Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K) → Fin n → E :=
    Sum.elim (Sum.elim fr.x fr.y) fun k => (bK k : Fin n → E)
  have hli : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ j, g (.inl (.inl j)) = 0 := by
      intro j
      have := congrArg (formL σ J (fr.y j)) hg
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, map_zero] at this
      simpa [Fintype.sum_sum_type, v, formL_apply, hfr.xy, hfr.yy, ((hK _).1 (bK _).2 j).2] using this
    have h2 : ∀ j, g (.inl (.inr j)) = 0 := by
      intro j
      have := congrArg (formL σ J (fr.x j)) hg
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, map_zero] at this
      simpa [Fintype.sum_sum_type, v, formL_apply, hfr.xx, yx, ((hK _).1 (bK _).2 j).1, hε0] using this
    have h3 : ∑ k, g (.inr k) • bK k = 0 := by
      apply Subtype.ext
      simpa [Fintype.sum_sum_type, v, h1, h2] using hg
    have h4 := Fintype.linearIndependent_iff.1 bK.linearIndependent _ h3
    rintro ((j | j) | j)
    exacts [h1 j, h2 j, h4 j]
  have hsp : ⊤ ≤ Submodule.span E (Set.range v) := by
    intro u _
    let a := ∑ i, form σ J u (fr.y i) • fr.x i + ∑ i, (ε * form σ J u (fr.x i)) • fr.y i
    have ha : a ∈ Submodule.span E (Set.range v) :=
      add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl (.inl i), rfl⟩))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl (.inr i), rfl⟩))
    have hu : u - a ∈ K := by
      rw [hK]
      intro j
      constructor
      · rw [← formL_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [a, map_sub, map_add (f := _), map_sum, map_smul, formL_apply, hfr.xx, yx, smul_eq_mul, mul_zero,
          Finset.sum_const_zero, mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linear_combination (-form σ J u (fr.x j)) * hε
      · rw [← formL_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [a, map_sub, map_add (f := _), map_sum, map_smul]
        simp [formL_apply, hfr.xy, hfr.yy]
    have hb : u - a ∈ Submodule.span E (Set.range v) := by
      have : u - a = ∑ k, bK.repr ⟨_, hu⟩ k • (bK k : Fin n → E) := by
        have := congrArg Subtype.val (bK.sum_repr ⟨_, hu⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr i, rfl⟩)
    simpa using add_mem hb ha
  let B := Module.Basis.mk hli hsp
  let e : ((Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K)) ≃ Fin n := B.indexEquiv (Pi.basisFun E (Fin n))
  let M : Matrix (Fin n) (Fin n) E := Matrix.of fun l k => v (e.symm k) l
  have hM : IsUnit M := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e.symm e.symm.injective
  let lam0 : (Fin fr.r ⊕ Fin fr.r) ⊕ Fin (Module.finrank E K) → (Fin fr.r → ℝ) →ₗ[ℝ] ℝ :=
    Sum.elim (Sum.elim (fun i => LinearMap.proj i) fun i => -LinearMap.proj i) fun _ => 0
  refine ⟨hM.unit, fun k => lam0 (e.symm k), ⟨fun i => e (.inl (.inl i)), fun i j h => by simpa using h⟩,
    ⟨fun i => e (.inl (.inr i)), fun i j h => by simpa using h⟩, fun i j h => by simpa using e.injective h,
    fun i t => ⟨congrArg (fun z => lam0 z t) (e.symm_apply_apply _), congrArg (fun z => lam0 z t) (e.symm_apply_apply _)⟩,
    fun k hk => ?_, fun i => congrArg v (e.symm_apply_apply _), fun t => ?_⟩
  · obtain ⟨k, rfl⟩ := e.surjective k
    rcases k with (j | j) | j
    · exact absurd rfl (hk j).1
    · exact absurd rfl (hk j).2
    · simp [lam0]
  · have key : ∀ k, mat (fr.a t) *ᵥ incV F (v k) = rId F (lam0 k t) • incV F (v k) := by
      rintro ((j | j) | j)
      · exact hfr.ax t j
      · exact hfr.ay t j
      · have := hfr.a0 t _ ((hK _).1 (bK j).2)
        simpa [lam0, rId_zero, v] using this
    ext l k
    have := congrFun (key (e.symm k)) l
    rw [Matrix.mul_diagonal, mul_comm, ← Algebra.smul_def]
    exact this

end PositivityTheory.ThKEst

end
end

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sqAll : SqAll := sqAll_of' coefSum coefEq_of (coefBd_of coefReal_of)

theorem sqSo : SqSo :=
  sqSo_of' soFin_of soCut_of (parity_of coefEq_of fourierInj_of) coefSum coefEq_of (coefBd_of coefReal_of)

theorem latTor : LatTor := latTor_of frameBasis_of oneVar_of

theorem latFull : LatFull := latFull_of latTor (minor_of frameBasis_of)

theorem domWeilU (h : GlobalTheory.Published.SiegelSetUnitary) : DomWeilU :=
  domWeilU_of grpTop_of epsOf_of (siegelAll_of h) sqAll latInv_of latMeas latCpt_of (latArch_of frameBasis_of) latTor
    Sq.posWt' Sq.square_integrable_integral_holds

theorem soSemiU (h : GlobalTheory.Published.SiegelSetUnitary) : SoSemiU :=
  soSemiU_of grpTop_of epsOf_of (siegelAll_of h) sqSo latInv_of latCpt_of latFull Sq.posWt'

theorem domSoU (h : GlobalTheory.Published.SiegelSetUnitary) : DomSoU := domSoU_of epsOf_of finVolU (soSemiU h)

theorem weilConv (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : WeilConv :=
  weilConv_of hB (domWeil_of_U (domWeilU h)) soFin_of

theorem soDecay (h : GlobalTheory.Published.SiegelSetUnitary) : SoDecay := soDecay_of (soSemi_of_U (soSemiU h)) soFin_of

theorem soCont (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : SoCont := soCont_of hB (domSoU h) soFin_of

theorem kDecay (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : KDecay :=
  kDecay_of hB Sq.triplePair_holds (weilConv h hB) (soDecay h) (domSoU h) soFin_of

theorem iCont (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : PositivityTheory.ThKF.ICont :=
  iCont_of hB grpTop_of epsOf_of (domWeil_of_U (domWeilU h)) (domSoU h) soFin_of

end PositivityTheory.ThKEst

end
