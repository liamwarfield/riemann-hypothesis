module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameDarbouxCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameSchwartzBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzThetaPolynomialGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzThetaPolynomialGrowth
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.FinDenom

theorem finDiv_finPart_mul' {F : Type} [Field F] [NumberField F] {N m : ℕ} {T : AF F} (hT : GlobalTheory.FinSupp.FinDiv F N ((m : AF F) * T))
    (a : 𝓞 F) : GlobalTheory.FinSupp.FinDiv F N (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) * T) := by
  intro v
  obtain ⟨b, hb, e⟩ := hT v
  have ha : algebraMap F (Fv F v) (a : F) ∈ v.adicCompletionIntegers F := HeightOneSpectrum.coe_mem_adicCompletionIntegers v a
  refine ⟨algebraMap F (Fv F v) (a : F) * b, mul_mem ha hb, ?_⟩
  have e1 : evFin F v (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F)))) =
      evFin F v (algebraMap F (AF F) ((m : F) * (a : F))) := rfl
  rw [map_mul, e1, AlgHom.commutes, map_mul, map_natCast]
  simp only [map_mul, map_natCast] at e
  rw [mul_comm ((m : Fv F v)) _, mul_assoc, e]
  ring

theorem finPart_mul_congr {F : Type} [Field F] [NumberField F] (x : AF F) {y z : AF F} (h : y.2 = z.2) :
    GlobalTheory.FinSupp.finPart F x * y = GlobalTheory.FinSupp.finPart F (x * z) :=
  Prod.ext (zero_mul _) (by show x.2 * y.2 = x.2 * z.2; rw [h])

theorem exists_denominator_of_finite_component : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
      ∀ (x : Fin n × Fin d → AF F) (ξ : Fin n × Fin d → F), (∀ i, (x i).2 = (algebraMap F (AF F) (ξ i)).2) →
        om (g, h) Φ x ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  have S := hP.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨N, hN1, hinv⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_small_heisenberg_lattice F (Fin n × Fin d) B.ψ hstd.1 Φ hΦ
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.exists_scale_movedHeisenbergLattice_polynomial_heights F E n d (Fin n × Fin d) M.co.e N hN1
  obtain ⟨D, hD1, hD⟩ := GlobalTheory.T.exists_bounded_denominator_standardChar_trivial F
  refine ⟨D * C, k, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hmT⟩ := hC g.1 h.1
  refine ⟨D * m, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_⟩
  · push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC (by positivity)
  · intro x ξ hxξ hξ i
    have key : ∀ a : 𝓞 F, B.ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * ((m : F) * ξ i)))) = 1 := by
      intro a
      set c : AF F := GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) with hc
      set y : Fin n × Fin d → AF F := c • Pi.single i 1 with hy
      set w' := M.co.e.symm (0, y) with hw'
      set p : UA σ X.J × UA σ W.J := (g, h) with hp
      set w := actAB (cA σ) p⁻¹ w' with hw
      have hwe : M.co.e w = c • M.co.e ((((g.1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
          M.co.e.symm (0, Pi.single i 1) * (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ) := by
        rw [hw, hw', hy, hp]
        rw [show ((0 : Fin n × Fin d → AF F), c • Pi.single i (1 : AF F)) = c • ((0 : Fin n × Fin d → AF F), Pi.single i (1 : AF F)) by simp]
        rw [LinearEquiv.map_smul, ← LinearEquiv.map_smul M.co.e]
        congr 1
        simp only [actAB, Prod.inv_mk, Subgroup.coe_inv]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hrho : M.co.rho B.ψ w Φ = Φ := by
        unfold Darboux.rho
        apply hinv
        intro l
        rw [hwe]
        obtain ⟨h1, h2⟩ := hmT i l
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul' h1 a
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul' h2 a
      have himpl := S.impl p w Φ hΦ
      rw [hrho] at himpl
      have hact : actAB (cA σ) p w = w' := by
        rw [hw]
        simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, hp]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
          Matrix.mul_one]
      rw [hact] at himpl
      have hx := congrFun himpl x
      simp only [Darboux.rho, hw', LinearEquiv.apply_symm_apply, schr, zero_dotProduct, mul_zero, add_zero] at hx
      have h1 : B.ψ (x ⬝ᵥ y) = 1 := by
        have hne : om p Φ x ≠ 0 := hξ
        exact (mul_eq_right₀ hne).1 hx.symm
      rw [hy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hc, finPart_mul_congr _ (hxξ i), ← map_mul] at h1
      convert h1 using 3
      ring_nf
    have := hD B.ψ hstd _ key
    convert this using 1
    push_cast
    ring

end GlobalTheory.FinDenom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzThetaPolynomialGrowthStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_theta_polynomial_growth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
      ∀ (x : Fin n × Fin d → AF F) (ξ : Fin n × Fin d → F), (∀ i, (x i).2 = (algebraMap F (AF F) (ξ i)).2) →
        om (g, h) Φ x ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  first | exact @GlobalTheory.FinDenom.exists_denominator_of_finite_component | exact GlobalTheory.FinDenom.exists_denominator_of_finite_component | (intros; apply GlobalTheory.FinDenom.exists_denominator_of_finite_component <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameSchwartzBound
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.TorusTheta

theorem min_pow_le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) : min 1 c ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [zero_add, pow_one]
      exact (min_le_right _ _).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : 0 < t ⟨i.val + 1, hj⟩ := hpos _
      calc min 1 c ^ (k + 1 + 1) = min 1 c * min 1 c ^ (k + 1) := by ring
        _ ≤ min 1 c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_right (min_le_right _ _) h3.le
        _ ≤ t i := h2
  have := key (r - i.val - 1) i (by omega)
  refine le_trans ?_ this
  exact pow_le_pow_of_le_one hm0.le hm1 (by omega)

theorem mul_norm_le_norm_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] {c' : ℝ} (hc' : 0 < c')
    (s : ι → ℝ) (hs : ∀ i, c' ≤ s i) (v : ι → V) : c' * ‖v‖ ≤ ‖fun i => s i • v i‖ := by
  rw [← le_div_iff₀' hc']
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [le_div_iff₀' hc']
  have hsi : 0 < s i := hc'.trans_le (hs i)
  calc c' * ‖v i‖ ≤ s i * ‖v i‖ := mul_le_mul_of_nonneg_right (hs i) (norm_nonneg _)
    _ = ‖s i • v i‖ := by rw [norm_smul, Real.norm_of_nonneg hsi.le]
    _ ≤ ‖fun i => s i • v i‖ := norm_le_pi_norm (fun i => s i • v i) i

theorem prod_elim_pow {κ : Type} [Fintype κ] {r : ℕ} (blk : κ → Option (Fin r)) (t : Fin r → ℝ) (f d : ℕ)
    (hcard : ∀ i : Fin r, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) :
    ∏ j, (blk j).elim 1 t ^ f = (∏ i, t i ^ (f * d)) ^ 2 := by
  rw [← Finset.prod_fiberwise (Finset.univ : Finset κ) blk (fun j => ((blk j).elim 1 t : ℝ) ^ f)]
  have h1 : ∀ o : Option (Fin r), ∏ j ∈ Finset.univ.filter (fun j => blk j = o), (blk j).elim 1 t ^ f =
      (o.elim 1 t ^ f) ^ (Finset.univ.filter (fun j => blk j = o)).card := by
    intro o
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl (fun o _ => h1 o), Fintype.prod_option]
  simp only [Option.elim_none, Option.elim_some, one_pow, one_mul, hcard]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GlobalTheory.TorusTheta

namespace GlobalTheory.TorusTheta

theorem theta_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt c hc Φ hΦ
  obtain ⟨co, blk, hrat, hcard, hact⟩ := GlobalTheory.T.witt_frame_darboux_coordinates F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt
  obtain ⟨M₁, om₁, e, c₀, hco, hP₁, hc₀, he⟩ := GlobalTheory.T.darboux_coords_rational_points F E σ B n d X W M χX χW om r s r' s' hP co hrat
  obtain ⟨N₀, k₃, C₃, hlat⟩ := GlobalTheory.LatScaleSum.thetaSum_norm_le_pow F (Fin n × Fin d)
  have heΦ := (he Φ hΦ).1
  obtain ⟨C₁, k₁, hdec⟩ := GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ N₀
  obtain ⟨C₂, k₂, hden⟩ := GlobalTheory.T.schwartz_theta_polynomial_growth F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ
  set c' : ℝ := min 1 c ^ r₀ with hc'def
  have hc'0 : 0 < c' := pow_pos (lt_min one_pos hc) _
  have hc'1 : c' ≤ 1 := pow_le_one₀ (lt_min one_pos hc).le (min_le_left _ _)
  refine ⟨‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃, k₁ + k₂ * k₃, ?_⟩
  intro t htc a hta a' ha' y h
  have tlow : ∀ i, c' ≤ t i := min_pow_le_of_mem_cone hc htc
  have tpos : ∀ i, 0 < t i := fun i => hc'0.trans_le (tlow i)
  set u : Fin n × Fin d → ℝ := fun j => (blk j).elim 1 t with hudef
  have hulow : ∀ j, c' ≤ u j := by
    intro j
    simp only [hudef]
    cases blk j with
    | none => exact hc'1
    | some i => exact tlow i
  have hupos : ∀ j, 0 < u j := fun j => hc'0.trans_le (hulow j)
  obtain ⟨κ, hκ, hom⟩ := GlobalTheory.T.torus_action_model_coordinates F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ a' u hupos
    (by rw [hco]; exact hact t tpos a hta a' ha')

  have hΨ0 : om (y, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΦ
  have hT : om (a', 1) (om (y, h) Φ) ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΨ0
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = om₁ (y, h) (e Φ) := ⟨_, rfl⟩
  have hΨ : Ψ ∈ schA F (Fin n × Fin d) := hΨdef ▸ (IsUWeilPair.isUSplitting hP₁.weil).pres _ _ heΦ
  have hmul : ((a' * y, h) : UA σ X.J × UA σ W.J) = (a', 1) * (y, h) := by
    ext <;> simp
  have hsplit : om (a' * y, h) Φ = om (a', 1) (om (y, h) Φ) := by
    rw [hmul, map_mul, Module.End.mul_apply]
  have heT : e (om (a', 1) (om (y, h) Φ)) = om₁ (a', 1) Ψ := by
    rw [(he _ hΨ0).2.2, (he Φ hΦ).2.2, hΨdef]
  have hthT : thetaSum F (om (a', 1) (om (y, h) Φ)) = c₀⁻¹ * thetaSum F (om₁ (a', 1) Ψ) := by
    rw [← heT, (he _ hT).2.1, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
  have hfun : om₁ (a', 1) Ψ = fun x => κ * Ψ (fun j => infScale F (u j) * x j) := funext (hom Ψ hΨ)
  have hkey : theta om Φ (a' * y) h =
      c₀⁻¹ * (κ * thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))) := by
    show thetaSum F (om (a' * y, h) Φ) = _
    rw [hsplit, hthT, hfun]
    unfold thetaSum
    rw [tsum_mul_left]

  have hκ' : ‖κ‖ = ∏ i, t i ^ (Module.finrank ℚ F * d) := by
    have h2 : ‖κ‖ ^ 2 = (∏ i, t i ^ (Module.finrank ℚ F * d)) ^ 2 := by
      rw [hκ]
      exact prod_elim_pow blk t _ d hcard
    have hnn : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
      Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
    exact (pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).1 h2

  set P : ℝ := (ht y : ℝ) * ht h with hPdef
  have hP0 : 0 ≤ P := mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  obtain ⟨m, hm1, hmC, hmint⟩ := hden y h
  have hdecay : ∀ ξ : Fin n × Fin d → F,
      ‖Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j)‖ *
        (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := by
    intro ξ
    beta_reduce
    have h1 := hdec y h (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))
    rw [← hΨdef] at h1
    have hnorm : c' * ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
      simp only [evI_infScale_mul]
      exact mul_norm_le_norm_smul hc'0 u hulow _
    have hle : 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        c'⁻¹ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) := by
      have hi : 1 ≤ c'⁻¹ := one_le_inv₀ hc'0 |>.2 hc'1
      have h3 : ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
          c'⁻¹ * ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
        rw [le_inv_mul_iff₀ hc'0]; exact hnorm
      nlinarith [norm_nonneg (fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i)))]
    have hpow : (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤
        (c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀ := by
      have h0 : 0 ≤ 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ :=
        add_nonneg zero_le_one (norm_nonneg _)
      have h4 := pow_le_pow_left₀ h0 hle N₀
      rw [mul_pow] at h4
      exact h4
    calc ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀
        ≤ ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          ((c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (c'⁻¹) ^ N₀ * (‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) := by ring
      _ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hint : ∀ ξ : Fin n × Fin d → F,
      Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j) ≠ 0 →
        ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
    intro ξ hne
    rw [hΨdef] at hne
    exact hmint _ ξ (fun i => infScale_mul_snd F (u i) _) hne
  have hS := hlat ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) m (fun x => Ψ (fun j => infScale F (u j) * x j)) hm1 hdecay hint

  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmk : (m : ℝ) ^ k₃ ≤ |C₂| ^ k₃ * P ^ (k₂ * k₃) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hm0 (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hP0 _))) k₃
  have hS' : ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖ ≤
      |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by
    refine hS.trans ?_
    calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) * (m : ℝ) ^ k₃
        ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (m : ℝ) ^ k₃ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hm0 _)
          calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) ≤ |C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁))| := le_abs_self _
            _ = |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c'⁻¹) ^ N₀),
                abs_of_nonneg (pow_nonneg hP0 _)]
      _ ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (|C₂| ^ k₃ * P ^ (k₂ * k₃)) :=
          mul_le_mul_of_nonneg_left hmk (by positivity)
      _ = |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by ring
  rw [hkey, norm_mul, norm_mul, norm_inv, hκ']
  have hT0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
  calc ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) * ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖)
      ≤ ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) *
          (|C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃))) := by gcongr
    _ = _ := by ring

end GlobalTheory.TorusTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameSchwartzBoundStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_witt_frame_schwartz_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  first | exact @GlobalTheory.TorusTheta.theta_torus_le | exact GlobalTheory.TorusTheta.theta_torus_le | (intros; apply GlobalTheory.TorusTheta.theta_torus_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelContinuousFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelContinuousFunctional
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaKernelCont

theorem theta_pureA_clm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ (g : UA σ X.J) (h : UA σ W.J),
    ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), theta om (pureA F f φ) g h = T f := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ g h
  obtain ⟨l, hl, hlθ⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  have hs := hP.weil.isUSplitting
  obtain ⟨T, hT⟩ := hs.adm (g, h) l hl φ hφ
  refine ⟨T, fun f => ?_⟩
  have hmem : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have hmem' : om (g, h) (pureA F f φ) ∈ schA F (Fin n × Fin d) := hs.pres (g, h) _ hmem
  rw [← hT f, LinearMap.comp_apply, hlθ _ hmem']
  rfl

end GlobalTheory.ThetaKernelCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelContinuousFunctionalStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_continuous_functional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ (g : UA σ X.J) (h : UA σ W.J),
    ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), theta om (pureA F f φ) g h = T f := by
  first | exact @GlobalTheory.ThetaKernelCont.theta_pureA_clm | exact GlobalTheory.ThetaKernelCont.theta_pureA_clm | (intros; apply GlobalTheory.ThetaKernelCont.theta_pureA_clm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameDomain
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.SiegelTheta

theorem transp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : GAd σ ((1 : E) • J.map σ)) :
    ∃ a' : UA σ J, (a' : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = HA.mat (AF F) σ ((1 : E) • J.map σ) a := by
  have e := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ (c := (1 : E)) one_ne_zero
  refine ⟨⟨HA.mat (AF F) σ ((1 : E) • J.map σ) a, ?_⟩, rfl⟩
  have : HA.mat (AF F) σ ((1 : E) • J.map σ) a ∈ HR (AF F) σ ((1 : E) • J.map σ) := a.2
  rw [← e] at this
  exact this

theorem ht_bdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) {C₀ K : Set (GAd σ J)} (hC₀ : IsCompact C₀) (hK : IsCompact K) :
    ∃ B : ℝ, ∀ x ∈ C₀, ∀ k ∈ K, (heightGL F (HA.mat (AF F) σ J (x * k)) : ℝ) ≤ B := by
  have hc : Continuous fun q : GAd σ J × GAd σ J => (heightGL F (HA.mat (AF F) σ J (q.1 * q.2)) : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp (continuous_subtype_val.comp (continuous_mul : Continuous fun p : GAd σ J × GAd σ J => p.1 * p.2)))
  obtain ⟨B, hB⟩ := ((hC₀.prod hK).image hc).bddAbove
  exact ⟨B, fun x hx k hk => hB ⟨(x, k), ⟨hx, hk⟩, rfl⟩⟩

end GlobalTheory.SiegelTheta

namespace GlobalTheory.SiegelTheta

theorem theta_le_seminorm_height_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hP : IsPair B M χX χW om r s r' s') (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (Ω C₀ : Set (GAd σ ((1 : E) • X.J.map σ))) (K : Subgroup (GAd σ ((1 : E) • X.J.map σ))) (c : ℝ),
      IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GAd σ ((1 : E) • X.J.map σ))) → 0 < c →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        a⁻¹ * p * a ∈ C₀) →
      ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)),
        ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J) (g : UA σ X.J), ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
          GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ k ∈ K,
          g.1 = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (p * a * k) →
          ‖theta om (pureA F f φ) g h‖ ≤
            C * (T.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f *
              (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr Ω C₀ K c hΩ hC₀ hK hc hconj φ hφ
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  obtain ⟨Bd, hBd⟩ := ht_bdd ((1 : E) • X.J.map σ) hC₀ hK
  let I := {q : UA σ W.J × UA σ X.J × GAd σ ((1 : E) • X.J.map σ) × (Fin r₀ → ℝ) × GAd σ ((1 : E) • X.J.map σ) ×
      GAd σ ((1 : E) • X.J.map σ) // q.2.2.1 ∈ Ω ∧ q.2.2.2.1 ∈ GlobalTheory.SiegelSet.cone r₀ c ∧
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf q.2.2.2.1 q.2.2.2.2.1 ∧ q.2.2.2.2.2 ∈ K ∧
      (q.2.1 : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (q.2.2.1 * q.2.2.2.2.1 * q.2.2.2.2.2)}
  have hT := fun q : I => GlobalTheory.T.theta_kernel_continuous_functional F E σ B n d X W M χX χW om r s r' s' hP φ hφ q.1.2.1 q.1.1
  choose T hT using hT
  let P : I → ℝ := fun q => ∏ i, q.1.2.2.2.1 i ^ (Module.finrank ℚ F * d)
  have hP0 : ∀ q : I, 0 < P q := fun q => Finset.prod_pos fun i _ => pow_pos (q.2.2.1.1 i) _
  have hpt : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, ∃ (N : ℕ) (C : ℝ), ∀ q : I,
      ‖((P q)⁻¹ • T q) f‖ ≤ C * (ht q.1.1 : ℝ) ^ N := by
    intro f
    obtain ⟨C₁, k₁, h₁⟩ := GlobalTheory.T.siegel_set_witt_frame_schwartz_bound F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr c hc (pureA F f φ)
      (Submodule.subset_span ⟨f, φ, hφ, rfl⟩)
    refine ⟨k₁, |C₁| * (max Bd 0) ^ k₁, fun q => ?_⟩
    obtain ⟨⟨h, g, p, t, a, k⟩, hp, htc, ha, hk, hg⟩ := q
    obtain ⟨a', ha'⟩ := transp hσ X.J a
    have hy : ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) =
        HA.mat (AF F) σ ((1 : E) • X.J.map σ) ((a⁻¹ * p * a) * k) := by
      have : (a⁻¹ * p * a) * k = a⁻¹ * (p * a * k) := by group
      rw [this]
      change (a' : GL (Fin n) (AE F E))⁻¹ * (g : GL (Fin n) (AE F E)) = _
      rw [ha', hg]
      rfl
    have hty : (ht (a'⁻¹ * g) : ℝ) ≤ max Bd 0 := by
      refine le_trans ?_ (le_max_left _ _)
      show (heightGL F ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) : ℝ) ≤ Bd
      rw [hy]
      exact hBd _ (hconj p hp t htc a ha) k hk
    have hb := h₁ t htc a ha a' ha' (a'⁻¹ * g) h
    rw [mul_inv_cancel_left] at hb
    have hPq : 0 < ∏ i, t i ^ (Module.finrank ℚ F * d) := Finset.prod_pos fun i _ => pow_pos (htc.1 i) _
    show ‖((∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ • T _) f‖ ≤ _
    rw [ContinuousLinearMap.smul_apply, ← hT, norm_smul, Real.norm_of_nonneg (inv_pos.2 hPq).le]
    have h0 : (0 : ℝ) ≤ (ht h : ℝ) := NNReal.coe_nonneg _
    have hy0 : (0 : ℝ) ≤ (ht (a'⁻¹ * g) : ℝ) := NNReal.coe_nonneg _
    calc (∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ * ‖theta om (pureA F f φ) g h‖
        ≤ (∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ * (C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ *
            ∏ i, t i ^ (Module.finrank ℚ F * d)) := mul_le_mul_of_nonneg_left hb (inv_pos.2 hPq).le
      _ = C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ := by field_simp
      _ ≤ |C₁| * ((max Bd 0) * ht h) ^ k₁ :=
          mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg hy0 h0) (mul_le_mul_of_nonneg_right hty h0) _)
            (pow_nonneg (mul_nonneg hy0 h0) _) (abs_nonneg _)
      _ = |C₁| * (max Bd 0) ^ k₁ * (ht h : ℝ) ^ k₁ := by rw [mul_pow]; ring
  obtain ⟨N, C, S, hN⟩ := GlobalTheory.T.uniform_schwartz_seminorm_bound (Fin n × Fin d → mixedEmbedding.mixedSpace F) I (fun q => (P q)⁻¹ • T q)
    (fun q => (ht q.1.1 : ℝ)) (fun q => NNReal.coe_nonneg _) hpt
  refine ⟨N, C, S, fun f h g p hp t htc a ha k hk hg => ?_⟩
  let q : I := ⟨(h, g, p, t, a, k), hp, htc, ha, hk, hg⟩
  have e1 : theta om (pureA F f φ) g h = P q • ((P q)⁻¹ • T q f) := by
    rw [smul_smul, mul_inv_cancel₀ (hP0 q).ne', one_smul]
    exact hT q f
  have e2 := hN q f
  simp only [ContinuousLinearMap.smul_apply] at e2
  rw [e1, norm_smul, Real.norm_of_nonneg (hP0 q).le]
  calc P q * ‖(P q)⁻¹ • T q f‖ ≤ P q * (C * (S.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left e2 (hP0 q).le
    _ = _ := by ring

end GlobalTheory.SiegelTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameDomainStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_witt_frame_domain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hP : IsPair B M χX χW om r s r' s') (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (Ω C₀ : Set (GAd σ ((1 : E) • X.J.map σ))) (K : Subgroup (GAd σ ((1 : E) • X.J.map σ))) (c : ℝ),
      IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GAd σ ((1 : E) • X.J.map σ))) → 0 < c →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        a⁻¹ * p * a ∈ C₀) →
      ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)),
        ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J) (g : UA σ X.J), ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
          GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ k ∈ K,
          g.1 = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (p * a * k) →
          ‖theta om (pureA F f φ) g h‖ ≤
            C * (T.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f *
              (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  first | exact @GlobalTheory.SiegelTheta.theta_le_seminorm_height_torus | exact GlobalTheory.SiegelTheta.theta_le_seminorm_height_torus | (intros; apply GlobalTheory.SiegelTheta.theta_le_seminorm_height_torus <;> assumption)
end
