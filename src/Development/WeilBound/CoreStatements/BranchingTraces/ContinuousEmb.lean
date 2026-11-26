module

public import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportInt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurH
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.FromDS
public import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender

@[expose] public section

section -- merged from Development.WeilBound.HeckeVectors.HeckeDoubleCosets.HeckeCoefficientDegrees.DegreeHcOfGoodPresentFamily
noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.D.Upq.Coef

section UJ

open ReciprocityTheory.ChartRestriction.DS

theorem fdeg_gap (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (h : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      120 * (n : ℝ) ^ 3 ≤ h → 1 ≤ pOf ε → 1 ≤ qOf ε → v ≠ 0 →
      Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam := by
  obtain ⟨c, hc, hH⟩ := fdCons_muG n ε
  refine ⟨c, hc, fun lam h H _ _ _ σ v hl hσ hgap hh hp hq hv => ?_⟩
  have hn : 1 ≤ n := hp.trans ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
  have ht : thrStar ε ≤ 32 * (n : ℝ) ^ 3 := by
    have hp_le : pOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    have hq_le : qOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    have hq0_le : S7.q0 ε ≤ n := (min_le_right _ _).trans hq_le
    have hp_real : (pOf ε : ℝ) ≤ n := by exact_mod_cast hp_le
    have hq_real : (qOf ε : ℝ) ≤ n := by exact_mod_cast hq_le
    have hq0_real : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast hq0_le
    have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn_le_cube : (n : ℝ) ≤ (n : ℝ) ^ 3 := le_self_pow₀ hn_real (by norm_num)
    have hsq_le_cube : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 :=
      pow_le_pow_right₀ hn_real (by norm_num)
    unfold thrStar
    apply max_le
    · have hprod : (n : ℝ) * pOf ε * qOf ε ≤ n * n * n := by gcongr
      nlinarith
    · have hsqrt : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n :=
        Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
      have hprod : 16 * (n : ℝ) * S7.q0 ε ≤ 16 * n * n := by gcongr
      nlinarith
  refine hH lam H σ v hl hσ h hgap (by linarith) hp hq (fun μ hμ hg => ?_) hv
  have hq0 : 1 ≤ S7.q0 ε := by unfold S7.q0; omega
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε :=
      le_max_right _ _
    have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    linarith
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor S7.psiExists T hμ hg hq0 h8
  exact ⟨T, Ψ, hP⟩

end UJ


open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] [CompleteSpace Wp] [CompleteSpace Wq]

end CompanionTheory.D.Upq.Coef

end
end

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace PositivityTheory.UnitaryDecomposition

open Formalism.REAL Formalism.MainNotions.S

theorem idem_avg {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G → K →L[ℂ] K)
    (hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x)) (hadj : ∀ g x y, ⟪ρ g x, y⟫_ℂ = ⟪x, ρ g⁻¹ y⟫_ℂ) (hn : ∀ g x, ‖ρ g x‖ = ‖x‖)
    (hc : ∀ x, Continuous fun g => ρ g x) (φ : G → ℂ) (hφ : Integrable φ ν) (hsym : ∀ g, φ g⁻¹ = conj (φ g)) (κ : ℂ)
    (hconv : ∀ x, ∫ h, φ h * φ (h⁻¹ * x) ∂ν = κ * φ x) (b : K) :
    ∃ b' : K, (∀ a, ⟪b', a⟫_ℂ = ∫ h, φ h * ⟪b, ρ h a⟫_ℂ ∂ν) ∧ ⟪b', b'⟫_ℂ = κ * ⟪b', b⟫_ℂ := by
  classical
  have hbd : ∀ (x y : K) (g : G), ‖⟪x, ρ g y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := fun x y g => by
    calc ‖⟪x, ρ g y⟫_ℂ‖ ≤ ‖x‖ * ‖ρ g y‖ := norm_inner_le_norm _ _
      _ = ‖x‖ * ‖y‖ := by rw [hn]
  have hcont : ∀ x y : K, Continuous fun g => ⟪x, ρ g y⟫_ℂ := fun x y => continuous_const.inner (hc y)
  have hint : ∀ x y : K, Integrable (fun g => φ g * ⟪x, ρ g y⟫_ℂ) ν := fun x y =>
    hφ.mul_bdd (hcont x y).aestronglyMeasurable (Filter.Eventually.of_forall (hbd x y))
  let L : K →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∫ h, φ h * ⟪b, ρ h a⟫_ℂ ∂ν
      map_add' := fun x y => by
        simp only [map_add (f := _), inner_add_right, mul_add]
        exact integral_add (hint b x) (hint b y)
      map_smul' := fun c x => by
        simp only [map_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1
        funext h
        ring }
  have hLb : ∀ a, ‖L a‖ ≤ ((∫ h, ‖φ h‖ ∂ν) * ‖b‖) * ‖a‖ := fun a => by
    calc ‖L a‖ = ‖∫ h, φ h * ⟪b, ρ h a⟫_ℂ ∂ν‖ := rfl
      _ ≤ ∫ h, ‖φ h‖ * (‖b‖ * ‖a‖) ∂ν := by
        apply norm_integral_le_of_norm_le (hφ.norm.mul_const _)
        exact Filter.Eventually.of_forall fun h => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hbd b a h) (norm_nonneg _)
      _ = _ := by
        rw [integral_mul_const]
        ring
  set b' := (InnerProductSpace.toDual ℂ K).symm (L.mkContinuous _ hLb) with hb'
  have hb'a : ∀ a, ⟪b', a⟫_ℂ = ∫ h, φ h * ⟪b, ρ h a⟫_ℂ ∂ν := fun a => by
    rw [hb', InnerProductSpace.toDual_symm_apply]
    rfl
  refine ⟨b', hb'a, ?_⟩
  set F : G → ℂ := fun g => ⟪b, ρ g b⟫_ℂ with hF
  have hFinv : ∀ g, conj (F g) = F g⁻¹ := fun g => by
    simp only [hF]
    rw [inner_conj_symm, hadj]
  have hpt : ∀ h, ⟪b, ρ h b'⟫_ℂ = ∫ k, φ k * F (h * k) ∂ν := fun h => by
    have e1 : ⟪b, ρ h b'⟫_ℂ = conj ⟪b', ρ h⁻¹ b⟫_ℂ := by
      rw [inner_conj_symm, hadj, inv_inv]
    rw [e1, hb'a, ← integral_conj, ← integral_inv_eq_self (fun k => φ k * F (h * k)) ν]
    congr 1
    funext k
    show conj (φ k * ⟪b, ρ k (ρ h⁻¹ b)⟫_ℂ) = φ k⁻¹ * F (h * k⁻¹)
    rw [map_mul, ← hsym, ← hmul]
    change φ k⁻¹ * conj (F (k * h⁻¹)) = φ k⁻¹ * F (h * k⁻¹)
    rw [hFinv, _root_.mul_inv_rev, inv_inv]
  have hI : Integrable (Function.uncurry fun h g => φ h * φ (h⁻¹ * g) * F g) (ν.prod ν) := by
    have hP : Integrable (fun z : G × G => φ z.1 * φ (z.1⁻¹ * z.2)) (ν.prod ν) := by
      have he : MeasurableEmbedding (fun z : G × G => (z.1, z.1 * z.2)) :=
        (MeasurableEquiv.shearMulRight G).measurableEmbedding
      rw [← (measurePreserving_prod_mul ν ν).integrable_comp_emb he]
      simpa [Function.comp_def] using hφ.mul_prod hφ
    exact hP.mul_bdd ((hcont b b).comp continuous_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hbd b b z.2)
  have hmain : ∫ h, φ h * ⟪b, ρ h b'⟫_ℂ ∂ν = κ * ∫ h, φ h * ⟪b, ρ h b⟫_ℂ ∂ν := by
    calc ∫ h, φ h * ⟪b, ρ h b'⟫_ℂ ∂ν = ∫ h, φ h * ∫ k, φ k * F (h * k) ∂ν ∂ν := by
          congr 1
          funext h
          rw [hpt]
      _ = ∫ h, ∫ g, φ h * φ (h⁻¹ * g) * F g ∂ν ∂ν := by
          congr 1
          funext h
          rw [← integral_const_mul, ← integral_mul_left_eq_self (fun g => φ h * φ (h⁻¹ * g) * F g) h]
          congr 1
          funext g
          simp [mul_assoc]
      _ = ∫ g, ∫ h, φ h * φ (h⁻¹ * g) * F g ∂ν ∂ν := integral_integral_swap hI
      _ = ∫ g, κ * φ g * F g ∂ν := by
          congr 1
          funext g
          rw [integral_mul_const, hconv]
      _ = κ * ∫ h, φ h * ⟪b, ρ h b⟫_ℂ ∂ν := by
          rw [← integral_const_mul]
          simp [hF, mul_assoc]
  rw [hb'a b', hb'a b]
  exact hmain

variable {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

theorem emb_mul (a b : Matrix (Fin n) (Fin n) ℂ) : emb e (a * b) = emb e a * emb e b := by
  simp [emb, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem emb_one : emb e 1 = 1 := by simp [emb, Matrix.fromBlocks_one]

theorem emb_col (a : Matrix (Fin n) (Fin n) ℂ) (d : Fin (n + 1)) : emb e a d (zi e) = if d = zi e then 1 else 0 := by
  simp only [emb, zi, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases hq : e.symm d with i | ⟨⟩
  · have hd : d ≠ e (Sum.inr ()) := by
      intro hd'
      rw [hd', Equiv.symm_apply_apply] at hq
      cases hq
    simp [hd]
  · have hd : d = e (Sum.inr ()) := by rw [← hq, Equiv.apply_symm_apply]
    simp [hd]

theorem jm_emb (hF : Fits ε ε' e) : Jm ε = emb e (Jm ε') := by
  obtain ⟨h0, h1⟩ := hF
  simp only [zi] at h0
  ext i j
  obtain ⟨x, rfl⟩ := e.surjective i
  obtain ⟨y, rfl⟩ := e.surjective j
  simp only [emb, Jm, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.diagonal_apply, e.injective.eq_iff]
  rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩ <;> simp [Matrix.diagonal_apply, h0, h1, Matrix.one_apply]

theorem emb_ct (a : Matrix (Fin n) (Fin n) ℂ) : (emb e a)ᴴ = emb e aᴴ := by
  simp [emb, Matrix.fromBlocks_conjTranspose]

def embU (hF : Fits ε ε' e) (h : UJ ε') : UJ ε :=
  ⟨⟨emb e (um h), emb e (um h⁻¹), by rw [← emb_mul, ← emb_one (e := e)]; congr 1; exact h.1.mul_inv,
    by rw [← emb_mul, ← emb_one (e := e)]; congr 1; exact h.1.inv_mul⟩, by
    show (emb e (um h))ᴴ * Jm ε * emb e (um h) = Jm ε
    rw [jm_emb hF, emb_ct, ← emb_mul, ← emb_mul]
    exact congrArg _ h.2⟩

theorem um_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : um g⁻¹ = (um g)⁻¹ := Matrix.coe_units_inv g.1

theorem continuous_emb : Continuous fun h : UJ ε' => emb e (um h) := by
  have hu : Continuous fun h : UJ ε' => um h := Units.continuous_val.comp continuous_subtype_val
  refine continuous_matrix fun i j => ?_
  simp only [emb, Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize e.symm i = p
  generalize e.symm j = q
  rcases p with x | x <;> rcases q with y | y <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]
  · exact (continuous_apply y).comp ((continuous_apply x).comp hu)
  all_goals exact continuous_const

private theorem fdeg_of_isHCParam_sub_single_ne {m : ℕ} {lam : Fin m → ℝ} (s : Fin m)
    (h : Formalism.QuantumDeterminants.IsHCParam (lam - Pi.single s 1)) (a b : Fin m) (hab : a ≠ b) :
    |lam a - lam b| ≤ ((if a = s then 2 else 1) * (if b = s then 2 else 1) : ℝ) *
      |(lam - Pi.single s 1 : Fin m → ℝ) a - (lam - Pi.single s 1 : Fin m → ℝ) b| := by
  set l' := (lam - Pi.single s 1 : Fin m → ℝ) with hl'
  have hd : 1 ≤ |l' a - l' b| := by
    obtain ⟨ka, hka⟩ := h.2 a
    obtain ⟨kb, hkb⟩ := h.2 b
    have hne : l' a ≠ l' b := fun hq => hab (h.1.injective hq)
    have hk : ka ≠ kb := by
      rintro rfl
      apply hne
      linarith
    have hz : l' a - l' b = ((ka - kb : ℤ) : ℝ) := by
      push_cast
      linarith
    rw [hz]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hk)
  have hla : lam a = l' a + (if a = s then 1 else 0) := by
    rw [hl', Pi.sub_apply, Pi.single_apply]
    ring
  have hlb : lam b = l' b + (if b = s then 1 else 0) := by
    rw [hl', Pi.sub_apply, Pi.single_apply]
    ring
  rw [hla, hlb]
  have h1 := le_abs_self (l' a - l' b)
  have h2 := neg_abs_le (l' a - l' b)
  split_ifs with ha hb hb
  · exact absurd (ha.trans hb.symm) hab
  all_goals
    rw [abs_le]
    constructor <;> linarith

theorem fdeg_shift {m : ℕ} {lam : Fin m → ℝ} (s : Fin m) (h : Formalism.QuantumDeterminants.IsHCParam (lam - Pi.single s 1)) :
    Formalism.QuantumDeterminants.fdegHC lam ≤ 2 ^ (2 * m) * Formalism.QuantumDeterminants.fdegHC (lam - Pi.single s 1) := by
  set l' := lam - Pi.single s 1 with hl'
  set c : Fin m → ℝ := fun a => if a = s then 2 else 1 with hc
  have hc1 : ∀ a, 1 ≤ c a := fun a => by
    simp only [hc]
    split_ifs <;> norm_num
  unfold Formalism.QuantumDeterminants.fdegHC
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right
  · calc _ ≤ ∏ a : Fin m, ∏ b ∈ Finset.univ.filter (fun b => a < b), (c a * c b * |l' a - l' b|) := by
          apply Finset.prod_le_prod₀ (fun a _ => Finset.prod_nonneg fun b _ => abs_nonneg _)
          intro a _
          apply Finset.prod_le_prod₀ (fun b _ => abs_nonneg _)
          intro b hb
          exact fdeg_of_isHCParam_sub_single_ne s h a b (Finset.mem_filter.mp hb).2.ne
      _ = (∏ a : Fin m, ∏ b ∈ Finset.univ.filter (fun b => a < b), (c a * c b)) *
            ∏ a : Fin m, ∏ b ∈ Finset.univ.filter (fun b => a < b), |l' a - l' b| := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [← Finset.prod_mul_distrib]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _
            (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ => abs_nonneg _)
          calc ∏ a : Fin m, ∏ b ∈ Finset.univ.filter (fun b => a < b), (c a * c b)
                ≤ ∏ a : Fin m, ∏ b : Fin m, (c a * c b) := by
                apply Finset.prod_le_prod₀
                · intro a _
                  refine Finset.prod_nonneg fun b _ => ?_
                  have := hc1 a
                  have := hc1 b
                  positivity
                · intro a _
                  rw [Finset.prod_filter]
                  apply Finset.prod_le_prod₀
                  · intro b _
                    have := hc1 a
                    have := hc1 b
                    split_ifs <;> nlinarith
                  · intro b _
                    have := hc1 a
                    have := hc1 b
                    split_ifs <;> nlinarith
            _ = 2 ^ (2 * m) := by
                simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
                  Finset.prod_pow, hc, Finset.prod_ite_eq', Finset.mem_univ, if_true]
                ring
  · refine Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b hb => ?_
    exact sub_nonneg.mpr (Nat.cast_le.mpr (le_of_lt (Finset.mem_filter.mp hb).2))

end PositivityTheory.UnitaryDecomposition
