module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaUpToConstant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeUnitaryMaximalCompactEqProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeMaximalCompactInterIsotropicFlagLevi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaGaugeDefiniteAndUnitBodyVolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedIwasawaIntegralSmallBallAsymptotics
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SlabMeasureSqueeze
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SlabMeasureSqueezeStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLieAlgebrasRelativePosition
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLieAlgebrasRelativePosition
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.LiePos

variable {n : ℕ} {ε : Fin n → Bool}

theorem J_mul_J : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem inG_conjTranspose {X : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X) : Formalism.REAL.inG ε Xᴴ := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := J_mul_J
  have hJ' : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y) = Y := fun Y => by
    rw [← mul_assoc, hJ, one_mul]
  unfold Formalism.REAL.inG at *
  rw [conjTranspose_conjTranspose]
  have e := congrArg (fun M => Formalism.REAL.Jm ε * M * Formalism.REAL.Jm ε) h
  simp only [mul_add, add_mul, mul_assoc, hJ, hJ', mul_one, mul_zero, zero_mul] at e
  rw [add_comm]
  exact e

theorem inG_sub {X Y : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X) (k : Formalism.REAL.inG ε Y) :
    Formalism.REAL.inG ε (X - Y) := by
  unfold Formalism.REAL.inG at *
  rw [conjTranspose_sub, sub_mul, mul_sub]
  rw [show Xᴴ * Formalism.REAL.Jm ε - Yᴴ * Formalism.REAL.Jm ε + (Formalism.REAL.Jm ε * X - Formalism.REAL.Jm ε * Y) =
      (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X) - (Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y) by abel, h, k, sub_zero]

theorem comm_of_maxK {g : Formalism.REAL.UJ ε} (hg : g ∈ maxK ε) :
    uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g := by
  have hU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp hg
  calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hU]
    _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [mul_assoc]
    _ = Formalism.REAL.Jm ε * uMat g := by rw [h1, one_mul]

theorem skew_of_comm {X : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X)
    (hc : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X) : Xᴴ = -X := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := J_mul_J
  have h' : Xᴴ * Formalism.REAL.Jm ε = -(X * Formalism.REAL.Jm ε) := by
    rw [hc]; exact eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = -(X * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by rw [h']
    _ = -X := by rw [neg_mul, mul_assoc, hJ, mul_one]

theorem exp_unitary {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ = -Z) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Z))ᴴ * NormedSpace.exp ((t : ℂ) • Z) = 1 := by
  have hA : ((t : ℂ) • Z)ᴴ = -((t : ℂ) • Z) := by
    rw [conjTranspose_smul, hZ, smul_neg, Complex.star_def, Complex.conj_ofReal]
  have hc : Commute (-((t : ℂ) • Z)) ((t : ℂ) • Z) := (Commute.refl _).neg_left
  rw [← Matrix.exp_conjTranspose, hA, ← Matrix.exp_add_of_commute _ _ hc, neg_add_cancel, NormedSpace.exp_zero]

theorem mem_span_of_subset {S S' : Set (Formalism.REAL.UJ ε)} {d d' : ℕ} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    {E' : Fin d' → Matrix (Fin n) (Fin n) ℂ} (h : IsCut ε S E) (h' : IsCut ε S' E') (hS : S ⊆ S') (i : Fin d) :
    E i ∈ Submodule.span ℝ (Set.range E') := by
  obtain ⟨A', -, -, hA', hS'⟩ := h'
  have hT : E i ∈ A' := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε S d E h).2.1 A' (fun g hg => by
    have hg' : g ∈ S' := hS hg
    rw [hS'] at hg'
    exact hg') i
  exact (hA' _).1 ⟨hT, h.inG (Submodule.subset_span ⟨i, rfl⟩)⟩

theorem lieRel : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsCut ε (maxK ε ∩ flagM ε W) EL → LieRel EN EM EK EL := by
  intro n ε a j W hW dN dM dK dL EN EM EK EL hN hM hK hL
  obtain ⟨hlow, hkeep⟩ := GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps n ε a j W hW
  obtain ⟨htr, hle, hone, -⟩ := GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag n ε a j W hW
  have hENlow : ∀ i, EN i ∈ lowers ε W := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dN EN hN).2.1 (lowers ε W) hlow
  have hEMkeep : ∀ k, EM k ∈ keeps ε W :=
    (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dM EM hM).2.1 (keeps ε W) (fun m hm => sub_mem (hkeep m hm).1 hone)
  have hEMstar : ∀ k, (EM k)ᴴ ∈ keeps ε W := by
    let T2 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
      { carrier := {Y | Yᴴ ∈ keeps ε W}
        add_mem' := fun {A B} hA hB => by
          simp only [Set.mem_ofPred_eq, conjTranspose_add] at *
          exact add_mem hA hB
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, conjTranspose_zero]
          exact zero_mem _
        smul_mem' := fun c Y hY => by
          simp only [Set.mem_ofPred_eq] at *
          rw [conjTranspose_smul, star_trivial]
          exact Submodule.smul_mem _ c hY }
    exact (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dM EM hM).2.1 T2 (fun m hm => by
      change (uMat m - 1)ᴴ ∈ keeps ε W
      rw [conjTranspose_sub, conjTranspose_one]
      exact sub_mem (hkeep m hm).2 hone)
  let TC : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := {Y | Y * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Y}
      add_mem' := fun {A B} hA hB => by
        simp only [Set.mem_ofPred_eq] at *
        rw [add_mul, mul_add, hA, hB]
      zero_mem' := by simp
      smul_mem' := fun c Y hY => by
        simp only [Set.mem_ofPred_eq] at *
        rw [smul_mul_assoc, mul_smul_comm, hY] }
  have hEK : ∀ i, EK i ∈ TC := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dK EK hK).2.1 TC (fun g hg => by
    change (uMat g - 1) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (uMat g - 1)
    rw [sub_mul, mul_sub, one_mul, mul_one, comm_of_maxK hg])
  have hspan : Submodule.span ℝ (Set.range EK) ≤ TC :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hEK i)
  have hELK : ∀ i, EL i ∈ Submodule.span ℝ (Set.range EK) :=
    mem_span_of_subset hL hK Set.inter_subset_left
  refine ⟨fun i k => htr _ (hENlow i) _ (hEMstar k), fun i k => htr _ (hENlow i) _ (hEMkeep k),
    fun i k => htr _ (hENlow i) _ (hle (hENlow k)), mem_span_of_subset hL hM Set.inter_subset_right, hELK,
    fun i => skew_of_comm (hK.inG (hELK i)) (hspan (hELK i)), fun i => ?_⟩
  have hG : Formalism.REAL.inG ε (EN i) := hN.inG (Submodule.subset_span ⟨i, rfl⟩)
  have hY : Formalism.REAL.inG ε (EN i - (EN i)ᴴ) := inG_sub hG (inG_conjTranspose hG)
  have hskew : (EN i - (EN i)ᴴ)ᴴ = -(EN i - (EN i)ᴴ) := by
    rw [conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]
  refine (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dK EK hK).2.2 _ hY (fun t g hg => ?_)
  change (uMat g)ᴴ * uMat g = 1
  rw [hg]
  exact exp_unitary hskew t

end GlobalTheory.IwConst.LiePos
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLieAlgebrasRelativePositionStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_lieAlgebras_relative_position : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsCut ε (maxK ε ∩ flagM ε W) EL → LieRel EN EM EK EL := by
  first | exact @GlobalTheory.IwConst.LiePos.lieRel | exact GlobalTheory.IwConst.LiePos.lieRel | (intros; apply GlobalTheory.IwConst.LiePos.lieRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLintegralUnfoldCompactLevi
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLintegralUnfoldCompactLevi
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem iwasawa_shift_lintegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (M : Set G) (μM μK : Measure G) [SFinite μK] (δ φ ψ : G → ENNReal)
    (hδ : Measurable δ) (hφ : Measurable φ) (hψ : Measurable ψ) (hM : μM Mᶜ = 0) (l : G)
    (h1 : μM.map (fun g => g * l) = μM) (h2 : μK.map (fun g => l * g) = μK)
    (h3 : ∀ m ∈ M, δ (m * l) = δ m) (u : G) :
    ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM
      = ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM := by
  have hae : ∀ᵐ m ∂μM, m ∈ M := by rw [ae_iff]; exact hM

  have hK : ∀ m, ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK
      = ∫⁻ k, φ (u * (m * l⁻¹) * k) * ψ k ∂μK := by
    intro m
    conv_rhs => rw [← h2, show (fun g : G => l * g) = ⇑(MeasurableEquiv.mulLeft l) from rfl,
      lintegral_map_equiv]
    simp [mul_assoc]
  simp_rw [hK]

  conv_rhs => rw [← h1, show (fun g : G => g * l) = ⇑(MeasurableEquiv.mulRight l) from rfl,
    lintegral_map_equiv]
  apply lintegral_congr_ae
  filter_upwards [hae] with m hm
  simp [mul_assoc, h3 m hm]

theorem iwasawa_unfold_lintegral : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (M L : Set G) (μN μM μK νL : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] [SFinite νL] (δ φ ψ : G → ENNReal), Measurable δ → Measurable φ → Measurable ψ → μM Mᶜ = 0 → νL Lᶜ = 0 → (∀ l ∈ L, μM.map (fun g => g * l) = μM) → (∀ l ∈ L, μK.map (fun g => l * g) = μK) → (∀ l ∈ L, ∀ m ∈ M, δ (m * l) = δ m) → νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM ∂μN := by
  intro G _ _ _ M L μN μM μK νL _ _ _ _ δ φ ψ hδ hφ hψ hM hL h1 h2 h3
  have hLae : ∀ᵐ l ∂νL, l ∈ L := by rw [ae_iff]; exact hL

  have hH : Measurable fun p : G × G × G =>
      δ p.2.1 * ∫⁻ k, φ (p.1 * p.2.1 * k) * ψ (p.2.2 * k) ∂μK := by
    refine Measurable.mul (hδ.comp measurable_snd.fst) ?_
    exact Measurable.lintegral_prod_right'
      (f := fun q : (G × G × G) × G => φ (q.1.1 * q.1.2.1 * q.2) * ψ (q.1.2.2 * q.2)) (by fun_prop)
  have hX : Measurable fun p : G × G =>
      ∫⁻ m, δ m * ∫⁻ k, φ (p.1 * m * k) * ψ (p.2 * k) ∂μK ∂μM :=
    Measurable.lintegral_prod_right' (f := fun q : (G × G) × G =>
        δ q.2 * ∫⁻ k, φ (q.1.1 * q.2 * k) * ψ (q.1.2 * k) ∂μK)
      (hH.comp (f := fun q : (G × G) × G => (q.1.1, q.2, q.1.2)) (by fun_prop))

  have step1 : ∀ u m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK
      = ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := by
    intro u m
    have hg : Measurable fun l => ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK :=
      Measurable.lintegral_prod_right' (f := fun q : G × G => φ (u * m * q.2) * ψ (q.1 * q.2))
        (by fun_prop)
    calc δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK
        = δ m * ∫⁻ k, ∫⁻ l, φ (u * m * k) * ψ (l * k) ∂νL ∂μK := by
          congr 1
          exact lintegral_congr fun k => (lintegral_const_mul _ (hψ.comp (measurable_mul_const k))).symm
      _ = δ m * ∫⁻ l, ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := by
          congr 1
          exact lintegral_lintegral_swap (by
            exact (show Measurable fun q : G × G => φ (u * m * q.1) * ψ (q.2 * q.1) by fun_prop).aemeasurable)
      _ = ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := (lintegral_const_mul _ hg).symm
  have step2 : ∀ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM
      = ∫⁻ l, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂νL := by
    intro u
    calc _ = ∫⁻ m, ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL ∂μM :=
          lintegral_congr fun m => step1 u m
      _ = _ := lintegral_lintegral_swap (by
          exact (hH.comp (f := fun q : G × G => (u, q.1, q.2)) (by fun_prop)).aemeasurable)

  have key : ∀ᵐ l ∂νL, ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂μN
      = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN := by
    filter_upwards [hLae] with l hl
    exact lintegral_congr fun u =>
      (iwasawa_shift_lintegral M μM μK δ φ ψ hδ hφ hψ hM l (h1 l hl) (h2 l hl) (h3 l hl) u).symm
  calc νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN
      = ∫⁻ _l, (∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN) ∂νL := by
        rw [lintegral_const]; exact mul_comm _ _
    _ = ∫⁻ l, ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂μN ∂νL :=
        lintegral_congr_ae (key.mono fun _ hl => hl.symm)
    _ = ∫⁻ u, ∫⁻ l, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂νL ∂μN :=
        (lintegral_lintegral_swap (by exact hX.aemeasurable)).symm
    _ = _ := lintegral_congr fun u => (step2 u).symm

end GlobalTheory.IwConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLintegralUnfoldCompactLeviStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_lintegral_unfold_compact_levi : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (M L : Set G) (μN μM μK νL : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] [SFinite νL] (δ φ ψ : G → ENNReal), Measurable δ → Measurable φ → Measurable ψ → μM Mᶜ = 0 → νL Lᶜ = 0 → (∀ l ∈ L, μM.map (fun g => g * l) = μM) → (∀ l ∈ L, μK.map (fun g => l * g) = μK) → (∀ l ∈ L, ∀ m ∈ M, δ (m * l) = δ m) → νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM ∂μN := by
  first | exact @GlobalTheory.IwConst.iwasawa_unfold_lintegral | exact GlobalTheory.IwConst.iwasawa_unfold_lintegral | (intros; apply GlobalTheory.IwConst.iwasawa_unfold_lintegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagDimensionCount
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagDimensionCount
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem finrank_le_card_of_isotropic {n : ℕ} (ε : Fin n → Bool) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ x ∈ V, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0) (b : Bool) :
    Module.finrank ℂ V ≤ (univ.filter fun a => ε a = b).card := by

  let f : V →ₗ[ℂ] ({a // ε a = b} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : {a // ε a = b} → Fin n)) ∘ₗ V.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : ∀ a, ε a = b → (x : Fin n → ℂ) a = 0 := fun a ha => by
      simpa [f] using congrFun hx ⟨a, ha⟩
    have hterm : ∀ a, star ((x : Fin n → ℂ) a) * ((if ε a then (1 : ℂ) else -1) * (x : Fin n → ℂ) a)
        = (if b then (-1 : ℂ) else 1) * ((Complex.normSq ((x : Fin n → ℂ) a) : ℝ) : ℂ) := by
      intro a
      by_cases ha : ε a = b
      · simp [hx0 a ha]
      · have hb : ε a = !b := by cases h1 : ε a <;> cases b <;> simp_all
        rw [Complex.normSq_eq_conj_mul_self, hb]
        cases b <;> simp [Complex.star_def] <;> ring
    have h0 := hV x x.2
    simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, hterm,
      ← Finset.mul_sum] at h0
    have hc : (if b then (-1 : ℂ) else 1) ≠ 0 := by cases b <;> simp
    have hsum : (∑ a, Complex.normSq ((x : Fin n → ℂ) a) : ℝ) = 0 := by
      have := (mul_eq_zero.mp h0).resolve_left hc
      exact_mod_cast this
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).mp hsum
    ext a
    simpa using hall a (Finset.mem_univ a)
  calc Module.finrank ℂ V ≤ Module.finrank ℂ ({a // ε a = b} → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hf
    _ = Fintype.card {a // ε a = b} := Module.finrank_fintype_fun_eq_card ℂ
    _ = (univ.filter fun a => ε a = b).card := Fintype.card_subtype _

private theorem finrank_last_eq_sum_of_finrank_succ {n : ℕ} : ∀ (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), W 0 = ⊥ →
    (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) →
    Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i := by
  intro a
  induction a with
  | zero =>
    intro j W h0 _
    simp [show Fin.last 0 = (0 : Fin 1) from rfl, h0]
  | succ a ih =>
    intro j W h0 hstep
    have hprev := ih (fun i => j i.castSucc) (fun i => W i.castSucc) (by simpa using h0)
      (fun i => by have hs := hstep i.castSucc; rw [Fin.succ_castSucc] at hs; exact hs)
    rw [Fin.sum_univ_castSucc, ← hprev, ← Fin.succ_last, hstep (Fin.last a)]

theorem finrank_last_eq_sum {n : ℕ} {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : IsIsoFlag ε j W) :
    Module.finrank ℂ (W (Fin.last a)) = ∑ i, j i :=
  finrank_last_eq_sum_of_finrank_succ a j W h.1 h.2.2.1

private theorem sq_sum_eq_sum_sq_add_two_mul_sum_lt' {a : ℕ} (j : Fin a → ℕ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
  have split : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if i = k then j i * j k else 0) + (if k < i then j i * j k else 0) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have hsym : ∑ i, ∑ k, (if k < i then j i * j k else 0) = ∑ i, ∑ k, (if i < k then j i * j k else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hexp : ∑ i, ∑ k, j i * j k = ∑ i, ∑ k, ((if i < k then j i * j k else 0) +
      (if i = k then j i * j k else 0) + (if k < i then j i * j k else 0)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => split i k
  have hdiag : ∑ i, ∑ k, (if i = k then j i * j k else 0) = ∑ i, j i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp [sq]
  rw [sq, Finset.sum_mul_sum, hexp]
  simp only [Finset.sum_add_distrib]
  rw [hsym, hdiag]
  simp only [Finset.sum_filter]
  ring

theorem flag_dims : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → p + q = n ∧ n ^ 2 = 2 * dimN n j + ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) ∧ p ^ 2 + q ^ 2 = dimN n j + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) := by
  intro n ε a j W h p q hp hq
  have hpq : p + q = n := by
    rw [← hp, ← hq]
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun a => ε a = true)
    simpa using this

  have hV : ∀ x ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = 0 :=
    fun x hx => h.2.2.2 x hx x hx
  have hS := finrank_last_eq_sum h
  have hSp : ∑ i, j i ≤ p := by
    rw [← hS, ← hp]; exact finrank_le_card_of_isotropic ε _ hV true
  have hSq : ∑ i, j i ≤ q := by
    rw [← hS, ← hq]; exact finrank_le_card_of_isotropic ε _ hV false
  have hsq := sq_sum_eq_sum_sq_add_two_mul_sum_lt' j
  subst hpq
  simp only [dimN]
  set S := ∑ i, j i
  set X := ∑ i, j i ^ 2
  set T := ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k
  obtain ⟨P, rfl⟩ := Nat.exists_eq_add_of_le hSp
  obtain ⟨Q, rfl⟩ := Nat.exists_eq_add_of_le hSq
  have e1 : S + P + (S + Q) - 2 * S = P + Q := by omega
  have e2 : S + P - S = P := by omega
  have e3 : S + Q - S = Q := by omega
  rw [e1, e2, e3]
  refine ⟨by trivial, ?_, ?_⟩ <;> nlinarith [hsq]

end GlobalTheory.IwConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagDimensionCountStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlag_dimension_count : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → p + q = n ∧ n ^ 2 = 2 * dimN n j + ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) ∧ p ^ 2 + q ^ 2 = dimN n j + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) := by
  first | exact @GlobalTheory.IwConst.flag_dims | exact GlobalTheory.IwConst.flag_dims | (intros; apply GlobalTheory.IwConst.flag_dims <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightInvariantEqSmulLeftInvariantProbability
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightInvariantEqSmulLeftInvariantProbability
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem right_inv_eq_smul_left_inv :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (K : Set G) (μ ν : Measure G) [SFinite μ] [SFinite ν], μ Kᶜ = 0 → ν Kᶜ = 0 → μ Set.univ = 1 → (∀ k ∈ K, μ.map (fun g => k * g) = μ) → (∀ k ∈ K, ν.map (fun g => g * k) = ν) → ν = ν Set.univ • μ := by
  intro G _ _ _ K μ ν _ _ hμK hνK hμ1 hμinv hνinv
  ext A hA

  have hS : MeasurableSet {p : G × G | p.1 * p.2 ∈ A} := measurable_mul hA
  have hμae : ∀ᵐ g ∂μ, g ∈ K := by
    rw [ae_iff]
    exact hμK
  have hνae : ∀ᵐ g ∂ν, g ∈ K := by
    rw [ae_iff]
    exact hνK
  have h1 : (ν.prod μ) {p : G × G | p.1 * p.2 ∈ A} = ν Set.univ * μ A := by
    rw [Measure.prod_apply hS]
    have hc : ∀ᵐ h ∂ν, μ (Prod.mk h ⁻¹' {p : G × G | p.1 * p.2 ∈ A}) = μ A := by
      filter_upwards [hνae] with h hh
      show μ ((fun g => h * g) ⁻¹' A) = μ A
      rw [← Measure.map_apply (measurable_const_mul h) hA, hμinv h hh]
    rw [lintegral_congr_ae hc, lintegral_const, mul_comm]
  have h2 : (ν.prod μ) {p : G × G | p.1 * p.2 ∈ A} = ν A := by
    rw [Measure.prod_apply_symm hS]
    have hc : ∀ᵐ g ∂μ, ν ((fun h => (h, g)) ⁻¹' {p : G × G | p.1 * p.2 ∈ A}) = ν A := by
      filter_upwards [hμae] with g hg
      show ν ((fun h => h * g) ⁻¹' A) = ν A
      rw [← Measure.map_apply (measurable_mul_const g) hA, hνinv g hg]
    rw [lintegral_congr_ae hc, lintegral_const, hμ1, mul_one]
  rw [Measure.smul_apply, smul_eq_mul, ← h1, h2]

end GlobalTheory.IwConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightInvariantEqSmulLeftInvariantProbabilityStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_invariant_eq_smul_left_invariant_probability : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (K : Set G) (μ ν : Measure G) [SFinite μ] [SFinite ν], μ Kᶜ = 0 → ν Kᶜ = 0 → μ Set.univ = 1 → (∀ k ∈ K, μ.map (fun g => k * g) = μ) → (∀ k ∈ K, ν.map (fun g => g * k) = ν) → ν = ν Set.univ • μ := by
  first | exact @GlobalTheory.IwConst.right_inv_eq_smul_left_inv | exact GlobalTheory.IwConst.right_inv_eq_smul_left_inv | (intros; apply GlobalTheory.IwConst.right_inv_eq_smul_left_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaConstant
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.IwConst

open Filter Topology

theorem triple_mono {G : Type} [MeasurableSpace G] {N M K : Set G} {μN μM μK : Measure G} (hN : μN Nᶜ = 0)
    (hM : μM Mᶜ = 0) (hK : μK Kᶜ = 0) (δ : G → ENNReal) {F F' : G → G → G → ENNReal}
    (h : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, F u m k ≤ F' u m k) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k ∂μK ∂μM ∂μN ≤ ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F' u m k ∂μK ∂μM ∂μN := by
  refine lintegral_mono_ae ?_
  filter_upwards [show N ∈ ae μN from mem_ae_iff.mpr hN] with u hu
  refine lintegral_mono_ae ?_
  filter_upwards [show M ∈ ae μM from mem_ae_iff.mpr hM] with m hm
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine lintegral_mono_ae ?_
  filter_upwards [show K ∈ ae μK from mem_ae_iff.mpr hK] with k hk
  exact h u hu m hm k hk

theorem triple_const {G : Type} [MeasurableSpace G] (μN μM μK : Measure G) (δ : G → ENNReal)
    (F : G → G → G → ENNReal) {V β : ENNReal} (hV : V ≠ ⊤) (hβ : β ≠ ⊤) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k * β ∂(V • μK) ∂μM ∂μN =
      V * β * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k ∂μK ∂μM ∂μN := by
  have hVβ : V * β ≠ ⊤ := ENNReal.mul_ne_top hV hβ
  simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_mul_const' _ _ hβ]
  have key : ∀ u m, δ m * (V * ((∫⁻ k, F u m k ∂μK) * β)) = V * β * (δ m * ∫⁻ k, F u m k ∂μK) := by
    intro u m; ring
  simp_rw [key, lintegral_const_mul' _ _ hVβ]

theorem ballVol_ne_zero (d : ℕ) : ballVol d ≠ 0 := by
  unfold ballVol
  exact (Metric.measure_ball_pos _ _ one_pos).ne'

theorem ballVol_ne_top (d : ℕ) : ballVol d ≠ ⊤ := by
  unfold ballVol
  exact measure_ball_lt_top.ne

theorem volU_pos' (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  refine mul_pos (Finset.prod_pos fun l _ => ?_) (by positivity)
  positivity

theorem tendsto_mul_balls {f g : ℝ → ENNReal} {d e : ℕ} {V : ENNReal} (hV : V ≠ ⊤)
    (hf : Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (𝓝[>] 0) (𝓝 (ballVol d)))
    (hg : Tendsto (fun r : ℝ => g r / ENNReal.ofReal (r ^ e)) (𝓝[>] 0) (𝓝 (ballVol e))) :
    Tendsto (fun r : ℝ => V * f r * g r / ENNReal.ofReal (r ^ (d + e))) (𝓝[>] 0)
      (𝓝 (V * (ballVol d * ballVol e))) := by
  have hlim : Tendsto (fun r : ℝ => V * ((f r / ENNReal.ofReal (r ^ d)) * (g r / ENNReal.ofReal (r ^ e))))
      (𝓝[>] 0) (𝓝 (V * (ballVol d * ballVol e))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul hf (Or.inr (ballVol_ne_top e)) hg (Or.inr (ballVol_ne_top d))) (Or.inr hV)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) ≤ r := le_of_lt hr
  rw [pow_add, ENNReal.ofReal_mul (pow_nonneg hr' _), div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
  ring

private theorem hs_conjTranspose_mul_mul_of_unitary {n : ℕ} (U X : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    Formalism.REAL.hs (Uᴴ * X * U) = Formalism.REAL.hs X := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have key : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ((Formalism.REAL.hs Y : ℝ) : ℂ) = (Y * Yᴴ).trace := by
    intro Y
    simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  have h1 : ((Formalism.REAL.hs (Uᴴ * X * U) : ℝ) : ℂ) = ((Formalism.REAL.hs X : ℝ) : ℂ) := by
    rw [key, key, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc, hU', Matrix.mul_one]
  exact_mod_cast h1

private theorem map_mul_right_eq_of_isGaugeSub {n : ℕ} {ε : Fin n → Bool} (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    {d : ℕ} (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hAE : ∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E))
    (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub {g | uMat g - 1 ∈ A} d μ)
    (l : Formalism.REAL.UJ ε) (hl : uMat l - 1 ∈ A) (hu : (uMat l)ᴴ * uMat l = 1) :
    μ.map (fun g => g * l) = μ := by
  have huniq := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hE hAE μ hμ).2.2.1
  have hcut : IsCut ε {g | uMat g - 1 ∈ A} E := ⟨A, hA, hE, hAE, rfl⟩
  obtain ⟨H, hH, -⟩ := hcut.subgroup
  have hlH : l ∈ H := by rw [← SetLike.mem_coe, hH]; exact hl
  have hlinv : l⁻¹ ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ A} := by
    rw [← hH]; exact H.inv_mem hlH
  have hinvU : uMat l⁻¹ = (uMat l)ᴴ := by
    have h1 : uMat l⁻¹ * uMat l = 1 := by simp [uMat]
    calc uMat l⁻¹ = uMat l⁻¹ * (uMat l * (uMat l)ᴴ) := by rw [mul_eq_one_comm.mp hu, Matrix.mul_one]
      _ = (uMat l)ᴴ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  apply huniq
  obtain ⟨h0, hinv, hlim⟩ := hμ
  have he : (fun g : Formalism.REAL.UJ ε => g * l) = ⇑(MeasurableEquiv.mulRight l) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [he, MeasurableEquiv.map_apply, ← hH]
    have hpre : ⇑(MeasurableEquiv.mulRight l) ⁻¹' (↑H)ᶜ = (↑H : Set (Formalism.REAL.UJ ε))ᶜ := by
      ext g
      simp [H.mul_mem_cancel_right hlH]
    rw [hpre, hH]
    exact h0
  · intro s hs
    rw [Measure.map_map (measurable_const_mul s) (measurable_mul_const l),
      show ((fun g => s * g) ∘ fun g => g * l) = (fun g => g * l) ∘ (fun g => s * g) by
        funext g; simp [mul_assoc],
      ← Measure.map_map (measurable_mul_const l) (measurable_const_mul s), hinv s hs]
  · refine hlim.congr (fun r => ?_)
    congr 1
    rw [he, MeasurableEquiv.map_apply]
    conv_rhs => rw [← hinv l⁻¹ hlinv]
    have he2 : (fun g : Formalism.REAL.UJ ε => l⁻¹ * g) = ⇑(MeasurableEquiv.mulLeft l⁻¹) := rfl
    rw [he2, MeasurableEquiv.map_apply]
    congr 1
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq, MeasurableEquiv.coe_mulRight, MeasurableEquiv.coe_mulLeft]
    have hg : uMat (l⁻¹ * g * l) - 1 = (uMat l)ᴴ * (uMat g - 1) * uMat l := by
      rw [show uMat (l⁻¹ * g * l) = uMat l⁻¹ * uMat g * uMat l by simp [uMat], hinvU]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu]
    rw [hg, hs_conjTranspose_mul_mul_of_unitary _ _ hu]

private theorem lintegral_lintegral_mul_const {G : Type} [MeasurableSpace G] (μN μM μK : Measure G) (δ : G → ENNReal)
    (F : G → G → G → ENNReal) {β : ENNReal} (hβ : β ≠ ⊤) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k * β ∂μK ∂μM ∂μN = β * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k ∂μK ∂μM ∂μN := by
  have h := triple_const μN μM μK δ F (V := 1) ENNReal.one_ne_top hβ
  rw [one_smul, one_mul] at h
  exact h

private theorem lintegral_indicator_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G)
    {s : Set G} (hs : MeasurableSet s) (k : G) :
    ∫⁻ l, s.indicator 1 (l * k) ∂ν = ν {l | l * k ∈ s} := by
  have h := lintegral_indicator_one (μ := ν) (measurable_mul_const k hs)
  refine Eq.trans ?_ h
  congr 1

theorem iwasawa_constant : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (flagN ε W) (dimN n j) μN → IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM → μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) → ∀ (c : ℝ) (κ : ENNReal), IsGauge ε c → (∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ → ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN) → ENNReal.ofReal c * κ = ENNReal.ofReal (cIw p q j) := by
  intro n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv c κ hc hform
  obtain ⟨hpq, hn2, hdK⟩ := GlobalTheory.T.isotropicFlag_dimension_count n ε a j W hW p q hp hq
  obtain ⟨AN, EN, hAN, hEN, hAEN, hNset⟩ := GlobalTheory.T.exists_nilpotentAlgebra_isotropicFlagUnipotentRadical n ε a j W hW
  obtain ⟨AM, EM, hAM, hEM, hAEM, hMset⟩ := GlobalTheory.T.exists_algebra_isotropicFlagSelfAdjointLevi n ε a j W hW
  obtain ⟨⟨AK, EK, hAK, hEK, hAEK, hKset⟩, ⟨AL, EL, hAL, hEL, hAEL, hLset⟩⟩ :=
    GlobalTheory.T.exists_algebras_maxCompact_and_levi_inter n ε a j W hW p q hp hq
  have cN : IsCut ε (flagN ε W) EN := ⟨AN, hAN, hEN, hAEN, hNset⟩
  have cM : IsCut ε (flagM ε W) EM := ⟨AM, hAM, hEM, hAEM, hMset⟩
  have cK : IsCut ε (maxK ε) EK := ⟨AK, hAK, hEK, hAEK, hKset⟩
  have cL : IsCut ε (maxK ε ∩ flagM ε W) EL := ⟨AL, hAL, hEL, hAEL, hLset⟩
  have hrel := GlobalTheory.T.iwasawa_lieAlgebras_relative_position n ε a j W hW _ _ _ _ EN EM EK EL cN cM cK cL
  obtain ⟨hnd, hvol⟩ := GlobalTheory.T.iwasawaGauge_definite_and_unitBody_volume n _ _ _ _ EN EM EK EL cN.isON cM.isON cK.isON cL.isON hrel hdK

  have hN' : IsGaugeSub {g | uMat g - 1 ∈ AN} (dimN n j) μN := by rw [← hNset]; exact hN
  have hM' : IsGaugeSub {g | uMat g - 1 ∈ AM} ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM := by
    rw [← hMset]; exact hM
  have : SigmaFinite μN := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε AN _ EN hAN hEN hAEN μN hN').1
  have : SigmaFinite μM := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε AM _ EM hAM hEM hAEM μM hM').1
  obtain ⟨νL, hνσ, hνL⟩ := GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε AL _ EL hAL hEL hAEL
  have := hνσ
  have hνL' : IsGaugeSub (maxK ε ∩ flagM ε W) ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) νL := by
    rw [hLset]; exact hνL
  have : IsFiniteMeasureOnCompacts νL := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε AL _ EL hAL hEL hAEL νL hνL).2.1
  obtain ⟨μ0, hμ0σ, hμ0⟩ := GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε AK _ EK hAK hEK hAEK
  have := hμ0σ
  have hμ0' : IsGaugeSub (maxK ε) (p ^ 2 + q ^ 2) μ0 := by rw [hKset]; exact hμ0
  have hVK := GlobalTheory.T.volume_unitaryMaximalCompact_eq_prod n ε p q hp hq μ0 hμ0'
  have hVL := GlobalTheory.T.volume_maximalCompact_inter_isotropicFlagLevi n ε p q hp hq a j W hW νL hνL'

  have rK : ∀ l ∈ maxK ε, μ0.map (fun g => g * l) = μ0 := fun l hl =>
    map_mul_right_eq_of_isGaugeSub AK EK hAK hEK hAEK μ0 hμ0 l (by
      have h : l ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ AK} := by rw [← hKset]; exact hl
      exact h) hl
  have rM : ∀ l ∈ maxK ε ∩ flagM ε W, μM.map (fun g => g * l) = μM := fun l hl =>
    map_mul_right_eq_of_isGaugeSub AM EM hAM hEM hAEM μM hM' l (by
      have h : l ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ AM} := by rw [← hMset]; exact hl.2
      exact h) hl.1
  have rL : ∀ l ∈ maxK ε ∩ flagM ε W, νL.map (fun g => g * l) = νL := fun l hl =>
    map_mul_right_eq_of_isGaugeSub AL EL hAL hEL hAEL νL hνL l (by
      have h : l ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ AL} := by rw [← hLset]; exact hl
      exact h) hl.1
  have : IsProbabilityMeasure μK := ⟨hK1⟩
  have hμ0eq := GlobalTheory.T.right_invariant_eq_smul_left_invariant_probability (Formalism.REAL.UJ ε) (maxK ε) μK μ0 hK0 hμ0'.1 hK1 hKinv rK
  rw [hVK] at hμ0eq

  have hvpos : ∀ i, 0 < volU i := volU_pos'
  have hVtop : ENNReal.ofReal (volU p * volU q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hδ := GlobalTheory.T.leviFactorInverseModulus_properties n ε a j W
  have hΓtop : volume {v | gau EN EM EK EL v ≤ 1} ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ballVol_ne_top _)) (ballVol_ne_top _)
  obtain ⟨ρ₀, hρ₀, hlimS⟩ := GlobalTheory.T.localisedIwasawaIntegral_smallBall_asymptotics n ε a j W hW _ _ _ _ EN EM EK EL cN cM cK cL.isON hnd hΓtop
    μN μM μ0 hN hM hμ0'
  have hρ : 0 < min ρ₀ (1 / 8) := lt_min hρ₀ (by norm_num)
  have hS := hlimS (min ρ₀ (1 / 8)) hρ (min_le_left _ _)
  set ρ := min ρ₀ (1 / 8) with hρdef

  obtain ⟨Fp, hFp⟩ : ∃ F : ℝ → ENNReal, F = fun r =>
      ∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) ∂μ0 ∂μM ∂μN := ⟨_, rfl⟩
  obtain ⟨Sp, hSp⟩ : ∃ F : ℝ → ENNReal, F = fun r =>
      ∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) * (slab ε EL ρ r).indicator 1 k
        ∂μ0 ∂μM ∂μN := ⟨_, rfl⟩
  have hBtop : ∀ s, νL (hsBall ε s) ≠ ⊤ := fun s => ((isCompact_hsBall ε s).measure_lt_top).ne

  have hFmono : ∀ s r, s ≤ r → Fp s ≤ Fp r := by
    intro s r hsr
    simp only [hFp]
    refine triple_mono hN.1 hM.1 hμ0'.1 _ (fun u _ m _ k _ => ?_)
    refine Set.indicator_le_indicator_of_subset (fun g hg => ?_) (fun _ => by positivity) _
    exact (le_trans hg hsr : nrm (uMat g - 1) ≤ r)

  have hsand : ∀ η : ℝ, 0 < η → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      νL (hsBall ε (r / (1 + η))) * Fp r ≤ νL Set.univ * Sp r ∧
        νL Set.univ * Sp r ≤ νL (hsBall ε ((1 + η) * r)) * Fp r := by
    intro η hη
    filter_upwards [GlobalTheory.T.slab_measure_squeeze' n ε a j W hW _ EL cL hrel.2.2.2.2.2.1 νL hνL'.1 rL ρ η hρ
      (min_le_right _ _) hη] with r hr
    have hswap := GlobalTheory.T.iwasawa_lintegral_unfold_compact_levi (Formalism.REAL.UJ ε) (flagM ε W) (maxK ε ∩ flagM ε W) μN μM μ0 νL (dlt j W)
      ((hsBall ε r).indicator 1) ((slab ε EL ρ r).indicator 1) hδ.1
      (measurable_one.indicator (measurableSet_hsBall ε r)) (measurable_one.indicator (measurableSet_slab ε EL ρ r))
      hM.1 hνL'.1 rM (fun l hl => hμ0'.2.1 l hl.1) hδ.2.1
    simp only [hSp, hFp]
    rw [hswap]
    constructor
    · rw [← lintegral_lintegral_mul_const _ _ _ _ _ (hBtop _)]
      refine triple_mono hN.1 hM.1 hμ0'.1 _ (fun u hu m hm k hk => ?_)
      by_cases hmem : u * m * k ∈ hsBall ε r
      · rw [Set.indicator_of_mem hmem, lintegral_indicator_mul_right νL (measurableSet_slab ε EL ρ r) k]
        simp only [Pi.one_apply, one_mul]
        exact (hr u hu m hm k hk hmem).1
      · simp [hmem]
    · rw [← lintegral_lintegral_mul_const _ _ _ _ _ (hBtop _)]
      refine triple_mono hN.1 hM.1 hμ0'.1 _ (fun u hu m hm k hk => ?_)
      by_cases hmem : u * m * k ∈ hsBall ε r
      · rw [Set.indicator_of_mem hmem, lintegral_indicator_mul_right νL (measurableSet_slab ε EL ρ r) k]
        simp only [Pi.one_apply, one_mul]
        exact (hr u hu m hm k hk hmem).2
      · simp [hmem]

  have hf : Tendsto (fun r : ℝ => ENNReal.ofReal c * Formalism.REAL.muG ε (hsBall ε r) / ENNReal.ofReal (r ^ (n ^ 2)))
      (𝓝[>] 0) (𝓝 (ballVol (n ^ 2))) := by
    have h3 := ((GlobalTheory.T.riemannianHaarGauge_whole_group n ε).1 c hc).2.2.2
    refine h3.congr (fun r => ?_)
    rw [Measure.smul_apply, smul_eq_mul]
    rfl
  have hg : Tendsto (fun r : ℝ => νL (hsBall ε r) /
      ENNReal.ofReal (r ^ ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2))) (𝓝[>] 0)
      (𝓝 (ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2))) := hνL'.2.2
  have hFK : ∀ r, Fp r = ENNReal.ofReal (volU p * volU q) *
      ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) *
        ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) ∂μK ∂μM ∂μN := by
    intro r
    have h := triple_const μN μM μK (dlt j W) (fun u m k => (hsBall ε r).indicator 1 (u * m * k)) hVtop
      ENNReal.one_ne_top
    simp only [mul_one] at h
    simp only [hFp]
    rw [hμ0eq, h]
    rfl
  have hmuG : ∀ r, Formalism.REAL.muG ε (hsBall ε r) = κ *
      ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) *
        ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) ∂μK ∂μM ∂μN := by
    intro r
    rw [← hform _ (measurable_one.indicator (measurableSet_hsBall ε r)), lintegral_indicator_one
      (measurableSet_hsBall ε r)]
  have hb : Tendsto (fun r : ℝ => ENNReal.ofReal c * κ * (Fp r * νL (hsBall ε r)) /
      ENNReal.ofReal (r ^ (n ^ 2 + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (volU p * volU q) * (ballVol (n ^ 2) *
        ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)))) := by
    refine (tendsto_mul_balls hVtop hf hg).congr (fun r => ?_)
    rw [hFK, hmuG]
    congr 1
    ring
  have hvtop : ENNReal.ofReal (volU p * volU q) * (ballVol (n ^ 2) *
      ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top hVtop (ENNReal.mul_ne_top (ballVol_ne_top _) (ballVol_ne_top _))
  have hF := GlobalTheory.T.tendsto_small_ball_density_of_squeeze (fun r => ENNReal.ofReal c * κ * (νL Set.univ * Sp r)) _ _ hvtop (fun η hη => by
    refine ⟨fun r => ENNReal.ofReal c * κ * (Fp r * νL (hsBall ε r)), hb, ?_⟩
    have h1η : (1 : ENNReal) ≤ ENNReal.ofReal (1 + η) := ENNReal.one_le_ofReal.mpr (by linarith)
    filter_upwards [hsand η hη, self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    constructor
    · refine le_trans ?_ (le_mul_of_one_le_left (by positivity) h1η)
      show ENNReal.ofReal c * κ * (Fp (r / (1 + η)) * νL (hsBall ε (r / (1 + η)))) ≤
        ENNReal.ofReal c * κ * (νL Set.univ * Sp r)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc Fp (r / (1 + η)) * νL (hsBall ε (r / (1 + η))) ≤ Fp r * νL (hsBall ε (r / (1 + η))) :=
            mul_le_mul_of_nonneg_right (hFmono _ _ (div_le_self hr0'.le (by linarith))) (by positivity)
        _ = νL (hsBall ε (r / (1 + η))) * Fp r := mul_comm _ _
        _ ≤ νL Set.univ * Sp r := hr.1
    · refine le_trans ?_ (le_mul_of_one_le_left (by positivity) h1η)
      show ENNReal.ofReal c * κ * (νL Set.univ * Sp r) ≤
        ENNReal.ofReal c * κ * (Fp ((1 + η) * r) * νL (hsBall ε ((1 + η) * r)))
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc νL Set.univ * Sp r ≤ νL (hsBall ε ((1 + η) * r)) * Fp r := hr.2
        _ ≤ νL (hsBall ε ((1 + η) * r)) * Fp ((1 + η) * r) :=
            mul_le_mul_of_nonneg_left (hFmono _ _ (by nlinarith)) (by positivity)
        _ = Fp ((1 + η) * r) * νL (hsBall ε ((1 + η) * r)) := mul_comm _ _)

  have hexp : dimN n j + ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2 + (p ^ 2 + q ^ 2)) =
      n ^ 2 + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) := by
    rw [hdK, hn2]; ring
  have hΓ0 : volume {v | gau EN EM EK EL v ≤ 1} ≠ 0 := by
    rw [hvol]
    refine mul_ne_zero (mul_ne_zero ?_ (ballVol_ne_zero _)) (ballVol_ne_zero _)
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hF2 : Tendsto (fun r => ENNReal.ofReal c * κ * (νL Set.univ * Sp r) /
      ENNReal.ofReal (r ^ (n ^ 2 + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal c * κ * νL Set.univ * volume {v | gau EN EM EK EL v ≤ 1})) := by
    rw [← hexp]
    refine (ENNReal.Tendsto.const_mul hS (Or.inl hΓ0)).congr (fun r => ?_)
    simp only [hSp]
    rw [mul_div_assoc, mul_div_assoc, mul_assoc]
  have heq := tendsto_nhds_unique hF2 hF

  rw [hvol, hVL, ← hn2] at heq
  have hB0 : ballVol (n ^ 2) * ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) ≠ 0 :=
    mul_ne_zero (ballVol_ne_zero _) (ballVol_ne_zero _)
  have hBt : ballVol (n ^ 2) * ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (ballVol_ne_top _) (ballVol_ne_top _)
  have hAL : 0 < (∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) *
      volU (q - ∑ i, j i) :=
    mul_pos (mul_pos (Finset.prod_pos fun i _ => mul_pos (hvpos _) (by positivity)) (hvpos _)) (hvpos _)
  have hT : (0 : ℝ) < (2 : ℝ) ^ ((dimN n j : ℝ) / 2) := by positivity
  have heq2 : ENNReal.ofReal c * κ * (ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2))) =
      ENNReal.ofReal (volU p * volU q) := by
    refine (ENNReal.mul_left_inj hB0 hBt).mp ?_
    rw [← heq]
    ring
  have hc0 : 0 ≤ cIw p q j := by
    unfold cIw
    exact (div_pos (mul_pos (by positivity) (mul_pos (hvpos p) (hvpos q))) hAL).le
  have hcIw : ENNReal.ofReal (cIw p q j) * (ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2))) =
      ENNReal.ofReal (volU p * volU q) := by
    rw [← ENNReal.ofReal_mul hAL.le, ← ENNReal.ofReal_mul hc0]
    congr 1
    have h2 : (2 : ℝ) ^ (-((dimN n j : ℝ) / 2)) * (2 : ℝ) ^ ((dimN n j : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    unfold cIw
    rw [hpq]
    rw [show ∀ x y z w : ℝ, x * y / z * (z * w) = x * w * y * (z / z) by intros; ring, div_self hAL.ne', h2]
    ring
  have hne0 : ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2)) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hAL).ne' (ENNReal.ofReal_pos.mpr hT).ne'
  have hnet : ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  exact (ENNReal.mul_left_inj hne0 hnet).mp (heq2.trans hcIw.symm)

end GlobalTheory.IwConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaConstantStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_integration_formula_constant : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (flagN ε W) (dimN n j) μN → IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM → μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) → ∀ (c : ℝ) (κ : ENNReal), IsGauge ε c → (∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ → ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN) → ENNReal.ofReal c * κ = ENNReal.ofReal (cIw p q j) := by
  first | exact @GlobalTheory.IwConst.iwasawa_constant | exact GlobalTheory.IwConst.iwasawa_constant | (intros; apply GlobalTheory.IwConst.iwasawa_constant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryIwasawaIntegrationFormulaRealPlace
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem iwasawaFormula : IwasawaFormula := by
  intro n ε p q hp hq a j hj W hW c μN μM μK hc hN hM hK0 hK1 hKinv φ hφ
  obtain ⟨κ, -, -, hκ⟩ := GlobalTheory.T.iwasawa_integration_formula_up_to_constant n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv
  have hconst := GlobalTheory.T.iwasawa_integration_formula_constant n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv c κ hc hκ
  rw [hκ φ hφ, ← mul_assoc, hconst]

end GlobalTheory.FlagMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryIwasawaIntegrationFormulaRealPlaceStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwasawa_integration_formula_real_place : IwasawaFormula := by
  first | exact @GlobalTheory.FlagMeas.iwasawaFormula | exact GlobalTheory.FlagMeas.iwasawaFormula | (intros; apply GlobalTheory.FlagMeas.iwasawaFormula <;> assumption)
end
