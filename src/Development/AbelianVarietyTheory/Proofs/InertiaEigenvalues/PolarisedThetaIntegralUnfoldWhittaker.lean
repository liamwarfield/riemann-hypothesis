module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidSpanContinuousAutomorphicCuspidal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidSpanContinuousAutomorphicCuspidal
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.JSW.SpanProps

theorem avg_eq_zero {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {F : GA E a → ℂ}
    (hcont : Continuous F) (hleft : ∀ γ g, F (ratGL E a γ * g) = F g) (hc : IsCuspidal F)
    (r : ℕ) (hr : 0 < r) (hra : r ≤ a - 1) (g : GA E a) :
    avg (ratV E (UnipotentBlockColumnIndex a r (a - 1))) (fun x => F (blkU x * g)) = 0 := by
  have hra' : r < a := by omega
  have hper := per_blk (E := E) (r := r) (m := a - 1) hcont (fun c g => hleft _ g) g
  have hper2 : Per (ratN E a r) (fun x => F (blkU (blkIxHomeo r x) * g)) :=
    ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
      simp only [map_add (f := _)]
      exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
  have key := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratN E a r) (ratV E _) (isCoLat_ratV E (BlockIx a r))
    (isCoLat_ratV E _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
  rw [← key]
  have hfun : (fun x => F (blkU (blkIxHomeo r x) * g)) = fun x => F (unip x * g) :=
    funext fun x => by rw [← blkU_comp_equiv]; rfl
  rw [hfun] at hper2 ⊢
  letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
  haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice _ (ratN E a r) (isCoLat_ratV E (BlockIx a r))
  obtain ⟨-, -, -, hint⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average _ _ (isCoLat_ratV E (BlockIx a r)) μ 𝓕 hμ hF _ hper2
  have hc' := hc r hr hra' μ 𝓕 hμ hF g
  rw [hint, h1] at hc'
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc'
  exact hc'

end GlobalTheory.JSW.SpanProps

theorem GlobalTheory.JSW.mspanR_cont_left_avg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1))
    (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → ∀ φ ∈ GlobalTheory.JSW.mspanR π, Continuous φ ∧
    (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) ∧
    ∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0 := by
  intro E _ _ _ m π ω hω hc F hF
  have hπ : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπ F hF
  have h0 := (h []).2
  rw [GlobalTheory.JSW.word_nil] at h0
  refine ⟨h0.cont, h0.left, fun r hr hrm g => ?_⟩
  exact GlobalTheory.JSW.SpanProps.avg_eq_zero (a := m + 1) h0.cont h0.left h0.cusp r hr hrm g
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidSpanContinuousAutomorphicCuspidalStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1))
    (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → ∀ φ ∈ GlobalTheory.JSW.mspanR π, Continuous φ ∧
    (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) ∧
    ∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0 := by
  first | exact @GlobalTheory.JSW.mspanR_cont_left_avg | exact GlobalTheory.JSW.mspanR_cont_left_avg | (intros; apply GlobalTheory.JSW.mspanR_cont_left_avg; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittaker
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric _root_.Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem lastRow_uGL_mul (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (GroundTheory.Automorphic.FourierWhittaker.uGL X * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, GroundTheory.Automorphic.FourierWhittaker.coe_uGL, Matrix.mul_apply,
    GroundTheory.Automorphic.FourierWhittaker.uMat_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro c _ hc
    rw [if_neg (Ne.symm hc), dite_eq_right (not_lt.2 (Fin.le_last c)), zero_mul]
  · simp

theorem jswWhit_fT (φ : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (g : GA E (m + 1)) :
    GlobalTheory.JSW.whit (fT φ Φ) g = sqrtC Φ (yInf g) * GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv (yInf g))) := by
  simp only [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only
  rw [fT_of_lastRow (lastRow_uGL_mul X g), mul_assoc (GroundTheory.Automorphic.FourierWhittaker.uGL X) g]
  ring

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric _root_.Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem indN_eq_re (N : ℕ) (y : Fin (m + 1) → Af E) : indN N y = ((indN N y).re : ℂ) := by
  unfold indN; split_ifs <;> simp

theorem indN_re_nonneg (N : ℕ) (y : Fin (m + 1) → Af E) : 0 ≤ (indN N y).re := by
  unfold indN; split_ifs <;> simp

theorem wt_coe (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    (((wt N x g : ℝ≥0) : ℝ) : ℂ) = indN N (yFin g) * (detPow E (m + 1) x g : ℂ) := by
  have h0 : 0 ≤ detPow E (m + 1) x g := norm_nonneg _
  rw [wt, Real.coe_toNNReal _ (mul_nonneg (indN_re_nonneg N _) h0), Complex.ofReal_mul, ← indN_eq_re]

theorem sqrtC_mul_conj {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (u : Fin (m + 1) → Cinf E) :
    sqrtC Φ u * conj (sqrtC Φ u) = Φ u := by
  rw [sqrtC, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hΦ u).1]
  exact Complex.ext (by simp) (by simp [(hΦ u).2])

theorem psi_lastRow_eq {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ φ' : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) =
      fT φ Φ g * conj (fT φ' Φ g) * (((wt N x g : ℝ≥0) : ℝ) : ℂ) := by
  rw [wt_coe, fT, fT, map_mul]
  have h := sqrtC_mul_conj hΦ (yInf g)
  change φ (g * (infGL E (m + 1)) (secInv (yInf g))) * conj (φ' (g * (infGL E (m + 1)) (secInv (yInf g)))) *
    Φ (yInf g) * indN N (yFin g) * (detPow E (m + 1) x g : ℂ) = _
  rw [← h]
  ring

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric _root_.Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem uInt_eq {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ φ' : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.uInt φ φ' Φ N x g =
      GlobalTheory.JSW.whit (fT φ Φ) g * conj (GlobalTheory.JSW.whit (fT φ' Φ) g) * (((wt N x g : ℝ≥0) : ℝ) : ℂ) := by
  rw [wt_coe, jswWhit_fT, jswWhit_fT, map_mul]
  have h := sqrtC_mul_conj hΦ (yInf g)
  change GlobalTheory.JSW.whit φ (g * (infGL E (m + 1)) (secInv (yInf g))) *
    conj (GlobalTheory.JSW.whit φ' (g * (infGL E (m + 1)) (secInv (yInf g)))) *
    Φ (yInf g) * indN N (yFin g) * (detPow E (m + 1) x g : ℂ) = _
  rw [← h]
  ring


omit [_root_.NumberField.IsTotallyComplex E] in
theorem NE_eq_ratMirU_zero : GlobalTheory.CellDec.NE E (m + 1) = ratMirU E (m + 1) 0 := by
  have h : GlobalTheory.SmGL.unipB E (Fin (m + 1)) = mirU E (m + 1) 0 := by
    ext γ
    rw [GlobalTheory.SmGL.mem_unipB, mem_mirU_zero]
  rw [GlobalTheory.CellDec.NE, ratMirU, h]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isMir_of_mem_mirU_zero {γ : GL (Fin (m + 1)) E} (hγ : γ ∈ mirU E (m + 1) 0) : IsMir m γ := by
  intro i k h
  refine hγ i k (Nat.zero_le _) ?_
  rcases h with h | h
  · have := k.2; change (k : ℕ) ≤ i; omega
  · have := k.2; omega

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric _root_.Formalism.L2.Host

theorem enorm_uInt_self {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}
    {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ = ‖GlobalTheory.JSW.whit (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) := by
  rw [uInt_eq hΦ, enorm_mul, enorm_mul, RCLike.enorm_conj, pow_two]
  congr 1
  have h0 : (((wt N x g : ℝ≥0) : ℝ) : ℂ) = ((wt N x g : ℝ≥0) : ℂ) := rfl
  rw [h0, enorm_eq_nnnorm]
  congr 1
  ext
  simp

set_option synthInstance.maxHeartbeats 400000 in
theorem zint_unfold : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
  ∃ c : ℝ, 0 < c ∧ ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω →
    π'.HasCentChar ω' → ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (𝓕 𝓕₀ : Set (GA E (m + 1))), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ →
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, 1 < x → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.ZEul.uInt φ φ' Φ N x) 𝓕₀ μ ∧
        GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = (c : ℂ) * ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ := by
  intro E _ _ _ m μ _
  refine ⟨1, one_pos, ?_⟩
  intro π π' ω ω' hω hω' hπ hπ' φ φ' hφ hφ' N Φ _hN hΦs _hΦc hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x _hx h1 h2
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
  obtain ⟨𝓕P, h𝓕P⟩ : ∃ 𝓕P, IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ := by
    haveI : DiscreteTopology (ratMirU E (m + 1) m) := discrete_of_le_range (Subgroup.map_le_range _ _)
    exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ
  have h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ := NE_eq_ratMirU_zero (E := E) (m := m) ▸ h𝓕₀
  obtain ⟨hc, hl, hv⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π ω hω hπ φ hφ
  obtain ⟨hc', hl', hv'⟩ := GlobalTheory.T.cuspFormRapidSpan_continuous_automorphic_cuspidal E m π' ω' hω' hπ' φ' hφ'
  have hΦcont : Continuous Φ := hΦs.continuous
  have hG := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ hc hl hv Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  have hG' := GlobalTheory.T.archTranslatedSqrtWeightedFun_good_mirabolicTop E m φ' hc' hl' hv' Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  obtain ⟨hwm, hwΓ, hwU⟩ := GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant E m N x
  have hU := GlobalTheory.MirTower.unfold_mirabolic E (m + 1) μ (GlobalTheory.StdCharConductor.psi E) (GlobalTheory.StdCharConductor.stdPsi_psi E)
    𝓕P 𝓕₀ h𝓕P h𝓕₀' (wt N x) hwm hwΓ hwU
  have hW : ∀ f : GA E (m + 1) → ℂ, Good (GlobalTheory.StdCharConductor.psi E) m f → ∀ g,
      GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := fun f hf g =>
    GlobalTheory.T.globalWhittakerCoeff_eq_iteratedColumnTransform E m f hf.cont (fun γ hγ g => hf.left γ (isMir_of_mem_mirU_zero hγ) g) g
  have hd : ∫⁻ g in 𝓕P, ‖fT φ Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG]
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG]
    simp only [e]
    exact h1
  have hd' : ∫⁻ g in 𝓕P, ‖fT φ' Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG']
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG']
    simp only [e]
    exact h2
  obtain ⟨hI1, hI2, hEq⟩ := hU.2 _ _ hG hG' hd hd'
  have e1 : GlobalTheory.ZEul.uInt φ φ' Φ N x = fun g => GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g *
      conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g) * ((wt N x g : ℝ) : ℂ) := by
    funext g
    rw [uInt_eq hΦp, hW _ hG, hW _ hG']
  have e2 : (fun g => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)) =
      fun g => fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ) := funext fun g => psi_lastRow_eq hΦp φ φ' N x g
  have hfin : ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ := by
    rw [show (fun g => ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ) =
      fun g => ‖fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ)‖ₑ from funext fun g => by rw [psi_lastRow_eq hΦp]]
    exact hI1.2.ne
  refine ⟨by rw [e1]; exact hI2, ?_⟩
  have hUnfold := GlobalTheory.ZUnfTheta.zint_eq_mirabolic E m μ 𝓕 𝓕P h𝓕 h𝓕P
    φ φ' hc.measurable hc'.measurable hl hl' N Φ hΦcont x hfin
  rw [hUnfold, e2, Complex.ofReal_one, one_mul, e1]
  exact hEq

end GlobalTheory.ZUnf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittakerStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
open GlobalTheory.MirTower GlobalTheory.CuspGeneric GlobalTheory.RSJ GlobalTheory.ZUnf in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
  ∃ c : ℝ, 0 < c ∧ ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω →
    π'.HasCentChar ω' → ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (𝓕 𝓕₀ : Set (GA E (m + 1))), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ →
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, 1 < x → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.ZEul.uInt φ φ' Φ N x) 𝓕₀ μ ∧
        GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = (c : ℂ) * ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ := by
  exact @_root_.GlobalTheory.ZUnf.zint_unfold
end
