module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationRealMovesFrameDetChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumCompactVacuumReadsDetCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockVacAtOfReads
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.FockVac

theorem hasDerivAt_translate {n g : ℕ} (c : Fin g → ℝ) (H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ)
    (hH : ∀ z w, H z w = ∑ j, (c j : ℂ) * z j * conj (w j)) (F : (Fin n → Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F)
    (Z A : Fin n → Fin g → ℂ) :
    HasDerivAt (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A)))
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b)) *
        (-(Real.pi * ∑ b, H (A b) (Z b)) * F Z + fderiv ℂ F Z A)) 0 := by
  have hc : ∀ z w, conj (H z w) = H w z := fun z w => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hH, map_sum, map_mul, conj_ofReal, conj_conj]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e : (fun t : ℝ => cexp (Real.pi * I * ((∑ b, (H (Z b) (((t : ℂ) • A) b)).im : ℝ) : ℂ)) *
      (cexp (-(Real.pi / 2 : ℂ) * ∑ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b)) * F (Z + (t : ℂ) • A))) =
      fun t : ℝ => (fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) + (-(Real.pi * ∑ b, H (A b) (Z b)) * u +
        -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) t := by
    funext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    have h1 : ∀ b, I * ((H (Z b) (((t : ℂ) • A) b)).im : ℂ) = t * (H (Z b) (A b) - H (A b) (Z b)) / 2 := fun b => by
      have h2 : H (Z b) (((t : ℂ) • A) b) = t * H (Z b) (A b) := by
        simp only [hH, Pi.smul_apply, smul_eq_mul, map_mul, conj_ofReal, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [h2, ← hc (Z b) (A b), Complex.sub_conj, Complex.im_ofReal_mul]
      push_cast
      ring
    have h3 : ∀ b, H ((Z + (t : ℂ) • A) b) ((Z + (t : ℂ) • A) b) =
        H (Z b) (Z b) + t * H (Z b) (A b) + t * H (A b) (Z b) + t ^ 2 * H (A b) (A b) := fun b => by
      simp only [hH, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_add (f := _), conj_ofReal, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [Complex.ofReal_sum, mul_assoc, Finset.mul_sum]
    simp only [h1, h3, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [e]
  refine HasDerivAt.comp_ofReal (e := fun u : ℂ => cexp (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b) +
    (-(Real.pi * ∑ b, H (A b) (Z b)) * u + -(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b)) * u ^ 2)) * F (Z + u • A)) ?_
  rw [Complex.ofReal_zero]
  have h1 : HasDerivAt (fun u : ℂ => Z + u • A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const A).const_add Z
  have h2 : HasDerivAt (fun u : ℂ => F (Z + u • A)) (fderiv ℂ F Z A) 0 := by
    have := (hF (Z + (0 : ℂ) • A)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h1
    rwa [zero_smul, add_zero] at this
  have h3 := ((((hasDerivAt_id (0 : ℂ)).const_mul (-(Real.pi * ∑ b, H (A b) (Z b)))).fun_add
    ((hasDerivAt_pow 2 (0 : ℂ)).const_mul (-(Real.pi / 2 : ℂ) * (∑ b, H (A b) (A b))))).const_add
      (-(Real.pi / 2 : ℂ) * ∑ b, H (Z b) (Z b))).cexp.fun_mul h2
  refine h3.congr_deriv ?_
  simp only [id, zero_smul, add_zero, mul_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Nat.add_one_sub_one, pow_one]
  ring

theorem isFockVacAt_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (s τ)) f := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv f φ hf hR τ z
  obtain ⟨hd, -, hH⟩ := hx_of_isONFr _ r g V.rank X bas idx hs hev x hx0
  obtain ⟨-, hadd, hline, -⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x
  have hJ := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x s hx0 hinv).2.2 τ z
  have hF := GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hR.1 hd
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real (WeilVacMove.isTheta_add (WeilVacMove.isTheta_dRho hψ hθ τ z hf)
    (WeilVacMove.isTheta_smul I (WeilVacMove.isTheta_dRho hψ hθ τ _ hf))) fun w hw => ?_
  have hw' : w.map (finPart D) = 0 := hw
  have key : ∀ u, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ u f w =
      cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ u 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ u 1))) := fun u => by
    rw [← (hasDerivAt_translate _ _ hH _ hF _ _).deriv]
    unfold Formalism.IndefR.Datum.dRho
    congr 1
    funext t
    have h0 : (w + lineAt θ τ u t).map (finPart D) = 0 := by
      ext i j
      have h1 := congrFun (congrFun hw' i) j
      have h2 := congrFun (congrFun ((WeilVacMove.isLineAt_lineAt hθ τ u).2.1 t) i) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at h1 h2
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply, map_add, h1, h2, add_zero]
    rw [heisO, GlobalTheory.AdThSympl.psi_symplOH_eq_of_isONFr D ψ θ V W r g hr X bas idx hψ hθ hV hev hm hs x hx0 w _ hw', hR.2 _ h0, hadd, hline]
  have hI : ∀ a b : Fin g → ℂ, hx X bas idx x (I • a) b = I * hx X bas idx x a b := fun a b => by
    simp only [hH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [annih, Pi.add_apply, Pi.smul_apply, key, key, hJ, map_smul]
  simp only [Pi.smul_apply, hI, ← Finset.mul_sum, smul_eq_mul]
  linear_combination (cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx X bas idx x (zOf θ V W hr X idx x w b) (zOf θ V W hr X idx x w b)) *
        (-(Real.pi * ∑ b, hx X bas idx x (zOf θ V W hr X idx x (lineAt θ τ z 1) b) (zOf θ V W hr X idx x w b)) *
          thA X bas idx φ x (zOf θ V W hr X idx x w) +
          fderiv ℂ (thA X bas idx φ x) (zOf θ V W hr X idx x w) (zOf θ V W hr X idx x (lineAt θ τ z 1)))) * I_mul_I

end GlobalTheory.AdTh.FockVac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumCompactVacuumReadsDetCharacter
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.RealCompact

theorem realM_tauE {D : D7} (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dite_eq_left h, ← GlobalTheory.SmoothForms.RealPts.tauE_injective D h.choose_spec]

theorem mat_frMove {D : D7} (θ : InfFam D) (W : HSp D) (X : Data D.host.E W.rank) (k : GA D W)
    (x : Frame X.Ψ W.rank) (ρ : D.what₂.Tau) (τ : X.Ψ) (h : τ.1 = tauE D ρ) :
    mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
  rw [← realM_tauE, ← h]
  rfl

theorem isONFr_frMove {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (X : Data D.host.E W.rank)
    (hX : IsMod W rfl X) (k : GA D W) (x : Frame X.Ψ W.rank) (hx : IsONFr X x) :
    IsONFr X (frMove θ W rfl X k x) := by
  intro τ
  obtain ⟨ρ, hρ⟩ := (hX.psi τ.1).1 τ.2
  have hu : (compAt θ ρ (Formalism.L2.Theta.mt W k))ᴴ * gramAt D W ρ * compAt θ ρ (Formalism.L2.Theta.mt W k) = gramAt D W ρ :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W k ρ
  have hG : X.Gm.map τ.1 = -(gramAt D W ρ)ᵀ := by
    rw [hX.model.1, hρ]
    ext a b
    exact map_neg (tauE D ρ) _
  have e : ∀ y : Matrix (Fin W.rank) (Fin W.rank) ℂ, FD.gram τ.1 X.Gm y = -(yᴴ * gramAt D W ρ * y)ᵀ := by
    intro y
    have e0 : FD.gram τ.1 X.Gm y = yᵀ * (X.Gm.map τ.1 * yᴴᵀ) := by
      ext a b
      simp only [FD.gram, hermC, FD.col, of_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc,
        conjTranspose_apply, RCLike.star_def]
    rw [e0, hG, transpose_mul, transpose_mul, Matrix.neg_mul, Matrix.mul_neg]
  rw [mat_frMove θ W X k x ρ τ hρ, ← hx τ, e, e, conjTranspose_mul]
  congr 2
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_assoc]

theorem om_compact_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ k ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W k) = compAt θ τ (Formalism.L2.Theta.mt W k) * s τ) → Reads θ V W hr X bas idx (om (1, k) f) (mu k • φ) (frMove θ W hr X k x) := by
  intro D ψ θ V W χV χW om hP mu hmu r g hr X bas idx hX hS x s hx hs f φ hf hR k hk hks
  subst hr
  have hstd := hP.weil.std
  obtain ⟨cW, cV, -⟩ := GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x s
    hx hs
  have hvac := GlobalTheory.AdTh.FockVac.isFockVacAt_of_reads D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x s
    hx hs f φ hf hR
  choose a ha using hP.expV
  choose b hb using hP.expW
  obtain ⟨n, hn⟩ := hP.even
  choose p hp hd using fun τ => GlobalTheory.VacuumCharacter.detPlus_one (n := 0) (s τ) (cW τ).1
  have hom := GlobalTheory.T.vacuum_character_positive_definite_source D ψ θ V W χV χW om hP.weil hP.inf hP.sigV hP.sigW s cV cW _ _ ha hb
    (fun τ => a τ + n) (fun τ => a τ - n) (fun τ => -(p τ + b τ))
    (fun τ => by rw [hn]; push_cast; ring) (fun τ => by rw [hn]; push_cast; ring)
    (fun τ => by rw [hp]; push_cast; ring) f hf hvac 1 (one_mem _) k hk hks
  have hx' := isONFr_frMove hP.inf W X hX k x hx
  have hs' : IsInvOf W rfl X (frMove θ W rfl X k x) s := fun ρ τ h => by
    have e1 : s ρ * mat x τ = -(mat x τ * sgnM X) := hs ρ τ h
    show s ρ * _ = _
    rw [mat_frMove θ W X k x ρ τ h, ← Matrix.mul_assoc, hks, Matrix.mul_assoc, e1, Matrix.mul_neg, Matrix.mul_assoc]
  have h2 := GlobalTheory.AdTh.reads_two_frames D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x _ s hx hx' hs hs'
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt W k)) (fun ρ τ h => mat_frMove θ W X k x ρ τ h) f φ hR
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.VacuumCharacter.exists_root hP.inf W
    (fun τ => (GlobalTheory.SmoothForms.RealPts.gramAt_unit W τ).ne_zero) k hk
  have hmk : mu k = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt W k)).det ^ a τ := by rw [hmu.2 k y hy, hyv χV a ha]
  have h3 := fun c : ℂ => (GlobalTheory.AdTh.reads_linear_injective D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS
    _ hx' _ _ _ _ h2 h2).1 c 0
  simp only [zero_smul, add_zero] at h3
  rw [hom]
  convert h3 _ using 1
  rw [smul_smul, hmk, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have d2 := (hd τ 1 _ (hks τ)).2
  have h0 : (compAt θ τ (Formalism.L2.Theta.mt W k)).det ≠ 0 := by
    have := congrArg Matrix.det (GlobalTheory.UnitaryChar.compAt_mt_mul θ W τ k k⁻¹)
    rw [mul_inv_cancel, GlobalTheory.UnitaryChar.compAt_mt_one, det_one, det_mul] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  have hn2 : V.rank / 2 = n := by omega
  rw [d2] at h0
  rw [GlobalTheory.UnitaryChar.compAt_mt_one, det_one, _root_.one_zpow, mul_one, hn2]
  conv_lhs => rw [d2]
  have hA := left_ne_zero_of_mul h0
  have hB := right_ne_zero_of_mul h0
  generalize ((1 / 2 : ℂ) • (1 + s τ) * compAt θ τ (Formalism.L2.Theta.mt W k) + (1 / 2 : ℂ) • (1 - s τ)).det = A at hA ⊢
  generalize ((1 / 2 : ℂ) • (1 - s τ) * compAt θ τ (Formalism.L2.Theta.mt W k) + (1 / 2 : ℂ) • (1 + s τ)).det = B at hB ⊢
  rw [mul_zpow, zpow_add₀ hA, zpow_sub₀ hB, zpow_natCast, zpow_natCast, div_pow]
  have := pow_ne_zero n hA
  have := pow_ne_zero n hB
  field_simp

end GlobalTheory.AdTh.RealCompact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumCompactVacuumReadsDetCharacterStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_compact_vacuum_reads_det_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ k ∈ GinfC W, (∀ τ, s τ * compAt θ τ (Formalism.L2.Theta.mt W k) = compAt θ τ (Formalism.L2.Theta.mt W k) * s τ) → Reads θ V W hr X bas idx (om (1, k) f) (mu k • φ) (frMove θ W hr X k x) := by
  first | exact @GlobalTheory.AdTh.RealCompact.om_compact_reads | exact GlobalTheory.AdTh.RealCompact.om_compact_reads | (intros; apply GlobalTheory.AdTh.RealCompact.om_compact_reads <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationRealMovesFrameDetChar
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealMove

theorem muVal_mul {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : Formalism.L2.Pj.MuVal V χ mu)
    (g g' : GA D V) : mu (g * g') = mu g * mu g' := by
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  have hxx : IsDetRoot V (g * g') (x * x') := by
    unfold IsDetRoot at *
    rw [map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, map_mul]
    rw [mul_mul_mul_comm, ← hx, ← hx']
  rw [h.2 _ _ hxx, h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem frMove_mul {D : D7} (θ : InfFam D) (W : HSp D) (X : Data D.host.E W.rank) (hX : IsMod W rfl X)
    (u v : GA D W) (x : Frame X.Ψ W.rank) :
    frMove θ W rfl X (u * v) x = frMove θ W rfl X u (frMove θ W rfl X v x) := by
  funext τ
  have hτ : ∃ ρ, τ.1 = tauE D ρ := (hX.psi τ.1).1 τ.2
  have e : realM θ (Formalism.L2.Theta.mt W (u * v)) τ.1 =
      realM θ (Formalism.L2.Theta.mt W u) τ.1 * realM θ (Formalism.L2.Theta.mt W v) τ.1 := by
    unfold realM
    rw [dite_eq_left hτ, dite_eq_left hτ, dite_eq_left hτ, GlobalTheory.UnitaryChar.compAt_mt_mul]
  show (Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W (u * v)) τ.1) * mat x τ :
      Matrix (Fin W.rank) (Fin W.rank) ℂ) =
    Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W u) τ.1) *
      (Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W v) τ.1) * mat x τ)
  rw [e, ← Matrix.mul_assoc]
  simp

theorem om_real_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r), IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ u ∈ GinfC W, Reads θ V W hr X bas idx (om (1, u) f) (mu u • φ) (frMove θ W hr X u x) := by
  intro D ψ θ V W χV χW om hP mu hmu r g hr X bas idx hX hS x hx f φ hf hR
  subst hr
  have hstd := hP.weil.std
  obtain ⟨X', m, hq', hq, bas', idx', hs, -, -, -, -, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hstd hP.inf hP.even hP.std hX hS
  set C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hP.inf, X', m, g, X.p0, hq', bas', idx', hs, hP.even⟩ with hC
  obtain ⟨⟨B, hB⟩, hBx⟩ := hfr x hx
  obtain ⟨hIsB, hinv, -, -, -, -, -, hmv, hTh⟩ := hBx B hB
  have hfe : f = C.Th (C.xB B) φ := (hTh f φ hR.1).1 ⟨hf, hR⟩
  have hON : ∀ u, IsONFr X (frMove θ W rfl X u x) := fun u => (hmv u).1
  have hpres : ∀ u : GA D W, IsThetaFunO ψ V W (om (1, u) f) := fun u => hP.weil.om_pres _ _ hf
  have hc : ∀ u : GA D W, ∃ c : ℂ, u ∈ GinfC W → ‖c‖ = 1 ∧
      Reads θ V W rfl X bas idx (om (1, u) f) (c • φ) (frMove θ W rfl X u x) := by
    intro u
    by_cases hu : u ∈ GinfC W
    swap
    · exact ⟨1, fun h => absurd h hu⟩
    obtain ⟨c, hc1, hc⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D V W C om (GlobalTheory.Ker.isWeak_of_datum hP.weil) 1 (one_mem _)
      u hu B hIsB
    refine ⟨c, fun _ => ⟨hc1, ?_⟩⟩
    have h1 := hc φ hR.1
    rw [← hfe] at h1
    obtain ⟨-, -, -, -, -, -, -, -, hTh'⟩ := (hfr _ (hON u)).2 _ (hmv u).2
    have h2 := ((hTh' (C.Th (C.xB (C.mvB u B)) φ) φ hR.1).2 rfl).2
    have h3 := (GlobalTheory.T.thetaReading_linear_injective_at_orthonormal_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS _ (hON u)
      _ _ _ _ h2 h2).1 c 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at h3
    rw [h1]
    exact h3
  choose c hc using hc
  by_cases hφ : φ = 0
  · intro u hu
    have := (hc u hu).2
    rw [hφ, smul_zero] at this ⊢
    exact this
  obtain ⟨G, hG⟩ := GlobalTheory.T.inner_thetaFunctions_reading_testFunction_frames D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS
  obtain ⟨K, hK0, hK⟩ := (hG x x hx hx).2.2 φ hR.1 hφ
  obtain ⟨μ, 𝓕, hμ⟩ := (GlobalTheory.Ker.ScalarProduct.ip_basic D V W C).1
  have hmul : ∀ u ∈ GinfC W, ∀ v ∈ GinfC W, c (u * v) = c u * c v := by
    intro u hu v hv
    have h1 := hK _ _ (hON (u * v)) (hON u) _ _ _ _ (hpres _) (hpres _) (hc _ (mul_mem hu hv)).2 (hc u hu).2 μ 𝓕 hμ
    have hR1 : Reads θ V W rfl X bas idx f ((1 : ℂ) • φ) x := by rwa [one_smul]
    have h2 := hK _ _ (hON v) hx _ _ _ _ (hpres _) hf (hc v hv).2 hR1 μ 𝓕 hμ
    have h3 := GlobalTheory.WeilInner.om_inner D ψ V W χV χW om hP.weil μ 𝓕 hμ (1, u) _ _ (hpres v) hf
    have h4 : om (1, u * v) f = om (1, u) (om (1, v) f) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [h4, h3, h2, frMove_mul θ W X hX, (hG _ _ (hON v) hx).2.1 u, map_one, mul_one] at h1
    have h5 : c v = c (u * v) * conj (c u) :=
      mul_right_cancel₀ (mul_ne_zero hK0 (hG _ _ (hON v) hx).1) h1
    have h6 : c u * conj (c u) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, (hc u hu).1]; simp
    rw [h5]
    linear_combination (-c (u * v)) * h6
  have hmu0 : ∀ u, mu u ≠ 0 := fun u h => by
    have := hmu.norm u
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hcart := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x _
    hx hinv).1
  have hone := GlobalTheory.UnitaryChar.char_eq_one D θ W hP.inf _ hcart (fun u => c u / mu u)
    (fun u hu v hv => by
      show c (u * v) / mu (u * v) = c u / mu u * (c v / mu v)
      rw [hmul u hu v hv, muVal_mul hmu, mul_div_mul_comm])
    (fun k hk hks => by
      have h1 := GlobalTheory.T.weilDatum_compact_vacuum_reads_det_character D ψ θ V W χV χW om hP mu hmu W.rank g rfl X bas idx hX hS x _ hx hinv f φ hf hR k hk hks
      have h2 := (GlobalTheory.T.thetaReading_linear_injective_at_orthonormal_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS _ (hON k)
        _ _ _ _ (hc k hk).2 h1).2.1 rfl
      have h3 : c k = mu k := smul_left_injective ℂ hφ h2
      show c k / mu k = 1
      rw [h3, div_self (hmu0 k)])
  intro u hu
  have h : c u = mu u := (div_eq_one_iff_eq (hmu0 u)).1 (hone u hu)
  rw [← h]
  exact (hc u hu).2

end GlobalTheory.RealMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationRealMovesFrameDetCharStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_real_moves_frame_detChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r), IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ u ∈ GinfC W, Reads θ V W hr X bas idx (om (1, u) f) (mu u • φ) (frMove θ W hr X u x) := by
  first | exact @GlobalTheory.RealMove.om_real_reads | exact GlobalTheory.RealMove.om_real_reads | (intros; apply GlobalTheory.RealMove.om_real_reads <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicClassicalVacuumFactorEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicClassicalVacuumFactorEq
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VacFactor

section Mean

open scoped ENNReal Pointwise

theorem lintegral_translate {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] {μ : Measure V} [μ.IsAddLeftInvariant] {L : AddSubgroup V} [Countable L] {F : Set V}
    (hF : IsAddFundamentalDomain L F μ) {φ : V → ℝ≥0∞} (hp : ∀ p ∈ L, ∀ s, φ (p + s) = φ s) (s : V) :
    ∫⁻ t in F, φ (s + t) ∂μ = ∫⁻ t in F, φ t ∂μ := by
  rw [← (hF.vadd_of_comm s).setLIntegral_eq hF φ fun p x => hp p p.2 x]
  exact (measurePreserving_add_left μ s).setLIntegral_comp_emb (measurableEmbedding_addLeft s) φ F

theorem integral_prod_eq {V U : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] {μ : Measure V} [μ.IsAddLeftInvariant] [SigmaFinite μ]
    [NormedAddCommGroup U] [MeasurableSpace U] [BorelSpace U]
    [SecondCountableTopology U] {ν : Measure U} [ν.IsAddLeftInvariant] [SigmaFinite ν] {n : ℕ}
    (e : V →+ (Fin n → U)) (he : Continuous e) (hs : Function.Surjective e)
    {A : AddSubgroup U} [Countable A] {F : Set U} (hF : IsAddFundamentalDomain A F ν)
    {Γ : AddSubgroup V} [Countable Γ] {F' : Set V} (hF' : IsAddFundamentalDomain Γ F' μ)
    (hΓ : ∀ γ ∈ Γ, ∀ k, e γ k ∈ A) {φ : U → ℝ} (hc : Continuous φ) (h0 : ∀ z, 0 ≤ φ z)
    (hp : ∀ p ∈ A, ∀ z, φ (p + z) = φ z) (hm : (∫ z in F, φ z ∂ν) / (ν F).toReal = 1) :
    ∫ v in F', ∏ k, φ (e v k) ∂μ = (μ F').toReal := by
  have hv : (ν F).toReal ≠ 0 := fun h => by simp [h] at hm
  obtain ⟨hv0, hv1⟩ := ENNReal.toReal_ne_zero.1 hv
  rw [div_eq_one_iff_eq hv] at hm
  have hi : IntegrableOn φ F ν := Integrable.of_integral_ne_zero (hm ▸ hv)
  have h1 : ∫⁻ z in F, ENNReal.ofReal (φ z) ∂ν = ν F := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall h0), hm, ENNReal.ofReal_toReal hv1]
  have hφ : Continuous fun z => ENNReal.ofReal (φ z) := ENNReal.continuous_ofReal.comp hc
  let G : (Fin n → U) → ℝ≥0∞ := fun z => ∏ k, ENNReal.ofReal (φ (z k))
  have hG : Measurable G := Finset.measurable_prod _ fun k _ => hφ.measurable.comp (measurable_pi_apply k)
  have hsw := lintegral_lintegral_swap (μ := μ.restrict F') (ν := Measure.pi fun _ : Fin n => ν.restrict F)
    (f := fun s t => G (e s + t)) (hG.comp ((he.comp continuous_fst).add continuous_snd).measurable).aemeasurable
  have e1 : ∀ s, ∫⁻ t, G (e s + t) ∂(Measure.pi fun _ : Fin n => ν.restrict F) = ν F ^ n := fun s => by
    have := GlobalTheory.RestrMeas.lintegral_fin_prod_eq_prod (μ := fun _ : Fin n => ν.restrict F)
      (f := fun k t => ENNReal.ofReal (φ (e s k + t)))
      fun k => (hφ.comp (continuous_const.add continuous_id)).measurable.aemeasurable
    refine this.trans ?_
    rw [Finset.prod_congr rfl fun k _ => (lintegral_translate hF (φ := fun z => ENNReal.ofReal (φ z))
      (fun p h z => by simp only [hp p h z]) (e s k)).trans h1]
    simp
  have e2 : ∀ t, ∫⁻ s in F', G (e s + t) ∂μ = ∫⁻ s in F', G (e s) ∂μ := fun t => by
    obtain ⟨t, rfl⟩ := hs t
    simp only [add_comm _ (e t), ← map_add (f := _)]
    refine lintegral_translate hF' (φ := fun s => G (e s)) (fun p h z => ?_) t
    simp only [G, map_add (f := _), Pi.add_apply, hp _ (hΓ p h _)]
  simp only [e1, e2, lintegral_const, Measure.restrict_apply_univ, Measure.pi_univ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hsw
  rw [mul_comm] at hsw
  have e3 := (ENNReal.mul_left_inj (pow_ne_zero n hv0) (ENNReal.pow_ne_top hv1)).1 hsw
  have hcc : Continuous fun v => ∏ k, φ (e v k) :=
    continuous_finsetProd _ fun k _ => hc.comp ((continuous_apply k).comp he)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun v => Finset.prod_nonneg fun k _ => h0 _)
    hcc.aestronglyMeasurable, e3]
  simp only [G, ENNReal.ofReal_prod_of_nonneg fun k _ => h0 _]

end Mean

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}

theorem exists_meanOne {n : ℕ} (hs : IsSympl X bas) (hn : Even n) {w : E} (hw : IsIntegral ℤ w) (hw' : w + cc w = 1)
    {L : Lt E r} (hL : SelfD X L) {v : TF n g} (hv : IsVac X bas w (tens (stdL E n) L) v) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : ∃ ϑ, IsTheta1 X bas idx w x L ϑ ∧ MeanOne X bas idx x L ϑ := by
  obtain ⟨b, hb, hb'⟩ := VacNorm.exists_sympl_of_selfD hs hL
  obtain ⟨c₁, c₂, C, hC, h₁, h₂, hx'⟩ := VacForm.thA_vacuum E r X g bas idx n hs hn w hw hw' L hL v hv b hb hb'
  obtain ⟨hh, hτ, hH, he, -⟩ := hx' x hx _ _ rfl rfl
  clear hx'
  obtain ⟨a₁, rfl⟩ : ∃ a₁ : Fin g → ℝ, c₁ = fun i => (a₁ i : ℂ) :=
    ⟨fun i => (c₁ i).re, funext fun i => by rcases h₁ i with h | h <;> simp [h]⟩
  obtain ⟨a₂, rfl⟩ : ∃ a₂ : Fin g → ℝ, c₂ = fun i => (a₂ i : ℂ) :=
    ⟨fun i => (c₂ i).re, funext fun i => by rcases h₂ i with h | h <;> simp [h]⟩
  set P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i k => pv X idx x (b (Sum.inl k)) i with hP
  set Q : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i k => pv X idx x (b (Sum.inr k)) i with hQ
  have hPu : IsUnit P.det := by
    by_contra hne
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · simp at hne
    · haveI : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
      rw [nonsing_inv_apply_not_isUnit _ hne, det_zero] at hh
      exact not_isUnit_zero hh
  generalize hh' : P⁻¹ = h at *
  generalize hτ' : h * Q = τ at *
  have hhP : h * P = 1 := by rw [← hh', nonsing_inv_mul _ hPu]
  have hpv : ∀ m : Fin g ⊕ Fin g → ℤ, h *ᵥ pv X idx x (∑ j, m j • b j) =
      (fun i => (m (Sum.inl i) : ℂ)) + τ *ᵥ (fun i => (m (Sum.inr i) : ℂ)) := by
    intro m
    have : pv X idx x (∑ j, m j • b j) =
        P *ᵥ (fun i => (m (Sum.inl i) : ℂ)) + Q *ᵥ (fun i => (m (Sum.inr i) : ℂ)) := by
      funext i
      rw [pv, per_sum]
      simp only [per_zsmul, Fintype.sum_sum_type, hP, hQ, pv]
      simp [mulVec, dotProduct, mul_comm]
    rw [this, mulVec_add, mulVec_mulVec, mulVec_mulVec, hhP, hτ', one_mulVec]
  have h0 : IsTheta1 X bas idx w x L fun z => CanTh.canTh τ a₁ a₂ (h *ᵥ z) := by
    refine ⟨(CanTh.differentiable_canTh hτ.2 a₁ a₂).comp (differentiable_pi.2 fun i => ?_), fun u hu => ?_⟩
    · simp only [dotProduct, mulVec]
      fun_prop
    · obtain ⟨m, rfl⟩ := (hb u).1 hu
      funext z
      have e := VacProd.thetaSign_mul_canonicalTheta_multiplier hL hw hw' (fun m => (hb _).2 ⟨m, rfl⟩) hb' h₁ he m
      simp only [Pi.smul_apply, smul_eq_mul, fock, hH]
      rw [mulVec_add h z (pv X idx x _), CanTh.canTh_add_period hτ.1 hτ.2 a₁ a₂ _ _ (hpv m)]
      generalize pv X idx x (∑ j, m j • b j) = p
      have e2 : cexp (-(((1 : ℕ) : ℂ) * Real.pi * ((h *ᵥ (z + (1 / 2 : ℂ) • p)) ⬝ᵥ
          ((τ.map Complex.im)⁻¹.map fun t : ℝ => (t : ℂ)) *ᵥ star (h *ᵥ p)))) *
          cexp (Real.pi * Geo.Tor.hermForm (CanTh.imInv τ) (h *ᵥ z) (h *ᵥ p) +
            Real.pi / 2 * Geo.Tor.hermForm (CanTh.imInv τ) (h *ᵥ p) (h *ᵥ p)) = 1 := by
        rw [← Complex.exp_add, Complex.exp_eq_one_iff]
        refine ⟨0, ?_⟩
        simp only [Geo.Tor.hermForm, CanTh.imInv, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
        push_cast
        ring
      linear_combination (CanTh.canTh τ a₁ a₂ (h *ᵥ z)) * e + (CanTh.canTh τ a₁ a₂ (h *ᵥ z)) *
        (eps1 X w (∑ j, m j • b j) * CanTh.canMult a₁ a₂ (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i))) * e2
  let p : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) fun u v => by
    unfold pv; rw [per_add]; rfl
  let A : AddSubgroup (Fin g → ℂ) := L.toAddSubgroup.map p
  have hA : ∀ z, z ∈ A ↔ ∃ v ∈ L, z = pv X idx x v := fun z =>
    ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩⟩
  have hA' : ∀ lam, lam ∈ A ↔ ∃ m n : Fin g → ℤ,
      h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) := by
    intro lam
    rw [hA]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨m, rfl⟩ := (hb u).1 hu
      exact ⟨_, _, hpv m⟩
    · rintro ⟨m, m', e⟩
      refine ⟨_, (hb _).2 ⟨Sum.elim m m', rfl⟩, ?_⟩
      have e' : h *ᵥ lam = h *ᵥ pv X idx x (∑ j, Sum.elim m m' j • b j) := e.trans (hpv (Sum.elim m m')).symm
      have := congrArg (h⁻¹ *ᵥ ·) e'
      simpa only [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec] using this
  obtain ⟨Fd, hFd, hm⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar
    g τ h _ _ A hτ.1 hτ.2 hh h₁ h₂ hA'
  have hpos : 0 < Real.sqrt (2 ^ g * (τ.map Complex.im).det) :=
    Real.sqrt_pos.2 (mul_pos (by positivity) hτ.2.det_pos)
  generalize Real.sqrt (2 ^ g * (τ.map Complex.im).det) = t at hm hpos
  refine ⟨fun z => (Real.sqrt t : ℂ) * CanTh.canTh τ a₁ a₂ (h *ᵥ z), ⟨h0.1.const_mul _, fun u hu => ?_⟩,
    A, Fd, hA, hFd, ?_⟩
  · funext z
    have := congrFun (h0.2 u hu) z
    simp only [Pi.smul_apply, smul_eq_mul, fock] at this ⊢
    linear_combination (Real.sqrt t : ℂ) * this
  · rw [← mul_inv_cancel₀ hpos.ne', ← hm, ← mul_div_assoc, ← integral_const_mul]
    congr 2
    funext z
    unfold CanTh.canTh
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hpos.le, _root_.mul_assoc,
      mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
    congr 3
    have : ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hH, this, re_ofReal_mul, VacNorm.re_dot_star]
    unfold CanTh.imInv
    rw [VacNorm.re_dot]
    push_cast; ring

theorem norm_sq_periodic {w : E} {L : Lt E r} {x : Frame X.Ψ r} {c : Fin g → ℝ}
    (hH : ∀ z z' : Fin g → ℂ, hx X bas idx x z z' = ∑ j, (c j : ℂ) * z j * conj (z' j))
    {ϑ : (Fin g → ℂ) → ℂ} (hϑ : IsTheta1 X bas idx w x L ϑ) {u : Fin r → E} (hu : u ∈ L) (z : Fin g → ℂ) :
    ‖ϑ (pv X idx x u + z)‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x (pv X idx x u + z) (pv X idx x u + z)).re) =
      ‖ϑ z‖ ^ 2 * Real.exp (-Real.pi * (hx X bas idx x z z).re) := by
  have hp := congrFun (hϑ.2 u hu) z
  have hε : ‖eps1 X w u‖ = 1 := by
    rw [eps1, Complex.norm_exp]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, fock] at hp
  generalize pv X idx x u = p at hp ⊢
  rw [← hp, add_comm p z, norm_mul, norm_mul, hε, _root_.one_mul, mul_pow, Complex.norm_exp,
      ← Real.exp_nat_mul, mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add]
  congr 2
  simp only [Nat.cast_one, _root_.one_mul, neg_re, re_ofReal_mul, hH, re_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

end GlobalTheory.AdTh.VacFactor


open GlobalTheory.AdTh.VacFactor in
theorem GlobalTheory.AdTh.norm_factor_eq_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → X.Λ = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) X.Λ) v → ∀ κ : ℂ, Reads θ V W hr X bas idx f (κ • v) x → (∀ x' ∈ X.dom, IsUnitFr X x' → ∀ (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ), IsTheta1 X bas idx (H.w0 : D.host.E) x' X.Λ ϑ → MeanOne X bas idx x' X.Λ ϑ → (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X bas idx v x' z) → ‖κ'‖ = ‖κ‖) := by
  intro D ψ θ V W r g hr X bas idx hstd hinf hV he hm hs H _ ΛV ΛW _ _ _ _ x s hx f hf v hv κ hR
  subst hr
  have hw := GlobalTheory.Dict.VSetup.hostHalfRoot_add_conj_eq_one H
  have hi : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  have hL : SelfD X X.Λ := GlobalTheory.SW.Lev.selfD_of_sympl hs
  obtain ⟨hd, hu, hH⟩ := GlobalTheory.AdTh.hx_of_isONFr _ _ g _ X bas idx hs he x hx
  obtain ⟨ρ, hρ, hn⟩ := VacNorm.norm_factor_eq _ _ X g bas idx _ hs he _ hi hw _ hL v hv
  obtain ⟨ϑ, hϑ, hmean⟩ := exists_meanOne (idx := idx) hs he hi hw hL hv hd
  obtain ⟨κ₀, hκ₀⟩ := VacProd.prod_eq_mul_thA _ _ X g bas idx _ hs he _ hi hw _ hL v hv x hd ϑ hϑ
  have h₀ := hn x hd hu ϑ κ₀ hϑ hmean hκ₀
  suffices h : ρ = ‖κ‖ from fun x' hx' hu' ϑ' κ' h1 h2 h3 => (hn x' hx' hu' ϑ' κ' h1 h2 h3).trans h
  obtain ⟨X', m, hq', hq, bas', idx', hs', hΛ, -, -, -, -, -, hB⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hstd hinf he hV hm hs
  obtain ⟨⟨B, hB1⟩, hB2⟩ := hB x hx
  let C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hinf, X', m, g, X.p0, hq', bas', idx', hs', he⟩
  obtain ⟨hCB, -, -, hz, hpv, -⟩ := hB2 B hB1
  have hd' : C.xB B ∈ X'.dom := GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hCB)
  obtain ⟨⟨e, hE⟩, -⟩ := GlobalTheory.Ker.zR_laws _ _ X' g X.p0 hq' bas' idx' V.rank hs' he _ hd'
  obtain ⟨⟨⟨μ, 𝓕⟩, hμ⟩, hone⟩ := hf.2.norm
  have hone := hone _ hμ
  obtain ⟨N, hN, hip⟩ := GlobalTheory.Ker.TorusMean.ipO_eq_mean D V W C μ 𝓕 hμ f f hf.2.theta hf.2.theta
  obtain ⟨⟨F', hF'⟩, hip⟩ := hip N hN dvd_rfl
  obtain ⟨A, F, hA, hF, hmean⟩ := hmean
  let φ : (Fin g → ℂ) → ℝ := fun z => ‖ϑ z‖ ^ 2 * Real.exp (-Real.pi * (Dict.hx X bas idx x z z).re)
  have hc : Continuous φ := by
    have := hϑ.1.continuous
    simp only [φ, hH]
    fun_prop
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable A := by
    refine ((Set.countable_range (pv X idx x)).mono fun z hz => ?_).to_subtype
    obtain ⟨u, -, rfl⟩ := (hA z).1 hz
    exact ⟨u, rfl⟩
  haveI := GlobalTheory.Ker.TorusMean.haar_WR X' (n := V.rank)
  have key := integral_prod_eq (μ := volume) (ν := volume) (e : GlobalTheory.Ker.WR X' V.rank →+ (Fin V.rank → Fin g → ℂ))
    e.continuous e.surjective hF hF' (fun γ hγ k => ?_) hc (fun z => by positivity) (fun p hp z => ?_) hmean
  · have h1 := hip F' hF' (fun v => ((‖κ‖ ^ 2 / ρ ^ 2 * ∏ k, φ (e v k) : ℝ) : ℂ)) fun w hw => ?_
    · have h2 : GlobalTheory.Ker.ipO μ 𝓕 f f = 1 := by
        simp only [GlobalTheory.Ker.ipO, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [integral_complex_ofReal]
        exact congrArg Complex.ofReal hone
      change ∫ v in F', ∏ k, φ (e v k) = _ at key
      rw [h2, integral_complex_ofReal, integral_const_mul, key] at h1
      have h3 : (1 : ℝ) = (volume F').toReal⁻¹ * (‖κ‖ ^ 2 / ρ ^ 2 * (volume F').toReal) := by exact_mod_cast h1
      have h4 : (volume F').toReal ≠ 0 := fun h => by simp [h] at h3
      rw [mul_left_comm, inv_mul_cancel₀ h4, mul_one, eq_comm, div_eq_one_iff_eq (by positivity)] at h3
      exact ((sq_eq_sq₀ (norm_nonneg _) hρ.le).1 h3).symm
    · have h2 : e (C.realPt w) = zOf θ V W rfl X idx x w := (hE _).trans (hz w)
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hR.2 w hw]
      simp only [h2]
      generalize zOf θ V W rfl X idx x w = z
      congr 1
      simp only [φ, Finset.prod_mul_distrib, Finset.prod_pow, ← norm_prod, hκ₀, ← Real.exp_sum]
      rw [UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, norm_mul, h₀, Complex.norm_exp, mul_pow,
        ← Real.exp_nat_mul, show (-(Real.pi / 2 : ℂ)) = ((-(Real.pi / 2) : ℝ) : ℂ) by push_cast; ring,
        re_ofReal_mul, re_sum, ← Finset.mul_sum,
        show ∀ t : ℝ, ((2 : ℕ) : ℝ) * (-(Real.pi / 2) * t) = -Real.pi * t from fun t => by push_cast; ring]
      field_simp
  · obtain ⟨y, hy, rfl⟩ := (GlobalTheory.Ker.TorusMean.mem_latR_iff X' N γ).1 hγ
    rw [map_nsmul]
    refine nsmul_mem ((hA _).2 ⟨y k, hΛ ▸ hy k, ?_⟩) N
    exact (congrFun (hE _) k).trans (hpv (y k))
  · obtain ⟨u, hu, rfl⟩ := (hA p).1 hp
    exact norm_sq_periodic hH hϑ hu z
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicClassicalVacuumFactorEqStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_adelicClassicalVacuumFactor_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → X.Λ = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) X.Λ) v → ∀ κ : ℂ, Reads θ V W hr X bas idx f (κ • v) x → (∀ x' ∈ X.dom, IsUnitFr X x' → ∀ (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ), IsTheta1 X bas idx (H.w0 : D.host.E) x' X.Λ ϑ → MeanOne X bas idx x' X.Λ ϑ → (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X bas idx v x' z) → ‖κ'‖ = ‖κ‖) := by
  first | exact @GlobalTheory.AdTh.norm_factor_eq_of_reads | exact GlobalTheory.AdTh.norm_factor_eq_of_reads | (intros; apply GlobalTheory.AdTh.norm_factor_eq_of_reads <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVacuumMultiplierConstantPerLattice
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacFamily

theorem muVal_mul {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : Formalism.L2.Pj.MuVal V χ mu)
    (g g' : GA D V) : mu (g * g') = mu g * mu g' := by
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  have hxx : IsDetRoot V (g * g') (x * x') := by
    unfold IsDetRoot at *
    rw [map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, map_mul]
    rw [mul_mul_mul_comm, ← hx, ← hx']
  rw [h.2 _ _ hxx, h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem compAt_fin {D : D7} (θ : InfFam D) (V : HSp D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  have h1 : infHom V k = 1 := hk
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V k) = ((infHom V k).val).map (θ τ) := rfl
  rw [h2, h1, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem frMove_mul_fin {D : D7} (θ : InfFam D) (W : HSp D) (X : Data D.host.E W.rank)
    (u : GA D W) {k : GA D W} (hk : k ∈ GfC W) (x : Frame X.Ψ W.rank) :
    frMove θ W rfl X (u * k) x = frMove θ W rfl X u x := by
  funext τ
  have e : realM θ (Formalism.L2.Theta.mt W (u * k)) τ.1 = realM θ (Formalism.L2.Theta.mt W u) τ.1 := by
    unfold realM
    split_ifs with h
    · rw [GlobalTheory.UnitaryChar.compAt_mt_mul, compAt_fin θ W hk, Matrix.mul_one]
    · rfl
  unfold frMove
  rw [e]

theorem isONFr_frMove {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (X : Data D.host.E W.rank)
    (hX : IsMod W rfl X) (u : GA D W) {x : Frame X.Ψ W.rank} (hx : IsONFr X x) :
    IsONFr X (frMove θ W rfl X u x) := by
  intro τ
  have hτ : ∃ ρ, τ.1 = tauE D ρ := (hX.psi τ.1).1 τ.2
  have hG : X.Gm = -(W.gram)ᵀ := by rw [hX.model.1]; simp
  have e : mat (frMove θ W rfl X u x) τ = compAt θ hτ.choose (Formalism.L2.Theta.mt W u) * mat x τ := by
    show (Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W u) τ.1) * mat x τ :
      Matrix (Fin W.rank) (Fin W.rank) ℂ) = _
    unfold realM
    rw [dite_eq_left hτ]
    simp
  have hu : (compAt θ hτ.choose (Formalism.L2.Theta.mt W u))ᴴ * gramAt D W hτ.choose *
      compAt θ hτ.choose (Formalism.L2.Theta.mt W u) = gramAt D W hτ.choose :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W u _
  have hg : gramAt D W hτ.choose = W.gram.map τ.1 := by
    conv_rhs => rw [hτ.choose_spec]
    rfl
  rw [hg] at hu
  rw [← hx τ, e, hG, GlobalTheory.FrameCplx.gram_eq, GlobalTheory.FrameCplx.gram_eq, Matrix.conjTranspose_mul]
  congr 2
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_assoc]

abbrev twist {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}

theorem latO_le {D : D7} (V W : HSp D) (LV : Set (Fin V.rank → D.host.E))
    {L L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} (h : twist L ≤ twist L') :
    latO V W LV (L : Set (Fin W.rank → D.host.E)) (fun _ => True) ≤
      latO V W LV (L' : Set (Fin W.rank → D.host.E)) fun _ => True := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  have key : ∀ w ∈ twist L', ∀ b : 𝓞 D.host.E,
      (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((b • w) i * ∑ k, star (s k) * V.gram k j) : WO V W) ∈
        latO V W LV (L' : Set (Fin W.rank → D.host.E)) fun _ => True := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a', ha', t', ht', rfl⟩ := hw
      intro b
      refine AddSubgroup.subset_closure ⟨α, hα, hP, b • a', (D.host.AA.coeToSubmodule).smul_mem b ha',
        s, hs, t', ht', ?_⟩
      ext i j
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, smul_mul_assoc]
    | zero =>
      intro b
      convert (latO V W LV (L' : Set (Fin W.rank → D.host.E)) fun _ => True).zero_mem
      ext i j
      simp
    | add w w' _ _ h1 h2 =>
      intro b
      convert add_mem (h1 b) (h2 b)
      ext i j
      simp only [Matrix.of_apply, smul_add, Pi.add_apply, add_mul, TensorProduct.tmul_add, Matrix.add_apply]
    | smul c w _ h1 =>
      intro b
      rw [smul_smul]
      exact h1 _
  have := key (a • t) (h (Submodule.subset_span ⟨a, ha, t, ht, rfl⟩)) 1
  rw [one_smul] at this
  exact this

theorem actO_mul {D : D7} (V W : HSp D) (h h' : GA D W) (u : WO V W) :
    actO V W 1 (h * h') u = actO V W 1 h (actO V W 1 h' u) := by
  have e1 : Formalism.L2.Theta.mt V 1⁻¹ = 1 := by rw [inv_one]; rfl
  have e2 : Formalism.L2.Theta.mt W (h * h') = Formalism.L2.Theta.mt W h * Formalism.L2.Theta.mt W h' := rfl
  unfold actO
  rw [e1, e2]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem actO_one {D : D7} (V W : HSp D) (u : WO V W) : actO V W 1 1 u = u := by
  have e1 : Formalism.L2.Theta.mt V 1⁻¹ = 1 := by rw [inv_one]; rfl
  have e2 : Formalism.L2.Theta.mt W 1 = 1 := rfl
  unfold actO
  rw [e1, e2]
  simp only [Matrix.mul_one, Matrix.one_mul]

theorem latR_rfl {E : Type} [Field E] [NumberField E] {m : ℕ} (L : Submodule (𝓞 E) (Fin m → E)) : latR rfl L = L := by
  have : LinearMap.funLeft (𝓞 E) E (Fin.cast (rfl : m = m).symm) = LinearMap.id := rfl
  unfold latR
  rw [this, Submodule.map_id]

theorem latG_mul {D : D7} (W : HSp D) {u : GA D W} (hu : u ∈ GinfC W) (k : GA D W) :
    Formalism.L2.Pj.latG W (u * k) = Formalism.L2.Pj.latG W k := by
  have h : finHom W u = 1 := hu
  unfold Formalism.L2.Pj.latG Formalism.L2.Pj.gLat
  rw [map_mul, h, one_mul]

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h2 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have hc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hs, map_neg, map_natCast]
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at hre him
    have h0 : (τ (H.rt : E)).re = 0 := by
      by_contra h
      have h5 : (τ (H.rt : E)).im = 0 := mul_left_cancel₀ h (by linarith)
      rw [h5] at hre
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    rw [cc, IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [h0]
  have h3 : (2 : E) * cc (H.w0 : E) = 1 - (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    rw [sub_eq_add_neg, ← hc]
    exact this
  linear_combination (h2 + h3) / 2

theorem mem_stdL {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Fin n → E) :
    w ∈ stdL E n ↔ ∀ j, ∃ b : 𝓞 E, (b : E) = w j := by
  rw [stdL, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ j
    refine ⟨c j, ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    choose c hc using h
    refine ⟨c, funext fun j => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ← hc]

theorem exists_vacuum_multiplier : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), V.rank ≠ 0 → (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → SelfD X X.Λ → ∀ (x₀ : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x₀ → IsInvOf W hr X x₀ s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) X.Λ) v → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x' ∈ X.dom, IsUnitFr X x' → ∀ (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ), IsTheta1 X bas idx (H.w0 : D.host.E) x' X.Λ ϑ → MeanOne X bas idx x' X.Λ ϑ → (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X bas idx v x' z) → ‖κ'‖ = ‖κ‖) ∧ ∀ k : GA D W, latR hr (Formalism.L2.Pj.latG W k) = X.Λ → IsONFr X (frMove θ W hr X k x₀) ∧ Reads θ V W hr X bas idx (om (1, k) f) ((κ * mu k) • v) (frMove θ W hr X k x₀) := by
  intro D ψ θ V W χV χW om hP mu hmu r g hr X bas idx hX hS H hH ΛV ΛW hV0 hΛV hΛW hsV hsW hstdV hsd x₀ s hx hinv f hf v hv
  subst hr
  have hstd := hP.weil.std
  by_cases hex : ∃ k : GA D W, latR rfl (Formalism.L2.Pj.latG W k) = X.Λ
  swap
  · obtain ⟨ρ, hρ, h⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq D.host.E W.rank X g bas idx V.rank hS hP.even _
      H.w0.isIntegral_coe (hostHalfRoot_add_conj_eq_one H) X.Λ hsd v hv
    refine ⟨ρ, by exact_mod_cast hρ.ne', fun x' hx' hu ϑ κ' h1 h2 h3 => ?_, fun k hk => absurd ⟨k, hk⟩ hex⟩
    rw [h x' hx' hu ϑ κ' h1 h2 h3, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  have hsplit := (GlobalTheory.UnitarySplit.real_finite_split D W).1
  have hfin1 : Formalism.IndefR.FWT.fin V 1 = 1 := map_one _
  have hmv := fun k => GlobalTheory.MovedLat.moved_lattices D V W ΛV ΛW hΛV hΛW hsV hsW 1 k
  have hV1 : Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V 1) = ΛV := by rw [hfin1]; exact (hmv 1).2.2.2.2.1
  simp only [hV1] at hmv
  obtain ⟨k₁, hk₁⟩ := hex
  obtain ⟨u₁, hu₁, k₀, hk₀, rfl⟩ := hsplit k₁
  rw [latR_rfl, latG_mul W hu₁] at hk₁
  obtain ⟨-, hs₀, hl₀, ht₀, -, -⟩ := hmv k₀
  set L₀ := Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W k₀) with hL₀
  have hf₀ : IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (L₀ : Set (Fin W.rank → D.host.E))
      (om (1, k₀) f) :=
    GlobalTheory.WeilVacMove.isVacO_om D ψ θ V W χV χW om hP.weil hP.inf _ _ s s _ _ _ _ 1 k₀
      (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [compAt_fin θ W hk₀, Matrix.one_mul, Matrix.mul_one]) hl₀ f hf
  have hL : ∀ L : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L = twist L₀ → X.Λ = latR rfl L := fun L h => by
    rw [latR_rfl, h, ← hk₁, ht₀]
  have hconj : ∀ w : Fin V.rank → D.host.E, w ∈ stdL D.host.E V.rank ↔ (fun j => star (w j)) ∈ ΛV := by
    intro w
    have hb : ∀ b : 𝓞 D.host.E, ((H.bar b : 𝓞 D.host.E) : D.host.E) = star (b : D.host.E) := fun b => H.bar_eq b
    rw [mem_stdL, ← SetLike.mem_coe, hstdV, SetLike.mem_coe, Formalism.L2.Pj.stdLat, Submodule.mem_pi]
    refine forall_congr' fun j => ⟨?_, fun h => ?_⟩
    · rintro ⟨b, e⟩ -
      exact Submodule.mem_one.2 ⟨H.bar b, by rw [← e]; exact hb b⟩
    · obtain ⟨b, e⟩ := Submodule.mem_one.1 (h (Set.mem_univ _))
      refine ⟨H.bar b, ?_⟩
      rw [hb, show (b : D.host.E) = star (w j) from e, star_star]
  obtain ⟨κ₀, hκ₀, hR₀⟩ := GlobalTheory.T.adelicVacuum_reads_multiple_classicalVacuum D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS H hH ΛV L₀
    _ X.Λ hP.sigV hP.sigW hsV hs₀ hconj hL x₀ s hx hinv _ hf₀ v hv
  have hN := GlobalTheory.T.norm_adelicClassicalVacuumFactor_eq D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS H hH ΛV L₀
    hsV hs₀ hstdV hL x₀ s hx _ hf₀ v hv κ₀ hR₀
  have hmu0 : mu k₀ ≠ 0 := fun h => by
    have := hmu.norm k₀
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hcart := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x₀ s
    hx hinv).1
  refine ⟨κ₀ / mu k₀, div_ne_zero hκ₀ hmu0, fun x' hx' hu ϑ κ' h1 h2 h3 => ?_, fun k hk => ?_⟩
  · rw [hN x' hx' hu ϑ κ' h1 h2 h3, norm_div, hmu.norm, div_one]
  refine ⟨isONFr_frMove hP.inf W X hX k hx, ?_⟩
  obtain ⟨u, hu, c, hc, rfl⟩ := hsplit k
  rw [latR_rfl, latG_mul W hu] at hk
  obtain ⟨-, -, hl, ht, -, -⟩ := hmv c
  have htw : twist (Formalism.IndefR.Bridge.hLat W (Formalism.IndefR.FWT.fin W c)) = twist L₀ :=
    ht.symm.trans (hk.trans (hk₁.symm.trans ht₀))
  have hlat := le_antisymm (latO_le V W ΛV htw.le) (latO_le V W ΛV htw.ge)
  rw [hlat] at hl
  have hk' : c * k₀⁻¹ ∈ GfC W := mul_mem hc (inv_mem hk₀)
  have hfix := GlobalTheory.T.weilRep_lattice_stabilizer_vacuum_eq_det_char_smul D ψ θ V W χV χW om hP mu hmu H ΛV L₀ hV0 hsV hs₀ s hcart _ hf₀ _ hk' (fun w => by
    rw [hl₀ w, hl]
    constructor
    · rintro ⟨w₀, hw₀, rfl⟩
      exact ⟨w₀, hw₀, by rw [← actO_mul, inv_mul_cancel_right]⟩
    · rintro ⟨w₀, hw₀, e⟩
      refine ⟨w₀, hw₀, ?_⟩
      have := congrArg (actO V W 1 (k₀ * c⁻¹)) e
      rw [← actO_mul, ← actO_mul, inv_mul_cancel_right] at this
      rw [← this, show k₀ * c⁻¹ * (c * k₀⁻¹) = 1 by group, actO_one])
  have hth : IsThetaFunO ψ V W (om (1, c * k₀⁻¹) (om (1, k₀) f)) := hP.weil.om_pres _ _ hf₀.2.theta
  have hR := (GlobalTheory.AdTh.reads_linear_injective D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x₀ hx
    _ _ _ _ hR₀ hR₀).1 (mu (c * k₀⁻¹)) 0
  rw [zero_smul, zero_smul, add_zero, add_zero, ← hfix] at hR
  have hR' := GlobalTheory.T.weilRepresentation_real_moves_frame_detChar D ψ θ V W χV χW om hP mu hmu W.rank g rfl X bas idx hX hS x₀ hx _ _ hth hR u hu
  have e1 : om (1, u) (om (1, c * k₀⁻¹) (om (1, k₀) f)) = om (1, u * c) f := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk]
    simp only [mul_one, mul_assoc, inv_mul_cancel]
  have e2 : κ₀ / mu k₀ * mu (u * c) = mu u * (mu (c * k₀⁻¹) * κ₀) := by
    have : mu c = mu (c * k₀⁻¹) * mu k₀ := by rw [← muVal_mul hmu, inv_mul_cancel_right]
    rw [muVal_mul hmu, this]
    field_simp
  rw [e1, smul_smul, smul_smul, mul_assoc, ← e2] at hR'
  rw [frMove_mul_fin θ W X u hc]
  exact hR'

end GlobalTheory.VacFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVacuumMultiplierConstantPerLatticeStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vacuum_multiplier_constant_per_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), V.rank ≠ 0 → (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V → (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → SelfD X X.Λ → ∀ (x₀ : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x₀ → IsInvOf W hr X x₀ s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens (stdL D.host.E V.rank) X.Λ) v → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x' ∈ X.dom, IsUnitFr X x' → ∀ (ϑ : (Fin g → ℂ) → ℂ) (κ' : ℂ), IsTheta1 X bas idx (H.w0 : D.host.E) x' X.Λ ϑ → MeanOne X bas idx x' X.Λ ϑ → (∀ z : Fin V.rank → Fin g → ℂ, ∏ b, ϑ (z b) = κ' * thA X bas idx v x' z) → ‖κ'‖ = ‖κ‖) ∧ ∀ k : GA D W, latR hr (Formalism.L2.Pj.latG W k) = X.Λ → IsONFr X (frMove θ W hr X k x₀) ∧ Reads θ V W hr X bas idx (om (1, k) f) ((κ * mu k) • v) (frMove θ W hr X k x₀) := by
  first | exact @GlobalTheory.VacFamily.exists_vacuum_multiplier | exact GlobalTheory.VacFamily.exists_vacuum_multiplier | (intros; apply GlobalTheory.VacFamily.exists_vacuum_multiplier <;> assumption)
end
