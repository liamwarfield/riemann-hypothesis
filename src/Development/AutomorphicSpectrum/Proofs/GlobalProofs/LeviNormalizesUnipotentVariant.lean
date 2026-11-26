module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem mem_frameStab_initCols {C : Matrix (Fin n) (Fin r) E} {k : Fin r} {g : GAd σ J}
    (h : ∀ i : Fin r, i ≤ k → (matHom _ σ J g).1 *ᵥ (adMat F C)ᵀ i = (adMat F C)ᵀ i) :
    g ∈ frameStab σ J (initCols C k) ⊤ := by
  simp only [GlobalTheory.StdPar.frameStab, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq, Subgroup.mem_top, true_and]
  refine ⟨1, ?_⟩
  rw [Units.val_one, Matrix.mul_one]
  ext i j
  have hjk : Fin.castLE (Nat.succ_le_of_lt k.isLt) j ≤ k := by
    rw [Fin.le_iff_val_le_val, Fin.val_castLE]
    exact Nat.lt_succ_iff.mp j.isLt
  exact congrFun (h _ hjk) i

theorem uPart_le_levi_general (X Y : Matrix (Fin n) (Fin r) E) (T : Finset (Fin r)) :
    uPart σ J X Y T ≤ levi σ J X Y T := by
  intro g hg
  have hfix : ∀ y ∈ GlobalTheory.StdPar.colSpan F X (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T) ⊔
      GlobalTheory.StdPar.colSpan F Y (GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T),
      (↑(GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g) : Matrix (Fin n) (Fin n) _) *ᵥ y = y := hg
  simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf, Subgroup.mem_inf]
  intro k hk
  constructor
  · apply mem_frameStab_initCols
    intro i hi
    exact hfix _ (Submodule.mem_sup_left (Submodule.subset_span ⟨i, ⟨k, hk, hi⟩, rfl⟩))
  · apply mem_frameStab_initCols
    intro i hi
    exact hfix _ (Submodule.mem_sup_right (Submodule.subset_span ⟨i, ⟨k, hk, hi⟩, rfl⟩))

end General

theorem uPart_le_levi : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)),
    uPart D.sp.cm.sig V.gram X Y T ≤ levi D.sp.cm.sig V.gram X Y T := by
  intro D V m X Y T
  exact uPart_le_levi_general X Y T

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_part_le_levi : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)), uPart D.sp.cm.sig V.gram X Y T ≤ levi D.sp.cm.sig V.gram X Y T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLevi
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLevi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

theorem isFrameFam_mul_infMat_inv : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsFrameFam V ε fr → ∀ b : GA D V,
        IsFrameFam V ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) := by
  intro D θ hθ V ε fr h b τ
  have h1 : infMat D.sp.cm.sig V.gram (θ τ) b * infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ = 1 := by
    rw [← Formalism.L2.Fam.ThC.infMat_mul, mul_inv_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have h2 : infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) b = 1 := by
    rw [← Formalism.L2.Fam.ThC.infMat_mul, inv_mul_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have hu : IsUnit (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹) := IsUnit.of_mul_eq_one _ h2
  have hinv : (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ = infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ :=
    Matrix.inv_eq_right_inv h1
  refine ⟨?_, ?_⟩
  · show IsUnit (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)
    rw [hinv]
    exact (h τ).1.mul hu
  · show (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)ᴴ * Formalism.REAL.Jm (ε τ) *
        (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) = _
    rw [hinv, Matrix.conjTranspose_mul]
    have e := GlobalTheory.Doubling.infMat_isometry (V := V) hθ τ b⁻¹
    rw [← (h τ).2] at e ⊢
    simpa only [Matrix.mul_assoc] using e

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLeviStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_family_right_translate : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ b : GA D V, IsFrameFam V ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.isFrameFam_mul_infMat_inv | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.isFrameFam_mul_infMat_inv | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.isFrameFam_mul_infMat_inv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FrameFamilyRightTranslate
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FrameFamilyRightTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl

theorem foldr_lineDer_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GAd σ J) (l : List (ℝ → GAd σ J))
    (f : GAd σ J → ℂ) :
    l.foldr lineDer (fun x => f (x * b)) =
      fun x => (l.map fun γ t => b⁻¹ * γ t * b).foldr lineDer f (x * b) := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    rw [List.foldr_cons, ih, List.map_cons, List.foldr_cons]
    funext x
    simp only [lineDer]
    congr 1
    funext t
    congr 1
    simp only [mul_assoc, mul_inv_cancel_left]

variable {D : D7}

theorem isSmModOn_mul_right (V : HSp D) {Γ : Set (GA D V)} {φ : GA D V → ℂ}
    (h : IsSmModOn D.sp.cm.sig V.gram Γ φ) (b : GA D V) :
    IsSmModOn D.sp.cm.sig V.gram Γ (fun x => φ (x * b)) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hN : (GfC V).Normal := MonoidHom.normal_ker _
  refine ⟨fun γ hγ x => ?_, ?_, h.cont.comp (continuous_id.mul continuous_const), ?_, ?_⟩
  · show φ (γ * x * b) = φ (x * b)
    rw [mul_assoc]
    exact h.left γ hγ _
  · obtain ⟨A, hA, eA⟩ := h.level
    refine ⟨A.comap (MulAut.conj b⁻¹).toMonoidHom, ?_, fun k hk hk' x => ?_⟩
    · have hc : Continuous fun y : GA D V => b⁻¹ * y * b⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hA.preimage hc
    · have hk2 : b⁻¹ * k * b⁻¹⁻¹ ∈ A := hk
      have hk3 : b⁻¹ * k * b⁻¹⁻¹ ∈ GfC V := hN.conj_mem k hk' b⁻¹
      rw [inv_inv] at hk2 hk3
      show φ (x * k * b) = φ (x * b)
      rw [← eA _ hk2 hk3 (x * b)]
      congr 1
      simp only [mul_assoc, mul_inv_cancel_left]
  · exact GlobalTheory.UAut.isSm_mul_right_of_isCMExt _ _ (GlobalTheory.AdelicU.isCMExt_host D) φ b h.smooth
  · obtain ⟨N, hN'⟩ := h.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN' (l.map fun γ t => b⁻¹ * γ t * b) (by
      intro γ' hγ'
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hγ'
      exact GlobalTheory.UAut.RightTranslate.isRealLine_conj (GlobalTheory.AdelicU.isCMExt_host D) (hl γ hγ) b)
    refine ⟨max C 0 * (height D.sp.cm.sig V.gram b : ℝ) ^ N, fun x => ?_⟩
    rw [foldr_lineDer_mul_right]
    have h1 : (height D.sp.cm.sig V.gram (x * b) : ℝ) ≤
        (height D.sp.cm.sig V.gram x : ℝ) * (height D.sp.cm.sig V.gram b : ℝ) := by
      exact_mod_cast height_mul_le _ _ x b
    have h0 : (0 : ℝ) ≤ (height D.sp.cm.sig V.gram (x * b) : ℝ) := by positivity
    calc ‖(l.map fun γ t => b⁻¹ * γ t * b).foldr lineDer φ (x * b)‖
        ≤ C * (height D.sp.cm.sig V.gram (x * b) : ℝ) ^ N := hC _
      _ ≤ max C 0 * (height D.sp.cm.sig V.gram (x * b) : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((height D.sp.cm.sig V.gram x : ℝ) * (height D.sp.cm.sig V.gram b : ℝ)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 N) (le_max_right _ _)
      _ = max C 0 * (height D.sp.cm.sig V.gram b : ℝ) ^ N * (height D.sp.cm.sig V.gram x : ℝ) ^ N := by
          rw [mul_pow]; ring

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem infMat_inv_mul (hθ : IsInfFam θ) (V : HSp D) (b : GA D V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) b = 1 ∧
      infMat D.sp.cm.sig V.gram (θ τ) b * infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ = 1 := by
  have rp := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hm := rp.2.2.2.1
  have h1 : infMat D.sp.cm.sig V.gram (θ τ) 1 = 1 := rp.2.2.2.2.1 1 (one_mem _) τ
  exact ⟨by rw [← hm, inv_mul_cancel, h1], by rw [← hm, mul_inv_cancel, h1]⟩

theorem isFrame_mul_inv (hθ : IsInfFam θ) (V : HSp D) (b : GA D V) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ) :
    IsUnit (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) ∧
      (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)ᴴ * Formalism.REAL.Jm e * (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) =
        gramAt D V τ := by
  obtain ⟨e1, e2⟩ := infMat_inv_mul hθ V b τ
  rw [Matrix.inv_eq_left_inv e1]
  have hB : IsUnit (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹) := ⟨⟨_, _, e1, e2⟩, rfl⟩
  refine ⟨hP.mul hB, ?_⟩
  have hu : (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ =
      gramAt D V τ := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V b⁻¹ τ
  rw [← hu, ← h, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem inv_mul_kAt_mul (hθ : IsInfFam θ) (V : HSp D) (b : GA D V) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ)
    (k : Formalism.REAL.KG e) :
    b⁻¹ * kAt θ V τ e (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) k * b = kAt θ V τ e P k := by
  obtain ⟨hP', h'⟩ := isFrame_mul_inv hθ V b τ hP h
  have hx := isAtTau_kAt θ V hθ τ hP' h' k
  have rp := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hm := rp.2.2.2.1
  have hN : (GinfC V).Normal := MonoidHom.normal_ker _
  refine Model.isAtTau_unique θ V hθ ⟨?_, ?_, fun τ' c => ?_⟩ (isAtTau_kAt θ V hθ τ hP h k)
  · have := hN.conj_mem _ hx.1 b⁻¹
    rwa [inv_inv] at this
  · obtain ⟨e1, e2⟩ := infMat_inv_mul hθ V b τ
    rw [hm, hm, hx.2.1, Matrix.inv_eq_left_inv e1, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv e2]
    simp only [Matrix.mul_assoc]
    rw [e1, Matrix.mul_one, ← Matrix.mul_assoc (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹), e1, Matrix.one_mul]
  · obtain ⟨e1, -⟩ := infMat_inv_mul hθ V b τ'
    rw [hm, hm, hx.2.2 _ c, Matrix.mul_one, e1]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl

theorem cuspOn_mul_right : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (φ : GA D V → ℂ), φ ∈ cuspOn θ V X Y T U ε fr ρ c → ∀ b : GA D V, (fun x => φ (x * b)) ∈ cuspOn θ V X Y T (U.map (MulAut.conj b).toMonoidHom) ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) ρ c := by
  intro D θ hθ V U ε fr hfr W _ _ ρ c m X Y T φ hφ b
  obtain ⟨⟨f1, f2, f3, f4⟩, f5⟩ := hφ
  have hN : (GfC V).Normal := MonoidHom.normal_ker _
  refine ⟨⟨isSmModOn_mul_right V f1 b, fun u hu hu' g => ?_, fun τ x => ?_, fun τ k => ?_⟩, fun T' hT' => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hu' ⊢
    have ha' : a ∈ GfC V := by
      have := hN.conj_mem _ hu' b⁻¹
      simpa [mul_assoc] using this
    rw [← f2 a ha ha' (g * b)]
    congr 1
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  · have e : (fun k => φ (x * kAt θ V τ (ε τ) (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) k * b)) =
        fun k => φ (x * b * kAt θ V τ (ε τ) (fr τ) k) := funext fun k => by
      rw [← inv_mul_kAt_mul hθ V b τ (hfr τ).1 (hfr τ).2 k]
      simp only [mul_assoc, mul_inv_cancel_left]
    show (fun k => φ (x * kAt θ V τ (ε τ) (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) k * b)) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ τ)
    rw [e]
    exact f3 τ (x * b)
  · have := GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ b τ k (GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ f1.smooth)
    show gelf θ V τ k (rTr V b φ) = c τ k • rTr V b φ
    rw [this, f4]
    rfl
  · intro μ 𝓕 hμ h𝓕 h1 g
    have := f5 T' hT' μ 𝓕 hμ h𝓕 h1 (g * b)
    simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FrameFamilyRightTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_frame_K_type_coefficients : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (φ : GA D V → ℂ), φ ∈ cuspOn θ V X Y T U ε fr ρ c → ∀ b : GA D V, (fun x => φ (x * b)) ∈ cuspOn θ V X Y T (U.map (MulAut.conj b).toMonoidHom) ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) ρ c := by
  exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl.cuspOn_mul_right
end
end
