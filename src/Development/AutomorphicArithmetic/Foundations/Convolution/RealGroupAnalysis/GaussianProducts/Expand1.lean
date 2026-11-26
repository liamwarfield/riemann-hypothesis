module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.BdInv
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CoordinateEmbedNormZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatMeas
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private theorem hat_n {D : Dat F E} (W : Weil D) (Ψ : S4 F) (ξ : Fin 2 → F) (b : A F) (g : G1 F) :
    hat (W.Om (nU b * g) Ψ).1 (pt ξ) = ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) * hat (W.Om g Ψ).1 (pt ξ) := by
  have hH := (_root_.UpperTheory.ConvolutionTheory.R2.hatSt F E D W).n b (W.Om g Ψ) (pt ξ)
  have e : W.Om (nU b * g) Ψ = W.Om (nU b) (W.Om g Ψ) := by rw [map_mul]; rfl
  have e1 : pt ξ 1 + b * pt ξ 0 = pt ξ 1 := by simp [pt]
  have e3 : b * (pt ξ 2 ^ 2 - rt D.δ * pt ξ 3 ^ 2) = rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b := by
    simp only [pt, rt, map_sub, map_mul, map_pow]
    simp
    ring
  rw [e, hH, e1, Function.update_eq_self, e3]

private theorem hat_meas {D : Dat F E} (W : Weil D) (Ψ : S4 F) (v : V4 F) :
    Measurable fun g : G1 F => hat (W.Om g Ψ).1 v := by
  have hc : Continuous fun p : G1 F × A F =>
      (W.Om p.1 Ψ).1 (Function.update v 1 p.2) * ψ (-(p.2 * v 1)) := by
    have h2 : Continuous fun s : A F => Function.update v 1 s := continuous_const.update 1 continuous_id
    have h1 : Continuous fun p : G1 F × A F => (p.1, Function.update v 1 p.2) :=
      continuous_fst.prodMk (h2.comp continuous_snd)
    have h3 : Continuous fun s : A F => ψ (-(s * v 1)) :=
      Pp.cont_ψ.comp ((continuous_id.mul continuous_const).neg)
    exact ((W.cont Ψ).comp h1).mul (h3.comp continuous_snd)
  exact (hc.stronglyMeasurable.integral_prod_right (ν := adeleMeasure F)).measurable

end UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage

open UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage in
theorem UpperTheory.ConvolutionTheory.R2.G.uxAv :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (f : GL (Fin 2) (A F) → ℂ), Pp.Lf f → ∀ φ h ξ, NInv (ux W f φ h ξ) ∧ av (ux W f φ h ξ) = wx W f φ h ξ ∧
    ∀ b g, ‖ux W f φ h ξ (nU b * g)‖ = ‖f (gl (nU b * g) * dM (nu F h))‖ * ‖hat (W.Om g (W.L h φ)).1 (pt ξ)‖ := by
  intro F E _ _ _ _ _ _ _ D W f hf φ h ξ
  have hgl : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
  have hux : ∀ b g, ux W f φ h ξ (nU b * g) =
      f (gl (nU b) * (gl g * dM (nu F h))) * ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) *
        hat (W.Om g (W.L h φ)).1 (pt ξ) := by
    intro b g
    simp only [ux]
    rw [hat_n, hgl, mul_assoc (gl (nU b)), mul_assoc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have h1 : Continuous fun g : G1 F => f (gl g * dM (nu F h)) :=
      hf.1.comp (_root_.UpperTheory.ConvolutionTheory.R2.M.continuous_gl.mul continuous_const)
    exact h1.measurable.mul (hat_meas W _ _)
  · intro c g
    rw [hux]
    have e : rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * rt c = rt ((ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * c) := (map_mul _ _ _).symm
    have e2 : f (gl (nU (rt c)) * (gl g * dM (nu F h))) = f (gl g * dM (nu F h)) := by
      obtain ⟨γ, hγ⟩ := Pp.rat_n c
      rw [← hγ, hf.2]
    rw [e, Pp.ψ_rt, mul_one, e2]
    rfl
  · funext g
    simp only [av, wx]
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun b => hux b g)
  · intro b g
    simp only [ux]
    rw [hat_n, norm_mul, norm_mul, Pp.norm_ψ, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AbsFin
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AbsFin1
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AdelicWeightFourNonneg
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_cD (s : (A F)ˣ) : Continuous (cD s : G1 F → G1 F) := by
  refine Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
  have he : ∀ i j, Continuous fun g : G1 F => g.1 i j := fun i j =>
    (Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_elem i j
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact he 0 0
  · exact (he 0 1).mul continuous_const
  · exact continuous_const.mul (he 1 0)
  · exact he 1 1

private theorem cD_cD_inv (s : (A F)ˣ) (k : G1 F) : cD s (cD s⁻¹ k) = k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD, mul_assoc]

private theorem infOrth_cD {s : (A F)ˣ} (h1 : (s : A F).1 = 1) (h2 : ((s⁻¹ : (A F)ˣ) : A F).1 = 1)
    {k : G1 F} (hk : InfOrth k) : InfOrth (cD s k) := by
  have hm : ∀ a b : A F, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  have hent : ∀ i j, ((cD s k).1 i j).1 = (k.1 i j).1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · change (k.1 0 1 * ((s⁻¹ : (A F)ˣ) : A F)).1 = _
      rw [hm, h2, mul_one]
      rfl
    · change ((s : A F) * k.1 1 0).1 = _
      rw [hm, h1, one_mul]
      rfl
    · rfl
  intro i j
  have e : ∀ a b c d : A F, (a * b + c * d).1 = a.1 * b.1 + c.1 * d.1 := fun _ _ _ _ => rfl
  have h := hk i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, e, Matrix.transpose_apply, Matrix.transpose_apply] at h ⊢
  rw [hent, hent, hent, hent]
  exact h

private theorem adelicWeightFour_mono {L L' : (FractionalIdeal (𝓞 F)⁰ F)ˣ}
    (h : (L : FractionalIdeal (𝓞 F)⁰ F) ≤ L') (N : ℕ) (v : V4 F) : wt4 L N v ≤ wt4 L' N v :=
  Finset.prod_le_prod₀ (fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _)
    fun i _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_mono h N (v i)

private theorem adelicWeightFour_nonneg (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (v : V4 F) : 0 ≤ wt4 L N v :=
  Finset.prod_nonneg fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _

private theorem common_majorant {n : ℕ} (Ψ : Fin n → V4 F → ℂ)
    (hΨ : ∀ i, Ψ i ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (N : ℕ) :
    ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧ ∀ i v, ‖Ψ i v‖ ≤ B * wt4 L N v := by
  have one : ∀ i, ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧
      ∀ v, ‖Ψ i v‖ ≤ B * wt4 L N v := by
    intro i
    obtain ⟨M, L, hM, hb⟩ := GlobalTheory.CompanionTheory.EpConvB.exists_majorant (hΨ i)
      (isCompact_singleton (x := (1 : GL (Fin 4) (A F)))) N
    refine ⟨M, L, hM, fun v => ?_⟩
    have h := hb 1 rfl v
    simpa [wt4] using h
  choose B L hB hb using one
  have key : ∀ s : Finset (Fin n), ∃ (B' : ℝ) (L' : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B' ∧
      ∀ i ∈ s, ∀ v, ‖Ψ i v‖ ≤ B' * wt4 L' N v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, 1, le_rfl, by simp⟩
    | insert a s _ ih =>
      obtain ⟨B', L', h0, h⟩ := ih
      refine ⟨B a + B', fractionalIdealSupUnit (L a) L', add_nonneg (hB a) h0, fun i hi v => ?_⟩
      have hl : wt4 (L a) N v ≤ wt4 (fractionalIdealSupUnit (L a) L') N v :=
        adelicWeightFour_mono le_sup_left N v
      have hr : wt4 L' N v ≤ wt4 (fractionalIdealSupUnit (L a) L') N v :=
        adelicWeightFour_mono le_sup_right N v
      have hw := adelicWeightFour_nonneg (fractionalIdealSupUnit (L a) L') N v
      rcases Finset.mem_insert.1 hi with rfl | hi
      · calc ‖Ψ i v‖ ≤ B i * wt4 (L i) N v := hb i v
          _ ≤ B i * wt4 (fractionalIdealSupUnit (L i) L') N v :=
            mul_le_mul_of_nonneg_left hl (hB i)
          _ ≤ (B i + B') * wt4 (fractionalIdealSupUnit (L i) L') N v :=
            mul_le_mul_of_nonneg_right (by linarith) hw
      · calc ‖Ψ i v‖ ≤ B' * wt4 L' N v := h i hi v
          _ ≤ B' * wt4 (fractionalIdealSupUnit (L a) L') N v :=
            mul_le_mul_of_nonneg_left hr h0
          _ ≤ (B a + B') * wt4 (fractionalIdealSupUnit (L a) L') N v :=
            mul_le_mul_of_nonneg_right (by linarith [hB a]) hw
  obtain ⟨B', L', h0, h⟩ := key Finset.univ
  exact ⟨B', L', h0, fun i v => h i (Finset.mem_univ i) v⟩

end UpperTheory.ConvolutionTheory.R2.G

theorem UpperTheory.ConvolutionTheory.R2.G.majL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ φ ∈ Fock D.δ, ∀ h : GL (Fin 2) (A E), ((nu F h : (A F)ˣ) : A F).1 = 1 → ∀ N : ℕ,
    ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧ ∀ k ∈ KK F, ∀ v, ‖hat (W.Om k (W.L h φ)).1 v‖ ≤ B * wt4 L N v := by
  intro F E _ _ _ _ _ _ _ D W φ hφ h ht N
  have hinv : (((nu F h)⁻¹ : (A F)ˣ) : A F).1 = 1 := by
    have h1 : (((nu F h : (A F)ˣ) : A F) * (((nu F h)⁻¹ : (A F)ˣ) : A F)).1 = (1 : A F).1 := by
      rw [Units.mul_inv]
    have h2 : (((nu F h : (A F)ˣ) : A F) * (((nu F h)⁻¹ : (A F)ˣ) : A F)).1 =
        ((nu F h : (A F)ˣ) : A F).1 * (((nu F h)⁻¹ : (A F)ˣ) : A F).1 := rfl
    rw [h2, ht, one_mul] at h1
    exact h1
  have hC : IsCompact (cD (nu F h)⁻¹ '' KK F) :=
    (UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2.image (continuous_cD _)
  have hO : ∀ k ∈ cD (nu F h)⁻¹ '' KK F, InfOrth k := by
    rintro _ ⟨k, hk, rfl⟩
    exact infOrth_cD hinv (by rw [inv_inv]; exact ht) hk.1
  obtain ⟨U, -, hU, hm⟩ := (fockSt F E D W).om φ hφ _ hC hO
  obtain ⟨n, b, c, B, -, -, hb⟩ := coefBd F E D W φ _ U hC hU hm
  obtain ⟨H, hH⟩ := hatLin F
  obtain ⟨B', L, hB', hmaj⟩ := common_majorant (fun i => (H (W.L h (b i))).1)
    (fun i => (H (W.L h (b i))).2) N
  refine ⟨n * (|B| * B'), L, by positivity, fun k hk v => ?_⟩
  obtain ⟨hc, he⟩ := hb _ ⟨k, hk, rfl⟩
  have hcomm : W.Om k (W.L h φ) = W.L h (W.Om (cD (nu F h)⁻¹ k) φ) := by
    have h1 := LinearMap.congr_fun (W.comm h (cD (nu F h)⁻¹ k)) φ
    rw [cD_cD_inv] at h1
    exact h1.symm
  have hexp : hat (W.Om k (W.L h φ)).1 v =
      ∑ i, c i (cD (nu F h)⁻¹ k) * (H (W.L h (b i))).1 v := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hcomm, he, ← hH, map_sum, map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [hexp]
  have hw := adelicWeightFour_nonneg L N v
  calc ‖∑ i, c i (cD (nu F h)⁻¹ k) * (H (W.L h (b i))).1 v‖
      ≤ ∑ i, ‖c i (cD (nu F h)⁻¹ k) * (H (W.L h (b i))).1 v‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, |B| * (B' * wt4 L N v) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact mul_le_mul ((hc i).trans (le_abs_self B)) (hmaj i v) (norm_nonneg _) (abs_nonneg B)
    _ = n * (|B| * B') * wt4 L N v := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.absFin1 :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h : GL (Fin 2) (A E), ((nu F h : (A F)ˣ) : A F).1 = 1 → ∑' ξ, abelian₂ M (ux W f.1 φ h ξ) ≠ ⊤ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h hnu
  haveI := M.prob
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨N, hN⟩ := UpperTheory.ConvolutionTheory.R2.G.zetaFin F
  obtain ⟨B', L, hB'0, hB'⟩ := UpperTheory.ConvolutionTheory.R2.G.majL F E D W φ hφ h hnu N
  have hC : IsCompact ((fun k : G1 F => gl k * dM (nu F h)) '' KK F) :=
    (UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2.image (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.mul continuous_const)
  obtain ⟨B, hB0, hB⟩ := UpperTheory.ConvolutionTheory.R2.G.bdInv F π f hf _ hC
  have hLf := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1
  let w : IdeleGroup F → (Fin 2 → F) → ℝ := fun a ξ =>
    wt4 L N ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)]
  have hw : ∀ ξ, Continuous fun a : IdeleGroup F => w a ξ := by
    intro ξ
    have h1 : Continuous (wt4 L N : V4 F → ℝ) :=
      continuous_finsetProd _ fun i _ =>
        (GlobalTheory.CompanionTheory.EpConvB.continuous_adeleWeight L N).comp (continuous_apply i)
    refine h1.comp (continuous_pi fun i => ?_)
    fin_cases i
    · exact continuous_const
    · exact Units.continuous_coe_inv
    · exact Units.continuous_val.mul continuous_const
    · exact Units.continuous_val.mul continuous_const
  have pw : ∀ (a : IdeleGroup F), ∀ k ∈ KK F, ∀ (b : A F) (ξ : Fin 2 → F),
      ‖ux W f.1 φ h ξ (nU b * (mD a * k))‖ ≤ B * B' * w a ξ := by
    intro a k hk b ξ
    rw [(UpperTheory.ConvolutionTheory.R2.G.uxAv F E D W f.1 hLf φ h ξ).2.2 b (mD a * k)]
    have hgl : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
    have e1 : gl (nU b * (mD a * k)) * dM (nu F h) = gl (nU b * mD a) * (gl k * dM (nu F h)) := by
      rw [← mul_assoc, hgl (nU b * mD a) k, mul_assoc]
    have h1 := (hB b a _ ⟨k, hk, rfl⟩).1
    rw [← e1] at h1
    have e2 : hat (W.Om (mD a * k) (W.L h φ)).1 (pt ξ) = ((W.η.1 a : ℂˣ) : ℂ) * ((ab a : ℝ) : ℂ) *
        hat (W.Om k (W.L h φ)).1 ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F) * rt (ξ 0), (a : A F) * rt (ξ 1)] := by
      rw [map_mul, Module.End.mul_apply, (UpperTheory.ConvolutionTheory.R2.hatSt F E D W).m]
      simp [pt]
    have hη : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
      have h2 : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
        have := congrArg (fun u : ℂˣ => (u : ℂ)) (W.η_sq a)
        simpa using this
      have h3 : ‖((W.η.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := by rw [← norm_pow, h2, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
    have hab : 0 < ab a := UpperTheory.ConvolutionTheory.R2.M.ab_pos a
    have h4 : ‖hat (W.Om (mD a * k) (W.L h φ)).1 (pt ξ)‖ ≤ ab a * (B' * w a ξ) := by
      rw [e2, norm_mul, norm_mul, hη, one_mul, Complex.norm_real, Real.norm_of_nonneg hab.le]
      exact mul_le_mul_of_nonneg_left (hB' k hk _) hab.le
    calc _ ≤ (B * (ab a)⁻¹) * (ab a * (B' * w a ξ)) :=
          mul_le_mul h1 h4 (norm_nonneg _) (mul_nonneg hB0 (inv_pos.2 hab).le)
      _ = B * B' * w a ξ := by field_simp
  have hae : ∀ᵐ p ∂M.ν, p.2 ∈ KK F := by
    have h0 : ∀ᵐ k ∂M.κ, k ∈ KK F := by
      rw [ae_iff]
      exact M.supp
    exact Measure.quasiMeasurePreserving_snd.ae h0
  let G : (Fin 2 → F) → IdeleGroup F → ℝ≥0∞ := fun ξ a =>
    _root_.UpperTheory.ConvolutionTheory.R2.M.wt a * ENNReal.ofReal (w a ξ)
  have hG : ∀ ξ, Measurable (G ξ) := fun ξ =>
    _root_.UpperTheory.ConvolutionTheory.R2.M.measurable_wt.mul (hw ξ).measurable.ennreal_ofReal
  have key : ∀ ξ, abelian₂ M (ux W f.1 φ h ξ) ≤ ENNReal.ofReal (B * B') * ∫⁻ a, G ξ a ∂(ideleMeasure F) := by
    intro ξ
    have hm : Measurable fun p : IdeleGroup F × G1 F => G ξ p.1 := (hG ξ).comp measurable_fst
    have e : ∫⁻ p, G ξ p.1 ∂M.ν = ∫⁻ a, G ξ a ∂(ideleMeasure F) := by
      rw [Meas.ν, lintegral_prod _ hm.aemeasurable]
      simp
    rw [← e, ← lintegral_const_mul _ hm, abelian₂, _root_.UpperTheory.ConvolutionTheory.R2.M.J0]
    refine lintegral_mono_ae (hae.mono fun p hp => ?_)
    have hb : ∫⁻ b in fundamentalSet F, ‖ux W f.1 φ h ξ (nU b * (mD p.1 * p.2))‖ₑ ∂(adeleMeasure F) ≤
        ENNReal.ofReal (B * B') * ENNReal.ofReal (w p.1 ξ) := by
      have hw0 : 0 ≤ B * B' := mul_nonneg hB0 hB'0
      calc _ ≤ ∫⁻ _ in fundamentalSet F, ENNReal.ofReal (B * B' * w p.1 ξ) ∂(adeleMeasure F) := by
            refine lintegral_mono fun b => ?_
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (pw p.1 p.2 hp b ξ)
        _ = _ := by
            rw [setLIntegral_const, adeleMeasure_fundamentalSet, mul_one, ENNReal.ofReal_mul hw0]
    calc _ ≤ _root_.UpperTheory.ConvolutionTheory.R2.M.wt p.1 * (ENNReal.ofReal (B * B') * ENNReal.ofReal (w p.1 ξ)) := by
          gcongr
      _ = _ := by
          simp only [G]
          ring
  have hsum : ∑' ξ, ∫⁻ a, G ξ a ∂(ideleMeasure F) ≠ ⊤ := by
    rw [← lintegral_tsum fun ξ => (hG ξ).aemeasurable]
    have e : ∀ a, ∑' ξ, G ξ a = _root_.UpperTheory.ConvolutionTheory.R2.M.wt a * ∑' ξ, ENNReal.ofReal (w a ξ) :=
      fun a => ENNReal.tsum_mul_left
    simp_rw [e]
    exact hN L
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum key)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.UxCen
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.uxCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2) (s : (A F)ˣ) (h : GL (Fin 2) (A E)), ∃ (h₁ : GL (Fin 2) (A E)) (c : ℂ), nu F h = s ^ 4 * nu F h₁ ∧
    ∀ f ∈ π.V, ∀ φ ξ g, ux W f.1 φ h ξ g = c * ux W f.1 φ h₁ ξ (g * mD (s ^ 2)⁻¹) := by
  intro F E _ _ _ _ _ _ _ D W π s h
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨z, hz⟩ : ∃ z : (A E)ˣ, ideleNorm F E z = s ^ 2 := ⟨ideleEmbedding F E s, D.ideleNorm_emb s⟩
  obtain ⟨hL, hnu⟩ := UpperTheory.ConvolutionTheory.R2.Ff.lCen F E D W z
  rw [hz] at hL hnu
  obtain ⟨h₁, rfl⟩ : ∃ h₁, h = Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁ :=
    ⟨_, (mul_inv_cancel_left _ _).symm⟩
  have hnh : nu F (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁) = s ^ 4 * nu F h₁ := by
    rw [nu_mul, hnu, ← pow_mul]
  refine ⟨h₁, ((ω (s ^ 2) : ℂˣ) : ℂ), hnh, fun f hf φ ξ g => ?_⟩
  have e0 : dM (s ^ 4) = gl (mD (s ^ 2)⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) (s ^ 2) := by
    rw [← gl_mD_mul_dM_sq (s ^ 2), mD_inv, gl_inv, inv_mul_cancel_left, ← pow_mul]
  have e1 : gl g * dM (s ^ 4 * nu F h₁) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (s ^ 2) * (gl (g * mD (s ^ 2)⁻¹) * dM (nu F h₁)) := by
    rw [dM_mul, e0, mul_assoc (gl _) _ (dM _), UpperTheory.ConvolutionTheory.R2.scalar_comm (s ^ 2) (dM _),
      UpperTheory.ConvolutionTheory.R2.scalar_comm (s ^ 2) (gl _ * dM _), gl_mul]
    simp only [mul_assoc]
  have e2 : W.Om g (W.L (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁) φ) =
      W.Om (g * mD (s ^ 2)⁻¹) (W.L h₁ φ) := by
    rw [map_mul, hL, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [ux, ux, hnh, e1, hω f hf, e2, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.LamRight
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors


open scoped Pointwise in
private theorem lint_add {F : Type} [Field F] [NumberField F] {h : A F → ℝ≥0∞}
    (hh : ∀ (k : F) x, h (rt k + x) = h x) (a : A F) :
    ∫⁻ b in fundamentalSet F, h (b + a) ∂(adeleMeasure F) = ∫⁻ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  have hD := isAddFundamentalDomain_fundamentalSet F
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
    refine (Set.countable_range (fun ξ : F => (rt ξ : A F))).mono ?_ |>.to_subtype
    rintro _ ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩
  have hT := hD.vadd_of_comm a
  have hp := measurePreserving_add_right (adeleMeasure F) a
  have e : (fun b : A F => b + a) ⁻¹' (a +ᵥ fundamentalSet F) = fundamentalSet F := by
    ext x
    simp [Set.mem_vadd_set, add_comm]
  have h1 := hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.addRight a).measurableEmbedding h (a +ᵥ fundamentalSet F)
  rw [e] at h1
  rw [h1]
  refine hT.setLIntegral_eq hD h ?_
  rintro ⟨_, k, rfl⟩ x
  exact hh k x

theorem UpperTheory.ConvolutionTheory.R2.G.lamRight :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (u : G1 F → ℂ), NInv u → ∀ (c : ℂ) (g₀ : G1 F), abelian₂ M (fun g => c * u (g * g₀)) = ‖c‖ₑ * abelian₂ M u := by
  intro F _ _ _ M₀ u hu c g₀
  have hnU : Measurable (nU : A F → G1 F) := M.continuous_nU.measurable
  set U : G1 F → ℝ≥0∞ := fun g => ∫⁻ b in fundamentalSet F, ‖u (nU b * g)‖ₑ ∂(adeleMeasure F) with hUdef
  have hUm : Measurable U :=
    Measurable.lintegral_prod_right' (ν := (adeleMeasure F).restrict (fundamentalSet F))
      (f := fun q : G1 F × A F => ‖u (nU q.2 * q.1)‖ₑ)
      (hu.1.comp ((hnU.comp measurable_snd).mul measurable_fst)).enorm
  have hUi : ∀ b g, U (nU b * g) = U g := by
    intro a g
    have := lint_add (F := F) (h := fun b => ‖u (nU b * g)‖ₑ) (fun k x => by
      simp only [M.nU_add, mul_assoc, hu.2]) a
    simp only [hUdef]
    rw [← this]
    simp only [M.nU_add, mul_assoc]
  have hc : ‖c‖ₑ ≠ ⊤ := enorm_ne_top
  have hJ := M.lintegral_unipotent_quotient_right_invariant F M₀ U hUm hUi g₀
  have hL : abelian₂ M₀ (fun g => c * u (g * g₀)) = ‖c‖ₑ * M.J0 M₀ (fun g => U (g * g₀)) := by
    simp only [abelian₂, M.J0]
    rw [← lintegral_const_mul' _ _ hc]
    refine lintegral_congr fun p => ?_
    have : ∫⁻ b in fundamentalSet F, ‖c * u (nU b * (mD p.1 * p.2) * g₀)‖ₑ ∂(adeleMeasure F) =
        ‖c‖ₑ * U (mD p.1 * p.2 * g₀) := by
      simp only [hUdef, enorm_mul, mul_assoc]
      exact lintegral_const_mul' _ _ hc
    rw [this]
    ring
  rw [hL, hJ]
  rfl
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.absFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h : GL (Fin 2) (A E), ∑' ξ, abelian₂ M (ux W f.1 φ h ξ) ≠ ⊤ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  obtain ⟨s, hs⟩ := UpperTheory.ConvolutionTheory.R2.G.nuPos F E D h
  obtain ⟨h₁, c, hnu, hux⟩ := UpperTheory.ConvolutionTheory.R2.G.uxCen F E D W π s h
  have hnu₁ : ((nu F h₁ : (A F)ˣ) : A F).1 = 1 := by
    have e : nu F h * (s ^ 4)⁻¹ = nu F h₁ := by
      rw [hnu, mul_comm, inv_mul_cancel_left]
    rw [← e]
    exact hs
  have hLf : Pp.Lf f.1 := (Pp.cuspZero F π f hf).1
  have hterm : ∀ ξ, abelian₂ M (ux W f.1 φ h ξ) = ‖c‖ₑ * abelian₂ M (ux W f.1 φ h₁ ξ) := by
    intro ξ
    have e : ux W f.1 φ h ξ = fun g => c * ux W f.1 φ h₁ ξ (g * mD (s ^ 2)⁻¹) :=
      funext fun g => hux f hf φ ξ g
    rw [e]
    exact UpperTheory.ConvolutionTheory.R2.G.lamRight F M _ (UpperTheory.ConvolutionTheory.R2.G.uxAv F E D W f.1 hLf φ h₁ ξ).1 c _
  simp only [hterm]
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top enorm_ne_top (UpperTheory.ConvolutionTheory.R2.G.absFin1 F E D W M π f hf φ hφ h₁ hnu₁)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.UnfoldSum
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem enorm_tsum_le' {β : Type*} (f : β → ℂ) : ‖∑' b, f b‖ₑ ≤ ∑' b, ‖f b‖ₑ := by
  by_cases h : ∑' b, ‖f b‖ₑ = ⊤
  · simp [h]
  · have hs : Summable fun b => ‖f b‖ := by
      simpa [toReal_enorm] using ENNReal.summable_toReal h
    have h1 : ‖∑' b, f b‖ ≤ ∑' b, ‖f b‖ := norm_tsum_le_tsum_norm hs
    have h2 : ENNReal.ofReal (∑' b, ‖f b‖) = ∑' b, ‖f b‖ₑ := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
      simp [ofReal_norm_eq_enorm]
    rw [← h2, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal h1

private theorem tsum_comm_of_enorm {α β : Type*} (f : α → β → ℂ) (h : ∑' a, ∑' b, ‖f a b‖ₑ ≠ ⊤) :
    ∑' b, ∑' a, f a b = ∑' a, ∑' b, f a b := by
  have h' : ∑' p : α × β, ‖Function.uncurry f p‖ₑ ≠ ⊤ := by
    have : ∑' p : α × β, ‖Function.uncurry f p‖ₑ = ∑' a, ∑' b, ‖f a b‖ₑ :=
      ENNReal.tsum_prod (f := fun a b => ‖f a b‖ₑ)
    rwa [this]
  have hs : Summable fun p => ‖Function.uncurry f p‖ := by
    simpa [toReal_enorm] using ENNReal.summable_toReal h'
  exact (Summable.of_norm hs).tsum_comm

theorem UpperTheory.ConvolutionTheory.R2.G.unfoldSum :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (σ : Rw F → Matrix.SpecialLinearGroup (Fin 2) F), _root_.UpperTheory.ConvolutionTheory.R2.M.RowSec σ → ∀ (ι : Type) [Countable ι] (u : ι → G1 F → ℂ), (∀ i, NInv (u i)) → ∑' i, abelian₂ M (u i) ≠ ⊤ →
    Summable (fun i => ‖M.I0 (av (u i))‖) ∧ IntegrableOn (fun g => ∑' r, ∑' i, u i (ratS F (σ r) * g)) M.D M.μ ∧
    ∫ g in M.D, ∑' r, ∑' i, u i (ratS F (σ r) * g) ∂M.μ = ∑' i, M.I0 (av (u i)) := by
  intro F _ _ _ M σ hσ ι _ u hu hL
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hLi : ∀ i, abelian₂ M (u i) ≠ ⊤ := fun i => ne_top_of_le_ne_top hL (ENNReal.le_tsum (f := fun i => abelian₂ M (u i)) i)
  have hC := fun i => _root_.UpperTheory.ConvolutionTheory.R2.M.unfC F M σ (u i) hσ (hu i).1 (hu i).2 (hLi i)
  have hTL : ∀ i, ∫⁻ g in M.D, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ∂M.μ = abelian₂ M (u i) := fun i =>
    _root_.UpperTheory.ConvolutionTheory.R2.M.unfL F M σ (fun g => ‖u i g‖ₑ) hσ (hu i).1.enorm
      (fun ξ g => by simp only [(hu i).2 ξ g])
  have hTm : ∀ i, Measurable fun g : G1 F => ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ := fun i =>
    Measurable.tsum fun r => ((hu i).1.comp (measurable_const_mul _)).enorm
  have hTT : ∫⁻ g in M.D, ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ∂M.μ = ∑' i, abelian₂ M (u i) := by
    rw [lintegral_tsum fun i => (hTm i).aemeasurable]
    exact tsum_congr hTL
  have hfin : ∀ᵐ g ∂(M.μ.restrict M.D), ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ ≠ ⊤ := by
    have hm : AEMeasurable (fun g : G1 F => ∑' i, ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ) (M.μ.restrict M.D) :=
      (Measurable.tsum hTm).aemeasurable
    filter_upwards [ae_lt_top' hm (by rw [hTT]; exact hL)] with g hg using hg.ne
  have hST : ∀ i g, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ≤ ∑' r, ‖u i (ratS F (σ r) * g)‖ₑ := fun i g =>
    enorm_tsum_le' _
  have hSL : ∀ i, ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≤ abelian₂ M (u i) := fun i =>
    (lintegral_mono fun g => hST i g).trans_eq (hTL i)
  have hsum : ∑' i, ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≠ ⊤ :=
    ne_top_of_le_ne_top hL (ENNReal.tsum_le_tsum hSL)
  have hSm : ∀ i, AEStronglyMeasurable (fun g => ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) :=
    fun i => (hC i).2.1.aestronglyMeasurable
  have hI := integral_tsum hSm hsum
  have hae : ∀ᵐ g ∂(M.μ.restrict M.D),
      ∑' r, ∑' i, u i (ratS F (σ r) * g) = ∑' i, ∑' r, u i (ratS F (σ r) * g) := by
    filter_upwards [hfin] with g hg using
      tsum_comm_of_enorm (fun i r => u i (ratS F (σ r) * g)) hg
  have hI0 : ∀ i, M.I0 (av (u i)) = ∫ g in M.D, ∑' r, u i (ratS F (σ r) * g) ∂M.μ := fun i =>
    ((hC i).2.2.2).symm
  refine ⟨?_, ?_, ?_⟩
  · have hle : ∀ i, ‖M.I0 (av (u i))‖ₑ ≤ ∫⁻ g in M.D, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ := fun i => by
      rw [hI0 i]
      exact enorm_integral_le_lintegral_enorm _
    have : ∑' i, ‖M.I0 (av (u i))‖ₑ ≠ ⊤ := ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hle)
    simpa [toReal_enorm] using ENNReal.summable_toReal this
  · have hsm : AEStronglyMeasurable (fun g => ∑' i, ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) := by
      refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
        (f := fun (s : Finset ι) g => ∑ i ∈ s, ∑' r, u i (ratS F (σ r) * g)) ?_ ?_
      · intro s
        exact Finset.aestronglyMeasurable_fun_sum s fun i _ => hSm i
      · filter_upwards [hfin] with g hg
        have h1 : ∑' i, ‖∑' r, u i (ratS F (σ r) * g)‖ₑ ≠ ⊤ :=
          ne_top_of_le_ne_top hg (ENNReal.tsum_le_tsum fun i => hST i g)
        have h2 : Summable fun i => ‖∑' r, u i (ratS F (σ r) * g)‖ := by
          simpa [toReal_enorm] using ENNReal.summable_toReal h1
        exact (Summable.of_norm h2).hasSum
    have hint : Integrable (fun g => ∑' i, ∑' r, u i (ratS F (σ r) * g)) (M.μ.restrict M.D) := by
      refine ⟨hsm, ?_⟩
      have hb : ∫⁻ g in M.D, ‖∑' i, ∑' r, u i (ratS F (σ r) * g)‖ₑ ∂M.μ ≤ ∑' i, abelian₂ M (u i) := by
        rw [← hTT]
        refine lintegral_mono fun g => ?_
        exact (enorm_tsum_le' _).trans (ENNReal.tsum_le_tsum fun i => hST i g)
      exact lt_of_le_of_lt hb hL.lt_top
    exact hint.congr (hae.mono fun g hg => hg.symm)
  · rw [integral_congr_ae hae, hI]
    exact tsum_congr fun i => (hI0 i).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Kern
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private def eqv (F : Type) : (Fin 2 → F) × (Fin 2 → F) ≃ (Fin 4 → F) where
  toFun p := ![p.1 0, p.1 1, p.2 0, p.2 1]
  invFun x := (![x 0, x 1], ![x 2, x 3])
  left_inv p := by
    rcases p with ⟨a, b⟩
    refine Prod.ext ?_ ?_ <;> (ext i; fin_cases i <;> rfl)
  right_inv x := by ext i; fin_cases i <;> rfl

theorem UpperTheory.ConvolutionTheory.R2.G.kern :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (σ : Rw F → Matrix.SpecialLinearGroup (Fin 2) F), M.RowSec σ → ∀ φ : S4 F,
    Th φ.1 = ThRow 0 0 φ.1 + ∑' r : Rw F, ∑' ξ : Fin 2 → F, hat (W.Om (ratS F (σ r)) φ).1 (pt ξ) := by
  intro F E _ _ _ _ _ _ _ D W σ hσ φ
  have H := UpperTheory.ConvolutionTheory.R2.hatSt F E D W
  have hs : Summable (fun ξ : Fin 4 → F => hat φ.1 fun i => rt (ξ i)) :=
    (poisson_of_mem_schwartzBruhatPi (H.mem φ)).1.of_norm
  have hs2 : Summable (fun p : (Fin 2 → F) × (Fin 2 → F) => hat φ.1 ![rt (p.1 0), rt (p.1 1), rt (p.2 0), rt (p.2 1)]) := by
    have h := ((eqv F).summable_iff).2 hs
    refine h.congr fun p => ?_
    simp only [Function.comp]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hrowsum : Summable (fun r : Fin 2 → F => ThRow (rt (r 0)) (rt (r 1)) φ.1) := hs2.prod
  have hth : Th φ.1 = ∑' r : Fin 2 → F, ThRow (rt (r 0)) (rt (r 1)) φ.1 := by
    rw [H.th φ, Th, ← (eqv F).tsum_eq, ]
    have : (fun p : (Fin 2 → F) × (Fin 2 → F) => hat φ.1 fun i => rt ((eqv F) p i)) =
        fun p => hat φ.1 ![rt (p.1 0), rt (p.1 1), rt (p.2 0), rt (p.2 1)] := by
      funext p
      congr 1
      ext i
      fin_cases i <;> rfl
    rw [this, hs2.tsum_prod]
    rfl
  have hr : ∀ r : Rw F, ThRow (rt (r.1 0)) (rt (r.1 1)) φ.1 =
      ∑' ξ : Fin 2 → F, hat (W.Om (ratS F (σ r)) φ).1 (pt ξ) := by
    intro r
    have hv : (![0, 1] : Fin 2 → F) ᵥ* (σ r).1 = r.1 := by
      rw [← hσ r]
      ext j
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have h := H.row (σ r) ![0, 1] φ
    rw [hv] at h
    rw [← h]
    simp [ThRow, pt]
  rw [hth, hrowsum.tsum_eq_add_tsum_ite (0 : Fin 2 → F)]
  have h0 : ThRow (rt ((0 : Fin 2 → F) 0)) (rt ((0 : Fin 2 → F) 1)) φ.1 = ThRow 0 0 φ.1 := by simp
  rw [h0]
  refine congrArg _ ?_
  have h1 := tsum_subtype {r : Fin 2 → F | r ≠ 0} (fun r => ThRow (rt (r 0)) (rt (r 1)) φ.1)
  have h2 : ∑' r : Rw F, ∑' ξ : Fin 2 → F, hat (W.Om (ratS F (σ r)) φ).1 (pt ξ) =
      ∑' r : {r : Fin 2 → F | r ≠ 0}, ThRow (rt (r.1 0)) (rt (r.1 1)) φ.1 :=
    tsum_congr fun r => (hr r).symm
  rw [h2, h1]
  refine tsum_congr fun r => ?_
  by_cases h : r = 0
  · simp [h]
  · simp [h]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.expand1 :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, Summable (fun ξ => ‖Wx W M f.1 φ h ξ‖) ∧
    lift W M f.1 φ h = T0 W M f.1 φ h + ∑' ξ, Wx W M f.1 φ h ξ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hL := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1
  obtain ⟨σ, hσ⟩ := exists_rowSec (F := F)
  have hN := fun ξ => UpperTheory.ConvolutionTheory.R2.G.uxAv F E D W f.1 hL φ h ξ
  obtain ⟨hs, hi, he⟩ := UpperTheory.ConvolutionTheory.R2.G.unfoldSum F M σ hσ (Fin 2 → F) (ux W f.1 φ h)
    (fun ξ => (hN ξ).1) (UpperTheory.ConvolutionTheory.R2.G.absFin F E D W M π f hf φ hφ h)
  have hav : ∀ ξ, M.I0 (av (ux W f.1 φ h ξ)) = Wx W M f.1 φ h ξ := fun ξ => by
    rw [(hN ξ).2.1]; rfl
  simp only [hav] at hs he
  obtain ⟨-, c2, -⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ h
  have hk : ∀ g : G1 F, f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 =
      f.1 (gl g * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1 +
        ∑' r, ∑' ξ, ux W f.1 φ h ξ (ratS F (σ r) * g) := by
    intro g
    rw [UpperTheory.ConvolutionTheory.R2.G.kern F E D W σ hσ (W.Om g (W.L h φ)), mul_add]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    have e1 : f.1 (gl (ratS F (σ r) * g) * dM (nu F h)) = f.1 (gl g * dM (nu F h)) := by
      rw [gl_mul, gl_ratS, mul_assoc, hL.2]
    have e2 : W.Om (ratS F (σ r) * g) (W.L h φ) = W.Om (ratS F (σ r)) (W.Om g (W.L h φ)) := by
      rw [map_mul]; rfl
    simp only [ux]
    rw [e1, e2]
  refine ⟨hs, ?_⟩
  have hlift : lift W M f.1 φ h = ∫ g in M.D, (f.1 (gl g * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1 +
      ∑' r, ∑' ξ, ux W f.1 φ h ξ (ratS F (σ r) * g)) ∂M.μ :=
    integral_congr_ae (Eventually.of_forall hk)
  rw [hlift, integral_add c2 hi, he]
  rfl
