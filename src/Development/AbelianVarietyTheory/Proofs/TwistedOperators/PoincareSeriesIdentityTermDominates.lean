module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompSmulLatticeEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharInfinityEqCoeffMulHalfNormPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumProdNormLeOfProdNormLowerBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LongElementEmbeddingNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompSmulLatticeEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decomp_smul_lattice_embedding : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (x : GA D Y) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin V.rank → D.host.E), w ∈ 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) → ∃ y ∈ 𝔪 • latAt Λ x, ∃ u : 𝓞 D.host.E, u ∈ 𝔪 ∧ w = frameMat V Y d.ι *ᵥ y + (u : D.host.E) • zv d := by
  first | exact @GlobalTheory.UnitaryEmbeddingLattice.mem_smul_lattice_unitaryEmbedding | exact GlobalTheory.UnitaryEmbeddingLattice.mem_smul_lattice_unitaryEmbedding | (intros; apply GlobalTheory.UnitaryEmbeddingLattice.mem_smul_lattice_unitaryEmbedding <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtAbsNormLeProdNormCmTypeEmbeddings
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtAbsNormLeProdNormCmTypeEmbeddings
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CMNorm

theorem sqrt_absNorm_le_prod_tauE : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (u : 𝓞 D.host.E), u ∈ 𝔪 → u ≠ 0 → Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, ‖tauE D τ (u : D.host.E)‖ := by
  intro D 𝔪 u hu hu0
  have hnorm : ∏ τ, ‖tauE D τ (u : D.host.E)‖ ^ 2 = |((Algebra.norm ℚ (u : D.host.E) : ℚ) : ℝ)| := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm]
    refine (Fintype.prod_bijective _ (GlobalTheory.LevelSeries.mk_tauE_bij D) _ _ (fun τ => ?_))
    rw [NumberField.InfinitePlace.mult, if_neg (GlobalTheory.LevelSeries.mk_tauE_complex D τ)]
    rfl
  have hspan : Ideal.span {u} ≤ 𝔪 := (Ideal.span_singleton_le_iff_mem _).2 hu
  have hne : Ideal.absNorm (Ideal.span {u}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hu0
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hspan
  have hle : Ideal.absNorm 𝔪 ≤ Ideal.absNorm (Ideal.span {u}) := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have habs : ((Ideal.absNorm (Ideal.span {u}) : ℕ) : ℝ) = |((Algebra.norm ℚ (u : D.host.E) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton]
    rw [← Algebra.coe_norm_int]
    push_cast
    simp
  have hle' : ((Ideal.absNorm 𝔪 : ℕ) : ℝ) ≤ (∏ τ, ‖tauE D τ (u : D.host.E)‖) ^ 2 := by
    rw [← Finset.prod_pow, hnorm, ← habs]; exact_mod_cast hle
  calc Real.sqrt (Ideal.absNorm 𝔪) ≤ Real.sqrt ((∏ τ, ‖tauE D τ (u : D.host.E)‖) ^ 2) := Real.sqrt_le_sqrt hle'
    _ = ∏ τ, ‖tauE D τ (u : D.host.E)‖ := Real.sqrt_sq (Finset.prod_nonneg fun τ _ => norm_nonneg _)

end GlobalTheory.CMNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtAbsNormLeProdNormCmTypeEmbeddingsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_absNorm_le_prod_norm_cmTypeEmbeddings : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (u : 𝓞 D.host.E), u ∈ 𝔪 → u ≠ 0 → Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ τ, ‖tauE D τ (u : D.host.E)‖ := by
  first | exact @GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE | exact GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE | (intros; apply GlobalTheory.CMNorm.sqrt_absNorm_le_prod_tauE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqUnitaryEmbeddingOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqUnitaryEmbeddingOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

theorem norm_sq_unitaryEmbedding_add : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (x : GA D Y) (τ : D.what₂.Tau) (y : Fin Y.rank → D.host.E) (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) ^ 2 = nrm θ A x τ y ^ 2 + ‖tauE D τ u‖ ^ 2 := by
  intro D θ hθ Y V d A B hAd x τ y u
  let φ : AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ :=
    (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hinc : ∀ e, φ (incA D e) = tauE D τ e := by
    intro e
    have := (hθ τ).1 e
    simpa [φ, incA, inclR] using this
  have hcmp : ∀ {W : HSp D} (g : GA D W), cmp θ τ g = (matHom W g).1.map φ := by
    intro W g; rfl
  have hinv : (stabilizerEmbedding d x)⁻¹ = stabilizerEmbedding d x⁻¹ :=
    (map_inv (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)) x).symm
  set P := (frameMat V Y d.ι).map (tauE D τ) with hP
  set Q := (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (tauE D τ) with hQ
  have key : cmp θ τ (stabilizerEmbedding d x)⁻¹ = GlobalTheory.UnitaryEmbeddingProperties.ex P Q (cmp θ τ x⁻¹) := by
    rw [hinv, hcmp, hcmp, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula, GlobalTheory.UnitaryEmbeddingProperties.ex_map, Matrix.map_map, Matrix.map_map]
    have hf : (⇑φ ∘ ⇑(incA D)) = ⇑(tauE D τ) := funext hinc
    rw [hf]
  have hQP : Q * P = 1 := GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map (tauE D τ) d
  have hQz0 : GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ zv d = 0 := by
    have hp := d.perp
    have h0 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V Y d.ι) * V.gram) *ᵥ zv d = 0 := by
      funext i
      have := congr_fun (congr_fun hp i) 0
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, zv] using this
    rw [GlobalTheory.UnitaryEmbeddingProperties.qM, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have hQz : Q *ᵥ (fun i => tauE D τ (zv d i)) = 0 := by
    funext i
    have := congr_fun hQz0 i
    rw [hQ]
    change ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map (tauE D τ) *ᵥ (⇑(tauE D τ) ∘ zv d)) i = 0
    rw [← RingHom.map_mulVec, this]
    exact map_zero _
  have hvec : (fun i => tauE D τ ((frameMat V Y d.ι *ᵥ y + u • zv d) i)) =
      P *ᵥ (fun i => tauE D τ (y i)) + tauE D τ u • fun i => tauE D τ (zv d i) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hP, RingHom.map_mulVec]
    rfl
  have hex : ∀ (h : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (w : Fin Y.rank → ℂ) (a : ℂ),
      GlobalTheory.UnitaryEmbeddingProperties.ex P Q h *ᵥ (P *ᵥ w + a • fun i => tauE D τ (zv d i)) =
        P *ᵥ (h *ᵥ w) + a • fun i => tauE D τ (zv d i) := by
    intro h w a
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, GlobalTheory.UnitaryEmbeddingProperties.ex_mul_P P Q hQP,
      ← Matrix.mulVec_mulVec]
    congr 2
    rw [GlobalTheory.UnitaryEmbeddingProperties.ex, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hQz,
      Matrix.mulVec_zero, add_zero]
  unfold nrm
  rw [key, hvec, hex]
  exact hAd τ _ _

end GlobalTheory.SepPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqUnitaryEmbeddingOrthogonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_unitaryEmbedding_orthogonal : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (x : GA D Y) (τ : D.what₂.Tau) (y : Fin Y.rank → D.host.E) (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) ^ 2 = nrm θ A x τ y ^ 2 + ‖tauE D τ u‖ ^ 2 := by
  first | exact @GlobalTheory.SepPer.norm_sq_unitaryEmbedding_add | exact GlobalTheory.SepPer.norm_sq_unitaryEmbedding_add | (intros; apply GlobalTheory.SepPer.norm_sq_unitaryEmbedding_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeNormRationalTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeNormRationalTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.MajDom

theorem re_form_le {n : ℕ} (G fr : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool)
    (h : frᴴ * Formalism.REAL.Jm ε * fr = G) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (G *ᵥ v)).re ≤ ∑ i, ‖(fr *ᵥ v) i‖ ^ 2 := by
  subst h
  have e : star v ⬝ᵥ ((frᴴ * Formalism.REAL.Jm ε * fr) *ᵥ v) =
      star (fr *ᵥ v) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (fr *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have hd : ∀ w : Fin n → ℂ, Formalism.REAL.Jm ε *ᵥ w = fun i => (if ε i = true then (1 : ℂ) else -1) * w i := by
    intro w; funext i; exact Matrix.mulVec_diagonal _ _ _
  rw [e, hd, dotProduct, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hw : star (fr *ᵥ v) i * ((if ε i = true then (1 : ℂ) else -1) * (fr *ᵥ v) i) =
      (if ε i = true then (1 : ℂ) else -1) * ((‖(fr *ᵥ v) i‖ : ℂ) ^ 2) := by
    rw [← Complex.conj_mul', Pi.star_apply, Complex.star_def]
    ring
  rw [hw]
  split_ifs
  · simp only [one_mul]
    norm_cast
  · have : (-((‖(fr *ᵥ v) i‖ : ℂ) ^ 2)).re = -(‖(fr *ᵥ v) i‖ ^ 2) := by norm_cast
    rw [neg_one_mul, this]
    nlinarith [sq_nonneg ‖(fr *ᵥ v) i‖]

theorem form_isom {n : ℕ} (G P : Matrix (Fin n) (Fin n) ℂ) (hP : Pᴴ * G * P = G) (u : Fin n → ℂ) :
    star (P *ᵥ u) ⬝ᵥ (G *ᵥ (P *ᵥ u)) = star u ⬝ᵥ (G *ᵥ u) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP]

end GlobalTheory.SepPer.MajDom

namespace GlobalTheory.SepPer.MajDom

variable {D : D7}

theorem tauE_sig (τ : D.what₂.Tau) (a : D.host.E) :
    tauE D τ (D.sp.cm.sig a) = starRingEnd ℂ (tauE D τ a) :=
  D.sp.cm.cmUnram.2.1 _ a

theorem cmp_mulVec (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (γ : GA D V) (z₀ z : Fin V.rank → D.host.E)
    (h : mt V γ *ᵥ ratV z₀ = ratV z) (τ : D.what₂.Tau) :
    cmp θ τ γ *ᵥ (fun i => tauE D τ (z₀ i)) = fun i => tauE D τ (z i) := by
  let φ : AE D →+* ℂ := (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hφ : ∀ e : D.host.E, φ (incA D e) = tauE D τ e := by
    intro e
    show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ e)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    exact (hθ τ).1 e
  have hc : cmp θ τ γ = (mt V γ).map φ := rfl
  have e1 : (⇑φ ∘ ratV z₀) = fun j => tauE D τ (z₀ j) := funext fun j => hφ (z₀ j)
  funext i
  have := congrArg (fun w => φ (w i)) h
  simp only [RingHom.map_mulVec] at this
  rw [e1] at this
  rw [hc, this]
  exact hφ (z i)

theorem form_zv {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau) :
    star (fun i => tauE D τ (zv d i)) ⬝ᵥ (gramAt D V τ *ᵥ fun i => tauE D τ (zv d i)) = 1 := by
  have hg := congrArg (fun M => tauE D τ (M 0 0)) d.gram
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [antiDiagonalSignGramMatrix, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    tauE_sig] at hg
  simp only [dotProduct, Matrix.mulVec, gramAt, Matrix.map_apply, Pi.star_apply, Complex.star_def, Finset.mul_sum, zv]
  refine Eq.trans ?_ (hg.trans (by simp))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc]
  congr 1
  exact (tauE_sig τ _).symm

end GlobalTheory.SepPer.MajDom

namespace GlobalTheory.SepPer.MajDom

theorem one_le_nrm : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (B : Fr V) (x : GA D Y)
    (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z →
    ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  intro D θ hθ Y V d B x γ z _ hmt τ
  set G := gramAt D V τ
  set u₀ : Fin V.rank → ℂ := fun i => tauE D τ (zv d i) with hu₀
  set P := cmp θ τ (stabilizerEmbedding d x)⁻¹ * cmp θ τ γ with hP
  have hv : cmp θ τ (stabilizerEmbedding d x)⁻¹ *ᵥ (fun i => tauE D τ (z i)) = P *ᵥ u₀ := by
    rw [← cmp_mulVec θ hθ γ (zv d) z hmt τ, Matrix.mulVec_mulVec]
  have hPG : Pᴴ * G * P = G := by
    have h1 := GlobalTheory.Doubling.infMat_isometry hθ τ (stabilizerEmbedding d x)⁻¹
    have h2 := GlobalTheory.Doubling.infMat_isometry hθ τ γ
    calc Pᴴ * G * P = (cmp θ τ γ)ᴴ * ((cmp θ τ (stabilizerEmbedding d x)⁻¹)ᴴ * G * cmp θ τ (stabilizerEmbedding d x)⁻¹) * cmp θ τ γ := by
          rw [hP, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]
  have hform : star (P *ᵥ u₀) ⬝ᵥ (G *ᵥ (P *ᵥ u₀)) = 1 := by
    rw [form_isom G P hPG u₀]
    exact form_zv d τ
  have key := re_form_le G (B.fr τ) (B.ε τ) (B.fr_gram τ) (P *ᵥ u₀)
  rw [hform, Complex.one_re] at key
  unfold nrm eu
  rw [hv]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt key

end GlobalTheory.SepPer.MajDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeNormRationalTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_norm_rational_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (B : Fr V) (x : GA D Y) (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z → ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  first | exact @GlobalTheory.SepPer.MajDom.one_le_nrm | exact GlobalTheory.SepPer.MajDom.one_le_nrm | (intros; apply GlobalTheory.SepPer.MajDom.one_le_nrm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LongElementEmbeddingNorm
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.LongSum

theorem long_sum : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (Λ : Lat Y) (x : GA D Y) (s : ℝ), IsSelfDualC Y Λ → 0 ≤ s → s ≤ 1 → Long θ A Λ x s → Long θ B (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) s ∧ (∀ τ, nrm θ B (stabilizerEmbedding d x) τ (zv d) = 1) ∧ ∀ (γ : GA D V) z, γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z → ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  intro D θ hθ Y V d A B hAd Λ x s _ hs0 hs1 hL
  have hzero : ∀ τ, nrm θ A x τ 0 = 0 := fun τ => by
    have e : (fun i => tauE D τ ((0 : Fin Y.rank → D.host.E) i)) = 0 := by funext i; simp
    unfold nrm
    rw [e, mulVec_zero, mulVec_zero]
    simp [eu]
  have hz : ∀ τ (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (u • zv d) = ‖tauE D τ u‖ := fun τ u => by
    have h := GlobalTheory.T.norm_sq_unitaryEmbedding_orthogonal D θ hθ Y V d A B hAd x τ 0 u
    rw [mulVec_zero, zero_add, hzero] at h
    have h2 : nrm θ B (stabilizerEmbedding d x) τ (u • zv d) ^ 2 = ‖tauE D τ u‖ ^ 2 := by rw [h]; ring
    have h0 : 0 ≤ nrm θ B (stabilizerEmbedding d x) τ (u • zv d) := Real.sqrt_nonneg _
    exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).1 h2
  have hge : ∀ τ y (u : D.host.E), nrm θ A x τ y ≤ nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) := fun τ y u => by
    have h := GlobalTheory.T.norm_sq_unitaryEmbedding_orthogonal D θ hθ Y V d A B hAd x τ y u
    have h0 : 0 ≤ nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) := Real.sqrt_nonneg _
    have h1 : 0 ≤ nrm θ A x τ y := Real.sqrt_nonneg _
    nlinarith [sq_nonneg ‖tauE D τ u‖]
  refine ⟨?_, fun τ => ?_, fun γ z hγ hz' τ => GlobalTheory.T.one_le_norm_rational_translate D θ hθ Y V d B x γ z hγ hz' τ⟩
  · intro 𝔪 h𝔪 w hw hw0
    obtain ⟨y, hy, u, hu, rfl⟩ := GlobalTheory.T.exists_decomp_smul_lattice_embedding D Y V d Λ x 𝔪 w hw
    by_cases hy0 : y = 0
    · subst hy0
      rw [mulVec_zero, zero_add] at hw0 ⊢
      have hu0 : u ≠ 0 := by
        rintro rfl; exact hw0 (by simp)
      have e : ∏ τ, nrm θ B (stabilizerEmbedding d x) τ ((u : D.host.E) • zv d) = ∏ τ, ‖tauE D τ (u : D.host.E)‖ :=
        Finset.prod_congr rfl fun τ _ => hz τ _
      rw [e]
      refine le_trans ?_ (GlobalTheory.T.sqrt_absNorm_le_prod_norm_cmTypeEmbeddings D 𝔪 u hu hu0)
      have h1 : s ^ Fintype.card D.what₂.Tau ≤ 1 := pow_le_one₀ hs0 hs1
      have h2 : 0 ≤ Real.sqrt (Ideal.absNorm 𝔪) := Real.sqrt_nonneg _
      nlinarith
    · refine le_trans (hL 𝔪 h𝔪 y hy hy0) ?_
      exact Finset.prod_le_prod₀ (fun τ _ => Real.sqrt_nonneg _) fun τ _ => hge τ y u
  · have h := hz τ 1
    rw [one_smul, map_one, norm_one] at h
    exact h

end GlobalTheory.SepPer.LongSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LongElementEmbeddingNormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.long_element_embedding_norm : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (Λ : Lat Y) (x : GA D Y) (s : ℝ), IsSelfDualC Y Λ → 0 ≤ s → s ≤ 1 → Long θ A Λ x s → Long θ B (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) s ∧ (∀ τ, nrm θ B (stabilizerEmbedding d x) τ (zv d) = 1) ∧ ∀ (γ : GA D V) z, γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z → ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  first | exact @GlobalTheory.SepPer.LongSum.long_sum | exact GlobalTheory.SepPer.LongSum.long_sum | (intros; apply GlobalTheory.SepPer.LongSum.long_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenCongruenceEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenCongruenceEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitaryEmbeddingOpenLevel

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem col_mem (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (p : Fin c) :
    (fun i => d.a i p) ∈ d.lat Λ (fun _ => 1) := by
  refine ⟨0, Λ.zero_mem, Pi.single p 1, fun q => ?_, ?_⟩
  · by_cases h : q = p
    · subst h; rw [Pi.single_eq_same]; exact FractionalIdeal.one_mem_one _
    · rw [Pi.single_eq_of_ne h]; exact FractionalIdeal.zero_mem _
  · funext i; simp [mulVec_single]

theorem map_mem (d : HermitianOrthogonalExtensionData A B c ε) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {y : Fin A.rank → D.host.E}
    (hy : y ∈ Λ) : frameMat B A d.ι *ᵥ y ∈ d.lat Λ (fun _ => 1) :=
  ⟨y, hy, 0, fun _ => FractionalIdeal.zero_mem _, by simp⟩

theorem lat_eq (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) :
    d.lat Λ (fun _ => 1) = Λ.map ((frameMat B A d.ι).mulVecLin.restrictScalars (𝓞 D.host.E)) ⊔
      Submodule.span (𝓞 D.host.E) (Set.range fun p i => d.a i p) := by
  refine le_antisymm ?_ (sup_le ?_ (Submodule.span_le.2 ?_))
  · rintro _ ⟨y, hy, u, hu, rfl⟩
    refine Submodule.add_mem_sup ⟨y, hy, rfl⟩ ?_
    choose r hr using fun p => (FractionalIdeal.mem_one_iff _).1 (hu p)
    have e : d.a *ᵥ u = ∑ p, r p • fun i => d.a i p := by
      funext i
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, ← hr, Algebra.smul_def, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩; exact map_mem d hy
  · rintro _ ⟨p, rfl⟩; exact col_mem d Λ p

theorem isLattice_lat (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) : Submodule.IsFullLattice D.host.E (d.lat Λ (fun _ => 1)) := by
  have hfg : Submodule.IsLattice D.host.E (d.lat Λ (fun _ => 1)) := by
    apply Submodule.IsLattice.of_fg D.host.E
    rw [lat_eq]
    exact (hΛ.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  let S := Submodule.span D.host.E (d.lat Λ (fun _ => 1) : Set (Fin B.rank → D.host.E))
  have hmap : ∀ y : Fin A.rank → D.host.E, frameMat B A d.ι *ᵥ y ∈ S := by
    intro y
    have hy : y ∈ Submodule.span D.host.E (Λ : Set _) := by rw [hΛ.span_eq_top]; trivial
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (map_mem d hy)
    | zero => simp
    | add x y _ _ hx hy => simpa only [mulVec_add] using S.add_mem hx hy
    | smul a x _ hx => simpa only [mulVec_smul] using S.smul_mem a hx
  have hcols : ∀ u : Fin c → D.host.E, d.a *ᵥ u ∈ S := by
    intro u
    have e : d.a *ᵥ u = ∑ p, u p • fun i => d.a i p := by
      funext i
      simp [mulVec, dotProduct, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun p _ => S.smul_mem _ (Submodule.subset_span (col_mem d Λ p))
  have : Submodule.IsLattice D.host.E (d.lat Λ (fun _ => 1)) := hfg
  refine ⟨?_⟩
  apply Submodule.eq_top_iff'.2
  intro x
  have h := congrArg (fun M => M *ᵥ x) (GlobalTheory.UnitaryEmbeddingGroup.decomp d hε)
  simp only [add_mulVec, ← mulVec_mulVec, one_mulVec] at h
  rw [← h]
  exact S.add_mem (hmap _) (hcols _)

end GlobalTheory.UnitaryEmbeddingOpenLevel


open GlobalTheory.UnitaryEmbeddingOpenLevel in
theorem GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → IsOpen {g : GA D V | Lev.finE V g ∈ congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪} := by
  intro D Y V d Λ 𝔪 hΛ h𝔪
  exact (congLev_open_compact V (isLattice_lat d one_ne_zero
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice Y Λ hΛ)) h𝔪).1

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenCongruenceEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_congruence_embedding : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → IsOpen {g : GA D V | Lev.finE V g ∈ congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪} := by
  first | exact @GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen | exact GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen | (intros; apply GlobalTheory.UnitaryEmbeddingOpenLevel.levOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumLongVectorsDecayWeightLe
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumLongVectorsDecayWeightLe
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

variable {D : D7}

def compVec (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) :
    (Fin V.rank → D.host.E) →+ (D.what₂.Tau → EuclideanSpace ℂ (Fin V.rank)) where
  toFun w τ := WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (w i)))
  map_zero' := by
    funext τ
    have h : (fun i => tauE D τ ((0 : Fin V.rank → D.host.E) i)) = 0 := by
      funext i; simp
    show WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ ((0 : Fin V.rank → D.host.E) i))) = 0
    rw [h, Matrix.mulVec_zero, Matrix.mulVec_zero]
    rfl
  map_add' x y := by
    funext τ
    have h : (fun i => tauE D τ ((x + y) i)) = (fun i => tauE D τ (x i)) + fun i => tauE D τ (y i) := by
      funext i; simp
    show WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ ((x + y) i))) =
      WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (x i))) +
        WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (y i)))
    rw [h, Matrix.mulVec_add, Matrix.mulVec_add, WithLp.toLp_add]

theorem norm_compVec (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (w : Fin V.rank → D.host.E) (τ : D.what₂.Tau) :
    ‖compVec θ V B g w τ‖ = nrm θ B g τ w := by
  rw [EuclideanSpace.norm_eq]; rfl

theorem latSum_le : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (L : Lat V) (R : ℝ), 1 ≤ V.rank → 1 < R → (∀ w ∈ L, w ≠ 0 → R ≤ ∏ τ, nrm θ B g τ w) → ∀ s : Finset (Fin V.rank → D.host.E), (∀ w ∈ s, w ∈ L ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + nrm θ B g τ w) / 3) ^ (2 * V.rank + 5))⁻¹ ≤ Real.exp ((6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) / R := by
  intro D θ V B g L R hn hR hL s hs
  classical
  have hnorm : ∀ w τ, ‖compVec θ V B g w τ‖ = nrm θ B g τ w := norm_compVec θ V B g
  by_cases hι : IsEmpty D.what₂.Tau
  · have hs0 : s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      have h1 := hL w (hs w hw).1 (hs w hw).2
      rw [Finset.univ_eq_empty, Finset.prod_empty] at h1
      linarith
    subst hs0
    rw [Finset.sum_empty]
    exact div_nonneg (Real.exp_pos _).le (by linarith)
  · haveI : Nonempty D.what₂.Tau := not_isEmpty_iff.mp hι
    have hzero : ∀ w, compVec θ V B g w = 0 → ∏ τ, nrm θ B g τ w = 0 := by
      intro w h0
      refine Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _)) ?_
      rw [← hnorm, h0, Pi.zero_apply, norm_zero]
    have hinj : Set.InjOn (compVec θ V B g) (s : Set _) := by
      intro x hx y hy hxy
      by_contra hne
      have hm : x - y ∈ L := L.sub_mem (hs x hx).1 (hs y hy).1
      have h1 := hL _ hm (sub_ne_zero.mpr hne)
      have hz : compVec θ V B g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hzero _ hz] at h1
      linarith
    have key := GlobalTheory.T.lattice_sum_prod_norm_le_of_prod_norm_lower_bound D.what₂.Tau V.rank (L.toAddSubgroup.map (compVec θ V B g)) R hn hR ?_
      (s.image (compVec θ V B g)) ?_
    · rw [Finset.sum_image hinj] at key
      simpa only [hnorm] using key
    · intro v hv hv0
      obtain ⟨w, hwL, rfl⟩ := AddSubgroup.mem_map.mp hv
      have hwL' : w ∈ L := hwL
      have hw0 : w ≠ 0 := by rintro rfl; exact hv0 (map_zero _)
      simpa only [hnorm] using hL w hwL' hw0
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      refine ⟨AddSubgroup.mem_map_of_mem _ (hs w hw).1, ?_⟩
      intro h0
      have h1 := hL w (hs w hw).1 (hs w hw).2
      rw [hzero w h0] at h1
      linarith

end GlobalTheory.SepPer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumLongVectorsDecayWeightLeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeSum_longVectors_decayWeight_le : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (L : Lat V) (R : ℝ), 1 ≤ V.rank → 1 < R → (∀ w ∈ L, w ≠ 0 → R ≤ ∏ τ, nrm θ B g τ w) → ∀ s : Finset (Fin V.rank → D.host.E), (∀ w ∈ s, w ∈ L ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + nrm θ B g τ w) / 3) ^ (2 * V.rank + 5))⁻¹ ≤ Real.exp ((6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) / R := by
  first | exact @GlobalTheory.SepPer.latSum_le | exact GlobalTheory.SepPer.latSum_le | (intros; apply GlobalTheory.SepPer.latSum_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalImageRationalPointMulVec
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalImageRationalPointMulVec
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

theorem ratPt_mulVec_ratV : ∀ (D : D7) (V : HSp D) (γ : GA D V), γ ∈ GQ V → ∀ y : Fin V.rank → D.host.E,
    ∃ z : Fin V.rank → D.host.E, mt V γ *ᵥ ratV y = ratV z := by
  intro D V γ hγ y
  obtain ⟨e, he⟩ := GlobalTheory.Ker.Grp.exists_equiv V
  have h : mt V γ = ((e.symm ⟨γ, hγ⟩).1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) := by
    have := he (e.symm ⟨γ, hγ⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  refine ⟨((e.symm ⟨γ, hγ⟩).1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ y, ?_⟩
  rw [h]
  funext i
  simp only [ratV]
  exact (RingHom.map_mulVec (incA D) _ y i).symm

end GlobalTheory.SepPer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalImageRationalPointMulVecStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_image_rationalPoint_mulVec : ∀ (D : D7) (V : HSp D) (γ : GA D V), γ ∈ GQ V → ∀ y : Fin V.rank → D.host.E, ∃ z : Fin V.rank → D.host.E, mt V γ *ᵥ ratV y = ratV z := by
  first | exact @GlobalTheory.SepPer.ratPt_mulVec_ratV | exact GlobalTheory.SepPer.ratPt_mulVec_ratV | (intros; apply GlobalTheory.SepPer.ratPt_mulVec_ratV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesIdentityTermDominates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdDom

theorem eu_sub_le {n : ℕ} (u u' : Fin n → ℂ) : eu (u - u') ≤ eu u + eu u' := by
  have h : ∀ y : Fin n → ℂ, eu y = ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))‖ := fun y => by
    rw [EuclideanSpace.norm_eq]; rfl
  rw [h, h, h, WithLp.toLp_sub]; exact norm_sub_le _ _

theorem nrm_sub_le {D : D7} (θ : InfFam D) {V : HSp D} (B : Fr V) (g : GA D V) (τ : D.what₂.Tau)
    (y y' : Fin V.rank → D.host.E) : nrm θ B g τ (y - y') ≤ nrm θ B g τ y + nrm θ B g τ y' := by
  unfold nrm
  have e : (fun i => tauE D τ ((y - y') i)) = (fun i => tauE D τ (y i)) - fun i => tauE D τ (y' i) := by
    funext i; simp
  rw [e, mulVec_sub, mulVec_sub]; exact eu_sub_le _ _

theorem nrm_nonneg' {D : D7} (θ : InfFam D) {V : HSp D} (B : Fr V) (g : GA D V) (τ : D.what₂.Tau)
    (y : Fin V.rank → D.host.E) : 0 ≤ nrm θ B g τ y := Real.sqrt_nonneg _


set_option maxHeartbeats 1600000 in
theorem identity_dominates : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Base d → ∀ (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → ∀ (v : GlobalTheory.Unf.Vol Y) (φ : GA D Y → ℂ) (c : ℂ) (b s : ℝ) (x : GA D Y), GlobalTheory.Unf.IsContAut Y φ → (∀ h, ‖φ h‖ ≤ b) → b / 2 < ‖φ x‖ → 0 ≤ s → s ≤ 1 → Long θ p.A Λ x s → p.AdelicAt θ d Q (d.lat Λ fun _ => 1) 𝔪 v.μ φ c → 2 * Real.exp (Q + (6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) ≤ s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → 1 < s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → ∫ h in v.𝓕, poin θ M (congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪) (p.v θ) (stabilizerEmbedding d x⁻¹) (p.v θ) (stabilizerEmbedding d h) * φ h ∂v.μ ≠ 0 := by
  intro D θ hθ Y V d S S' M₀ M p Q hbase Λ 𝔪 hΛ h𝔪 v φ c b s x hφ hbnd hx hs0 hs1 hlong had hR2 hR1
  classical
  obtain ⟨ι, hι, hιc, hιi, hιQ, -, -, hιr, -, -⟩ := GlobalTheory.T.exists_unitary_embedding_stabilizer D θ hθ Y V 1 1 one_ne_zero d
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := v.haar
  set K := congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪 with hK
  set f : GA D V → ℂ := fun g => coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * g) with hf
  have hcoef : Measurable (coef θ M K (p.v θ) (p.v θ)) := by
    have h1 := GlobalTheory.T.continuous_realPlacesMatrixCoefficientProduct D θ hθ V S M (p.v θ) (p.v θ)
    have h2 := GlobalTheory.T.isOpen_congruence_embedding D Y V d Λ 𝔪 hΛ h𝔪
    unfold coef
    exact Measurable.ite h2.measurableSet h1.measurable measurable_const
  have hfm : ∀ γ : GA D V, Measurable fun h => f (γ * ι h) := fun γ =>
    hcoef.comp (continuous_const.mul (continuous_const.mul hιc)).measurable
  have hcomap : (GQ V).comap ι = GQ Y := by ext h; simp [Subgroup.mem_comap, hιQ]
  have hfund : IsFundamentalDomain ((GQ V).comap ι) v.𝓕 v.μ := by rw [hcomap]; exact v.fund
  have hinv : ∀ γ ∈ (GQ V).comap ι, ∀ h, φ (γ * h) = φ h := fun γ hγ h =>
    hφ.1 γ (by rw [← hcomap]; exact hγ) h
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hbnd x)
  have hV1 : 1 ≤ V.rank := by have := d.rank; omega
  obtain ⟨hlongV, hz₀, hz1⟩ := GlobalTheory.T.long_element_embedding_norm D θ hθ Y V d p.A p.B hbase.adapted Λ x s hΛ hs0 hs1 hlong
  choose z hz using fun q : GQ V ⧸ ι.range.subgroupOf (GQ V) => GlobalTheory.T.exists_rational_image_rationalPoint_mulVec D V _ (q.out).2 (zv d)
  have hterm : ∀ q : GQ V ⧸ ι.range.subgroupOf (GQ V),
      Integrable (fun h => f ((q.out : GA D V) * ι h)) v.μ ∧
      (∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ) * (∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ (z q)) ^ (2 * V.rank + 5) ≤
        Real.exp Q * ‖c‖ ∧
      (z q - zv d ∉ 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) → ∀ h, f ((q.out : GA D V) * ι h) = 0) := by
    intro q
    have := had.term x _ (z q) (q.out).2 (hz q)
    simpa only [hf, hι, mul_assoc] using this
  have hmtm : ∀ a a' : GA D V, mt V (a * a') = mt V a * mt V a' := fun a a' => by simp [Formalism.L2.Theta.mt]
  have hmt1 : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  have hfix : ∀ g : GA D V, mt V g *ᵥ ratV (zv d) = ratV (zv d) → g ∈ ι.range := by
    intro g hg
    rw [hιr]
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have := congrFun hg i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, ratV, zv] using this
  have hcos : ∀ q q' : GQ V ⧸ ι.range.subgroupOf (GQ V),
      ((q.out : GA D V))⁻¹ * (q'.out : GA D V) ∈ ι.range → q = q' := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using h
  have hinj : ∀ q q', z q = z q' → q = q' := by
    intro q q' h
    refine hcos q q' (hfix _ ?_)
    rw [hmtm, ← Matrix.mulVec_mulVec, hz q', ← h, ← hz q, Matrix.mulVec_mulVec, ← hmtm, inv_mul_cancel, hmt1,
      Matrix.one_mulVec]
  set q₁ : GQ V ⧸ ι.range.subgroupOf (GQ V) := ((1 : GQ V) : GQ V ⧸ ι.range.subgroupOf (GQ V)) with hq₁
  have hq1 : ∀ q, z q = zv d → q = q₁ := by
    intro q h
    rw [← QuotientGroup.out_eq' q, hq₁, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hfix _ (by rw [hz, h])

  have hTle : ∀ q : GQ V ⧸ ι.range.subgroupOf (GQ V), ‖∫ h, f ((q.out : GA D V) * ι h) * φ h ∂v.μ‖ ≤
      b * ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ := by
    intro q
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun h => norm_nonneg _)
      ((hterm q).1.norm.const_mul b) (Filter.Eventually.of_forall fun h => ?_)
    dsimp only
    rw [norm_mul, mul_comm b]
    exact mul_le_mul_of_nonneg_left (hbnd h) (norm_nonneg _)
  have hLle : ∀ q : GQ V ⧸ ι.range.subgroupOf (GQ V), ∫⁻ h, ‖f ((q.out : GA D V) * ι h) * φ h‖ₑ ∂v.μ ≤
      ENNReal.ofReal (b * ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ) := by
    intro q
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal ((hterm q).1.norm.const_mul b)
      (Filter.Eventually.of_forall fun h => mul_nonneg hb0 (norm_nonneg _))]
    refine lintegral_mono fun h => ?_
    rw [← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, mul_comm b]
    exact mul_le_mul_of_nonneg_left (hbnd h) (norm_nonneg _)
  set β : (GQ V ⧸ ι.range.subgroupOf (GQ V)) → ℝ := fun q => b * ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ with hβ
  have hβ0 : ∀ q, 0 ≤ β q := fun q => mul_nonneg hb0 (integral_nonneg fun _ => norm_nonneg _)
  have hβle : ∀ q, β q ≤ b * (Real.exp Q * ‖c‖) := by
    intro q
    refine mul_le_mul_of_nonneg_left ?_ hb0
    have hP : 1 ≤ ∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ (z q) := by
      simpa using Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
        (fun τ _ => hz1 _ (z q) (q.out).2 (hz q) τ)
    exact (le_mul_of_one_le_right (integral_nonneg fun _ => norm_nonneg _) (one_le_pow₀ hP)).trans (hterm q).2.1

  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) := ⟨_, rfl⟩
  obtain ⟨Kx, hKx⟩ : ∃ Kx : ℝ, Kx = (6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau := ⟨_, rfl⟩
  obtain ⟨Bt, hBt⟩ : ∃ Bt : ℝ, Bt = b * (Real.exp Q * ‖c‖) * (Real.exp Kx / R) := ⟨_, rfl⟩
  rw [← hRdef] at hR1 hR2
  rw [← hKx] at hR2
  have htail : ∀ t : Finset (GQ V ⧸ ι.range.subgroupOf (GQ V)), ∑ q ∈ t.erase q₁, β q ≤ Bt := by
    intro t
    obtain ⟨L, hL⟩ : ∃ L : Lat V, L = 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : (GQ V ⧸ ι.range.subgroupOf (GQ V)) → (Fin V.rank → D.host.E), w = fun q => z q - zv d :=
      ⟨_, rfl⟩
    have hwq : ∀ q, w q = z q - zv d := fun q => by rw [hw]
    obtain ⟨t', ht'⟩ : ∃ t' : Finset (GQ V ⧸ ι.range.subgroupOf (GQ V)), t' = (t.erase q₁).filter (fun q => w q ∈ L) :=
      ⟨_, rfl⟩
    have h1 : ∑ q ∈ t.erase q₁, β q = ∑ q ∈ t', β q := by
      rw [ht']
      refine (Finset.sum_filter_of_ne fun q _ hq => ?_).symm
      by_contra hL'
      apply hq
      have h0 := (hterm q).2.2 (fun h => hL' (by rw [hwq, hL]; exact h))
      simp [hβ, h0]
    have h2 : ∀ q ∈ t', β q ≤ b * (Real.exp Q * ‖c‖) *
        ∏ τ, (((1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3) ^ (2 * V.rank + 5))⁻¹ := by
      intro q _
      have hτ : ∀ τ, (1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3 ≤ nrm θ p.B (stabilizerEmbedding d x) τ (z q) := by
        intro τ
        have a1 := nrm_sub_le θ p.B (stabilizerEmbedding d x) τ (z q) (zv d)
        have a2 := hz1 _ (z q) (q.out).2 (hz q) τ
        rw [hz₀ τ] at a1
        rw [hwq]
        linarith
      have hP' : 0 < ∏ τ, (1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3 :=
        Finset.prod_pos fun τ _ => by have := nrm_nonneg' θ p.B (stabilizerEmbedding d x) τ (w q); positivity
      have hPP : ∏ τ, (1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3 ≤ ∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ (z q) :=
        Finset.prod_le_prod₀ (fun τ _ => by have := nrm_nonneg' θ p.B (stabilizerEmbedding d x) τ (w q); positivity) fun τ _ => hτ τ
      have ha := (hterm q).2.1
      have ha0 : 0 ≤ ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ := integral_nonneg fun _ => norm_nonneg _
      rw [Finset.prod_inv_distrib, Finset.prod_pow, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hb0
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hP' _)]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP'.le hPP _) ha0).trans ha
    have hw_inj : Set.InjOn w t' := by
      intro q _ q' _ h
      exact hinj q q' (sub_left_inj.1 (by rwa [hwq, hwq] at h))
    have hws : ∀ y ∈ t'.image w, y ∈ L ∧ y ≠ 0 := by
      intro y hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      rw [ht', Finset.mem_filter, Finset.mem_erase] at hq
      exact ⟨hq.2, fun h0 => hq.1.1 (hq1 q (sub_eq_zero.1 (by rwa [hwq] at h0)))⟩
    have hsum := GlobalTheory.T.latticeSum_longVectors_decayWeight_le D θ V p.B (stabilizerEmbedding d x) L R hV1 hR1 (fun y hy hy0 => hRdef ▸ hlongV 𝔪 h𝔪 y (hL ▸ hy) hy0) (t'.image w) hws
    rw [← hKx] at hsum
    calc ∑ q ∈ t.erase q₁, β q = ∑ q ∈ t', β q := h1
      _ ≤ ∑ q ∈ t', b * (Real.exp Q * ‖c‖) * ∏ τ, (((1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3) ^ (2 * V.rank + 5))⁻¹ :=
        Finset.sum_le_sum h2
      _ = b * (Real.exp Q * ‖c‖) * ∑ y ∈ t'.image w, ∏ τ, (((1 + nrm θ p.B (stabilizerEmbedding d x) τ y) / 3) ^ (2 * V.rank + 5))⁻¹ := by
        rw [Finset.sum_image hw_inj, Finset.mul_sum]
      _ ≤ Bt := by rw [hBt]; exact mul_le_mul_of_nonneg_left hsum (by positivity)

  have hall : ∀ t : Finset (GQ V ⧸ ι.range.subgroupOf (GQ V)), ∑ q ∈ t, β q ≤ b * (Real.exp Q * ‖c‖) + Bt := by
    intro t
    calc ∑ q ∈ t, β q ≤ ∑ q ∈ insert q₁ t, β q :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) fun q _ _ => hβ0 q
      _ = β q₁ + ∑ q ∈ (insert q₁ t).erase q₁, β q := (Finset.add_sum_erase _ _ (Finset.mem_insert_self _ _)).symm
      _ ≤ _ := add_le_add (hβle q₁) (htail _)
  have hβs : Summable β := summable_of_sum_le hβ0 hall
  have hfin : (∑' q : GQ V ⧸ ι.range.subgroupOf (GQ V), ∫⁻ h, ‖f ((q.out : GQ V) * ι h) * φ h‖ₑ ∂v.μ) ≠ ⊤ := by
    have h1 : (∑' q : GQ V ⧸ ι.range.subgroupOf (GQ V), ∫⁻ h, ‖f ((q.out : GQ V) * ι h) * φ h‖ₑ ∂v.μ) ≤
        ∑' q, ENNReal.ofReal (β q) := ENNReal.tsum_le_tsum hLle
    have h2 : (∑' q, ENNReal.ofReal (β q)) = ENNReal.ofReal (∑' q, β q) := (ENNReal.ofReal_tsum_of_nonneg hβ0 hβs).symm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h1.trans h2.le)
  have hU := GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup (GA D V) (GA D Y) v.μ ι hιi (GQ V) v.𝓕 hfund f φ hfm hφ.2.measurable hinv hfin
  have htarget : (∫ h in v.𝓕, poin θ M K (p.v θ) (stabilizerEmbedding d x⁻¹) (p.v θ) (stabilizerEmbedding d h) * φ h ∂v.μ) =
      ∫ h in v.𝓕, (∑' γ : GQ V, f (γ * ι h)) * φ h ∂v.μ := by
    congr 1; funext h; simp only [poin, hf, hι, mul_assoc]
  have h1r : ((q₁.out : GQ V) : GA D V) ∈ ι.range := by
    have := QuotientGroup.out_eq' q₁
    rw [hq₁, QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
    simpa using this
  obtain ⟨h₀, hh₀⟩ := h1r
  have hh₀Q : h₀ ∈ GQ Y := (hιQ h₀).1 (hh₀ ▸ (q₁.out).2)
  have hT1 : ∫ h, f ((q₁.out : GA D V) * ι h) * φ h ∂v.μ = c * φ x := by
    rw [← hh₀, ← had.one x]
    have e : (fun h => f (ι h₀ * ι h) * φ h) = fun h =>
        (fun h' => coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h') * φ h') (h₀ * h) := by
      funext h
      show f (ι h₀ * ι h) * φ h = coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d (h₀ * h)) * φ (h₀ * h)
      rw [← map_mul, hφ.1 h₀ hh₀Q h]
      simp only [hf, hι]
    rw [e]
    exact integral_mul_left_eq_self (μ := v.μ)
      (fun h' => coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h') * φ h') h₀
  rw [htarget]
  intro hI0
  have hH' := hU.2.update q₁ 0
  have hβ's : Summable (Function.update β q₁ 0) := hβs.update q₁ 0
  have hnorm := hH'.norm_le_of_bounded hβ's.hasSum (fun q => by
    by_cases hq : q = q₁
    · subst hq; simp
    · simp only [Function.update_apply, hq, if_false]; exact hTle q)
  have hts : ∑' q, Function.update β q₁ 0 q ≤ Bt := by
    refine hβ's.tsum_le_of_sum_le fun t => ?_
    rw [← Finset.sum_erase t (a := q₁) (by simp)]
    calc _ = ∑ q ∈ t.erase q₁, β q := Finset.sum_congr rfl fun q hq => by
            simp [Function.update_apply, Finset.ne_of_mem_erase hq]
      _ ≤ Bt := htail t
  rw [hI0, add_zero, zero_sub, norm_neg, hT1, norm_mul] at hnorm
  have hRpos : 0 < R := by linarith
  have hq' : Real.exp Q * Real.exp Kx / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hRpos, ← Real.exp_add]; linarith
  have hBt : Bt ≤ b * ‖c‖ / 2 := by
    calc Bt = (b * ‖c‖) * (Real.exp Q * Real.exp Kx / R) := by rw [hBt]; ring
      _ ≤ (b * ‖c‖) * (1 / 2) := mul_le_mul_of_nonneg_left hq' (by positivity)
      _ = _ := by ring
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 had.ne
  have := mul_lt_mul_of_pos_left hx hc0
  nlinarith

end GlobalTheory.IdDom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesIdentityTermDominatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSeries_pairing_ne_zero_of_large_level : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Base d → ∀ (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → ∀ (v : GlobalTheory.Unf.Vol Y) (φ : GA D Y → ℂ) (c : ℂ) (b s : ℝ) (x : GA D Y), GlobalTheory.Unf.IsContAut Y φ → (∀ h, ‖φ h‖ ≤ b) → b / 2 < ‖φ x‖ → 0 ≤ s → s ≤ 1 → Long θ p.A Λ x s → p.AdelicAt θ d Q (d.lat Λ fun _ => 1) 𝔪 v.μ φ c → 2 * Real.exp (Q + (6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) ≤ s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → 1 < s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → ∫ h in v.𝓕, poin θ M (congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪) (p.v θ) (stabilizerEmbedding d x⁻¹) (p.v θ) (stabilizerEmbedding d h) * φ h ∂v.μ ≠ 0 := by
  first | exact @GlobalTheory.IdDom.identity_dominates | exact GlobalTheory.IdDom.identity_dominates | (intros; apply GlobalTheory.IdDom.identity_dominates <;> assumption)
end
