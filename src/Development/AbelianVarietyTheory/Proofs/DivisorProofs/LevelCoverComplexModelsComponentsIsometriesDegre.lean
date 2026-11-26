module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentIndexSumEqConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverPullbackReadingEqUnitConstPowMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCoverArithmeticGroupLeFiniteIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverComparisonScalarEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverComparisonScalarEqOne
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevScalar

open scoped Matrix

section Alg

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem isIntegral_eig_of_congr (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (M : ℕ) (hM : M ≠ 0) (A : Matrix (Fin r) (Fin r) E)
    (hA : ∀ x ∈ Λ, ∃ y ∈ Λ, A *ᵥ x - x = M • y) (τ : E →+* ℂ) (w : Fin r → ℂ) (hw : w ≠ 0) (lam : ℂ)
    (he : w ᵥ* A.map τ = lam • w) : IsIntegral ℤ ((lam - 1) / M) := by
  classical
  let φ : (Fin r → E) →+ ℂ :=
    { toFun := fun v => w ⬝ᵥ (τ ∘ v)
      map_zero' := by simp [dotProduct]
      map_add' := fun a b => by simp [dotProduct, mul_add, Finset.sum_add_distrib] }
  have hφ : ∀ v, φ v = w ⬝ᵥ (τ ∘ v) := fun _ => rfl
  have hφA : ∀ v, φ (A *ᵥ v) = lam * φ v := by
    intro v
    have : (τ ∘ (A *ᵥ v)) = A.map τ *ᵥ (τ ∘ v) := by
      funext i; exact RingHom.map_mulVec τ A v i
    rw [hφ, hφ, this, Matrix.dotProduct_mulVec, he, smul_dotProduct, smul_eq_mul]
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) _
  let ψ : Λ →ₗ[ℤ] ℂ := (φ.comp Λ.subtype.toAddMonoidHom).toIntLinearMap
  have hψ : ∀ x : Λ, ψ x = φ x := fun _ => rfl
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
  refine isIntegral_of_smul_mem_submodule (LinearMap.range ψ) ?_ ?_ _ ?_
  · intro h0
    have h1 : ∀ x ∈ Λ, φ x = 0 := fun x hx => by
      have : ψ ⟨x, hx⟩ ∈ LinearMap.range ψ := ⟨_, rfl⟩
      rw [h0] at this
      exact this
    have h2 : ∀ x : Fin r → E, φ x = 0 := by
      intro x
      have hx : x ∈ Submodule.span E (Λ : Set (Fin r → E)) := hsp ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => exact map_zero φ
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul a x _ hx =>
        have : (τ ∘ (a • x)) = τ a • (τ ∘ x) := by funext i; simp
        rw [hφ] at hx
        rw [hφ, this, dotProduct_smul, hx, smul_zero]
    apply hw
    funext i
    have := h2 (Pi.single i 1)
    have e : (τ ∘ (Pi.single i (1 : E) : Fin r → E)) = Pi.single i 1 := by
      funext k; by_cases h : k = i
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [hφ, e] at this
    simpa using this
  · rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hA x hx
    refine ⟨⟨y, hy⟩, ?_⟩
    have := congrArg φ hxy
    rw [map_sub, hφA, map_nsmul, nsmul_eq_mul] at this
    rw [hψ, hψ, smul_eq_mul]
    field_simp
    linear_combination -this

theorem det_ne_zero_of_gram [IsCMField E] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (u : Matrix (Fin r) (Fin r) ℂ) (hu : gram τ G u = G.map τ) : u.det ≠ 0 := by
  have e : gram τ G u = uᵀ * (G.map τ * u.map (starRingEnd ℂ)) := by
    ext a b
    simp [gram, hermC, col, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  intro h0
  have h1 : (G.map τ).det = τ G.det := (RingHom.map_det τ G).symm
  rw [← hu, e, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul] at h1
  exact hG ((map_eq_zero τ).1 h1.symm)

theorem eq_one_of_congr (ζ : E) (hζ : ∀ φ : E →+* ℂ, ‖φ ζ‖ = 1) (M : ℕ) (hM : 3 ≤ M)
    (hi : IsIntegral ℤ ((ζ - 1) / M)) : ζ = 1 := by
  by_contra hne
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h0 : (⟨(ζ - 1) / M, hi⟩ : 𝓞 E) ≠ 0 := fun h =>
    div_ne_zero (sub_ne_zero.2 hne) hM0 (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ := NumberField.exists_conjugate_one_le_norm h0
  have h1 : 1 ≤ ‖φ ((ζ - 1) / M)‖ := hφ
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  rw [map_div₀, norm_div, map_natCast, Complex.norm_natCast, le_div_iff₀ (by linarith), map_sub, map_one] at h1
  have h2 := norm_sub_le (φ ζ) 1
  rw [hζ, norm_one] at h2
  linarith

theorem norm_eq_one_of_herm [IsCMField E] (hr : 0 < r) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (ζ : E)
    (h : ∀ v w, herm G (ζ • v) (ζ • w) = herm G v w) (φ : E →+* ℂ) : ‖φ ζ‖ = 1 := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hs : ∀ v w, herm G (ζ • v) (ζ • w) = ζ * cc ζ * herm G v w := by
    intro v w
    simp only [herm, cc, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hb : ∀ a b, herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
    intro a b
    simp [herm, cc, Pi.single_apply, apply_ite]
  have h1 : ζ * cc ζ = 1 := by
    by_contra hne
    apply hG
    have : G = 0 := by
      ext a b
      have := (hs (Pi.single a 1) (Pi.single b 1)).symm.trans (h _ _)
      rw [hb] at this
      exact (mul_left_eq_self₀.1 this).resolve_left hne
    rw [this, Matrix.det_zero]
  have h2 := congrArg (fun x => ‖φ x‖) h1
  simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj, norm_mul, map_one, norm_one,
    Complex.norm_conj] at h2
  nlinarith [norm_nonneg (φ ζ)]

theorem exists_row_eig (hr : 0 < r) (A : Matrix (Fin r) (Fin r) ℂ) :
    ∃ (lam : ℂ) (w : Fin r → ℂ), w ≠ 0 ∧ w ᵥ* A = lam • w := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨lam, hl⟩ := Module.End.exists_eigenvalue (K := ℂ) (A.vecMulLinear : Module.End ℂ (Fin r → ℂ))
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  exact ⟨lam, w, hw.2, hw.apply_eq_smul⟩

theorem row_eig_conj (A B u : Matrix (Fin r) (Fin r) ℂ) (hu : u.det ≠ 0) (h : u * A = B * u) (lam : ℂ)
    (w : Fin r → ℂ) (hw : w ≠ 0) (he : w ᵥ* A = lam • w) :
    ∃ w' : Fin r → ℂ, w' ≠ 0 ∧ w' ᵥ* B = lam • w' := by
  have hU : IsUnit u.det := isUnit_iff_ne_zero.2 hu
  refine ⟨w ᵥ* u⁻¹, fun h0 => hw ?_, ?_⟩
  · have := congrArg (· ᵥ* u) h0
    simpa [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul u hU] using this
  · have e : u⁻¹ * B = A * u⁻¹ := by
      calc u⁻¹ * B = u⁻¹ * (B * u) * u⁻¹ := by
            rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv u hU, mul_one]
        _ = A * u⁻¹ := by rw [← h, ← mul_assoc, Matrix.nonsing_inv_mul u hU, one_mul]
    rw [Matrix.vecMul_vecMul, e, ← Matrix.vecMul_vecMul, he, Matrix.smul_vecMul]

end Alg

theorem isIntegral_eig {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r}
    {dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r} (hL : Laws D j Xo c U dict)
    {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (k : (U σ).Comp) {γ : GL (Fin D.R.r) D.host.E} (hγ : γ ∈ ((U σ).X k).Γ)
    {τ : D.host.E →+* ℂ} (hτ : τ ∈ ((U σ).X k).Ψ) (lam : ℂ) (w : Fin D.R.r → ℂ) (hw : w ≠ 0)
    (he : w ᵥ* (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = lam • w) :
    IsIntegral ℤ ((lam - 1) / l.M) := by
  obtain ⟨G, Λ, g, Λk, u, -, hk, -⟩ := GlobalTheory.T.principalLevel_components_doubleCosets_congruence D j H Dw l Xo c U dict hL σ hσ
  obtain ⟨hG, -, -, hfg, hsp, hu, hΓ, -⟩ := hk k
  obtain ⟨γ', ⟨-, hc⟩, hint⟩ := hΓ γ hγ
  have hdet := det_ne_zero_of_gram τ G (hG ▸ ((U σ).X k).Gm_det) _ (hu τ hτ)
  obtain ⟨w', hw', he'⟩ := row_eig_conj _ _ _ hdet (hint τ hτ) lam w hw he
  have h3 := l.three_le
  exact isIntegral_eig_of_congr _ hfg hsp l.M (by omega) _ hc τ w' hw' lam he'

theorem scalar_eq_one_of_conj : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∀ ζ : D.host.E, ((MulAut.conj δ γ₂ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * Matrix.scalar (Fin D.R.r) ζ → Matrix.scalar (Fin D.R.r) ζ = 1 := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hG hδ _ γ₂ hγ₂ γ hγ ζ hζ
  rcases Nat.eq_zero_or_pos D.R.r with hr | hr
  · ext a
    exact absurd a.isLt (by omega)
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := hσ₂
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h : ComplexEmbedding.conjugate τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ
    · exact ⟨_, h⟩
    · exact ⟨τ, (Data.cmType _ τ).2 h⟩
  have hτ₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ :=
    (((hL₂.unf σ₂ hσ₂).2.1 k₂).2 τ).2 ((((hL.unf _ hσ).2.1 k).2 τ).1 hτ)
  have hmul : (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (γ₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
      ζ • ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)) := by
    have e : (δ * γ₂ : GL (Fin D.R.r) D.host.E) = MulAut.conj δ γ₂ * δ := by simp
    have e' := congrArg (fun x : GL (Fin D.R.r) D.host.E => (x : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)) e
    simp only [Units.val_mul] at e'
    rw [e', hζ, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, Matrix.smul_mul]

  have hnorm : ∀ φ : D.host.E →+* ℂ, ‖φ ζ‖ = 1 := by
    refine norm_eq_one_of_herm hr _ ((U₂ σ₂).X k₂).Gm_det ζ fun v w => ?_
    have hs : Function.Surjective (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.2 δ.isUnit
    obtain ⟨v, rfl⟩ := hs v
    obtain ⟨w, rfl⟩ := hs w
    have key : ∀ x, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ
        (ζ • (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ x) =
        (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ ((γ₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ x) := by
      intro x
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul, Matrix.smul_mulVec]
    have h1 := (Data.Γ_stab _ γ hγ).1
    rw [← hG] at h1
    rw [← h1, key, key, hδ, (Data.Γ_stab _ γ₂ hγ₂).1, hδ]

  obtain ⟨lam, w, hw, he⟩ := exists_row_eig hr ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ)
  have hinv : ∀ x : GL (Fin D.R.r) D.host.E, (x : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ *
      ((x⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = 1 := by
    intro x
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one τ (map_zero τ) (map_one τ)]
  have he1 : lam • w ᵥ* ((γ⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ = w := by
    rw [← Matrix.smul_vecMul, ← he, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  have hlam : lam ≠ 0 := by
    rintro rfl
    exact hw (by rw [← he1, zero_smul])
  have ha := isIntegral_eig hL hσ k (inv_mem hγ) hτ lam⁻¹ w hw (by
    rw [eq_inv_smul_iff₀ hlam]; exact he1)
  have hb := isIntegral_eig hL₂ hσ₂ k₂ hγ₂ hτ₂ (τ ζ * lam)
    (w ᵥ* (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) (fun h0 => hw (by
      have := congrArg (· ᵥ* ((δ⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ) h0
      simpa only [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one, Matrix.zero_vecMul] using this)) (by
      have e : ∀ B : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E, (ζ • B).map τ = τ ζ • B.map τ := by
        intro B; ext a b; simp
      rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, hmul, e, Matrix.map_mul, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul, he,
        Matrix.smul_vecMul, smul_smul])
  have h3 := l.three_le
  have h3' := d.l₂.three_le
  have hM : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hM₂ : (d.l₂.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hMM : (d.l₂.M : ℂ) = l.M * d.pd := by exact_mod_cast hlev.2.1
  have hint : IsIntegral ℤ (τ ((ζ - 1) / l.M)) := by
    have e : τ ((ζ - 1) / l.M) = (lam⁻¹ - 1) / l.M + (d.pd : ℂ) * ((τ ζ * lam - 1) / d.l₂.M) +
        (d.l₂.M : ℂ) * ((lam⁻¹ - 1) / l.M * ((τ ζ * lam - 1) / d.l₂.M)) := by
      have hp : (d.pd : ℂ) ≠ 0 := fun h => hM₂ (by rw [hMM, h, mul_zero])
      rw [map_div₀, map_sub, map_one, map_natCast, hMM]
      field_simp
      ring
    rw [e]
    exact (ha.add ((isIntegral_natCast _).mul hb)).add ((isIntegral_natCast _).mul (ha.mul hb))
  have hint' : IsIntegral ℤ ((ζ - 1) / (l.M : D.host.E)) :=
    (isIntegral_algHom_iff τ.toIntAlgHom τ.injective).1 hint
  rw [eq_one_of_congr ζ hnorm l.M h3 hint', map_one]

end GlobalTheory.LevScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverComparisonScalarEqOneStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverComparison_scalar_eq_one : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∀ ζ : D.host.E, ((MulAut.conj δ γ₂ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * Matrix.scalar (Fin D.R.r) ζ → Matrix.scalar (Fin D.R.r) ζ = 1 := by
  first | exact @GlobalTheory.LevScalar.scalar_eq_one_of_conj | exact GlobalTheory.LevScalar.scalar_eq_one_of_conj | (intros; apply GlobalTheory.LevScalar.scalar_eq_one_of_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqArithmeticGroupMulScalarOfMovedFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqArithmeticGroupMulScalarOfMovedFrames
noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevModel

theorem orbit_open_scalar {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (τ₀ : Ψ) (G : Subgroup (GL (Fin r) E)) (h : GL (Fin r) E) {O : Set (Frame Ψ r)} (hO : IsOpen O)
    (hne : O.Nonempty) (hdet : ∀ y ∈ O, (mat y τ₀).det ≠ 0)
    (H1 : ∀ y ∈ O, ∃ γ ∈ G, ∃ b ∈ Bor Ψ r, lact h y = rmul (lact γ y) b) :
    ∃ γ ∈ G, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ hy₀
  set B₀ := Metric.ball y₀ ρ with hB₀
  let f : Option G → Set (Frame Ψ r) := fun o => match o with
    | none => B₀ᶜ
    | some γ' => ReciprocityTheory.ChartRestriction.G.PullbackSections.TSet Ψ ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have hc : ∀ o, IsClosed (f o) := by
    rintro (_ | γ')
    · exact Metric.isOpen_ball.isClosed_compl
    · exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isClosed_TSet _ _
  have hU : ⋃ o, f o = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    by_cases hx : x ∈ B₀
    · obtain ⟨γ', hγ', b, hb, e⟩ := H1 x (hball hx)
      exact ⟨some ⟨γ', hγ'⟩, ReciprocityTheory.ChartRestriction.G.PullbackSections.mem_TSet Ψ h γ' hb e⟩
    · exact ⟨none, hx⟩
  have hd := dense_iUnion_interior_of_closed hc hU
  obtain ⟨y, hyB, hyU⟩ := hd.inter_open_nonempty B₀ Metric.isOpen_ball ⟨_, Metric.mem_ball_self hρ⟩
  obtain ⟨o, ho⟩ := Set.mem_iUnion.1 hyU
  cases o with
  | none => exact absurd hyB (interior_subset ho)
  | some γ' =>
    set g : Matrix (Fin r) (Fin r) E := ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hg
    obtain ⟨κ, hκ⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.scalar_step τ₀ g
      (W := interior (f (some γ')) ∩ B₀) (isOpen_interior.inter Metric.isOpen_ball)
      (fun x hx => interior_subset hx.1) (y := y) ⟨ho, hyB⟩ (hdet y (hball hyB))
    have hent : ∀ a b, τ₀.1 (g a b) = if a = b then κ else 0 := by
      intro a b
      have := congrFun (congrFun hκ a) b
      simpa [Matrix.one_apply] using this
    have hh : (h : Matrix (Fin r) (Fin r) E) = (γ'.1 : Matrix (Fin r) (Fin r) E) * g := by
      rw [hg, ← Units.val_mul, mul_inv_cancel_left]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exact ⟨γ'.1, γ'.2, 0, by ext a; exact Fin.elim0 a⟩
    · refine ⟨γ'.1, γ'.2, g ⟨0, hr⟩ ⟨0, hr⟩, ?_⟩
      rw [hh]
      congr 1
      ext a b
      apply τ₀.1.injective
      rw [hent a b, Matrix.scalar_apply, Matrix.diagonal_apply]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab, hent, if_pos rfl]
      · rw [if_neg hab, if_neg hab, map_zero]

theorem eq_mul_scalar_of_moved {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ h : GL (Fin r) E) (hΨ : X₂.Ψ = X.Ψ)
    (H : ∀ x ∈ X₂.dom, ∀ x' : Frame X.Ψ r, GlobalTheory.LevModel.Moved X₂ X δ x x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact h x' = rmul (lact γ x') b) :
    ∃ γ ∈ X.Γ, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  classical

  obtain ⟨τ₁⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases hτ : τ₁ ∈ X.Ψ
    · exact ⟨τ₁, hτ⟩
    · refine ⟨ComplexEmbedding.conjugate τ₁, ?_⟩
      by_contra hc
      exact hτ ((X.cmType τ₁).2 hc)
  have hmem : ∀ τ : X₂.Ψ, τ.1 ∈ X.Ψ := fun τ => hΨ ▸ τ.2
  have hmem' : ∀ τ : X.Ψ, τ.1 ∈ X₂.Ψ := fun τ => hΨ.symm ▸ τ.2

  let back : Frame X.Ψ r → Frame X₂.Ψ r := fun y τ =>
    (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y ⟨τ.1, hmem τ⟩ : Matrix (Fin r) (Fin r) ℂ)
  let fwd : Frame X₂.Ψ r → Frame X.Ψ r := fun x τ =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, hmem' τ⟩ : Matrix (Fin r) (Fin r) ℂ)
  have hback : Continuous back := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    have hm : Continuous fun y : Frame X.Ψ r => mat y ⟨τ.1, hmem τ⟩ := continuous_apply _
    exact (continuous_const.matrix_mul hm).matrix_elem a b
  have hbf : ∀ x, back (fwd x) = x := by
    intro x
    funext τ
    show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ
    rw [← Matrix.mul_assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul, Matrix.one_mul]
  have hmoved : ∀ y, GlobalTheory.LevModel.Moved X₂ X δ (back y) y := by
    intro y τ h₂ h₁
    show mat y ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ *
      (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * mat y ⟨τ, h₁⟩)
    rw [← Matrix.mul_assoc]
    have := ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul τ (δ⁻¹ : GL (Fin r) E)
    rw [inv_inv] at this
    rw [this, Matrix.one_mul]
  have hdom : (X₂.dom).Nonempty := ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X₂ (ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.chosenFrame_isOrthogonal X₂)⟩
  obtain ⟨x₀, hx₀⟩ := hdom
  refine orbit_open_scalar ⟨τ₀, hτ₀⟩ X.Γ h (O := back ⁻¹' X₂.dom)
    ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X₂).preimage hback) ⟨fwd x₀, by rw [Set.mem_preimage, hbf]; exact hx₀⟩ ?_
    (fun y hy => H _ hy y (hmoved y))
  intro y hy
  have h1 := (hy ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩).1
  have h2 : mat (back y) ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩ =
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ₀ * mat y ⟨τ₀, hτ₀⟩ := rfl
  rw [h2, Matrix.det_mul] at h1
  exact right_ne_zero_of_mul h1

end GlobalTheory.LevModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqArithmeticGroupMulScalarOfMovedFramesStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_arithmeticGroup_mul_scalar_of_moved_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ h : GL (Fin r) E), X₂.Ψ = X.Ψ → (∀ x ∈ X₂.dom, ∀ x' : Frame X.Ψ r, GlobalTheory.LevModel.Moved X₂ X δ x x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact h x' = rmul (lact γ x') b) → ∃ γ ∈ X.Γ, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  first | exact @GlobalTheory.LevModel.eq_mul_scalar_of_moved | exact GlobalTheory.LevModel.eq_mul_scalar_of_moved | (intros; apply GlobalTheory.LevModel.eq_mul_scalar_of_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCoverArithmeticGroupLeFiniteIndex
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevModel

theorem goodEmb_comp_eF {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0)
    (σ₂ : d.c₂.F →+* ℂ) (h : GoodEmb d.c₂ σ₂) : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := by
  unfold GoodEmb at h ⊢
  rw [← h]
  rfl

theorem conj_arithGroup_le : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ((U₂ σ₂).X k₂).Γ.map (MulAut.conj δ).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj δ).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ≠ 0 := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hGm hδ hov
  have hσ := goodEmb_comp_eF d σ₂ hσ₂
  have hΨ : ((U₂ σ₂).X k₂).Ψ = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ := by
    ext τ
    rw [((hL₂.unf σ₂ hσ₂).2.1 k₂).2 τ, ((hL.unf _ hσ).2.1 k).2 τ]
  refine ⟨?_, GlobalTheory.T.relIndex_conj_isometry_flagDomainGroup_ne_zero _ _ δ hGm hδ⟩
  intro g hg
  obtain ⟨γ₂, hγ₂, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨γ, hγ, ζ, hζ⟩ := GlobalTheory.T.eq_arithmeticGroup_mul_scalar_of_moved_frames _ _ δ (MulAut.conj δ γ₂) hΨ
    (fun x hx x' hm => GlobalTheory.T.arithmeticGroup_conj_isometry_moves_cover_point D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hGm hδ hov γ₂ hγ₂ x hx x' hm)
  have h1 := GlobalTheory.T.coverComparison_scalar_eq_one D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hlev σ₂ hσ₂ k₂ k δ hGm hδ hov γ₂ hγ₂ γ hγ ζ hζ
  have e : (MulAut.conj δ).toMonoidHom γ₂ = γ := by
    apply Units.ext
    show ((MulAut.conj δ γ₂ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = _
    rw [hζ, h1, mul_one]
  rw [e]
  exact hγ

end GlobalTheory.LevModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCoverArithmeticGroupLeFiniteIndexStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_coverArithmeticGroup_le_finite_index : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ((U₂ σ₂).X k₂).Γ.map (MulAut.conj δ).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj δ).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ ≠ 0 := by
  first | exact @GlobalTheory.LevModel.conj_arithGroup_le | exact GlobalTheory.LevModel.conj_arithGroup_le | (intros; apply GlobalTheory.LevModel.conj_arithGroup_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComplexModelsComponentsIsometriesDegre
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevModel

theorem levCover_model : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∃ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E) (N : ℕ), 0 < N ∧ (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0) ∧ (∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N) ∧ ∃ t : (U₂ σ₂).Comp → ℂ, (∀ k₂, ‖t k₂‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → ∀ k₂ (x : Frame ((U₂ σ₂).X k₂).Ψ D.R.r) (x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ D.R.r), x ∈ ((U₂ σ₂).X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ) (h₁ : τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ), mat x' ⟨τ, h₁⟩ = (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → Even n → rdU (U₂ σ₂) g k₂ x = t k₂ ^ n * rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂) x' := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ
  have h1 := GlobalTheory.T.levelCover_component_over_base_rational_isometry D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ
  choose π δ hGm hIso hOv using h1
  have h2 := fun k₂ => GlobalTheory.T.conj_coverArithmeticGroup_le_finite_index D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ k₂ (π k₂) (δ k₂) (hGm k₂) (hIso k₂) (hOv k₂)
  obtain ⟨N, hN, hsum⟩ := GlobalTheory.T.levelCover_component_index_sum_eq_const D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ π δ
    (fun k₂ => ⟨hGm k₂, hIso k₂, (h2 k₂).1, (h2 k₂).2, hOv k₂⟩)
  have h4 := fun k₂ => GlobalTheory.T.levelCover_pullback_reading_eq_unitConst_pow_mul D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ hσ k₂ (π k₂) (δ k₂) (hGm k₂) (hIso k₂) (hOv k₂)
  choose t ht hread using h4
  refine ⟨π, δ, N, hN, fun k₂ => ⟨hGm k₂, hIso k₂, (h2 k₂).1, (h2 k₂).2⟩, hsum, t, ht, ?_⟩
  intro a n hD f hf g hg hP k₂ x x' hx hm hn
  exact hread k₂ a n hD f hf g hg hP x x' hx hm hn

end GlobalTheory.LevModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComplexModelsComponentsIsometriesDegreStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_complexModels_components_isometries_degree : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∃ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E) (N : ℕ), 0 < N ∧ (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0) ∧ (∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N) ∧ ∃ t : (U₂ σ₂).Comp → ℂ, (∀ k₂, ‖t k₂‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → ∀ k₂ (x : Frame ((U₂ σ₂).X k₂).Ψ D.R.r) (x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ D.R.r), x ∈ ((U₂ σ₂).X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ) (h₁ : τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ), mat x' ⟨τ, h₁⟩ = (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → Even n → rdU (U₂ σ₂) g k₂ x = t k₂ ^ n * rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂) x' := by
  first | exact @GlobalTheory.LevModel.levCover_model | exact GlobalTheory.LevModel.levCover_model | (intros; apply GlobalTheory.LevModel.levCover_model <;> assumption)
end
