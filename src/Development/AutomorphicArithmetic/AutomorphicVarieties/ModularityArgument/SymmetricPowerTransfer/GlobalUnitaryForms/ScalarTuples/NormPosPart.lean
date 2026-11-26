module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.HsHasse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.ExGLand
open NumberField Matrix

namespace UpperTheory.V.Z.Sym.Glob

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem ex_real (φ : F →+* ℂ) : ∃ σ : F →+* ℝ, ∀ x, φ x = (σ x : ℂ) := by
  have h := InfinitePlace.isReal_of_mk_isReal (IsTotallyReal.isReal (InfinitePlace.mk φ))
  exact ⟨h.embedding, fun x => (h.coe_embedding_apply x).symm⟩

theorem exG_nonsq {Δ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) : ∀ r : F, r ^ 2 ≠ Δ + 0 * r := by
  intro r hr
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  obtain ⟨σ, -⟩ := ex_real φ
  have h := hΔ σ
  have h2 := congrArg σ hr
  simp only [map_pow, zero_mul, add_zero] at h2
  nlinarith [sq_nonneg (σ r)]

theorem exG_ne {x : F} (h : TPos x) : x ≠ 0 := by
  intro hx
  obtain ⟨σ, -⟩ := ex_real (Classical.arbitrary (InfinitePlace F)).embedding
  have := h σ
  simp [hx] at this

private theorem emb_star {Δ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (φ : Lsq F Δ →+* ℂ) :
    (∀ x, φ (star x) = starRingEnd ℂ (φ x)) ∧ (φ QuadraticAlgebra.omega).im ≠ 0 := by
  obtain ⟨σ, hσ⟩ := ex_real (φ.comp (algebraMap F (Lsq F Δ)))
  have hσ' : ∀ t : F, φ (algebraMap F _ t) = (σ t : ℂ) := hσ
  set w := φ QuadraticAlgebra.omega with hwdef
  have hw : w * w = (σ Δ : ℂ) := by
    rw [hwdef, ← map_mul, ← hσ']
    congr 1
    ext <;> simp
  have hre := congrArg Complex.re hw
  have him := congrArg Complex.im hw
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  have hneg := hΔ σ
  have hwi : w.im ≠ 0 := by
    intro h0
    rw [h0] at hre
    nlinarith [sq_nonneg w.re]
  have hwr : w.re = 0 := by
    have : 2 * w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hwi
  have hd : ∀ x : Lsq F Δ, φ x = (σ x.re : ℂ) + (σ x.im : ℂ) * w := by
    intro x
    conv_lhs => rw [show x = algebraMap F _ x.re + algebraMap F _ x.im * QuadraticAlgebra.omega by ext <;> simp]
    rw [map_add (f := _), map_mul, hσ', hσ']
  refine ⟨fun x => ?_, hwi⟩
  rw [hd, hd]
  apply Complex.ext <;> simp [hwr]

theorem exG_land {Δ : F} (hΔ : ∀ σ : F →+* ℝ, σ Δ < 0) (g : Fin 3 → F) (hg : ∀ i, TPos (g i)) (y : Lsq F Δ)
    (hy : algebraMap F (Lsq F Δ) (∏ i, g i) = y * star y) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Lsq F Δ), IsUnit P.det ∧
      diagonal (fun i => algebraMap F (Lsq F Δ) (g i)) = Pᵀ * P.map star := by
  haveI : Fact (∀ r : F, r ^ 2 ≠ Δ + 0 * r) := ⟨exG_nonsq hΔ⟩
  haveI : Module.Finite ℚ (Lsq F Δ) := Module.Finite.trans F (Lsq F Δ)
  haveI : NumberField (Lsq F Δ) := ⟨⟩
  haveI : IsTotallyComplex (Lsq F Δ) := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff]
    intro hr
    apply (emb_star hΔ w.embedding).2
    rw [← hr.coe_embedding_apply]
    exact Complex.ofReal_im _
  haveI : Algebra.IsQuadraticExtension F (Lsq F Δ) :=
    { finrank_eq_two' := QuadraticAlgebra.finrank_eq_two Δ 0 }
  haveI : IsCMField (Lsq F Δ) := IsCMField.ofCMExtension F (Lsq F Δ)
  have hcc : ∀ x : Lsq F Δ, ReciprocityTheory.ChartRestriction.G.FD.cc x = star x := by
    intro x
    obtain φ := (Classical.arbitrary (InfinitePlace (Lsq F Δ))).embedding
    apply φ.injective
    simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, IsCMField.complexEmbedding_complexConj, (emb_star hΔ φ).1]
  have hstar : ∀ t : F, star (algebraMap F (Lsq F Δ) t) = algebraMap F (Lsq F Δ) t := by
    intro t
    ext <;> simp
  set G' : Matrix (Fin 3) (Fin 3) (Lsq F Δ) := diagonal (fun i => algebraMap F (Lsq F Δ) (g i)) with hG'
  have hdet : G'.det = algebraMap F (Lsq F Δ) (∏ i, g i) := by
    rw [hG', det_diagonal, map_prod]
  have hprod : (∏ i, g i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => exG_ne (hg i))
  obtain ⟨P, hP, hPe⟩ := GlobalTheory.QNorm.landherr_and_landherrSt.1 (Lsq F Δ) 3 1 G'
    (by
      intro a b
      rw [hcc]
      by_cases h : a = b
      · subst h
        simp
      · simp [Matrix.one_apply, h, Ne.symm h])
    (by
      intro a b
      rw [hcc]
      by_cases h : a = b
      · subst h
        simp [hG', hstar]
      · simp [hG', Matrix.diagonal_apply, h, Ne.symm h])
    (by simp)
    (by
      rw [hdet]
      exact (map_ne_zero_iff _ (algebraMap F (Lsq F Δ)).injective).mpr hprod)
    (by
      intro τ
      obtain ⟨σ, hσ⟩ := ex_real (τ.comp (algebraMap F (Lsq F Δ)))
      have hσ' : ∀ t : F, τ (algebraMap F _ t) = (σ t : ℂ) := hσ
      refine ⟨diagonal (fun i => ((Real.sqrt (σ (g i)) : ℝ) : ℂ)), ?_, ?_⟩
      · rw [det_diagonal]
        refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
        rw [Complex.ofReal_ne_zero]
        exact (Real.sqrt_pos.mpr (hg i σ)).ne'
      · ext a b
        by_cases h : a = b
        · subst h
          simp only [hG', Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.mul_apply, Matrix.transpose_apply,
            Matrix.diagonal_apply, Matrix.one_apply]
          simp [hσ']
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg a σ).le]
        · simp [hG', Matrix.diagonal_apply, h, Ne.symm h, Matrix.mul_apply, Matrix.one_apply])
    (by
      refine ⟨y⁻¹, ?_⟩
      rw [hcc, det_one, hdet, hy, star_inv₀, one_div, mul_inv])
  have hm : P.map ReciprocityTheory.ChartRestriction.G.FD.cc = P.map star := Matrix.ext fun a b => hcc (P a b)
  refine ⟨P, isUnit_iff_ne_zero.mpr hP, ?_⟩
  rw [hPe, Matrix.mul_one, hm]

end UpperTheory.V.Z.Sym.Glob
end

open NumberField Matrix QuadraticAlgebra

namespace UpperTheory.V.Z.Sym.Glob

open Loc

section Gram

variable {K : Type} [Field K] {Δ τ : K}

private theorem st_alg' (c : K) : star (algebraMap K (Lsq K Δ) c) = algebraMap K _ c := by
  ext <;> simp

private theorem tr_form (m x y : EL Δ τ) :
    QuadraticAlgebra.trace (m * x * star (sigL y)) =
      (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) * x.re * star y.re +
      (algebraMap K (Lsq K Δ) τ * m.re + 2 * m.im) * x.re * star y.im +
      (algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im) * x.im * star y.re +
      (2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) * x.im * star y.im := by
  simp only [QuadraticAlgebra.trace, LinearMap.coe_mk, AddHom.coe_mk, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sigL]
  ring

private theorem star_parts {m : EL Δ τ} (h : star (sigL m) = m) :
    star m.im = -m.im ∧ star m.re = m.re + algebraMap K (Lsq K Δ) τ * m.im := by
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sigL] at h1 h2
  refine ⟨by linear_combination -h2, by linear_combination h1 + algebraMap K (Lsq K Δ) τ * h2⟩

private theorem diag_sum (Pm : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (g : Fin 3 → Lsq K Δ)
    (e : diagonal g = Pmᵀ * Pm.map star) (a a' : Fin 3 → Lsq K Δ) :
    ∑ k, (Pm *ᵥ a) k * star ((Pm *ᵥ a') k) = ∑ i, g i * a i * star (a' i) := by
  have hij : ∀ i j, ∑ k, Pm k i * star (Pm k j) = diagonal g i j := by
    intro i j
    rw [e]
    simp [Matrix.mul_apply]
  calc ∑ k, (Pm *ᵥ a) k * star ((Pm *ᵥ a') k)
      = ∑ k, ∑ i, ∑ j, Pm k i * star (Pm k j) * (a i * star (a' j)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, ∑ j, (∑ k, Pm k i * star (Pm k j)) * (a i * star (a' j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ = ∑ i, g i * a i * star (a' i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp_rw [hij]
        rw [Finset.sum_eq_single i]
        · simp [mul_assoc]
        · intro j _ hj
          rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
          ring
        · simp

private theorem gram_diag [CharZero K] {c : K} {d m : EL Δ τ} (h : IsDat c d m) :
    ∃ g : K, algebraMap K (Lsq K Δ) g = QuadraticAlgebra.trace m ∧ (g ≠ 0 → ∃ (g2 : K) (b y : Lsq K Δ),
      (∀ u v : Sp Δ τ, herm c m u v = algebraMap K (Lsq K Δ) c * u.1 * star v.1 +
        algebraMap K (Lsq K Δ) g * (u.2.re + u.2.im * b) * star (v.2.re + v.2.im * b) +
        algebraMap K (Lsq K Δ) g2 * u.2.im * star v.2.im) ∧
      algebraMap K (Lsq K Δ) (g * g2) = algebraMap K (Lsq K Δ) (2 - τ) * (y * star y)) := by
  obtain ⟨hsi, hsr⟩ := star_parts h.m_star
  have fix : ∀ z : Lsq K Δ, star z = z → algebraMap K (Lsq K Δ) z.re = z := by
    intro z hz
    have h1 := congrArg QuadraticAlgebra.im hz
    rw [QuadraticAlgebra.im_star] at h1
    have h2 : z.im = 0 := by
      have h3 : (2 : K) * z.im = 0 := by linear_combination -h1
      simpa using h3
    ext
    · simp
    · simp [h2]
  have hA : QuadraticAlgebra.trace m = 2 * m.re + algebraMap K (Lsq K Δ) τ * m.im := rfl
  have hAs : star (QuadraticAlgebra.trace m) = QuadraticAlgebra.trace m := by
    rw [hA]
    simp only [star_add, star_mul', st_alg', star_ofNat, hsr, hsi]
    ring
  refine ⟨(QuadraticAlgebra.trace m).re, fix _ hAs, fun hg0 => ?_⟩
  have hG : algebraMap K (Lsq K Δ) (QuadraticAlgebra.trace m).re =
      2 * m.re + algebraMap K (Lsq K Δ) τ * m.im := (fix _ hAs).trans hA
  obtain ⟨y, hy⟩ := exG_norm h
  have hGi : algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹ *
      algebraMap K (Lsq K Δ) (QuadraticAlgebra.trace m).re = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hg0, map_one]
  have hG2 : algebraMap K (Lsq K Δ) ((2 - τ) * QuadraticAlgebra.norm y / (QuadraticAlgebra.trace m).re) *
      algebraMap K (Lsq K Δ) (QuadraticAlgebra.trace m).re =
      algebraMap K (Lsq K Δ) (2 - τ) * (y * star y) := by
    rw [← map_mul, div_mul_cancel₀ _ hg0, map_mul, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  refine ⟨(2 - τ) * QuadraticAlgebra.norm y / (QuadraticAlgebra.trace m).re,
    algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹ *
      (algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im), y, ?_, ?_⟩
  · intro u v
    simp only [herm]
    rw [tr_form]
    rw [hG] at hGi hG2 ⊢
    rw [QuadraticAlgebra.norm_def] at hy
    simp only [map_sub, map_add (f := _), map_ofNat] at hG2 hy
    simp only [star_add, star_mul', star_sub, star_pow, st_alg', star_ofNat, hsr, hsi]
    linear_combination
      (-((algebraMap K (Lsq K Δ) τ * m.re + 2 * m.im) * u.2.re * star v.2.im) -
        (algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im) * u.2.im * star v.2.re -
        u.2.im * star v.2.im * ((2 * m.re + algebraMap K (Lsq K Δ) τ * m.im) -
          algebraMap K (Lsq K Δ) ((2 - τ) * QuadraticAlgebra.norm y / (QuadraticAlgebra.trace m).re)) -
        u.2.im * star v.2.im * algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹ *
          (algebraMap K (Lsq K Δ) τ * m.re + ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * m.im) *
          (algebraMap K (Lsq K Δ) τ * m.re + 2 * m.im)) * hGi +
      (-(u.2.im * star v.2.im * algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹)) * hG2 +
      (u.2.im * star v.2.im * algebraMap K (Lsq K Δ) ((QuadraticAlgebra.trace m).re)⁻¹ *
        (2 - algebraMap K (Lsq K Δ) τ)) * hy
  · rw [map_mul, mul_comm]
    exact hG2

end Gram

section Main

variable {F : Type} [Field F] [NumberField F]

private theorem hs_sq {K : Type} [Field K] [CharZero K] {D : K} (h0 : D ≠ 0) (h : IsSquare D) (x : K) : hs D x = 1 := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := by
    rintro rfl
    simp at h0
  unfold hs
  rw [if_pos]
  refine ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
  field_simp
  ring

private theorem disc_norm {Δ : F} (D : Dat Δ) (hok : D.Ok) (hΔ0 : Δ ≠ 0) {w : F} (hw : TPos w) (hw0 : w ≠ 0) (hev : D.Ev w) :
    ∃ u : Lsq F Δ, algebraMap F (Lsq F Δ) w = u * star u := by
  have harch : ∀ σ : F →+* ℝ, hs (σ Δ) (σ w) = 1 := by
    intro σ
    unfold hs
    rw [if_pos]
    exact ⟨Real.sqrt (σ w), 0, by simp [Real.sq_sqrt (hw σ).le]⟩
  have hloc : ∀ v : Pl F, hs (cv v Δ) (cv v w) = 1 := by
    intro v
    by_cases hv : v ∈ D.Sg
    · haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
      exact hs_sq ((map_ne_zero (cv v)).mpr hΔ0) (hok.split v hv) _
    · have hl := hok.off v hv
      exact (hsLaw (Ov v) (Kv v) _ hl).2.1 _ _ hl.even (hev v hv)
  have hH := hsHasse F Δ w hΔ0 hw0 harch hloc
  unfold hs at hH
  split_ifs at hH with hab
  · obtain ⟨a, b, hab⟩ := hab
    refine ⟨⟨a, b⟩, ?_⟩
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    congr 1
    rw [QuadraticAlgebra.norm_def]
    simp only
    linear_combination -hab
  · norm_num at hH

private theorem norm_pos_part {Δ : F} (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (y : Lsq F Δ) (σ : F →+* ℝ) :
    0 ≤ σ (QuadraticAlgebra.norm y) := by
  have h := hneg σ
  rw [QuadraticAlgebra.norm_def]
  simp only [map_add (f := _), map_sub, map_mul, map_zero, zero_mul, add_zero]
  nlinarith [sq_nonneg (σ y.re), sq_nonneg (σ y.im), mul_nonneg (neg_nonneg.mpr h.le) (sq_nonneg (σ y.im))]

end Main

theorem exG : ExG := by
  intro F _ _ Δ D hok τ c d m hdat hpos hev
  haveI : IsTotallyReal F := hok.real
  have hΔ0 : Δ ≠ 0 := by
    intro h0
    exact exG_nonsq hok.neg 0 (by rw [h0]; ring)
  obtain ⟨g, hg, hg2⟩ := gram_diag hdat
  have hcpos : TPos c := by
    have hne : ((1, 0) : Sp Δ τ) ≠ 0 := by
      intro h0
      have h1 := congrArg Prod.fst h0
      simp at h1
    have h1 := hpos _ hne
    simpa [herm, sigL] using h1
  have hx1ne : ((0, ⟨1, 0⟩) : Sp Δ τ) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun p : Sp Δ τ => p.2.re) h0
    simp at h1
  have hx1 : herm c m (0, ⟨1, 0⟩) (0, ⟨1, 0⟩) = algebraMap F (Lsq F Δ) g := by
    rw [hg, herm, tr_form]
    simp only [star_zero, star_one, mul_zero, zero_mul, mul_one, add_zero, zero_add, map_zero]
    rfl
  have hgpos : TPos g := by
    have h1 := hpos _ hx1ne
    rw [hx1] at h1
    simpa using h1
  have hg0 : g ≠ 0 := exG_ne hgpos
  obtain ⟨g2, b, y, hform, hprod⟩ := hg2 hg0
  have hx2ne : ((0, ⟨-b, 1⟩) : Sp Δ τ) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun p : Sp Δ τ => p.2.im) h0
    simp at h1
  have hx2 : herm c m (0, ⟨-b, 1⟩) (0, ⟨-b, 1⟩) = algebraMap F (Lsq F Δ) g2 := by
    rw [hform]
    simp
  have hg2pos : TPos g2 := by
    have h1 := hpos _ hx2ne
    rw [hx2] at h1
    simpa using h1
  have hmain : g * g2 = (2 - τ) * QuadraticAlgebra.norm y := by
    have h1 := congrArg QuadraticAlgebra.re hprod
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← map_mul] at h1
    simpa using h1
  have h2τ : TPos (2 - τ) := by
    intro σ
    have h1 := hgpos σ
    have h2 := hg2pos σ
    have h3 := norm_pos_part hok.neg y σ
    have h4 := congrArg σ hmain
    rw [map_mul, map_mul] at h4
    by_contra hle
    push_neg at hle
    nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hle) h3]
  have hw : TPos (c * (2 - τ)) := fun σ => by
    rw [map_mul]
    exact mul_pos (hcpos σ) (h2τ σ)
  obtain ⟨u, hu⟩ := disc_norm D hok hΔ0 hw (exG_ne hw) hev
  let gi : Fin 3 → F := ![c, g, g2]
  have hgi : ∀ i, TPos (gi i) := by
    intro i
    fin_cases i
    · exact hcpos
    · exact hgpos
    · exact hg2pos
  have hprod3 : algebraMap F (Lsq F Δ) (∏ i, gi i) = (u * y) * star (u * y) := by
    have hp : ∏ i, gi i = c * (g * g2) := by
      simp [gi, Fin.prod_univ_three, mul_assoc]
    have hu' : algebraMap F (Lsq F Δ) c * algebraMap F (Lsq F Δ) (2 - τ) = u * star u := by
      rw [← map_mul]
      exact hu
    rw [hp, map_mul, hprod, star_mul']
    linear_combination (y * star y) * hu'
  obtain ⟨P, hPdet, hPe⟩ := exG_land hok.neg gi hgi (u * y) hprod3
  let Co : Sp Δ τ ≃ₗ[Lsq F Δ] (Fin 3 → Lsq F Δ) :=
    { toFun := fun x => ![x.1, x.2.re + x.2.im * b, x.2.im]
      invFun := fun a => (a 0, (⟨a 1 - a 2 * b, a 2⟩ : EL Δ τ))
      map_add' := by
        intro x x'
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro r x
        funext i
        fin_cases i <;> simp [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul] <;> ring
      left_inv := by
        intro x
        ext <;> simp
      right_inv := by
        intro a
        funext i
        fin_cases i <;> simp }
  let Pe := Co.trans (P.toLinearEquiv' (P.invertibleOfIsUnitDet hPdet))
  have hherm : ∀ x x' : Sp Δ τ, herm c m x x' = ∑ i, Pe x i * star (Pe x' i) := by
    intro x x'
    have e1 : ∀ z, Pe z = P *ᵥ Co z := fun z => by
      first
        | rfl
        | (simp only [Pe, LinearEquiv.trans_apply]; rw [← Matrix.toLin'_apply]; rfl)
        | (simp only [Pe, LinearEquiv.trans_apply, ← LinearEquiv.coe_toLinearMap, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply])
    rw [e1, e1, diag_sum P (fun i => algebraMap F (Lsq F Δ) (gi i)) hPe, Fin.sum_univ_three, hform]
    simp [Co, gi]
  obtain ⟨δ, ι', hM⟩ := exG_models hdat Pe hherm
  exact ⟨δ, ι', Pe, hM⟩

end UpperTheory.V.Z.Sym.Glob
