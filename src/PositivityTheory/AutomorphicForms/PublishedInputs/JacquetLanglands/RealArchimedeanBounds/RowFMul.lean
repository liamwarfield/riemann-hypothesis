module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.RowFMul
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightMultiplicativityAlt

theorem rowF_mul {F : Type} [Field F] [NumberField F] (s : Fin 2 → F) (x y : GF F) :
    rowF s (x * y) = rowF s x ᵥ* y.val := by
  simp only [rowF, Units.val_mul, Matrix.vecMul_vecMul]

theorem row_mul {F : Type} [Field F] [NumberField F] (t : Af F) (k : GF F) (M : Matrix (Fin 2) (Fin 2) (Af F)) :
    (fun i => t * k.val 1 i) ᵥ* M = fun i => t * (k.val * M) 1 i := by
  ext i
  simp [Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, mul_add, mul_assoc]

theorem zc_val {F : Type} [Field F] [NumberField F] (z : (Af F)ˣ) :
    (zc F z).val = Matrix.scalar (Fin 2) (z : Af F) := rfl

theorem det_zc {F : Type} [Field F] [NumberField F] (z : (Af F)ˣ) :
    Matrix.GeneralLinearGroup.det (zc F z) = z * z := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, zc_val, pow_two]

theorem part1 (hM : AMem) (hR : ARow) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ)
    (s : Fin 2 → F) (hs : s ≠ 0) (x h : GF F) (hh : h ∈ Hc c) :
    absF (Matrix.GeneralLinearGroup.det (x * h)) / nF s (x * h) ^ 2 =
      absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 := by
  obtain ⟨-, -, hKc, hH, hdet, -⟩ := hM F
  obtain ⟨hA1, hA2, hA3, -⟩ := UpperTheory.V.Sd.Hm.absf F
  obtain ⟨k', hk', z, rfl⟩ := (hH c h).1 hh
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  have hk'0 : k' ∈ K0 F := hKc c hk'
  have e1 : nF s x = absF t := (hR F s x).2 t k hk ht
  have hx : rowF s x = fun i => (t : Af F) * k.val 1 i := funext ht
  have e2 : nF s (x * (k' * zc F z)) = absF (t * z) := by
    refine (hR F s _).2 (t * z) (k * k') (mul_mem hk hk'0) fun i => ?_
    rw [rowF_mul, hx, row_mul]
    simp only [Units.val_mul, zc_val, ← Matrix.mul_assoc, Matrix.scalar_apply, Matrix.mul_diagonal]
    ring
  have e3 : absF (Matrix.GeneralLinearGroup.det k') = 1 := hA3 _ fun w => (hdet k' hk'0 w).1
  rw [e1, e2, map_mul, map_mul, det_zc]
  simp only [hA2, e3]
  have := (hA1 t).ne'
  have := (hA1 z).ne'
  field_simp

theorem part2 (hM : AMem) (hR : ARow) (hMo : AMono) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (a : GF F) : ∃ C : ℝ, ∀ s : Fin 2 → F, s ≠ 0 → ∀ x : GF F,
      absF (Matrix.GeneralLinearGroup.det (x * a)) / nF s (x * a) ^ 2 ≤
        C * (absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2) := by
  obtain ⟨hK, hO, -, -, hdet, -, hN, -⟩ := hM F
  obtain ⟨hA1, hA2, -, -⟩ := UpperTheory.V.Sd.Hm.absf F
  obtain ⟨N, hN0, hNa⟩ := hN a⁻¹
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨n, hn⟩ : ∃ n : (Af F)ˣ, (n : Af F) = (N : Af F) :=
    ⟨ratU F (Units.mk0 (N : F) hNF), by simp [ratU]⟩
  refine ⟨absF (Matrix.GeneralLinearGroup.det a) / absF n ^ 2, fun s hs x => ?_⟩
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  obtain ⟨t', k', hk', ht'⟩ := (hR F s (x * a)).1 hs
  rw [(hR F s x).2 t k hk ht, (hR F s (x * a)).2 t' k' hk' ht']
  have key : absF (n * t) ≤ absF t' := by
    refine hMo F _ _ fun w => ?_
    have hrow : rowF s x = rowF s (x * a) ᵥ* (a⁻¹ : GF F).val := by
      rw [← rowF_mul, mul_inv_cancel_right]
    have hint : ∀ i j, Valued.v (pLoc F w (k'.val i j)) ≤ 1 := fun i j =>
      (hO _).1 (((hK k').1 hk').1 i j) w
    have hint2 : ∀ i j, Valued.v (pLoc F w ((N : Af F) * (a⁻¹ : GF F).val i j)) ≤ 1 := fun i j =>
      (hO _).1 (hNa i j) w
    have heq : ∀ i, (n : Af F) * ((t : Af F) * k.val 1 i) = (t' : Af F) * (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
        k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i)) := by
      intro i
      have h1 := congrFun hrow i
      rw [← ht i, hn, h1]
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ht']
      ring
    have hS : ∀ i, Valued.v (pLoc F w (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
        k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i))) ≤ 1 := by
      intro i
      rw [map_add (f := _)]
      refine Valuation.map_add_le _ ?_ ?_ <;> rw [map_mul, map_mul] <;> exact mul_le_one' (hint _ _) (hint2 _ _)
    have hmax := (hdet k hk w).2
    obtain ⟨i, hi⟩ : ∃ i, Valued.v (pLoc F w (k.val 1 i)) = 1 := by
      rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with h | h
      · exact ⟨0, h.symm.trans hmax⟩
      · exact ⟨1, h.symm.trans hmax⟩
    calc Valued.v (pLoc F w ((n * t : (Af F)ˣ) : Af F))
        = Valued.v (pLoc F w ((n : Af F) * ((t : Af F) * k.val 1 i))) := by
          simp only [Units.val_mul, map_mul, hi, mul_one]
      _ = Valued.v (pLoc F w (t' : Af F)) * Valued.v (pLoc F w (k'.val 1 0 * ((N : Af F) * (a⁻¹ : GF F).val 0 i) +
          k'.val 1 1 * ((N : Af F) * (a⁻¹ : GF F).val 1 i))) := by
          rw [heq i, map_mul (pLoc F w), map_mul Valued.v]
      _ ≤ Valued.v (pLoc F w (t' : Af F)) * 1 := mul_le_mul' le_rfl (hS i)
      _ = _ := mul_one _
  rw [map_mul, hA2]
  have key2 : absF n * absF t ≤ absF t' := by rw [← hA2]; exact key
  have p1 := hA1 n
  have p2 := hA1 t
  have p3 := hA1 t'
  have p4 := hA1 (Matrix.GeneralLinearGroup.det x)
  have p5 := hA1 (Matrix.GeneralLinearGroup.det a)
  calc absF (Matrix.GeneralLinearGroup.det x) * absF (Matrix.GeneralLinearGroup.det a) / absF t' ^ 2
      ≤ absF (Matrix.GeneralLinearGroup.det x) * absF (Matrix.GeneralLinearGroup.det a) / (absF n * absF t) ^ 2 :=
        div_le_div_of_nonneg_left (mul_pos p4 p5).le (pow_pos (mul_pos p1 p2) 2)
          (pow_le_pow_left₀ (mul_pos p1 p2).le key2 2)
    _ = _ := by
      field_simp

end UpperTheory.Esk.HeightMultiplicativityAlt

theorem UpperTheory.Esk.dMul : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.AMono → UpperTheory.Esk.ARow → UpperTheory.Esk.DMul := by
  intro hM _ hMo hR F _ _ _ c _ χ
  exact ⟨fun s hs x h hh => UpperTheory.Esk.HeightMultiplicativityAlt.part1 hM hR F c s hs x h hh,
    fun a => UpperTheory.Esk.HeightMultiplicativityAlt.part2 hM hR hMo F a⟩
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AUnitP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.NearUnitLemmas

open scoped Classical

abbrev bU (F : Type) [Field F] [NumberField F] :=
  (NumberField.Units.basisUnitLattice F).ofZLatticeBasis ℝ (NumberField.Units.unitLattice F)

theorem abs_sg {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    |sg v x| = v x := by
  simpa [Real.norm_eq_abs] using InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v) x

theorem near_unit (F : Type) [Field F] [NumberField F] (a : NumberField.Units.dirichletUnitTheorem.logSpace F) :
    ∃ x : (𝓞 F)ˣ, ∀ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      |a w - InfinitePlace.mult w.1 * Real.log (w.1 (x : F))| ≤ ∑ i, ‖bU F i‖ := by
  have hmem : (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) ∈
      NumberField.Units.unitLattice F := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (NumberField.Units.unitLattice F)
      (NumberField.Units.basisUnitLattice F)]
    exact (ZSpan.floor (bU F) a).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.1 hmem
  refine ⟨x.toMul, fun w => ?_⟩
  have h1 : InfinitePlace.mult w.1 * Real.log (w.1 ((x.toMul : (𝓞 F)ˣ) : F)) =
      (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) w := by
    rw [← hx]; rfl
  rw [h1]
  have h2 : a w - (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) w =
      ZSpan.fract (bU F) a w := by rw [ZSpan.fract_apply]; rfl
  rw [h2, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ w).trans (ZSpan.norm_fract_le _ _)

end UpperTheory.Esk.NearUnitLemmas

namespace UpperTheory.Esk

open UpperTheory.Esk.NearUnitLemmas in
theorem aUnit : UpperTheory.Esk.AUnit := by
  classical
  intro F _ _ _
  set M : ℝ := ∑ i, ‖bU F i‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨Real.exp (2 * (Fintype.card (InfinitePlace F) * M)), Real.exp_pos _, fun y hy => ?_⟩
  set L : InfinitePlace F → ℝ := fun w => Real.log |y w|
  set m : ℝ := (∑ w, L w) / Fintype.card (InfinitePlace F)
  obtain ⟨x, hx⟩ := near_unit F (fun w => m - L w.1)
  set u : F := (x : F)
  have hmult : ∀ w : InfinitePlace F, InfinitePlace.mult w = 1 :=
    fun w => (IsTotallyReal.isReal w).mult_eq_one
  set d : InfinitePlace F → ℝ := fun w => Real.log (w u) + L w - m
  have hn : (Fintype.card (InfinitePlace F) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsum : ∑ w, d w = 0 := by
    have h0 : ∑ w : InfinitePlace F, Real.log (w u) = 0 := by
      simpa [hmult] using NumberField.Units.sum_mult_mul_log x
    simp only [d, Finset.sum_sub_distrib, Finset.sum_add_distrib, h0, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, m]
    field_simp
    ring
  have hne : ∀ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, |d w| ≤ M := by
    intro w
    have := hx w
    rw [hmult, Nat.cast_one, one_mul] at this
    calc |d w| = |(m - L w.1) - Real.log (w.1 u)| := by
          rw [← abs_neg]; congr 1; simp only [d]; ring
      _ ≤ M := this
  have hall : ∀ w, |d w| ≤ Fintype.card (InfinitePlace F) * M := by
    intro w
    by_cases hw : w = NumberField.Units.dirichletUnitTheorem.w₀
    · subst hw
      have h := Fintype.sum_eq_add_sum_subtype_ne d NumberField.Units.dirichletUnitTheorem.w₀
      rw [hsum] at h
      have h' : d NumberField.Units.dirichletUnitTheorem.w₀ =
          -∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, d w := by
        linarith
      rw [h', abs_neg]
      calc |∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, d w|
          ≤ ∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, |d w| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, M :=
            Finset.sum_le_sum fun w _ => hne w
        _ = (Fintype.card {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} : ℝ) * M := by
            simp
        _ ≤ Fintype.card (InfinitePlace F) * M := by
            gcongr
            exact_mod_cast Fintype.card_subtype_le _
    · calc |d w| ≤ M := hne ⟨w, hw⟩
        _ ≤ Fintype.card (InfinitePlace F) * M := by
          have : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
          nlinarith
  have hu0 : ∀ w : InfinitePlace F, 0 < w u := fun w => NumberField.Units.pos_at_place x w
  have hval : ∀ w, |sg w u * y w| = Real.exp (d w + m) := by
    intro w
    simp only [d, L]
    rw [abs_mul, abs_sg, sub_add_cancel, Real.exp_add, Real.exp_log (hu0 w),
      Real.exp_log (abs_pos.2 (hy w))]
  refine ⟨u, ?_, ?_, ?_, fun v v' => ?_⟩
  · intro h
    have := hu0 NumberField.Units.dirichletUnitTheorem.w₀
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  · exact NumberField.RingOfIntegers.isIntegral_coe (x : 𝓞 F)
  · have : u⁻¹ = ((x⁻¹ : (𝓞 F)ˣ) : F) := by simp [u]
    rw [this]
    exact NumberField.RingOfIntegers.isIntegral_coe ((x⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  · rw [hval, hval, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := (abs_le.1 (hall v)).2
    have h2 := (abs_le.1 (hall v')).1
    linarith

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DMinkP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

variable {F : Type} [Field F]

namespace UpperTheory.Esk.MinkowskiHeightLemmas

private theorem term (σ : F →+* ℝ) (γ : GL (Fin 2) F) (s : Fin 2 → F) (z : P) :
    |(Matrix.GeneralLinearGroup.map σ γ • z).1.im| /
      ‖(σ (s 0) : ℂ) * (Matrix.GeneralLinearGroup.map σ γ • z).1 + (σ (s 1) : ℂ)‖ ^ 2 =
    |σ γ.val.det| * (|z.1.im| / ‖(σ ((s ᵥ* γ.val) 0) : ℂ) * z.1 + (σ ((s ᵥ* γ.val) 1) : ℂ)‖ ^ 2) := by
  set g := Matrix.GeneralLinearGroup.map σ γ
  have hd : den g z.1 ≠ 0 := den_ne g z.2
  have hdet : g.val.det = σ γ.val.det := by
    rw [det_eq, Matrix.det_fin_two]; simp [g]
  have e : (σ (s 0) : ℂ) * (g • z).1 + (σ (s 1) : ℂ) =
      ((σ ((s ᵥ* γ.val) 0) : ℂ) * z.1 + (σ ((s ᵥ* γ.val) 1) : ℂ)) / den g z.1 := by
    rw [coe_smul, eq_div_iff hd, add_mul, mul_assoc, div_mul_cancel₀ _ hd]
    simp [g, num, den, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    ring
  rw [e, coe_smul, im_div, hdet, norm_div, div_pow, Complex.normSq_eq_norm_sq, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg ‖den g z.1‖)]
  have hn : ‖den g z.1‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hd)
  by_cases h0 : ‖(σ ((s ᵥ* γ.val) 0) : ℂ) * z.1 + (σ ((s ᵥ* γ.val) 1) : ℂ)‖ ^ 2 = 0
  · rw [h0]; simp
  · field_simp

private theorem ht_act {I Gf : Type} [Group Gf] [Fintype I] (D : Dat F I Gf) (s : Fin 2 → F) (γ : GL (Fin 2) F)
    (z : X I) (x : Gf) (hrat : D.hf s (D.j γ * x) * ∏ v, |D.σ v γ.val.det| = D.hf (s ᵥ* γ.val) x) :
    D.Ht (s ᵥ* γ.val) z x = D.Ht s (D.act γ z) (D.j γ * x) := by
  simp only [Dat.Ht, Dat.act, Dat.r, term, Finset.prod_mul_distrib, ← hrat]
  ring

private theorem row_ne {σ : F →+* ℝ} {s : Fin 2 → F} (hs : s ≠ 0) {w : ℂ} (hw : w.im ≠ 0) :
    (σ (s 0) : ℂ) * w + (σ (s 1) : ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  simp [hw] at h1
  rw [h1] at h
  simp at h
  exact hs (funext fun i => by fin_cases i <;> simp [h1, h])

private theorem arch_le {σ : F →+* ℝ} {N : ℕ} (hN : N ≠ 0) {C : ℝ} (hC : 0 < C) {s : Fin 2 → F} (hs : s ≠ 0)
    {w : ℂ} (hw : w.im ≠ 0) (hb : ‖(σ (s 0) : ℂ) * w + (σ (s 1) : ℂ)‖ ^ 2 ≤ C * |w.im|) :
    1 / ((N : ℝ) ^ 2 * C) ≤ |w.im| / ‖(σ (((N : F) • s) 0) : ℂ) * w + (σ (((N : F) • s) 1) : ℂ)‖ ^ 2 := by
  have e : (σ (((N : F) • s) 0) : ℂ) * w + (σ (((N : F) • s) 1) : ℂ) = (N : ℂ) * ((σ (s 0) : ℂ) * w + (σ (s 1) : ℂ)) := by
    simp [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]; ring
  have hY := row_ne (σ := σ) hs hw
  have hY2 : 0 < ‖(σ (s 0) : ℂ) * w + (σ (s 1) : ℂ)‖ ^ 2 := by positivity
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  rw [e, norm_mul, mul_pow, Complex.norm_natCast, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hb hN2.le]

private theorem fin_min {α : Type} (S : Finset α) (f : α → ℝ) (hf : ∀ a, 0 < f a) : ∃ c : ℝ, 0 < c ∧ ∀ a ∈ S, c ≤ f a := by
  by_cases hS : S.Nonempty
  · obtain ⟨a, -, ha⟩ := S.exists_min_image f hS
    exact ⟨f a, hf a, ha⟩
  · exact ⟨1, one_pos, fun a ha => absurd ⟨a, ha⟩ hS⟩

private theorem nF_le (hMem : AMem) (hMono : AMono) (hRow : ARow) [NumberField F] {x : GF F} {N : ℕ}
    (hNx : ∀ i j, (N : Af F) * x.val i j ∈ Ohat F) {s0 : Fin 2 → F} (hint : ∀ i, IsIntegral ℤ (s0 i))
    (hs : (N : F) • s0 ≠ 0) : nF ((N : F) • s0) x ≤ 1 := by
  obtain ⟨t, k, hk, hrow⟩ := (hRow F ((N : F) • s0) x).1 hs
  rw [(hRow F _ x).2 t k hk hrow]
  have hM := hMem F
  have hmem : ∀ i, rowF ((N : F) • s0) x i ∈ Ohat F := fun i => by
    simp only [rowF, Matrix.vecMul, dotProduct]
    refine Subring.sum_mem _ fun j _ => ?_
    have e : algebraMap F (Af F) (((N : F) • s0) j) * x.val j i = algebraMap F (Af F) (s0 j) * ((N : Af F) * x.val j i) := by
      rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]; ring
    rw [e]
    exact Subring.mul_mem _ ((hM.2.2.2.2.2.1 (s0 j)).1 (hint j)) (hNx j i)
  calc absF t ≤ absF 1 := hMono F t 1 (fun w => by
        have hv : ∀ i, Valued.v (pLoc F w (rowF ((N : F) • s0) x i)) ≤ 1 := fun i => (hM.2.1 _).1 (hmem i) w
        obtain ⟨-, hmax⟩ := hM.2.2.2.2.1 k hk w
        rw [Units.val_one, map_one, map_one]
        rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with h | h <;> rw [h] at hmax
        · have := hv 0
          rwa [hrow 0, map_mul, map_mul, hmax, mul_one] at this
        · have := hv 1
          rwa [hrow 1, map_mul, map_mul, hmax, mul_one] at this)
    _ = 1 := by simp [absF]

private theorem exists_height_lower_bound (hMem : AMem) (hMono : AMono) (hRow : ARow) (hMink : AMink) (hHt : DHt) (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (c : Pl F → ℕ) (hc : {w | c w ≠ 0}.Finite) (χ : Hc c →* ℂˣ) (x : GF F) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ z : X (InfinitePlace F), ∃ s, s ≠ 0 ∧ c₀ ≤ (mkDat c χ).Ht s z x := by
  obtain ⟨C, hC, hmink⟩ := hMink F
  obtain ⟨N, hN, hNx⟩ := (hMem F).2.2.2.2.2.2.1 x
  have hpos : ∀ s : Fin 2 → F, s ≠ 0 → 0 < absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 :=
    fun s hs => (hHt F c hc χ).1 s hs x
  have ha : 0 < absF (Matrix.GeneralLinearGroup.det x) := by
    by_contra h
    replace h := not_lt.1 h
    exact (hpos ![1, 0] (by intro h; simpa using congrFun h 0)).not_ge (div_nonpos_of_nonpos_of_nonneg h (sq_nonneg _))
  refine ⟨absF (Matrix.GeneralLinearGroup.det x) * (1 / ((N : ℝ) ^ 2 * C)) ^ Fintype.card (InfinitePlace F), by positivity,
    fun z => ?_⟩
  obtain ⟨s0, hs0, hint, hb⟩ := hmink (fun v => (z v).1) (fun v => (z v).2)
  have hs : (N : F) • s0 ≠ 0 := smul_ne_zero (Nat.cast_ne_zero.2 hN) hs0
  refine ⟨_, hs, ?_⟩
  have hn := nF_le hMem hMono hRow hNx hint hs
  have hn0 : 0 ≤ nF ((N : F) • s0) x := finprod_nonneg fun w => (norm_nonneg _).trans (le_max_left _ _)
  have hp := hpos _ hs
  have hfin : absF (Matrix.GeneralLinearGroup.det x) ≤ absF (Matrix.GeneralLinearGroup.det x) / nF ((N : F) • s0) x ^ 2 := by
    have h2 : 0 < nF ((N : F) • s0) x ^ 2 := by
      rcases (pow_nonneg hn0 2).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at hp; exact absurd hp (lt_irrefl 0)
    rw [le_div_iff₀ h2]
    nlinarith [pow_le_one₀ hn0 hn (n := 2)]
  have harch : (1 / ((N : ℝ) ^ 2 * C)) ^ Fintype.card (InfinitePlace F) ≤ ∏ v, |(z v).1.im| /
      ‖((mkDat c χ).σ v (((N : F) • s0) 0) : ℂ) * (z v).1 + ((mkDat c χ).σ v (((N : F) • s0) 1) : ℂ)‖ ^ 2 := by
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun v _ => arch_le hN hC hs0 (z v).2 (hb v)
  have hm := mul_le_mul harch hfin ha.le (Finset.prod_nonneg fun _ _ => by positivity)
  unfold Dat.Ht
  change _ ≤ _ * (absF (Matrix.GeneralLinearGroup.det x) / nF ((N : F) • s0) x ^ 2)
  linarith

end UpperTheory.Esk.MinkowskiHeightLemmas

open UpperTheory.Esk.MinkowskiHeightLemmas in
theorem UpperTheory.Esk.dMink : UpperTheory.Esk.AMem → UpperTheory.Esk.AMono → UpperTheory.Esk.ARow → UpperTheory.Esk.ABnfH → UpperTheory.Esk.AMink → UpperTheory.Esk.DHt → UpperTheory.Esk.DMul → UpperTheory.Esk.DMink := by
  intro hMem hMono hRow hBnfH hMink hHt hMul F _ _ _ c hc χ
  obtain ⟨S, hS⟩ := hBnfH F c hc
  choose cf hcf hcz using fun x => exists_height_lower_bound hMem hMono hRow hMink hHt F c hc χ x
  obtain ⟨c₀, hc₀, hle⟩ := fin_min S cf hcf
  refine ⟨c₀, hc₀, fun z x => ?_⟩
  obtain ⟨b, -, x', hx', h, hh, e⟩ := hS x
  obtain ⟨s', hs', hs'le⟩ := hcz x' ((mkDat c χ).act b z)
  refine ⟨s' ᵥ* b.val, ?_, ?_⟩
  · intro h0
    apply hs'
    have := congrArg (· ᵥ* (b⁻¹ : GL (Fin 2) F).val) h0
    simpa [Matrix.vecMul_vecMul] using this
  · rw [ht_act _ _ _ _ _ ((hHt F c hc χ).2.1 s' hs' b x)]
    have ej : (mkDat c χ).j b * x = x' * h := e
    have hH : h ∈ (mkDat c χ).H := Subgroup.mem_sup_left hh
    have hl := (hMul F c hc χ).1 s' hs' x' h hH
    rw [ej]
    unfold Dat.Ht at hs'le ⊢
    rw [hl]
    exact (hle x' hx').trans hs'le
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DEntryP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.MatrixEntryBounds

theorem abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]

theorem abs_le_of_sq (t s : ℝ) (hs : 0 ≤ s) (h : t ^ 2 ≤ s ^ 2) : |t| ≤ s := by
  have := sq_le_sq.1 h
  rwa [abs_of_nonneg hs] at this

theorem core (δ C c0 x y x' y' a b c d M L R K : ℝ) (hδ : 0 < δ) (hc0 : 0 < c0) (hx : |x| ≤ C)
    (hy : c0 ≤ |y|) (hdet : |a * d - b * c| ≤ C) (hM : M * δ = 4 * C) (hL : L * c0 ^ 2 = M)
    (hR : R * c0 = C) (hK : K * (c0 ^ 2 * δ ^ 2) = 2 * C ^ 2 * δ ^ 2 + 48 * c0 ^ 2)
    (hyy : 0 < y * y') (hk : δ * ((x - x') ^ 2 + (y + y') ^ 2) ≤ 4 * (y * y'))
    (hden : y' * ((c * x + d) ^ 2 + (c * y) ^ 2) = (a * d - b * c) * y)
    (hre : x' * (c * x + d) - y' * (c * y) = a * x + b)
    (him : x' * (c * y) + y' * (c * x + d) = a * y) :
    |c| ≤ 1 + L ∧ |d| ≤ 1 + M + (1 + L) * C ∧ |a| ≤ 1 + K * M ∧ |b| ≤ (1 + K * M) * (1 + R) * |y| := by
  have hC : 0 ≤ C := (abs_nonneg x).trans hx
  have hy0 : 0 < |y| := hc0.trans_le hy
  have hy'0 : y' ≠ 0 := right_ne_zero_of_mul hyy.ne'
  have hay' : 0 < |y'| := abs_pos.2 hy'0
  have hyy' : y * y' = |y| * |y'| := by rw [← abs_mul, abs_of_pos hyy]
  have h1 : δ * y ^ 2 ≤ 4 * (y * y') := by
    linarith [mul_nonneg hδ.le (sq_nonneg (x - x')), mul_nonneg hδ.le (sq_nonneg y'), mul_pos hδ hyy]
  have h2 : δ * y' ^ 2 ≤ 4 * (y * y') := by
    linarith [mul_nonneg hδ.le (sq_nonneg (x - x')), mul_nonneg hδ.le (sq_nonneg y), mul_pos hδ hyy]
  have h3 : δ * (x - x') ^ 2 ≤ 4 * (y * y') := by
    linarith [mul_nonneg hδ.le (sq_nonneg y'), mul_nonneg hδ.le (sq_nonneg y), mul_pos hδ hyy]
  set N := (c * x + d) ^ 2 + (c * y) ^ 2 with hN
  have e : (y * y') * (δ * N) = (a * d - b * c) * (δ * y ^ 2) := by linear_combination (δ * y) * hden
  have e2 : (a * d - b * c) * (δ * y ^ 2) ≤ C * (4 * (y * y')) := by
    calc (a * d - b * c) * (δ * y ^ 2) ≤ |a * d - b * c| * (δ * y ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ C * (δ * y ^ 2) := mul_le_mul_of_nonneg_right hdet (by positivity)
      _ ≤ C * (4 * (y * y')) := mul_le_mul_of_nonneg_left h1 hC
  have hδN : δ * N ≤ 4 * C := le_of_mul_le_mul_left (by linarith [e, e2]) hyy
  have hNM : N ≤ M := le_of_mul_le_mul_right (by linarith [hδN, hM]) hδ
  have hN0 : 0 ≤ N := by positivity
  have hcy : (c * y) ^ 2 ≤ M := by linarith [sq_nonneg (c * x + d)]
  have hcxd : (c * x + d) ^ 2 ≤ M := by linarith [sq_nonneg (c * y)]
  have hc0y : c0 ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ hc0.le hy 2
  have hc2 : c ^ 2 ≤ L := by
    have : c ^ 2 * c0 ^ 2 ≤ L * c0 ^ 2 := by
      rw [hL]; linarith [mul_le_mul_of_nonneg_left hc0y (sq_nonneg c)]
    exact le_of_mul_le_mul_right this (by positivity)
  have hc : |c| ≤ 1 + L := (abs_le_one_add_sq c).trans (by linarith)
  have hcxd' : |c * x + d| ≤ 1 + M := (abs_le_one_add_sq _).trans (by linarith)
  have hcx : |c * x| ≤ (1 + L) * C := by
    rw [abs_mul]; exact mul_le_mul hc hx (abs_nonneg _) ((abs_nonneg c).trans hc)
  have hd : |d| ≤ 1 + M + (1 + L) * C := by
    have a1 := abs_le.1 hcxd'
    have a2 := abs_le.1 hcx
    exact abs_le.2 ⟨by linarith [a1.1, a2.2], by linarith [a1.2, a2.1]⟩

  have hy' : δ * |y'| ≤ 4 * |y| := by
    have : |y'| * (δ * |y'|) ≤ |y'| * (4 * |y|) := by
      calc |y'| * (δ * |y'|) = δ * y' ^ 2 := by rw [← sq_abs y']; ring
        _ ≤ 4 * (y * y') := h2
        _ = |y'| * (4 * |y|) := by rw [hyy']; ring
    exact le_of_mul_le_mul_left this hay'
  have A2 : δ ^ 2 * y' ^ 2 ≤ 16 * y ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hy' 2
    rw [mul_pow, mul_pow, sq_abs, sq_abs] at this
    linarith
  have A1 : δ ^ 2 * (x - x') ^ 2 ≤ 16 * y ^ 2 := by
    have h4 : δ * (δ * (x - x') ^ 2) ≤ δ * (4 * (y * y')) := mul_le_mul_of_nonneg_left h3 hδ.le
    have h5 : δ * (4 * (y * y')) ≤ 16 * y ^ 2 := by
      rw [hyy']
      linarith [mul_le_mul_of_nonneg_left hy' (abs_nonneg y), sq_abs y]
    linarith
  have A3 : c0 ^ 2 * x ^ 2 ≤ C ^ 2 * y ^ 2 := by
    have hx2 : x ^ 2 ≤ C ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    have := mul_le_mul hc0y hx2 (sq_nonneg _) (sq_nonneg _)
    linarith
  have hW : x' ^ 2 + y' ^ 2 ≤ K * y ^ 2 := by
    have hp : 0 < c0 ^ 2 * δ ^ 2 := by positivity
    refine le_of_mul_le_mul_right ?_ hp
    have : K * y ^ 2 * (c0 ^ 2 * δ ^ 2) = (2 * C ^ 2 * δ ^ 2 + 48 * c0 ^ 2) * y ^ 2 := by rw [← hK]; ring
    rw [this]
    linarith [mul_le_mul_of_nonneg_left A1 (sq_nonneg c0), mul_le_mul_of_nonneg_left A2 (sq_nonneg c0),
      mul_le_mul_of_nonneg_left A3 (sq_nonneg δ), mul_nonneg (sq_nonneg (c0 * δ)) (sq_nonneg (2 * x - x'))]
  have E : (a * x + b) ^ 2 + (a * y) ^ 2 = (x' ^ 2 + y' ^ 2) * N := by rw [hN, ← hre, ← him]; ring
  have hKM : (x' ^ 2 + y' ^ 2) * N ≤ K * y ^ 2 * M :=
    mul_le_mul hW hNM hN0 ((add_nonneg (sq_nonneg _) (sq_nonneg _)).trans hW)
  have hy2 : 0 < y ^ 2 := by rw [← sq_abs]; positivity
  have hKM0 : 0 ≤ K * M := by
    have : 0 ≤ K * M * y ^ 2 := by linarith [sq_nonneg (a * x + b), sq_nonneg (a * y)]
    exact nonneg_of_mul_nonneg_left this hy2
  have ha2 : a ^ 2 ≤ K * M := by
    have : a ^ 2 * y ^ 2 ≤ K * M * y ^ 2 := by linarith [sq_nonneg (a * x + b)]
    exact le_of_mul_le_mul_right this hy2
  have ha : |a| ≤ 1 + K * M := (abs_le_one_add_sq a).trans (by linarith)
  have hb1 : |a * x + b| ≤ (1 + K * M) * |y| := by
    apply abs_le_of_sq _ _ (by positivity)
    rw [mul_pow, sq_abs]
    linarith [sq_nonneg (a * y), mul_le_mul_of_nonneg_right (show K * M ≤ (1 + K * M) ^ 2 by linarith [sq_nonneg (K * M)])
      (sq_nonneg y)]
  have hR0 : 0 ≤ R := by
    by_contra h
    have := mul_neg_of_neg_of_pos (not_le.1 h) hc0
    linarith
  have hxR : |x| ≤ R * |y| := hx.trans (by rw [← hR]; exact mul_le_mul_of_nonneg_left hy hR0)
  have hax : |a * x| ≤ (1 + K * M) * (R * |y|) := by
    rw [abs_mul]; exact mul_le_mul ha hxR (abs_nonneg _) (by linarith)
  refine ⟨hc, hd, ha, ?_⟩
  have b1 := abs_le.1 hb1
  have b2 := abs_le.1 hax
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [b1.1, b1.2, b2.1, b2.2]

end UpperTheory.Esk.MatrixEntryBounds

namespace UpperTheory.Esk.MatrixEntryBounds

theorem main : ∀ δ C c : ℝ, 0 < δ → 0 < c → ∃ B : ℝ, ∀ (g : GL (Fin 2) ℝ) (z : P), |z.1.re| ≤ C → c ≤ |z.1.im| →
    |g.val.det| ≤ C → δ ≤ kap z (g • z) → |g 1 0| ≤ B ∧ |g 0 0| ≤ B ∧ |g 1 1| ≤ B ∧ |g 0 1| ≤ B * |z.1.im| := by
  intro δ C c0 hδ hc0
  have hM : (4 * C / δ) * δ = 4 * C := div_mul_cancel₀ _ hδ.ne'
  have hL : (4 * C / δ / c0 ^ 2) * c0 ^ 2 = 4 * C / δ := div_mul_cancel₀ _ (by positivity)
  have hR : (C / c0) * c0 = C := div_mul_cancel₀ _ hc0.ne'
  have hK : (2 * C ^ 2 / c0 ^ 2 + 48 / δ ^ 2) * (c0 ^ 2 * δ ^ 2) = 2 * C ^ 2 * δ ^ 2 + 48 * c0 ^ 2 := by
    field_simp
  refine ⟨max (max (1 + 4 * C / δ / c0 ^ 2) (1 + 4 * C / δ + (1 + 4 * C / δ / c0 ^ 2) * C))
    (max (1 + (2 * C ^ 2 / c0 ^ 2 + 48 / δ ^ 2) * (4 * C / δ))
      ((1 + (2 * C ^ 2 / c0 ^ 2 + 48 / δ ^ 2) * (4 * C / δ)) * (1 + C / c0))), ?_⟩
  intro g z hx hy hdet hk
  unfold kap at hk
  split_ifs at hk with hyy
  swap
  · exact absurd hk (not_le.2 hδ)
  have hn : ‖z.1 - (starRingEnd ℂ) (g • z).1‖ ^ 2 = (z.1.re - (g • z).1.re) ^ 2 + (z.1.im + (g • z).1.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hpos : 0 < (z.1.re - (g • z).1.re) ^ 2 + (z.1.im + (g • z).1.im) ^ 2 := by
    nlinarith [sq_nonneg (z.1.re - (g • z).1.re), sq_nonneg (z.1.im - (g • z).1.im)]
  rw [hn, le_div_iff₀ hpos] at hk
  have hns : Complex.normSq (den g z.1) = (g 1 0 * z.1.re + g 1 1) ^ 2 + (g 1 0 * z.1.im) ^ 2 := by
    rw [Complex.normSq_apply]; simp [den]; ring
  have hne : Complex.normSq (den g z.1) ≠ 0 := (Complex.normSq_pos.2 (den_ne g z.2)).ne'
  have hden : (g • z).1.im * ((g 1 0 * z.1.re + g 1 1) ^ 2 + (g 1 0 * z.1.im) ^ 2) =
      (g 0 0 * g 1 1 - g 0 1 * g 1 0) * z.1.im := by
    rw [← hns, coe_smul, im_div, det_eq, div_mul_cancel₀ _ hne]
  have hW : (g • z).1 * den g z.1 = num g z.1 := by rw [coe_smul, div_mul_cancel₀ _ (den_ne g z.2)]
  have hre := congrArg Complex.re hW
  have him := congrArg Complex.im hW
  simp [num, den, Complex.mul_re, Complex.mul_im] at hre him
  obtain ⟨h1, h2, h3, h4⟩ := core δ C c0 z.1.re z.1.im (g • z).1.re (g • z).1.im (g 0 0) (g 0 1) (g 1 0) (g 1 1)
    _ _ _ _ hδ hc0 hx hy (by rwa [det_eq] at hdet) hM hL hR hK hyy hk hden
    (by linear_combination hre) (by linear_combination him)
  refine ⟨h1.trans ((le_max_left _ _).trans (le_max_left _ _)), h3.trans ((le_max_left _ _).trans (le_max_right _ _)),
    h2.trans ((le_max_right _ _).trans (le_max_left _ _)),
    h4.trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (abs_nonneg _))⟩

end UpperTheory.Esk.MatrixEntryBounds

theorem UpperTheory.Esk.dEntry : UpperTheory.Esk.DEntry := UpperTheory.Esk.MatrixEntryBounds.main
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.IntegralTransvectionMemSlIntegersConjugateZero
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CompactSubgroupMembership

variable {F : Type} [Field F] [NumberField F]

def mP (w : Pl F) (c : ℕ) : AddSubgroup (w.adicCompletion F) :=
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c).toAddSubgroup.map
    (w.adicCompletionIntegers F).subtype.toAddMonoidHom

theorem mem_parahoricTimesPrincipalCongruence_iff {w : Pl F} {c : ℕ} {g : GL (Fin 2) (w.adicCompletion F)} :
    g ∈ K1 w c ↔ (∀ a b, g a b ∈ w.adicCompletionIntegers F) ∧
      (∀ a b, (g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b ∈ w.adicCompletionIntegers F) ∧
      g 1 0 ∈ mP w c ∧ g 1 1 - 1 ∈ mP w c := by
  have key : ∀ k : GL (Fin 2) (w.adicCompletionIntegers F),
      k ∈ ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)))) ↔
      k 1 0 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ∧
        k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c := fun k => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq, map_one]
    change ![0, 1] ᵥ* _ = ![0, 1] ↔ _
    rw [funext_iff, Fin.forall_fin_two]
    simp [Matrix.vecMul, dotProduct]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := (key k).1 hk
    refine ⟨fun a b => (k a b).2, fun a b => ?_, ⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
    rw [← map_inv]; exact ((k⁻¹ : GL (Fin 2) (w.adicCompletionIntegers F)) a b).2
  · rintro ⟨ha, hb, ⟨y, hy, e⟩, ⟨y', hy', e'⟩⟩
    have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) (w.adicCompletionIntegers F).subtype) := fun x y h =>
      Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
    let k : GL (Fin 2) (w.adicCompletionIntegers F) :=
      ⟨Matrix.of fun a b => ⟨g a b, ha a b⟩, Matrix.of fun a b => ⟨(g⁻¹ : GL (Fin 2) (w.adicCompletion F)) a b, hb a b⟩,
        inj (by rw [map_mul, map_one]; exact g.mul_inv), inj (by rw [map_mul, map_one]; exact g.inv_mul)⟩
    refine ⟨k, (key k).2 ⟨?_, ?_⟩, Units.ext rfl⟩
    · rw [show k 1 0 = y from Subtype.ext e.symm]; exact hy
    · rw [show k 1 1 - 1 = y' from Subtype.ext e'.symm]; exact hy'

theorem mem_mP_zero {w : Pl F} {x : w.adicCompletion F} (hx : x ∈ w.adicCompletionIntegers F) : x ∈ mP w 0 :=
  ⟨⟨x, hx⟩, by simp, rfl⟩

theorem mem_O {x : Af F} : x ∈ Ohat F ↔ ∀ w : Pl F, pLoc F w x ∈ w.adicCompletionIntegers F := by
  simp [Ohat, Subring.mem_iInf]

theorem mem_Ov {x : Af F} : x ∈ Ohat F ↔ ∀ w : Pl F, Valued.v (pLoc F w x) ≤ 1 := by
  rw [mem_O]; simp only [HeightOneSpectrum.mem_adicCompletionIntegers]

theorem v_le {x : Af F} (hx : x ∈ Ohat F) (w : Pl F) : Valued.v (pLoc F w x) ≤ 1 := mem_Ov.1 hx w

theorem integral_transvection_mem_slIntegers_conjugate_zero {g : GF F} :
    g ∈ K0 F ↔ (∀ i j, g.val i j ∈ Ohat F) ∧ ∀ i j, (g⁻¹ : GF F).val i j ∈ Ohat F := by
  simp only [K0, Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv, mem_O]
  constructor
  · intro h
    exact ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2.1 i j⟩
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w, mem_mP_zero (h1 1 0 w),
      mem_mP_zero (sub_mem (h1 1 1 w) (one_mem _))⟩

theorem Kc_le (c : Pl F → ℕ) : Kc c ≤ K0 F := fun g hg => by
  rw [integral_transvection_mem_slIntegers_conjugate_zero]
  simp only [Kc, Subgroup.mem_iInf, Subgroup.mem_comap, mem_parahoricTimesPrincipalCongruence_iff, ← map_inv] at hg
  exact ⟨fun i j => mem_O.2 fun w => (hg w).1 i j, fun i j => mem_O.2 fun w => (hg w).2.1 i j⟩

theorem zc_normal : ((zc F).range).Normal :=
  ⟨fun n hn g => by
    obtain ⟨z, rfl⟩ := hn
    have := Subgroup.mem_center_iff.1 (zc_center z) g
    exact ⟨z, by rw [this, mul_inv_cancel_right]⟩⟩

theorem mem_Hc (c : Pl F → ℕ) (h : GF F) : h ∈ Hc c ↔ ∃ k ∈ Kc c, ∃ z, h = k * zc F z := by
  have := zc_normal (F := F)
  change h ∈ Kc c ⊔ (zc F).range ↔ _
  rw [Subgroup.mem_sup_of_normal_right]
  constructor
  · rintro ⟨k, hk, _, ⟨z, rfl⟩, rfl⟩
    exact ⟨k, hk, z, rfl⟩
  · rintro ⟨k, hk, z, rfl⟩
    exact ⟨k, hk, _, ⟨z, rfl⟩, rfl⟩

theorem det_mem {g : GF F} (h : ∀ i j, g.val i j ∈ Ohat F) : g.val.det ∈ Ohat F := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

theorem k_prop {k : GF F} (hk : k ∈ K0 F) (w : Pl F) :
    Valued.v (pLoc F w ((Matrix.GeneralLinearGroup.det k : (Af F)ˣ) : Af F)) = 1 ∧
      max (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) = 1 := by
  obtain ⟨h1, h2⟩ := integral_transvection_mem_slIntegers_conjugate_zero.1 hk
  refine ⟨?_, ?_⟩
  · have hd2 := v_le (det_mem h2) w
    have hdd : k.val.det * (k⁻¹ : GF F).val.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have e1 : Valued.v (pLoc F w k.val.det) * Valued.v (pLoc F w (k⁻¹ : GF F).val.det) = 1 := by
      rw [← map_mul, ← map_mul, hdd, map_one, map_one]
    change Valued.v (pLoc F w k.val.det) = 1
    exact le_antisymm (v_le (det_mem h1) w) (e1 ▸ mul_le_of_le_one_right' hd2)
  · have e : k.val 1 0 * (k⁻¹ : GF F).val 0 1 + k.val 1 1 * (k⁻¹ : GF F).val 1 1 = 1 := by
      have := congrFun (congrFun (Units.mul_inv k) 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at this
      exact this
    have hv : Valued.v (pLoc F w (k.val 1 0) * pLoc F w ((k⁻¹ : GF F).val 0 1) +
        pLoc F w (k.val 1 1) * pLoc F w ((k⁻¹ : GF F).val 1 1)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_add (f := _), e, map_one, map_one]
    refine le_antisymm (max_le (v_le (h1 1 0) w) (v_le (h1 1 1) w)) ?_
    refine hv.ge.trans ((Valuation.map_add _ _ _).trans (max_le_max ?_ ?_))
    · rw [map_mul]; exact mul_le_of_le_one_right' (v_le (h2 0 1) w)
    · rw [map_mul]; exact mul_le_of_le_one_right' (v_le (h2 1 1) w)

theorem val_pLoc (w : Pl F) (x : F) :
    Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem int_iff (t : F) : IsIntegral ℤ t ↔ algebraMap F (Af F) t ∈ Ohat F := by
  rw [mem_Ov]
  simp only [val_pLoc]
  constructor
  · intro h w
    exact HeightOneSpectrum.valuation_le_one w (⟨t, h⟩ : 𝓞 F)
  · intro h
    obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F t h
    exact RingOfIntegers.isIntegral_coe r

theorem af_den (a : Af F) : ∃ n : ℕ, n ≠ 0 ∧ (n : Af F) * a ∈ Ohat F := by
  have hU : IsOpen {z : Af F | a - z ∈ Ohat F} :=
    isOpen_Ohat.preimage (f := fun z : Af F => a - z) (by fun_prop)
  obtain ⟨x, hx⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).exists_mem_open hU
    ⟨a, by simp⟩
  obtain ⟨m, hm0, hm⟩ :=
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  have h1 : algebraMap F (Af F) (m • x) ∈ Ohat F :=
    mem_Ohat.2 (GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles F ⟨_, hm⟩)
  have h2 := add_mem h1 (mul_mem (intCast_mem (Ohat F) m) hx)
  have h3 : (m : Af F) * a ∈ Ohat F := by
    convert h2 using 1
    rw [zsmul_eq_mul, map_mul, map_intCast]; ring
  rcases Int.natAbs_eq m with h | h
  · rw [h] at h3; simpa using h3
  · rw [h] at h3; simpa using neg_mem h3

theorem den_ex (g : GF F) : ∃ N : ℕ, N ≠ 0 ∧ ∀ i j, (N : Af F) * g.val i j ∈ Ohat F := by
  choose n hn0 hn using fun p : Fin 2 × Fin 2 => af_den (g.val p.1 p.2)
  refine ⟨∏ p, n p, Finset.prod_ne_zero_iff.2 fun p _ => hn0 p, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (i, j))
  rw [hk, Nat.cast_mul, mul_comm ((n (i, j) : ℕ) : Af F), mul_assoc]
  exact mul_mem (natCast_mem _ k) (hn (i, j))

theorem unit_scalar_mem_maximal_compact {u : (Af F)ˣ} (hu : ∀ w : Pl F, Valued.v (pLoc F w (u : Af F)) = 1) :
    zc F u ∈ K0 F ∧ ∀ t ∈ Ohat F, aff u t ∈ K0 F := by
  have hu1 : (u : Af F) ∈ Ohat F := mem_Ov.2 fun w => (hu w).le
  have hu2 : ((u⁻¹ : (Af F)ˣ) : Af F) ∈ Ohat F := by
    refine mem_Ov.2 fun w => ?_
    have : Valued.v (pLoc F w (u : Af F)) * Valued.v (pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [hu w, one_mul] at this
    exact this.le
  refine ⟨integral_transvection_mem_slIntegers_conjugate_zero.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun t ht => integral_transvection_mem_slIntegers_conjugate_zero.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · fin_cases i <;> fin_cases j <;> simp [zc, hu1]
  · rw [show (zc F u)⁻¹ = zc F u⁻¹ from (map_inv (zc F) u).symm]
    fin_cases i <;> fin_cases j <;> simp [-map_inv, zc, hu2]
  · change (!![(u : Af F), t; 0, 1] : Matrix (Fin 2) (Fin 2) (Af F)) i j ∈ Ohat F
    fin_cases i <;> fin_cases j <;> simp [hu1, ht]
  · change (!![((u⁻¹ : (Af F)ˣ) : Af F), -(((u⁻¹ : (Af F)ˣ) : Af F) * t); 0, 1] : Matrix (Fin 2) (Fin 2) (Af F)) i j ∈
      Ohat F
    fin_cases i <;> fin_cases j <;> simp [hu2, mul_mem hu2 ht]

end UpperTheory.Esk.CompactSubgroupMembership

open UpperTheory.Esk.CompactSubgroupMembership in
theorem UpperTheory.Esk.aMem : UpperTheory.Esk.AMem := by
  intro F _ _
  exact ⟨fun g => integral_transvection_mem_slIntegers_conjugate_zero, fun x => mem_Ov, Kc_le, mem_Hc, fun k hk w => k_prop hk w, int_iff, den_ex,
    fun u hu => unit_scalar_mem_maximal_compact hu⟩
end
end
