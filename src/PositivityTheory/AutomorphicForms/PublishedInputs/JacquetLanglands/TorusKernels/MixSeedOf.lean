module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FinalH
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DCount
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementE

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfGTerm
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ValuationDetCongruenceSubgroupEqOne
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.adelicTermLemmas

variable {F : Type} [Field F] [NumberField F]

theorem hc_decomp {c : Pl F → ℕ} {h : GF F} (hh : h ∈ Hc c) : ∃ k ∈ Kc c, ∃ z, h = k * zc F z := by
  have hN : (zc F).range.Normal := ⟨fun n hn g => by
    obtain ⟨z, rfl⟩ := hn
    refine ⟨z, ?_⟩
    rw [(Subgroup.mem_center_iff.1 (zc_center z) g), mul_assoc, mul_inv_cancel, mul_one]⟩
  have h2 : h ∈ ((Kc c ⊔ (zc F).range : Subgroup (GF F)) : Set (GF F)) := hh
  rw [Subgroup.mul_normal] at h2
  obtain ⟨k, hk, y, ⟨z, rfl⟩, rfl⟩ := h2
  exact ⟨k, hk, z, rfl⟩

theorem valuation_det_congruence_subgroup_eq_one (w : Pl F) (n : ℕ) {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w n) :
    Valued.v (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)).det = 1 := by
  obtain ⟨k, -, rfl⟩ := hg
  have hu : IsUnit (k : Matrix (Fin 2) (Fin 2) (w.adicCompletionIntegers F)).det :=
    (Matrix.GeneralLinearGroup.det k).isUnit
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hu
  rw [← hu]
  exact congrArg Valued.v ((w.adicCompletionIntegers F).subtype.map_det _).symm

theorem mem_local_congruence_of_mem_global {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) (w : Pl F) :
    Matrix.GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := by
  have := Subgroup.mem_iInf.1 hk w
  exact this

theorem list_prod_inv {α : Type*} (W : List α) (f : α → ℝ) : (W.map fun w => (f w)⁻¹).prod = ((W.map f).prod)⁻¹ := by
  induction W with
  | nil => simp
  | cons w W ih => simp [ih, mul_comm]

theorem det_zc (z : (Af F)ˣ) : Matrix.GeneralLinearGroup.det (zc F z) = z ^ 2 := by
  ext
  simp [zc, sq]

variable [IsTotallyReal F]

theorem absF_det_Kc {c : Pl F → ℕ} {k : GF F} (hk : k ∈ Kc c) : absF (Matrix.GeneralLinearGroup.det k) = 1 := by
  refine (Hm.absf F).2.2.1 _ fun w => ?_
  have h := valuation_det_congruence_subgroup_eq_one w (c w) (mem_local_congruence_of_mem_global hk w)
  rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  exact h

theorem prod_reAt {c : Pl F → ℕ} {W : List (Pl F)} {n : ℕ} {a : Fin n → GF F} (hR : IsReps c W a) {γ : GL (Fin 2) F}
    {x : GF F} {i : Fin n} {k : GF F} (hk : k ∈ Kc c) {z : (Af F)ˣ} (hrel : jF F γ * x * (k * zc F z) = x * a i) :
    ∏ v, |reAt v γ.val.det| = absF z ^ 2 * (W.map fun w => (normV w : ℝ)).prod := by
  have h1 := (Hm.absf F).2.2.2 (Matrix.GeneralLinearGroup.det γ)
  have h2 : Units.map (algebraMap F (Af F)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) =
      Matrix.GeneralLinearGroup.det (jF F γ) := by
    rw [jF, Matrix.GeneralLinearGroup.map_det]; rfl
  have h3 : Matrix.GeneralLinearGroup.det (jF F γ) * (Matrix.GeneralLinearGroup.det k * z ^ 2) =
      Matrix.GeneralLinearGroup.det (a i) := by
    have := congrArg Matrix.GeneralLinearGroup.det hrel
    simp only [map_mul, det_zc] at this
    have e : Matrix.GeneralLinearGroup.det x * (Matrix.GeneralLinearGroup.det (jF F γ) * (Matrix.GeneralLinearGroup.det k * z ^ 2)) =
        Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det (a i) := by
      rw [← this, ← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm (Matrix.GeneralLinearGroup.det x)]
    exact mul_left_cancel e
  have h4 := congrArg absF h3
  rw [(Hm.absf F).2.1, (Hm.absf F).2.1, absF_det_Kc hk, pow_two, (Hm.absf F).2.1, hR.det i] at h4
  rw [list_prod_inv] at h4
  rw [h2] at h1
  have hp : 0 < absF (Matrix.GeneralLinearGroup.det (jF F γ)) := (Hm.absf F).1 _
  have hz : 0 < absF z := (Hm.absf F).1 _
  have hN : (W.map fun w => (normV w : ℝ)).prod ≠ 0 := by
    intro h0
    rw [h0, inv_zero] at h4
    have : 0 < absF (Matrix.GeneralLinearGroup.det (jF F γ)) * (1 * (absF z * absF z)) := by positivity
    linarith
  have e1 : (∏ v, |reAt v γ.val.det|) = (absF (Matrix.GeneralLinearGroup.det (jF F γ)))⁻¹ := by
    rw [Matrix.GeneralLinearGroup.val_det_apply] at h1
    exact eq_inv_of_mul_eq_one_left h1
  rw [e1]
  rw [one_mul] at h4
  field_simp
  have h5 : absF (Matrix.GeneralLinearGroup.det (jF F γ)) * (absF z * absF z) * (W.map fun w => (normV w : ℝ)).prod = 1 := by
    rw [h4, inv_mul_cancel₀ hN]
  nlinarith [h5]

theorem val_nat_le (ν : Valuation ℂ ℝ≥0) (m : ℕ) : ν (m : ℂ) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    exact (Valuation.map_add ν _ _).trans (max_le ih (by simp))

theorem tr_conj {R : Type*} [CommRing R] (g y : GL (Fin 2) R) :
    ((g * y * g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).trace = (y : Matrix (Fin 2) (Fin 2) R).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem det_conj2 {R : Type*} [CommRing R] (g y : GL (Fin 2) R) :
    ((g * y * g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = (y : Matrix (Fin 2) (Fin 2) R).det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
  congr 1
  simp

section Loc

variable {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι)

theorem nu_eq_one_iff (v : InfinitePlace F) (y : (D.pl v).adicCompletion F) : nu ι (D.em v y) = 1 ↔ Valued.v y = 1 := by
  constructor
  · intro h
    rcases lt_or_eq_of_le ((D.le v y).1 h.le) with h2 | h2
    · exact absurd ((D.lt v y).2 h2) (by rw [h]; exact lt_irrefl 1)
    · exact h2
  · intro h
    rcases lt_or_eq_of_le ((D.le v y).2 h.le) with h2 | h2
    · exact absurd ((D.lt v y).1 h2) (by rw [h]; exact lt_irrefl 1)
    · exact h2

theorem gl_apply (v : InfinitePlace F) (y : GF F) (p q : Fin 2) :
    (D.gl y v : Matrix (Fin 2) (Fin 2) ℂ) p q =
      D.em v ((↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) y) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)) p q) := rfl

theorem gl_zc (v : InfinitePlace F) (y : (Af F)ˣ) :
    (D.gl (zc F y) v : Matrix (Fin 2) (Fin 2) ℂ) = D.ea v y • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext p q
  rw [gl_apply]
  fin_cases p <;> fin_cases q <;> simp [zc, LDat.ea]

open Classical in
theorem loc (hU : GUnit) {c : Pl F → ℕ} (hc : ∀ v, c (D.pl v) = 1) {W : List (Pl F)} {r : ℕ} (hr : 1 ≤ r)
    (hW : ∀ v, r ≤ W.count (D.pl v)) {n : ℕ} {a : Fin n → GF F} (hR : IsReps c W a) {γ : GL (Fin 2) F} {x : GF F} {i : Fin n}
    {k : GF F} (hk : k ∈ Kc c) {z : (Af F)ˣ} (hrel : jF F γ = x * (a i * k⁻¹ * zc F z⁻¹) * x⁻¹) (v : InfinitePlace F) (N : ℕ) :
    ∃ τ δ U : ℂ, v.embedding γ.val.trace = (D.ea v z)⁻¹ * τ ∧ v.embedding γ.val.det = ((D.ea v z)⁻¹) ^ 2 * δ ∧
      nu ι τ ≤ 1 ∧ nu ι δ ≤ 1 ∧ nu ι δ ≤ nu ι l ^ r ∧ nu ι U ≤ 1 ∧ δ * U = (l : ℂ) ^ W.count (D.pl v) ∧
      ∀ t : ℕ, (l - 1) * l ^ N ∣ t → nu ι (τ ^ (2 * t) - 1) ≤ nu ι l ^ N ∧ nu ι (U ^ t - 1) ≤ nu ι l ^ N := by
  have hea : ∀ y : F, D.em v (pLoc F (D.pl v) (algebraMap F (Af F) y)) = v.embedding y := fun y => D.em_alg v y
  obtain ⟨hK, -⟩ := (glFacts F l ι D).1 c hc
  obtain ⟨hK0, hK1, hK2, -, -⟩ := hK k⁻¹ (inv_mem hk) v
  obtain ⟨u, hu⟩ := hR.loc i (D.pl v) (by rw [hc]; exact one_ne_zero)
  set M : Matrix (Fin 2) (Fin 2) ℂ := (D.gl (a i * k⁻¹) v : Matrix (Fin 2) (Fin 2) ℂ) with hM
  set T : (D.pl v).adicCompletion F := (↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) (a i * k⁻¹)) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).trace with hT
  set Δ : (D.pl v).adicCompletion F := (↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) (a i * k⁻¹)) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det with hΔ
  have hτT : M.trace = D.em v T := by
    rw [hM, hT, Matrix.trace_fin_two, Matrix.trace_fin_two, map_add (f := _), gl_apply, gl_apply]
  have hδΔ : M.det = D.em v Δ := by
    rw [hM, hΔ, Matrix.det_fin_two, Matrix.det_fin_two, gl_apply, gl_apply, gl_apply, gl_apply, map_sub, (D.em v).map_mul, (D.em v).map_mul]

  have hS : (D.gl (zc F z⁻¹) v : Matrix (Fin 2) (Fin 2) ℂ) = (D.ea v z)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [gl_zc, map_units_inv]
  have hj : D.gl (jF F γ) v = D.gl x v * (D.gl (a i * k⁻¹) v * D.gl (zc F z⁻¹) v) * (D.gl x v)⁻¹ := by
    rw [hrel]; simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply]
  have htr : v.embedding γ.val.trace = (D.ea v z)⁻¹ * M.trace := by
    have e1 : v.embedding γ.val.trace = (D.gl (jF F γ) v : Matrix (Fin 2) (Fin 2) ℂ).trace := by
      rw [Matrix.trace_fin_two, Matrix.trace_fin_two, map_add (f := _), gl_apply, gl_apply]
      simp only [jF, Matrix.GeneralLinearGroup.map_apply, ← hea]
    rw [e1, hj, tr_conj, Units.val_mul, hS, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  have hdt : v.embedding γ.val.det = ((D.ea v z)⁻¹) ^ 2 * M.det := by
    have e1 : v.embedding γ.val.det = (D.gl (jF F γ) v : Matrix (Fin 2) (Fin 2) ℂ).det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul, gl_apply, gl_apply, gl_apply, gl_apply]
      simp only [jF, Matrix.GeneralLinearGroup.map_apply, ← hea]
    rw [e1, hj, det_conj2, Units.val_mul, hS, Matrix.mul_smul, Matrix.mul_one, Matrix.det_smul, Fintype.card_fin]
  set cnt := W.count (D.pl v) with hcnt
  set e : ℂ := D.em v ((atFin (D.pl v) (unif (D.pl v)) : (D.pl v).adicCompletion F)) with he_def
  set K : Matrix (Fin 2) (Fin 2) ℂ := (D.gl k⁻¹ v : Matrix (Fin 2) (Fin 2) ℂ) with hK_def
  have hA : ∀ p q, (D.gl (a i) v : Matrix (Fin 2) (Fin 2) ℂ) p q = !![e ^ cnt, D.em v (u : (D.pl v).adicCompletion F); 0, 1] p q := by
    intro p q
    rw [gl_apply, hu]
    fin_cases p <;> fin_cases q <;> simp [aff, he_def, hcnt]
  have hMmul : M = (D.gl (a i) v : Matrix (Fin 2) (Fin 2) ℂ) * K := by
    rw [hM, hK_def, map_mul, Pi.mul_apply, Units.val_mul]
  have hτ' : M.trace = e ^ cnt * K 0 0 + D.em v (u : (D.pl v).adicCompletion F) * K 1 0 + K 1 1 := by
    rw [hMmul, Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hA]
    simp
  have hϖ : Valued.v ((atFin (D.pl v) (unif (D.pl v)) : (D.pl v).adicCompletion F)) = WithZero.exp (-1 : ℤ) :=
    Formalism.L2.Host.unif_spec _
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    have : WithZero.exp (-1 : ℤ) < WithZero.exp 0 := WithZero.exp_lt_exp.2 (by norm_num)
    simpa using this
  have he : nu ι e < 1 := (D.lt v _).2 (by rw [hϖ]; exact hexp)
  have hu1 : nu ι (D.em v (u : (D.pl v).adicCompletion F)) ≤ 1 := (D.le v _).2 u.2
  have hcnt1 : cnt ≠ 0 := by have := hW v; omega
  have hτ1 : nu ι M.trace = 1 := by
    have h1 : nu ι (M.trace - 1) < 1 := by
      have e1 : M.trace - 1 = e ^ cnt * K 0 0 + D.em v (u : (D.pl v).adicCompletion F) * K 1 0 + (K 1 1 - 1) := by
        rw [hτ']; ring
      rw [e1]
      refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ ?_) hK2
      · rw [map_mul, map_pow]
        calc nu ι e ^ cnt * nu ι (K 0 0) ≤ nu ι e ^ cnt * 1 := mul_le_mul_of_nonneg_left (hK0 0 0) zero_le
          _ = nu ι e ^ cnt := mul_one _
          _ < 1 := pow_lt_one₀ zero_le he hcnt1
      · rw [map_mul]
        calc nu ι (D.em v (u : (D.pl v).adicCompletion F)) * nu ι (K 1 0) ≤ 1 * nu ι (K 1 0) := mul_le_mul_of_nonneg_right hu1 zero_le
          _ = nu ι (K 1 0) := one_mul _
          _ < 1 := hK1
    have e2 : M.trace = 1 + (M.trace - 1) := by ring
    rw [e2]
    exact Valuation.map_one_add_of_lt _ h1
  have hTv : Valued.v T = 1 := (nu_eq_one_iff D v T).1 (hτT ▸ hτ1)
  have hΔmul : Δ = (↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) (a i)) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det *
      (↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) k⁻¹) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det := by
    rw [hΔ, map_mul, Units.val_mul, Matrix.det_mul]
  have hAdet : (↑(Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) (a i)) : Matrix (Fin 2) (Fin 2) ((D.pl v).adicCompletion F)).det =
      ((atFin (D.pl v) (unif (D.pl v)) : (D.pl v).adicCompletion F)) ^ cnt := by
    rw [hu]; simp [aff, Matrix.det_fin_two, hcnt]
  have hKdet := valuation_det_congruence_subgroup_eq_one (D.pl v) (c (D.pl v)) (mem_local_congruence_of_mem_global (inv_mem hk) (D.pl v))
  have hvΔ : Valued.v Δ = Valued.v (((l : ℕ) : (D.pl v).adicCompletion F)) ^ cnt := by
    rw [hΔmul, hAdet, map_mul, hKdet, map_pow, hϖ, D.unif v, mul_one]
  have hΔ0 : Δ ≠ 0 := by
    rw [hΔ]; exact (Matrix.GeneralLinearGroup.map (pLoc F (D.pl v)) (a i * k⁻¹)).det_ne_zero
  set Y : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) ^ cnt / Δ with hY_def
  have hY : Valued.v Y = 1 := by
    rw [hY_def, map_div₀, map_pow, hvΔ, div_self]
    exact pow_ne_zero _ (by rw [D.unif v]; exact WithZero.exp_ne_zero)
  have hUeq : D.em v Y = (l : ℂ) ^ cnt / D.em v Δ := by
    rw [hY_def, map_div₀, map_pow, map_natCast]
  have hδ0 : D.em v Δ ≠ 0 := (map_ne_zero (D.em v)).2 hΔ0
  have hδU : M.det * D.em v Y = (l : ℂ) ^ cnt := by
    rw [hδΔ, hUeq, mul_div_cancel₀ _ hδ0]
  have hU1 : nu ι (D.em v Y) = 1 := (nu_eq_one_iff D v Y).2 hY
  have hνδ : nu ι M.det = nu ι (l : ℂ) ^ cnt := by
    have := congrArg (nu ι) hδU
    rw [map_mul, hU1, mul_one, map_pow] at this
    exact this
  have hνl : nu ι (l : ℂ) ≤ 1 := val_nat_le _ l
  have hδr : nu ι M.det ≤ nu ι (l : ℂ) ^ r := by
    rw [hνδ]; exact pow_le_pow_of_le_one zero_le hνl (hW v)
  have hδ1 : nu ι M.det ≤ 1 := hδr.trans (pow_le_one₀ zero_le hνl)
  refine ⟨M.trace, M.det, D.em v Y, htr, hdt, hτ1.le, hδ1, hδr, hU1.le, hδU, fun t ht => ⟨?_, ?_⟩⟩
  · rw [hτT]; exact hU F l ι D v T hTv N (2 * t) (dvd_mul_of_dvd_right ht 2)
  · exact hU F l ι D v Y hY N t ht

end Loc

end UpperTheory.Esk.adelicTermLemmas
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ValNatCastLe
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.adelicTermLemmas

theorem ch_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) (n : ℕ) :
    f (ch a b n) = ch (f a) (f b) n := by
  have key : ∀ n, f (ch a b n) = ch (f a) (f b) n ∧ f (ch a b (n + 1)) = ch (f a) (f b) (n + 1) := by
    intro n
    induction n with
    | zero => simp [ch]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simp only [ch, map_sub, map_mul, ih.1, ih.2]
  exact (key n).1

theorem ch_hom {R : Type*} [CommRing R] (s τ δ : R) (n : ℕ) :
    ch (s * τ) (s ^ 2 * δ) (n + 1) = s ^ n * ch τ δ (n + 1) := by
  have key : ∀ n, ch (s * τ) (s ^ 2 * δ) (n + 1) = s ^ n * ch τ δ (n + 1) ∧
      ch (s * τ) (s ^ 2 * δ) (n + 2) = s ^ (n + 1) * ch τ δ (n + 2) := by
    intro n
    induction n with
    | zero => simp [ch]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have e : ch (s * τ) (s ^ 2 * δ) (n + 1 + 2) =
          s * τ * ch (s * τ) (s ^ 2 * δ) (n + 2) - s ^ 2 * δ * ch (s * τ) (s ^ 2 * δ) (n + 1) := rfl
      have e' : ch τ δ (n + 1 + 2) = τ * ch τ δ (n + 2) - δ * ch τ δ (n + 1) := rfl
      rw [e, e', ih.1, ih.2]
      ring
  exact (key n).1

theorem val_prod_sub {ι : Type*} (ν : Valuation ℂ ℝ≥0) (s : Finset ι) (f g : ι → ℂ) (m : ℝ≥0)
    (hf : ∀ i ∈ s, ν (f i) ≤ 1) (hg : ∀ i ∈ s, ν (g i) ≤ 1) (hfg : ∀ i ∈ s, ν (f i - g i) ≤ m) :
    ν (∏ i ∈ s, f i) ≤ 1 ∧ ν (∏ i ∈ s, g i) ≤ 1 ∧ ν (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ m :=
  _root_.UpperTheory.Reformulated.B.ProdSubProdLeOfFactorsClose.main ν s f g m hf hg hfg

open Classical in
theorem nz_prod {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι) (k₀ : ℕ)
    (t : InfinitePlace F → ℕ) (W : List (Pl F)) :
    (W.map (nz D k₀ t)).prod =
      (W.map fun w => ((((normV w : ℝ) ^ ((k₀ : ℝ) / 2 - 1) : ℝ)) : ℂ)).prod * ∏ v, (l : ℂ) ^ (t v * W.count (D.pl v)) := by
  induction W with
  | nil => simp
  | cons w W ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]
    have e : ∀ v, (l : ℂ) ^ (t v * (w :: W).count (D.pl v)) =
        (if D.pl v = w then (l : ℂ) ^ t v else 1) * (l : ℂ) ^ (t v * W.count (D.pl v)) := by
      intro v
      rw [List.count_cons]
      by_cases h : D.pl v = w
      · subst h
        rw [if_pos rfl]
        simp [mul_add, pow_add]
        try ring
      · have h' : ¬ (w == D.pl v) = true := by
          rw [beq_iff_eq]; exact fun e => h e.symm
        simp [h, h']
    simp only [e, Finset.prod_mul_distrib, nz]
    ring

theorem local_cong (ν : Valuation ℂ ℝ≥0) (hG : GCh) (τ δ U : ℂ) (m : ℝ≥0) (k₀ t : ℕ) (hk : 2 ≤ k₀) (hτ : ν τ ≤ 1)
    (hδ1 : ν δ ≤ 1) (hδ : ν δ ≤ m) (hτt : ν (τ ^ (2 * t) - 1) ≤ m) (hU1 : ν U ≤ 1) (hU : ν (U ^ t - 1) ≤ m) :
    ν (ch τ δ (k₀ - 1)) ≤ 1 ∧ ν (ch τ δ (k₀ + 2 * t - 1) * U ^ t) ≤ 1 ∧
      ν (ch τ δ (k₀ - 1) - ch τ δ (k₀ + 2 * t - 1) * U ^ t) ≤ m := by
  obtain ⟨n, rfl⟩ : ∃ n, k₀ = n + 2 := ⟨k₀ - 2, by omega⟩
  have e0 : n + 2 - 1 = n + 1 := by omega
  have e1 : n + 2 + 2 * t - 1 = (n + 2 * t) + 1 := by omega
  rw [e0, e1]
  obtain ⟨A1, A2⟩ := hG ν τ δ hτ hδ1 n
  obtain ⟨B1, B2⟩ := hG ν τ δ hτ hδ1 (n + 2 * t)
  have hUt : ν (U ^ t) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ (by positivity) hU1
  refine ⟨A1, ?_, ?_⟩
  · rw [map_mul]; exact mul_le_one' B1 hUt
  · have e : ch τ δ (n + 1) - ch τ δ (n + 2 * t + 1) * U ^ t =
        (ch τ δ (n + 1) - τ ^ n) + (τ ^ n * (1 - τ ^ (2 * t))) + (τ ^ (n + 2 * t) - ch τ δ (n + 2 * t + 1)) +
          ch τ δ (n + 2 * t + 1) * (1 - U ^ t) := by ring
    rw [e]
    have hτn : ν (τ ^ n) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ (by positivity) hτ
    refine ν.map_add_le (ν.map_add_le (ν.map_add_le (A2.trans hδ) ?_) ?_) ?_
    · rw [map_mul, ν.map_sub_swap]
      exact (mul_le_of_le_one_left (by positivity) hτn).trans hτt
    · rw [ν.map_sub_swap]; exact B2.trans hδ
    · rw [map_mul, ν.map_sub_swap]
      exact (mul_le_of_le_one_left (by positivity) B1).trans hU

end UpperTheory.Esk.adelicTermLemmas
end
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.adelicTermLemmas

theorem term_v (k₀ t' cnt : ℕ) (hk : 2 ≤ k₀) (s τ δ U L : ℂ) (hs : s ≠ 0) (hδ : δ ≠ 0) (hδU : δ * U = L ^ cnt) (d tr : ℝ)
    (hd : 0 < d) (htr : (tr : ℂ) = s * τ) (hdet : (d : ℂ) = s ^ 2 * δ) :
    L ^ (t' * cnt) * -(((ch tr d (k₀ + 2 * t' - 1) * d ^ (1 - ((k₀ + 2 * t' : ℕ) : ℝ) / 2) : ℝ) : ℂ)) =
      (s ^ (k₀ - 2) * ((d ^ (1 - (k₀ : ℝ) / 2) : ℝ) : ℂ)) * -(ch τ δ (k₀ + 2 * t' - 1) * U ^ t') := by
  have e1 : ((ch tr d (k₀ + 2 * t' - 1) : ℝ) : ℂ) = s ^ (k₀ - 2 + 2 * t') * ch τ δ (k₀ + 2 * t' - 1) := by
    have h := ch_map Complex.ofRealHom tr d (k₀ + 2 * t' - 1)
    simp only [Complex.ofRealHom_eq_coe] at h
    rw [h, htr, hdet]
    have hk' : k₀ + 2 * t' - 1 = (k₀ - 2 + 2 * t') + 1 := by omega
    rw [hk', ch_hom]
  have e2 : ((d ^ (1 - ((k₀ + 2 * t' : ℕ) : ℝ) / 2) : ℝ) : ℂ) = ((d ^ (1 - (k₀ : ℝ) / 2) : ℝ) : ℂ) * ((s ^ 2 * δ) ^ t')⁻¹ := by
    have h : (1 - ((k₀ + 2 * t' : ℕ) : ℝ) / 2) = (1 - (k₀ : ℝ) / 2) + (-(t' : ℝ)) := by push_cast; ring
    rw [h, Real.rpow_add hd, Real.rpow_neg hd.le, Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_inv,
      Complex.ofReal_pow, hdet]
  rw [Complex.ofReal_mul, e1, e2, mul_comm t' cnt, pow_mul, ← hδU, pow_add, mul_pow, mul_pow, ← pow_mul]
  field_simp

theorem list_prod_ofReal {α : Type*} (W : List α) (f : α → ℝ) : (W.map fun w => ((f w : ℝ) : ℂ)).prod = (((W.map f).prod : ℝ) : ℂ) := by
  induction W with
  | nil => simp
  | cons w W ih => simp [ih]

end UpperTheory.Esk.adelicTermLemmas

open UpperTheory.Esk.adelicTermLemmas Classical in
theorem UpperTheory.Esk.pf_GTerm : UpperTheory.Esk.GCh → UpperTheory.Esk.GUnit → UpperTheory.Esk.GMod → UpperTheory.Esk.GTerm := by
  intro hG hU hMod F _ _ _ l _ ι D c χ hc k₀ hk₀ N t ht W r hr hW n a hR γ x i hell hmem
  obtain ⟨k, hk, z, hkz⟩ := hc_decomp hmem
  have hrel1 : jF F γ * x * (k * zc F z) = x * a i := by rw [← hkz]; group
  have hrel2 : jF F γ = x * (a i * k⁻¹ * zc F z⁻¹) * x⁻¹ := by
    have hcz : k⁻¹ * zc F z⁻¹ = zc F z⁻¹ * k⁻¹ := Subgroup.mem_center_iff.1 (zc_center z⁻¹) k⁻¹
    have e : jF F γ = x * a i * (k * zc F z)⁻¹ * x⁻¹ := by rw [← hrel1]; group
    rw [e, mul_inv_rev, ← map_inv, ← hcz]
    simp only [mul_assoc]
  have hloc := fun v => loc D hU hc hr hW hR hk hrel2 v N
  choose τ δ U htr hdt hτ1 hδ1 hδr hU1 hδU hpow using hloc
  have hs0 : ∀ v, (D.ea v (z : Af F))⁻¹ ≠ 0 := fun v => inv_ne_zero ((z.isUnit.map (D.ea v)).ne_zero)
  have hσ : ∀ v (y : F), (((mkDat c χ).σ v y : ℝ) : ℂ) = v.embedding y := fun v y =>
    InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) y
  have hre : ∀ v (y : F), reAt v y = (mkDat c χ).σ v y := fun v y => by rw [reAt, ← hσ, Complex.ofReal_re]
  have hdpos : ∀ v, 0 < (mkDat c χ).σ v γ.val.det := fun v => by
    have := hell v
    nlinarith [sq_nonneg ((mkDat c χ).σ v γ.val.trace)]
  have hδ0 : ∀ v, δ v ≠ 0 := fun v h => by
    have h1 := hdt v
    rw [h, mul_zero, ← hσ] at h1
    exact (hdpos v).ne' (by exact_mod_cast h1)
  set A : ℝ := absF z with hA_def
  have hA : 0 < A := (Hm.absf F).1 z
  set Nw : ℝ := (W.map fun w => (normV w : ℝ)).prod with hNw
  have hp : ∏ v, (mkDat c χ).σ v γ.val.det = A ^ 2 * Nw := by
    rw [hA_def, hNw, ← prod_reAt hR hk hrel1]
    exact Finset.prod_congr rfl fun v _ => by rw [hre, abs_of_pos (hdpos v)]
  have hN : 0 < Nw := by
    have h1 : 0 < A ^ 2 * Nw := hp ▸ Finset.prod_pos fun v _ => hdpos v
    exact pos_of_mul_pos_right h1 (by positivity)
  have hreal : (W.map fun w => (normV w : ℝ) ^ ((k₀ : ℝ) / 2 - 1)).prod * ∏ v, (mkDat c χ).σ v γ.val.det ^ (1 - (k₀ : ℝ) / 2) =
      (A ^ (k₀ - 2))⁻¹ := by
    rw [Real.list_prod_map_rpow' W (fun w => (normV w : ℝ)) (fun _ _ => Nat.cast_nonneg _),
      Real.finsetProd_rpow _ _ (fun v _ => (hdpos v).le), hp, ← hNw]
    have e1 : (A ^ 2 * Nw) ^ (1 - (k₀ : ℝ) / 2) = (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) * Nw ^ (1 - (k₀ : ℝ) / 2) :=
      Real.mul_rpow (by positivity) hN.le
    have e2 : Nw ^ ((k₀ : ℝ) / 2 - 1) * Nw ^ (1 - (k₀ : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hN, show (k₀ : ℝ) / 2 - 1 + (1 - (k₀ : ℝ) / 2) = 0 by ring, Real.rpow_zero]
    have e3 : (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) = (A ^ (k₀ - 2))⁻¹ := by
      rw [← Real.rpow_natCast_mul hA.le, show ((2 : ℕ) : ℝ) * (1 - (k₀ : ℝ) / 2) = -((k₀ - 2 : ℕ) : ℝ) by
        rw [Nat.cast_sub hk₀]; push_cast; ring, Real.rpow_neg hA.le, Real.rpow_natCast]
    rw [e1, ← e3]
    calc Nw ^ ((k₀ : ℝ) / 2 - 1) * ((A ^ 2) ^ (1 - (k₀ : ℝ) / 2) * Nw ^ (1 - (k₀ : ℝ) / 2))
        = (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) * (Nw ^ ((k₀ : ℝ) / 2 - 1) * Nw ^ (1 - (k₀ : ℝ) / 2)) := by ring
      _ = (A ^ 2) ^ (1 - (k₀ : ℝ) / 2) := by rw [e2, mul_one]
  set Q : ℂ := (((A : ℂ) * ∏ v, D.ea v (z : Af F)) ^ (k₀ - 2))⁻¹ with hQ
  have key : ∀ t' : InfinitePlace F → ℕ, (W.map (nz D k₀ t')).prod * (mkDat c χ).orb (fun v => k₀ + 2 * t' v) γ =
      Q * ∏ v, -(ch (τ v) (δ v) (k₀ + 2 * t' v - 1) * U v ^ t' v) := by
    intro t'
    rw [nz_prod]
    simp only [Dat.orb]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl fun v _ => term_v k₀ (t' v) (W.count (D.pl v)) hk₀ _ (τ v) (δ v) (U v) (l : ℂ) (hs0 v) (hδ0 v)
      (hδU v) _ _ (hdpos v) (by rw [hσ]; exact htr v) (by rw [hσ]; exact hdt v)]
    rw [Finset.prod_mul_distrib, ← mul_assoc]
    congr 1
    rw [Finset.prod_mul_distrib, list_prod_ofReal, mul_comm (∏ v, _ ^ (k₀ - 2)), ← mul_assoc, ← Complex.ofReal_prod,
      ← Complex.ofReal_mul, hreal, hQ, mul_pow, mul_inv, Finset.prod_pow, Finset.prod_inv_distrib, Complex.ofReal_inv,
      Complex.ofReal_pow, inv_pow]
  have hQ1 : nu ι Q = 1 := by
    rw [hQ, map_inv₀, map_pow, hA_def, (hMod F l ι D z).2, one_pow, inv_one]
  have hcong := fun v => local_cong (nu ι) hG (τ v) (δ v) (U v) (max (nu ι l ^ N) (nu ι l ^ r)) k₀ (t v) hk₀ (hτ1 v) (hδ1 v)
    ((hδr v).trans (le_max_right _ _)) ((hpow v (t v) (ht v)).1.trans (le_max_left _ _)) (hU1 v)
    ((hpow v (t v) (ht v)).2.trans (le_max_left _ _))
  obtain ⟨p1, p2, p3⟩ := val_prod_sub (nu ι) Finset.univ (fun v => -(ch (τ v) (δ v) (k₀ - 1)))
    (fun v => -(ch (τ v) (δ v) (k₀ + 2 * t v - 1) * U v ^ t v)) (max (nu ι l ^ N) (nu ι l ^ r))
    (fun v _ => by rw [Valuation.map_neg]; exact (hcong v).1) (fun v _ => by rw [Valuation.map_neg]; exact (hcong v).2.1)
    (fun v _ => by rw [neg_sub_neg, Valuation.map_sub_swap]; exact (hcong v).2.2)
  have h0 := key 0
  simp only [Pi.zero_apply, mul_zero, add_zero, pow_zero, mul_one] at h0
  rw [h0, key t]
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, hQ1, one_mul]; exact p1
  · rw [map_mul, hQ1, one_mul]; exact p2
  · rw [← mul_sub, map_mul, hQ1, one_mul]; exact p3
end
end

namespace UpperTheory.Esk

theorem holWC : HolWC := holWC_of dAx dTwo' dGood' dReps (pf_GTerm s_GCh s_GUnit s_GMod)

end UpperTheory.Esk
