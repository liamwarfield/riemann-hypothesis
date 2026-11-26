module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadratic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfect

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralUnitaryGroupTransitiveNormOneVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHermitianMatrixCongruentOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormOneAddEqOne
namespace GlobalTheory.UnitValueExistence

open Matrix

theorem norm_add_lt_one {E : Type} [NormedField E] [IsUltrametricDist E] {a b : E}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

theorem norm_one_add_eq_one {E : Type} [NormedField E] [IsUltrametricDist E] {a : E}
    (ha : ‖a‖ < 1) : ‖1 + a‖ = 1 := by
  have h : ‖(1 : E)‖ ≠ ‖a‖ := by rw [norm_one]; exact ha.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h, norm_one, max_eq_left ha.le]

theorem norm_det_lt_one {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (h : ∀ i j, ‖G i j‖ < 1) : ‖G.det‖ < 1 := by
  rw [Matrix.det_apply']
  refine Finset.sum_induction _ (fun x : E => ‖x‖ < 1) (fun a b ha hb => norm_add_lt_one ha hb)
    (by simp) ?_
  intro σ _
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  rw [norm_mul, hs, one_mul, norm_prod]
  obtain ⟨i⟩ := ‹Nonempty n›
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have h2 : ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => (h _ _).le)
  calc ‖G (σ i) i‖ * ∏ x ∈ Finset.univ.erase i, ‖G (σ x) x‖ ≤ ‖G (σ i) i‖ * 1 :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact h _ _

theorem exists_unit_value {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
    (hstar : ∀ y : E, ‖star y‖ = ‖y‖) (e0 : E) (he : ‖e0‖ ≤ (1 : ℝ)) (htr : e0 + star e0 = 1)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E)
    (hG : Matrix.IsHermitian G) (hint : ∀ i j, ‖G i j‖ ≤ (1 : ℝ)) (hdet : ‖G.det‖ = (1 : ℝ)) :
    ∃ (i : n) (w : n → E), (∀ a, ‖w a‖ ≤ (1 : ℝ)) ∧ w i = 1 ∧
      ‖star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ) := by
  by_cases hd : ∃ i, ‖G i i‖ = 1
  · obtain ⟨i, hi⟩ := hd
    refine ⟨i, Pi.single i 1, ?_, by simp, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp
      · simp [Pi.single_eq_of_ne ha]
    · have hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1 := by
        rw [Pi.star_single, star_one]
      rw [hs, single_dotProduct, Matrix.mulVec_single_one]
      simpa using hi
  · have hdiag : ∀ i, ‖G i i‖ < 1 := fun i =>
      lt_of_le_of_ne (hint i i) (fun h => hd ⟨i, h⟩)
    have hex : ∃ i j, ‖G i j‖ = 1 := by
      by_contra hne
      have := norm_det_lt_one G (fun i j => lt_of_le_of_ne (hint i j) (fun h => hne ⟨i, j, h⟩))
      exact this.ne hdet
    obtain ⟨i, j, hij⟩ := hex
    have hne : i ≠ j := by
      rintro rfl
      exact (hdiag i).ne hij
    have hg0 : G i j ≠ 0 := by
      intro h; rw [h, norm_zero] at hij; exact zero_ne_one hij
    set t : E := e0 / G i j with ht
    have htn : ‖t‖ ≤ 1 := by rw [ht, norm_div, hij, div_one]; exact he
    have htG : G i j * t = e0 := by rw [ht]; field_simp
    have hji : G j i = star (G i j) := (hG.apply j i).symm
    have htG' : star t * G j i = star e0 := by rw [hji, ← star_mul, htG]
    refine ⟨i, Pi.single i 1 + Pi.single j t, ?_, ?_, ?_⟩
    · intro a
      by_cases ha : a = i
      · subst ha; simp [Pi.single_eq_of_ne hne]
      · by_cases hb : a = j
        · subst hb; simpa [Pi.single_eq_of_ne ha] using htn
        · simp [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]
    · simp [Pi.single_eq_of_ne hne]
    · have hs : star (Pi.single i (1 : E) + Pi.single j t : n → E)
          = Pi.single i 1 + Pi.single j (star t) := by
        rw [star_add, Pi.star_single, Pi.star_single, star_one]
      have key : star (Pi.single i (1 : E) + Pi.single j t : n → E) ⬝ᵥ
          Matrix.mulVec G (Pi.single i 1 + Pi.single j t)
          = 1 + (G i i + star t * (G j j * t)) := by
        rw [hs, add_dotProduct, single_dotProduct, single_dotProduct, Matrix.mulVec_add]
        simp only [Pi.add_apply, Matrix.mulVec, dotProduct_single]
        linear_combination htG + htG' + htr
      rw [key]
      apply norm_one_add_eq_one
      apply norm_add_lt_one (hdiag i)
      rw [norm_mul, norm_mul, hstar]
      have h1 := hdiag j
      have h2 := norm_nonneg t
      have h3 := norm_nonneg (G j j)
      have h4 : ‖G j j‖ * ‖t‖ ≤ ‖G j j‖ := mul_le_of_le_one_right h3 htn
      have h5 : ‖t‖ * (‖G j j‖ * ‖t‖) ≤ ‖G j j‖ * ‖t‖ :=
        mul_le_of_le_one_left (mul_nonneg h3 h2) htn
      linarith

theorem main : (let d1 : {E : Type} → [NormedField E] → {n m : Type} → Matrix n m E → Prop := @(fun {E : Type} [NormedField E] {n m : Type} (h : Matrix n m E) ↦ ∀ (i : n) (j : m), ‖h i j‖ ≤ (1 : ℝ)); ∀ {E : Type} [inst : NormedField E] [IsUltrametricDist E] [inst_2 : StarRing E], (∀ (y : E), ‖Star.star y‖ = ‖y‖) → ∀ (e0 : E), ‖e0‖ ≤ (1 : ℝ) → e0 + Star.star e0 = (1 : E) → ∀ {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] [Nonempty n] (G : Matrix n n E), Matrix.IsHermitian G → d1 G → ‖Matrix.det G‖ = (1 : ℝ) → ∃ (i : n) (w : n → E), (∀ (a : n), ‖w a‖ ≤ (1 : ℝ)) ∧ w i = (1 : E) ∧ ‖Star.star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ)) := by
  intro d1 E _ _ _ hstar e0 he htr n _ _ _ G hG hint hdet
  exact exists_unit_value hstar e0 he htr G hG hint hdet

end GlobalTheory.UnitValueExistence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHermitianMatrixCongruentOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.HermUnimod

section Gen

variable {E : Type} [NormedField E]

def Intg {n m : Type} (h : Matrix n m E) : Prop := ∀ i j, ‖h i j‖ ≤ 1

theorem nsum_le [IsUltrametricDist E] {ι : Type} (s : Finset ι) (f : ι → E) {r : ℝ} (hr : 0 ≤ r) (h : ∀ i ∈ s, ‖f i‖ ≤ r) :
    ‖∑ i ∈ s, f i‖ ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem intg_mul [IsUltrametricDist E] {l n m : Type} [Fintype n] {A : Matrix l n E} {B : Matrix n m E} (hA : Intg A)
    (hB : Intg B) : Intg (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine nsum_le _ _ zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

theorem intg_conjT [StarRing E] (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n m : Type} {A : Matrix n m E} (hA : Intg A) :
    Intg Aᴴ := by
  intro i j
  rw [conjTranspose_apply, hs]
  exact hA j i

theorem intg_one {n : Type} [DecidableEq n] : Intg (1 : Matrix n n E) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem norm_det_conjT [StarRing E] (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n E) : ‖Aᴴ.det‖ = ‖A.det‖ := by
  rw [det_conjTranspose, hs]

def Good (n : Type) [Fintype n] [DecidableEq n] (E : Type) [NormedField E] [StarRing E] : Prop :=
  ∀ G : Matrix n n E, G.IsHermitian → (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 →
    ∃ h : Matrix n n E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1

end Gen

section Step

variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]

theorem intg_fromBlocks {l m n o : Type} {A : Matrix n l E} {B : Matrix n m E} {C : Matrix o l E}
    {D : Matrix o m E} (hA : Intg A) (hB : Intg B) (hC : Intg C) (hD : Intg D) :
    Intg (fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

theorem intg_sub {n m : Type} {A B : Matrix n m E} (hA : Intg A) (hB : Intg B) : Intg (A - B) := by
  intro i j
  rw [Matrix.sub_apply, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (by rw [norm_neg]; exact hB i j))

theorem intg_neg {n m : Type} {A : Matrix n m E} (hA : Intg A) : Intg (-A) := by
  intro i j
  change ‖-(A i j)‖ ≤ 1
  rw [norm_neg]
  exact hA i j

theorem intg_zero {n m : Type} : Intg (0 : Matrix n m E) := by
  intro i j
  simp

theorem schur_conj {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m E) (B : Matrix m Unit E) :
    (fromBlocks 1 0 (-Bᴴ) 1 : Matrix (m ⊕ Unit) (m ⊕ Unit) E)ᴴ * fromBlocks A B Bᴴ 1 *
        fromBlocks 1 0 (-Bᴴ) 1 = fromBlocks (A - B * Bᴴ) 0 0 1 := by
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, sub_eq_add_neg]

theorem good_sum (hs : ∀ y : E, ‖star y‖ = ‖y‖) {m : Type} [Fintype m] [DecidableEq m] (H : Good m E)
    (G : Matrix (m ⊕ Unit) (m ⊕ Unit) E) (hG : G.IsHermitian) (hGi : ∀ i j, ‖G i j‖ ≤ 1)
    (hGd : ‖G.det‖ = 1) (hk : G (Sum.inr ()) (Sum.inr ()) = 1) :
    ∃ h : Matrix (m ⊕ Unit) (m ⊕ Unit) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  have hD : G.toBlocks₂₂ = 1 := by
    ext ⟨⟩ ⟨⟩
    simp [toBlocks₂₂, hk]
  have hG' : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₁ 1 := by
    rw [← hD, fromBlocks_toBlocks]
  set A := G.toBlocks₁₁
  set B := G.toBlocks₁₂
  set C := G.toBlocks₂₁
  have hh := hG
  rw [hG', isHermitian_fromBlocks_iff] at hh
  obtain ⟨hA, hBC, -, -⟩ := hh
  rw [← hBC] at hG'
  have hAi : Intg A := fun i j => hGi _ _
  have hBi : Intg B := fun i j => hGi _ _
  have hA'i : Intg (A - B * Bᴴ) := intg_sub hAi (intg_mul hBi (intg_conjT hs hBi))
  have hA'h : (A - B * Bᴴ).IsHermitian := hA.sub (isHermitian_mul_conjTranspose_self B)
  have hA'd : ‖(A - B * Bᴴ).det‖ = 1 := by
    rw [← det_fromBlocks_one₂₂, ← hG']
    exact hGd
  obtain ⟨h', hi', hd', hh'⟩ := H _ hA'h hA'i hA'd
  refine ⟨fromBlocks 1 0 (-Bᴴ) 1 * fromBlocks h' 0 0 1, ?_, ?_, ?_⟩
  · exact intg_mul (intg_fromBlocks intg_one intg_zero (intg_neg (intg_conjT hs hBi)) intg_one)
      (intg_fromBlocks hi' intg_zero intg_zero intg_one)
  · rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
    simp [hd']
  · rw [conjTranspose_mul, hG']
    calc (fromBlocks h' 0 0 1)ᴴ * (fromBlocks 1 0 (-Bᴴ) 1)ᴴ * fromBlocks A B Bᴴ 1 *
          (fromBlocks 1 0 (-Bᴴ) 1 * fromBlocks h' 0 0 1)
        = (fromBlocks h' 0 0 1)ᴴ * ((fromBlocks 1 0 (-Bᴴ) 1)ᴴ * fromBlocks A B Bᴴ 1 *
          fromBlocks 1 0 (-Bᴴ) 1) * fromBlocks h' 0 0 1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [schur_conj]
        simp [fromBlocks_conjTranspose, fromBlocks_multiply, hh']

end Step

section Main

variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]

theorem sol_transfer (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (e : n ≃ n') (G : Matrix n n E) (h : Matrix n' n' E) (hi : ∀ i j, ‖h i j‖ ≤ 1)
    (hd : ‖h.det‖ = 1) (hh : hᴴ * reindex e e G * h = 1) :
    ∃ h : Matrix n n E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  refine ⟨reindex e.symm e.symm h, fun i j => hi _ _, by rw [det_reindex_self]; exact hd, ?_⟩
  have : reindex e.symm e.symm (hᴴ * reindex e e G * h) = 1 := by rw [hh]; simp
  rw [← this]
  simp only [reindex_apply, Equiv.symm_symm, conjTranspose_submatrix]
  rw [← submatrix_mul_equiv (hᴴ * _) h e e e, ← submatrix_mul_equiv hᴴ _ e e e]
  simp

theorem good_all (hs : ∀ y : E, ‖star y‖ = ‖y‖)
    (piv : ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E), G.IsHermitian →
      Intg G → ‖G.det‖ = 1 → ∃ P : Matrix n n E, Intg P ∧ ‖P.det‖ = 1 ∧ ∃ k, (Pᴴ * G * P) k k = 1) :
    ∀ (m : ℕ) (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = m → Good n E := by
  intro m
  induction m with
  | zero =>
    intro n _ _ hc G _ _ _
    haveI : IsEmpty n := Fintype.card_eq_zero_iff.1 hc
    refine ⟨1, fun i => isEmptyElim i, by simp, ?_⟩
    ext i
    exact isEmptyElim i
  | succ m ih =>
    intro n _ _ hc G hG hGi hGd
    haveI : Nonempty n := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨P, hPi, hPd, k, hk⟩ := piv n G hG hGi hGd
    have hM : (Pᴴ * G * P).IsHermitian := isHermitian_conjTranspose_mul_mul P hG
    have hMi : Intg (Pᴴ * G * P) := intg_mul (intg_mul (intg_conjT hs hPi) hGi) hPi
    have hMd : ‖(Pᴴ * G * P).det‖ = 1 := by
      rw [det_mul, det_mul, norm_mul, norm_mul, norm_det_conjT hs, hPd, hGd, one_mul, one_mul]
    let e : n ≃ {j // j ≠ k} ⊕ Unit :=
      (Equiv.optionSubtypeNe k).symm.trans (Equiv.optionEquivSumPUnit.{0, 0} _)
    have hc' : Fintype.card {j // j ≠ k} = m := by
      have := Fintype.card_congr (Equiv.optionSubtypeNe k)
      rw [Fintype.card_option] at this
      omega
    have hk' : reindex e e (Pᴴ * G * P) (Sum.inr ()) (Sum.inr ()) = 1 := by
      simpa [e, reindex_apply, Equiv.optionSubtypeNe] using hk
    obtain ⟨h, hi, hd, hh⟩ := good_sum hs (ih _ hc') (reindex e e (Pᴴ * G * P))
      (by simpa [reindex_apply] using hM.submatrix e.symm) (fun i j => hMi _ _)
      (by rw [det_reindex_self]; exact hMd) hk'
    obtain ⟨h₁, hi₁, hd₁, hh₁⟩ := sol_transfer hs e _ h hi hd hh
    refine ⟨P * h₁, intg_mul hPi hi₁, by rw [det_mul, norm_mul, hPd, hd₁, one_mul], ?_⟩
    rw [conjTranspose_mul, ← hh₁]
    simp only [Matrix.mul_assoc]

end Main

section Piv

theorem pivot_w {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]
    (hs : ∀ y : E, ‖star y‖ = ‖y‖) (e0 : E) (he0 : ‖e0‖ ≤ 1) (he0' : e0 + star e0 = 1) {n : Type}
    [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E) (hG : G.IsHermitian) (hGi : Intg G)
    (hGd : ‖G.det‖ = 1) :
    ∃ i, ∃ w : n → E, (∀ a, ‖w a‖ ≤ 1) ∧ w i = 1 ∧ ‖star w ⬝ᵥ (G *ᵥ w)‖ = 1 := by
  first
  | exact @_root_.GlobalTheory.UnitValueExistence.main
  | exact _root_.GlobalTheory.UnitValueExistence.main
  | (apply _root_.GlobalTheory.UnitValueExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitValueExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitValueExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitValueExistence.main ..)

end Piv

section Field

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem fixed_mem (a : E) (ha : star a = a) : ∃ u : F, algebraMap F E u = a := by
  let L : E →ₗ[F] E :=
    { toFun := fun y => star y - y
      map_add' := by
        intro x y
        simp only [star_add]
        abel
      map_smul' := by
        intro c y
        simp only [Algebra.smul_def, star_mul', Unram.star_fix, RingHom.id_apply, mul_sub] }
  have hfin : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hlt : LinearMap.ker L < ⊤ := by
    obtain ⟨y, hy⟩ := Unram.star_ne (F := F) (E := E)
    refine lt_top_iff_ne_top.2 fun h => hy ?_
    have : y ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simpa [L, sub_eq_zero] using this
  have h1 : Module.finrank F (LinearMap.ker L) < 2 := hfin ▸ Submodule.finrank_lt hlt.ne
  have hle : LinearMap.range (Algebra.linearMap F E) ≤ LinearMap.ker L := by
    rintro _ ⟨x, rfl⟩
    simp [L, Unram.star_fix]
  have hr : Module.finrank F (LinearMap.range (Algebra.linearMap F E)) = 1 := by
    rw [LinearMap.finrank_range_of_inj (algebraMap F E).injective, Module.finrank_self]
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hmem : a ∈ LinearMap.ker L := by simp [L, ha]
  rw [← heq] at hmem
  obtain ⟨u, hu⟩ := hmem
  exact ⟨u, hu⟩

theorem quad_col {n : Type} [Fintype n] (G P : Matrix n n E) (k : n) :
    (Pᴴ * G * P) k k = star (fun a => P a k) ⬝ᵥ (G *ᵥ fun a => P a k) := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

include F in
theorem pivot {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E) (hG : G.IsHermitian)
    (hGi : Intg G) (hGd : ‖G.det‖ = 1) :
    ∃ P : Matrix n n E, Intg P ∧ ‖P.det‖ = 1 ∧ ∃ k, (Pᴴ * G * P) k k = 1 := by
  haveI := Unram.ultraE (F := F) (E := E)
  have hs : ∀ y : E, ‖star y‖ = ‖y‖ := Unram.norm_star (F := F)
  obtain ⟨-, ⟨e0, he0, he0'⟩, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  obtain ⟨i, w, hw, hwi, hq⟩ := pivot_w hs e0 he0 he0' G hG hGi hGd
  have ha : star (star w ⬝ᵥ (G *ᵥ w)) = star w ⬝ᵥ (G *ᵥ w) := by
    calc star (star w ⬝ᵥ (G *ᵥ w)) = (star w ᵥ* Gᴴ) ⬝ᵥ w := by rw [star_dotProduct, star_mulVec, star_star]
      _ = star w ⬝ᵥ (G *ᵥ w) := by rw [← dotProduct_mulVec, hG.eq]
  obtain ⟨u, hu⟩ := fixed_mem (F := F) _ ha
  have hu1 : ‖u‖ = 1 := by rw [← norm_algebraMap' E u, hu]; exact hq
  obtain ⟨v0, hv0⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E u hu1
  rw [hu] at hv0
  have hv0n : ‖v0‖ = 1 := by
    have h := congrArg norm hv0
    rw [norm_mul, hs, hq] at h
    nlinarith [norm_nonneg v0]
  have hv0ne : v0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv0n
    exact zero_ne_one hv0n
  have hc : ‖(star v0)⁻¹‖ = 1 := by rw [norm_inv, hs, hv0n, inv_one]
  refine ⟨(1 : Matrix n n E).updateCol i ((star v0)⁻¹ • w), ?_, ?_, i, ?_⟩
  · intro p q
    rw [updateCol_apply]
    split_ifs
    · rw [Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]
      exact hw p
    · exact intg_one p q
  · rw [← cramer_apply, cramer_one]
    simp [hc, hwi]
  · rw [quad_col]
    have hcol : (fun a => (1 : Matrix n n E).updateCol i ((star v0)⁻¹ • w) a i) = (star v0)⁻¹ • w := by
      funext a
      simp
    have hst : star ((star v0)⁻¹ • w) = v0⁻¹ • star w := by
      funext p
      simp [star_mul', star_inv₀]
    rw [hcol, hst, smul_dotProduct, mulVec_smul, dotProduct_smul, ← hv0, smul_eq_mul, smul_eq_mul]
    have hsv : star v0 ≠ 0 := by rwa [star_ne_zero]
    field_simp

end Field

theorem unimodular_hermitian_eq_conj : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (s : ℕ) (G : Matrix (Fin s) (Fin s) E), G.IsHermitian →
    (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 →
    ∃ h : Matrix (Fin s) (Fin s) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  intro F E _ _ _ _ _ s G hG hGi hGd
  haveI := Unram.ultraE (F := F) (E := E)
  exact good_all (Unram.norm_star (F := F)) (fun n _ _ _ G hG hGi hGd => pivot (F := F) (E := E) G hG hGi hGd) s (Fin s)
    (Fintype.card_fin s) G hG hGi hGd

end GlobalTheory.HermUnimod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHermitianMatrixCongruentOneStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_hermitian_matrix_congruent_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (s : ℕ) (G : Matrix (Fin s) (Fin s) E), G.IsHermitian → (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 → ∃ h : Matrix (Fin s) (Fin s) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  first | exact @GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj | exact GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj | (intros; apply GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralUnitaryGroupTransitiveNormOneVectors
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.UnitaryTransitive

variable {E : Type} [NormedField E] [StarRing E]

theorem nsub [IsUltrametricDist E] (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]; simpa using IsUltrametricDist.norm_add_le_max a (-b)

def ext0 {r : ℕ} (x : Fin r → E) : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) x 0

@[simp] theorem snocZeroLastCoordinate_castSucc {r : ℕ} (x : Fin r → E) (j : Fin r) : ext0 x j.castSucc = x j := by
  simp [ext0]
@[simp] theorem snocZeroLastCoordinate_last {r : ℕ} (x : Fin r → E) : ext0 x (Fin.last r) = 0 := by
  simp [ext0]

theorem star_snocZeroLastCoordinate_dotProduct {r : ℕ} (x : Fin r → E) (f : Fin (r + 1) → E) :
    star (ext0 x) ⬝ᵥ f = star x ⬝ᵥ (fun j => f j.castSucc) := by
  simp [dotProduct, Fin.sum_univ_castSucc]

theorem dotProduct_snocZeroLastCoordinate {r : ℕ} (x : Fin r → E) (f : Fin (r + 1) → E) :
    f ⬝ᵥ ext0 x = (fun j => f j.castSucc) ⬝ᵥ x := by
  simp [dotProduct, Fin.sum_univ_castSucc]

end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive
variable {E : Type} [Field E] [StarRing E]
theorem rank_one_entry {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (a b : Fin r → E) (m m' : Fin r) :
    (gᴴ * (replicateCol Unit a * replicateRow Unit b) * g) m m' = (gᴴ *ᵥ a) m * (b ᵥ* g) m' := by
  have e : gᴴ * (replicateCol Unit a * replicateRow Unit b) * g =
      replicateCol Unit (gᴴ *ᵥ a) * replicateRow Unit (b ᵥ* g) := by
    rw [Matrix.replicateCol_mulVec, Matrix.replicateRow_vecMul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e]; simp [Matrix.mul_apply]

theorem star_dot_col {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (w : Fin r → E) (m : Fin r) :
    star (star w ⬝ᵥ (fun j => g j m)) = (gᴴ *ᵥ w) m := by
  simp [dotProduct, Matrix.mulVec, star_sum, mul_comm]

theorem dot_col {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (b : Fin r → E) (m : Fin r) :
    b ⬝ᵥ (fun j => g j m) = (b ᵥ* g) m := by
  simp [dotProduct, Matrix.vecMul]
end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive

theorem uO_transitive_of_last_unit (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E) (hv : ∀ i, ‖v i‖ ≤ 1) (h1 : star v ⬝ᵥ v = 1)
    (hn : ‖v (Fin.last r)‖ = 1) : ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  haveI := Unram.ultraE (F := F) (E := E)
  have hst : ∀ x : E, ‖star x‖ = ‖x‖ := Unram.norm_star (F := F)
  set w : Fin r → E := fun j => v j.castSucc with hw
  set G : Matrix (Fin r) (Fin r) E := 1 + replicateCol Unit (-w) * replicateRow Unit (star w) with hG
  have hGe : ∀ i j, G i j = (1 : Matrix (Fin r) (Fin r) E) i j - w i * star (w j) := by
    intro i j; simp [G, Matrix.mul_apply, sub_eq_add_neg]
  have hGh : G.IsHermitian := by
    apply Matrix.IsHermitian.ext; intro i j; rw [hGe, hGe]
    by_cases h : i = j
    · subst h; simp [mul_comm]
    · simp [Matrix.one_apply, h, Ne.symm h, mul_comm]
  have hGi : ∀ i j, ‖G i j‖ ≤ 1 := by
    intro i j; rw [hGe]; refine (nsub _ _).trans (max_le ?_ ?_)
    · by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · rw [norm_mul, hst]; exact mul_le_one₀ (hv _) (norm_nonneg _) (hv _)
  have hsplit : star v ⬝ᵥ v = star w ⬝ᵥ w + star (v (Fin.last r)) * v (Fin.last r) := by
    simp [dotProduct, Fin.sum_univ_castSucc, w]
  have hGd : ‖G.det‖ = 1 := by
    rw [hG, det_one_add_replicateCol_mul_replicateRow, dotProduct_neg]
    have : 1 + -(star w ⬝ᵥ w) = star (v (Fin.last r)) * v (Fin.last r) := by
      linear_combination h1.symm + hsplit
    rw [this, norm_mul, hst, hn]; norm_num
  obtain ⟨g, hgi, -, hg⟩ := GlobalTheory.T.unimodular_hermitian_matrix_congruent_one F E r G hGh hGi hGd
  set c : Fin r → E := fun m => star w ⬝ᵥ (fun j => g j m) with hc
  have hg' : ∀ m m', star (fun j => g j m) ⬝ᵥ (fun j => g j m') - star (c m) * c m' = (1 : Matrix (Fin r) (Fin r) E) m m' := by
    intro m m'
    have := congrFun (congrFun hg m) m'
    rw [← this, hG, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.add_apply, rank_one_entry,
      hc, star_dot_col, dot_col, Matrix.mulVec_neg]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, sub_eq_add_neg]
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun i l =>
    Fin.lastCases (motive := fun _ => E) (v i) (fun m => ext0 (fun j => g j m) i - c m * v i) l
  have cl : (fun i => K i (Fin.last r)) = v := by funext i; simp [K]
  have cs : ∀ m, (fun i => K i m.castSucc) = ext0 (fun j => g j m) - c m • v := by
    intro m; funext i; simp [K]
  have key : ∀ a b, (star K * K) a b = star (fun i => K i a) ⬝ᵥ (fun i => K i b) := by
    intro a b; rfl
  have d2 : ∀ m, star v ⬝ᵥ ext0 (fun j => g j m) = c m := by
    intro m; rw [dotProduct_snocZeroLastCoordinate]; rfl
  have d3 : ∀ m, star (ext0 (fun j => g j m)) ⬝ᵥ v = star (c m) := by
    intro m; rw [star_snocZeroLastCoordinate_dotProduct, hc, star_dot_col]; rfl
  have d4 : ∀ m m', star (ext0 (fun j => g j m)) ⬝ᵥ ext0 (fun j => g j m') =
      star (fun j => g j m) ⬝ᵥ (fun j => g j m') := by
    intro m m'; rw [star_snocZeroLastCoordinate_dotProduct]; simp
  have hU : star K * K = 1 := by
    ext a b
    rw [key]
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rw [cl, h1]; simp
      | cast m' =>
        rw [cl, cs, dotProduct_sub, dotProduct_smul, d2, h1, smul_eq_mul, mul_one, sub_self,
          Matrix.one_apply_ne (Fin.castSucc_ne_last m').symm]
    | cast m =>
      induction b using Fin.lastCases with
      | last =>
        rw [cl, cs, star_sub, star_smul, sub_dotProduct, smul_dotProduct, d3, h1]
        simp [Matrix.one_apply, (Fin.castSucc_ne_last m)]
      | cast m' =>
        rw [cs, cs, star_sub, star_smul, sub_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_sub,
          dotProduct_smul, dotProduct_smul, d2, d3, d4, h1]
        have e1 : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) m.castSucc m'.castSucc =
            (1 : Matrix (Fin r) (Fin r) E) m m' := by
          simp [Matrix.one_apply, Fin.castSucc_inj]
        rw [e1, ← hg' m m']
        simp only [smul_eq_mul]
        ring
  refine ⟨⟨K, Matrix.mem_unitaryGroup_iff'.2 hU⟩, ?_, ?_⟩
  · intro i l
    show ‖K i l‖ ≤ 1
    induction l using Fin.lastCases with
    | last => simpa [K] using hv i
    | cast m =>
      simp only [K, Matrix.of_apply, Fin.lastCases_castSucc]
      have hcm : ‖c m‖ ≤ 1 := by
        rw [hc]
        exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun j _ => by
          rw [norm_mul, Pi.star_apply, hst]; exact mul_le_one₀ (hv _) (norm_nonneg _) (hgi _ _))
      refine (nsub _ _).trans (max_le ?_ ?_)
      · induction i using Fin.lastCases with
        | last => simp
        | cast j => simpa using hgi j m
      · rw [norm_mul]; exact mul_le_one₀ hcm (norm_nonneg _) (hv _)
  · show K *ᵥ Pi.single (Fin.last r) 1 = v
    rw [Matrix.mulVec_single_one]; exact cl

end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive

theorem uO_transitive : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 →
    ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  intro F E _ _ _ _ _ r v hv h1
  haveI := Unram.ultraE (F := F) (E := E)
  have hst : ∀ x : E, ‖star x‖ = ‖x‖ := Unram.norm_star (F := F)
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le (Finset.univ : Finset (Fin (r + 1)))
    (fun i => star (v i) * v i)
  have hs : (∑ j, star (v j) * v j) = 1 := h1
  rw [hs, norm_one, norm_mul, hst] at hi
  have hvi : ‖v i‖ = 1 := by nlinarith [hv i, norm_nonneg (v i)]
  set σ : Equiv.Perm (Fin (r + 1)) := Equiv.swap i (Fin.last r) with hσ
  have hσσ : ∀ j, σ (σ j) = j := fun j => Equiv.swap_apply_self _ _ _
  have h1' : star (v ∘ σ) ⬝ᵥ (v ∘ σ) = 1 := by
    rw [← hs]; exact Equiv.sum_comp σ (fun j => star (v j) * v j)
  have hn' : ‖(v ∘ σ) (Fin.last r)‖ = 1 := by simp [hσ, hvi]
  obtain ⟨k, hk, hkv⟩ := uO_transitive_of_last_unit F E r (v ∘ σ) (fun j => hv _) h1' hn'
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) E := k.1.submatrix σ id
  have hU : star K * K = 1 := by
    have hk1 : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
    ext a b
    rw [← hk1]
    simp only [K, Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, id]
    exact Equiv.sum_comp σ (fun j => star (k.1 j a) * k.1 j b)
  refine ⟨⟨K, Matrix.mem_unitaryGroup_iff'.2 hU⟩, fun a b => hk (σ a) b, ?_⟩
  show K *ᵥ Pi.single (Fin.last r) 1 = v
  funext j
  have := congrFun hkv (σ j)
  rw [Matrix.mulVec_single_one] at this ⊢
  simpa [K, hσσ] using this

end GlobalTheory.UnitaryTransitive
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralUnitaryGroupTransitiveNormOneVectorsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnitaryGroup_transitive_norm_one_vectors : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 → ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  first | exact @GlobalTheory.UnitaryTransitive.uO_transitive | exact GlobalTheory.UnitaryTransitive.uO_transitive | (intros; apply GlobalTheory.UnitaryTransitive.uO_transitive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActLiftHermitianBlockMemIntegralUnitaryMu
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step

section Blocks
variable {r : ℕ} {E : Type} [Field E]

theorem embHom_castSucc_castSucc (M : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.castSucc b) = M a b := by
  have ha : finSumFinEquiv.symm (Fin.castSucc a) = (Sum.inl a : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc a
  have hb : finSumFinEquiv.symm (Fin.castSucc b) = (Sum.inl b : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc b
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_castSucc_last (M : Matrix (Fin r) (Fin r) E) (a : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.last r) = 0 := by
  have ha : finSumFinEquiv.symm (Fin.castSucc a) = (Sum.inl a : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc a
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_last_castSucc (M : Matrix (Fin r) (Fin r) E) (b : Fin r) :
    embHom r E M (Fin.last r) (Fin.castSucc b) = 0 := by
  have ha : finSumFinEquiv.symm (Fin.castSucc b) = (Sum.inl b : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc b
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_last_last (M : Matrix (Fin r) (Fin r) E) :
    embHom r E M (Fin.last r) (Fin.last r) = 1 := by
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, hb]

theorem eq_embHom_of_last (h : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hc : ∀ i, h i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hr : ∀ j, h (Fin.last r) j = if j = Fin.last r then 1 else 0) :
    h = embHom r E (h.submatrix Fin.castSucc Fin.castSucc) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [embHom_last_last, hr]; simp
    | cast b => rw [embHom_last_castSucc, hr]; simp [Fin.castSucc_ne_last]
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [embHom_castSucc_last, hc]; simp [Fin.castSucc_ne_last]
    | cast b => rw [embHom_castSucc_castSucc]; rfl

end Blocks

end GlobalTheory.JR.Step

namespace GlobalTheory.JR.Step

section Main
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

theorem actU_liftH_support {r : ℕ} (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ = 1)
    (g : Matrix.unitaryGroup (Fin (r + 1)) E)
    (hg : unitU (r + 1) F E (actU g (liftH X ν l)) ≠ 0) :
    ∃ k ∈ uO (r + 1) E, ∃ s, g = k * uEmb r E s := by
  have hmem := Set.mem_of_indicator_ne_zero hg
  have hv : ∀ i, ‖(g.1 *ᵥ (ν • eL r E)) i‖ ≤ 1 := hmem.2.1
  set v : Fin (r + 1) → E := fun i => g.1 i (Fin.last r) with hvdef
  have hgv : g.1 *ᵥ eL r E = v := by
    funext i; simp [eL, Matrix.mulVec_single_one, v]
  have hint : ∀ i, ‖v i‖ ≤ 1 := by
    intro i
    have := hv i
    rw [Matrix.mulVec_smul, hgv, Pi.smul_apply, smul_eq_mul, norm_mul, hν, one_mul] at this
    exact this
  have hunit : star v ⬝ᵥ v = 1 := by
    have h1 : (star g.1 * g.1) (Fin.last r) (Fin.last r) = 1 := by
      rw [Matrix.mem_unitaryGroup_iff'.mp g.2]; simp
    rw [← h1]
    simp [dotProduct, Matrix.mul_apply, v, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  obtain ⟨k, hk, hke⟩ := GlobalTheory.T.integralUnitaryGroup_transitive_norm_one_vectors F E r v hint hunit
  set h := k⁻¹ * g with hh
  have he : h.1 *ᵥ eL r E = eL r E := by
    have hgk : g.1 *ᵥ eL r E = k.1 *ᵥ eL r E := by rw [hgv]; exact hke.symm
    have hk1 : (k⁻¹).1 = star k.1 := rfl
    calc h.1 *ᵥ eL r E = star k.1 *ᵥ (g.1 *ᵥ eL r E) := by
          rw [Matrix.mulVec_mulVec, ← hk1]; rfl
      _ = star k.1 *ᵥ (k.1 *ᵥ eL r E) := by rw [hgk]
      _ = eL r E := by rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp k.2, Matrix.one_mulVec]
  have hse : star h.1 *ᵥ eL r E = eL r E := by
    conv_lhs => rw [← he]
    rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp h.2, Matrix.one_mulVec]
  have hc : ∀ i, h.1 i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
    intro i
    have := congrFun he i
    simpa [eL, Matrix.mulVec_single_one, Pi.single_apply] using this
  have hr : ∀ j, h.1 (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
    intro j
    have h0 := congrArg star (congrFun hse j)
    simp only [eL, Matrix.mulVec_single_one, Pi.single_apply, Matrix.star_eq_conjTranspose] at h0
    have h3 : star ((h.1)ᴴ.col (Fin.last r) j) = h.1 (Fin.last r) j := by
      simp [Matrix.col, Matrix.conjTranspose_apply]
    rw [← h3, h0]
    split_ifs <;> simp
  set S := h.1.submatrix Fin.castSucc Fin.castSucc with hSdef
  have hS : h.1 = embHom r E S := eq_embHom_of_last h.1 hc hr
  have hstar : star (embHom r E S) = embHom r E (star S) := by
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one]
  have h1 : embHom r E (S * star S) = 1 := by
    rw [map_mul, ← hstar, ← hS]; exact Matrix.mem_unitaryGroup_iff.mp h.2
  have hSu : S ∈ Matrix.unitaryGroup (Fin r) E := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext a b
    have h2 := congrFun (congrFun h1 (Fin.castSucc a)) (Fin.castSucc b)
    rw [embHom_castSucc_castSucc] at h2
    rw [h2]
    simp [Matrix.one_apply, Fin.castSucc_inj]
  refine ⟨k, hk, ⟨S, hSu⟩, ?_⟩
  have hu : uEmb r E ⟨S, hSu⟩ = h := Subtype.ext hS.symm
  rw [hu, hh, mul_inv_cancel_left]

end Main

end GlobalTheory.JR.Step

theorem GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s :=
  fun X ν l hν g hg => GlobalTheory.JR.Step.actU_liftH_support X ν l hν g hg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActLiftHermitianBlockMemIntegralUnitaryMuStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAct_liftHermitianBlock_mem_integralUnitary_mul_embedding : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s := by
  first | exact @GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb | exact GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb | (intros; apply GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb <;> assumption)
end
