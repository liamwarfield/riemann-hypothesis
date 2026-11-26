module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Assembly

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.BlockDiagMulBlockShift
section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.ConjMatrixApply
section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.PadicNormDivLeOne
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem sq_conj (d : ℕ) : conj (sq d) = -sq d := by
  simp [sq, Complex.conj_ofReal]

theorem sq_mul_sq (d : ℕ) : sq d * sq d = -(d : ℂ) := by
  rw [← pow_two]
  have h : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  rw [sq, mul_pow, h, Complex.I_sq]; ring

def Kc (d : ℕ) (hd : 0 < d) : Subfield ℂ where
  carrier := {z | ∃ q₁ q₂ : ℚ, z = q₁ + q₂ * sq d}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a + c, b + e, by push_cast; ring⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    have := sq_mul_sq d
    push_cast
    linear_combination (b * e : ℂ) * this
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    by_cases h0 : (a : ℂ) + b * sq d = 0
    · exact ⟨0, 0, by rw [h0]; simp⟩
    have hn : (a ^ 2 + d * b ^ 2 : ℚ) ≠ 0 := by
      intro hn
      have hb : b = 0 := by
        by_contra hb
        have : (0 : ℚ) < a ^ 2 + d * b ^ 2 := by
          have : (0 : ℚ) < d := by exact_mod_cast hd
          positivity
        linarith
      have ha : a = 0 := by subst hb; simpa using hn
      apply h0; subst ha; subst hb; simp
    refine ⟨a / (a ^ 2 + d * b ^ 2), -b / (a ^ 2 + d * b ^ 2), ?_⟩
    have hn' : ((a ^ 2 + d * b ^ 2 : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hn
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    have := sq_mul_sq d
    push_cast at hn' ⊢
    field_simp
    linear_combination (-(b:ℂ) ^ 2) * this

theorem conj_mem_Kc {d : ℕ} {hd : 0 < d} {z : ℂ} (hz : z ∈ Kc d hd) : conj z ∈ Kc d hd := by
  obtain ⟨a, b, rfl⟩ := hz
  exact ⟨a, -b, by simp [sq_conj]⟩

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem conj_entry_int {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} {ha : 0 < a₀} {hdK : 0 < dK} {lam : ℂ} {hlam : lam ≠ 0}
    (hCm : CmOK a₀ b₀ c₀ dK) (l : ℕ) [Fact l.Prime] (hl5 : 5 ≤ l)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) {n : Type} [Fintype n] [DecidableEq n]
    (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (hΛ : IsSelfDual (matH h) Λ)
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hIso : IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hIdx : ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)))
    (τ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (hτ : ∀ y ∈ pow4 Λ, τ y ∈ pow4 Λ) (x w : Fin 4 × n) :
    ∃ q₁ q₂ : ℚ, padicNorm l q₁ ≤ 1 ∧ padicNorm l q₂ ≤ 1 ∧
      g₁ (τ (g₁.symm (Pi.single w 1))) x = q₁ + q₂ * sq dK := by
  classical
  have hl2 : ¬ l ∣ 2 := fun h2 => by have := Nat.le_of_dvd two_pos h2; omega
  have hla : ¬ l ∣ a₀ := by
    intro hla
    apply hin
    refine ⟨(b₀ : ZMod l), ?_⟩
    have e := congrArg (Int.cast : ℤ → ZMod l) hCm.1
    push_cast at e
    have ha0 : (a₀ : ZMod l) = 0 := (CharP.cast_eq_zero_iff (ZMod l) l a₀).mpr hla
    rw [ha0] at e
    linear_combination -e
  set N := relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
    (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) with hN
  have hN0 : N ≠ 0 := fun h0 => hIdx (by rw [h0]; exact dvd_zero l)
  have hden : ¬ l ∣ 2 * N ^ 2 * a₀ := by
    intro hd
    have hp : l.Prime := Fact.out
    rcases (Nat.Prime.dvd_mul hp).mp hd with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
      · exact hl2 h''
      · exact hIdx (hp.dvd_of_dvd_pow h'')
    · exact hla h'
  have he : Pi.single w (lam * (a₀ : ℂ)) ∈ stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n) := by
    intro i _
    by_cases hi : i = w
    · subst hi
      rw [Pi.single_eq_same]
      exact (cmL a₀ b₀ dK ha hdK lam hlam).ω₁_mem_lattice
    · rw [Pi.single_eq_of_ne hi]
      exact (cmL a₀ b₀ dK ha hdK lam hlam).lattice.toAddSubgroup.zero_mem
  have h1 := idx_smul_symm_mem (cmL a₀ b₀ dK ha hdK lam hlam) h Λ hΛ g₁ hIso he
  have h3 := idx_smul_mem (cmL a₀ b₀ dK ha hdK lam hlam) Λ g₁ (hτ _ h1)
  have h4 := h3 x (Set.mem_univ x)
  obtain ⟨m, k, hmk⟩ := PeriodPair.mem_lattice.mp h4
  have hsingle : Pi.single w (lam * (a₀ : ℂ)) = (lam * (a₀ : ℂ)) • Pi.single w (1 : ℂ) := by
    ext i; by_cases hi : i = w
    · subst hi; simp
    · simp [Pi.single_eq_of_ne hi]
  rw [hsingle, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hmk
  simp only [map_smul, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at hmk
  have hω1 : (cmL a₀ b₀ dK ha hdK lam hlam).ω₁ = lam * (a₀ : ℂ) := rfl
  have hω2 : (cmL a₀ b₀ dK ha hdK lam hlam).ω₂ = lam * cmTheta b₀ dK := rfl
  rw [hω1, hω2, cmTheta] at hmk
  refine ⟨((2 * m * a₀ + k * b₀ : ℤ) : ℚ) / ((2 * N ^ 2 * a₀ : ℕ) : ℚ),
    ((k : ℤ) : ℚ) / ((2 * N ^ 2 * a₀ : ℕ) : ℚ), ?_, ?_, ?_⟩
  · rw [padicNorm.div, (padicNorm.nat_eq_one_iff _).mpr hden, div_one]; exact padicNorm.of_int _
  · rw [padicNorm.div, (padicNorm.nat_eq_one_iff _).mpr hden, div_one]; exact padicNorm.of_int _
  · have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
    have hac : (a₀ : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    set E := g₁ (τ (g₁.symm (Pi.single w 1))) x with hEdef
    have hE : ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) * E =
        lam * (2 * (m : ℂ) * a₀ + k * b₀ + k * (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) := by
      linear_combination (-2 : ℂ) * hmk
    have hc : ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) ≠ 0 := by simp [hNc, hac, hlam]
    have hE' : E = lam * (2 * (m : ℂ) * a₀ + k * b₀ + k * (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) /
        ((N : ℂ) ^ 2 * (lam * (a₀ : ℂ)) * 2) := by
      rw [eq_div_iff hc, mul_comm]; exact hE
    rw [hE']
    unfold sq
    push_cast
    field_simp

theorem gmat_eq {n : Type} [Fintype n] [DecidableEq n] (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    gmat g = LinearMap.toMatrix' (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) := by
  ext x w
  rw [LinearMap.toMatrix'_apply]
  rfl

theorem conj_matrix_apply {n : Type} [Fintype n] [DecidableEq n] (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (T : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) (x w : Fin 4 × n) :
    (LinearMap.toMatrix' (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) * T * gmat g) x w
      = g (Matrix.toLin' T (g.symm (Pi.single w 1))) x := by
  have e : LinearMap.toMatrix' (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) * T * gmat g =
      LinearMap.toMatrix' ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ Matrix.toLin' T ∘ₗ
        (g.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))) := by
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', gmat_eq, mul_assoc]
  rw [e, LinearMap.toMatrix'_apply]
  rfl

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {n : Type} [Fintype n] [DecidableEq n]

def mv {R : Type*} [Zero R] [One R] (a : Fin 4) : Matrix (Fin 4 × n) (Fin 4 × n) R :=
  fun x y => if x.1 = a ∧ y.1 = 0 ∧ x.2 = y.2 then 1 else 0

theorem mv_mul_apply {R : Type*} [CommRing R] (a : Fin 4) (G : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (z w : Fin 4 × n) : ((mv a : Matrix (Fin 4 × n) (Fin 4 × n) R) * G) z w = if z.1 = a then G (0, z.2) w else 0 := by
  simp only [Matrix.mul_apply, mv]
  by_cases h : z.1 = a
  · rw [Fintype.sum_eq_single (0, z.2)]
    · simp [h]
    · intro y hy
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hy (Prod.ext h0 h2.symm)
  · simp [h]

theorem blockShift_mul_apply {R : Type*} [CommRing R] (k : Fin 4) (G : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (z w : Fin 4 × n) : ((bmv0 k : Matrix (Fin 4 × n) (Fin 4 × n) R) * G) z w = if z.1 = 0 then G (k, z.2) w else 0 := by
  simp only [Matrix.mul_apply, bmv0]
  by_cases h : z.1 = 0
  · rw [Fintype.sum_eq_single (k, z.2)]
    · simp [h]
    · intro y hy
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hy (Prod.ext h0 h2.symm)
  · simp [h]

theorem mv_mulVec (a : Fin 4) (y : Fin 4 × n → ℂ) :
    (mv a : Matrix _ _ ℂ).mulVec y = fun x => if x.1 = a then y (0, x.2) else 0 := by
  funext x
  simp only [Matrix.mulVec, dotProduct, mv]
  by_cases h : x.1 = a
  · rw [Fintype.sum_eq_single (0, x.2)]
    · simp [h]
    · intro z hz
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hz (Prod.ext h0 h2.symm)
  · simp [h]

theorem blockShift_mulVec (k : Fin 4) (y : Fin 4 × n → ℂ) :
    (bmv0 k : Matrix _ _ ℂ).mulVec y = fun x => if x.1 = 0 then y (k, x.2) else 0 := by
  funext x
  simp only [Matrix.mulVec, dotProduct, bmv0]
  by_cases h : x.1 = 0
  · rw [Fintype.sum_eq_single (k, x.2)]
    · simp [h]
    · intro z hz
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hz (Prod.ext h0 h2.symm)
  · simp [h]

theorem mv_pres (Λ : AddSubgroup (n → ℂ)) (a : Fin 4) :
    ∀ y ∈ pow4 Λ, Matrix.toLin' (mv a : Matrix _ _ ℂ) y ∈ pow4 Λ := by
  intro y hy
  have hy' : ∀ b, slice b y ∈ Λ := hy
  show ∀ b, slice b _ ∈ Λ
  intro b
  rw [Matrix.toLin'_apply, mv_mulVec]
  by_cases h : b = a
  · subst h
    convert hy' 0 using 1
    funext i
    simp [slice]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, h]

theorem blockShift_mapsTo (Λ : AddSubgroup (n → ℂ)) (k : Fin 4) :
    ∀ y ∈ pow4 Λ, Matrix.toLin' (bmv0 k : Matrix _ _ ℂ) y ∈ pow4 Λ := by
  intro y hy
  have hy' : ∀ b, slice b y ∈ Λ := hy
  show ∀ b, slice b _ ∈ Λ
  intro b
  rw [Matrix.toLin'_apply, blockShift_mulVec]
  by_cases h : b = 0
  · subst h
    convert hy' k using 1
    funext i
    simp [slice]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, h]

theorem bd4_transpose {R : Type*} [Zero R] (P : Matrix n n R) : (bd4 P).transpose = bd4 P.transpose := by
  ext x y
  by_cases h : x.1 = y.1
  · simp [bd4, Matrix.transpose_apply, h]
  · simp [bd4, Matrix.transpose_apply, h, Ne.symm h]

theorem bd4_smul {R : Type*} [CommRing R] (c : R) (P : Matrix n n R) : bd4 (c • P) = c • bd4 P := by
  ext x y
  by_cases h : x.1 = y.1 <;> simp [bd4, h]

theorem bd4_one {R : Type*} [CommRing R] : bd4 (1 : Matrix n n R) = 1 := by
  ext x y
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp [bd4, Matrix.one_apply, Prod.ext_iff, h1, h2]

theorem blockDiag_mul_blockShift {R : Type*} [CommRing R] (P : Matrix n n R) (k : Fin 4) :
    bd4 P * bmv0 k = bmv0 k * bd4 P := by
  ext x y
  rw [blockShift_mul_apply]
  simp only [Matrix.mul_apply, bd4, bmv0]
  rw [Fintype.sum_eq_single (0, y.2)]
  · by_cases h1 : x.1 = 0 <;> by_cases h2 : y.1 = k
    · simp [h1, h2]
    · have h2' : k ≠ y.1 := fun h => h2 h.symm
      simp [h1, h2, h2']
    · simp [h1, h2]
    · simp [h1, h2]
  · intro z hz
    by_cases hc : z.1 = 0 ∧ y.1 = k ∧ z.2 = y.2
    · exact absurd (Prod.ext hc.1 hc.2.2 : z = (0, y.2)) hz
    · rw [if_neg hc, mul_zero]

theorem exists_cols (G Gi : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) (hG : G * Gi = 1) :
    ∃ w : n → Fin 4 × n, IsUnit (Matrix.of fun i j => G (0, i) (w j)) := by
  classical
  set v : Fin 4 × n → (n → ℂ) := fun j i => G (0, i) j with hv
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ j, (∑ k, Gi j (0, k) * x k) • v j := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]
      have h : ∀ k, ∑ j, G (0, i) j * Gi j (0, k) = if i = k then 1 else 0 := fun k => by
        have := congrFun (congrFun hG (0, i)) (0, k)
        simpa [Matrix.mul_apply, Matrix.one_apply] using this
      symm
      calc ∑ j, (∑ k, Gi j (0, k) * x k) * G (0, i) j
          = ∑ k, (∑ j, G (0, i) j * Gi j (0, k)) * x k := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
        _ = x i := by simp [h]
    rw [hx]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range v)
  rw [hspan] at hbspan
  let B := Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))
  let e := B.indexEquiv (Pi.basisFun ℂ n)
  have hmem : ∀ i : n, ∃ j, v j = ((e.symm i : b) : n → ℂ) := fun i => hbs (e.symm i).2
  choose w hw using hmem
  refine ⟨w, ?_⟩
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  have hfun : (Matrix.of fun i j => G (0, i) (w j)).col =
      (fun x : b => (x : n → ℂ)) ∘ e.symm := by
    funext j i
    simp [Matrix.col, Matrix.transpose_apply, ← hw j, hv]
  rw [hfun]
  exact hbli.comp _ e.symm.injective

end Blocks

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem area_cmL_ne (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) :
    area (cmL a₀ b₀ dK ha hdK lam hlam) ≠ 0 := by
  unfold area cmL scalePair cmPair
  simp only
  have e : conj (lam * (a₀ : ℂ)) * (lam * cmTheta b₀ dK) =
      (((a₀ : ℝ) * Complex.normSq lam : ℝ) : ℂ) * cmTheta b₀ dK := by
    rw [map_mul, Complex.conj_natCast]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have hth : (cmTheta b₀ dK).im = Real.sqrt dK / 2 := by
    simp [cmTheta]
  rw [e, Complex.im_ofReal_mul, hth]
  have h1 : (0 : ℝ) < a₀ := by exact_mod_cast ha
  have h2 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
  have h3 : 0 < Real.sqrt dK := Real.sqrt_pos.mpr (by exact_mod_cast hdK)
  exact abs_ne_zero.mpr (by positivity)

theorem gram_G (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hIso : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))) :
    (gmat g₁).transpose * bd4 h * (gmat g₁).map conj = (((area L : ℝ) : ℂ)⁻¹) • (1 : Matrix _ _ ℂ) := by
  ext u w
  have h1 := hIso (g₁.symm (Pi.single u 1)) (g₁.symm (Pi.single w 1))
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, stdH_apply] at h1
  have hl : ∑ i, (Pi.single u (1 : ℂ) : Fin 4 × n → ℂ) i * ((area L : ℝ) : ℂ)⁻¹ *
      conj ((Pi.single w (1 : ℂ) : Fin 4 × n → ℂ) i) =
      (((area L : ℝ) : ℂ)⁻¹ • (1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ)) u w := by
    by_cases huw : u = w
    · subst huw
      simp [Pi.single_apply, Matrix.one_apply]
    · simp [Pi.single_apply, Matrix.one_apply, huw]
      intro hi
      exact absurd hi.symm huw
  rw [hl] at h1
  rw [h1]
  simp only [matH, LinearMap.mk₂'ₛₗ_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, gmat, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem ratStep : RatStep := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hCm l _ hl5 hld hin n _ _ h Λ g₀ g₁ hLat hIso hIdx
  have hΛ : IsSelfDual (matH h) Λ := hLat.2.1
  set L := cmL a₀ b₀ dK ha hdK lam hlam with hL
  set G := gmat g₁ with hGdef
  set Gi : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
    LinearMap.toMatrix' (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) with hGidef
  have hGGi : G * Gi = 1 := by
    rw [hGdef, hGidef, gmat_eq, ← LinearMap.toMatrix'_comp]
    have : ((g₁.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
        = LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hGiG : Gi * G = 1 := by
    rw [hGdef, hGidef, gmat_eq, ← LinearMap.toMatrix'_comp]
    have : ((g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ (g₁.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
        = LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hint : ∀ T : Matrix (Fin 4 × n) (Fin 4 × n) ℂ, (∀ y ∈ pow4 Λ, Matrix.toLin' T y ∈ pow4 Λ) →
      ∀ x w, ∃ q₁ q₂ : ℚ, padicNorm l q₁ ≤ 1 ∧ padicNorm l q₂ ≤ 1 ∧ (Gi * T * G) x w = q₁ + q₂ * sq dK := by
    intro T hT x w
    rw [hGidef, hGdef, conj_matrix_apply]
    exact conj_entry_int hCm l hl5 hin h Λ hΛ g₁ hIso hIdx _ hT x w
  obtain ⟨w, hPu⟩ := exists_cols G Gi hGGi
  set P : Matrix n n ℂ := Matrix.of fun i j => G (0, i) (w j) with hP
  have hdetP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  set Pinv := P⁻¹ with hPinv
  have hPP : P * Pinv = 1 := Matrix.mul_nonsing_inv P hdetP
  have hPP' : Pinv * P = 1 := Matrix.nonsing_inv_mul P hdetP
  set S : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
    Matrix.of fun x (y : Fin 4 × n) => (Gi * (mv y.1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) * G) x (w y.2) with hS
  clear_value S
  have hGS : G * S = bd4 P := by
    ext z ⟨a, j⟩
    have e := congrFun (congrFun (show G * (Gi * (mv a : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) * G) =
      (mv a : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) * G by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGGi, Matrix.one_mul]) z) (w j)
    rw [mv_mul_apply, Matrix.mul_apply] at e
    rw [Matrix.mul_apply]
    simp only [hS, Matrix.of_apply]
    rw [e]
    simp only [bd4, hP, Matrix.of_apply]
  have hSdef : S = Gi * bd4 P := by rw [← hGS, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
  set M := bd4 Pinv * G with hM
  clear_value M
  have hSM : S * M = 1 := by
    rw [hSdef, hM, Matrix.mul_assoc, ← Matrix.mul_assoc (bd4 P), bd4_mul, hPP, bd4_one, Matrix.one_mul, hGiG]
  have hMS : M * S = 1 := by
    rw [hSdef, hM, Matrix.mul_assoc, ← Matrix.mul_assoc G, hGGi, Matrix.one_mul, bd4_mul, hPP', bd4_one]
  have hSK : ∀ x y, S x y ∈ Kc dK hdK := fun x y => by
    obtain ⟨q₁, q₂, -, -, e⟩ := hint (mv y.1) (mv_pres Λ y.1) x (w y.2)
    exact ⟨q₁, q₂, by rw [hS]; exact e⟩
  have hMK : ∀ x y, M x y ∈ Kc dK hdK := by
    set S' : Matrix (Fin 4 × n) (Fin 4 × n) (Kc dK hdK) := Matrix.of fun x y => ⟨S x y, hSK x y⟩ with hS'
    have hS'map : S'.map (Kc dK hdK).subtype = S := by ext x y; rfl
    have hdetS : IsUnit S.det := by
      have e := congrArg Matrix.det hSM
      rw [Matrix.det_mul, Matrix.det_one] at e
      exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one e)
    have hdet : IsUnit S'.det := by
      have e : (Kc dK hdK).subtype S'.det = S.det := by rw [RingHom.map_det]; rfl
      refine isUnit_iff_ne_zero.mpr fun h0 => ?_
      rw [h0, map_zero] at e
      exact not_isUnit_zero (e ▸ hdetS)
    have hinv : S * (S'⁻¹).map (Kc dK hdK).subtype = 1 := by
      rw [← hS'map, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have e : M = (S'⁻¹).map (Kc dK hdK).subtype := by
      calc M = M * (S * (S'⁻¹).map (Kc dK hdK).subtype) := by rw [hinv, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hMS, Matrix.one_mul]
    intro x y
    rw [e]
    exact (S'⁻¹ x y).2
  have hA : ((area L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast area_cmL_ne a₀ b₀ dK ha hdK lam hlam
  have hgram := gram_G L h g₁ hIso
  have hGi : Gi.transpose * Gi.map conj = ((area L : ℝ) : ℂ) • bd4 h := by
    have e1 : Gi.transpose * (G.transpose * bd4 h * G.map conj) * Gi.map conj = bd4 h := by
      have : Gi.transpose * (G.transpose * bd4 h * G.map conj) * Gi.map conj
          = (G * Gi).transpose * bd4 h * (G * Gi).map (starRingEnd ℂ) := by
        rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      rw [this, hGGi]; simp
    rw [hGdef] at e1
    rw [hgram, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at e1
    rw [← e1, smul_smul, mul_inv_cancel₀ hA, one_smul]
  set R : Matrix n n ℂ := ((area L : ℝ) : ℂ) • (P.transpose * h * P.map conj) with hR
  clear_value R
  have hbdR : bd4 R = S.transpose * S.map conj := by
    rw [hSdef, Matrix.transpose_mul, Matrix.map_mul, bd4_transpose, bd4_map _ (map_zero _),
      show bd4 P.transpose * Gi.transpose * (Gi.map (starRingEnd ℂ) * bd4 (P.map (starRingEnd ℂ)))
        = bd4 P.transpose * (Gi.transpose * Gi.map (starRingEnd ℂ)) * bd4 (P.map (starRingEnd ℂ)) by
          simp only [Matrix.mul_assoc],
      hGi, Matrix.mul_smul, Matrix.smul_mul, bd4_mul, bd4_mul, hR, bd4_smul]
  have hRK : ∀ i j, R i j ∈ Kc dK hdK := by
    intro i j
    have e : R i j = (S.transpose * S.map conj) (0, i) (0, j) := by rw [← hbdR]; simp [bd4]
    rw [e, Matrix.mul_apply]
    exact Subfield.sum_mem _ fun x _ => Subfield.mul_mem _ (hSK x (0, i)) (conj_mem_Kc (hSK x (0, j)))
  have hGramM : M.transpose * bd4 R * M.map conj = 1 := by
    rw [hbdR]
    calc M.transpose * (S.transpose * S.map conj) * M.map conj
        = (S * M).transpose * (S * M).map (starRingEnd ℂ) := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSM]; simp
  have hUeq : ∀ k : Fin 4, (bmv0 k : Matrix _ _ ℂ) * M = M * (Gi * bmv0 k * G) := by
    intro k
    calc (bmv0 k : Matrix _ _ ℂ) * M = bmv0 k * bd4 Pinv * G := by rw [hM, Matrix.mul_assoc]
      _ = bd4 Pinv * bmv0 k * G := by rw [blockDiag_mul_blockShift]
      _ = bd4 Pinv * (G * Gi) * bmv0 k * G := by rw [hGGi, Matrix.mul_one]
      _ = M * (Gi * bmv0 k * G) := by rw [hM]; simp only [Matrix.mul_assoc]
  have hMK' : ∀ x y, ∃ q₁ q₂ : ℚ, M x y = q₁ + q₂ * sq dK := hMK
  have hRK' : ∀ i j, ∃ q₁ q₂ : ℚ, R i j = q₁ + q₂ * sq dK := hRK
  choose M₁ M₂ hMd using hMK'
  choose R₁ R₂ hRd using hRK'
  have hkM : kmat dK (Matrix.of M₁) (Matrix.of M₂) = M := by
    ext x y; simp [kmat, hMd x y, mul_comm]
  have hkMc : kmat dK (Matrix.of M₁) (-Matrix.of M₂) = M.map conj := by
    ext x y; simp [kmat, hMd x y, sq_conj, mul_comm]
  have hkR : kmat dK (Matrix.of R₁) (Matrix.of R₂) = R := by
    ext x y; simp [kmat, hRd x y, mul_comm]
  refine ⟨lam • P, Matrix.of M₁, Matrix.of M₂, Matrix.of R₁, Matrix.of R₂, 1, padicNorm.one, ?_, ?_, ?_⟩
  · rw [hkM, bd4_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hlam, one_smul, hM, ← Matrix.mul_assoc,
      bd4_mul, hPP, bd4_one, Matrix.one_mul]
  · rw [hkM, hkR, hkMc, hGramM]; simp
  · intro k
    have := hint (bmv0 k) (blockShift_mapsTo Λ k)
    choose U₁ U₂ hU₁ hU₂ hUe using this
    refine ⟨Matrix.of U₁, Matrix.of U₂, fun x y => ⟨hU₁ x y, hU₂ x y⟩, ?_⟩
    rw [hkM, hUeq k]
    congr 1
    ext x y; simp [kmat, hUe x y, mul_comm]

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
