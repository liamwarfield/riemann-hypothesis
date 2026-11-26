module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnAverageQuasiInvariant
noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.JSBound

section Lattice

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unif_ne_zero : (uniformizer F : F) ≠ 0 := fun h =>
  valuation_uniformizer_ne_zero F (by rw [h, map_zero])

theorem unif_pow_ne_zero (M : ℕ) : (uniformizer F : F) ^ M ≠ 0 := pow_ne_zero _ unif_ne_zero

theorem exists_unif_pow_mul_mem (x : F) : ∃ m : ℕ, (uniformizer F : F) ^ m * x ∈ 𝒪[F] := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hvx : ValuativeRel.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one F) (Units.mk0 _ hvx)⁻¹
  refine ⟨m, ?_⟩
  have h1 : ValuativeRel.valuation F (uniformizer F : F) ^ m * ValuativeRel.valuation F x < 1 := by
    have := mul_lt_mul_of_pos_right hm (zero_lt_iff.mpr hvx)
    simpa [hvx] using this
  rw [Valuation.mem_integer_iff, map_mul, map_pow]
  exact h1.le

theorem unif_pow_mul_mem_of_le {m m' : ℕ} (h : m ≤ m') {y : F}
    (hy : (uniformizer F : F) ^ m * y ∈ 𝒪[F]) : (uniformizer F : F) ^ m' * y ∈ 𝒪[F] := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : (uniformizer F : F) ^ d ∈ 𝒪[F] := pow_mem (uniformizer F).2 d
  have := mul_mem h1 hy
  rwa [← mul_assoc, ← pow_add, add_comm d m] at this

theorem exists_div_unif_pow_smul {ι : Type} [Finite ι] (A : Matrix ι ι F) (c : ℕ) :
    ∃ N : ℕ, ∀ M, N ≤ M → Div c ((uniformizer F : F) ^ M • A) := by
  classical
  cases nonempty_fintype ι
  choose f hf using fun p : ι × ι => exists_unif_pow_mul_mem (A p.1 p.2)
  refine ⟨c + Finset.univ.sup f, fun M hM i j => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hle : f (i, j) ≤ Finset.univ.sup f + d :=
    (Finset.le_sup (f := f) (Finset.mem_univ (i, j))).trans (Nat.le_add_right _ _)
  refine ⟨_, unif_pow_mul_mem_of_le hle (hf (i, j)), ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_add, add_assoc]

def scG (m M : ℕ) : GL (Fin m) F where
  val := ((uniformizer F : F) ^ M)⁻¹ • (1 : Matrix (Fin m) (Fin m) F)
  inv := ((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)
  val_inv := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (unif_pow_ne_zero M), one_mul, one_smul]
  inv_val := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ (unif_pow_ne_zero M), one_mul, one_smul]

theorem image_scG_lat (m M : ℕ) :
    (fun x => ((scG m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x) '' lat F m 0 =
      lat F m M := by
  have hval : ((scG m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((uniformizer F : F) ^ M)⁻¹ • (1 : Matrix (Fin m) (Fin m) F) := rfl
  ext x
  simp only [Set.mem_image, hval, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    have := hy i
    simp only [pow_zero, one_mul] at this
    simpa [unif_pow_ne_zero M] using this
  · intro hx
    refine ⟨(uniformizer F : F) ^ M • x, fun i => ?_, ?_⟩
    · simpa using hx i
    · rw [smul_smul, inv_mul_cancel₀ (unif_pow_ne_zero M), one_smul]

end Lattice

theorem column_average_quasi_invariant : L0 → ColumnsMirabolic → FormCoefficientStability → FormQuasiInvariantMirabolic := by
  intro h0 h3 h4 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B B' hk hI hC g hg u' u
  have H0 := h0 F μ ψ hψ
  obtain ⟨-, -, -, hPP, hT, -⟩ := h3 F μ ψ hψ n k hk
  have hg1 := hPP g hg
  obtain ⟨t, hdet, hcomm, hlast⟩ := hT g hg1
  have hlast' := hlast hg
  have := Measures.metrizableSpace F
  obtain ⟨T, hTdef⟩ : ∃ T, T = (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) := ⟨_, rfl⟩
  obtain ⟨Ti, hTidef⟩ : ∃ Ti, Ti = ((t⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :=
    ⟨_, rfl⟩
  rw [← hTdef] at hdet hcomm hlast'
  have hTTi : ∀ x, T *ᵥ (Ti *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hTdef, hTidef, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hTiT : ∀ x, Ti *ᵥ (T *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hTdef, hTidef, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  let h : (Fin (k + 1) → F) → ℂ := fun x => ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u)
  have hpt : ∀ x, ψ (-x (Fin.last k)) * B (ρ g u') (ρ (col n k x) (ρ g u)) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        h (Ti *ᵥ x) := by
    intro x
    have e1 : col n k x * g = g * col n k (Ti *ᵥ x) := by rw [hcomm, hTTi]
    have e2 : ρ (col n k x) (ρ g u) = ρ g (ρ (col n k (Ti *ᵥ x)) u) := by
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]
    have e3 : (Ti *ᵥ x) (Fin.last k) = x (Fin.last k) := by
      have := hlast' (Ti *ᵥ x)
      rw [hTTi] at this
      exact this.symm
    rw [e2, hI.quasi g hg1]
    simp only [h, e3]
    ring
  obtain ⟨M₁, hM₁⟩ := hC (ρ g u) (ρ g u')
  obtain ⟨M₂, hM₂⟩ := hC u u'
  obtain ⟨-, c, hc⟩ := h4 F μ ψ hψ n V ρ hρ l k B hk hI u u'
  obtain ⟨N, hN⟩ := exists_div_unif_pow_smul T (c + 1)
  obtain ⟨N', hN'⟩ := exists_div_unif_pow_smul (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (c + 1)

  obtain ⟨M, hMM₁, hMN⟩ : ∃ M, M₁ ≤ M ∧ N ≤ M := ⟨max M₁ N, le_max_left _ _, le_max_right _ _⟩
  have step1 : B' (ρ g u') (ρ g u) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        ∫ x in lat F (k + 1) M, h (Ti *ᵥ x) ∂(Measure.pi fun _ => μ) := by
    rw [hM₁ M hMM₁, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hcont : Continuous fun x : Fin (k + 1) → F => Ti *ᵥ x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hmeas : MeasurableSet ((fun x => Ti *ᵥ x) '' lat F (k + 1) M) :=
    (((H0.2 (k + 1)).1 M).1.image hcont).measurableSet
  have step2 := (H0.2 (k + 1)).2 t ((fun x => Ti *ᵥ x) '' lat F (k + 1) M)
    (fun x => h (Ti *ᵥ x)) hmeas
  rw [← hTdef, Set.image_image] at step2
  simp only [hTTi, hTiT, Set.image_id'] at step2

  have hG : (fun x => (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F) : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0 =
      (fun x => Ti *ᵥ x) '' lat F (k + 1) M := by
    rw [← image_scG_lat (k + 1) M, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [Units.val_mul, ← hTidef, Matrix.mulVec_mulVec]
  have hGdiv : Div (c + 1) (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) := by
    have : (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) F) = (uniformizer F : F) ^ M • T := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hTdef]
      change ((uniformizer F : F) ^ M • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F)) * _ = _
      rw [Matrix.smul_mul, Matrix.one_mul]
    rw [this]
    exact hN M hMN
  have step3 := hc _ hGdiv
  rw [hG] at step3

  obtain ⟨M', hM'₂, hM'N⟩ : ∃ M', M₂ ≤ M' ∧ N' ≤ M' :=
    ⟨max M₂ N', le_max_left _ _, le_max_right _ _⟩
  have hSdiv : Div (c + 1) (((scG (k + 1) M' : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) := hN' M' hM'N
  have step4 := hc _ hSdiv
  rw [image_scG_lat] at step4
  have step5 := hM₂ M' hM'₂
  have hmod : (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - k) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        ((Measures.modulus T.det : ℝ) : ℂ) := by
    rw [hdet, ← pow_succ]
    congr 1
    omega
  rw [step1, step2, hmod, mul_assoc]
  congr 2
  rw [step5, step4]
  exact step3

end GlobalTheory.CompanionTheory.JSBound

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoZeroOfSumSqLe
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisTer
theorem UpperTheory.Reformulated.B.DYhd3.main :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
      (∀ (u u' : V), (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ[ℂ] ℂ) u : V → ℂ) u') = ((B : V → V →ₗ[ℂ] ℂ) u' : V → ℂ) u) →
        (∀ (u : V), (0 : ℝ) ≤ (((B : V → V →ₗ[ℂ] ℂ) u : V → ℂ) u).re) →
          ∀ (x y : V),
            ‖((B : V → V →ₗ[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤
              (((B : V → V →ₗ[ℂ] ℂ) x : V → ℂ) x).re * (((B : V → V →ₗ[ℂ] ℂ) y : V → ℂ) y).re := by
  intro V _ _ B hsymm hpos x y
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun u v => B u v
      conj_inner_symm := fun u v => hsymm v u
      re_inner_nonneg := fun u => hpos u
      add_left := fun u v w => by simp
      smul_left := fun u v r => by simp }
  have h : ‖B x y‖ * ‖B y x‖ ≤ (B x x).re * (B y y).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (c := c) x y
  have h2 : ‖B y x‖ = ‖B x y‖ := by
    rw [← hsymm x y]; exact RCLike.norm_conj _
  rw [h2] at h
  rw [sq]
  exact h
end

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.Satake

theorem norm_sq_le_of_psd {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (herm : ∀ u u', starRingEnd ℂ (B u u') = B u' u) (psd : ∀ u, 0 ≤ (B u u).re) (x y : V) :
    ‖B x y‖ ^ 2 ≤ (B x x).re * (B y y).re :=
  _root_.UpperTheory.Reformulated.B.DYhd3.main B herm psd x y

theorem tendsto_zero_of_sum_sq_le (g : ℕ → ℂ) (D : ℝ)
    (hD : ∀ T, ∑ j ∈ Finset.range T, ‖g j‖ ^ 2 ≤ D) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  have hs : Summable fun j => ‖g j‖ ^ 2 :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) hD
  have h0 := hs.tendsto_atTop_zero
  have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
  rw [Real.sqrt_zero] at h1
  refine tendsto_zero_iff_norm_tendsto_zero.2 (h1.congr fun j => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

theorem recursion_scaled {n : ℕ} (s : ℂ) (hs : s ≠ 0) (z : Fin n → ℂ) (h : ℕ → ℂ) (j : ℕ)
    (hrec : ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) * h (j - r) = 0) :
    ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) *
        (h (j - r) / s ^ (j - r)) = 0 := by
  have key : ∀ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) *
        (h (j - r) / s ^ (j - r)) = ((-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) * h (j - r)) / s ^ j := by
    intro r hr
    have hrj : r ≤ j := by simpa [Nat.lt_succ_iff] using hr
    have e1 : (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) =
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) / s ^ r := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 hS).2]
    have e2 : s ^ j = s ^ r * s ^ (j - r) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e1, e2]
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, hrec, zero_div]

theorem bound_arith (r : ℝ) (hr : 0 < r) (m j : ℕ) (W H a b : ℝ)
    (hcs : (W * ((r ^ ((m + 1) * j))⁻¹ * H)) ^ 2 ≤ a * b) :
    W ^ 2 * (H / r ^ j) ^ 2 ≤ a * ((r ^ 2) ^ (j * m) * b) := by
  have hY : (r ^ 2) ^ (j * m) = (r ^ (j * m)) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hXY : r ^ ((m + 1) * j) = r ^ j * r ^ (j * m) := by
    rw [← pow_add]
    congr 1
    ring
  have hX : r ^ j ≠ 0 := (pow_pos hr _).ne'
  have hYn : r ^ (j * m) ≠ 0 := (pow_pos hr _).ne'
  have e : W ^ 2 * (H / r ^ j) ^ 2 = (r ^ (j * m)) ^ 2 * (W * ((r ^ ((m + 1) * j))⁻¹ * H)) ^ 2 := by
    rw [hXY]
    field_simp
  rw [e, hY]
  calc _ ≤ (r ^ (j * m)) ^ 2 * (a * b) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by ring

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem inU_zero_of_mem {g : GL (Fin n) F} (hg : g ∈ unipotent F n) : inU 0 g := by
  refine ⟨hg, fun i j hj => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [hg.2 i, Matrix.one_apply_eq]
  · have hlt : j < i := by
      have : (j : ℕ) < i := by
        have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
        omega
      exact this
    rw [hg.1 hlt, Matrix.one_apply_ne hij]

theorem antitone_single (hn : 0 < n) (j : ℕ) :
    Antitone (Pi.single (⟨0, hn⟩ : Fin n) (j : ℤ) : Fin n → ℤ) := by
  intro a b hab
  by_cases hb : b = ⟨0, hn⟩
  · have ha : a = ⟨0, hn⟩ := by
      subst hb
      exact Fin.ext (by have h : (a : ℕ) ≤ 0 := hab; show (a : ℕ) = 0; omega)
    rw [ha, hb]
  · by_cases ha : a = ⟨0, hn⟩
    · simp [ha, hb]
    · simp [ha, hb]

theorem rhoPair_single_zero (hn : 0 < n) (j : ℕ) :
    rhoPair (Pi.single (⟨0, hn⟩ : Fin n) (j : ℤ) : Fin n → ℤ) = ((n : ℤ) - 1) * j := by
  rw [rhoPair, Finset.sum_eq_single (⟨0, hn⟩ : Fin n) (fun b _ hb => by simp [hb])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

end

theorem l10 : L6 → L7 → L8 → liftZP_newton → ParameterUpperBound := by
  intro h6 h7 h8 h9
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hsm hn l B hW hU v z hH hg i
  obtain ⟨g₀, hg₀⟩ := hg
  have hlv : l v ≠ 0 := by
    intro h0
    apply hg₀
    rw [h7 F ψ hψ n V ρ v z hH l hW g₀, h0, zero_mul]
  obtain ⟨B', hI, hbd⟩ := h6 F μ ψ hψ n V ρ hsm l B hn hW hU
  obtain ⟨C, hC⟩ := hbd v hH.1
  have hn0 : 0 < n := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set s := sqrtQ F with hsdef
  have hs : s ≠ 0 := sqrtQ_ne_zero
  set r := ‖s‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 hs
  have hq : (qF F : ℝ) = r ^ 2 := by
    rw [hrdef, ← norm_pow, hsdef, sqrtQ_sq, Complex.norm_natCast]
  set w := B' v v with hwdef
  have hw : w ≠ 0 := fun h => hlv (hI.null v h)
  have hW' : Whit ρ ψ (B' v) := fun g hg u => hI.equi g (inU_zero_of_mem hg) u v
  let h : ℕ → ℂ := fun j => evalAt z (schur (Pi.single (⟨0, hn0⟩ : Fin (m + 2)) (j : ℤ)))
  let a : ℕ → GL (Fin (m + 2)) F := fun j => torusPow F (m + 2) (Pi.single ⟨0, hn0⟩ (j : ℤ))
  have hC' : ∀ T : ℕ, ∑ j ∈ Finset.range T, (qF F : ℝ) ^ (j * m) *
      (B' (ρ (a j) v) (ρ (a j) v)).re ≤ C := hC
  have hval : ∀ j, B' v (ρ (a j) v) = w * ((s ^ ((m + 1) * j))⁻¹ * h j) := by
    intro j
    rw [h7 F ψ hψ (m + 2) V ρ v z hH (B' v) hW', sphericalWhittaker_torusPow hψ.1, if_pos (antitone_single hn0 j),
      halfModulus_eq, rhoPair_single_zero]
    congr 2
    rw [_root_.zpow_neg]
    congr 1
    rw [← zpow_natCast]
    congr 1
    push_cast
    ring
  let g : ℕ → ℂ := fun j => h j / s ^ j
  have hterm : ∀ j, ‖w‖ ^ 2 * ‖g j‖ ^ 2 ≤
      w.re * ((qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re) := by
    intro j
    have hcs := norm_sq_le_of_psd B' hI.herm hI.psd v (ρ (a j) v)
    rw [hval j, norm_mul, norm_mul, norm_inv, norm_pow] at hcs
    have := bound_arith r hr m j ‖w‖ ‖h j‖ w.re _ hcs
    rw [hq]
    simpa [g, norm_div, norm_pow] using this
  have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw) 2
  have hsum : ∀ T, ∑ j ∈ Finset.range T, ‖g j‖ ^ 2 ≤ w.re * C / ‖w‖ ^ 2 := by
    intro T
    rw [le_div_iff₀ hwpos, Finset.sum_mul]
    calc _ ≤ ∑ j ∈ Finset.range T,
          w.re * ((qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re) :=
          Finset.sum_le_sum fun j _ => by rw [mul_comm]; exact hterm j
      _ = w.re * ∑ j ∈ Finset.range T,
          (qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re := by rw [Finset.mul_sum]
      _ ≤ w.re * C := mul_le_mul_of_nonneg_left (hC' T) (hI.psd v)
  have htend := tendsto_zero_of_sum_sq_le g _ hsum
  obtain ⟨h80, h8r⟩ := h8 (m + 2) hn0 z
  have hg0 : g 0 = 1 := by
    simpa [g, h] using h80
  have hrec : ∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard r, ∏ i ∈ S, (z i : ℂ) / s) * g (j - r) = 0 :=
    fun j hj => recursion_scaled s hs (fun i => (z i : ℂ)) h j (h8r j hj)
  have hfin := h9 (m + 2) (fun i => (z i : ℂ) / s) g hg0 hrec htend i
  have hsq : Real.sqrt (qF F) = r := by rw [hq, Real.sqrt_sq hr.le]
  rw [hsq]
  rw [norm_div, div_lt_one hr] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.Satake
end
