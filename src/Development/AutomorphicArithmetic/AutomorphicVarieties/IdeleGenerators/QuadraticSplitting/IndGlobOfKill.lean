module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MixMatrixResidueProperties
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd.S2 GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem um_add_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

private theorem um_add_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

private theorem um_sub_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a - b‖ < 1 := by
  rw [sub_eq_add_neg]; exact um_add_lt ha (by rwa [norm_neg])

private theorem um_sub_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact um_add_le ha (by rwa [norm_neg])

private theorem le_of_cong {a x : K} (h : ‖a - x‖ < 1) (hx : ‖x‖ = 1) : ‖a‖ ≤ 1 := by
  have := um_add_le h.le hx.le
  rwa [sub_add_cancel] at this

private theorem diff_lt {a b x : K} (ha : ‖a - x‖ < 1) (hb : ‖b - x‖ < 1) : ‖a - b‖ < 1 := by
  have := um_sub_lt ha hb
  rwa [sub_sub_sub_cancel_right] at this

private theorem half_lt (h2 : ‖(2 : K)‖ = 1) {a b x : K} (ha : ‖a - x‖ < 1) (hb : ‖b - x‖ < 1) :
    ‖(2 : K)⁻¹ * (a + b) - x‖ < 1 := by
  have h0 : (2 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; exact zero_ne_one h2
  have e : (2 : K)⁻¹ * (a + b) - x = (2 : K)⁻¹ * ((a - x) + (b - x)) := by
    field_simp; ring
  rw [e, norm_mul, norm_inv, h2, inv_one, one_mul]
  exact um_add_lt ha hb

private theorem key (h2 : ‖(2 : K)‖ = 1) (γ : Kˣ) (x : K) (A B : Matrix (Fin 2) (Fin 2) K) (hγ : ‖(γ : K)‖ = 1) (hx : ‖x‖ = 1)
    (a00 : ‖A 0 0 - 1‖ < 1) (a11 : ‖A 1 1 - x‖ < 1) (a10 : ‖A 1 0‖ < 1) (a01 : ‖A 0 1‖ ≤ 1)
    (b00 : ‖B 0 0 - 1‖ < 1) (b11 : ‖B 1 1 - x‖ < 1) (b10 : ‖B 1 0‖ < 1) (b01 : ‖B 0 1‖ ≤ 1) :
    (∀ i j, ‖mix γ A B i j‖ ≤ 1) ∧ (∀ i, ‖mix γ A B i i - ![x, 1, x, 1] i‖ < 1) ∧
    (∀ i j, i ≠ j → wt i j ∉ vV → ‖mix γ A B i j‖ < 1) ∧
    (‖A 0 1‖ = 1 → ‖mix γ A B 1 0‖ = 1 ∨ (‖mix γ A B 1 2‖ = 1 ∧ ‖mix γ A B 3 0‖ = 1)) := by
  have hh : ∀ y : K, ‖(2 : K)⁻¹ * y‖ = ‖y‖ := fun y => by rw [norm_mul, norm_inv, h2, inv_one, one_mul]
  have h0 : (2 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; exact zero_ne_one h2
  have p : ‖A 1 0 / γ‖ < 1 := by rwa [norm_div, hγ, div_one]
  have p' : ‖-(A 1 0 / γ)‖ < 1 := by rwa [norm_neg]
  have qe : ‖γ * A 0 1‖ = ‖A 0 1‖ := by rw [norm_mul, hγ, one_mul]
  have q : ‖γ * A 0 1‖ ≤ 1 := qe ▸ a01
  have q' : ‖-(γ * A 0 1)‖ ≤ 1 := by rwa [norm_neg]
  have c00 := le_of_cong a00 norm_one
  have c11 := le_of_cong a11 hx
  have d00 := le_of_cong b00 norm_one
  have d11 := le_of_cong b11 hx
  have e01 : ‖mix γ A B 0 1‖ < 1 := (hh _).trans_lt (um_sub_lt p b10)
  have e02 : ‖mix γ A B 0 2‖ < 1 := (hh _).trans_lt (diff_lt b11 a11)
  have e03 : ‖mix γ A B 0 3‖ < 1 := (hh _).trans_lt (um_add_lt p b10)
  have e13 : ‖mix γ A B 1 3‖ < 1 := (hh _).trans_lt (diff_lt a00 b00)
  have e20 : ‖mix γ A B 2 0‖ < 1 := (hh _).trans_lt (diff_lt b11 a11)
  have e21 : ‖mix γ A B 2 1‖ < 1 := (hh _).trans_lt (um_sub_lt p' b10)
  have e23 : ‖mix γ A B 2 3‖ < 1 := (hh _).trans_lt (um_add_lt p' b10)
  have e31 : ‖mix γ A B 3 1‖ < 1 := (hh _).trans_lt (diff_lt a00 b00)
  have e00 : ‖mix γ A B 0 0‖ ≤ 1 := (hh _).trans_le (um_add_le c11 d11)
  have e11 : ‖mix γ A B 1 1‖ ≤ 1 := (hh _).trans_le (um_add_le c00 d00)
  have e22 : ‖mix γ A B 2 2‖ ≤ 1 := (hh _).trans_le (um_add_le c11 d11)
  have e33 : ‖mix γ A B 3 3‖ ≤ 1 := (hh _).trans_le (um_add_le c00 d00)
  have e10 : ‖mix γ A B 1 0‖ ≤ 1 := (hh _).trans_le (um_sub_le q b01)
  have e12 : ‖mix γ A B 1 2‖ ≤ 1 := (hh _).trans_le (um_sub_le q' b01)
  have e30 : ‖mix γ A B 3 0‖ ≤ 1 := (hh _).trans_le (um_add_le q b01)
  have e32 : ‖mix γ A B 3 2‖ ≤ 1 := (hh _).trans_le (um_add_le q' b01)
  refine ⟨fun i j => ?_, fun i => ?_, fun i j hij hw => ?_, fun h => ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [e00, e01.le, e02.le, e03.le, e10, e11, e12, e13.le, e20.le, e21.le, e22, e23.le, e30, e31.le, e32, e33]
  · fin_cases i
    exacts [half_lt h2 a11 b11, half_lt h2 a00 b00, half_lt h2 a11 b11, half_lt h2 a00 b00]
  · fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact (hw (by decide)).elim
      | assumption
  · have m10 : mix γ A B 1 0 = (2 : K)⁻¹ * (γ * A 0 1 - B 0 1) := rfl
    have m12 : mix γ A B 1 2 = (2 : K)⁻¹ * (-(γ * A 0 1) - B 0 1) := rfl
    have m30 : mix γ A B 3 0 = (2 : K)⁻¹ * (γ * A 0 1 + B 0 1) := rfl
    have s : mix γ A B 1 0 + mix γ A B 3 0 = γ * A 0 1 := by
      rw [m10, m30]; field_simp; ring
    have n : ‖mix γ A B 1 2‖ = ‖mix γ A B 3 0‖ := by
      rw [← norm_neg, m12, m30]; congr 1; ring
    rcases e10.eq_or_lt with h1 | h1
    · exact Or.inl h1
    rcases e30.eq_or_lt with h3 | h3
    · exact Or.inr ⟨n.trans h3, h3⟩
    have := um_add_lt h1 h3
    rw [s, qe, h] at this
    exact absurd this (lt_irrefl _)

end

theorem UpperTheory.mixMatrix_residue_properties :
    UpperTheory.V.Sd.S2.MixRes := by
  intro l hl l2 γ x A B hγ hx hA hB
  have h2 : ‖(2 : Qbar l)‖ = 1 := by
    have e : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by
      rw [map_natCast]; rfl
    rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hl.out Nat.prime_two).2 l2
  exact key h2 γ x A B hγ hx hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2 GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem c_trans {a b x : K} (ha : ‖a - b‖ < 1) (hb : ‖b - x‖ < 1) : ‖a - x‖ < 1 := by
  have := (IsUltrametricDist.norm_add_le_max (a - b) (b - x)).trans_lt (max_lt ha hb)
  rwa [sub_add_sub_cancel] at this

omit [IsUltrametricDist K] in
private theorem c_symm {a b : K} (ha : ‖a - b‖ < 1) : ‖b - a‖ < 1 := by rwa [norm_sub_rev]

omit [IsUltrametricDist K] in
private theorem c_neg {a b : K} (ha : ‖a - b‖ < 1) : ‖-a - -b‖ < 1 := by
  rw [← neg_sub', norm_neg]; exact ha

private theorem c_norm {a x : K} (h : ‖a - x‖ < 1) (hx : ‖x‖ = 1) : ‖a‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - x) (y := x) (by rw [hx]; exact h.ne)
  rw [sub_add_cancel, hx, max_eq_right h.le] at this
  exact this

private theorem c_mul {a b x y : K} (ha : ‖a - x‖ < 1) (hb : ‖b - y‖ < 1) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖a * b - x * y‖ < 1 := by
  have e : a * b - x * y = (a - x) * b + x * (b - y) := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rwa [norm_mul, c_norm hb hy, mul_one]
  · rwa [norm_mul, hx, one_mul]

private def Sh (M : M4 K) (x : Fin 4 → K) : Prop :=
  (∀ i j, ‖M i j‖ ≤ 1) ∧ (∀ i, ‖M i i - x i‖ < 1) ∧ ∀ i j, i ≠ j → wt i j ∉ vV → ‖M i j‖ < 1

private theorem Sh.mul_diag {M : M4 K} {x d y : Fin 4 → K} (h : Sh M x) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hd : ∀ i, ‖d i - y i‖ < 1) : Sh (M * Matrix.diagonal d) (fun i => x i * y i) := by
  have n : ∀ i j, ‖(M * Matrix.diagonal d) i j‖ = ‖M i j‖ := fun i j => by
    rw [Matrix.mul_diagonal, norm_mul, c_norm (hd j) (hy j), mul_one]
  refine ⟨fun i j => (n i j).trans_le (h.1 i j), fun i => ?_, fun i j a b => (n i j).trans_lt (h.2.2 i j a b)⟩
  rw [Matrix.mul_diagonal]
  exact c_mul (h.2.1 i) (hd i) (hx i) (hy i)

private theorem Sh.smul {M : M4 K} {x : Fin 4 → K} {d : K} (h : Sh M x) (hx : ∀ i, ‖x i‖ = 1)
    (hd : ‖d - 1‖ < 1) : Sh (d • M) x := by
  have n : ∀ i j, ‖(d • M) i j‖ = ‖M i j‖ := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, c_norm hd norm_one, one_mul]
  refine ⟨fun i j => (n i j).trans_le (h.1 i j), fun i => ?_, fun i j a b => (n i j).trans_lt (h.2.2 i j a b)⟩
  have := c_mul hd (h.2.1 i) norm_one (hx i)
  rwa [one_mul] at this

end

private theorem gsp_smul {K : Type} [CommRing K] {ν d : K} {M : M4 K} (h : IsGSp ν M) : IsGSp (d ^ 2 * ν) (d • M) := by
  have e : adj (d • M) = d • adj M := by
    ext i j
    simp only [adj_apply, Matrix.smul_apply]
    rw [smul_comm]
  unfold IsGSp at *
  rw [e, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul, smul_smul, pow_two]

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem mem_range (F : IntermediateField ℚ Ω) (g : G ℚ Ω) : g ∈ (resQ F).range ↔ g ∈ F.fixingSubgroup := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact h.commutes ⟨x, hx⟩
  · intro hg
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact ⟨{ g.toRingEquiv with commutes' := fun x => hg x.1 x.2 }, rfl⟩

private theorem cont_res (F : IntermediateField ℚ Ω) : Continuous (resQ F) :=
  UpperTheory.V.Af.continuous_restrictScalarsHom ℚ F Ω

end

theorem UpperTheory.V.Sd.S2.indGlob_of_kill (hk : IndKill) : IndGlob := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H
  have val : ∀ g, twF T R δ g = (δ g : Qbar l) • (R (resQ T.F g) : M4 (Qbar l)) := fun g => tw_val _ _ g
  have un : ∀ i g, ‖(ch T i g : Qbar l)‖ = 1 := fun i g => H.chars.unit _ g
  have nα : ‖(α : Qbar l)‖ = 1 := c_norm H.α_cong (un _ _)
  have nβ : ‖(β : Qbar l)‖ = 1 := c_norm H.β_cong (un _ _)
  have nγ : ‖((β / α : (Qbar l)ˣ) : Qbar l)‖ = 1 := by
    rw [Units.val_div_eq_div_val, norm_div, nα, nβ, div_one]
  have nrm : (resQ k₀).range.Normal := Subgroup.normal_of_index_eq_two H.mix.index
  have inn : ∀ (g : G T.F Ω) (h : G k₀ Ω), resQ k₀ h = resQ T.F g →
      Sh (R (resQ T.F g) : M4 (Qbar l)) (fun i => ch T i (resQ T.F g)) ∧ (‖r h 0 1‖ = 1 →
        ‖R (resQ T.F g) 1 0‖ = 1 ∨ (‖R (resQ T.F g) 1 2‖ = 1 ∧ ‖R (resQ T.F g) 3 0‖ = 1)) := by
    intro g h hg
    obtain ⟨h', hh'⟩ := nrm.conj_mem' (resQ k₀ h) ⟨h, rfl⟩ (resQ T.F T.g0)
    have e := H.mix.on h h' hh'
    have a := H.rib h ((mem_range _ _).1 ⟨g, hg.symm⟩)
    have b := H.rib h' ((mem_range _ _).1 ⟨T.g0⁻¹ * g * T.g0, by rw [hh', hg, map_mul, map_mul, map_inv]⟩)
    have ex : up D.ξ (resQ k₀ h') = up D.ξ (resQ k₀ h) := by
      rw [hh', map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
    rw [ex] at b
    obtain ⟨m1, m2, m3, m4⟩ := UpperTheory.mixMatrix_residue_properties l H.hyp.good.l_odd (β / α) _ (r h) (r h') nγ (H.chars.unit _ _) a b
    rw [← e, hg] at m1 m2 m3 m4
    refine ⟨⟨m1, fun i => c_trans (m2 i) (c_symm ?_), m3⟩, m4⟩
    have := H.chars.inn g ((mem_range _ _).1 ⟨h, hg⟩) i
    fin_cases i <;> exact this
  have all : ∀ g : G T.F Ω, Sh (R (resQ T.F g) : M4 (Qbar l)) (fun i => ch T i (resQ T.F g)) := by
    intro g
    by_cases hg : resQ T.F g ∈ (resQ k₀).range
    · obtain ⟨h, hh⟩ := hg
      exact (inn g h hh).1
    · have : resQ T.F (g * T.g0⁻¹) ∈ (resQ k₀).range := by
        rw [map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two H.mix.index, inv_mem_iff]
        exact iff_of_false hg H.mix.nmem
      obtain ⟨h, hh⟩ := this
      have s := (inn _ h hh).1.mul_diag (d := ![(β : Qbar l), -(α : Qbar l), -(β : Qbar l), (α : Qbar l)])
        (y := fun i => ch T i (resQ T.F T.g0)) (fun i => un _ _) (fun i => un _ _) (by
          intro i
          fin_cases i
          · exact H.β_cong
          · exact c_trans (c_neg H.α_cong) (c_symm H.chars.c1)
          · exact c_trans (c_neg H.β_cong) (c_symm H.chars.c2)
          · exact H.α_cong)
      rw [← H.mix.off, ← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel_right] at s
      convert s using 2 with i
      rw [← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]
  have all' : ∀ g : G T.F Ω, Sh (twF T R δ g) (fun i => ch T i (resQ T.F g)) := fun g => by
    rw [val]
    exact (all g).smul (fun i => un _ _) (H.δ_one g)
  refine ⟨?_, fun g => ?_, hk Ω l c D T k₀ φ ι k t r α β R δ H, ?_, fun g => (all' g).1, fun g => (all' g).2.1,
    fun g => (all' g).2.2, ?_⟩
  · rw [show (twF T R δ : G T.F Ω → M4 (Qbar l)) = _ from funext val]
    exact (Units.continuous_val.comp H.δ_cont).smul (Units.continuous_val.comp (H.cont.comp (cont_res T.F)))
  · rw [val, ← H.δ_sq g, Units.val_mul, Units.val_pow_eq_pow_val]
    exact gsp_smul (H.gsp _)
  · rw [val, H.mix.off]
    exact (Matrix.isDiag_diagonal _).smul _
  · obtain ⟨h, hF, h1⟩ := H.ns
    obtain ⟨g, hg⟩ := (mem_range _ _).2 hF
    have n : ∀ i j, ‖twF T R δ g i j‖ = ‖R (resQ T.F g) i j‖ := fun i j => by
      rw [val, Matrix.smul_apply, smul_eq_mul, norm_mul, c_norm (H.δ_one g) norm_one, one_mul]
    rcases (inn g h hg.symm).2 h1 with e | ⟨e, e'⟩
    · exact Or.inl ⟨g, (n _ _).trans e⟩
    · exact Or.inr ⟨⟨g, (n _ _).trans e⟩, g, (n _ _).trans e'⟩
