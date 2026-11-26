module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoIrr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.RigidDiag
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem block_of_comm {K : Type} [NormedField K] [IsUltrametricDist K] (M X : M4 K) (d : Fin 4 → K)
    (hM : ∀ i j, ‖M i j - Matrix.diagonal d i j‖ < 1) (hd : ∀ i j, lamW i ≠ lamW j → ‖d i - d j‖ = 1)
    (hb : IsBlock M) (hX : IsBlock (X * M - M * X)) : IsBlock X := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4 × Fin 4))
    (fun p => ‖M p.1 p.2 - Matrix.diagonal d p.1 p.2‖) Finset.univ_nonempty
  obtain ⟨⟨i, j⟩, hq, hm⟩ := Finset.exists_max_image
    (Finset.univ.filter fun q : Fin 4 × Fin 4 => lamW q.1 ≠ lamW q.2) (fun q => ‖X q.1 q.2‖) ⟨(0, 1), by decide⟩
  have hij : lamW i ≠ lamW j := (Finset.mem_filter.1 hq).2
  have hm' : ∀ a b, lamW a ≠ lamW b → ‖X a b‖ ≤ ‖X i j‖ := fun a b h =>
    hm (a, b) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  set ρ := ‖M p.1 p.2 - Matrix.diagonal d p.1 p.2‖ with hρ
  have hρ1 : ρ < 1 := hM _ _
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  obtain ⟨N, hN⟩ : ∃ N, N = M - Matrix.diagonal d := ⟨_, rfl⟩
  have hNρ : ∀ a b, ‖N a b‖ ≤ ρ := fun a b => by
    rw [hN]; exact hp (a, b) (Finset.mem_univ _)
  have hNb : IsBlock N := fun a b h => by
    have : a ≠ b := fun e => h (by rw [e])
    rw [hN, Matrix.sub_apply, hb a b h, Matrix.diagonal_apply_ne _ this, sub_zero]
  have hMN : M = N + Matrix.diagonal d := by rw [hN, sub_add_cancel]
  have h0 := hX i j hij
  rw [hMN, mul_add, add_mul] at h0
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at h0
  have h1 : X i j * (d i - d j) = (X * N) i j + -(N * X) i j := by linear_combination -h0
  have hx0 := norm_nonneg (X i j)
  have h2 : ‖(X * N) i j‖ ≤ ‖X i j‖ * ρ := by
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    by_cases hk : lamW k = lamW j
    · rw [norm_mul]
      exact mul_le_mul (hm' i k (by rw [hk]; exact hij)) (hNρ _ _) (norm_nonneg _) hx0
    · rw [hNb k j hk, mul_zero, norm_zero]; positivity
  have h3 : ‖-(N * X) i j‖ ≤ ‖X i j‖ * ρ := by
    rw [norm_neg, Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    by_cases hk : lamW i = lamW k
    · rw [norm_mul, mul_comm]
      exact mul_le_mul (hm' k j (by rw [← hk]; exact hij)) (hNρ _ _) (norm_nonneg _) hx0
    · rw [hNb i k hk, zero_mul, norm_zero]; positivity
  have h4 : ‖X i j‖ ≤ ‖X i j‖ * ρ := by
    calc ‖X i j‖ = ‖X i j * (d i - d j)‖ := by rw [norm_mul, hd i j hij, mul_one]
      _ ≤ _ := by rw [h1]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 h3)
  have h5 : ‖X i j‖ ≤ 0 := by nlinarith
  intro a b h
  exact norm_le_zero_iff.1 ((hm' a b h).trans h5)

private theorem diag_of_comm {K : Type} [Field K] (X h : M4 K) (hX : X ∈ sp4 K) (hb : IsBlock X)
    (h02 : h 0 2 = 0) (h20 : h 2 0 = 0) (hne : h 0 0 ≠ h 2 2)
    (c02 : (X * h - h * X) 0 2 = 0) (c20 : (X * h - h * X) 2 0 = 0) :
    ∃ a b : K, ∀ (Y : M4 K) i j, (X * Y - Y * X) i j = (a * ((wt i j).1 : K) + b * ((wt i j).2 : K)) * Y i j := by
  have hs : ∀ i j, (sgn i * sgn j) • X j.rev i.rev = -X i j := fun i j => congrFun (congrFun hX i) j
  have z01 := hb 0 1 (by decide)
  have z03 := hb 0 3 (by decide)
  have z10 := hb 1 0 (by decide)
  have z12 := hb 1 2 (by decide)
  have z21 := hb 2 1 (by decide)
  have z23 := hb 2 3 (by decide)
  have z30 := hb 3 0 (by decide)
  have z32 := hb 3 2 (by decide)
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z10, z12, z21, z23, z30, z32, h02, h20] at c02 c20
  have z02 : X 0 2 = 0 := by
    have : X 0 2 * (h 0 0 - h 2 2) = 0 := by linear_combination -c02
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have z20 : X 2 0 = 0 := by
    have : X 2 0 * (h 0 0 - h 2 2) = 0 := by linear_combination c20
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have z13 : X 1 3 = 0 := by simpa [sgn, Fin.rev, z02] using hs 0 2
  have z31 : X 3 1 = 0 := by simpa [sgn, Fin.rev, z20] using hs 2 0
  have z33 : X 3 3 = -X 0 0 := by simpa [sgn, Fin.rev] using hs 0 0
  have z22 : X 2 2 = -X 1 1 := by simpa [sgn, Fin.rev] using hs 1 1
  refine ⟨X 0 0 - X 1 1, X 0 0 + X 1 1, fun Y i j => ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z10, z12, z21, z23, z30, z32, z02, z20, z13, z31, z33, z22, wt, lamW, muW] <;> ring

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem norm_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) : ‖algebraMap c.O (PadicAlgCl l) x‖ ≤ 1 :=
  norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)

private theorem norm_eq_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : residue c.O x ≠ 0) :
    ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := by
  obtain ⟨u, rfl⟩ := (residue_ne_zero_iff_isUnit x).1 hx
  have h1 : ‖algebraMap c.O (PadicAlgCl l) u‖ * ‖algebraMap c.O (PadicAlgCl l) (u⁻¹ : c.Oˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h2 := norm_le_one c u
  have h3 := norm_le_one c (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg (algebraMap c.O (PadicAlgCl l) u)
  nlinarith

theorem UpperTheory.V.GradeZeroInterpolatingElement.rigidDiag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → D.RigidAt r → ∀ r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l)), D.PtIn _ r' → (∀ g i j, (r' g i j).fst = r g i j) → ∃ a b : PadicAlgCl l, ∀ g i j, (r' g i j).snd = (a * ((wt i j).1 : PadicAlgCl l) + b * ((wt i j).2 : PadicAlgCl l)) * r g i j := by
  intro Ω _ _ _ l _ c D hD r hr hrig r' hr' hfst
  obtain ⟨X, hX, hsnd⟩ := hrig r' hr' hfst
  obtain ⟨-, hcl, -⟩ := eptInt D hD r hr
  obtain ⟨-, -, ⟨hb, h02, h20⟩, -⟩ := ptIn D hD _ r hr
  obtain ⟨-, -, ⟨hb', h02', h20'⟩, -⟩ := ptIn D hD _ r' hr'
  obtain ⟨-, hsg, -, -, -, -, -, -, -, hph, -⟩ := facts D hD
  have hr0 : ∀ g, D.r0E g = Matrix.diagonal fun i => algebraMap c.O (PadicAlgCl l) (D.ps i g) := fun g => by
    ext i j
    show algebraMap c.O (PadicAlgCl l) (Matrix.diagonal (fun i => (D.ps i g : c.O)) i j) = _
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq]
    · simp only [Matrix.diagonal_apply_ne _ h, map_zero]
  have hbar : ∀ i, Raw.bar (D.ps i) D.ph = Raw.bar (D.ps i) (D.sg l) := fun i => by
    have := congrFun (congrFun hph i) i
    change residue c.O (Matrix.diagonal (fun i => (D.ps i D.ph : c.O)) i i) =
      residue c.O (Matrix.diagonal (fun i => (D.ps i (D.sg l) : c.O)) i i) at this
    simpa only [Matrix.diagonal_apply_eq] using this
  have hXb : IsBlock X := by
    refine block_of_comm (r D.ph) X (fun i => algebraMap c.O (PadicAlgCl l) (D.ps i D.ph))
      (fun i j => by rw [← hr0]; exact hcl _ i j) (fun i j h => ?_) hb fun i j h => ?_
    · rw [← map_sub]
      refine norm_eq_one c _ ?_
      rw [map_sub, sub_ne_zero]
      have := (hsg l (Finset.mem_insert_self _ _)).2.2 i j h
      rwa [← hbar, ← hbar] at this
    · rw [← hsnd, hb' i j h]; rfl
  have hh : ∀ i j, (D.hEl r' i j).snd = (X * D.hEl r - D.hEl r * X) i j := fun i j => by
    have e : X * D.hEl r - D.hEl r * X = (X * r D.g0 - r D.g0 * X) +
        algebraMap c.O (PadicAlgCl l) (D.th D.g0) • (X * r D.g0⁻¹ - r D.g0⁻¹ * X) := by
      simp only [Raw.hEl, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, Matrix.add_apply, Matrix.smul_apply, ← hsnd, ← hsnd, Raw.hEl, Matrix.add_apply, Matrix.smul_apply,
      TrivSqZeroExt.snd_add, smul_eq_mul, smul_eq_mul, ← Algebra.smul_def, ← Algebra.smul_def]
    rfl
  have hne : D.hEl r 0 0 ≠ D.hEl r 2 2 := by
    intro he
    have hi : ∀ i, ‖D.hEl r i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0 + D.th D.g0 * D.ps i D.g0⁻¹)‖ < 1 := fun i => by
      have a1 := hcl D.g0 i i
      have a2 := hcl D.g0⁻¹ i i
      rw [hr0, Matrix.diagonal_apply_eq] at a1 a2
      have e : D.hEl r i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0 + D.th D.g0 * D.ps i D.g0⁻¹) =
          (r D.g0 i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0)) + algebraMap c.O (PadicAlgCl l) (D.th D.g0) *
            (r D.g0⁻¹ i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0⁻¹)) := by
        rw [Raw.hEl, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a1 ?_)
      rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one c _) (norm_nonneg _) a2
    have e : ((D.al D.g0 : c.O) - 1) * ((D.Psi D.g0 : c.O) - 1) =
        (D.ps 0 D.g0 + D.th D.g0 * D.ps 0 D.g0⁻¹) - (D.ps 2 D.g0 + D.th D.g0 * D.ps 2 D.g0⁻¹) := by
      have p0 : D.ps 0 = D.th := rfl
      have p2 : D.ps 2 = D.al := rfl
      have t : (D.th D.g0 : c.O) = D.al D.g0 * D.Psi D.g0 := rfl
      have u1 : (D.th D.g0 : c.O) * D.th D.g0⁻¹ = 1 := by rw [map_inv, Units.mul_inv]
      have u2 : (D.al D.g0 : c.O) * D.al D.g0⁻¹ = 1 := by rw [map_inv, Units.mul_inv]
      rw [p0, p2, u1, t]
      linear_combination (D.Psi D.g0 : c.O) * u2
    have n1 : ‖algebraMap c.O (PadicAlgCl l) (((D.al D.g0 : c.O) - 1) * ((D.Psi D.g0 : c.O) - 1))‖ = 1 := by
      refine norm_eq_one c _ ?_
      rw [map_mul, map_sub, map_sub, map_one]
      exact mul_ne_zero (sub_ne_zero.2 hD.genElt_alpha) (sub_ne_zero.2 hD.genElt_Psi)
    rw [e, map_sub] at n1
    have a1 := hi 0
    have a2 := hi 2
    rw [← he] at a2
    rw [← norm_neg] at a1
    have a3 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a1 a2)
    rw [neg_sub, sub_add_sub_cancel, n1] at a3
    exact lt_irrefl _ a3
  obtain ⟨a, b, hab⟩ := diag_of_comm X (D.hEl r) hX hXb h02 h20 hne (by rw [← hh, h02']; rfl) (by rw [← hh, h20']; rfl)
  exact ⟨a, b, fun g i j => by rw [hsnd, hab]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TanScale
section Gen

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem ts_monomial {O σ S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (f : MvPowerSeries σ O →ₐ[O] S) (m : σ →₀ ℕ) :
    f (monomial m 1) = m.prod fun s k => f (MvPowerSeries.X s) ^ k := by
  rw [← MvPolynomial.coe_monomial, GlobalTheory.algHom_coe_mvPolynomial, MvPolynomial.aeval_monomial, map_one, one_mul]

private theorem ts_prod {X σ S : Type} [AddCommGroup X] [CommRing S] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (x : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i k => ((t (Multiplicative.ofAdd (wt i)) : S) * x i) ^ k) =
      (t (Multiplicative.ofAdd (Finsupp.weight wt d)) : S) * d.prod fun i k => x i ^ k := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), hf, hg, map_add (f := _), ofAdd_add,
      map_mul, Units.val_mul]
    ring
  | single i k =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      Finsupp.weight_single, ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val, mul_pow]

private theorem ts_approx {O X σ : Type} [CommRing O] [AddCommGroup X] [Finite σ] (wt : σ → X)
    (F : MvPowerSeries σ O) (n : ℕ) :
    ∃ s : Finset X, (n : ℕ∞) ≤ (F - ∑ j ∈ s, wcomp O wt j F).order := by
  classical
  refine ⟨(truncTotal n F).support.image (Finsupp.weight wt), nat_le_order fun d hd => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra h0
    refine h (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 ?_))
    rwa [coeff_truncTotal _ hd]

private theorem ts_vanish {O X σ S : Type} [CommRing O] [AddCommGroup X] [Finite σ] [CommRing S]
    [Algebra O S] (wt : σ → X) (J : Ideal S) [IsHausdorff J S] (φ : MvPowerSeries σ O →ₐ[O] S)
    (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ J) (F : MvPowerSeries σ O) (h : ∀ j, φ (wcomp O wt j F) = 0) :
    φ F = 0 := by
  refine GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => ?_
  obtain ⟨s, hs⟩ := ts_approx wt F n
  have := GlobalTheory.algHom_mem_pow_of_le_order φ hφ hs
  simpa [h] using this

section Core

variable {O X R K : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
  [CommRing K] [Algebra O K] (ξ : W.A →ₐ[O] K)

private theorem ts_zprod (m : W.σ →₀ ℕ) :
    ((m.prod fun s k => W.zA s ^ k : W.A) : R) = W.π (monomial m 1) := by
  rw [ts_monomial]
  exact map_finsuppProd W.A.val _ _

variable [Module.Free ℤ X] [Module.Finite ℤ X] {B : Type} [CommRing B] [Algebra O B] (ι : B →ₐ[O] K)
  (t : Multiplicative X →* Kˣ) (g : MvPowerSeries W.σ O →ₐ[O] B)

private theorem ts_step (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (I J : Ideal B) (S : Set (W.σ →₀ ℕ)) (j : X) (hS : ∀ n ∈ S, Finsupp.weight W.wt n = j)
    (hJ : ∀ n ∈ S, g (monomial n 1) ∈ J)
    (hI : ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b → ∃ c, ι c = ξ x ∧ g b - c ∈ I)
    (F : MvPowerSeries W.σ O) (hF : ∀ n, n ∉ S → coeff n F = 0) (x : W.A) (hx : (x : R) = W.π F) :
    ∃ c, ι c = t (Multiplicative.ofAdd j) * ξ x ∧ g F - c ∈ I * J := by
  obtain ⟨μ, hμ, h⟩ := part_span O R X W S j hS
  obtain ⟨b, hb, rfl⟩ := h F hF
  let β : (W.σ →₀ ℕ) → W.A := fun m => ⟨W.π (b m), W.part_le_A ⟨b m, hb m, rfl⟩⟩
  choose c hc hc' using fun m => hI (b m) (hb m) (β m) rfl
  have hx' : x = ∑ m ∈ μ, β m * m.prod fun s k => W.zA s ^ k := by
    apply Subtype.ext
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Subalgebra.coe_mul, ts_zprod, map_mul]
  refine ⟨∑ m ∈ μ, c m * g (monomial m 1), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hx', map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [map_mul, map_mul, hc, ts_monomial, map_finsuppProd, map_finsuppProd]
      simp only [map_pow, hg]
      rw [ts_prod W.wt t (fun s => ξ (W.zA s)), hS m (hμ hm)]
      ring
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun m hm => ?_
      rw [map_mul, ← sub_mul]
      exact Ideal.mul_mem_mul (hc' m) (hJ m (hμ hm))

private theorem ts_agree (hι : Function.Injective ι)
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) [IsHausdorff J B] (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) (j : X) (F : MvPowerSeries W.σ O) (hF : F ∈ wtPart O W.wt j)
    (x : W.A) (hx : (x : R) = W.π F) : ι (g F) = t (Multiplicative.ofAdd j) * ξ x := by
  classical
  have hQ : ∀ N : ℕ, ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b →
      ∃ c, ι c = ξ x ∧ g b - c ∈ J ^ N := by
    intro N
    induction N with
    | zero =>
      intro b hb x hx
      obtain ⟨c, hc⟩ := h0 x ⟨b, hb, hx.symm⟩
      exact ⟨c, hc, by simp⟩
    | succ N ih =>
      intro b hb x hx
      obtain ⟨c, hc, hc'⟩ := ts_step W ξ ι t g hg (J ^ N) J {n | Finsupp.weight W.wt n = 0 ∧ n ≠ 0} 0
        (fun n hn => hn.1) (fun n hn => by
          have := GlobalTheory.algHom_sub_constantCoeff_mem g hJ (monomial n 1)
          rwa [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg hn.2.symm, map_zero,
            sub_zero] at this) ih
        (b - algebraMap O _ (constantCoeff b)) (fun n hn => by
          rw [map_sub, MvPowerSeries.algebraMap_apply, coeff_C]
          split_ifs with h
          · subst h; simp
          · rw [sub_zero]
            exact hb n fun h' => hn ⟨h', h⟩)
        (x - algebraMap O _ (constantCoeff b)) (by
          rw [map_sub, AlgHom.commutes, ← hx]; rfl)
      refine ⟨c + algebraMap O B (constantCoeff b), ?_, ?_⟩
      · rw [map_add (f := _), hc, AlgHom.commutes, map_sub, AlgHom.commutes]
        simp
      · rw [map_sub, AlgHom.commutes, sub_sub, add_comm] at hc'
        rwa [pow_succ]
  obtain ⟨c, hc, hc'⟩ := ts_step W ξ ι t g hg ⊥ ⊤ {n | Finsupp.weight W.wt n = j} j (fun n hn => hn)
    (fun _ _ => trivial) (fun b hb x hx => by
      obtain ⟨c, hc, -⟩ := hQ 0 b hb x hx
      refine ⟨c, hc, ?_⟩
      rw [Ideal.mem_bot, sub_eq_zero]
      refine GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun N => ?_
      obtain ⟨c', hc1, hc2⟩ := hQ N b hb x hx
      rwa [hι (hc.trans hc1.symm)]) F hF x hx
  rw [Ideal.bot_mul, Ideal.mem_bot, sub_eq_zero] at hc'
  rw [hc', hc]

private theorem ts_factor [DecidableEq X] (hι : Function.Injective ι)
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) [IsHausdorff J B] (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) :
    ∃ f : R →ₐ[O] B, (ι.comp f).comp W.A.val = act W.gr t ξ := by
  have key := ts_agree W ξ ι t g hι hg J hJ h0
  have hker : ∀ F ∈ RingHom.ker W.π, g F = 0 := by
    intro F hF
    refine ts_vanish W.wt J g hJ F fun j => hι ?_
    have h1 : W.π (wcomp O W.wt j F) = 0 := W.homog F hF j
    rw [key j _ (wcomp_mem O W.wt j F) 0 h1.symm, map_zero, map_zero, mul_zero]
  let f : R →ₐ[O] B := (Ideal.Quotient.liftₐ (RingHom.ker W.π) g hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom
  have hf : ∀ F, f (W.π F) = g F := by
    intro F
    have : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π F) = Ideal.Quotient.mk _ F := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [f, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    erw [this]
    rfl
  refine ⟨f, AlgHom.ext fun x => ?_⟩
  induction x using DirectSum.Decomposition.inductionOn W.gr with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | @homogeneous j x =>
    obtain ⟨x, hx⟩ := x
    rw [act_of_mem W.gr t ξ hx]
    obtain ⟨F, hF, hFx⟩ := hx
    have hFx' : (x : R) = W.π F := hFx.symm
    rw [← key j F hF x hFx', ← hf, ← hFx']
    rfl

end Core

end Gen

section SlopeTestRemainingChoices

open IsLocalRing Polynomial

private theorem ts_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem ts_norm_lt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
    (y : R →ₐ[ℤ_[l]] PadicAlgCl l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt y a ha

end SlopeTestRemainingChoices

section Ext

open IsLocalRing UpperTheory.V.Alg

private theorem ts_ext {O X R K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X]
    [CommRing R] [Algebra O R] (W : WPres O X R) [NormedField K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (hw : ∀ x : K, ‖x‖ ≤ 1 → IsIntegral O x)
    (ξ : W.A →ₐ[O] DualNumber K) (h1 : ∀ x, ‖(ξ x).fst‖ ≤ 1) (hz : ∀ s, ‖(ξ (W.zA s)).fst‖ < 1)
    (hfg : ((W.gr 0).map ξ.toLinearMap).FG) :
    ∃ Ξ : R →ₐ[O] DualNumber K, ∀ x : W.A, Ξ x = ξ x := by
  have hw' : ∀ x : DualNumber K, ‖x.fst‖ ≤ 1 → IsIntegral O x := fun x hx => by
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    refine IsIntegral.add ((hw _ hx).map (TrivSqZeroExt.inlAlgHom O K K)) ?_
    exact ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by simp [pow_two]⟩
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ hinj).2 hp.ne_zero
  let y : W.σ → DualNumber K := fun s => ξ (W.zA s)
  have hc : ∀ s, ∃ n : ℕ, IsIntegral O ((algebraMap O K p)⁻¹ • y s ^ n) := fun s => by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hp0) (hz s)
    refine ⟨n, hw' _ ?_⟩
    rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_pow, smul_eq_mul, norm_mul, norm_inv, norm_pow, ← div_eq_inv_mul]
    exact div_le_one_of_le₀ hn.le (norm_nonneg _)
  choose e he using hc
  obtain ⟨T, hT⟩ := id hfg
  let G : Set (DualNumber K) := (T : Set _) ∪ Set.range y ∪ Set.range fun s => (algebraMap O K p)⁻¹ • y s ^ e s
  have hG : G.Finite := (T.finite_toSet.union (Set.finite_range _)).union (Set.finite_range _)
  have hGi : ∀ x ∈ G, IsIntegral O x := by
    rintro x ((hx | ⟨s, rfl⟩) | ⟨s, rfl⟩)
    · have : x ∈ (W.gr 0).map ξ.toLinearMap := hT ▸ Submodule.subset_span hx
      obtain ⟨a, -, rfl⟩ := this
      exact hw' _ (h1 a)
    · exact hw' _ (hz s).le
    · exact he s
  let B : Subalgebra O (DualNumber K) := Algebra.adjoin O G
  haveI : Module.Finite O B := Algebra.finite_adjoin_of_finite_of_isIntegral hG hGi
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite O B
  haveI := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal O) B
  let J : Ideal B := ((maximalIdeal O).map (algebraMap O B)).radical
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg ((maximalIdeal O).map (algebraMap O B))
    (IsNoetherian.noetherian _)
  haveI : IsAdicComplete J B :=
    { toIsHausdorff := GlobalTheory.NilpotentEval.isHausdorff_of_pow_le hN
      toIsPrecomplete := GlobalTheory.NilpotentEval.isPrecomplete_of_pow_le hN Ideal.le_radical }
  let yB : W.σ → B := fun s => ⟨y s, Algebra.subset_adjoin (Or.inl (Or.inr ⟨s, rfl⟩))⟩
  have hyB : ∀ s, yB s ∈ J := fun s => by
    refine ⟨e s, ?_⟩
    have : yB s ^ e s = algebraMap O B p *
        ⟨(algebraMap O K p)⁻¹ • y s ^ e s, Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)⟩ := by
      apply Subtype.ext
      show y s ^ e s = algebraMap O (DualNumber K) p * ((algebraMap O K p)⁻¹ • y s ^ e s)
      rw [← Algebra.smul_def, ← algebraMap_smul K p, smul_inv_smul₀ hp0]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp.not_isUnit)
  obtain ⟨f, hf⟩ := ts_factor W ξ B.val 1 (GlobalTheory.mvEvalAdic O J yB hyB) Subtype.val_injective
    (fun s => by rw [GlobalTheory.mvEvalAdic_X]; simp [yB, y]) J (fun s => by rw [GlobalTheory.mvEvalAdic_X]; exact hyB s)
    (fun x hx => by
      have h1 : ξ x ∈ Submodule.span O (T : Set (DualNumber K)) := hT ▸ Submodule.mem_map_of_mem hx
      have h2 : Submodule.span O (T : Set (DualNumber K)) ≤ B.toSubmodule :=
        Submodule.span_le.2 fun a ha => Algebra.subset_adjoin (Or.inl (Or.inl ha))
      exact ⟨⟨ξ x, h2 h1⟩, rfl⟩)
  refine ⟨B.val.comp f, fun x => ?_⟩
  have h2 : (B.val.comp f) x = act W.gr 1 ξ x := DFunLike.congr_fun hf x
  rw [h2]
  clear h2
  induction x using DirectSum.Decomposition.inductionOn W.gr with
  | zero => rw [map_zero, map_zero]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | @homogeneous j x => rw [act_of_mem W.gr 1 ξ x.2]; simp

private def ts_near {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] (hO : ∀ a : O, ‖algebraMap O K a‖ ≤ 1) (A : Subalgebra O R) (m : Ideal R) (f : A →ₐ[O] K) :
    Subalgebra O A where
  carrier := {x | ∃ a : O, (x : R) - algebraMap O R a ∈ m ∧ ‖f x - algebraMap O K a‖ < 1}
  add_mem' := by
    rintro x y ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩
    refine ⟨a + b, ?_, ?_⟩
    · convert add_mem ha hb using 1
      rw [map_add (f := _), Subalgebra.coe_add]; ring
    · have : f (x + y) - algebraMap O K (a + b) = (f x - algebraMap O K a) + (f y - algebraMap O K b) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha' hb')
  mul_mem' := by
    rintro x y ⟨a, ha, ha'⟩ ⟨b, hb, hb'⟩
    refine ⟨a * b, ?_, ?_⟩
    · convert add_mem (m.mul_mem_right (y : R) ha) (m.mul_mem_left (algebraMap O R a) hb) using 1
      rw [map_mul, Subalgebra.coe_mul]; ring
    · have : f (x * y) - algebraMap O K (a * b) =
          (f x - algebraMap O K a) * f y + algebraMap O K a * (f y - algebraMap O K b) := by
        rw [map_mul, map_mul]; ring
      have hy : ‖f y‖ ≤ 1 := by
        rw [← sub_add_cancel (f y) (algebraMap O K b)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb'.le (hO b))
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans_lt ha'
      · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (hO a)).trans_lt hb'
  algebraMap_mem' a := ⟨a, by simp, by simp⟩

end Ext

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.tanScale :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] DualNumber (PadicAlgCl l), (∀ g i j, ‖(M.rep ξ g i j).fst - D.r0E g i j‖ < 1) → D.PtIn _ (M.rep ξ) := by
  intro Ω _ _ _ l _ c D hD M hF ξ hξ
  obtain ⟨-, -, WS, hWS, hz⟩ := sInternal D hD M
  have hsp := spanMono D hD M hF
  have hO : ∀ a : c.O, ‖algebraMap c.O (PadicAlgCl l) a‖ ≤ 1 := fun a =>
    (ts_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)
  have hO' : ∀ a ∈ maximalIdeal c.O, ‖algebraMap c.O (PadicAlgCl l) a‖ < 1 := ts_norm_lt c.O.val
  let f : M.SS →ₐ[c.O] PadicAlgCl l := (TrivSqZeroExt.fstHom c.O _ _).comp ξ
  let N := ts_near hO M.SS (maximalIdeal M.S) f
  have hent : ∀ g i j, M.ru.hom g i j ∈ N.map M.SS.val := fun g i j => by
    refine ⟨M.ent g i j, ⟨D.r0 g i j, ?_, hξ g i j⟩, rfl⟩
    rw [← res_eq_zero_iff c.O, map_sub, AlgHom.commutes, sub_eq_zero]
    exact M.ru.red g i j
  have hN : ∀ x : M.SS, x ∈ N := fun x => by
    have h1 : (⨆ w, M.sPart w) ≤ (N.map M.SS.val).toSubmodule := by
      refine iSup_le fun w => ?_
      rw [hsp w, Submodule.span_le]
      rintro _ ⟨L, -, rfl⟩
      refine Subalgebra.list_prod_mem _ fun y hy => ?_
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy
      exact hent _ _ _
    obtain ⟨y, hy, hyx⟩ := h1 x.2
    rwa [← (Subtype.ext hyx : y = x)]
  have hle : WS.A ≤ M.SS := fun x hx => iSup_mono (fun w => (hWS w).le) hx
  have hge : M.SS ≤ WS.A := fun x hx => iSup_mono (fun w => (hWS w).ge) hx
  have hfg : (WS.part 0).FG := by
    haveI := hF M.S M.ru M.pt
    have h1 : (Algebra.adjoin c.O (mono M.ru.hom 0)).toSubmodule.FG := Module.Finite.iff_fg.1 this
    refine h1.of_le ?_
    rw [hWS, hsp, Submodule.span_le]
    exact Algebra.subset_adjoin
  obtain ⟨Ξ, hΞ⟩ := ts_ext WS (K := PadicAlgCl l) Subtype.val_injective
    (fun x hx => ((ts_intIff x).2 hx).tower_top) (ξ.comp (Subalgebra.inclusion hle))
    (fun x => by
      obtain ⟨a, -, ha⟩ := hN (Subalgebra.inclusion hle x)
      show ‖f (Subalgebra.inclusion hle x)‖ ≤ 1
      rw [← sub_add_cancel (f _) (algebraMap c.O _ a)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.le (hO a)))
    (fun s => by
      obtain ⟨a, ha0, ha⟩ := hN (Subalgebra.inclusion hle (WS.zA s))
      have h1 : algebraMap c.O M.S a ∈ maximalIdeal M.S := by
        have := Ideal.sub_mem _ (hz s) ha0
        rwa [show WS.z s - (((Subalgebra.inclusion hle (WS.zA s) : M.SS) : M.S) - algebraMap c.O M.S a) =
          algebraMap c.O M.S a from sub_sub_cancel _ _] at this
      have h2 : a ∈ maximalIdeal c.O := fun hu => h1 (hu.map _)
      show ‖f (Subalgebra.inclusion hle (WS.zA s))‖ < 1
      rw [← sub_add_cancel (f _) (algebraMap c.O _ a)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha (hO' a h2)))
    (Submodule.FG.map _ (Submodule.fg_of_fg_map_injective WS.A.val.toLinearMap Subtype.val_injective (by
      refine hfg.of_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hx)))
  refine ⟨M.S, _, _, _, M.ru, Ξ, M.pt, ?_⟩
  ext1 g
  ext1 i j
  exact (hΞ ⟨_, hge (M.ent g i j).2⟩).symm
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem graded_subalgebra_internal {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    [DecidableEq X] (𝒜 : X → Submodule O R) [SetLike.GradedMonoid 𝒜] (h : iSupIndep 𝒜) :
    DirectSum.IsInternal fun j => (𝒜 j).comap (gradedSub 𝒜).val.toLinearMap := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hs i hi
    have h1 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 h s (fun i => (v i : R)) hv
      (by rw [← AddSubmonoidClass.coe_finsetSum, hs]; rfl) i hi
    exact Subtype.ext h1
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ ⨆ j, 𝒜 j := hx
    induction hx' using Submodule.iSup_induction' with
    | mem i x hi => exact Submodule.mem_iSup_of_mem i hi
    | zero => exact zero_mem _
    | add x y hx1 hy1 ihx ihy => exact add_mem (ihx hx1) (ihy hy1)

private theorem extend_point_degree_zero_graded {O A B K : Type} [CommRing O] [CommRing A] [CommRing B] [CommRing K] [Algebra O A]
    [Algebra O B] [Algebra O K] (𝓑 : ℤ × ℤ → Submodule O B) [GradedAlgebra 𝓑] (φ : A →ₐ[O] B) (X : A →ₐ[O] K)
    (hk : ∀ f, φ f = 0 → X f = 0) (hs : ∀ n, ∀ b ∈ 𝓑 (0, n), ∃ a, φ a = b) (u v : B) (hu : u ∈ 𝓑 (1, 0))
    (hv : v ∈ 𝓑 (-1, 0)) (a₀ : A) (h₀ : φ a₀ = u * v) (c : Kˣ) (hc : X a₀ = c) :
    ∃ Ξ : B →ₐ[O] K, ∀ n a, φ a ∈ 𝓑 (0, n) → Ξ (φ a) = X a := by
  have hk' : ∀ f f', φ f = φ f' → X f = X f' := fun f f' h => by
    rw [← sub_eq_zero, ← map_sub]
    exact hk _ (by rw [map_sub, h, sub_self])
  have hm : ∀ (w : ℤ × ℤ), ∀ f ∈ 𝓑 w, ∀ p q : ℕ, w.1 + p = q → ∃ a, φ a = f * u ^ p * v ^ q := by
    intro w f hf p q h
    have h1 := SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem hf (SetLike.pow_mem_graded p hu))
      (SetLike.pow_mem_graded q hv)
    have h2 : w + p • ((1, 0) : ℤ × ℤ) + q • ((-1, 0) : ℤ × ℤ) = (0, w.2) := by
      ext <;> simp
      omega
    rw [h2] at h1
    exact hs _ _ h1
  have h0 : ∀ w : ℤ × ℤ, w.1 + ((-w.1).toNat : ℕ) = (w.1.toNat : ℕ) := fun w => by omega
  choose g hg using fun (w : ℤ × ℤ) (f : 𝓑 w) => hm w f f.2 _ _ (h0 w)
  let ψ : ∀ w, 𝓑 w →ₗ[O] K := fun w =>
    { toFun := fun f => X (g w f) * ((c⁻¹ : Kˣ) : K) ^ w.1.toNat
      map_add' := fun a b => by
        rw [← add_mul, ← map_add (f := _)]
        congr 1
        exact hk' _ _ (by rw [map_add (f := _), hg, hg, hg, Submodule.coe_add]; ring)
      map_smul' := fun r b => by
        rw [RingHom.id_apply, ← smul_mul_assoc, ← map_smul]
        congr 1
        exact hk' _ _ (by rw [map_smul, hg, hg, Submodule.coe_smul, smul_mul_assoc, smul_mul_assoc]) }
  have hψ : ∀ w (f : 𝓑 w) (p q : ℕ) a, w.1 + p = q → φ a = f * u ^ p * v ^ q → X a = ψ w f * (c : K) ^ q := by
    intro w f p q a h ha
    obtain ⟨d, hd⟩ : ∃ d : ℕ, q = w.1.toNat + d := ⟨q - w.1.toNat, by omega⟩
    have hp : p = (-w.1).toNat + d := by omega
    have e1 : X a = X (g w f * a₀ ^ d) := hk' _ _ (by
      rw [ha, map_mul, map_pow, hg, h₀, hd, hp]; ring)
    show _ = X (g w f) * ((c⁻¹ : Kˣ) : K) ^ w.1.toNat * _
    rw [e1, map_mul, map_pow, hc, hd, pow_add, mul_assoc, ← mul_assoc (_ ^ _), ← mul_pow, Units.inv_mul, one_pow,
      one_mul]
  have hone : ψ 0 (GradedMonoid.GOne.one (A := fun j => 𝓑 j)) = 1 := by
    have := hψ 0 (GradedMonoid.GOne.one (A := fun j => 𝓑 j)) 0 0 1 (by simp) (by simp)
    simpa using this.symm
  have hmul : ∀ {i j} (a : 𝓑 i) (b : 𝓑 j), ψ (i + j) (GradedMonoid.GMul.mul (A := fun j => 𝓑 j) a b) = ψ i a * ψ j b := by
    intro i j a b
    have e1 := hψ i a _ _ _ (h0 i) (hg i a)
    have e2 := hψ j b _ _ _ (h0 j) (hg j b)
    have e3 := hψ (i + j) (GradedMonoid.GMul.mul (A := fun j => 𝓑 j) a b) ((-i.1).toNat + (-j.1).toNat) (i.1.toNat + j.1.toNat)
      (g i a * g j b) (by simp only [Prod.fst_add]; omega)
      (by rw [map_mul, hg, hg, SetLike.coe_gMul]; ring)
    rw [map_mul, e1, e2] at e3
    apply (c.isUnit.pow (i.1.toNat + j.1.toNat)).mul_right_cancel
    rw [← e3]; ring
  refine ⟨(DirectSum.toAlgebra O (fun j => 𝓑 j) ψ hone hmul).comp (DirectSum.decomposeAlgEquiv 𝓑).toAlgHom,
    fun n a ha => ?_⟩
  have h : DirectSum.decompose 𝓑 (φ a) = DirectSum.of (fun j => 𝓑 j) (0, n) ⟨φ a, ha⟩ :=
    DirectSum.decompose_of_mem 𝓑 ha
  have e := hψ (0, n) ⟨φ a, ha⟩ 0 0 a (by simp) (by simp)
  rw [pow_zero, mul_one] at e
  rw [e]
  simp [h, DirectSum.toAlgebra]
  erw [DirectSum.toSemiring_of]
  rfl

private theorem derivation_to_dual_number_point {O A K : Type} [CommRing O] [CommRing A] [Field K] [Algebra O A] [Algebra O K]
    (x : A →ₐ[O] K) (δ : A →ₗ[O] K) (hδ : δ ∈ PtDer x K) :
    ∃ X : A →ₐ[O] DualNumber K, ∀ f, (X f).fst = x f ∧ (X f).snd = δ f := by
  have hδ' : ∀ f g, δ (f * g) = x f • δ g + x g • δ f := hδ
  have h1 : δ 1 = 0 := by
    have := hδ' 1 1
    simpa using this
  refine ⟨{ toFun := fun f => TrivSqZeroExt.inl (x f) + TrivSqZeroExt.inr (δ f)
            map_one' := by ext <;> simp [h1]
            map_mul' := fun f g => by ext <;> simp [hδ', mul_comm]
            map_zero' := by ext <;> simp
            map_add' := fun f g => by ext <;> simp
            commutes' := fun r => by
              rw [Algebra.algebraMap_eq_smul_one (A := A), Algebra.algebraMap_eq_smul_one (A := DualNumber K)]
              ext <;> simp [h1] }, fun f => ?_⟩
  constructor <;> simp

private theorem torus_dual_number_weight_vector (K : Type) [Field K] (a b : K) : ∃ s : (DualNumber K)ˣ × (DualNumber K)ˣ, ∀ w,
    (wv s w : DualNumber K).fst = 1 ∧ (wv s w : DualNumber K).snd = a * w.1 + b * w.2 := by
  let e : Multiplicative K →* DualNumber K :=
    { toFun := fun a => TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr a.toAdd
      map_one' := by ext <;> simp
      map_mul' := fun f g => by ext <;> simp [add_comm] }
  refine ⟨(e.toHomUnits (.ofAdd a), e.toHomUnits (.ofAdd b)), fun w => ?_⟩
  simp only [wv]
  rw [← map_zpow e.toHomUnits, ← map_zpow e.toHomUnits, ← map_mul, MonoidHom.coe_toHomUnits]
  constructor <;> simp [e, mul_comm]

private theorem torus_dual_number_lift_zero (K : Type) [Field K] (t : Kˣ × Kˣ) : ∃ s : (DualNumber K)ˣ × (DualNumber K)ˣ, ∀ w,
    (wv s w : DualNumber K).fst = wv t w ∧ (wv s w : DualNumber K).snd = 0 := by
  let e := Units.map (algebraMap K (DualNumber K) : K →* DualNumber K)
  refine ⟨(e t.1, e t.2), fun w => ?_⟩
  have : wv (e t.1, e t.2) w = e (wv t w) := by simp only [wv, map_mul, map_zpow]
  rw [this]
  constructor <;> simp [e, TrivSqZeroExt.algebraMap_eq_inl]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem exists_lift_of_derivation_on_ideal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hL : Loc.LocalPublishedTheorems) (hS : SoV Ω l) (hF : D.Fin0)
    (hN : D.NoEnd) (x : M.A →ₐ[c.O] PadicAlgCl l) (hx : OnS M.eqns.ideal x)
    (h2 : TwoSigned M.gr x) (δ : M.A →ₗ[c.O] PadicAlgCl l) (hδ : δ ∈ PtDer x (PadicAlgCl l))
    (hI : ∀ f ∈ M.eqns.ideal, δ f = 0) : ∃ Ξ : M.SS →ₐ[c.O] DualNumber (PadicAlgCl l),
      ∀ n, ∀ f ∈ M.gr n, (Ξ (M.toSS f)).fst = x f ∧ (Ξ (M.toSS f)).snd = δ f := by
  obtain ⟨hker, hsur, hgr⟩ := kerA D hD M
  obtain ⟨ξ₀, hξ₀⟩ := ptLift D hD M x hx
  have hirr := twoIrr D hD M hL hS hF hN ξ₀ (hξ₀ ▸ h2)
  have hne : ∀ i j, ∃ g, ξ₀ (M.ent g i j) ≠ 0 := fun i j => by
    by_contra hc
    push Not at hc
    have h1 : Submodule.span (PadicAlgCl l) (Set.range (M.rep ξ₀)) ≤
        LinearMap.ker (Matrix.entryLinearMap (PadicAlgCl l) (PadicAlgCl l) i j) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hc g
    rw [hirr] at h1
    simpa using h1 (Submodule.mem_top (x := Matrix.single i j 1))
  obtain ⟨g₁, hg₁⟩ := hne 0 1
  obtain ⟨g₂, hg₂⟩ := hne 1 0
  have hu : (M.ent g₁ 0 1).1 ∈ M.sPart (1, 0) := M.entry_mem g₁ 0 1
  have hv : (M.ent g₂ 1 0).1 ∈ M.sPart (-1, 0) := M.entry_mem g₂ 1 0
  obtain ⟨a₀, -, ha₀⟩ := hsur 0 (M.ent g₁ 0 1 * M.ent g₂ 1 0) (SetLike.GradedMul.mul_mem hu hv)
  have hxa : x a₀ ≠ 0 := by
    rw [← hξ₀, AlgHom.comp_apply, ha₀, map_mul]
    exact mul_ne_zero hg₁ hg₂
  obtain ⟨X, hX⟩ := derivation_to_dual_number_point x δ hδ
  have hXu : IsUnit (X a₀) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [(hX a₀).1]; exact hxa.isUnit)
  let 𝒜 : ℤ × ℤ → Submodule c.O M.SS := fun j => (M.sPart j).comap M.SS.val.toLinearMap
  have hint : DirectSum.IsInternal 𝒜 := graded_subalgebra_internal M.sPart (sInternal D hD M).1
  letI : GradedAlgebra 𝒜 :=
    { toDecomposition := hint.chooseDecomposition
      one_mem := (SetLike.GradedOne.one_mem : (1 : M.S) ∈ M.sPart 0)
      mul_mem := fun _ _ _ _ ha hb => (SetLike.GradedMul.mul_mem ha hb : _ ∈ M.sPart _) }
  obtain ⟨Ξ, hΞ⟩ := extend_point_degree_zero_graded 𝒜 M.toSS X
    (fun f hf => by
      have := (hker f).1 hf
      ext
      · rw [(hX f).1, hx f this]; rfl
      · rw [(hX f).2, hI f this]; rfl)
    (fun n b hb => by obtain ⟨a, -, ha⟩ := hsur n b hb; exact ⟨a, ha⟩) _ _ hu hv a₀ ha₀ hXu.unit rfl
  exact ⟨Ξ, fun n f hf => ⟨(congrArg TrivSqZeroExt.fst (hΞ n f (hgr n f hf))).trans (hX f).1,
    (congrArg TrivSqZeroExt.snd (hΞ n f (hgr n f hf))).trans (hX f).2⟩⟩

set_option maxHeartbeats 800000 in
private theorem derivation_kills_ideal_lifts {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hL : Loc.LocalPublishedTheorems) (hS : SoV Ω l) (hF : D.Fin0)
    (hN : D.NoEnd) (hR : D.AllIrr D.RigidAt) (x : M.A →ₐ[c.O] PadicAlgCl l) (hx : OnS M.eqns.ideal x)
    (h2 : TwoSigned M.gr x) (δ : M.A →ₗ[c.O] PadicAlgCl l) (hδ : δ ∈ PtDer x (PadicAlgCl l))
    (hI : ∀ f ∈ M.eqns.ideal, δ f = 0) : ∃ b : PadicAlgCl l, ∀ n, ∀ f ∈ M.gr n, δ f = b * (n * x f) := by
  obtain ⟨-, -, hgr⟩ := kerA D hD M
  obtain ⟨Ξ, hΞ⟩ := exists_lift_of_derivation_on_ideal D hD M hL hS hF hN x hx h2 δ hδ hI
  let p : DualNumber (PadicAlgCl l) →ₐ[c.O] PadicAlgCl l := TrivSqZeroExt.fstHom c.O _ _
  let q : PadicAlgCl l →ₐ[c.O] DualNumber (PadicAlgCl l) := TrivSqZeroExt.inlAlgHom c.O _ _
  obtain ⟨t, r, hr, hrt⟩ := ptScale D hD M hF (p.comp Ξ)
  obtain ⟨s, hs⟩ := torus_dual_number_lift_zero _ t
  obtain ⟨Ξ₁, -, hΞ₁⟩ := ptAct D hD M (DualNumber (PadicAlgCl l)) Ξ s
  have hfst : ∀ w (f : M.SS), f.1 ∈ M.sPart w → (Ξ₁ f).fst = wv t w * (Ξ f).fst := fun w f hf => by
    rw [hΞ₁ w f hf, TrivSqZeroExt.fst_mul, (hs w).1]
  have hsnd : ∀ w (f : M.SS), f.1 ∈ M.sPart w → (Ξ₁ f).snd = wv t w * (Ξ f).snd := fun w f hf => by
    rw [hΞ₁ w f hf, DualNumber.snd_mul, (hs w).1, (hs w).2, zero_mul, add_zero]
  have hr1 : ∀ g i j, (M.rep Ξ₁ g i j).fst = r g i j := fun g i j => by
    rw [hrt]
    exact hfst _ _ (M.entry_mem g i j)
  have hr2 : M.rep (p.comp Ξ₁) = r := by
    ext g i j
    exact hr1 g i j
  have hpx : ∀ n, ∀ f ∈ M.gr n, (Ξ₁ (M.toSS f)).fst = wv t (0, n) * x f := fun n f hf => by
    rw [hfst _ _ (hgr n f hf), (hΞ n f hf).1]
  have hirr1 : Irr r := by
    rw [← hr2]
    refine twoIrr D hD M hL hS hF hN _ ⟨fun h => h2.1 fun n hn f hf => ?_, fun h => h2.2 fun n hn f hf => ?_⟩
    all_goals
      have h3 : (Ξ₁ (M.toSS f)).fst = 0 := h n hn f hf
      rw [hpx n f hf] at h3
      exact (Units.mul_right_eq_zero _).1 h3
  have hin : D.PtIn _ (M.rep Ξ₁) := tanScale D hD M hF Ξ₁ fun g i j => by
    exact (congrArg (fun z => ‖z - D.r0E g i j‖) (hr1 g i j)).trans_lt ((eptInt D hD r hr).2.1 g i j)
  obtain ⟨a, b, hab⟩ := rigidDiag D hD r hr (hR r hr hirr1) _ hin hr1
  obtain ⟨s', hs'⟩ := torus_dual_number_weight_vector _ a b
  obtain ⟨Ξ₂, -, hΞ₂⟩ := ptAct D hD M (DualNumber (PadicAlgCl l)) (q.comp (p.comp Ξ₁)) s'
  have h2f : ∀ w (f : M.SS), f.1 ∈ M.sPart w → (Ξ₂ f).fst = (Ξ₁ f).fst := fun w f hf => by
    rw [hΞ₂ w f hf, TrivSqZeroExt.fst_mul, (hs' w).1, one_mul]
    rfl
  have h2s : ∀ w (f : M.SS), f.1 ∈ M.sPart w → (Ξ₂ f).snd = (a * w.1 + b * w.2) * (Ξ₁ f).fst := fun w f hf => by
    rw [hΞ₂ w f hf, DualNumber.snd_mul, (hs' w).1, (hs' w).2]
    show 1 * 0 + _ * (Ξ₁ f).fst = _
    rw [mul_zero, zero_add]
  have he : Ξ₂ = Ξ₁ := ptExt D hD M hF (DualNumber (PadicAlgCl l)) _ _ (by
    ext g i j
    · exact h2f _ _ (M.entry_mem g i j)
    · exact ((h2s _ _ (M.entry_mem g i j)).trans (congrArg _ (hr1 g i j))).trans (hab g i j).symm)
  refine ⟨b, fun n f hf => ?_⟩
  have e := h2s _ _ (hgr n f hf)
  subst he
  have e := (hsnd _ _ (hgr n f hf)).symm.trans e
  rw [hpx n f hf, (hΞ n f hf).2] at e
  apply (Units.mul_right_inj (wv t (0, n))).1
  rw [e]
  simp only [Int.cast_zero]
  ring

theorem UpperTheory.V.GradeZeroInterpolatingElement.m4 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], Loc.LocalPublishedTheorems → SoV Ω l → D.Fin0 → D.NoEnd → D.AllIrr D.RigidAt → Alg.M4 M.gr (PadicAlgCl l) M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hL hS hF hN hR x hx h2 δ hδ δ' hδ' hI hI'
  obtain ⟨b, hb⟩ := derivation_kills_ideal_lifts D hD M hL hS hF hN hR x hx h2 δ hδ hI
  obtain ⟨b', hb'⟩ := derivation_kills_ideal_lifts D hD M hL hS hF hN hR x hx h2 δ' hδ' hI'
  have key : ∀ c₁ c₂ : PadicAlgCl l, c₁ * b + c₂ * b' = 0 → c₁ • δ + c₂ • δ' = 0 := fun c₁ c₂ h => by
    ext f
    induction f using DirectSum.Decomposition.inductionOn M.gr with
    | zero => exact map_zero _
    | @homogeneous n f =>
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hb n f f.2, hb' n f f.2,
        LinearMap.zero_apply]
      linear_combination ((n : PadicAlgCl l) * x f) * h
    | add f g hf hg => rw [map_add (f := _), hf, hg]; simp
  by_cases h0 : b = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, key _ _ (by simp [h0])⟩
  · exact ⟨b', -b, Or.inr (neg_ne_zero.2 h0), key _ _ (by ring)⟩
