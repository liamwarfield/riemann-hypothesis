module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonGr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Origin
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem UpperTheory.V.UnitaryThreeInertia.map_eq_zero_of_cc {O A σ : Type} [CommRing O] [CommRing A] [Fintype σ]
    (φ : MvPowerSeries σ O →+* A) (hφ : ∀ i, φ (MvPowerSeries.X i) = 0) (p : MvPowerSeries σ O)
    (hp : MvPowerSeries.constantCoeff p = 0) : φ p = 0 := by
  classical
  have hsupp : ∀ n : σ →₀ ℕ, n ≠ 0 → n.support.Nonempty :=
    fun n hn => Finsupp.support_nonempty_iff.mpr hn
  let sel : (σ →₀ ℕ) → σ → Prop := fun n i => ∃ h : n ≠ 0, (hsupp n h).choose = i
  let q : σ → MvPowerSeries σ O := fun i m =>
    if sel (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) p else 0
  have hX : ∀ (n : σ →₀ ℕ) (i : σ) (f : MvPowerSeries σ O),
      MvPowerSeries.coeff n (MvPowerSeries.X i * f)
        = if Finsupp.single i 1 ≤ n then MvPowerSeries.coeff (n - Finsupp.single i 1) f else 0 := by
    intro n i f
    rw [show (MvPowerSeries.X i : MvPowerSeries σ O) = MvPowerSeries.monomial (Finsupp.single i 1) 1
      from rfl, MvPowerSeries.coeff_monomial_mul, one_mul]
  have hq : ∀ (i : σ) (m : σ →₀ ℕ), MvPowerSeries.coeff m (q i)
      = if sel (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) p else 0 :=
    fun i m => rfl
  have hdec : p = ∑ i, MvPowerSeries.X i * q i := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [hX, hq]
    by_cases hn : n = 0
    · subst hn
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hp]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      intro hle
      have := hle i
      simp at this
    · set j := (hsupp n hn).choose with hj
      have hjmem : j ∈ n.support := (hsupp n hn).choose_spec
      have hjle : Finsupp.single j 1 ≤ n := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hjmem)
      rw [Finset.sum_eq_single j]
      · rw [if_pos hjle, tsub_add_cancel_of_le hjle, if_pos ⟨hn, rfl⟩]
      · intro b _ hb
        by_cases hble : Finsupp.single b 1 ≤ n
        · rw [if_pos hble, tsub_add_cancel_of_le hble, if_neg]
          rintro ⟨_, hb'⟩
          exact hb hb'.symm
        · rw [if_neg hble]
      · intro h
        exact absurd (Finset.mem_univ j) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul, hφ, zero_mul]

private theorem UpperTheory.V.UnitaryThreeInertia.map_eq_cc {O σ : Type} [CommRing O] [Fintype σ]
    (φ : MvPowerSeries σ O →ₐ[O] O) (hφ : ∀ i, φ (MvPowerSeries.X i) = 0) (p : MvPowerSeries σ O) :
    φ p = MvPowerSeries.constantCoeff p := by
  have h0 : MvPowerSeries.constantCoeff
      (p - algebraMap O (MvPowerSeries σ O) (MvPowerSeries.constantCoeff p)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr rfl
  have h := UpperTheory.V.UnitaryThreeInertia.map_eq_zero_of_cc (φ : MvPowerSeries σ O →+* O) (fun i => hφ i) _ h0
  rw [map_sub, sub_eq_zero] at h
  have h2 : φ (algebraMap O (MvPowerSeries σ O) (MvPowerSeries.constantCoeff p))
      = MvPowerSeries.constantCoeff p := by
    rw [AlgHom.commutes]
    rfl
  exact h.trans h2

theorem UpperTheory.V.UnitaryThreeInertia.hasOrigin :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → ∃ h : W.HasOrigin, push (W.origin h) u = r0 F.η F.Ψ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg₁ R _ _ _ u hu W hW
  obtain ⟨f, hf, -⟩ := hu.univ O (F.rz O) (UpperTheory.V.UnitaryThreeInertia.isPt_rz F hF g₁)
  have hz : ∀ i, f (W.z i) = 0 := by
    intro i
    obtain ⟨g, a, b, -, -, hzi⟩ := hW.var i
    rw [hzi, map_sub]
    have h1 : f ((u g).mat a b) = ((F.rz O) g).mat a b := by
      rw [← hf]
      rfl
    have h2 : f (((F.rz R) g).mat a b) = ((F.rz O) g).mat a b := by
      show f (algebraMap O R _) = _
      rw [AlgHom.commutes]
      rfl
    rw [h1, h2, sub_self]
  haveI := W.fin
  let ψ : MvPowerSeries W.σ O →ₐ[O] O := f.comp W.π
  have hψ : ∀ p, ψ p = MvPowerSeries.constantCoeff p :=
    UpperTheory.V.UnitaryThreeInertia.map_eq_cc ψ (fun i => hz i)
  have hO : W.HasOrigin := by
    intro p hp
    rw [← hψ]
    show f (W.π p) = 0
    rw [hp, map_zero]
  refine ⟨hO, ?_⟩
  have heq : W.origin hO = f := by
    ext x
    obtain ⟨p, rfl⟩ := W.surj x
    rw [UpperTheory.V.Alg.WPres.origin_π, ← hψ]
    rfl
  rw [heq, hf]
  exact MonoidHom.ext fun g => rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtBasis
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem lb_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have h1 : IsUnit ((t : O) - 1) := by
    have : (t : O) ^ 2 - 1 = ((t : O) - 1) * ((t : O) + 1) := by ring
    rw [this] at ht
    exact isUnit_of_mul_isUnit_left ht
  have hi : ((t⁻¹ : Oˣ) : O) * (t : O) = 1 := by simp
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have : (t : O) - ((t⁻¹ : Oˣ) : O) = ((t⁻¹ : Oˣ) : O) * ((t : O) ^ 2 - 1) := by
      linear_combination (-(t : O)) * hi
    rw [this]
    exact (Units.isUnit _).mul ht
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have : 1 - ((t⁻¹ : Oˣ) : O) = ((t⁻¹ : Oˣ) : O) * ((t : O) - 1) := by
      linear_combination (-1 : O) * hi
    rw [this]
    exact (Units.isUnit _).mul h1
  fin_cases a <;> fin_cases b <;> simp [wt1] at hab ⊢
  all_goals first
    | exact h1 | exact h2 | exact h3
    | exact (by simpa [neg_sub] using h1.neg)
    | exact (by simpa [neg_sub] using h2.neg)
    | exact (by simpa [neg_sub] using h3.neg)

theorem UpperTheory.V.UnitaryThreeInertia.lt_basis :
    ∀ {O R R' D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [CommRing R'] [Algebra O R'] [IsCO O R'] [Group D]
      (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R'), Function.Surjective p →
      ∀ (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r' : D →* GG (m := 3) (R := R')) (x : D), Red η Ψ r' → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → CondT η Ψ I r' →
      (∃ X, GrMat 𝒜 X ∧ X.map p = (r' x).mat) →
      ∃ h : GL (Fin 3) R, InHat h ∧ GrMat 𝒜 h.val ∧ InHat (GeneralLinearGroup.map (p : R →+* R') h) ∧ TriIn η Ψ I r' (GeneralLinearGroup.map (p : R →+* R') h) := by
  intro O R R' D _ _ _ _ _ _ _ _ _ _ 𝒜 _ p hp η Ψ I r' x hr hx hΨ hc hex
  obtain ⟨X, hX, hXp⟩ := hex
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  haveI : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp
  have hm : ∀ y : R, p y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
    intro y
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff (p : R →+* R') y)
  have hd : (r0 η Ψ x).mat = diagonal fun i => (((Ψ x) ^ wt1 i : Oˣ) : O) := by
    unfold GG.mat
    rw [unitaryThreeReflection_left, tor_val]
  have hred := hr.red x
  rw [hd] at hred
  have hent : ∀ a b : Fin 3, p (X a b) = (r' x).mat a b := by
    intro a b
    rw [← hXp]
    rfl
  have hoff : ∀ a b : Fin 3, a ≠ b → X a b ∈ maximalIdeal R := by
    intro a b hab
    rw [← hm, hent]
    have := hred a b
    simpa [Matrix.map_apply, Matrix.diagonal_apply_ne _ hab] using this
  have hdiff : ∀ a b : Fin 3, a ≠ b → IsUnit (X a a - X b b) := by
    intro a b hab
    by_contra hn
    have h1 : X a a - X b b ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    rw [← hm, map_sub, hent, hent] at h1
    have ha := hred a a
    have hb := hred b b
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.diagonal_apply_eq] at ha hb
    have hu : IsUnit (algebraMap O R' ((((Ψ x) ^ wt1 a : Oˣ) : O) - (((Ψ x) ^ wt1 b : Oˣ) : O))) :=
      (lb_unit (Ψ x) hΨ a b hab).map _
    apply (IsLocalRing.mem_maximalIdeal _).mp _ hu
    have : algebraMap O R' ((((Ψ x) ^ wt1 a : Oˣ) : O) - (((Ψ x) ^ wt1 b : Oˣ) : O)) =
        ((r' x).mat a a - (r' x).mat b b) - ((r' x).mat a a - algebraMap O R' (((Ψ x) ^ wt1 a : Oˣ) : O))
          + ((r' x).mat b b - algebraMap O R' (((Ψ x) ^ wt1 b : Oˣ) : O)) := by
      rw [map_sub]
      ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.sub_mem _ h1 ha) hb
  obtain ⟨h, hh⟩ := exists_canon X hdiff hoff
  have hg := canon_graded 𝒜 X h hdiff hX hh
  have hh' := canon_map.1 (p : R →+* R') X h hh
  have hXp' : X.map (p : R →+* R') = (r' x).mat := hXp
  rw [hXp'] at hh'
  exact ⟨h, hh.hat, hg.1, hh'.hat, (cond_iff_canon η Ψ I r' x _ hr hx hΨ hh').1.1 hc⟩
end
