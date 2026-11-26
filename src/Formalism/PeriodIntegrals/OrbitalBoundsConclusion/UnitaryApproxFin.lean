module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.TopStep
public import Lemmata.GeneralBFactRightTer.Imports

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Assembly
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.SkewApprox
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Cayley
noncomputable section

open Matrix

namespace PI.UnitaryApproxFinWork

variable {n : Type} [Fintype n] [DecidableEq n] {A : Type} [CommRing A] (ρ : A →+* A)

theorem cT_add (M N : Matrix n n A) : PI.UnitaryApproxDefs.cT ρ (M + N) = PI.UnitaryApproxDefs.cT ρ M + PI.UnitaryApproxDefs.cT ρ N := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT]

theorem cT_sub (M N : Matrix n n A) : PI.UnitaryApproxDefs.cT ρ (M - N) = PI.UnitaryApproxDefs.cT ρ M - PI.UnitaryApproxDefs.cT ρ N := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT]

theorem cayley_unitary (J X : Matrix n n A) (hX : PI.UnitaryApproxDefs.cT ρ X * J + J * X = 0)
    (hQ : IsUnit (1 + X).det) :
    PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹) * J * ((1 - X) * (1 + X)⁻¹) = J := by
  have hXJ : PI.UnitaryApproxDefs.cT ρ X * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have hcP : PI.UnitaryApproxDefs.cT ρ (1 - X) * J = J * (1 + X) := by
    rw [cT_sub ρ, PI.UnitaryApproxDefs.cT_one, sub_mul, one_mul, hXJ, sub_neg_eq_add, mul_add, mul_one]
  have hcQ : PI.UnitaryApproxDefs.cT ρ (1 + X) * J = J * (1 - X) := by
    rw [cT_add ρ, PI.UnitaryApproxDefs.cT_one, add_mul, one_mul, hXJ, mul_sub, mul_one, sub_eq_add_neg]
  have hinvQ : PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + X) = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.mul_nonsing_inv _ hQ, PI.UnitaryApproxDefs.cT_one]
  have hcomm : (1 + X) * (1 - X) = (1 - X) * (1 + X) := by noncomm_ring
  rw [PI.UnitaryApproxDefs.cT_mul]
  calc PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 - X) * J * ((1 - X) * (1 + X)⁻¹)
      = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * (PI.UnitaryApproxDefs.cT ρ (1 - X) * J) * (1 - X) * (1 + X)⁻¹ := by simp only [mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * J * ((1 + X) * (1 - X)) * (1 + X)⁻¹ := by rw [hcP]; simp only [mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * J * (1 - X) * ((1 + X) * (1 + X)⁻¹) := by rw [hcomm]; simp only [mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * (J * (1 - X)) := by rw [Matrix.mul_nonsing_inv _ hQ, mul_one, mul_assoc]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + X)⁻¹ * (PI.UnitaryApproxDefs.cT ρ (1 + X) * J) := by rw [hcQ]
    _ = J := by rw [← mul_assoc, hinvQ, one_mul]

theorem cayley_mem_UJ (J X : Matrix n n A) (hJd : IsUnit J.det) (hX : PI.UnitaryApproxDefs.cT ρ X * J + J * X = 0)
    (hQ : IsUnit (1 + X).det) :
    ∃ γ ∈ PI.UnitaryApproxDefs.UJ ρ J, (γ : Matrix n n A) = (1 - X) * (1 + X)⁻¹ := by
  have hU := cayley_unitary ρ J X hX hQ
  have hdet := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have h2 : J.det * ((PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹)).det * ((1 - X) * (1 + X)⁻¹).det) = J.det * 1 := by
    rw [mul_one]
    calc J.det * ((PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹)).det * ((1 - X) * (1 + X)⁻¹).det)
        = (PI.UnitaryApproxDefs.cT ρ ((1 - X) * (1 + X)⁻¹)).det * J.det * ((1 - X) * (1 + X)⁻¹).det := by ring
      _ = J.det := hdet
  have h3 := hJd.mul_left_cancel h2
  have hu : IsUnit ((1 - X) * (1 + X)⁻¹).det := isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact h3⟩
  exact ⟨Matrix.nonsingInvUnit _ hu, hU, rfl⟩

theorem lie_of_unitary (J g : Matrix n n A) (hg : PI.UnitaryApproxDefs.cT ρ g * J * g = J) (hP : IsUnit (1 + g).det) :
    PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹) = 0 := by
  have hL : PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + g) = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.mul_nonsing_inv _ hP, PI.UnitaryApproxDefs.cT_one]
  have hLinv : PI.UnitaryApproxDefs.cT ρ (1 + g) * PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ = 1 := by
    rw [← PI.UnitaryApproxDefs.cT_mul, Matrix.nonsing_inv_mul _ hP, PI.UnitaryApproxDefs.cT_one]
  have hR : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
  have e1 : (1 - PI.UnitaryApproxDefs.cT ρ g) * J * (1 + g) + (1 + PI.UnitaryApproxDefs.cT ρ g) * J * (1 - g) =
      J + J - (PI.UnitaryApproxDefs.cT ρ g * J * g + PI.UnitaryApproxDefs.cT ρ g * J * g) := by noncomm_ring
  have key : PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) * (1 + g) = 0 := by
    rw [PI.UnitaryApproxDefs.cT_mul]
    calc PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 - g) * J + J * ((1 - g) * (1 + g)⁻¹)) * (1 + g)
        = (PI.UnitaryApproxDefs.cT ρ (1 + g) * PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹) * PI.UnitaryApproxDefs.cT ρ (1 - g) * J * (1 + g) +
            PI.UnitaryApproxDefs.cT ρ (1 + g) * J * (1 - g) * ((1 + g)⁻¹ * (1 + g)) := by
          simp only [mul_add, add_mul, mul_assoc]
          abel
      _ = PI.UnitaryApproxDefs.cT ρ (1 - g) * J * (1 + g) + PI.UnitaryApproxDefs.cT ρ (1 + g) * J * (1 - g) := by
          rw [hLinv, Matrix.nonsing_inv_mul _ hP, one_mul, mul_one]
      _ = 0 := by
          rw [cT_sub ρ, cT_add ρ, PI.UnitaryApproxDefs.cT_one, e1, hg, sub_self]
  calc PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)
      = PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) *
          ((1 + g) * (1 + g)⁻¹) := by rw [hL, hR, one_mul, mul_one]
    _ = PI.UnitaryApproxDefs.cT ρ (1 + g)⁻¹ * (PI.UnitaryApproxDefs.cT ρ (1 + g) * (PI.UnitaryApproxDefs.cT ρ ((1 - g) * (1 + g)⁻¹) * J + J * ((1 - g) * (1 + g)⁻¹)) *
          (1 + g)) * (1 + g)⁻¹ := by simp only [mul_assoc]
    _ = 0 := by rw [key, mul_zero, zero_mul]

end PI.UnitaryApproxFinWork

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.SigmaMemIntOE
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : Type} [Fintype n] [DecidableEq n]

def MS (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
    (M : Matrix n n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i j, M i j ∈ Sv E v

def MC (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F)
    (M : Matrix n n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∃ A, MS E v A ∧ M = dv E v d • A

variable {v : HeightOneSpectrum (𝓞 F)}

theorem MS_mul {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)

theorem MS_add {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M + N) := fun i j => Subring.add_mem _ (hM i j) (hN i j)

theorem MS_sub {M N : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) (hN : MS E v N) :
    MS E v (M - N) := fun i j => Subring.sub_mem _ (hM i j) (hN i j)

theorem MS_one : MS E v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem MS_smul {a : E ⊗[F] v.adicCompletion F} (ha : a ∈ Sv E v)
    {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : MS E v (a • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ ha (hM i j)

def toS {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : Matrix n n (Sv E v) :=
  fun i j => ⟨M i j, hM i j⟩

theorem map_toS {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    (Sv E v).subtype.mapMatrix (toS hM) = M := by
  ext i j
  rfl

theorem MS_adjugate {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    MS E v M.adjugate := by
  intro i j
  rw [← map_toS hM, ← RingHom.map_adjugate]
  exact ((toS hM).adjugate i j).2

private lemma dv_mem_Sv' (d : 𝓞 F) : dv E v d ∈ Sv E v := by
  apply Subring.subset_closure
  left
  exact ⟨⟨algebraMap F E (d : F),
    ⟨⟨algebraMap F E (d : F), (RingOfIntegers.isIntegral_coe d).algebraMap⟩, rfl⟩⟩, rfl⟩

theorem det_one_add (π : 𝓞 F) {A : Matrix n n (E ⊗[F] v.adicCompletion F)} (hA : MS E v A) :
    ∃ s ∈ Sv E v, (1 + dv E v π • A).det = 1 + dv E v π * s := by
  let p : Sv E v := ⟨dv E v π, dv_mem_Sv' π⟩
  let B := toS hA
  let I : Ideal (Sv E v) := Ideal.span {p}
  have hp0 : Ideal.Quotient.mk I p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have h0 : (Ideal.Quotient.mk I).mapMatrix (p • B) = 0 := by
    ext i j
    simp [hp0]
  have hmap : (Ideal.Quotient.mk I).mapMatrix (1 + p • B) = 1 := by
    rw [map_add (f := _), map_one, h0, add_zero]
  have hdet : Ideal.Quotient.mk I ((1 + p • B).det - 1) = 0 := by
    rw [map_sub, RingHom.map_det, hmap, Matrix.det_one, map_one, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdet)
  refine ⟨(t : E ⊗[F] v.adicCompletion F), t.2, ?_⟩
  have h2 : (Sv E v).subtype.mapMatrix (1 + p • B) = 1 + dv E v π • A := by
    rw [map_add (f := _), map_one]
    congr 1
  have h4 : (1 + p • B).det = 1 + p * t := by
    rw [mul_comm, ht]
    ring
  rw [← h2, ← RingHom.map_det, h4]
  simp [p]

theorem MC_entries {d : 𝓞 F} {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (h : MC E v d M) (i j : n) :
    Cong E v d (M i j) := by
  obtain ⟨A, hA, rfl⟩ := h
  exact ⟨A i j, hA i j, by rw [Matrix.smul_apply, smul_eq_mul]⟩

theorem MC_of_entries {d : 𝓞 F} {M : Matrix n n (E ⊗[F] v.adicCompletion F)}
    (h : ∀ i j, Cong E v d (M i j)) : MC E v d M := by
  choose t ht heq using h
  refine ⟨Matrix.of fun i j => t i j, fun i j => ht i j, ?_⟩
  ext i j
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact heq i j

theorem MC_cancel {c e : 𝓞 F} (hc : c ≠ 0) {M A : Matrix n n (E ⊗[F] v.adicCompletion F)}
    (h : dv E v c • M = dv E v (c * e) • A) : M = dv E v e • A := by
  have hx : algebraMap F E (c : F) ≠ 0 := by simpa using hc
  have hu : IsUnit (dv E v c) :=
    (IsUnit.mk0 _ hx).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))
  have hmul : dv E v (c * e) = dv E v c * dv E v e := by simp [dv]
  rw [hmul, mul_smul] at h
  exact hu.smul_left_cancel.1 h

theorem sigma_mem_intOE (σ : E →ₐ[F] E) {x : E} (hx : x ∈ PI.UnitaryApproxDefs.intOE E) : σ x ∈ PI.UnitaryApproxDefs.intOE E := by
  simp only [PI.UnitaryApproxDefs.intOE, RingHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨σ y, (RingOfIntegers.isIntegral_coe y).map σ.toRingHom.toIntAlgHom⟩, rfl⟩

theorem sigR_mem_Sv (σ : E →ₐ[F] E) {s : E ⊗[F] v.adicCompletion F} (hs : s ∈ Sv E v) :
    PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) s ∈ Sv E v := by
  have h : Sv E v ≤ (Sv E v).comap (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · simp only [Subring.coe_comap, Set.mem_preimage]
      apply Subring.subset_closure
      left
      exact ⟨⟨σ x, sigma_mem_intOE σ hx⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩
    · simp only [Subring.coe_comap, Set.mem_preimage]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, by simp [PI.UnitaryApproxDefs.sigR]⟩
  exact h hs

theorem MS_cT (σ : E →ₐ[F] E) {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    MS E v (PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) M) := fun i j => sigR_mem_Sv σ (hM j i)

theorem sigR_dv (σ : E →ₐ[F] E) (d : 𝓞 F) : PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (dv E v d) = dv E v d := by
  simp [PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE, dv]

theorem cT_map (σ : E →ₐ[F] E) (M : Matrix n n E) :
    PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (M.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) =
      (PI.UnitaryApproxDefs.cT (σ : E →+* E) M).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) := by
  ext i j
  simp [PI.UnitaryApproxDefs.cT, PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]

end PI.UnitaryApproxFinWork

end
end

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

theorem dv_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : dv E v 2 = 2 := by
  have h2 : ((2 : 𝓞 F) : F) = 2 := map_ofNat (algebraMap (𝓞 F) F) 2
  simp only [dv, h2, map_ofNat]

theorem skew_approx (hAE : ApproxE) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (Y : (v : HeightOneSpectrum (𝓞 F)) → Matrix n n (E ⊗[F] v.adicCompletion F))
    (hY : ∀ v ∈ T, PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (Y v) = -Y v) (δ : 𝓞 F) (hδ : δ ≠ 0) :
    ∃ Y' : Matrix n n E, PI.UnitaryApproxDefs.cT (σ : E →+* E) Y' = -Y' ∧
      ∀ v ∈ T, MC E v δ (Y'.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) - Y v) := by
  have h2δ : (2 * δ : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hδ
  have hz : ∀ i j, ∃ e : E, ∀ v ∈ T,
      Cong E v (2 * δ) (Y v i j - PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) e) :=
    fun i j => hAE F E T (fun v => Y v i j) (2 * δ) h2δ
  choose Z hZ using hz
  refine ⟨Matrix.of fun i j => (2⁻¹ : E) * (Z i j - σ (Z j i)), ?_, fun v hv => ?_⟩
  · ext i j
    show (σ : E →+* E) ((2⁻¹ : E) * (Z j i - σ (Z i j))) = -((2⁻¹ : E) * (Z i j - σ (Z j i)))
    simp only [AlgHom.coe_toRingHom, map_mul, map_inv₀, map_ofNat, map_sub, hσ]
    ring
  · obtain ⟨A, hAS, hAeq⟩ := MC_of_entries (E := E) (v := v) (d := 2 * δ)
      (M := Y v - (Matrix.of Z).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) (fun i j => hZ i j v hv)
    refine ⟨PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) A - A, MS_sub (MS_cT σ hAS) hAS, ?_⟩
    ext i j
    have e1 := congrFun (congrFun hAeq i) j
    have e2 := congrArg (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (congrFun (congrFun hAeq j) i)
    have e3 := congrFun (congrFun (hY v hv) i) j
    change PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (Y v j i) = -(Y v i j) at e3
    change Y v i j - PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (Z i j) = dv E v (2 * δ) * A i j at e1
    change PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (Y v j i - PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (Z j i)) =
      PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (dv E v (2 * δ) * A j i) at e2
    rw [map_sub, map_mul, sigR_inclE, sigR_dv] at e2
    rw [dv_mul, dv_two] at e1 e2
    change PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) ((2⁻¹ : E) * (Z i j - σ (Z j i))) - Y v i j =
      dv E v δ * (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (A j i) - A i j)
    have hh : PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E) * 2 = 1 := by
      rw [← map_ofNat (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero,
        map_one]
    rw [map_mul, map_sub]
    linear_combination (-(PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E))) * e1 +
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E)) * e2 -
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (2⁻¹ : E)) * e3 +
      (Y v i j + dv E v δ * (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) (A j i) - A i j)) * hh

end PI.UnitaryApproxFinWork

end
end

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

theorem exists_common {F : Type} [Field F] [NumberField F] {ι : Type} (s : Finset ι)
    (Q : ι → 𝓞 F → Prop) (hQ : ∀ i c r, Q i c → Q i (c * r)) (h : ∀ i ∈ s, ∃ c, c ≠ 0 ∧ Q i c) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i ∈ s, Q i c := by
  first | exact Bl.general_b_fact_right_ter.goal1 .. | (apply Bl.general_b_fact_right_ter.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_ter.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_ter.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_ter.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_ter.goal1 <;> first | assumption | infer_instance)

theorem local_err {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (h2 : IsUnit (2 : R)) (g X XR W N γR : Matrix n n R)
    (hXP : (1 + X) * (1 + g) = 2) (hΔ' : (XR - X) * (1 + g) = (2 : R) • W) (hN : (1 + W) * N = 1)
    (hγ' : γR * (1 + XR) = 1 - XR) :
    g - γR = (1 + g) * W * N := by
  obtain ⟨Δ, rfl⟩ : ∃ Δ, XR = X + Δ := ⟨XR - X, by abel⟩
  have hΔ : Δ * (1 + g) = (2 : R) • W := by rwa [add_sub_cancel_left] at hΔ'
  have hγ : γR * (1 + (X + Δ)) = 1 - (X + Δ) := hγ'
  have h2m : (2 : Matrix n n R) = (2 : R) • 1 := by rw [two_smul, one_add_one_eq_two]
  have hQP : (1 + (X + Δ)) * (1 + g) = (2 : R) • (1 + W) := by
    rw [← add_assoc, Matrix.add_mul, hXP, hΔ, h2m, smul_add]
  have key : (2 : R) • (γR * (1 + W)) = (2 : R) • ((1 + g) - (1 + W)) := by
    have e1 : γR * ((2 : R) • (1 + W)) = (1 - (X + Δ)) * (1 + g) := by
      rw [← hQP, ← Matrix.mul_assoc, hγ]
    rw [← Matrix.mul_smul, e1, smul_sub, ← hQP]
    have e2 : (1 - (X + Δ)) * (1 + g) = (2 : R) • (1 + g) - (1 + (X + Δ)) * (1 + g) := by
      rw [two_smul]; noncomm_ring
    rw [e2]
  have k2 := h2.smul_left_cancel.mp key
  calc g - γR = g * ((1 + W) * N) - γR * ((1 + W) * N) := by rw [hN, Matrix.mul_one, Matrix.mul_one]
    _ = g * ((1 + W) * N) - (γR * (1 + W)) * N := by rw [Matrix.mul_assoc]
    _ = (1 + g) * W * N := by rw [k2]; noncomm_ring

theorem local_unit {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (h2 : IsUnit (2 : R)) (g X XR W : Matrix n n R)
    (hXP : (1 + X) * (1 + g) = 2) (hΔ : (XR - X) * (1 + g) = (2 : R) • W) (hW : IsUnit (1 + W).det) :
    IsUnit (1 + XR).det := by
  have h2m : (2 : Matrix n n R) = (2 : R) • 1 := by rw [two_smul, one_add_one_eq_two]
  have hQP : (1 + XR) * (1 + g) = (2 : R) • (1 + W) := by
    have : 1 + XR = (1 + X) + (XR - X) := by abel
    rw [this, Matrix.add_mul, hXP, hΔ, h2m, smul_add]
  have hd := congrArg Matrix.det hQP
  rw [Matrix.det_mul, Matrix.det_smul] at hd
  have hu : IsUnit ((1 + XR).det * (1 + g).det) := by
    rw [hd]; exact (h2.pow _).mul hW
  exact isUnit_of_mul_isUnit_left hu

theorem cayleyStep : CayleyStep := by
  intro hAE hB hU F E _ _ _ _ _ n _ _ σ J h1 hJ hdet T g hg hP D hD
  classical
  rcases T.eq_empty_or_nonempty with hT | ⟨v0, hv0⟩
  · exact ⟨1, Subgroup.one_mem _, by simp [hT]⟩

  have hJJi : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hdet
  have hJiJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  have hJiH : PI.UnitaryApproxDefs.cT (σ : E →+* E) J⁻¹ = J⁻¹ := by
    have hcTJ : PI.UnitaryApproxDefs.cT (σ : E →+* E) J = J := hJ
    have : PI.UnitaryApproxDefs.cT (σ : E →+* E) J⁻¹ * J = 1 := by
      calc PI.UnitaryApproxDefs.cT (σ : E →+* E) J⁻¹ * J = PI.UnitaryApproxDefs.cT (σ : E →+* E) J⁻¹ * PI.UnitaryApproxDefs.cT (σ : E →+* E) J := by
            rw [hcTJ]
        _ = PI.UnitaryApproxDefs.cT (σ : E →+* E) (J * J⁻¹) := (PI.UnitaryApproxDefs.cT_mul _ _ _).symm
        _ = 1 := by rw [hJJi, PI.UnitaryApproxDefs.cT_one]
    exact (Matrix.inv_eq_left_inv this).symm
  obtain ⟨cJ, hcJ0, hcJ⟩ := exists_common (F := F) (Finset.univ : Finset (n × n))
    (fun p c => algebraMap F E (c : F) * J⁻¹ p.1 p.2 ∈ PI.UnitaryApproxDefs.intOE E)
    (fun p c r h => by
      rw [show ((c * r : 𝓞 F) : F) = (c : F) * (r : F) from map_mul (algebraMap (𝓞 F) F) c r,
        map_mul, mul_comm (algebraMap F E (c : F)), mul_assoc]
      exact Subring.mul_mem _ (algebraMap_mem_intOE r) h)
    (fun p _ => exists_int_mul (J⁻¹ p.1 p.2))

  obtain ⟨cP, hcP0, hcP⟩ := exists_common (F := F) (T ×ˢ (Finset.univ : Finset (n × n)))
    (fun q c => dv E q.1 c * (1 + (g q.1 : Matrix n n (E ⊗[F] q.1.adicCompletion F))) q.2.1 q.2.2 ∈
      Sv E q.1)
    (fun q c r h => by
      rw [dv_mul, mul_comm (dv E q.1 c), mul_assoc]
      exact Subring.mul_mem _ (dv_mem_Sv _ r) h)
    (fun q _ => hB F E q.1 _)

  obtain ⟨π, hπ0, hπ⟩ := exists_common (F := F) T (fun v c => c ∈ v.asIdeal)
    (fun v c r h => Ideal.mul_mem_right r _ h)
    (fun v _ => Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot |>.imp fun c hc => ⟨hc.2, hc.1⟩)
  set e : 𝓞 F := 2 * (cP * D * π) with he
  set δ : 𝓞 F := cJ * cP * e with hδ
  have he0 : e ≠ 0 := mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero hcP0 hD) hπ0)
  have hδ0 : δ ≠ 0 := mul_ne_zero (mul_ne_zero hcJ0 hcP0) he0

  let Xl : (v : HeightOneSpectrum (𝓞 F)) → Matrix n n (E ⊗[F] v.adicCompletion F) := fun v =>
    (1 - (g v : Matrix n n _)) * (1 + (g v : Matrix n n _))⁻¹
  have hJR : ∀ v : HeightOneSpectrum (𝓞 F), PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F))
      (J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) = J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) := by
    intro v; rw [cT_map]; rw [show PI.UnitaryApproxDefs.cT (σ : E →+* E) J = J from hJ]
  have hlie : ∀ v ∈ T, PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)) (Xl v) *
      J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) +
      J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) * Xl v = 0 := fun v hv =>
    lie_of_unitary _ _ _ (hg v hv) (hP v hv)
  have hskew : ∀ v ∈ T, PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F))
      (J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) * Xl v) =
      -(J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) * Xl v) := by
    intro v hv
    rw [PI.UnitaryApproxDefs.cT_mul, hJR]
    exact eq_neg_of_add_eq_zero_left (hlie v hv)
  obtain ⟨Y', hY'skew, hY'⟩ := skew_approx hAE σ h1 T
    (fun v => J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) * Xl v) hskew δ hδ0

  set X' : Matrix n n E := J⁻¹ * Y' with hX'
  have hX'lie : PI.UnitaryApproxDefs.cT (σ : E →+* E) X' * J + J * X' = 0 := by
    rw [hX', PI.UnitaryApproxDefs.cT_mul, hJiH, hY'skew, Matrix.mul_assoc, hJiJ, Matrix.mul_one, ← Matrix.mul_assoc,
      hJJi, Matrix.one_mul, neg_add_cancel]

  have hloc : ∀ v ∈ T, ∃ W N : Matrix n n (E ⊗[F] v.adicCompletion F),
      (1 + Xl v) * (1 + (g v : Matrix n n _)) = 2 ∧
      (X'.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) - Xl v) * (1 + (g v : Matrix n n _)) =
        (2 : E ⊗[F] v.adicCompletion F) • W ∧
      (1 + W) * N = 1 ∧ IsUnit (1 + W).det ∧ MC E v D ((1 + (g v : Matrix n n _)) * W * N) := by
    intro v hv
    set ι : E →+* E ⊗[F] v.adicCompletion F := PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) with hι
    set P : Matrix n n (E ⊗[F] v.adicCompletion F) := 1 + (g v : Matrix n n _) with hPdef
    have hXP : (1 + Xl v) * P = 2 := by
      show (1 + (1 - (g v : Matrix n n _)) * P⁻¹) * P = 2
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hP v hv),
        Matrix.mul_one, hPdef]
      rw [← one_add_one_eq_two]
      abel
    have hJiJR : J⁻¹.map ι * J.map ι = 1 := by
      rw [← Matrix.map_mul, hJiJ, Matrix.map_one _ (map_zero ι) (map_one ι)]
    have hXR : X'.map ι = J⁻¹.map ι * Y'.map ι := by rw [hX', Matrix.map_mul]
    obtain ⟨A, hAS, hAeq⟩ := hY' v hv
    have hAeq' : Y'.map ι - J.map ι * Xl v = dv E v δ • A := hAeq
    have hΔ1 : X'.map ι - Xl v = J⁻¹.map ι * (Y'.map ι - J.map ι * Xl v) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hJiJR, Matrix.one_mul, hXR]
    set B : Matrix n n (E ⊗[F] v.adicCompletion F) := dv E v cJ • J⁻¹.map ι with hBdef
    have hBS : MS E v B := fun i j => by
      rw [hBdef, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, hι, dv, ← map_mul]
      exact inclE_mem_Sv v (hcJ (i, j) (Finset.mem_univ _))
    set P' : Matrix n n (E ⊗[F] v.adicCompletion F) := dv E v cP • P with hP'def
    have hP'S : MS E v P' := fun i j => by
      rw [hP'def, Matrix.smul_apply, smul_eq_mul]
      exact hcP (v, (i, j)) (Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩)
    have hc : dv E v (cJ * cP) • ((X'.map ι - Xl v) * P) = dv E v (cJ * cP * e) • (B * A * P') := by
      rw [hΔ1, hAeq', hBdef, hP'def, hδ]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, dv_mul]
      congr 1
      ring
    have hΔP := MC_cancel (mul_ne_zero hcJ0 hcP0) hc
    set W1 : Matrix n n (E ⊗[F] v.adicCompletion F) := dv E v (cP * D) • (B * A * P') with hW1def
    have hW1S : MS E v W1 := MS_smul (dv_mem_Sv v _) (MS_mul (MS_mul hBS hAS) hP'S)
    obtain ⟨s, hs, hdet1⟩ := det_one_add π hW1S
    obtain ⟨u, hu, hu1⟩ := hU F E v π (hπ v hv) s hs
    refine ⟨dv E v π • W1, u • (1 + dv E v π • W1).adjugate, hXP, ?_, ?_, ?_, ?_⟩
    · rw [hΔP, he, hW1def, dv_mul, dv_two, dv_mul v (cP * D) π]
      simp only [smul_smul]
      congr 1
      ring
    · rw [Matrix.mul_smul, Matrix.mul_adjugate, hdet1, smul_smul, mul_comm u, hu1, one_smul]
    · rw [hdet1]; exact IsUnit.of_mul_eq_one _ hu1
    · refine ⟨(dv E v π • (P' * (B * A * P'))) * (u • (1 + dv E v π • W1).adjugate),
        MS_mul (MS_smul (dv_mem_Sv v π) (MS_mul hP'S (MS_mul (MS_mul hBS hAS) hP'S)))
          (MS_smul hu (MS_adjugate (MS_add MS_one (MS_smul (dv_mem_Sv v π) hW1S)))), ?_⟩
      rw [hW1def, hP'def]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, dv_mul]
      congr 1
      ring
  have h2u : ∀ v : HeightOneSpectrum (𝓞 F), IsUnit (2 : E ⊗[F] v.adicCompletion F) := by
    intro v
    have := (IsUnit.mk0 (2 : E) two_ne_zero).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))
    rwa [map_ofNat] at this

  have hQ : IsUnit (1 + X').det := by
    obtain ⟨W, N, hXP, hΔ, -, hWu, -⟩ := hloc v0 hv0
    have hl := local_unit (h2u v0) _ _ _ _ hXP hΔ hWu
    have hmap : (1 + X'.map (PI.UnitaryApproxDefs.inclE (F := F) (v0.adicCompletion F))).det =
        PI.UnitaryApproxDefs.inclE (F := F) (v0.adicCompletion F) (1 + X').det := by
      rw [RingHom.map_det, map_add (f := _), map_one]; rfl
    rw [hmap] at hl
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, map_zero, isUnit_zero_iff] at hl
    have hinj : Function.Injective (PI.UnitaryApproxDefs.inclE (F := F) (v0.adicCompletion F) : E → _) :=
      Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := E)
        (B := v0.adicCompletion F) (algebraMap F _).injective
    exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact hl))
  obtain ⟨γ, hγU, hγ⟩ := cayley_mem_UJ (σ : E →+* E) J X' hdet hX'lie hQ
  refine ⟨γ, hγU, fun v hv i j => ?_⟩
  obtain ⟨W, N, hXP, hΔ, hN, -, hMC⟩ := hloc v hv
  have hγQ : (γ : Matrix n n E) * (1 + X') = 1 - X' := by
    rw [hγ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.mul_one]
  have hγR : (γ : Matrix n n E).map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) *
      (1 + X'.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) =
      1 - X'.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)) := by
    have := congrArg (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F)).mapMatrix hγQ
    simpa [map_mul, map_add (f := _), map_sub, map_one] using this
  have herr := local_err (h2u v) _ _ _ _ _ _ hXP hΔ hN hγR
  rw [← herr] at hMC
  exact MC_entries hMC i j

end PI.UnitaryApproxFinWork

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.ApproxE
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_span_int : ∃ (d : ℕ) (b : Fin d → E), (∀ k, b k ∈ PI.UnitaryApproxDefs.intOE E) ∧
    ∀ e : E, ∃ f : Fin d → F, e = ∑ k, f k • b k := by
  let B := (NumberField.integralBasis E).reindex (Fintype.equivFin _)
  refine ⟨_, fun k => B k, fun k => ?_, fun e => ?_⟩
  · show B k ∈ (algebraMap (𝓞 E) E).range
    refine ⟨RingOfIntegers.basis E ((Fintype.equivFin _).symm k), ?_⟩
    simp only [B, Module.Basis.reindex_apply, NumberField.integralBasis_apply]
  · refine ⟨fun k => ((B.repr e k : ℚ) : F), ?_⟩
    conv_lhs => rw [← B.sum_repr e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_ratCast, eq_ratCast]

theorem tensor_decomp {d : ℕ} (b : Fin d → E) (hb : ∀ e : E, ∃ f : Fin d → F, e = ∑ k, f k • b k)
    {R : Type} [CommRing R] [Algebra F R] (x : E ⊗[F] R) :
    ∃ c : Fin d → R, x = ∑ k, b k ⊗ₜ[F] c k := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul e r =>
    obtain ⟨f, hf⟩ := hb e
    refine ⟨fun k => f k • r, ?_⟩
    rw [hf, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨c1, h1⟩ := hx
    obtain ⟨c2, h2⟩ := hy
    refine ⟨c1 + c2, ?_⟩
    simp [h1, h2, TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem approxEStep : ApproxEStep := by
  intro hW
  unfold ApproxE
  intro F E _ _ _ _ _ T x D hD
  obtain ⟨d, b, hbint, hb⟩ := exists_span_int (F := F) (E := E)
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : Fin d → v.adicCompletion F,
      x v = ∑ k, b k ⊗ₜ[F] c k := fun v => tensor_decomp b hb (x v)
  choose c hc using hc
  have ha : ∀ k, ∃ a : F, ∀ v ∈ T, ∃ t ∈ v.adicCompletionIntegers F,
      c v k - algebraMap F (v.adicCompletion F) a = algebraMap F (v.adicCompletion F) (D : F) * t :=
    fun k => hW F T (fun v => c v k) D hD
  choose a ht using ha
  refine ⟨∑ k, a k • b k, fun v hv => ?_⟩
  choose t htO hteq using fun k => ht k v hv
  refine ⟨∑ k, (1 : E) ⊗ₜ[F] t k * PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (b k), ?_, ?_⟩
  · exact Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (one_tmul_mem_Sv v (htO k)) (inclE_mem_Sv v (hbint k))
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hc v, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [PI.UnitaryApproxDefs.inclE, dv, Algebra.TensorProduct.includeLeftRingHom_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [TensorProduct.smul_tmul, ← TensorProduct.tmul_sub, Algebra.smul_def (a k), mul_one, hteq k,
        ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]

end PI.UnitaryApproxFinWork

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.UnitaryScalars
noncomputable section

open TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace PI.UnitaryApproxFinWork

theorem unitary_scalars : UnitS := by
  intro F E _ _ _ _ _ v π hπ s hs
  classical
  let O := v.adicCompletionIntegers F
  let S := Sv E v
  have hgen2 : ∀ y : O, ((1 : E) ⊗ₜ[F] (y : v.adicCompletion F)) ∈ S := by
    intro y
    exact Subring.subset_closure (Or.inr ⟨⟨y, y.2⟩, rfl⟩)
  let ψ : O →+* E ⊗[F] v.adicCompletion F :=
    (Algebra.TensorProduct.includeRight :
      v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F).toRingHom.comp O.subtype
  have hψ : ∀ y : O, ψ y = (1 : E) ⊗ₜ[F] (y : v.adicCompletion F) := fun y => rfl
  let φ : O →+* S := ψ.codRestrict S (fun y => by rw [hψ]; exact hgen2 y)
  letI : Algebra O (E ⊗[F] v.adicCompletion F) := ψ.toAlgebra
  letI : Algebra O S := φ.toAlgebra
  let f : S →ₐ[O] E ⊗[F] v.adicCompletion F := { S.subtype with commutes' := fun r => rfl }
  have hle : S ≤ (integralClosure O (E ⊗[F] v.adicCompletion F)).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hx
      obtain ⟨p, hpm, hp⟩ := NumberField.RingOfIntegers.isIntegral_coe z
      refine ⟨p.map (Int.castRingHom O), hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap O (E ⊗[F] v.adicCompletion F)).comp (Int.castRingHom O) =
          (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (E := E)).comp (algebraMap ℤ E) :=
        RingHom.ext_int _ _
      rw [hcomp]
      have := Polynomial.hom_eval₂ p (algebraMap ℤ E) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (E := E))
        (algebraMap (𝓞 E) E z)
      rw [hp, map_zero] at this
      exact this.symm
    · exact isIntegral_algebraMap (x := (⟨y, hy⟩ : O))
  have hIntS : Algebra.IsIntegral O S :=
    ⟨fun x => (isIntegral_algHom_iff f Subtype.val_injective).1 (hle x.2)⟩
  have hπv : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    rw [wa_valued_algebraMap]
    exact (valuation_lt_one_iff_mem v π).2 hπ
  let πO : O := ⟨algebraMap F (v.adicCompletion F) (π : F), by
    rw [mem_adicCompletionIntegers]; exact hπv.le⟩
  have hπmax : πO ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
    have h1 : Valued.v (w : v.adicCompletion F) ≤ 1 := by
      have := w.2
      rwa [mem_adicCompletionIntegers] at this
    have h2 : algebraMap F (v.adicCompletion F) (π : F) * (w : v.adicCompletion F) = 1 :=
      congrArg Subtype.val hw
    have h3 : Valued.v (algebraMap F (v.adicCompletion F) (π : F) * (w : v.adicCompletion F)) < 1 :=
      calc _ = Valued.v (algebraMap F (v.adicCompletion F) (π : F)) *
            Valued.v (w : v.adicCompletion F) := map_mul _ _ _
        _ ≤ Valued.v (algebraMap F (v.adicCompletion F) (π : F)) * 1 := mul_le_mul' le_rfl h1
        _ < 1 := by rw [mul_one]; exact hπv
    rw [h2, map_one] at h3
    exact lt_irrefl _ h3
  have hd : dv E v π = (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) (π : F) := by
    simp only [dv, PI.UnitaryApproxDefs.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.algebraMap_eq_smul_one]
    exact TensorProduct.smul_tmul _ _ _
  have hxS : 1 + dv E v π * s ∈ S :=
    S.add_mem S.one_mem (S.mul_mem (by rw [hd]; exact hgen2 πO) hs)
  have key : IsUnit (⟨1 + dv E v π * s, hxS⟩ : S) := by
    by_contra h
    obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 h)
    have hP : (M.comap (algebraMap O S)).IsMaximal := by
      letI := hIntS
      exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    have hπM : algebraMap O S πO ∈ M := by
      have : πO ∈ M.comap (algebraMap O S) := by
        rw [IsLocalRing.eq_maximalIdeal hP]; exact hπmax
      exact this
    have e : (1 : S) = ⟨1 + dv E v π * s, hxS⟩ - algebraMap O S πO * ⟨s, hs⟩ := by
      apply Subtype.ext
      change (1 : E ⊗[F] v.adicCompletion F) = (1 + dv E v π * s) -
        ((1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) (π : F)) * s
      rw [hd]; ring
    have h1 : (1 : S) ∈ M := by
      rw [e]; exact M.sub_mem hxM (M.mul_mem_right _ hπM)
    exact hM.ne_top ((Ideal.eq_top_iff_one M).2 h1)
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 key
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

end PI.UnitaryApproxFinWork

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.BoundedRationalUnitary
noncomputable section

open TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace PI.UnitaryApproxFinWork

theorem bd_int_mult {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ N : ℤ, N ≠ 0 ∧ IsIntegral ℤ ((N : K) * e) := by
  have halg : IsAlgebraic ℤ e :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  exact ⟨y, hy0, by rwa [zsmul_eq_mul] at hyint⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bd_local (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) :
    ∃ N : ℤ, N ≠ 0 ∧ Valued.v ((N : v.adicCompletion F) * a) ≤ 1 := by
  obtain ⟨b, hb, hab⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨(Ideal.absNorm (Ideal.span {b}) : ℤ), ?_, ?_⟩
  · have h0 : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hb0
    exact_mod_cast h0
  · have hab' : a * algebraMap F (v.adicCompletion F) (b : F) ∈ v.adicCompletionIntegers F := by
      first
      | exact hab
      | (convert hab using 2)
      | simpa using hab
    have hc' : algebraMap F (v.adicCompletion F) (c : F) ∈ v.adicCompletionIntegers F := by
      first
      | exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v c
      | (convert IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v c using 1)
      | simpa using IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v c
    have hcast : algebraMap F (v.adicCompletion F) (c : F) * algebraMap F (v.adicCompletion F) (b : F) =
        ((Ideal.absNorm (Ideal.span {b}) : ℤ) : v.adicCompletion F) := by
      rw [← map_mul, show (c : F) * (b : F) = ((c * b : 𝓞 F) : F) from rfl, hc]
      simp
    rw [← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← hcast]
    have e : algebraMap F (v.adicCompletion F) (c : F) * algebraMap F (v.adicCompletion F) (b : F) * a =
        algebraMap F (v.adicCompletion F) (c : F) * (a * algebraMap F (v.adicCompletion F) (b : F)) := by
      ring
    rw [e]
    exact mul_mem hc' hab'

theorem bd_main (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : E ⊗[F] v.adicCompletion F) * x ∈ Sv E v := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | tmul e t =>
    obtain ⟨N₁, hN₁, h₁⟩ := bd_int_mult e
    obtain ⟨N₂, hN₂, h₂⟩ := bd_local v t
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, ?_⟩
    have hL : ((N₁ : ℤ) : E ⊗[F] v.adicCompletion F) = (N₁ : E) ⊗ₜ[F] (1 : v.adicCompletion F) := by
      rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_intCast]
    have hR : ((N₂ : ℤ) : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] (N₂ : v.adicCompletion F) := by
      rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]
    have e1 : ((N₁ * N₂ : ℤ) : E ⊗[F] v.adicCompletion F) * (e ⊗ₜ[F] t) =
        ((N₁ : E) * e) ⊗ₜ[F] (1 : v.adicCompletion F) *
          ((1 : E) ⊗ₜ[F] ((N₂ : v.adicCompletion F) * t)) := by
      rw [Int.cast_mul, hL, hR]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e1]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨⟨(N₁ : E) * e,
      RingHom.mem_range.2 ⟨⟨_, h₁⟩, rfl⟩⟩, rfl⟩))
      (Subring.subset_closure (Set.mem_union_right _ ⟨⟨(N₂ : v.adicCompletion F) * t, ?_⟩, rfl⟩))
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 h₂
  | add x y hx hy =>
    obtain ⟨N₁, hN₁, h₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, ?_⟩
    have e2 : ((N₁ * N₂ : ℤ) : E ⊗[F] v.adicCompletion F) * (x + y) =
        (N₂ : E ⊗[F] v.adicCompletion F) * ((N₁ : E ⊗[F] v.adicCompletion F) * x) +
          (N₁ : E ⊗[F] v.adicCompletion F) * ((N₂ : E ⊗[F] v.adicCompletion F) * y) := by
      push_cast
      ring
    rw [e2]
    exact Subring.add_mem _ (Subring.mul_mem _ (intCast_mem _ N₂) h₁)
      (Subring.mul_mem _ (intCast_mem _ N₁) h₂)

theorem bounded_rational_unitary : BddR := by
  intro F E _ _ _ _ _ v x
  obtain ⟨N, hN, h⟩ := bd_main v x
  refine ⟨(N : 𝓞 F), by exact_mod_cast hN, ?_⟩
  have e : dv E v (N : 𝓞 F) = (N : E ⊗[F] v.adicCompletion F) := by
    unfold dv
    simp [PI.UnitaryApproxDefs.inclE]
  rw [e]
  exact h

end PI.UnitaryApproxFinWork

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.EigenvalueAvoidance
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

theorem ea_finite_bad {E R : Type*} [Field E] [CommRing R] (ι : E →+* R)
    {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n R) (m : Ideal R) [m.IsMaximal] :
    {μ : E | (1 + ι μ • g).det ∈ m}.Finite := by
  classical
  let f : E →+* (R ⧸ m) := (Ideal.Quotient.mk m).comp ι
  let gb : Matrix n n (R ⧸ m) := g.map (Ideal.Quotient.mk m)
  let P : Polynomial (R ⧸ m) :=
    ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C).det
  have hev : ∀ c : R ⧸ m, P.eval c = (1 + c • gb).det := by
    intro c
    have h := (Polynomial.evalRingHom c).map_det
      ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C)
    rw [Polynomial.coe_evalRingHom] at h
    show Polynomial.eval c (Matrix.det _) = _
    rw [h]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring
  have hP0 : P ≠ 0 := by
    intro h
    have h0 := hev 0
    rw [h] at h0
    simp at h0
  have hfin : {c : R ⧸ m | P.eval c = 0}.Finite := by
    apply (P.roots.toFinset.finite_toSet).subset
    intro c hc
    simp only [Set.mem_setOf_eq] at hc
    simp [Polynomial.mem_roots hP0, hc]
  apply (hfin.preimage (fun _ _ _ _ h => f.injective h)).subset
  intro μ hμ
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hμ ⊢
  rw [hev]
  have h1 : Ideal.Quotient.mk m (1 + ι μ • g).det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hμ
  rw [RingHom.map_det] at h1
  convert h1 using 2
  ext i j
  by_cases hij : i = j <;> simp [f, gb, Matrix.one_apply, hij]

theorem ea_artinian {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : IsArtinianRing (E ⊗[F] v.adicCompletion F) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (v.adicCompletion F ⊗[F] E) := IsArtinianRing.of_finite (v.adicCompletion F) _
  have hs : Function.Surjective (Algebra.TensorProduct.comm F (v.adicCompletion F) E) :=
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).surjective
  first
    | exact hs.isArtinianRing
    | exact IsArtinianRing.of_surjective _ hs
    | exact Function.Surjective.isArtinianRing hs

theorem eigenvalue_avoidance : EigAvoid := by
  intro F E _ _ _ _ _ n _ _ σ hσ hθ T g
  classical
  obtain ⟨θ, hθ⟩ := hθ
  let bad : Set E := ⋃ v ∈ (T : Set (HeightOneSpectrum (𝓞 F))),
    ⋃ m ∈ {m : Ideal (E ⊗[F] v.adicCompletion F) | m.IsMaximal},
      {μ : E | (1 + PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ • g v).det ∈ m}
  have hbad : bad.Finite := by
    refine Set.Finite.biUnion T.finite_toSet fun v _ => ?_
    haveI : IsArtinianRing (E ⊗[F] v.adicCompletion F) := ea_artinian v
    refine Set.Finite.biUnion (IsArtinianRing.setOfPred_isMaximal_finite _) fun m hm => ?_
    haveI : m.IsMaximal := hm
    exact ea_finite_bad _ (g v) m
  have hnz1 : ∀ t : ℕ, (t : E) + θ ≠ 0 := by
    intro t h
    apply hθ
    have h' : θ = -(t : E) := by linear_combination h
    rw [h', map_neg, map_natCast]
  have hnz2 : ∀ t : ℕ, (t : E) + σ θ ≠ 0 := by
    intro t h
    apply hθ
    have h' : σ θ = -(t : E) := by linear_combination h
    have h'' : θ = -(t : E) := by rw [← hσ θ, h', map_neg, map_natCast]
    rw [h', h'']
  let f : ℕ → E := fun t => ((t : E) + θ) / ((t : E) + σ θ)
  have hinj : Function.Injective f := by
    intro s t hst
    have hst' : ((s : E) + θ) / ((s : E) + σ θ) = ((t : E) + θ) / ((t : E) + σ θ) := hst
    rw [div_eq_div_iff (hnz2 s) (hnz2 t)] at hst'
    have h2 : ((s : E) - t) * (σ θ - θ) = 0 := by linear_combination hst'
    rcases mul_eq_zero.mp h2 with h | h
    · exact_mod_cast sub_eq_zero.mp h
    · exact absurd (sub_eq_zero.mp h) hθ
  have hrange : ¬ Set.range f ⊆ bad := fun h =>
    Set.infinite_range_of_injective hinj (hbad.subset h)
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := Set.not_subset.mp hrange
  refine ⟨f t, ?_, ?_⟩
  · show σ (((t : E) + θ) / ((t : E) + σ θ)) * (((t : E) + θ) / ((t : E) + σ θ)) = 1
    rw [map_div₀, map_add (f := _), map_add (f := _), map_natCast, hσ]
    have h1 := hnz1 t
    have h2 := hnz2 t
    field_simp
  · intro v hv
    by_contra hu
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
    exact ht (Set.mem_iUnion₂.mpr ⟨v, Finset.mem_coe.mpr hv, Set.mem_iUnion₂.mpr ⟨m, hm, hmem⟩⟩)

end PI.UnitaryApproxFinWork

end
end

theorem unitary_approximation_finite : PI.UnitaryApproxFin.UnitaryApproxFin :=
  PI.UnitaryApproxFinWork.unitaryApproxFin_of PI.UnitaryApproxFinWork.topStep
    PI.UnitaryApproxFinWork.cayleyStep PI.UnitaryApproxFinWork.approxEStep
    PI.UnitaryApproxFinWork.weak_approximation_finite_unitary PI.UnitaryApproxFinWork.bounded_rational_unitary
    PI.UnitaryApproxFinWork.unitary_scalars PI.UnitaryApproxFinWork.eigenvalue_avoidance
