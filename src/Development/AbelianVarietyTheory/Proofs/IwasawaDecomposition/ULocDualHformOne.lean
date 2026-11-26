module

public import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ULocDualHformOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

theorem uLocDual_intOE_map {E : Type} [Field E] [NumberField E] (σ : E →+* E) {a : E}
    (ha : a ∈ intOE E) : σ a ∈ intOE E := by
  obtain ⟨r, rfl⟩ := ha
  exact ⟨⟨σ r, (RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom⟩, rfl⟩

theorem uLocDual_hform_one {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (x y : Fin n → E) :
    Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold Formalism.UG.hform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, mul_one]
  · intro j _ hj; rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem uLocDual_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : ∀ x, σ (σ x) = x) (n : ℕ) [NeZero n] (p q : 𝓞 E) (_ : (p : E) ≠ 0) (_ : (q : E) = σ (p : E)),
    Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹))) = rll_dLat n (q : E) := by
  intro F E _ _ _ _ _ σ _ n _ p q hp hq
  have e : dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹)) =
      (rll_dLat n (q : E) : Set (Fin n → E)) := by
    ext y
    rw [SetLike.mem_coe, rll_mem_dLat]
    show (∀ x ∈ rll_dLat n ((p : E)⁻¹), Formalism.UG.hform (σ : E →+* E) 1 x y ∈ (algebraMap (𝓞 E) E).range) ↔ _
    simp only [uLocDual_hform_one]
    constructor
    · intro hy
      refine ⟨fun i hi => ?_, ?_⟩
      · have := hy (Pi.single i 1) ⟨fun j _ => by
          by_cases hj : j = i
          · subst hj; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _, by
          rw [Pi.single_eq_of_ne (Ne.symm hi), mul_zero]; exact zero_mem _⟩
        rw [Finset.sum_eq_single i] at this
        · rwa [Pi.single_eq_same, map_one, one_mul] at this
        · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have := hy (Pi.single (lastIdx n) (p : E)) ⟨fun j hj => by
          rw [Pi.single_eq_of_ne hj]; exact zero_mem _, by
          rw [Pi.single_eq_same, inv_mul_cancel₀ hp]; exact one_mem _⟩
        rw [Finset.sum_eq_single (lastIdx n)] at this
        · rw [Pi.single_eq_same] at this
          show (q : E) * y (lastIdx n) ∈ intOE E
          rw [hq]; exact this
        · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨h1, h2⟩ x ⟨hx1, hx2⟩
      refine sum_mem fun i _ => ?_
      by_cases hi : i = lastIdx n
      · subst hi
        have hl : x (lastIdx n) = (p : E) * ((p : E)⁻¹ * x (lastIdx n)) := by
          rw [mul_inv_cancel_left₀ hp]
        rw [hl, map_mul, mul_comm ((σ : E →+* E) (p : E)), mul_assoc]
        refine mul_mem (uLocDual_intOE_map _ hx2) ?_
        have : (σ : E →+* E) (p : E) = (q : E) := by rw [hq]; rfl
        rw [this]; exact h2
      · exact mul_mem (uLocDual_intOE_map _ (hx1 i hi)) (h1 i hi)
  rw [e, Submodule.span_eq]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UlocOfTrivDisc
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem uloc_of_triv_disc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (_ : (T : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ levelVL σ J v S.Lb)
    (_ : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb),
    x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad S v hT x hx hy
  have hL : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := by
    unfold Formalism.UG.levelVL Formalism.UG.level at hx
    exact hx.2
  have hLi : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔
      ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
        latS (F := F) (v.adicCompletion F) (intV E v) S.Lb :=
    (stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)).inv_mem hL
  have hsub : latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    unfold Formalism.UG.latS
    apply Submodule.span_mono
    apply Set.image_mono
    intro z hz
    exact Submodule.subset_span (S.Lb_int z hz)
  have hfw : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    intro y hy'
    have h2 := Submodule.add_mem _ (hsub (hy y hy')) hy'
    rwa [sub_add_cancel] at h2
  have hbw : ∀ y, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) →
      y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    intro y hw
    have hd := hy _ hw
    have hi := hsub ((hLi _).1 hd)
    have key : y = (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y -
        ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
          ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
            ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) -
            (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) := by
      have hinv : ∀ u, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
          ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ u) = u := by
        intro u
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [Matrix.mulVec_sub, hinv, hinv, sub_sub_cancel]
    rw [key]
    exact Submodule.sub_mem _ hw hi
  rw [S.UlocAlt v hT, Subgroup.mem_inf]
  refine ⟨hx, ⟨?_, ?_⟩⟩
  · show ∀ y, y ∈ _ ↔ _
    exact fun y => ⟨hfw y, hbw y⟩
  · intro z
    have h0 := S.fT_L v hT
      (⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (z : Fin n → E ⊗[F] v.adicCompletion F), hfw z z.2⟩ - z)
      (by
        show (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (z : Fin n → E ⊗[F] v.adicCompletion F) -
          (z : Fin n → E ⊗[F] v.adicCompletion F) ∈ _
        exact hy z z.2)
    rw [map_sub, sub_eq_zero] at h0
    exact h0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmInverseHalfDifferentMulRelativeDifferent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped nonZeroDivisors Pointwise UpperHalfPlane

namespace GlobalTheory.Mem.PerField

theorem ideal_eq_of_pow_eq {A : Type} [CommRing A] [IsDedekindDomain A] {I J : Ideal A} {n : ℕ} (hn : n ≠ 0)
    (h : I ^ n = J ^ n) : I = J := by
  apply le_antisymm
  · rw [← Ideal.dvd_iff_le, ← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn, h]
  · rw [← Ideal.dvd_iff_le, ← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hn, h]

theorem exists_pow_eq_span {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ β : 𝓞 E, I ^ n = Ideal.span {β} := by
  classical
  by_cases hI : I = ⊥
  · exact ⟨1, one_ne_zero, 0, by simp [hI]⟩
  have hI' : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), Fintype.card_ne_zero, ?_⟩
  have h1 : ClassGroup.mk0 (⟨I, hI'⟩ ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (pow_mem hI' (Fintype.card (ClassGroup (𝓞 E))))).1 h1
  exact ⟨_, (Ideal.span_singleton_generator _).symm⟩

theorem span_root {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (f : E →+* L)
    {I : Ideal (𝓞 E)} {n : ℕ} (hn : n ≠ 0) {β : 𝓞 E} (h : I ^ n = Ideal.span {β}) {x : L}
    (hx : x ^ n = f β) :
    Submodule.span (𝓞 L) {x} = Submodule.span (𝓞 L) {y | ∃ c ∈ I, y = f (c : E)} := by
  have hi : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hx]
    exact (RingOfIntegers.isIntegral_coe β).map f.toIntAlgHom
  let x' : 𝓞 L := ⟨x, hi⟩
  let f' : 𝓞 E →+* 𝓞 L := RingOfIntegers.mapRingHom f
  have e : Ideal.span {x'} = I.map f' := by
    apply ideal_eq_of_pow_eq hn
    rw [← Ideal.map_pow, h, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
    congr 2
    exact RingOfIntegers.ext hx
  have e2 := congrArg (Submodule.map (Algebra.linearMap (𝓞 L) L)) e
  rw [Ideal.map, Ideal.span, Ideal.span, Submodule.map_span, Submodule.map_span, Set.image_singleton] at e2
  refine e2.trans ?_
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩

variable {R : Ranks} (H : Host R)

theorem cmInverseHalfDifferent_mul_relativeDifferent :
    H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have h1 : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  have hb : H.𝔟 ≠ ⊥ := by
    intro h0
    apply hd
    rw [h1, h0, Ideal.bot_mul]
  rw [h1, FractionalIdeal.coeIdeal_mul, Host.AA0, ← mul_assoc,
    inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hb), one_mul]

theorem ellLat_eq {LL : Type} [Field LL] [NumberField LL] (embE : H.E →+* LL) (g : R.GG) :
    ellLat H embE g = Submodule.span (𝓞 LL)
      {y | ∃ c ∈ (H.conj • H.𝔟 : Ideal (𝓞 H.E)), y = (embE.comp (H.sigmaOf g : H.E →+* H.E)) (c : H.E)} := by
  apply le_antisymm
  · refine Submodule.span_mono ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have : a * (b : H.E) ∈ H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) :=
      FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ hb)
    rw [cmInverseHalfDifferent_mul_relativeDifferent] at this
    obtain ⟨c, hc, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 this
    exact ⟨c, hc, by rw [← e]; rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    have : (c : H.E) ∈ H.AA0 * (differentIdeal (𝓞 H.K) (𝓞 H.E) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
      rw [cmInverseHalfDifferent_mul_relativeDifferent]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ hc
    refine FractionalIdeal.mul_induction_on
      (C := fun z => (embE.comp (H.sigmaOf g : H.E →+* H.E)) z ∈ ellLat H embE g) this ?_ ?_
    · intro a ha b hb
      obtain ⟨b', hb', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
      exact Submodule.subset_span ⟨a, ha, b', hb', rfl⟩
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy

theorem mem_baseLat (w : ℂ) : w ∈ baseLat H ↔ ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, H.ccK.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', H.ccK.add_mem hc hc', by simp⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, H.ccK.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem finrank_K : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)

theorem discr_K : NumberField.discr H.K = -(H.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_K H) H.hyp.2.1.squarefree
    (by have := H.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))

theorem exists_periodPair_baseLat : ∃ L : PeriodPair, ∀ z, z ∈ baseLat H ↔ z ∈ L.lattice := by
  let σ : H.K →+* ℂ := H.φ₀.comp H.K.val.toRingHom
  let I : (Ideal (𝓞 H.K))⁰ := ⟨H.ccK, mem_nonZeroDivisors_of_ne_zero H.ccK_ne_bot⟩
  obtain ⟨L, hL⟩ := QuadraticZeta.exists_periodPair (finrank_K H) (discr_K H) σ
    (FractionalIdeal.mk0 H.K I)
  refine ⟨L, fun z => ?_⟩
  rw [mem_baseLat, ← SetLike.mem_coe, hL]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : H.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, rfl⟩

theorem isIntegral_jLat : IsIntegral ℤ (jLat (baseLat H)) := by
  obtain ⟨L, hL⟩ := exists_periodPair_baseLat H
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [jLat, TaylorLogMetric.discr, hd.1, hd.2.1, g₂_cube_div_eq_modularJ ha h]
  refine isIntegral_modularJ_of_ringOfIntegers (finrank_K H) (H.φ₀.comp H.K.val.toRingHom) fun α x hx ↦ ?_
  have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
    rw [h, Submodule.mem_span_pair]
    simp [mul_right_inj' ha]
  rw [key, ← hL, mem_baseLat] at hx ⊢
  obtain ⟨c, hc, e⟩ := hx
  refine ⟨α * c, H.ccK.mul_mem_left α hc, ?_⟩
  rw [mul_left_comm, e]
  simp

theorem exists_fieldOK : ∀ (R : Ranks) (H : Host R) (M : IntermediateField ℚ ℂ), FiniteDimensional ℚ M → ∃ M' : IntermediateField ℚ ℂ, FiniteDimensional ℚ M' ∧ M ≤ M' ∧ ∀ (LL : Type) [Field LL] [NumberField LL] (emb : LL →+* ℂ) (embE : H.E →+* LL), emb.comp embE = H.φ₀ → (∀ x ∈ M', ∃ a, emb a = x) → FieldOK H emb embE := by
  intro R H M hM
  obtain ⟨n, hn, β, hβ⟩ := exists_pow_eq_span (H.conj • H.𝔟 : Ideal (𝓞 H.E))
  choose z hz using fun σ : H.E ≃ₐ[ℚ] H.E =>
    IsAlgClosed.exists_pow_nat_eq (H.φ₀ (σ (β : H.E))) (Nat.pos_of_ne_zero hn)
  let T : Set ℂ := insert (jLat (baseLat H)) (Set.range z)
  have : Finite T := (Set.finite_range z).insert _
  have hT : FiniteDimensional ℚ (IntermediateField.adjoin ℚ T) := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx ↦ ?_
    rcases hx with rfl | ⟨σ, rfl⟩
    · exact (isIntegral_jLat H).tower_top
    · refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
      rw [hz]
      exact (Algebra.IsIntegral.isIntegral (R := ℚ) (σ (β : H.E))).map H.φ₀.toRatAlgHom
  refine ⟨M ⊔ IntermediateField.adjoin ℚ T, inferInstance, le_sup_left, ?_⟩
  intro LL _ _ emb embE he hM'
  have hT' : ∀ x ∈ T, ∃ a, emb a = x := fun x hx =>
    hM' x ((le_sup_right : _ ≤ M ⊔ _) (IntermediateField.subset_adjoin ℚ T hx))
  refine ⟨hT' _ (Set.mem_insert _ _), fun g => ?_⟩
  obtain ⟨x, hx⟩ := hT' _ (Set.mem_insert_of_mem _ ⟨H.sigmaOf g, rfl⟩)
  refine ⟨x, ?_⟩
  rw [IsGen, ellLat_eq]
  refine span_root _ hn hβ ?_
  apply emb.injective
  rw [map_pow, hx, hz, ← he]
  rfl

end GlobalTheory.Mem.PerField
end
