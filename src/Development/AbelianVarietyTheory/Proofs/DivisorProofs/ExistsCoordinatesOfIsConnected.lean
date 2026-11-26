module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerIdealFinrankEqPowOfIdempotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePDivGroupLevelCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePDivGroupLevelCoordinates
set_option autoImplicit false

open GlobalTheory GlobalTheory.PDivGroup
open scoped TensorProduct

namespace GlobalTheory.PDiv

theorem exists_aug_dUnit_eq {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A] (w : Cot R A) :
    ∃ a : A, Coalgebra.counit (R := R) a = 0 ∧ dUnit (R := R) a = w := by
  obtain ⟨x, rfl⟩ := (augIdeal R A).toCotangent_surjective w
  exact ⟨x, x.2, AugCot.d_coe _ x⟩

theorem exists_aug_lift_dUnit_eq {R A C : Type*} [CommRing R] [CommRing A] [CommRing C] [Bialgebra R A]
    [Bialgebra R C] {f : C →ₐc[R] A} (hf : Function.Surjective f) (a : A)
    (ha : Coalgebra.counit (R := R) a = 0) (w : Cot R C) (hw : cotMap f w = dUnit (R := R) a) :
    ∃ c : C, Coalgebra.counit (R := R) c = 0 ∧ dUnit (R := R) c = w ∧ f c = a := by
  obtain ⟨y, hy, rfl⟩ := exists_aug_dUnit_eq w
  have h1 : dUnit (R := R) (f y - a) = 0 := by
    rw [dUnit, map_sub, sub_eq_zero]
    exact (cotMap_d f y).symm.trans hw
  have h2 : Bialgebra.counitAlgHom R A (f y - a) = 0 := by simp [hy, ha]
  rw [dUnit, AugCot.d_eq_zero_iff, h2, map_zero, sub_zero] at h1
  have h3 : f y - a ∈ Ideal.map (f : C →ₐ[R] A) (augIdeal R C ^ 2) := by
    rw [Ideal.map_pow]
    have := kerIdeal_of_surjective hf
    rw [kerIdeal] at this
    rw [this]
    exact h1
  obtain ⟨z, hz, hfz⟩ := (Ideal.mem_map_iff_of_surjective (f : C →ₐ[R] A) hf).1 h3
  have hz0 : Bialgebra.counitAlgHom R C z = 0 := Ideal.pow_le_self two_ne_zero hz
  have hz1 : Coalgebra.counit (R := R) z = 0 := hz0
  refine ⟨y - z, by rw [map_sub, hy, hz1, sub_zero], ?_, ?_⟩
  · rw [dUnit, map_sub, (AugCot.d_eq_zero_iff _ z).2 (by rw [hz0, map_zero, sub_zero]; exact hz), sub_zero]
  · have : f z = f y - a := hfz
    rw [map_sub, this, sub_sub_cancel]

theorem exists_compatible_dUnit_eq {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (w : G.omega) :
    ∃ x : ∀ n, G.A n, (∀ n, Coalgebra.counit (R := O) (x n) = 0) ∧ (∀ n, G.res n (x (n + 1)) = x n) ∧
      ∀ n, dUnit (R := O) (x n) = w.1 n := by
  obtain ⟨a, ha⟩ := exists_aug_dUnit_eq (w.1 0)
  have step : ∀ (n : ℕ) (a : {a : G.A n // Coalgebra.counit (R := O) a = 0 ∧ dUnit (R := O) a = w.1 n}),
      ∃ c : {a : G.A (n + 1) // Coalgebra.counit (R := O) a = 0 ∧ dUnit (R := O) a = w.1 (n + 1)},
        G.res n c.1 = a.1 := fun n a => by
    obtain ⟨c, h1, h2, h3⟩ := exists_aug_lift_dUnit_eq (G.res_surjective n) a.1 a.2.1 (w.1 (n + 1))
      ((w.2 n).trans a.2.2.symm)
    exact ⟨⟨c, h1, h2⟩, h3⟩
  choose s hs using step
  let x : ∀ n, {a : G.A n // Coalgebra.counit (R := O) a = 0 ∧ dUnit (R := O) a = w.1 n} :=
    fun n => Nat.rec ⟨a, ha⟩ s n
  exact ⟨fun n => (x n).1, fun n => (x n).2.1, fun n => hs n (x n), fun n => (x n).2.2⟩

theorem exists_compatible_coordinates (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) (G : PDivGroup p O) :
    ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n), (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧
      (∀ n i, G.res n (x (n + 1) i) = x n i) ∧
      (∀ n, Submodule.span O (Set.range fun i => PDiv.dUnit (R := O) (x n i)) = ⊤) ∧
      ∀ n, ∃ l : Fin d → (PDiv.Cot O (G.A n) →ₗ[O] O ⧸ Ideal.span {(p : O) ^ n}),
        ∀ i j, l i (PDiv.dUnit (R := O) (x n j)) = if i = j then 1 else 0 := by
  have : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨h1, h2⟩ := omega_finite_projective p C v O hv G
  have : Module.Free O G.omega := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis O G.omega
  choose x hx0 hx1 hx2 using fun i => exists_compatible_dUnit_eq G (b i)
  refine ⟨_, fun n i => x i n, fun n i => hx0 i n, fun n i => hx1 i n, fun n => ?_, fun n => ?_⟩
  · have : (fun i => dUnit (R := O) (x i n)) = G.omegaLevel n ∘ b := funext fun i => hx2 i n
    rw [this, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.2 (G.omegaLevel_surjective n)]
  · have hker : ∀ i, LinearMap.ker (G.omegaLevel n) ≤
        LinearMap.ker ((Ideal.span {(p : O) ^ n}).mkQ ∘ₗ b.coord i) := fun i w hw => by
      obtain ⟨u, rfl⟩ := (G.omega_val_eq_zero_iff n w).1 hw
      rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    refine ⟨fun i => ((LinearMap.ker (G.omegaLevel n)).liftQ _ (hker i)) ∘ₗ
      ((G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)).symm.toLinearMap, fun i j => ?_⟩
    have h : ((G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)).symm (dUnit (R := O) (x j n)) =
        Submodule.Quotient.mk (b j) := by
      rw [LinearEquiv.symm_apply_eq, hx2]
      rfl
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply, LinearMap.comp_apply,
      Module.Basis.coord_apply, b.repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]

end GlobalTheory.PDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePDivGroupLevelCoordinatesStatement
open GlobalTheory GlobalTheory.PDivGroup
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_pDivGroup_level_coordinates : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n), (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n, Submodule.span O (Set.range fun i => PDiv.dUnit (R := O) (x n i)) = ⊤) ∧ ∀ n, ∃ l : Fin d → (PDiv.Cot O (G.A n) →ₗ[O] O ⧸ Ideal.span {(p : O) ^ n}), ∀ i j, l i (PDiv.dUnit (R := O) (x n j)) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.PDiv.exists_compatible_coordinates | exact GlobalTheory.PDiv.exists_compatible_coordinates | (intros; apply GlobalTheory.PDiv.exists_compatible_coordinates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalSurjectiveOfCotangentSpanTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanSubMemSq
namespace GlobalTheory.PowerIdealSurjectivity

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

lemma exists_span_sub_mem_sq (ε : A →ₐ[O] O) {d : ℕ} (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (hs : Submodule.span O (Set.range fun i ↦ GlobalTheory.AugCot.d ε (x i)) = ⊤) {c : A}
    (hc : c ∈ RingHom.ker ε) :
    ∃ m ∈ Submodule.span O (Set.range x), m ∈ RingHom.ker ε ∧ c - m ∈ RingHom.ker ε ^ 2 := by
  classical

  let J : Submodule O A := (RingHom.ker ε ^ 2).restrictScalars O
  let D : A →ₗ[O] A ⧸ J := J.mkQ ∘ₗ (LinearMap.id - (Algebra.linearMap O A) ∘ₗ ε.toLinearMap)
  have hDa : ∀ a, D a = Submodule.Quotient.mk (a - algebraMap O A (ε a)) := fun a => rfl
  have hmemI : ∀ a, a - algebraMap O A (ε a) ∈ RingHom.ker ε := fun a =>
    RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)
  have hD : ∀ a b : A, D (a * b) = ε a • D b + ε b • D a := by
    intro a b
    rw [hDa, hDa, hDa, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, Submodule.restrictScalars_mem]
    have key : a * b - algebraMap O A (ε (a * b)) -
        (ε a • (b - algebraMap O A (ε b)) + ε b • (a - algebraMap O A (ε a))) =
        (a - algebraMap O A (ε a)) * (b - algebraMap O A (ε b)) := by
      rw [map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    rw [key, pow_two]
    exact Ideal.mul_mem_mul (hmemI a) (hmemI b)
  have hdc : GlobalTheory.AugCot.d ε c ∈ Submodule.span O (Set.range fun i => GlobalTheory.AugCot.d ε (x i)) := by
    rw [hs]
    exact Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hdc
  have hε0 : ε (∑ i, r i • x i) = 0 := by simp [map_sum, hx]
  refine ⟨∑ i, r i • x i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩),
    RingHom.mem_ker.mpr hε0, ?_⟩
  have hdm : GlobalTheory.AugCot.d ε (∑ i, r i • x i) = GlobalTheory.AugCot.d ε c := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hr, map_sum]
    simp only [map_smul]
  have h := congrArg (GlobalTheory.AugCot.lift ε D hD) hdm
  rw [GlobalTheory.AugCot.lift_d, GlobalTheory.AugCot.lift_d, hDa, hDa, Submodule.Quotient.eq,
    Submodule.restrictScalars_mem] at h
  have hεc : ε c = 0 := RingHom.mem_ker.mp hc
  rw [hε0, hεc, map_zero, sub_zero, sub_zero] at h
  rw [← neg_sub]
  exact (RingHom.ker ε ^ 2).neg_mem h

lemma exists_sub_mem_pow (B : Subalgebra O A) (I : Ideal A)
    (h0 : ∀ a, ∃ b ∈ B, a - b ∈ I) (h1 : ∀ c ∈ I, ∃ m ∈ B, m ∈ I ∧ c - m ∈ I ^ 2) (n : ℕ) (a : A) :
    ∃ b ∈ B, a - b ∈ I ^ (n + 1) := by

  have step : ∀ k : ℕ, ∀ c ∈ I ^ (k + 1), ∃ m ∈ B, m ∈ I ^ (k + 1) ∧ c - m ∈ I ^ (k + 2) := by
    intro k
    induction k with
    | zero =>
      intro c hc
      rw [zero_add, pow_one] at hc
      obtain ⟨m, hmB, hmI, hcm⟩ := h1 c hc
      exact ⟨m, hmB, by rwa [zero_add, pow_one], hcm⟩
    | succ k ih =>
      intro c hc
      have hc' : c ∈ I ^ (k + 1) * I := by rw [← pow_succ]; exact hc
      refine Submodule.mul_induction_on
        (C := fun c => ∃ m ∈ B, m ∈ I ^ (k + 1 + 1) ∧ c - m ∈ I ^ (k + 1 + 2)) hc' ?_ ?_
      · intro y hy z hz
        obtain ⟨my, hmyB, hmyI, hy'⟩ := ih y hy
        obtain ⟨mz, hmzB, hmzI, hz'⟩ := h1 z hz
        refine ⟨my * mz, B.mul_mem hmyB hmzB, ?_, ?_⟩
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hmyI hmzI
        · have e : y * z - my * mz = y * (z - mz) + (y - my) * mz := by ring
          rw [e]
          refine Ideal.add_mem _ ?_ ?_
          · have := Ideal.mul_mem_mul hy hz'
            rwa [← pow_add] at this
          · have := Ideal.mul_mem_mul hy' hmzI
            rwa [← pow_succ] at this
      · rintro y z ⟨my, hmyB, hmyI, hy'⟩ ⟨mz, hmzB, hmzI, hz'⟩
        refine ⟨my + mz, B.add_mem hmyB hmzB, Ideal.add_mem _ hmyI hmzI, ?_⟩
        have e : y + z - (my + mz) = (y - my) + (z - mz) := by ring
        rw [e]
        exact Ideal.add_mem _ hy' hz'
  induction n with
  | zero =>
    obtain ⟨b, hb, hab⟩ := h0 a
    exact ⟨b, hb, by rwa [zero_add, pow_one]⟩
  | succ n ih =>
    obtain ⟨b, hb, hab⟩ := ih
    obtain ⟨m, hmB, -, hm⟩ := step n (a - b) hab
    refine ⟨b + m, B.add_mem hb hmB, ?_⟩
    have e : a - (b + m) = a - b - m := by ring
    rw [e]
    exact hm

theorem aeval_surjective (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Module.Finite O A] [IsLocalRing A] (q : O) (hq : q ∈ IsLocalRing.maximalIdeal O)
    (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (hN : ∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N)
    (hs : Submodule.span O (Set.range fun i ↦ GlobalTheory.AugCot.d ε (x i)) = ⊤) :
    Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O → A) := by
  classical
  let B : Subalgebra O A := Algebra.adjoin O (Set.range x)
  have h0 : ∀ a, ∃ b ∈ B, a - b ∈ RingHom.ker ε := fun a =>
    ⟨algebraMap O A (ε a), B.algebraMap_mem _,
      RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)⟩
  have h1 : ∀ c ∈ RingHom.ker ε, ∃ m ∈ B, m ∈ RingHom.ker ε ∧ c - m ∈ RingHom.ker ε ^ 2 := by
    intro c hc
    obtain ⟨m, hm, hmI, hcm⟩ := exists_span_sub_mem_sq ε x hx hs hc
    exact ⟨m, Algebra.span_le_adjoin O _ hm, hmI, hcm⟩

  let φ : A →ₗ[O] A := LinearMap.id - (Algebra.linearMap O A) ∘ₗ ε.toLinearMap
  have hφ : ∀ a, φ a = a - algebraMap O A (ε a) := fun a => rfl
  have hfg : (RingHom.ker ε).FG := by
    apply Submodule.FG.of_restrictScalars O
    have heq : (RingHom.ker ε).restrictScalars O = LinearMap.range φ := by
      ext c
      rw [Submodule.restrictScalars_mem, LinearMap.mem_range]
      constructor
      · intro hc
        refine ⟨c, ?_⟩
        rw [hφ, show ε c = 0 from RingHom.mem_ker.mp hc, map_zero, sub_zero]
      · rintro ⟨a, rfl⟩
        rw [hφ]
        exact RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)
    rw [heq, ← Submodule.map_top]
    exact (Module.Finite.fg_top (R := O) (M := A)).map φ

  have hker_ne : RingHom.ker ε ≠ ⊤ := RingHom.ker_ne_top ε
  have hle_span : RingHom.ker ε ≤ Ideal.span (Set.range x) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := RingHom.ker ε) hfg ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hker_ne
    · intro c hc
      obtain ⟨m, hm, -, hcm⟩ := exists_span_sub_mem_sq ε x hx hs hc
      have hm' : m ∈ Ideal.span (Set.range x) := Submodule.span_le_restrictScalars O A _ hm
      rw [pow_two, ← smul_eq_mul] at hcm
      rw [show c = m + (c - m) by ring]
      exact Submodule.add_mem_sup hm' hcm

  have hrad : Ideal.span (Set.range x) ≤ (Ideal.span {algebraMap O A q}).radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨N, hNi⟩ := hN i
    exact ⟨N, Ideal.mem_span_singleton.mpr hNi⟩
  have hfgx : (Ideal.span (Set.range x)).FG :=
    ⟨Finset.univ.image x, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  obtain ⟨K, hK⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfgx

  have htop : (⊤ : Submodule O A) ≤ Subalgebra.toSubmodule B := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
      Module.Finite.fg_top ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro a _
      obtain ⟨b, hb, hab⟩ := exists_sub_mem_pow B (RingHom.ker ε) h0 h1 K a
      have h2 : a - b ∈ Ideal.span (Set.range x) ^ K :=
        Ideal.pow_right_mono hle_span K (Ideal.pow_le_pow_right (Nat.le_succ K) hab)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hK h2)
      have h3 : a - b ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O A) := by
        rw [← hy, mul_comm, ← Algebra.smul_def]
        exact Submodule.smul_mem_smul hq Submodule.mem_top
      rw [show a = b + (a - b) by ring]
      exact Submodule.add_mem_sup hb h3
  intro a
  have ha : a ∈ B := htop Submodule.mem_top
  rw [show B = (MvPolynomial.aeval x).range from Algebra.adjoin_range_eq_range_aeval O x] at ha
  obtain ⟨p, hp⟩ := ha
  exact ⟨p, hp⟩

end GlobalTheory.PowerIdealSurjectivity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalSurjectiveOfCotangentSpanTop
open GlobalTheory
open scoped Pointwise

namespace GlobalTheory.NakAug

theorem surj : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by
  first
  | exact @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | (apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective ..)

end GlobalTheory.NakAug
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalSurjectiveOfCotangentSpanTopStatement
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_surjective_of_cotangent_span_top : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by
  first | exact @GlobalTheory.NakAug.surj | exact GlobalTheory.NakAug.surj | (intros; apply GlobalTheory.NakAug.surj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationsQuotientBialgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationsQuotientBialgebra
open scoped TensorProduct

namespace GlobalTheory

theorem quotient_base_change_invariant_derivations :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] (I : Ideal O) (d : ℕ) (l : Fin d → (A →ₗ[O] O ⧸ I)), (∀ i a b, l i (a * b) = Coalgebra.counit (R := O) a • l i b + Coalgebra.counit (R := O) b • l i a) → ∃ D : Fin d → Derivation (O ⧸ I) ((O ⧸ I) ⊗[O] A) ((O ⧸ I) ⊗[O] A), ∀ i a, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] A) (D i (1 ⊗ₜ a)) = l i a := by
  intro O A _ _ _ I d l hl
  set S := O ⧸ I
  set B := S ⊗[O] A
  let ε := Bialgebra.counitAlgHom S B
  let Δ := Bialgebra.comulAlgHom S B
  have hεt : ∀ (s : S) (a : A), ε (s ⊗ₜ a) = Coalgebra.counit (R := O) a • s := by
    intro s a
    show Coalgebra.counit (R := S) (s ⊗ₜ[O] a) = _
    rw [TensorProduct.counit_tmul]
    rfl
  have hε : (∀ b : B, TensorProduct.lid S B (LinearMap.rTensor B ε.toLinearMap (Δ b)) = b) ∧
      (∀ b : B, TensorProduct.rid S B (LinearMap.lTensor B ε.toLinearMap (Δ b)) = b) := by
    constructor
    · intro b
      have := Coalgebra.rTensor_counit_comul (R := S) b
      show TensorProduct.lid S B (LinearMap.rTensor B Coalgebra.counit (Coalgebra.comul b)) = b
      rw [this]; simp
    · intro b
      have := Coalgebra.lTensor_counit_comul (R := S) b
      show TensorProduct.rid S B (LinearMap.lTensor B Coalgebra.counit (Coalgebra.comul b)) = b
      rw [this]; simp
  have key : ∀ i, ∃ D : Derivation S B B, ∀ b, ε (D b) = LinearMap.liftBaseChange S (l i) b := by
    intro i
    refine invariant_derivation_exists S B ε Δ hε (LinearMap.liftBaseChange S (l i)) ?_
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul t c =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hεt, hεt]
        rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
          LinearMap.liftBaseChange_tmul, hl]
        simp only [smul_eq_mul, smul_add, Algebra.smul_def]
        ring
      | add y₁ y₂ ih₁ ih₂ =>
        rw [mul_add, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
        ring
    | add x₁ x₂ ih₁ ih₂ =>
      rw [add_mul, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
      ring
  choose D hD using key
  refine ⟨D, fun i a => ?_⟩
  rw [hD, LinearMap.liftBaseChange_tmul, one_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationsQuotientBialgebraStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_derivations_quotient_bialgebra : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] (I : Ideal O) (d : ℕ) (l : Fin d → (A →ₗ[O] O ⧸ I)), (∀ i a b, l i (a * b) = Coalgebra.counit (R := O) a • l i b + Coalgebra.counit (R := O) b • l i a) → ∃ D : Fin d → Derivation (O ⧸ I) ((O ⧸ I) ⊗[O] A) ((O ⧸ I) ⊗[O] A), ∀ i a, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] A) (D i (1 ⊗ₜ a)) = l i a := by
  first | exact @GlobalTheory.quotient_base_change_invariant_derivations | exact GlobalTheory.quotient_base_change_invariant_derivations | (intros; apply GlobalTheory.quotient_base_change_invariant_derivations <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPowNatCastDvdFiniteIntegersAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPowNatCastDvdFiniteIntegersAlgebra
namespace GlobalTheory

open IsLocalRing

theorem maxIdeal_pow_dvd_natCast_of_integers :
    ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type)
      [CommRing O] [Algebra O C], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A]
      [Module.Finite O A] [IsLocalRing A] (a : A), a ∈ IsLocalRing.maximalIdeal A →
      ∃ N : ℕ, (p : A) ∣ a ^ N := by
  intro p hp C _ _ v O _ _ hv A _ _ _ _ a ha

  set J : Ideal O := (maximalIdeal A).comap (algebraMap O A) with hJdef
  haveI : J.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal A)

  have hJp : ∀ c ∈ J, ∃ k : ℕ, (p : O) ∣ c ^ k := by
    intro c hc
    have hlt : v (algebraMap O C c) < 1 := by
      refine lt_of_le_of_ne (hv.map_le_one c) ?_
      intro h1
      have hu : IsUnit c := hv.isUnit_of_one' h1
      have : IsUnit (algebraMap O A c) := hu.map _
      exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ hc this)
    have hp0 : 0 < v (algebraMap O C (p : O)) := by
      rw [map_natCast]
      exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 hp)
    obtain ⟨k, hk⟩ := NNReal.exists_pow_lt_of_lt_one hp0 hlt
    refine ⟨k, hv.dvd_of_le ?_⟩
    rw [map_pow, map_pow]
    exact hk.le

  have hI : J.map (algebraMap O A) ≤ (Ideal.span {(p : A)}).radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    obtain ⟨k, d, hd⟩ := hJp c hc
    refine ⟨k, ?_⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨algebraMap O A d, ?_⟩
    rw [← map_pow, hd, map_mul, map_natCast]

  have ha' : a ∈ (J.map (algebraMap O A)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQ, hQp⟩
    have hle : J ≤ Q.comap (algebraMap O A) := Ideal.map_le_iff_le_comap.1 hQ
    have hQc : Q.comap (algebraMap O A) = J :=
      ((inferInstance : J.IsMaximal).eq_of_le (Ideal.IsPrime.comap (algebraMap O A)).ne_top hle).symm
    haveI : (Q.comap (algebraMap O A)).IsMaximal := by rw [hQc]; infer_instance
    haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (algebraMap O A) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) Q this
    rw [IsLocalRing.eq_maximalIdeal this]
    exact ha
  have h2 : a ∈ (Ideal.span {(p : A)}).radical := by
    have := Ideal.radical_mono hI ha'
    rwa [Ideal.radical_idem] at this
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, Ideal.mem_span_singleton.1 hN⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPowNatCastDvdFiniteIntegersAlgebraStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalIdeal_pow_natCast_dvd_finite_integers_algebra : ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (a : A), a ∈ IsLocalRing.maximalIdeal A → ∃ N : ℕ, (p : A) ∣ a ^ N := by
  first | exact @GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers | exact GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers | (intros; apply GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAnnihilatedOfAevalMemKerPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAnnihilatedOfAevalMemKerPow
open scoped TensorProduct

namespace GlobalTheory.TriangularityLowCoeff

open MvPolynomial

noncomputable def iterDer {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}
    (D : Fin d → Derivation R A A) : List (Fin d) → A →ₗ[R] A
  | [] => LinearMap.id
  | i :: L => (iterDer D L) ∘ₗ (D i).toLinearMap

noncomputable def expOf {d : ℕ} (L : List (Fin d)) : Fin d →₀ ℕ :=
  Multiset.toFinsupp (L : Multiset (Fin d))

noncomputable def fac {d : ℕ} : List (Fin d) → (Fin d →₀ ℕ) → ℕ
  | [], _ => 1
  | i :: L, m => ((m + expOf L) i + 1) * fac L m

theorem expOf_cons {d : ℕ} (i : Fin d) (L : List (Fin d)) :
    expOf (i :: L) = Finsupp.single i 1 + expOf L := by
  rw [expOf, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton, expOf]

theorem degree_expOf {d : ℕ} (L : List (Fin d)) : (expOf L).degree = L.length := by
  induction L with
  | nil => simp [expOf]
  | cons i L ih => rw [expOf_cons, map_add (f := _), ih, Finsupp.degree_single]; simp; omega

theorem expOf_apply_le {d : ℕ} (L : List (Fin d)) (i : Fin d) : expOf L i ≤ L.length := by
  rw [expOf, Multiset.toFinsupp_apply, Multiset.coe_count]
  exact List.count_le_length

theorem expOf_toList {d : ℕ} (α : Fin d →₀ ℕ) : expOf (Finsupp.toMultiset α).toList = α := by
  rw [expOf, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp]

theorem fac_dvd {d : ℕ} (L : List (Fin d)) : fac L 0 ∣ (L.length).factorial ^ L.length := by
  induction L with
  | nil => simp [fac]
  | cons i L ih =>
    simp only [fac, zero_add, List.length_cons]
    rw [pow_succ']
    refine mul_dvd_mul (Nat.dvd_factorial (by omega) (by have := expOf_apply_le L i; omega)) ?_
    exact ih.trans (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (by omega)) _)

theorem der_mem_pow {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (J : Ideal A) : ∀ (k : ℕ) (x : A), x ∈ J ^ (k + 1) → D x ∈ J ^ k
  | 0, x, _ => by simp
  | k + 1, x, hx => by
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on (C := fun x => D x ∈ J ^ (k + 1)) hx ?_ ?_
    · intro a ha b hb
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hb)
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha (der_mem_pow D J k b hb)
    · intro x y hx hy
      rw [map_add (f := _)]
      exact Ideal.add_mem _ hx hy

theorem iterDer_mem {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}
    (D : Fin d → Derivation R A A) (J : Ideal A) :
    ∀ (L : List (Fin d)) (m : ℕ) (x : A), x ∈ J ^ (L.length + m) → iterDer D L x ∈ J ^ m
  | [], m, x, hx => by simpa [iterDer] using hx
  | i :: L, m, x, hx => by
    show iterDer D L (D i x) ∈ J ^ m
    apply iterDer_mem D J L m
    apply der_mem_pow (D i) J
    have e : L.length + m + 1 = (i :: L).length + m := by simp; omega
    rw [e]; exact hx

theorem der_aeval {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (D : Derivation R B B) (y : Fin d → B) (Q : MvPolynomial (Fin d) R) :
    D (aeval y Q) = ∑ j, aeval y (pderiv j Q) * D (y j) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    rw [map_mul, aeval_X, D.leibniz, hp, smul_eq_mul, smul_eq_mul]
    simp only [pderiv_mul, pderiv_X, map_add (f := _), map_mul, aeval_X, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_apply, hj]
      · simp

theorem coeff_iterPD {R : Type} [CommRing R] {d : ℕ} :
    ∀ (L : List (Fin d)) (m : Fin d →₀ ℕ) (Q : MvPolynomial (Fin d) R),
      AddMonoidAlgebra.coeff (iterDer (fun i => pderiv i) L Q) m = AddMonoidAlgebra.coeff Q (m + expOf L) * (fac L m : R)
  | [], m, Q => by simp [iterDer, expOf, fac]
  | i :: L, m, Q => by
    show AddMonoidAlgebra.coeff (iterDer (fun i => pderiv i) L (pderiv i Q)) m = _
    rw [coeff_iterPD L m, coeff_pderiv, fac, expOf_cons]
    have e : m + expOf L + Finsupp.single i 1 = m + (Finsupp.single i 1 + expOf L) := by abel
    rw [e]; push_cast; ring

theorem aeval_mem_pow {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (hy : ∀ i, ε (y i) = 0) (n : ℕ) (Q : MvPolynomial (Fin d) R)
    (hQ : Q ∈ idealOfVars (Fin d) R ^ n) : aeval y Q ∈ RingHom.ker ε ^ n := by
  have h1 : Ideal.map (aeval y) (idealOfVars (Fin d) R) ≤ RingHom.ker ε := by
    rw [idealOfVars, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp [RingHom.mem_ker, hy]
  have h2 := Ideal.mem_map_of_mem (aeval y) hQ
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

theorem eval_aeval {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (hy : ∀ i, ε (y i) = 0) (Q : MvPolynomial (Fin d) R) :
    ε (aeval y Q) = AddMonoidAlgebra.coeff Q 0 := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hy, coeff_mul_X']

theorem eval_iterDer_aeval {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B)
    (hy : ∀ i, ε (y i) = 0) (hD : ∀ i j, ε (D i (y j)) = if i = j then 1 else 0) :
    ∀ (L : List (Fin d)) (Q : MvPolynomial (Fin d) R), Q ∈ idealOfVars (Fin d) R ^ L.length →
      ε (iterDer D L (aeval y Q)) = AddMonoidAlgebra.coeff (iterDer (fun i => pderiv i) L Q) 0
  | [], Q, _ => by simpa [iterDer] using eval_aeval ε y hy Q
  | i :: L, Q, hQ => by
    show ε (iterDer D L (D i (aeval y Q))) = AddMonoidAlgebra.coeff (iterDer (fun i => pderiv i) L (pderiv i Q)) 0
    have hP : ∀ j, pderiv j Q ∈ idealOfVars (Fin d) R ^ L.length := fun j =>
      der_mem_pow (pderiv j) _ L.length Q (by simpa using hQ)
    have key : ∀ j, ε (iterDer D L (aeval y (pderiv j Q) * D i (y j))) =
        ε (D i (y j)) * AddMonoidAlgebra.coeff (iterDer (fun i => pderiv i) L (pderiv j Q)) 0 := by
      intro j
      set x := aeval y (pderiv j Q)
      set u := D i (y j)
      have split : x * u = ε u • x + x * (u - algebraMap R B (ε u)) := by
        rw [Algebra.smul_def]; ring
      have hmem : x * (u - algebraMap R B (ε u)) ∈ RingHom.ker ε ^ (L.length + 1) := by
        rw [pow_succ]
        refine Ideal.mul_mem_mul (aeval_mem_pow ε y hy _ _ (hP j)) ?_
        simp [RingHom.mem_ker]
      have h0 : ε (iterDer D L (x * (u - algebraMap R B (ε u)))) = 0 := by
        have := iterDer_mem D (RingHom.ker ε) L 1 _ hmem
        rw [pow_one, RingHom.mem_ker] at this
        exact this
      rw [split, map_add (f := _), map_add (f := _), h0, add_zero, map_smul, map_smul, smul_eq_mul,
        eval_iterDer_aeval ε y D hy hD L (pderiv j Q) (hP j)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [der_aeval, map_sum, map_sum]
    simp only [key, hD, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem exists_mul_coeff_eq_zero (d N : ℕ) : ∃ K : ℕ, 0 < K ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B), (∀ i, ε (y i) = 0) →
    (∀ i j, ε (D i (y j)) = if i = j then 1 else 0) → ∀ P : MvPolynomial (Fin d) R,
    (∀ α : Fin d →₀ ℕ, N ≤ α.degree → AddMonoidAlgebra.coeff P α = 0) →
    MvPolynomial.aeval y P ∈ RingHom.ker ε ^ N → ∀ α, (K : R) * AddMonoidAlgebra.coeff P α = 0 := by
  refine ⟨(N.factorial ^ N) ^ N, by positivity, ?_⟩
  intro R B _ _ _ ε y D hy hD P hhi hP
  set c : ℕ := N.factorial ^ N with hc
  have claim : ∀ k, k ≤ N → ∀ α : Fin d →₀ ℕ, α.degree < k → ((c ^ k : ℕ) : R) * AddMonoidAlgebra.coeff P α = 0 := by
    intro k
    induction k with
    | zero => intro _ α h; omega
    | succ k ih =>
      intro hk α hα
      rcases Nat.lt_or_ge α.degree k with h | h
      · rw [pow_succ, Nat.cast_mul, mul_comm ((c ^ k : ℕ) : R), mul_assoc, ih (by omega) α h, mul_zero]
      · have hdeg : α.degree = k := by omega
        set L := (Finsupp.toMultiset α).toList
        have hL : expOf L = α := expOf_toList α
        have hlen : L.length = k := by rw [← degree_expOf, hL, hdeg]
        set P' := C ((c ^ k : ℕ) : R) * P
        have hP'1 : P' ∈ idealOfVars (Fin d) R ^ L.length := by
          rw [mem_pow_idealOfVars_iff', hlen]
          intro β hβ
          rw [coeff_C_mul, ih (by omega) β hβ]
        have hP'2 : aeval y P' ∈ RingHom.ker ε ^ (L.length + 1) := by
          rw [map_mul]
          refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) hP)
        have e1 := eval_iterDer_aeval ε y D hy hD L P' hP'1
        have e2 := iterDer_mem D (RingHom.ker ε) L 1 _ hP'2
        rw [pow_one, RingHom.mem_ker, e1, coeff_iterPD, zero_add, hL, coeff_C_mul] at e2
        obtain ⟨g, hg⟩ : fac L 0 ∣ c := by
          refine (fac_dvd L).trans ?_
          rw [hc, hlen]
          exact (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (by omega)) k).trans
            (pow_dvd_pow _ (by omega))
        have hg' : (c : R) = (fac L 0 : R) * (g : R) := by rw [hg, Nat.cast_mul]
        push_cast at e2
        calc ((c ^ (k + 1) : ℕ) : R) * AddMonoidAlgebra.coeff P α = (c : R) ^ k * (c : R) * AddMonoidAlgebra.coeff P α := by
              push_cast; ring
          _ = (c : R) ^ k * ((fac L 0 : R) * (g : R)) * AddMonoidAlgebra.coeff P α := by rw [← hg']
          _ = ((c : R) ^ k * AddMonoidAlgebra.coeff P α * (fac L 0 : R)) * g := by ring
          _ = 0 := by rw [e2, zero_mul]
  intro α
  rcases Nat.lt_or_ge α.degree N with h | h
  · exact claim N le_rfl α h
  · rw [hhi α h, mul_zero]

end GlobalTheory.TriangularityLowCoeff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAnnihilatedOfAevalMemKerPowStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_annihilated_of_aeval_mem_ker_pow : ∀ (d N : ℕ), ∃ K : ℕ, 0 < K ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B), (∀ i, ε (y i) = 0) → (∀ i j, ε (D i (y j)) = if i = j then 1 else 0) → ∀ P : MvPolynomial (Fin d) R, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → AddMonoidAlgebra.coeff P α = 0) → MvPolynomial.aeval y P ∈ RingHom.ker ε ^ N → ∀ α, (K : R) * AddMonoidAlgebra.coeff P α = 0 := by
  first | exact @GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero | exact GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero | (intros; apply GlobalTheory.TriangularityLowCoeff.exists_mul_coeff_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
namespace GlobalTheory.FinProjComplete

theorem mem_smul_top_pi {R ι : Type*} [CommRing R] [Finite ι] (J : Ideal R) (x : ι → R) :
    x ∈ (J • ⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := fun _ : ι => R) i) h
    rw [Submodule.map_smul''] at this
    simpa using Submodule.smul_mono le_rfl le_top this
  · have hx : x = ∑ i, x i • Pi.single i (1 : R) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial

theorem isAdicComplete_pi {R ι : Type*} [CommRing R] [Finite ι] (J : Ideal R)
    [IsAdicComplete J R] : IsAdicComplete J (ι → R) := by
  have hR : ∀ (x : R) n, x ≡ 0 [SMOD (J ^ n • ⊤ : Submodule R R)] ↔ x ∈ J ^ n := by
    intro x n; simp [SModEq.sub_mem]
  suffices h : IsHausdorff J (ι → R) ∧ IsPrecomplete J (ι → R) from
    have := h.1; have := h.2; {}
  refine ⟨⟨fun x hx => funext fun j => IsHausdorff.haus' (I := J) (x j) fun n => ?_⟩,
    ⟨fun u hu => ?_⟩⟩
  · rw [hR]
    have := SModEq.sub_mem.1 (hx n)
    simpa using (mem_smul_top_pi (J ^ n) _).1 this j
  · have h1 : ∀ i, ∃ L : R, ∀ k, u k i ≡ L [SMOD (J ^ k • ⊤ : Submodule R R)] :=
      fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using (mem_smul_top_pi (J ^ a) _).1 (SModEq.sub_mem.1 (hu hab)) i
    choose L hL using h1
    refine ⟨L, fun k => SModEq.sub_mem.2 ((mem_smul_top_pi (J ^ k) _).2 fun i => ?_)⟩
    have := SModEq.sub_mem.1 (hL i k)
    rw [smul_eq_mul, Ideal.mul_top] at this
    simpa using this

theorem map_mem_pow_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (f : M →ₗ[R] N) {x y : M} {n : ℕ}
    (h : x ≡ y [SMOD (J ^ n • ⊤ : Submodule R M)]) :
    f x ≡ f y [SMOD (J ^ n • ⊤ : Submodule R N)] := by
  rw [SModEq.sub_mem] at h ⊢
  have := Submodule.mem_map_of_mem (f := f) h
  rw [Submodule.map_smul'', map_sub] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem isAdicComplete_of_retract {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (π : N →ₗ[R] M) (s : M →ₗ[R] N)
    (hs : ∀ x, π (s x) = x) [IsAdicComplete J N] : IsAdicComplete J M := by
  suffices h : IsHausdorff J M ∧ IsPrecomplete J M from
    have := h.1; have := h.2; {}
  refine ⟨⟨fun x hx => ?_⟩, ⟨fun u hu => ?_⟩⟩
  · have : s x = 0 := IsHausdorff.haus' (I := J) (s x) fun n => by
      simpa using map_mem_pow_smul_top J s (hx n)
    rw [← hs x, this, map_zero]
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => s (u k))
      fun hab => map_mem_pow_smul_top J s (hu hab)
    exact ⟨π L, fun n => by simpa [hs] using map_mem_pow_smul_top J π (hL n)⟩

theorem isAdicComplete_span_natCast_of_finite_projective (p : ℕ) (O A : Type) [CommRing O] [CommRing A]
    [Algebra O A] [Module.Finite O A] [Module.Projective O A]
    [IsAdicComplete (Ideal.span {(p : O)}) O] : IsAdicComplete (Ideal.span {(p : A)}) A := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' O A
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have : IsAdicComplete (Ideal.span {(p : O)}) (Fin r → O) := isAdicComplete_pi _
  have hO : IsAdicComplete (Ideal.span {(p : O)}) A :=
    isAdicComplete_of_retract _ π s fun x => by simpa using LinearMap.congr_fun hs x
  have hmap : (Ideal.span {(p : O)}).map (algebraMap O A) = Ideal.span {(p : A)} := by
    simp [Ideal.map_span]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).2 hO

end GlobalTheory.FinProjComplete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastFiniteProjectiveAlgebraStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_span_natCast_finite_projective_algebra : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  first | exact @GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective | exact GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective | (intros; apply GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesOfIsConnected
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open scoped TensorProduct

theorem GlobalTheory.PDivGroup.exists_coords_of_isConn : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, PDivLat.IsConn G → ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n) (ev : ∀ n, MvPowerSeries (Fin d) O →ₐ[O] G.A n), (∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N) ∧ (∀ n, IsEval p (x n) (ev n)) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n, Function.Surjective (ev n)) ∧ ∀ m N : ℕ, ∃ n, ∀ f, ev n f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G hG
  obtain ⟨d, x, hcou, hres, hspan, hl⟩ := GlobalTheory.T.exists_compatible_pDivGroup_level_coordinates p C v O hv G
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (Fact.out : ¬IsUnit (p : O))
  have hmem : ∀ n i, ¬IsUnit (x n i) := by
    intro n i hu
    have h1 := hu.map (Bialgebra.counitAlgHom O (G.A n))
    rw [Bialgebra.counitAlgHom_apply, hcou n i] at h1
    exact not_isUnit_zero h1
  have hnil : ∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N := fun n i => by
    haveI := hG n
    exact GlobalTheory.T.maximalIdeal_pow_natCast_dvd_finite_integers_algebra p hp0 C v O hv (G.A n) (x n i) ((IsLocalRing.mem_maximalIdeal _).2 (hmem n i))
  have hex : ∀ n, ∃ E : MvPowerSeries (Fin d) O →ₐ[O] G.A n, IsEval p (x n) E := fun n => by
    haveI := GlobalTheory.T.isAdicComplete_span_natCast_finite_projective_algebra p O (G.A n)
    exact ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O (G.A n) (Fin d) (x n) (hnil n)).1).exists
  choose ev hev using hex
  have hpoly : ∀ n (P : MvPolynomial (Fin d) O),
      ev n (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (x n) P := by
    intro n P
    have h : (ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (x n) :=
      MvPolynomial.algHom_ext fun i => by
        simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, (hev n).1 i]
    exact DFunLike.congr_fun h P
  refine ⟨d, x, ev, hnil, hev, hres, hcou, fun n => ?_, fun m N => ?_⟩
  · haveI := hG n
    intro a
    obtain ⟨P, hP⟩ := GlobalTheory.T.aeval_surjective_of_cotangent_span_top O (G.A n) (p : O) hpm (Bialgebra.counitAlgHom O (G.A n)) d (x n)
      (fun i => by rw [Bialgebra.counitAlgHom_apply]; exact hcou n i)
      (fun i => by simpa [map_natCast] using hnil n i) (hspan n) a
    exact ⟨P, (hpoly n P).trans hP⟩
  · obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.coeff_annihilated_of_aeval_mem_ker_pow d N
    obtain ⟨e, u, hu, hKu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hK0.ne' p (Fact.out : p.Prime).ne_one
    refine ⟨m + e, fun f hf α hα => ?_⟩
    obtain ⟨P, hPdeg, hPco, hPmem⟩ := GlobalTheory.T.exists_truncation_congr_of_padicContinuousEval_eq_zero p O (G.A (m + e)) d (x (m + e)) (ev (m + e)) (hev _) (m + e) N f hf
    obtain ⟨l, hlx⟩ := hl (m + e)
    let I : Ideal O := Ideal.span {(p : O) ^ (m + e)}
    let l' : Fin d → (G.A (m + e) →ₗ[O] O ⧸ I) :=
      fun i => l i ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (G.A (m + e)))
    obtain ⟨D, hD⟩ := GlobalTheory.T.exists_invariant_derivations_quotient_bialgebra O (G.A (m + e)) I d l' (fun i a b => by
      simp only [l', LinearMap.comp_apply, AugCot.d_mul, map_add (f := _), map_smul, Bialgebra.counitAlgHom_apply])
    let φ : G.A (m + e) →ₐ[O] (O ⧸ I) ⊗[O] G.A (m + e) := Algebra.TensorProduct.includeRight
    have hy0 : ∀ j, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) (φ (x (m + e) j)) = 0 := by
      intro j
      simp [φ, Algebra.TensorProduct.includeRight_apply, TensorProduct.counit_tmul, hcou]
    have hDy : ∀ i j, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) (D i (φ (x (m + e) j))) =
        if i = j then 1 else 0 := fun i j => (hD i _).trans (hlx i j)
    have hdeg : ∀ β : Fin d →₀ ℕ, N ≤ β.degree →
        AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap O (O ⧸ I)) P) β = 0 := fun β hβ => by
      rw [MvPolynomial.coeff_map, hPdeg β hβ, map_zero]
    have hmemB : MvPolynomial.aeval (fun j => φ (x (m + e) j)) (MvPolynomial.map (algebraMap O (O ⧸ I)) P) ∈
        RingHom.ker (Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e))) ^ N := by
      rw [MvPolynomial.aeval_map_algebraMap, ← MvPolynomial.comp_aeval, AlgHom.comp_apply]
      refine (Ideal.map_le_iff_le_comap.1 ?_) hPmem
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span]
      refine sup_le (Ideal.pow_right_mono ?_ N) ?_
      · rw [Ideal.span_le]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        exact hy0 j
      · rw [Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
        have h0 : φ ((p : G.A (m + e)) ^ (m + e)) = 0 := by
          rw [map_pow, map_natCast]
          have h1 : ((p : (O ⧸ I) ⊗[O] G.A (m + e))) ^ (m + e) =
              algebraMap (O ⧸ I) _ (Ideal.Quotient.mk I ((p : O) ^ (m + e))) := by
            rw [map_pow, map_pow, map_natCast, map_natCast]
          rw [h1, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
        rw [SetLike.mem_coe, h0]
        exact zero_mem _
    have key := hK (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) _ _ D hy0 hDy _ hdeg hmemB α
    rw [MvPolynomial.coeff_map, ← map_natCast (algebraMap O (O ⧸ I)), ← map_mul,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at key
    rw [← hPco α hα]
    have hpO : (p : O) ≠ 0 := by
      intro h
      have h2 := congrArg (algebraMap O C) h
      rw [map_natCast, map_zero] at h2
      exact hp0 (by exact_mod_cast h2)
    have hunit : IsUnit (u : O) := by
      by_contra hnu
      have hcop : IsCoprime (u : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2
        ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hu)))
      obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom O)
      have h3 : a * Int.castRingHom O u + b * Int.castRingHom O p ∈ IsLocalRing.maximalIdeal O := by
        refine add_mem (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
        · simpa using (IsLocalRing.mem_maximalIdeal _).2 hnu
        · simpa using hpm
      rw [hab] at h3
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
    rw [hKu, Nat.cast_mul, Nat.cast_pow, pow_add, mul_assoc, mul_comm ((p : O) ^ m)] at key
    have key2 := (mul_dvd_mul_iff_left (pow_ne_zero e hpO)).1 key
    exact (hunit.dvd_mul_left).1 key2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesOfIsConnectedStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_of_isConnected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, PDivLat.IsConn G → ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n) (ev : ∀ n, MvPowerSeries (Fin d) O →ₐ[O] G.A n), (∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N) ∧ (∀ n, IsEval p (x n) (ev n)) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n, Function.Surjective (ev n)) ∧ ∀ m N : ℕ, ∃ n, ∀ f, ev n f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  first | exact @GlobalTheory.PDivGroup.exists_coords_of_isConn | exact GlobalTheory.PDivGroup.exists_coords_of_isConn | (intros; apply GlobalTheory.PDivGroup.exists_coords_of_isConn <;> assumption)
end
