module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.PerfCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.EventuallyMQGrFiniteAnnihilator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenQuotientWeightPieceLeOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenAPieceIdeal2LeTwoPow
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenAPieceSupSpanSqLeAdd
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem locLen_le_of_exact {O B K : Type} [CommRing O] [CommRing B] [Algebra O B] [Field K] [Algebra O K]
    (σ : B →ₐ[O] K) {M N P : Type} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (f : M →ₗ[B] N) (g : N →ₗ[B] P) (h : Function.Exact f g) :
    locLen σ N ≤ locLen σ M + locLen σ P := by
  haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
  exact Formalism.MainNotions.V.Pf.V2.length_le_of_exact (LocalizedModule.map (RingHom.ker σ).primeCompl f)
    (LocalizedModule.map (RingHom.ker σ).primeCompl g) (LocalizedModule.map_exact _ f g h)

theorem UpperTheory.V.Alg.M.locLen_aPiece_sup_span_sq_le_add :
    ∀ (O K A : Type) [CommRing O] [Field K] [Algebra O K] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
      (σ : 𝒜 0 →ₐ[O] K) (J : Ideal A), J.IsHomogeneous 𝒜 → ∀ (d : ℤ) (t : A), t ∈ 𝒜 d → ∀ w : ℤ,
      locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w) ≤
        locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t}) (w - d)) + locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t}) w) := by
  intro O K A _ _ _ _ _ 𝒜 _ σ J hJ d t ht w
  have h1 : J ⊔ Ideal.span {t} ≤ Submodule.comap (LinearMap.mulLeft A t) (J ⊔ Ideal.span {t ^ 2}) := by
    intro a ha
    obtain ⟨j, hj, b, hb, rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    show t * (j + c * t) ∈ J ⊔ Ideal.span {t ^ 2}
    rw [show t * (j + c * t) = t * j + c * t ^ 2 by ring]
    exact Submodule.add_mem_sup (J.mul_mem_left _ hj) (Ideal.mem_span_singleton'.2 ⟨c, rfl⟩)
  have h2 : J ⊔ Ideal.span {t ^ 2} ≤ Submodule.comap (LinearMap.id : A →ₗ[A] A) (J ⊔ Ideal.span {t}) :=
    sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self t two_ne_zero)) J
  let F : (A ⧸ (J ⊔ Ideal.span {t})) →ₗ[𝒜 0] A ⧸ (J ⊔ Ideal.span {t ^ 2}) :=
    (Submodule.mapQ _ _ (LinearMap.mulLeft A t) h1).restrictScalars (𝒜 0)
  let G : (A ⧸ (J ⊔ Ideal.span {t ^ 2})) →ₗ[𝒜 0] A ⧸ (J ⊔ Ideal.span {t}) :=
    (Submodule.mapQ _ _ (LinearMap.id : A →ₗ[A] A) h2).restrictScalars (𝒜 0)
  have hF : ∀ a : A, F (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (t * a) := fun a => rfl
  have hG : ∀ a : A, G (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := fun a => rfl
  have hF' : ∀ x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t}) (w - d), F x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨t * a, ?_, (hF a).symm⟩
    have := SetLike.GradedMul.mul_mem ht (show a ∈ 𝒜 (w - d) from ha)
    rwa [add_sub_cancel] at this
  have hG' : ∀ x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w, G x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t}) w := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (hG a).symm⟩
  refine locLen_le_of_exact σ (F.restrict hF') (G.restrict hG') ?_
  rintro ⟨_, a, ha, rfl⟩
  constructor
  · intro h
    have h0 : Ideal.Quotient.mk (J ⊔ Ideal.span {t}) a = 0 := congrArg Subtype.val h
    obtain ⟨j, hj, b, hb, hab⟩ := Submodule.mem_sup.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    have ha' : a ∈ 𝒜 w := ha
    have e1 : ((DirectSum.decompose 𝒜 (t * c)) (d + (w - d)) : A) = t * DirectSum.decompose 𝒜 c (w - d) :=
      DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 ht
    rw [add_sub_cancel] at e1
    have e2 : a = (DirectSum.decompose 𝒜 j w : A) + t * DirectSum.decompose 𝒜 c (w - d) := by
      rw [← e1, ← DirectSum.decompose_of_mem_same 𝒜 ha', ← hab, DirectSum.decompose_add, mul_comm c t]
      rfl
    refine ⟨⟨Ideal.Quotient.mk _ (DirectSum.decompose 𝒜 c (w - d) : A),
      ⟨_, (DirectSum.decompose 𝒜 c (w - d)).2, rfl⟩⟩, Subtype.ext ?_⟩
    show Ideal.Quotient.mk _ (t * (DirectSum.decompose 𝒜 c (w - d) : A)) = Ideal.Quotient.mk _ a
    rw [eq_comm, Ideal.Quotient.eq, e2, add_sub_cancel_right]
    exact Submodule.mem_sup_left (hJ w hj)
  · rintro ⟨⟨_, c, hc, rfl⟩, h⟩
    rw [← h]
    apply Subtype.ext
    show Ideal.Quotient.mk (J ⊔ Ideal.span {t}) (t * c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Submodule.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩))
end

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem homRange {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] {ι : Type} (t : ι → A) (d : ℤ) (ht : ∀ i, t i ∈ 𝒜 d) :
    (Ideal.span (Set.range t)).IsHomogeneous 𝒜 := by
  refine Ideal.homogeneous_span 𝒜 _ ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨d, ht i⟩

private theorem sqMem {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] {t : A} {d : ℤ} (ht : t ∈ 𝒜 d) : t ^ 2 ∈ 𝒜 (d + d) := by
  rw [pow_two]
  exact SetLike.mul_mem_graded ht ht

private theorem spanSucc {A : Type} [CommRing A] {n : ℕ} (t : Fin (n + 1) → A) :
    Ideal.span (Set.range t) = Ideal.span {t 0} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ) := by
  rw [Fin.range_fin_succ, Ideal.span_insert]
  rfl

private theorem gen {O K A : Type} [CommRing O] [Field K] [Algebra O K] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (σ : 𝒜 0 →ₐ[O] K) (d : ℤ) (c : ℕ∞) (n : ℕ) :
    ∀ (t : Fin n → A), (∀ i, t i ∈ 𝒜 d) → ∀ J : Ideal A, J.IsHomogeneous 𝒜 →
      (∀ w, locLen σ (aPiece 𝒜 (J ⊔ Ideal.span (Set.range t)) w) ≤ c) →
      ∀ w, locLen σ (aPiece 𝒜 (J ⊔ Ideal.span (Set.range fun i => t i ^ 2)) w) ≤ 2 ^ n * c := by
  induction n generalizing c with
  | zero =>
    intro t _ J _ h w
    have e1 : Set.range (fun i : Fin 0 => t i ^ 2) = Set.range t := by
      simp [Set.range_eq_empty]
    rw [e1, pow_zero, one_mul]
    exact h w
  | succ n ih =>
    intro t ht J hJ h w
    have hJ1 : (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)).IsHomogeneous 𝒜 :=
      hJ.sup (homRange 𝒜 _ d fun i => ht i.succ)
    have h1 : ∀ w', locLen σ (aPiece 𝒜 ((J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔
        Ideal.span {t 0 ^ 2}) w') ≤ 2 * c := by
      intro w'
      have e : (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔ Ideal.span {t 0} =
          J ⊔ Ideal.span (Set.range t) := by
        rw [spanSucc t, sup_assoc, sup_comm (Ideal.span (Set.range fun i : Fin n => t i.succ))]
      refine (locLen_aPiece_sup_span_sq_le_add O K A 𝒜 σ _ hJ1 d (t 0) (ht 0) w').trans ?_
      rw [e, two_mul]
      exact add_le_add (h _) (h _)
    have hsq : (Ideal.span ({t 0 ^ 2} : Set A)).IsHomogeneous 𝒜 := by
      apply Ideal.homogeneous_span
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact ⟨d + d, sqMem 𝒜 (ht 0)⟩
    have hJ2 : (J ⊔ Ideal.span {t 0 ^ 2}).IsHomogeneous 𝒜 := hJ.sup hsq
    have h2 := ih (2 * c) (fun i => t i.succ) (fun i => ht i.succ) (J ⊔ Ideal.span {t 0 ^ 2}) hJ2
      (by
        intro w'
        have e : J ⊔ Ideal.span {t 0 ^ 2} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ) =
            (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔ Ideal.span {t 0 ^ 2} := by
          rw [sup_assoc, sup_assoc, sup_comm (Ideal.span {t 0 ^ 2})]
        rw [e]
        exact h1 w') w
    have e : J ⊔ Ideal.span {t 0 ^ 2} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ ^ 2) =
        J ⊔ Ideal.span (Set.range fun i => t i ^ 2) := by
      rw [spanSucc (fun i => t i ^ 2), sup_assoc]
    rw [e] at h2
    calc _ ≤ 2 ^ n * (2 * c) := h2
      _ = 2 ^ (n + 1) * c := by rw [pow_succ, mul_assoc]

theorem UpperTheory.V.Alg.M.locLen_aPiece_ideal2_le_two_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ σ : 𝒜 0 →ₐ[O] K, (∀ w, locLen σ (aPiece 𝒜 Q.ideal w) ≤ 1) → ∀ w, locLen σ (aPiece 𝒜 (ideal2 Q) w) ≤ 2 ^ (r + 1 + r') := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q σ h1
  have hJ0 : (Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z)).IsHomogeneous 𝒜 := by
    apply Ideal.homogeneous_span
    rintro y ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨-2, Q.hG i⟩
    · exact ⟨2, Q.hE' i⟩
    · exact ⟨0, (Q.hZ i).1⟩
  have hE := homRange 𝒜 Q.E 1 Q.hE
  have hF2 := homRange 𝒜 (fun i => Q.F i ^ 2) (-1 + -1) fun i => sqMem 𝒜 (Q.hF i)
  have step1 := gen 𝒜 σ (-1) 1 (r + 1) Q.F Q.hF
    (Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range Q.E))
    (hJ0.sup hE)
    (by
      intro w'
      have e : Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range Q.E) ⊔
          Ideal.span (Set.range Q.F) = Q.ideal := by
        simp only [Eqns.ideal, Ideal.span_union]
        ac_rfl
      rw [e]
      exact h1 w')
  have step2 := gen 𝒜 σ 1 (2 ^ (r + 1) * 1) r' Q.E Q.hE
    (Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range fun i => Q.F i ^ 2))
    (hJ0.sup hF2)
    (by
      intro w'
      have e : Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔
          Ideal.span (Set.range fun i => Q.F i ^ 2) ⊔ Ideal.span (Set.range Q.E) =
          Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range Q.E) ⊔
          Ideal.span (Set.range fun i => Q.F i ^ 2) := by
        ac_rfl
      rw [e]
      exact step1 w')
  intro w
  have e : Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔
      Ideal.span (Set.range fun i => Q.F i ^ 2) ⊔ Ideal.span (Set.range fun i => Q.E i ^ 2) = ideal2 Q := by
    simp only [ideal2, Ideal.span_union]
    ac_rfl
  have h := step2 w
  rw [e] at h
  calc _ ≤ 2 ^ r' * (2 ^ (r + 1) * 1) := h
    _ = 2 ^ (r + 1 + r') := by rw [mul_one, pow_add (2 : ℕ∞) (r + 1) r', mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocalizedLengthLeOfSurjective
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem localized_length_le_of_surjective {O B K : Type} [CommRing O] [CommRing B] [Algebra O B] [Field K] [Algebra O K]
    (σ : B →ₐ[O] K) {L M N : Type} [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (φ : L →ₗ[B] M) (ψ : L →ₗ[B] N) (hφ : Function.Surjective φ)
    (h : ∀ x, ψ x = 0 → ∃ t : B, σ t ≠ 0 ∧ t • φ x = 0) : locLen σ M ≤ locLen σ N := by
  haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
  unfold locLen
  set S := (RingHom.ker σ).primeCompl
  have hs : Function.Surjective (LocalizedModule.map S φ) := LocalizedModule.map_surjective S φ hφ
  have hk : LinearMap.ker (LocalizedModule.map S ψ) ≤ LinearMap.ker (LocalizedModule.map S φ) := by
    intro y hy
    induction y using LocalizedModule.induction_on with
    | h x s =>
      rw [LinearMap.mem_ker, LocalizedModule.map_mk] at hy ⊢
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hy ⊢
      obtain ⟨u, hu⟩ := hy
      have h1 : ψ ((u : B) • x) = 0 := by simpa [Submonoid.smul_def] using hu
      obtain ⟨t, ht, h2⟩ := h _ h1
      refine ⟨⟨t, ht⟩ * u, ?_⟩
      simpa [Submonoid.smul_def, mul_smul] using h2
  have hs2 : Function.Surjective ((LinearMap.ker (LocalizedModule.map S ψ)).liftQ (LocalizedModule.map S φ) hk) := by
    intro y
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  refine (Module.length_le_of_surjective _ hs2).trans ?_
  exact Module.length_le_of_injective ((LinearMap.ker (LocalizedModule.map S ψ)).liftQ (LocalizedModule.map S ψ) le_rfl)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))

section

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]

private def u4w (μ : Fin 3 →₀ ℕ) : ℤ := 2 * ((μ 1 : ℤ) - μ 0 - μ 2)

private theorem weight_submodule_mul_le (i j : ℤ) : oz 𝒜 i * oz 𝒜 j ≤ oz 𝒜 (i + j) :=
  Submodule.mul_le.2 fun _ ha _ hb => (mem_oz 𝒜).2 (SetLike.GradedMul.mul_mem ((mem_oz 𝒜).1 ha) ((mem_oz 𝒜).1 hb))

private theorem weight_submodule_pow_le {P : Submodule (𝒜 0) A} {i : ℤ} (h : P ≤ oz 𝒜 i) (n : ℕ) : P ^ n ≤ oz 𝒜 (n * i) := by
  induction n with
  | zero =>
    rw [pow_zero, Submodule.one_le]
    simpa using (SetLike.GradedOne.one_mem : (1 : A) ∈ 𝒜 0)
  | succ n ih =>
    rw [pow_succ]
    refine (mul_le_mul' ih h).trans ((weight_submodule_mul_le 𝒜 _ _).trans (le_of_eq ?_))
    congr 1; push_cast; ring

private theorem lattice_le_weight_submodule {F : A} (hF : F ∈ 𝒜 (-1)) (μ : Fin 3 →₀ ℕ) : lat (mN 𝒜 F) μ ≤ oz 𝒜 (u4w μ) := by
  have h2 : mN 𝒜 F 2 ≤ oz 𝒜 (-2) := by
    show Submodule.span (𝒜 0) {F ^ 2} ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 ≤ _
    refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (sq_mem_neg 𝒜 hF)) ?_
    exact (mul_le_mul' (weight_submodule_mul_le 𝒜 _ _) le_rfl).trans (weight_submodule_mul_le 𝒜 _ _)
  have h0 : mN 𝒜 F 0 ≤ oz 𝒜 (-2) := le_rfl
  have h1 : mN 𝒜 F 1 ≤ oz 𝒜 2 := le_rfl
  rw [lat, Fin.prod_univ_three]
  refine (mul_le_mul' ((mul_le_mul' (weight_submodule_pow_le 𝒜 h0 _) (weight_submodule_pow_le 𝒜 h1 _)).trans (weight_submodule_mul_le 𝒜 _ _))
    (weight_submodule_pow_le 𝒜 h2 _)).trans ((weight_submodule_mul_le 𝒜 _ _).trans (le_of_eq ?_))
  congr 1; unfold u4w; ring

private theorem power_mul_mem_lattice (hp : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n ∧ oz 𝒜 (2 * n) = oz 𝒜 2 ^ n)
    (F : A) {f g : A} (hf : f ∈ 𝒜 (-2)) (hg : g ∈ 𝒜 2) (μ : Fin 3 →₀ ℕ) {a : A} (ha : a ∈ 𝒜 (u4w μ)) :
    ∃ n : ℕ, (f * g) ^ n * a ∈ lat (mN 𝒜 F) μ := by
  have hl : oz 𝒜 (-2) ^ (μ 0 + 2 * μ 2) * oz 𝒜 2 ^ (μ 1 + μ 2) ≤ lat (mN 𝒜 F) μ := by
    have h2 : oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 ≤ mN 𝒜 F 2 := le_sup_right
    rw [lat, Fin.prod_univ_three]
    refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl (pow_le_pow_left' h2 (μ 2)))
    show _ = oz 𝒜 (-2) ^ μ 0 * oz 𝒜 2 ^ μ 1 * _
    ring
  have hfg : ∀ n : ℕ, (f * g) ^ n ∈ oz 𝒜 (-2) ^ n * oz 𝒜 2 ^ n := fun n => by
    rw [mul_pow]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow (oz 𝒜 (-2)) hf n) (Submodule.pow_mem_pow (oz 𝒜 2) hg n)
  rcases le_total (μ 0 + 2 * μ 2) (μ 1 + μ 2) with h | h
  · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le h
    refine ⟨μ 0 + 2 * μ 2, hl ?_⟩
    have ha' : a ∈ oz 𝒜 2 ^ c := by
      rw [← (hp c).2, mem_oz]
      have : u4w μ = 2 * c := by unfold u4w; omega
      rwa [this] at ha
    rw [hc, pow_add (oz 𝒜 2) _ c, ← mul_assoc]
    exact Submodule.mul_mem_mul (hfg _) ha'
  · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le h
    refine ⟨μ 1 + μ 2, hl ?_⟩
    have ha' : a ∈ oz 𝒜 (-2) ^ c := by
      rw [← (hp c).1, mem_oz]
      have : u4w μ = -(2 * c) := by unfold u4w; omega
      rwa [this] at ha
    rw [hc, pow_add (oz 𝒜 (-2)) _ c, mul_right_comm]
    exact Submodule.mul_mem_mul (hfg _) ha'

private def u4K (F : A) (b : 𝒜 0) (J : Ideal (rees (mN 𝒜 F))) (μ : Fin 3 →₀ ℕ) : AddSubmonoid A where
  carrier := {a | ∃ n : ℕ, ∃ p ∈ J, p.1 = MvPolynomial.monomial μ ((b : A) ^ n * a)}
  zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
  add_mem' := by
    rintro a a' ⟨n, p, hp, e⟩ ⟨n', p', hp', e'⟩
    refine ⟨n + n', b ^ n' • p + b ^ n • p',
      J.add_mem (Submodule.smul_of_tower_mem _ _ hp) (Submodule.smul_of_tower_mem _ _ hp'), ?_⟩
    show b ^ n' • p.1 + b ^ n • p'.1 = _
    rw [e, e', MvPolynomial.smul_monomial, MvPolynomial.smul_monomial, ← map_add (f := _)]
    congr 1
    show ((b ^ n' : 𝒜 0) : A) * _ + ((b ^ n : 𝒜 0) : A) * _ = _
    simp only [SetLike.GradeZero.coe_pow]
    ring

private theorem generated_component_mem (hp : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n ∧ oz 𝒜 (2 * n) = oz 𝒜 2 ^ n)
    (F : A) {f g : A} (hf : f ∈ 𝒜 (-2)) (hg : g ∈ 𝒜 2) (b : 𝒜 0) (hb : (b : A) = f * g)
    (J : Ideal (rees (mN 𝒜 F))) (μ ν : Fin 3 →₀ ℕ) (hν : ν ≤ μ) {y : A} (hy : y ∈ 𝒜 (u4w ν))
    (q : rees (mN 𝒜 F)) (hq : q ∈ J) (e : q.1 = MvPolynomial.monomial ν y) (c : A) :
    (DirectSum.decompose 𝒜 (c * y) (u4w μ) : A) ∈ u4K 𝒜 F b J μ := by
  obtain ⟨ν', rfl⟩ := exists_add_of_le hν
  have hw : u4w (ν + ν') = u4w ν' + u4w ν := by
    simp only [u4w, Finsupp.add_apply]; push_cast; ring
  rw [hw, DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hy]
  obtain ⟨n, hn⟩ := power_mul_mem_lattice 𝒜 hp F hf hg ν' (DirectSum.decompose 𝒜 c (u4w ν')).2
  refine ⟨n, mono _ ν' _ hn * q, J.mul_mem_left _ hq, ?_⟩
  show MvPolynomial.monomial ν' _ * q.1 = _
  rw [e, MvPolynomial.monomial_mul, add_comm, hb, mul_assoc]

end

theorem UpperTheory.V.Alg.M.locLen_mQ_gr_le_locLen_aPiece :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ J : Ideal (mR Q), secs (ts Q) ≤ J → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ J) →
    ∀ σ : 𝒜 0 →ₐ[O] K, ¬ idD 𝒜 ≤ RingHom.ker σ → ∀ d : Deg 3, 1 ≤ d →
      locLen σ ((mQ Q J).gr d) ≤ locLen σ (aPiece 𝒜 (ideal2 Q) (2 * (d 1 - d 0 - d 2))) := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q J hJ hZ σ hσ d hd
  have hp := oz_two_mul_eq_pow O A 𝒜 x hW
  obtain ⟨b, ⟨f, hf, g, hg, hb⟩, hbσ⟩ : ∃ b : 𝒜 0, (∃ f ∈ 𝒜 (-2), ∃ g ∈ 𝒜 2, (b : A) = f * g) ∧ σ b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hσ (Ideal.span_le.2 fun b ⟨f, hf, g, hg, hb⟩ => hcon b ⟨f, hf, g, hg, hb⟩)
  obtain ⟨μ, rfl⟩ : ∃ μ : Fin 3 →₀ ℕ, toDeg μ = d :=
    ⟨Finsupp.equivFunOnFinite.symm fun i => (d i).toNat, funext fun i => by
      have : (1 : ℤ) ≤ d i := hd i
      simp only [toDeg, Finsupp.equivFunOnFinite_symm_apply_apply]
      omega⟩
  have hμ : ∀ i, Finsupp.single i 1 ≤ μ := fun i => by
    have : (1 : ℤ) ≤ (μ i : ℤ) := hd i
    rw [Finsupp.single_le_iff]; omega
  have hsec : ∀ (i : Fin 3) (y : A) (hy : y ∈ mN 𝒜 (Q.F (Fin.last r)) i), (e i, sec _ i y hy) ∈ ts Q →
      ∀ c : A, (DirectSum.decompose 𝒜 (c * y) (u4w μ) : A) ∈ u4K 𝒜 _ b J μ := fun i y hy hm =>
    generated_component_mem 𝒜 hp _ hf hg b hb J μ _ (hμ i)
      (lattice_le_weight_submodule 𝒜 (Q.hF (Fin.last r)) _ (by rw [lat_single]; exact hy)) _ (hJ (Ideal.subset_span ⟨_, hm⟩)) rfl
  have hI : ∀ y ∈ ideal2 Q, ∀ c : A, (DirectSum.decompose 𝒜 (c * y) (u4w μ) : A) ∈ u4K 𝒜 _ b J μ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
      · induction i using Fin.lastCases with
        | last =>
          exact hsec 2 _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
            (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
        | cast i =>
          exact hsec 0 _ (sq_mem_neg 𝒜 (Q.hF _)) (List.mem_append_left _ (List.mem_ofFn.2 ⟨i, rfl⟩))
      · exact hsec 0 _ (Q.hG i) (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_ofFn.2 ⟨i, rfl⟩)))))
      · exact hsec 1 _ (sq_mem_pos 𝒜 (Q.hE i)) (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.2 ⟨i, rfl⟩)))))
      · exact hsec 1 _ (Q.hE' i) (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_ofFn.2 ⟨i, rfl⟩))))
      · exact generated_component_mem 𝒜 hp _ hf hg b hb J μ 0 bot_le (Q.hZ i).1 _ (hZ i) rfl
    | zero => intro c; simp
    | add y z _ _ h1 h2 =>
      intro c
      rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact add_mem (h1 c) (h2 c)
    | smul a y _ h1 =>
      intro c
      rw [smul_eq_mul, ← mul_assoc]
      exact h1 _
  let φ0 : lat (mN 𝒜 (Q.F (Fin.last r))) μ →ₗ[𝒜 0] mR Q :=
    { toFun := fun h => mono _ μ h.1 h.2
      map_add' := fun h h' => Subtype.ext (map_add (MvPolynomial.monomial μ) h.1 h'.1)
      map_smul' := fun c h => Subtype.ext (MvPolynomial.smul_monomial c).symm }
  let φ : lat (mN 𝒜 (Q.F (Fin.last r))) μ →ₗ[𝒜 0] (mQ Q J).gr (toDeg μ) :=
    LinearMap.codRestrict _ ((J.mkQ.restrictScalars (𝒜 0)) ∘ₗ φ0) fun h => ⟨φ0 h, mono_mem _ μ h.1 h.2, rfl⟩
  let ψ : lat (mN 𝒜 (Q.F (Fin.last r))) μ →ₗ[𝒜 0] aPiece 𝒜 (ideal2 Q) (u4w μ) :=
    LinearMap.codRestrict _ ((Ideal.Quotient.mkₐ (𝒜 0) (ideal2 Q)).toLinearMap ∘ₗ Submodule.subtype _) fun h =>
      ⟨h.1, lattice_le_weight_submodule 𝒜 (Q.hF (Fin.last r)) μ h.2, rfl⟩
  refine localized_length_le_of_surjective σ φ ψ ?_ ?_
  · rintro ⟨_, p, hp', rfl⟩
    refine ⟨⟨AddMonoidAlgebra.coeff p.1 μ, p.2 μ⟩, Subtype.ext ?_⟩
    show J.mkQ (mono _ μ _ (p.2 μ)) = J.mkQ p
    congr 1
    apply Subtype.ext
    ext ν
    show AddMonoidAlgebra.coeff (MvPolynomial.monomial μ _) ν = _
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [h]
    · exact (hp' ν fun h' => h (toDeg_injective h').symm).symm
  · intro h h0
    have h1 : h.1 ∈ ideal2 Q := Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Subtype.val h0)
    have h2 := hI _ h1 1
    rw [one_mul, DirectSum.decompose_of_mem_same 𝒜 (lattice_le_weight_submodule 𝒜 (Q.hF (Fin.last r)) μ h.2)] at h2
    obtain ⟨n, p, hpJ, e⟩ := h2
    refine ⟨b ^ n, by rw [map_pow]; exact pow_ne_zero _ hbσ, ?_⟩
    rw [← map_smul]
    apply Subtype.ext
    show J.mkQ (φ0 (b ^ n • h)) = 0
    have : φ0 (b ^ n • h) = p := by
      apply Subtype.ext
      rw [e]
      show MvPolynomial.monomial μ (((b ^ n : 𝒜 0) : A) * h.1) = _
      rw [SetLike.GradeZero.coe_pow]
    rw [this]
    exact (Submodule.Quotient.mk_eq_zero _).2 hpJ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.HerbrandFinLen
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LengthQuotientSpanEqFinsumValuation
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open scoped nonZeroDivisors

private theorem length_quotient_eq_norm_valuation {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {D : Type} [CommRing D] [Algebra O D] [Module.Finite O D] [Module.Free O D] (a : D) :
    Module.length O (D ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal O (Algebra.norm O a) := by
  classical
  let b := Module.Free.chooseBasis O D
  let f : D →ₗ[O] D := Algebra.lmul O D a
  let Φ := LinearMap.toMatrix b b f
  have hdet : Algebra.norm O a = Φ.det := by
    rw [Algebra.norm_apply, LinearMap.det_toMatrix]
  have hmul : Φ.mulVecLin = b.equivFun.toLinearMap ∘ₗ f ∘ₗ b.equivFun.symm.toLinearMap := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := b.equivFun.surjective y
    simp only [Matrix.mulVecLin_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    simp only [Module.Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr b b f x
  have hI : (Ideal.span {a}).restrictScalars O = LinearMap.range f := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', LinearMap.mem_range, f,
      Algebra.coe_lmul_eq_mul]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
  have hmap : (LinearMap.range f).map b.equivFun.toLinearMap = LinearMap.range Φ.mulVecLin := by
    rw [hmul, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ← LinearMap.range_eq_map]
  let e : (D ⧸ Ideal.span {a}) ≃ₗ[O] KStar.Selmer.H2 Φ :=
    (Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {a})).symm.trans
      ((Submodule.quotEquivOfEq _ _ hI).trans (Submodule.Quotient.equiv _ _ b.equivFun hmap))
  rw [e.length_eq, hdet]
  exact KStar.Selmer.length_cokernel_eq_addVal_det Φ

private theorem algHom_finite_domain_injective {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] (σ : D →ₐ[O] K) :
    Function.Injective σ := by
  have : Algebra.IsIntegral O D := Algebra.IsIntegral.of_finite O D
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hker : (RingHom.ker σ).comap (algebraMap O D) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]
    exact ⟨fun h => (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).1 h,
      fun h => by simp [h]⟩
  have hmem : x ∈ RingHom.ker σ := hx
  rw [Ideal.eq_bot_of_comap_eq_bot hker] at hmem
  exact hmem

attribute [local instance] FractionRing.liftAlgebra in
private theorem algebra_norm_eq_prod_embeddings {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    {K : Type} [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] [Module.Free O D]
    (a : D) : ∃ _ : Fintype (D →ₐ[O] K), algebraMap O K (Algebra.norm O a) = ∏ σ : D →ₐ[O] K, σ a := by
  classical
  have : IsScalarTower O (FractionRing O) K := FractionRing.isScalarTower_liftAlgebra O K
  let M := Algebra.algebraMapSubmonoid D O⁰
  let L := Localization M
  have hM : M ≤ D⁰ := by
    rintro _ ⟨m, hm, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O D)).2 (nonZeroDivisors.ne_zero hm))
  have : IsDomain L := IsLocalization.isDomain_localization hM
  have hF : IsField L := by
    have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
    exact isField_of_isIntegral_of_isField' (Field.toIsField (FractionRing O))
  letI : Field L := hF.toField
  letI : Algebra (FractionRing O) L := localizationAlgebra O⁰ D
  have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
  have hN : Algebra.norm (FractionRing O) (algebraMap D L a) =
      algebraMap O (FractionRing O) (Algebra.norm O a) :=
    Algebra.norm_localization O O⁰ a
  have hE := Algebra.norm_eq_prod_embeddings (FractionRing O) K (algebraMap D L a)
  let r : (L →ₐ[FractionRing O] K) → (D →ₐ[O] K) := fun τ =>
    (τ.restrictScalars O).comp (IsScalarTower.toAlgHom O D L)
  have hinj : Function.Injective r := by
    intro τ₁ τ₂ h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext M
    ext d
    exact DFunLike.congr_fun h d
  have hsurj : Function.Surjective r := by
    intro σ
    have hu : ∀ y : M, IsUnit ((σ : D →+* K) y) := by
      rintro ⟨_, m, hm, rfl⟩
      rw [AlgHom.coe_toRingHom, AlgHom.commutes]
      exact isUnit_iff_ne_zero.2
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).2 (nonZeroDivisors.ne_zero hm))
    let τ₀ : L →+* K := IsLocalization.lift hu
    have hc : τ₀.comp (algebraMap (FractionRing O) L) = algebraMap (FractionRing O) K := by
      apply IsLocalization.ringHom_ext O⁰
      ext c
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply O D L, IsLocalization.lift_eq]
      simp
    refine ⟨{ τ₀ with commutes' := fun x => DFunLike.congr_fun hc x }, ?_⟩
    ext d
    simp [r, τ₀, IsLocalization.lift_eq]
  letI inst : Fintype (D →ₐ[O] K) := Fintype.ofSurjective r hsurj
  refine ⟨inst, ?_⟩
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) K, ← hN, hE]
  exact Fintype.prod_bijective r ⟨hinj, hsurj⟩ _ _ (fun τ => rfl)

theorem UpperTheory.V.Alg.M.length_quotient_span_eq_finsum_valuation :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] (a : D), a ≠ 0 →
      Finite (D →ₐ[O] K) ∧ Module.length O (D ⧸ Ideal.span {a}) ≠ ⊤ ∧
      (((Module.length O (D ⧸ Ideal.span {a})).toNat : ℕ) : ℝ) = ∑ᶠ σ : D →ₐ[O] K, v (σ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv D _ _ _ _ _ a ha
  classical
  have : Module.Free O D := inferInstance
  obtain ⟨hF, hN⟩ := algebra_norm_eq_prod_embeddings (O := O) (K := K) a
  have hn : Algebra.norm O a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have hσ : ∀ σ : D →ₐ[O] K, σ a ≠ 0 := fun σ h => ha (algHom_finite_domain_injective σ (h.trans (map_zero _).symm))
  have h1 : v 1 = 0 := by
    have := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    linarith
  have hp : ∀ s : Finset (D →ₐ[O] K), v (∏ σ ∈ s, σ a) = ∑ σ ∈ s, v (σ a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert τ s hτ ih =>
      rw [Finset.prod_insert hτ, Finset.sum_insert hτ,
        hv.mul _ _ (hσ τ) (Finset.prod_ne_zero_iff.2 fun σ _ => hσ σ), ih]
  rw [length_quotient_eq_norm_valuation]
  refine ⟨inferInstance, fun h => hn (IsDiscreteValuationRing.addVal_eq_top_iff.1 h), ?_⟩
  rw [← hv.base _ hn, hN, hp, finsum_eq_sum_of_fintype]
end

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open UpperTheory.V.abelian₂ (invLen coinvLen snake_len)
open scoped Pointwise

private theorem ker_range {R : Type} [CommRing R] (g : R) (M : Type) [AddCommGroup M] [Module R M] :
    LinearMap.ker (LinearMap.lsmul R M g) = Submodule.torsionBy R M g ∧
      LinearMap.range (LinearMap.lsmul R M g) = g • (⊤ : Submodule R M) := by
  constructor
  · ext x; simp
  · ext x
    simp [Submodule.mem_smul_pointwise_iff_exists]

private theorem theta_eq {R : Type} [CommRing R] (g : R) (M : Type) [AddCommGroup M] [Module R M] :
    theta g M = ((coinvLen g M).toNat : ℤ) - ((invLen g M).toNat : ℤ) := by
  unfold theta
  rw [(ker_range g M).1, (ker_range g M).2]
  rfl

private theorem herbrand_finLen {R : Type} [CommRing R] (g : R) (M : Type) [AddCommGroup M] [Module R M]
    (h : Module.length R M ≠ ⊤) :
    invLen g M ≠ ⊤ ∧ coinvLen g M ≠ ⊤ ∧ coinvLen g M = invLen g M := by
  have h1 := KStar.Selmer.length_ker_eq_length_coker (LinearMap.lsmul R M g) h
  rw [(ker_range g M).1, (ker_range g M).2] at h1
  have h2 : invLen g M ≠ ⊤ :=
    ne_top_of_le_ne_top h (Module.length_le_of_injective _ (Submodule.injective_subtype _))
  have h3 : coinvLen g M = invLen g M := h1.symm
  exact ⟨h2, h3 ▸ h2, h3⟩

private theorem herbrand_equiv {R : Type} [CommRing R] (g : R) {M N : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    invLen g M = invLen g N ∧ coinvLen g M = coinvLen g N := by
  have key : ∀ {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N),
      invLen g M ≤ invLen g N ∧ coinvLen g N ≤ coinvLen g M := by
    intro M N _ _ _ _ e
    refine ⟨?_, ?_⟩
    · exact (snake_len R g M N PUnit e.toLinearMap 0 e.injective (fun _ => ⟨0, rfl⟩)
        (fun y => ⟨fun _ => e.surjective y, fun _ => rfl⟩)).2.2.2.1
    · exact (snake_len R g PUnit M N 0 e.toLinearMap (fun _ _ _ => rfl) e.surjective
        (fun y => ⟨fun h => ⟨0, (e.map_eq_zero_iff.1 h).symm⟩, by
          rintro ⟨_, rfl⟩; simp⟩)).2.2.2.2.1
  exact ⟨le_antisymm (key e).1 (key e.symm).1, le_antisymm (key e.symm).2 (key e).2⟩

private theorem loc_self {S : Type} [CommRing S] (P Q : Ideal S) [hP : P.IsPrime] (h : Q = P) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (S ⧸ Q)) = 1 := by
  subst h
  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  constructor
  · rw [← not_subsingleton_iff_nontrivial, LocalizedModule.subsingleton_iff]
    intro h
    obtain ⟨r, hr, hr'⟩ := h (Submodule.Quotient.mk 1)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hr'
    exact hr (by simpa using hr')
  · intro x hx y
    induction x using LocalizedModule.induction_on with | h m s => ?_
    induction y using LocalizedModule.induction_on with | h m' s' => ?_
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective Q m
    obtain ⟨r', rfl⟩ := Submodule.Quotient.mk_surjective Q m'
    have hr : r ∈ Q.primeCompl := fun hr => hx (by
      rw [(Submodule.Quotient.mk_eq_zero Q).2 hr, LocalizedModule.zero_mk])
    refine ⟨Localization.mk (r' * s) (⟨r, hr⟩ * s'), ?_⟩
    rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, ← Submodule.Quotient.mk_smul, smul_eq_mul, Submonoid.coe_mul]
    congr 1
    ring

private theorem loc_not_le {S : Type} [CommRing S] (P Q : Ideal S) [hP : P.IsPrime] (h : ¬ Q ≤ P) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (S ⧸ Q)) = 0 := by
  rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp h
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Q x
  refine ⟨s, hs', ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Q.mul_mem_right _ hs

private theorem len_eq (O : Type) [CommRing O] [IsLocalRing O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B]
    (X : Type) [AddCommGroup X] [Module O X] [Module B X] [IsScalarTower O B X] :
    Module.length O X = Module.length B X := by
  rw [IsLocalRing.length_restrictScalars O B X]
  have : Module.length (ResidueField O) (ResidueField B) = 1 := by
    rw [Module.length_eq_of_surjective (S := ResidueField O) (R := ResidueField B) (resMap_bijective O B).2]
    exact Module.length_eq_one _ _
  rw [this, mul_one]

private theorem prime_case (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ) (hv : IsNVal O K v)
    (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (P : Ideal B) [P.IsPrime] [Module.Finite O (B ⧸ P)]
    (a : B) (S : Finset (B →ₐ[O] K)) (hS : ∀ σ ∈ S, σ a ≠ 0) (hS' : ∀ σ : B →ₐ[O] K, σ ∉ S → locLen σ (B ⧸ P) = 0) :
    invLen a (B ⧸ P) ≠ ⊤ ∧ coinvLen a (B ⧸ P) ≠ ⊤ ∧
      ((coinvLen a (B ⧸ P)).toNat : ℝ) - ((invLen a (B ⧸ P)).toNat : ℝ) =
        ∑ σ ∈ S, ((locLen σ (B ⧸ P)).toNat : ℝ) * v (σ a) := by
  classical
  have h0 : ∀ σ : B →ₐ[O] K, ¬ P ≤ RingHom.ker σ → locLen σ (B ⧸ P) = 0 := fun σ h =>
    haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
    loc_not_le _ P h
  by_cases hinj : P.comap (algebraMap O B) = ⊥
  · haveI : FaithfulSMul O (B ⧸ P) := by
      rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
      intro c hc
      have : c ∈ P.comap (algebraMap O B) := by
        rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
        exact hc
      rwa [hinj] at this
    have hτ : ∀ τ : (B ⧸ P) →ₐ[O] K, Function.Injective τ := fun τ => by
      rw [RingHom.injective_iff_ker_eq_bot]
      refine Ideal.eq_bot_of_comap_eq_bot (R := O) ?_
      rw [eq_bot_iff]
      intro c hc
      have : τ (algebraMap O _ c) = 0 := hc
      rw [AlgHom.commutes] at this
      exact (FaithfulSMul.algebraMap_injective O K) (this.trans (map_zero _).symm)
    have h1 : ∀ τ : (B ⧸ P) →ₐ[O] K, locLen (τ.comp (Ideal.Quotient.mkₐ O P)) (B ⧸ P) = 1 := fun τ => by
      haveI : (RingHom.ker (τ.comp (Ideal.Quotient.mkₐ O P))).IsPrime := RingHom.ker_isPrime _
      refine loc_self _ P ?_
      ext x
      rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, AlgHom.comp_apply, map_eq_zero_iff _ (hτ τ)]
      rfl
    have hmem : ∀ τ : (B ⧸ P) →ₐ[O] K, τ.comp (Ideal.Quotient.mkₐ O P) ∈ S := fun τ => by
      by_contra h
      exact one_ne_zero ((h1 τ).symm.trans (hS' _ h))
    have ha : Ideal.Quotient.mk P a ≠ 0 := fun h =>
      hS _ (hmem (IsAlgClosed.lift (R := O) (S := B ⧸ P) (M := K))) (by
        rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, h, map_zero])
    obtain ⟨hf, hne, heq⟩ := length_quotient_span_eq_finsum_valuation O K v hv (B ⧸ P) _ ha
    have hi : invLen a (B ⧸ P) = 0 := by
      have : Submodule.torsionBy B (B ⧸ P) a = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : Ideal.Quotient.mk P a * x = 0 := (Submodule.mem_torsionBy_iff _ _).1 hx
        exact (mul_eq_zero.1 hx').resolve_left ha
      unfold invLen
      rw [this]
      exact Module.length_bot
    have hc : coinvLen a (B ⧸ P) = Module.length O ((B ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P a}) := by
      rw [len_eq O B]
      have : a • (⊤ : Submodule B (B ⧸ P)) = (Ideal.span {Ideal.Quotient.mk P a}).restrictScalars B := by
        ext x
        rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
        constructor
        · rintro ⟨b, -, rfl⟩
          exact ⟨b, mul_comm _ _⟩
        · rintro ⟨b, rfl⟩
          exact ⟨b, trivial, mul_comm (Ideal.Quotient.mk P a) b⟩
      exact ((Submodule.quotEquivOfEq _ _ this).trans (Submodule.Quotient.restrictScalarsEquiv B _)).length_eq
    refine ⟨by simp [hi], hc ▸ hne, ?_⟩
    haveI := Fintype.ofFinite ((B ⧸ P) →ₐ[O] K)
    rw [hi, hc, heq, finsum_eq_sum_of_fintype]
    simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero]
    refine Finset.sum_of_injOn (fun τ => τ.comp (Ideal.Quotient.mkₐ O P)) ?_ (fun τ _ => hmem τ) ?_ ?_
    · intro τ _ τ' _ h
      exact Ideal.Quotient.algHom_ext O h
    · intro σ _ hσ
      rw [h0 σ fun hle => hσ ⟨Ideal.Quotient.liftₐ P σ hle, by simp, by ext; rfl⟩]
      simp
    · intro τ _
      rw [h1]
      simp
  · have hmax : P.IsMaximal := by
      haveI : (P.comap (algebraMap O B)).IsMaximal :=
        Ring.DimensionLEOne.maximalOfPrime hinj (Ideal.comap_isPrime _ _)
      haveI : (Ideal.comap (algebraMap O (B ⧸ P)) ⊥).IsMaximal := by
        convert this using 1
        ext x
        rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_bot, ← Ideal.Quotient.eq_zero_iff_mem]
        rfl
      have := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) (⊥ : Ideal (B ⧸ P)) this
      exact Ideal.Quotient.maximal_of_isField _ (Ring.isField_iff_maximal_bot.2 this)
    haveI : IsSimpleModule B (B ⧸ P) := isSimpleModule_iff_quot_maximal.mpr ⟨P, hmax, ⟨LinearEquiv.refl _ _⟩⟩
    obtain ⟨h1, h2, h3⟩ := herbrand_finLen a (B ⧸ P) (by rw [Module.length_eq_one]; simp)
    refine ⟨h1, h2, ?_⟩
    rw [h3, sub_self]
    refine (Finset.sum_eq_zero fun σ _ => ?_).symm
    rw [h0 σ fun hle => hinj ?_]
    · simp
    · rw [eq_bot_iff]
      intro c hc
      have : σ (algebraMap O B c) = 0 := hle hc
      rw [AlgHom.commutes] at this
      exact (FaithfulSMul.algebraMap_injective O K) (this.trans (map_zero _).symm)

theorem UpperTheory.V.Alg.M.th_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (M : Type) [AddCommGroup M] [Module B M] [Module.Finite B M],
      Module.Finite O (B ⧸ Module.annihilator B M) → ∀ (a : B) (S : Finset (B →ₐ[O] K)) (c : ℕ),
      (∀ σ ∈ S, σ a ≠ 0 ∧ 0 ≤ v (σ a) ∧ locLen σ M ≤ c) → (∀ σ : B →ₐ[O] K, σ ∉ S → locLen σ M = 0) →
      (theta a M : ℝ) ≤ c * ∑ σ ∈ S, v (σ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv B _ _ _ M _ _ hM hfin a S c hS hS'
  have key : ∀ (I : Ideal B), Module.Finite O (B ⧸ I) → ∀ (N : Type) [AddCommGroup N] [Module B N]
      [hN : Module.Finite B N], I ≤ Module.annihilator B N → (∀ σ ∈ S, locLen σ N ≠ ⊤) →
      (∀ σ : B →ₐ[O] K, σ ∉ S → locLen σ N = 0) →
      invLen a N ≠ ⊤ ∧ coinvLen a N ≠ ⊤ ∧ ((coinvLen a N).toNat : ℝ) - ((invLen a N).toNat : ℝ) =
        ∑ σ ∈ S, ((locLen σ N).toNat : ℝ) * v (σ a) := by
    intro I hI N _ _ hN
    induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime B with
    | subsingleton N =>
      intro _ _ _
      obtain ⟨h1, h2, h3⟩ := herbrand_finLen a N (by simp)
      refine ⟨h1, h2, ?_⟩
      rw [h3, sub_self]
      refine (Finset.sum_eq_zero fun σ _ => ?_).symm
      have : locLen σ N = 0 := by
        unfold locLen
        exact Module.length_eq_zero
      simp [this]
    | quotient N p e =>
      intro hle _ h0
      have hl : ∀ σ : B →ₐ[O] K, locLen σ N = locLen σ (B ⧸ p.1) := fun σ =>
        GlobalTheory.length_localizedModule_congr _ e
      have hle' : I ≤ p.1 := by
        rw [e.annihilator_eq, Ideal.annihilator_quotient] at hle
        exact hle
      haveI : Module.Finite O (B ⧸ p.1) :=
        Module.Finite.of_surjective (Ideal.Quotient.factorₐ O hle').toLinearMap (Ideal.Quotient.factor_surjective hle')
      rw [(herbrand_equiv a e).1, (herbrand_equiv a e).2]
      simp only [hl] at h0 ⊢
      exact prime_case O K v hv B p.1 a S (fun σ h => (hS σ h).1) h0
    | exact N₁ N₂ N₃ f g hf hg hfg ih₁ ih₃ =>
      intro hle ht h0
      have hl : ∀ σ : B →ₐ[O] K, locLen σ N₂ = locLen σ N₁ + locLen σ N₃ := fun σ =>
        GlobalTheory.length_localizedModule_eq_add_of_exact _ f g hf hg hfg
      have ht1 : ∀ σ ∈ S, locLen σ N₁ ≠ ⊤ := fun σ h h' => ht σ h (by rw [hl, h', top_add])
      have ht3 : ∀ σ ∈ S, locLen σ N₃ ≠ ⊤ := fun σ h h' => ht σ h (by rw [hl, h', add_top])
      obtain ⟨a1, b1, c1⟩ := ih₁ (hle.trans (f.annihilator_le_of_injective hf)) ht1
        fun σ h => (add_eq_zero.1 ((hl σ).symm.trans (h0 σ h))).1
      obtain ⟨a3, b3, c3⟩ := ih₃ (hle.trans (g.annihilator_le_of_surjective hg)) ht3
        fun σ h => (add_eq_zero.1 ((hl σ).symm.trans (h0 σ h))).2
      obtain ⟨s1, s2, s3, -⟩ := snake_len B a N₁ N₂ N₃ f g hf hg hfg
      have a2 : invLen a N₂ ≠ ⊤ := ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨a1, a3⟩) s2
      have b2 : coinvLen a N₂ ≠ ⊤ := ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨b1, b3⟩) s3
      refine ⟨a2, b2, ?_⟩
      have s := congrArg (fun x : ℕ∞ => (x.toNat : ℝ)) s1
      have t1 : invLen a N₁ + invLen a N₃ ≠ ⊤ := WithTop.add_ne_top.2 ⟨a1, a3⟩
      have t2 : invLen a N₂ + coinvLen a N₁ ≠ ⊤ := WithTop.add_ne_top.2 ⟨a2, b1⟩
      rw [ENat.toNat_add t1 b2, ENat.toNat_add a1 a3, ENat.toNat_add t2 b3, ENat.toNat_add a2 b1] at s
      push_cast at s
      have : ∑ σ ∈ S, ((locLen σ N₂).toNat : ℝ) * v (σ a) =
          ∑ σ ∈ S, ((locLen σ N₁).toNat : ℝ) * v (σ a) + ∑ σ ∈ S, ((locLen σ N₃).toNat : ℝ) * v (σ a) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun σ h => ?_
        rw [hl, ENat.toNat_add (ht1 σ h) (ht3 σ h)]
        push_cast
        ring
      linarith
  obtain ⟨-, -, h⟩ := key _ hfin M le_rfl
    (fun σ h => ne_top_of_le_ne_top (ENat.coe_ne_top c) (hS σ h).2.2) hS'
  rw [theta_eq]
  push_cast
  rw [h, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ h => mul_le_mul_of_nonneg_right ?_ (hS σ h).2.1
  exact_mod_cast ENat.toNat_le_of_le_coe (hS σ h).2.2
end

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.up_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    SpansCot x 𝒜 (-1) Q.F → SpansCot x 𝒜 (-2) Q.G → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal → M4 𝒜 K Q.ideal →
    ∀ a : 𝒜 0, M5 𝒜 K x Q.ideal a → ∀ T : Finset (A →ₐ[O] K), Covers 𝒜 Q.ideal T →
    ∀ J : Ideal (mR Q), (GMod.self (mGr Q)).IsHomSub J → secs (ts Q) ≤ J → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ J) →
      ∀ᶠ d in atTop, (chi [(0, algebraMap (𝒜 0) (mR Q) a)] (mQ Q J) d : ℝ) ≤ 2 ^ (r + 1 + r') * ∑ ξ ∈ T, v (ξ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv A _ _ 𝒜 _ _ x hW r s r' s' m Q hF hG h2 h3 h4 a h5 T hT J hJ hsec hZ
  classical
  have hfg := fg_holds O A 𝒜 x hW
  have hN : ∀ i, (mN 𝒜 (Q.F (Fin.last r)) i).FG := by
    intro i
    fin_cases i
    · exact hfg _
    · exact hfg _
    · exact (Submodule.fg_span_singleton _).sup (((hfg _).mul (hfg _)).mul (hfg _))
  let X : HidaSetting 3 := { B := 𝒜 0, R := mR Q, 𝒜 := mGr Q, std := std_holds (𝒜 0) A 3 _ hN }
  have hself : (GMod.self (mGr Q)).IsGr (mGr Q) :=
    ⟨fun {d e} {p} {q : mR Q} (hp : p ∈ mGr Q d) (hq : q ∈ mGr Q e) => (SetLike.mul_mem_graded hp hq : p * q ∈ mGr Q (d + e)),
      rees_internal _, Module.Finite.self (mR Q)⟩
  have hGr : (mQ Q J).IsGr (mGr Q) := ((ruleGr 3 X _ hself).1 J hJ).2
  have hfin : ∀ d, Module.Finite (𝒜 0) ((mQ Q J).gr d) := (ruleFin 3 X _ hGr).1
  obtain ⟨hI, -, -⟩ := hom_holds O A 𝒜 x hW r s r' s' m Q
  have hD : ∀ ξ : A →ₐ[O] K, TwoSigned 𝒜 ξ ↔ ¬ idD 𝒜 ≤ RingHom.ker (res0 𝒜 ξ) := by
    intro ξ
    obtain ⟨hn, hp⟩ := sign_holds O A 𝒜 x hW K ξ
    rw [TwoSigned, hn, hp]
    constructor
    · rintro ⟨⟨f, hf, hf0⟩, g, hg, hg0⟩ hle
      have hm : f * g ∈ 𝒜 0 := by
        have := SetLike.GradedMul.mul_mem hf hg
        simpa using this
      have h1 : (⟨f * g, hm⟩ : 𝒜 0) ∈ idD 𝒜 := Ideal.subset_span ⟨f, hf, g, hg, rfl⟩
      have h2 : ξ (f * g) = 0 := hle h1
      rw [map_mul] at h2
      exact mul_ne_zero hf0 hg0 h2
    · intro h
      by_contra hc
      refine h (Ideal.span_le.2 ?_)
      rintro b ⟨f, hf, g, hg, hb⟩
      show ξ (b : A) = 0
      rw [hb, map_mul]
      by_contra hne
      exact hc ⟨⟨f, hf, left_ne_zero_of_mul hne⟩, g, hg, right_ne_zero_of_mul hne⟩
  have hpos : ∀ ξ ∈ T, ξ a ≠ 0 ∧ 0 ≤ v (ξ a) := fun ξ hξ =>
    ⟨h5.2.2 ξ (hT.1 ξ hξ).1 (hT.1 ξ hξ).2,
      valuation_nonneg_apply_degreeZero_of_onS O K v hv A 𝒜 x Q.ideal h2 ξ (hT.1 ξ hξ).1 a a.2 (h5.2.2 ξ (hT.1 ξ hξ).1 (hT.1 ξ hξ).2)⟩
  have hsum : ∑ σ ∈ T.image (res0 𝒜), v (σ a) ≤ ∑ ξ ∈ T, v (ξ a) :=
    Finset.sum_image_le_of_nonneg (f := fun σ : 𝒜 0 →ₐ[O] K => v (σ a)) (g := res0 𝒜) (s := T) fun σ hσ => by
      obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 hσ
      exact (hpos ξ hξ).2
  filter_upwards [eventually_mQ_gr_finite_annihilator O K A 𝒜 x hW r s r' s' m Q hF hG h2 h3 J hJ hsec hZ, eventually_ge_atTop 1] with d hd hd1
  haveI := hfin d
  have key := th_holds O K v hv (𝒜 0) ((mQ Q J).gr d) hd.1 a (T.image (res0 𝒜)) (2 ^ (r + 1 + r')) ?_ ?_
  · rw [chi_single0 _ hGr.internal]
    refine key.trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  · intro σ hσ
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 hσ
    refine ⟨(hpos ξ hξ).1, (hpos ξ hξ).2, ?_⟩
    have hσ' := (hD ξ).1 (hT.1 ξ hξ).2
    refine (locLen_mQ_gr_le_locLen_aPiece O K A 𝒜 x hW r s r' s' m Q J hsec hZ _ hσ' d hd1).trans ?_
    push_cast
    exact locLen_aPiece_ideal2_le_two_pow O K A 𝒜 x hW r s r' s' m Q _ (locLen_quotientWeightPiece_le_one O K A 𝒜 x hW _ hI h2 h4 _ hσ') _
  · intro σ hσ
    refine hd.2 σ ?_
    by_contra hc
    rw [not_or] at hc
    obtain ⟨ξ, hξ, rfl⟩ := tsp_holds O K A 𝒜 x hW _ hI σ fun b hb => by
      by_contra hne
      exact hc.2 ⟨b, hb, hne⟩
    obtain ⟨ξ', hξ', t, rfl⟩ := hT.2 ξ hξ ((hD ξ).2 hc.1)
    refine hσ (Finset.mem_image.2 ⟨ξ', hξ', AlgHom.ext fun b => ?_⟩)
    show ξ' (b : A) = act 𝒜 (tz t) ξ' (b : A)
    rw [act_of_mem 𝒜 _ _ b.2]
    simp
