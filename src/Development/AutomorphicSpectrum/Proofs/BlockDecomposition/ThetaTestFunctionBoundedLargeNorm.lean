module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleEqNormModule
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormula

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBoundedOnCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBoundedOnCompact
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.IdeleModBdd

theorem ideleModule_bounded_on_compact : ∀ (K : Type) [Field K] [NumberField K] (C : Set (AdeleRing (𝓞 K) K)), IsCompact C → ∃ R : ℝ, ∀ a : IdeleGroup K, (a : AdeleRing (𝓞 K) K) ∈ C → (IdeleGroup.ideleModule K a : ℝ) ≤ R := by
  intro K _ _ C hC
  let U : Finset (HeightOneSpectrum (𝓞 K)) → Set (AdeleRing (𝓞 K) K) := fun S =>
    {x | ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers K}
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v : HeightOneSpectrum (𝓞 K) => v ∉ S)).preimage continuous_snd
  have hcov : C ⊆ ⋃ S, U S := by
    intro x _
    have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ x.2 v ∈ v.adicCompletionIntegers K}.Finite :=
      Filter.eventually_cofinite.1 x.2.2
    exact Set.mem_iUnion.2 ⟨hfin.toFinset, fun v hv => by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)⟩
  have hdir : Directed (· ⊆ ·) U := fun S T =>
    ⟨S ∪ T, fun x hx v hv => hx v fun h => hv (Finset.mem_union_left _ h),
      fun x hx v hv => hx v fun h => hv (Finset.mem_union_right _ h)⟩
  obtain ⟨S, hS⟩ := hC.elim_directed_cover U hUo hcov hdir
  have hfinB : ∀ v : HeightOneSpectrum (𝓞 K), ∃ B : ℝ, ∀ x ∈ C, ‖x.2 v‖ ≤ B := fun v => by
    have hc : Continuous fun x : AdeleRing (𝓞 K) K => ‖x.2 v‖ :=
      continuous_norm.comp ((RestrictedProduct.continuous_eval v).comp continuous_snd)
    obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  have hinfB : ∀ w : InfinitePlace K, ∃ B : ℝ, ∀ x ∈ C, ‖x.1 w‖ ≤ B := fun w => by
    have hc : Continuous fun x : AdeleRing (𝓞 K) K => ‖x.1 w‖ :=
      continuous_norm.comp ((continuous_apply w).comp continuous_fst)
    obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  choose Bf hBf using hfinB
  choose Bi hBi using hinfB
  refine ⟨(∏ w : InfinitePlace K, max (Bi w) 0 ^ w.mult) * ∏ v ∈ S, max (Bf v) 1, ?_⟩
  intro a ha
  rw [IdeleGroup.ideleModule_eq]
  have h1 : ∏ w : InfinitePlace K, ‖(a : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult ≤
      ∏ w : InfinitePlace K, max (Bi w) 0 ^ w.mult :=
    Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ =>
      pow_le_pow_left₀ (norm_nonneg _) ((hBi w _ ha).trans (le_max_left _ _)) _
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(a : AdeleRing (𝓞 K) K).2 v‖ ≤
      ∏ v ∈ S, max (Bf v) 1 := by
    have hfs := IdeleGroup.finite_mulSupport_norm a
    have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
        ‖(a : AdeleRing (𝓞 K) K).2 v‖) ⊆ ((hfs.toFinset ∪ S : Finset _) : Set _) := fun v hv => by
      simp only [Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inl hv
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    calc ∏ v ∈ hfs.toFinset ∪ S, ‖(a : AdeleRing (𝓞 K) K).2 v‖
        ≤ ∏ v ∈ hfs.toFinset ∪ S, (if v ∈ S then max (Bf v) 1 else 1) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
          split_ifs with hv
          · exact (hBf v _ ha).trans (le_max_left _ _)
          · exact (Valued.toNormedField.norm_le_one_iff).2
              ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 (hS ha v hv))
      _ = ∏ v ∈ S, (if v ∈ S then max (Bf v) 1 else 1) :=
          (Finset.prod_subset Finset.subset_union_right fun v _ hv => if_neg hv).symm
      _ = ∏ v ∈ S, max (Bf v) 1 := Finset.prod_congr rfl fun v hv => if_pos hv
  exact mul_le_mul h1 h2 (IdeleGroup.finiteModule_pos a).le
    (Finset.prod_nonneg fun _ _ => by positivity)

end GlobalTheory.CompanionTheory.IdeleModBdd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBoundedOnCompactStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_module_bounded_on_compact : ∀ (K : Type) [Field K] [NumberField K] (C : Set (AdeleRing (𝓞 K) K)), IsCompact C → ∃ R : ℝ, ∀ a : IdeleGroup K, (a : AdeleRing (𝓞 K) K) ∈ C → (IdeleGroup.ideleModule K a : ℝ) ≤ R := by
  first | exact @GlobalTheory.CompanionTheory.IdeleModBdd.ideleModule_bounded_on_compact | exact GlobalTheory.CompanionTheory.IdeleModBdd.ideleModule_bounded_on_compact | (intros; apply GlobalTheory.CompanionTheory.IdeleModBdd.ideleModule_bounded_on_compact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionBoundedLargeNorm
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish

open GlobalTheory.CompanionTheory.SW.WBox (cK)

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem cK_tmul_mul (r : R) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((r ⊗ₜ[F] (1 : E)) * y) k = r * cK R b y k := by
  have e : (r ⊗ₜ[F] (1 : E)) * y = r • y := by
    rw [Algebra.smul_def]
    rfl
  simp [cK, e]

theorem cK_nat_mul (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((N : R ⊗[F] E) * y) k = (N : R) * cK R b y k := by
  have e : (N : R ⊗[F] E) = (N : R) ⊗ₜ[F] (1 : E) := by
    exact (map_natCast (algebraMap R (R ⊗[F] E)) N).symm
  rw [e, cK_tmul_mul]

end Coord

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem scale_one (v : HeightOneSpectrum (𝓞 F)) (Q : Set (Fv F v)) (hQ : IsCompact Q) :
    ∃ N : ℕ, 0 < N ∧ ∀ t ∈ Q, (N : Fv F v) * t ∈ v.adicCompletionIntegers F := _root_.GlobalTheory.CompanionTheory.SW.LS.scale_one v Q hQ

theorem scale_lat [NumberField E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (K : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ Y ∈ K, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := by
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hh := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.1 d b
  have hc : ∀ q : Fin 1 × Fin 1 × Fin d, Continuous fun Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E => cK (Fv F v) b (Y q.1 q.2.1) q.2.2 :=
    fun q => (continuous_apply q.2.2).comp (hh.continuous.comp (continuous_apply_apply q.1 q.2.1))
  choose n hn0 hn using fun q => scale_one v _ (hK.image (hc q))
  refine ⟨∏ q, n q, Finset.prod_pos fun q _ => hn0 q, fun Y hY a i k => ?_⟩
  change cK (Fv F v) b (((∏ q, n q : ℕ) : Fv F v ⊗[F] E) * Y a i) k ∈ _
  rw [cK_nat_mul]
  obtain ⟨c, hc'⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (a, i, k))
  rw [hc']
  have h1 := hn (a, i, k) _ ⟨Y, hY, rfl⟩
  have e : ((n (a, i, k) * c : ℕ) : Fv F v) * cK (Fv F v) b (Y a i) k =
      (c : Fv F v) * ((n (a, i, k) : Fv F v) * cK (Fv F v) b (Y a i) k) := by
    push_cast; ring
  rw [e]
  exact mul_mem (natCast_mem _ c) h1

theorem nat_mul_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    {Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E} (hY : Y ∈ latV b v) :
    (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := fun a i k => by
  change cK (Fv F v) b ((N : Fv F v ⊗[F] E) * Y a i) k ∈ _
  rw [cK_nat_mul]
  exact mul_mem (natCast_mem _ N) (hY a i k)

end Scale

theorem exists_compact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (hT : IsTest σ J b S φ A) :
    ∃ K : Set (Fin 1 → Fin 1 → AF F ⊗[F] E), IsCompact K ∧
      ∀ Y : Fin 1 → Fin 1 → AF F ⊗[F] E, (∀ v, projV v (projFin Y) ∈ A v) → projInf Y ∈ tsupport φ → Y ∈ K := by
  obtain ⟨hφc, hφs, hφ0, -, hAS, hAoff⟩ := hT
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1
  obtain ⟨u1, u2⟩ := GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm d b 1 1
  have hSc : ∀ v, ∃ N : ℕ, 0 < N ∧ (v ∈ S → ∀ Y ∈ A v, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v) := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨N, h0, h1⟩ := scale_lat σ hcm b v (A v) (hAS v hv).1
      exact ⟨N, h0, fun _ => h1⟩
    · exact ⟨1, one_pos, fun h => absurd h hv⟩
  choose n hn0 hn using hSc
  set N1 : ℕ := ∏ v ∈ S, n v with hN1
  have hN1p : 0 < N1 := Finset.prod_pos fun v _ => hn0 v
  have hsc : ∀ v, ∀ Y ∈ A v, (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := fun v Y hY => by
    by_cases hv : v ∈ S
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n hv
      have h1 := nat_mul_latV b v c (hn v hv Y hY)
      have e : (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) = fun a i => (c : Fv F v ⊗[F] E) * ((n v : Fv F v ⊗[F] E) * Y a i) := by
        funext a i
        rw [hN1, hc]
        push_cast
        ring
      rw [e]
      exact h1
    · rw [hAoff v hv] at hY
      exact nat_mul_latV b v N1 hY
  obtain ⟨r1, hr1⟩ := (IsCompact.image hφs t9).bddAbove
  refine ⟨_, u1 N1 r1 hN1p, fun Y hY hs => ⟨fun v => hsc v _ (hY v), hr1 ⟨_, hs, rfl⟩⟩⟩

theorem mem_of_Psi_ne {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) (h : Psi φ A Y ≠ 0) :
    (∀ v, projV v (projFin Y) ∈ A v) ∧ projInf Y ∈ tsupport φ := by
  unfold Psi at h
  by_cases h1 : ∀ v, projV v (projFin Y) ∈ A v
  · refine ⟨h1, subset_tsupport φ ?_⟩
    rw [Set.indicator_of_mem (by exact h1)] at h
    intro h2
    exact h (by simp [h2])
  · rw [Set.indicator_of_notMem (by exact h1)] at h
    exact absurd rfl h

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cont_f : Continuous fun Y : Fin 1 → Fin 1 → AF F ⊗[F] E => GroundTheory.BlockD.ThmBHecke.adeleEquiv F E (Y 0 0) :=
    GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp (continuous_apply_apply 0 0)

theorem hdiag (t : Eˣ) : GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofE t) = IdeleGroup.diagonal E t := by
    apply Units.ext
    exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA (t : E)

theorem mod_mul (y : (AF F ⊗[F] E)ˣ) (t : Eˣ) : (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE t)) : ℝ) = (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E y) : ℝ) := by
  rw [map_mul, map_mul, hdiag, IdeleGroup.ideleModule_diagonal, mul_one]

theorem exists_term (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (y : (AF F ⊗[F] E)ˣ)
    (h : Th φ A y ≠ 0) : ∃ X : Fin 1 → Fin 1 → E, X ≠ 0 ∧
      Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 := by
  unfold Th at h
  obtain ⟨X, hX⟩ := not_forall.1 (fun hall => h (ENNReal.tsum_eq_zero.2 hall))
  exact ⟨X.1, X.2, hX⟩

theorem entry_ne {X : Fin 1 → Fin 1 → E} (h : X ≠ 0) : X 0 0 ≠ 0 := fun h0 => h (by
  funext a i
  rw [Subsingleton.elim a 0, Subsingleton.elim i 0, h0]
  rfl)

theorem coe_eq (y : (AF F ⊗[F] E)ˣ) {X : Fin 1 → Fin 1 → E} (h : X 0 0 ≠ 0) :
    ((GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE (Units.mk0 _ h)) : IdeleGroup E) : AdeleRing (𝓞 E) E) =
      GroundTheory.BlockD.ThmBHecke.adeleEquiv F E ((y : AF F ⊗[F] E) * inclR (AF F) (X 0 0)) := rfl
end

theorem th_eq_zero_of_large_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∃ R : ℝ, ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → R < md n → Th φ A y = 0 := by
  intro F E _ _ _ _ _ σ hcm J hJ d b S φ A hT
  obtain ⟨K, hK, hmem⟩ := exists_compact σ hcm J b S φ A hT
  obtain ⟨R, hR⟩ := GlobalTheory.T.idele_module_bounded_on_compact E _ (hK.image (cont_f (F := F) (E := E)))
  refine ⟨R, fun y n hn hlt => ?_⟩
  by_contra hne
  obtain ⟨X, hX0, hX⟩ := exists_term φ A y hne
  obtain ⟨h1, h2⟩ := mem_of_Psi_ne φ A _ hX
  have hYK := hmem _ h1 h2
  have ht := entry_ne hX0
  have hle := hR (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE (Units.mk0 _ ht)))
    (by rw [coe_eq]; exact ⟨_, hYK, rfl⟩)
  rw [mod_mul, GlobalTheory.T.idele_module_eq_norm_module F E σ hcm y n hn] at hle
  exact absurd hle (not_le.2 hlt)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionBoundedLargeNormStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_test_function_bounded_large_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∃ R : ℝ, ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → R < md n → Th φ A y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish.th_eq_zero_of_large_module | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish.th_eq_zero_of_large_module | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish.th_eq_zero_of_large_module <;> assumption)
end
