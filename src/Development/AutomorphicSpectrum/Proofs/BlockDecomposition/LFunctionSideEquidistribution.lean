module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionBoundedLargeNorm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayLimit

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleClassCompactRayDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleClassCompactRayDecomposition
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem isNm_ofF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (u : (AF F)ˣ) : IsNm σ (ofF u : (AF F ⊗[F] E)ˣ) (u * u) := by
  unfold IsNm
  have hs : sigR (AF F) σ ((u : AF F) ⊗ₜ[F] (1 : E)) = (u : AF F) ⊗ₜ[F] (1 : E) := by
    simp [sigR]
  have e : ((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (u : AF F) ⊗ₜ[F] (1 : E) := rfl
  rw [e, hs, Units.val_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem ideleEquiv_ofE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : Eˣ) :
    GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofE t) = IdeleGroup.diagonal E t := by
  apply Units.ext
  rw [GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv]
  exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA (t : E)

theorem exists_unit_decomp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (θ : ℝ →+* Ainf F) (hθ : Continuous θ)
    (r : ℝ → (AF F)ˣ) (hr : IsRay θ r) :
    ∃ K : Set (AF F ⊗[F] E)ˣ, IsCompact K ∧ ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n →
      ∃ (q : Eˣ) (k : (AF F ⊗[F] E)ˣ) (ε : ℝ), k ∈ K ∧ 0 < ε ∧ y = ofE q * (k * ofF (r ε)) ∧
        md n = ε ^ (2 * Module.finrank ℚ F) := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  refine ⟨(GroundTheory.BlockD.ThmBHecke.ideleEquiv F E).symm '' D,
    hD.image GroundTheory.BlockD.ThmBHecke.continuous_ideleEquiv_symm, fun y n hyn => ?_⟩
  have hd : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hm : 2 * Module.finrank ℚ F ≠ 0 := by omega
  have hn : 0 < md n := (IdeleGroup.ideleModule F n).2
  set m := 2 * Module.finrank ℚ F with hmdef
  set ε : ℝ := md n ^ ((m : ℝ)⁻¹) with hεdef
  have hε : 0 < ε := Real.rpow_pos_of_pos hn _
  have hεm : md n = ε ^ m := (Real.rpow_inv_natCast_pow hn.le hm).symm
  have hray : md (r ε * r ε) = ε ^ m := by
    have h1 := ((GlobalTheory.T.ray_norm_and_module_formula F hcm.1 θ hθ r hr).2 ε hε)
    have h2 : md (r ε * r ε) = md (r ε) * md (r ε) := by simp [md, map_mul]
    rw [h2, h1, hmdef, two_mul, pow_add]
  have hy := GlobalTheory.T.idele_module_eq_norm_module F E σ hcm y n hyn
  have hu := GlobalTheory.T.idele_module_eq_norm_module F E σ hcm (ofF (r ε)) (r ε * r ε) (isNm_ofF σ (r ε))
  set I := GroundTheory.BlockD.ThmBHecke.ideleEquiv F E with hI
  have hker : I (y * (ofF (r ε))⁻¹) ∈ IdeleGroup.normOneSubgroup E := by
    refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
    have hpos : (0 : ℝ) < ε ^ m := pow_pos hε m
    rw [map_mul, map_inv, map_mul, map_inv]
    change ((IdeleGroup.ideleModule E (I y) : ℝ)) *
      ((IdeleGroup.ideleModule E (I (ofF (r ε))) : ℝ))⁻¹ = 1
    rw [hy, hu, hray, hεm]
    exact mul_inv_cancel₀ hpos.ne'
  obtain ⟨t, ht⟩ := hxD _ hker
  refine ⟨t⁻¹, I.symm (IdeleGroup.diagonal E t * I (y * (ofF (r ε))⁻¹)), ε, ⟨_, ht, rfl⟩, hε, ?_, hεm⟩
  apply I.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hI, ideleEquiv_ofE, map_inv, ← hI, map_mul, map_inv]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleClassCompactRayDecompositionStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_class_compact_ray_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∃ K : Set (AF F ⊗[F] E)ˣ, IsCompact K ∧ ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → ∃ (q : Eˣ) (k : (AF F ⊗[F] E)ˣ) (ε : ℝ), k ∈ K ∧ 0 < ε ∧ y = ofE q * (k * ofF (r ε)) ∧ md n = ε ^ (2 * Module.finrank ℚ F) := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.exists_unit_decomp | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.exists_unit_decomp | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.exists_unit_decomp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionRayAsymptotic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionRayAsymptotic
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box

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

theorem cK_incl (e : E) (k : Fin d) : cK R b (inclR R e) k = algebraMap F R (b.repr e k) := by
  simp [cK, inclR, Algebra.TensorProduct.basis_repr_tmul, Algebra.algebraMap_eq_smul_one]

end Coord

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem scale_one (v : HeightOneSpectrum (𝓞 F)) (Q : Set (Fv F v)) (hQ : IsCompact Q) :
    ∃ N : ℕ, 0 < N ∧ ∀ t ∈ Q, (N : Fv F v) * t ∈ v.adicCompletionIntegers F := by
  set p : ℕ := Ideal.absNorm v.asIdeal with hp
  have hp0 : 0 < p := Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hp1 : Valued.v (p : Fv F v) < 1 := by
    have h1 : ((p : 𝓞 F)) ∈ v.asIdeal := by
      simpa [hp] using Ideal.absNorm_mem v.asIdeal
    have h2 := (v.valuation_lt_one_iff_mem (K := F) (p : 𝓞 F)).2 h1
    have h3 : (p : Fv F v) = algebraMap (𝓞 F) (Fv F v) (p : 𝓞 F) := (map_natCast _ p).symm
    rw [h3]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (p : 𝓞 F)).trans_lt h2
  have hO : IsOpen {t : Fv F v | Valued.v t ≤ 1} := Valued.isOpen_integer (Fv F v)
  have hopen : ∀ k : ℕ, IsOpen {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1} := fun k =>
    hO.preimage (continuous_const.mul continuous_id)
  obtain ⟨k, hk⟩ := hQ.elim_directed_cover (fun k : ℕ => {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1}) hopen
    (fun t _ => by
      by_cases ht : t = 0
      · exact Set.mem_iUnion.2 ⟨0, by simp [ht]⟩
      · have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
        obtain ⟨n, hn⟩ := exists_pow_lt₀ hp1 (Units.mk0 _ (inv_ne_zero hvt))
        refine Set.mem_iUnion.2 ⟨n, ?_⟩
        simp only [Set.mem_ofPred_eq, map_mul, map_pow]
        exact (mul_le_mul' hn.le le_rfl).trans (inv_mul_cancel₀ hvt).le)
    (directed_of_isDirected_le fun i j hij t ht => by
      simp only [Set.mem_ofPred_eq] at ht ⊢
      rw [← Nat.sub_add_cancel hij, pow_add, mul_assoc, map_mul, map_pow]
      exact mul_le_one' (pow_le_one' hp1.le _) ht)
  exact ⟨p ^ k, pow_pos hp0 k, fun t ht => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by
    rw [Nat.cast_pow]
    exact hk ht)⟩

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

theorem ofF_mul_incl (u : (AF F)ˣ) (e : E) :
    ((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) e = (u : AF F) ⊗ₜ[F] e := by
  change ((u : AF F) ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] e) = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem projV_ofF (u : (AF F)ˣ) (hu : (u : AF F).2 = 1) (v : HeightOneSpectrum (𝓞 F)) (X : Fin 1 → Fin 1 → E) :
    projV v (projFin fun a i => ((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) =
      ratTup (Fv F v) X := by
  funext a i
  have h1 : sndA F (u : AF F) = 1 := hu
  change Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
    (((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i))) = (1 : Fv F v) ⊗ₜ[F] X a i
  rw [ofF_mul_incl]
  simp only [Algebra.TensorProduct.map_tmul, h1, map_one, AlgHom.id_apply]

theorem projInf_ofF (u : (AF F)ˣ) (t : Ainf F) (hu : (u : AF F).1 = t) (X : Fin 1 → Fin 1 → E) :
    projInf (fun a i => ((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) =
      fun a i => (t ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i := by
  funext a i
  have h1 : fstA F (u : AF F) = t := hu
  change Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)
    (((ofF u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) = (t ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] X a i)
  rw [ofF_mul_incl]
  simp [Algebra.TensorProduct.map_tmul, h1, Algebra.TensorProduct.tmul_mul_tmul]

end Scale

theorem unit_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∃ (N : ℕ) (ρ : ℝ), 0 < N ∧ ∀ k ∈ K, ∀ (X : Fin 1 → Fin 1 → E) (ε : ℝ), 0 < ε → Psi φ A (fun a i => ((k * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 → (∀ (p : Fin 1 × Fin 1 × Fin d) (v : HeightOneSpectrum (𝓞 F)), algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧ ∀ (p : Fin 1 × Fin 1 × Fin d) (w : InfinitePlace F), ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ ρ := by
  intro F E _ _ _ _ _ σ hcm J hJ d b θ r hray S φ A hT K hK
  obtain ⟨hφc, hφs, hφ0, -, hAS, hAoff⟩ := hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
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
  have hK1 := u1 N1 r1 hN1p
  set K1 := {X : Fin 1 → Fin 1 → AF F ⊗[F] E | (∀ v, (fun a i => (N1 : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧
    sizeTup b (projInf X) ≤ r1} with hK1d
  have hcont : Continuous (fun q : (AF F ⊗[F] E)ˣ × (Fin 1 → Fin 1 → AF F ⊗[F] E) =>
      (fun a i => (q.1 : AF F ⊗[F] E) * q.2 a i : Fin 1 → Fin 1 → AF F ⊗[F] E)) :=
    continuous_pi fun a => continuous_pi fun i =>
      (Units.continuous_val.comp continuous_fst).mul ((continuous_apply_apply a i).comp continuous_snd)
  have hK2 : IsCompact ((fun q : (AF F ⊗[F] E)ˣ × (Fin 1 → Fin 1 → AF F ⊗[F] E) =>
      (fun a i => (q.1 : AF F ⊗[F] E) * q.2 a i : Fin 1 → Fin 1 → AF F ⊗[F] E)) '' ((Inv.inv '' K) ×ˢ K1)) :=
    ((hK.image continuous_inv).prod hK1).image hcont
  obtain ⟨N, ρ, hN, hρ, hsub⟩ := u2 _ hK2
  refine ⟨N, N * ρ, hN, fun k hk X ε hε hne => ?_⟩
  set Y : Fin 1 → Fin 1 → AF F ⊗[F] E := fun a i =>
    ((k * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i) with hY
  have hmem : (∀ v, projV v (projFin Y) ∈ A v) ∧ φ (projInf Y) ≠ 0 := by
    by_contra hcon
    apply hne
    unfold Psi
    by_cases h1 : ∀ v, projV v (projFin Y) ∈ A v
    · rw [Set.indicator_of_mem (by exact h1)]
      have h2 : φ (projInf Y) = 0 := by
        by_contra h2
        exact hcon ⟨h1, h2⟩
      simp [h2]
    · rw [Set.indicator_of_notMem (by exact h1)]
  obtain ⟨hmv, hφne⟩ := hmem
  have hYK : Y ∈ K1 := ⟨fun v => hsc v _ (hmv v), hr1 ⟨_, subset_tsupport φ hφne, rfl⟩⟩
  set W : Fin 1 → Fin 1 → AF F ⊗[F] E := fun a i =>
    ((ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i) with hW
  have hWY : (fun a i => ((k⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * Y a i) = W := by
    funext a i
    simp only [hY, hW, Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨hW1, hW2⟩ := hsub W ⟨(k⁻¹, Y), ⟨⟨k, hk, rfl⟩, hYK⟩, hWY⟩
  obtain ⟨hr1', hr2'⟩ := hray ε hε
  have hWv : ∀ v, projV v (projFin W) = ratTup (Fv F v) X := fun v => projV_ofF _ hr2' v X
  have hWinf : projInf W = fun a i => (θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i := projInf_ofF _ _ hr1' X
  simp only [hWv, hWinf] at hW1 hW2
  refine ⟨fun q v => ?_, fun q w => ?_⟩
  · have h1 := hW1 v q.1 q.2.1 q.2.2
    change cK (Fv F v) b ((N : Fv F v ⊗[F] E) * ratTup (Fv F v) X q.1 q.2.1) q.2.2 ∈ _ at h1
    rw [cK_nat_mul, ratTup, cK_incl] at h1
    rwa [map_mul, map_natCast]
  · have e1 : θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X q.1 q.2.1) q.2.2) =
        N • (θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) := by
      rw [map_mul, map_natCast, nsmul_eq_mul]
      ring
    set D : Fin 1 → Fin 1 → Ainf F ⊗[F] E := fun a i => (θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X a i with hD
    have h2 : ‖(θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) w‖ ≤ ρ := by
      refine le_trans ?_ hW2
      have e2 : (Algebra.TensorProduct.basis (Ainf F) b).repr (D q.1 q.2.1) q.2.2 =
          θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2) := by
        change cK (Ainf F) b ((θ ε ⊗ₜ[F] (1 : E)) * ratTup (Ainf F) X q.1 q.2.1) q.2.2 = _
        rw [cK_tmul_mul, ratTup, cK_incl]
      rw [← e2, sizeTup]
      have n0 : ∀ (y : Ainf F ⊗[F] E), 0 ≤ sizeInf b y := fun y =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc _ ≤ ∑ v : InfinitePlace F, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (D q.1 q.2.1) q.2.2 v‖ :=
            Finset.single_le_sum (f := fun v : InfinitePlace F => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (D q.1 q.2.1) q.2.2 v‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
        _ ≤ sizeInf b (D q.1 q.2.1) :=
            Finset.single_le_sum (f := fun k => ∑ v : InfinitePlace F, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (D q.1 q.2.1) k v‖)
              (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ q.2.2)
        _ ≤ ∑ i, sizeInf b (D q.1 i) :=
            Finset.single_le_sum (f := fun i => sizeInf b (D q.1 i)) (fun _ _ => n0 _) (Finset.mem_univ q.2.1)
        _ ≤ ∑ a, ∑ i, sizeInf b (D a i) :=
            Finset.single_le_sum (f := fun a => ∑ i, sizeInf b (D a i))
              (fun _ _ => Finset.sum_nonneg fun _ _ => n0 _) (Finset.mem_univ q.1)
    rw [e1]
    change ‖N • ((θ ε * algebraMap F (Ainf F) (b.repr (X q.1 q.2.1) q.2.2)) w)‖ ≤ _
    exact (norm_nsmul_le ..).trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N))

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionRayAsymptoticStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_test_function_ray_asymptotic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∃ (N : ℕ) (ρ : ℝ), 0 < N ∧ ∀ k ∈ K, ∀ (X : Fin 1 → Fin 1 → E) (ε : ℝ), 0 < ε → Psi φ A (fun a i => ((k * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 → (∀ (p : Fin 1 × Fin 1 × Fin d) (v : HeightOneSpectrum (𝓞 F)), algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧ ∀ (p : Fin 1 × Fin 1 × Fin d) (w : InfinitePlace F), ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ ρ := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayFormula
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd

def cnt {F : Type} [Field F] [NumberField F] (θ : ℝ →+* Ainf F) (ι : Type) (K : Set (ι → Ainf F)) (ε : ℝ) : ℝ≥0∞ :=
  ∑' _y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
    (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K}, (1 : ℝ≥0∞)

theorem count : PositivityTheory.Rg.Mass.Equi → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ (ι : Type) [Fintype ι] (K : Set (ι → Ainf F)), IsCompact K → ∃ B : ℝ≥0, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι)) * cnt θ ι K ε ≤ B := by
  intro hEq F _ _ hF θ hθ li lam hli hlam ι _ K hK
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI := hli.1
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact
    (hK.union (isCompact_singleton (x := (0 : ι → Ainf F)))) isClosed_empty (Set.disjoint_empty _)
  have hL := hEq F hF θ hθ li lam hli hlam ι ∅ (f : (ι → Ainf F) → ℝ) (fun _ _ => 0) f.continuous hfc (by simp)
  simp only [Finset.prod_empty, mul_one] at hL
  set L := ∫ y, f y ∂(Measure.pi fun _ : ι => li) with hLdef
  have hLpos : 0 < L := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous hfc (fun x => (hf01 x).1)
      (x := 0) ?_
    rw [hf1 (Or.inr rfl)]
    exact one_ne_zero
  refine ⟨Real.toNNReal (L + 1), ?_⟩
  filter_upwards [hL.eventually (lt_mem_nhds (half_lt_self hLpos)), hL.eventually (gt_mem_nhds (lt_add_one L)),
    self_mem_nhdsWithin] with ε h1 h2 h3
  set u : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} → ℝ :=
    fun x => f fun i => θ ε * algebraMap F (Ainf F) (x.1 i) with hu
  have hu0 : ∀ x, 0 ≤ u x := fun x => (hf01 _).1
  have hsum : Summable u := by
    by_contra hns
    have e0 : ∑' x, u x = 0 := tsum_eq_zero_of_not_summable hns
    simp only [hu] at e0
    rw [e0, mul_zero] at h1
    linarith
  have hle : cnt θ ι K ε ≤ ∑' x, ENNReal.ofReal (u x) := by
    have hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K} =>
        (⟨y.1, fun v _ i => y.2.1 v i⟩ : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}) :=
      fun y y' e => Subtype.ext (Subtype.mk.inj e)
    refine le_trans (le_of_eq (tsum_congr fun y => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj fun x => ENNReal.ofReal (u x))
    simp only [hu]
    rw [hf1 (Or.inl y.2.2)]
    simp
  rw [← ENNReal.ofReal_tsum_of_nonneg hu0 hsum] at hle
  have hpos : 0 ≤ ε ^ (Module.finrank ℚ F * Fintype.card ι) := pow_nonneg (le_of_lt h3) _
  calc _ ≤ ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι)) * ENNReal.ofReal (∑' x, u x) := mul_le_mul' le_rfl hle
    _ = ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x, u x) := (ENNReal.ofReal_mul hpos).symm
    _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal (le_of_lt h2)
    _ = _ := rfl

def box (F : Type) [Field F] [NumberField F] (ι : Type) (ρ : ℝ) : Set (ι → Ainf F) :=
  {x | ∀ i w, ‖x i w‖ ≤ ρ}

theorem cnt_anti {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F) (hθ : Continuous θ)
    (r : ℝ → (AF F)ˣ) (hr : IsRay θ r) (ι : Type) (ρ : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) :
    cnt θ ι (box F ι ρ) ε ≤ cnt θ ι (box F ι ρ) δ := by
  have hn := (GlobalTheory.T.ray_norm_and_module_formula F hF θ hθ r hr).1
  have hm : ∀ y : ι → F, (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ →
      (fun i => θ δ * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ := fun y h i w => by
    have e : ∀ t : ℝ, ‖(θ t * algebraMap F (Ainf F) (y i)) w‖ = |t| * ‖algebraMap F (Ainf F) (y i) w‖ := fun t => by
      change ‖θ t w * algebraMap F (Ainf F) (y i) w‖ = _
      rw [norm_mul, hn]
    have h1 : ‖(θ ε * algebraMap F (Ainf F) (y i)) w‖ ≤ ρ := h i w
    change ‖(θ δ * algebraMap F (Ainf F) (y i)) w‖ ≤ ρ
    rw [e] at h1 ⊢
    rw [abs_of_pos hδ]
    rw [abs_of_pos (hδ.trans_le hδε)] at h1
    exact (mul_le_mul_of_nonneg_right hδε (norm_nonneg _)).trans h1
  have hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ} =>
      (⟨y.1, y.2.1, hm y.1 y.2.2⟩ : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ δ * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ}) :=
    fun y y' e => Subtype.ext (Subtype.mk.inj e)
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun _ => (1 : ℝ≥0∞)

theorem isCompact_box {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (ι : Type) (ρ : ℝ) :
    IsCompact (box F ι ρ) := by
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
  have e : box F ι ρ = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
    ext x
    exact ⟨fun h i _ w _ => mem_closedBall_zero_iff.2 (h i w),
      fun h i w => mem_closedBall_zero_iff.1 (h i (Set.mem_univ _) w (Set.mem_univ _))⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun w => isCompact_closedBall _ _

theorem Th_le {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (b : Module.Basis (Fin 2) F E)
    (θ : ℝ →+* Ainf F) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (B0 : ℝ) (hB0 : ∀ x, ‖φ x‖ ≤ B0)
    (N : ℕ) (hN : 0 < N) (ρ ε : ℝ) (y : (AF F ⊗[F] E)ˣ)
    (hbox : ∀ X : Fin 1 → Fin 1 → E, Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 →
      (∀ (p : Fin 1 × Fin 1 × Fin 2) (v : HeightOneSpectrum (𝓞 F)),
        algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧
      ∀ (p : Fin 1 × Fin 1 × Fin 2) (w : InfinitePlace F),
        ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ ρ) :
    Th φ A y ≤ Real.toNNReal B0 * cnt θ (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) ε := by
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set Y := fun X : Fin 1 → Fin 1 → E => fun p : Fin 1 × Fin 1 × Fin 2 => (N : F) * b.repr (X p.1 p.2.1) p.2.2 with hY
  have hYi : Function.Injective Y := fun X X' e => by
    funext a i
    refine b.repr.injective (Finsupp.ext fun k => ?_)
    have h1 := congrFun e (a, i, k)
    exact mul_left_cancel₀ hN0 h1
  set g : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) → ℝ≥0∞ :=
    fun X => Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i)) with hg
  set T : Set ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) := {X | g X ≠ 0} with hTdef
  have hPsi : ∀ Z : Fin 1 → Fin 1 → AF F ⊗[F] E, Psi φ A Z ≤ Real.toNNReal B0 := fun Z => by
    unfold Psi
    refine (Set.indicator_le_self' (fun _ _ => bot_le) _).trans ?_
    rw [ENNReal.ofReal, ENNReal.coe_le_coe]
    exact Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hB0 _))
  have e1 : Th φ A y = ∑' X : T, g X.1 := by
    rw [tsum_subtype T g]
    refine tsum_congr fun X => ?_
    by_cases hX : X ∈ T
    · rw [Set.indicator_of_mem hX]
    · rw [Set.indicator_of_notMem hX]
      exact not_not.1 hX
  rw [e1, cnt, ← ENNReal.tsum_mul_left]
  have hmap : ∀ X : T, (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
      algebraMap F (Fv F v) (Y X.1.1 i) ∈ v.adicCompletionIntegers F) ∧
        (fun i => θ ε * algebraMap F (Ainf F) (Y X.1.1 i)) ∈ box F _ ρ := fun X => by
    obtain ⟨h2, h3⟩ := hbox X.1.1 X.2
    exact ⟨fun v i => h2 i v, fun i w => h3 i w⟩
  have hinj : Function.Injective fun X : T => (⟨Y X.1.1, hmap X⟩ : {y : Fin 1 × Fin 1 × Fin 2 → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
      algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
        (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F _ ρ}) := fun X X' e =>
    Subtype.ext (Subtype.ext (hYi (congrArg Subtype.val e)))
  refine le_trans (ENNReal.tsum_le_tsum fun X => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
    fun _ => (Real.toNNReal B0 : ℝ≥0∞) * 1)
  rw [mul_one]
  exact hPsi _

theorem unit_bound : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∀ ε₁ : ℝ, ∃ C : ℝ≥0, ∀ k ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ENNReal.ofReal (ε ^ (2 * Module.finrank ℚ F)) * Th φ A (k * ofF (r ε)) ≤ C := by
  intro hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT K hK ε₁
  obtain ⟨N, ρ, hN, hbox⟩ := GlobalTheory.T.theta_test_function_ray_asymptotic F E σ hcm J hJ d b θ r hr S φ A hT K hK
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at this
    simpa using this.symm
  subst hd
  obtain ⟨B, hB⟩ := count hEq F hcm.1 θ hθ li lam hli hlam (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) (isCompact_box hcm.1 _ ρ)
  obtain ⟨B0, hB0⟩ := hT.2.1.exists_bound_of_continuous hT.1
  have e2 : Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 * Module.finrank ℚ F := by
    rw [show Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 from rfl, mul_comm]
  rw [e2] at hB
  set m := 2 * Module.finrank ℚ F with hm
  set c : ℝ → ℝ≥0∞ := cnt θ (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) with hc
  obtain ⟨ε₀, hε₀, hI⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hB
  have hε₀' : (0 : ℝ) < ε₀ := hε₀
  set ε₂ := ε₀ / 2 with hε₂
  have h2pos : 0 < ε₂ := half_pos hε₀'
  have h2 : ENNReal.ofReal (ε₂ ^ m) * c ε₂ ≤ B := hI ⟨h2pos, half_lt_self hε₀'⟩
  set E2 : ℝ≥0 := Real.toNNReal (ε₂ ^ m) with hE2
  have hE2pos : E2 ≠ 0 := by
    simp only [hE2, ne_eq, Real.toNNReal_eq_zero, not_le]
    exact pow_pos h2pos _
  set D : ℝ≥0 := B + Real.toNNReal (ε₁ ^ m) * (E2⁻¹ * B) with hD
  refine ⟨Real.toNNReal B0 * D, fun k hk ε hε hε1 => ?_⟩
  have hTh := Th_le b θ φ A B0 hB0 N hN ρ ε (k * ofF (r ε)) fun X h => hbox k hk X ε hε h
  have hcD : ENNReal.ofReal (ε ^ m) * c ε ≤ D := by
    by_cases hlt : ε < ε₀
    · have h1 : ENNReal.ofReal (ε ^ m) * c ε ≤ B := hI ⟨hε, hlt⟩
      refine h1.trans ?_
      rw [ENNReal.coe_le_coe, hD]
      exact le_self_add
    · have hle : ε₂ ≤ ε := (half_le_self hε₀'.le).trans (not_lt.1 hlt)
      have h3 : c ε ≤ c ε₂ := cnt_anti hcm.1 θ hθ r hr _ ρ h2pos hle
      have h4 : c ε₂ ≤ ((E2⁻¹ * B : ℝ≥0) : ℝ≥0∞) := by
        have e : c ε₂ = (E2 : ℝ≥0∞)⁻¹ * ((E2 : ℝ≥0∞) * c ε₂) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hE2pos) ENNReal.coe_ne_top, one_mul]
        rw [e, ENNReal.coe_mul, ENNReal.coe_inv hE2pos]
        exact mul_le_mul' le_rfl h2
      have h5 : ENNReal.ofReal (ε ^ m) ≤ (Real.toNNReal (ε₁ ^ m) : ℝ≥0∞) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hε1 m)
      calc ENNReal.ofReal (ε ^ m) * c ε ≤ (Real.toNNReal (ε₁ ^ m) : ℝ≥0∞) * ((E2⁻¹ * B : ℝ≥0) : ℝ≥0∞) :=
            mul_le_mul' h5 (h3.trans h4)
        _ ≤ D := by
            rw [← ENNReal.coe_mul, ENNReal.coe_le_coe, hD]
            exact le_add_self
  calc ENNReal.ofReal (ε ^ m) * Th φ A (k * ofF (r ε))
      ≤ ENNReal.ofReal (ε ^ m) * ((Real.toNNReal B0 : ℝ≥0∞) * c ε) := mul_le_mul' le_rfl hTh
    _ = (Real.toNNReal B0 : ℝ≥0∞) * (ENNReal.ofReal (ε ^ m) * c ε) := by ring
    _ ≤ (Real.toNNReal B0 : ℝ≥0∞) * D := mul_le_mul' le_rfl hcD
    _ = ((Real.toNNReal B0 * D : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_mul]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayFormulaStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_theta_integral_ray_formula : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∀ ε₁ : ℝ, ∃ C : ℝ≥0, ∀ k ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ENNReal.ofReal (ε ^ (2 * Module.finrank ℚ F)) * Th φ A (k * ofF (r ε)) ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd.unit_bound | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd.unit_bound | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd.unit_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesInvariantRationalUnits
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesInvariantRationalUnits
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

def unitPermNonzero {E : Type} [Field E] (q : Eˣ) :
    ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) ≃ ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) where
  toFun X := ⟨fun a i => (q : E) * X.1 a i, by
    intro h
    apply X.2
    funext a i
    have h1 : (q : E) * X.1 a i = 0 := congrFun (congrFun h a) i
    simpa using h1⟩
  invFun X := ⟨fun a i => ((q⁻¹ : Eˣ) : E) * X.1 a i, by
    intro h
    apply X.2
    funext a i
    have h1 : ((q⁻¹ : Eˣ) : E) * X.1 a i = 0 := congrFun (congrFun h a) i
    simpa using h1⟩
  left_inv X := by
    apply Subtype.ext
    funext a i
    simp
  right_inv X := by
    apply Subtype.ext
    funext a i
    simp

theorem Th_ofE_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (q : Eˣ) (y : (AF F ⊗[F] E)ˣ), Th φ A (ofE q * y) = Th φ A y := by
  intro F E _ _ _ _ φ A q y
  unfold Th
  rw [← Equiv.tsum_eq (unitPermNonzero q)
    (fun X => Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i)))]
  refine tsum_congr fun X => ?_
  congr 1
  funext a i
  have hq : ((ofE q : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = inclR (AF F) (q : E) := rfl
  have hX : ((unitPermNonzero q X).1 a i) = (q : E) * X.1 a i := rfl
  rw [Units.val_mul, hq, hX, map_mul]
  ring

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesInvariantRationalUnitsStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_invariant_rational_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (q : Eˣ) (y : (AF F ⊗[F] E)ˣ), Th φ A (ofE q * y) = Th φ A y := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryScalarHasNormOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryScalarHasNormOne
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem isNm_ue_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ h : HA (AF F) σ J, IsNm σ (ue (AF F) σ J h) 1 := by
  intro F E _ _ _ _ _ σ _ J hJ h
  have hg : cT (sigR (AF F) σ) ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) * JR (AF F) J *
      ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) = JR (AF F) J := h.2
  have hx : ((ue (AF F) σ J h : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) 0 0 := by
    simp only [ue, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  have he := congrFun (congrFun hg 0) 0
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, cT, JR, Matrix.transpose_apply,
    Matrix.map_apply, Fin.default_eq_zero, Fin.isValue] at he
  have hj : J 0 0 ≠ 0 := by
    have := hJ.2
    rwa [Matrix.det_fin_one] at this
  have hu : IsUnit (inclR (F := F) (AF F) (J 0 0)) := (IsUnit.mk0 _ hj).map (inclR (F := F) (AF F))
  show ((1 : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E) = sigR (AF F) σ _ * _
  rw [hx, Units.val_one, ← Algebra.TensorProduct.one_def]
  apply hu.mul_left_cancel
  rw [mul_one]
  exact he.symm.trans (by ring)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryScalarHasNormOneStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_scalar_has_norm_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ h : HA (AF F) σ J, IsNm σ (ue (AF F) σ J h) 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.isNm_ue_one | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.isNm_ue_one | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.isNm_ue_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneSiegelWeilThetaAverage
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneSiegelWeilThetaAverage
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem actW_rat_one {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (g : HA (AF F) σ J) (X : Fin 1 → Fin 1 → E) (a i : Fin 1) :
    actW (AF F) σ J g (ratTup (AF F) X) a i = (ue (AF F) σ J g : AF F ⊗[F] E) * inclR (AF F) (X a i) := by
  have e : ((ue (AF F) σ J g : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (HA.mat (AF F) σ J g).val 0 0 := by
    simp [ue, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  rw [e]
  simp only [actW, actTup, Matrix.mulVec, dotProduct, ratTup, Fin.sum_univ_one, Subsingleton.elim i 0,
    Subsingleton.elim a 0]

theorem mean_eq_lint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ 1 J μ → IsFDH F E σ 1 J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ x : (AF F ⊗[F] E)ˣ, mean σ J μ 𝓕 φ A x = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, Th φ A (x * ue (AF F) σ J h⁻¹) ∂μ ∧ Measurable fun h : HA (AF F) σ J => Th φ A (x * ue (AF F) σ J h⁻¹) := by
  intro F E _ _ _ _ _ σ hcm J hJ μ 𝓕 hμ h𝓕 d b S φ A hT x
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 1
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 1 J hJ (AF F)
  obtain ⟨ac, -, -, -⟩ := hact 1
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨k1, -, -, -, -, -, -, k8, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  have := k8 1 1
  obtain ⟨t1, t2, t3, t4, t5, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1
  obtain ⟨hφc, -, hφ0, -, hAS, hAoff⟩ := hT
  have hs : ∀ v, Continuous fun X : Fin 1 → Fin 1 → AF F ⊗[F] E => projV v (projFin X) := fun v => (t3 v).comp t2
  have hP : IsOpen {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := by
    have e : {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} =
        (⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' A v) ∩ intOff b S := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, intOff]
      refine ⟨fun h => ⟨fun v _ => h v, fun v hv => hAoff v hv ▸ h v⟩, fun h v => ?_⟩
      by_cases hv : v ∈ S
      · exact h.1 v hv
      · rw [hAoff v hv]; exact h.2 v hv
    rw [e]
    exact (isOpen_biInter_finset fun v hv => (hAS v hv).2.1.preimage (hs v)).inter (t5 S)
  have hPsi : Measurable (Psi φ A) :=
    (ENNReal.measurable_ofReal.comp (hφc.comp t1).measurable).indicator hP.measurableSet
  have hmul : Continuous fun (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) (a i : Fin 1) => (x : AF F ⊗[F] E) * Y a i :=
    continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)
  set Φ : (Fin 1 → Fin 1 → AF F ⊗[F] E) → ℝ≥0∞ := fun Y => Psi φ A fun a i => (x : AF F ⊗[F] E) * Y a i with hΦd
  have hΦ : Measurable Φ := hPsi.comp hmul.measurable
  have hQ : MeasurableSet {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin fun a i => (x : AF F ⊗[F] E) * X a i) ∈ A v} :=
    (hP.preimage hmul).measurableSet
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hterm : ∀ (h : HA (AF F) σ J), Th φ A (x * ue (AF F) σ J h⁻¹) =
      ∑' X : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _), Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) := fun h => by
    refine tsum_congr fun X => ?_
    simp only [hΦd]
    congr 1
    funext a i
    rw [actW_rat_one, Units.val_mul, mul_assoc]
  refine ⟨?_, ?_⟩
  · simp only [hterm]
    rw [← PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm 1 J hJ μ 𝓕 hμ h𝓕 1 _ Φ hΦ, mean, ← lintegral_indicator hQ]
    refine lintegral_congr fun X => ?_
    simp only [hΦd, Psi, Set.indicator, Set.mem_setOf_eq]
  · simp only [hterm]
    exact Measurable.tsum fun X => hΦ.comp (ac.comp (continuous_inv.prodMk continuous_const)).measurable

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneSiegelWeilThetaAverageStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_siegel_weil_theta_average : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ 1 J μ → IsFDH F E σ 1 J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ x : (AF F ⊗[F] E)ˣ, mean σ J μ 𝓕 φ A x = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, Th φ A (x * ue (AF F) σ J h⁻¹) ∂μ ∧ Measurable fun h : HA (AF F) σ J => Th φ A (x * ue (AF F) σ J h⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.mean_eq_lint | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.mean_eq_lint | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.mean_eq_lint <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionSideEquidistribution
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem nm_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {x x' : (AF F ⊗[F] E)ˣ} {n n' : (AF F)ˣ} (h : IsNm σ x n) (h' : IsNm σ x' n') : IsNm σ (x * x') (n * n') := by
  unfold IsNm at *
  have e : ((n * n' : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E) = ((n : AF F) ⊗ₜ[F] (1 : E)) * ((n' : AF F) ⊗ₜ[F] (1 : E)) := by
    simp
  rw [e, h, h']
  simp only [Units.val_mul, map_mul]
  ring

theorem nm_ofF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (a : (AF F)ˣ) : IsNm σ (ofF a) (a * a) := by
  unfold IsNm
  have e : ((ofF a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (a : AF F) ⊗ₜ[F] (1 : E) := rfl
  rw [e]
  simp [sigR]

theorem ray_sq {F : Type} [Field F] [NumberField F] {θ : ℝ →+* Ainf F} {r : ℝ → (AF F)ˣ} (hr : IsRay θ r) {ε : ℝ}
    (hε : 0 < ε) : r (ε ^ 2) = r ε * r ε := by
  apply Units.ext
  have h1 := hr ε hε
  have h2 := hr (ε ^ 2) (by positivity)
  refine Prod.ext ?_ ?_
  · change ((r (ε ^ 2) : AF F)).1 = (r ε : AF F).1 * (r ε : AF F).1
    rw [h1.1, h2.1, ← map_mul, sq]
  · change ((r (ε ^ 2) : AF F)).2 = (r ε : AF F).2 * (r ε : AF F).2
    rw [h1.2, h2.2, one_mul]

theorem md_mul {F : Type} [Field F] [NumberField F] (a b : (AF F)ˣ) : md (a * b) = md a * md b := by
  simp [md]

theorem md_pos {F : Type} [Field F] [NumberField F] (a : (AF F)ˣ) : 0 < md a := (IdeleGroup.ideleModule F a).2

theorem bound : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A →
    ∃ C : ℝ≥0, ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → ENNReal.ofReal (md n) * Th φ A y ≤ C := by
  intro hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT
  obtain ⟨K, hK, hdec⟩ := GlobalTheory.T.idele_class_compact_ray_decomposition F E σ hcm θ hθ r hr
  obtain ⟨R, hR⟩ := GlobalTheory.T.theta_test_function_bounded_large_norm F E σ hcm J hJ d b S φ A hT
  obtain ⟨C, hC⟩ := GlobalTheory.T.rank_one_theta_integral_ray_formula hEq F E σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT K hK (max 1 R)
  refine ⟨C, fun y n hn => ?_⟩
  obtain ⟨q, k, ε, hk, hε, rfl, hm⟩ := hdec y n hn
  rw [GlobalTheory.T.theta_series_invariant_rational_units]
  by_cases h : ε ≤ max 1 R
  · rw [hm]
    exact hC k hk ε hε h
  · have h1 : 1 < ε := lt_of_le_of_lt (le_max_left _ _) (not_le.1 h)
    have h2 : R < ε := lt_of_le_of_lt (le_max_right _ _) (not_le.1 h)
    have h3 : 2 * Module.finrank ℚ F ≠ 0 := by
      have := Module.finrank_pos (R := ℚ) (M := F)
      omega
    have h4 : ε ≤ ε ^ (2 * Module.finrank ℚ F) := le_self_pow₀ h1.le h3
    have h5 := hR _ n hn (by rw [hm]; linarith)
    rw [GlobalTheory.T.theta_series_invariant_rational_units] at h5
    rw [h5, mul_zero]
    exact bot_le

theorem lside : PositivityTheory.Rg.Mass.Equi → LSide := by
  intro hEq F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm θ hθ r hr S φ A hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have hG := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 1 J hJ (AF F)
  haveI : IsTopologicalGroup (HA (AF F) σ J) := hG.1
  haveI : LocallyCompactSpace (HA (AF F) σ J) := hG.2.1
  haveI : SecondCountableTopology (HA (AF F) σ J) := hG.2.2.1
  haveI : T2Space (HA (AF F) σ J) := hG.2.2.2.1
  haveI : BorelSpace (HA (AF F) σ J) := hG.2.2.2.2.1
  have hfin : μ 𝓕 < ⊤ := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm 1 J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm 1 J hJ).1
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  have h0 : μ 𝓕 ≠ 0 := (GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕' hfin).1
  have hft : μ 𝓕 ≠ ⊤ := hfin.ne
  obtain ⟨C, hC⟩ := bound hEq F E σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT
  obtain ⟨R, hR⟩ := GlobalTheory.T.theta_test_function_bounded_large_norm F E σ hcm J hJ d b S φ A hT
  have hM := fun x => GlobalTheory.T.rank_one_siegel_weil_theta_average F E σ hcm J hJ μ 𝓕 hμ h𝓕 d b S φ A hT x
  have hnm : ∀ (x : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ) (h : HA (AF F) σ J), IsNm σ x n → IsNm σ (x * ue (AF F) σ J h⁻¹) n :=
    fun x n h hn => by simpa using nm_mul hn (GlobalTheory.T.unitary_scalar_has_norm_one F E σ hcm J hJ h⁻¹)
  have hcan : (μ 𝓕)⁻¹ * μ 𝓕 = 1 := ENNReal.inv_mul_cancel h0 hft
  refine ⟨⟨C, fun x n hn => ?_⟩, ⟨R, fun x n hn hRn => ?_⟩, fun x n hn => ?_⟩
  · rw [(hM x).1, mul_left_comm, ← lintegral_const_mul _ (hM x).2]
    calc _ ≤ (μ 𝓕)⁻¹ * ∫⁻ _ in 𝓕, (C : ℝ≥0∞) ∂μ := by
            gcongr with h
            exact hC _ n (hnm x n h hn)
      _ = C := by
            rw [lintegral_const, Measure.restrict_apply_univ, mul_comm (C : ℝ≥0∞), ← mul_assoc, hcan, one_mul]
  · rw [(hM x).1]
    have : ∀ h : HA (AF F) σ J, Th φ A (x * ue (AF F) σ J h⁻¹) = 0 := fun h => hR _ n (hnm x n h hn) hRn
    simp [this]
  · set m := 2 * Module.finrank ℚ F with hmdef
    have hmr := (GlobalTheory.T.ray_norm_and_module_formula F hcm.1 θ hθ r hr).2
    have hmd : ∀ ε : ℝ, 0 < ε → md (n * r (ε ^ 2)) = md n * ε ^ m := fun ε hε => by
      rw [md_mul, hmr _ (by positivity), hmdef, pow_mul]
    have hne : ∀ ε : ℝ, 0 < ε → IsNm σ (x * ofF (r ε)) (n * r (ε ^ 2)) := fun ε hε => by
      rw [ray_sq hr hε]
      exact nm_mul hn (nm_ofF _)
    set f : ℝ → HA (AF F) σ J → ℝ≥0∞ := fun ε h =>
      ENNReal.ofReal (md (n * r (ε ^ 2))) * Th φ A (x * ofF (r ε) * ue (AF F) σ J h⁻¹) with hf
    have hfm : ∀ ε, Measurable (f ε) := fun ε => (hM _).2.const_mul _
    have hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ h, f ε h ≤ C := by
      filter_upwards [self_mem_nhdsWithin] with ε hε h
      exact hC _ _ (hnm _ _ h (hne ε hε))
    have hpt : ∀ h, Tendsto (fun ε => f ε h) (𝓝[>] 0) (𝓝 (vol b li lam S φ A)) := fun h => by
      have hy := hnm x n h hn
      have e0 : ∀ ε, x * ofF (r ε) * ue (AF F) σ J h⁻¹ = x * ue (AF F) σ J h⁻¹ * ofF (r ε) := fun ε => by
        rw [mul_assoc, mul_comm (ofF (r ε)), ← mul_assoc]
      have hT1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Th φ A (x * ue (AF F) σ J h⁻¹ * ofF (r ε)) ≠ ⊤ := by
        filter_upwards [hbd, self_mem_nhdsWithin] with ε h1 h2 h3
        have h4 := h1 h
        simp only [hf, e0, h3] at h4
        rw [ENNReal.mul_top (by simpa using md_pos _)] at h4
        exact absurd h4 (not_le.2 ENNReal.coe_lt_top)
      have hL := GlobalTheory.T.rank_one_theta_integral_ray_limit hEq F E σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT _ n hy hT1
      have hmn : ENNReal.ofReal (md n) ≠ 0 := by simpa using md_pos n
      have h2 := ENNReal.Tendsto.const_mul hL (Or.inr (ENNReal.ofReal_ne_top (r := md n)))
      rw [← mul_assoc, ENNReal.mul_inv_cancel hmn ENNReal.ofReal_ne_top, one_mul] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      simp only [hf]
      rw [e0, hmd ε hε', ENNReal.ofReal_mul (md_pos n).le]
      exact (mul_assoc _ _ _).symm
    have hlim : Tendsto (fun ε => ∫⁻ h in 𝓕, f ε h ∂μ) (𝓝[>] 0) (𝓝 (∫⁻ _ in 𝓕, vol b li lam S φ A ∂μ)) := by
      refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => (C : ℝ≥0∞))
        (Eventually.of_forall hfm) (hbd.mono fun ε h => ae_of_all _ h) ?_ (ae_of_all _ hpt)
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top hft
    have h2 := ENNReal.Tendsto.const_mul hlim (Or.inr (ENNReal.inv_ne_top.2 h0)) (a := (μ 𝓕)⁻¹)
    rw [lintegral_const, Measure.restrict_apply_univ, mul_comm (vol b li lam S φ A), ← mul_assoc, hcan, one_mul] at h2
    refine h2.congr fun ε => ?_
    simp only [hf]
    rw [(hM _).1, lintegral_const_mul _ (hM _).2, mul_left_comm]
    rfl

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionSideEquidistributionStatement
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l_function_side_equidistribution : PositivityTheory.Rg.Mass.Equi → LSide := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside <;> assumption)
end
