module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneEuler
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneStandard
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneStandard
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero

theorem mass_dilated_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (a e : ℕ), 0 < a → Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e → ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1) → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b v lam hlam m hm a e ha h1 h2
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have hnorm := GlobalTheory.CompanionTheory.SW.Dil.norm_natCast v a e ha h1 h2
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ht : (a : Fv F v) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact (pow_ne_zero e (inv_ne_zero hq)) hnorm.symm
  have ht2 : (a : Fv F v) ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hnorm2 : ‖(a : Fv F v) ^ 2‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ (2 * e) := by
    rw [norm_pow, hnorm, ← pow_mul, mul_comm]
  have hs1 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam _ ht e hnorm
  have hs2 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam _ ht2 (2 * e) hnorm2
  set q : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) with hqdef
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E :=
    fun y => algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) * y with hf
  have hcast : algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) = (a : Fv F v ⊗[F] E) := map_natCast _ _
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := GlobalTheory.CompanionTheory.SW.Dil.coordK_map (Fv F v) σ hσ b lam _ ht _ hs1
  have hk1 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => (a : Fv F v ⊗[F] E)
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    change IsUnit (a : Fv F v ⊗[F] E)
    rw [← hcast]
    exact ht.isUnit.map _
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf, hcast]
    rw [Subsingleton.elim p 0, mul_comm]
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S => (a ^ 2) • S
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) ((a : Fv F v) ^ 2) *
        (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    change (a ^ 2) • (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j = _
    rw [nsmul_eq_mul, map_pow, hcast]
    push_cast
    rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    exact (continuous_nsmul (a ^ 2)).measurable
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam _ ht2 _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g := by
    intro S
    ext i j
    have hsig : sigR (Fv F v) σ (a : Fv F v ⊗[F] E) = a := map_natCast _ _
    rw [hτe, map_pow, hcast, GlobalTheory.CompanionTheory.SW.Dil.cT_scalar _ _ hsig]
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hfree : IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm hfree g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)
  have hτs : τ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) =
      hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ := by
    have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ = 0 := by
      apply Subtype.ext
      funext i j
      simp [hermOf]
    rw [h0]
    exact smul_zero _
  rw [hτs] at key
  have hA : MeasurableSet (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) :=
    GlobalTheory.CompanionTheory.SW.Growth.measurable_latV b v
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' (latV b v)) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : ((q ^ e) ^ 2) ^ M = q ^ (2 * e) * q ^ (e * (2 * M - 2)) := by
    rw [← pow_add, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) - 2 = 2 * k := by omega
    rw [this]
    ring
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have hq0 : ((q ^ (2 * e) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    refine pow_ne_zero _ ?_
    rw [hqdef]
    exact_mod_cast hq
  have key3 := (ENNReal.mul_right_inj hq0 ENNReal.coe_ne_top).1 key2
  have hset : {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} =
      (fun X => rmul (Fv F v) X g) ⁻¹' (latV b v) := by
    rw [hrm]
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hf, hcast]
  have hof : ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) =
      ((q ^ (e * (2 * M - 2)) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [hset, ← key3, hof]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneStandardStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_volume_rank_one_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (a e : ℕ), 0 < a → Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e → ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1) → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero.mass_dilated_lattice | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero.mass_dilated_lattice | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero.mass_dilated_lattice <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneEuler
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero

open GlobalTheory.CompanionTheory.SW.Growth

section Abstract
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M : ℕ}

theorem growth_of_scale (b : Module.Basis (Fin d) F E)
    (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hscale : ∀ (v : HeightOneSpectrum (𝓞 F)) (a e : ℕ), 0 < a → Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e →
      ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1) →
      μ v (dilSet b v a) = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) * μ v (latV b v))
    (hfin : ∀ v, μ v (latV b v) < ⊤)
    (hsum : Summable fun v => |(μ v (latV b v)).toReal - 1|)
    (hne : ∀ v, μ v ≠ 0) :
    (∀ a : ℕ, 0 < a → ∀ v, μ v (dilSet b v a) < ⊤) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧
        κ * (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) ≤ ∏' v, (μ v (dilSet b v a)).toReal := by
  have hdil : ∀ (a : ℕ), 0 < a → ∀ v, μ v (dilSet b v a) < ⊤ := by
    intro a ha v
    obtain ⟨e, he, -, -⟩ := exists_exponents (F := F) a ha
    rw [hscale v a (e v) ha (he v).1 (he v).2]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin v)
  have hpos : ∀ v, 0 < (μ v (latV b v)).toReal := by
    intro v
    obtain ⟨n, hn, hnz⟩ := exists_pos_mass b v (μ v) (hne v)
    obtain ⟨e, he, -, -⟩ := exists_exponents (F := F) n hn
    have hz : μ v (latV b v) ≠ 0 := by
      intro h0
      rw [hscale v n (e v) hn (he v).1 (he v).2, h0, mul_zero] at hnz
      exact hnz rfl
    exact ENNReal.toReal_pos hz (hfin v).ne
  obtain ⟨hmulL, -, hprodpos, -⟩ := GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod _ (fun v => (μ v (latV b v)).toReal) hsum
  refine ⟨hdil, ∏' v, (μ v (latV b v)).toReal, hprodpos hpos, fun k => ⟨k + 1, Nat.lt_succ_self k, ?_⟩⟩
  set a := k + 1 with hadef
  have ha : 0 < a := Nat.succ_pos k
  obtain ⟨e, he, hfs, hprod⟩ := exists_exponents (F := F) a ha
  have hid : ∀ v, (μ v (dilSet b v a)).toReal =
      (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2) * (μ v (latV b v)).toReal := by
    intro v
    rw [hscale v a (e v) ha (he v).1 (he v).2, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), pow_mul]
  have hf2 : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2)) :=
    hfs.fun_comp (g := fun y : ℝ => y ^ (2 * M - 2)) (one_pow _)
  have hmul : Multipliable
      (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ)) ^ e v) ^ (2 * M - 2)) :=
    (hasProd_prod_of_ne_finset_one (s := Set.Finite.toFinset hf2) (fun v hv =>
      by_contra fun h => hv ((Set.Finite.mem_toFinset hf2).2 h))).multipliable
  rw [tprod_congr hid, hmul.tprod_mul hmulL, tprod_eq_finprod hf2, ← finprod_pow hfs, hprod, ← pow_mul,
    mul_comm]

end Abstract

theorem growth_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) → (∀ a : ℕ, 0 < a → ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} < ⊤) ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧ κ * (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) ≤ ∏' v, (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b lam hlam m hm hne
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.finite_volume_rank_one_product F E σ hσ M J hJ hM h₀ d b lam hlam m hm
  have hscale := fun (v : HeightOneSpectrum (𝓞 F)) (a e : ℕ) (ha : 0 < a) h1 h2 =>
    GlobalTheory.T.local_volume_rank_one_standard F E σ hσ M J hJ hM h₀ d b v (lam v) (hlam v) (m v) (hm v) a e ha h1 h2
  exact growth_of_scale b (fun v => m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))
    hscale hfin hsum hne

end GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteVolumeRankOneEulerStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_volume_rank_one_euler : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) → (∀ a : ℕ, 0 < a → ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} < ⊤) ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ k : ℕ, ∃ a : ℕ, k < a ∧ κ * (a : ℝ) ^ (Module.finrank ℚ F * (2 * M - 2)) ≤ ∏' v, (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero.growth_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero.growth_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.GrowthZero.growth_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNondegenerateOfIwasawa
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UpperLeftBlockMatrix
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}

theorem npow_mul' {r h : ℝ≥0} (t : ℂ) : npow (r * h) t = npow r t * npow h t := by
  simp only [npow, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg r.2 h.2 t

theorem npow_inv' {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r⁻¹ t = npow r (-t) := by
  have hr' : 0 < r⁻¹ := inv_pos.2 hr
  rw [npow_eq_exp hr', npow_eq_exp hr]
  congr 1
  rw [NNReal.coe_inv, Real.log_inv]
  push_cast
  ring

theorem npow_add' {r : ℝ≥0} (hr : 0 < r) (s t : ℂ) : npow r (s + t) = npow r s * npow r t := by
  rw [npow_eq_exp hr, npow_eq_exp hr, npow_eq_exp hr, ← Complex.exp_add]
  congr 1
  ring

theorem npow_zero' (r : ℝ≥0) (hr : 0 < r) : npow r 0 = 1 := by
  rw [npow_eq_exp hr]; simp

theorem upperLeft_blockMatrix {R : Type} (x y z t : Matrix (Fin n) (Fin n) R) : blkA (blk4 x y z t) = x := by
  ext i j
  simp [blkA, blk4, Matrix.toBlocks₁₁]

theorem det_ad (a : GL (Fin n) (AE D)) :
    (Matrix.GeneralLinearGroup.det (ad a) : (AE D)ˣ) =
      conjUnit (R := AF D.host.F) D.sp.cm.sig (Matrix.GeneralLinearGroup.det a⁻¹ : (AE D)ˣ) := by
  apply Units.ext
  have h1 : ((Matrix.GeneralLinearGroup.det (ad a) : (AE D)ˣ) : AE D) = (adj (a⁻¹).1 : Mx D n n).det :=
    Matrix.GeneralLinearGroup.val_det_apply _
  have h2 : (adj (a⁻¹).1 : Mx D n n).det = cA D ((a⁻¹).1.det) := by
    unfold adj
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (cA D) _).symm
  have h3 : ((Matrix.GeneralLinearGroup.det a⁻¹ : (AE D)ˣ) : AE D) = (a⁻¹).1.det :=
    Matrix.GeneralLinearGroup.val_det_apply _
  rw [h1, h2, ← h3]
  rfl
theorem absA_ad (a : GL (Fin n) (AE D)) : absA D (Matrix.GeneralLinearGroup.det (ad a)) =
    (absA D (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  rw [det_ad, GlobalTheory.DiagThetaRule.absA_conj, map_inv, map_inv]

theorem exists_ad (a : GL (Fin n) (AE D)) : ∃ m' ∈ P D n, mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1 := by
  obtain ⟨m', hm'⟩ := exists_levi (ad a)
  obtain ⟨m'', hm''⟩ := exists_levi (ad a)⁻¹
  have e1 : mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1 := by
    rw [hm']
    have : (adj ((ad a)⁻¹).1 : Mx D n n) = a.1 := adj_adj _
    rw [this]
    rfl
  have h1 : m'' * m' = 1 := mat_inj (by
    rw [mat_mul, mat_one, hm', hm'']
    have := levi_mul_inv (D := D) (ad a)⁻¹
    rwa [inv_inv] at this)
  exact ⟨m', levi_mem_P hm' hm'' h1, e1⟩

theorem gram_pt (V : HSp D) (h : GA D V) (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) :
    StdUnn.inner V (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (ξ.map (incA D)) : Mx D V.rank n)
      (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (ξ.map (incA D)) : Mx D V.rank n) = (gramQ V ξ).map (incA D) := by
  have h0 : gramQ V ξ = ξᴴ * (HSpace.gram V * ξ) := rfl
  have e : ((gramQ V ξ).map (incA D) : Mx D n n) =
      HMul.hMul (adj (ξ.map (incA D))) (HMul.hMul (gA V) (ξ.map (incA D)) : Mx D V.rank n) := by
    change rat (gramQ V ξ) = HMul.hMul (adj (rat ξ)) (HMul.hMul (gA V) (rat ξ) : Mx D V.rank n)
    rw [h0, rat_mul, rat_mul, rat_conjTranspose]
    rfl
  rw [e]
  unfold GlobalTheory.StdUnn.inner
  have u := GlobalTheory.MixModel.mt_unitary V h⁻¹
  calc _ = HMul.hMul (adj (ξ.map (incA D))) (HMul.hMul (HMul.hMul (adj (Formalism.L2.Theta.mt V h⁻¹))
        (HMul.hMul (gA V) (Formalism.L2.Theta.mt V h⁻¹) : Mx D V.rank V.rank) : Mx D V.rank V.rank) (ξ.map (incA D)) : Mx D V.rank n) := by
        rw [adj_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [u]

theorem ifrB_step {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (ν : Measure (GA D V)) (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    {b1 : Mx D n n} (hu : mat u = blk4 1 b1 0 1) (φ : schwartzA θ V.rank n) (β : HermE D n) :
    IfrB V ν (ω (m * u) φ).1 β = ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
        ψ (halfTr (Matrix.trace (b1 * (adj a.1 * β.1.map (incA D) * a.1))))) *
      IfrB V ν (fun x => φ.1 (HMul.hMul x a.1)) β := by
  set K : ℂ := (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
        ψ (halfTr (Matrix.trace (b1 * (adj a.1 * β.1.map (incA D) * a.1)))) with hK
  have key : (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = n ∧ gramQ V x = β.1},
      (ω (m * u) φ).1 (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) =
      fun h => K * ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = n ∧ gramQ V x = β.1},
        φ.1 (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)) : Mx D V.rank n) a.1) := by
    funext h
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [weil_pt hω a hm hu, inner_mul_right, gram_pt, x.2.2, hK]
    ring
  unfold IfrB
  rw [key]
  show ⨍ q, K * _ ∂_ = _
  simp only [average_eq, integral_const_mul, mul_smul_comm]
  rfl

end GlobalTheory.CompanionTheory.IwaAd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNondegenerateOfIwasawa
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}

set_option maxHeartbeats 4000000 in
theorem whit_step (hK : WhitKA) {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {Φ : schwartzA θ V.rank n} (hS : Std D n V ψ χ θ μ ω H l s ν Φ) (hR : InRange V n)
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} {nb : hermA D n → G D n} (hC : CoefData nb lam 𝓖)
    {w : G D n} (hw : mat w = blk4 0 1 (-1) 0) {β : HermE D n} (hβ : β.1.det ≠ 0)
    (a : GL (Fin n) (AE D)) {m u k : G D n} (hk : k ∈ K D n) (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    (b1 : hermA D n) (hu : mat u = blk4 1 b1.1 0 1) :
    HolValueAt (fun z => ∫ b, npow (H (w * nb b * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam)
      (s0 V n) (IfrB V ν (ω (m * u * k) Φ).1 β) := by
  have hω := hS.hω
  have hH := hS.hH
  obtain ⟨𝓕, h𝓕⟩ := hS.hμ
  have hμ : μ.IsAddHaarMeasure := h𝓕.1
  have hl : lam.IsAddHaarMeasure := hC.2.1
  have hnb : IsNMap nb := hC.1
  have hub : u = nb b1 := mat_inj (by rw [hnb b1]; exact hu)
  set A := absA D (Matrix.GeneralLinearGroup.det a) with hAdef
  have hA : 0 < A := absA_pos _
  obtain ⟨m', hm'P, hm'⟩ := exists_ad a
  have hwm : w * m = m' * w := weyl_mul hw a hm hm'
  have hblk : blkA (mat m') = (ad a).1 := by rw [hm', upperLeft_blockMatrix]; rfl
  set φ0 : schwartzA θ V.rank n := ω k Φ with hφ0
  have hωe : ω (m * u * k) Φ = ω (m * u) φ0 := by
    rw [map_mul (f := ω) (m * u) k]; rfl
  set T : Mx D n n := adj a.1 * β.1.map (incA D) * a.1 with hT
  set ct : ℂ := ψ (halfTr (Matrix.trace (T * b1.1))) with hct
  set c0 : ℂ := (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow A ((V.rank : ℂ) / 2) with hc0
  have hpt : ∀ (z : ℂ) (b' : hermA D n),
      npow (H (w * nb (cg a (b' - b1)) * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 (cg a (b' - b1)) *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (cg a (b' - b1)).1 : Mx D n n))) =
      (npow A (s0 V n - z) * (c0 * npow A (-(V.rank : ℂ))) * ct) *
        (npow (H (w * nb b' * k)) (z - s0 V n) * Jt ψ V μ φ0.1 b' *
          ψ (-halfTr (Matrix.trace (HMul.hMul T b'.1 : Mx D n n)))) := by
    intro z b'
    have e : w * nb (cg a (b' - b1)) * (m * u * k) = m' * (w * nb b' * k) := by
      calc _ = w * (nb (cg a (b' - b1)) * m) * u * k := by simp only [mul_assoc]
        _ = w * (m * nb (b' - b1)) * u * k := by rw [nb_cg_mul hnb a hm]
        _ = (w * m) * (nb (b' - b1) * nb b1) * k := by rw [hub]; simp only [mul_assoc]
        _ = m' * w * nb b' * k := by rw [hwm, ← nb_add hnb, sub_add_cancel]
        _ = _ := by simp only [mul_assoc]
    have hHe : H (w * nb (cg a (b' - b1)) * (m * u * k)) = A⁻¹ * H (w * nb b' * k) := by
      rw [e, height_mul hH hm'P (ad a) hblk, absA_ad]
    have hJ : Jt ψ V μ (ω (m * u * k) Φ).1 (cg a (b' - b1)) = c0 * (npow A (-(V.rank : ℂ)) * Jt ψ V μ φ0.1 b') := by
      rw [hωe, jt_step hω hμ a hm hu φ0 (b' - b1), sub_add_cancel]
    have e1 : Matrix.trace (HMul.hMul (β.1.map (incA D)) (cg a (b' - b1)).1 : Mx D n n) =
        Matrix.trace (T * (b' - b1).1) := trace_beta a _ _
    have e2 : Matrix.trace (T * (b' - b1).1) = Matrix.trace (T * b'.1) + -Matrix.trace (T * b1.1) := by
      have : (b' - b1).1 = b'.1 - b1.1 := rfl
      rw [this, Matrix.mul_sub, Matrix.trace_sub, sub_eq_add_neg]
    have hch : ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) (cg a (b' - b1)).1 : Mx D n n))) =
        ψ (-halfTr (Matrix.trace (HMul.hMul T b'.1 : Mx D n n))) * ct := by
      rw [e1, e2, halfTr_add, halfTr_neg, neg_add, neg_neg, AddChar.map_add_eq_mul]
    rw [hHe, hJ, hch, npow_mul', npow_inv' hA, show -(z - s0 V n) = s0 V n - z from neg_sub z (s0 V n)]
    ring
  have hint : ∀ z : ℂ, (∫ b, npow (H (w * nb b * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam) =
      npow A (s0 V n - z) * ((npow A (n : ℂ) * (c0 * npow A (-(V.rank : ℂ))) * ct) *
        whitT ψ V μ lam nb w H φ0.1 T k z) := by
    intro z
    set Gz : hermA D n → ℂ := fun b => npow (H (w * nb b * (m * u * k))) (z - s0 V n) * Jt ψ V μ (ω (m * u * k) Φ).1 b *
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) with hGz
    have h1 : ∫ c, Gz (cg a c) ∂lam = npow A (-(n : ℂ)) * ∫ b, Gz b ∂lam := GlobalTheory.CompanionTheory.CgMod.integral_cg D n lam hl a Gz
    have h2 : ∫ x, Gz (cg a (x - b1)) ∂lam = ∫ c, Gz (cg a c) ∂lam :=
      integral_shift_herm lam hl (fun c => Gz (cg a c)) b1
    have h3 : ∫ x, Gz (cg a (x - b1)) ∂lam =
        (npow A (s0 V n - z) * (c0 * npow A (-(V.rank : ℂ))) * ct) * whitT ψ V μ lam nb w H φ0.1 T k z := by
      simp only [hGz, hpt, integral_const_mul]
      rfl
    have h4 : npow A (n : ℂ) * npow A (-(n : ℂ)) = 1 := by
      rw [← npow_add' hA, add_neg_cancel, npow_zero' A hA]
    rw [h3, h1] at h2
    calc ∫ b, Gz b ∂lam = (npow A (n : ℂ) * npow A (-(n : ℂ))) * ∫ b, Gz b ∂lam := by rw [h4, one_mul]
      _ = npow A (n : ℂ) * (npow A (-(n : ℂ)) * ∫ b, Gz b ∂lam) := by ring
      _ = _ := by rw [← h2]; ring
  have h0 := hK D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  have hc := (holValueAt_const (npow A (n : ℂ) * (c0 * npow A (-(V.rank : ℂ))) * ct) (s0 V n)).mul h0
  have hfin := holValueAt_npow_sub_mul _ (fun z => ∫ b, npow (H (w * nb b * (m * u * k))) (z - s0 V n) *
      Jt ψ V μ (ω (m * u * k) Φ).1 b * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam)
    (s0 V n) _ A 0 hA hc (fun z _ => hint z)
  have hval : npow A (n : ℂ) * (c0 * npow A (-(V.rank : ℂ))) * ct *
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) - n) *
        IfrB V ν (fun x => (ω k Φ).1 (HMul.hMul x a.1)) β) = IfrB V ν (ω (m * u * k) Φ).1 β := by
    have h5 : npow A (n : ℂ) * npow A (-(V.rank : ℂ)) * npow A ((V.rank : ℂ) - n) = 1 := by
      rw [← npow_add' hA, ← npow_add' hA]
      have : (n : ℂ) + -(V.rank : ℂ) + ((V.rank : ℂ) - n) = 0 := by ring
      rw [this, npow_zero' A hA]
    have h6 : ψ (halfTr (Matrix.trace (b1.1 * T))) = ct := by
      rw [hct, Matrix.trace_mul_comm]
    rw [hωe, ifrB_step hω ν a hm hu φ0 β, ← hAdef, ← hT, ← hc0, h6]
    calc _ = (npow A (n : ℂ) * npow A (-(V.rank : ℂ)) * npow A ((V.rank : ℂ) - n)) * (c0 * ct *
            IfrB V ν (fun x => φ0.1 (HMul.hMul x a.1)) β) := by ring
      _ = _ := by rw [h5, one_mul]
  rw [hval] at hfin
  exact hfin

theorem iwaRedA : GlobalTheory.CompanionTheory.IwaAd.WhitKA → PositivityTheory.PfSWUS.WhitNDg := by
  intro hK D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ g
  obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n g
  obtain ⟨a, ha⟩ := exists_blkA hp
  obtain ⟨m, u, b, rfl, hm, hu⟩ := exists_levi_unip hp a ha
  have hbh : adj b = b := (exists_unip b).1 ⟨u, hu⟩
  exact whit_step hK hS hR hC hw hβ a hk hm ⟨b, hbh⟩ hu

end GlobalTheory.CompanionTheory.IwaAd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNondegenerateOfIwasawaStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_nondegenerate_of_iwasawa : GlobalTheory.CompanionTheory.IwaAd.WhitKA → PositivityTheory.PfSWUS.WhitNDg := by
  first | exact @GlobalTheory.CompanionTheory.IwaAd.iwaRedA | exact GlobalTheory.CompanionTheory.IwaAd.iwaRedA | (intros; apply GlobalTheory.CompanionTheory.IwaAd.iwaRedA <;> assumption)
end
end
end
