module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JordanExponentsMaximalHermitianLatticeBadPrime
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantModuleIsometriesEqNormOneResidues
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsGenericTermIffNoLocalDefectBaseFrames
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantModuleIsometriesEqNormOneResiduesStatement
open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discriminantModule_isometries_eq_normOne_residues : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ L 𝔭 b a → ∀ i, vF 𝔭 (a i) = 1 → (∀ j, j ≠ i → vF 𝔭 (a j) = 0) → discAut h ⊤ L 𝔭 = normRepCount K (extP K 𝔭 ^ 1) 1 1 := by
  first | exact @GlobalTheory.DiscAutLenOne.discAut_eq_normRepCount | exact GlobalTheory.DiscAutLenOne.discAut_eq_normRepCount | (intros; apply GlobalTheory.DiscAutLenOne.discAut_eq_normRepCount <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.JordanExponentsMaximalHermitianLatticeBadPrimeStatement
open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jordan_exponents_maximal_hermitian_lattice_bad_prime : ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V], IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ P ∈ badP h M, ∀ (b : Fin (Module.finrank K (⊤ : Submodule K V)) → V) (a : Fin (Module.finrank K (⊤ : Submodule K V)) → 𝓞 F), IsJordanIn h ⊤ M (P.comap (algebraMap (𝓞 F) (𝓞 K))) b a → ∃ i, vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a i) = 1 ∧ ∀ j, j ≠ i → vF (P.comap (algebraMap (𝓞 F) (𝓞 K))) (a j) = 0 := by
  first | exact @GlobalTheory.MaxLatExpo.main | exact GlobalTheory.MaxLatExpo.main | (intros; apply GlobalTheory.MaxLatExpo.main <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio
open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
open scoped Classical

namespace GlobalTheory.Mass.MaxFormula

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] in
theorem nondegenerate_of_pos {h : V →ₗ⋆[K] V →ₗ[K] K} [NumberField K] (hd : IsTotPosDef h) :
    h.Nondegenerate := by
  have han : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x h0 φ
    simp [hx] at this
  exact ⟨fun x hx => han x (hx x), fun x hx => han x (hx x)⟩

theorem localMassFactor_eq_of_mem_badPrimes (hK : IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) {P : Ideal (𝓞 K)}
    (hP : P ∈ badP h M) :
    lamP h M (P.comap (algebraMap (𝓞 F) (𝓞 K))) =
      ((qIn P : ℝ) ^ Module.finrank K V - (-1) ^ Module.finrank K V) / ((qIn P : ℝ) + 1) := by
  have hnd := nondegenerate_of_pos hd
  obtain ⟨hc, hq2, hq, -⟩ := (GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM).2.2.2 P hP
  have hPm : P.IsMaximal := hP.1
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  have h𝔭 : 𝔭.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) P
  obtain ⟨hJ1, hJ2⟩ := jordan_splitting_exists K F V hK hF h hs
  have hfull := hM.1.1
  have hlat := hfull.toIsLattice
  obtain ⟨b, a, hJ⟩ := hJ1 ⊤ M (fun x _ hx => hnd.1 x fun y => hx y trivial)
    ⟨hlat.fg, hfull.span_eq_top⟩ hM.1.2 𝔭 h𝔭
  obtain ⟨i, hi, hj⟩ := GlobalTheory.T.jordan_exponents_maximal_hermitian_lattice_bad_prime K F V hK hF h hs hd M hM P hP b a hJ
  have hv : vd h M 𝔭 = 1 := by
    rw [hJ2 M hlat 𝔭 h𝔭 b a hJ, vJof, Finset.sum_eq_single i (fun j _ => hj j) (by simp)]
    exact hi
  have hcJ : cJof 𝔭 a = 1 := by
    rw [cJof, Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun h1 => by_contra fun h2 => h1 (hj j h2), ?_⟩
    rintro rfl
    rw [hi]
    exact one_ne_zero
  have hN : Ideal.absNorm 𝔭 = qIn P := by
    have := absNorm_comap_inert hK hF hPm hc
    rw [hq] at this
    exact Nat.pow_left_injective two_ne_zero this
  have hη : etaF K F 𝔭 = -1 := by rw [h𝔭def, etaF_comap hK hF hPm, if_pos hc]
  have hdisc : (discAut h ⊤ M 𝔭 : ℝ) = (qIn P : ℝ) + 1 := by
    have hq0 : (qIn P : ℝ) ≠ 0 := by exact_mod_cast (by omega : qIn P ≠ 0)
    rw [GlobalTheory.T.discriminantModule_isometries_eq_normOne_residues K F V hK hF h hs M hlat 𝔭 h𝔭 b a hJ i hi hj,
      ThirdPropositionSlot.normRepCount_extP hK hF h𝔭 le_rfl, ThirdPropositionSlot.alphaStd_one, hη, hN]
    field_simp
    ring
  have hm : 1 ≤ Module.finrank K V := by
    have := i.pos
    rwa [finrank_top] at this
  obtain ⟨m, hm'⟩ : ∃ m, Module.finrank K V = m + 1 := ⟨_, (Nat.sub_add_cancel hm).symm⟩
  have hpos := alphaStd_pos hK hF h𝔭 m
  have hq0 : (0 : ℝ) < qIn P := by exact_mod_cast (by omega : 0 < qIn P)
  rw [lamP, alpha_discriminant_holds K F V hK hF h hs hd M hlat hM.1.2 𝔭 h𝔭 b a hJ, hv, hcJ, hdisc, hm',
    Nat.add_sub_cancel, mul_one]
  have hstep : alphaStd K 𝔭 (m + 1) =
      alphaStd K 𝔭 m * (1 - (-1) ^ (m + 1) * ((qIn P : ℝ) ^ (m + 1))⁻¹) := by
    rw [alphaStd, Finset.prod_Icc_succ_top (by omega), hη, hN, zpow_neg, zpow_natCast, ← hN, ← hη]
    rfl
  rw [hstep, hN]
  field_simp

theorem lamG_eq_lamMax (hK : IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : IsMaxLat h M) :
    lamG F h M = lamMax h M := by
  have hst := GlobalTheory.MaxLatStruct.main K V h hK hs (nondegenerate_of_pos hd) M hM
  have hfin := hst.1
  let g : {P // P ∈ hfin.toFinset} → {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} := fun P =>
    ⟨P.1.comap (algebraMap (𝓞 F) (𝓞 K)), by
      have : P.1.IsMaximal := (hfin.mem_toFinset.1 P.2).1
      exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) P.1⟩
  have hg : Function.Injective g := by
    intro P Q hPQ
    have hP := hfin.mem_toFinset.1 P.2
    have hQ := hfin.mem_toFinset.1 Q.2
    have := (comap_eq_comap_iff hK hF hP.1 hQ.1).1 (congrArg Subtype.val hPQ)
    rw [(hst.2.2.2 P.1 hP).1, or_self] at this
    exact Subtype.ext this.symm
  rw [lamG, lamMax, finprod_mem_eq_finite_toFinset_prod _ hfin,
    tprod_eq_prod (s := hfin.toFinset.attach.image g), Finset.prod_image fun _ _ _ _ e => hg e,
    ← Finset.prod_attach hfin.toFinset]
  · exact Finset.prod_congr rfl fun P _ => localMassFactor_eq_of_mem_badPrimes hK hF hs hd hM (hfin.mem_toFinset.1 P.2)
  · intro 𝔭 h𝔭
    obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
    have hlat := hM.1.1
    apply localMassFactor_of_valuation_eq_zero hK hF hs hd hlat hM.1.2 𝔭.2
    rw [← hP𝔭]
    refine (isUnimodularAt_iff_vd hK hF hs hd hlat hM.1.2 hP).1 (by_contra fun hb => h𝔭 ?_)
    exact Finset.mem_image.2 ⟨⟨P, hfin.mem_toFinset.2 ⟨hP, hb⟩⟩, Finset.mem_attach _ _,
      Subtype.ext hP𝔭⟩

theorem main : MaxMass := by
  intro K _ _ _ hK n hn
  obtain ⟨F, _, _, _, hF⟩ := exists_fixF K hK
  obtain ⟨c₁, -, hall⟩ := massConst_all binary_hermitian_represents liStat hK hF
  refine ⟨c₁ * ∏ j ∈ Finset.Icc 2 n, massRatioRightSide K j, fun V _ _ _ _ _ h hs hp hr M hM => ?_⟩
  have hd : IsTotPosDef h := fun x hx φ => hp φ x hx
  rw [hall n hn V h M hs hd hr hM.1.1 hM.1.2, lamG_eq_lamMax hK hF hs hd hM]

end GlobalTheory.Mass.MaxFormula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatioStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalHermitianLattice_massRatio : MaxMass := by
  first | exact @GlobalTheory.Mass.MaxFormula.main | exact GlobalTheory.Mass.MaxFormula.main | (intros; apply GlobalTheory.Mass.MaxFormula.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabLPIsLabelActK
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SerSys.LabDepth

open GlobalTheory.WeilDeligne

section Transport

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime]
  (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (i : ℚ_[p] ≃+* w.adicCompletion F) (hi : Continuous i)
include hw hi

theorem norm_symm_le (z : w.adicCompletion F) (hz : ‖z‖ ≤ 1) : ‖i.symm z‖ ≤ 1 := by
  by_contra h
  push Not at h
  set t := i.symm z with ht
  have ht0 : t ≠ 0 := by rintro h0; rw [h0, norm_zero] at h; linarith
  have h1 : ‖t⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h
  have h2 : ‖t⁻¹‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one t⁻¹ (-1)).2 (by simpa using h1)
    exact this
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h3 : ‖t⁻¹ / (p : ℚ_[p])‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p, div_le_one₀ (by have := (Fact.out : p.Prime).one_lt; positivity)]
    simpa using h2
  have h4 := GlobalTheory.TypeRec.Model.emb_le w p i.toRingHom hi _ h3
  have e : z⁻¹ = (p : w.adicCompletion F) * i.toRingHom (t⁻¹ / (p : ℚ_[p])) := by
    rw [map_div₀, map_inv₀, map_natCast]
    change z⁻¹ = (p : w.adicCompletion F) * ((i t)⁻¹ / p)
    rw [ht, RingEquiv.apply_symm_apply]
    have hpE : (p : w.adicCompletion F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    field_simp
  have h5 : ‖z⁻¹‖ < 1 := by
    rw [e, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h4) (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w p hw)
  have hz0 : z ≠ 0 := by rintro rfl; simp [ht] at ht0
  rw [norm_inv] at h5
  have := (one_le_inv₀ (norm_pos_iff.2 hz0)).2 hz
  linarith


omit hw in
theorem norm_symm_lt (z : w.adicCompletion F) (hz : ‖z‖ < 1) : ‖i.symm z‖ < 1 := by
  by_contra h
  push Not at h
  set t := i.symm z with ht
  have ht0 : t ≠ 0 := by rintro h0; rw [h0, norm_zero] at h; linarith
  have h1 : ‖t⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h
  have h4 := GlobalTheory.TypeRec.Model.emb_le w p i.toRingHom hi _ h1
  have e : i.toRingHom t⁻¹ = z⁻¹ := by
    rw [map_inv₀]; change (i t)⁻¹ = z⁻¹; rw [ht, RingEquiv.apply_symm_apply]
  rw [e, norm_inv] at h4
  have hz0 : z ≠ 0 := by rintro rfl; simp [ht] at ht0
  have := (one_lt_inv₀ (norm_pos_iff.2 hz0)).2 hz
  linarith

theorem exists_ker_red {n : ℕ} (u : GL (Fin n) (w.adicCompletion F))
    (hu : u ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion F) (Fin n)) :
    ∃ y : (GlobalTheory.GLp.red p n).ker, GlobalTheory.GLp.inc p n y = Matrix.GeneralLinearGroup.map i.symm.toRingHom u := by
  rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne w n).2, GlobalTheory.AdelicU.mem_princ_iff,
    GlobalTheory.AdelicU.mem_GLint_iff] at hu
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  have hM : ∀ a b, ‖i.symm (u.1 a b)‖ ≤ 1 := fun a b => norm_symm_le w p hw i hi _
    (Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h1 a b)))
  have hN : ∀ a b, ‖i.symm ((u⁻¹).1 a b)‖ ≤ 1 := fun a b => norm_symm_le w p hw i hi _
    (Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h2 a b)))
  let M : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun a b => ⟨i.symm (u.1 a b), hM a b⟩
  let N : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun a b => ⟨i.symm ((u⁻¹).1 a b), hN a b⟩
  have hMm : M.map (PadicInt.Coe.ringHom (p := p)) = u.1.map i.symm := rfl
  have hNm : N.map (PadicInt.Coe.ringHom (p := p)) = (u⁻¹).1.map i.symm := rfl
  have hinj : Function.Injective (Matrix.map · (PadicInt.Coe.ringHom (p := p)) : Matrix (Fin n) (Fin n) ℤ_[p] → _) :=
    Matrix.map_injective Subtype.coe_injective
  have e1 : M * N = 1 := hinj (by
    simp only
    rw [Matrix.map_mul, hMm, hNm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← RingEquiv.coe_toRingHom i.symm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
  have e2 : N * M = 1 := hinj (by
    simp only
    rw [Matrix.map_mul, hMm, hNm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← RingEquiv.coe_toRingHom i.symm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])
  let y : GL (Fin n) ℤ_[p] := ⟨M, N, e1, e2⟩
  have hy : GlobalTheory.GLp.red p n y = 1 := by
    refine Units.ext (Matrix.ext fun a b => ?_)
    change PadicInt.toZMod (M a b) = (1 : Matrix (Fin n) (Fin n) (ZMod p)) a b
    have h4 : M a b - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) a b ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      have h5 := norm_symm_lt w p i hi _ (Valued.toNormedField.norm_lt_one_iff.2 (h3 a b))
      convert h5 using 1
      rw [PadicInt.norm_def, PadicInt.coe_sub, Matrix.sub_apply, map_sub]
      congr 1
      by_cases hab : a = b
      · subst hab; simp; rfl
      · simp [Matrix.one_apply_ne hab]; rfl
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h4
    rw [h4]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  exact ⟨⟨y, hy⟩, Units.ext rfl⟩

end Transport

theorem exists_pull (D : D7) (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (π : QRep (D.host.g k) n)
    (hπ : IrrSm π) (hfix : fixK1 π.ρ ≠ ⊥) :
    ∃ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)),
      Nonempty (π ≅ pull I k v σ) ∧
      GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n)) ≠ ⊥ := by
  let _ := (I.i k v).toRingHom.toAlgebra
  have : ContinuousSMul ℚ_[D.host.g k] ((D.naut.plGw k v).adicCompletion D.host.E) :=
    continuousSMul_of_algebraMap _ _ (I.cont k v)
  let el : ℚ_[D.host.g k] ≃ₗ[ℚ_[D.host.g k]] (D.naut.plGw k v).adicCompletion D.host.E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (I.i k v).bijective
  have hi : Continuous (I.i k v).symm := by
    refine el.toContinuousLinearEquiv.symm.continuous.congr fun y => (I.i k v).injective ?_
    exact (el.toContinuousLinearEquiv.apply_symm_apply y).trans ((I.i k v).apply_symm_apply y).symm
  have hc : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) (I.i k v).symm.toRingHom) :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  have hg : ∀ g : GL (Fin n) ℚ_[D.host.g k], Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun a b => (I.i k v).symm_apply_apply _)
  refine ⟨⟨π, π.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom), fun x => (hπ.2 x).preimage hc,
    GlobalTheory.CuspRep.ParLaws.isIrreducible_comp ((GlobalTheory.GLp.Model.isIrrRep_iff _).1 hπ.1) _ fun g => ⟨_, hg g⟩⟩,
    ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ π) fun g => LinearMap.ext fun x => ?_)⟩, ?_⟩
  · change π.ρ g x = π.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g)) x
    rw [hg]
  · obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hfix
    refine (Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, hy0⟩
    obtain ⟨z, hz⟩ := exists_ker_red (D.naut.plGw k v) (D.host.g k) (D.naut.plGw_over k v) (I.i k v) (I.cont k v) u hu
    change π.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom u) y = y
    rw [← hz]
    have := (Submodule.mem_iInf _).1 hy z
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this

theorem tame_of_isTameWD {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x : WD h}
    (hx : GlobalTheory.LocLanglands.IsTameWD x) : x.tame := by
  obtain ⟨n, a, rfl, ha⟩ := hx
  refine (WD.tame_mk a).2 fun σ hσ => ha σ ⟨Wild_le_Ine hσ, fun y hy => ?_⟩
  have e : (σ : G E Ω) y - y = ((σ : G E Ω) y / y - 1) * y := by field_simp
  have h0 : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
  rw [e, map_mul]
  exact mul_lt_of_lt_one_left h0 (hσ y hy)

end GlobalTheory.SerSys.LabDepth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RMeasExAll
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RMeasAll

theorem rMeasEx_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (u u' : D.what₂.Word), (∀ τ, GoodW D τ u u' 1 (locW C u u' τ)) → RMeasEx hI C u u' := by
  intro D X Y hF hI C u u' hW t hG hr τ
  obtain ⟨_, _, h3, h4, h5, h6, h7, _⟩ := hW τ
  have hTu : 0 < Formalism.MainNotions.S.Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hTu' : 0 < Formalism.MainNotions.S.Tr D u' := Nat.cast_pos.2 (D.mem u').A.T_prime.pos
  obtain ⟨p, hp⟩ := Formalism.L2.SG.LoopTerm.relPtEx_holds hI C u u' t hG hr τ
  exact GlobalTheory.Amp.RootQuot.exists_rMeas D (locW C u u' τ) _ p h3 h4 (by rw [h5]; exact hTu) (by rw [h6]; exact hTu') h7 hp

end GlobalTheory.RMeasAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpUniMul
universe u_1

namespace GlobalTheory.UpperUnipotentProductFlagMeasures

theorem upUni_mul {R : Type u_1} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (h : Formalism.MainNotions.S.IsUpUni l) (h' : Formalism.MainNotions.S.IsUpUni l') : Formalism.MainNotions.S.IsUpUni (l * l') := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(h i k).1 hk, zero_mul]
    · rw [(h' k j).1 (lt_of_lt_of_le hji hk), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(h i i).2 rfl, (h' i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [(h i k).1 hk, zero_mul]
      · rw [(h' k i).1 hk, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

end GlobalTheory.UpperUnipotentProductFlagMeasures
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsAtPointOfRelevantTermRelevantFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsAtPointOfRelevantTermRelevantFinite
noncomputable section
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver

theorem terms_at_point_of_relevant : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t₀ : TauC Y u u', t₀.G ≠ 0 → t₀.relevant → ∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t₀ ∧ (∀ t : TauC Y u u', ptPN t = ptPN t₀ → t.relevant ∧ Gval (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1)) w) ∧ (GTerm.toTerm '' {t : TauC Y u u' | ptPN t = ptPN t₀}).Finite := by
  intro D X Y u u' t₀ hG hrel
  have hrows : IsRowReps D (X.Fu u) (Y.what₂ u) := Y.rowsOK u
  have hex : ∃ v, t₀.toTerm.atPt v ∧ t₀.toTerm.relevant := by
    obtain ⟨v, hv⟩ := Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' t₀.toTerm hG hrel
    exact ⟨v, hv, hrel⟩
  have hw₀ : t₀.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t₀.toTerm) := Formalism.L2.SG.PairVal.ptOf_spec _ hex
  refine ⟨Formalism.L2.SG.PairVal.ptOf t₀.toTerm, rfl, ?_⟩
  have key : ∀ t : TauC Y u u', ptPN t = ptPN t₀ →
      t.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf t₀.toTerm) ∧ t.toTerm.relevant := by
    intro t ht
    have hpt : Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.ptOf t₀.toTerm :=
      Formalism.L2.SG.Pf.FormRelPf.toPts_injective ht
    by_cases h : ∃ v, t.toTerm.atPt v ∧ t.toTerm.relevant
    · exact ⟨hpt ▸ Formalism.L2.SG.PairVal.ptOf_spec _ h, h.choose_spec.2⟩
    · exfalso
      have hj : Formalism.L2.SG.PairVal.ptOf t.toTerm = Formalism.L2.SG.PairVal.junkPoint D u u' := by
        unfold Formalism.L2.SG.PairVal.ptOf
        exact dif_neg h
      obtain ⟨F', -, hGv, hc⟩ := hw₀
      have he := Formalism.L2.SG.WConst.gPoint_eq_gval (lf D (X.Fu u)) F' _ hc
      rw [← hpt, hj] at he
      have hz := Formalism.L2.SG.PairVal.Gpt_junkPoint_eq_zero D u u'
      exact hGv (he.symm.trans hz)
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨hat, hr⟩ := key t ht
    have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam (hrows.1 t.lam t.mem)
    have hmk : Formalism.L2.SG.TermDef.mk t.toTerm.lam (lf D (X.Fu u)) (PD D t.toTerm.lam (lf D (X.Fu u)) u')
        (Quot.out t.toTerm.cls) = t.toTerm.cls := Quot.out_eq _
    have hA : Formalism.L2.SG.TermDef.AtPt t.toTerm.lam (lf D (X.Fu u)) (PD D t.toTerm.lam (lf D (X.Fu u)) u')
        (Formalism.L2.SG.TermDef.mk t.toTerm.lam (lf D (X.Fu u)) (PD D t.toTerm.lam (lf D (X.Fu u)) u')
          (Quot.out t.toTerm.cls)) (Formalism.L2.SG.PairVal.ptOf t₀.toTerm) := by
      rw [hmk]
      exact hat
    exact ⟨hr, (Formalism.L2.SG.TermDef.atPt_mk hTF.1 hTF.2.1 _ _).1 hA⟩
  · refine (Formalism.L2.SG.TermDef.term_atPt_finite (Formalism.L2.SG.Closed.TermsAtFinite_holds D u u') (D.sp.Y_sig 0)
      (X.Fu u) (Y.what₂ u) hrows (Formalism.L2.SG.PairVal.ptOf t₀.toTerm)).subset ?_
    rintro _ ⟨t, ht, rfl⟩
    exact (key t ht).1

end GlobalTheory.LocOver
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsAtPointOfRelevantTermRelevantFiniteStatement
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.terms_at_point_of_relevant_term_relevant_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t₀ : TauC Y u u', t₀.G ≠ 0 → t₀.relevant → ∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t₀ ∧ (∀ t : TauC Y u u', ptPN t = ptPN t₀ → t.relevant ∧ Gval (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1)) w) ∧ (GTerm.toTerm '' {t : TauC Y u u' | ptPN t = ptPN t₀}).Finite := by
  first | exact @GlobalTheory.LocOver.terms_at_point_of_relevant | exact GlobalTheory.LocOver.terms_at_point_of_relevant | (intros; apply GlobalTheory.LocOver.terms_at_point_of_relevant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericGenericTermsClosedUnderLocalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericGenericTermsClosedUnderLocalUnitary
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOrbit

theorem mem_ngSet_iff {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u') :
    t ∈ (Y.tO u u').ngSet ↔ t.G ≠ 0 ∧ ¬ t.generic := by
  show (if t.G = 0 then (0:ℝ) else 1) ≠ 0 ∧ ¬ t.generic ↔ _
  by_cases h : t.G = 0 <;> simp [h]

theorem mem_genSet_iff {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u') :
    t ∈ (Y.tO u u').genSet ↔ t.G ≠ 0 ∧ t.generic := by
  show (if t.G = 0 then (0:ℝ) else 1) ≠ 0 ∧ t.generic ↔ _
  by_cases h : t.G = 0 <;> simp [h]

theorem finrank_Vp_eq (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Ranks.r, Ranks.rS]
  omega

theorem img_inv_img {D : D7} (Z : LocDat D) (p : PlF D) (h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
    (A : Submodule (Z.M p).L.O (Vp D p)) : LocNG.img h⁻¹ (LocNG.img h A) = A := by
  ext x
  simp only [LocNG.img, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨h x, ⟨x, hx, rfl⟩, by simp⟩

theorem noBB_of_moved {D : D7} (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D)
    (hRel : (FP p).RelG (LocNG.theta (Z.M p))) (h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hh : h ∈ (FP p).UW0)
    (A B : Submodule (Z.M p).L.O (Vp D p)) (hAB : LocNG.img h A = B)
    (hB : ∀ d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = B → ¬ LocNG.BBne (H := locH Z p) τ) :
    ∀ d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = A → ¬ LocNG.BBne (H := locH Z p) τ := by
  intro d τ hτ hL hbb
  obtain ⟨act, hmv, -⟩ := GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_eq D p) hRel
  have hm : LocNG.Datum.Moves h d (act.smul ⟨h, hh⟩ d) := (hmv ⟨h, hh⟩ d _).2 rfl
  obtain ⟨h1, h2⟩ := GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_eq D p) hRel h hh d _ τ hτ hm
  exact hB _ _ h1 (by show LocNG.img h τ.abelian₂ = B; rw [hL, hAB]) (h2.2 hbb)

theorem closed_ng_gen : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → LocClosed F F' Z FP (Y.tO u u').ngSet ∧ LocClosed F F' Z FP (Y.tO u u').genSet ∧ (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ ∀ t ∈ (Y.tO u u').genSet, t.G ≠ 0 := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel
  have gen := fun t Λ hT => GlobalTheory.T.isGenericTerm_iff_no_localDefect_baseFrames D X Y u u' F F' w hw hG Z FP hB hRel t Λ hT
  have pt := fun t Λ hT => (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hw hG t Λ hT).1
  have back : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D), TG F F' t Λ → TG F F' t' Λ' →
      (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ') → t'.generic → t.generic := by
    intro t t' Λ Λ' hT hT' hloc hg
    rw [gen t Λ hT]
    rw [gen t' Λ' hT'] at hg
    intro p
    obtain ⟨h, hh, hAB⟩ := hloc p
    exact noBB_of_moved Z FP p (hRel p) h hh _ _ hAB (hg p)
  have fwd : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D), TG F F' t Λ → TG F F' t' Λ' →
      (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ') → t.generic → t'.generic := by
    intro t t' Λ Λ' hT hT' hloc hg
    rw [gen t' Λ' hT']
    rw [gen t Λ hT] at hg
    intro p
    obtain ⟨h, hh, hAB⟩ := hloc p
    exact noBB_of_moved Z FP p (hRel p) h⁻¹ (inv_mem hh) _ _ (by rw [← hAB, img_inv_img]) (hg p)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t t' Λ Λ' hT hT' hloc ht
    rw [mem_ngSet_iff] at ht ⊢
    exact ⟨pt t' Λ' hT', fun hg => ht.2 (back t t' Λ Λ' hT hT' hloc hg)⟩
  · intro t t' Λ Λ' hT hT' hloc ht
    rw [mem_genSet_iff] at ht ⊢
    exact ⟨pt t' Λ' hT', fwd t t' Λ Λ' hT hT' hloc ht.2⟩
  · intro t ht
    exact ((mem_ngSet_iff Y u u' t).1 ht).1
  · intro t ht
    exact ((mem_genSet_iff Y u u' t).1 ht).1

end GlobalTheory.LocOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericGenericTermsClosedUnderLocalUnitaryStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGeneric_generic_terms_closed_under_localUnitary : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → LocClosed F F' Z FP (Y.tO u u').ngSet ∧ LocClosed F F' Z FP (Y.tO u u').genSet ∧ (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ ∀ t ∈ (Y.tO u u').genSet, t.G ≠ 0 := by
  first | exact @GlobalTheory.LocOrbit.closed_ng_gen | exact GlobalTheory.LocOrbit.closed_ng_gen | (intros; apply GlobalTheory.LocOrbit.closed_ng_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FullExistsOfLocTied
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory

theorem fullExists_of_locTied : ∀ (D : D7) (X : HidaSetting D), Formalism.L2.SG.Pf.LocCP.LocTied D → Nonempty (Formalism.L2.SG.Full.Full X) := by

  intro D X hT
  exact Formalism.L2.SG.Pf.fullExists_tied Formalism.L2.SG.Pf.trExistsC_holds Formalism.L2.SG.Pf.lattice_steps_hold
    Formalism.L2.SG.Closed.LocCTied_holds D X (Formalism.L2.SG.Closed.level_subgroup_is_group X) hT

end GlobalTheory
end
