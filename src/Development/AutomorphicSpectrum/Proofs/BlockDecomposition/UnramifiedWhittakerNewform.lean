module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform
noncomputable section

open Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL mem_integralGL_iff)
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RankinSelberg

open Ad3 Ad3.R

def lowT {F : Type} [Field F] (a d : Fˣ) (z : F) : GL (Fin 2) F :=
  ⟨!![(a : F), 0; z, (d : F)], !![((a⁻¹ : Fˣ) : F), 0; -z * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F), ((d⁻¹ : Fˣ) : F)],
    by
      have ha := a.ne_zero
      have hd := d.ne_zero
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring,
    by
      have ha := a.ne_zero
      have hd := d.ne_zero
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem lowT_mem {a d : Fˣ} {z : F} (ha : (a : F) ∈ 𝒪[F]) (ha' : ((a⁻¹ : Fˣ) : F) ∈ 𝒪[F])
    (hd : (d : F) ∈ 𝒪[F]) (hd' : ((d⁻¹ : Fˣ) : F) ∈ 𝒪[F]) (hz : z ∈ 𝒪[F]) :
    lowT a d z ∈ integralGL F 2 := by
  have e1 : (lowT a d z : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; z, (d : F)] := rfl
  have e2 : ((lowT a d z)⁻¹ : GL (Fin 2) F).val =
      !![((a⁻¹ : Fˣ) : F), 0; -z * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F), ((d⁻¹ : Fˣ) : F)] := rfl
  rw [mem_integralGL_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [e1]
    fin_cases i <;> fin_cases j
    · exact ha
    · exact zero_mem _
    · exact hz
    · exact hd
  · rw [e2]
    fin_cases i <;> fin_cases j
    · exact ha'
    · exact zero_mem _
    · exact mul_mem (mul_mem (neg_mem hz) ha') hd'
    · exact hd'

private theorem mem_integers_iff_ord_nonneg' {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← normalizedValuation_le_one_iff, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

theorem le_ord_sub_one {n : ℕ} (hn : 1 ≤ n) {u : Fˣ} (hu : u ∈ unitFiltrationUnits F (n - 1))
    (h1 : (u : F) - 1 ≠ 0) : (n : ℤ) - 1 ≤ ord ((u : F) - 1) := by
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ (⟨v, hv⟩ : unitFiltration F (n - 1))
  have hF : ((unitsIncl F v : Fˣ) : F) - 1 = (ϖ : F) ^ (n - 1) * (a : F) := by
    rw [coe_unitsIncl]
    have := congrArg Subtype.val ha
    exact_mod_cast this
  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    apply hϖ.ne_zero
    exact Subtype.ext h
  have ha0 : (a : F) ≠ 0 := by
    intro h
    apply h1
    rw [hF, h, mul_zero]
  have hpow : ∀ k : ℕ, ord ((ϖ : F) ^ k) = k := by
    intro k
    induction k with
    | zero => simp [GroundTheory.LocalField.ord]
    | succ k ih =>
      rw [pow_succ, ord_mul (pow_ne_zero _ hϖ0) hϖ0, ih, ord_uniformizer hϖ]
      push_cast
      ring
  have ha' : 0 ≤ ord (a : F) := (mem_integers_iff_ord_nonneg' ha0).mp a.2
  rw [hF, ord_mul (pow_ne_zero _ hϖ0) ha0, hpow]
  push_cast [Nat.cast_sub hn]
  linarith

theorem unit_mem_integers {u : Fˣ} (hu : ord (u : F) = 0) : (u : F) ∈ 𝒪[F] := by
  exact (mem_integers_iff_ord_nonneg' u.ne_zero).mpr hu.ge

theorem ne_zero_of_ord {y : F} (hy : ord y = -1) : y ≠ 0 := by
  rintro rfl
  simp [GroundTheory.LocalField.ord] at hy

theorem entry_mem {n : ℕ} (hn : 1 ≤ n) {u : Fˣ} (hu : u ∈ unitFiltrationUnits F (n - 1))
    (h1 : (u : F) - 1 ≠ 0) {y : F} (hy : ord y = -1) :
    (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * (((u : F) - 1) * y⁻¹) ∈ 𝒪[F] ∧ ((u : F) - 1) * y⁻¹ ∈ 𝒪[F] := by
  have hy0 := ne_zero_of_ord hy
  have h0 : ((u : F) - 1) * y⁻¹ ≠ 0 := mul_ne_zero h1 (inv_ne_zero hy0)
  have hyi : ord y⁻¹ = 1 := by
    have := ord_units_inv (Units.mk0 y hy0)
    simpa [hy] using this
  have hz : (n : ℤ) ≤ ord (((u : F) - 1) * y⁻¹) := by
    rw [ord_mul h1 (inv_ne_zero hy0), hyi]
    linarith [le_ord_sub_one hn hu h1]
  have hpi : ord (((unifUnit F)⁻¹ ^ n : Fˣ) : F) = -n := by
    rw [← zpow_natCast, ord_units_zpow, ord_units_inv, ord_unifUnit]
    ring
  have hn0 : (0 : ℤ) ≤ n := by positivity
  constructor
  · rw [mem_integers_iff_ord_nonneg' (mul_ne_zero (Units.ne_zero _) h0), ord_mul (Units.ne_zero _) h0, hpi]
    linarith
  · rw [mem_integers_iff_ord_nonneg' h0]
    linarith

theorem lower_torus_conjugate_unipotent {u : Fˣ} {y : F} (hy : y ≠ 0) :
    lowT u 1 (((u : F) - 1) * y⁻¹) * uni2 y = uni2 y * lowT 1 u (((u : F) - 1) * y⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowT, Ad3.uni2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem unipotent_conj_moves_char : Ad3.R.U2 := by
  unfold Ad3.R.U2 Ad3.R.ForF
  intro F _ _ _ _ _ _ ψ _ ω _ hc y hy
  set n := quasiCharConductor ω with hn_def
  have hn : 1 ≤ n := hc
  have hnot : ¬ (unitFiltrationUnits F (n - 1) ≤ ω.ker) := by
    intro hle
    have : n ≤ n - 1 := Nat.sInf_le hle
    omega
  obtain ⟨u, hu, hωu⟩ := SetLike.not_le_iff_exists.mp hnot
  rw [MonoidHom.mem_ker] at hωu
  have h1 : (u : F) - 1 ≠ 0 := by
    intro h
    apply hωu
    have : u = 1 := Units.ext (sub_eq_zero.mp h)
    rw [this, map_one]
  have hord : ord (u : F) = 0 := by
    obtain ⟨v, -, hv⟩ := Subgroup.mem_map.mp hu
    rw [← hv, coe_unitsIncl]
    exact ord_unit v
  have hu1 : (u : F) ∈ 𝒪[F] := unit_mem_integers hord
  have hu2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := unit_mem_integers (by rw [ord_units_inv, hord, neg_zero])
  have h11 : ((1 : Fˣ) : F) ∈ 𝒪[F] := by
    rw [Units.val_one]
    exact one_mem _
  have h12 : (((1 : Fˣ)⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    rw [inv_one, Units.val_one]
    exact one_mem _
  have he := entry_mem hn hu h1 hy
  refine ⟨lowT u 1 (((u : F) - 1) * y⁻¹), 1, lowT 1 u (((u : F) - 1) * y⁻¹), u, ?_, ?_,
    lower_torus_conjugate_unipotent (ne_zero_of_ord hy), ?_⟩
  · unfold Ad3.R.GammaZeroLevelMembership
    exact ⟨lowT_mem hu1 hu2 h11 h12 he.2, he.1, rfl⟩
  · unfold Ad3.R.GammaZeroLevelMembership
    exact ⟨lowT_mem h11 h12 hu1 hu2 he.2, he.1, rfl⟩
  · rw [map_one]
    exact fun h => hωu h.symm

end GlobalTheory.CompanionTheory.RankinSelberg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewformStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_whittaker_newform : Ad3.R.U2 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | exact GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralProperties
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter
open Ad3.R Ad3

theorem countable_range : Countable (AdelicGLn.diagonal ℚ 2).range := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  haveI : Countable (GL (Fin 2) ℚ) := Function.Injective.countable (f := fun u : GL (Fin 2) ℚ => (u.val, u.inv)) (fun a b h => Units.ext (congrArg Prod.fst h))
  exact (Set.countable_range (AdelicGLn.diagonal ℚ 2)).to_subtype

theorem md_pos (a : Jd) : 0 < md a := (IdeleGroup.ideleModule ℚ a).2
theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md, map_mul]
theorem md_one : md 1 = 1 := by simp [md]
theorem continuous_md : Continuous md := continuous_subtype_val.comp IdeleGroup.continuous_ideleModule
theorem continuous_Dt : Continuous Dt := continuous_md.comp (AdelicGLn.continuous_det ℚ 2)
theorem Dt_pos (g : G2) : 0 < Dt g := md_pos _
theorem Dt_mul (g h : G2) : Dt (g * h) = Dt g * Dt h := by
  simp [Dt, map_mul, md_mul]
theorem Dt_inv (g : G2) : Dt g⁻¹ = (Dt g)⁻¹ := by
  have := Dt_mul g g⁻¹
  have h1 : Dt (1 : G2) = 1 := by simp [Dt, md_one]
  rw [mul_inv_cancel, h1] at this
  exact eq_inv_of_mul_eq_one_right this.symm
theorem Dt_dia (γ : GL (Fin 2) ℚ) : Dt (dia2 γ) = 1 := by
  have := Reduction.rationalGL_le_normOneGL (K := ℚ) (n := 2) ⟨γ, rfl⟩
  rw [Reduction.mem_normOneGL] at this
  exact this
theorem Dt_central (z : Jd) : Dt (dg2 z z) = md z ^ 2 := by
  have : GeneralLinearGroup.det (dg2 z z) = z * z := by
    ext
    simp [dg2, Matrix.det_fin_two]
  rw [Dt, this, md_mul, sq]

theorem exists_ne_one {η : HeckeCharacter ℚ} (h : η ≠ 1) : ∃ z : Jd, η.toIdele z ≠ 1 := by
  by_contra hc
  push_neg at hc
  apply h
  ext x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  have := hc z
  rw [HeckeCharacter.toIdele_apply] at this
  show ((η (IdeleClassGroup.mk ℚ z) : Circle) : ℂ) = ((1 : Circle) : ℂ)
  rw [this]

open scoped Pointwise

theorem measurableSet_band : MeasurableSet band := by
  have : band = Dt ⁻¹' Set.Ico 1 2 := by
    ext g; simp [band]
  rw [this]
  exact continuous_Dt.measurable measurableSet_Ico

theorem mem_band_dia {γ : GL (Fin 2) ℚ} {g : G2} : dia2 γ * g ∈ band ↔ g ∈ band := by
  simp [band, Dt_mul, Dt_dia]

theorem fundamental_domain_integral_central_vanishing : Ad3.R.G1a → Ad3.R.G1 := by
  intro hA μ 𝓕 mK 𝓓 hS F hF hB hL
  haveI := hS.haar
  haveI := hS.right
  obtain ⟨-, hz, hT⟩ := hA μ 𝓕 mK 𝓓 hS
  have hbM := measurableSet_band
  have Fm : Measurable F := hF.measurable
  have hIndL : LInv (band.indicator F) := by
    intro γ g
    by_cases hg : g ∈ band
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (mem_band_dia.2 hg), hL]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (mem_band_dia.1 h))]
  have hIndM : Measurable (band.indicator F) := Fm.indicator hbM
  have hI : ∀ f : G2 → ℂ, ∫ g in 𝓕 ∩ band, f g ∂μ = ∫ g in 𝓕, band.indicator f g ∂μ :=
    fun f => (setIntegral_indicator hbM).symm
  refine ⟨?_, ?_, ?_⟩
  · intro hC h
    obtain ⟨z, hz1, -⟩ := hz (Dt h)⁻¹ (inv_pos.2 (Dt_pos h))
    set Bh : Set G2 := {g | g * h⁻¹ ∈ band} with hBh
    have hBhM : MeasurableSet Bh :=
      hbM.preimage (continuous_id.mul continuous_const).measurable
    have hBhL : LInv (Bh.indicator F) := by
      intro γ g
      have hm : dia2 γ * g ∈ Bh ↔ g ∈ Bh := by
        simp only [hBh, Set.mem_setOf_eq, mul_assoc, mem_band_dia]
      by_cases hg : g ∈ Bh
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hL]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    have e1 : ∀ g, Bh.indicator F (g * h) = band.indicator (fun g => F (g * h)) g := by
      intro g
      have hm : g * h ∈ Bh ↔ g ∈ band := by simp [hBh]
      by_cases hg : g ∈ band
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg)]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    have e2 : ∀ g, band.indicator F (dg2 z z * g) = Bh.indicator F g := by
      intro g
      have hm : dg2 z z * g ∈ band ↔ g ∈ Bh := by
        have : Dt (dg2 z z * g) = Dt (g * h⁻¹) := by
          rw [Dt_mul, Dt_mul, Dt_central, hz1, Dt_inv, mul_comm]
        simp only [hBh, Set.mem_setOf_eq, band, this]
      by_cases hg : g ∈ Bh
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hC]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    rw [hI, hI]
    simp_rw [← e1]
    rw [(hT (fun g => g * h) (Or.inr (Or.inl ⟨h, rfl⟩))).2 _ (Fm.indicator hBhM) hBhL]
    simp_rw [← e2]
    exact (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hIndM hIndL
  · intro η hη hc hne
    obtain ⟨z0, h0⟩ := exists_ne_one hne
    obtain ⟨z1, hz1, hz1'⟩ := hz ((md z0) ^ 2)⁻¹ (inv_pos.2 (pow_pos (md_pos _) 2))
    set z : Jd := z0 * z1 with hzdef
    have hmd : md z ^ 2 = 1 := by
      rw [hzdef, md_mul, mul_pow, hz1]
      exact mul_inv_cancel₀ (pow_pos (md_pos _) 2).ne'
    have hηz : η.toIdele z ≠ 1 := by
      rw [hzdef, map_mul, hz1' η hη, mul_one]
      exact h0
    have hηz' : (η.toIdele z : ℂ) ≠ 1 := fun h => hηz (Circle.ext (by simpa using h))
    have e : ∀ g, band.indicator F (dg2 z z * g) = (η.toIdele z : ℂ) * band.indicator F g := by
      intro g
      have hm : dg2 z z * g ∈ band ↔ g ∈ band := by
        have : Dt (dg2 z z * g) = Dt g := by rw [Dt_mul, Dt_central, hmd, one_mul]
        simp only [band, Set.mem_setOf_eq, this]
      by_cases hg : g ∈ band
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hc]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h)), mul_zero]
    have key := (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hIndM hIndL
    simp_rw [e] at key
    rw [integral_const_mul] at key
    rw [hI]
    have : ((η.toIdele z : ℂ) - 1) * ∫ g in 𝓕, band.indicator F g ∂μ = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hηz')
  · intro hC hne hI0
    apply hne
    have hn : ∀ g, F g * conj (F g) = ((Complex.normSq (F g) : ℝ) : ℂ) := fun g => Complex.mul_conj _
    simp_rw [hn] at hI0
    rw [integral_complex_ofReal] at hI0
    have hI1 : ∫ g in 𝓕 ∩ band, Complex.normSq (F g) ∂μ = 0 := by exact_mod_cast hI0
    obtain ⟨C, hCb⟩ := hB
    have hmeas : MeasurableSet (𝓕 ∩ band) := hS.meas.inter hbM
    have hint : IntegrableOn (fun g => Complex.normSq (F g)) (𝓕 ∩ band) μ := by
      refine Measure.integrableOn_of_bounded (M := C ^ 2) hS.vol.ne
        (Complex.continuous_normSq.comp hF).aestronglyMeasurable ?_
      refine Eventually.of_forall fun g => ?_
      rw [Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCb g) 2
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun g => Complex.normSq_nonneg (F g)) hint).1 hI1
    set t : Set G2 := band ∩ {g | F g ≠ 0} with ht
    have h0 : μ (t ∩ 𝓕) = 0 := by
      have h1 := (ae_iff.1 ((ae_restrict_iff' hmeas).1 hae))
      refine measure_mono_null ?_ h1
      rintro g ⟨⟨hb, hf⟩, hg⟩
      simp only [Set.mem_setOf_eq, not_forall]
      exact ⟨⟨hg, hb⟩, by simpa using hf⟩
    have hinv : ∀ γ ∈ (AdelicGLn.diagonal ℚ 2).range, ∀ x : G2, γ * x ∈ t ↔ x ∈ t := by
      rintro _ ⟨δ, rfl⟩ x
      have e1 := hL δ x
      simp only [ht, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [show AdelicGLn.diagonal ℚ 2 δ * x = dia2 δ * x from rfl, mem_band_dia, e1]
    have hts : ∀ γ : (AdelicGLn.diagonal ℚ 2).range, γ • t = t := by
      intro γ
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
      exact hinv _ (γ⁻¹).2 x
    haveI := countable_range
    set_option synthInstance.maxHeartbeats 200000 in
    have hμt : μ t = 0 := hS.fd.measure_zero_of_invariant t hts h0
    set U : Set G2 := {g | 1 < Dt g ∧ Dt g < 2 ∧ F g ≠ 0} with hU
    have hUo : IsOpen U := by
      refine (isOpen_lt continuous_const continuous_Dt).inter
        ((isOpen_lt continuous_Dt continuous_const).inter (isOpen_ne_fun hF continuous_const))
    have hU0 : U = ∅ := hUo.eq_empty_of_measure_zero
      (measure_mono_null (show U ⊆ t from fun g hg => ⟨⟨hg.1.le, hg.2.1⟩, hg.2.2⟩) hμt)
    funext g
    by_contra hg
    obtain ⟨z, hz1, -⟩ := hz (3 / 2 / Dt g) (div_pos (by norm_num) (Dt_pos g))
    have hD : Dt (dg2 z z * g) = 3 / 2 := by
      rw [Dt_mul, Dt_central, hz1, div_mul_cancel₀ _ (Dt_pos g).ne']
    have hmem : dg2 z z * g ∈ U := by
      refine ⟨by rw [hD]; norm_num, by rw [hD]; norm_num, ?_⟩
      rw [hC]
      exact hg
    rw [hU0] at hmem
    exact hmem

end GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralPropertiesStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_integral_properties : Ad3.R.G1a → Ad3.R.G1 := by
  first | exact @GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing | exact GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing | (intros; apply GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows
open scoped ContDiff

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CutOff

section Row

variable {R : Type} [CommRing R] {k : ℕ}

def eRow (R : Type) [CommRing R] (k : ℕ) : Fin k → R := fun c => if (c : ℕ) + 1 = k then 1 else 0

def lastEnt (r : Fin k → R) : R := ∑ c : Fin k, if (c : ℕ) + 1 = k then r c else 0

def lastRowM (A : Matrix (Fin k) (Fin k) R) : Fin k → R := fun c => ∑ i : Fin k, if (i : ℕ) + 1 = k then A i c else 0

def rowM (r : Fin k → R) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i c => if (i : ℕ) + 1 = k then r c else (1 : Matrix (Fin k) (Fin k) R) i c

def rowI (r : Fin k → R) : Fin k → R :=
  fun c => if (c : ℕ) + 1 = k then Ring.inverse (lastEnt r) else -(r c * Ring.inverse (lastEnt r))

theorem rowM_apply_last (r : Fin k → R) (i c : Fin k) (h : (i : ℕ) + 1 = k) : rowM r i c = r c := by
  simp [rowM, h]

theorem rowM_apply_ne (r : Fin k → R) (i c : Fin k) (h : (i : ℕ) + 1 ≠ k) :
    rowM r i c = (1 : Matrix (Fin k) (Fin k) R) i c := by
  simp [rowM, h]

theorem lastEnt_eq (r : Fin k → R) (l : Fin k) (hl : (l : ℕ) + 1 = k) : lastEnt r = r l := by
  rw [lastEnt, Finset.sum_eq_single l]
  · simp [hl]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · simp

theorem rowM_mul_rowM (r t : Fin k → R) (l : Fin k) (hl : (l : ℕ) + 1 = k) (i c : Fin k) :
    (rowM r * rowM t) i c = if (i : ℕ) + 1 = k then
      (if (c : ℕ) + 1 = k then r l * t c else r c + r l * t c) else rowM t i c := by
  have hlast : ∀ j : Fin k, (j : ℕ) + 1 = k → j = l := fun j hj => Fin.ext (by omega)
  by_cases hi : (i : ℕ) + 1 = k
  · rw [if_pos hi, Matrix.mul_apply]
    have e : ∀ j, rowM r i j * rowM t j c =
        r j * (if j = l then t c else (1 : Matrix (Fin k) (Fin k) R) j c) := fun j => by
      rw [rowM_apply_last r i j hi]
      by_cases hj : j = l
      · subst hj; rw [rowM_apply_last t _ c hl, if_pos rfl]
      · rw [rowM_apply_ne t j c (fun h => hj (hlast j h)), if_neg hj]
    simp only [e]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    have e2 : ∀ j ∈ Finset.univ.erase l, r j * (if j = l then t c else (1 : Matrix (Fin k) (Fin k) R) j c) =
        if j = c then r j else 0 := fun j hj => by
      rw [if_neg (Finset.ne_of_mem_erase hj), Matrix.one_apply]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl e2, if_pos rfl, Finset.sum_ite_eq' ]
    by_cases hc : (c : ℕ) + 1 = k
    · have : c = l := hlast c hc
      subst this
      simp [hc]
    · have : c ≠ l := fun h => hc (h ▸ hl)
      simp [hc, this, add_comm]
  · rw [if_neg hi, Matrix.mul_apply]
    simp only [rowM_apply_ne r i _ hi, Matrix.one_apply]
    simp

variable {r : Fin k → R}

theorem rowM_mul_rowI (h : IsUnit (lastEnt r)) : rowM r * rowM (rowI r) = 1 := by
  ext i c
  by_cases hk : ∃ l : Fin k, (l : ℕ) + 1 = k
  · obtain ⟨l, hl⟩ := hk
    have hu : r l * Ring.inverse (r l) = 1 := by
      rw [← lastEnt_eq r l hl] at *
      exact Ring.mul_inverse_cancel _ h
    rw [rowM_mul_rowM _ _ l hl]
    have e : Ring.inverse (lastEnt r) = Ring.inverse (r l) := by rw [lastEnt_eq r l hl]
    by_cases hi : (i : ℕ) + 1 = k
    · have hil : i = l := Fin.ext (by omega)
      subst hil
      by_cases hc : (c : ℕ) + 1 = k
      · have hcl : c = i := Fin.ext (by omega)
        subst hcl
        simp only [if_pos hl, rowI, e, Matrix.one_apply, if_true]
        exact hu
      · have hcl : i ≠ c := fun h => hc (h ▸ hl)
        simp only [if_pos hl, if_neg hc, rowI, e, Matrix.one_apply, if_neg hcl]
        linear_combination (- r c) * hu
    · rw [if_neg hi, rowM_apply_ne _ _ _ hi]
  · exact absurd ⟨⟨k - 1, by have := i.2; omega⟩, by have := i.2; simp; omega⟩ hk

theorem rowI_mul_rowM (h : IsUnit (lastEnt r)) : rowM (rowI r) * rowM r = 1 := by
  ext i c
  by_cases hk : ∃ l : Fin k, (l : ℕ) + 1 = k
  · obtain ⟨l, hl⟩ := hk
    have hu : r l * Ring.inverse (r l) = 1 := by
      rw [← lastEnt_eq r l hl] at *
      exact Ring.mul_inverse_cancel _ h
    rw [rowM_mul_rowM _ _ l hl]
    have e : Ring.inverse (lastEnt r) = Ring.inverse (r l) := by rw [lastEnt_eq r l hl]
    have el : rowI r l = Ring.inverse (r l) := by simp [rowI, hl, e]
    by_cases hi : (i : ℕ) + 1 = k
    · have hil : i = l := Fin.ext (by omega)
      subst hil
      by_cases hc : (c : ℕ) + 1 = k
      · have hcl : c = i := Fin.ext (by omega)
        subst hcl
        simp only [if_pos hl, el, Matrix.one_apply, if_true]
        linear_combination hu
      · have hcl : i ≠ c := fun h => hc (h ▸ hl)
        simp only [if_pos hl, if_neg hc, el, Matrix.one_apply, if_neg hcl]
        simp only [rowI, if_neg hc, e]
        ring
    · rw [if_neg hi, rowM_apply_ne _ _ _ hi]
  · exact absurd ⟨⟨k - 1, by have := i.2; omega⟩, by have := i.2; simp; omega⟩ hk


open Classical in
def rowGL (r : Fin k → R) : GL (Fin k) R :=
  if h : IsUnit (lastEnt r) then ⟨rowM r, rowM (rowI r), rowM_mul_rowI h, rowI_mul_rowM h⟩ else 1

theorem rowGL_val (h : IsUnit (lastEnt r)) : (rowGL r).val = rowM r := by
  simp [rowGL, h]

theorem rowGL_inv_val (h : IsUnit (lastEnt r)) : ((rowGL r)⁻¹).val = rowM (rowI r) := by
  simp [rowGL, h]

theorem lastEnt_eRow (hk : 1 ≤ k) : lastEnt (eRow R k) = 1 := by
  rw [lastEnt_eq _ ⟨k - 1, by omega⟩ (by simp; omega)]
  simp [eRow]; omega

theorem rowM_eRow : rowM (eRow R k) = 1 := by
  ext i c
  by_cases hi : (i : ℕ) + 1 = k
  · rw [rowM_apply_last _ _ _ hi, eRow, Matrix.one_apply]
    by_cases hc : (c : ℕ) + 1 = k
    · rw [if_pos hc, if_pos (Fin.ext (by omega))]
    · rw [if_neg hc, if_neg (fun h : i = c => hc (h ▸ hi))]
  · rw [rowM_apply_ne _ _ _ hi]

theorem rowGL_eRow (hk : 1 ≤ k) : rowGL (eRow R k) = 1 := by
  by_cases h : IsUnit (lastEnt (eRow R k))
  · exact Units.ext ((rowGL_val h).trans rowM_eRow)
  · simp [rowGL, h]

theorem lastRow_mul_rowGL_inv (A : GL (Fin k) R) (h : IsUnit (lastEnt r)) (hA : lastRowM A.val = r) :
    Mir (k - 1) (A * (rowGL r)⁻¹) := by
  intro i j hij
  have hi : (i : ℕ) + 1 = k := by have := i.2; have := j.2; omega
  have e1 : ∀ m, A.val i m = rowM r i m := fun m => by
    rw [rowM_apply_last _ _ _ hi, ← hA, lastRowM, Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (by omega))
    · simp
  have e2 : (A * (rowGL r)⁻¹).val i j = (rowM r * rowM (rowI r)) i j := by
    rw [Units.val_mul, rowGL_inv_val h, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [e1]
  rw [e2, rowM_mul_rowI h]

end Row

section Adelic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def latS (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)) : AddSubgroup (Af E) where
  carrier := {a | (∀ w, w ∉ S → pLoc E w a ∈ Formalism.UG.Ov E w) ∧ ∀ w ∈ S, pLoc E w a ∈ B w}
  add_mem' := fun {a b} ha hb => ⟨fun w hw => by
      rw [map_add (pLoc E w)]
      exact add_mem (ha.1 w hw) (hb.1 w hw), fun w hw => by
      rw [map_add (pLoc E w)]
      exact add_mem (ha.2 w hw) (hb.2 w hw)⟩
  zero_mem' := ⟨fun w _ => by rw [map_zero]; exact zero_mem _, fun w _ => by rw [map_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun w hw => by
      rw [map_neg]; exact neg_mem (ha.1 w hw), fun w hw => by
      rw [map_neg]; exact neg_mem (ha.2 w hw)⟩


variable (E k) in
def nuFin : Measure (Fin k → Af E) := Measure.pi fun _ => GroundTheory.Global.finiteAdeleMeasure E

def boxL (L : Set (Af E)) (c : Fin k → Af E) : Set (Fin k → Af E) := {f | ∀ i, f i - c i ∈ L}

variable [_root_.NumberField.IsTotallyComplex E]


variable (E k) in
def nuInf : Measure (Fin k → Cinf E) :=
  (Measure.pi fun _ => GroundTheory.Global.infiniteAdeleMeasure E).map fun y i => (infEq E).symm (y i)

def glue (S : Finset (Pl E)) (a : GL (Fin k) (Cinf E)) (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) : GA E k :=
  (S.toList.map fun w => fl k w (u w)).prod * infGL E k a

def sOf (S : Finset (Pl E)) (y : Fin k → Ad E) : GA E k :=
  glue S (rowGL fun i => pInf E (y i)) fun w => rowGL fun i => pLoc E w (pFin E (y i))

def etaOf (b : (Fin k → Cinf E) → ℝ) (L : Set (Af E)) (y : Fin k → Ad E) : ℝ :=
  b (fun i => pInf E (y i)) * (boxL L (eRow (Af E) k)).indicator (fun _ => 1) fun i => pFin E (y i)

end Adelic

end GlobalTheory.CompanionTheory.CutOff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacter
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate

open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem mem_integer_iff_ord {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord hx]


omit [MeasurableSpace F] [BorelSpace F] in
theorem inv_mul_mem_of_ord_le {m y : F} (hm : m ≠ 0) (hy : y ≠ 0 → ord m ≤ ord y) :
    m⁻¹ * y ∈ 𝒪[F] := by
  rcases eq_or_ne y 0 with rfl | h0
  · simp
  · have := hy h0
    rw [mem_integer_iff_ord (mul_ne_zero (inv_ne_zero hm) h0), ord_mul (inv_ne_zero hm) h0,
      ord_inv hm]
    omega

omit [MeasurableSpace F] [BorelSpace F] in
theorem le_ord_of_mem {n : ℕ} {y : F} (h0 : y ≠ 0)
    (hc : (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * y ∈ 𝒪[F]) : (n : ℤ) ≤ ord y := by
  have e : ((unifUnit F)⁻¹ ^ n : Fˣ) = unifUnit F ^ (-(n : ℤ)) := by
    rw [inv_pow, _root_.zpow_neg, zpow_natCast]
  have h := (mem_integer_iff_ord (mul_ne_zero (Units.ne_zero _) h0)).1 hc
  rw [ord_mul (Units.ne_zero _) h0, e, ord_unifUnit_zpow] at h
  omega


omit [MeasurableSpace F] [BorelSpace F] in
theorem ord_lower_right {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin 2) F} {d : Fˣ} (h : GammaZeroLevelMembership n x d) :
    ord (d : F) = 0 := by
  obtain ⟨hx, hc, hd⟩ := h
  have hxi := ((GLnLocal.mem_integralGL_iff F 2).1 hx).1
  have hπ : ((unifUnit F : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have h0 : 0 ≤ ord (d : F) := (mem_integer_iff_ord d.ne_zero).1 (hd ▸ hxi 1 1)
  by_contra hne
  have h1 : ord ((unifUnit F : Fˣ) : F) ≤ ord (x 1 1) := by
    rw [ord_unifUnit, ← hd]; omega
  have hd' := inv_mul_mem_of_ord_le hπ (y := x 1 1) fun _ => h1
  have hc' := inv_mul_mem_of_ord_le hπ (y := x 1 0) fun h0 => by
    have := le_ord_of_mem h0 hc
    rw [ord_unifUnit]; omega
  have hdet : ((unifUnit F : Fˣ) : F)⁻¹ * (Matrix.GeneralLinearGroup.det x : F) ∈ 𝒪[F] := by
    have : ((unifUnit F : Fˣ) : F)⁻¹ * (Matrix.GeneralLinearGroup.det x : F) =
        x 0 0 * (((unifUnit F : Fˣ) : F)⁻¹ * x 1 1) -
          x 0 1 * (((unifUnit F : Fˣ) : F)⁻¹ * x 1 0) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
      ring
    rw [this]
    exact sub_mem (mul_mem (hxi 0 0) hd') (mul_mem (hxi 0 1) hc')
  have hz : ord (Matrix.GeneralLinearGroup.det x : F) = 0 := GodementSectionLocal.ord_det_eq_zero hx
  have hdn : (Matrix.GeneralLinearGroup.det x : F) ≠ 0 := Units.ne_zero _
  have := (mem_integer_iff_ord (mul_ne_zero (inv_ne_zero hπ) hdn)).1 hdet
  rw [ord_mul (inv_ne_zero hπ) hdn, ord_inv hπ, ord_unifUnit, hz] at this
  omega

end Local

theorem mem_Gamma0Level_of_places (N : ℕ) [NeZero N] (u : AdelicGLn.FiniteAdelicGL ℚ 2)
    (hint : ∀ v : Pl, glAt v u ∈ integralGL (Qv v) 2)
    (hlev : ∀ v : Pl, ((N : Qv v))⁻¹ * glAt v u 1 0 ∈ 𝒪[Qv v]) : u ∈ Gamma0Level N := by
  refine ⟨(AdelicGLn.mem_integralFiniteGL_iff_forall ℚ 2).2 fun v => ?_, ?_⟩
  · have e : (AdelicGLn.finiteRestrictedEquiv ℚ 2 u v : GL (Fin 2) (Qv v)) = glAt v u :=
      Units.ext (Matrix.ext fun a b => rfl)
    rw [e]
    exact hint v
  · rw [GL2Classical.mem_levelIdeal_iff, mem_integralFiniteAdeles]
    intro v
    have hw : adeleAt v ((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) = ((N : Qv v))⁻¹ := by
      have h1 : ((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) * (N : Af) = 1 := by
        rw [← GL2Classical.coe_levelUnit N, Units.inv_mul]
      have h2 := congrArg (adeleAt v) h1
      rw [map_mul, map_natCast, map_one] at h2
      exact eq_inv_of_mul_eq_one_left h2
    have e : (((((GL2Classical.levelUnit N)⁻¹ : Afˣ)) : Af) *
        (u : Matrix (Fin 2) (Fin 2) Af) 1 0) v = ((N : Qv v))⁻¹ * glAt v u 1 0 := by
      rw [← hw]
      exact map_mul (adeleAt v) _ _
    rw [e]
    exact (mem_valuationInteger_iff v _).1 (hlev v)

theorem exists_finEmb (h : G2) (hinf : ∀ w, infAt w h = 1) :
    ∃ u : AdelicGLn.FiniteAdelicGL ℚ 2, h = finEmb ℚ 2 u ∧ ∀ v : Pl, glAt v u = finAt v h := by
  refine ⟨(AdelicGLn.prodEquiv ℚ 2 h).2, ?_, fun v => Units.ext (Matrix.ext fun a b => rfl)⟩
  apply (AdelicGLn.prodEquiv ℚ 2).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext ?_ rfl
  apply (AdelicGLn.infiniteEquiv ℚ 2).injective
  funext w
  rw [map_one]
  exact hinf w

theorem lift_right {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    (hL : Lift k N f ω φ) {h : G2} (hinf : ∀ w, infAt w h = 1)
    (hint : ∀ v : Pl, finAt v h ∈ integralGL (Qv v) 2)
    (hlev : ∀ v : Pl, ((N : Qv v))⁻¹ * finAt v h 1 0 ∈ 𝒪[Qv v])
    (D : Afˣ) (hD : ∀ v, ord (lf v D : Qv v) = 0)
    (hD' : ∀ v, pOf v ∣ N → (lf v D : Qv v) = finAt v h 1 1) (g : G2) :
    φ (g * h) = (ω.toIdele (IdeleGroup.ofFinite D) : ℂ) * φ g := by
  obtain ⟨u, rfl, hu⟩ := exists_finEmb h hinf
  refine hL.level u (mem_Gamma0Level_of_places N u (fun v => ?_) fun v => ?_) D hD (fun v hv => ?_) g
  · rw [hu v]; exact hint v
  · rw [hu v]; exact hlev v
  · rw [hu v]; exact hD' v hv

theorem natCast_ne_zero_at (N : ℕ) [NeZero N] (v : Pl) : (N : Qv v) ≠ 0 := by
  have h : (algebraMap ℚ (Qv v)) (N : ℚ) ≠ 0 :=
    (map_ne_zero _).2 (Nat.cast_ne_zero.2 (NeZero.ne N))
  rwa [map_natCast] at h

theorem lf_one (v : Pl) : (lf v (1 : Afˣ) : Qv v) = 1 := by
  simp [lf]

theorem lift_right_good {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ}
    {φ : G2 → ℂ} (hord : ∀ v : Pl, ¬ pOf v ∣ N → ord (N : Qv v) = 0)
    (hL : Lift k N f ω φ) {h : G2} (hinf : ∀ w, infAt w h = 1)
    (hint : ∀ v : Pl, finAt v h ∈ integralGL (Qv v) 2)
    (hbad : ∀ v : Pl, pOf v ∣ N → finAt v h = 1) (g : G2) : φ (g * h) = φ g := by
  have key := lift_right hL hinf hint (fun v => ?_) 1 (fun v => ?_) (fun v hv => ?_) g
  · simpa using key
  · by_cases hv : pOf v ∣ N
    · rw [hbad v hv]; simp
    · refine inv_mul_mem_of_ord_le (natCast_ne_zero_at N v) fun h0 => ?_
      rw [hord v hv]
      exact (mem_integer_iff_ord h0).1 (((GLnLocal.mem_integralGL_iff _ 2).1 (hint v)).1 1 0)
  · rw [lf_one]; exact ord_one
  · rw [lf_one, hbad v hv]; simp

theorem ofFinite_toFinite_of_inf {a' d' : Jd} (h3 : ∀ w, infAt w (dg2 a' d' : G2) = 1) :
    IdeleGroup.ofFinite (IdeleGroup.toFinite ℚ d') = d' := by
  apply (IdeleGroup.prodEquiv ℚ).injective
  refine Prod.ext ?_ ?_
  · have e : (IdeleGroup.prodEquiv ℚ d').1 = 1 := by
      apply Units.ext
      funext w
      have h := congrArg (fun M : GL (Fin 2) _ => M 1 1) (h3 w)
      show (d' : 𝔸[ℚ]).1 w = 1
      simpa [dg2] using h
    rw [e]
    exact IdeleGroup.toInfinite_ofFinite _
  · exact IdeleGroup.toFinite_ofFinite _

theorem lift_local_invariance : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance := by
  intro hB k N _ hk χ hχ f a hf he ω φ hω hL
  obtain ⟨hloc, -, -, -, -, -, -, hid⟩ := hB
  have hordN : ∀ v : Pl, ord (N : Qv v) = N.factorization (pOf v) :=
    fun v => (hloc v).2.2.2.2.1 N (NeZero.ne N)
  have hgood : ∀ v : Pl, ¬ pOf v ∣ N → ord (N : Qv v) = 0 := fun v hv => by
    rw [hordN v, Nat.factorization_eq_zero_of_not_dvd hv]; rfl
  refine ⟨fun v hv x hx h hh g => ?_, fun v hv x d hxd h hh g => ?_, fun κ hκ hκ' g => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hh
    refine lift_right_good hgood hL h3 (fun v' => ?_) (fun v' hv' => ?_) g
    · by_cases e : v' = v
      · subst e; rw [h1]; exact hx
      · rw [h2 v' e]; exact one_mem _
    · refine h2 v' fun e => hv (e ▸ hv')
  · obtain ⟨h1, h2, h3⟩ := hh
    have hn : 1 ≤ N.factorization (pOf v) :=
      (hloc v).2.2.1.factorization_pos_of_dvd (NeZero.ne N) hv
    have hu : ord (d : Qv v) = 0 := ord_lower_right hn hxd
    obtain ⟨x', a', d', -, ⟨e1, e2, e3⟩, -, -, hc⟩ := hid v 0 1 d
    have hcomp : ∀ v' : Pl, (lf v' (IdeleGroup.toFinite ℚ d') : Qv v') =
        finAt v' (dg2 a' d' : G2) 1 1 := fun v' => rfl
    have hdv : (lf v (IdeleGroup.toFinite ℚ d') : Qv v) = d := by
      rw [hcomp v, e1]; simp [dg2]
    have hov : ∀ v' : Pl, v' ≠ v → (lf v' (IdeleGroup.toFinite ℚ d') : Qv v') = 1 := fun v' hv' => by
      rw [hcomp v', e2 v' hv']; simp
    have key := lift_right hL h3 (fun v' => ?_) (fun v' => ?_) (IdeleGroup.toFinite ℚ d')
      (fun v' => ?_) (fun v' hv' => ?_) g
    · rw [ofFinite_toFinite_of_inf e3, (hc ω).2] at key
      exact key
    · by_cases e : v' = v
      · subst e; rw [h1]; exact hxd.1
      · rw [h2 v' e]; exact one_mem _
    · by_cases e : v' = v
      · subst e
        rw [h1]
        refine inv_mul_mem_of_ord_le (natCast_ne_zero_at N v') fun h0 => ?_
        rw [hordN v']
        exact le_ord_of_mem h0 hxd.2.1
      · rw [h2 v' e]; simp
    · by_cases e : v' = v
      · subst e; rw [hdv]; exact hu
      · rw [hov v' e]; exact ord_one
    · by_cases e : v' = v
      · subst e; rw [hdv, h1]; exact hxd.2.2
      · rw [hov v' e, h2 v' e]; simp
  · exact lift_right_good hgood hL hκ (fun v' => κ.2.2 v') hκ' g

end GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacterStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_level_character : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance | exact GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangularStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_unitary_upper_triangular : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ), IsUnit g → ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ, g = k * b ∧ b.BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular | exact GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular | (intros; apply GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistedCentralizerDiagonal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistedCentralizerDiagonal
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.SwapCent

theorem twCent_swap : ∀ (H : Type) [Group H] (N : H),
    twCent ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (N, (1 : H)) =
      (twCent (MonoidHom.id H) N).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  intro H _ N
  ext ⟨a, b⟩
  constructor
  · intro h
    have h' : (a, b) * (N, (1 : H)) = (N, (1 : H)) * (b, a) := h
    have h1 : a * N = N * b := congrArg Prod.fst h'
    have h2 : b = a := by simpa using congrArg Prod.snd h'
    subst h2
    exact ⟨b, h1, rfl⟩
  · rintro ⟨x, hx, hxe⟩
    have hx' : x * N = N * x := hx
    have e1 : x = a := congrArg Prod.fst hxe
    have e2 : x = b := congrArg Prod.snd hxe
    subst e1
    subst e2
    change (x, x) * (N, (1 : H)) = (N, (1 : H)) * (x, x)
    simp [hx']

end GlobalTheory.CompanionTheory.SwapCent
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistedCentralizerDiagonalStatement
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_twisted_centralizer_diagonal : ∀ (H : Type) [Group H] (N : H), twCent ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (N, (1 : H)) = (twCent (MonoidHom.id H) N).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  first | exact @GlobalTheory.CompanionTheory.SwapCent.twCent_swap | exact GlobalTheory.CompanionTheory.SwapCent.twCent_swap | (intros; apply GlobalTheory.CompanionTheory.SwapCent.twCent_swap <;> assumption)
end
end
