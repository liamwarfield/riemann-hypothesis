module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticExistsIntegersUniformiser
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordInjectiveRangeMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussAtUniformiser
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueGaussIntegralNormForm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueGaussIntegralNormForm
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise

noncomputable section

namespace GlobalTheory.JR.ResidueGauss

theorem setIntegral_addChar_eq_zero {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (H : AddSubgroup G) (f : G → ℂ)
    (hf : ∀ x y, f (x + y) = f x * f y) (s₀ : G) (hs₀ : s₀ ∈ H) (hne : f s₀ ≠ 1) :
    ∫ x in (H : Set G), f x ∂μ = 0 := by
  have hmp : MeasurePreserving (fun x => s₀ + x) μ μ := measurePreserving_add_left μ s₀
  have hpre : (fun x => s₀ + x) ⁻¹' (H : Set G) = H := by
    ext x; simp [H.add_mem_cancel_left hs₀]
  have e := hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft s₀) f H
  rw [hpre] at e
  simp_rw [hf s₀] at e
  rw [integral_const_mul] at e
  have h : (f s₀ - 1) * ∫ x in (H : Set G), f x ∂μ = 0 := by rw [sub_mul, e]; ring
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hne)

theorem setIntegral_comp_mul_unit {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure R) [μ.IsAddHaarMeasure] (S : Set R) (u v : R) (huv : u * v = 1) (h0 : μ S ≠ 0)
    (hT : μ S ≠ ⊤) (hu : ∀ y ∈ S, u * y ∈ S) (hv : ∀ y ∈ S, v * y ∈ S) (g : R → ℂ) :
    ∫ y in S, g (u * y) ∂μ = ∫ y in S, g y ∂μ := by
  have hU : IsUnit u := ⟨⟨u, v, huv, by rw [mul_comm]; exact huv⟩, rfl⟩
  set w : Rˣ := hU.unit with hw
  have hwv : (w : R) = u := IsUnit.unit_spec hU
  have hvu : v * u = 1 := by rw [mul_comm]; exact huv
  have hwS : w • S = S := by
    ext y
    simp only [Set.mem_smul_set, Units.smul_def, hwv, smul_eq_mul]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hu z hz
    · intro hy; exact ⟨v * y, hv y hy, by rw [← mul_assoc, huv, one_mul]⟩
  have hΔ : distribHaarChar R w = 1 := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul h0 hT
    rw [hwS]; simp
  let e : R ≃ₜ R :=
    { toFun := fun y => u * y
      invFun := fun y => v * y
      left_inv := fun y => by simp only; rw [← mul_assoc, hvu, one_mul]
      right_inv := fun y => by simp only; rw [← mul_assoc, huv, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have hemb : MeasurableEmbedding (fun y => u * y) := e.toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun y => u * y) μ μ := by
    refine ⟨hemb.measurable, ?_⟩
    ext T hT'
    rw [Measure.map_apply hemb.measurable hT']
    have : (fun y => u * y) ⁻¹' T = w⁻¹ • T := by
      ext y
      rw [Set.mem_inv_smul_set_iff, Units.smul_def, hwv]
      rfl
    rw [this, ← distribHaarChar_mul, map_inv, hΔ]
    simp
  have hpre : (fun y => u * y) ⁻¹' S = S := by
    ext y
    constructor
    · intro hy
      have := hv _ hy
      simp only at this
      rwa [← mul_assoc, hvu, one_mul] at this
    · intro hy; exact hu y hy
  have := hmp.setIntegral_preimage_emb hemb g S
  rwa [hpre] at this

theorem setIntegral_swap_of_continuous {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (S : Set X) (T : Set Y) (hS : μ S ≠ ⊤) (hT : ν T ≠ ⊤) (g : X → Y → ℂ)
    (hg : Continuous (Function.uncurry g)) (hb : ∀ x y, ‖g x y‖ ≤ 1) :
    ∫ x in S, ∫ y in T, g x y ∂ν ∂μ = ∫ y in T, ∫ x in S, g x y ∂μ ∂ν := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hS.lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict T) := ⟨by simpa using hT.lt_top⟩
  apply integral_integral_swap
  exact Integrable.of_bound hg.aestronglyMeasurable 1 (Eventually.of_forall fun q => hb q.1 q.2)

theorem algebraMap_continuous_isCompact_preimage {F E : Type} [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [U : Unram F E] (A : Et F E) :
    Continuous (algebraMap A.K A.L) ∧
      ∀ O : Set A.L, IsCompact O → IsCompact (algebraMap A.K A.L ⁻¹' O) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨-, hinj, -, -, -⟩ := Et.quadratic_structure F E A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  let ιF : A.K →ₗ[F] A.L := (IsScalarTower.toAlgHom F A.K A.L).toLinearMap
  have hιF : ∀ s, ιF s = algebraMap A.K A.L s := fun s => rfl
  have hc : Continuous (algebraMap A.K A.L) := by
    have := IsModuleTopology.continuous_of_linearMap ιF
    exact this
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ιF (LinearMap.ker_eq_bot.2 hinj)
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  refine ⟨hc, fun O hO => ?_⟩
  refine (hO.image hrc).of_isClosed_subset (hO.isClosed.preimage hc) ?_
  intro s hs
  exact ⟨algebraMap A.K A.L s, hs, LinearMap.congr_fun hr s⟩

theorem residue_algebra {K L : Type} [CommRing K] [CommRing L] [StarRing L] [Algebra K L]
    (hK : IsField K) (hinj : Function.Injective (algebraMap K L)) (N : L → K)
    (hN : ∀ y, algebraMap K L (N y) = y * star y) (O : Subring L) (ϖ : Kˣ)
    (hOs : ∀ y ∈ O, star y ∈ O) (hϖO : algebraMap K L (ϖ : K) ∈ O)
    (hϖnu : ¬ ∃ z ∈ O, algebraMap K L (ϖ : K) * z = 1)
    (hdich : ∀ y ∈ O, (∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) ∨ ∃ z ∈ O, y * z = 1)
    (hnorm : ∀ s : K, algebraMap K L s ∈ O → (∃ r ∈ O, algebraMap K L s * r = 1) → ∃ w ∈ O, N w = s) :
    (∀ y ∈ O, (¬ ∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) →
      algebraMap K L (N y) ∈ O ∧ (¬ ∃ t, algebraMap K L t ∈ O ∧ N y = ϖ * t) ∧
        ∃ r, algebraMap K L r ∈ O ∧ N y * r = 1) ∧
    (∀ s, algebraMap K L s ∈ O → (¬ ∃ t, algebraMap K L t ∈ O ∧ s = ϖ * t) →
      (∃ r, algebraMap K L r ∈ O ∧ s * r = 1) ∧ ∃ w ∈ O, ∃ v ∈ O, w * v = 1 ∧ N w = s) := by
  set ι := algebraMap K L with hι
  have hNmul1 : ∀ y z, y * z = 1 → N y * N z = 1 := by
    intro y z h
    apply hinj
    rw [map_mul, hN, hN, map_one]
    calc y * star y * (z * star z) = (y * z) * star (y * z) := by rw [star_mul']; ring
      _ = 1 := by rw [h, star_one, one_mul]
  refine ⟨fun y hy hny => ?_, fun s hs hns => ?_⟩
  · have hNO : ι (N y) ∈ O := by rw [hN]; exact O.mul_mem hy (hOs y hy)
    obtain ⟨z, hz, hyz⟩ := (hdich y hy).resolve_left hny
    have h1 := hNmul1 y z hyz
    have hNz : ι (N z) ∈ O := by rw [hN]; exact O.mul_mem hz (hOs z hz)
    refine ⟨hNO, ?_, N z, hNz, h1⟩
    rintro ⟨t, ht, e⟩
    apply hϖnu
    refine ⟨ι t * ι (N z), O.mul_mem ht hNz, ?_⟩
    rw [← map_mul, ← map_mul, ← mul_assoc, ← e, h1, map_one]
  · have hsu : ∃ z ∈ O, ι s * z = 1 := by
      refine (hdich _ hs).resolve_left ?_
      rintro ⟨z, hz, e⟩
      apply hns
      refine ⟨((ϖ⁻¹ : Kˣ) : K) * s, ?_, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
      have : ι (((ϖ⁻¹ : Kˣ) : K) * s) = z := by
        rw [map_mul, e, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      rw [this]; exact hz
    obtain ⟨z, hz, hsz⟩ := hsu
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hsz
      have h10 : (1 : K) = 0 := hinj (by rw [map_one, map_zero]; exact hsz.symm)
      obtain ⟨x, y, hxy⟩ := hK.exists_pair_ne
      exact hxy (by rw [← one_mul x, ← one_mul y, h10, zero_mul, zero_mul])
    obtain ⟨r, hr⟩ := hK.mul_inv_cancel hs0
    have hzr : z = ι r := by
      calc z = ι (s * r) * z := by rw [hr, map_one, one_mul]
        _ = ι r := by rw [map_mul, mul_comm (ι s), mul_assoc, hsz, mul_one]
    have hrO : ι r ∈ O := hzr ▸ hz
    refine ⟨⟨r, hrO, hr⟩, ?_⟩
    obtain ⟨w, hw, hNw⟩ := hnorm s hs ⟨ι r, hrO, by rw [← map_mul, hr, map_one]⟩
    refine ⟨w, hw, star w * ι r, O.mul_mem (hOs w hw) hrO, ?_, hNw⟩
    rw [← mul_assoc, ← hN, hNw, ← map_mul, hr, map_one]

set_option maxHeartbeats 1000000 in
theorem residue_gauss_integral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → IsField A.K → IsField A.L → ∀ (O : Subring A.L) (ϖ : A.Kˣ), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) → μ {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z} = ENNReal.ofReal (A.absK (ϖ : A.K) ^ 2) * μ (O : Set A.L) → ∀ a : A.K, (∀ s : A.K, algebraMap A.K A.L s ∈ O → A.psiK ψ (a * ϖ * s) = 1) → (∃ s : A.K, algebraMap A.K A.L s ∈ O ∧ A.psiK ψ (a * s) ≠ 1) → ∫ y in (O : Set A.L), A.psiK ψ (a * A.NL y) ∂μ = -((A.absK (ϖ : A.K) : ℝ) : ℂ) * (((μ (O : Set A.L)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ U A ψ μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖnu hdich hnorm hvol a ha hna
  classical
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨-, hinj, hN, -, -⟩ := Et.quadratic_structure F E A
  obtain ⟨hιc, hιK⟩ := algebraMap_continuous_isCompact_preimage A
  obtain ⟨hψlc, hψn, -⟩ := (GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ
  obtain ⟨alg1, alg2⟩ := residue_algebra hK hinj A.NL hN O ϖ hOs hϖO hϖnu hdich hnorm
  set ι := algebraMap A.K A.L with hι
  set p : A.K := (ϖ : A.K) with hp

  set f : A.K → ℂ := fun t => A.psiK ψ (a * t) with hfdef
  have hfadd : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    simp only [hfdef, Et.psiK, mul_add, map_add (f := _), AddChar.map_add_eq_mul]
  have hfc : Continuous f := by
    have htr : Continuous (fun t : A.K => Algebra.trace F A.K t) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hψlc.continuous.comp (htr.comp (continuous_const.mul continuous_id))
  have hfn : ∀ t, ‖f t‖ = 1 := fun t => hψn _

  set OK : Subring A.K := O.comap ι with hOK
  have memOK : ∀ s, s ∈ OK ↔ ι s ∈ O := fun s => Iff.rfl
  set PK : Set A.K := ϖ • (OK : Set A.K) with hPK
  have memPK : ∀ s, s ∈ PK ↔ ∃ t, ι t ∈ O ∧ s = p * t := by
    intro s
    simp only [hPK, Set.mem_smul_set, SetLike.mem_coe, memOK, Units.smul_def, smul_eq_mul]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  set UK : Set A.K := (OK : Set A.K) \ PK with hUK
  set PL : Set A.L := {y | ∃ z ∈ O, y = ι p * z} with hPL
  set UL : Set A.L := (O : Set A.L) \ PL with hUL
  have hPKsub : PK ⊆ OK := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := (memPK s).1 hs
    exact (memOK _).2 (by rw [map_mul]; exact O.mul_mem hϖO ht)
  have hPLsub : PL ⊆ O := by
    rintro y ⟨z, hz, rfl⟩
    exact O.mul_mem hϖO hz
  have hPLeq : PL = (fun z => ι p * z) '' (O : Set A.L) := by
    ext y; simp only [hPL, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

  have hOKo : IsOpen (OK : Set A.K) := hOo.preimage hιc
  have hOKc : IsCompact (OK : Set A.K) := hιK _ hOc
  have hPKc : IsCompact PK := by
    rw [hPK]; exact hOKc.image (continuous_const_smul ϖ)
  have hPLc : IsCompact PL := by
    rw [hPLeq]; exact hOc.image (continuous_const.mul continuous_id)
  have hOKm : MeasurableSet (OK : Set A.K) := hOKc.isClosed.measurableSet
  have hPKm : MeasurableSet PK := hPKc.isClosed.measurableSet
  have hUKm : MeasurableSet UK := hOKm.diff hPKm
  have hOm : MeasurableSet (O : Set A.L) := hOc.isClosed.measurableSet
  have hPLm : MeasurableSet PL := hPLc.isClosed.measurableSet
  have hULm : MeasurableSet UL := hOm.diff hPLm
  have h1UK : (1 : A.K) ∈ UK := by
    refine ⟨(memOK 1).2 (by rw [map_one]; exact O.one_mem), fun h => hϖnu ?_⟩
    obtain ⟨t, ht, e⟩ := (memPK 1).1 h
    exact ⟨ι t, ht, by rw [← map_mul, ← e, map_one]⟩
  have hUKo : IsOpen UK := hOKo.sdiff hPKc.isClosed

  set μK : Measure A.K := Measure.addHaar with hμK
  set x : ℝ := A.absK p with hxdef
  have hx : x = (distribHaarChar A.K ϖ : ℝ) := EtMeas.absK_unit A ϖ
  have hx0 : 0 ≤ x := by rw [hx]; exact NNReal.coe_nonneg _
  have hOKT : μK OK ≠ ⊤ := hOKc.measure_lt_top.ne
  have hPKT : μK PK ≠ ⊤ := hPKc.measure_lt_top.ne
  have hUKT : μK UK ≠ ⊤ := (measure_mono Set.sdiff_subset).trans_lt hOKc.measure_lt_top |>.ne
  have hUK0 : μK UK ≠ 0 := hUKo.measure_ne_zero μK ⟨1, h1UK⟩
  have hOT : μ O ≠ ⊤ := hOc.measure_lt_top.ne
  have hO0 : μ O ≠ 0 := hOo.measure_ne_zero μ ⟨1, O.one_mem⟩
  set mK : ℝ := (μK OK).toReal with hmK
  set M : ℝ := (μ O).toReal with hM
  have hmPK : (μK PK).toReal = x * mK := by
    rw [hPK, ← distribHaarChar_mul, ENNReal.toReal_mul, hx]; rfl
  have hmUK : (μK UK).toReal = mK - x * mK := by
    rw [hUK, measure_sdiff hPKsub hPKm.nullMeasurableSet hPKT, ENNReal.toReal_sub_of_le (measure_mono hPKsub) hOKT,
      hmPK]
  have hmPL : (μ PL).toReal = x ^ 2 * M := by
    rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  have hmUL : (μ UL).toReal = M - x ^ 2 * M := by
    rw [hUL, measure_sdiff hPLsub hPLm.nullMeasurableSet (measure_ne_top_of_subset hPLsub hOT),
      ENNReal.toReal_sub_of_le (measure_mono hPLsub) hOT, hmPL]
  have hmUKpos : 0 < (μK UK).toReal := ENNReal.toReal_pos hUK0 hUKT

  have hf1 : ∀ m, ι m ∈ O → f (p * m) = 1 := by
    intro m hm
    simp only [hfdef]
    rw [← mul_assoc]; exact ha m hm
  have hNp : ∀ z, A.NL (ι p * z) = p * (p * A.NL z) := by
    intro z
    apply hinj
    rw [hN, map_mul, map_mul, hN, star_mul', A.star_K]
    ring

  set I : ℂ := ∫ y in (O : Set A.L), f (A.NL y) ∂μ with hIdef
  have hI1 : ∀ s ∈ UK, ∫ y in (O : Set A.L), f (s * A.NL y) ∂μ = I := by
    intro s hs
    obtain ⟨-, w, hw, v, hv, hwv, hNw⟩ :=
      alg2 s ((memOK s).1 hs.1) (fun ⟨t, ht, e⟩ => hs.2 ((memPK s).2 ⟨t, ht, e⟩))
    have key : ∀ y, A.NL (w * y) = s * A.NL y := by
      intro y
      apply hinj
      rw [hN, map_mul, hN, ← hNw, hN, star_mul']
      ring
    have := setIntegral_comp_mul_unit μ (O : Set A.L) w v hwv hO0 hOT (fun y hy => O.mul_mem hw hy)
      (fun y hy => O.mul_mem hv hy) (fun y => f (A.NL y))
    simp only [key] at this
    exact this

  have hIOK : IntegrableOn f OK μK := hfc.continuousOn.integrableOn_compact hOKc
  have hintOK : ∫ s in (OK : Set A.K), f s ∂μK = 0 := by
    obtain ⟨s₀, hs₀, hne⟩ := hna
    exact setIntegral_addChar_eq_zero μK OK.toAddSubgroup f hfadd s₀ hs₀ hne
  have hintPK : ∫ s in PK, f s ∂μK = (μK PK).toReal := by
    rw [setIntegral_congr_fun hPKm (g := fun _ => (1 : ℂ)) (fun s hs => by
      obtain ⟨t, ht, rfl⟩ := (memPK s).1 hs; exact hf1 t ht)]
    simp [Measure.real]
  have hintUK : ∫ s in UK, f s ∂μK = -((μK PK).toReal : ℂ) := by
    rw [hUK, setIntegral_sdiff hPKm hIOK hPKsub, hintOK, hintPK, zero_sub]
  have hUKmul : ∀ t ∈ UK, ∫ s in UK, f (s * t) ∂μK = -((μK PK).toReal : ℂ) := by
    intro t ht
    obtain ⟨⟨r, hr, htr⟩, -⟩ :=
      alg2 t ((memOK t).1 ht.1) (fun ⟨m, hm, e⟩ => ht.2 ((memPK t).2 ⟨m, hm, e⟩))
    have hcl : ∀ u v : A.K, u * v = 1 → ι u ∈ O → ι v ∈ O → ∀ s ∈ UK, u * s ∈ UK := by
      intro u v huv hu hv s hs
      refine ⟨(memOK _).2 (by rw [map_mul]; exact O.mul_mem hu hs.1), fun h => hs.2 ?_⟩
      obtain ⟨m, hm, e⟩ := (memPK _).1 h
      refine (memPK s).2 ⟨v * m, by rw [map_mul]; exact O.mul_mem hv hm, ?_⟩
      calc s = v * (u * s) := by rw [← mul_assoc, mul_comm v u, huv, one_mul]
        _ = p * (v * m) := by rw [e]; ring
    have := setIntegral_comp_mul_unit μK UK t r htr hUK0 hUKT (hcl t r htr ht.1 hr)
      (hcl r t (by rw [mul_comm]; exact htr) hr ht.1) f
    simp only [mul_comm _ t]
    rw [this, hintUK]
  have hJP : ∀ y ∈ PL, ∫ s in UK, f (s * A.NL y) ∂μK = (μK UK).toReal := by
    rintro y ⟨z, hz, rfl⟩
    rw [setIntegral_congr_fun hUKm (g := fun _ => (1 : ℂ)) (fun s hs => by
      simp only [hNp]
      rw [show s * (p * (p * A.NL z)) = p * (s * p * A.NL z) by ring]
      refine hf1 _ ?_
      rw [map_mul, map_mul, hN]
      exact O.mul_mem (O.mul_mem hs.1 hϖO) (O.mul_mem hz (hOs z hz)))]
    simp [Measure.real]
  have hJU : ∀ y ∈ UL, ∫ s in UK, f (s * A.NL y) ∂μK = -((μK PK).toReal : ℂ) := by
    intro y hy
    obtain ⟨h1, h2, -⟩ := alg1 y hy.1 hy.2
    exact hUKmul _ ⟨(memOK _).2 h1, fun h => h2 ((memPK _).1 h)⟩

  have hswap := setIntegral_swap_of_continuous μK μ UK (O : Set A.L) hUKT hOT (fun s y => f (s * A.NL y))
    (hfc.comp (continuous_fst.mul ((EtMeas.continuous_NL A).comp continuous_snd))) (fun s y => (hfn _).le)
  have hLHS : ∫ s in UK, ∫ y in (O : Set A.L), f (s * A.NL y) ∂μ ∂μK = (μK UK).toReal * I := by
    rw [setIntegral_congr_fun hUKm (g := fun _ => I) hI1]
    simp [Measure.real]
  have hOsplit : (O : Set A.L) = PL ∪ UL := (Set.union_sdiff_cancel hPLsub).symm
  have hRHS : ∫ y in (O : Set A.L), ∫ s in UK, f (s * A.NL y) ∂μK ∂μ =
      (μ PL).toReal * (μK UK).toReal + (μ UL).toReal * (-((μK PK).toReal : ℂ)) := by
    have hPLT : μ PL ≠ ⊤ := measure_ne_top_of_subset hPLsub hOT
    have hULT : μ UL ≠ ⊤ := measure_ne_top_of_subset Set.sdiff_subset hOT
    have i1 : IntegrableOn (fun y => ∫ s in UK, f (s * A.NL y) ∂μK) PL μ :=
      (integrableOn_const hPLT).congr_fun (fun y hy => (hJP y hy).symm) hPLm
    have i2 : IntegrableOn (fun y => ∫ s in UK, f (s * A.NL y) ∂μK) UL μ :=
      (integrableOn_const hULT).congr_fun (fun y hy => (hJU y hy).symm) hULm
    rw [hOsplit, setIntegral_union Set.disjoint_sdiff_right hULm i1 i2,
      setIntegral_congr_fun hPLm hJP, setIntegral_congr_fun hULm hJU]
    simp [Measure.real]
  rw [hLHS, hRHS] at hswap
  have hne : ((μK UK).toReal : ℂ) ≠ 0 := by exact_mod_cast hmUKpos.ne'
  apply mul_left_cancel₀ hne
  rw [hswap, hmUK, hmPL, hmUL, hmPK]
  push_cast
  ring

end GlobalTheory.JR.ResidueGauss
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueGaussIntegralNormFormStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_gauss_integral_norm_form : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → IsField A.K → IsField A.L → ∀ (O : Subring A.L) (ϖ : A.Kˣ), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) → μ {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z} = ENNReal.ofReal (A.absK (ϖ : A.K) ^ 2) * μ (O : Set A.L) → ∀ a : A.K, (∀ s : A.K, algebraMap A.K A.L s ∈ O → A.psiK ψ (a * ϖ * s) = 1) → (∃ s : A.K, algebraMap A.K A.L s ∈ O ∧ A.psiK ψ (a * s) ≠ 1) → ∫ y in (O : Set A.L), A.psiK ψ (a * A.NL y) ∂μ = -((A.absK (ϖ : A.K) : ℝ) : ℂ) * (((μ (O : Set A.L)).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.JR.ResidueGauss.residue_gauss_integral | exact GlobalTheory.JR.ResidueGauss.residue_gauss_integral | (intros; apply GlobalTheory.JR.ResidueGauss.residue_gauss_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureLUnitSmulAbsKSq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureLUnitSmulAbsKSq
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory.JR.ScaleHaarL

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ (c : A.Kˣ) (S : Set A.L), μ {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = ENNReal.ofReal (A.absK (c : A.K) ^ 2) * μ S := by
  intro F E _ _ _ _ U A μ hμ c S
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := GlobalTheory.JR.EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨⟨b⟩, -, -, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  let u : A.Lˣ := Units.map (algebraMap A.K A.L : A.K →* A.L) c
  have hu : (u : A.L) = algebraMap A.K A.L (c : A.K) := rfl
  have hset : {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = u • S := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, Units.smul_def, hu, smul_eq_mul]
    exact ⟨fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩, fun ⟨z, hz, h⟩ => ⟨z, hz, h.symm⟩⟩
  have hc1 : Continuous (b.equivFun.symm : (Fin 2 → A.K) → A.L) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F)
  have hc2 : Continuous (b.equivFun : A.L → (Fin 2 → A.K)) :=
    IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)
  let e : (Fin 2 → A.K) ≃ₜ+ A.L :=
    { b.equivFun.symm.toAddEquiv with
      continuous_toFun := hc1
      continuous_invFun := hc2 }
  have key : distribHaarChar A.L u = distribHaarChar A.K c ^ 2 := by
    rw [GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e c u (fun x => ?_),
      GlobalTheory.JR.ModuleNorm.distribHaarChar_pi_two]
    change b.equivFun.symm ((c : A.K) • x) = (u : A.L) * b.equivFun.symm x
    rw [map_smul, Algebra.smul_def, hu]
  rw [hset, ← distribHaarChar_mul μ u S, key, GlobalTheory.JR.EtMeas.absK_unit]
  rw [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.JR.ScaleHaarL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureLUnitSmulAbsKSqStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_L_unit_smul_absK_sq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ (c : A.Kˣ) (S : Set A.L), μ {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = ENNReal.ofReal (A.absK (c : A.K) ^ 2) * μ S := by
  first | exact @GlobalTheory.JR.ScaleHaarL.main | exact GlobalTheory.JR.ScaleHaarL.main | (intros; apply GlobalTheory.JR.ScaleHaarL.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticGaussIntegralStableOfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticGaussIntegralStableOfDualLattice
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilQuad

theorem gaussInt_stable_of_dual : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ (t : A.K) (M D : AddSubgroup A.L), IsOpen (M : Set A.L) → IsCompact (M : Set A.L) → IsOpen (D : Set A.L) → IsCompact (D : Set A.L) → (∀ m ∈ M, A.psiK ψ (t * x * A.NL m) = 1) → (D : Set A.L) = {y : A.L | ∀ m ∈ M, A.kerL ψ (t * x) y m = 1} → IsStableGauss A ψ x μ t (gaussInt A ψ x μ t (D : Set A.L)) := by
  intro F E _ _ _ _ hU A ψ x μ hψ hμ t M D hMo hMc hDo hDc hN hD
  obtain ⟨⟨bas⟩, hinj, hNL, hTr, -⟩ := Et.quadratic_structure F E A
  haveI : Module.Finite A.K A.L := Module.Finite.of_basis bas
  haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hpsi : ∀ u v : A.K, A.psiK ψ (u + v) = A.psiK ψ u * A.psiK ψ v := by
    intro u v
    simp only [Et.psiK, map_add (f := _), AddChar.map_add_eq_mul]
  have hNadd : ∀ y m : A.L, A.NL (y + m) = A.NL y + Algebra.trace A.K A.L (star y * m) + A.NL m := by
    intro y m
    apply hinj
    simp only [map_add (f := _), hNL, hTr, star_add, star_mul, star_star]
    ring
  set g : A.L → ℂ := fun y => A.psiK ψ (t * x * A.NL y) with hg
  have hgadd : ∀ y m : A.L, g (y + m) = g y * A.kerL ψ (t * x) y m * A.psiK ψ (t * x * A.NL m) := by
    intro y m
    simp only [hg, Et.kerL, ← hpsi, hNadd]
    congr 1
    ring
  have hkadd : ∀ y y' m : A.L, A.kerL ψ (t * x) (y + y') m = A.kerL ψ (t * x) y m * A.kerL ψ (t * x) y' m := by
    intro y y' m
    simp only [Et.kerL, ← hpsi, star_add, add_mul, map_add (f := _), mul_add]
  have hmemD : ∀ y, y ∈ D ↔ ∀ m ∈ M, A.kerL ψ (t * x) y m = 1 := fun y => Set.ext_iff.1 hD y
  have hMD : M ≤ D := by
    intro m hm
    rw [hmemD]
    intro m' hm'
    have h := hgadd m m'
    have h1 : g (m + m') = 1 := hN _ (M.add_mem hm hm')
    have h2 : g m = 1 := hN _ hm
    rw [h1, h2, hN _ hm'] at h
    simpa using h.symm

  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro y
    have c1 : Continuous (fun m : A.L => Algebra.trace A.K A.L (star y * m)) :=
      IsModuleTopology.continuous_of_linearMap
        (((Algebra.trace A.K A.L).comp (LinearMap.mulLeft A.K (star y))).restrictScalars F)
    have c2 : Continuous (fun m : A.L => Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))) :=
      (IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)).comp (continuous_const.mul c1)
    have hU0 : {m : A.L | m ∈ M ∧ ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1} ∈ 𝓝 (0 : A.L) := by
      have hM : (M : Set A.L) ∈ 𝓝 (0 : A.L) := hMo.mem_nhds M.zero_mem
      have h0 : Metric.closedBall (0 : F) 1 ∈ 𝓝 (Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * (0 : A.L)))) := by
        simp only [mul_zero, map_zero]
        exact Metric.closedBall_mem_nhds 0 one_pos
      have hbound : {m : A.L | ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1} ∈ 𝓝 (0 : A.L) :=
        Filter.mem_of_superset ((c2.continuousAt (x := (0 : A.L))).preimage_mem_nhds h0)
        (fun m hm => (show ‖Algebra.trace F A.K (t * x * Algebra.trace A.K A.L (star y * m))‖ ≤ 1 by
          simpa [Metric.mem_closedBall, dist_zero_right] using hm))
      filter_upwards [hM, hbound] with m hmM hmBound
      exact ⟨hmM, hmBound⟩
    have hU1 := (continuous_sub_right y).continuousAt.preimage_mem_nhds (by rw [sub_self]; exact hU0)
    refine ContinuousAt.congr (f := fun _ => g y) continuousAt_const ?_
    filter_upwards [hU1] with z hz
    show g y = g z
    obtain ⟨hzM, hz1⟩ := hz
    have := hgadd y (z - y)
    rw [add_sub_cancel] at this
    rw [this, hN _ hzM, Et.kerL, Et.psiK, hψ.1 _ hz1]
    simp

  refine ⟨D, hDo, hDc, fun Λ hΛo hΛc hDΛ => ?_⟩
  have hmeas : ∀ S : Set A.L, IsOpen S → MeasurableSet S := fun S hS => hS.measurableSet
  have hint : IntegrableOn g (Λ : Set A.L) μ := hgc.continuousOn.integrableOn_compact' hΛc (hmeas _ hΛo)
  have hsplit : (Λ : Set A.L) = (D : Set A.L) ∪ ((Λ : Set A.L) \ (D : Set A.L)) :=
    (Set.union_diff_cancel (show (D : Set A.L) ⊆ Λ from hDΛ)).symm

  haveI : DiscreteTopology (A.L ⧸ D) := QuotientAddGroup.discreteTopology hDo
  have hmk : Continuous (QuotientAddGroup.mk : A.L → A.L ⧸ D) := continuous_quot_mk
  set S : A.L ⧸ D → Set A.L := fun q => ((Λ : Set A.L) \ (D : Set A.L)) ∩ QuotientAddGroup.mk ⁻¹' {q} with hS
  have hSo : ∀ q, MeasurableSet (S q) := fun q =>
    ((hmeas _ hΛo).diff (hmeas _ hDo)).inter (hmeas _ ((isOpen_discrete {q}).preimage hmk))
  have hzero : ∀ q, ∫ y in S q, g y ∂μ = 0 := by
    intro q
    by_cases hne : (S q).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, integral_zero_measure]
    obtain ⟨y₀, ⟨hy₀Λ, hy₀D⟩, hy₀q⟩ := hne
    have hy₀ : ¬ ∀ m ∈ M, A.kerL ψ (t * x) y₀ m = 1 := fun h => hy₀D ((hmemD y₀).2 h)
    push_neg at hy₀
    obtain ⟨m₀, hm₀, hc⟩ := hy₀
    have hm₀D : m₀ ∈ D := hMD hm₀
    have hshift : ∀ y ∈ S q, g (m₀ + y) = A.kerL ψ (t * x) y₀ m₀ * g y := by
      intro y hy
      obtain ⟨-, hyq⟩ := hy
      have hrel : -y₀ + y ∈ D := by
        rw [← QuotientAddGroup.eq]
        exact (hy₀q.trans hyq.symm)
      have h1 : A.kerL ψ (t * x) y m₀ = A.kerL ψ (t * x) y₀ m₀ := by
        have := hkadd y₀ (-y₀ + y) m₀
        rw [add_neg_cancel_left, (hmemD _).1 hrel m₀ hm₀, mul_one] at this
        exact this
      rw [add_comm, hgadd, h1, hN _ hm₀]
      ring
    have hpre : (fun y => m₀ + y) ⁻¹' (S q) = S q := by
      ext y
      simp only [hS, Set.mem_preimage, Set.mem_inter_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
      have e1 : m₀ + y ∈ Λ ↔ y ∈ Λ := ⟨fun h => by simpa using Λ.sub_mem h (hDΛ hm₀D), fun h => Λ.add_mem (hDΛ hm₀D) h⟩
      have e2 : m₀ + y ∈ D ↔ y ∈ D := ⟨fun h => by simpa using D.sub_mem h hm₀D, fun h => D.add_mem hm₀D h⟩
      have e3 : (QuotientAddGroup.mk (m₀ + y) : A.L ⧸ D) = QuotientAddGroup.mk y := by
        rw [QuotientAddGroup.eq]
        simpa using D.neg_mem hm₀D
      rw [e1, e2, e3]
    have htr := (measurePreserving_add_left μ m₀).setIntegral_preimage_emb (measurableEmbedding_addLeft m₀) g (S q)
    rw [hpre] at htr
    have h2 : ∫ y in S q, g (m₀ + y) ∂μ = A.kerL ψ (t * x) y₀ m₀ * ∫ y in S q, g y ∂μ := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun (hSo q) (fun y hy => hshift y hy)
    rw [h2] at htr
    have h3 : (A.kerL ψ (t * x) y₀ m₀ - 1) * ∫ y in S q, g y ∂μ = 0 := by rw [sub_mul, htr]; ring
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc)
  have hfin : (QuotientAddGroup.mk '' (Λ : Set A.L) : Set (A.L ⧸ D)).Finite :=
    (hΛc.image hmk).finite_of_discrete
  have hunion : ((Λ : Set A.L) \ (D : Set A.L)) = ⋃ q ∈ hfin.toFinset, S q := by
    ext y
    simp only [hS, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hy
      exact ⟨_, ⟨y, hy.1, rfl⟩, hy, rfl⟩
    · rintro ⟨_, _, hy, _⟩
      exact hy
  have hrest : ∫ y in (Λ : Set A.L) \ (D : Set A.L), g y ∂μ = 0 := by
    rw [hunion, integral_biUnion_finset]
    · exact Finset.sum_eq_zero (fun q _ => hzero q)
    · exact fun q _ => hSo q
    · intro q₁ _ q₂ _ hq
      refine Set.disjoint_left.2 ?_
      rintro y ⟨-, h1⟩ ⟨-, h2⟩
      exact hq ((Set.mem_singleton_iff.1 h1).symm.trans (Set.mem_singleton_iff.1 h2))
    · exact fun q _ => hint.mono_set (fun y hy => hy.1.1)
  show ∫ y in (Λ : Set A.L), g y ∂μ = ∫ y in (D : Set A.L), g y ∂μ
  rw [hsplit, setIntegral_union Set.disjoint_sdiff_right ((hmeas _ hΛo).diff (hmeas _ hDo))
    (hint.mono_set hDΛ) (hint.mono_set Set.diff_subset), hrest, add_zero]

end GlobalTheory.JR.WeilQuad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticGaussIntegralStableOfDualLatticeStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticGaussIntegral_stable_of_dual_lattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ (t : A.K) (M D : AddSubgroup A.L), IsOpen (M : Set A.L) → IsCompact (M : Set A.L) → IsOpen (D : Set A.L) → IsCompact (D : Set A.L) → (∀ m ∈ M, A.psiK ψ (t * x * A.NL m) = 1) → (D : Set A.L) = {y : A.L | ∀ m ∈ M, A.kerL ψ (t * x) y m = 1} → IsStableGauss A ψ x μ t (gaussInt A ψ x μ t (D : Set A.L)) := by
  first | exact @GlobalTheory.JR.WeilQuad.gaussInt_stable_of_dual | exact GlobalTheory.JR.WeilQuad.gaussInt_stable_of_dual | (intros; apply GlobalTheory.JR.WeilQuad.gaussInt_stable_of_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussAtUniformiser
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.WeilQuad.NonNorm

section Help
open scoped Pointwise
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem stable_unique (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K)
    {G G' : ℂ} (h : IsStableGauss A ψ x μ u G) (h' : IsStableGauss A ψ x μ u G') : G = G' := by
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  obtain ⟨Λ₀, ho, hc, hG⟩ := h
  obtain ⟨Λ₁, ho', hc', hG'⟩ := h'
  have hs : ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) = (Λ₀ : Set A.L) + (Λ₁ : Set A.L) :=
    AddSubgroup.add_normal Λ₀ Λ₁
  have hO : IsOpen ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := AddSubgroup.isOpen_mono le_sup_left ho
  have hC : IsCompact ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := by rw [hs]; exact hc.add hc'
  rw [← hG _ hO hC le_sup_left, ← hG' _ hO hC le_sup_right]

theorem NL_algebraMap [Unram F E] (A : Et F E) (c : A.K) : A.NL (algebraMap A.K A.L c) = c ^ 2 := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [hN, A.star_K, map_pow, sq]

theorem absK_zpow (A : Et F E) (u : A.Kˣ) (n : ℤ) :
    A.absK ((u ^ n : A.Kˣ) : A.K) = A.absK (u : A.K) ^ n := by
  simp [Et.absK, map_zpow]

theorem absK_pos (A : Et F E) (u : A.Kˣ) : 0 < A.absK (u : A.K) := by
  simp only [Et.absK, Units.isUnit, dite_true, IsUnit.unit_of_val_units]
  exact_mod_cast ((Group.isUnit u).map (distribHaarChar A.K)).ne_zero.bot_lt

theorem dual_mul (A : Et F E) (ψ : AddChar F ℂ) (O : Subring A.L) (t a : A.K) :
    {y : A.L | ∀ m ∈ O, A.kerL ψ (t * a) y m = 1} =
      {y : A.L | ∀ m ∈ O, A.kerL ψ a (algebraMap A.K A.L t * y) m = 1} := by
  ext y
  simp only [Set.mem_setOf_eq, Et.kerL]
  refine forall₂_congr fun m _ => ?_
  have : Algebra.trace A.K A.L (star (algebraMap A.K A.L t * y) * m) =
      t * Algebra.trace A.K A.L (star y * m) := by
    rw [star_mul', A.star_K, mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [this, mul_comm t a, mul_assoc]

theorem scaled_mul (A : Et F E) (O : Subring A.L) (t c : A.Kˣ) :
    {y : A.L | algebraMap A.K A.L (t : A.K) * y ∈ {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (c : A.K) * z}} =
      {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((t⁻¹ * c : A.Kˣ) : A.K) * z} := by
  ext y
  simp only [Set.mem_setOf_eq, Units.val_mul, map_mul]
  refine exists_congr fun z => and_congr_right fun _ => ?_
  have h1 : algebraMap A.K A.L ((t⁻¹ : A.Kˣ) : A.K) * algebraMap A.K A.L (t : A.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  constructor
  · intro h; rw [← one_mul y, ← h1, mul_assoc, h, ← mul_assoc]
  · intro h; rw [h, ← mul_assoc, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

end Help

section Levels
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem kerL_mul_left (A : Et F E) (ψ : AddChar F ℂ) (a c : A.K) (y m : A.L) :
    A.kerL ψ a (algebraMap A.K A.L c * y) m = A.kerL ψ a y (algebraMap A.K A.L c * m) := by
  simp only [Et.kerL]
  rw [star_mul', A.star_K]
  ring_nf

theorem kerL_one (A : Et F E) (ψ : AddChar F ℂ) (a : A.K) (m : A.L) :
    A.kerL ψ a 1 m = A.psiK ψ (a * Algebra.trace A.K A.L m) := by
  simp [Et.kerL]

theorem trace_algebraMap_mul (A : Et F E) (c : A.K) (w : A.L) :
    Algebra.trace A.K A.L (algebraMap A.K A.L c * w) = c * Algebra.trace A.K A.L w := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem level0 : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ O : Subring A.L, IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) → ∀ t : A.K, {y : A.L | ∀ m ∈ O, A.kerL ψ (t * x) y m = 1} = (O : Set A.L) → IsStableGauss A ψ x μ t (((μ (O : Set A.L)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ A ψ x μ hψ hμ O hOo hOc hOs htr t hD
  obtain ⟨-, -, hN, htrL, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have h1 : (1 : A.L) ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (t * x) y m = 1} := by rw [hD]; exact O.one_mem
  have hM : ∀ m ∈ O, A.psiK ψ (t * x * A.NL m) = 1 := fun m hm => by
    obtain ⟨z, hz, hzs⟩ := htr (A.NL m) (by rw [hN]; exact O.mul_mem hm (hOs m hm))
    have := h1 z hz
    rwa [kerL_one, hzs] at this
  have hDeq : ((O.toAddSubgroup : AddSubgroup A.L) : Set A.L) =
      {y : A.L | ∀ m ∈ O.toAddSubgroup, A.kerL ψ (t * x) y m = 1} := by
    simpa using hD.symm
  have hG := GlobalTheory.T.quadraticGaussIntegral_stable_of_dual_lattice F E A ψ x μ hψ hμ t O.toAddSubgroup O.toAddSubgroup hOo hOc hOo hOc
    (fun m hm => hM m hm) hDeq
  convert hG using 1
  simp only [gaussInt, Subring.coe_toAddSubgroup]
  rw [setIntegral_congr_fun hOo.measurableSet (g := fun _ => (1 : ℂ)) (fun y hy => hM y hy)]
  simp [Measure.real]

end Levels

section Level1
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def scaledSub (A : Et F E) (O : Subring A.L) (c : A.K) : AddSubgroup A.L where
  carrier := {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L c * z}
  add_mem' := by
    rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    exact ⟨z + z', O.add_mem hz hz', by ring⟩
  zero_mem' := ⟨0, O.zero_mem, by simp⟩
  neg_mem' := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨-z, O.neg_mem hz, by ring⟩

def mulHomeo [Unram F E] (A : Et F E) (c : A.Kˣ) : A.L ≃ₜ A.L :=
  haveI := GlobalTheory.JR.EtMeas.finite_L A
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  { toFun := fun y => algebraMap A.K A.L (c : A.K) * y
    invFun := fun y => algebraMap A.K A.L ((c⁻¹ : A.Kˣ) : A.K) * y
    left_inv := fun y => by
      simp only [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    right_inv := fun y => by
      simp only [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    continuous_toFun := continuous_const.mul continuous_id
    continuous_invFun := continuous_const.mul continuous_id }

theorem scaledSub_eq_image [Unram F E] (A : Et F E) (O : Subring A.L) (c : A.Kˣ) :
    ((scaledSub A O c : AddSubgroup A.L) : Set A.L) = mulHomeo A c '' (O : Set A.L) := by
  ext y
  simp only [scaledSub, AddSubgroup.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk,
    Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

theorem level1 : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → IsField A.K → IsField A.L → ∀ (O : Subring A.L) (ϖ : A.Kˣ), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) → μ {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z} = ENNReal.ofReal (A.absK (ϖ : A.K) ^ 2) * μ (O : Set A.L) → ∀ t : A.K, {y : A.L | ∀ m ∈ O, A.kerL ψ (t * x) y m = 1} = {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z} → IsStableGauss A ψ x μ t (-((A.absK (ϖ : A.K) : ℝ) : ℂ) * (((μ (O : Set A.L)).toReal : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ A ψ x μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖu hdich htr hnorm hsc t hD
  obtain ⟨-, hinj, hN, htrL, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hmemD : ∀ y : A.L, (∀ m ∈ O, A.kerL ψ (t * x) y m = 1) ↔ ∃ z ∈ O, y = algebraMap A.K A.L ϖ * z := fun y => by
    have := congrArg (y ∈ ·) hD
    simpa using this

  have hϖD : ∀ m ∈ O, A.kerL ψ (t * x) (algebraMap A.K A.L ϖ) m = 1 := (hmemD _).2 ⟨1, O.one_mem, by simp⟩
  have hψϖ : ∀ s : A.K, algebraMap A.K A.L s ∈ O → A.psiK ψ (t * x * ϖ * s) = 1 := fun s hs => by
    obtain ⟨w, hw, hws⟩ := htr s hs
    have := hϖD w hw
    simp only [Et.kerL, A.star_K, trace_algebraMap_mul, hws] at this
    rwa [← mul_assoc] at this

  have hnt : ∃ s : A.K, algebraMap A.K A.L s ∈ O ∧ A.psiK ψ (t * x * s) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∀ m ∈ O, A.kerL ψ (t * x) 1 m = 1 := fun m hm => by
      rw [kerL_one]
      exact hcon _ (by rw [htrL]; exact O.add_mem hm (hOs m hm))
    obtain ⟨z, hz, hz1⟩ := (hmemD 1).1 h1
    exact hϖu ⟨z, hz, hz1.symm⟩

  let M := scaledSub A O ϖ
  have hMo : IsOpen (M : Set A.L) := by
    rw [scaledSub_eq_image]; exact (mulHomeo A ϖ).isOpenMap _ hOo
  have hMc : IsCompact (M : Set A.L) := by
    rw [scaledSub_eq_image]; exact hOc.image (mulHomeo A ϖ).continuous
  have hM : ∀ m ∈ M, A.psiK ψ (t * x * A.NL m) = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have hs : algebraMap A.K A.L ((ϖ : A.K) * A.NL z) ∈ O := by
      rw [map_mul, hN]; exact O.mul_mem hϖO (O.mul_mem hz (hOs z hz))
    have := hψϖ _ hs
    have hmul : A.NL (algebraMap A.K A.L ϖ * z) = A.NL (algebraMap A.K A.L ϖ) * A.NL z :=
      map_mul (Algebra.norm A.K) _ _
    rw [hmul, NL_algebraMap, show (ϖ : A.K) ^ 2 * A.NL z = (ϖ : A.K) * ((ϖ : A.K) * A.NL z) by ring]
    rwa [← mul_assoc]
  have hDeq : ((O.toAddSubgroup : AddSubgroup A.L) : Set A.L) =
      {y : A.L | ∀ m ∈ M, A.kerL ψ (t * x) y m = 1} := by
    ext y
    simp only [Subring.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_setOf_eq]
    have e1 : (∀ m ∈ M, A.kerL ψ (t * x) y m = 1) ↔ ∀ m ∈ O, A.kerL ψ (t * x) (algebraMap A.K A.L ϖ * y) m = 1 := by
      constructor
      · intro h m hm; rw [kerL_mul_left]; exact h _ ⟨m, hm, rfl⟩
      · rintro h _ ⟨m, hm, rfl⟩; rw [← kerL_mul_left]; exact h m hm
    rw [e1, hmemD]
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have hc : y = z := by
        have := congrArg (fun w => algebraMap A.K A.L ((ϖ⁻¹ : A.Kˣ) : A.K) * w) hzy
        simpa only [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] using this
      rw [hc]; exact hz
  have hG := GlobalTheory.T.quadraticGaussIntegral_stable_of_dual_lattice F E A ψ x μ hψ hμ t M O.toAddSubgroup hMo hMc hOo hOc hM hDeq
  convert hG using 1
  simp only [gaussInt, Subring.coe_toAddSubgroup]
  rw [GlobalTheory.T.residue_gauss_integral_norm_form F E A ψ μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖu hdich hnorm hsc (t * x) hψϖ hnt]

end Level1

theorem gauss_at_uniformiser : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → ∃ ϖ : A.Kˣ, (¬ ∃ y, A.NL y = ϖ) ∧ IsStableGauss A ψ x μ ϖ (-(G₁ * ((A.absK ϖ : ℂ))⁻¹)) := by
  intro F E _ _ _ _ _ A ψ x μ ω hH G₁ hG₁
  obtain ⟨hK, hL, hψ, hSD, hω⟩ := hH
  have hμ : μ.IsAddHaarMeasure := hSD.1
  obtain ⟨ϖ, O, hOo, hOc, hOs, hϖn, hϖO, hϖu, hdich, htr, hnorm, hnb, hex⟩ := GlobalTheory.T.unramifiedQuadratic_exists_integers_uniformiser F E A hK hL
  obtain ⟨e, he⟩ := GlobalTheory.T.hermitianTraceDual_integers_eq_uniformizer_pow F E A ψ hψ hK hL ϖ O hOo hOc hOs hϖO hϖu hdich hnb hex x
  have hsc := GlobalTheory.T.haar_measure_L_unit_smul_absK_sq F E A μ hμ ϖ O

  have hD : ∀ t : A.Kˣ, {y : A.L | ∀ m ∈ O, A.kerL ψ ((t : A.K) * x) y m = 1} =
      {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((t⁻¹ * ϖ ^ e : A.Kˣ) : A.K) * z} := fun t => by
    rw [dual_mul A ψ O t x, ← scaled_mul A O t (ϖ ^ e), ← he]; rfl
  have hO1 : {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((1 : A.Kˣ) : A.K) * z} = (O : Set A.L) := by
    ext y; simp

  have hnp : ∀ j : ℤ, ∃ ℓ : A.L, A.NL ℓ = ((ϖ ^ (2 * j) : A.Kˣ) : A.K) := fun j =>
    ⟨algebraMap A.K A.L ((ϖ ^ j : A.Kˣ) : A.K), by
      rw [NL_algebraMap, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]; norm_num⟩
  have hmove : ∀ (t : A.Kˣ) (j : ℤ) (G : ℂ), IsStableGauss A ψ x μ (t : A.K) G →
      IsStableGauss A ψ x μ ((t * ϖ ^ (2 * j) : A.Kˣ) : A.K) (G * ((A.absK (ϖ : A.K) : ℂ) ^ (2 * j))⁻¹) :=
    fun t j G h => by
      have := GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm F E A ψ x μ ω ⟨hK, hL, hψ, hSD, hω⟩ t (ϖ ^ (2 * j)) (hnp j) G h
      rwa [absK_zpow, Complex.ofReal_zpow] at this
  have hb : (A.absK (ϖ : A.K) : ℂ) ≠ 0 := by exact_mod_cast (absK_pos A ϖ).ne'
  obtain ⟨k, r, hr, hek⟩ : ∃ k r : ℤ, (r = 0 ∨ r = 1) ∧ e = 2 * k + r :=
    ⟨e / 2, e % 2, Int.emod_two_eq_zero_or_one e, by omega⟩
  refine ⟨ϖ, hϖn, ?_⟩
  rcases hr with rfl | rfl
  ·
    have h0 := level0 F E A ψ x μ hψ hμ O hOo hOc hOs htr ((ϖ ^ (2 * k) : A.Kˣ) : A.K) (by
      rw [hD, hek, show ((ϖ ^ (2 * k))⁻¹ * ϖ ^ (2 * k + 0) : A.Kˣ) = 1 by group]; exact hO1)
    have h1 := level1 F E A ψ x μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖu hdich htr hnorm hsc
      ((ϖ ^ (2 * k) * ϖ⁻¹ : A.Kˣ) : A.K) (by
      rw [hD, hek, show ((ϖ ^ (2 * k) * ϖ⁻¹)⁻¹ * ϖ ^ (2 * k + 0) : A.Kˣ) = ϖ by group])
    have g1 := hmove _ (-k) _ h0
    rw [show (ϖ ^ (2 * k) * ϖ ^ (2 * -k) : A.Kˣ) = 1 by group, Units.val_one] at g1
    have gϖ := hmove _ (1 - k) _ h1
    rw [show (ϖ ^ (2 * k) * ϖ⁻¹ * ϖ ^ (2 * (1 - k)) : A.Kˣ) = ϖ by group] at gϖ
    rw [stable_unique A ψ x μ 1 hG₁ g1]
    convert gϖ using 1
    rw [show (2 : ℤ) * (1 - k) = 2 + 2 * -k by ring, zpow_add₀ hb]
    have hP : (A.absK (ϖ : A.K) : ℂ) ^ (2 * -k) ≠ 0 := zpow_ne_zero _ hb
    field_simp
  ·
    have h1 := level1 F E A ψ x μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖu hdich htr hnorm hsc
      ((ϖ ^ (2 * k) : A.Kˣ) : A.K) (by
      rw [hD, hek, show ((ϖ ^ (2 * k))⁻¹ * ϖ ^ (2 * k + 1) : A.Kˣ) = ϖ by group])
    have h0 := level0 F E A ψ x μ hψ hμ O hOo hOc hOs htr ((ϖ ^ (2 * k) * ϖ : A.Kˣ) : A.K) (by
      rw [hD, hek, show ((ϖ ^ (2 * k) * ϖ)⁻¹ * ϖ ^ (2 * k + 1) : A.Kˣ) = 1 by group]; exact hO1)
    have g1 := hmove _ (-k) _ h1
    rw [show (ϖ ^ (2 * k) * ϖ ^ (2 * -k) : A.Kˣ) = 1 by group, Units.val_one] at g1
    have gϖ := hmove _ (-k) _ h0
    rw [show (ϖ ^ (2 * k) * ϖ * ϖ ^ (2 * -k) : A.Kˣ) = ϖ by group] at gϖ
    rw [stable_unique A ψ x μ 1 hG₁ g1]
    convert gϖ using 1
    have hP : (A.absK (ϖ : A.K) : ℂ) ^ (2 * -k) ≠ 0 := zpow_ne_zero _ hb
    field_simp

end GlobalTheory.JR.WeilQuad.NonNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussAtUniformiserStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonNorm_uniformizer_isStableGauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → ∃ ϖ : A.Kˣ, (¬ ∃ y, A.NL y = ϖ) ∧ IsStableGauss A ψ x μ ϖ (-(G₁ * ((A.absK ϖ : ℂ))⁻¹)) := by
  first | exact @GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser | exact GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser | (intros; apply GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralTransformWeil
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.WeilQuad
open scoped Pointwise

theorem isStableGauss_unique {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K)
    {G G' : ℂ} (h : IsStableGauss A ψ x μ u G) (h' : IsStableGauss A ψ x μ u G') : G = G' := by
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  obtain ⟨Λ₀, ho, hc, hG⟩ := h
  obtain ⟨Λ₁, ho', hc', hG'⟩ := h'
  have hs : ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) = (Λ₀ : Set A.L) + (Λ₁ : Set A.L) := AddSubgroup.add_normal Λ₀ Λ₁
  have hO : IsOpen ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := AddSubgroup.isOpen_mono le_sup_left ho
  have hC : IsCompact ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := by rw [hs]; exact hc.add hc'
  rw [← hG _ hO hC le_sup_left, ← hG' _ hO hC le_sup_right]

theorem absK_units_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (a b : A.Kˣ) :
    A.absK ((a * b : A.Kˣ) : A.K) = A.absK a * A.absK b := by
  simp [Et.absK]

theorem absK_units_ne {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) (a : A.Kˣ) : A.absK (a : A.K) ≠ 0 := by
  simp only [Et.absK, Units.isUnit, dite_true, IsUnit.unit_of_val_units, ne_eq, NNReal.coe_eq_zero]
  exact ((Group.isUnit a).map (distribHaarChar A.K)).ne_zero

theorem gauss_transform : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (u : A.Kˣ) (G G₁ : ℂ), IsStableGauss A ψ x μ u G → IsStableGauss A ψ x μ 1 G₁ → G = G₁ * ω u * ((A.absK u : ℂ))⁻¹ := by
  intro F E _ _ _ _ _ A ψ x μ ω hH u G G₁ hG hG₁
  have hω := hH.2.2.2.2
  by_cases hu : ∃ y, A.NL y = u
  · have h1 := GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm F E A ψ x μ ω hH 1 u hu G₁ (by simpa using hG₁)
    rw [one_mul] at h1
    rw [isStableGauss_unique A ψ x μ _ hG h1, (hω u).1 hu]; ring
  · obtain ⟨ϖ, hϖ, hGϖ⟩ := GlobalTheory.T.exists_nonNorm_uniformizer_isStableGauss F E A ψ x μ ω hH G₁ hG₁
    have hps : ϖ * (ϖ⁻¹ * u) = u := mul_inv_cancel_left ϖ u
    have hs : ∃ y, A.NL y = ((ϖ⁻¹ * u : A.Kˣ) : A.K) := by
      by_contra hs
      have hm := (GlobalTheory.T.normGroupSign_mul_and_neg_one F E A ψ x μ ω hH).1 ϖ (ϖ⁻¹ * u)
      rw [hps, (hω u).2 hu, (hω ϖ).2 hϖ, (hω _).2 hs] at hm
      norm_num at hm
    have h2 := GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm F E A ψ x μ ω hH ϖ (ϖ⁻¹ * u) hs _ hGϖ
    rw [hps] at h2
    rw [isStableGauss_unique A ψ x μ _ hG h2, (hω u).2 hu]
    have e1 := absK_units_ne A ϖ
    have e2 := absK_units_ne A (ϖ⁻¹ * u)
    conv_rhs => rw [← hps, absK_units_mul]
    push_cast
    field_simp

end GlobalTheory.JR.WeilQuad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralTransformWeilStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableQuadraticGaussIntegral_transform_weil : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (u : A.Kˣ) (G G₁ : ℂ), IsStableGauss A ψ x μ u G → IsStableGauss A ψ x μ 1 G₁ → G = G₁ * ω u * ((A.absK u : ℂ))⁻¹ := by
  first | exact @GlobalTheory.JR.WeilQuad.gauss_transform | exact GlobalTheory.JR.WeilQuad.gauss_transform | (intros; apply GlobalTheory.JR.WeilQuad.gauss_transform <;> assumption)
end
