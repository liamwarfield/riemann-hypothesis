module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

theorem volPairEx_and_finVol : ∀ (D : D7) (V : HSp D), V.SigOK → VolPairEx V ∧ Formalism.L2.Pj.FinVol V := by
  intro D V hs
  have h := GlobalTheory.Mem.Vol.volIs_trueVol _ _ D.sp.cm _ (tauE D) D.cd V
    (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hs
  obtain ⟨⟨μ, hμ⟩, hall⟩ := h
  have hex : VolPairEx V := by
    obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := hall μ hμ
    exact ⟨(μ, 𝓕), hμ, h𝓕⟩
  refine ⟨hex, ?_⟩
  have hp := volPair_isVolPair V hex
  have hm : (volPair V).1 (volPair V).2 =
      ENNReal.ofReal (GlobalTheory.Mem.Vol.trueVol D.sp.cm (tauE D) D.cd V) :=
    (hall _ hp.1).2 _ hp.2
  unfold Formalism.L2.Pj.FinVol
  rw [muQ_univ, hm]
  exact ⟨(ENNReal.ofReal_pos.2 (GlobalTheory.Mem.Vol.trueVol_pos _ _ _ _)).ne', ENNReal.ofReal_ne_top⟩

end GlobalTheory.FinalJoin2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeZBaseOfPowLeN
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open GlobalTheory.EX

theorem x_le_zBase_of_pow_le_n {D : D7} (L : SizeData₂ D) (hn : L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ)) :
    L.sc.x ≤ zBase L := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  have hL : 1 ≤ L.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow hx.le he.le
  have h1 : L.sc.x ≤ L.sc.x ^ (2 + 8 * L.sc.eps) := by
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hf : (D.R.n : ℝ) ≤ D.R.f := by
    unfold Ranks.f; exact_mod_cast (by omega : D.R.n ≤ 2 * D.R.n)
  have hr : (1 : ℝ) ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hxf : L.sc.x ≤ (D.R.f : ℝ) := h1.trans (hn.trans hf)
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  unfold zBase
  calc L.sc.x ≤ (D.R.f : ℝ) * 1 * 1 := by linarith
    _ ≤ _ := by gcongr

end GlobalTheory.FinalJoin2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSmallIffOpo
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

namespace GlobalTheory.FinalJoin2

theorem FO_eq_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D = Q.c.F := by
  apply le_antisymm
  · rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    have e := h (Q.eO.symm y)
    rw [RingEquiv.apply_symm_apply] at e
    have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
    rw [e']
    exact SetLike.coe_mem _
  · intro z hz
    haveI := Q.c.fin
    haveI : NumberField Q.c.F := NumberField.mk
    have hint : ∀ x : 𝓞 Q.c.F, ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) ∈ FO D := fun x => by
      have e : D.what₂.phiO (Q.eO x) = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) := h x
      rw [← e]
      exact phiO_mem_FO D _
    obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 Q.c.F) (⟨z, hz⟩ : Q.c.F)
    have : z = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) / ((algebraMap (𝓞 Q.c.F) Q.c.F y : Q.c.F) : ℂ) := by
      have := congrArg (fun t : Q.c.F => (t : ℂ)) hxy
      simpa using this.symm
    rw [this]
    exact div_mem (hint x) (hint y)

theorem fieldSmall_iff_opo : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D),
    FieldSmall D large₂ ↔ OPO large₂ (recB h.toLawsCore) := by
  intro D T h large₂
  have hF : FO D = T.Q.c.F := FO_eq_coeff T.Q h.toLawsCore.pins.2.2.1
  letI : NumberField (FO D) := NumberField.mk
  let e : FO D ≃+* (recB h.toLawsCore).KO := (IntermediateField.equivOfEq hF).toRingEquiv
  have h1 : Module.finrank ℚ (FO D) = Module.finrank ℚ (recB h.toLawsCore).KO :=
    (LinearEquiv.ofBijective e.toRingHom.toRatAlgHom.toLinearMap e.bijective).finrank_eq
  have h2 : NumberField.discr (FO D) = NumberField.discr (recB h.toLawsCore).KO :=
    NumberField.discr_eq_discr_of_ringEquiv _ e
  unfold FieldSmall OPO
  rw [← h1, ← h2]

end GlobalTheory.FinalJoin2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecordSubFour
set_option autoImplicit false

namespace GlobalTheory.FinalJoin.RecordRun

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem exists_pageRun_record_sub_four : ∃ CK : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), SizesAt L → Pm.CnW = 10 → (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → (10 : ℝ) ^ 60 ≤ L.sc.x → 1000 ≤ Tp.CP → Tp.CP ^ 20 ≤ zBase L → ∀ (B : WeightFamilies.Prov D) (Q : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B Q j), InR D j → OPO L B → PageRun L X ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP L.Ct (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) :=
  ⟨10, fun _ _ _ T hK S hCnW hg hx hC hCZ B Q _ X hj hO =>
    pageRun_record T hK S hCnW hg hx hC hCZ B Q hj.1 hj.2 X hO⟩

end GlobalTheory.FinalJoin.RecordRun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.Hilbert90FiniteIdelesCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.Hilbert90FiniteIdelesCongruence
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdeleNinety

theorem fixed_baseChange {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (c : E →ₐ[F] E) (hcc : ∀ x, c (c x) = x)
    (hfix : ∀ x, c x = x → ∃ t : F, x = algebraMap F E t) (y : R ⊗[F] E)
    (hy : Algebra.TensorProduct.map (AlgHom.id F R) c y = y) : ∃ a : R, y = a ⊗ₜ 1 := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + Algebra.TensorProduct.map (AlgHom.id F R) c z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := hfix (x + c x) (by rw [map_add (f := _), hcc, add_comm])
      refine ⟨t • a, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← TensorProduct.tmul_add, ht,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add (f := _), TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT y
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [← TensorProduct.smul_tmul', ← ht, hy, ← two_smul F y, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem conj_ne_one (D : D7) : cF D ≠ 1 := by
  intro h
  obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
  obtain ⟨t, s, hs, hts⟩ := D.sp.cm.cmUnram.2.2 P hM
  have hs' : (s : D.host.E) = cF D (t : D.host.E) := hs
  rw [h] at hs'
  have : s = t := Subtype.ext hs'
  rw [this, sub_self] at hts
  exact hts P.zero_mem

theorem fixed_conj (D : D7) (x : D.host.E) (hx : cF D x = x) : ∃ t : D.host.F, x = algebraMap D.host.F D.host.E t := by
  have : Algebra.IsQuadraticExtension D.host.F D.host.E := { finrank_eq_two' := D.sp.cm.deg2 }
  have hcard : Nat.card (D.host.E ≃ₐ[D.host.F] D.host.E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, D.sp.cm.deg2]
  obtain ⟨g, -, hg⟩ := (Nat.card_eq_two_iff' (1 : D.host.E ≃ₐ[D.host.F] D.host.E)).1 hcard
  obtain ⟨t, ht⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := D.host.F) x).2 fun f => by
    by_cases hf : f = 1
    · rw [hf]; rfl
    · rw [hg f hf, ← hg _ (conj_ne_one D), hx]
  exact ⟨t, ht.symm⟩

theorem coe_cjFin (D : D7) (y : (AfE D)ˣ) : ((cjFin D y : (AfE D)ˣ) : AfE D) = barF D (y : AfE D) := by
  have h : D.conjF = (cF D : D.host.E →ₐ[D.host.F] D.host.E) :=
    AlgHom.ext fun x => (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  unfold cjFin barF
  rw [h]
  rfl

theorem finiteIdeles_normOne_eq_div_conj_with_congruence : ∀ (D : D7), (∀ x : (AfE D)ˣ, NormOne x → ∃ y, x = y / cjFin D y) ∧ (∀ y : (AfE D)ˣ, cjFin D y = y → ∃ a : Af D.host.F, (y : AfE D) = a ⊗ₜ 1) ∧ ∀ (p N : ℕ) (x : (AfE D)ˣ), p.Prime → p ≠ 2 → p ∣ N → 0 < N → NormOne x → CongOne N x → ∃ y, IntUnit y ∧ CongOne p y ∧ x = y / cjFin D y := by
  intro D
  have hcc : ∀ x, cF D (cF D x) = x := fun x => star_star x
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun p N x hp h2 hpN _ hx hc => ?_⟩
  · obtain ⟨y, hy⟩ := GlobalTheory.UCls.NormOne.finiteAdele_quadratic_exists_unit_eq_mul_sg (cF D) hcc (fixed_conj D) (conj_ne_one D) (x : AfE D) hx
    refine ⟨y, ?_⟩
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by rw [Units.val_mul, coe_cjFin]; exact hy.symm)
  · exact fixed_baseChange (Af D.host.F) (cF D : D.host.E →ₐ[D.host.F] D.host.E) hcc (fixed_conj D) _
      ((coe_cjFin D y).symm.trans (congrArg Units.val hy))
  · obtain ⟨w, hw, hwe⟩ := hc
    obtain ⟨k, rfl⟩ := hpN
    obtain ⟨y, y', hy, hy', hyy, hroot, hq⟩ := GlobalTheory.OddRoot.exists_root_odd D p (hp.odd_of_ne_two h2) (x : AfE D)
      (k • w) (nsmul_mem hw k) (by rw [hwe, mul_smul]) hx
    refine ⟨Units.mkOfMulEqOne y y' hyy, ⟨hy, hy'⟩, hq, ?_⟩
    rw [eq_div_iff_mul_eq']
    exact Units.ext (by rw [Units.val_mul, coe_cjFin]; exact hroot.symm)

end GlobalTheory.IdeleNinety
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.Hilbert90FiniteIdelesCongruenceStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteIdeles_normOne_eq_div_conj_of_congOne : ∀ (D : D7), (∀ x : (AfE D)ˣ, NormOne x → ∃ y, x = y / cjFin D y) ∧ (∀ y : (AfE D)ˣ, cjFin D y = y → ∃ a : Af D.host.F, (y : AfE D) = a ⊗ₜ 1) ∧ ∀ (p N : ℕ) (x : (AfE D)ˣ), p.Prime → p ≠ 2 → p ∣ N → 0 < N → NormOne x → CongOne N x → ∃ y, IntUnit y ∧ CongOne p y ∧ x = y / cjFin D y := by
  first | exact @GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence | exact GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence | (intros; apply GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermuted
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermuted
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem weberSet_finite (L : PeriodPair) {n : ℕ} (hn : 0 < n) : (weberSet L n).Finite := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  let f : ℤ × ℤ → ℂ := fun s => L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) *
    L.weierstrassP ((s.1 * L.ω₁ + s.2 * L.ω₂) / n)
  refine Set.Finite.insert _
    ((((Set.finite_Ico (0 : ℤ) n).prod (Set.finite_Ico (0 : ℤ) n)).image f).subset ?_)
  rintro _ ⟨z, hz, -, rfl⟩
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
  refine ⟨(a % n, b % n), ⟨⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩,
    ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩⟩, ?_⟩
  have e : (a * L.ω₁ + b * L.ω₂) / n = (((a % n : ℤ) : ℂ) * L.ω₁ + ((b % n : ℤ) : ℂ) * L.ω₂) / n +
      (((a / n : ℤ) : ℂ) * L.ω₁ + ((b / n : ℤ) : ℂ) * L.ω₂) := by
    have a1 : ((a % n : ℤ) : ℂ) + n * ((a / n : ℤ) : ℂ) = a := by
      exact_mod_cast Int.emod_add_mul_ediv a n
    have a2 : ((b % n : ℤ) : ℂ) + n * ((b / n : ℤ) : ℂ) = b := by
      exact_mod_cast Int.emod_add_mul_ediv b n
    rw [← a1, ← a2]
    field_simp
    ring
  simp only [f]
  rw [e, L.weierstrassP_add_coe _ ⟨_, PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩⟩]

theorem exists_map_weber_eq (L : PeriodPair) (n : ℕ) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) (τ : ℂ ≃+* ℂ)
    (hτ : τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2))
    (t : ℂ) (hnt : (n : ℂ) * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    ∃ t', (n : ℂ) * t' ∈ L.lattice ∧ t' ∉ L.lattice ∧
      τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) =
        L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t' := by
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  set J := L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) with hJ
  set u := L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) with hu
  have hu0 : u ≠ 0 := div_ne_zero (mul_ne_zero h2 h3) hD
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hu0 (by simpa using hm.symm)
  have hmu : (m ^ 2)⁻¹ = u := by rw [hm, inv_inv]
  have H := isHomothetic_scalePeriods L m hm0
  set L' := scalePeriods L m hm0
  have hJ1 : J - 1 = 27 * L.g₃ ^ 2 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [hJ, div_sub_one hD, sub_sub_cancel]
  have e2 : L'.g₂ = J * (J - 1) / 27 := by
    rw [H.g₂_eq, show (m ^ 4)⁻¹ = ((m ^ 2)⁻¹) ^ 2 by ring, hmu, hJ1, hu, hJ]
    generalize L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = D
    ring
  have e3 : L'.g₃ = J * (J - 1) ^ 2 / 729 := by
    rw [H.g₃_eq, show (m ^ 6)⁻¹ = ((m ^ 2)⁻¹) ^ 3 by ring, hmu, hJ1, hu, hJ]
    generalize L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = D
    ring
  have f2 : L'.g₂ = τ L'.g₂ := by
    rw [e2]; simp [hτ, map_ofNat]
  have f3 : L'.g₃ = τ L'.g₃ := by
    rw [e3]; simp [hτ, map_ofNat]
  obtain ⟨s, -, hc⟩ := GlobalTheory.ConjPoint.exists_conjEquiv f2 f3
  obtain ⟨w, hw⟩ := latticePoint_surjective L' (s (latticePoint L' (m * t)))
  obtain ⟨t', rfl⟩ : ∃ t', w = m * t' := ⟨m⁻¹ * w, by field_simp⟩
  have hconj := (hc _ _).2 hw.symm
  have h1 := (hconj.nsmul_mem_iff f2 f3 n).1 (by rw [mul_left_comm]; exact (H _).2 hnt)
  rw [mul_left_comm] at h1
  obtain ⟨-, h4, h5, -⟩ := hconj.resolve_left fun h => ht ((H t).1 h.1)
  refine ⟨t', (H _).1 h1, fun h => h4 ((H _).2 h), ?_⟩
  rw [H.weierstrassP_mul, H.weierstrassP_mul, hmu] at h5
  exact h5.symm

theorem weberSet_finite_algebraic_permuted : ∀ (L : PeriodPair) (n : ℕ), 0 < n → L.g₂ ≠ 0 → L.g₃ ≠ 0 → (weberSet L n).Finite ∧ (IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ w ∈ weberSet L n, IsAlgebraic ℚ w) ∧ ∀ τ : ℂ ≃+* ℂ, τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ t, (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice → ∃ t', (n : ℂ) * t' ∈ L.lattice ∧ t' ∉ L.lattice ∧ τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) = (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') := by
  intro L n hn h2 h3
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  refine ⟨weberSet_finite L hn, fun hj => ?_, exists_map_weber_eq L n h2 h3⟩
  rintro _ (rfl | ⟨z, hz, hz', rfl⟩)
  · exact hj
  · exact GlobalTheory.WeberField.weber_isAlgebraic L hj hn hz' (by rwa [mul_div_cancel₀ _ hn0])

end GlobalTheory.FieldSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermutedStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberValues_finite_algebraic_permuted : ∀ (L : PeriodPair) (n : ℕ), 0 < n → L.g₂ ≠ 0 → L.g₃ ≠ 0 → (weberSet L n).Finite ∧ (IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ w ∈ weberSet L n, IsAlgebraic ℚ w) ∧ ∀ τ : ℂ ≃+* ℂ, τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ t, (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice → ∃ t', (n : ℂ) * t' ∈ L.lattice ∧ t' ∉ L.lattice ∧ τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) = (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') := by
  first | exact @GlobalTheory.FieldSize.weberSet_finite_algebraic_permuted | exact GlobalTheory.FieldSize.weberSet_finite_algebraic_permuted | (intros; apply GlobalTheory.FieldSize.weberSet_finite_algebraic_permuted <;> assumption)
end
end
