module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PmTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PmSeedP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KeepLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobeniusTraceCountBoundOfCmEigensystemCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RigSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSeedB

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWLevel
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWinNumN
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br
namespace UpperTheory.GalN.V.Win.N
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.CongNum
section
private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have h : normV w = Ideal.absNorm w.asIdeal := (Ideal.absNorm_eq_natCard w.asIdeal).symm
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [h]
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top
private theorem est {p e : ℕ} (hp : 5 ≤ p) (he : 2 ≤ e) {t z₁ z₂ z₃ : ℂ} (h1 : ‖z₁‖ = 1) (h2 : ‖z₂‖ = 1) (h3 : ‖z₃‖ = 1)
    (ht : ‖t‖ ≤ 3 * (Real.sqrt p * (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) + (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) :
    t - eis4 p e z₁ z₂ z₃ ≠ 0 ∧ ‖t - eis4 p e z₁ z₂ z₃‖ ≤ (p : ℝ) ^ (2 * (e + 1)) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  set x : ℝ := (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2) with hx
  set y : ℝ := (p : ℝ) ^ e with hy
  have hx0 : 0 ≤ x := by positivity
  have hxx : x * x = p * y := by
    rw [hx, ← Real.rpow_add (by linarith), hy, ← pow_succ', ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hy2 : (p : ℝ) ^ 2 ≤ y := pow_le_pow_right₀ (by linarith) he
  have hy0 : 0 ≤ y := by positivity
  have hxy : 2 * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0, mul_nonneg (show (0:ℝ) ≤ p - 4 by linarith) (mul_nonneg (show (0:ℝ) ≤ p by linarith) hy0)]
  have hsx : Real.sqrt p * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    rw [mul_pow, Real.sq_sqrt (by linarith), pow_two x, hxx]
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0]
  replace ht : ‖t‖ ≤ 7 / 2 * y := by linarith
  have n1 : ‖(p : ℂ) ^ (e + 1) * z₁‖ = p * y := by simp [h1, hy, pow_succ']
  have n2 : ‖(p : ℂ) ^ e * z₂‖ = y := by simp [h2, hy]
  have n3 : ‖(p : ℂ) * z₃‖ = p := by simp [h3]
  have hr : ‖t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)‖ ≤ 7 / 2 * y + (y + p + 1) := by
    refine (norm_sub_le _ _).trans (add_le_add ht ?_)
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, ← n2, ← n3]
    have := norm_add_le ((p : ℂ) ^ e * z₂) ((p : ℂ) * z₃)
    simpa using this
  have hE : t - eis4 p e z₁ z₂ z₃ = (t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)) - (p : ℂ) ^ (e + 1) * z₁ := by
    rw [eis4]; ring
  have hlt : 7 / 2 * y + (y + p + 1) < p * y := by nlinarith
  constructor
  · intro h0
    rw [hE, sub_eq_zero] at h0
    rw [h0, n1] at hr
    linarith
  · rw [hE]
    refine (norm_sub_le _ _).trans ?_
    rw [n1, mul_comm 2, pow_mul, pow_succ' (p : ℝ) e, ← hy]
    have : (2 : ℝ) ≤ p * y := by nlinarith
    nlinarith
private theorem size {c A M e N d p : ℕ} (hN : N ≤ c * (M * (e + 1 + 1)) ^ A) (hM : 1 ≤ M) (hp : 5 ≤ p) :
    ((N * d : ℕ) : ℝ) * Real.log ((p : ℝ) ^ (2 * (e + 1))) ≤
      ((c * 2 ^ A * 2 : ℕ) : ℝ) * d * ((M : ℝ) * (e + 1)) ^ (A + 1) * Real.log p := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h1 : N * d * (2 * (e + 1)) ≤ c * 2 ^ A * 2 * d * (M * (e + 1)) ^ (A + 1) := by
    have a1 : (M * (e + 1 + 1)) ^ A ≤ 2 ^ A * (M * (e + 1)) ^ A := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) _
    have a2 : e + 1 ≤ M * (e + 1) := Nat.le_mul_of_pos_left _ hM
    calc N * d * (2 * (e + 1)) ≤ c * (2 ^ A * (M * (e + 1)) ^ A) * d * (2 * (M * (e + 1))) := by
          gcongr
          exact hN.trans (by gcongr)
      _ = _ := by ring
  rw [Real.log_pow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  exact_mod_cast h1
end
theorem number_sp4_of_admissible_to_admissible_n :
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.GalN.V.LevelPNAlt → _root_.UpperTheory.GalN.V.AdmResNAlt →
    (∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin 4 → ℤ) (wt : ℤ)
      (r : G ℚ Ω →* GL (Fin 4) (Qbar l)), _root_.UpperTheory.V.Af.AdmRAlt ι M m wt r → _root_.UpperTheory.GalN.V.AdmRNAlt ι M m wt r) →
    _root_.UpperTheory.V.Af.NumberSp4Alt := by
  intro hP hLP hA hR
  obtain ⟨c, A, hc⟩ := _root_.UpperTheory.GalN.V.Win.N.countQ_alt hP hLP hA 4 (by norm_num)
  refine ⟨c * 2 ^ A * 2, A + 1, fun e he M hM p w hp hw h5 hpM k hk z₁ z₂ z₃ h1 h2 h3 => ?_⟩
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨D, hD, hcl⟩ := hc ![(e : ℤ) + 1, e, 1, 0] (e + 1)
    (by
      rw [Fin.strictAnti_iff_succ_lt]
      intro i; fin_cases i <;> simp <;> omega)
    (by intro i; fin_cases i <;> simp [Fin.rev] <;> omega) (e + 1)
    (by intro i; fin_cases i <;> simp [abs_le] <;> omega) M hM p w hp hw hpM
  haveI := D.fin
  letI := Fintype.ofFinite D.S
  let f : D.S × (ZMod k)ˣ → ℂ := fun x =>
    (D.β x.1).sum - eis4 p e (z₁ ^ (x.2 : ZMod k).val) (z₂ ^ (x.2 : ZMod k).val) (z₃ ^ (x.2 : ZMod k).val)
  have hzi : ∀ z : ℂ, z ^ k = 1 → IsIntegral ℤ z := fun z hz => IsIntegral.of_pow hk (hz ▸ isIntegral_one)
  have hzn : ∀ z : ℂ, z ^ k = 1 → ∀ a : ℕ, ‖z ^ a‖ = 1 := fun z hz a => by
    rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hz hk.ne', one_pow]
  have hi : ∀ x, IsIntegral ℤ (f x) := fun x => by
    have hpi : IsIntegral ℤ (p : ℂ) := isIntegral_natCast p
    refine IsIntegral.sub (IsIntegral.multiset_sum fun b hb => ?_) ?_
    · simpa using D.int 0 (by intro i; fin_cases i <;> simp <;> omega) x.1 b hb
    · exact ((((hpi.pow _).mul ((hzi _ h1).pow _)).add ((hpi.pow _).mul ((hzi _ h2).pow _))).add
        (hpi.mul ((hzi _ h3).pow _))).add isIntegral_one
  have hconj : ∀ σ : ℂ ≃+* ℂ, ∃ u : D.S × (ZMod k)ˣ ≃ D.S × (ZMod k)ˣ, ∀ x, f (u x) = σ (f x) := fun σ => by
    obtain ⟨u, hu⟩ := D.conj σ
    obtain ⟨b, hb⟩ := exists_unit_pow k σ
    refine ⟨u.prodCongr (Equiv.mulLeft b), fun x => ?_⟩
    simp only [f, eis4, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, hu, Equiv.coe_mulLeft, Units.val_mul, map_sub,
      map_add, map_mul, map_pow, map_one, map_natCast, map_multiset_sum, hb _ h1, hb _ h2, hb _ h3,
      pow_val_mul h1, pow_val_mul h2, pow_val_mul h3]
  have hest : ∀ x, f x ≠ 0 ∧ ‖f x‖ ≤ (p : ℝ) ^ (2 * (e + 1)) := fun x => by
    refine est h5 he (hzn _ h1 _) (hzn _ h2 _) (hzn _ h3 _) ?_
    simpa only [Nat.cast_ofNat] using WinC.sum_le (D.pure x.1) (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _) (n := 3) (D.card _)
  obtain ⟨NN, hNN⟩ := exists_int_prod f hi hconj
  obtain ⟨h0, hlog⟩ := log_abs_le f NN hNN (fun x => (hest x).1) _ fun x => (hest x).2
  refine ⟨NN, h0, hlog.trans ?_, fun l _ hl2 hlp Ω _ _ _ ι B hB σ hσ X hX hX' => ?_⟩
  · rw [Fintype.card_prod, ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
    exact size hD hM h5
  replace hX := fun r hr => hR Ω l ι _ _ _ r (hX r hr)
  obtain ⟨cl, hinj, hfr⟩ := hcl l hl2 hlp Ω ι
  have hone : ∀ z : ℂ, z ^ k = 1 → z ^ (((1 : (ZMod k)ˣ) : ZMod k)).val = z := fun z hz => by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hz, pow_one]
  have key : ∀ (r) (hr : r ∈ X), (r σ : Matrix (Fin 4) (Fin 4) (Qbar l)).trace - ι.symm (eis4 p e z₁ z₂ z₃) =
      ι.symm (f (cl ⟨r, hX r hr⟩, 1)) := fun r hr => by
    have h := (hfr ⟨r, hX r hr⟩ B hB).2 σ (by rwa [normV_rat hp w hw])
    rw [map_inv] at h
    rw [trace_eq_sum_of_inv ι _ _ h]
    simp only [f, hone _ h1, hone _ h2, hone _ h3, map_sub]
  refine ⟨fun r hr h => ?_, ?_⟩
  · have := key r hr
    rw [h, sub_self, eq_comm, map_eq_zero_iff _ ι.symm.injective] at this
    exact (hest _).1 this
  · have := norm_le_prod ι f hi NN hNN (fun r : X => (cl ⟨r.1, hX r.1 r.2⟩, (1 : (ZMod k)ˣ))) fun r r' h =>
      Subtype.ext (hX' _ r.2 _ r'.2 (hinj _ _ (congrArg Prod.fst h)))
    refine this.trans_eq ?_
    rw [← Finset.prod_coe_sort X]
    exact Finset.prod_congr rfl fun r _ => by rw [key r.1 r.2]
end
end UpperTheory.GalN.V.Win.N
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af
namespace UpperTheory.GalN.V
theorem numberSp4_n_alt : _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Af.NumberSp4Alt := fun P =>
  _root_.UpperTheory.GalN.V.Win.N.number_sp4_of_admissible_to_admissible_n P (_root_.UpperTheory.V.Keep.levelPA_alt P) (_root_.UpperTheory.V.Z.Win.A4.admissible_restriction_level_n_of_printed_results P) fun _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨h.irr, _root_.UpperTheory.GalN.V.autQN'_alt P (by norm_num) h.dual h.aut, h.level, h.dual, h.safe⟩
end UpperTheory.GalN.V
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PmExTh
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthPm
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EigenbasisRankFour
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.Ws.Eb
private theorem tan_one {K H : Type} [CommRing K] [Group H] {n : ℕ} {ρ : H →* GL (Fin n) K} {y : H → Matrix (Fin n) (Fin n) K}
    {ρ' : H →* GL (Fin n) (DualNumber K)} (h : IsTan ρ y ρ') (g : H) (hg : ρ' g = 1) : y g = 0 := by
  have e1 := h g
  rw [hg] at e1
  have e2 : (ρ g : Matrix (Fin n) (Fin n) K) = 1 := by
    ext i j
    have := congrArg TrivSqZeroExt.fst (e1 i j)
    by_cases h : i = j <;> simpa [Matrix.one_apply, h] using this.symm
  ext i j
  have := congrArg TrivSqZeroExt.snd (e1 i j)
  rw [e2, mul_one] at this
  by_cases h : i = j <;> simpa [Matrix.one_apply, h] using this.symm
private theorem at_l (hP : Loc.LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n}
    (B : W.UniversalOrdinaryDeterminantRing r) (Λ : W.LamObj r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (hΛ : ∀ a, (x' (Λ.toPair B.u a)).snd = 0)
    {ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)} {y : F.G₀ → Matrix (Fin n) (Fin n) (PadicAlgCl l)} {ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))}
    (hcont : Continuous ρ) (hy : y ∈ Z1 (Loc.adGL ρ)) (htan : IsTan ρ y ρ') {P : GL (Fin n) (PadicAlgCl l)}
    {R : Representation (PadicAlgCl l) F.Γ (Matrix (Fin n) (Fin n) (PadicAlgCl l))} (hR : IsAdExt F ρ P R)
    {z : F.Γ → Matrix (Fin n) (Fin n) (PadicAlgCl l)} (hzy : ∀ g : F.G₀, z g = y g) (v : F.Vl)
    (hfl : W.HasFlag (ρ'.comp (F.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i))
    (m : Fin n → ℤ) (k : ℕ) (hm : ∀ i j, i < j → m j + 2 ≤ m i) (hk : 0 < k) (φ : F.Gv v →* Formalism.BasicNotions.Loc.GQ l)
    (hφ : Topology.IsOpenEmbedding φ) (h1 : ∀ g, φ g ∈ Loc.Iq l ↔ g ∈ F.Iv v)
    (h2 : ∀ i, ∀ g ∈ F.Iv v, (W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) g *
      Loc.cycA l l (PadicAlgCl l) (φ g) ^ (-m i)) ^ k = 1) :
    (fun g : F.Gv v => z (F.φ v g)) ∈ Loc.finiteCocycles φ (R.comp (F.η.ker.subtype.comp (F.φ v)) :
      Representation (PadicAlgCl l) (F.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) := by
  have e1 : (R.comp (F.η.ker.subtype.comp (F.φ v)) : Representation (PadicAlgCl l) (F.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) =
      Loc.adGL (ρ.comp (F.φ v)) := MonoidHom.ext fun g => LinearMap.ext fun X => hR.ad _ X
  rw [e1]
  simp only [hzy]
  refine locL hP φ hφ (ρ.comp (F.φ v)) (hcont.comp (F.φ_cont v)) _
    ⟨hy.1.comp (F.φ_cont v), fun g h => ?_⟩ _ (htan.comp (F.φ v)) _ m k hfl hm hk fun i g hg => ⟨?_, h2 i g ((h1 g).1 hg)⟩
  · exact (congrArg y (map_mul _ g h)).trans (hy.2 _ _)
  · have e2 := congrArg Units.val (DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i) ⟨g, (h1 g).1 hg⟩)
    exact (congrArg (fun b => (x' b).snd) e2).symm.trans (hΛ _)
section
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
private theorem over_l (v : W.Vl l L) : (s.A v).valuation (l : Ω) < 1 := by
  simpa using (s.hA v _).2 v.2
private theorem arith (hP : _root_.UpperTheory.V.Af.HypothesesH') (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : x.Arith fun v j _ => -m v j := by
  have hl : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal := fun v => by
    refine (s.hw v _).1 ?_
    simpa using over_l (s := s) v
  refine ⟨fun v τ i j hij => ?_, fun v j => ?_⟩
  · have := hm v i j hij
    simp only
    omega
  · exact UpperTheory.V.Loc.laArith hP.toClassicalTheorems.litN.aut.art (s.hw v) (hl v) _ (Ws.Pt.psi_cont x v j) (m v j) k hk (hw v j)
private theorem noRatio (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) (v : W.Vl l L) (i j : Fin n) :
    x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
  intro hij
  have hne : 1 - m v i + m v j ≠ 0 := by
    rcases lt_trichotomy i j with h | h | h
    · have := hm v i j h
      omega
    · subst h
      omega
    · have := hm v j i h
      omega
  obtain ⟨g, hg, hg1⟩ := Ws.Pt.cycIne L Ω l (s.A v) (over_l v) ((1 - m v i + m v j) * k)
    (mul_ne_zero hne (by exact_mod_cast hk.ne'))
  have hgD : g ∈ Dec (F := L) (s.A v) :=
    (GlobalTheory.WeilDeligne.Weil_le_Dec (s.hw v)) (GlobalTheory.WeilDeligne.ineIncl (s.hw v) ⟨g, hg⟩).2
  have h1 := hw v i ⟨g, hgD⟩ hg
  have h2 := hw v j ⟨g, hgD⟩ hg
  have e : x.psi v i ⟨g, hgD⟩ = x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g := by
    rw [hij]; rfl
  apply hg1
  have e2 : x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i) =
      (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) * cycBar L Ω l g ^ (1 - m v i + m v j) := by
    rw [e, mul_assoc, mul_assoc, ← zpow_add, ← zpow_one_add]
    congr 2
    ring
  change (x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i)) ^ k = 1 at h1
  change (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) ^ k = 1 at h2
  rw [e2, mul_pow, h2, one_mul] at h1
  rw [zpow_mul, zpow_natCast, h1]
private theorem par (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : Par x := fun v =>
  ⟨m v, k, fun i j h => by have := hm v i j h; omega, hk, fun i j g hg => by
    have e : x.psi v i g / x.psi v j g * cycBar L Ω l g ^ (m v j - m v i) =
        (x.psi v i g * cycBar L Ω l g ^ (-m v i)) / (x.psi v j g * cycBar L Ω l g ^ (-m v j)) := by
      rw [mul_div_mul_comm, div_eq_mul_inv (_ ^ (-m v i)), ← zpow_neg, ← zpow_add]
      congr 2
      ring
    rw [e, div_pow, hw v i g hg, hw v j g hg, div_one]⟩
private theorem free (hP : _root_.UpperTheory.V.Af.HypothesesH') (hn : 1 ≤ n) (ι : PadicAlgCl l ≃+* ℂ) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l))
    (m : W.Vl l L → Fin n → ℤ) (hρ : Continuous ρ) (haut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i)
    (hfl : ∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : Free V.frame fun v => x.psi v := fun v : W.Vl l L => by
  obtain ⟨g, hg, hf⟩ := _root_.UpperTheory.V.Z.Win.RR.exists_cycZ_eq_one_freeRatios_of_ne_mul_cycBar hP L Ω l s.odd ι n hn ρ hρ haut (s.A v) (over_l v) (x.psi v) (m v) k (hfl v)
    (fun i j h => by have := hm v i j h; omega) hk (hw v) (noRatio x m hm k hk hw v)
  refine ⟨g, ?_, hf⟩
  have e : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ (W.Lp L) Ω l (W.resP L Ω g) := DFunLike.congr_fun V.hε _
  exact e.trans hg
end
theorem UpperTheory.V.Th.eigenbasis_rank_four :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) → ∀ (c : Coef l), W.Large L c → ∀ (r : W.Resid V.frame c.O 4) (B : W.UniversalOrdinaryDeterminantRing r) (Λ : W.LamObj r) (ι : PadicAlgCl l ≃+* ℂ) (J : Ideal B.B), B.HidaPropsAlt ι J Λ → r.V0ok → (∀ η : V.frame.G₀ →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (V.frame.eps c.O (ResidueField c.O)).ker ≤ η.ker → (∀ i, ∃ j, η * r.chib i = r.chib j) → η = 1) → (∃ i j, ∀ m : ℕ, 0 < m → m ≤ 4 → (r.chib i / r.chib j) ^ m ≠ 1) → ∀ (x : B.Pt) (ρ : G L Ω →* GL (Fin 4) (PadicAlgCl l)) (m : W.Vl l L → Fin 4 → ℤ), J ≤ RingHom.ker x → x.IsRep ρ → Continuous ρ →
          _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) → Af.IsIrr (ρ.comp (cycBar L Ω l).ker.subtype) → (∀ v i j, i < j → m v j + 2 ≤ m v i) →
          (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) →
          (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) → (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) →
          ∀ q : Ideal B.B, q.IsPrime → q ≤ RingHom.ker x → J ≤ q := by
  intro hU hAd l _ L Ω _ _ _ _ _ _ s V hV hζ c hc r B Λ ι J hJ h0 hC hD4 x ρ m hJx hx hρ haut hv0 hirr hm hfl ⟨k, hk, hkk⟩
  obtain ⟨Λ', ⟨e'⟩⟩ := hU.lam l L Ω s V c 4 r
  obtain ⟨e₁⟩ := lamIso Λ' Λ
  obtain ⟨e, he⟩ : ∃ e : MvPowerSeries (Fin (4 * Module.finrank ℚ (W.Lp L))) c.O →ₐ[c.O] Λ.Λ, Function.Bijective e :=
    ⟨(e'.symm.trans e₁ :), (e'.symm.trans e₁).bijective⟩
  refine regOfTan c _ B.B ((Λ.toPair B.u).comp e) J ?_ (fun a ha b hb => ?_) x hJx fun x' hx' hΛ => ?_
  · exact hJ.ring.fin.comp (RingHom.Finite.of_surjective (e : MvPowerSeries (Fin (4 * Module.finrank ℚ (W.Lp L))) c.O →+* Λ.Λ) he.2)
  · exact hJ.ring.tf (e a) ((map_ne_zero_iff e he.1).2 ha) b hb
  have hΛ' : ∀ a, (x' (Λ.toPair B.u a)).snd = 0 := fun a => by
    obtain ⟨a, rfl⟩ := he.2 a
    exact hΛ a
  have hxx : (dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l)) = (x : B.B →+* PadicAlgCl l) := RingHom.ext hx'
  have hn1 : 1 ≤ 4 := by omega
  obtain ⟨ρ₀, rfl, hfull, hD⟩ := factor V B x ρ hn1 hx hirr
  obtain ⟨ρ', y, hD', hred, hfull', hcont, hy, htan⟩ := liftRep B x' ρ₀ hn1 hfull (by rw [hxx, hD])
  obtain ⟨hO, hI⟩ := relKill B x' ρ' hfull' hD'
  obtain ⟨P', hP'⟩ := relForm B x' ρ' hfull' hD'
  obtain ⟨hP, hrel⟩ := cocRel V.frame c.O ρ₀ y ρ' P' htan hP'
  obtain ⟨R, hR⟩ := adExt V.frame c.O ρ₀ _ hfull hP
  obtain ⟨Z, hZ⟩ := hrel R hR
  obtain ⟨z, hz, hzy⟩ := cocExt V.frame ρ₀ _ R hfull hcont hR y hy Z hZ
  have hinj : ∀ v : V.frame.Vl, Function.Injective fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) := fun v => by
    rw [hxx]
    refine psiInj (s.A v.1) (s.w v.1) (s.hw v.1) ?_ (x.psi v) (m v) k
      (StrictAnti.injective fun i j h => by have := hm v i j h; omega) hk (hkk v)
    have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
    exact (s.hw v.1 _).1 (by simpa using h1)
  have hfl₀ : ∀ v : V.frame.Vl, W.HasFlag (ρ₀.comp (V.frame.φ v)) fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) := fun v => by
    rw [hxx]
    exact hfl v
  have hfl' : ∀ v : V.frame.Vl, W.HasFlag (ρ'.comp (V.frame.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i) := fun v =>
    flagDual _ _ (hinj v) (by rw [← hred] at hfl₀; exact hfl₀ v) (hO v)
  have hbk := bkAb V R z hz
    (fun v φ hφ h1 h2 => at_l hU.coh.loc B Λ x' hΛ' hcont hy htan hR hzy v (hfl' v) (m v) k (hm v) hk φ hφ h1 fun i g hg => by
      rw [hxx, h2]
      exact hkk v i g hg)
    (bkAw V hV r R z hz (fun u g hg => (hzy g).trans (tan_one htan g (hI u g hg)))
      fun g hg => (hzy g).trans (cocycle_vanishes_on_inertia_of_point_pseudodeformation V B x ρ₀ h0 hD hcont y hy g hg))
  have hapt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ₀ := ⟨hcont, hx, ⟨_, arith hU.pr x m hm k hk hkk⟩, haut, by
    rintro _ ⟨g, hg, rfl⟩
    exact hv0 g hg, hfl⟩
  have hirr₀ : U3.MatIrr ⊤ (W.mat ρ₀) := fun N hN => (AlgebraTools.Det.irrIffSpan (W.mat ρ₀)).2 hfull N fun g v hv => hN g trivial v hv
  have hnice := _root_.UpperTheory.V.Th.nice0four_alt ι x ρ₀ hapt hirr₀ (free hU.pr hn1 ι x _ m hρ haut hm hfl k hk hkk) hC hD4
  obtain ⟨X, hX⟩ := hAd l L Ω s V hV hζ c hc 4 (by omega) le_rfl r h0 B ι x ρ₀ hnice (par x m hm k hk hkk) _ R hP hR z hz hbk
  obtain ⟨Q, hQ⟩ := conjOf ρ₀ y ρ' X htan fun g => by rw [← hzy, hX, hR.ad]
  exact constOf B x' ρ₀ ρ' Q hD' hQ hinj hfl₀ hfl'
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaModularIdealMap
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
open UpperTheory.V.Ws.H5 in
theorem UpperTheory.V.Ws.hida_modular_ideal_map :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ (n : ℕ) (φ' : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ' → J₀.map φ' = J := by
  intro _ Ω _ _ _ l _ c D T _ _ c' h K X B Λ ι J₀ hM φ hφ J hJ n φ' hφ'
  subst hJ
  have hl : ((l : ℕ) : B.B) ∈ maximalIdeal B.B := by
    haveI := (UpperTheory.V.Base.dvrFacts l c'.O).2.2.1
    have h1 : ((l : ℕ) : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    have h2 := map_nonunit (algebraMap c'.O B.B) _ (map_nonunit (algebraMap ℤ_[l] c'.O) _ h1)
    simpa using h2
  have stab : ∀ γ : K.V.frame.G₀ →* B.Bˣ, TwCh K.V.frame γ → ∃ τ : B.B →ₐ[c'.O] B.B,
      TwMap B (RingHom.id B.B) (τ : B.B →+* B.B) γ ∧ ∀ b ∈ J₀, τ b ∈ J₀ := fun γ hγ => by
    obtain ⟨τ, hτ⟩ := twMapEx B (AlgHom.id c'.O B.B) γ hγ
    exact ⟨τ, hτ, fun b hb => closedJ _ J₀ _ (twJN B J₀ hM.dense hM.twist hl γ hγ τ hτ b hb)⟩
  have key : ∀ (γ : K.V.frame.G₀ →* c'.Oˣ), TwCh K.V.frame γ → ∀ f f' : B.B →ₐ[c'.O] X.B,
      TwMap B (f : B.B →+* X.B) (f' : B.B →+* X.B) (W.pushCh (algebraMap c'.O X.B) γ) → J₀.map f' ≤ J₀.map f := by
    intro γ hγ f f' hf
    obtain ⟨τ, hτ, hτJ⟩ := stab _ ((twChOps _ γ hγ).2.2 B.B (algebraMap c'.O B.B) inferInstance)
    have h1 := hτ.comp (f : B.B →+* X.B)
    have h2 : W.pushCh (f : B.B →+* X.B) (W.pushCh (algebraMap c'.O B.B) γ) = W.pushCh (algebraMap c'.O X.B) γ :=
      MonoidHom.ext fun g => Units.ext (f.commutes _)
    rw [h2, RingHom.comp_id] at h1
    have h3 : f' = f.comp τ := twMapUniq B _ _ f' (f.comp τ) hf h1
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, h3]
    exact Ideal.mem_map_of_mem _ (hτJ b hb)
  obtain ⟨β₀, hβ, hβ'⟩ := descend K
  have hn := (twChOps _ β₀ hβ).1 n
  have hT := phiTw K X B β₀ hβ' n φ φ' hφ hφ'
  refine le_antisymm (key _ hn φ φ' hT) (key _ (twChOps _ _ hn).2.1 φ' φ ?_)
  have hu : ∀ g, algebraMap c'.O X.B (((β₀ ^ n)⁻¹ g : c'.Oˣ) : c'.O) * algebraMap c'.O X.B (((β₀ ^ n) g : c'.Oˣ) : c'.O) = 1 :=
    fun g => by rw [← map_mul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one, map_one]
  refine ⟨fun g i hi => ?_, fun v i g => ?_⟩
  · rw [hT.1 g i hi, ← mul_assoc, ← mul_pow]
    erw [hu g]
    rw [one_pow, one_mul]
  · rw [hT.2 v i g, mul_assoc, mul_comm (_ : X.B) ((W.pushCh _ (β₀ ^ n)⁻¹ _ : X.Bˣ) : X.B)]
    erw [hu]
    rw [mul_one]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointRepresentationWeights
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.Pt.point_representation_weights :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : W.Resid V.frame c.O n) (B : W.UniversalOrdinaryDeterminantRing r) (ι : PadicAlgCl l ≃+* ℂ) (J : Ideal B.B), B.PointTheoremBaseObject ι J → ∀ (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)) (m : W.Vl l L → Fin n → ℤ), 2 ≤ n → n ≤ 4 → x.IsRep ρ → Continuous ρ → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) → (∀ v i j, i < j → m v j + 2 ≤ m v i) → (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) → (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) → (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) → J ≤ RingHom.ker x := by
  intro hP l _ L Ω _ _ _ _ _ _ s V c n r B ι J hJ x ρ m hn2 hn4 hrep hc haut hv0 hm hfl ⟨k, hk, hw⟩
  have hov : ∀ v : W.Vl l L, (s.A v).valuation (l : Ω) < 1 := fun v => by
    simpa using (s.hA v _).2 v.2
  have hl : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal := fun v => by
    refine (s.hw v _).1 ?_
    simpa using hov v
  refine hJ x (fun v j _ => -m v j) ρ hn2 hn4 ⟨fun v τ i j hij => ?_, fun v j => ?_⟩
    hrep hc haut hv0
    fun v => ⟨hfl v, fun i j hij => ?_⟩
  · have := hm v i j hij
    simp only
    omega
  · exact UpperTheory.V.Loc.laArith hP.toClassicalTheorems.litN.aut.art (s.hw v) (hl v) _ (psi_cont x v j) (m v j) k hk (hw v j)
  · have hne : 1 - m v i + m v j ≠ 0 := by
      rcases lt_trichotomy i j with h | h | h
      · have := hm v i j h
        omega
      · subst h
        omega
      · have := hm v j i h
        omega
    obtain ⟨g, hg, hg1⟩ := cycIne L Ω l (s.A v) (hov v) ((1 - m v i + m v j) * k)
      (mul_ne_zero hne (by exact_mod_cast hk.ne'))
    have hgD : g ∈ Dec (F := L) (s.A v) :=
      (GlobalTheory.WeilDeligne.Weil_le_Dec (s.hw v)) (GlobalTheory.WeilDeligne.ineIncl (s.hw v) ⟨g, hg⟩).2
    have h1 := hw v i ⟨g, hgD⟩ hg
    have h2 := hw v j ⟨g, hgD⟩ hg
    have e : x.psi v i ⟨g, hgD⟩ = x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g := by
      rw [hij]; rfl
    apply hg1
    have e2 : x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i) =
        (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) * cycBar L Ω l g ^ (1 - m v i + m v j) := by
      rw [e, mul_assoc, mul_assoc, ← zpow_add, ← zpow_one_add]
      congr 2
      ring
    change (x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i)) ^ k = 1 at h1
    change (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) ^ k = 1 at h2
    rw [e2, mul_pow, h2, one_mul] at h1
    rw [zpow_mul, zpow_natCast, h1]
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
private theorem gsp_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) :
    IsGSp (f ν) (g.map f) := by
  have a : adj (g.map f) = (adj g).map f := by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  unfold IsGSp at h ⊢
  rw [a, ← Matrix.map_mul, h]
  ext i j
  simp [Matrix.one_apply, apply_ite f]
theorem UpperTheory.V.Th.local_zero_of_modular_p :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
        X.LocZero J (y : X.A →+* PadicAlgCl l) := by
  intro hU hA Ω _ _ _ l _ c D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ y hs q hq hqy
  obtain ⟨w, κ, π, a, k, hgap, hw, hκ, hk, hev, hκw, hreg, hatt⟩ := hs.aut
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Even (w 0 + n) := ⟨(w 0).natAbs, by
    rcases Int.natAbs_eq (w 0) with e | e <;> exact Int.even_iff.2 (by omega)⟩
  obtain ⟨d0, h0, e0⟩ := hgap 0
  obtain ⟨d1, h1, e1⟩ := hgap 1
  obtain ⟨d2, h2, e2⟩ := hgap 2
  replace e0 : w 0 = w 1 + 2 * d0 := e0
  replace e1 : w 1 = w 2 + 2 * d1 := e1
  replace e2 : w 2 = w 3 + 2 * d2 := e2
  rw [Int.even_iff] at hn hev
  obtain ⟨φ', hφ'⟩ := (_root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link hU D T hF hD c' h K X n).2 B
  obtain ⟨m, hm, hmk⟩ := Pt.ptWts K X B n φ' hφ' y w (fun i => Int.even_iff.2 (by fin_cases i <;> simp <;> omega)) hw
  have hg : ∀ v i j, i < j → m v j + 2 ≤ m v i := fun v i j hij => by
    have := hm v i j
    fin_cases i <;> fin_cases j <;> simp at hij this ⊢ <;> omega
  obtain ⟨hi, hi'⟩ := Pt.ptIrr K n _ hs.irr
  have hc := Pt.rho_cont K n (Pt.pt_cont X y hi)
  have hrep : (Link.pt φ' y).IsRep (K.rhoQ n _) := auRep D T c' h K X B n φ' hφ' y _ fun _ => rfl
  have hmul : ∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g))))
      ((X.P.map (y : X.A →+* PadicAlgCl l)).r g) := fun g => by
    rw [← y.commutes]
    exact _root_.gsp_map (y : X.A →+* PadicAlgCl l) (X.pair.mult g)
  have hunr := Pt.ptUnr K n (X.P.map (y : X.A →+* PadicAlgCl l)).r fun g hg => by
    change (y : X.A →+* PadicAlgCl l).mapMatrix (X.P.r g) = 1
    rw [X.pair.kill g hg, map_one]
  have hfl := Pt.ptFlag K X B n φ' hφ' y
  obtain ⟨Pp, hPp⟩ := Pt.ptPair K n _ hmul
  have haut := _root_.UpperTheory.V.Z.Win.Birth.ptAutR'_alt hU.pr K n ι _ hmul κ π a k hκ hk (Int.even_iff.2 (by omega)) hκw hreg hatt
    (Z.ImaginaryQuadraticEtaCharacter.potOfPair l T.L Ω K.s 4 _ _ Pp hPp _ m hg hfl hmk)
  have hJx := _root_.UpperTheory.V.Ws.Pt.point_representation_weights hU.pr l T.L Ω K.s K.V c' 4 K.r B ι J₀ hM.pt _ _ m (by norm_num) (by norm_num) hrep hc haut hunr hg hfl hmk
  rw [← _root_.UpperTheory.V.Ws.hida_modular_ideal_map hU D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ n φ' hφ', Ideal.map_le_iff_le_comap]
  exact _root_.UpperTheory.V.Th.eigenbasis_rank_four hU hA l T.L Ω K.s K.V K.hV K.noMu c' K.large K.r B Λ ι J₀ hM.toHidaProps K.v0 (P1.condC D T hF hD c' h K)
    (P1.condD D T hF hD c' h K) _ _ m hJx hrep hc haut hunr hi' hg hfl hmk
    _ (hq.comap φ') fun b hb => hqy _ hb
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.Gal.projectedFormsSystemPart.pm_exists_of_unramified_adjoint_lifting :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Ws.PMExAlt := fun U hA => _root_.UpperTheory.Gal.projectedFormsSystemPart.promodular_existence_of_local_zero U (_root_.UpperTheory.V.Th.local_zero_of_modular_p U hA)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ConductorAtMapInjectiveCoeff
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CountS
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
theorem UpperTheory.V.Z.Win.A4.exists_frob_nonvanishing_with_sha_bound :
    _root_.UpperTheory.V.Af.NumberSp4Alt → ∃ C A : ℕ, ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ k : ℕ, 0 < k → D.ψ ^ k = 1 → D.ξ ^ k = 1 → D.om ^ k = 1 → ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ N → p ∉ D.S → ∀ ι, D.AllIrr (_root_.UpperTheory.V.Aut.IsAut4Alt ι) → ∃ σ : G ℚ Ω, D.AllIrr (fun r => D.aVal σ r ≠ 0) ∧ (D.Ineq σ → Chr.nrm l c.O D.sha * Real.log l ≤ 2 * C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p) := by
  classical
  rintro ⟨C, A, hnum⟩
  refine ⟨C, A, ?_⟩
  intro Ω _ _ _ l hl c D hD N hN hψN hξN hoN k hk hψ hξ ho p hp hp5 hpN hpS ι haut
  have hlp : l ≠ p := fun h => hpS (h ▸ hD.l_mem)
  obtain ⟨-, hfr, -, hco, -, -, -, -, hpl, -⟩ := ML.placeBasic Ω
  have hB : ML.Over (D.pl p) p := hD.pl_over p hp
  obtain ⟨σ, hσ⟩ := hfr _ p hp hB
  obtain ⟨w, hw, -, hpw⟩ := hpl _ p hp hB
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => by
    refine hco _ p l ((Nat.coprime_primes hp hl.out).2 hlp.symm) hB ?_
    have h1 := (hw ((l : ℕ) : 𝓞 ℚ)).2 h
    have e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [e] at h1
    exact h1
  have hχ : (((chiO ℚ Ω l c.O σ : c.Oˣ) : c.O) : PadicAlgCl l) = (p : PadicAlgCl l) := by
    have hz : (cycZ ℚ Ω l σ : ℤ_[l]) = (p : ℤ_[l]) := by
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      exact cycZ_toZModPow_eq hlw hw hσ.2 n
    simp only [chiO, MonoidHom.comp_apply, Units.coe_map]
    rw [hz]
    simp
  have h3 : (D.om⁻¹ * D.ξ) ^ k = 1 := by rw [mul_pow, inv_pow, ho, hξ, inv_one, one_mul]
  have h1 : (D.om⁻¹ * D.ξ * D.ψ) ^ k = 1 := by rw [mul_pow, h3, hψ, one_mul]
  have mapped_pow (χ : G ℚ Ω →* c.Oˣ) (h : χ ^ k = 1) :
      ι ((χ σ : c.O) : PadicAlgCl l) ^ k = 1 := by
    have hσpow : χ σ ^ k = 1 := by
      rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]
    rw [← map_pow]
    have hcast : ((χ σ : c.O) : PadicAlgCl l) ^ k = 1 := by
      rw [← Subalgebra.coe_pow, ← Units.val_pow_eq_pow_val, hσpow]
      rfl
    rw [hcast, map_one]
  obtain ⟨NN, hNN, hlog, hX⟩ := hnum D.e hD.two_le N hN p w hp hpw hp5 hpN k hk _ _ _
    (mapped_pow _ h1) (mapped_pow _ hψ) (mapped_pow _ h3)
  replace hX := hX l hD.l_odd hlp Ω ι (D.pl p) hw σ hσ
  have htrace : (D.r0E σ).trace = ι.symm (Af.eis4 p D.e
      (ι (((D.om⁻¹ * D.ξ * D.ψ) σ : c.O) : PadicAlgCl l))
      (ι ((D.ψ σ : c.O) : PadicAlgCl l)) (ι (((D.om⁻¹ * D.ξ) σ : c.O) : PadicAlgCl l))) := by
    have hsum : (D.r0E σ).trace = ∑ i, (((D.ps i σ : c.Oˣ) : c.O) : PadicAlgCl l) := by
      simp [Raw.r0E, Raw.r0, mapRep, diagRep, Matrix.trace]
    rw [hsum]
    simp only [Fin.sum_univ_four, Raw.ps, Raw.th, Raw.al, Raw.Psi, Chr.Psi, Af.eis4, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      zpow_natCast, MonoidHom.mul_apply, MonoidHom.one_apply, MonoidHom.inv_apply, MonoidHom.pow_apply,
      Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, Subalgebra.coe_mul, Subalgebra.coe_one,
      Subalgebra.coe_pow, map_add, map_mul, map_pow, map_natCast, map_one, RingEquiv.symm_apply_apply, hχ]
    ring
  rw [← htrace] at hX
  have hadm : ∀ r, D.EPt r → Irr r → _root_.UpperTheory.V.Af.AdmRAlt ι N ![(D.e : ℤ) + 1, D.e, 1, 0] (D.e + 1) r.toHomUnits := by
    intro r hr hi
    obtain ⟨hlev, θ, hθ, hdual, -⟩ := level D hD N hN hψN hξN hoN r hr
    exact ⟨((irrIff _).1 r).1 hi, haut r hr hi, hlev, ⟨θ, hθ, hdual⟩, _root_.UpperTheory.V.Z.Win.A4.safe4' D hD N hN hψN hξN hoN r hr⟩
  have hne : D.AllIrr (fun r => D.aVal σ r ≠ 0) := by
    intro r hr hi
    have h := (hX {r.toHomUnits} (fun s hs => by rw [Finset.mem_singleton.1 hs]; exact hadm r hr hi)
      (fun s hs s' hs' _ => by rw [Finset.mem_singleton.1 hs, Finset.mem_singleton.1 hs'])).1 _
      (Finset.mem_singleton_self _)
    exact sub_ne_zero.2 h
  refine ⟨σ, hne, ?_⟩
  rintro ⟨-, Xi, hXi, hconj, hle⟩
  have hinj : Function.Injective fun r : G ℚ Ω →* M4 (PadicAlgCl l) => r.toHomUnits := fun r r' h =>
    MonoidHom.ext fun g => congrArg Units.val (DFunLike.congr_fun h g)
  have h := (hX (Xi.image fun r => r.toHomUnits) (fun s hs => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      exact hadm r (hXi r hr).1 (hXi r hr).2) (fun s hs s' hs' hss => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hs'
      rw [hconj r hr r' hr' (((irrIff _).2 r r').2 hss)])).2
  rw [Finset.prod_image hinj.injOn] at h
  change _ ≤ ∏ r ∈ Xi, ‖D.aVal σ r‖ at h
  have hN0 : 0 < ‖(NN : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast hNN)
  have h4 := Real.log_le_log hN0 h
  rw [Real.log_prod fun r hr => norm_ne_zero_iff.2 (hne r (hXi r hr).1 (hXi r hr).2)] at h4
  have h5 : -Real.log ‖(NN : PadicAlgCl l)‖ ≤ Real.log |(NN : ℝ)| := by
    have hq : (NN : ℚ) ≠ 0 := by exact_mod_cast hNN
    have hx : ‖(NN : PadicAlgCl l)‖ = (l : ℝ) ^ (-(padicValInt l NN : ℤ)) := by
      have hc : (((NN : ℚ) : ℚ_[l]) : PadicAlgCl l) = (NN : PadicAlgCl l) := by simp
      rw [← hc, PadicAlgCl.norm_extends, Padic.eq_padicNorm]
      have hnorm := padicNorm.eq_zpow_of_ne_zero (p := l) hq
      rw [padicValRat.of_int] at hnorm
      rw [hnorm]
      push_cast
      rfl
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    have hdvd : ((l : ℤ) ^ padicValInt l NN) ∣ NN := padicValInt_dvd NN
    have hle : ((l : ℤ) ^ padicValInt l NN) ≤ |NN| :=
      Int.le_of_dvd (abs_pos.mpr hNN) ((dvd_abs _ _).mpr hdvd)
    have hle' : (l : ℝ) ^ padicValInt l NN ≤ |(NN : ℝ)| := by exact_mod_cast hle
    rw [hx, Real.log_zpow]
    push_cast
    rw [neg_mul, neg_neg, ← Real.log_pow]
    exact Real.log_le_log (pow_pos hl0 _) hle'
  have h6 : (C : ℝ) * Nat.totient k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p ≤
      C * k * ((N : ℝ) * (D.e + 1)) ^ A * Real.log p := by
    have : (Nat.totient k : ℝ) ≤ k := by exact_mod_cast Nat.totient_le k
    have := Real.log_natCast_nonneg p
    gcongr
  rw [Finset.sum_neg_distrib] at hle
  linarith
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Transfer
variable {O O' : Type} [CommRing O] [CommRing O'] {N : ℕ} (f : O →+* O')
private def chHom : DirichletCharacter O N →* DirichletCharacter O' N where
  toFun χ := χ.ringHomComp f
  map_one' := MulChar.ringHomComp_one f
  map_mul' a b := MulChar.ringHomComp_mul a b f
private theorem chHom_inj (hf : Function.Injective f) : Function.Injective (chHom (N := N) f) :=
  MulChar.injective_ringHomComp hf
private theorem chHom_ord (hf : Function.Injective f) (χ : DirichletCharacter O N) : orderOf (chHom f χ) = orderOf χ :=
  orderOf_injective _ (chHom_inj f hf) _
private theorem chHom_comp (r : ℕ) (χ : DirichletCharacter O N) : chHom f (comp r χ) = comp r (chHom f χ) := by
  refine MulChar.ext fun a => ?_
  show f (comp r χ a) = _
  simp only [HV.comp, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rfl
private theorem map_injective_coeff_twist_comm (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (th0 l χ) = th0 l (chHom f χ) := by
  simp only [th0, lPrime, lPart, map_mul, map_inv, map_pow, chHom_ord f hf]
private theorem chHom_chiP (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    chHom f (chiP l χ) = chiP l (chHom f χ) := by
  simp only [chiP, map_mul, map_inv, chHom_comp, map_injective_coeff_twist_comm f hf]
private theorem conductor_at_map_injective_coeff (hf : Function.Injective f) (l : ℕ) (χ : DirichletCharacter O N) :
    n0 l (chHom f χ) = n0 l χ := by
  have h : chHom f (th1 l χ) = th1 l (chHom f χ) := by
    simp only [th1, map_mul, map_inv, chHom_comp, map_injective_coeff_twist_comm f hf]
  unfold n0 f0
  rw [← h, chHom_ord f hf]
private theorem chHom_ker (hf : Function.Injective f) (χ : DirichletCharacter O N) :
    (chHom f χ).toUnitHom.ker = χ.toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  exact map_eq_one_iff f hf
private theorem parity_at_map_injective_coeff [NeZero N] (hf : Function.Injective f) (χ : DirichletCharacter O N) :
    c2 (chHom f χ) = c2 χ := by
  have h : ∀ φ : DirichletCharacter O N, (chHom f φ).conductor = φ.conductor := fun φ => by
    unfold DirichletCharacter.conductor
    congr 1
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    by_cases hd : d ∣ N
    · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
        chHom_ker f hf]
    · exact ⟨fun h => absurd h.dvd hd, fun h => absurd h.dvd hd⟩
  unfold c2 psi2
  rw [← chHom_comp, h]
private theorem chHom_even (hf : Function.Injective f) (e : ℕ) (χ : DirichletCharacter O N) :
    PsiEven e (chHom f χ) ↔ PsiEven e χ := by
  show f (χ (-1)) = _ ↔ χ (-1) = _
  rw [← hf.eq_iff (a := χ (-1)), map_pow, map_neg f, map_one f]
end Transfer
private theorem enough_of_le {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity c.O n] : HasEnoughRootsOfUnity c'.O n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot c.O n
  exact ⟨⟨_, hζ.map_of_injective (f := Subalgebra.inclusion h) (Subalgebra.inclusion_injective h)⟩, inferInstance⟩
private theorem main_big (hA : _root_.UpperTheory.V.Aut.SymplecticFourImageDense) (hP : CohomologyHyp) (hM : LemmaM) (hM' : LemmaM') (hLP : LemmaP) (hN : _root_.UpperTheory.V.Af.NumberSp4Alt)
    (hAd : _root_.UpperTheory.V.Th.RigiditySymplecticFour) (hX : X.CorX)
    (hSo : ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], SoV Ω l ∧ SoFin Ω l)
    (χ : Formalism.HC.PChar) : ∃ C : ℕ, ∀ h : Host, h.chi = χ → ∀ t : ℕ, h.Big t →
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ),
      l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, h.CaseII l e ψ ∨ h.CaseIII l e ψ →
      HasEnoughRootsOfUnity c.O (2 ^ h.nII l ψ) → HasEnoughRootsOfUnity c.O (2 ^ h.nIII l ψ) →
      VLe Ω c e ψ (((l : ℝ) * h.N * e) ^ C) := by
  obtain ⟨C, A, hc⟩ := _root_.UpperTheory.V.Z.Win.A4.exists_frob_nonvanishing_with_sha_bound hN
  obtain ⟨C', hC'⟩ := arith χ C A
  refine ⟨C', fun h hχ t ht Ω _ _ _ l hl c e hl2 he0 het ψ hψ hcase r1 r2 => ?_⟩
  obtain ⟨D, hD, hOf⟩ := dataEx hX Ω h t ht l c e hl2 he0 het ψ hψ hcase r1 r2
  obtain ⟨hF, hNE, ι, hAU⟩ := hA Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf
  have hctx : Ctx2 D ∨ Ctx3 D :=
    hOf.imp (fun hc => ⟨hD, h, t, e, ψ, ht, he0, het, hψ, hc.1, hc.2⟩)
      (fun hc => ⟨hD, h, t, e, ψ, ht, he0, het, hψ, hc.1, hc.2⟩)
  have hsha := shaEq Ω h t ht l c e hl2 he0 het ψ hψ D hD hOf
  obtain ⟨M⟩ := exModel D hD hLP (phiGam D hD hP) (nums D hD hP) (locBase D hD hP.loc)
  have ho : 0 < h.o := (hostIndex h).2.2.2.1
  have hlp := hl.out
  obtain ⟨n', p₁, m₀, hO, hn', hm₀, har⟩ : ∃ n' p₁ m₀ : ℕ, Aut.OfChar D e ψ n' p₁ m₀ ∧ c2 ψ ≤ n' ∧ m₀ ∣ h.o ∧
      ((n' = h.nII l ψ ∧ p₁ = 1) ∨ (n' = h.nIII l ψ ∧ p₁ = UpperTheory.V.pOne χ)) := by
    rcases hOf with ⟨-, hO⟩ | ⟨h3, hO⟩
    · refine ⟨_, _, _, hO, ?_, one_dvd _, Or.inl ⟨rfl, rfl⟩⟩
      have h1 : 2 ^ c2 ψ ≤ max (l * h.N * 4 ^ n0 l ψ) (2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2) := by
        refine le_trans ?_ (le_max_right _ _)
        have hq : 0 < h.q := NeZero.pos _
        have := hlp.pos
        rw [pow_add, mul_assoc, mul_assoc, mul_assoc]
        exact Nat.le_mul_of_pos_right _ (by positivity)
      have h2 := Nat.clog_mono_right 2 h1
      rwa [Nat.clog_pow 2 _ (by norm_num)] at h2
    · obtain ⟨a, -, b, -⟩ := (hostOdd h c.O ψ (h.mem_X.1 hψ).1).1 h3.2.2.1
      exact ⟨_, _, _, hO, b ▸ Nat.zero_le _, a.trans (Nat.ordCompl_dvd _ _), Or.inr ⟨rfl, by rw [hχ]⟩⟩
  obtain ⟨⟨k1, k2, k3⟩, o1, o2, o3⟩ := levOf Ω h t ht l c e hl2 he0 het ψ hψ D hD n' p₁ m₀ hO hn' hm₀
  have hp₁ : 0 < p₁ := by
    obtain ⟨a, -⟩ := hO.xi
    exact NeZero.pos _
  have hNp := h.N_pos
  have hlpos := hlp.pos
  obtain ⟨q1, q2, q3, -⟩ := pZeroLe (l * h.N * p₁) (by positivity)
  have q4 : ¬ pZero (l * h.N * p₁) ∣ 2 := fun hd => by have := Nat.le_of_dvd two_pos hd; omega
  have q5 : ¬ pZero (l * h.N * p₁) ∣ l * 2 ^ n' * h.N * p₁ := fun hd => by
    rw [show l * 2 ^ n' * h.N * p₁ = 2 ^ n' * (l * h.N * p₁) by ring] at hd
    exact ((Nat.Prime.dvd_mul q1).1 hd).elim (fun a => q4 (q1.dvd_of_dvd_pow a)) q3
  have q6 : pZero (l * h.N * p₁) ∉ D.S := fun hd => by
    rw [hO.S_eq] at hd
    have hd := Nat.dvd_of_mem_primeFactors hd
    rw [show 2 * l * h.N * p₁ = 2 * (l * h.N * p₁) by ring] at hd
    exact ((Nat.Prime.dvd_mul q1).1 hd).elim q4 q3
  have hlev : 1 ≤ l * 2 ^ n' * h.N * p₁ := Nat.pos_of_ne_zero (by positivity)
  have hk : 0 < (l - 1) * 2 ^ n' * (2 * h.o) := by
    have : 0 < l - 1 := Nat.sub_pos_of_lt hlp.one_lt
    positivity
  obtain ⟨σ, hσ, hle⟩ := hc D hD _ hlev k1 k2 k3 _ hk o1 o2 o3 _ q1 q2 q5 q6 ι hAU
  have hI : D.Ineq σ := galoisRep_ineq_of_allIrreducible_nonvanishing D hD M hM hM' hP.loc (hSo Ω l).1 (hSo Ω l).2 hF hNE
    (fun r hr hi => hAd Ω l c D hctx _ hlev k1 k2 k3 ι r hr hi (hAU r hr hi)) σ hσ
  have he2 : 2 ≤ e := hO.e_eq ▸ hD.two_le
  have hb := hC' h hχ l c e hl2 he2 ψ hψ n' p₁ har
  have hle' := hle hI
  rw [hO.e_eq] at hle'
  refine ⟨ne_top_of_le_ne_top hI.1 hsha, le_trans ?_ (hle'.trans hb)⟩
  exact mul_le_mul_of_nonneg_right (Chr.nrm_mono l hsha hI.1) (Real.log_natCast_nonneg l)
theorem UpperTheory.V.Th.sp4Main_alt :
    _root_.UpperTheory.V.Aut.SymplecticFourImageDense → CohomologyHyp → LemmaM → LemmaM' → LemmaP → _root_.UpperTheory.V.Af.NumberSp4Alt → _root_.UpperTheory.V.Th.RigiditySymplecticFour → X.CorX → (∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], SoV Ω l ∧ SoFin Ω l) → CountII ∧ CountIII := by
  intro hA hP hM hM' hLP hN hAd hX hSo
  have key : CountShape fun h l _ _ e ψ => h.CaseII l e ψ ∨ h.CaseIII l e ψ := by
    intro χ
    obtain ⟨C, hC⟩ := main_big hA hP hM hM' hLP hN hAd hX hSo χ
    refine ⟨C, fun h hχ t ht Ω _ _ _ l _ c e hl2 he0 het ψ hψ hcase => ?_⟩
    obtain ⟨c₁, h₁⟩ := exists_coef l (2 ^ (h.nII l ψ + h.nIII l ψ))
    obtain ⟨c', hc, hc₁⟩ := (coefSup l).1 c c₁
    have h₂ := enough_of_le hc₁ (2 ^ (h.nII l ψ + h.nIII l ψ))
    let f : c.O →+* c'.O := (Subalgebra.inclusion hc).toRingHom
    have hf : Function.Injective f := Subalgebra.inclusion_injective hc
    have e2 : h.nII l (chHom f ψ) = h.nII l ψ := by
      unfold Host.nII
      rw [conductor_at_map_injective_coeff f hf, parity_at_map_injective_coeff f hf]
    have e3 : h.nIII l (chHom f ψ) = h.nIII l ψ := by
      unfold Host.nIII
      rw [conductor_at_map_injective_coeff f hf]
    have hψ' : chHom f ψ ∈ h.X c' e := by
      rw [h.mem_X] at hψ ⊢
      refine ⟨?_, (chHom_even f hf e ψ).2 hψ.2⟩
      unfold Host.IsChar
      rw [chHom_ker f hf]
      exact hψ.1
    have hcase' : h.CaseII l e (chHom f ψ) ∨ h.CaseIII l e (chHom f ψ) := by
      rcases hcase with ⟨a, b, d⟩ | ⟨a, b, d, g⟩
      · refine Or.inl ⟨a, ?_, d⟩
        unfold EV
        rw [← chHom_chiP f hf, chHom_ord f hf]
        exact b
      · exact Or.inr ⟨a, b, (chHom_ord f hf ψ).symm ▸ d, fun h0 => g ((map_eq_one_iff _ (chHom_inj f hf)).1 h0)⟩
    have hV := hC h hχ t ht Ω l c' e hl2 he0 het _ hψ' hcase'
      (e2.symm ▸ HasEnoughRootsOfUnity.of_dvd c'.O (pow_dvd_pow 2 (Nat.le_add_right _ (h.nIII l ψ))))
      (e3.symm ▸ HasEnoughRootsOfUnity.of_dvd c'.O (pow_dvd_pow 2 (Nat.le_add_left _ (h.nII l ψ))))
    obtain ⟨a, b⟩ := coefIndep Ω l c c' h.N e ψ (chHom f ψ) fun _ => rfl
    exact ⟨fun h0 => hV.1 (a.1 h0), b ▸ hV.2⟩
  refine ⟨fun χ => ?_, fun χ => ?_⟩
  · obtain ⟨C, hC⟩ := key χ
    exact ⟨C, fun h hχ t ht Ω _ _ _ l _ c e a b d ψ hψ hc => hC h hχ t ht Ω l c e a b d ψ hψ (Or.inl hc)⟩
  · obtain ⟨C, hC⟩ := key χ
    exact ⟨C, fun h hχ t ht Ω _ _ _ l _ c e a b d ψ hψ hc => hC h hχ t ht Ω l c e a b d ψ hψ (Or.inr hc)⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.DescentVanishingReductions
open UpperTheory.V.Lit UpperTheory.V.W
theorem adjoint_lift_of_prints (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.UnramifiedInputs :=
  have hN := hH.litN
  ⟨⟨_root_.UpperTheory.V.W.locPrints_of_litN hN, hN.coh.pt, hN.coh.gf, hN.coh.ge, hN.coh.uo, hN.coh.gw⟩, hH, _root_.UpperTheory.V.HV.Core.modU_of_printsH hH, levEx, lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN),
    b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))⟩
theorem adjoint_lifting_of_cohomology (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Th.AdjointLiftingTheorem := _root_.UpperTheory.V.Th.adjoint_lifting_of_cohomology hH (_root_.UpperTheory.V.W.cohP_alt hH.litN)
theorem pmEx_of_printsH (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.PMExAlt := _root_.UpperTheory.Gal.projectedFormsSystemPart.pm_exists_of_unramified_adjoint_lifting (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH) (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lifting_of_cohomology hH)
theorem countII_and_countIII_of_printsH_of_sp4In (hH : _root_.UpperTheory.V.Af.HypothesesH') (hK : ∃ CK : ℝ, LemmaK CK) (hS : _root_.UpperTheory.V.Aut.SymplecticFourImageDense) : CountII ∧ CountIII := by
  have hN := hH.litN
  obtain ⟨CK, hL⟩ := hK
  refine _root_.UpperTheory.V.Th.sp4Main_alt hS (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH).coh Alg.M.main_holds Alg.M.mprime_holds Alg.lemmaP (_root_.UpperTheory.GalN.V.numberSp4_n_alt hH.toClassicalTheorems)
    (_root_.UpperTheory.V.Th.rigSp4_alt (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lift_of_prints hH) (_root_.UpperTheory.V.HV.DescentVanishingReductions.adjoint_lifting_of_cohomology hH)) (X.corX X.lemmaX X.residual_bernoulli_nonvanishing) fun Ω _ _ _ l _ => ⟨?_, fun c => ?_⟩
  · exact X.soBar CK hL (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK ℚ Ω l
  · exact X.soFin CK hL (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK ℚ Ω l c.O
end UpperTheory.V.HV.DescentVanishingReductions
end
