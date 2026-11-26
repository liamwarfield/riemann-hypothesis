module

public import Formalism.PairingDivisors.StatementA
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology

namespace GlobalTheory.CMVal.OrderUnits

variable {E : Type} [Field E] [NumberField E]

theorem ball_mem_nhds (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (z : P.adicCompletion E) :
    {x : P.adicCompletion E | Valued.v (x - z) ≤ WithZero.exp (-(n : ℤ))} ∈ 𝓝 z := by
  set t : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) ^ n with ht
  have hv : Valued.v (t : P.adicCompletion E) = WithZero.exp (-(n : ℤ)) := by
    have h2 : Valued.v ((Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) : (P.adicCompletion E)ˣ) : P.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec P
    rw [ht, Units.val_pow_eq_pow_val, map_pow, h2, ← WithZero.exp_nsmul]
    simp
  have hc : Continuous fun x : P.adicCompletion E => (x - z) / (t : P.adicCompletion E) := by fun_prop
  have ho := (Valued.isOpen_valuationSubring (P.adicCompletion E)).preimage hc
  refine mem_of_superset (ho.mem_nhds ?_) ?_
  · show (z - z) / (t : P.adicCompletion E) ∈ Valued.v.valuationSubring
    rw [sub_self, zero_div]; exact zero_mem _
  · intro x hx
    have hx' : Valued.v ((x - z) / (t : P.adicCompletion E)) ≤ 1 := hx
    rw [map_div₀, hv, div_le_one₀ (WithZero.exp_pos)] at hx'
    exact hx'

theorem val_int_le (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (b : 𝓞 E) (hb : b ∈ P.asIdeal ^ n) :
    Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (P.intValuation_le_pow_iff_mem b n).2 hb

theorem exists_cong {c : Ideal (OF E)} (v : HeightOneSpectrum (OF E)) (n : ℕ) (hn : v.asIdeal ^ n ∣ c)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ P ∈ S, Over P v) {z : Af E} (hz : z ∈ hatO c) :
    ∃ a : OF E, ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P) ≤ WithZero.exp (-(n : ℤ)) := by
  have hev : ∀ P : HeightOneSpectrum (𝓞 E), Continuous fun z : Af E => z P := fun P =>
    RestrictedProduct.continuous_eval P
  have hU : ∀ᶠ x : Af E in 𝓝 z, ∀ P ∈ S, Valued.v (x P - z P) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [Filter.eventually_all_finset]
    intro P _
    exact (hev P).tendsto z (ball_mem_nhds P n (z P))
  have hz1 : z ∈ closure (((orderC c).map (algebraMap E (Af E)) : Subring (Af E)) : Set (Af E)) := hz
  obtain ⟨x, ⟨k, hk, rfl⟩, hx⟩ := ((mem_closure_iff_frequently.1 hz1).and_eventually hU).exists
  obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hk
  refine ⟨a, fun P hP => ?_⟩
  have hb' : b ∈ P.asIdeal ^ n := by
    have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal ^ n := by
      refine (Ideal.map_mono (Ideal.le_of_dvd hn)).trans ?_
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_le_iff_le_comap]
      exact (hS P hP).ge
    exact h1 hb
  have h2 := val_int_le P n b hb'
  have h3 := hx P hP
  rw [map_add (f := _)] at h3
  have h4 : algebraMap E (Af E) (algebraMap (OF E) E a) P - z P =
      ((algebraMap E (Af E) (algebraMap (OF E) E a) + algebraMap E (Af E) (algebraMap (𝓞 E) E b)) P - z P) -
        algebraMap E (Af E) (algebraMap (𝓞 E) E b) P := by
    change _ = (algebraMap E (Af E) (algebraMap (OF E) E a) P + algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z P) - _
    ring
  rw [h4]
  exact Valuation.map_sub_le _ h3 h2

theorem val_le_one {c : Ideal (OF E)} {z : Af E} (hz : z ∈ hatO c) (P : HeightOneSpectrum (𝓞 E)) : Valued.v (z P) ≤ 1 := by
  obtain ⟨a, ha⟩ := exists_cong (P.under (OF E)) 0 (by simp) {P} (fun P' hP' => by
    rw [Finset.mem_singleton.1 hP']; rfl) hz
  have h1 := ha P (Finset.mem_singleton_self P)
  have h2 := val_int_le P 0 (algebraMap (OF E) (𝓞 E) a) (by simp)
  have h3 : z P = algebraMap E (Af E) (algebraMap (OF E) E a) P - (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P) := by
    ring
  rw [h3]
  exact (Valuation.map_sub_le _ h2 h1).trans_eq (by simp)

theorem val_eq_one {c : Ideal (OF E)} {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) P) = 1 := by
  have h1 := val_le_one (mem_hatOUnits.1 hy).1 P
  have h2 := val_le_one (mem_hatOUnits.1 hy).2 P
  have h3 : Valued.v ((y : Af E) P) * Valued.v ((↑y⁻¹ : Af E) P) = 1 := by
    rw [← map_mul]
    exact (congrArg Valued.v (coord P y).val_inv).trans (map_one _)
  exact le_antisymm h1 (by
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ Valued.v ((y : Af E) P) * 1 := by gcongr
      _ = _ := mul_one _)

theorem finPart_eq_one_of_level {c : Ideal (OF E)} {χ : HChar E} (hF : TrivOnF χ)
    (hl : ∀ v : HeightOneSpectrum (OF E), ∃ n : ℕ, v.asIdeal ^ n ∣ c ∧ ∀ P, Over P v → LevelLe χ P n)
    {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) : finPart χ y = 1 := by
  refine Fibre.finPart_eq_one_of_fibres E χ y fun v => ?_
  set S := Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v with hS
  have hO : ∀ P ∈ S, Over P v := fun P hP => by
    rw [hS] at hP
    unfold Formalism.L2.Host.aboveF at hP
    rw [Set.Finite.mem_toFinset] at hP
    have : P.under (OF E) = v := hP
    rw [← this]; rfl
  obtain ⟨n, hn, hlev⟩ := hl v
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Finset.prod_eq_one fun P hP => (χ.unrAt_iff P).2 (hlev P (hO P hP)) _ (val_eq_one hy P)
  obtain ⟨a, ha⟩ := exists_cong v n hn S hO (mem_hatOUnits.1 hy).1
  have hva : ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P) = 1 := fun P hP => by
    have hlt : Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - (y : Af E) P) < Valued.v ((y : Af E) P) := by
      rw [val_eq_one hy P]
      refine (ha P hP).trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    rw [Valuation.map_eq_of_sub_lt _ hlt, val_eq_one hy P]
  by_cases h0 : algebraMap (OF E) E a = 0
  · refine Finset.prod_eq_one fun P hP => ?_
    have h1 := hva P hP
    rw [h0, map_zero] at h1
    exact absurd (h1.symm.trans (map_zero _)) one_ne_zero
  let k' : (maximalRealSubfield E)ˣ := Units.mk0 (a : maximalRealSubfield E)
    (fun h1 => h0 (congrArg Subtype.val h1))
  have h2 := hF.1 v k'
  unfold Formalism.L2.Host.HChar.resFin at h2
  rw [MonoidHom.finsetProd_apply] at h2
  rw [← h2]
  refine Finset.prod_congr rfl fun P hP => ?_
  set u : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) k') with hu
  have hu' : (u : P.adicCompletion E) = algebraMap E (Af E) (algebraMap (OF E) E a) P := rfl
  have hvu : Valued.v (u : P.adicCompletion E) = 1 := hva P hP
  show χ.loc P (coord P y) = χ.loc P u
  have h3 : χ.loc P (u / coord P y) = 1 := by
    refine hlev P (hO P hP) _ ?_ ?_
    · show Valued.v ((u / coord P y : (P.adicCompletion E)ˣ) : P.adicCompletion E) = 1
      rw [Units.val_div_eq_div_val, map_div₀, hvu, coe_coord, val_eq_one hy P, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one (coord P y).ne_zero, map_div₀, coe_coord, val_eq_one hy P, div_one, hu']
      exact ha P hP
  rw [map_div, div_eq_one] at h3
  exact h3.symm

theorem finPart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E),
    UnramFin E → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ →
      ∀ y ∈ hatOUnits (condQ 𝔣 Q), finPart χ y = 1 := by
  intro E _ _ _ I _ φ _ s κ 𝔣 Q χ _ _ _ hχ y hy
  refine finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hy
  by_cases hv : v ∈ Q
  · refine ⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩
    rw [pow_one]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
  · exact ⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _,
      fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩

end GlobalTheory.CMVal.OrderUnits
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUnique
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TwPairUniq

theorem main : ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
    ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨hI, -, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i
  obtain ⟨hJ, hJflat, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q j
  have hT : IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) :=
    GlobalTheory.T.isTateTwistResolution_tensor_flat q i j (i + j) rfl _ _ hI hJ hJflat τ hτ
  obtain ⟨huniv, -, hext⟩ := GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ
  obtain ⟨-, -, hK⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q (i + j)
  obtain ⟨⟨u, hu⟩, huniq⟩ := hK _ hT
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, hν⟩ := hext u
    show IsTwPair (pick IsTwPair)
    refine pick_spec ⟨ν, fun U ζ => ?_⟩
    exact (hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).symm.trans (hu U ζ)
  · intro k hk μ ν hμ hν E n m w h
    subst hk
    obtain ⟨uμ, huμ, -⟩ := huniv μ (𝟙 _) (𝟙 _)
    obtain ⟨uν, huν, -⟩ := huniv ν (𝟙 _) (𝟙 _)
    have hom := huniq uμ uν (fun U ζ =>
      (huμ U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).trans ((hμ U ζ).trans ((hν U ζ).symm.trans
        (huν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).symm)))
    obtain ⟨hid, -, -, -, hhtp⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)
    have key : ∀ (π : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))) (v : T ⟶ res _ (tw q (i + j))),
        τ.Compat π (𝟙 _) (𝟙 _) v → ∀ a b, π.cup E h a b = cpush _ v w (τ.cup E h a b) := by
      intro π v hc a b
      rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ π (𝟙 _) (𝟙 _) v hc E h a b, (hid _ _ n a).2, (hid _ _ m b).2]
    refine AddMonoidHom.ext fun a => AddMonoidHom.ext fun b => ?_
    rw [key μ uμ huμ, key ν uν huν, (hhtp uμ uν hom _ w).2]

end GlobalTheory.EtC.TwPairUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique : ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k → ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν → ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h := by
  first
  | exact @GlobalTheory.EtC.TwPairUniq.main
  | exact GlobalTheory.EtC.TwPairUniq.main
  | (intros; apply GlobalTheory.EtC.TwPairUniq.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.IdeleModule
variable {E : Type} [Field E] [NumberField E]

theorem coord_ne (y : (Af E)ˣ) (v : HeightOneSpectrum (𝓞 E)) : Valued.v ((y : Af E) v) ≠ 0 := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 v
  simpa using this

theorem modF_finite (y : (Af E)ˣ) : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v ((y : Af E) v)))).Finite := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  positivity

theorem modF_mul (y y' : (Af E)ˣ) : modF (y * y') = modF y * modF y' := by
  unfold modF
  rw [← finprod_mul_distrib (modF_finite y) (modF_finite y')]
  refine finprod_congr fun v => ?_
  have : ((y * y' : (Af E)ˣ) : Af E) v = (y : Af E) v * (y' : Af E) v := rfl
  rw [this, map_mul, WithZero.log_mul (coord_ne y v) (coord_ne y' v), zpow_add₀ (absNorm_pos v).ne']

theorem modF_pos (y : (Af E)ˣ) : 0 < modF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (absNorm_pos v) _

theorem modF_princ (k : Eˣ) :
    modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|((Algebra.norm ℚ (k : E) : ℚ) : ℝ)|)⁻¹ := by
  have h := FinitePlace.prod_eq_inv_abs_norm (K := E) k.ne_zero
  push_cast at h
  rw [← h, ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  unfold modF
  refine finprod_congr fun v => ?_
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have h1 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom k : (Af E)ˣ) : Af E) v) = v.valuation E (k : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : E)
  rw [h1, WithZeroMulInt.toNNReal_neg_apply _ h0]
  push_cast
  congr 1

end GlobalTheory.CMVal.IdeleModule

theorem GlobalTheory.CMVal.modF_mul_pos_principal : ∀ (E : Type) [Field E] [NumberField E], (∀ y y' : (Af E)ˣ, modF (y * y') = modF y * modF y') ∧ (∀ y : (Af E)ˣ, 0 < modF y) ∧ ∀ k : Eˣ, modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|(Algebra.norm ℚ (k : E) : ℝ)|)⁻¹ :=
  fun _ _ _ => ⟨IdeleModule.modF_mul, IdeleModule.modF_pos, IdeleModule.modF_princ⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cover_chart_smooth_normal : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ I : Finset (Fin (d + 1)), I.Nonempty → Module.Finite (rA k x I) (integralClosure (rA k x I) K) ∧ IsFractionRing (rB k K x I) K ∧ Algebra.Smooth k (rB k K x I) := by
  first | (exact @GlobalTheory.PD.rB_finite_frac_smooth) | (exact GlobalTheory.PD.rB_finite_frac_smooth) | (intros; apply GlobalTheory.PD.rB_finite_frac_smooth  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConnectedGlobalSections

variable {q : ℕ} [NeZero q] {i : ℤ}

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (t : Sec F U) :
    Sec.res g (n • t) = n • Sec.res g t := map_nsmul ((F.obj.map g.op).hom) n t

theorem res_twGen {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ

theorem prim_map_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    (ζ.map g.appTop.hom).map k.appTop.hom = ζ.map (k ≫ g).appTop.hom := by
  apply Subtype.ext
  simp [Prim.map]
  rfl

theorem nsmul_eq_up {U : Scheme.{0}} (n : ℕ) (t : Sec (tw q i) U) : n • t = (ULift.up (n : ZMod q)) • t := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

theorem scalar_eq {U : Scheme.{0}} [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c d : ZMod q)
    (h : c.val • twGen i ζ = d.val • twGen i ζ) : c = d := by
  have h0 : (c - d).val • twGen i ζ = 0 := by
    rw [nsmul_eq_up, ZMod.natCast_zmod_val]
    rw [nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
    have : (ULift.up (c - d) : ULift.{1} (ZMod q)) = ULift.up c - ULift.up d := rfl
    rw [this, sub_smul, h, sub_self]
  have hd := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 U ζ _ h0
  have hv : (c - d).val = 0 := Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt _)
  exact sub_eq_zero.1 ((ZMod.val_eq_zero _).1 hv)

theorem q_nsmul {U : Scheme.{0}} (t : Sec (tw q i) U) (k : ℕ) : (q * k) • t = 0 := by
  rw [nsmul_eq_up]
  have : ((q * k : ℕ) : ZMod q) = 0 := by simp
  rw [this]
  exact zero_smul _ t

theorem sec_eq_nsmul (X : Scheme.{0}) [Nonempty X] (hX : ∀ s : Set X, IsClopen s → s = ∅ ∨ s = Set.univ)
    (ζ : Prim q Γ(X, ⊤)) (y : Sec (tw q i) X) : ∃ c : ℕ, y = c • twGen i ζ := by
  classical
  let P : ∀ V : Scheme.{0}, (V ⟶ X) → ℕ → Prop := fun V g c => Sec.res g y = c • twGen i (ζ.map g.appTop.hom)
  have hstab : ∀ c (V W : Scheme.{0}) (g : V ⟶ X) (k : W ⟶ V), P V g c → P W (k ≫ g) c := by
    intro c V W g k h
    simp only [P] at h ⊢
    rw [res_comp, h, res_nsmul, res_twGen, prim_map_comp]
  have hloc := (loc_iff_etale_affine_points X (fun V g => ∃ c, P V g c)
    (fun V W g k ⟨c, h⟩ => ⟨c, hstab c V W g k h⟩)).1 ((GlobalTheory.T.tateTwist_sections_locally_generated q i).2.1 X ζ y)
  let S : ZMod q → Set X := fun c =>
    {x | ∃ (V : Scheme.{0}) (g : V ⟶ X), IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g c.val}
  have hopen : ∀ c, IsOpen (S c) := by
    intro c
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨V, g, hV, hg, hx, hP⟩
    haveI := hg
    refine ⟨Set.range g, ?_, g.isOpenMap.isOpen_range, hx⟩
    rintro _ ⟨v, rfl⟩
    exact ⟨V, g, hV, hg, ⟨v, rfl⟩, hP⟩
  have hcov : ∀ x, ∃ c, x ∈ S c := by
    intro x
    obtain ⟨V, g, hV, hg, hx, n, hn⟩ := hloc x
    refine ⟨(n : ZMod q), V, g, hV, hg, hx, ?_⟩
    simp only [P] at hn ⊢
    rw [hn, nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val]
  have hdisj : ∀ c d x, x ∈ S c → x ∈ S d → c = d := by
    rintro c d x ⟨V, g, -, -, ⟨v, rfl⟩, hP⟩ ⟨V', g', -, -, ⟨v', hv'⟩, hP'⟩
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := g') v v' hv'.symm
    haveI : Nonempty ↥(Limits.pullback g g') := ⟨z⟩
    have h1 := hstab _ _ _ g (pullback.fst g g') hP
    have h2 := hstab _ _ _ g' (pullback.snd g g') hP'
    simp only [P] at h1 h2
    rw [pullback.condition] at h1
    exact scalar_eq _ c d (h1.symm.trans h2)
  obtain ⟨x0⟩ := ‹Nonempty X›
  obtain ⟨c0, hx0⟩ := hcov x0
  have hcompl : (S c0)ᶜ = ⋃ d ∈ ({c0}ᶜ : Set (ZMod q)), S d := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨d, hd⟩ := hcov x
      exact ⟨d, fun h => hx (h ▸ hd), hd⟩
    · rintro ⟨d, hd, hxd⟩ hx
      exact hd (hdisj d c0 x hxd hx)
  have hclopen : IsClopen (S c0) := by
    refine ⟨?_, hopen c0⟩
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_biUnion fun d _ => hopen d
  have huniv : S c0 = Set.univ := by
    rcases hX _ hclopen with h | h
    · rw [h] at hx0; exact absurd hx0 (Set.notMem_empty _)
    · exact h
  refine ⟨c0.val, (sec_ext_glue (ZMod q) (tw q i) X).1 _ _ ?_⟩
  refine (loc_iff_etale_affine_points X (fun _ g => Sec.res g y = Sec.res g (c0.val • twGen i ζ))
    (fun V W g k h => by rw [res_comp, res_comp, h])).2 ?_
  intro x
  obtain ⟨V, g, hV, hg, hx, hP⟩ : x ∈ S c0 := huniv ▸ Set.mem_univ x
  refine ⟨V, g, hV, hg, hx, ?_⟩
  rw [hP, res_nsmul, res_twGen]

end GlobalTheory.EtC.ConnectedGlobalSections

namespace GlobalTheory.EtC.ConnectedGlobalSections

theorem clopen_of_idem (B : Type) [CommRing B] (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (s : Set (Spec (CommRingCat.of B))) (hs : IsClopen s) : s = ∅ ∨ s = Set.univ := by
  obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.1 (show IsClopen (X := PrimeSpectrum B) s from hs)
  rcases hB e he with rfl | rfl
  · left
    change (s : Set (PrimeSpectrum B)) = ∅
    rw [h]; simp <;> rfl
  · right
    change (s : Set (PrimeSpectrum B)) = Set.univ
    rw [h]; simp <;> rfl

end GlobalTheory.EtC.ConnectedGlobalSections


open GlobalTheory.EtC.ConnectedGlobalSections in
theorem GlobalTheory.EtC.h_zero_pull_bijective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A'),
    IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → Nontrivial A' →
    (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) → (∀ e : A', IsIdempotentElem e → e = 0 ∨ e = 1) →
    ∀ i : ℤ, Function.Bijective (pull _ (spMap f) (tw q i) 0) := by
  intro q _ A A' _ _ f hq ⟨ζ0, hζ0⟩ hA' hidA hidA' i
  haveI : Nontrivial A := f.domain_nontrivial
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)
  let g : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom f)
  haveI : Nonempty (Spec (CommRingCat.of A)) := inferInstance
  haveI : Nonempty (Spec (CommRingCat.of A')) := inferInstance
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⟨ζ0, hq, hζ0⟩
  have hres : Function.Bijective (Sec.res (F := tw q i) g) := by
    constructor
    · change Function.Injective ((tw q i).obj.map g.op).hom
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨c, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A hidA) ζ y
      have h0 : c • twGen i (ζ.map g.appTop.hom) = 0 := by
        rw [← res_twGen, ← res_nsmul]; exact hy
      obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 _ _ _ h0
      exact q_nsmul _ k
    · intro y
      obtain ⟨c, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A' hidA') (ζ.map g.appTop.hom) y
      exact ⟨c • twGen i ζ, by rw [res_nsmul, res_twGen]⟩
  have key : ∀ s, pull _ (spMap f) (tw q i) 0 (e _ s) = e _ (Sec.res g s) := fun s => he g s
  have hfun : ⇑(pull _ (spMap f) (tw q i) 0) = e _ ∘ Sec.res g ∘ (e _).symm := by
    funext x
    obtain ⟨s, rfl⟩ := (e _).surjective x
    simp [key]
  rw [hfun]
  exact (e _).bijective.comp (hres.comp (e _).symm.bijective)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h_zero_pullback_twist_bijective : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A'), IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → Nontrivial A' → (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) → (∀ e : A', IsIdempotentElem e → e = 0 ∨ e = 1) → ∀ i : ℤ, Function.Bijective (pull _ (spMap f) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.h_zero_pull_bijective) | (exact GlobalTheory.EtC.h_zero_pull_bijective) | (intros; apply GlobalTheory.EtC.h_zero_pull_bijective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicRingClassLatticeOneEqOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicRingClassLatticeOneEqOrder
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.HatCap

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_integral :
    IsOpen {y : Af E | ∀ v : HeightOneSpectrum (𝓞 E), y v ∈ v.adicCompletionIntegers E} :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion E))

theorem mem_orderC_of_mem_hatO {c : Ideal (OF E)} (hc : c ≠ ⊥) {x : E} (hx : algebraMap E (Af E) x ∈ hatO c) :
    x ∈ orderC c := by
  obtain ⟨n, hnc, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  have hnE : algebraMap (OF E) E n ≠ 0 := by
    intro h
    apply hn0
    have h' : ((n : maximalRealSubfield E) : E) = 0 := h
    exact_mod_cast h'
  set m : E := algebraMap (OF E) E n with hm
  have hcont : Continuous fun z : Af E => (algebraMap E (Af E) x - z) * algebraMap E (Af E) m⁻¹ :=
    (continuous_const.sub continuous_id).mul continuous_const
  have hU := isOpen_integral.preimage hcont
  obtain ⟨_, hz, y, hy, rfl⟩ := mem_closure_iff.1 hx _ hU (by
    rw [Set.mem_preimage, sub_self, zero_mul]
    exact fun v => zero_mem _)
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = (x - y) * m⁻¹ := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_
    have h3 : (algebraMap E (Af E) ((x - y) * m⁻¹)) v ∈ v.adicCompletionIntegers E := by
      rw [map_mul, map_sub]; exact hz v
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)
  have hxy : x = y + algebraMap (𝓞 E) E (b * algebraMap (OF E) (𝓞 E) n) := by
    have : algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) n) = m := rfl
    rw [map_mul, hb, this, mul_assoc, inv_mul_cancel₀ hnE]; ring
  rw [hxy]
  refine add_mem hy (mem_orderC.2 ⟨0, _, Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem _ hnc), by simp⟩)

theorem lattice_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by
  intro E _ _ _ c hc
  ext x
  rw [mem_lattice, inv_one, Units.val_one, mul_one]
  exact ⟨mem_orderC_of_mem_hatO hc, algebraMap_mem_hatO⟩

end GlobalTheory.CMVal.HatCap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicRingClassLatticeOneEqOrderStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicRingClassLattice_one_eq_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → lattice c 1 = (orderC c : Set E) := by
  first | exact @GlobalTheory.CMVal.HatCap.lattice_one | exact GlobalTheory.CMVal.HatCap.lattice_one | (intros; apply GlobalTheory.CMVal.HatCap.lattice_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDifferentExponentDenominator
noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.DifferentElement

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

theorem mult_ratio (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (l : ℕ) (hl : l.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsPrime) (hlP : (l : 𝓞 E) ∈ P) :
    (multiplicity P (differentIdeal ℤ (𝓞 E)) : ℚ) / (multiplicity P (Ideal.span {(l : 𝓞 E)}) : ℚ) =
      ((NumberField.discr E).natAbs.factorization l : ℚ) / (Module.finrank ℚ E : ℚ) := by
  classical
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 ((Submodule.mem_bot _).1 hlP)
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hd : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E l
    ((NumberField.discr E).natAbs.factorization l) (ordCompl[l] (NumberField.discr E).natAbs) hl
    (Nat.not_dvd_ordCompl hl hd) (Nat.ordProj_mul_ordCompl_eq_self _ _).symm P hP hlP
  have hpos := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos E l hl hP hlP
  simp only [multiplicity_eq_count_normalizedFactors hirr, normalize_eq]
  have hn : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [div_eq_div_iff (by exact_mod_cast hpos.ne') hn]
  convert congrArg (fun t : ℕ => (t : ℚ)) h using 1 <;> push_cast <;> ring

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement


end GlobalTheory.DifferentElement
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointHol
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.TangentOrigin

namespace GlobalTheory.AnPer

theorem exists_point_hol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens E)
    (X : Scheme.{0}) (e : E → (Sp ℂ ⟶ X)) (U : X.Opens), IsAffineOpen U → IsHolTo (W : Set E) e → (∀ p ∈ W, ⊤ ≤ e p ⁻¹ᵁ U) →
    ∃ x : Sp (Hol W) ⟶ X, ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x = e p := by
  intro E _ _ _ W X e U hU he hW
  have ha : ∀ f : Γ(X, U), AnalyticOnNhd ℂ (fun p => valAt' (e p) U f) W := fun f p hp =>
    SCV.analyticAt_of_differentiableOn (he U f).2 ((he U f).1.mem_nhds ⟨hp, hW p hp⟩)
  have hv : ∀ (f : Γ(X, U)) (p : E) (hp : p ∈ W), (Hol.mk _ (ha f)).fn p = evalPt (e p) U (hW p hp) f :=
    fun f p hp => (Hol.fn_mk _ _ hp).trans (valAt'_eq_evalPt _ _ _ _)
  let ψ : Γ(X, U) →+* Hol W :=
    { toFun := fun f => Hol.mk _ (ha f)
      map_one' := Hol.ext_fn fun p hp => by rw [hv _ p hp, map_one, ← Hol.ev_apply p hp, map_one]
      map_mul' := fun f g => Hol.ext_fn fun p hp => by rw [Hol.fn_mul _ _ hp, hv _ p hp, hv _ p hp, hv _ p hp, map_mul]
      map_zero' := Hol.ext_fn fun p hp => by rw [hv _ p hp, map_zero, ← Hol.ev_apply p hp, map_zero]
      map_add' := fun f g => Hol.ext_fn fun p hp => by rw [Hol.fn_add _ _ hp, hv _ p hp, hv _ p hp, hv _ p hp, map_add (f := _)] }
  obtain ⟨x, hx, hxψ⟩ := exists_evalPt_eq hU ψ
  have h' : ∀ (p : E) (hp : p ∈ W), ⊤ ≤ (spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x) ⁻¹ᵁ U := fun p hp q _ => hx trivial
  refine ⟨x, hx, fun p hp => ext_evalPt hU (h' p hp) (hW p hp) (RingHom.ext fun f => ?_)⟩
  rw [evalPt_spMap_comp _ x U hx, hxψ]
  exact (Hol.ev_apply p hp _).trans (hv f p hp)

theorem point_hol_ext : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E)
    (X S : Scheme.{0}) (s : X ⟶ S) [IsSeparated s] (x x' : Sp (Hol W) ⟶ X), x ≫ s = x' ≫ s →
    (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x = spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x') → x = x' := by
  intro E _ _ W X S s _ x x' hs h
  have : _root_.IsReduced (Hol W) := isReduced_of_injective (holSub W).val Subtype.val_injective
  suffices IsDominant (equalizer.ι x x') from
    ext_of_isDominant_of_isSeparated s hs (equalizer.ι x x') (equalizer.condition _ _)
  refine ⟨?_⟩
  have hd : Dense (Set.range fun p : W => PrimeSpectrum.comap (Hol.ev p.1 p.2 : Hol W →+* ℂ) default) := by
    rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro f hf
    have : f = 0 := Hol.ext_fn fun p hp => by
      have h1 := (PrimeSpectrum.mem_vanishingIdeal _ _).1 hf _ ⟨⟨p, hp⟩, rfl⟩
      have h2 : Hol.ev p hp f ∈ (default : PrimeSpectrum ℂ).asIdeal := h1
      rw [Ideal.eq_bot_of_prime (default : PrimeSpectrum ℂ).asIdeal, Ideal.mem_bot] at h2
      rw [← Hol.ev_apply p hp, ← Hol.ev_apply p hp, h2, map_zero]
    rw [this]
    exact zero_mem _
  refine Dense.mono ?_ hd
  rintro _ ⟨p, rfl⟩
  refine ⟨equalizer.lift _ (h p.1 p.2) (default : PrimeSpectrum ℂ), ?_⟩
  exact congrArg (fun m : Sp ℂ ⟶ Sp (Hol W) => m (default : PrimeSpectrum ℂ)) (equalizer.lift_ι _ (h p.1 p.2))

end GlobalTheory.AnPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegersOfMemHatO
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.Conv

variable {E : Type} [Field E] [NumberField E]

theorem mem_integers_of_mem_hatO {c : Ideal (OF E)} {y : Af E} (hy : y ∈ hatO c) (v : HeightOneSpectrum (𝓞 E)) :
    y v ∈ v.adicCompletionIntegers E := by
  have hc : IsClosed {y : Af E | y v ∈ v.adicCompletionIntegers E} :=
    (Valued.isClosed_valuationSubring (v.adicCompletion E)).preimage (RestrictedProduct.continuous_eval v)
  refine closure_minimal (t := {y : Af E | y v ∈ v.adicCompletionIntegers E}) ?_ hc hy
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  have : algebraMap (OF E) E a + algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by
    rw [map_add (f := _)]; rfl
  rw [this]
  refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one _)

theorem exists_denominator (c : Ideal (OF E)) (y : (Af E)ˣ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ lattice c y, ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = n * x := by
  obtain ⟨n, hn, hy⟩ := PI.AdCpctDenWork.exists_nat_adele (y : Af E)
  refine ⟨n, hn, fun x hx => ?_⟩
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_
  have h1 := mul_mem (hy v) (mem_integers_of_mem_hatO hx v)
  have h2 : ((n : Af E) * (y : Af E)) * (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) = algebraMap E (Af E) (n * x) := by
    rw [map_mul, map_natCast]
    linear_combination ((n : Af E) * algebraMap E (Af E) x) * y.mul_inv
  have h3 : (algebraMap E (Af E) (n * x)) v ∈ v.adicCompletionIntegers E := by
    rw [← h2]; exact h1
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)


omit [NumberField E] in
theorem exists_generator : ∃ g : Ideal (𝓞 E) → 𝓞 E, ∀ b : 𝓞 E, ∃ u : (𝓞 E)ˣ, g (Ideal.span {b}) * u = b := by
  classical
  refine ⟨fun I => if h : ∃ b, Ideal.span {b} = I then h.choose else 0, fun b => ?_⟩
  have h : ∃ b', Ideal.span {b'} = Ideal.span {b} := ⟨b, rfl⟩
  simp only [dif_pos h]
  exact Ideal.span_singleton_eq_span_singleton.1 h.choose_spec

theorem summable_norm_rpow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ) (t : ℝ), c ≠ ⊥ → 1 < t → Summable fun q : modUnits (lattice c y) => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-t) := by
  intro E _ _ _ c y t _ ht
  obtain ⟨n, hn, hL⟩ := exists_denominator c y
  choose b hb using fun q : modUnits (lattice c y) => hL _ (out_mem_lattice q).1
  obtain ⟨g, hg⟩ := exists_generator (E := E)
  choose u hu using hg
  have hn' : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  let f : modUnits (lattice c y) → Units.torsion E × Ideal (𝓞 E) :=
    fun q => (IsCMField.unitsMulComplexConjInv E (u (b q)), Ideal.span {b q})
  have hf : Function.Injective f := by
    intro q q' h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have h3 : u (b q') * (u (b q))⁻¹ ∈ IsCMField.realUnits E := by
      rw [← IsCMField.unitsMulComplexConjInv_ker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    obtain ⟨v, hv⟩ := (IsCMField.mem_realUnits_iff E _).1 h3
    have h4 : b q' = algebraMap (OF E) (𝓞 E) v * b q := by
      rw [hv]
      have e1 := hu (b q)
      have e2 := hu (b q')
      rw [← h2] at e2
      rw [Units.val_mul]
      linear_combination (-1 : 𝓞 E) * e2 + ((u (b q') : 𝓞 E) * (↑(u (b q))⁻¹ : 𝓞 E)) * e1
        - (g (Ideal.span {b q}) * (u (b q') : 𝓞 E)) * (u (b q)).mul_inv
    have h5 : (q'.1.out : E) = algebraMap (OF E) E v * q.1.out := by
      apply mul_left_cancel₀ hn'
      rw [← hb q', h4, map_mul, hb q, mul_left_comm]; rfl
    apply Subtype.ext
    rw [← Quotient.out_eq q.1, ← Quotient.out_eq q'.1]
    exact Quotient.sound ⟨v, h5⟩
  have hI := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow E).2 t ht).1
  have hP : Summable fun p : Units.torsion E × Ideal (𝓞 E) => (Ideal.absNorm p.2 : ℝ) ^ (-t) := by
    refine (summable_prod_of_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _).2 ⟨fun _ => hI, ?_⟩
    exact Summable.of_finite
  have hN : (0 : ℝ) < |(Algebra.norm ℚ (n : E) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hn')
  refine ((hP.comp_injective hf).mul_left (|(Algebra.norm ℚ (n : E) : ℝ)| ^ t)).congr fun q => ?_
  have h1 : (Ideal.absNorm (Ideal.span {b q}) : ℝ) =
      |(Algebra.norm ℚ (n : E) : ℝ)| * |(Algebra.norm ℚ (q.1.out : E) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hb q, Nat.cast_natAbs, Int.cast_abs,
      ← Algebra.coe_norm_int]
    simp
  show _ * (Ideal.absNorm (Ideal.span {b q}) : ℝ) ^ (-t) = _
  rw [h1, Real.mul_rpow hN.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hN]
  simp

end GlobalTheory.CMVal.Conv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdNormSq
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.TermUnit

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]


omit [NumberField E] [Fintype I] in
theorem bijective_mk {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  constructor
  · intro i j hij
    have hj := InfinitePlace.mk_eq_iff.mp hij
    obtain ⟨k, -, hk⟩ := h (φ j)
    have e1 : i = k := hk i (hj.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm))
    have e2 : j = k := hk j (Or.inl rfl)
    rw [e1, e2]
  · intro w
    obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    show InfinitePlace.mk (φ i) = w
    rcases hi with hi | hi
    · rw [← hi, InfinitePlace.mk_embedding]
    · rw [← InfinitePlace.mk_conjugate_eq (φ i), ← hi, InfinitePlace.mk_embedding]

theorem prod_norm_sq [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (x : E) :
    ∏ i, ‖φ i x‖ ^ 2 = |(Algebra.norm ℚ x : ℝ)| := by
  calc ∏ i, ‖φ i x‖ ^ 2 = ∏ w : InfinitePlace E, w x ^ InfinitePlace.mult w :=
        Fintype.prod_bijective _ (bijective_mk h) _ _ fun i => by
          rw [IsTotallyComplex.mult_eq, InfinitePlace.apply]
    _ = _ := by rw [InfinitePlace.prod_eq_abs_norm]; push_cast; rfl

theorem prod_cpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (z : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ z = ((∏ j ∈ t, f j : ℝ) : ℂ) ^ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j)]

theorem term_unit [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (u : (OF E)ˣ) :
    term φ (2 * s) κ σ (algebraMap (OF E) E u) = 1 := by
  set x := algebraMap (OF E) E (u : OF E) with hxdef
  have hxmem : x ∈ maximalRealSubfield E := by
    rw [hxdef, IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
    exact (algebraMap (OF E) (maximalRealSubfield E) u).2
  have hreal : ∀ i, starRingEnd ℂ (φ i x) = φ i x := fun i => by
    rw [starRingEnd_apply]
    exact (mem_maximalRealSubfield_iff x).mp hxmem (φ i)
  have hx0 : x ≠ 0 := (u.isUnit.map (algebraMap (OF E) E)).ne_zero
  have hN : |(Algebra.norm ℚ x : ℝ)| = 1 := by
    have hv := NumberField.isUnit_iff_norm.mp (u.isUnit.map (algebraMap (OF E) (𝓞 E)))
    have hc : ((algebraMap (OF E) (𝓞 E) u : 𝓞 E) : E) = x :=
      (IsScalarTower.algebraMap_apply (OF E) (𝓞 E) E u).symm
    rw [RingOfIntegers.coe_norm, hc] at hv
    exact_mod_cast hv
  have hprod : ∏ i, ‖φ i x‖ = 1 := by
    have hsq : (∏ i, ‖φ i x‖) ^ 2 = 1 := by rw [← Finset.prod_pow, prod_norm_sq h x, hN]
    exact (pow_eq_one_iff_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) two_ne_zero).mp hsq
  have hfac : ∀ i, (φ i x)⁻¹ ^ (2 * s + κ i) * starRingEnd ℂ (φ i x) ^ κ i * ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * σ) =
      ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * ((s : ℂ) + σ)) := fun i => by
    have hr : φ i x ≠ 0 := (map_ne_zero (φ i)).mpr hx0
    have ha : ((‖φ i x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hr)
    have hsq : ((‖φ i x‖ : ℝ) : ℂ) ^ 2 = φ i x ^ 2 := by
      have hm := Complex.mul_conj (φ i x)
      rw [hreal, Complex.normSq_eq_norm_sq] at hm
      rw [sq (φ i x), hm]
      push_cast
      ring
    rw [show -2 * ((s : ℂ) + σ) = -((2 * s : ℕ) : ℂ) + -2 * σ by push_cast; ring,
      Complex.cpow_add _ _ ha, Complex.cpow_neg, Complex.cpow_natCast, hreal]
    congr 1
    rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hr, one_pow, mul_one, inv_pow, pow_mul, pow_mul, hsq]
  simp only [term]
  rw [Finset.prod_congr rfl fun i _ => hfac i, prod_cpow _ _ (fun i => norm_nonneg _), hprod]
  simp

theorem norm_term [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) {x : E} (hx : x ≠ 0) :
    ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re)) := by
  have hpos : ∀ i, 0 < ‖φ i x‖ := fun i => norm_pos_iff.mpr ((map_ne_zero (φ i)).mpr hx)
  rw [← prod_norm_sq h x, ← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  simp only [term, norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha := hpos i
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos ha, inv_pow, ← Real.rpow_natCast _ (2 * s + κ i),
    ← Real.rpow_natCast _ (κ i), ← Real.rpow_neg ha.le, ← Real.rpow_add ha, ← Real.rpow_add ha,
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul ha.le]
  congr 1
  simp
  ring

private theorem term_mul' (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (σ : ℂ) (y x : E) :
    term φ k κ σ (y * x) = term φ k κ σ y * term φ k κ σ x := by
  simp only [term, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_mul, mul_inv, norm_mul, mul_pow]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  ring

theorem term_unit_and_norm (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (x : E) :
    (∀ u : (OF E)ˣ, term φ (2 * s) κ σ (algebraMap (OF E) E u * x) = term φ (2 * s) κ σ x) ∧
      (x ≠ 0 → ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re))) := by
  refine ⟨fun u => ?_, fun hx => norm_term h s κ σ hx⟩
  rw [term_mul', term_unit h s κ σ u, one_mul]

end GlobalTheory.CMVal.TermUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivOfLocallyConstantBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivOfLocallyConstantBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem bij_of_subsingleton_pair {A B : Type*} [Subsingleton A] [Subsingleton B] (_b₀ : B) (a₀ : A) (φ : A → B) :
    Function.Bijective φ :=
  ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨a₀, Subsingleton.elim _ _⟩⟩

theorem eqv_of_gen_lc : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g →
    ∀ (U V : Scheme.{0}) (s : U ⟶ S) (f : V ⟶ U), AcycF R (sch.obj U) F → AcycF R (sch.obj V) F →
    Function.Bijective (fun φ : LocallyConstant U R ↦ φ.comap f.base.hom) → Eqv R (sch.map f) F := by
  intro R _ F S g hg U V s f hU hV hb n
  obtain ⟨hneg, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F
  obtain ⟨eL, -, hE⟩ := GlobalTheory.T.freeRankOne_etaleSheaf_equiv_locallyConstant R F S g hg
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := hneg (sch.obj U) n hn
    have := hneg (sch.obj V) n hn
    exact bij_of_subsingleton_pair 0 0 _
  · have key : (fun x ↦ pull R (sch.map f) F 0 x) =
        (fun x ↦ e V (eL V (f ≫ s) (LocallyConstant.comap f.base.hom ((eL U s).symm ((e U).symm x))))) := by
      funext x
      conv_lhs => rw [← (e U).apply_symm_apply x, ← (eL U s).apply_symm_apply ((e U).symm x)]
      rw [he, hE]
    change Function.Bijective (fun x ↦ pull R (sch.map f) F 0 x)
    rw [key]
    exact (e V).bijective.comp ((eL V (f ≫ s)).bijective.comp
      (hb.comp ((eL U s).symm.bijective.comp (e U).symm.bijective)))
  · have := hU n hn
    have := hV n hn
    exact bij_of_subsingleton_pair 0 0 _

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivOfLocallyConstantBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g → ∀ (U U' : Scheme.{0}) (s : U ⟶ S) (f : U' ⟶ U), AcycF R (sch.obj U) F → AcycF R (sch.obj U') F → Function.Bijective (fun φ : LocallyConstant U R => φ.comap f.base.hom) → Eqv R (sch.map f) F := by
  first | exact @GlobalTheory.EtC.eqv_of_gen_lc | exact GlobalTheory.EtC.eqv_of_gen_lc | (intros; apply GlobalTheory.EtC.eqv_of_gen_lc <;> assumption)
end
end
