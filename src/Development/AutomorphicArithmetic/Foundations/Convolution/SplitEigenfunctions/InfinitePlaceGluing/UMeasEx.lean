module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NormChar
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SameSatTwist
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDual

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UMeasEx
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private lemma eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma mem_UU_iff (t : IdeleGroup ℚ) :
    t ∈ UU ↔ IdeleGroup.toInfinite ℚ t = 1 ∧ IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ := by
  have hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    intro v
    rw [← map_mul]
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))
    have h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
    rw [h', map_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Units.ext h1, (mem_finiteIntegralUnits ℚ).2 fun v => ?_⟩
    have hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := h2 v
    have hi := hinv v
    rw [hv, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  · rintro ⟨h1, h2⟩
    refine ⟨congrArg Units.val h1, fun v => ?_⟩
    obtain ⟨ha, hb⟩ := (mem_finiteIntegralUnits ℚ).1 h2 v
    exact eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) (by rw [mul_comm]; exact hinv v)

private lemma measurableSet_UU : MeasurableSet (UU : Set (IdeleGroup ℚ)) := by
  have h : (UU : Set (IdeleGroup ℚ)) = {t | IdeleGroup.toInfinite ℚ t = 1} ∩
      IdeleGroup.toFinite ℚ ⁻¹' (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    ext t
    exact mem_UU_iff t
  rw [h]
  exact (isClosed_eq (IdeleGroup.continuous_toInfinite ℚ) continuous_const).measurableSet.inter
    ((isOpen_finiteIntegralUnits ℚ).preimage (IdeleGroup.continuous_toFinite ℚ)).measurableSet

private noncomputable def ef (x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : IdeleGroup ℚ := (IdeleGroup.prodEquiv ℚ).symm (1, x)

private lemma measurable_ef : Measurable ef :=
  ((map_continuous (IdeleGroup.prodEquiv ℚ).symm).comp (continuous_const.prodMk continuous_id)).measurable

private lemma toInfinite_ef (x) : IdeleGroup.toInfinite ℚ (ef x) = 1 :=
  congrArg Prod.fst ((IdeleGroup.prodEquiv ℚ).apply_symm_apply (1, x))

private lemma toFinite_ef (x) : IdeleGroup.toFinite ℚ (ef x) = x :=
  congrArg Prod.snd ((IdeleGroup.prodEquiv ℚ).apply_symm_apply (1, x))

private lemma mul_ef {t : IdeleGroup ℚ} (h : IdeleGroup.toInfinite ℚ t = 1) (x) :
    t * ef x = ef (IdeleGroup.toFinite ℚ t * x) := by
  refine (IdeleGroup.prodEquiv ℚ).injective ?_
  rw [map_mul]
  refine Prod.ext ?_ ?_
  · change IdeleGroup.toInfinite ℚ t * IdeleGroup.toInfinite ℚ (ef x) = IdeleGroup.toInfinite ℚ (ef _)
    rw [h, toInfinite_ef, toInfinite_ef, one_mul]
  · change IdeleGroup.toFinite ℚ t * IdeleGroup.toFinite ℚ (ef x) = IdeleGroup.toFinite ℚ (ef _)
    rw [toFinite_ef, toFinite_ef]

theorem uMeasEx_of :
    UMeasEx := by
  have hU : MeasurableSet (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
    (isOpen_finiteIntegralUnits ℚ).measurableSet
  refine ⟨⟨((finiteIdeleMeasure ℚ).restrict (finiteIntegralUnits ℚ)).map ef, ⟨?_⟩, ?_, ?_⟩⟩
  · rw [Measure.map_apply measurable_ef MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, finiteIdeleMeasure_finiteIntegralUnits]
  · rw [Measure.map_apply measurable_ef measurableSet_UU.compl,
      Measure.restrict_apply (measurable_ef measurableSet_UU.compl)]
    convert measure_empty (μ := finiteIdeleMeasure ℚ)
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe,
      Set.mem_empty_iff_false, iff_false, not_and, not_not]
    intro hx hxU
    exact hx ((mem_UU_iff _).2 ⟨toInfinite_ef x, by rwa [toFinite_ef]⟩)
  · intro t ht
    obtain ⟨h1, h2⟩ := (mem_UU_iff t).1 ht
    have hg := (measurePreserving_mul_left (finiteIdeleMeasure ℚ) (IdeleGroup.toFinite ℚ t)).restrict_preimage hU
    have hpre : (fun x => IdeleGroup.toFinite ℚ t * x) ⁻¹'
        (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) = finiteIntegralUnits ℚ := by
      ext x
      exact (finiteIntegralUnits ℚ).mul_mem_cancel_left h2
    rw [hpre] at hg
    have hf : Measurable fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ) :=
      (continuous_const.mul continuous_id).measurable
    rw [Measure.map_map hf measurable_ef]
    have hc : (fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ)) ∘ ef = ef ∘ fun x => IdeleGroup.toFinite ℚ t * x := by
      funext x
      exact mul_ef h1 x
    rw [hc, ← Measure.map_map measurable_ef hg.measurable, hg.map_eq]

end UpperTheory.ConvolutionTheory.RankTwoDescent
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ExistsNat
open NumberField IsDedekindDomain
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open UpperTheory.ConvolutionTheory.RankTwoDescent
open HeckeValGen GlobalTheory.HeckeSplit

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.ChExPf

private theorem nat_le_one (v : H.P ℚ) (c : ℕ) : Valued.v (c : H.Kv v) ≤ 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
    push_cast
    exact Valuation.map_add_le _ ih (by simp)

private theorem dvd_le (v : H.P ℚ) {a b : ℕ} (h : a ∣ b) : Valued.v (b : H.Kv v) ≤ Valued.v (a : H.Kv v) := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  rw [map_mul]
  exact mul_le_of_le_one_right' (nat_le_one v c)

private theorem exists_nat {K : Type} [Field K] [NumberField K] (v : H.P K) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Valued.v (m : H.Kv v) ≤ WithZero.exp (-(n : ℤ)) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  refine ⟨Ideal.absNorm v.asIdeal ^ n, pow_pos (Nat.pos_of_ne_zero h0) n, ?_⟩
  have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n ∈ v.asIdeal ^ n :=
    Ideal.pow_mem_pow (Ideal.absNorm_mem _) n
  have h1 := (v.intValuation_le_pow_iff_mem _ n).2 hm
  have h3 : Valued.v ((algebraMap (𝓞 K) K (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n) : K) : v.adicCompletion K) ≤
      WithZero.exp (-(n : ℤ)) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    exact h1
  have h2 : ((Ideal.absNorm v.asIdeal ^ n : ℕ) : H.Kv v) =
      ((algebraMap (𝓞 K) K (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n) : K) : v.adicCompletion K) := by
    change _ = algebraMap K (v.adicCompletion K) _
    simp
  rw [h2]
  exact h3

end UpperTheory.ConvolutionTheory.RankTwoDescent.ChExPf

open UpperTheory.ConvolutionTheory.RankTwoDescent.ChExPf in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.chEx_of :
    ChEx := by
  intro χ
  classical
  set S := (GlobalTheory.HCharRam.ram_finite ℚ χ).toFinset with hSdef
  choose n hn using fun v => GlobalTheory.HeckeSplit.exists_level χ.1 χ.2.1 v
  choose M hM0 hM using fun v : H.P ℚ => exists_nat v (n v)
  refine ⟨∏ v ∈ S, M v, Finset.prod_pos fun v _ => hM0 v, fun N hN t ht hD => ?_⟩
  have key := GlobalTheory.HeckeSplit.char_eq_prod_local χ.1 χ.2.1 t S (fun v hv => by
    have hu : χ.UnrAt v := by
      by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc)
    exact hu _ (ht.2 v))
  have hinf : infPart ℚ t = 1 := Units.ext ht.1
  rw [key, hinf, map_one, map_one, one_mul]
  refine Finset.prod_eq_one fun v hv => hn v _ ?_
  have h1 : Valued.v (H.cp v ((t : A ℚ) - 1)) ≤ Valued.v (N : H.Kv v) := (hD v)
  rw [map_sub, map_one] at h1
  exact h1.trans ((dvd_le v ((Finset.dvd_prod_of_mem M hv).trans hN)).trans (hM v))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.Landau
open UpperTheory.ConvolutionTheory.RankTwoDescent

open scoped ComplexOrder

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.landau_of :
    Landau := by
  intro b hb0 hb1 hbs hent
  obtain ⟨F, hF, hFb⟩ := hent
  by_contra hinf
  have hinf' : ({n | 1 ≤ b n} \ {0, 1} : Set ℕ).Infinite :=
    Set.Infinite.diff hinf (Set.toFinite _)
  obtain ⟨m, hm⟩ := exists_nat_gt (F 0).re
  obtain ⟨S, hSsub, hScard⟩ := hinf'.exists_subset_card_eq m
  have hS0 : ∀ n ∈ S, n ≠ 0 := fun n hn h => (hSsub hn).2 (by simp [h])
  have hS1 : 1 ∉ S := fun hn => (hSsub hn).2 (by simp)
  have hS2 : ∀ n ∈ S, 1 ≤ b n := fun n hn => (hSsub hn).1
  let a : ℕ → ℂ := fun n => if n ∈ S then 0 else b n
  let G : ℂ → ℂ := fun s => F s - ∑ n ∈ S, b n / (n : ℂ) ^ s
  have hG : Differentiable ℂ G := by
    refine hF.sub (Differentiable.fun_sum fun n hn => ?_)
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hS0 n hn)
    exact (differentiable_const _).div (differentiable_id.const_cpow (Or.inl hn0))
      fun s => by simp [Complex.cpow_eq_zero_iff, hn0]
  have hsum : ∀ s : ℂ, 4 < s.re →
      HasSum (LSeries.term a s) (LSeries b s - ∑ n ∈ S, b n / (n : ℂ) ^ s) := by
    intro s hs
    have h1 : HasSum (LSeries.term b s) (LSeries b s) := (hbs s hs).LSeriesHasSum
    have h2 : HasSum (fun n => if n ∈ S then LSeries.term b s n else 0)
        (∑ n ∈ S, b n / (n : ℂ) ^ s) := by
      have h3 : HasSum (fun n => if n ∈ S then LSeries.term b s n else 0)
          (∑ n ∈ S, if n ∈ S then LSeries.term b s n else 0) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
      have h5 : (∑ n ∈ S, if n ∈ S then LSeries.term b s n else 0) =
          ∑ n ∈ S, b n / (n : ℂ) ^ s :=
        Finset.sum_congr rfl fun n hn => by
          simp [hn, LSeries.term_of_ne_zero (hS0 n hn)]
      rwa [h5] at h3
    have h6 : LSeries.term a s =
        fun n => LSeries.term b s n - if n ∈ S then LSeries.term b s n else 0 := by
      funext n
      by_cases hn : n ∈ S
      · simp [a, hn, LSeries.term_def]
      · simp [a, hn, LSeries.term_def]
    rw [h6]
    exact h1.sub h2
  have ha0 : 0 ≤ a := by
    intro n
    by_cases hn : n ∈ S
    · simp [a, hn]
    · simpa [a, hn] using hb0 n
  have ha1 : 0 < a 1 := by
    simp [a, hS1, hb1]
  have habs : LSeries.abscissaOfAbsConv a ≤ (4 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      (hsum y (by simpa using hy)).summable
  have hEq : {s : ℂ | (4 : ℝ) < s.re}.EqOn G (LSeries a) := by
    intro s hs
    have hs' : (4 : ℝ) < s.re := hs
    have h4 : (4 : ℝ) < s.re := hs'
    have : LSeries a s = LSeries b s - ∑ n ∈ S, b n / (n : ℂ) ^ s :=
      LSeriesHasSum.LSeries_eq (hsum s h4)
    simp only [G, hFb s h4]
    exact this.symm
  have hpos := LSeries.positive_of_differentiable_of_eqOn ha0 ha1 hG habs hEq 0
  have hG0 : G ((0 : ℝ) : ℂ) = F 0 - ∑ n ∈ S, b n := by
    simp [G]
  rw [hG0] at hpos
  have hre : (∑ n ∈ S, b n).re < (F 0).re := by
    have := (Complex.lt_def.mp hpos).1
    simpa using this
  have hcard : (m : ℝ) ≤ (∑ n ∈ S, b n).re := by
    rw [Complex.re_sum, ← hScard]
    have : ∀ n ∈ S, (1 : ℝ) ≤ (b n).re := fun n hn => by
      simpa using (Complex.le_def.mp (hS2 n hn)).1
    simpa using Finset.card_nsmul_le_sum S _ 1 this
  linarith
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.CenExOf
section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.CentralCharGaloisInvariantOfConjInv
open NumberField IsDedekindDomain GroundTheory.Global Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.LocalScalarValues

open GroundTheory.Global.AdeleBaseChange GlobalTheory.Mem.LocTriv

variable {E : Type} [Field E] [NumberField E]

private theorem loc_eq_val (ψ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (hu : ψ.UnrAt w)
    (y : (w.adicCompletion E)ˣ) (hy : IsUnifAt w y) : ψ.loc w y = ψ.val w := by
  have h2 := unif_spec w
  have h3 := hu (y * (atFin w (unif w))⁻¹) (by
    unfold IsUnitAt
    unfold IsUnifAt at hy h2
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3

private theorem smul_local (c : E ≃ₐ[ℚ] E) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    ∃ x' : ((c • w).adicCompletion E)ˣ, Valued.v (x' : (c • w).adicCompletion E) = Valued.v (x : w.adicCompletion E) ∧
      c • (Neutral.B1.localIdele E w x : IdeleGroup E) = Neutral.B1.localIdele E (c • w) x' := by
  have hs : ∀ u, ((c • (Neutral.B1.localIdele E w x : IdeleGroup E) : IdeleGroup E) : AdeleRing (𝓞 E) E).2 u =
      finiteCompletionMap (c : E ≃+* E) u (ev (comapPrime (c : E ≃+* E) u) (Neutral.B1.localIdele E w x : AdeleRing (𝓞 E) E)) :=
    fun u => smul_snd c _ u
  have ev_self : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ),
      ev v (Neutral.B1.localIdele E v y : AdeleRing (𝓞 E) E) = y :=
    fun v y => Neutral.B1.localIdele_snd_self E v y
  have ev_ne : ∀ {v u : HeightOneSpectrum (𝓞 E)}, u ≠ v → ∀ (y : (v.adicCompletion E)ˣ),
      ev u (Neutral.B1.localIdele E v y : AdeleRing (𝓞 E) E) = 1 :=
    fun hu y => (Neutral.B1.localIdele_isSupportedAt E _ y).2 _ hu
  refine ⟨Units.map (ev (c • w)) (c • (Neutral.B1.localIdele E w x : IdeleGroup E)), ?_,
    Units.ext (Prod.ext ?_ (Subtype.ext (funext fun u => ?_)))⟩
  · change Valued.v (((c • (Neutral.B1.localIdele E w x : IdeleGroup E) : IdeleGroup E) : AdeleRing (𝓞 E) E).2 (c • w)) = _
    rw [hs, valued_finiteCompletionMap, comapPrime_eq_inv_smul, inv_smul_smul, ev_self]
  · funext u
    change (c • ((Neutral.B1.localIdele E w x : IdeleGroup E) : AdeleRing (𝓞 E) E)).1 u = 1
    rw [smul_fst]
    exact map_one _
  · change ((c • (Neutral.B1.localIdele E w x : IdeleGroup E) : IdeleGroup E) : AdeleRing (𝓞 E) E).2 u =
      ev u (Neutral.B1.localIdele E (c • w) _ : AdeleRing (𝓞 E) E)
    by_cases hu : u = c • w
    · subst hu
      rw [ev_self]
      rfl
    · have h1 : comapPrime (c : E ≃+* E) u ≠ w := by
        rw [comapPrime_eq_inv_smul]
        rintro rfl
        exact hu (smul_inv_smul c u).symm
      rw [ev_ne hu, hs, ev_ne h1]
      exact map_one _

end UpperTheory.LocalScalarValues

open UpperTheory.LocalScalarValues in
theorem UpperTheory.centralChar_galois_invariant_of_conjInv :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar E), P.HasCentChar ω → ConjInv P → ∀ (c : E ≃ₐ[ℚ] E) (z : IdeleGroup E), ω.1 (c • z) = ω.1 z := by
  intro E _ _ _ P ω hω hc c z
  let ψ : Neutral.B1.Ideles E →* ℂˣ :=
    { toFun := fun a => ω.1 (c • (a : IdeleGroup E)) * (ω.1 a)⁻¹
      map_one' := by
        rw [smul_one, map_one, inv_one, mul_one]
      map_mul' := fun a b => by
        rw [smul_mul', map_mul, map_mul, mul_inv, mul_mul_mul_comm] }
  have hψ : ∀ a, ψ a = ω.1 (c • (a : IdeleGroup E)) * (ω.1 a)⁻¹ := fun _ => rfl
  have hcont : Continuous ψ :=
    (ω.2.1.comp (continuous_const_smul c)).mul ω.2.1.inv
  have hd : ∀ k, ψ (Neutral.B1.diagUnits E k) = 1 := fun k => by
    have e : ∀ k : Eˣ, (Neutral.B1.diagUnits E k : IdeleGroup E) = IdeleGroup.diagonal E k := fun _ => Units.ext rfl
    have e2 : ∀ k : Eˣ, ω.1 (IdeleGroup.diagonal E k) = 1 := fun k => (congrArg ω.1 (e k)).symm.trans (ω.2.2 k)
    rw [hψ, e, smul_diagonal, e2, e2, inv_one, mul_one]
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ω.UnrAt w ∧ ω.UnrAt (c • w) ∧
      ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) →
        ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat w' B := by
    have h1 := Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ω)
    have h2 := (MulAction.injective c).tendsto_cofinite.eventually h1
    filter_upwards [h1, h2, hc] with w a b d using ⟨a, b, d⟩
  have h1 : ψ = 1 := GlobalTheory.FrobDense.eq_one_of_away ψ hcont hd (Filter.eventually_cofinite.1 hev).toFinset
    fun w hw y => by
      have hw' := not_not.1 (fun h => hw ((Set.Finite.mem_toFinset _).2 h))
      obtain ⟨hu, hu', hs⟩ := hw'
      refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.comp (Neutral.B1.localIdele E w)) (fun x hx => ?_) y
      obtain ⟨x', hv, he⟩ := smul_local c w x
      obtain ⟨B, hB, hB'⟩ := hs (c • w) (HeightOneSpectrum.ext (Ideal.under_smul (𝓞 ℚ) w.asIdeal c))
      have e1 : ω.1 (Neutral.B1.localIdele E w x) = B.prod :=
        (loc_eq_val ω w hu x hx).trans (PositivityTheory.jumpWindows.PSmo.val_eq_prod hω hB)
      have e2 : ω.1 (Neutral.B1.localIdele E (c • w) x') = B.prod :=
        (loc_eq_val ω (c • w) hu' x' (hv.trans hx)).trans (PositivityTheory.jumpWindows.PSmo.val_eq_prod hω hB')
      rw [MonoidHom.comp_apply, hψ, he, e1, e2, mul_inv_cancel]
  have h2 : ψ z = 1 := by rw [h1]; rfl
  rw [hψ, mul_inv_eq_one] at h2
  exact h2
end

open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.cenEx_of :
    CenEx := by
  intro E _ _ _ hE P hP
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar (GlobalTheory.CuspRep.CG.mk P)
  obtain ⟨χ, hχ⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.A.normChar_of_inv hE ω (UpperTheory.centralChar_galois_invariant_of_conjInv E P ω hω hP)
  refine ⟨χ, fun f hf z g => ?_⟩
  have h1 := (GlobalTheory.CuspRep.CuspSub.hasCentral_iff (π := P) (ω := ω)).2 hω z f hf
  have h2 := congrFun (congrArg Subtype.val h1) g
  rw [GlobalTheory.CuspRep.scalar_comm, ← hχ z]
  exact h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.PhiMem
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private abbrev Fa : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

private theorem dv_iff {N : ℕ} (hN : 0 < N) (z : Fa) :
    (∀ v : H.P ℚ, Valued.v (z v) ≤ Valued.v ((N : H.Kv v))) ↔
      ∃ u : Fa, (∀ v, u v ∈ v.adicCompletionIntegers ℚ) ∧ z = N • u := by
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set w : Fa := algebraMap ℚ Fa (N : ℚ)⁻¹ with hw
  have hwN : w * (N : Fa) = 1 := by
    rw [hw, ← map_natCast (algebraMap ℚ Fa), ← map_mul, inv_mul_cancel₀ hNq, map_one]
  constructor
  · intro h
    refine ⟨w * z, fun v => ?_, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have e1 : (w * z) v = w v * z v := rfl
      have e2 : w v * (N : H.Kv v) = 1 := by
        have := congrArg (pLoc ℚ v) hwN
        rwa [map_mul, map_natCast, map_one] at this
      rw [e1, map_mul]
      calc Valued.v (w v) * Valued.v (z v) ≤ Valued.v (w v) * Valued.v (N : H.Kv v) := mul_le_mul' le_rfl (h v)
        _ = 1 := by rw [← map_mul, e2, map_one]
    · rw [nsmul_eq_mul, ← mul_assoc, mul_comm (N : Fa), hwN, one_mul]
  · rintro ⟨u, hu, rfl⟩ v
    have e1 : (N • u) v = (N : H.Kv v) * u v := by
      exact (map_nsmul (pLoc ℚ v) N u).trans (nsmul_eq_mul _ _)
    rw [e1, map_mul]
    have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hu v)
    exact mul_le_of_le_one_right' this

private abbrev Mx : Type := mixedEmbedding.mixedSpace ℚ

private instance : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
  ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (Subsingleton.elim w.1 Rat.infinitePlace ▸ Rat.isReal_infinitePlace)⟩

private def mE : Mx ≃L[ℝ] ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun y => y.1 ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun t => (fun _ => t, 0)
      left_inv := fun y => by
        refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
        exact congrArg y.1 (Subsingleton.elim (α := {w : InfinitePlace ℚ // w.IsReal}) _ _)
      right_inv := fun _ => rfl }

private def eE : (Fin 2 → Mx) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.piCongrRight fun _ => mE).trans (EuclideanSpace.equiv (Fin 2) ℝ).symm

private theorem eE_apply (x : Fin 2 → A ℚ) (i : Fin 2) : eE (infPartPi x) i = re (x i) := rfl

private theorem temp (p : MvPolynomial (Fin 2) ℂ) :
    (fun y : Fin 2 → Mx => MvPolynomial.eval (fun i => ((eE y i : ℝ) : ℂ)) p).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    exact (Complex.ofRealCLM.comp ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
      eE.toContinuousLinearMap)).hasTemperateGrowth

private def phiS (p : MvPolynomial (Fin 2) ℂ) : SchwartzMap (Fin 2 → Mx) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun y : Fin 2 → Mx => MvPolynomial.eval (fun i => ((eE y i : ℝ) : ℂ)) p)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eE (gaussianSchwartz (EuclideanSpace ℝ (Fin 2))))

private theorem cond_iff {N : ℕ} (hN : 0 < N) (x : Fin 2 → A ℚ) :
    (∀ v, Dv N v (x 0) ∧ Dv N v (x 1 - 1)) ↔
      ∀ i, ∃ u : Fa, (∀ v, u v ∈ v.adicCompletionIntegers ℚ) ∧
        finPartPi x i = algebraMap ℚ Fa ((![0, 1] : Fin 2 → ℚ) i) + N • u := by
  have h0 := dv_iff hN (x 0).2
  have h1 := dv_iff hN ((x 1 - 1).2)
  have e1 : ∀ u : Fa, (x 1 - 1).2 = N • u ↔ (x 1).2 = 1 + N • u := fun u => by
    change (x 1).2 - 1 = N • u ↔ _
    rw [sub_eq_iff_eq_add']
  constructor
  · intro h i
    fin_cases i
    · obtain ⟨u, hu, e⟩ := h0.1 fun v => (h v).1
      exact ⟨u, hu, by simpa [finPartPi] using e⟩
    · obtain ⟨u, hu, e⟩ := h1.1 fun v => (h v).2
      exact ⟨u, hu, by simpa [finPartPi] using (e1 u).1 e⟩
  · intro h v
    refine ⟨h0.2 ?_ v, h1.2 ?_ v⟩
    · obtain ⟨u, hu, e⟩ := h 0
      exact ⟨u, hu, by simpa [finPartPi] using e⟩
    · obtain ⟨u, hu, e⟩ := h 1
      exact ⟨u, hu, (e1 u).2 (by simpa [finPartPi] using e)⟩

private theorem phiS_apply (p : MvPolynomial (Fin 2) ℂ) (x : Fin 2 → A ℚ) :
    phiS p (infPartPi x) = MvPolynomial.eval (fun i => (re (x i) : ℂ)) p *
      Complex.exp (-(Real.pi : ℂ) * ((re (x 0) ^ 2 + re (x 1) ^ 2 : ℝ) : ℂ)) := by
  rw [phiS, SchwartzMap.smulLeftCLM_apply_apply (temp p), SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, gaussianSchwartz_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, smul_eq_mul]
  simp only [eE_apply]
  push_cast
  rfl

theorem phiMem_of :
    PhiMem := by
  intro N p hN
  have e : PhiN N p = schwartzBruhatTensorPi (phiS p) (GlobalTheory.CompanionTheory.ThetaUniq.cosetInd ℚ N ![0, 1]) := by
    funext x
    rw [PhiN, schwartzBruhatTensorPi, phiS_apply, GlobalTheory.CompanionTheory.ThetaUniq.cosetInd, Set.indicator_apply]
    split_ifs with h h' h''
    · rw [Pi.one_apply, mul_one]
    · exact absurd ((cond_iff hN x).1 h) h'
    · exact absurd ((cond_iff hN x).2 h'') h
    · rw [mul_zero]
  rw [e]
  exact schwartzBruhatTensorPi_mem _
    ((mem_finiteSchwartzBruhatPi ℚ).2 (GlobalTheory.CompanionTheory.ThetaUniq.cosetInd_mem_SB ℚ (Fin 2) N hN _))

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
end
