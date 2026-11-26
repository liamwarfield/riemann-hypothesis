module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationComplexConjOfNotSplit
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.SplitOfSquare

private theorem valued_v_algebraMap_adicCompletion_foundation {F : Type} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x :=
  u.valuedAdicCompletion_eq_valuation' x

theorem exists_valuation_lt_one {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) (a : F) (ha : a ≠ 0)
    (h : IsSquare (algebraMap F (u.adicCompletion F) a)) : ∃ c : F, u.valuation F (1 / 4 - c ^ 2 * a) < 1 := by
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply ha
    simpa using hs
  obtain ⟨π, hπ⟩ := u.valuation_exists_uniformizer F
  have hπ1 : u.valuation F π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set h2 : u.adicCompletion F := algebraMap F (u.adicCompletion F) 2⁻¹ with hh2
  set p : u.adicCompletion F := algebraMap F (u.adicCompletion F) π with hp
  have hp0 : p ≠ 0 := (map_ne_zero _).mpr hπ0
  have hvp : Valued.v p < 1 := by rw [hp, valued_v_algebraMap_adicCompletion_foundation]; exact hπ1
  have hI := Valued.isOpen_integer (u.adicCompletion F)
  have hcont : Continuous (fun y : u.adicCompletion F => (y * s - h2) * p⁻¹) :=
    ((continuous_id.mul continuous_const).sub continuous_const).mul continuous_const
  obtain ⟨c, hc⟩ := (u.denseRange_algebraMap F).exists_mem_open (hI.preimage hcont) ⟨h2 * s⁻¹, by
    simp only [Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff]
    rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one, sub_self, zero_mul, map_zero]
    exact zero_le⟩
  refine ⟨c, ?_⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, Valuation.mem_integer_iff] at hc
  set y := algebraMap F (u.adicCompletion F) c
  set z := y * s - h2 with hz_def
  have hz : Valued.v z < 1 := by
    calc Valued.v z = Valued.v (z * p⁻¹) * Valued.v p := by
          rw [← map_mul, inv_mul_cancel_right₀ hp0]
      _ ≤ 1 * Valued.v p := by gcongr
      _ < 1 := by rw [one_mul]; exact hvp
  have hhalf : h2 + h2 = 1 := by
    rw [hh2, ← map_add (f := _), ← map_one (algebraMap F (u.adicCompletion F))]
    congr 1
    norm_num
  have hkey : algebraMap F (u.adicCompletion F) (1 / 4 - c ^ 2 * a) = -z * (1 + z) := by
    have e1 : (1 / 4 : F) = 2⁻¹ * 2⁻¹ := by norm_num
    rw [e1, map_sub, map_mul, map_mul, map_pow, hs, ← hh2]
    rw [hz_def]
    linear_combination (h2 - y * s) * hhalf
  rw [← valued_v_algebraMap_adicCompletion_foundation, hkey]
  have h1z : Valued.v (1 + z) ≤ 1 := by
    calc Valued.v (1 + z) ≤ max (Valued.v (1 : u.adicCompletion F)) (Valued.v z) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := by rw [map_one]; exact max_le le_rfl hz.le
  calc Valued.v (-z * (1 + z)) = Valued.v z * Valued.v (1 + z) := by
        rw [map_mul, Valuation.map_neg]
    _ ≤ Valued.v z * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact hz

theorem valuation_complexConj_of_not_split {L : Type} [Field L] [NumberField L] [IsCMField L]
    (w : HeightOneSpectrum (𝓞 L)) (hw : ¬ IsSplitAt w) (y : L) :
    w.valuation L (IsCMField.complexConj L y) = w.valuation L y := by
  set σ : L ≃+* L := (IsCMField.complexConj L).toRingEquiv with hσ
  have hne : w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) ≠ ⊥ := by
    intro hbot
    apply w.ne_bot
    rw [eq_bot_iff] at hbot ⊢
    intro x hx
    have hx' : (RingOfIntegers.mapRingEquiv σ).symm x ∈
        w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) := by
      rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
      exact hx
    have h0 := hbot hx'
    rw [Ideal.mem_bot] at h0 ⊢
    simpa using h0
  obtain ⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 L),
      w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ) :=
    ⟨⟨_, Ideal.comap_isPrime _ _, hne⟩, rfl⟩
  have hfix : ∀ x : 𝓞 (maximalRealSubfield L),
      RingOfIntegers.mapRingEquiv σ (algebraMap _ (𝓞 L) x) = algebraMap _ (𝓞 L) x := by
    intro x
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingEquiv_apply]
    have hx : ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x : 𝓞 L) : L) =
        algebraMap (maximalRealSubfield L) L (x : maximalRealSubfield L) := rfl
    rw [hx]
    exact (IsCMField.complexConj L).commutes _
  have hsame : w' = w := by
    by_contra hne'
    apply hw
    refine ⟨w', hne', ?_⟩
    ext x
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, hw', hfix]
  have key := GlobalTheory.QNorm.valuation_of_eq_comap σ w w' hw' y
  rw [hsame] at key
  exact key.symm

theorem isSplitAt_of_isSquare : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : maximalRealSubfield L) (δ : L), δ ^ 2 = a → δ ∉ maximalRealSubfield L → ∀ w : HeightOneSpectrum (𝓞 L), IsSquare (algebraMap (maximalRealSubfield L) ((w.under (𝓞 (maximalRealSubfield L))).adicCompletion (maximalRealSubfield L)) a) → IsSplitAt w := by
  intro L _ _ _ a δ hδ hδL w hsq
  by_contra hw
  set u := w.under (𝓞 (maximalRealSubfield L)) with hu
  have ha : a ≠ 0 := by
    rintro rfl
    apply hδL
    have h0 : δ = 0 := by simpa using hδ
    rw [h0]
    exact zero_mem _
  obtain ⟨c, hc⟩ := exists_valuation_lt_one u a ha hsq
  have hconj : IsCMField.complexConj L δ = -δ := by
    have h1 : (IsCMField.complexConj L δ) ^ 2 = δ ^ 2 := by
      rw [← map_pow, hδ, IsCMField.complexConj_apply_eq_self]
    have h2 : IsCMField.complexConj L δ ≠ δ := fun h =>
      hδL ((IsCMField.complexConj_eq_self_iff L δ).mp h)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact absurd h h2
    · exact h
  set x : L := 2⁻¹ + (c : L) * δ with hx
  have hcc : IsCMField.complexConj L (c : L) = c := IsCMField.complexConj_apply_eq_self L c
  have hx' : IsCMField.complexConj L x = 2⁻¹ - (c : L) * δ := by
    rw [hx, map_add (f := _), map_mul, hcc, hconj, map_inv₀, map_ofNat]
    ring
  have hsum : x + IsCMField.complexConj L x = 1 := by
    rw [hx', hx]
    ring
  have hprod : x * IsCMField.complexConj L x =
      algebraMap (maximalRealSubfield L) L (1 / 4 - c ^ 2 * a) := by
    rw [hx', hx]
    simp only [map_sub, map_mul, map_pow, map_div₀, map_one, map_ofNat]
    change _ = 1 / 4 - (c : L) ^ 2 * (a : L)
    linear_combination (-(c : L) ^ 2) * hδ
  have : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  have hlt : w.valuation L (x * IsCMField.complexConj L x) < 1 := by
    rw [hprod, ← HeightOneSpectrum.valuation_liesOver L u w]
    exact pow_lt_one₀ zero_le hc
      (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal u.ne_bot).ne'
  have heq := valuation_complexConj_of_not_split w hw x
  rw [map_mul, heq] at hlt
  have hx1 : w.valuation L x < 1 := by
    by_contra hge
    push Not at hge
    exact absurd hlt (not_lt.mpr (one_le_mul hge hge))
  have hadd := Valuation.map_add (w.valuation L) x (IsCMField.complexConj L x)
  rw [hsum, map_one, heq, max_self] at hadd
  exact absurd (lt_of_le_of_lt hadd hx1) (lt_irrefl 1)

end GlobalTheory.SplitOfSquare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousBdGen
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem re_add (x y : Ainf F) (w : InfinitePlace F) : re (x + y) w = re x w + re y w := by
  have : (x + y) w = x w + y w := rfl
  simp only [re, this, map_add (f := _), Complex.add_re]

theorem re_neg (x : Ainf F) (w : InfinitePlace F) : re (-x) w = -re x w := by
  have : (-x) w = -x w := rfl
  simp only [re, this, map_neg, Complex.neg_re]

theorem re_mul [IsTotallyReal F] (x y : Ainf F) (w : InfinitePlace F) :
    re (x * y) w = re x w * re y w := by
  have hw : w.IsReal := IsTotallyReal.isReal w
  have : (x * y) w = x w * y w := rfl
  simp only [re, this, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, map_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem re_sum [IsTotallyReal F] {ι : Type} (s : Finset ι) (f : ι → Ainf F) (w : InfinitePlace F) :
    re (∑ i ∈ s, f i) w = ∑ i ∈ s, re (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (0 : Ainf F) w = 0 := rfl
    simp [re, this]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, re_add, ih]

theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem inf_add (u v : Fin N → AF F) : inf (u + v) = inf u + inf v := by
  funext l; simp [inf, map_add (f := _)]

theorem inf_neg (u : Fin N → AF F) : inf (-u) = -inf u := by
  funext l; simp [inf, map_neg]

theorem fin_add (u v : Fin N → AF F) : fin (u + v) = fin u + fin v := by
  funext l; simp [fin, map_add (f := _)]

theorem sz_add_le (u v : Fin N → AF F) : sz (u + v) ≤ sz u + sz v := by
  unfold sz
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [inf_add, Pi.add_apply, re_add]
  exact abs_add_le _ _

theorem sz_neg (u : Fin N → AF F) : sz (-u) = sz u := by
  unfold sz
  simp only [inf_neg, Pi.neg_apply, re_neg, abs_neg]

theorem inf_mulVec (M : Matrix (Fin N) (Fin N) (AF F)) (u : Fin N → AF F) (l : Fin N) :
    inf (M.mulVec u) l = ∑ m, fstA F (M l m) * inf u m := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [inf, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem sz_mulVec_le [IsTotallyReal F] (M : Matrix (Fin N) (Fin N) (AF F)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u, sz (M.mulVec u) ≤ A * sz u := by
  set D : ℝ := ∑ l, ∑ m, ∑ w : InfinitePlace F, |re (fstA F (M l m)) w| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hle : ∀ l m w, |re (fstA F (M l m)) w| ≤ D := by
    intro l m w
    have h1 : |re (fstA F (M l m)) w| ≤ ∑ w' : InfinitePlace F, |re (fstA F (M l m)) w'| :=
      Finset.single_le_sum (f := fun w' => |re (fstA F (M l m)) w'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ w)
    have h2 : ∑ w' : InfinitePlace F, |re (fstA F (M l m)) w'| ≤
        ∑ m', ∑ w' : InfinitePlace F, |re (fstA F (M l m')) w'| :=
      Finset.single_le_sum (f := fun m' => ∑ w' : InfinitePlace F, |re (fstA F (M l m')) w'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ m)
    have h3 : ∑ m', ∑ w' : InfinitePlace F, |re (fstA F (M l m')) w'| ≤ D :=
      Finset.single_le_sum (f := fun l' => ∑ m', ∑ w' : InfinitePlace F, |re (fstA F (M l' m')) w'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ l)
    linarith
  have hs : ∀ (u : Fin N → AF F) m w, |re (inf u m) w| ≤ sz u := by
    intro u m w
    have h1 : |re (inf u m) w| ≤ ∑ w' : InfinitePlace F, |re (inf u m) w'| :=
      Finset.single_le_sum (f := fun w' => |re (inf u m) w'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ w)
    have h2 : ∑ w' : InfinitePlace F, |re (inf u m) w'| ≤ sz u :=
      Finset.single_le_sum (f := fun m' => ∑ w' : InfinitePlace F, |re (inf u m') w'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ m)
    linarith
  refine ⟨(N : ℝ) * (Fintype.card (InfinitePlace F) : ℝ) * ((N : ℝ) * D), by positivity, fun u => ?_⟩
  have key : ∀ l w, |re (inf (M.mulVec u) l) w| ≤ (N : ℝ) * D * sz u := by
    intro l w
    rw [inf_mulVec, re_sum]
    calc |∑ m, re (fstA F (M l m) * inf u m) w| ≤ ∑ m, |re (fstA F (M l m) * inf u m) w| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m : Fin N, D * sz u := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [re_mul, abs_mul]
          exact mul_le_mul (hle l m w) (hs u m w) (abs_nonneg _) hD0
      _ = (N : ℝ) * D * sz u := by simp [Finset.sum_const, Finset.card_univ]; ring
  calc sz (M.mulVec u) = ∑ l, ∑ w : InfinitePlace F, |re (inf (M.mulVec u) l) w| := rfl
    _ ≤ ∑ _l : Fin N, ∑ _w : InfinitePlace F, (N : ℝ) * D * sz u :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun w _ => key l w
    _ = (N : ℝ) * (Fintype.card (InfinitePlace F) : ℝ) * ((N : ℝ) * D) * sz u := by
        simp [Finset.sum_const, Finset.card_univ]; ring

theorem decay_of_comp {Φ : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (f : (Fin N → AF F) → (Fin N → AF F))
    (hf : Continuous f) (m : (Fin N → AF F) → ℂ) (hm : Continuous m) (B : ℝ) (hB : ∀ u, ‖m u‖ ≤ B)
    (hK : ∀ K : Set (Fin N → Af F), IsCompact K →
      ∃ K' : Set (Fin N → Af F), IsCompact K' ∧ ∀ u, fin (f u) ∈ K → fin u ∈ K')
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hsz : ∀ u, sz u ≤ A * sz (f u) + C) :
    Decay fun u => m u * Φ (f u) := by
  obtain ⟨hc, ⟨K, hKc, hK0⟩, hd⟩ := hΦ
  refine ⟨hm.mul (hc.comp hf), ?_, fun k => ?_⟩
  · obtain ⟨K', hK'c, hK'⟩ := hK K hKc
    refine ⟨K', hK'c, fun u hu => ?_⟩
    have : fin (f u) ∉ K := fun h => hu (hK' u h)
    show m u * Φ (f u) = 0
    rw [hK0 _ this, mul_zero]
  · obtain ⟨D, hD⟩ := hd k
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    refine ⟨B * (1 + A + C) ^ k * D, fun u => ?_⟩
    have h1 : 1 + sz u ≤ (1 + A + C) * (1 + sz (f u)) := by
      have := hsz u; have := sz_nonneg (f u); nlinarith
    have h2 : (1 + sz u) ^ k ≤ (1 + A + C) ^ k * (1 + sz (f u)) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith [sz_nonneg u]) h1 k
    have h3 := hD (f u)
    rw [norm_mul]
    calc ‖m u‖ * ‖Φ (f u)‖ * (1 + sz u) ^ k
        ≤ B * ‖Φ (f u)‖ * ((1 + A + C) ^ k * (1 + sz (f u)) ^ k) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (hB u) (norm_nonneg _)) h2
            (pow_nonneg (by linarith [sz_nonneg u]) _) (mul_nonneg hB0 (norm_nonneg _))
      _ = B * (1 + A + C) ^ k * (‖Φ (f u)‖ * (1 + sz (f u)) ^ k) := by ring
      _ ≤ B * (1 + A + C) ^ k * D :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hB0 (pow_nonneg (by linarith) _))

end GlobalTheory.SWQ

noncomputable section

namespace GlobalTheory.SWQ

theorem continuous_qd' {F : Type} [Field F] [NumberField F] {N : ℕ} (a : Fin N → F) :
    Continuous (qd (AF F) a) := by
  unfold qd; fun_prop

theorem continuous_Bd_gen {F : Type} [Field F] {N : ℕ} (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] (a : Fin N → F) (y : Fin N → R) :
    Continuous fun x => Bd R a x y := by
  unfold Bd; fun_prop

theorem continuous_Bd' {F : Type} [Field F] [NumberField F] {N : ℕ} (a : Fin N → F)
    (y : Fin N → AF F) : Continuous fun x => Bd (AF F) a x y :=
  continuous_Bd_gen (AF F) a y

theorem fin_mulVec {F : Type} [Field F] [NumberField F] {N : ℕ} (M : Matrix (Fin N) (Fin N) (AF F))
    (v : Fin N → AF F) : fin (M.mulVec v) = (M.map (sndA F).toRingHom).mulVec (fin v) := by
  funext l
  exact RingHom.map_mulVec (sndA F).toRingHom M v l

theorem decay_ops : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → (∀ b, Decay (Ub ψ a b Φ)) ∧ (∀ x y, Decay (rho ψ a x y Φ)) ∧
      (∀ t : AF F, IsUnit t → Decay (Da t Φ)) ∧ (∀ c : ℂ, Decay (c • Φ)) ∧
      ∀ g : GL (Fin N) (AF F), Decay fun u => Φ ((g : Matrix (Fin N) (Fin N) (AF F)).mulVec u) := by
  intro F _ _ N ψ lam ν a hc Φ hΦ
  haveI : IsTotallyReal F := hc.1
  have hψc : Continuous ψ := hc.2.1.1
  have hψ1 : ∀ x, ‖ψ x‖ = 1 := hc.2.1.2.1
  have hGL : ∀ g : GL (Fin N) (AF F), Decay fun u => Φ ((g : Matrix (Fin N) (Fin N) (AF F)).mulVec u) := by
    intro g
    have hinv : ((g⁻¹ : GL (Fin N) (AF F)) : Matrix (Fin N) (Fin N) (AF F)) * (g : Matrix _ _ _) = 1 :=
      Units.inv_mul g
    obtain ⟨A, hA, hAle⟩ := sz_mulVec_le ((g⁻¹ : GL (Fin N) (AF F)) : Matrix (Fin N) (Fin N) (AF F))
    have h := decay_of_comp hΦ (fun u => (g : Matrix (Fin N) (Fin N) (AF F)).mulVec u)
      (continuous_const.matrix_mulVec continuous_id) (fun _ => (1 : ℂ)) continuous_const 1 (by simp) ?_
      A 0 hA le_rfl ?_
    · simpa using h
    · intro K hK
      refine ⟨(fun z => (((g⁻¹ : GL (Fin N) (AF F)) : Matrix (Fin N) (Fin N) (AF F)).map
          (sndA F).toRingHom).mulVec z) '' K,
        hK.image (continuous_const.matrix_mulVec continuous_id), fun u hu => ⟨_, hu, ?_⟩⟩
      simp only
      rw [fin_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    · intro u
      have h := hAle ((g : Matrix (Fin N) (Fin N) (AF F)).mulVec u)
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h
      linarith
  refine ⟨fun b => ?_, fun x y => ?_, fun t ht => ?_, fun c => ?_, hGL⟩
  · exact decay_of_comp hΦ id continuous_id (fun u => ψ (b * qd (AF F) a u))
      (hψc.comp (continuous_const.mul (continuous_qd' a))) 1 (fun u => (hψ1 _).le)
      (fun K hK => ⟨K, hK, fun u h => h⟩) 1 0 zero_le_one le_rfl (fun u => by simp)
  · exact decay_of_comp hΦ (fun u => u + x) (continuous_id.add continuous_const)
      (fun u => ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y))
      (hψc.comp ((continuous_Bd' a y).add continuous_const)) 1 (fun u => (hψ1 _).le)
      (fun K hK => ⟨(fun z => z - fin x) '' K, hK.image (continuous_sub_right _),
        fun u hu => ⟨_, hu, by simp only [fin_add, add_sub_cancel_right]⟩⟩)
      1 (sz x) zero_le_one (sz_nonneg x) (fun u => by
        have h1 := sz_add_le (u + x) (-x)
        rw [sz_neg, add_neg_cancel_right] at h1
        linarith)
  · let g : GL (Fin N) (AF F) := Units.map (Matrix.scalar (Fin N) : AF F →+* Matrix (Fin N) (Fin N) (AF F)).toMonoidHom ht.unit
    have h := hGL g
    convert h using 1
    congr 1
    funext l
    simp [Da, g, Matrix.mulVec_diagonal]
  · have h := decay_of_comp hΦ id continuous_id (fun _ => c) continuous_const ‖c‖ (fun _ => le_rfl)
      (fun K hK => ⟨K, hK, fun u h => h⟩) 1 0 zero_le_one le_rfl (fun u => by simp)
    convert h using 1
    funext u
    rfl

end GlobalTheory.SWQ
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CountableOfNumberField
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.SWQ

theorem countable_of_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem map_unit_mul_eq (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)) [ν.IsAddHaarMeasure]
    (w : (AF F)ˣ) : ν.map (fun x => w • x) = (distribHaarChar (AF F) w⁻¹ : ℝ≥0∞) • ν := by
  ext S hS
  rw [Measure.map_apply (measurable_const_smul w) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
    distribHaarChar_mul]

theorem modrat_main : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν →
    ∀ t : F, t ≠ 0 → ν.map (fun x => (algebraMap F (AF F) t) * x) = ν := by
  intro F _ _ _ ν hν t ht
  obtain ⟨hH, D, _, hD, hD1⟩ := hν
  haveI := hH
  haveI := countable_of_numberField F
  set K := (algebraMap F (AF F)).range.toAddSubgroup with hK
  haveI : Countable K := by
    refine Function.Surjective.countable (f := fun r : F => (⟨algebraMap F (AF F) r, ⟨r, rfl⟩⟩ : K)) ?_
    rintro ⟨x, ⟨r, rfl⟩⟩
    exact ⟨r, rfl⟩
  have htu : IsUnit (algebraMap F (AF F) t) := (isUnit_iff_ne_zero.mpr ht).map _
  set u : (AF F)ˣ := htu.unit with hu
  have hmul : (fun x : AF F => (algebraMap F (AF F) t) * x) = fun x => u • x := by
    funext x; rfl
  rw [hmul]

  let e : K ≃ K :=
    { toFun := fun g => ⟨algebraMap F (AF F) t⁻¹ * g, by
        obtain ⟨r, hr⟩ := g.2; exact ⟨t⁻¹ * r, by rw [map_mul, hr]⟩⟩
      invFun := fun g => ⟨algebraMap F (AF F) t * g, by
        obtain ⟨r, hr⟩ := g.2; exact ⟨t * r, by rw [map_mul, hr]⟩⟩
      left_inv := fun g => by
        ext; simp only; rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
      right_inv := fun g => by
        ext; simp only; rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] }
  have hqmp : Measure.QuasiMeasurePreserving (MulAction.toPerm u).symm ν ν := by
    refine ⟨(measurable_const_smul u⁻¹).aemeasurable, ?_⟩
    have : ⇑(MulAction.toPerm u).symm = fun x : AF F => u⁻¹ • x := rfl
    rw [this, map_unit_mul_eq F ν u⁻¹]
    exact Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _
  have hD' : IsAddFundamentalDomain K (MulAction.toPerm u '' D) ν := by
    refine hD.image_of_equiv (MulAction.toPerm u) hqmp e ?_
    intro g x
    change u • ((e g : AF F) + x) = (g : AF F) + u • x
    change algebraMap F (AF F) t * (algebraMap F (AF F) t⁻¹ * (g : AF F) + x) = (g : AF F) + algebraMap F (AF F) t * x
    rw [mul_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
  have himg : (MulAction.toPerm u '' D) = u • D := rfl
  have h1 : ν (u • D) = 1 := by rw [← himg, hD'.measure_eq hD, hD1]
  have hchar : distribHaarChar (AF F) u = 1 := by
    have := distribHaarChar_mul ν u D
    rw [h1, hD1, mul_one] at this
    exact_mod_cast this
  rw [map_unit_mul_eq F ν u, map_inv, hchar, inv_one, ENNReal.coe_one, one_smul]

end GlobalTheory.SWQ
end
end
