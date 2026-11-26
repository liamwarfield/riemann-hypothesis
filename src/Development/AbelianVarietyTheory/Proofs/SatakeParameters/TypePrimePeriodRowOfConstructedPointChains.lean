module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsCosetSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.EntryG
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramified

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetLossOfFamilyFacts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.LiftTypePrime.Jets (intAt_mul intAt_sum intAt_of_isIntegral isIntegral_exp)
open GlobalTheory.MomT.CosetSum

noncomputable section

namespace GlobalTheory.DatumJets

section Int

variable {p : ℕ} [Fact p.Prime] {lam : TaylorLogMetric.Qbar →+* ℂ_[p]}

end Int

section Idx

variable {X : Fields} {a b : ℕ}

end Idx

theorem map_jetSum {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) {cA c : ℕ}
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (hcA0 : 0 < cA) (hc0 : 0 < c) (Ξ : HomE X.E a b → X.K) {e : DVar X.Tau a b →₀ ℕ} (he : e ∈ RatIdx A S cA c N N' Ξ) :
    A.σ₀ (jetSum A S cA c N N' Ξ e) = (A.chiF a b N N')⁻¹ *
      latSum (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) fun x => A.σ₀ (Ξ x) * jetC A.cD (A.thInd S N N' c x) e := by
  have := GlobalTheory.MomT.finite_quot_divLat_mulLat_homAt X.E a b S N N' cA c hN.1 hN'.1 hcA0 hc0
  have := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [jetSum, latSum, latSum, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  generalize Function.surjInv (Submodule.Quotient.mk_surjective _) z = x
  by_cases h0 : Ξ x = 0
  · simp [h0]
  · have h := he x x.2 h0
    rw [map_mul, Amb.jetK, desc, dite_eq_left h, h.choose_spec]
    ring

end GlobalTheory.DatumJets
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundConstantOneOfChainAgreement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationBoundTypePrimePlaceOfChainAgreeme
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaJetIntegralityTypePrimeOfSplitTableBound
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaJetIntegralityTypePrimeOfSplitTableBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.AtG
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.DatumJets (SplitSet map_jetSum)
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.JetsFromTables

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}

omit [NumberField E] [StarRing E] in
theorem homAt_mono {S T : Finset (HeightOneSpectrum (𝓞 E))} (h : T ⊆ S) : homAt S N N' ≤ homAt T N N' :=
  fun _ hx P hP => hx P (h hP)

theorem homAt_of_smul {T : Finset (HeightOneSpectrum (𝓞 E))} {r : 𝓞 E} (hr : ∀ P ∈ T, r ∉ P.asIdeal) {x : HomE E a b}
    (hx : r • x ∈ homAt T N N') : x ∈ homAt T N N' := by
  intro P hP y hy
  obtain ⟨s, hs, hsy⟩ := (mem_locP P N' _).1 (hx P hP y hy)
  refine (mem_locP P N' _).2 ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs (hr P hP), ?_⟩
  rwa [mul_smul]

end Loc

section Level

variable {X : Fields} (A : Amb X) {a b : ℕ} {S : Finset (HeightOneSpectrum (𝓞 X.E))}
  {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

theorem jetC_refine (hLa : A.LaHyp a b S) (hE : A.ESmooth a b) {M c k : ℕ} (hM : 0 < M) (hc : 0 < c) (hk : 0 < k) {x : HomE X.E a b}
    (hR : InRange S M (c * k) N N' x) (m : DVar X.Tau a b →₀ ℕ) :
    jetC A.cD (A.thInd S N N' c x) m =
      latSum (mulLat c (homAt S N N')) (mulLat (c * k) (homAt S N N')) fun y => jetC A.cD (A.thInd S N N' (c * k) (x + y)) m := by
  have hadd := indAdd_of A a b S M hM (lattice_classes_finite_refinement X a b S) (indTieD_of_la A a b S M hM hLa)
  have hsm : A.IndSmooth a b S M := indSmooth_of A _ _ _ _ hE
  have := fin_mul S N N' hR.1 hR.2.1 c k hc hk
  let _ := Fintype.ofFinite (↥(mulLat c (homAt S N N')) ⧸ (mulLat (c * k) (homAt S N N')).comap (mulLat c (homAt S N N')).subtype)
  have h1 : A.thInd S N N' c x = fun w => ∑ z, A.thInd S N N' (c * k)
      (x + (lrep (mulLat c (homAt S N N')) (mulLat (c * k) (homAt S N N')) z : HomE X.E a b)) w := by
    funext w
    rw [hadd N N' c k x hc hk hR w, latSum_eq, finsum_eq_sum_of_fintype]
  rw [latSum_eq, finsum_eq_sum_of_fintype]
  unfold jetC derivAt0
  rw [h1, iteratedFDeriv_sum (fun z _ => hsm N N' (c * k) _ (hR.add (Subtype.coe_prop _)) _), Finset.sum_apply, _root_.sum_apply,
    Finset.mul_sum]

theorem latSum_coarsen (hLa : A.LaHyp a b S) (hE : A.ESmooth a b) (hN : IsSdLat N) (hN' : IsSdLat N') {cA c k : ℕ} (hA : 0 < cA)
    (hc : 0 < c) (hk : 0 < k) (Ξ : HomE X.E a b → ℂ) (hinv : ∀ x y, y ∈ mulLat c (homAt S N N') → Ξ (x + y) = Ξ x)
    (m : DVar X.Tau a b →₀ ℕ) :
    (latSum (divLat cA (homAt S N N')) (mulLat (c * k) (homAt S N N')) fun x => Ξ x * jetC A.cD (A.thInd S N N' (c * k) x) m) =
      latSum (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) fun x => Ξ x * jetC A.cD (A.thInd S N N' c x) m := by
  have hck := Nat.mul_pos hc hk
  have := fin_div S N N' hN hN' cA (c * k) hA hck
  have := fin_mul S N N' hN hN' c k hc hk
  rw [latSum_tower _ (mulLat c (homAt S N N')) _ (mulLat_mul_le c k _) (mulLat_le_divLat c cA _) _ ?_]
  · refine latSum_congr _ _ fun x hx => ?_
    rw [jetC_refine A hLa hE (Nat.mul_pos hA hck) hc hk ⟨hN, hN', hck, Dvd.intro_left cA rfl, divLat_mul_of cA (c * k) _ hx⟩ m,
      ← latSum_mul_left]
    exact latSum_congr _ _ fun y hy => by rw [hinv x y hy]
  · intro x y hy
    have h1 : A.thInd S N N' (c * k) (x + y) = A.thInd S N N' (c * k) x := by
      unfold Amb.thInd Amb.liftW
      rw [isLift_congr A S N N' (c * k) (x + y) x (by simpa using hy)]
    rw [hinv x y (mulLat_mul_le c k _ hy), h1]

theorem jetSum_level (hLa : A.LaHyp a b S) (hE : A.ESmooth a b) (hN : IsSdLat N) (hN' : IsSdLat N') {cA c₁ c₂ M : ℕ} (hA : 0 < cA)
    (hM : 0 < M) (h₁ : c₁ ∣ M) (h₂ : c₂ ∣ M) (Ξ : HomE X.E a b → X.K)
    (i₁ : ∀ x y, y ∈ mulLat c₁ (homAt S N N') → Ξ (x + y) = Ξ x) (i₂ : ∀ x y, y ∈ mulLat c₂ (homAt S N N') → Ξ (x + y) = Ξ x)
    {m : DVar X.Tau a b →₀ ℕ} (r₁ : m ∈ RatIdx A S cA c₁ N N' Ξ) (r₂ : m ∈ RatIdx A S cA c₂ N N' Ξ) :
    jetSum A S cA c₁ N N' Ξ m = jetSum A S cA c₂ N N' Ξ m := by
  have p₁ := Nat.pos_of_dvd_of_pos h₁ hM
  have p₂ := Nat.pos_of_dvd_of_pos h₂ hM
  obtain ⟨k₁, e₁⟩ := h₁
  obtain ⟨k₂, e₂⟩ := h₂
  apply A.σ₀.injective
  rw [map_jetSum A S hN hN' hA p₁ Ξ r₁, map_jetSum A S hN hN' hA p₂ Ξ r₂,
    ← latSum_coarsen A hLa hE hN hN' hA p₁ (Nat.pos_of_mul_pos_left (e₁ ▸ hM)) _ (fun x y hy => congrArg A.σ₀ (i₁ x y hy)),
    ← latSum_coarsen A hLa hE hN hN' hA p₂ (Nat.pos_of_mul_pos_left (e₂ ▸ hM)) _ (fun x y hy => congrArg A.σ₀ (i₂ x y hy)),
    ← e₁, ← e₂]

theorem notMem_of_split {ϖ : 𝓞 X.E} {p : ℕ} (hctx : SplitSet A a b S ϖ p) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ S)
    (hϖ : ϖ ∉ P.asIdeal) : X.conjO ϖ ∉ P.asIdeal ∧ (p : 𝓞 X.E) ∉ P.asIdeal := by
  obtain ⟨-, hLa, -, -, -, hn, -, hS⟩ := hctx
  have h1 : X.conjO ϖ ∉ P.asIdeal := fun h => hLa.2.2.1 P hP (hS _ h)
  exact ⟨h1, fun h => (P.isPrime.mem_or_mem (hn ▸ h)).elim hϖ h1⟩

theorem datum_bound {ϖ : 𝓞 X.E} {p cA cB : ℕ} (hctx : SplitSet A a b S ϖ p) (hN : IsSdLat N) (hN' : IsSdLat N') (hA : 0 < cA)
    (hB : 0 < cB) (hpB : p ∣ cB) (w : HeightOneSpectrum (𝓞 X.K)) (κ : X.K) (Ξ : HomE X.E a b → X.K)
    (hΞ : GlobalTheory.ColPeriod.DatumAt (divs ϖ) S p cB w N N' Ξ) {m : DVar X.Tau a b →₀ ℕ}
    (hrat : ∀ c : ℕ, 0 < c → c ∣ cA * cB → m ∈ RatIdx A S cA c N N' Ξ)
    (hb : ∀ (c' : ℕ) (x : HomE X.E a b), 0 < c' → ¬ p ∣ c' → x ∈ divLat c' (homAt S N N') →
      w.valuation X.K (κ * A.jetK S N N' (p * c') x m) ≤ 1) :
    w.valuation X.K (κ * jetSum A S cA cB N N' Ξ m) ≤ 1 := by
  classical
  obtain ⟨h1, h2, h3⟩ := hΞ
  have hp : p.Prime := hctx.2.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := left_ne_zero_of_mul (by rw [hctx.2.2.2.2.2.1]; exact_mod_cast hp.ne_zero)
  have hsub : divs ϖ ⊆ S := fun P hP => hctx.2.2.2.2.2.2.2 P ((mem_divs hϖ0 P).1 hP)
  have hM := Nat.mul_pos hA hB
  obtain ⟨n, c', hc', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' p hp.ne_one
  have hc0 : 0 < c' := Nat.pos_of_ne_zero fun h => hc' (h ▸ dvd_zero p)
  have hpn : ∀ P ∈ S \ divs ϖ, ((p ^ n : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun P hP h => by
    rw [Finset.mem_sdiff, mem_divs hϖ0] at hP
    rw [Nat.cast_pow] at h
    exact (notMem_of_split A hctx hP.1 hP.2).2 (P.isPrime.mem_of_pow_mem n h)
  have hL : p * c' ∣ cA * cB :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.Prime.coprime_iff_not_dvd hp).2 hc') (hpB.mul_left _) ⟨p ^ n, by rw [hn, mul_comm]⟩
  have h3' : ∀ x z, z ∈ mulLat p (homAt S N N') → z ∈ mulLat cB (homAt (S \ divs ϖ) N N') → Ξ (x + z) = Ξ x := fun x z hz hz' =>
    h3 x z (Submodule.map_mono (homAt_mono hsub) hz) (by convert hz')
  have hB' : (cB : X.E) ≠ 0 := by exact_mod_cast hB.ne'
  rw [jetSum_level A hctx.2.1 hctx.2.2.2.1 hN hN' hA hM (Dvd.intro_left _ rfl) hL Ξ (fun x y hy => ?_) (fun x y hy => ?_)
    (hrat _ hB (Dvd.intro_left _ rfl)) (hrat _ (Nat.mul_pos hp.pos hc0) hL)]
  · have := fin_div S N N' hN hN' cA (p * c') hA (Nat.mul_pos hp.pos hc0)
    let _ := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat (p * c') (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
    rw [jetSum, latSum_eq, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Valuation.map_sum_le _ fun z _ => ?_
    generalize lrep _ _ z = x
    obtain ⟨x, hx⟩ := x
    dsimp only
    by_cases h0 : Ξ x = 0
    · simp [h0]
    rw [mul_left_comm, map_mul]
    refine mul_le_one' (h1 x) (hb c' x hc0 hc' ((mem_divLat _ _ _).2 fun P hP => ?_))
    by_cases hP' : P ∈ divs ϖ
    · exact Submodule.smul_mem _ (c' : 𝓞 X.E) (h2 x h0) P hP'
    · refine homAt_of_smul hpn (x := (c' : 𝓞 X.E) • x) ?_ P (Finset.mem_sdiff.2 ⟨hP, hP'⟩)
      rw [smul_smul, ← Nat.cast_mul, ← hn, mul_comm, Nat.cast_mul, mul_smul]
      exact homAt_mono Finset.sdiff_subset (Submodule.smul_mem _ _ ((mem_divLat _ _ _).1 hx))
  · obtain ⟨k, rfl⟩ := hpB
    exact h3' x y (mulLat_mul_le p k _ hy) (Submodule.map_mono (homAt_mono Finset.sdiff_subset) hy)
  · refine h3' x y (mulLat_mul_le p c' _ hy) ?_
    obtain ⟨t, ht, rfl⟩ := (mem_mulLat _ _ _).1 hy
    refine (mem_mulLat _ _ _).2 ⟨(cB : X.E)⁻¹ • ((p * c' : ℕ) : 𝓞 X.E) • t, homAt_of_smul hpn ?_, ?_⟩
    · have e : ((p ^ n : ℕ) : 𝓞 X.E) • (cB : X.E)⁻¹ • ((p * c' : ℕ) : 𝓞 X.E) • t = ((p * cA : ℕ) : 𝓞 X.E) • t := by
        have e1 : (cA : X.E) * cB = p ^ n * c' := by exact_mod_cast hn
        simp only [Nat.cast_smul_eq_nsmul]
        simp only [← Nat.cast_smul_eq_nsmul X.E, smul_smul]
        congr 1
        push_cast
        field_simp
        linear_combination (-(p : X.E)) * e1
      rw [e]
      exact homAt_mono Finset.sdiff_subset (Submodule.smul_mem _ _ ht)
    · rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul X.E, smul_smul, mul_inv_cancel₀ hB', one_smul]

end Level

section Host

theorem half_coords {d g : ℕ} (hd : d.Prime) (hodd : d % 2 = 1) {a b : ℚ} {t : ℤ} (ht : 2 * a = t) (hn : a ^ 2 + d * b ^ 2 = g) :
    ∃ m n : ℤ, a = m + n / 2 ∧ b = n / 2 := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have h1 : (d * (2 * b)) ^ 2 = ((d * (4 * g - t ^ 2) : ℤ) : ℚ) := by
    push_cast
    rw [← ht, ← hn]; ring
  have h2 : IsIntegral ℤ ((d : ℚ) * (2 * b)) := IsIntegral.of_pow (n := 2) two_pos (h1 ▸ isIntegral_algebraMap (x := (d * (4 * g - t ^ 2) : ℤ)))
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have hr' : (r : ℚ) = d * (2 * b) := hr
  have h3 : r ^ 2 = d * (4 * g - t ^ 2) := by
    rw [← hr'] at h1; exact_mod_cast h1
  obtain ⟨s, hs⟩ : (d : ℤ) ∣ r := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨_, h3⟩
  have hb : 2 * b = s := mul_left_cancel₀ hd0 (by rw [← hr', hs]; push_cast; ring)
  have h4 : t ^ 2 + d * s ^ 2 = 4 * g := by
    have : (t : ℚ) ^ 2 + d * s ^ 2 = 4 * g := by rw [← ht, ← hb, ← hn]; ring
    exact_mod_cast this
  have h5 : Even (t - s) := by
    have hdo : Odd (d : ℤ) := by exact_mod_cast Nat.odd_iff.2 hodd
    have h6 : Even (t ^ 2 + d * s ^ 2) := h4 ▸ ⟨2 * g, by ring⟩
    simpa [parity_simps, Int.not_even_iff_odd.2 hdo] using h6
  obtain ⟨m, hm⟩ := h5
  have hm' : (t : ℚ) - s = m + m := by exact_mod_cast hm
  exact ⟨m, s, by linarith, by linarith⟩

theorem isQInt_piG {D : D7} (EX : ErrX D) (i : Fin 2) :
    Formalism.L2.AlgTh.IsQInt D.host.d (D.host.φ₀ ((EX.piG i : 𝓞 D.host.E) : D.host.E)) := by
  obtain ⟨a, b, hab⟩ := GlobalTheory.QuadSubfield.exists_coords D (EX.piG_K i)
  have hc := GlobalTheory.QuadSubfield.conj_coords D a b
  have hn := EX.piG_norm i
  have hint : IsIntegral ℤ (((EX.piG i : 𝓞 D.host.E) : D.host.E) + D.host.conj ((EX.piG i : 𝓞 D.host.E) : D.host.E)) :=
    (EX.piG i).isIntegral_coe.add (map_isIntegral_int D.host.conj (EX.piG i).isIntegral_coe)
  rw [hab, hc] at hint hn
  have e : (a : D.host.E) + b * D.host.sqrtMinusD + (a - b * D.host.sqrtMinusD) = algebraMap ℚ D.host.E (2 * a) := by
    simp; ring
  rw [e, isIntegral_algebraMap_iff ] at hint
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hn' : a ^ 2 + D.host.d * b ^ 2 = D.host.g i := by
    have : (a : D.host.E) ^ 2 + D.host.d * b ^ 2 = D.host.g i := by
      linear_combination hn + (b : D.host.E) ^ 2 * D.host.sqrtMinusD_sq
    exact_mod_cast this
  have hh := D.host.hyp
  obtain ⟨m, n, hm, hn⟩ := half_coords hh.2.1 (by have := hh.2.2.2.1; omega) (t := t) (by simpa using ht.symm) hn'
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  refine ⟨m, n, ?_⟩
  rw [hab, map_add (f := _), map_mul, map_ratCast, map_ratCast, hφ, hm, hn, Formalism.L2.Th1.CM.omegaK]
  push_cast
  ring

end Host

theorem jetLossAll_of_jetSplitAmb : JetSplitAmb → ∀ (D : D7) (EX : ErrX D)
    (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), GlobalTheory.ColPeriod.JetLossAll D EX sel B χ cD := by
  intro hJ D EX sel δ B χ cD hH hsel hA i w hw u mu cst hcst j b _ hb N N' hN hN' hsN hsN' Ξ hΞ e _ hrat
  have hPr := hH.2.2.2.2
  have hX := hH.2.2.2.1.ok
  have hp : (D.host.g i).Prime := hPr.g_prime i
  have : Fact (D.host.g i).Prime := ⟨hp⟩
  have hs : (recSeam D).Ok := ⟨GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recSeam_emb D, bridge_star_holds D.R D.host⟩
  have hcc : TaylorLogMetric.IsCurveIdeal D D.host.ccK := by rw [hH.1]; exact ⟨by simp, by simp⟩
  have hev : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hb' : Even b := hb ▸ hev _
  have hV : B.VecP χ := GlobalTheory.ColNorms.familyVectors D _ δ B χ hH.2.2.1 hH.2.1 hcc hA.1 hA.2.1 (GlobalTheory.ExponentsFinite.yFinite _ _ _)
  obtain ⟨hL, hE⟩ := GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth D _ (recSeam D) _ δ B χ cD _ b hX hs hcc hA.1 hV (hev j) hb'
  obtain ⟨hctx, hA0, hB0, hg⟩ := GlobalTheory.T.datumJets_typePrimeBadPrimesLevelsHypotheses D EX sel δ B χ cD hH hsel i u mu cst hcst _ b hL hE
  have hcong : D.host.g i ≡ 1 [MOD D.host.QS * D.host.q * D.host.d] := hPr.g_cong i
  have hnd : ∀ t, t ∣ D.host.QS * D.host.q * D.host.d → ¬ D.host.g i ∣ t := fun t ht h =>
    hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd.1
      ((hcong.of_dvd (h.trans ht)).symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)))))
  have h5 : 5 ≤ D.host.g i := by
    have h4 : D.host.g i ≡ 1 [MOD 4] := hcong.of_dvd ((by norm_num : 4 ∣ 16).trans D.host.toHostRaw.sixteen_dvd_condN)
    have := hp.one_lt
    unfold Nat.ModEq at h4
    omega
  have hpd : ¬ D.host.g i ∣ D.host.d := hnd _ (Dvd.intro_left _ rfl)
  have hpq : D.host.g i ≠ D.host.q := fun h => hnd D.host.q D.host.toHostRaw.q_dvd_condN h.dvd
  have hdisc := GlobalTheory.GoodDepth.not_dvd_discr_host D.R D.host _ hp (UpperTheory.Ram.g_notMem_small D i) hpq fun h => hpd h.dvd
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.place_over_p_induced_by_algebraic_padic_embedding _ (recSeam D).σ₀ (D.host.g i) w hw
  obtain ⟨ι, hι⟩ := GlobalTheory.ThLoc.place_extends_to_iso _ lam
  have hιC : ∀ x ∈ TaylorLogMetric.Qbar, TaylorLogMetric.lamC lam x = ι x := fun x hx => by rw [TaylorLogMetric.lamC, dite_eq_left hx]; exact (hι ⟨x, hx⟩).symm
  have hval : ∀ k : D.what₂.LL, ‖ι ((recSeam D).σ₀ k)‖ ≤ 1 → w.valuation _ k ≤ 1 := fun k hk => by
    have hq : (recSeam D).σ₀ k ∈ TaylorLogMetric.Qbar := by
      rw [mem_algebraicClosure_iff]
      exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) k).algHom (recSeam D).σ₀.toRatAlgHom
    exact (hlam k).1 ⟨hq, by rwa [hιC _ hq]⟩
  have hcD : ∀ τ, ‖ι (cD τ)‖ ≤ 1 := fun τ => by
    obtain ⟨M, _, hM, hs⟩ := hA.2.2
    obtain ⟨s, hsc, hsp⟩ := hs τ
    rw [← hsc, ← hιC _ (GlobalTheory.EigenGenerator.mem_Qbar M s)]
    exact (GlobalTheory.EigenGenerator.norm_generator_eq_one D _ lam (UpperTheory.Ram.g_notMem_small D i) hpq M hM τ s hsp).le
  have hstd : ∀ {n : ℕ} {L : Submodule (𝓞 D.host.E) (Sp D.host.E n)}, L.FG → GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (D.host.g i) L →
      (recSeam D).StdAtP (D.host.g i) L := fun hL h => by
    obtain ⟨s, hs, h1, h2⟩ := GlobalTheory.LiftTypePrime.ProdComb.eqAt_std (GlobalTheory.DatumJets.Transl.stdAt_of_stdOver D hp hL h)
    exact ⟨s, hs, h2, h1⟩
  set πE : D.host.E := ((EX.piG i : 𝓞 D.host.E) : D.host.E) with hπE
  have hτ : ∀ τ, (recFields D).embC (recSeam D).σ₀ τ πE = D.host.φ₀ πE := fun τ =>
    (hs.1 τ πE).trans (hH.2.1 τ ⟨πE, EX.piG_K i⟩)
  have hτ' : ∀ τ, (recFields D).embC (recSeam D).σ₀ τ (star πE) = conj (D.host.φ₀ πE) := fun τ => by
    rw [hX.conjE, hτ]
  have hπ0 : (recFields D).conjO (EX.piG i) ≠ 0 :=
    right_ne_zero_of_mul (by rw [hPr.piG_norm i]; exact_mod_cast hp.ne_zero)
  have hcc' : (recFields D).conjO ((recFields D).conjO (EX.piG i)) = EX.piG i := Subtype.ext (star_star _)
  have hsplit : Formalism.L2.AlgTh.SplitS (ambOf (recSeam D) B χ cD) (Sall sel mu u) (D.host.g i) (D.host.φ₀ πE) (EX.piG i) := by
    refine ⟨hτ, hτ', fun P hP => ⟨fun hS h => ?_, fun h => hctx.2.2.2.2.2.2.2 P ?_⟩⟩
    · by_cases h' : (recFields D).conjO (EX.piG i) ∈ P.asIdeal
      · obtain ⟨x, y, hxy⟩ := hPr.piG_cop i
        exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ h')))
      · exact (notMem_of_split _ hctx hS h').2 hP
    · exact (P.isPrime.mem_or_mem ((hPr.piG_norm i).symm ▸ hP)).resolve_left h
  have hππ : D.host.φ₀ πE * conj (D.host.φ₀ πE) = (D.host.g i : ℂ) := by
    rw [← GlobalTheory.QuadSubfield.emb_conj, ← map_mul, EX.piG_norm i, map_natCast]
  refine datum_bound _ hctx hN hN' hA0 hB0 hg w _ Ξ hΞ hrat fun c' x hc0 hc' hx => hval _ ?_
  have key := hJ (recSeam D) B χ cD hs hcc hA.1 hA.2.1 _ b _ N N' (D.host.g i) ι (hev j) hb' hN hN' (hstd hN.1.fg hsN)
    (hstd hN'.1.fg hsN') hdisc hcD h5 hpd hctx.2.1 _ _ (isQInt_piG EX i) hππ hsplit c' x hc0 hc' hx e
  have hκ : (recSeam D).σ₀ (e.prod fun k n => (recFields D).emb k.1 (star πE) ^ n) = conj (D.host.φ₀ πE) ^ e.degree := by
    rw [map_finsuppProd, Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun k _ => by rw [map_pow]; exact congrArg (· ^ e k) (hτ' k.1)
  rw [map_mul (recSeam D).σ₀, map_mul (recSeam D).σ₀, hκ]
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  refine le_of_eq_of_le ?_ key
  rw [Fields.f, mul_right_comm (Fintype.card _)]
  exact (mul_comm _ _).trans ((congrArg _ (mul_comm _ _)).trans (mul_assoc _ _ _).symm)

end GlobalTheory.JetsFromTables
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaJetIntegralityTypePrimeOfSplitTableBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaJetIntegrality_typePrime_of_splitTableBound : JetSplitAmb → ∀ (D : D7) (EX : ErrX D) (sel : _) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : _) (cD : _), GlobalTheory.ColPeriod.JetLossAll D EX sel B χ cD := by
  first | exact @GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb | exact GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb | (intros; apply GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodBoundOfJetLoss
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsStdSplit
open NumberField IsDedekindDomain Matrix

noncomputable section

namespace GlobalTheory.ColPeriod

open _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.StdReps

theorem splitNonConj_vG {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (i : Fin 2) :
    GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj (Pr.vG i) := by
  intro P hP Q hQ h
  have h1 : cO X.E (Pr.piG i) ∈ Q.asIdeal := decoFin_mem_of_mem_divs hQ
  have h2 : cO X.E (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hP
  rw [h, mem_conjP, cO_cO] at h1
  obtain ⟨a, b, e⟩ := hPr.piG_cop i
  apply one_notMem P
  rw [← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem exists_std_split {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    (hST : GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit.SplitNonConj ST) {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    ∃ γ : UF E n, ∀ P ∈ ST, localization₂ P.asIdeal (gmap γ.1 N) = stdAt E n P ∧
      localization₂ (conjPrime₂ P).asIdeal (gmap γ.1 N) = stdAt E n (conjPrime₂ P) := by
  obtain ⟨g, hg, hc⟩ := exists_unitary_carries hST (by first | exact hN | exact hN.1)
  let f : Sp E n ≃ₗ[E] Sp E n := Matrix.toLin'OfInv (M := gᴴ) (M' := g) hg (mul_eq_one_comm.1 hg)
  have hf : ∀ x, f x = g *ᵥ x := fun x => rfl
  have hU : f ∈ UF E n := by
    intro x y
    rw [hf, hf, hStd_apply, hStd_apply]
    change star (g *ᵥ x) ⬝ᵥ (g *ᵥ y) = star x ⬝ᵥ y
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec]
  have huni : IsUnimodular (hStd E n) (gmap f N) := by
    have e : dual (hStd E n) N = N := hN.2
    change dual (hStd E n) (gmap f N) = gmap f N
    rw [dual_gmap f hU, e]
  refine ⟨⟨f, hU⟩, fun P hP => ?_⟩
  have h : localization₂ P.asIdeal (gmap f N) = stdAt E n P := by
    ext x
    rw [mem_localization_gmap, ← (hc P hP).2, ← hf, LinearEquiv.apply_symm_apply]
  exact ⟨h, le_antisymm (localization_conj_le_of_le stdLat_lattice.fg stdLat_unimodular huni h.ge)
    (localization_conj_le_of_le (gmap_lattice f N hN.1).fg huni stdLat_unimodular h.le)⟩

theorem stdMove : StdMove := by
  intro X Pr hPr i n N hN
  obtain ⟨γ, hγ⟩ := exists_std_split (splitNonConj_vG hPr i) hN
  refine ⟨γ, fun Q hQ => ?_⟩
  have h0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h1.symm)
  rw [← hPr.piG_norm i] at hQ
  rcases Q.isPrime.mem_or_mem hQ with h | h
  · have hm : conjPrime₂ Q ∈ Pr.vG i := (Formalism.L2.Col.mem_divs h0 _).2 (by
      change cO X.E (cO X.E (Pr.piG i)) ∈ Q.asIdeal
      rwa [cO_cO])
    have hcc : conjPrime₂ (conjPrime₂ Q) = Q := by
      ext x
      rw [mem_conjP, mem_conjP, cO_cO]
    have := (hγ _ hm).2
    rwa [hcc] at this
  · exact (hγ _ ((Formalism.L2.Col.mem_divs h0 _).2 h)).1

end GlobalTheory.ColPeriod
end
end

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound

section Val

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem vAdd_mul_of_ne {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy), neg_add]

theorem vAdd_pow_eq (x : K) (n : ℕ) : vAdd w (x ^ n) = n * vAdd w x := by
  unfold vAdd
  rw [map_pow, WithZero.log_pow]
  simp

theorem vAdd_prod_of_ne {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i, f i ≠ 0) :
    vAdd w (∏ i ∈ s, f i) = ∑ i ∈ s, vAdd w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vAdd]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, vAdd_mul_of_ne w (h a) (Finset.prod_ne_zero_iff.2 fun i _ => h i), ih]

theorem vAdd_nonneg_of_le {x : K} (hx : x ≠ 0) (h : w.valuation K x ≤ 1) : 0 ≤ vAdd w x := by
  unfold vAdd
  have := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hx) one_ne_zero).2 h
  rw [WithZero.log_one] at this
  omega

theorem mem_of_vAdd_pos {a : 𝓞 K} (h : 0 < vAdd w (a : K)) : a ∈ w.asIdeal := by
  by_contra hn
  have h1 : w.valuation K (a : K) = 1 := (w.valuation_eq_one_iff_notMem (K := K)).2 hn
  rw [vAdd, h1, WithZero.log_one] at h
  omega

end Val

theorem sum_nuW_nonneg {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {j : ℕ} (hj : j < R.m)
    (τ : X.Tau) : 0 ≤ ∑ a, (W.nuW u (j + 1) τ).w a := by
  obtain ⟨s, s', ⟨h1, h2, -⟩, h3⟩ := chainWeights X Pr R W u j hj
  refine Finset.sum_nonneg fun a _ => ?_
  have h4 := (W.lamTrue u (j + 1) τ).anti (show Fin.castLE (N_lt_succ R j).le a ≤ ⟨R.N j, N_lt_succ R j⟩ from a.2.le)
  rw [h2 τ _ le_rfl] at h4
  rw [← h3, ← h1]
  omega

theorem recWts_ok {D : D7} (EX : ErrX D) : (recWts EX).Ok := by
  exact
    { row_ok τ := ⟨D.hc τ, rfl⟩
      hc_row := recWts_row EX
      u_first u u' τ h := (D.hcW_first u τ h).trans (D.hcW_first u' τ h).symm
      u_last u u' τ h := (D.hcW_last u τ (by omega)).trans (D.hcW_last u' τ (by omega)).symm }

theorem emb_star_piG {D : D7} (EX : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) :
    (recFields D).emb τ (@star _ (recFields D).starE.toStar (((recPrimes EX).piG i : 𝓞 D.host.E) : D.host.E)) = tauPib EX i τ := by
  have h : ∀ x : D.host.E, @star _ (recFields D).starE.toStar x = D.host.conj x := fun x => by
    apply D.host.φ₀.injective
    let _ := D.host.isCMField_hostE
    change D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm
  rw [h]
  rfl

theorem vG_loss_le {D : D7} (L : SizeData₂ D) (EX : ErrX D) (hPr : (recPrimes EX).Ok) (i : Fin 2) (w : LiftErrorLocal.Pl D)
    (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) :
    (∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j ≠ 0) ∧
    LiftErrorLocal.vG D w (∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) ≤
      (∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) + LiftErrorLocal.errC D L := by
  have hg0 : (D.host.g i : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero
  have hπ : ∀ τ, tauPib EX i τ ≠ 0 := by
    intro τ h
    have h1 : (recFields D).emb τ (((recFields D).conjO (EX.piG i) : 𝓞 D.host.E) : D.host.E) = 0 :=
      (emb_star_piG EX i τ).trans h
    have h2 : (recFields D).conjO (EX.piG i) = 0 := RingOfIntegers.ext ((map_eq_zero _).1 h1)
    have h3 := hPr.piG_norm i
    change EX.piG i * (recFields D).conjO (EX.piG i) = _ at h3
    rw [h2, mul_zero] at h3
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h3.symm)
  have e : ∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j = (D.host.g i : D.what₂.LL) ^ (D.R.f * D.R.N j * D.R.N (j + 1)) *
      ∏ τ, tauPib EX i τ ^ (∑ a, ((recWts EX).nuW u (j + 1) τ).w a).toNat := fun j => by
    rw [← D.what₂.card_Tau]
    simp only [← emb_star_piG]
    rfl
  have hne : ∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j ≠ 0 := fun j => by
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ hg0) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hπ τ))
  refine ⟨hne, ?_⟩
  have hw' : D.what₂.places.resChar w = D.host.g i := hw
  have hvg : vAdd (D.plEq w) (D.host.g i : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
    have h1 := D.what₂.places.val_resChar w
    rw [hw', D.val_eq w _ hg0] at h1
    exact_mod_cast h1
  have he : (0 : ℝ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h1 : ∀ j ∈ Finset.range D.R.m, (vAdd (D.plEq w) (lossAt (Pr := recPrimes EX) (recWts EX) i u j) : ℝ) / D.what₂.places.ramIdx w ≤
      vNN EX i u (1 + j) w + D.R.f * (D.R.N D.R.m * (D.R.N D.R.m + D.R.t)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have h2 : (D.R.f : ℝ) * D.R.N j * D.R.N (j + 1) ≤ D.R.f * D.R.N D.R.m * (D.R.N D.R.m + D.R.t) := by
      exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.exp_le D j hj'
    have h3 : ∀ τ, (((∑ a, ((recWts EX).nuW u (j + 1) τ).w a).toNat : ℕ) : ℝ) = nuAbs D u (1 + j) τ := fun τ => by
      rw [add_comm 1 j, partitionSize D EX u j hj' τ, ← Int.cast_natCast,
        Int.toNat_of_nonneg (sum_nuW_nonneg (Pr := recPrimes EX) (recWts EX) u hj' τ)]
    rw [e, vAdd_mul_of_ne _ (pow_ne_zero _ hg0) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hπ τ)),
      vAdd_prod_of_ne _ _ _ fun τ => pow_ne_zero _ (hπ τ)]
    simp only [vAdd_pow_eq, hvg]
    push_cast
    simp only [h3]
    rw [add_div, mul_div_assoc, div_self he.ne', mul_one, vNN]
    linarith
  have h4 : 0 ≤ (D.R.f : ℝ) * ((D.R.m : ℝ) ^ 3 * L.etaSz) := by
    have := L.etaSz_pos.le
    positivity
  unfold LiftErrorLocal.vG
  rw [vAdd_prod_of_ne _ _ _ hne, Int.cast_sum, Finset.sum_div]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, LiftErrorLocal.lifts, LiftErrorLocal.errC,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  nlinarith

end GlobalTheory.ColPeriod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationBoundTypePrimePlaceOfChainAgreeme
noncomputable section

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker GlobalTheory.AtG
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound GlobalTheory.ColPeriod

namespace GlobalTheory.ColPeriodTies

theorem boundAt_of_chainTie (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D)
    (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
    (eta : Formalism.L2.Host.HChar D.host.E) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (C1 : ℝ)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.Integrality) (hJ : JetLossAll D EX sel B χ cD) (hC : 1 ≤ C1)
    (hH : HostTie EX) (hCT : CharTie Ch mu0 eta sel) (hA : AnTie D δ χ cD) (i : Fin 2) (hS : SizeAt D i)
    (w : LiftErrorLocal.Pl D) (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hCh : ChainTie Ch sel Dx mu0 (ambOf (recSeam D) B χ cD) u μ) :
    BoundAt L EX C1 i w u μ := by
  classical
  obtain ⟨-, hTied, -, hsel⟩ := hCT
  obtain ⟨ξ, cst, I, hI, b, hY, hK, hF, hP, eM, jA, -, -, hrat, hcol, hrow, hper⟩ := hCh
  rintro φ hφ F ⟨c, hc⟩
  have hX := hH.2.2.2.1.ok
  have hPr := hH.2.2.2.2
  obtain ⟨hne, hloss⟩ := vG_loss_le L EX hPr i w hw u
  choose! x hx using hrow.2.2.1
  have hxF : jA (∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.OtoLL (c v) • x v) = F := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, map_sum]
    exact Finset.sum_congr rfl fun v hv => by rw [LinearMap.map_smulₛₗ, hx v hv]; rfl
  have hxM := (hrow.2.2.2 _).2 ⟨fun v => ⟨D.what₂.OtoLL (c v), D.O_int _⟩, hxF.trans hc⟩
  refine ⟨_, (hxF ▸ hper φ _).symm, ?_⟩
  have hw' : D.what₂.places.resChar w = D.host.g i := hw
  have hg : ((D.host.g i : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
    refine mem_of_vAdd_pos _ ?_
    have h1 := D.what₂.places.val_resChar w
    rw [hw', D.val_eq w _ (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero)] at h1
    have h2 : vAdd (D.plEq w) (D.host.g i : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by exact_mod_cast h1
    have h3 : (((D.host.g i : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = (D.host.g i : D.what₂.LL) := map_natCast (algebraMap _ _) _
    rw [h3, h2]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hTS : (recPrimes EX).T u ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)
  have hgS : ∀ k, (recPrimes EX).g k ∈ badS D := fun k => by
    fin_cases k <;> simp [badS, hostS]
  have hb : 2 * (recFields D).f * D.R.N D.R.m + 1 < D.host.g i := by
    rw [show (recFields D).f = D.R.f from D.what₂.card_Tau]
    exact hS.1
  have hdeg : ∀ j < D.R.m, (∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a) + 1 < (D.host.g i : ℤ) := by
    intro j hj
    have h1 := (hS.2 u (j + 1) (Finset.mem_Icc.2 ⟨by omega, hj⟩)).1
    have h2 : LiftErrorLocal.Dpi D u (j + 1) = ((∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun τ _ => partitionSize D EX u j hj τ
    have h3 := Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => sum_nuW_nonneg (Pr := recPrimes EX) (recWts EX) u hj τ
    rw [h2] at h1
    have h4 : 2 * (∑ τ, ∑ a, ((recWts EX).nuW u (j + 1) τ).w a) + 2 < (D.host.g i : ℤ) := by exact_mod_cast h1
    omega
  have hcolb := colMu_bound_all (recWts EX) Ch sel ξ cst I _ (hJ hH hsel hA) GlobalTheory.JetOpWeylLat.jetOpWeyl chainWeights stdMove levelPrimes
    (scalarUnit_of levelPrimes heckeUnit twistUnit) entryAtG (EntQ.entryAtQ volumeAtQ) TopTwist.topAtQ hX hPr hsel u hTS hgS hI
    hTied b hY (Formalism.L2.Col.rPsymF Ch) hK hF i (D.plEq w) hg
    (fun j hj b' => wtUnit_chF (recWts EX) sel ξ I hX u hF (hPr.g_prime i) hb _ hg hj b') hdeg hrat _ ((hcol φ).1 hφ)
  have hm := GlobalTheory.BranchMembers.members _ _ _ (recWts EX) (recWts_ok EX) u
  have hval := valuation_PtilE_le_one (recWts EX) Ch sel ξ hX hPr hsel u hTS (hB _ _ _ _ _ _ _) (fun τ => (hm τ).1)
    (fun τ => (hm τ).2) (Formalism.L2.Col.rPsymF Ch) hP (hPr.g_prime i) (hPr.T_ne_g u i) hb (D.plEq w) hg
    ((∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) • _) hcolb _ hxM
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hval
  suffices key : ∀ y : D.what₂.LL, (D.plEq w).valuation D.what₂.LL
      ((∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) * y) ≤ 1 →
      y = 0 ∨ -(∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) - C1 * LiftErrorLocal.errC D L ≤ LiftErrorLocal.vG D w y from key _ hval
  intro y hval
  by_cases hy : y = 0
  · exact Or.inl hy
  right
  have hc0 := Finset.prod_ne_zero_iff.2 fun j (_ : j ∈ Finset.range D.R.m) => hne j
  have h1 := vAdd_nonneg_of_le _ (mul_ne_zero hc0 hy) hval
  rw [vAdd_mul_of_ne _ hc0 hy] at h1
  have he : (0 : ℝ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h2 : 0 ≤ LiftErrorLocal.vG D w (∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) + LiftErrorLocal.vG D w y := by
    unfold LiftErrorLocal.vG
    rw [← add_div]
    exact div_nonneg (by exact_mod_cast h1) he.le
  have h3 : 0 ≤ LiftErrorLocal.errC D L := by
    have := L.etaSz_pos.le
    unfold LiftErrorLocal.errC
    positivity
  nlinarith

theorem boundAt_of_ties : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup),
    TiesAt D EX Dx μ → ∀ i : Fin 2, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i → ∀ w, LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word,
      D.what₂.places.resChar w ≠ (D.mem u).A.T → GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.BoundAt L EX 1 i w u μ := by
  intro hJS D L EX Dx μ ⟨Ch, mu0, eta, sel, δ, B, χ, cD, hH, hCT, hA, hCh⟩ i hS w hw u _
  have hJ : JetLossAll D EX sel B χ cD := GlobalTheory.T.thetaJetIntegrality_typePrime_of_splitTableBound hJS D EX sel δ B χ cD
  exact boundAt_of_chainTie D L EX Dx Ch mu0 eta sel B χ cD 1
    (GlobalTheory.BranchFormula.integrality Formalism.L2.DIV.BrJ.branching_interlacing_pairs) hJ le_rfl
    hH hCT hA i hS w hw u μ (hCh u)

end GlobalTheory.ColPeriodTies

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationBoundTypePrimePlaceOfChainAgreemeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodValuationBound_typePrimePlace_of_chainAgreement : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup), TiesAt D EX Dx μ → ∀ i : Fin 2, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i → ∀ w, LiftErrorLocal.Over D i w → ∀ u : D.what₂.Word, D.what₂.places.resChar w ≠ (D.mem u).A.T → GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.BoundAt L EX 1 i w u μ := by
  first | exact @GlobalTheory.ColPeriodTies.boundAt_of_ties | exact GlobalTheory.ColPeriodTies.boundAt_of_ties | (intros; apply GlobalTheory.ColPeriodTies.boundAt_of_ties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundConstantOneOfChainAgreement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

namespace GlobalTheory.AtG

theorem jetTableBound_constantOne_of_chainAgreement : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D),
    (∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D EX Dx μ) → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i) →
    Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant D L EX 1 := by
  intro hJ D L EX Dx hT hS i w hw u hu μ hμ
  exact GlobalTheory.T.periodValuationBound_typePrimePlace_of_chainAgreement hJ D L EX Dx μ (hT μ hμ) i (hS i) w hw u hu

end GlobalTheory.AtG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundConstantOneOfChainAgreementStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.propositionCOneUsedTuples_one_of_tiesAt_sizeAt : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D), (∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D EX Dx μ) → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i) → Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant D L EX 1 := by
  first | exact @GlobalTheory.AtG.jetTableBound_constantOne_of_chainAgreement | exact GlobalTheory.AtG.jetTableBound_constantOne_of_chainAgreement | (intros; apply GlobalTheory.AtG.jetTableBound_constantOne_of_chainAgreement <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDegreesSmallAgainstTypePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDegreesSmallAgainstTypePrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

noncomputable section

namespace GlobalTheory.AtG.KernelSizes

variable {D : D7} {L : SizeData₂ D}

theorem key_ineq (A N Y : ℝ) (hA : 10 ≤ A) (hN : 2 ≤ N) (h1 : A ^ 8 ≤ Y) (h2 : N ^ 16 ≤ Y) :
    6 * A ^ 2 * N + 2 < Y := by
  have hA1 : 1 ≤ A := by linarith
  by_cases h : N ≤ A ^ 5
  · have hA7 : 1 ≤ A ^ 7 := one_le_pow₀ hA1
    have e1 : 6 * A ^ 2 * N ≤ 6 * A ^ 7 := by
      have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 6 * A ^ 2)
      calc 6 * A ^ 2 * N ≤ 6 * A ^ 2 * A ^ 5 := this
        _ = 6 * A ^ 7 := by ring
    have e2 : A ^ 8 = A * A ^ 7 := by ring
    have e3 : 10 * A ^ 7 ≤ A * A ^ 7 := mul_le_mul_of_nonneg_right hA (by positivity)
    linarith
  · push_neg at h
    have hA25 : A ^ 2 ≤ A ^ 5 := pow_le_pow_right₀ hA1 (by norm_num)
    have hAN : A ^ 2 < N := lt_of_le_of_lt hA25 h
    have e1 : 6 * A ^ 2 * N < 6 * N * N := by nlinarith
    have hN14 : 8 ≤ N ^ 14 := by
      have : (2 : ℝ) ^ 14 ≤ N ^ 14 := pow_le_pow_left₀ (by norm_num) hN 14
      linarith
    have e2 : N ^ 16 = N ^ 2 * N ^ 14 := by ring
    have e3 : N ^ 2 * 8 ≤ N ^ 2 * N ^ 14 := mul_le_mul_of_nonneg_left hN14 (by positivity)
    nlinarith

theorem exists_Y (P : ParameterChoice' D L) :
    ∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧ (D.R.N D.R.m : ℝ) ^ 16 ≤ Y ∧ ∀ i, Y ≤ (D.host.g i : ℝ) := by
  obtain ⟨Y, h1, h2, -, h4⟩ := P.g_Y
  have hx0 : (0 : ℝ) < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hq : (0 : ℝ) < D.host.q := lt_trans (Real.rpow_pos_of_pos hx0 _) P.qd_pow.1
  have hd : (0 : ℝ) < D.host.d := lt_trans (Real.rpow_pos_of_pos hx0 _) P.qd_pow.2
  have hq1 : (1 : ℝ) ≤ D.host.q := by
    have : 0 < D.host.q := by exact_mod_cast hq
    exact_mod_cast this
  have hd1 : (1 : ℝ) ≤ D.host.d := by
    have : 0 < D.host.d := by exact_mod_cast hd
    exact_mod_cast this
  have hQ1 : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hc : (1 : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by
    unfold LevelStarExponents.condE
    push_cast
    calc (1 : ℝ) ≤ 1 * 1 * 1 := by norm_num
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by gcongr
  have hcC : 1 ≤ (LevelStarExponents.condE D : ℝ) ^ P.CY := Real.one_le_rpow hc P.CY_pos.le
  have hY0 : 0 ≤ Y := le_trans (by positivity) h1
  have hN4 : (D.R.N D.R.m : ℝ) ^ 4 ≤ Y ^ ((1 : ℝ) / 4) := by
    have hN : 0 ≤ (D.R.N D.R.m : ℝ) ^ 4 := by positivity
    nlinarith
  refine ⟨Y, h1, ?_, fun i => (h4 i).1⟩
  have h5 : ((D.R.N D.R.m : ℝ) ^ 4) ^ 4 ≤ (Y ^ ((1 : ℝ) / 4)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hN4 4
  have h6 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y := by
    rw [← Real.rpow_natCast (Y ^ ((1 : ℝ) / 4)), ← Real.rpow_mul hY0]
    norm_num
  rw [h6] at h5
  calc (D.R.N D.R.m : ℝ) ^ 16 = ((D.R.N D.R.m : ℝ) ^ 4) ^ 4 := by ring
    _ ≤ Y := h5

theorem nuAbs_le (P : ParameterChoice' D L) (u : D.what₂.Word) (j : ℕ) (hj : j ∈ LiftErrorLocal.lifts D) (τ : D.what₂.Tau) :
    nuAbs D u j τ ≤ (D.R.N D.R.m : ℝ) * (3 * L.sc.a) := by
  unfold LiftErrorLocal.lifts at hj
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := by omega
  have hb : ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b' := fun t => by
    have := P.bT_le' t
    have := GlobalTheory.CoreHt.RowsRange.b'_pos L
    linarith
  have hT : GlobalTheory.CoreHt.ThickUp L := fun j h1 h2 τ hc => (L.win_thick j h1 h2 τ hc).2
  have ha : 0 ≤ L.sc.a := by
    unfold Scale.a
    have := GlobalTheory.CoreHt.RowsRange.one_le_b L
    have := L.sc.one_lt_alt
    positivity
  have hrow : ∀ r ∈ Finset.range (D.R.N (i + 1 - 1)), DV.nuRow D u (i + 1) τ r ≤ 3 * L.sc.a := by
    intro r hr
    rw [Finset.mem_range, Nat.add_sub_cancel] at hr
    exact (RowWeightLemmas.nuRow_anti' D u i hi τ r 0 (Nat.zero_le _) hr).trans
      (GlobalTheory.CoreHt.RowsRange.nuRow_zero_le_three_mul L P hb hT u i hi τ)
  unfold nuAbs
  have hs := Finset.sum_le_card_nsmul _ _ _ hrow
  rw [Finset.card_range, nsmul_eq_mul, Nat.add_sub_cancel] at hs
  have hNi : (D.R.N i : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.N i ≤ D.R.N D.R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right (D.R.t + 1) hi.le
      omega
    exact_mod_cast this
  rw [Nat.add_sub_cancel]
  calc _ ≤ (D.R.N i : ℝ) * (3 * L.sc.a) := hs
    _ ≤ _ := mul_le_mul_of_nonneg_right hNi (by positivity)

theorem Dpi_le (P : ParameterChoice' D L) (u : D.what₂.Word) (j : ℕ) (hj : j ∈ LiftErrorLocal.lifts D) :
    LiftErrorLocal.Dpi D u j ≤ (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * (3 * L.sc.a)) := by
  unfold LiftErrorLocal.Dpi
  have hs := Finset.sum_le_card_nsmul (Finset.univ : Finset D.what₂.Tau) (fun τ => nuAbs D u j τ) _
    (fun τ _ => nuAbs_le P u j hj τ)
  rw [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at hs
  exact hs

theorem sizeAt_of_params : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L →
    Formalism.MainNotions.SizesAt L → L.sc.eps = eps → x0 ≤ L.sc.x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i := by
  intro eps _ _
  refine ⟨0, fun D L P hS _ _ i => ?_⟩
  obtain ⟨Y, hY1, hY2, hY3⟩ := exists_Y P
  have hx1 := L.sc.one_lt_alt
  have hk5 : (5 : ℝ) ≤ D.R.k := P.five_le_k
  have hb2 : 2 ≤ L.sc.b := by
    have h1 := GlobalTheory.CoreHt.RowsRange.one_le_scL L
    have h2 := Real.add_one_le_exp L.sc.L
    unfold Scale.b
    linarith
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by
    have : D.R.f ≤ D.R.k := D.R.f_le_k
    exact_mod_cast this
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hNk : (D.R.k : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this

  have hxk : L.sc.x ≤ D.R.k := by
    have hK := hS.2.2.1.1
    have he : (1 : ℝ) ≤ 9 / 2 + 10 * L.sc.eps - szTh L := by
      unfold szTh
      linarith [L.sc.eps_pos, L.sc.eps_lt]
    have := Real.rpow_le_rpow_of_exponent_le hx1.le he
    rw [Real.rpow_one] at this
    linarith
  have hak : L.sc.a ≤ D.R.k * L.sc.b := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right hxk (by linarith)
  set A : ℝ := (D.R.k : ℝ) * L.sc.b with hA
  set N : ℝ := (D.R.N D.R.m : ℝ) with hN
  have hA10 : 10 ≤ A := by rw [hA]; nlinarith
  have hN2 : 2 ≤ N := by linarith
  have hkey := key_ineq A N Y hA10 hN2 hY1 hY2
  have hkA : (D.R.k : ℝ) ^ 2 * L.sc.b ≤ A ^ 2 := by
    rw [hA]
    have : (D.R.k : ℝ) ^ 2 * L.sc.b * 1 ≤ (D.R.k : ℝ) ^ 2 * L.sc.b * L.sc.b :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith

  have hD : ∀ u : D.what₂.Word, ∀ j ∈ LiftErrorLocal.lifts D, LiftErrorLocal.Dpi D u j ≤ 3 * A ^ 2 * N := by
    intro u j hj
    have h1 := Dpi_le P u j hj
    have hN0 : 0 ≤ N := by linarith
    have h2 : (D.R.f : ℝ) * (N * (3 * L.sc.a)) ≤ (D.R.k : ℝ) * (N * (3 * (D.R.k * L.sc.b))) := by
      apply mul_le_mul hfk _ (by have := GlobalTheory.CoreHt.RowsRange.one_le_b L; unfold Scale.a; positivity) (by linarith)
      exact mul_le_mul_of_nonneg_left (by linarith) hN0
    have h3 : (D.R.k : ℝ) * (N * (3 * (D.R.k * L.sc.b))) = 3 * ((D.R.k : ℝ) ^ 2 * L.sc.b) * N := by ring
    have h4 : 3 * ((D.R.k : ℝ) ^ 2 * L.sc.b) * N ≤ 3 * A ^ 2 * N := by
      have := mul_le_mul_of_nonneg_left hkA (by norm_num : (0 : ℝ) ≤ 3)
      exact mul_le_mul_of_nonneg_right this hN0
    linarith
  have hg := hY3 i
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  refine ⟨?_, fun u j hj => ?_⟩
  · have h1 : (2 * D.R.f * D.R.N D.R.m + 1 : ℝ) < D.host.g i := by
      have : (2 : ℝ) * D.R.f * N ≤ 2 * (3 * A ^ 2 * N) := by
        have : (D.R.f : ℝ) ≤ 3 * A ^ 2 := by nlinarith
        nlinarith
      linarith
    exact_mod_cast h1
  · have h := hD u j hj
    constructor
    · linarith
    · nlinarith

end GlobalTheory.AtG.KernelSizes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDegreesSmallAgainstTypePrimesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDegrees_small_against_typePrimes : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → Formalism.MainNotions.SizesAt L → L.sc.eps = eps → x0 ≤ L.sc.x → ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i := by
  first | exact @GlobalTheory.AtG.KernelSizes.sizeAt_of_params | exact GlobalTheory.AtG.KernelSizes.sizeAt_of_params | (intros; apply GlobalTheory.AtG.KernelSizes.sizeAt_of_params <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimePeriodRowOfConstructedPointChains
noncomputable section

namespace GlobalTheory.AtG

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

theorem row_atG_of_jetSplitAmb : JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd),
    RowE Q Lk (fun _ D O _ _ => ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D O.ex.errX O.X μ) →
    Row Q Lk fun 𝒜 _ => Closed (W3 𝒜) fun Fm _ => ∃ C1, (∃ x0, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 := by
  intro hJ Bd Q Lk hE
  refine ⟨_, hE, fun 𝒜 σ s => ?_⟩
  refine ⟨1 / 100, by norm_num, fun eps he hle => ?_⟩
  obtain ⟨xs, hxs⟩ := GlobalTheory.T.kernelDegrees_small_against_typePrimes eps he (by linarith)
  refine ⟨⟨0, fun _ => 0, fun _ => 2, fun _ => 0⟩, fun Fm CH hc hL => ?_⟩
  have hg : (2 : ℝ) ≤ Fm.cX.err.g := hL.2.2.1 Fm.cX.err.g (by simp [FamP.cMid])
  obtain ⟨κ, -, -, t⟩ := s Fm (w3_a hc)
  refine ⟨1, ⟨xs, fun x hx hx0 i => ?_⟩, Formalism.MainNotions.J.family_type_prime_loss Fm zero_le_one (by linarith)⟩
  refine GlobalTheory.T.propositionCOneUsedTuples_one_of_tiesAt_sizeAt hJ (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX (Fm.X x i) (t x hx i).2 ?_
  exact hxs (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i) (Fm.L_eps x i) (by rw [Fm.L_x x i hx]; exact hx0)

end GlobalTheory.AtG

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimePeriodRowOfConstructedPointChainsStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimePeriodRow_of_constructedPointChains : JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), RowE Q Lk (fun _ D O _ _ => ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D O.ex.errX O.X μ) → Row Q Lk fun 𝒜 _ => Closed (W3 𝒜) fun Fm _ => ∃ C1, (∃ x0, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i, Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 := by
  first | exact @GlobalTheory.AtG.row_atG_of_jetSplitAmb | exact GlobalTheory.AtG.row_atG_of_jetSplitAmb | (intros; apply GlobalTheory.AtG.row_atG_of_jetSplitAmb <;> assumption)
end
