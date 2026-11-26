module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.ThetaMove
  GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.ThetaMove.LatticeFacts

theorem exp_pi_int (b : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))
    = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))) := by
  have h : (Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ)
      = -((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ)) + (b : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  congr 1
  push_cast; ring

theorem al_sign (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T x = 1 ∨ TaylorLogMetric.al D T x = -1 := by
  unfold TaylorLogMetric.al
  rcases Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D T x x).re)) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem latAll {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.LatAll := by
  have h0 : δ ≠ 0 := delta_ne_zero B
  refine ⟨fun N N' L L' hA => ⟨?_, fun x _ => al_sign D _ x, ?_⟩, fun N N' L₁ L₁' L₂ L₂' h₁ h₂ =>
    ⟨IO.La_index_ne_zero cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂, IO.La_index_ne_zero cc hcc δ L₂ L₁ L₂' L₁' h₂ h₁⟩⟩
  · have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
    apply le_antisymm
    · intro v hv
      exact self_dual_lattice D cc hcc δ hδ h0 N N' L L' hA v (fun y hy => hv y hy)
    · intro v hv y hy
      obtain ⟨a, b, -, hab⟩ := hI v hv y hy
      refine ⟨b, ?_⟩
      show (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) v y).im = (b : ℝ)
      rw [hab]; simp
  · intro x hx y hy
    have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
    have hs := IO.semiChar_of_HfInt _ hI x hx y hy
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    have him : (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im = (b : ℝ) := by rw [hab]; simp
    rw [hs]
    congr 1
    show Complex.exp (-((Real.pi : ℂ) * Complex.I * (((TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im : ℝ) : ℂ)))
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (((TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im : ℝ) : ℂ))
    rw [him]; exact (exp_pi_int b).symm

theorem laHyp_and_eSmooth : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.VecP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b := by
  intro D X s cc δ B χ cD a b hX hs hcc hδ hV ha hb
  have hL := latAll B hcc hδ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hV a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hV a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.ThetaMove.LatticeFacts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmoothStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_latticeHyp_and_smooth : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.VecP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b := by
  first | exact @GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth | exact GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth | (intros; apply GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLiftHalfLatticeRational
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLiftHalfLatticeRational
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT

theorem natCast_smul_eq_ring {E : Type} [Field E] [NumberField E] {a b : ℕ} (n : ℕ) (y : HomE E a b) :
    (n : 𝓞 E) • y = (n : E) • y := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem natCast_smul_mem {E : Type} [Field E] [NumberField E] {a b : ℕ} (M : Submodule (𝓞 E) (HomE E a b)) (n : ℕ)
    {y : HomE E a b} (hy : y ∈ M) : (n : E) • y ∈ M := by
  rw [← natCast_smul_eq_ring]; exact M.smul_mem _ hy

theorem exists_lift_halfAO : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), A.AA.FG → A.AA ≠ ⊥ → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∀ x ∈ divLat cA (homAt S N N'), ∃ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') := by
  intro X A a b S N N' cA c hfg hne _ hU hN hN' hcA hc x hx
  obtain ⟨-, hfull, -, hloc⟩ := GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hfg hne hN hN'
  have hF : GlobalTheory.ThetaMove.Full (per A N N') := fun y => by
    obtain ⟨n, hn, hy⟩ := hfull y
    exact ⟨n, hn, by rwa [natCast_smul_eq_ring]⟩
  have hD : ((cA * c : ℕ) : X.E) ≠ 0 := by exact_mod_cast (Nat.mul_pos hcA hc).ne'
  obtain ⟨t, h1, h2⟩ := hF.approx S (((cA * c : ℕ) : X.E)⁻¹ • x)
  have hx' : (cA : X.E) • x ∈ homAt S N N' := by
    rw [← natCast_smul_eq_ring]; exact hx
  refine ⟨((cA * c : ℕ) : X.E) • t, ?_, (cA : X.E) • (t - ((cA * c : ℕ) : X.E)⁻¹ • x), ?_, ?_⟩
  · unfold halfAO twist₂
    rw [Submodule.mem_iInf]
    intro Q
    rw [Submodule.mem_comap]
    change ((((cA * c : ℕ) : X.E) ^ (-expS S Q))⁻¹ • ((cA * c : ℕ) : X.E) • t) ∈ _
    unfold expS
    split_ifs with hQ hQ'
    · have e : ((((cA * c : ℕ) : X.E) ^ (-(1 : ℤ)))⁻¹ • ((cA * c : ℕ) : X.E) • t) =
          ((cA * c : ℕ) : X.E) • ((cA * c : ℕ) : X.E) • (t - ((cA * c : ℕ) : X.E)⁻¹ • x) + (c : X.E) • (cA : X.E) • x := by
        rw [smul_sub, smul_inv_smul₀ hD, smul_sub, zpow_neg, inv_inv, zpow_one, smul_smul (c : X.E), mul_comm (c : X.E),
          ← Nat.cast_mul, sub_add_cancel]
      rw [e]
      exact add_mem (natCast_smul_mem _ _ (natCast_smul_mem _ _ (h1 Q hQ)))
        (natCast_smul_mem _ _ ((hloc Q (hU Q hQ) _).2 (hx' Q hQ)))
    · rw [neg_neg, zpow_one, inv_smul_smul₀ hD]
      exact h2 Q hQ
    · rw [neg_zero, zpow_zero, inv_one, one_smul]
      exact natCast_smul_mem _ _ (h2 Q hQ)
  · intro P hP
    exact (hloc P (hU P hP) _).1 (natCast_smul_mem _ _ (h1 P hP))
  · change (c : 𝓞 X.E) • (cA : X.E) • (t - ((cA * c : ℕ) : X.E)⁻¹ • x) = _
    rw [natCast_smul_eq_ring, smul_smul, mul_comm (c : X.E), ← Nat.cast_mul, smul_sub, smul_inv_smul₀ hD]

end GlobalTheory.MomT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLiftHalfLatticeRationalStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_halfLattice_rational : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), A.AA.FG → A.AA ≠ ⊥ → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∀ x ∈ divLat cA (homAt S N N'), ∃ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') := by
  first | exact @GlobalTheory.MomT.exists_lift_halfAO | exact GlobalTheory.MomT.exists_lift_halfAO | (intros; apply GlobalTheory.MomT.exists_lift_halfAO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodLatticeHalfLatticeInclusionsSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodLatticeHalfLatticeInclusionsSplitPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.HalfIncl

section Loc

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

theorem mem_of_loc {M : Submodule (𝓞 E) W} {x : W} (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  have hne : M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) ≠ ⊤ := fun e => hx (by
    have : (1 : 𝓞 E) ∈ M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
  exact hs (hle (by simpa using hsx))

theorem loc_self (Q : HeightOneSpectrum (𝓞 E)) {M : Submodule (𝓞 E) W} {x : W} (hx : x ∈ M) : x ∈ localization₂ Q.asIdeal M :=
  ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩

variable [Module E W] [IsScalarTower (𝓞 E) E W]

theorem loc_smul {Q : HeightOneSpectrum (𝓞 E)} {M : Submodule (𝓞 E) W} {x : W} {k k' : E}
    (hx : k' • x ∈ localization₂ Q.asIdeal M) (r s : 𝓞 E) (hs : s ∉ Q.asIdeal) (h : (s : E) * k = (r : E) * k') :
    k • x ∈ localization₂ Q.asIdeal M := by
  obtain ⟨t, ht, hx⟩ := hx
  refine ⟨t * s, Q.asIdeal.primeCompl.mul_mem ht hs, ?_⟩
  have : (t * s) • k • x = r • t • k' • x := by
    simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_mul]
    congr 1
    have h' : algebraMap (𝓞 E) E s * k = algebraMap (𝓞 E) E r * k' := h
    linear_combination (algebraMap (𝓞 E) E t) * h'
  rw [this]
  exact M.smul_mem _ hx

theorem loc_smul' {Q : HeightOneSpectrum (𝓞 E)} {M : Submodule (𝓞 E) W} {x : W} {k : E}
    (hx : x ∈ localization₂ Q.asIdeal M) (r s : 𝓞 E) (hs : s ∉ Q.asIdeal) (h : (s : E) * k = (r : E)) :
    k • x ∈ localization₂ Q.asIdeal M :=
  loc_smul (k' := 1) (by rwa [one_smul]) r s hs (by rwa [mul_one])

theorem mem_twO (M : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : W) :
    y ∈ twist₂ M c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ localization₂ Q.asIdeal M := by
  simp [twist₂, Submodule.mem_iInf]

theorem mem_mulLat (M : Submodule (𝓞 E) W) {c : ℕ} (hc : c ≠ 0) (y : W) :
    y ∈ mulLat c M ↔ (c : E)⁻¹ • y ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc
  have e : ∀ m : W, (c : 𝓞 E) • m = (c : E) • m := fun m => by
    rw [← algebraMap_smul E, map_natCast]
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [e, smul_smul, hcE] using hm
  · intro h
    exact ⟨_, h, by simp [e, smul_smul, hcE]⟩

theorem nat_notMem {Q : HeightOneSpectrum (𝓞 E)} {n p : ℕ} (h : Nat.Coprime n p) (hp : (p : 𝓞 E) ∈ Q.asIdeal) :
    (n : 𝓞 E) ∉ Q.asIdeal := fun hn => by
  obtain ⟨u, v, huv⟩ : IsCoprime (n : 𝓞 E) (p : 𝓞 E) := h.cast
  exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left _ hn) (Q.asIdeal.mul_mem_left _ hp)))

theorem exists_prime_over {p : ℕ} (hp : p.Prime) : ∃ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal := by
  have hu : ¬ IsUnit (p : 𝓞 E) := fun h => by
    have : IsUnit (p : ℤ) := isUnit_of_map_unit (algebraMap ℤ (𝓞 E)) _ (by simpa using h)
    exact hp.one_lt.ne' (by simpa [Int.isUnit_iff_natAbs_eq] using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 E)}) (by simpa [Ideal.span_singleton_eq_top] using hu)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩,
    hle (Ideal.mem_span_singleton_self _)⟩

theorem expS_conj [StarRing E] {S : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ P ∈ S, conjPrime₂ P ∉ S)
    (Q : HeightOneSpectrum (𝓞 E)) : expS S (conjPrime₂ Q) = -expS S Q := by
  unfold expS
  rw [GlobalTheory.CharValCompare.conjP_conjP]
  by_cases h1 : Q ∈ S
  · simp [h1, hS Q h1]
  · by_cases h2 : conjPrime₂ Q ∈ S <;> simp [h1, h2]

theorem expS_cases [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) :
    (Q ∈ S ∧ expS S Q = 1) ∨ (Q ∉ S ∧ conjPrime₂ Q ∈ S ∧ expS S Q = -1) ∨ (Q ∉ S ∧ conjPrime₂ Q ∉ S ∧ expS S Q = 0) := by
  unfold expS
  by_cases h1 : Q ∈ S
  · simp [h1]
  · by_cases h2 : conjPrime₂ Q ∈ S <;> simp [h1, h2]

end Loc

theorem half_inclusions : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Ctx A a b S SG ϖ p g cA → IsSdLat N → IsSdLat N' → A.AA ≠ ⊥ ∧ (∀ y ∈ per A N N', ((g : X.E) * ((ϖ : X.E) / star (ϖ : X.E))) • y ∈ halfBO S (per A N N') (p * g)) ∧ (∀ y ∈ halfBO S (per A N N') (p * g), ((g : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • y ∈ per A N N') ∧ (∀ x ∈ divLat cA (homAt S N N'), x ∈ homAt (divs ϖ) N N' → ∀ t ∈ halfAO S (per A N N') (cA * (p * g)), t - x ∈ mulLat (p * g) (homAt S N N') → ((cA * g : ℕ) : X.E) • t ∈ per A N N') ∧ (∀ y ∈ per A N N', y ∈ homAt S N N' ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ halfAO S (per A N N') (cA * (p * g)) ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt SG N N') ∧ ((((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt S N N') ↔ y ∈ smulLat (ϖ : X.E) (per A N N'))) ∧ (∀ (y : HomE X.E a b) (n : ℕ), Nat.Coprime n p → (n : X.E) • y ∈ smulLat ((ϖ : X.E) / star (ϖ : X.E)) (per A N N') → y ∈ mulLat p (homAt (divs ϖ) N N')) ∧ (∀ x ∈ halfBO S (per A N N') (p * g), ∀ y ∈ halfBO S (per A N N') (p * g), ∃ n : ℤ, coc A x y = n) ∧ ∀ x ∈ halfAO S (per A N N') (cA * (p * g)), ∀ y ∈ halfAO S (per A N N') (cA * (p * g)), ∃ n : ℤ, coc A x y = n := by
  intro X A a b S SG ϖ p g cA N N' hC hN hN'
  obtain ⟨hX, ⟨hδ, -, hSc, hAS, hfg, hLa⟩, hAc, -, hp, hϖ, hcop, hS, hSG, hg, hcA⟩ := hC
  have hp0 : p ≠ 0 := hp.ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; exact hp.one_lt.ne' (by simpa using hg)
  have hcA0 : cA ≠ 0 := by rintro rfl; exact hp.one_lt.ne' (by simpa using hcA)
  have hpE : (p : X.E) ≠ 0 := by exact_mod_cast hp0
  have hgE : (g : X.E) ≠ 0 := by exact_mod_cast hg0
  have hcE : (cA : X.E) ≠ 0 := by exact_mod_cast hcA0
  have hpO : (p : 𝓞 X.E) ≠ 0 := by exact_mod_cast hp0
  have hϖO : ϖ ≠ 0 := left_ne_zero_of_mul (hϖ ▸ hpO)
  obtain ⟨w, hw⟩ : ∃ w, w = X.conjO ϖ := ⟨_, rfl⟩
  have hstar : star (ϖ : X.E) = (w : X.E) := by rw [hw]; rfl
  have hconj : ∀ Q : HeightOneSpectrum (𝓞 X.E), w ∈ Q.asIdeal → conjPrime₂ Q ∈ S := fun Q h =>
    (hS _).2 (Or.inl (by rw [hw] at h; exact h))
  rw [← hw] at hϖ hcop hAc
  have hwO : w ≠ 0 := right_ne_zero_of_mul (hϖ ▸ hpO)
  have hpE' : (p : X.E) = (ϖ : X.E) * (w : X.E) := by
    have := congrArg (algebraMap (𝓞 X.E) X.E) hϖ
    rw [map_mul, map_natCast] at this
    exact this.symm
  have hϖE : (ϖ : X.E) ≠ 0 := left_ne_zero_of_mul (hpE' ▸ hpE)
  have hwE : (w : X.E) ≠ 0 := right_ne_zero_of_mul (hpE' ▸ hpE)
  have hSw : ∀ Q ∈ S, w ∉ Q.asIdeal := fun Q hQ h => hSc Q hQ (hconj Q h)
  have hnS : ∀ Q : HeightOneSpectrum (𝓞 X.E), Q ∉ S → ϖ ∉ Q.asIdeal := fun Q hQ h => hQ ((hS Q).2 (Or.inl h))
  have hpm : ∀ Q : HeightOneSpectrum (𝓞 X.E), ϖ ∈ Q.asIdeal → (p : 𝓞 X.E) ∈ Q.asIdeal := fun Q h =>
    hϖ ▸ Q.asIdeal.mul_mem_right _ h
  have hone : ∀ Q : HeightOneSpectrum (𝓞 X.E), (1 : 𝓞 X.E) ∉ Q.asIdeal := fun Q => Q.asIdeal.primeCompl.one_mem
  have hmul : ∀ (Q : HeightOneSpectrum (𝓞 X.E)) {s t : 𝓞 X.E}, s ∉ Q.asIdeal → t ∉ Q.asIdeal → s * t ∉ Q.asIdeal :=
    fun Q _ _ hs ht => Q.asIdeal.primeCompl.mul_mem hs ht
  have hAA : A.AA ≠ ⊥ := by
    obtain ⟨Q, hQ⟩ := exists_prime_over (E := X.E) hp
    have h1 : localization₂ Q.asIdeal A.AA = localization₂ Q.asIdeal 1 := by
      rcases Q.isPrime.mem_or_mem (hϖ ▸ hQ) with h | h
      · exact hAS Q ((hS Q).2 (Or.inl h))
      · exact hAc Q ((mem_divs hwO Q).2 h)
    intro h0
    have h2 : (1 : X.E) ∈ localization₂ Q.asIdeal A.AA := h1 ▸ loc_self Q (Submodule.mem_one.2 ⟨1, map_one _⟩)
    obtain ⟨s, hs, h3⟩ := h2
    rw [h0, Submodule.mem_bot, Algebra.smul_def, mul_one, RingOfIntegers.coe_eq_zero_iff] at h3
    exact hs (h3 ▸ Q.asIdeal.zero_mem)
  have hloc := fun P hP => (GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hfg hAA hN hN').2.2.2 P (hAS P hP)
  have hhom : ∀ T : Finset (HeightOneSpectrum (𝓞 X.E)), (∀ P ∈ T, P ∈ S) → ∀ y : HomE X.E a b,
      y ∈ homAt T N N' ↔ ∀ P ∈ T, y ∈ localization₂ P.asIdeal (per A N N') := fun T hT y =>
    forall₂_congr fun P hP => (hloc P (hT P hP) y).symm
  have hhS := hhom S fun _ h => h
  have hhG := hhom SG fun P h => (hS P).2 (Or.inr h)
  have hhD := hhom (divs ϖ) fun P h => (hS P).2 (Or.inl ((mem_divs hϖO P).1 h))
  have hcoc := (GlobalTheory.MomT.CocInt.cocycle_integral X A a b N N' hX hδ (hLa N N' hN hN').2).2.2
  have hpg : p * g ≠ 0 := mul_ne_zero hp0 hg0
  simp only [hstar]
  refine ⟨hAA, fun y hy => ?_, fun y hy => ?_, fun x _ hx t ht htx => ?_, fun y hy => ⟨?_, ?_, ?_, ?_⟩,
    fun y n hn hy => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_⟩
  · refine (mem_twO _ _ _ _).2 fun Q => ?_
    rw [smul_smul]
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> rw [e]
    · refine loc_smul' (loc_self Q hy) 1 (w * w) (hmul Q (hSw Q h1) (hSw Q h1)) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul' (loc_self Q hy) (g * g * ϖ * ϖ) 1 (hone Q) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul' (loc_self Q hy) (g * ϖ) w (fun h => h2 (hconj Q h)) ?_
      push_cast; field_simp
  · refine mem_of_loc fun Q => ?_
    have h := (mem_twO _ _ _ _).1 hy Q
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> rw [e] at h
    · refine loc_smul h (g * g * w * w) 1 (hone Q) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul h 1 (ϖ * ϖ) (hmul Q (hnS Q h1) (hnS Q h1)) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul h (g * w) ϖ (hnS Q h1) ?_
      push_cast; field_simp
  · refine mem_of_loc fun Q => ?_
    have h := (mem_twO _ _ _ _).1 ht Q
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> simp only [e, neg_zero, neg_neg] at h
    · by_cases hQ : ϖ ∈ Q.asIdeal
      · have h3 := (hhD x).1 hx Q ((mem_divs hϖO Q).2 hQ)
        have h4 := (hhS _).1 ((mem_mulLat _ hpg _).1 htx) Q h1
        have h5 : (1 : X.E) • (t - x) ∈ localization₂ Q.asIdeal (per A N N') := by
          refine loc_smul h4 (p * g) 1 (hone Q) ?_
          push_cast; field_simp
        rw [one_smul] at h5
        have h6 := add_mem h3 h5
        rw [add_sub_cancel] at h6
        refine loc_smul' h6 (cA * g) 1 (hone Q) ?_
        push_cast; field_simp
      · refine loc_smul h 1 p (hSG Q (((hS Q).1 h1).resolve_left hQ)) ?_
        push_cast; field_simp
    · refine loc_smul h (cA * g * (cA * (p * g))) 1 (hone Q) ?_
      push_cast; field_simp
    · refine loc_smul h (cA * g) 1 (hone Q) ?_
      push_cast; field_simp
  · exact (hhS y).2 fun P _ => loc_self P hy
  · refine (mem_twO _ _ _ _).2 fun Q => ?_
    rw [smul_smul]
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> simp only [e, neg_zero, neg_neg]
    · refine loc_smul' (loc_self Q hy) (cA * (p * g) * (cA * g * w)) 1 (hone Q) ?_
      push_cast; field_simp
    · refine loc_smul' (loc_self Q hy) 1 ϖ (hnS Q h1) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul' (loc_self Q hy) (cA * g * w) 1 (hone Q) ?_
      push_cast; field_simp
  · refine (mem_mulLat _ hpg _).2 ((hhG _).2 fun P hP => ?_)
    rw [smul_smul]
    refine loc_smul' (loc_self P hy) cA ϖ (fun h => hSG P hP (hpm P h)) ?_
    push_cast; simp only [hpE']; field_simp
  · rw [mem_mulLat _ hpg, hhS, smul_smul, mem_smulLat]
    constructor
    · intro h
      refine ⟨(ϖ : X.E)⁻¹ • y, mem_of_loc fun Q => ?_, by rw [smul_smul, mul_inv_cancel₀ hϖE, one_smul]⟩
      by_cases hQ : ϖ ∈ Q.asIdeal
      · refine loc_smul (h Q ((hS Q).2 (Or.inl hQ))) 1 cA (nat_notMem hcA (hpm Q hQ)) ?_
        push_cast; simp only [hpE']; field_simp
      · refine loc_smul' (loc_self Q hy) 1 ϖ hQ ?_
        push_cast; field_simp
    · rintro ⟨m, hm, rfl⟩ P _
      rw [smul_smul]
      refine loc_smul' (loc_self P hm) cA 1 (hone P) ?_
      push_cast; simp only [hpE']; field_simp
  · obtain ⟨m, hm, e⟩ := hy
    have hn0 : (n : X.E) ≠ 0 := by
      have : n ≠ 0 := by rintro rfl; exact hp.one_lt.ne' (by simpa using hn)
      exact_mod_cast this
    have e' : y = ((n : X.E)⁻¹ * ((ϖ : X.E) / (w : X.E))) • m := by
      have e2 : ((ϖ : X.E) / (w : X.E)) • m = (n : X.E) • y := e
      rw [mul_smul, e2, smul_smul, inv_mul_cancel₀ hn0, one_smul]
    refine (mem_mulLat _ hp0 _).2 ((hhD _).2 fun P hP => ?_)
    have hP' := (mem_divs hϖO P).1 hP
    have hw' := hSw P ((hS P).2 (Or.inl hP'))
    rw [e', smul_smul]
    refine loc_smul' (loc_self P hm) 1 (n * (w * w)) (hmul P (nat_notMem hn (hpm P hP')) (hmul P hw' hw')) ?_
    push_cast; simp only [hpE']; field_simp
  · refine hcoc x y fun Q => ⟨((p * g : ℕ) : X.E) ^ expS S Q, zpow_ne_zero _ (by exact_mod_cast hpg),
      (mem_twO _ _ _ _).1 hx Q, ?_⟩
    have h := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    rwa [expS_conj hSc, zpow_neg, inv_inv, ← star_natCast (R := X.E), ← star_zpow₀] at h
  · refine hcoc x y fun Q => ⟨((cA * (p * g) : ℕ) : X.E) ^ (-expS S Q),
      zpow_ne_zero _ (by exact_mod_cast mul_ne_zero hcA0 hpg), (mem_twO _ _ _ _).1 hx Q, ?_⟩
    have h := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    rwa [expS_conj hSc, zpow_neg, inv_inv, ← star_natCast (R := X.E), ← star_zpow₀] at h

end GlobalTheory.MomT.HalfIncl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodLatticeHalfLatticeInclusionsSplitPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLattice_halfLattice_inclusions_splitPrime : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Ctx A a b S SG ϖ p g cA → IsSdLat N → IsSdLat N' → A.AA ≠ ⊥ ∧ (∀ y ∈ per A N N', ((g : X.E) * ((ϖ : X.E) / star (ϖ : X.E))) • y ∈ halfBO S (per A N N') (p * g)) ∧ (∀ y ∈ halfBO S (per A N N') (p * g), ((g : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • y ∈ per A N N') ∧ (∀ x ∈ divLat cA (homAt S N N'), x ∈ homAt (divs ϖ) N N' → ∀ t ∈ halfAO S (per A N N') (cA * (p * g)), t - x ∈ mulLat (p * g) (homAt S N N') → ((cA * g : ℕ) : X.E) • t ∈ per A N N') ∧ (∀ y ∈ per A N N', y ∈ homAt S N N' ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ halfAO S (per A N N') (cA * (p * g)) ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt SG N N') ∧ ((((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt S N N') ↔ y ∈ smulLat (ϖ : X.E) (per A N N'))) ∧ (∀ (y : HomE X.E a b) (n : ℕ), Nat.Coprime n p → (n : X.E) • y ∈ smulLat ((ϖ : X.E) / star (ϖ : X.E)) (per A N N') → y ∈ mulLat p (homAt (divs ϖ) N N')) ∧ (∀ x ∈ halfBO S (per A N N') (p * g), ∀ y ∈ halfBO S (per A N N') (p * g), ∃ n : ℤ, coc A x y = n) ∧ ∀ x ∈ halfAO S (per A N N') (cA * (p * g)), ∀ y ∈ halfAO S (per A N N') (cA * (p * g)), ∃ n : ℤ, coc A x y = n := by
  first | exact @GlobalTheory.MomT.HalfIncl.half_inclusions | exact GlobalTheory.MomT.HalfIncl.half_inclusions | (intros; apply GlobalTheory.MomT.HalfIncl.half_inclusions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassPairingIntegralFormRowIsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassPairingIntegralFormRowIsIntegral
noncomputable section

namespace GlobalTheory.PairAtClass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

section

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
  (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hQ : Q.Ok)

theorem petersson_single_left (g w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) w = Q.wt c * ipVal emb σ Q.sgT (g c) (w c) := by
  letI := Q.clFin hQ
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

theorem petersson_single_right (g w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    Q.ipP emb σ hQ g (fun c' => if c' = c then w c' else 0) = Q.wt c * ipVal emb σ Q.sgT (g c) (w c) := by
  letI := Q.clFin hQ
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

theorem period_single (hI : I.Ok) (hc : ι → HCParam R) (G : Q.Mt emb σ)
    (w : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ) (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] :
    (Q.per emb σ hI hQ hc).period (fun c' => if c' = c then w c' else 0) G =
      Q.wt c * pairB Q.sgT (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1)) (w c))
        (Q.rd emb σ G c) := by
  letI := Q.clFin hQ
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine (Finset.sum_eq_single c (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ c) h)).trans ?_
  · simp [hb]
  · simp

end

theorem pair_integral : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hI : I.Ok) (hQ : Q.Ok) (hc : ι → HCParam R) (hF : (Q.S'.fam emb Q.sgT).Ok) (G : Q.Mt emb σ) (g : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ), (∀ w, (Q.per emb σ hI hQ hc).period w G = Q.ipP emb σ hQ g w) → ∀ (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] (y : Formalism.L2.DIV.VV K Q.sgT), y ∈ nabAt emb Q.sgT (Q.S'.Lsh c.1 (Q.S'.rep c)) → Q.rd emb σ G c = MvPolynomial.map σ y.1 → ∀ x ∈ (Q.S'.hlat emb Q.sgT hF).L, ∃ a : 𝓞 K, σ (a : K) = ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) * Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
  intro E K ι _ _ _ _ _ _ _ emb σ R I Q hI hQ hc hF G g hP c _ y hy hG x hx
  have hfin := hQ.step.fin_stab c.1 (Q.S'.rep c)
  have hne : ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) ≠ 0 := by
    haveI := hfin
    exact_mod_cast Nat.card_pos.ne'
  have hint := ((GlobalTheory.PeriodClassSum.pairBDual E K ι _ emb Q.sgT _ (hQ.step.lsh_full_lat c.1 (Q.S'.rep c)) (x.1 c)).1.1
    (hx c)) y hy
  obtain ⟨a, ha⟩ := hint
  refine ⟨a, ?_⟩
  have e12 : Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0)
      (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) =
      Q.ipP emb σ hQ g (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
    rw [petersson_single_left, petersson_single_right]
    simp
  rw [e12, ← hP, period_single, hG]
  show _ = _ * (Q.wt c * pairB Q.sgT (polOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) (fr0 emb σ (R.N R.m - 1))
    (evV emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) E) Q.sgT σ (x.1 c))) (MvPolynomial.map σ y.1))
  rw [GlobalTheory.PeriodOnStep.polOf_evV, ← GlobalTheory.PeriodOnStep.map_pairB, ← pairBK_apply, PerIn.wt, ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]
  rw [← ha, LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_one]

end GlobalTheory.PairAtClass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassPairingIntegralFormRowIsIntegralStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classPairing_integral_form_row_isIntegral : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hI : I.Ok) (hQ : Q.Ok) (hc : ι → HCParam R) (hF : (Q.S'.fam emb Q.sgT).Ok) (G : Q.Mt emb σ) (g : Q.S'.Cl → GlobalTheory.Mem.Col2.Fr emb σ (R.N R.m - 1) → ℂ), (∀ w, (Q.per emb σ hI hQ hc).period w G = Q.ipP emb σ hQ g w) → ∀ (c : Q.S'.Cl) [DecidableEq Q.S'.Cl] (y : Formalism.L2.DIV.VV K Q.sgT), y ∈ nabAt emb Q.sgT (Q.S'.Lsh c.1 (Q.S'.rep c)) → Q.rd emb σ G c = MvPolynomial.map σ y.1 → ∀ x ∈ (Q.S'.hlat emb Q.sgT hF).L, ∃ a : 𝓞 K, σ (a : K) = ((Nat.card (Q.S'.Stab c) : ℕ) : ℂ) * Q.ipP emb σ hQ (fun c' => if c' = c then g c' else 0) (fun c' => if c' = c then Q.S'.embF emb σ Q.sgT hF x c' else 0) := by
  first | exact @GlobalTheory.PairAtClass.pair_integral | exact GlobalTheory.PairAtClass.pair_integral | (intros; apply GlobalTheory.PairAtClass.pair_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRealAdelicHermitianSignatureCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRealAdelicHermitianSignatureCoordinates
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.RealSpaceCoord

theorem herm_eq_dot {P Q : ℕ} (x y : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm y x = star x ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ y) := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, Fintype.sum_sum_type, dotProduct, fromBlocks_mulVec, neg_mulVec,
    mul_comm]

theorem form_eq {M P Q : ℕ} (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (x y : Fin M → ℂ) :
    ∑ i, ∑ j, star (x i) * (Aᴴ * Formalism.UG.Jpq P Q * A) i j * y j = ActionCoordinates.herm (A *ᵥ y) (A *ᵥ x) := by
  rw [herm_eq_dot, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), P + Q = M → ∀ J : Matrix (Fin M) (Fin M) E, IsHermND σ J → ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ, (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∃ e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (T → ActionCoordinates.Wsp P Q), (∀ X ρ, e X ρ = A ρ *ᵥ fun i => θ ρ (X 0 i)) ∧ ∀ X Y ρ, θ ρ (hR (Ainf F) σ J (X 0) (Y 0)) = ActionCoordinates.herm (e Y ρ) (e X ρ) := by
  intro F E _ _ _ _ _ σ h T _ τ θ hτ hθ M P Q hM J hJ A hA
  obtain ⟨e0, he, hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ T τ θ h hτ hθ
  let B : T → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ := fun ρ => (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q)
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => by
    have hd : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
    simp only [B]
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul]
    rw [hd]
    exact ((map_ne_zero (τ ρ)).2 hJ.2).isUnit
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ =>
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hM])).2 (hBA ρ)
  have he' : ∀ z ρ, θ ρ (e0.symm z) = z ρ := fun z ρ => by rw [← he, e0.apply_symm_apply]
  refine ⟨{ toFun := fun X ρ => A ρ *ᵥ fun i => θ ρ (X 0 i)
            invFun := fun z _ i => e0.symm fun ρ => (B ρ *ᵥ z ρ) i
            left_inv := fun X => ?_
            right_inv := fun z => ?_
            map_add' := fun X Y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ _ => rfl, fun X Y ρ => ?_⟩
  · funext k i
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [mulVec_mulVec, hBA, one_mulVec]
    rw [RingEquiv.symm_apply_eq]
    funext ρ
    rw [he]
  · funext ρ
    simp only [he']
    rw [mulVec_mulVec, hAB, one_mulVec]
  · funext ρ
    refine Eq.trans ?_ (mulVec_add (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    congr 1
    funext i
    exact map_add (θ ρ) _ _
  · refine continuous_pi fun ρ => continuous_const.matrix_mulVec (continuous_pi fun i => ?_)
    simp only [← he]
    exact (continuous_apply ρ).comp (hc.comp ((continuous_apply i).comp (continuous_apply 0)))
  · exact continuous_pi fun _ => continuous_pi fun i => hc'.comp (continuous_pi fun ρ =>
      (continuous_apply i).comp (continuous_const.matrix_mulVec (continuous_apply ρ)))
  · refine Eq.trans ?_ (form_eq (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    rw [hA]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, Formalism.UG.hform, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Mem.VolInfIso.infEmb_sigR σ (τ ρ) (θ ρ) h (hθ ρ)]
    congr 2
    exact (hθ ρ).1 _

end GlobalTheory.RealSpaceCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRealAdelicHermitianSignatureCoordinatesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realAdelicHermitian_signature_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), P + Q = M → ∀ J : Matrix (Fin M) (Fin M) E, IsHermND σ J → ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ, (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∃ e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (T → ActionCoordinates.Wsp P Q), (∀ X ρ, e X ρ = A ρ *ᵥ fun i => θ ρ (X 0 i)) ∧ ∀ X Y ρ, θ ρ (hR (Ainf F) σ J (X 0) (Y 0)) = ActionCoordinates.herm (e Y ρ) (e X ρ) := by
  first | exact @GlobalTheory.RealSpaceCoord.exists_coord | exact GlobalTheory.RealSpaceCoord.exists_coord | (intros; apply GlobalTheory.RealSpaceCoord.exists_coord <;> assumption)
end
end
