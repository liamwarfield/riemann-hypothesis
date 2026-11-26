module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCutoffTranslateContDiff
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCutoffTranslateContDiff
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CutOff

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem contDiff_lastEnt : ContDiff ℝ ∞ (lastEnt : (Fin k → Cinf E) → Cinf E) := by
  unfold lastEnt
  refine ContDiff.sum fun c _ => ?_
  by_cases h : (c : ℕ) + 1 = k
  · simp only [if_pos h]
    exact contDiff_apply ℝ (fun _ : Fin k => Cinf E) c
  · simp only [if_neg h]
    exact contDiff_const

theorem isOpen_lastEnt_unit : IsOpen {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
  (Units.isOpen (R := Cinf E)).preimage (contDiff_lastEnt (E := E)).continuous

theorem contDiffOn_inverse_lastEnt :
    ContDiffOn ℝ ∞ (fun x : Fin k → Cinf E => Ring.inverse (lastEnt x))
      {x | IsUnit (lastEnt x)} := by
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (lastEnt x) := by
    rw [← hu]; exact contDiffAt_ringInverse ℝ u
  exact (h1.comp x (contDiff_lastEnt (E := E)).contDiffAt).contDiffWithinAt

def tauM (x : Fin k → Cinf E) : LieI (InfinitePlace E) k := Matrix.of.symm (rowM (rowI x))

theorem contDiffOn_tauM :
    ContDiffOn ℝ ∞ (tauM : (Fin k → Cinf E) → LieI (InfinitePlace E) k)
      {x | IsUnit (lastEnt x)} := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun c => ?_
  have hinv := contDiffOn_inverse_lastEnt (E := E) (k := k)
  by_cases hi : (i : ℕ) + 1 = k
  · have e : ∀ x : Fin k → Cinf E, tauM x i c = rowI x c := fun x => rowM_apply_last _ i c hi
    simp only [e]
    by_cases hc : (c : ℕ) + 1 = k
    · simp only [rowI, if_pos hc]
      exact hinv
    · simp only [rowI, if_neg hc]
      exact ((contDiff_apply ℝ (fun _ : Fin k => Cinf E) c).contDiffOn.mul hinv).neg
  · have e : ∀ x : Fin k → Cinf E, tauM x i c = (1 : Matrix (Fin k) (Fin k) (Cinf E)) i c :=
      fun x => rowM_apply_ne _ i c hi
    simp only [e]
    exact contDiffOn_const

theorem tauM_isUnit {x : Fin k → Cinf E} (h : IsUnit (lastEnt x)) :
    IsUnit (Matrix.of (tauM x)) := by
  have e : Matrix.of (tauM x) = (((rowGL x)⁻¹ : GL (Fin k) (Cinf E)) : Matrix (Fin k) (Fin k) (Cinf E)) :=
    (rowGL_inv_val h).symm
  rw [e]
  exact Units.isUnit _

theorem rt_inv_eq_orb (φ : XB E k) {x : Fin k → Cinf E} (h : IsUnit (lastEnt x)) :
    Rt E k (infGL E k (rowGL x))⁻¹ φ = orb (repI E k) φ (tauM x) := by
  have hu := tauM_isUnit h
  have e : hu.unit = (rowGL x)⁻¹ := Units.ext (by
    rw [IsUnit.unit_spec]; exact (rowGL_inv_val h).symm)
  rw [orb, dite_eq_left hu, e]
  change _ = Rt E k (infGL E k (rowGL x)⁻¹) φ
  rw [map_inv (infGL E k)]

theorem contDiff_cut_orbit {φ : XB E k} (hφ : SmV (repI E k) φ) {b : (Fin k → Cinf E) → ℝ}
    (hb : ContDiff ℝ ∞ b) (hs : ∀ x ∈ tsupport b, IsUnit (lastEnt x)) :
    ContDiff ℝ ∞ fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ := by
  have hO := isOpen_lastEnt_unit (E := E) (k := k)
  have hbc : ContDiff ℝ ∞ fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp hb
  have horb : ContDiffOn ℝ ∞ (fun x => orb (repI E k) φ (tauM x)) {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
    ContDiffOn.comp hφ contDiffOn_tauM fun x hx => tauM_isUnit hx
  have hF : ContDiffOn ℝ ∞ (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ)
      {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
    (hbc.contDiffOn.smul horb).congr fun x hx => by
      rw [rt_inv_eq_orb φ hx]
      rfl
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ tsupport b
  · exact hF.contDiffAt (hO.mem_nhds (hs x hx))
  · have e : (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq e

end GlobalTheory.CompanionTheory.CutOff

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCutoffTranslateContDiffStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_cutoff_translate_contDiff : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {φ : XB E k}, SmV (repI E k) φ → ∀ {b : (Fin k → Cinf E) → ℝ}, ContDiff ℝ ∞ b → (∀ x ∈ tsupport b, IsUnit (lastEnt x)) → ContDiff ℝ ∞ fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit | exact GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit | (intros; apply GlobalTheory.CompanionTheory.CutOff.contDiff_cut_orbit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableHeightPowOfPolynomialCount
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableHeightPowOfPolynomialCount
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem summable_rpow_neg_of_polynomial_count :
    ∀ (Q : Type) (h : Q → ℝ), (∀ q, 1 ≤ h q) → ∀ (C : ℝ) (c : ℕ),
    (∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C * T ^ c) → ∀ s : ℝ, (c : ℝ) < s →
    Summable fun q => h q ^ (-s) := by
  intro Q h h1 C c hc s hs
  classical
  have hC : 0 ≤ C := by
    have h2 := (hc 1 le_rfl).2
    have h3 : (0:ℝ) ≤ (Set.ncard {q | h q ≤ 1} : ℝ) := Nat.cast_nonneg _
    simp only [one_pow, mul_one] at h2
    linarith
  set r : ℝ := (2:ℝ) ^ ((c:ℝ) - s) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable fun k : ℕ => C * 2 ^ c * r ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hg0 : ∀ k : ℕ, 0 ≤ C * 2 ^ c * r ^ k := fun k => by positivity
  set K : Q → ℕ := fun q => ⌊Real.logb 2 (h q)⌋₊ with hK
  have hlog0 : ∀ q, 0 ≤ Real.logb 2 (h q) := fun q =>
    Real.logb_nonneg (by norm_num) (h1 q)
  have hlow : ∀ q, (2:ℝ) ^ (K q : ℝ) ≤ h q := fun q => by
    have hq : (0:ℝ) < h q := lt_of_lt_of_le one_pos (h1 q)
    have : (K q : ℝ) ≤ Real.logb 2 (h q) := Nat.floor_le (hlog0 q)
    calc (2:ℝ) ^ (K q : ℝ) ≤ (2:ℝ) ^ (Real.logb 2 (h q)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = h q := Real.rpow_logb (by norm_num) (by norm_num) hq
  have hupp : ∀ q, h q ≤ (2:ℝ) ^ (K q + 1) := fun q => by
    have hq : (0:ℝ) < h q := lt_of_lt_of_le one_pos (h1 q)
    have : Real.logb 2 (h q) ≤ ((K q + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc h q = (2:ℝ) ^ (Real.logb 2 (h q)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hq).symm
      _ ≤ (2:ℝ) ^ (((K q + 1 : ℕ)) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = (2:ℝ) ^ (K q + 1) := Real.rpow_natCast _ _
  have hterm : ∀ q, h q ^ (-s) ≤ ((2:ℝ) ^ (K q : ℝ)) ^ (-s) := fun q =>
    Real.rpow_le_rpow_of_nonpos (by positivity) (hlow q) (by linarith [(Nat.cast_nonneg c : (0:ℝ) ≤ c)])
  have hfib : ∀ (u : Finset Q) (k : ℕ),
      ∑ q ∈ u with K q = k, h q ^ (-s) ≤ C * 2 ^ c * r ^ k := by
    intro u k
    have hT : (1:ℝ) ≤ (2:ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    obtain ⟨hfin, hcard⟩ := hc _ hT
    have hsub : ((u.filter fun q => K q = k : Finset Q) : Set Q) ⊆ {q | h q ≤ (2:ℝ) ^ (k + 1)} := by
      intro q hq
      have hq' : K q = k := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
      have := hupp q
      rw [hq'] at this
      exact this
    have hcard2 : ((u.filter fun q => K q = k : Finset Q).card : ℝ) ≤ C * ((2:ℝ) ^ (k + 1)) ^ c := by
      refine le_trans ?_ hcard
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    have hb : ∀ q ∈ u.filter (fun q => K q = k), h q ^ (-s) ≤ ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
      intro q hq
      have hq' : K q = k := (Finset.mem_filter.mp hq).2
      have := hterm q
      rw [hq'] at this
      exact this
    have hb0 : (0:ℝ) ≤ ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by positivity
    calc ∑ q ∈ u with K q = k, h q ^ (-s)
        ≤ ((u.filter fun q => K q = k : Finset Q).card : ℝ) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
          simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hb
      _ ≤ (C * ((2:ℝ) ^ (k + 1)) ^ c) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) :=
          mul_le_mul_of_nonneg_right hcard2 hb0
      _ = C * 2 ^ c * r ^ k := by
          have e1 : ((2:ℝ) ^ (k + 1)) ^ c = 2 ^ c * ((2:ℝ) ^ (k : ℝ)) ^ (c : ℝ) := by
            rw [Real.rpow_natCast, Real.rpow_natCast, pow_succ, mul_pow, mul_comm]
          have e2 : r ^ k = ((2:ℝ) ^ (k : ℝ)) ^ (c : ℝ) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
            rw [← Real.rpow_add (by positivity), hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num)]
            congr 1
            ring
          rw [e1, e2]
          ring
  refine summable_of_sum_le (c := ∑' k : ℕ, C * 2 ^ c * r ^ k) (fun q => Real.rpow_nonneg (by linarith [h1 q]) _) ?_
  intro u
  calc ∑ q ∈ u, h q ^ (-s)
      = ∑ k ∈ u.image K, ∑ q ∈ u with K q = k, h q ^ (-s) :=
        (Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem K hq) _).symm
    _ ≤ ∑ k ∈ u.image K, C * 2 ^ c * r ^ k := Finset.sum_le_sum fun k _ => hfib u k
    _ ≤ ∑' k : ℕ, C * 2 ^ c * r ^ k := hg.sum_le_tsum _ fun k _ => hg0 k

end GlobalTheory.CompanionTheory.GodementH
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableHeightPowOfPolynomialCountStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_height_pow_of_polynomial_count : ∀ (Q : Type) (h : Q → ℝ), (∀ q, 1 ≤ h q) → ∀ (C : ℝ) (c : ℕ),
    (∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C * T ^ c) → ∀ s : ℝ, (c : ℝ) < s →
    Summable fun q => h q ^ (-s) := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.summable_rpow_neg_of_polynomial_count | exact GlobalTheory.CompanionTheory.GodementH.summable_rpow_neg_of_polynomial_count | (intros; apply GlobalTheory.CompanionTheory.GodementH.summable_rpow_neg_of_polynomial_count <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterRealPairing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSInf
noncomputable section

open NumberField IsDedekindDomain Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.JSInfStep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem nonempty_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩

variable [_root_.NumberField.IsTotallyComplex E]

def chiInf (ψ : AddChar (Ad E) ℂ) : AddChar (Cinf E) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHomClass.toAddMonoidHom (sInf E))

theorem chiInf_apply (ψ : AddChar (Ad E) ℂ) (z : Cinf E) : chiInf ψ z = ψ (sInf E z) := rfl

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

theorem pInf_sInf (x : Cinf E) : pInf E (sInf E x) = x := (infEq E).symm_apply_apply x

theorem pFin_sInf (x : Cinf E) : pFin E (sInf E x) = 0 := rfl

theorem chiInf_nondeg {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (z : Cinf E)
    (h : ∀ w, chiInf ψ (z * w) = 1) : z = 0 := by
  obtain ⟨d, hd⟩ := hψ.ann (sInf E z) fun c => by
    have e : sInf E z * algebraMap E (Ad E) c = sInf E (z * pInf E (algebraMap E (Ad E) c)) := by
      refine ad_ext ?_ ?_
      · rw [map_mul, pInf_sInf, pInf_sInf]
      · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]
    rw [e]
    exact h _
  obtain ⟨w⟩ := nonempty_pl (E := E)
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h0 : ((pFin E).comp (algebraMap E (Ad E))) d = 0 := by
    change pFin E (algebraMap E (Ad E) d) = 0
    rw [← hd, pFin_sInf]
  have hd0 : d = 0 := (injective_iff_map_eq_zero _).1 ((pFin E).comp (algebraMap E (Ad E))).injective d h0
  rw [← pInf_sInf z, hd, hd0, map_zero, map_zero]

end GlobalTheory.CompanionTheory.JSInfStep

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterRealPairing
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.JSPair

def dotL (E : Type) [Field E] [NumberField E] (k : ℕ) :
    (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] Cinf E :=
  ∑ i : Fin k, (ContinuousLinearMap.mul ℝ (Cinf E)).bilinearComp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)

theorem dotL_apply {E : Type} [Field E] [NumberField E] {k : ℕ} (x z : Fin k → Cinf E) :
    dotL E k x z = ∑ i, x i * z i := by
  simp [dotL, ContinuousLinearMap.sum_apply]

theorem exists_pairing : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  intro E _ _ _ k ψ h8 hψ
  obtain ⟨l, hl⟩ := h8 (InfinitePlace E) (GlobalTheory.CompanionTheory.JSInfStep.chiInf ψ)
    (hψ.cont.comp GlobalTheory.CompanionTheory.JSInfStep.continuous_sInf) (fun z => hψ.norm _)
  let β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (Fin k → Cinf E) (Cinf E) ℝ (-l)) ∘L dotL E k
  have hβ : ∀ x z, β x z = -l (∑ i, x i * z i) := fun x z => by
    simp [β, dotL_apply]
  refine ⟨β, fun y hy => ?_, fun x z => ?_⟩
  · funext i
    refine GlobalTheory.CompanionTheory.JSInfStep.chiInf_nondeg hψ (y i) fun w => ?_
    have h0 := hy (Pi.single i w)
    rw [hβ] at h0
    have e : ∑ j, (Pi.single i w : Fin k → Cinf E) j * y j = y i * w := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, mul_comm]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_mul]
      · simp
    rw [e] at h0
    have h1 : l (y i * w) = 0 := neg_eq_zero.1 h0
    rw [hl, h1]
    simp
  · have := hl (∑ i, x i * z i)
    rw [GlobalTheory.CompanionTheory.JSInfStep.chiInf_apply] at this
    rw [this, hβ]
    simp

end GlobalTheory.CompanionTheory.JSPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterRealPairingStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_character_real_pairing : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.CompanionTheory.JSPair.exists_pairing | exact GlobalTheory.CompanionTheory.JSPair.exists_pairing | (intros; apply GlobalTheory.CompanionTheory.JSPair.exists_pairing <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleBoundOfJointAnisotropic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleBoundOfJointAnisotropic
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.FormHeight

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

section Forms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {n : ℕ}

theorem sigR_conj (R : Type) [CommRing R] [Algebra F R] :
    sigR R (conj F E).toAlgHom = conjBase F E R := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem hermValue_eq_hR (R : Type) [CommRing R] [Algebra F R] (H : Matrix (Fin n) (Fin n) E)
    (x : Fin n → R ⊗[F] E) : hermValue F H R x = hR R (conj F E).toAlgHom H x x := by
  rw [hR, sigR_conj]
  simp only [hermValue, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc]
  rfl

theorem coords_algebraMap_mul_inclR (s : AF F) (z : E) :
    coords (Module.finBasis F E) (AF F)
        (algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F := F) (AF F) z) =
      s • Reduction.ratVec (fun k => (Module.finBasis F E).repr z k) := by
  have e : algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F := F) (AF F) z = s • ((1 : AF F) ⊗ₜ[F] z) := by
    simp [inclR, Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']
  rw [e, map_smul]
  congr 1
  funext k
  simp [coords, Reduction.ratVec, Algebra.TensorProduct.basis_repr_tmul]

theorem exists_adelicNorm_hermPoly_le (H : Matrix (Fin n) (Fin n) E) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Fin (Bridge.dimN F E n) → AF F, Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent
        (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) ≤
        C * Reduction.adelicNorm y ^ 2 :=
  exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos (hermPoly H (Module.finBasis F E))
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)

theorem one_le_mul_hgt_sq (J H : Matrix (Fin n) (Fin n) E) {C : ℝ}
    (hCb : ∀ y : Fin (Bridge.dimN F E n) → AF F, Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent
        (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) ≤
        C * Reduction.adelicNorm y ^ 2)
    (g : GAd (conj F E).toAlgHom J) {ξ : Fin n → E} (hξ : ξ ≠ 0)
    (s : GroundTheory.Global.IdeleGroup F) (hs : 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ))
    {z : E} (hz : z ≠ 0)
    (he : hR (AF F) (conj F E).toAlgHom H
        ((matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ)
        ((matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ) =
      algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) z) :
    1 ≤ C * hgt (conj F E).toAlgHom J g ξ ^ 2 := by
  set b := Module.finBasis F E with hb
  set v := (matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ with hv
  set y : Fin (Bridge.dimN F E n) → AF F := resVec (ι := Fin n) b (AF F) v with hy
  have ey : Reduction.ratVec (Bridge.cvec F ξ) ᵥ*
      (Bridge.trG (conj F E).toAlgHom J g : Matrix _ _ (AF F)) = y := by
    rw [Bridge.ratVec_cvec, Bridge.trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hy, hv, map_inv]
  have hfy : Reduction.HasFiniteContent y := by
    rw [← ey]
    exact Reduction.hasFiniteContent_height _ (Bridge.cvec_ne_zero hξ)
  have hz' : (fun k => b.repr z k) ≠ 0 := by
    intro h0
    apply hz
    apply b.repr.injective
    ext k
    simpa using congrFun h0 k
  have e : (fun k => MvPolynomial.aeval y (hermPoly H b k)) =
      (s : AF F) • Reduction.ratVec (fun k => b.repr z k) := by
    funext k
    rw [aeval_hermPoly, hermCoords, hy, ofResVec_resVec, hermValue_eq_hR, he,
      coords_algebraMap_mul_inclR]
  have hfz : Reduction.HasFiniteContent (fun k => MvPolynomial.aeval y (hermPoly H b k)) := by
    rw [e]
    exact (Reduction.hasFiniteContent_ratVec hz').smul s
  have h1 : 1 ≤ Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H b k)) := by
    rw [e, Reduction.adelicNorm_smul (Reduction.hasFiniteContent_ratVec hz')]
    exact one_le_mul_of_one_le_of_one_le hs (Reduction.one_le_adelicNorm_ratVec hz')
  exact h1.trans (hCb y hfy hfz)

end Forms

theorem min_le_of_one_le_mul_sq {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) (h : 1 ≤ D * t ^ 2) :
    min 1 D⁻¹ ≤ t := by
  by_cases h1 : 1 ≤ t
  · exact (min_le_left _ _).trans h1
  · replace h1 := not_le.1 h1
    have h3 : 1 ≤ D * t := by
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hD.le)
      nlinarith
    refine (min_le_right _ _).trans ?_
    rw [inv_le_iff_one_le_mul₀ hD, mul_comm]
    exact h3

theorem exists_pos_le_hgt_of_forms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (H : M → Matrix (Fin n) (Fin n) E) (L : Set (GAd σ J)), (∀ ξ : Fin n → E, (∀ j, hE σ (H j) ξ ξ = 0) → ξ = 0) → (∀ g ∈ L, ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (H j) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (H j) ξ ξ)) → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ := by
  intro F E _ _ _ _ _ σ hCM n J _ M _ H L hzero hL
  obtain ⟨hF, hEc, h2, hc⟩ := hCM
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  cases nonempty_fintype M
  choose C hC hCb using fun j => exists_adelicNorm_hermPoly_le (F := F) (H j)
  have hsum : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => (hC j).le
  have hD : 0 < 1 + ∑ j, C j := by linarith
  refine ⟨min 1 (1 + ∑ j, C j)⁻¹, lt_min one_pos (inv_pos.2 hD), fun g hg ξ hξ => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, hE (conj F E).toAlgHom (H j) ξ ξ ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hξ (hzero ξ hno)
  obtain ⟨s, hs, he⟩ := hL g hg j
  have h1 := one_le_mul_hgt_sq J (H j) (hCb j) g hξ s hs hj (he ξ)
  have ht : 0 ≤ hgt (conj F E).toAlgHom J g ξ := Reduction.adelicNorm_nonneg _
  have hle : C j ≤ 1 + ∑ j, C j := by
    have := Finset.single_le_sum (f := C) (fun i _ => (hC i).le) (Finset.mem_univ j)
    linarith
  exact min_le_of_one_le_mul_sq hD ht
    (h1.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)))

end GlobalTheory.CompanionTheory.ParCocompact.FormHeight

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleBoundOfJointAnisotropicStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_bound_of_joint_anisotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (H : M → Matrix (Fin n) (Fin n) E) (L : Set (GAd σ J)), (∀ ξ : Fin n → E, (∀ j, hE σ (H j) ξ ξ = 0) → ξ = 0) → (∀ g ∈ L, ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (H j) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (H j) ξ ξ)) → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.FormHeight.exists_pos_le_hgt_of_forms | exact GlobalTheory.CompanionTheory.ParCocompact.FormHeight.exists_pos_le_hgt_of_forms | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.FormHeight.exists_pos_le_hgt_of_forms <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCoefficientCongruencePullback
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCoefficientCongruencePullback
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem measurePreserving_of_covol {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G)
    (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm)
    (hT : ∀ γ ∈ Γ, T γ ∈ Γ) (hT' : ∀ γ ∈ Γ, T.symm γ ∈ Γ) : MeasurePreserving T μ μ := by
  let e : G ≃ᵐ G := (Homeomorph.mk T.toEquiv hc hc').toMeasurableEquiv
  have he : ∀ x, e x = T x := fun _ => rfl
  haveI hH : (μ.map e).IsAddHaarMeasure := T.isAddHaarMeasure_map μ hc hc'
  have hs : μ.map e = Measure.addHaarScalarFactor (μ.map e) μ • μ := Measure.isAddLeftInvariant_eq_smul _ _
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) μ
  set c := Measure.addHaarScalarFactor (μ.map e) μ with hcdef
  have hq : Measure.QuasiMeasurePreserving e μ μ := by
    refine ⟨e.measurable.aemeasurable, ?_⟩
    rw [hs]
    exact Measure.smul_absolutelyContinuous
  let σ : Γ → Γ := fun g => ⟨T.symm g, hT' g g.2⟩
  have hσ : Function.Bijective σ := by
    refine ⟨fun g g' h => ?_, fun g => ⟨⟨T g, hT g g.2⟩, ?_⟩⟩
    · apply Subtype.ext
      exact T.symm.injective (congrArg Subtype.val h)
    · apply Subtype.ext
      simp [σ]
  have hpre : IsAddFundamentalDomain Γ (e ⁻¹' 𝓕) μ := by
    refine hF.preimage_of_equiv hq hσ ?_
    intro g x
    show T (T.symm g + x) = g + T x
    simp
  have heq : μ (e ⁻¹' 𝓕) = μ 𝓕 := hpre.measure_eq hF
  have hmap : (μ.map e) 𝓕 = 1 := by rw [e.map_apply, heq, h1]
  have hc1 : c = 1 := by
    rw [hs] at hmap
    simp only [Measure.smul_apply, h1] at hmap
    have : ((c : ENNReal)) = 1 := by simpa [ENNReal.smul_def] using hmap
    exact_mod_cast this
  have : μ.map e = μ := by rw [hs, hc1, one_smul]
  exact ⟨e.measurable, this⟩

theorem integral_comp_of_covol {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G)
    (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm)
    (hT : ∀ γ ∈ Γ, T γ ∈ Γ) (hT' : ∀ γ ∈ Γ, T.symm γ ∈ Γ) (g : G → ℂ) :
    ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ :=
  (measurePreserving_of_covol Γ μ 𝓕 hF h1 T hc hc' hT hT').integral_comp
    (Homeomorph.mk T.toEquiv hc hc').toMeasurableEquiv.measurableEmbedding g

variable {D : D7}

def mulRightE {m r : ℕ} (A B : Mx D r r) (h1 : A * B = 1) (h2 : B * A = 1) : Mx D m r ≃+ Mx D m r where
  toFun y := y ⬝ A
  invFun y := y ⬝ B
  left_inv y := by
    show y ⬝ A ⬝ B = y
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  right_inv y := by
    show y ⬝ B ⬝ A = y
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  map_add' x y := Matrix.add_mul x y A

theorem adj_cong_mem {r : ℕ} (A : Mx D r r) (b : hermA D r) : A ⬝ b.1 ⬝ adj A ∈ hermA D r := by
  have hb : adj b.1 = b.1 := b.2
  show adj (A ⬝ b.1 ⬝ adj A) = A ⬝ b.1 ⬝ adj A
  rw [adj_mul, adj_mul, adj_adj, hb, Matrix.mul_assoc]

theorem cong_cancel {r : ℕ} (A B : Mx D r r) (h2 : B * A = 1) (b : Mx D r r) :
    B ⬝ (A ⬝ b ⬝ adj A) ⬝ adj B = b := by
  have h3 : adj A ⬝ adj B = 1 := by rw [← adj_mul, h2, adj_one]
  calc B ⬝ (A ⬝ b ⬝ adj A) ⬝ adj B = (B * A) * b * (adj A * adj B) := by
        simp only [Matrix.mul_assoc]
    _ = b := by
        rw [h2]
        erw [h3]
        simp

def congA {r : ℕ} (A B : Mx D r r) (h1 : A * B = 1) (h2 : B * A = 1) : hermA D r ≃+ hermA D r where
  toFun b := ⟨A ⬝ b.1 ⬝ adj A, adj_cong_mem A b⟩
  invFun b := ⟨B ⬝ b.1 ⬝ adj B, adj_cong_mem B b⟩
  left_inv b := Subtype.ext (cong_cancel A B h2 b.1)
  right_inv b := Subtype.ext (cong_cancel B A h1 b.1)
  map_add' x y := Subtype.ext (by
    show A ⬝ (x.1 + y.1) ⬝ adj A = A ⬝ x.1 ⬝ adj A + A ⬝ y.1 ⬝ adj A
    rw [Matrix.mul_add, Matrix.add_mul])

theorem rat_mul_inv {r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    rat a * rat a⁻¹ = (1 : Mx D r r) := by
  rw [← rat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 ha), rat_one]

theorem rat_inv_mul {r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    rat a⁻¹ * rat a = (1 : Mx D r r) := by
  rw [← rat_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 ha), rat_one]

theorem integral_mulRight {m r : ℕ} {μ : Measure (Mx D m r)} {𝓕 : Set (Mx D m r)}
    (hμ : IsCovolOne (ratMx D m r) μ 𝓕) (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0)
    (g : Mx D m r → ℂ) : ∫ y, g (y ⬝ rat a) ∂μ = ∫ y, g y ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m r
  haveI : BorelSpace (Mx D m r) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI i6 : DiscreteTopology (ratMx D m r) := i5
  haveI i7 : SecondCountableTopology (ratMx D m r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D m r) := TopologicalSpace.separableSpace_iff_countable.1
    (TopologicalSpace.SecondCountableTopology.to_separableSpace)
  obtain ⟨hH, hF, h1⟩ := hμ
  exact integral_comp_of_covol (ratMx D m r) μ 𝓕 hF h1
    (mulRightE (rat a) (rat a⁻¹) (rat_mul_inv a ha) (rat_inv_mul a ha))
    (continuous_id.matrix_mul continuous_const) (continuous_id.matrix_mul continuous_const)
    (by rintro _ ⟨γ, rfl⟩; exact ⟨γ * a, rat_mul γ a⟩)
    (by rintro _ ⟨γ, rfl⟩; exact ⟨γ * a⁻¹, rat_mul γ a⁻¹⟩) g

theorem integral_congA {r : ℕ} {lam : Measure (hermA D r)} {𝓖 : Set (hermA D r)}
    (hl : IsCovolOneH lam 𝓖) (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0)
    (g : hermA D r → ℂ) :
    ∫ b, g (congA (rat a) (rat a⁻¹) (rat_mul_inv a ha) (rat_inv_mul a ha) b) ∂lam = ∫ b, g b ∂lam := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D r r
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI i6 : DiscreteTopology (ratMx D r r) := i5
  haveI i7 : SecondCountableTopology (ratMx D r r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D r r) := TopologicalSpace.separableSpace_iff_countable.1
    (TopologicalSpace.SecondCountableTopology.to_separableSpace)
  haveI i8 : SecondCountableTopology (hermA D r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI i9 : BorelSpace (hermA D r) := Subtype.borelSpace _
  have hcl : IsClosed ((hermA D r : AddSubgroup (Mx D r r)) : Set (Mx D r r)) :=
    isClosed_eq continuous_adj continuous_id
  haveI : LocallyCompactSpace (hermA D r) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Countable (ratHerm D r) := by
    let f : ratHerm D r → ratMx D r r := fun x => ⟨x.1.1, x.2⟩
    have hf : Function.Injective f := fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ratMx D r r => z.1) h))
    exact hf.countable
  obtain ⟨hH, hF, h1⟩ := hl
  have hcont : ∀ A : Mx D r r, Continuous (fun b : hermA D r => A ⬝ b.1 ⬝ adj A) := fun A =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have hrat : ∀ (c : Matrix (Fin r) (Fin r) D.host.E) (γ : hermA D r), γ ∈ ratHerm D r →
      rat c ⬝ γ.1 ⬝ adj (rat c) ∈ ratMx D r r := by
    rintro c ⟨_, _⟩ ⟨γ, rfl⟩
    refine ⟨c * γ * cᴴ, ?_⟩
    show rat (c * γ * cᴴ) = _
    rw [rat_mul, rat_mul, rat_conjTranspose]
    rfl
  exact integral_comp_of_covol (ratHerm D r) lam 𝓖 hF h1
    (congA (rat a) (rat a⁻¹) (rat_mul_inv a ha) (rat_inv_mul a ha))
    ((hcont _).subtype_mk _) ((hcont _).subtype_mk _)
    (fun γ hγ => hrat a γ hγ) (fun γ hγ => hrat a⁻¹ γ hγ) g

theorem inner_mul_right (V : HSp D) {r : ℕ} (y : Mx D V.rank r) (A : Mx D r r) :
    GlobalTheory.StdUnn.inner V (y ⬝ A) (y ⬝ A) = adj A ⬝ GlobalTheory.StdUnn.inner V y y ⬝ A := by
  simp only [GlobalTheory.StdUnn.inner, adj_mul, Matrix.mul_assoc]

theorem trace_cong_left {r : ℕ} (P A b Q : Mx D r r) :
    Matrix.trace (P ⬝ (A ⬝ b ⬝ Q)) = Matrix.trace (Q ⬝ P ⬝ A ⬝ b) := by
  calc Matrix.trace (P ⬝ (A ⬝ b ⬝ Q)) = Matrix.trace ((P ⬝ A ⬝ b) ⬝ Q) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Q ⬝ (P ⬝ A ⬝ b)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Q ⬝ P ⬝ A ⬝ b) := by simp only [Matrix.mul_assoc]

theorem trace_cong_inner {r : ℕ} (A B b I : Mx D r r) (h1 : A * B = 1) (h2 : B * A = 1) :
    Matrix.trace ((B ⬝ b ⬝ adj B) ⬝ (adj A ⬝ I ⬝ A)) = Matrix.trace (b ⬝ I) := by
  have h3 : adj B ⬝ adj A = 1 := by rw [← adj_mul, h1, adj_one]
  calc Matrix.trace ((B ⬝ b ⬝ adj B) ⬝ (adj A ⬝ I ⬝ A))
      = Matrix.trace (B ⬝ (b ⬝ ((adj B ⬝ adj A) ⬝ (I ⬝ A)))) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (B ⬝ (b ⬝ (I ⬝ A))) := by
        rw [h3]
        simp
    _ = Matrix.trace ((b ⬝ (I ⬝ A)) ⬝ B) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (b ⬝ I ⬝ (A ⬝ B)) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (b ⬝ I) := by
        rw [h1]
        simp

theorem rat_congrH {r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (β : HermE D r) :
    (congrH a β).1.map (incA D) = adj (rat a) ⬝ β.1.map (incA D) ⬝ rat a := by
  have h : (congrH a β).1 = aᴴ * β.1 * a := rfl
  rw [h]
  show rat (aᴴ * β.1 * a) = _
  rw [rat_mul, rat_mul, rat_conjTranspose]
  rfl

theorem W_congr : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (φ : Mx D V.rank r → ℂ) (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → (∃ 𝓖, IsCovolOneH lam 𝓖) → W ψ V μ lam (pull a φ) β = W ψ V μ lam φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) := by
  intro D r V ψ μ lam φ β a ha ⟨𝓕, hμ⟩ ⟨𝓖, hl⟩
  set S := congA (rat a) (rat a⁻¹) (rat_mul_inv a ha) (rat_inv_mul a ha) with hS
  have hJ : ∀ b, Jt ψ V μ (pull a φ) b = Jt ψ V μ φ (S.symm b) := by
    intro b
    unfold Jt
    refine Eq.trans ?_ (integral_mulRight hμ a ha _)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show φ (y ⬝ rat a) * _ = φ (y ⬝ rat a) * _
    congr 3
    have : (S.symm b).1 = rat a⁻¹ ⬝ b.1 ⬝ adj (rat a⁻¹) := rfl
    rw [this, inner_mul_right, trace_cong_inner _ _ _ _ (rat_mul_inv a ha) (rat_inv_mul a ha)]
  unfold W
  simp only [hJ]
  refine (integral_congA hl a ha _).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [← hS, AddEquiv.symm_apply_apply]
  congr 4
  have : (S b).1 = rat a ⬝ b.1 ⬝ adj (rat a) := rfl
  rw [this, trace_cong_left, rat_congrH]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCoefficientCongruencePullbackStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_coefficient_congruence_pullback : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (φ : Mx D V.rank r → ℂ) (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → (∃ 𝓖, IsCovolOneH lam 𝓖) → W ψ V μ lam (pull a φ) β = W ψ V μ lam φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.W_congr | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.W_congr | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.W_congr <;> assumption)
end
end
