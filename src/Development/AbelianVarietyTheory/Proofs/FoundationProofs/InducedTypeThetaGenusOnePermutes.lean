module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.InducedType

open Formalism.FrobeniusOrbits Formalism.MainNotions.UnusedSlot33.HK

theorem sigmaOf_mul {R : Ranks} (H : Host R) (g g' : R.GG) :
    H.sigmaOf (g * g') = H.sigmaOf g * H.sigmaOf g' := map_mul (H.gal).symm g g'

theorem sigmaOf_one {R : Ranks} (H : Host R) : H.sigmaOf 1 = 1 := map_one (H.gal).symm

theorem emb_apply {R : Ranks} (H : Host R) (g : R.GG) (x : H.E) : H.emb g x = H.φ₀ (H.sigmaOf g x) := rfl

def galK {R : Ranks} (H : Host R) (g : R.Psi) : H.E ≃ₐ[H.K] H.E :=
  { (H.sigmaOf g : H.E ≃+* H.E) with
    commutes' := fun a => sigmaOf_fix_K H g g.2 a a.2 }

theorem galK_apply {R : Ranks} (H : Host R) (g : R.Psi) (x : H.E) : galK H g x = H.sigmaOf g x := rfl

theorem galK_bijective {R : Ranks} (H : Host R) : Function.Bijective (galK H) := by
  constructor
  · intro g g' h
    apply Subtype.ext
    apply (H.gal).symm.injective
    exact AlgEquiv.ext fun x => congrArg (fun f : H.E ≃ₐ[H.K] H.E => f x) h
  · intro s
    refine ⟨⟨H.galE (s.restrictScalars ℚ), ?_⟩, ?_⟩
    · rw [H.galE_mem_Psi_iff]
      exact s.commutes ⟨_, bE_mem H⟩
    · refine AlgEquiv.ext fun x => ?_
      rw [galK_apply, sigmaOf_galE]
      rfl

theorem restrict_K (D : D7) : GL3Theta.InducedCMType D := fun τ a => by
  change D.host.φ₀ (D.host.sigmaOf _ _) = _
  rw [sigmaOf_fix_K D.host _ (D.eTau τ).2 _ a.2]

theorem sum_eq_trace (D : D7) : TraceMapNormalisation D := fun y => by
  have hE := D.host.hostE_isGalois
  have h := trace_eq_sum_automorphisms (K := D.host.K) (L := D.host.E) y
  change _ = D.host.φ₀ (algebraMap D.host.K D.host.E _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  exact Fintype.sum_bijective (galK D.host ∘ D.eTau) ((galK_bijective D.host).comp D.eTau.bijective) _ _
    (fun τ => rfl)

theorem permutes (D : D7) : EmbeddingPermutesTypes D := fun M ρ hK hM => by
  have h0 : ∀ x, D.host.φ₀ x ∈ M := fun x => by
    have := hM (D.eTau.symm 1) x
    rwa [embT, Equiv.apply_symm_apply, emb_apply, Subgroup.coe_one, sigmaOf_one] at this
  let ψ : D.host.E →+* ℂ := (ρ : M →+* ℂ).comp (D.host.φ₀.codRestrict M h0)
  have hψ : ∀ x, cj M ρ (D.host.φ₀ x) = ψ x := fun x => by
    rw [cj, TaylorLogMetric.liftM, dite_eq_left (h0 x)]
    rfl
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 ψ
  have hgP : g ∈ D.R.Psi := by
    rw [← galE_sigmaOf D.host g, D.host.galE_mem_Psi_iff]
    apply D.host.φ₀.injective
    rw [← emb_apply, hg, ← hψ]
    exact (hK ⟨_, bE_mem D.host⟩).2
  refine ⟨D.eTau.trans ((Equiv.mulLeft (⟨g, hgP⟩ : D.R.Psi)).trans D.eTau.symm), fun τ x => ?_⟩
  rw [embT, emb_apply, hψ, ← hg, embT, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.coe_mulLeft, Subgroup.coe_mul, emb_apply, emb_apply, sigmaOf_mul]
  rfl

theorem induced_type : ∀ D : D7, admG1 D ∧ EmbeddingPermutesTypes D :=
  fun D => ⟨⟨restrict_K D, sum_eq_trace D⟩, permutes D⟩

end GlobalTheory.InducedType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedType_thetaGenusOne_permutes : ∀ D : D7, admG1 D ∧ EmbeddingPermutesTypes D := by
  first | exact @GlobalTheory.InducedType.induced_type | exact GlobalTheory.InducedType.induced_type | (intros; apply GlobalTheory.InducedType.induced_type <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OddTheta

theorem area_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    area Λ = latticeArea L := by
  have hA := latticeArea_eq L
  have hpos := latticeArea_pos L
  have key : ∀ w₁ ∈ L.lattice, ∀ w₂ ∈ L.lattice, ∃ k : ℤ,
      ((starRingEnd ℂ) w₁ * w₂).im = k * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im := by
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hw₁
    obtain ⟨m', n', rfl⟩ := PeriodPair.mem_lattice.1 hw₂
    refine ⟨m * n' - n * m', ?_⟩
    simp [Complex.mul_im, Complex.mul_re]
    ring
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨hA ▸ hpos, L.ω₁, (h _).2 L.ω₁_mem_lattice, L.ω₂, (h _).2 L.ω₂_mem_lattice, hA⟩, ?_⟩
  rintro a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩
  obtain ⟨k, hk⟩ := key w₁ ((h _).1 hw₁) w₂ ((h _).1 hw₂)
  rw [hk, abs_mul, ← hA] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  exact le_mul_of_one_le_left hpos.le hk1

theorem wpF_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) (z : ℂ) :
    wpF Λ z = L.weierstrassP z := by
  have hs : Summable (fun l : L.lattice => 1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) :=
    (L.hasSum_weierstrassP z).summable
  unfold wpF PeriodPair.weierstrassP
  rw [← hs.tsum_subtype_add_tsum_subtype_compl ({0} : Set L.lattice),
    tsum_singleton (0 : L.lattice) (fun l : L.lattice => 1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)]
  congr 1
  · simp
  · let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ (({0} : Set L.lattice)ᶜ : Set L.lattice) :=
      { toFun := fun w => ⟨⟨w.1, (h w.1).1 w.2.1⟩, fun hh =>
          w.2.2 (by simpa using congrArg Subtype.val (Set.mem_singleton_iff.1 hh))⟩
        invFun := fun l => ⟨l.1.1, (h _).2 l.1.2, fun hh =>
          l.2 (Set.mem_singleton_iff.2 (Subtype.ext (by simpa using hh)))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (e.tsum_eq (fun l => 1 / (z - ((l : L.lattice) : ℂ)) ^ 2 - 1 / ((l : L.lattice) : ℂ) ^ 2))

theorem law_iff (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (G : ℂ → ℂ) (ω z : ℂ) :
    U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z ↔
      G (z + ω) = sigmaSign L ω * Complex.exp (Real.pi * latticeForm L z ω +
        Real.pi * latticeForm L ω ω / 2) * G z := by
  have hs : (if ω / 2 ∈ Λ then (1 : ℂ) else -1) = sigmaSign L ω := by
    by_cases hw : ω / 2 ∈ Λ
    · rw [if_pos hw, sigmaSign_of_mem L ((h _).1 hw)]
    · rw [if_neg hw, sigmaSign_of_notMem L (fun hh => hw ((h _).2 hh))]
  have hU : U1 Λ ω G z = G (z + ω) *
      (Complex.exp (Real.pi * latticeForm L z ω + Real.pi * latticeForm L ω ω / 2))⁻¹ := by
    unfold U1
    rw [area_eq L Λ h, ← Complex.exp_neg]
    congr 2
    simp only [latticeForm]
    ring
  rw [hU, hs, mul_inv_eq_iff_eq_mul₀ (Complex.exp_ne_zero _)]
  constructor <;> intro hh <;> rw [hh] <;> ring

theorem eq_deriv_mul (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hlaw : ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) (z : ℂ) :
    G z = deriv G 0 * canonicalSigma L z := by
  have hlaw' : ∀ w ∈ L.lattice, ∀ z, G (z + w) = sigmaSign L w *
      Complex.exp (Real.pi * latticeForm L z w + Real.pi * latticeForm L w w / 2) * G z :=
    fun w hw z => (law_iff L Λ h G w z).1 (hlaw w ((h w).2 hw) z)
  obtain ⟨c, hc⟩ := exists_eq_mul_canonicalSigma L hG hlaw'
  have hGf : G = fun z => c * canonicalSigma L z := funext hc
  have hd : deriv G 0 = c := by
    rw [hGf]
    exact ((hasDerivAt_canonicalSigma_zero L).const_mul c).deriv.trans (mul_one c)
  rw [hd]
  exact hc z

theorem canonicalSigma_spec (L : PeriodPair) (Λ : AddSubgroup ℂ)
    (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    Differentiable ℂ (canonicalSigma L) ∧ deriv (canonicalSigma L) 0 = 1 ∧
      (∀ z, canonicalSigma L (-z) = -canonicalSigma L z) ∧
      ∀ ω ∈ Λ, ∀ z, U1 Λ ω (canonicalSigma L) z =
        (if ω / 2 ∈ Λ then 1 else -1) * canonicalSigma L z := by
  refine ⟨differentiable_canonicalSigma L, (hasDerivAt_canonicalSigma_zero L).deriv,
    canonicalSigma_neg L, ?_⟩
  intro ω hω z
  exact (law_iff L Λ h _ ω z).2 (canonicalSigma_add L ((h ω).1 hω) z)

theorem sgStar_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    sgStar Λ = canonicalSigma L := by
  have hP : ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
      ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z :=
    ⟨_, canonicalSigma_spec L Λ h⟩
  unfold sgStar
  obtain ⟨hd, h1, -, hl⟩ := Classical.epsilon_spec hP
  funext z
  rw [eq_deriv_mul L Λ h _ hd hl z, h1, one_mul]

theorem exists_periodPair (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  obtain ⟨w₁, w₂, hind, rfl⟩ := hΛ
  refine ⟨⟨w₁, w₂, hind⟩, fun z => ?_⟩
  show z ∈ AddSubgroup.closure {w₁, w₂} ↔ z ∈ Submodule.span ℤ {w₁, w₂}
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]

theorem sgStar_laws : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → (Differentiable ℂ (sgStar Λ) ∧ deriv (sgStar Λ) 0 = 1 ∧ (∀ z, sgStar Λ (-z) = -sgStar Λ z) ∧ ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z) ∧ (∀ z, sgStar Λ z = 0 ↔ z ∈ Λ) ∧ (∀ G : ℂ → ℂ, Differentiable ℂ G → (∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) → ∀ z, G z = deriv G 0 * sgStar Λ z) ∧ (∀ u v : ℂ, u ∉ Λ → v ∉ Λ → (wpF Λ u - wpF Λ v) * (sgStar Λ u ^ 2 * sgStar Λ v ^ 2) = -(sgStar Λ (u + v) * sgStar Λ (u - v))) ∧ ∀ c : ℂ, c ≠ 0 → ∀ z, sgStar (Λ.map (AddMonoidHom.mulLeft c)) (c * z) = c * sgStar Λ z := by
  intro Λ hΛ
  obtain ⟨L, h⟩ := exists_periodPair Λ hΛ
  have hσ := sgStar_eq L Λ h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ]
    exact canonicalSigma_spec L Λ h
  · intro z
    rw [hσ, canonicalSigma_eq_zero_iff L, h]
  · intro G hG hl z
    rw [hσ]
    exact eq_deriv_mul L Λ h G hG hl z
  · intro u v hu hv
    have hu' : u ∉ L.lattice := fun hh => hu ((h u).2 hh)
    have hv' : v ∉ L.lattice := fun hh => hv ((h v).2 hh)
    have hne : canonicalSigma L u ^ 2 * canonicalSigma L v ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ ((canonicalSigma_eq_zero_iff L).not.2 hu'))
        (pow_ne_zero _ ((canonicalSigma_eq_zero_iff L).not.2 hv'))
    rw [wpF_eq L Λ h, wpF_eq L Λ h, hσ, weierstrassP_sub_weierstrassP_canonicalSigma L hu' hv']
    exact div_mul_cancel₀ _ hne
  · intro c hc z
    have hhom := isHomothetic_scalePeriods L c hc
    have h' : ∀ x, x ∈ Λ.map (AddMonoidHom.mulLeft c) ↔ x ∈ (scalePeriods L c hc).lattice := by
      intro x
      rw [AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hhom y).2 ((h y).1 hy)
      · intro hx
        refine ⟨c⁻¹ * x, (h _).2 ((hhom _).1 ?_), ?_⟩
        · rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
        · simp [hc]
    rw [sgStar_eq (scalePeriods L c hc) _ h', hσ, hhom.canonicalSigma_mul]

end GlobalTheory.OddTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniquenessStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oddThetaFunction_existence_uniqueness : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → (Differentiable ℂ (sgStar Λ) ∧ deriv (sgStar Λ) 0 = 1 ∧ (∀ z, sgStar Λ (-z) = -sgStar Λ z) ∧ ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z) ∧ (∀ z, sgStar Λ z = 0 ↔ z ∈ Λ) ∧ (∀ G : ℂ → ℂ, Differentiable ℂ G → (∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) → ∀ z, G z = deriv G 0 * sgStar Λ z) ∧ (∀ u v : ℂ, u ∉ Λ → v ∉ Λ → (wpF Λ u - wpF Λ v) * (sgStar Λ u ^ 2 * sgStar Λ v ^ 2) = -(sgStar Λ (u + v) * sgStar Λ (u - v))) ∧ ∀ c : ℂ, c ≠ 0 → ∀ z, sgStar (Λ.map (AddMonoidHom.mulLeft c)) (c * z) = c * sgStar Λ z := by
  first | exact @GlobalTheory.OddTheta.sgStar_laws | exact GlobalTheory.OddTheta.sgStar_laws | (intros; apply GlobalTheory.OddTheta.sgStar_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.CurveLattice

open scoped UpperHalfPlane nonZeroDivisors Real

theorem eisG_eq_G (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    {k : ℕ} (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  have h1 : eisG Λ k = ∑' z : ℂ, ({w : ℂ | w ∈ Λ ∧ w ≠ 0}).indicator (fun w => (w ^ (2 * k))⁻¹) z := by
    rw [← tsum_subtype, eisG]
    exact tsum_congr fun w => one_div _
  have h2 : L.G (2 * k) = ∑' z : ℂ, (L.lattice : Set ℂ).indicator (fun w => (w ^ (2 * k))⁻¹) z := by
    rw [← tsum_subtype, PeriodPair.G]
    rfl
  rw [h1, h2]
  refine tsum_congr fun z => ?_
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Set.indicator, hk]
  · simp [Set.indicator, hz, h]

section

variable {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha

theorem indep_of_tau : LinearIndependent ℝ ![a * (τ : ℂ), a] := by
  rw [LinearIndependent.pair_iff]
  intro s t e
  have e2 : (s * τ + t : ℂ) = 0 := mul_left_cancel₀ ha (by
    simp only [Complex.real_smul] at e
    linear_combination e)
  have e3 : s = 0 := by simpa [τ.im_ne_zero] using congrArg Complex.im e2
  exact ⟨e3, by simpa [e3] using e2⟩

include h

omit ha in
theorem eq_closure_of_tau : Λ = AddSubgroup.closure {a * (τ : ℂ), a} := by
  ext x
  rw [h, AddSubgroup.mem_closure_pair]
  refine exists_congr fun m => exists_congr fun n => ?_
  rw [zsmul_eq_mul, zsmul_eq_mul, show (m : ℂ) * (a * τ) + n * a = a * (m * τ + n) by ring]

theorem discr_of_tau : TaylorLogMetric.discr Λ = (2 * π / a) ^ 12 * ModularForm.discriminant τ := by
  let L : PeriodPair := ⟨a * τ, a, indep_of_tau ha⟩
  have hL : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := fun x => by
    rw [PeriodPair.mem_lattice]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [show (m : ℂ) * L.ω₁ + n * L.ω₂ = a * (m * τ + n) by simp only [L]; ring]
  have hh : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z => by rw [h, hL]
  rw [← latticeCurve_Δ_eq_discriminant ha hL, latticeCurve_Δ, TaylorLogMetric.discr, g2, g3,
    eisG_eq_G L Λ hh (by norm_num), eisG_eq_G L Λ hh (by norm_num)]
  rfl

theorem area_of_tau : area Λ = ‖a‖ ^ 2 * τ.im := by
  have hy := τ.im_pos
  have hp : 0 < ‖a‖ ^ 2 * τ.im := by have := norm_pos_iff.2 ha; positivity
  have key : ∀ m n m' n' : ℤ, |((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im| =
      ‖a‖ ^ 2 * τ.im * |((n * m' - m * n' : ℤ) : ℝ)| := fun m n m' n' => by
    rw [← abs_of_pos hp, ← abs_mul]
    congr 1
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨hp, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩
    rw [key]
    simp
  · rintro r ⟨hr, w₁, h1, w₂, h2, rfl⟩
    obtain ⟨m, n, rfl⟩ := (h _).1 h1
    obtain ⟨m', n', rfl⟩ := (h _).1 h2
    rw [key] at hr ⊢
    have h0 : (n * m' - m * n' : ℤ) ≠ 0 := fun e => by simp [e] at hr
    have : (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
    exact le_mul_of_one_le_right hp.le this

end

theorem mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ w : ℂ) :
    w ∈ lamOf D cc δ ↔ ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem finrank_hostK (D : D7) : Module.finrank ℚ D.host.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K D.host.hyp.2.1.pos (D.host.sqd_sq)

theorem discr_hostK (D : D7) : NumberField.discr D.host.K = -(D.host.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_hostK D) D.host.hyp.2.1.squarefree
    (by have := D.host.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq))

theorem exists_tau (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧ (Ideal.absNorm cc : ℝ) = 2 * ‖a‖ ^ 2 * τ.im / √(D.host.d) ∧
      ∀ δ x : ℂ, x ∈ lamOf D cc δ ↔ ∃ m n : ℤ, δ * a * (m * (τ : ℂ) + n) = x := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let I : (Ideal (𝓞 D.host.K))⁰ := ⟨cc, mem_nonZeroDivisors_of_ne_zero hcc⟩
  obtain ⟨L, hL⟩ := QuadraticZeta.exists_periodPair (finrank_hostK D) (discr_hostK D) σ
    (FractionalIdeal.mk0 D.host.K I)
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have h' : ∀ z, z ∈ σ '' (cc : FractionalIdeal (𝓞 D.host.K)⁰ D.host.K) ↔
      ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = z := fun z => by
    rw [← h, ← SetLike.mem_coe, hL]
    rfl
  have hN := QuadraticZeta.absNorm_eq_of_image (finrank_hostK D) (discr_hostK D) σ ha h'
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at hN
  refine ⟨a, τ, ha, hN, fun δ x => ?_⟩
  rw [mem_lamOf]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨m, n, e⟩ := (h' _).1 ⟨(c : D.host.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
    exact ⟨m, n, by rw [mul_assoc, e]; rfl⟩
  · rintro ⟨m, n, rfl⟩
    obtain ⟨y, hy, e⟩ := (h' _).2 ⟨m, n, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, by rw [mul_assoc, ← e]; rfl⟩

theorem lattice_of_curve : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂}) ∧ δ ≠ 0 ∧ TaylorLogMetric.discr (lamOf D cc δ) = 1 ∧ area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ (∀ a : 𝓞 D.host.K, ∀ w ∈ (lamOf D cc δ), D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ (lamOf D cc δ)) := by
  intro D _ cc δ ⟨⟨hcc, _⟩, hδ⟩
  obtain ⟨a, τ, ha, hN, h⟩ := exists_tau D cc hcc
  have h1 := discr_of_tau (by simpa using ha) (h 1)
  rw [one_mul] at h1
  have hδ' : δ ^ 12 = (2 * π / a) ^ 12 * ModularForm.discriminant τ := hδ.trans h1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have := ModularForm.discriminant_ne_zero τ
    have := Real.pi_ne_zero
    simp [*] at hδ'
  have hda : δ * a ≠ 0 := mul_ne_zero hδ0 ha
  refine ⟨⟨_, _, indep_of_tau (τ := τ) hda, eq_closure_of_tau (h δ)⟩, hδ0, ?_, ?_, ?_⟩
  · rw [discr_of_tau hda (h δ), show (2 * π / (δ * a) : ℂ) ^ 12 * ModularForm.discriminant τ =
      ((2 * π / a) ^ 12 * ModularForm.discriminant τ) / δ ^ 12 by field_simp, ← hδ',
      div_self (pow_ne_zero _ hδ0)]
  · have hd : 0 < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
    rw [area_of_tau hda (h δ), hN, norm_mul]
    field_simp
  · intro b w hw
    obtain ⟨c, hc, rfl⟩ := (mem_lamOf D cc δ w).1 hw
    exact (mem_lamOf D cc δ _).2 ⟨b * c, cc.mul_mem_left b hc, by simp; ring⟩

end GlobalTheory.CurveLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatumStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealPeriodLattice_of_curveDatum : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂}) ∧ δ ≠ 0 ∧ TaylorLogMetric.discr (lamOf D cc δ) = 1 ∧ area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ (∀ a : 𝓞 D.host.K, ∀ w ∈ (lamOf D cc δ), D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ (lamOf D cc δ)) := by
  first | exact @GlobalTheory.CurveLattice.lattice_of_curve | exact GlobalTheory.CurveLattice.lattice_of_curve | (intros; apply GlobalTheory.CurveLattice.lattice_of_curve <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.LatticeInvariants

lemma tsum_subtype_congr {p q : ℂ → Prop} (f : ℂ → ℂ) (h : ∀ w, f w ≠ 0 → (p w ↔ q w)) :
    ∑' w : {w // p w}, f w = ∑' w : {w // q w}, f w := by
  refine (tsum_subtype {w | p w} f).trans (Eq.trans ?_ (tsum_subtype {w | q w} f).symm)
  congr with w
  by_cases h0 : f w = 0
  · simp [Set.indicator, h0]
  · simp [Set.indicator, h w h0]

lemma eisG_eq_tsum (Λ : AddSubgroup ℂ) {k : ℕ} (hk : k ≠ 0) :
    eisG Λ k = ∑' w : Λ, ((w : ℂ) ^ (2 * k))⁻¹ := by
  simp only [eisG, one_div]
  refine tsum_subtype_congr (p := fun w ↦ w ∈ Λ ∧ w ≠ 0) (q := fun w ↦ w ∈ Λ)
    (fun w ↦ (w ^ (2 * k))⁻¹) fun w hw ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  rintro rfl
  simp [hk] at hw

section

variable {L : PeriodPair} {Λ : AddSubgroup ℂ} (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
include h

lemma eisG_eq_G {k : ℕ} (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  rw [eisG_eq_tsum Λ hk]
  exact tsum_subtype_congr (p := fun w ↦ w ∈ Λ) (q := fun w ↦ w ∈ L.lattice)
    (fun w ↦ (w ^ (2 * k))⁻¹) fun w _ ↦ h w

lemma g2_eq : g2 Λ = L.g₂ := by rw [g2, eisG_eq_G h two_ne_zero]; rfl

lemma lattice_invariant_g3_eq : g3 Λ = L.g₃ := by rw [g3, eisG_eq_G h three_ne_zero]; rfl

lemma wpD_eq (z : ℂ) : wpD Λ z = L.derivWeierstrassP z := by
  rw [wpD, PeriodPair.derivWeierstrassP, neg_mul, ← tsum_mul_left]
  simp only [mul_one_div]
  congr 1
  exact tsum_subtype_congr (p := fun w ↦ w ∈ Λ) (q := fun w ↦ w ∈ L.lattice)
    (fun w ↦ 2 / (z - w) ^ 3) fun w _ ↦ h w

lemma wpF_eq (z : ℂ) : wpF Λ z = L.weierstrassP z := by
  rw [← L.weierstrassPExcept_add 0, wpF, add_comm]
  congr 1
  · refine Eq.trans (tsum_congr fun w ↦ ?_) (tsum_subtype_congr (p := fun w ↦ w ∈ Λ ∧ w ≠ 0)
      (q := fun w ↦ w ∈ L.lattice)
      (fun w ↦ if w = 0 then 0 else 1 / (z - w) ^ 2 - 1 / w ^ 2) fun w hw ↦ ?_)
    · rw [if_neg w.2.2]
    · have : w ≠ 0 := by rintro rfl; simp at hw
      simp [h, this]
  · simp

lemma area_eq : area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  refine IsLeast.csInf_eq ⟨⟨?_, L.ω₂, (h _).2 L.ω₂_mem_lattice, L.ω₁, (h _).2 L.ω₁_mem_lattice,
    by rw [mul_comm]⟩, ?_⟩
  · rw [abs_pos]
    intro h0
    have hi := LinearIndependent.pair_iff.mp L.indep
    simp only [Complex.mul_im, Complex.conj_im, Complex.conj_re] at h0
    have h1 := hi L.ω₂.re (-L.ω₁.re) (by
      apply Complex.ext <;> simp
      · ring
      · linarith)
    have h2 := hi L.ω₂.im (-L.ω₁.im) (by
      apply Complex.ext <;> simp
      · linarith
      · ring)
    have h3 : L.ω₂ = 0 := Complex.ext h1.1 h2.1
    simpa using (hi 0 1 (by simp [h3])).2
  · rintro a ⟨ha, w₁, h₁, w₂, h₂, rfl⟩
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h₁)
    obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h₂)
    have e : (starRingEnd ℂ (m * L.ω₁ + n * L.ω₂) * (p * L.ω₁ + q * L.ω₂)).im =
        (n * p - m * q : ℤ) * (L.ω₁ * starRingEnd ℂ L.ω₂).im := by
      simp
      ring
    rw [e, abs_mul] at ha ⊢
    have h1 : (n * p - m * q : ℤ) ≠ 0 := by
      intro h0
      simp [h0] at ha
    have h2 : (1 : ℝ) ≤ |((n * p - m * q : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h1
    exact le_mul_of_one_le_left (abs_nonneg _) h2

end

lemma discrete_of_eisG_ne_zero {Λ : AddSubgroup ℂ} {k : ℕ} (hk : k ≠ 0) (h : eisG Λ k ≠ 0) :
    DiscreteTopology Λ := by
  rw [eisG_eq_tsum Λ hk] at h
  have hs : Summable fun w : Λ ↦ ((w : ℂ) ^ (2 * k))⁻¹ := by
    by_contra hs
    exact h (tsum_eq_zero_of_not_summable hs)
  have hf : {w : Λ | ¬ ‖((w : ℂ) ^ (2 * k))⁻¹‖ < 1}.Finite :=
    Filter.eventually_cofinite.1
      ((tendsto_zero_iff_norm_tendsto_zero.1 hs.tendsto_cofinite_zero).eventually_lt_const one_pos)
  refine discreteTopology_iff_isOpen_singleton_zero.2 ?_
  have ho : IsOpen {w : Λ | ‖(w : ℂ)‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  convert ho.sdiff hf.isClosed using 1
  ext w
  simp only [Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_setOf_eq, not_not]
  constructor
  · rintro rfl
    simp [hk]
  · rintro ⟨h1, h2⟩
    by_contra h0
    have h3 : 0 < ‖(w : ℂ)‖ := by simpa using h0
    rw [norm_inv, norm_pow] at h2
    exact absurd h2 (not_lt.2 ((one_le_inv₀ (by positivity)).2 (pow_le_one₀ h3.le h1.le)))

lemma eisG_of_cyclic {Λ : AddSubgroup ℂ} {a : ℂ} (ha : a ∈ Λ) (h : ∀ w ∈ Λ, ∃ m : ℤ, m • a = w)
    {k : ℕ} (hk : k ≠ 0) : eisG Λ k = (a ^ (2 * k))⁻¹ * (2 * riemannZeta (2 * k : ℕ)) := by
  rw [eisG_eq_tsum Λ hk]
  rcases eq_or_ne a 0 with rfl | h0
  · have : ∀ w : Λ, (w : ℂ) = 0 := fun w ↦ by simpa [eq_comm] using h w w.2
    simp [this, hk]
  let e : ℤ → Λ := fun m ↦ ⟨m • a, Λ.zsmul_mem ha m⟩
  have he : Function.Bijective e := ⟨fun m n hmn ↦ by simpa [e, h0] using hmn,
    fun w ↦ (h w w.2).imp fun m hm ↦ Subtype.ext hm⟩
  rw [← (Equiv.ofBijective e he).tsum_eq,
    two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by omega) (even_two_mul k), ← tsum_mul_left]
  congr with m
  simp [e, mul_pow]

lemma discr_of_cyclic {Λ : AddSubgroup ℂ} {a : ℂ} (ha : a ∈ Λ)
    (h : ∀ w ∈ Λ, ∃ m : ℤ, m • a = w) : TaylorLogMetric.discr Λ = 0 := by
  have h6 : riemannZeta 6 = Real.pi ^ 6 / 945 := by
    have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show bernoulli (2 * 3) = 1 / 42 by decide +kernel] at this
    norm_num [Nat.factorial] at this
    rw [this]
    ring
  rw [TaylorLogMetric.discr, g2, g3, eisG_of_cyclic ha h two_ne_zero, eisG_of_cyclic ha h three_ne_zero]
  norm_num only [riemannZeta_four, h6]
  simp only [← inv_pow]
  ring

lemma exists_periodPair_of_discr_ne_zero {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  have hd : DiscreteTopology Λ := by
    by_cases h2 : eisG Λ 2 = 0
    · refine discrete_of_eisG_ne_zero three_ne_zero fun h3 ↦ h ?_
      simp [TaylorLogMetric.discr, g2, g3, h2, h3]
    · exact discrete_of_eisG_ne_zero two_ne_zero h2
  let M : Submodule ℤ ℂ := AddSubgroup.toIntSubmodule Λ
  have hM : DiscreteTopology M := hd
  by_cases hs : Submodule.span ℝ (M : Set ℂ) = ⊤
  · have hZ : IsZLattice ℝ M := ⟨hs⟩
    let b := Module.finBasisOfFinrankEq ℤ M ((ZLattice.rank ℝ M).trans Complex.finrank_real_complex)
    have hi := (b.ofZLatticeBasis ℝ M).linearIndependent
    have e : ⇑(b.ofZLatticeBasis ℝ M) = ![(b 0 : ℂ), b 1] := by
      ext i
      fin_cases i <;> simp
    refine ⟨⟨b 0, b 1, e ▸ hi⟩, fun z ↦ ?_⟩
    change z ∈ M ↔ z ∈ Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)}
    rw [← Matrix.range_cons_cons_empty _ _ ![], ← e, b.ofZLatticeBasis_span ℝ M]
  · have h1 : Module.finrank ℤ M ≤ 1 := by
      have e := Real.finrank_eq_int_finrank_of_discrete (s := (M : Set ℂ))
        (by rw [Submodule.span_eq]; exact hM)
      rw [Set.finrank, Set.finrank, Submodule.span_eq] at e
      have := Submodule.finrank_lt hs
      rw [Complex.finrank_real_complex] at this
      omega
    obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h1
    exact absurd (discr_of_cyclic (a := v) v.2 fun w hw ↦
      (hv ⟨w, hw⟩).imp fun m hm ↦ congrArg Subtype.val hm) h

lemma exists_periodPair_of_invariants {a b : ℂ} (h : a ^ 3 - 27 * b ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b := by
  obtain ⟨τ, hτ⟩ := exists_E₄_cube_div_discriminant_eq (1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2))
  let L := periodPairOfTau τ
  have h1 := g₂_cube_div_eq_modularJ one_ne_zero (mem_lattice_periodPairOfTau τ)
  have h0 := g₂_cube_sub_g₃_sq_ne_zero L
  rw [modularJ_def, hτ, div_eq_div_iff h0 h] at h1
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq h0 h (by linear_combination h1 / 1728)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hu (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  refine ⟨scalePeriods L c hc0, ?_, ?_⟩
  · rw [H.g₂_eq, h2, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; simp
  · rw [H.g₃_eq, h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; simp

theorem invariants_dictionary : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z, z ∈ Λ ↔ z ∈ L.lattice) → g2 Λ = L.g₂ ∧ g3 Λ = L.g₃ ∧ TaylorLogMetric.discr Λ ≠ 0 ∧ area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ (∀ z, z ∉ Λ → wpF Λ z = L.weierstrassP z ∧ wpD Λ z = L.derivWeierstrassP z) ∧ (∀ (Λ' : AddSubgroup ℂ), g2 Λ' = g2 Λ → g3 Λ' = g3 Λ → Λ' = Λ) ∧ ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ (L' : PeriodPair), L'.g₂ = a ∧ L'.g₃ = b := by
  intro L Λ h
  have hΔ : TaylorLogMetric.discr Λ ≠ 0 := by
    rw [TaylorLogMetric.discr, g2_eq h, lattice_invariant_g3_eq h]
    exact g₂_cube_sub_g₃_sq_ne_zero L
  refine ⟨g2_eq h, lattice_invariant_g3_eq h, hΔ, area_eq h, fun z _ ↦ ⟨wpF_eq h z, wpD_eq h z⟩,
    fun Λ' h2 h3 ↦ ?_, fun a b ↦ exists_periodPair_of_invariants⟩
  obtain ⟨L', h'⟩ := exists_periodPair_of_discr_ne_zero (Λ := Λ')
    (by rwa [TaylorLogMetric.discr, h2, h3])
  rw [g2_eq h, g2_eq h'] at h2
  rw [lattice_invariant_g3_eq h, lattice_invariant_g3_eq h'] at h3
  ext z
  rw [h, h', lattice_eq_of_g₂_eq_of_g₃_eq h2 h3]

end GlobalTheory.LatticeInvariants
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionaryStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeInvariants_periodPair_dictionary : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z, z ∈ Λ ↔ z ∈ L.lattice) → g2 Λ = L.g₂ ∧ g3 Λ = L.g₃ ∧ TaylorLogMetric.discr Λ ≠ 0 ∧ area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ (∀ z, z ∉ Λ → wpF Λ z = L.weierstrassP z ∧ wpD Λ z = L.derivWeierstrassP z) ∧ (∀ (Λ' : AddSubgroup ℂ), g2 Λ' = g2 Λ → g3 Λ' = g3 Λ → Λ' = Λ) ∧ ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ (L' : PeriodPair), L'.g₂ = a ∧ L'.g₃ = b := by
  first | exact @GlobalTheory.LatticeInvariants.invariants_dictionary | exact GlobalTheory.LatticeInvariants.invariants_dictionary | (intros; apply GlobalTheory.LatticeInvariants.invariants_dictionary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem isIntegral_half_one_add {L : Type*} [Field L] [CharZero L] (d : ℕ) (hd : d % 16 = 7) (b : L)
    (hb : b ^ 2 = -(d : L)) : IsIntegral ℤ ((1 + b) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 4 * m := ⟨(d + 1) / 4, by omega⟩
  have hm' : (d : L) + 1 = 4 * (m : L) := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
  · monicity!
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_natCast]
    linear_combination (1 / 4 : L) * hb - (1 / 4 : L) * hm'

theorem exists_integer_map_eq_w0 :
    ∀ (D : D7), ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
  intro D
  have hsq := D.host.sqd_sq
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hd0 : (0 : ℝ) ≤ D.host.d := Nat.cast_nonneg _
  have key : ∀ b : D.host.K, (b : D.host.E) ^ 2 = -(D.host.d : D.host.E) →
      D.host.φ₀ (b : D.host.E) = Complex.I * (Real.sqrt D.host.d : ℂ) →
      ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
    intro b hb hφ
    have hb' : b ^ 2 = -(D.host.d : D.host.K) := by
      apply Subtype.ext
      simpa using hb
    refine ⟨⟨(1 + b) / 2, isIntegral_half_one_add _ hd16 b hb'⟩, ?_⟩
    change D.host.φ₀ (algebraMap D.host.K D.host.E ((1 + b) / 2)) = _
    rw [map_div₀, map_add (f := _), map_one, map_ofNat, map_div₀, map_add (f := _), map_one, map_ofNat]
    change (1 + D.host.φ₀ (b : D.host.E)) / 2 = _
    rw [hφ, w0]
  let b : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have h1 : (D.host.φ₀ (b : D.host.E)) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
    change (D.host.φ₀ (D.host.sqd)) ^ 2 = _
    rw [← map_pow, hsq, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt hd0]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact key b hsq h
  · refine key (-b) ?_ ?_
    · change (-(D.host.sqd)) ^ 2 = _
      rw [neg_sq, hsq]
    · change D.host.φ₀ (-(b : D.host.E)) = _
      rw [map_neg, h, neg_neg]

end GlobalTheory.NormSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrtStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_map_eq_halfOneAddSqrt : ∀ (D : D7), ∃ a : 𝓞 D.host.K, D.host.φ₀ (((a : D.host.K) : D.host.E)) = w0 D := by
  first | exact @GlobalTheory.NormSum.exists_integer_map_eq_w0 | exact GlobalTheory.NormSum.exists_integer_map_eq_w0 | (intros; apply GlobalTheory.NormSum.exists_integer_map_eq_w0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.CurveLattice

theorem exists_periodPair_of_im_ne_zero {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℂ) (a : 𝓞 K) (ha : (σ (a : K)).im ≠ 0) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ a ∈ I, z = σ (a : K) := by
  have hr : Module.finrank ℤ I = 2 :=
    (Ideal.finrank_eq_finrank (RingOfIntegers.basis K) I hI).trans ((RingOfIntegers.rank K).trans hK)
  let b : Module.Basis (Fin 2) ℤ I := Module.finBasisOfFinrankEq ℤ _ hr
  have hs : ∀ x : I, σ ((x : 𝓞 K) : K) =
      b.repr x 0 * σ ((b 0 : 𝓞 K) : K) + b.repr x 1 * σ ((b 1 : 𝓞 K) : K) := by
    intro x
    have := congrArg (fun x : I => σ ((x : 𝓞 K) : K)) (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ ((b 0 : 𝓞 K) : K) ≠ 0 := by
    rw [map_ne_zero]
    have : (b 0 : 𝓞 K) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
    exact_mod_cast this
  have h0 : (σ ((b 1 : 𝓞 K) : K) * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im ≠ 0 := by
    intro h0
    have e := hs ⟨a * b 0, I.mul_mem_left a (b 0).2⟩
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at e' h0 ha hb0
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨σ ((b 0 : 𝓞 K) : K), σ ((b 1 : 𝓞 K) : K), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 1 : 𝓞 K) : K)).im * e1 - (σ ((b 1 : 𝓞 K) : K)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 0 : 𝓞 K) : K)).re * e2 - (σ ((b 0 : 𝓞 K) : K)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, _, (hs ⟨x, hx⟩).symm⟩

theorem eisG_eq_periodPair_G (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {k : ℕ} (hk : k ≠ 0) :
    eisG Λ k = L.G (2 * k) := by
  have e1 := tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))
  have e2 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
  refine e1.trans (Eq.trans (tsum_congr fun w => ?_) e2.symm)
  by_cases hw : w = 0
  · subst hw
    simp [Set.indicator, hk]
  · simp [Set.indicator, hw, h]

theorem discr_ne_zero (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) : TaylorLogMetric.discr Λ ≠ 0 := by
  have := g₂_cube_sub_g₃_sq_ne_zero L
  rw [TaylorLogMetric.discr, g2, g3, eisG_eq_periodPair_G Λ L h two_ne_zero, eisG_eq_periodPair_G Λ L h three_ne_zero]
  exact this

theorem mem_lamOf_iff (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ z : ℂ) :
    z ∈ lamOf D cc δ ↔ ∃ c ∈ cc, z = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by simp⟩
  · intro hz
    exact AddSubgroup.subset_closure hz

theorem exists_periodPair_one (D : D7) {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc 1 ↔ z ∈ L.lattice := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  have hK : Module.finrank ℚ D.host.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K hd hb
  let s : D.host.K := ⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hs : s ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa [s] using hb)
  have hint : IsIntegral ℤ s := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hs]
    exact (isIntegral_natCast _).neg
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have him : (σ (((⟨s, hint⟩ : 𝓞 D.host.K) : 𝓞 D.host.K) : D.host.K)).im ≠ 0 := by
    intro h0
    change (σ s).im = 0 at h0
    have e : σ s ^ 2 = -(D.host.d : ℂ) := by rw [← map_pow, hs]; simp
    have e' := congrArg Complex.re e
    simp only [pow_two, Complex.mul_re, h0, Complex.neg_re, Complex.natCast_re] at e'
    have : (0 : ℝ) < D.host.d := by exact_mod_cast hd
    nlinarith [mul_self_nonneg (σ s).re]
  obtain ⟨L, hL⟩ := exists_periodPair_of_im_ne_zero hK σ (⟨s, hint⟩ : 𝓞 D.host.K) him hc
  refine ⟨L, fun z => ?_⟩
  rw [hL, mem_lamOf_iff]
  simp only [one_mul]
  rfl

theorem exists_periodPair_lamOf : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := by
  intro D cc δ h
  obtain ⟨L, hL⟩ := exists_periodPair_one D h.1.1
  have hδ : δ ≠ 0 := by
    rintro rfl
    have e : (0 : ℂ) ^ 12 = TaylorLogMetric.discr (lamOf D cc 1) := h.2
    exact discr_ne_zero _ L hL (by rw [← e]; simp)
  have hind : LinearIndependent ℝ ![δ * L.ω₁, δ * L.ω₂] := by
    have h1 := LinearIndependent.pair_iff.1 L.indep
    rw [LinearIndependent.pair_iff]
    intro x y e
    refine h1 x y (mul_left_cancel₀ hδ ?_)
    simp only [Complex.real_smul] at e ⊢
    linear_combination e
  refine ⟨⟨δ * L.ω₁, δ * L.ω₂, hind⟩, fun z => ?_⟩
  rw [mem_lamOf_iff, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 ((hL _).1 ((mem_lamOf_iff D cc 1 _).2 ⟨c, hc, rfl⟩))
    exact ⟨m, n, by linear_combination δ * e⟩
  · rintro ⟨m, n, rfl⟩
    obtain ⟨c, hc, e⟩ := (mem_lamOf_iff D cc 1 _).1 ((hL _).2 (PeriodPair.mem_lattice.2 ⟨m, n, rfl⟩))
    exact ⟨c, hc, by linear_combination δ * e⟩

end GlobalTheory.CurveLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodPair_idealCurveLattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := by
  first | exact @GlobalTheory.CurveLattice.exists_periodPair_lamOf | exact GlobalTheory.CurveLattice.exists_periodPair_lamOf | (intros; apply GlobalTheory.CurveLattice.exists_periodPair_lamOf <;> assumption)
end
end
