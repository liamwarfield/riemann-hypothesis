module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenCoreTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.NullIff
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.LcOf
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilThetaConvergence.WeilThetaConvergenceOfSiegelSet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
noncomputable section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.SwEis

def IwaU : Prop := ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
  Iwa ((adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n))) ((adCM D.sp.cm.sig χ).uK (-1) (Fin n))

def EIwa : Prop := Chart → IwaU

def Far : Prop :=
  ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    [T2Space G'] [LocallyCompactSpace G'] (Φ : G ≃ₜ* G') (Γ P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (η : G' → ℝ)
    (R : ℝ), IsCompact (K' : Set G') → IsPar Γ' K' P' c → IsHt Γ' K' P' η → (∀ g, g ∈ Γ ↔ Φ g ∈ Γ') → (∀ g, g ∈ P ↔ Φ g ∈ P') →
    (∀ x : ℝ, R < x → Conv Γ' P' fun g => x * η g) →
    ∀ f : G → ℂ, Continuous f → (∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) →
      (∀ z : ℂ, R < z.re → ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets P Γ → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g q‖ ≤ u q) ∧
      (∀ g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g) {z | R < z.re}) ∧
      ContinuousOn (fun y : ℂ × G => GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (y.1 * η (Φ x)) * f x) y.2)
        ({z | R < z.re} ×ˢ Set.univ) ∧
      ∀ z : ℂ, ∀ γ ∈ Γ, ∀ g, GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) (γ * g) =
        GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g

def EFar : Prop := HtLip → Far

def Glue : Prop :=
  ∀ (X I : Type) [TopologicalSpace X] (T : I → X → X) (e H : ℂ → X → ℂ) (A : ℂ → ℂ) (R : ℝ), Differentiable ℂ A → (∃ z, A z ≠ 0) →
    (∀ x, Differentiable ℂ (H · x)) → Continuous (fun y : ℂ × X => H y.1 y.2) →
    (∀ z : ℂ, R < z.re → ∀ x, H z x = A z * e z x) → (∀ x, DifferentiableOn ℂ (e · x) {z | R < z.re}) →
    ContinuousOn (fun y : ℂ × X => e y.1 y.2) ({z | R < z.re} ×ˢ Set.univ) → (∀ z i x, e z (T i x) = e z x) → ∀ s₀ : ℂ,
    ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → X → ℂ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
      (∀ x, DifferentiableOn ℂ (E · x) U) ∧ ContinuousOn (fun y : ℂ × X => E y.1 y.2) (U ×ˢ Set.univ) ∧
      (∀ z ∈ U, ∀ i x, E z (T i x) = E z x) ∧ ∀ z : ℂ, R < z.re → ∀ x, E z x = d.eval z * e z x

def ETop : Prop := Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll → TStd → IwaU → Scal → Far → Glue →
  PositivityTheory.Rg.Sw.Glob.EisStrong

end PositivityTheory.Rg.SwEis

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.StrongEisensteinBounds.Strong
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluing
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GaloisBoundFirst
open Filter Topology in
theorem UpperTheory.Reformulated.B.GaloisBoundFirst.main :
    ∀ (B : ℂ → ℂ),
      Differentiable ℂ B →
        (∃ (z : ℂ), B z ≠ (0 : ℂ)) →
          ∀ (a : ℂ), ∃ (k : ℕ) (v : ℂ → ℂ), Differentiable ℂ v ∧ v a ≠ (0 : ℂ) ∧ ∀ (z : ℂ), B z = (z - a) ^ k * v z := by
  rintro B hB ⟨z0, hz0⟩ a
  have han : AnalyticOnNhd ℂ B Set.univ := hB.differentiableOn.analyticOnNhd isOpen_univ
  have hnot : ¬ ∀ᶠ z in 𝓝 a, B z = 0 := fun h => hz0
    (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
      (Set.mem_univ z0))
  obtain ⟨k, g, hg, hga, hev⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff (han a (Set.mem_univ a))).2 hnot
  have hev' : ∀ᶠ z in 𝓝 a, z ≠ a → B z / (z - a) ^ k = g z := by
    filter_upwards [hev] with z hz hne
    have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hne)
    rw [hz, smul_eq_mul]
    field_simp
  let v : ℂ → ℂ := fun z => if z = a then g a else B z / (z - a) ^ k
  have hva : v a = g a := by simp [v]
  have hvne : ∀ z, z ≠ a → v z = B z / (z - a) ^ k := fun z hz => by simp [v, hz]
  refine ⟨k, v, ?_, by rwa [hva], ?_⟩
  · intro z
    by_cases hz : z = a
    · subst hz
      have : v =ᶠ[𝓝 z] g := by
        filter_upwards [hev'] with w hw
        by_cases hwz : w = z
        · rw [hwz, hva]
        · rw [hvne w hwz, hw hwz]
      exact (hg.differentiableAt.congr_of_eventuallyEq this)
    · have hd : DifferentiableAt ℂ (fun w => B w / (w - a) ^ k) z :=
        (hB z).div (((differentiableAt_id).sub (differentiableAt_const a)).pow k)
          (pow_ne_zero _ (sub_ne_zero.2 hz))
      have : v =ᶠ[𝓝 z] fun w => B w / (w - a) ^ k := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        exact hvne w hw
      exact hd.congr_of_eventuallyEq this
  · intro z
    by_cases hz : z = a
    · subst hz
      have hB0 : B z = (z - z) ^ k * g z := by
        simpa [smul_eq_mul] using hev.self_of_nhds
      rw [hva]; exact hB0
    · rw [hvne z hz]
      have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz)
      field_simp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluing
open Filter Topology Set
open PositivityTheory.Rg.SwEis

namespace GlobalTheory.CompanionTheory.PolyDenominator

theorem exists_pow_mul (B : ℂ → ℂ) (hB : Differentiable ℂ B) (hz : ∃ z, B z ≠ 0) (a : ℂ) :
    ∃ (k : ℕ) (v : ℂ → ℂ), Differentiable ℂ v ∧ v a ≠ 0 ∧ ∀ z, B z = (z - a) ^ k * v z :=
  _root_.UpperTheory.Reformulated.B.GaloisBoundFirst.main B hB hz a

theorem finite_zeros (B : ℂ → ℂ) (hB : Differentiable ℂ B) (hz : ∃ z, B z ≠ 0) {Q : Set ℂ} (hQ : IsCompact Q) :
    {z | z ∈ Q ∧ B z = 0}.Finite := by
  obtain ⟨z₀, hz₀⟩ := hz
  have han : AnalyticOnNhd ℂ B univ := fun x _ => hB.analyticAt x
  by_contra hinf
  have hinf' : ({z | z ∈ Q ∧ B z = 0} : Set ℂ).Infinite := hinf
  obtain ⟨x, hxQ, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact hQ (fun z hz => hz.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] x, B z = 0 :=
    (accPt_iff_frequently_nhdsNE.1 hacc).mono fun z hz => hz.2
  exact hz₀ (han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ x) hfreq (mem_univ z₀))

theorem factor_of_finset {Q : Set ℂ} (F : Finset ℂ) :
    ∀ B : ℂ → ℂ, Differentiable ℂ B → (∃ z, B z ≠ 0) → (∀ z ∈ Q, B z = 0 → z ∈ F) →
      ∃ (d : Polynomial ℂ) (u : ℂ → ℂ), d ≠ 0 ∧ Differentiable ℂ u ∧
        (∀ z, B z = d.eval z * u z) ∧ ∀ z ∈ Q, u z ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro B hB _ hF
    refine ⟨1, B, one_ne_zero, hB, fun z => by simp, fun z hz h0 => ?_⟩
    simpa using hF z hz h0
  | insert a F _ ih =>
    intro B hB hz hF
    obtain ⟨k, v, hv, hva, hBv⟩ := exists_pow_mul B hB hz a
    obtain ⟨d, u, hd, hu, hvu, huQ⟩ := ih v hv ⟨a, hva⟩ (by
      intro z hzQ h0
      have hza : z ≠ a := fun h => hva (h ▸ h0)
      have hBz : B z = 0 := by rw [hBv, h0, mul_zero]
      exact (Finset.mem_insert.1 (hF z hzQ hBz)).resolve_left hza)
    refine ⟨(Polynomial.X - Polynomial.C a) ^ k * d, u,
      mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)) hd, hu, fun z => ?_, huQ⟩
    rw [hBv, hvu]
    simp [mul_assoc]

theorem exists_poly_factor (A : ℂ → ℂ) (hA : Differentiable ℂ A) (hz : ∃ z, A z ≠ 0) {Q : Set ℂ} (hQ : IsCompact Q) :
    ∃ (d : Polynomial ℂ) (u : ℂ → ℂ), d ≠ 0 ∧ Differentiable ℂ u ∧
      (∀ z, A z = d.eval z * u z) ∧ ∀ z ∈ Q, u z ≠ 0 :=
  factor_of_finset (finite_zeros A hA hz hQ).toFinset A hA hz fun z hzQ h0 => by simpa using And.intro hzQ h0

theorem glue : Glue := by
  classical
  intro X I _ T e H A R hA hAne hHd hHc hHe hed hec heT s₀
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min s₀.re R - 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = s₀.im := ⟨_, rfl⟩
  have hQ : IsCompact (Icc a (R + 1) ×ℂ Icc (c - 1) (c + 1)) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨d, u, hd, hu, hAu, huQ⟩ := exists_poly_factor A hA hAne hQ
  let P : Set ℂ := {z | R < z.re}
  let W : Set ℂ := {z | a < z.re ∧ z.re < R + 1 ∧ c - 1 < z.im ∧ z.im < c + 1}
  let U : Set ℂ := P ∪ {z | a < z.re ∧ c - 1 < z.im ∧ z.im < c + 1}
  have hPo : IsOpen P := isOpen_lt continuous_const Complex.continuous_re
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hUo : IsOpen U := hPo.union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))
  have hWQ : ∀ z ∈ W, u z ≠ 0 := fun z hz => huQ z (Complex.mem_reProdIm.2
    ⟨⟨hz.1.le, hz.2.1.le⟩, ⟨hz.2.2.1.le, hz.2.2.2.le⟩⟩)
  have hUPW : ∀ z ∈ U, z ∈ P ∨ z ∈ W := by
    rintro z (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · by_cases h : R < z.re
      · exact Or.inl h
      · exact Or.inr ⟨h1, by linarith [not_lt.1 h], h2, h3⟩
  let E : ℂ → X → ℂ := fun z x => if R < z.re then d.eval z * e z x else H z x / u z
  have hEP : ∀ z, R < z.re → ∀ x, E z x = d.eval z * e z x := fun z h x => by simp [E, h]
  have hEW : ∀ z ∈ W, ∀ x, E z x = H z x / u z := by
    intro z hz x
    by_cases h : R < z.re
    · have h0 := hWQ z hz
      rw [hEP z h, hHe z h, hAu z]
      field_simp
    · simp [E, h]
  have hHT : ∀ i x z, H z (T i x) = H z x := by
    intro i x z
    have h1 : AnalyticOnNhd ℂ (H · (T i x)) univ := fun w _ => (hHd (T i x)).analyticAt w
    have h2 : AnalyticOnNhd ℂ (H · x) univ := fun w _ => (hHd x).analyticAt w
    have hmem : ((R + 1 : ℝ) : ℂ) ∈ P := by simp [P]
    have h3 : (H · (T i x)) =ᶠ[𝓝 ((R + 1 : ℝ) : ℂ)] (H · x) := by
      filter_upwards [hPo.mem_nhds hmem] with w hw
      rw [hHe w hw, hHe w hw, heT]
    exact congrFun (h1.eq_of_eventuallyEq h2 h3) z
  refine ⟨U, d, E, hUo, ⟨⟨R, subset_union_left⟩, ?_⟩, ?_, hd, ?_, ?_, ?_, fun z hz x => hEP z hz x⟩
  · rintro s (h | ⟨h1, h2, h3⟩) t ht
    · left
      simp only [P, mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
      exact lt_add_of_lt_of_nonneg h ht
    · right
      simp only [mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
      exact ⟨lt_add_of_lt_of_nonneg h1 ht, h2, h3⟩
  · by_cases h : R < s₀.re
    · exact Or.inl h
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · have := min_le_left s₀.re R
        rw [ha]; linarith
      · rw [hc]; linarith
      · rw [hc]; linarith
  · intro x z hz
    rcases hUPW z hz with h | h
    · have h1 : DifferentiableAt ℂ (fun w => d.eval w * e w x) z :=
        (d.differentiable z).mul ((hed x z h).differentiableAt (hPo.mem_nhds h))
      refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hPo.mem_nhds h] with w hw using hEP w hw x
    · have h1 : DifferentiableAt ℂ (fun w => H w x / u w) z := (hHd x z).div (hu z) (hWQ z h)
      refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hWo.mem_nhds h] with w hw using hEW w hw x
  · have hc1 : ContinuousOn (fun y : ℂ × X => d.eval y.1 * e y.1 y.2) (P ×ˢ univ) :=
      (d.continuous.comp continuous_fst).continuousOn.mul hec
    have hc2 : ContinuousOn (fun y : ℂ × X => H y.1 y.2 / u y.1) (W ×ˢ univ) :=
      hHc.continuousOn.div (hu.continuous.comp continuous_fst).continuousOn fun y hy => hWQ y.1 hy.1
    rintro ⟨z, x⟩ ⟨hz, -⟩
    rcases hUPW z hz with h | h
    · have ho : IsOpen (P ×ˢ (univ : Set X)) := hPo.prod isOpen_univ
      have hmem : (z, x) ∈ P ×ˢ (univ : Set X) := ⟨h, mem_univ x⟩
      have : ContinuousOn (fun y : ℂ × X => E y.1 y.2) (P ×ˢ univ) :=
        hc1.congr fun y hy => hEP y.1 hy.1 y.2
      exact (this.continuousAt (ho.mem_nhds hmem)).continuousWithinAt
    · have ho : IsOpen (W ×ˢ (univ : Set X)) := hWo.prod isOpen_univ
      have hmem : (z, x) ∈ W ×ˢ (univ : Set X) := ⟨h, mem_univ x⟩
      have : ContinuousOn (fun y : ℂ × X => E y.1 y.2) (W ×ˢ univ) :=
        hc2.congr fun y hy => hEW y.1 hy.1 y.2
      exact (this.continuousAt (ho.mem_nhds hmem)).continuousWithinAt
  · intro z hz i x
    rcases hUPW z hz with h | h
    · rw [hEP z h, hEP z h, heT]
    · rw [hEW z h, hEW z h, hHT]

end GlobalTheory.CompanionTheory.PolyDenominator
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluingStatement
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_gluing : Glue := by
  first | exact @GlobalTheory.CompanionTheory.PolyDenominator.glue | exact GlobalTheory.CompanionTheory.PolyDenominator.glue | (intros; apply GlobalTheory.CompanionTheory.PolyDenominator.glue <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimate
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr PositivityTheory.Rg.SwEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwEisIwa

theorem iwa_of_rank (hC : Chart) (D : D7) (χ : (AE D)ˣ →* Circle) (V : HSp D) :
    Iwa ((adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin V.rank))) ((adCM D.sp.cm.sig χ).uK (-1) (Fin V.rank)) := by
  obtain ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj V
  obtain ⟨Φ, p, -, hQ, hK, -, -⟩ := hC D χ V a ha
  intro g
  obtain ⟨q, k, hk, hqk⟩ := (GlobalTheory.Eis.isIwasawa_Khat (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha)).1
    (Φ.symm g * (p : GA D (dblSp V))⁻¹)
  refine ⟨Φ ((q : GA D (dblSp V)) * p), (hQ _).1 (Subgroup.mul_mem _ q.2 p.2),
    Φ ((p : GA D (dblSp V))⁻¹ * k * p), (hK k).1 hk, ?_⟩
  have h1 : Φ.symm g = (q : GA D (dblSp V)) * k * p := by
    rw [← hqk, inv_mul_cancel_right]
  have h2 : (q : GA D (dblSp V)) * p * ((p : GA D (dblSp V))⁻¹ * k * p) = (q : GA D (dblSp V)) * k * p := by
    group
  rw [← map_mul, h2, ← h1]
  exact (Φ.apply_symm_apply g).symm

theorem eIwa : EIwa := fun hC D χ n =>
  iwa_of_rank hC D χ (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n)

end GlobalTheory.CompanionTheory.SwEisIwa

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimateStatement
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_iwasawa_estimate : EIwa := by
  first | exact @GlobalTheory.CompanionTheory.SwEisIwa.eIwa | exact GlobalTheory.CompanionTheory.SwEisIwa.eIwa | (intros; apply GlobalTheory.CompanionTheory.SwEisIwa.eIwa <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimate
noncomputable section

namespace GlobalTheory.CompanionTheory.FarSeries

open PositivityTheory.RgEis PositivityTheory.Rg.SwEis Topology

theorem exp_mul_le {a b x s t L : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) (hL : |s - t| ≤ L) :
    Real.exp (x * s) ≤ Real.exp ((|a| + |b|) * L) * (Real.exp (a * t) + Real.exp (b * t)) := by
  have hx : |x| ≤ |a| + |b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a, abs_nonneg b]
    · linarith [le_abs_self b, abs_nonneg a]
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  have h3 : x * (s - t) ≤ (|a| + |b|) * L :=
    calc x * (s - t) ≤ |x * (s - t)| := le_abs_self _
      _ = |x| * |s - t| := abs_mul _ _
      _ ≤ (|a| + |b|) * L := mul_le_mul hx hL (abs_nonneg _) (by positivity)
  have h4 : Real.exp (x * t) ≤ Real.exp (a * t) + Real.exp (b * t) := by
    rcases le_total 0 t with ht | ht
    · have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h2 ht)
      linarith [Real.exp_pos (a * t)]
    · have := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right h1 ht)
      linarith [Real.exp_pos (b * t)]
  calc Real.exp (x * s) = Real.exp (x * (s - t)) * Real.exp (x * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ _ := mul_le_mul (Real.exp_le_exp.2 h3) h4 (Real.exp_pos _).le (Real.exp_pos _).le

theorem summable_along {G G' : Type} [Group G] [Group G'] [TopologicalSpace G'] (Φ : G ≃* G') (Γ P : Subgroup G) (Γ' K' P' : Subgroup G')
    (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (η : G' → ℝ) (hη : IsHt Γ' K' P' η) (x : ℝ)
    (hc : Conv Γ' P' fun g => x * η g) : Summable fun q : Cos P Γ => Real.exp (x * η (Φ (rep q))) := by
  let T : G' → ℂ := fun y => (Real.exp (x * η y) : ℂ)
  have hT : GlobalTheory.AutomorphicL2Unitary.LeftInv (P' ⊓ Γ') T := fun γ hγ y => by
    simp only [T, hη.left γ hγ.1 y, hη.rat γ hγ.2 hγ.1, zero_add]
  obtain ⟨-, h⟩ := GlobalTheory.StdUnn.cosetSum_along_mulEquiv G G' Φ P Γ P' Γ' hP hΓ T 1 1 (fun g => T (Φ g))
    (fun g => by simp) hT
  have h1 : GlobalTheory.Eis.CosetConv P' Γ' T (Φ (1 * 1)) := by
    refine (hc (Φ (1 * 1))).congr fun q => ?_
    show _ = ‖((Real.exp (x * η (rep q * Φ (1 * 1))) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine ((h 1).1 h1).congr fun q => ?_
  show ‖((Real.exp (x * η (Φ (rep q * 1))) : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_one]

theorem bounded_of_law {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (Φ : G ≃ₜ* G')
    (P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (hK : IsCompact (K' : Set G')) (hPar : IsPar Γ' K' P' c)
    (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (f : G → ℂ) (hf : Continuous f) (hlaw : ∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image Φ.symm.continuous).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  obtain ⟨p, hp, k, hk, e⟩ := hPar.iwa (Φ x)
  have hx : x = Φ.symm p * Φ.symm k := by
    apply Φ.injective
    simp [e]
  have hq : Φ.symm p ∈ P := (hP _).2 (by simpa using hp)
  rw [hx, hlaw _ hq, Φ.apply_symm_apply, norm_mul, hPar.ch.norm p hp, one_mul]
  exact (hM _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)

theorem eFar : EFar := by
  intro hLip G G' _ _ _ _ _ _ _ _ Φ Γ P Γ' K' P' c η R hK hPar hη hΓ hP hcv f hf hlaw
  have hsum : ∀ x : ℝ, R < x → Summable fun q : Cos P Γ => Real.exp (x * η (Φ (rep q))) := fun x hx =>
    summable_along Φ.toMulEquiv Γ P Γ' K' P' hΓ hP η hη x (hcv x hx)
  obtain ⟨M, hM0, hM⟩ := bounded_of_law Φ P Γ' K' P' c hK hPar hP f hf hlaw
  have key : ∀ a b : ℝ, R < a → R < b → ∀ C : Set G, IsCompact C → ∃ u : Cos P Γ → ℝ, Summable u ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ∀ g ∈ C, ∀ q : Cos P Γ,
        ‖Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g)‖ ≤ u q := by
    intro a b ha hb C hC
    obtain ⟨L, hL⟩ := hLip G' Γ' K' P' η hK hPar.iwa hη (Φ '' C) (hC.image Φ.continuous)
    refine ⟨fun q => M * Real.exp ((|a| + |b|) * L) *
      (Real.exp (a * η (Φ (rep q))) + Real.exp (b * η (Φ (rep q)))), ((hsum a ha).add (hsum b hb)).mul_left _, ?_⟩
    intro z h1 h2 g hg q
    have h3 := exp_mul_le (s := η (Φ (rep q * g))) (t := η (Φ (rep q))) (L := L) h1 h2
      (by rw [map_mul]; exact hL _ _ ⟨g, hg, rfl⟩)
    have h4 : (z * (η (Φ (rep q * g)) : ℂ)).re = z.re * η (Φ (rep q * g)) := by simp
    rw [norm_mul, Complex.norm_exp, h4]
    calc _ ≤ (Real.exp ((|a| + |b|) * L) * (Real.exp (a * η (Φ (rep q))) + Real.exp (b * η (Φ (rep q))))) * M :=
          mul_le_mul h3 (hM _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hcont : ∀ q : Cos P Γ, Continuous fun y : ℂ × G =>
      Complex.exp (y.1 * η (Φ (rep q * y.2))) * f (rep q * y.2) := fun q => by
    have h1 : Continuous fun y : ℂ × G => rep q * y.2 := continuous_const.mul continuous_snd
    have h2 : Continuous fun y : ℂ × G => ((η (Φ (rep q * y.2)) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hη.cont.comp (Φ.continuous.comp h1))
    exact (Complex.continuous_exp.comp (continuous_fst.mul h2)).mul (hf.comp h1)
  have hopen : ∀ a b : ℝ, IsOpen {z : ℂ | a < z.re ∧ z.re < b} := fun a b =>
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hab : ∀ z : ℂ, R < z.re → R < (R + z.re) / 2 ∧ R < z.re + 1 ∧ z ∈ {w : ℂ | (R + z.re) / 2 < w.re ∧ w.re < z.re + 1} :=
    fun z hz => ⟨by linarith, by linarith, by show _ ∧ _; constructor <;> linarith⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz C hC
    obtain ⟨u, hu, hb⟩ := key z.re z.re hz hz C hC
    exact ⟨u, hu, fun g hg q => hb z le_rfl le_rfl g hg q⟩
  · intro g z₀ hz₀
    obtain ⟨h1, h2, h3⟩ := hab z₀ hz₀
    obtain ⟨u, hu, hb⟩ := key _ _ h1 h2 {g} isCompact_singleton
    have hd : DifferentiableOn ℂ (fun z => ∑' q : Cos P Γ, Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g))
        {w : ℂ | (R + z₀.re) / 2 < w.re ∧ w.re < z₀.re + 1} := by
      refine Complex.differentiableOn_tsum_of_summable_norm hu (fun q => ?_) (hopen _ _)
        (fun q w hw => hb w hw.1.le hw.2.le g rfl q)
      have : Differentiable ℂ fun z : ℂ => Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g) := by fun_prop
      exact this.differentiableOn
    exact (hd.differentiableAt ((hopen _ _).mem_nhds h3)).differentiableWithinAt
  · rintro ⟨z₀, g₀⟩ ⟨hz₀, -⟩
    obtain ⟨h1, h2, h3⟩ := hab z₀ hz₀
    obtain ⟨C', hC'c, hC'm⟩ := exists_compact_mem_nhds (Φ g₀)
    have hCm : Φ.symm '' C' ∈ 𝓝 g₀ := Filter.mem_of_superset (Φ.continuous.continuousAt.preimage_mem_nhds hC'm)
      fun x hx => ⟨Φ x, hx, by simp⟩
    obtain ⟨u, hu, hb⟩ := key _ _ h1 h2 _ (hC'c.image Φ.symm.continuous)
    have hd : ContinuousOn (fun y : ℂ × G => ∑' q : Cos P Γ, Complex.exp (y.1 * η (Φ (rep q * y.2))) * f (rep q * y.2))
        ({w : ℂ | (R + z₀.re) / 2 < w.re ∧ w.re < z₀.re + 1} ×ˢ (Φ.symm '' C')) :=
      continuousOn_tsum (fun q => (hcont q).continuousOn) hu
        fun q y hy => hb y.1 hy.1.1.le hy.1.2.le y.2 hy.2 q
    exact (hd.continuousAt (prod_mem_nhds ((hopen _ _).mem_nhds h3) hCm)).continuousWithinAt
  · intro z γ hγ g
    refine GlobalTheory.Eis.leftInv_cosetSum (fun δ hδ x => ?_) γ hγ g
    have h1 : Φ δ ∈ P' := (hP δ).1 hδ.1
    have h2 : Φ δ ∈ Γ' := (hΓ δ).1 hδ.2
    simp only [hlaw δ hδ.1 x, map_mul, hη.left _ h1, hη.rat _ h2 h1, hPar.ch.rat _ h2 h1, zero_add, one_mul]

end GlobalTheory.CompanionTheory.FarSeries

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimateStatement
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_far_estimate : EFar := by
  first | exact @GlobalTheory.CompanionTheory.FarSeries.eFar | exact GlobalTheory.CompanionTheory.FarSeries.eFar | (intros; apply GlobalTheory.CompanionTheory.FarSeries.eFar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopology
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr PositivityTheory.Rg.SwEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwEisTop

theorem ext_mul_eq {G : Type} [Group G] (K P : Subgroup G) (f : G → ℝ)
    (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q) (hK : ∀ p ∈ P, p ∈ K → f p = 0)
    {p k : G} (hp : p ∈ P) (hk : k ∈ K) : ext K P f (p * k) = f p := by
  unfold ext
  have h : ∃ k' : K, p * k * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [dite_eq_left h]
  have h1 := h.choose_spec
  have hm : k * (h.choose : G)⁻¹ ∈ P := by
    have := P.mul_mem (P.inv_mem hp) h1
    simpa [mul_assoc] using this
  have hmK : k * (h.choose : G)⁻¹ ∈ K := K.mul_mem hk (K.inv_mem h.choose.2)
  rw [mul_assoc, hadd p hp _ hm, hK _ hm hmK, add_zero]

theorem absA_pos' {D : D7} (u : (AE D)ˣ) : 0 < absA D u := by
  have h : absA D u * absA D u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.mpr fun h0 => by simp [h0] at h

section Gen

variable {E R : Type} [Field E] [CommRing R] (A : Ad E R) (ε : ℤˣ) {ι : Type} [Fintype ι] [DecidableEq ι] (S : Set ι)

theorem uH_mul (hmul : ∀ p ∈ stab R ((Sum.inl '' S : Set (ι ⊕ ι))), ∀ q ∈ stab R ((Sum.inl '' S : Set (ι ⊕ ι))),
      bdet ((Sum.inl '' S : Set (ι ⊕ ι))) (p * q) = bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p * bdet ((Sum.inl '' S : Set (ι ⊕ ι))) q)
    (hlg : ∀ x y, A.lg (x * y) = A.lg x + A.lg y)
    (hk0 : ∀ p ∈ stab R ((Sum.inl '' S : Set (ι ⊕ ι))), p ∈ A.kGL (ι ⊕ ι) → A.lg (bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p) = 0)
    {p k : A.U ε ι} (hp : p ∈ A.uQ ε S) (hk : k ∈ A.uK ε ι) :
    A.uH ε S (p * k) = A.lg (bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p.1) :=
  ext_mul_eq (A.uK ε ι) (A.uQ ε S) (fun p => A.lg (bdet ((Sum.inl '' S : Set (ι ⊕ ι))) p.1))
    (fun p hp q hq => by
      show A.lg (bdet _ (p.1 * q.1)) = _
      exact (congrArg A.lg (hmul p.1 hp q.1 hq)).trans (hlg _ _))
    (fun p hp hk => hk0 _ hp hk) hp hk

end Gen

theorem exp_uH_eq (hDict : Dict) (hBd : BdetLaw) {D : D7} {χ : (AE D)ˣ →* Circle} {n : ℕ}
    (hGood : (adCM D.sp.cm.sig χ).Good) (Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* UD D χ n)
    (hP : ∀ g, g ∈ GlobalTheory.StdUnn.P D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n)))
    (hK : ∀ g, g ∈ GlobalTheory.StdUnn.K D n ↔ Ψ g ∈ (adCM D.sp.cm.sig χ).uK (-1) (Fin n))
    (hdet : ∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1 →
      bdet (Sum.inl '' (Set.univ : Set (Fin n))) (Ψ g).1 = Matrix.GeneralLinearGroup.det a)
    (hI : Iwa ((adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin n))) ((adCM D.sp.cm.sig χ).uK (-1) (Fin n)))
    {H : GlobalTheory.StdUnn.G D n → ℝ≥0} (hH : GlobalTheory.StdUnn.IsHeight H) (x : GlobalTheory.StdUnn.G D n) :
    Real.exp ((adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) = (H x : ℝ) := by
  have hBd' := hBd _ _ (adCM D.sp.cm.sig χ) hGood.toGoodL (Fin n ⊕ Fin n) (Sum.inl '' Set.univ)
  obtain ⟨p, hp, k, hk, e⟩ := hI (Ψ x)
  have h1 := uH_mul (adCM D.sp.cm.sig χ) (-1) (Set.univ : Set (Fin n)) hBd'.2.1 hGood.lgmul hBd'.2.2.2.2.1 hp hk
  rw [← e] at h1
  have hp₀ : Ψ.symm p ∈ GlobalTheory.StdUnn.P D n := (hP _).2 (by simpa using hp)
  have hk₀ : Ψ.symm k ∈ GlobalTheory.StdUnn.K D n := (hK _).2 (by simpa using hk)
  have hx : x = Ψ.symm p * Ψ.symm k := by rw [← map_mul, ← e, ContinuousMulEquiv.symm_apply_apply]
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp₀
  have h2 := hdet _ a ha
  rw [ContinuousMulEquiv.apply_symm_apply] at h2
  have h3 := hH _ hp₀ a ha _ hk₀
  rw [← hx] at h3
  have h4 : (adCM D.sp.cm.sig χ).lg (Matrix.GeneralLinearGroup.det a) =
      Real.log (absA D (Matrix.GeneralLinearGroup.det a)) := by
    have e5 := (hDict D.host.F D.host.E).2.2.2.2 (Matrix.GeneralLinearGroup.det a)
    show Real.log _ = _
    rw [e5]
  rw [h1, h2, h4, h3, Real.exp_log (by exact_mod_cast absA_pos' _)]

theorem law_div {D : D7} {n : ℕ} {χ : (AE D)ˣ →* Circle} {G' : Type} [Group G'] [TopologicalSpace G']
    (Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* G') (P' : Subgroup G') (η : G' → ℝ) (c : G' → ℂ)
    (hP : ∀ g, g ∈ GlobalTheory.StdUnn.P D n ↔ Ψ g ∈ P') (hleft : ∀ p ∈ P', ∀ g, η (p * g) = η p + η g)
    (hc : ∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1 →
      c (Ψ g) = χ (Matrix.GeneralLinearGroup.det a))
    {H : GlobalTheory.StdUnn.G D n → ℝ≥0} (hH : GlobalTheory.StdUnn.IsHeight H) (hexp : ∀ x, Real.exp (η (Ψ x)) = (H x : ℝ))
    {s₁ : ℂ} {φ : GlobalTheory.StdUnn.G D n → ℂ} (hφ : GlobalTheory.StdUnn.IsSection χ s₁ φ) :
    ∀ q ∈ GlobalTheory.StdUnn.P D n, ∀ g, φ (q * g) * Complex.exp (-(s₁ + (n : ℂ) / 2) * η (Ψ (q * g))) =
      c (Ψ q) * (φ g * Complex.exp (-(s₁ + (n : ℂ) / 2) * η (Ψ g))) := by
  intro q hq g
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
  have hq' := (hP q).1 hq
  have h3 : η (Ψ q) = Real.log (absA D (Matrix.GeneralLinearGroup.det a)) := by
    have h := hH q hq a ha 1 (one_mem _)
    rw [mul_one] at h
    rw [← Real.log_exp (η (Ψ q)), hexp q, h]
  rw [hφ.1 q hq a ha g, map_mul, hleft _ hq' _, h3, hc q a ha, npow_eq_exp (absA_pos' _)]
  have key : Complex.exp (((Real.log (absA D (Matrix.GeneralLinearGroup.det a)) : ℝ) : ℂ) * (s₁ + (n : ℂ) / 2)) *
      Complex.exp (-(s₁ + (n : ℂ) / 2) * ((Real.log (absA D (Matrix.GeneralLinearGroup.det a)) + η (Ψ g) : ℝ) : ℂ)) =
      Complex.exp (-(s₁ + (n : ℂ) / 2) * (η (Ψ g) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) * φ g) * key

theorem fin_div {D : D7} {n : ℕ} {G' : Type} [Group G'] [TopologicalSpace G']
    (Ψ : GlobalTheory.StdUnn.G D n ≃ₜ* G') (K' : Subgroup G') (η : G' → ℝ)
    (hK : ∀ g, g ∈ GlobalTheory.StdUnn.K D n ↔ Ψ g ∈ K') (hright : ∀ g, ∀ k ∈ K', η (g * k) = η g)
    {φ : GlobalTheory.StdUnn.G D n → ℂ} (hφ : IsKFinite (GlobalTheory.StdUnn.K D n) φ) (t : ℂ) (f : GlobalTheory.StdUnn.G D n → ℂ)
    (hf : ∀ x, f x = φ x * Complex.exp (t * η (Ψ x))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun x => f (x * Ψ.symm k))) := by
  haveI : FiniteDimensional ℂ (kSpan (GlobalTheory.StdUnn.K D n) φ) := hφ
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ :
    _ ≤ (kSpan (GlobalTheory.StdUnn.K D n) φ).map (LinearMap.mulRight ℂ (fun x => Complex.exp (t * η (Ψ x)))))
  rintro _ ⟨k, rfl⟩
  refine ⟨fun x => φ (x * Ψ.symm k), Submodule.subset_span ⟨Ψ.symm k, (hK _).2 (by simpa using k.2), rfl⟩, ?_⟩
  funext x
  simp [hf, LinearMap.mulRight_apply, map_mul, hright _ _ k.2]

theorem fun_eq {X : Type} (η : X → ℝ) (H : X → ℝ≥0) (hexp : ∀ x, Real.exp (η x) = (H x : ℝ)) (φ : X → ℂ)
    (s₁ z c : ℂ) : (fun x => Complex.exp ((z + c) * η x) * (φ x * Complex.exp (-(s₁ + c) * η x))) =
      fun x => ((H x : ℝ) : ℂ) ^ (z - s₁) * φ x := by
  funext x
  have hpos : (0 : ℝ) < H x := by rw [← hexp x]; exact Real.exp_pos _
  have hlog : Real.log (H x) = η x := by rw [← hexp x, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, hlog]
  have key : Complex.exp ((z + c) * η x) * Complex.exp (-(s₁ + c) * η x) = Complex.exp (η x * (z - s₁)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination φ x * key

theorem assemble {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [T2Space G'] [LocallyCompactSpace G'] (hFar : Far) (hGlue : Glue) (Φ : G ≃ₜ* G')
    (Γ P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (η : G' → ℝ) (R0 : ℝ) (hK : IsCompact (K' : Set G'))
    (hPar : IsPar Γ' K' P' c) (hHt : IsHt Γ' K' P' η) (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P')
    (hconv : ∀ x : ℝ, R0 < x → Conv Γ' P' fun g => x * η g) (f : G → ℂ) (hf : Continuous f)
    (hlaw : ∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) (A : ℂ → ℂ) (Hh : ℂ → G → ℂ) (R1 : ℝ) (hA : Differentiable ℂ A)
    (hAne : ∃ z, A z ≠ 0) (hHd : ∀ g, Differentiable ℂ (Hh · g)) (hHc : Continuous fun y : ℂ × G => Hh y.1 y.2)
    (hHeq : ∀ z : ℂ, R1 < z.re → ∀ g, Hh z g = A z * GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g)
    (w : ℝ) (F : ℂ → G → ℂ) (hF : ∀ z : ℂ, (fun x => Complex.exp ((z + (w : ℂ)) * η (Φ x)) * f x) = F z) (s₀ : ℂ) :
    ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G → ℂ) (σ : ℝ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
      (∀ g, DifferentiableOn ℂ (E · g) U) ∧ ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ) ∧
      (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, E z (γ * g) = E z g) ∧
      ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets P Γ → ℝ, Summable u ∧
          ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term P Γ (F z) g q‖ ≤ u q) ∧
        ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum P Γ (F z) g := by
  obtain ⟨R, hR1, hR0⟩ : ∃ R : ℝ, R1 ≤ R ∧ R0 ≤ R := ⟨max R1 R0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨hmaj, hdiff, hcont, hinv⟩ := hFar G G' Φ Γ P Γ' K' P' c η R hK hPar hHt hΓ hP
    (fun x hx => hconv x (lt_of_le_of_lt hR0 hx)) f hf hlaw
  obtain ⟨U', d', E', hU'o, hU'r, hs₀', hd', hE'd, hE'c, hE'i, hE'eq⟩ :=
    hGlue G Γ (fun i x => (i : G) * x)
      (fun z g => GlobalTheory.Eis.cosetSum P Γ (fun x => Complex.exp (z * η (Φ x)) * f x) g) Hh A R hA hAne hHd hHc
      (fun z hz x => hHeq z (lt_of_le_of_lt hR1 hz) x) hdiff hcont
      (fun z i x => hinv z i i.2 x) (s₀ + (w : ℂ))
  refine ⟨(· + (w : ℂ)) ⁻¹' U', Polynomial.taylor (w : ℂ) d', fun z g => E' (z + (w : ℂ)) g,
    R - w, hU'o.preimage (continuous_id.add continuous_const), hU'r.preimage_add _, hs₀', ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hd' ((Polynomial.taylor_eq_zero _ d').1 h)
  · intro g
    exact (hE'd g).comp (differentiableOn_id.add_const _) (fun z hz => hz)
  · refine hE'c.comp ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn ?_
    intro y hy
    exact ⟨hy.1, Set.mem_univ _⟩
  · intro z hz γ hγ g
    exact hE'i (z + (w : ℂ)) hz ⟨γ, hγ⟩ g
  · intro z hz
    have hz' : R < (z + (w : ℂ)).re := by
      have : (z + (w : ℂ)).re = z.re + w := by simp
      rw [this]; linarith
    refine ⟨fun C hC => ?_, fun g => ?_⟩
    · obtain ⟨u, hu, hb⟩ := hmaj (z + (w : ℂ)) hz' C hC
      refine ⟨u, hu, fun g hg q => ?_⟩
      rw [← hF z]
      exact hb g hg q
    · show E' (z + (w : ℂ)) g = _
      rw [hE'eq (z + (w : ℂ)) hz' g, Polynomial.taylor_eval, hF z]

theorem eTop : ETop := by
  intro hDict hDI hCM hGT hBd hExt hPar hSg hStd hIwa hScal hFar hGlue
  intro D n hn χ b hχ hres H hH s₁ φ hφ s₀
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hur := GlobalTheory.HeckeAdjoint.unramified_host D
  have hpow := GlobalTheory.LFun.resEtaPow_of_resEta _ _ hcm.2.2.1 χ b ((GlobalTheory.LFun.resEta_iff χ b).1 hres)
  have hGood : (adCM D.sp.cm.sig χ).Good := hCM _ _ D.sp.cm.sig χ b hcm hur hχ hpow
  obtain ⟨_, _, _, hT2, hLC, _, hKc⟩ := hGT _ _ (adCM D.sp.cm.sig χ) hGood (Fin n) (-1)
  obtain ⟨Ψ, hΓ, hP, hK, hdet⟩ := hStd hDict hDI D χ n
  have hI := hIwa D χ n
  obtain ⟨hPar1, hHt1, -⟩ := (hPar _ _ (adCM D.sp.cm.sig χ) hGood (Fin n) (-1) Set.univ).2 (by rw [inf_idem]; exact hI)
  rw [inf_idem] at hPar1
  have hW := hSg _ _ D.sp.cm.sig χ b hcm hur hχ hpow (-1) (Fin n) (by simp; omega) hI
  have hexp : ∀ x, Real.exp ((adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) = (H x : ℝ) :=
    fun x => exp_uH_eq hDict hBd hGood Ψ hP hK hdet hI hH x
  obtain ⟨R0, D0, Op0, H0, hwall⟩ := hW ℂ (1 : (adCM D.sp.cm.sig χ).uK (-1) (Fin n) →* (ℂ →L[ℂ] ℂ)) continuous_const
  have hf : Continuous fun x => φ x * Complex.exp (-(s₁ + (n : ℂ) / 2) * (adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) :=
    hφ.2.1.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (hHt1.cont.comp Ψ.continuous))))
  have hlaw := law_div Ψ _ _ ((adCM D.sp.cm.sig χ).uC (-1) (Fin n)) hP hHt1.left (fun g a ha => congrArg (fun u => ((χ u : Circle) : ℂ)) (hdet g a ha))
    hH hexp hφ
  have hfin := fin_div Ψ _ _ hK hHt1.right hφ.2.2 (-(s₁ + (n : ℂ) / 2))
    (fun x => φ x * Complex.exp (-(s₁ + (n : ℂ) / 2) * (adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x))) (fun x => rfl)
  obtain ⟨A0, Hh, R1, hA0, hA0ne, hHd, hHc, hHeq, -⟩ :=
    hScal _ _ Ψ _ _ _ _ _ _ _ _ hKc hPar1 hHt1 hΓ hP hW _ hf hlaw hfin
  exact assemble hFar hGlue Ψ _ _ _ _ _ _ _ R0 hKc hPar1 hHt1 hΓ hP hwall.convR _ hf hlaw A0 Hh R1 hA0 hA0ne hHd hHc hHeq
    ((n : ℝ) / 2) (fun z x => ((H x : ℝ) : ℂ) ^ (z - s₁) * φ x)
    (fun z => by
      have e := fun_eq (fun x => (adCM D.sp.cm.sig χ).uH (-1) Set.univ (Ψ x)) H hexp φ s₁ z ((n : ℂ) / 2)
      push_cast
      exact e) s₀

end GlobalTheory.CompanionTheory.SwEisTop
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTopologyStatement
open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_topology : ETop := by
  first | exact @GlobalTheory.CompanionTheory.SwEisTop.eTop | exact GlobalTheory.CompanionTheory.SwEisTop.eTop | (intros; apply GlobalTheory.CompanionTheory.SwEisTop.eTop <;> assumption)
end
end

namespace PositivityTheory.Rg.SwEis.Hd

open PositivityTheory.RgEis.Hd

theorem eisStrong : PositivityTheory.Rg.Sw.Glob.EisStrong :=
  GlobalTheory.T.eisenstein_topology dict dictInf (cmGood_of stdGood dict dictInf) grpTop bdetLaw extLaw (parLaw_of bdetLaw extLaw grpTop)
    sgAll GlobalTheory.T.standard_section_exists (GlobalTheory.T.eisenstein_iwasawa_estimate (GlobalTheory.T.chart_section_exists dict dictInf GlobalTheory.T.standard_section_exists)) (GlobalTheory.T.scalar_section_exists secLaw (wallLaw_of secLaw))
    (GlobalTheory.T.eisenstein_far_estimate htLip) GlobalTheory.T.eisenstein_gluing

end PositivityTheory.Rg.SwEis.Hd
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Wtc
namespace PositivityTheory.Rg.Sw.Glob

theorem wtc : GlobalTheory.Published.WeilThetaConvergence := GlobalTheory.CompanionTheory.WTC.weilThetaConvergence_of_core GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end PositivityTheory.Rg.Sw.Glob
end

namespace PositivityTheory.Rg.Sw.Glob

theorem absThm : AbsThm := AbsSt.absThm_of lv (cyc_of fft) (lc_of fft) nullIff

theorem top2 (hLF : LocFact) (hAA : AwayAct) (hLi : LocInst) (hTA : PositivityTheory.PfSWUS.ThetaAuto) (hLC : LieComm)
    (hDO : DerivOne) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top absThm hLF hAA hLi hTA hLC hDO hId PositivityTheory.Rg.SwEis.Hd.eisStrong hC wtc

theorem top3 (hLF : LocFact) (hAA : AwayAct) (hLi : LocInst) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil)
    (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top2 hLF hAA hLi (GlobalTheory.T.theta_automorphic_of_convergence wtc) hLC hDO hId hC

end PositivityTheory.Rg.Sw.Glob
