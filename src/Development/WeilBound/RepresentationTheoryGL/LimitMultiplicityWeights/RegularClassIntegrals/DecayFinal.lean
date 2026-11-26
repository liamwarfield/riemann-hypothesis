module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzBruhatSchroedingerFixedLocalField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelDomainOpenSubgroupBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMatrixIntegralAlmostAllPlaces

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

abbrev NF {k : ℕ} (C : Matrix (Fin n) (Fin k) E) : Subgroup (GAd σ J) := ratPts σ J ⊓ unipRad σ J C

variable {σ J}

def nsum (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ) (z g : GAd σ J) : ℂ := ∑' ν : Γ, f (z * ν * g)

def Van (N : Subgroup (GAd σ J)) (f : GAd σ J → ℂ) : Prop :=
  ∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GAd σ J), ∫ m : N, f (x * m * y) ∂ν = 0

end

def SmOf : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ f ∈ CcAd σ J, GlobalTheory.UAut.IsSm σ J f

def DerMem : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ f ∈ CcAd σ J, ∀ b : ℝ → GAd σ J, IsRealLine σ J b → lineDer b f ∈ CcAd σ J

def DerVan : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ N : Subgroup (GAd σ J), IsClosed (N : Set (GAd σ J)) → ∀ f ∈ CcAd σ J, ∀ b : ℝ → GAd σ J, IsRealLine σ J b →
      Van N f → Van N (lineDer b f)

def Level : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ f ∈ CcAd σ J, ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g

def SumSm : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ Γ : Subgroup (GAd σ J), Γ ≤ ratPts σ J → ∀ f ∈ CcAd σ J, ∀ z, GlobalTheory.UAut.IsSm σ J (nsum Γ f z) ∧
      ∀ b : ℝ → GAd σ J, IsRealLine σ J b → lineDer b (nsum Γ f z) = nsum Γ (lineDer b f) z

def Variation : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (k : ℕ) (C : Matrix (Fin n) (Fin k) E), GlobalTheory.UAut.IsIsoCols σ J C → ∀ f : GAd σ J → ℂ, Continuous f →
      HasCompactSupport f → Van (unipRad σ J C) f → ∀ (z g : GAd σ J) (e : ℝ),
      (∀ m ∈ unipRad σ J C, ‖nsum (NF σ J C) f z (m * g) - nsum (NF σ J C) f z g‖ ≤ e) → ‖nsum (NF σ J C) f z g‖ ≤ e

def NearCusp : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Cm : Set (GAd σ J)) (c : ℝ)
      (U : Subgroup (GAd σ J)), IsCompact Cm → 0 < c → IsOpen (U : Set (GAd σ J)) → ∀ s : Fin r,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ∀ m ∈ unipRad σ J (pre X s),
        ∃ γ ∈ NF σ J (pre X s), ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧ κ ∈ finPts σ J ∧
          m * (a * k) = γ * (a * k) * u * κ

def Base : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∃ A : ℕ,
    ∀ Γ : Subgroup (GAd D.sp.cm.sig V.gram), Γ ≤ ratPts D.sp.cm.sig V.gram →
    ∀ f : GAd D.sp.cm.sig V.gram → ℂ, Continuous f → HasCompactSupport f →
    ∀ C W : Set (GAd D.sp.cm.sig V.gram), IsCompact C → IsCompact W → ∃ B : ℝ, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ x ∈ C, ∀ y ∈ W,
        ‖nsum Γ f (x * a⁻¹) (a * y)‖ ≤ B * (∏ i, max (t i) 1) ^ A

def Core : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ s : Fin r, ∃ A : ℕ, ∀ m : ℕ,
    ∀ f ∈ CcAd D.sp.cm.sig V.gram, Van (unipRad D.sp.cm.sig V.gram (pre X s)) f →
    ∀ C W : Set (GAd D.sp.cm.sig V.gram), IsCompact C → IsCompact W → ∃ B : ℝ, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ x ∈ C, ∀ y ∈ W,
        ‖nsum (NF D.sp.cm.sig V.gram (pre X s)) f (x * a⁻¹) (a * y)‖ ≤ B * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m

def Bridge : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r),
    NA (frameFlag (isIsoFrame_firstCols hW j)) = unipRad D.sp.cm.sig V.gram (pre X j)

def Decay : Prop :=
  ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (c : ℝ), 0 < c → ∀ (j : Fin r) (f : GA D V → ℂ), f ∈ CcGA V →
    GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish (frameFlag (isIsoFrame_firstCols hW j)) f →
    ∀ C W : Set (GA D V), IsCompact C → IsCompact W → ∃ A : ℕ, ∀ m : ℕ, ∃ B : ℝ,
      ∀ t ∈ cone r c, ∀ a : GA D V, IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ x ∈ C, ∀ y ∈ W,
        ‖∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, f (x * (a⁻¹ * rat V ν * a) * y)‖ ≤
          B * (∏ i, max (t i) 1) ^ A * (root t j)⁻¹ ^ m

end MainStatements.WeightKernel.Dec

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DSmOfb
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem smOf : SmOf := by
  intro F E _ _ _ _ _ σ h n J _ f hf k γ hγ g
  exact (GlobalTheory.Orb.isSmoothRealFam_prod (fun i =>
    (GlobalTheory.ThK.CuspTransfer.Smooth.line_fam h (hγ i)).1.comp (contDiff_apply ℝ (fun _ => ℝ) i))).contDiff hf g

end MainStatements.WeightKernel.Dec

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.NsumLevel
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open PositivityTheory.ThKR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DCore

theorem nsum_level {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ)
    (z h κ : GAd σ J) (hκ : ∀ g, f (g * κ) = f g) : nsum Γ f z (h * κ) = nsum Γ f z h := by
  unfold nsum
  exact tsum_congr fun ν => by rw [← mul_assoc, hκ]

theorem nsum_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ)
    (z h γ : GAd σ J) (hγ : γ ∈ Γ) : nsum Γ f z (γ * h) = nsum Γ f z h := by
  unfold nsum
  have := (Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq (fun ν : Γ => f (z * ν * h))
  simpa [mul_assoc] using this

end MainStatements.WeightKernel.Dec.DCore

namespace MainStatements.WeightKernel.Dec
open MainStatements.WeightKernel.Dec.DCore

theorem core : DerMem → DerVan → Level → SumSm → Variation → NearCusp → Base → Core := by
  intro hDM hDV hL hSS hV hNC hBase D V r X Y hW c hc s
  have hcm := isCMExt_host D
  have hJV := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).2 V
  have hiso : GlobalTheory.UAut.IsIsoCols D.sp.cm.sig V.gram (pre X s) :=
    GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma hcm) hJV s.2
  have hcl : IsClosed (unipRad D.sp.cm.sig V.gram (pre X s) : Set (GAd D.sp.cm.sig V.gram)) :=
    GlobalTheory.UAut.unipFlag_const (σ := D.sp.cm.sig) (J := V.gram) (pre X s) 0 ▸
      GlobalTheory.UAut.isClosed_unipFlag hJV (sigma_sigma hcm) hiso _
  obtain ⟨A, hA⟩ := hBase D V r X Y hW c hc
  refine ⟨A, fun m => ?_⟩
  induction m with
  | zero =>
    intro f hf _ C W hC hWc
    obtain ⟨B, hB⟩ := hA (NF D.sp.cm.sig V.gram (pre X s)) inf_le_left f (continuous_of_mem_ccAd hf).1 (continuous_of_mem_ccAd hf).2 C W hC hWc
    exact ⟨B, fun t ht a ha x hx y hy => by simpa using hB t ht a ha x hx y hy⟩
  | succ m ih =>
    intro f hf hvan C W hC hWc
    obtain ⟨q, b, Ω₀, Cv, δ₁, hb, hΩ₀, hδ₁, hCv, hmv⟩ := GlobalTheory.T.siegel_set_uniform_smooth_bound _ _ D.sp.cm.sig hcm _ V.gram hJV
    have hW' : IsCompact ((fun x : GAd D.sp.cm.sig V.gram × GAd D.sp.cm.sig V.gram => x.1 * x.2) '' (W ×ˢ Ω₀)) :=
      (hWc.prod hΩ₀).image (by fun_prop)
    choose B hB using fun i => ih (lineDer (b i) f) (hDM _ _ _ hcm _ _ hJV f hf (b i) (hb i))
      (hDV _ _ _ hcm _ _ hJV _ hcl f hf (b i) (hb i) hvan) C _ hC hW'
    obtain ⟨B₀, hB₀⟩ := ih f hf hvan C W hC hWc
    obtain ⟨U, hUo, hU⟩ := hL _ _ _ hcm _ _ hJV f hf
    obtain ⟨M, hM0, hM⟩ := hNC _ _ _ hcm _ _ hJV r X Y hW W c U hWc hc hUo s
    have hR1 : 1 ≤ max 1 (M / δ₁) := le_max_left _ _
    have hSum : 0 ≤ ∑ i, |B i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|, fun t ht a ha x hx y hy => ?_⟩
    have hρ : 0 < ratio t s := ratio_pos ht s
    have hT : 0 ≤ (∏ i, max (t i) 1) ^ A :=
      pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) _
    have hρm : 0 < (ratio t s)⁻¹ ^ m := pow_pos (inv_pos.2 hρ) m
    have hρm1 : 0 < (ratio t s)⁻¹ ^ (m + 1) := pow_pos (inv_pos.2 hρ) _
    have key : (ratio t s)⁻¹ ^ m = ratio t s * (ratio t s)⁻¹ ^ (m + 1) := by
      rw [pow_succ]; field_simp
    have hB0a : 0 ≤ |B₀| := abs_nonneg _
    have hX : 0 ≤ Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by
      have := mul_nonneg (mul_nonneg hCv hM0) hSum
      positivity
    by_cases hcase : ratio t s ≤ max 1 (M / δ₁)
    · have h1 := hB₀ t ht a ha x hx y hy
      have h2 : B₀ * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m ≤
          |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hT) hρm.le
      have h3 : ratio t s * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) ≤
          max 1 (M / δ₁) * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right hcase (by positivity)
      have h4 : |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          ratio t s * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) := by
        rw [key]; ring
      have h5 : (max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) =
          max 1 (M / δ₁) * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) +
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by ring
      rw [h5]
      linarith
    · push Not at hcase
      have hδ : M / ratio t s ≤ δ₁ := by
        rw [div_le_iff₀ hρ]
        have h1 : M / δ₁ ≤ max 1 (M / δ₁) := le_max_right _ _
        rw [div_le_iff₀ hδ₁] at h1
        nlinarith
      have hsm := hSS _ _ _ hcm _ _ hJV (NF D.sp.cm.sig V.gram (pre X s)) inf_le_left f hf (x * a⁻¹)
      have hcc : ∀ i, ∀ x' ∈ Ω₀, ‖lineDer (b i) (nsum (NF D.sp.cm.sig V.gram (pre X s)) f (x * a⁻¹)) ((a * y) * x')‖ ≤
          |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m := fun i x' hx' => by
        rw [hsm.2 (b i) (hb i), mul_assoc]
        exact (hB i t ht a ha x hx (y * x') ⟨(y, x'), ⟨hy, hx'⟩, rfl⟩).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hT) hρm.le)
      have hvar := hV _ _ _ hcm _ _ hJV _ (pre X s) hiso f (continuous_of_mem_ccAd hf).1 (continuous_of_mem_ccAd hf).2
        hvan (x * a⁻¹) (a * y) (Cv * (M / ratio t s) * ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m)
        (fun m' hm' => by
          obtain ⟨γ, hγ, u, κ, hu, hκU, hκf, e'⟩ := hM t ht a ha y hy m' hm'
          rw [e', nsum_level _ _ _ _ _ (hU κ hκU hκf), mul_assoc γ, nsum_left _ _ _ _ _ hγ]
          exact hmv _ hsm.1 (a * y) u _ (div_nonneg hM0 hρ.le) hδ hu _ hcc)
      have hsum : ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m := by
        rw [Finset.sum_mul, Finset.sum_mul]
      have h6 : Cv * (M / ratio t s) * ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by
        rw [hsum, pow_succ, div_eq_mul_inv]; ring
      have h7 : 0 ≤ max 1 (M / δ₁) * |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by positivity
      rw [h6] at hvar
      have h5 : (max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) =
          max 1 (M / δ₁) * |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) +
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by ring
      rw [h5]
      linarith

end MainStatements.WeightKernel.Dec
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DDerMemc
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open scoped ContDiff ComplexConjugate Topology

noncomputable section

namespace MainStatements.WeightKernel.Dec.DDerMemc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exp_entry (Z : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z)) i j := by
  open scoped Matrix.Norms.Operator in
  have h1 : ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z) : Matrix (Fin n) (Fin n) ℂ) := by
    have : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    exact this.comp (contDiff_id.smul contDiff_const)
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp h1

theorem lineSm (h : IsCMExt F E σ) {b : ℝ → GAd σ J} (hb : IsRealLine σ J b) :
    ContDiff ℝ ∞ fun t => infCoord σ J (projInf σ J (b t)) := by
  classical
  obtain ⟨w, τ, Z, -, hZ⟩ := hb
  choose y hy hyZ using hZ
  refine contDiff_pi.2 fun u => contDiff_pi.2 fun τ' => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e0 : ∀ t, infCoord σ J (projInf σ J (b t)) u τ' i j = archMat σ J τ' (projArch σ J u (embArch σ J w (y t))) i j :=
    fun t => by rw [← hy t, ← projInfArch_projInf]; rfl
  simp only [e0]
  by_cases hu : u = w
  · subst hu
    simp only [projArch_embArch_self]
    have e1 : ∀ t, infEmb τ ((matHom _ σ J (y t)).1 i j) = (NormedSpace.exp (t • Z)) i j := fun t => by
      rw [← hyZ t]; rfl
    rcases infEmb_eq_or_conj h τ τ' with e | e
    · have : ∀ t, archMat σ J τ' (y t) i j = (NormedSpace.exp (t • Z)) i j := fun t => by
        rw [← e1 t, ← e]; rfl
      simp only [this]; exact exp_entry Z i j
    · have : ∀ t, archMat σ J τ' (y t) i j = conj ((NormedSpace.exp (t • Z)) i j) := fun t => by
        rw [← e1 t]
        change infEmb τ' _ = _
        rw [e]; rfl
      simp only [this]; exact Complex.conjCLE.contDiff.comp (exp_entry Z i j)
  · simp only [projArch_embArch_ne σ J hu]
    exact contDiff_const

theorem main (h : IsCMExt F E σ) {b : ℝ → GAd σ J} (hb : IsRealLine σ J b) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    (∀ g, DifferentiableAt ℝ (fun t => f (g * b t)) 0) ∧ lineDer b f ∈ CcAd σ J := by
  have hβ := lineSm h hb
  have hfin : ∀ t, projFin σ J (b t) = 1 := fun t =>
    mem_infPts.1 (GlobalTheory.RealLineInf.realLine_mem_infPts F E σ n J b hb t)
  have hbc : Continuous b := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
  have hb0 : b 0 = 1 := GlobalTheory.UAut.ConstAut.realLine_zero h hb
  obtain ⟨-, ⟨m, hm, em⟩, -⟩ := isGroupCoord_infCoord σ J
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨hac, Φ, hΦ, ea⟩, c, hc, rfl⟩ := hf
    set G := fun p : _ × ℝ => Φ (m (p.1, infCoord σ J (projInf σ J (b p.2)))) with hG
    have hGs : ContDiff ℝ ∞ G := hΦ.comp (hm.comp (contDiff_fst.prodMk (hβ.comp contDiff_snd)))
    have hd : ∀ x, HasDerivAt (fun t : ℝ => G (x, t)) (fderiv ℝ G (x, 0) (0, 1)) 0 := fun x =>
      ((hGs.differentiable (by simp)) (x, (0 : ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
    have ea' : ∀ (g : GInf σ J) t, a (g * projInf σ J (b t)) = G (infCoord σ J g, t) := fun g t => by
      rw [ea, em]
    have e1 : ∀ g, (fun t => infFin σ J a c (g * b t)) =
        fun t => G (infCoord σ J (projInf σ J g), t) * c (projFin σ J g) := fun g => funext fun t => by
      simp only [infFin, map_mul, hfin, mul_one, ea']
    refine ⟨fun g => by rw [e1]; exact ((hd _).mul_const _).differentiableAt, ?_⟩
    have e2 : lineDer b (infFin σ J a c) =
        infFin σ J (fun g => fderiv ℝ G (infCoord σ J g, 0) (0, 1)) c := funext fun g => by
      rw [lineDer, e1, ((hd _).mul_const _).deriv]; rfl
    rw [e2]
    refine infFin_mem_ccAd ⟨HasCompactSupport.intro hac.isCompact fun g hg => ?_,
      fun x => fderiv ℝ G (x, 0) (0, 1), ?_, fun _ => rfl⟩ hc
    · rw [← (hd _).deriv]
      have hc1 : Continuous fun t => g * projInf σ J (b t) :=
        continuous_const.mul ((continuous_projInf σ J).comp hbc)
      have : ∀ᶠ t in 𝓝 (0 : ℝ), g * projInf σ J (b t) ∈ (tsupport a)ᶜ :=
        hc1.continuousAt.eventually_mem ((isClosed_tsupport a).isOpen_compl.mem_nhds (by simpa [hb0] using hg))
      have e3 : (fun t : ℝ => G (infCoord σ J g, t)) =ᶠ[𝓝 0] fun _ => 0 :=
        this.mono fun t ht => (ea' g t).symm.trans (image_eq_zero_of_notMem_tsupport ht)
      rw [e3.deriv_eq, deriv_const]
    · exact ((hGs.fderiv_right (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const
  | zero => exact ⟨fun g => differentiableAt_const _, by
      have : lineDer b (0 : GAd σ J → ℂ) = 0 := funext fun g => by simp [lineDer]
      rw [this]; exact zero_mem _⟩
  | add f f' _ _ h1 h2 =>
    refine ⟨fun g => (h1.1 g).add (h2.1 g), ?_⟩
    have : lineDer b (f + f') = lineDer b f + lineDer b f' := funext fun g => deriv_add (h1.1 g) (h2.1 g)
    rw [this]; exact add_mem h1.2 h2.2
  | smul a f _ h1 =>
    refine ⟨fun g => (h1.1 g).const_smul a, ?_⟩
    have : lineDer b (a • f) = a • lineDer b f := funext fun g => deriv_const_smul a (h1.1 g)
    rw [this]; exact Submodule.smul_mem _ a h1.2

end MainStatements.WeightKernel.Dec.DDerMemc

theorem MainStatements.WeightKernel.Dec.derMem : MainStatements.WeightKernel.Dec.DerMem :=
  fun _ _ _ _ _ _ _ _ h _ _ _ _ hf _ hb => (MainStatements.WeightKernel.Dec.DDerMemc.main h hb hf).2
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DDerVan
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DDerVan

theorem mem_aux {G : Type*} [Group G] (K : Set G) (B : Set ℝ) (c : ℝ → G) (x y m : G) (t : ℝ)
    (hk : x * m * (y * c t) ∈ K) (ht : t ∈ B) :
    m ∈ (fun p : G × ℝ => x⁻¹ * p.1 * (y * c p.2)⁻¹) '' (K ×ˢ B) :=
  ⟨(x * m * (y * c t), t), ⟨hk, ht⟩, by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]⟩

end MainStatements.WeightKernel.Dec.DDerVan

theorem MainStatements.WeightKernel.Dec.derVan : MainStatements.WeightKernel.Dec.SmOf → MainStatements.WeightKernel.Dec.DerMem → MainStatements.WeightKernel.Dec.DerVan := by
  intro hSm hDer F E _ _ _ _ _ σ h n J hJ N hN f hf b hb hV ν _ x y
  have hfc := GlobalTheory.Orb.continuous_of_mem_ccAd (σ := σ) (J := J) hf
  have hf'c := GlobalTheory.Orb.continuous_of_mem_ccAd (σ := σ) (J := J) (hDer F E σ h n J hJ f hf b hb)
  have hs := hSm F E σ h n J hJ f hf
  have hbc : Continuous b := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
  have hK : IsCompact (tsupport f ∪ tsupport (lineDer b f)) := IsCompact.union hfc.2 hf'c.2
  have hS : IsCompact ((fun p : GAd σ J × ℝ => x⁻¹ * p.1 * (y * b p.2)⁻¹) ''
      ((tsupport f ∪ tsupport (lineDer b f)) ×ˢ Metric.closedBall (0 : ℝ) 1)) :=
    (hK.prod (isCompact_closedBall 0 1)).image
      ((continuous_const.mul continuous_fst).mul ((continuous_const.mul (hbc.comp continuous_snd)).inv))
  have hC := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  have key := GlobalTheory.LaurentAut.hasDerivAt_integral_cpt (𝕜 := ℝ) ν (x₀ := 0)
    (Φ := fun t (m : N) => f (x * m * (y * b t))) (Φ' := fun t (m : N) => lineDer b f (x * m * (y * b t))) hC ?_ ?_ ?_ ?_
  · have h0 : (fun t : ℝ => ∫ m : N, f (x * m * (y * b t)) ∂ν) = fun _ => 0 := funext fun t => hV ν x (y * b t)
    rw [h0] at key
    have e := key.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simpa [GlobalTheory.UAut.ConstAut.realLine_zero h hb] using e
  · intro t
    exact hfc.1.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  · exact hf'c.1.comp ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
      (continuous_const.mul (hbc.comp continuous_fst)))
  · intro t ht m hm
    have hnot : x * ↑m * (y * b t) ∉ tsupport f ∪ tsupport (lineDer b f) := fun hk =>
      hm (MainStatements.WeightKernel.Dec.DDerVan.mem_aux _ _ b x y (↑m) t hk ht)
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h' => hnot (Or.inl h')),
      image_eq_zero_of_notMem_tsupport (fun h' => hnot (Or.inr h'))⟩
  · intro t m
    have := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hb (x * ↑m * y) t
    simpa [mul_assoc] using this
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DSumSm
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DSumSm

lemma loc_fin {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {Γ : Subgroup G} [DiscreteTopology Γ] {f : G → ℂ} (hf : HasCompactSupport f) (z : G)
    [TopologicalSpace X] [WeaklyLocallyCompactSpace X] {φ : X → G} (hφ : Continuous φ) (x₀ : X) :
    ∃ S : Finset Γ, ∀ᶠ x in 𝓝 x₀, ∀ ν : Γ, ν ∉ S → f (z * ν * φ x) = 0 := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x₀
  have hfin := GlobalTheory.AutomorphicL2KernelContinuous.finite_contributing (Γ := Γ) hf (isCompact_singleton (x := z⁻¹))
    (hK.image hφ)
  refine ⟨hfin.toFinset, Filter.mem_of_superset hKn fun x hx ν hν => ?_⟩
  by_contra h
  apply hν
  rw [Set.Finite.mem_toFinset]
  exact ⟨z⁻¹, rfl, φ x, ⟨x, hx, rfl⟩, by simpa using h⟩

lemma cont_prod {G : Type} [Monoid G] [TopologicalSpace G] [ContinuousMul G] :
    ∀ (k : ℕ) (γ : Fin k → ℝ → G), (∀ i, Continuous (γ i)) →
      Continuous fun t : Fin k → ℝ => (List.ofFn fun i => γ i (t i)).prod
  | 0, γ, _ => by simpa using continuous_const
  | k + 1, γ, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact ((h 0).comp (continuous_apply 0)).mul
      ((cont_prod k (fun i => γ i.succ) (fun i => h i.succ)).comp
        (continuous_pi fun i => continuous_apply i.succ))

end MainStatements.WeightKernel.Dec.DSumSm

namespace MainStatements.WeightKernel.Dec

open DSumSm in
theorem sumSm : SmOf → SumSm := by
  intro hSm F E _ _ _ _ _ σ h n J hJ Γ hΓ f hf z
  have : DiscreteTopology Γ :=
    DiscreteTopology.of_subset (t := (Γ : Set (GAd σ J))) (s := (ratPts σ J : Set (GAd σ J)))
      (inferInstance : DiscreteTopology (ratPts σ J)) hΓ
  have hs : GlobalTheory.UAut.IsSm σ J f := hSm F E σ h n J hJ f hf
  have hcs : HasCompactSupport f := (continuous_of_mem_ccAd hf).2
  refine ⟨?_, ?_⟩
  · intro k γ hγ g
    rw [contDiff_iff_contDiffAt]
    intro t₀
    have hφ : Continuous fun t : Fin k → ℝ => g * (List.ofFn fun i => γ i (t i)).prod :=
      continuous_const.mul (cont_prod k γ fun i =>
        GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J (γ i) (hγ i))
    obtain ⟨S, hS⟩ := loc_fin (Γ := Γ) hcs z hφ t₀
    have hsum : ContDiffAt ℝ ∞ (fun t : Fin k → ℝ =>
        ∑ ν ∈ S, f (z * ν * (g * (List.ofFn fun i => γ i (t i)).prod))) t₀ := by
      refine ContDiff.contDiffAt (ContDiff.sum fun ν _ => ?_)
      have := hs k γ hγ (z * ν * g)
      simpa only [mul_assoc] using this
    refine hsum.congr_of_eventuallyEq (hS.mono fun t ht => ?_)
    exact tsum_eq_sum (s := S) (fun ν hν => ht ν hν)
  · intro b hb
    funext g
    have hbc := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
    obtain ⟨S, hS⟩ := loc_fin (Γ := Γ) (φ := fun t : ℝ => g * b t) hcs z (continuous_const.mul hbc) 0
    have hline : ∀ x : GAd σ J, ContDiff ℝ ∞ fun t : ℝ => f (x * b t) := by
      intro x
      have := (hs 1 (fun _ => b) (fun _ => hb) x).comp
        (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)
      convert this using 2
      simp [List.ofFn_succ]
    have e1 : (fun t => nsum Γ f z (g * b t)) =ᶠ[𝓝 0]
        fun t => ∑ ν ∈ S, f (z * ν * (g * b t)) :=
      hS.mono fun t ht => tsum_eq_sum (s := S) (fun ν hν => ht ν hν)
    have e2 : ∀ ν ∉ S, lineDer b f (z * ν * g) = 0 := by
      intro ν hν
      show deriv (fun t => f (z * ν * g * b t)) 0 = 0
      have : (fun t => f (z * ν * g * b t)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) :=
        hS.mono fun t ht => by simpa only [mul_assoc] using ht ν hν
      rw [this.deriv_eq, deriv_const]
    show deriv (fun t => nsum Γ f z (g * b t)) 0 = ∑' ν : Γ, lineDer b f (z * ν * g)
    rw [e1.deriv_eq, tsum_eq_sum (s := S) e2, deriv_fun_sum]
    · refine Finset.sum_congr rfl fun ν _ => ?_
      show _ = deriv (fun t => f (z * ν * g * b t)) 0
      simp only [mul_assoc]
    · intro ν _
      have := ((hline (z * ν * g)).differentiable (by simp)) 0
      simpa only [mul_assoc] using this

end MainStatements.WeightKernel.Dec

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DLevel
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem level_of_mem {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, b, hb, rfl⟩ := hx
    obtain ⟨V, hV, hVb⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨V.comap (projFin σ J), hV.preimage (continuous_projFin σ J), fun k hk hkf g => ?_⟩
    show a (projInf σ J (g * k)) * b (projFin σ J (g * k)) = a (projInf σ J g) * b (projFin σ J g)
    rw [map_mul, map_mul, mem_finPts.1 hkf, mul_one, (hVb _ hk _).2]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨V, hV, h'⟩ := hy
    exact ⟨U ⊓ V, hU.inter hV, fun k hk hkf g => by
      simp only [Pi.add_apply, h k hk.1 hkf g, h' k hk.2 hkf g]⟩
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf g => by simp only [Pi.smul_apply, h k hk hkf g]⟩

end MainStatements.WeightKernel.Dec.DLevel

theorem MainStatements.WeightKernel.Dec.level : MainStatements.WeightKernel.Dec.Level := by
  intro F E _ _ _ _ _ σ _ n J _ f hf
  exact MainStatements.WeightKernel.Dec.DLevel.level_of_mem hf

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DBridge
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem bridge : Bridge := by
  intro D V r X Y hW j
  rw [NA_frameFlag]
  rfl

end MainStatements.WeightKernel.Dec

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DVariationb
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem variation : Variation := by
  intro F E _ _ _ _ _ σ hCM n J hJ k C hC f hf hfs hV z g e he
  have := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  have hc : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipRad σ J C) := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  have hcl : IsClosed (unipRad σ J C : Set (GAd σ J)) :=
    GlobalTheory.UAut.unipFlag_const (σ := σ) (J := J) C 0 ▸ GlobalTheory.UAut.isClosed_unipFlag hJ (sigma_sigma hCM) hC _
  let ν : Measure (unipRad σ J C) := Measure.haar
  have h𝓕 := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)) ν
  have hfin : ν (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ≠ ⊤ := hc.measure_ne_top h𝓕
  have hpos : ν (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  let h : unipRad σ J C → ℂ := fun m => f (z * m * g)
  have hcont : Continuous h := by fun_prop
  let T := (Homeomorph.mulLeft z).trans (Homeomorph.mulRight g)
  have hK : IsCompact (T ⁻¹' tsupport f) := T.isCompact_preimage.2 hfs
  have hsupp : HasCompactSupport h :=
    HasCompactSupport.intro' (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK)
      ((isClosed_tsupport f).preimage (T.continuous.comp continuous_subtype_val))
      fun x hx => image_eq_zero_of_notMem_tsupport (f := f) (x := z * (x : GAd σ J) * g) hx
  have hint : Integrable h ν := hcont.integrable_of_hasCompactSupport hsupp
  have hV0 : ∫ m, h m ∂ν = 0 := hV ν z g
  let F' : (ratPts σ J).subgroupOf (unipRad σ J C) → unipRad σ J C → ℂ := fun γ x => h (γ • x)
  have hmeas : ∀ γ, AEStronglyMeasurable (F' γ) (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    fun γ => (hcont.comp (continuous_const_smul γ)).aestronglyMeasurable
  have hlin : ∑' γ, ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ‖F' γ x‖ₑ ∂ν ≠ ⊤ := by
    have hl : ∫⁻ x, ‖h x‖ₑ ∂ν = ∑' γ, ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ‖F' γ x‖ₑ ∂ν := by
      rw [h𝓕.lintegral_eq_tsum' (fun x => ‖h x‖ₑ), ← (Equiv.inv _).tsum_eq]; simp [F']
    rw [← hl]; exact hint.2.ne
  have e1 : ∫ m, h m ∂ν = ∑' γ, ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), F' γ x ∂ν := by
    rw [h𝓕.integral_eq_tsum' h hint, ← (Equiv.inv _).tsum_eq]; simp [F']
  have e2 := integral_tsum hmeas hlin
  have hΨ : ∀ x : unipRad σ J C, ∑' γ, F' γ x = nsum (NF σ J C) f z ((x : GAd σ J) * g) := fun x => by
    let eq : (ratPts σ J).subgroupOf (unipRad σ J C) ≃ NF σ J C :=
      { toFun := fun γ => ⟨γ.1.1, γ.2, γ.1.2⟩, invFun := fun ν => ⟨⟨ν.1, ν.2.2⟩, ν.2.1⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [nsum, ← eq.tsum_eq]
    congr 1; funext γ
    show f (z * ((γ • x : unipRad σ J C) : GAd σ J) * g) = _
    rw [Subgroup.smul_def]; simp [eq, mul_assoc]
  have hzero : ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)),
      nsum (NF σ J C) f z ((x : GAd σ J) * g) ∂ν = 0 := by
    simp_rw [← hΨ]; rw [e2]; exact e1.symm.trans hV0
  have hae : ∀ᵐ x ∂(ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))),
      HasSum (fun γ => F' γ x) (∑' γ, F' γ x) := by
    have h1 : ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ∑' γ, ‖F' γ x‖ₑ ∂ν ≠ ⊤ := by
      rw [lintegral_tsum (fun γ => (hmeas γ).enorm)]; exact hlin
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun γ => (hmeas γ).enorm) h1] with x hx
    have hs : Summable fun γ => ‖F' γ x‖₊ :=
      ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [enorm_eq_nnnorm] using hx.ne)
    exact (Summable.of_norm (NNReal.summable_coe.2 hs)).hasSum
  have hΨm : AEStronglyMeasurable (fun x : unipRad σ J C => ∑' γ, F' γ x)
      (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s => by first
        | exact Finset.aestronglyMeasurable_fun_sum s fun γ _ => hmeas γ
        | exact Finset.aestronglyMeasurable_sum s fun γ _ => hmeas γ) hae
  haveI : IsFiniteMeasure (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    isFiniteMeasure_restrict.2 hfin
  have hΨi : IntegrableOn (fun x : unipRad σ J C => nsum (NF σ J C) f z ((x : GAd σ J) * g))
      (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ν := by
    refine Integrable.of_bound (C := e + ‖nsum (NF σ J C) f z g‖) ?_ (.of_forall fun x => ?_)
    · simpa only [hΨ] using hΨm
    · have := he x x.2
      calc _ = ‖(nsum (NF σ J C) f z ((x : GAd σ J) * g) - nsum (NF σ J C) f z g) + nsum (NF σ J C) f z g‖ := by
              rw [sub_add_cancel]
        _ ≤ _ := (norm_add_le _ _).trans (by linarith)
  have key : ν.real (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) • nsum (NF σ J C) f z g =
      ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)),
        (nsum (NF σ J C) f z g - nsum (NF σ J C) f z ((x : GAd σ J) * g)) ∂ν := by
    rw [integral_sub (integrable_const _) hΨi, hzero, setIntegral_const, sub_zero]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := ν) hfin.lt_top
    (f := fun x : unipRad σ J C => nsum (NF σ J C) f z g - nsum (NF σ J C) f z ((x : GAd σ J) * g)) (C := e)
    (fun x _ => by rw [norm_sub_rev]; exact he x x.2)
  rw [← key, norm_smul, Real.norm_of_nonneg measureReal_nonneg] at hb
  have hp : 0 < ν.real (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) := ENNReal.toReal_pos hpos hfin
  nlinarith [norm_nonneg (nsum (NF σ J C) f z g)]

end MainStatements.WeightKernel.Dec
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DNearCusp
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay.NearCusp
open scoped Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem nearCusp : NearCusp := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW Cm c U hCm hc hU s
  have hσ := sigma_sigma hCM
  have hC : GlobalTheory.UAut.IsIsoCols σ J (pre X s) := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ s.2
  let Cf : Set (GFin σ J) := (fun z : GAd σ J => projFin σ J z) '' Cm
  have hCf : IsCompact Cf := hCm.image (continuous_projFin σ J)
  let Uf : Set (GFin σ J) := ofFin σ J ⁻¹' (U : Set (GAd σ J))
  have hUf : Uf ∈ 𝓝 (1 : GFin σ J) :=
    (hU.preimage (continuous_ofFin σ J)).mem_nhds (by simp only [Set.mem_preimage, map_one]; exact U.one_mem)
  let Wn : Set (GFin σ J) := {x | ∀ h ∈ Cf, h⁻¹ * x * h ∈ Uf}
  have hWn : Wn ∈ 𝓝 (1 : GFin σ J) := conj_mem_nhds hCf hUf
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.T.unipotent_radical_compact_fundamental_domain F E σ hCM n J hJ _ (pre X s) hC Wn hWn
  obtain ⟨M₁, hM₁, hM₁b⟩ := GlobalTheory.T.torus_conjugate_unipotent_bounded F E σ hCM n J hJ r X Y hW Q c hQ hc s
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_bound_archMat (σ := σ) (J := J) hCm
  refine ⟨C₀ * M₁, mul_nonneg hC₀ hM₁, ?_⟩
  intro t ht a ha k hk m hm
  obtain ⟨γ, hγ, q, hqQ, hqU, hqW, rfl⟩ := hQm m hm
  have hγU : γ ∈ unipRad σ J (pre X s) := by
    have := mul_mem hm (inv_mem hqU)
    rwa [mul_inv_cancel_right] at this
  have hfa : projFin σ J a = 1 := mem_infPts.1 ha.1
  refine ⟨γ, ⟨hγ, hγU⟩, ofInf σ J (projInf σ J ((a * k)⁻¹ * q * (a * k))),
    ofFin σ J (projFin σ J ((a * k)⁻¹ * q * (a * k))), ⟨mem_infPts.2 (projFin_ofInf σ J _), ?_⟩, ?_,
    mem_finPts.2 (projInf_ofFin σ J _), ?_⟩
  · intro w τ i j
    have hN := hM₁b q hqQ hqU t ht a ha w τ
    have ev : (a * k)⁻¹ * q * (a * k) = k⁻¹ * (a⁻¹ * q * a) * k := by group
    have hB : archMat σ J τ (projArch σ J w k⁻¹) * archMat σ J τ (projArch σ J w k) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    have key : archMat σ J τ (projArch σ J w (ofInf σ J (projInf σ J ((a * k)⁻¹ * q * (a * k))))) - 1 =
        archMat σ J τ (projArch σ J w k⁻¹) * (archMat σ J τ (projArch σ J w (a⁻¹ * q * a)) - 1) *
          archMat σ J τ (projArch σ J w k) := by
      rw [projArch_ofInf, projInfArch_projInf, ev, map_mul (projArch σ J w) _ k, map_mul (projArch σ J w) k⁻¹,
        map_mul (archMat σ J τ), map_mul (archMat σ J τ), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hB]
    rw [key]
    refine (GlobalTheory.CuspGeo.norm_mul_mul_apply_le _ _ _ _ hN i j).trans ?_
    rw [mul_div_assoc C₀]
    exact mul_le_mul_of_nonneg_right (hC₀b k hk w τ i j) (div_nonneg hM₁ (ratio_pos ht s).le)
  · have hh : projFin σ J k ∈ Cf := ⟨k, hk, rfl⟩
    have e : projFin σ J ((a * k)⁻¹ * q * (a * k)) =
        (projFin σ J k)⁻¹ * projFin σ J q * projFin σ J k := by
      simp only [map_mul, map_inv, hfa, one_mul]
    have := hqW _ hh
    rw [← e] at this
    exact this
  · rw [mul_assoc (γ * (a * k)), ofInf_projInf_mul_ofFin_projFin]
    group

end MainStatements.WeightKernel.Dec
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.NcardBiUnionLe
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DBase

theorem ncard_biUnion_le' {α ι : Type*} (I : Finset ι) (S : ι → Set α) (h : ∀ i ∈ I, (S i).Finite) :
    (⋃ i ∈ I, S i).ncard ≤ ∑ i ∈ I, (S i).ncard := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert j I hj ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
    refine (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) _)

end MainStatements.WeightKernel.Dec.DBase

namespace MainStatements.WeightKernel.Dec
open DBase

theorem base : Base := by
  intro D V r X Y hW c hc
  obtain ⟨V₀, hV₀c, hV₀n⟩ := exists_compact_mem_nhds (1 : GA D V)
  have hC₀ : IsCompact (V₀⁻¹ * V₀) := hV₀c.inv.mul hV₀c
  obtain ⟨A, B₀, hAB⟩ := GlobalTheory.T.finite_lattice_points_in_siegel_set_bound D V r X Y hW c hc _ hC₀
  refine ⟨A, fun Γ hΓ f hf hfs C W hC hW' => ?_⟩
  set K : Set (GA D V) := C⁻¹ * tsupport f * W⁻¹ with hK
  have hKc : IsCompact K := (hC.inv.mul hfs.isCompact).mul hW'.inv
  have hint : interior V₀ ∈ nhds (1 : GA D V) := interior_mem_nhds.2 hV₀n
  obtain ⟨I, hI⟩ := hKc.elim_finite_subcover (fun g : K => (g : GA D V) • interior V₀)
    (fun g => isOpen_interior.smul _) (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩,
      ⟨1, mem_of_mem_nhds hint, by simp⟩⟩)
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfs
  refine ⟨max M 0 * I.card * max B₀ 0, fun t ht a ha x hx y hy => ?_⟩
  obtain ⟨hfin₀, hcnt₀⟩ := hAB t ht a ha
  set S₀ := {δ : GF V | a⁻¹ * rat V δ * a ∈ V₀⁻¹ * V₀}
  set S : K → Set (GF V) := fun g => {δ : GF V | a⁻¹ * rat V δ * a ∈ (g : GA D V) • V₀}
  have hS : ∀ g, (S g).Finite ∧ (S g).ncard ≤ S₀.ncard := by
    intro g
    rcases (S g).eq_empty_or_nonempty with h | ⟨δ₀, hδ₀⟩
    · rw [h]; simp
    have hmap : ∀ δ ∈ S g, δ₀⁻¹ * δ ∈ S₀ := by
      intro δ hδ
      obtain ⟨u, hu, hu'⟩ := hδ
      obtain ⟨u₀, hu₀, hu₀'⟩ := hδ₀
      refine ⟨u₀⁻¹, Set.inv_mem_inv.2 hu₀, u, hu, ?_⟩
      simp only [smul_eq_mul] at hu' hu₀'
      have e : a⁻¹ * rat V (δ₀⁻¹ * δ) * a = (a⁻¹ * rat V δ₀ * a)⁻¹ * (a⁻¹ * rat V δ * a) := by
        simp [map_mul, map_inv, mul_assoc]
      rw [e, ← hu', ← hu₀']; group
    have hinj : Set.InjOn (fun δ => δ₀⁻¹ * δ) (S g) := fun _ _ _ _ h => mul_left_cancel h
    have hf1 : (S g).Finite := Set.Finite.of_finite_image (hfin₀.subset (by
      rintro _ ⟨δ, hδ, rfl⟩; exact hmap δ hδ)) hinj
    exact ⟨hf1, Set.ncard_le_ncard_of_injOn _ hmap hinj hfin₀⟩
  set T := {δ : GF V | a⁻¹ * rat V δ * a ∈ K}
  have hTsub : T ⊆ ⋃ g ∈ I, S g := by
    intro δ hδ
    obtain ⟨g, hg, hmem⟩ := Set.mem_iUnion₂.1 (hI hδ)
    exact Set.mem_iUnion₂.2 ⟨g, hg, Set.smul_set_mono interior_subset hmem⟩
  have hUfin : (⋃ g ∈ I, S g).Finite := Set.Finite.biUnion I.finite_toSet fun g _ => (hS g).1
  have hTfin : T.Finite := hUfin.subset hTsub
  have hTcnt : (T.ncard : ℝ) ≤ I.card * max B₀ 0 * (∏ i, max (t i) 1) ^ A := by
    have h1 : T.ncard ≤ I.card * S₀.ncard := by
      refine (Set.ncard_le_ncard hTsub hUfin).trans ((ncard_biUnion_le' I S fun g _ => (hS g).1).trans ?_)
      simpa using Finset.sum_le_sum (s := I) fun g _ => (hS g).2
    have hP : 0 ≤ (∏ i, max (t i) 1) ^ A :=
      pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) A
    calc (T.ncard : ℝ) ≤ I.card * S₀.ncard := by exact_mod_cast h1
      _ ≤ I.card * (max B₀ 0 * (∏ i, max (t i) 1) ^ A) := by
          gcongr
          exact hcnt₀.trans (by gcongr; exact le_max_left _ _)
      _ = _ := by ring

  set g : Γ → ℂ := fun ν => f (x * a⁻¹ * ν * (a * y)) with hg
  have hsupp : ∀ ν : Γ, g ν ≠ 0 → ∃ δ ∈ T, rat V δ = ν := by
    intro ν hν
    obtain ⟨δ, hδ⟩ : (ν : GA D V) ∈ (ratEmb D.sp.cm.sig V.gram).range :=
      (range_ratEmb D.sp.cm.sig V.gram).symm ▸ hΓ ν.2
    refine ⟨δ, ?_, hδ⟩
    have hs : x * a⁻¹ * ν * (a * y) ∈ tsupport f := subset_tsupport _ hν
    show a⁻¹ * rat V δ * a ∈ K
    refine ⟨x⁻¹ * (x * a⁻¹ * ν * (a * y)), ⟨x⁻¹, Set.inv_mem_inv.2 hx, _, hs, rfl⟩, y⁻¹,
      Set.inv_mem_inv.2 hy, ?_⟩
    show _ = _
    rw [show rat V δ = ν from hδ]; group
  have hsf : (Function.support g).Finite := by
    refine (hTfin.image (rat V)).preimage (Subtype.val_injective.injOn) |>.subset ?_
    intro ν hν
    obtain ⟨δ, hδ, e⟩ := hsupp ν hν
    exact ⟨δ, hδ, e⟩
  have hcard : (hsf.toFinset.card : ℝ) ≤ T.ncard := by
    have : (Function.support g).ncard ≤ T.ncard := by
      have h2 : (Function.support g).ncard ≤ (rat V '' T).ncard :=
        Set.ncard_le_ncard_of_injOn Subtype.val (fun ν hν => by
          obtain ⟨δ, hδ, e⟩ := hsupp ν hν; exact ⟨δ, hδ, e⟩) Subtype.val_injective.injOn (hTfin.image _)
      exact h2.trans (Set.ncard_image_le hTfin)
    rw [Set.ncard_eq_toFinset_card _ hsf] at this
    exact_mod_cast this
  show ‖∑' ν : Γ, g ν‖ ≤ _
  rw [tsum_eq_sum (s := hsf.toFinset) (fun ν hν => by simpa using hν)]
  have hP : 0 ≤ (∏ i, max (t i) 1) ^ A :=
    pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) A
  calc ‖∑ ν ∈ hsf.toFinset, g ν‖ ≤ ∑ ν ∈ hsf.toFinset, ‖g ν‖ := norm_sum_le _ _
    _ ≤ ∑ _ν ∈ hsf.toFinset, max M 0 := Finset.sum_le_sum fun ν _ => (hM _).trans (le_max_left _ _)
    _ = hsf.toFinset.card * max M 0 := by simp
    _ ≤ T.ncard * max M 0 := by gcongr
    _ ≤ (I.card * max B₀ 0 * (∏ i, max (t i) 1) ^ A) * max M 0 := by gcongr
    _ = _ := by ring

end MainStatements.WeightKernel.Dec
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DDecay
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

namespace DDecay

theorem tsum_eq (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r)
    (hB : NA (frameFlag (isIsoFrame_firstCols hW j)) = unipRad D.sp.cm.sig V.gram (pre X j))
    (g : GA D V → ℂ) :
    ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν) =
      ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := by
  have hS : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)) =
      rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) : Set (GF V)) := by
    rw [← Subgroup.coe_map, map_unipRat, hB]; rfl
  calc ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν)
      = ∑' b : (rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) :
          Set (GF V))), g b := (tsum_image g (ratEmb_injective _ _).injOn).symm
    _ = ∑' c : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)),
          g (Set.equivOfEq hS c) := (Equiv.tsum_eq (Set.equivOfEq hS) (fun b => g b)).symm
    _ = ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := rfl

end DDecay

theorem decay : Core → Bridge → Decay := by
  intro hCore hBridge D V r X Y hW c hc j f hf hU C W hC hW'
  obtain ⟨A, hA⟩ := hCore D V r X Y hW c hc j
  have hB := hBridge D V r X Y hW j
  have hV : Van (unipRad D.sp.cm.sig V.gram (pre X j)) f := by
    have h0 : Van (NA (frameFlag (isIsoFrame_firstCols hW j))) f := fun ν _ x y => (hU ν x y).2
    rw [hB] at h0
    exact h0
  refine ⟨A, fun m => ?_⟩
  obtain ⟨B, hBd⟩ := hA m f hf hV C W hC hW'
  refine ⟨B, fun t ht a ha x hx y hy => ?_⟩
  have h1 := hBd t ht a ha x hx y hy
  have h2 : ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm,
      f (x * (a⁻¹ * rat V ν * a) * y) = nsum (NF D.sp.cm.sig V.gram (pre X j)) f (x * a⁻¹) (a * y) := by
    rw [nsum, ← DDecay.tsum_eq D V r X Y hW j hB (fun g => f (x * a⁻¹ * g * (a * y)))]
    congr 1; funext ν; congr 1; group
  rw [h2]
  exact h1

end MainStatements.WeightKernel.Dec
end
end

namespace MainStatements.WeightKernel.Dec

theorem decay_holds : Decay :=
  decay (core derMem (derVan smOf derMem) level (sumSm smOf) variation nearCusp base) bridge

end MainStatements.WeightKernel.Dec
