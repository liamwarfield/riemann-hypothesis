module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.PositiveSumGrowth.AbsAPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSiegelEisensteinModerateGrowthConvergen
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSumModerateGrowthConvergent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSumModerateGrowthConvergent
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.EisConvGrowth

theorem eis_modGrowth : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → (V.rank : ℝ) / 2 < s₁.re → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V φ) := by
  intro D V a ha hI μ s₁ φ hφ h
  haveI := t2Space_adeleRing' (F := D.host.F)
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s₁.re + (V.rank : ℝ) / 2) :=
    hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.SWAbsGrowth.hgt_mul_le V a ha
  set τ : ℝ := s₁.re + (V.rank : ℝ) / 2 with hτ
  have hτ0 : 0 ≤ τ := by
    have : (0 : ℝ) ≤ (V.rank : ℝ) / 2 := by positivity
    linarith
  have hs := GlobalTheory.Eis.sphConv D V a hI s₁.re h
  set S := ∑' q : GlobalTheory.Eis.SiegelCosets V, (hgt V a (q.out : GQ (dblSp V)) : ℝ) ^ τ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set M : ℕ := ⌈τ⌉₊ with hM
  refine ⟨max C₁ 0 * (max C₂ 1) ^ M * S, 2 * V.rank * M, fun y => ?_⟩
  set H := GlobalTheory.Grow.height (dblSp V) y with hH
  have hH1 : 1 ≤ H := GlobalTheory.Grow.one_le_height _ y
  set K := max C₂ 1 * H ^ (2 * V.rank) with hK
  have hone : 1 ≤ K := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hH1)
  set c := max C₁ 0 * K ^ M with hc
  have hq : ∀ x : GA D (dblSp V), ‖φ (x * y)‖ ≤ c * (hgt V a x : ℝ) ^ τ := by
    intro x
    refine (hC₁ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by positivity)).trans ?_
    rw [hc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    have h3 : (hgt V a (x * y) : ℝ) ≤ hgt V a x * K :=
      (h₂ x y).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (NNReal.coe_nonneg _))
    refine (Real.rpow_le_rpow (NNReal.coe_nonneg _) h3 hτ0).trans ?_
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (by positivity), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← Real.rpow_natCast _ M]
    exact Real.rpow_le_rpow_of_exponent_le hone (Nat.le_ceil τ)
  have hsum : HasSum (fun q : GlobalTheory.Eis.SiegelCosets V => c * (hgt V a (q.out : GQ (dblSp V)) : ℝ) ^ τ) (c * S) :=
    hs.hasSum.mul_left c
  have hb : ‖GlobalTheory.Eis.eis V φ y‖ ≤ c * S := tsum_of_norm_bounded hsum fun q => hq _
  refine hb.trans (le_of_eq ?_)
  rw [hc, hK, mul_pow, ← pow_mul]
  ring

end GlobalTheory.EisConvGrowth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSumModerateGrowthConvergentStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelEisensteinSum_moderateGrowth_convergent : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → (V.rank : ℝ) / 2 < s₁.re → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V φ) := by
  first | exact @GlobalTheory.EisConvGrowth.eis_modGrowth | exact GlobalTheory.EisConvGrowth.eis_modGrowth | (intros; apply GlobalTheory.EisConvGrowth.eis_modGrowth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSiegelEisensteinModerateGrowthConvergen
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.SphGrowth

theorem spherical_eisenstein_modGrowth : ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (σ : ℂ))) :=
  fun D V _ a ha hI σ hσ => GlobalTheory.T.siegelEisensteinSum_moderateGrowth_convergent D V a ha hI 1 σ _ (GlobalTheory.Eis.sph_mem hI (σ : ℂ)) (by simpa using hσ)

end GlobalTheory.Core.Rk.SphGrowth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSiegelEisensteinModerateGrowthConvergenStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalSiegelEisenstein_moderate_growth_convergent : ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (σ : ℂ))) := by
  first | exact @GlobalTheory.Core.Rk.SphGrowth.spherical_eisenstein_modGrowth | exact GlobalTheory.Core.Rk.SphGrowth.spherical_eisenstein_modGrowth | (intros; apply GlobalTheory.Core.Rk.SphGrowth.spherical_eisenstein_modGrowth <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.PositiveSumGrowth.GrowPf
noncomputable section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.AutomorphicL2Unitary
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ResidueKilled.Tr

theorem posSum_growth' (D : D7) (V : HSp D) (hV : 0 < V.rank) (a : GL (Fin V.rank) (AE D)) (ha : IsMaj V a)
    (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) (p : GA D (dblSp V)) (c : ℝ≥0) (hc : 0 < c)
    (h : GA D (dblSp V) → ℝ) (hh : ∀ x, h x = Real.log (hgt V a (x * p⁻¹)) + Real.log c) (t : ℝ)
    (ht : (V.rank : ℝ) < t) : ∃ (C : ℝ) (N : ℕ), ∀ g,
      ‖GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (fun x => (Real.exp (t * h x) : ℂ)) g‖ ≤
        C * GlobalTheory.Grow.height (dblSp V) g ^ N := by
  have hσ : (V.rank : ℝ) / 2 < t - (V.rank : ℝ) / 2 := by linarith
  obtain ⟨C₀, A, hC₀⟩ := GlobalTheory.T.sphericalSiegelEisenstein_moderate_growth_convergent D V hV a ha hI (t - (V.rank : ℝ) / 2) hσ
  have hpos : ∀ y, 0 < hgt V a y := fun y => hgtH_pos _
  have hf : (fun x => (Real.exp (t * h x) : ℂ)) = (Real.exp (t * Real.log c) : ℂ) •
      fun x => GlobalTheory.Eis.sph V a (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ) (x * p⁻¹) := by
    funext x
    have e : (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ) + (V.rank : ℂ) / 2 = (t : ℂ) := by push_cast; ring
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.Eis.sph]
    rw [npow_eq_exp (hpos _), e, hh x, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  refine ⟨Real.exp (t * Real.log c) * |C₀| * GlobalTheory.Grow.height (dblSp V) p⁻¹ ^ A, A, fun g => ?_⟩
  rw [hf, GlobalTheory.Eis.cosetSum_smul, GlobalTheory.Eis.cosetSum_mul_right, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have h1 := hC₀ (g * p⁻¹)
  have h2 : GlobalTheory.Grow.height (dblSp V) (g * p⁻¹) ^ A ≤
      (GlobalTheory.Grow.height (dblSp V) g * GlobalTheory.Grow.height (dblSp V) p⁻¹) ^ A :=
    pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le (GlobalTheory.Grow.height_mul_le _ _ _) A
  have h3 : 0 ≤ GlobalTheory.Grow.height (dblSp V) (g * p⁻¹) ^ A := pow_nonneg (GlobalTheory.Grow.height_pos _ _).le A
  have h4 : ‖GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ)) (g * p⁻¹)‖ ≤
      |C₀| * (GlobalTheory.Grow.height (dblSp V) g * GlobalTheory.Grow.height (dblSp V) p⁻¹) ^ A :=
    h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C₀) h3).trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))
  calc Real.exp (t * Real.log c) * ‖GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V))
        (GlobalTheory.Eis.sph V a (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ)) (g * p⁻¹)‖
      ≤ Real.exp (t * Real.log c) * (|C₀| * (GlobalTheory.Grow.height (dblSp V) g * GlobalTheory.Grow.height (dblSp V) p⁻¹) ^ A) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = Real.exp (t * Real.log c) * |C₀| * GlobalTheory.Grow.height (dblSp V) p⁻¹ ^ A * GlobalTheory.Grow.height (dblSp V) g ^ A := by
        rw [mul_pow]; ring

end ResidueKilled.Tr
end
end

noncomputable section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.AutomorphicL2Unitary
open PositivityTheory.RgEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ResidueKilled.Tr

theorem ext_mul' {G : Type} [Group G] (K P : Subgroup G) (f : G → ℝ) (hadd : ∀ p ∈ P, ∀ q ∈ P, f (p * q) = f p + f q)
    (h0 : ∀ r ∈ P, r ∈ K → f r = 0) {p k : G} (hp : p ∈ P) (hk : k ∈ K) : ext K P f (p * k) = f p := by
  have h : ∃ k' : K, p * k * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  unfold ext
  rw [dite_eq_left h]
  have hs := h.choose_spec
  have hr : k * (h.choose : G)⁻¹ ∈ K := K.mul_mem hk (K.inv_mem h.choose.2)
  have e : p * k * (h.choose : G)⁻¹ = p * (k * (h.choose : G)⁻¹) := by group
  rw [e] at hs ⊢
  have hrP : k * (h.choose : G)⁻¹ ∈ P := by
    have := P.mul_mem (P.inv_mem hp) hs
    simpa using this
  rw [hadd p hp _ hrP, h0 _ hrP hr, add_zero]

theorem absA_pos (D : D7) (x : (AE D)ˣ) : 0 < absA D x := by
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have h1 := map_mul (absA D) x x⁻¹
  rw [mul_inv_cancel, map_one, h0, zero_mul] at h1
  exact one_ne_zero h1

set_option maxHeartbeats 4000000 in
theorem tTop : TTop := by
  intro hG hT hB hE hP hS hC hSc hDv D V hV a ha hI μ b hμ hb s₁ φ hφ
  have hCM := isCMExt_host D
  have hUn := GlobalTheory.HeckeAdjoint.unramified_host D
  have hHk : GlobalTheory.LFun.IsHecke D.host.F D.host.E μ := hμ
  have hRes := GlobalTheory.LFun.resEtaPow_of_resEta D.host.F D.host.E hCM.2.2.1 μ b hb
  have hgood := hG D.host.F D.host.E D.sp.cm.sig μ b hCM hUn hHk hRes
  obtain ⟨Φ, p, hΓ, hPs, hK, hbd, hlg⟩ := hC D μ V a ha
  obtain ⟨-, -, -, ht2, hlc, -, hKc⟩ := hT D.host.E (AE D) (adCM D.sp.cm.sig μ) hgood (Fin V.rank) (-1)
  have := ht2
  have := hlc
  have hiwa : Iwa ((adCM D.sp.cm.sig μ).uQ (-1) (Set.univ : Set (Fin V.rank))) ((adCM D.sp.cm.sig μ).uK (-1) (Fin V.rank)) := by
    intro y
    obtain ⟨q, k, hk, e⟩ := hI (Φ.symm y * (p : GA D (dblSp V))⁻¹)
    refine ⟨Φ ((q : GA D (dblSp V)) * p), (hPs _).1 (mul_mem q.2 p.2), Φ ((p : GA D (dblSp V))⁻¹ * k * p), (hK k).1 hk, ?_⟩
    have e2 : Φ.symm y = (q : GA D (dblSp V)) * k * p := by rw [← e]; group
    calc y = Φ (Φ.symm y) := (Φ.apply_symm_apply y).symm
      _ = Φ ((q : GA D (dblSp V)) * p * ((p : GA D (dblSp V))⁻¹ * k * p)) := by rw [e2]; congr 1; group
      _ = _ := map_mul Φ _ _
  have hW := hS D.host.F D.host.E D.sp.cm.sig μ b hCM hUn hHk hRes (-1) (Fin V.rank) (by rw [Fintype.card_fin]; exact hV) hiwa
  obtain ⟨-, hparU⟩ := hP D.host.E (AE D) (adCM D.sp.cm.sig μ) hgood (Fin V.rank) (-1) Set.univ
  obtain ⟨hIP', hIH, -⟩ := hparU (by rwa [inf_idem])
  rw [inf_idem] at hIP'
  obtain ⟨-, hmul, -, -, hzero, -⟩ := hB D.host.E (AE D) (adCM D.sp.cm.sig μ) hgood.toGoodL (Fin V.rank ⊕ Fin V.rank)
    (Sum.inl '' (Set.univ : Set (Fin V.rank)))
  set A := adCM D.sp.cm.sig μ with hAdef
  set η : A.U (-1) (Fin V.rank) → ℝ := A.uH (-1) (Set.univ : Set (Fin V.rank)) with hηdef
  set c : ℝ≥0 := absA D (aP V p) with hcdef
  have hc : 0 < c := absA_pos D _
  have hηQ : ∀ y ∈ A.uQ (-1) (Set.univ : Set (Fin V.rank)), ∀ k ∈ A.uK (-1) (Fin V.rank),
      η (y * k) = A.lg (bdet (Sum.inl '' (Set.univ : Set (Fin V.rank))) y.1) := by
    intro y hy k hk
    refine ext_mul' _ _ (fun q : A.U (-1) (Fin V.rank) => A.lg (bdet (Sum.inl '' (Set.univ : Set (Fin V.rank))) q.1)) ?_ ?_ hy hk
    · intro q₁ h₁ q₂ h₂
      show A.lg (bdet _ (q₁.1 * q₂.1)) = _
      rw [hmul q₁.1 h₁ q₂.1 h₂, hgood.lgmul]
    · intro r h₁ h₂
      exact hzero _ h₁ h₂
  have hηP : ∀ q : siegel V, η (Φ q) = Real.log (absA D (aP V q)) := by
    intro q
    have := hηQ (Φ q) ((hPs q).1 q.2) 1 (one_mem _)
    rw [mul_one] at this
    rw [this, hbd q, hlg]
  have hηx : ∀ x : GA D (dblSp V), η (Φ x) = Real.log (hgt V a (x * (p : GA D (dblSp V))⁻¹)) + Real.log c := by
    intro x
    obtain ⟨q, k, hk, e⟩ := hI (x * (p : GA D (dblSp V))⁻¹)
    have e2 : x = (q : GA D (dblSp V)) * p * ((p : GA D (dblSp V))⁻¹ * k * p) := by
      have : x = x * (p : GA D (dblSp V))⁻¹ * p := by group
      rw [this, e]; group
    have h1 : hgt V a (x * (p : GA D (dblSp V))⁻¹) = absA D (aP V q) := by rw [e, hgt_mul V a q hk]
    have h2 : η (Φ x) = Real.log (absA D (aP V (q * p))) := by
      rw [e2, map_mul, hηQ _ ((hPs _).1 (mul_mem q.2 p.2)) _ ((hK k).1 hk), ← Subgroup.coe_mul, hbd (q * p), hlg]
    rw [h1, h2, map_mul, map_mul, NNReal.coe_mul, Real.log_mul (NNReal.coe_pos.2 (absA_pos D _)).ne'
      (NNReal.coe_pos.2 (absA_pos D _)).ne']
  set u : ℂ := s₁ + (V.rank : ℂ) / 2 with hu
  set f : GA D (dblSp V) → ℂ := fun x => φ (x * (p : GA D (dblSp V))⁻¹) * Complex.exp (-u * η (Φ x)) with hf
  obtain ⟨hlaw, hφc, hφK⟩ := (mem_degPS V a).1 hφ
  have hflaw : ∀ q ∈ siegel V, ∀ g, f (q * g) = A.uC (-1) (Fin V.rank) (Φ q) * f g := by
    intro q hq g
    have h1 : φ (q * g * (p : GA D (dblSp V))⁻¹) = μ (aP V ⟨q, hq⟩) * npow (absA D (aP V ⟨q, hq⟩)) u *
        φ (g * (p : GA D (dblSp V))⁻¹) := by
      rw [mul_assoc]; exact hlaw ⟨q, hq⟩ (g * (p : GA D (dblSp V))⁻¹)
    have h2 : η (Φ (q * g)) = η (Φ q) + η (Φ g) := by rw [map_mul]; exact hIH.left _ ((hPs q).1 hq) _
    have h3 := hηP ⟨q, hq⟩
    have h4 : A.uC (-1) (Fin V.rank) (Φ q) = (μ (aP V ⟨q, hq⟩) : ℂ) := by
      show ((A.χ (bdet (Sum.inl '' (Set.univ : Set (Fin V.rank))) (Φ q).1) : Circle) : ℂ) = _
      rw [hbd ⟨q, hq⟩]; rfl
    have e5 : npow (absA D (aP V ⟨q, hq⟩)) u *
        Complex.exp (-u * ((Real.log (absA D (aP V ⟨q, hq⟩)) + η (Φ g) : ℝ) : ℂ)) = Complex.exp (-u * (η (Φ g) : ℂ)) := by
      rw [npow_eq_exp (absA_pos D _), ← Complex.exp_add]; congr 1; push_cast; ring
    simp only [hf]
    rw [h1, h2, h4, show η (Φ q) = Real.log (absA D (aP V ⟨q, hq⟩)) from h3, ← e5]
    ring
  have hfc : Continuous f :=
    (hφc.comp (continuous_id.mul continuous_const)).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (hIH.cont.comp (map_continuous Φ)))))
  have hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : A.uK (-1) (Fin V.rank) => fun x => f (x * Φ.symm k))) := by
    let T : (GA D (dblSp V) → ℂ) →ₗ[ℂ] (GA D (dblSp V) → ℂ) :=
      { toFun := fun ψ x => ψ (x * (p : GA D (dblSp V))⁻¹) * Complex.exp (-u * η (Φ x))
        map_add' := fun ψ ψ' => by funext x; simp [add_mul]
        map_smul' := fun z ψ => by funext x; simp [mul_assoc] }
    have : FiniteDimensional ℂ (kSpan (Khat V a) φ) := hφK
    refine Submodule.finiteDimensional_of_le (S₂ := (kSpan (Khat V a) φ).map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have hk' : (p : GA D (dblSp V)) * Φ.symm k * (p : GA D (dblSp V))⁻¹ ∈ Khat V a := by
      refine (hK _).2 ?_
      have e : (p : GA D (dblSp V))⁻¹ * ((p : GA D (dblSp V)) * Φ.symm k * (p : GA D (dblSp V))⁻¹) * p = Φ.symm k := by group
      rw [e, Φ.apply_symm_apply]; exact k.2
    refine ⟨fun g => φ (g * ((p : GA D (dblSp V)) * Φ.symm k * (p : GA D (dblSp V))⁻¹)),
      Submodule.subset_span ⟨_, hk', rfl⟩, ?_⟩
    funext x
    show φ (x * (p : GA D (dblSp V))⁻¹ * ((p : GA D (dblSp V)) * Φ.symm k * (p : GA D (dblSp V))⁻¹)) *
      Complex.exp (-u * η (Φ x)) = φ (x * Φ.symm k * (p : GA D (dblSp V))⁻¹) * Complex.exp (-u * η (Φ (x * Φ.symm k)))
    have e1 : x * (p : GA D (dblSp V))⁻¹ * ((p : GA D (dblSp V)) * Φ.symm k * (p : GA D (dblSp V))⁻¹) =
        x * Φ.symm k * (p : GA D (dblSp V))⁻¹ := by group
    have e2 : η (Φ (x * Φ.symm k)) = η (Φ x) := by rw [map_mul, Φ.apply_symm_apply]; exact hIH.right _ _ k.2
    rw [e1, e2]
  obtain ⟨Am, H, R, hAd, hAne, hHd, hHc, hHe, hHb⟩ := hSc (GA D (dblSp V)) (A.U (-1) (Fin V.rank)) Φ (GQ (dblSp V))
    (siegel V) (A.uΓ (-1) (Fin V.rank)) (A.uK (-1) (Fin V.rank)) (A.uQ (-1) Set.univ) (A.uC (-1) (Fin V.rank)) η
    (Fintype.card (Fin V.rank) : ℝ) hKc hIP' hIH hΓ hPs hW f hfc hflaw hfin
  have hgrow : ∀ r : ℝ, ∃ (C : ℝ) (N : ℕ), ∀ z : ℂ, ‖z‖ ≤ r → ∀ g,
      ‖H z g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N := by
    intro r
    set A₁ : ℝ := max (R + 1) (max (r + 1) ((V.rank : ℝ) + 1)) with hA₁
    set B₁ : ℝ := min (-R - 1) (min (-r - 1) (-1)) with hB₁
    have a1 := le_max_left (R + 1) (max (r + 1) ((V.rank : ℝ) + 1))
    have a2 := le_max_left (r + 1) ((V.rank : ℝ) + 1)
    have a3 := le_max_right (r + 1) ((V.rank : ℝ) + 1)
    have a4 := le_max_right (R + 1) (max (r + 1) ((V.rank : ℝ) + 1))
    have b1 := min_le_left (-R - 1) (min (-r - 1) (-1))
    have b2 := min_le_left (-r - 1) (-1)
    have b3 := min_le_right (-r - 1) (-1)
    have b4 := min_le_right (-R - 1) (min (-r - 1) (-1))
    obtain ⟨M, hM⟩ := hHb A₁ B₁ (by linarith) (by linarith)
    obtain ⟨C₁, N₁, h₁⟩ := posSum_growth' D V hV a ha hI (p : GA D (dblSp V)) c hc (fun x => η (Φ x)) hηx A₁
      (by linarith)
    obtain ⟨C₂, N₂, h₂⟩ := posSum_growth' D V hV a ha hI (p : GA D (dblSp V)) c hc (fun x => η (Φ x)) hηx
      ((Fintype.card (Fin V.rank) : ℝ) - B₁) (by rw [Fintype.card_fin]; linarith)
    refine ⟨|M| * (|C₁| + |C₂|), N₁ + N₂, fun z hz g => ?_⟩
    have hre := abs_le.1 ((Complex.abs_re_le_norm z).trans hz)
    have h₃ := hM z (by linarith) (by linarith) g
    have q₁ := h₁ g
    have q₂ := h₂ g
    beta_reduce at q₁ q₂
    have hone : (1 : ℝ) ≤ GlobalTheory.Grow.height (dblSp V) g := GlobalTheory.Grow.one_le_height _ g
    have w₁ : GlobalTheory.Grow.height (dblSp V) g ^ N₁ ≤ GlobalTheory.Grow.height (dblSp V) g ^ (N₁ + N₂) :=
      pow_le_pow_right₀ hone (by omega)
    have w₂ : GlobalTheory.Grow.height (dblSp V) g ^ N₂ ≤ GlobalTheory.Grow.height (dblSp V) g ^ (N₁ + N₂) :=
      pow_le_pow_right₀ hone (by omega)
    have w₀ : (0 : ℝ) ≤ GlobalTheory.Grow.height (dblSp V) g ^ N₁ := by positivity
    have w₀' : (0 : ℝ) ≤ GlobalTheory.Grow.height (dblSp V) g ^ N₂ := by positivity
    have r₁ : C₁ * GlobalTheory.Grow.height (dblSp V) g ^ N₁ ≤ |C₁| * GlobalTheory.Grow.height (dblSp V) g ^ (N₁ + N₂) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) w₀).trans (mul_le_mul_of_nonneg_left w₁ (abs_nonneg _))
    have r₂ : C₂ * GlobalTheory.Grow.height (dblSp V) g ^ N₂ ≤ |C₂| * GlobalTheory.Grow.height (dblSp V) g ^ (N₁ + N₂) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) w₀').trans (mul_le_mul_of_nonneg_left w₂ (abs_nonneg _))
    calc ‖H z g‖ ≤ M * _ := h₃
      _ ≤ |M| * _ := mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
      _ ≤ |M| * ((|C₁| + |C₂|) * GlobalTheory.Grow.height (dblSp V) g ^ (N₁ + N₂)) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = _ := by ring
  have hCont := hDv D (dblSp V)
    (fun z g => GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (fun x => Complex.exp (z * η (Φ x)) * f x) g) H Am R hAd
    hAne hHd hHc hHe hgrow
  have hflat := GlobalTheory.T.continuesWithModerateGrowth_shift_translate_pow D (dblSp V) _ (fun s g => GlobalTheory.Eis.eis V (flat V a φ s₁ s) g) (p : GA D (dblSp V)) c s₁
    ((V.rank : ℂ) / 2) hc (fun s g => ?_) hCont
  · exact ⟨⟨GlobalTheory.Eis.ContModel.isEisFamily_flat ha hμ hφ, hflat.1⟩, hflat.2⟩
  show GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (flat V a φ s₁ s) g = npow c (s₁ - s) *
    GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (fun x => Complex.exp ((s + (V.rank : ℂ) / 2) * η (Φ x)) * f x)
      (g * (p : GA D (dblSp V)))
  have e4 : GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (fun x => Complex.exp ((s + (V.rank : ℂ) / 2) * η (Φ x)) * f x)
      (g * (p : GA D (dblSp V))) = npow c (s - s₁) * GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (flat V a φ s₁ s) g := by
    rw [← GlobalTheory.Eis.cosetSum_mul_right, ← GlobalTheory.Eis.cosetSum_smul]
    congr 1
    funext x
    change Complex.exp ((s + (V.rank : ℂ) / 2) * η (Φ (x * (p : GA D (dblSp V))))) *
      (φ (x * (p : GA D (dblSp V)) * (p : GA D (dblSp V))⁻¹) *
        Complex.exp (-u * η (Φ (x * (p : GA D (dblSp V)))))) =
      npow c (s - s₁) * (φ x * npow (hgt V a x) (s - s₁))
    have hh := hηx (x * (p : GA D (dblSp V)))
    rw [show x * (p : GA D (dblSp V)) * (p : GA D (dblSp V))⁻¹ = x by group] at hh
    rw [hh, npow_eq_exp hc, npow_eq_exp (hgtH_pos _), show x * (p : GA D (dblSp V)) * (p : GA D (dblSp V))⁻¹ = x by group]
    calc _ = φ x * Complex.exp ((s + (V.rank : ℂ) / 2) * ((Real.log (hgt V a x) + Real.log c : ℝ) : ℂ) +
          -u * ((Real.log (hgt V a x) + Real.log c : ℝ) : ℂ)) := by rw [Complex.exp_add]; ring
      _ = φ x * Complex.exp ((Real.log c : ℂ) * (s - s₁) + (Real.log (hgt V a x) : ℂ) * (s - s₁)) := by
          congr 2; rw [hu]; push_cast; ring
      _ = _ := by rw [Complex.exp_add]; ring
  rw [e4, ← mul_assoc, ← npow_add hc, show s₁ - s + (s - s₁) = 0 by ring]
  simp [npow]

end ResidueKilled.Tr
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisibilityStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisibilityStatement
noncomputable section

open scoped Topology
open Filter Set Metric GlobalTheory.Cont

namespace GlobalTheory.CompanionTheory.DivMult

theorem exists_factor {A : ℂ → ℂ} (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (s₀ : ℂ) :
    ∃ (k : ℕ) (u : ℂ → ℂ) (r M : ℝ), 0 < r ∧ DifferentiableOn ℂ u (ball s₀ r) ∧ (∀ s ∈ ball s₀ r, u s ≠ 0) ∧
      (∀ s ∈ ball s₀ r, A s = (s - s₀) ^ k * u s) ∧ ∀ s ∈ ball s₀ r, ‖(u s)⁻¹‖ ≤ M := by
  have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
  have hnz : ¬∀ᶠ z in 𝓝 s₀, A z = 0 := by
    intro hev
    obtain ⟨w, hw⟩ := hne
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s₀)
      (hev.mono fun z hz => by simp [hz])
    exact hw (by simpa using this (mem_univ w))
  obtain ⟨k, g, hg, hg0, hev⟩ := (hA.analyticAt s₀).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hpos : 0 < ‖g s₀‖ := norm_pos_iff.mpr hg0
  have hcont : ∀ᶠ z in 𝓝 s₀, ‖g z - g s₀‖ < ‖g s₀‖ / 2 := by
    have h2 : ball (g s₀) (‖g s₀‖ / 2) ∈ 𝓝 (g s₀) := ball_mem_nhds _ (by positivity)
    filter_upwards [hg.continuousAt h2] with z hz
    simpa [dist_eq_norm] using hz
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hev.and (hcont.and hg.eventually_analyticAt))
  refine ⟨k, g, r, 2 / ‖g s₀‖, hr, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hball z hz).2.2.differentiableAt.differentiableWithinAt
  · intro z hz h0
    have h1 := (hball z hz).2.1
    rw [h0, zero_sub, norm_neg] at h1
    linarith
  · intro z hz
    simpa [smul_eq_mul] using (hball z hz).1
  · intro z hz
    have h1 := (hball z hz).2.1
    have hlow : ‖g s₀‖ / 2 ≤ ‖g z‖ := by
      have h3 := norm_sub_norm_le (g s₀) (g z)
      rw [norm_sub_rev] at h3
      linarith
    calc ‖(g z)⁻¹‖ = ‖g z‖⁻¹ := norm_inv _
      _ ≤ (‖g s₀‖ / 2)⁻¹ := inv_anti₀ (by positivity) hlow
      _ = 2 / ‖g s₀‖ := inv_div _ _

def glue (h F A : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ := if R < z.re then h z else F z / A z

variable {h F A : ℂ → ℂ} {R : ℝ}

theorem glue_eq (he : ∀ z : ℂ, R < z.re → F z = A z * h z) {z : ℂ} (hz : A z ≠ 0) : glue h F A R z = F z / A z := by
  unfold glue
  split_ifs with c
  · rw [he z c, mul_div_cancel_left₀ _ hz]
  · rfl

theorem glue_eventuallyEq (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (he : ∀ z : ℂ, R < z.re → F z = A z * h z) (s : ℂ) :
    glue h F A R =ᶠ[𝓝[≠] s] fun z => F z / A z := by
  have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
  rcases (hA.analyticAt s).eventually_eq_zero_or_eventually_ne_zero with hev | hev
  · exfalso
    obtain ⟨w, hw⟩ := hne
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s)
      (hev.mono fun z hz => by simp [hz])
    exact hw (by simpa using this (mem_univ w))
  · filter_upwards [hev] with z hz using glue_eq he hz

theorem isMerExt_glue (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (hF : Differentiable ℂ F)
    (he : ∀ z : ℂ, R < z.re → F z = A z * h z) : IsMerExt h univ (glue h F A R) := by
  refine ⟨isRightDomain_univ, fun s _ => ?_, ⟨R, fun z hz => ?_⟩⟩
  · have hm : MeromorphicAt (fun z => F z / A z) s :=
      (hF.analyticAt s).meromorphicAt.div (hA.analyticAt s).meromorphicAt
    exact hm.congr (glue_eventuallyEq hA hne he s).symm
  · have hz' : R < z.re := hz
    simp [glue, hz']

theorem cont_eq_div (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (hF : Differentiable ℂ F)
    (he : ∀ z : ℂ, R < z.re → F z = A z * h z) {s : ℂ} (hs : A s ≠ 0) : cont h s = F s / A s := by
  have hM := isMerExt_glue hA hne hF he
  have hE : IsExtAt h s (glue h F A R) := hM.isExtAt (mem_univ s)
  have hcont : ContinuousAt (fun z => F z / A z) s :=
    hF.continuous.continuousAt.div hA.continuous.continuousAt hs
  have ht : Tendsto (glue h F A R) (𝓝[≠] s) (𝓝 (F s / A s)) :=
    Tendsto.congr' (glue_eventuallyEq hA hne he s).symm (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  exact (hE.holValueAt_iff.mpr ht).valueAt.cont_eq

theorem div_multiplier : ResidueKilled.Tr.Div := by
  unfold ResidueKilled.Tr.Div
  intro D T e H A R hA hne hH hHc hmul hbd
  unfold GlobalTheory.EisCont.ContMod GlobalTheory.Cont.Continues
  refine ⟨fun g => ⟨_, isMerExt_glue hA hne (hH g) (fun z hz => hmul z hz g)⟩, fun s₀ => ?_⟩
  obtain ⟨k, u, r, M, hr, hu, hu0, hfac, hM⟩ := exists_factor hA hne s₀
  obtain ⟨C, N, hCN⟩ := hbd (‖s₀‖ + r)
  have hu1 : ContinuousOn (fun x : ℂ × _ => u x.1) (ball s₀ r ×ˢ (univ : Set (Formalism.L2.Theta.GA D T))) :=
    hu.continuousOn.comp continuous_fst.continuousOn (fun x hx => hx.1)
  unfold GlobalTheory.EisCont.RegAt
  refine ⟨k, r, fun s g => H s g * (u s)⁻¹, hr, ?_, ?_, ?_, C * M, N, ?_⟩
  · intro s hs hss g
    have hAs : A s = (s - s₀) ^ k * u s := hfac s hs
    have hus : u s ≠ 0 := hu0 s hs
    have hpow : (s - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hss)
    have hA0 : A s ≠ 0 := by rw [hAs]; exact mul_ne_zero hpow hus
    show H s g * (u s)⁻¹ = (s - s₀) ^ k * cont (fun z => e z g) s
    rw [cont_eq_div hA hne (hH g) (fun z hz => hmul z hz g) hA0, hAs]
    field_simp
    try ring
  · intro g
    exact (hH g).differentiableOn.mul (hu.inv hu0)
  · exact hHc.continuousOn.mul (hu1.inv₀ (fun x hx => hu0 x.1 hx.1))
  · intro s hs g
    have hs1 : ‖s - s₀‖ < r := by simpa [dist_eq_norm] using hs
    have hs2 := norm_sub_norm_le s s₀
    have hsr : ‖s‖ ≤ ‖s₀‖ + r := by linarith
    have hH1 := hCN s hsr g
    have hM1 := hM s hs
    show ‖H s g * (u s)⁻¹‖ ≤ C * M * GlobalTheory.Grow.height T g ^ N
    calc ‖H s g * (u s)⁻¹‖ = ‖H s g‖ * ‖(u s)⁻¹‖ := norm_mul _ _
      _ ≤ (C * GlobalTheory.Grow.height T g ^ N) * M := mul_le_mul hH1 hM1 (norm_nonneg _) (le_trans (norm_nonneg _) hH1)
      _ = C * M * GlobalTheory.Grow.height T g ^ N := by ring

end GlobalTheory.CompanionTheory.DivMult

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisibilityStatementStatement
open ResidueKilled.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisibility_statement : Div := by
  first | exact @GlobalTheory.CompanionTheory.DivMult.div_multiplier | exact GlobalTheory.CompanionTheory.DivMult.div_multiplier | (intros; apply GlobalTheory.CompanionTheory.DivMult.div_multiplier <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.SiegelEisensteinContinuationOf
namespace PositivityTheory.RgEis.Sp

open ResidueKilled.Tr

theorem siegelEisensteinContinuation_of (hD : Dict) (hI : DictInf) (hL : SecLaw) (hW : WallLaw) (hG : CMGood)
    (hT : GrpTop) (hB : BdetLaw) (hE : ExtLaw) (hP : ParLaw) (hS : SgAll) : GlobalTheory.Published.SiegelEisensteinContinuation :=
  ResidueKilled.Tr.tTop hG hT hB hE hP hS (GlobalTheory.T.chart_section_exists hD hI GlobalTheory.T.standard_section_exists) (GlobalTheory.T.scalar_section_exists hL hW) GlobalTheory.T.divisibility_statement

end PositivityTheory.RgEis.Sp
end

namespace PositivityTheory.RgEis.Sp.Hd

open PositivityTheory.RgEis.Hd

theorem siegelEisensteinContinuation : GlobalTheory.Published.SiegelEisensteinContinuation :=
  Sp.siegelEisensteinContinuation_of dict dictInf secLaw (wallLaw_of secLaw) (cmGood_of stdGood dict dictInf) grpTop bdetLaw
    extLaw (parLaw_of bdetLaw extLaw grpTop) PositivityTheory.RgEis.Hd.sgAll

end PositivityTheory.RgEis.Sp.Hd
