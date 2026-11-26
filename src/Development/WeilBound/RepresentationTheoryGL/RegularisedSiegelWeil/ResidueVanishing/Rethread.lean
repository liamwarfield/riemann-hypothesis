module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Leaves
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Eis
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Kplug

def K0 : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ omh →
    ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 →
    ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → ∀ f, IsThetaFunO ψ (dblSp A) B f → IsKFinVec omh (Khat A a) f →
      swSec A B omh ν 𝓨 f ∈ degPS A a χ⁻¹ (sZero A B)

def K1 : Prop :=
  ∀ (D : D7) (V : HSp D) (Φ : ℂ → GA D (dblSp V) → ℂ), EisContinues V Φ → (∀ s₀, ∃ k, EisRegularAt V Φ s₀ k) →
    (∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) {z : ℂ | (V.rank : ℝ) / 2 < z.re}) → ∀ s₀ : ℂ,
    ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → GA D (dblSp V) → ℂ) (ε : ℝ),
      IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧ (∀ g, DifferentiableOn ℂ (E · g) U) ∧
      ContinuousOn (fun y : ℂ × GA D (dblSp V) => E y.1 y.2) (U ×ˢ Set.univ) ∧
      (∀ z ∈ U, ∀ γ ∈ GQ (dblSp V), ∀ g, E z (γ * g) = E z g) ∧
      (∀ z : ℂ, (V.rank : ℝ) / 2 < z.re → ∀ g, E z g = d.eval z * eisSer V Φ g z) ∧ IsRad U d s₀ ε

def K2 : Prop :=
  ∀ (h e : ℂ → ℂ) (U : Set ℂ) (d : Polynomial ℂ) (s₀ : ℂ) (ε σ : ℝ), IsOpen U → IsRightDomain U → DifferentiableOn ℂ e U →
    d ≠ 0 → IsRad U d s₀ ε → (∀ z : ℂ, σ < z.re → e z = d.eval z * h z) →
    (∀ k : ℕ, 2 ≤ k → (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (e z / d.eval z) = 0) →
    CoeffAt h s₀ (-1) ((2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(s₀, ε), (z - s₀) ^ (1 - 1) * (e z / d.eval z)) ∧
      PoleLE h s₀ 1

def SimplePoleRescaling : Prop :=
  ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → CoeffAt h s₀ (-1) c → PoleLE h s₀ 1 →
    (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → CoeffAt h' s₀ (-1) c

def ContinuousInvariantCoefficients : Prop :=
  ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0) (φ : G D n → ℂ) (s₀ : ℂ) (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G D n → ℂ) (σ : ℝ),
    IsCont H φ s₀ U d E σ → ∀ ε, IsRad U d s₀ ε → ∀ k, Continuous (cf d E s₀ ε k) ∧ LeftInv (GF D n) (cf d E s₀ ε k)

def KillingPolyConst : Prop :=
  ∀ (D : D7) (A : HSp D) (μ : D.host.E), GlobalTheory.StdUnn.IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ →
    ∀ (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ p : siegel A, IsConj A a κ p →
      IsHt (hgtStd A a κ p) ∧ HasLevel (hgtStd A a κ p)

def ContinuationThroughChart : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ omh →
    ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ →
    ∀ μ : D.host.E, GlobalTheory.StdUnn.IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ →
    ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS →
    ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ →
    ∀ (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ p : siegel A, IsConj A a κ p →
    ∀ f, IsThetaFunO ψ (dblSp A) B f → IsKFinVec omh (Khat A a) f →
    ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f) →
    ∀ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → GA D (dblSp A) → ℂ),
      IsOpen U → IsRightDomain U → sZero A B ∈ U → d ≠ 0 → (∀ g, DifferentiableOn ℂ (E · g) U) →
      ContinuousOn (fun y : ℂ × GA D (dblSp A) => E y.1 y.2) (U ×ˢ Set.univ) →
      (∀ z ∈ U, ∀ γ ∈ GQ (dblSp A), ∀ g, E z (γ * g) = E z g) →
      (∀ z : ℂ, (A.rank : ℝ) / 2 < z.re → ∀ g,
        E z g = d.eval z * eisSer A (flat A a (swSec A B omh ν 𝓨 f) (sZero A B)) g z) →
      Continuous (fun g => (omS g Φ).1 0) ∧
      IsCont (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) U d
        (fun z g => npow (absA D (aP A p)) (z - sZero A B) * E z (κ.symm g * ((p : GA D (dblSp A))⁻¹))) ((A.rank : ℝ) / 2) ∧
      ∀ (z : ℂ), (A.rank : ℝ) / 2 < z.re → ∀ g : GA D (dblSp A),
        eisSer A (flat A a (swSec A B omh ν 𝓨 f) (sZero A B)) g z =
          npow (absA D (aP A p)) (sZero A B - z) * eisS (fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z) (κ (g * p))

def K4 : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)),
    GlobalTheory.Core.Rk.Exh.Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D W →* Module.End ℂ (WO (dblSp A) W → ℂ)),
    IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (ν : Measure (WO A W)) (𝓨 : Set (WO A W)), IsCovolOne (ratL W A) ν 𝓨 →
    ∀ μ : D.host.E, GlobalTheory.StdUnn.IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ →
    ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ W.rank A.rank), IsTransport ψ θ A W ν 𝓨 omh κ omS →
    ∀ p : siegel A, ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) →
    GlobalTheory.Core.Rk.Exh.Kills ψ χ omh m u → ∀ F : G D A.rank → ℂ, Continuous F → LeftInv (GF D A.rank) F →
    (∀ (X : Type) [MeasurableSpace X] (νX : Measure X) [IsFiniteMeasure νX] (c : X → G D A.rank), Measurable c →
      IsCompact (closure (Set.range c)) → ∀ w : X → ℂ, Integrable w νX →
      (∀ (Ψ : schwartzA θ W.rank A.rank) (h : GA D W), ∫ x, theta omS Ψ (c x) h * w x ∂νX = 0) →
      ∫ x, F (c x) * w x ∂νX = 0) →
    dblInt A χ⁻¹ m (fun g => F (κ (g * p))) (fun g => conj (u g)) (fun g => conj (u g)) = 0

section Target

open scoped ComplexConjugate Matrix NNReal
open IsDedekindDomain NumberField GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta)
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

def ResidueVanishing : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)),
    Defin θ A cA a → (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) →
    ∀ (B W : HSp D) (t : ℕ) (_ : HypDec B W t), HSpace.SigOK B → HSpace.SigOK W → 0 < W.rank → 0 < t →
    A.rank = W.rank + t → W.rank + 2 < 2 * t → W.rank < t →
    ∀ (χ : (AE D)ˣ →* Circle) (omB : WRep (dblSp A) B) (omW : WRep (dblSp A) W),
    IsWeilDatumO ψ (dblSp A) B 1 χ omB → IsWeilDatumO ψ (dblSp A) W 1 χ omW → ∀ ν 𝓕, IsCovolOne (ratL B A) ν 𝓕 →
    ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) →
    Kills ψ χ omW m u → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsKFinVec omB (Khat A a) φ →
    ∃ E₁, GlobalTheory.Eis.EisCoeffAt A (flat A a (swSec A B omB ν 𝓕 φ) (sZero A B)) (sZero A B) (-1) E₁ ∧
      GlobalTheory.Eis.dblInt A χ⁻¹ m E₁ (fun g => conj (u g)) (fun g => conj (u g)) = 0

end Target

end PositivityTheory.Rg.Rsw.Kplug

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.ContinuousInvariantCoefficients
noncomputable section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PositivityTheory.Rg.Rsw.Kplug

set_option maxHeartbeats 1000000 in
theorem continuation_through_chart : ContinuationThroughChart := by
  intro D ψ A B χ omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam a ha p hp f hf hK Φ hΦ U d E hU hR hs hd hhol hc hi he
  obtain ⟨h0, hflat, hact⟩ := GlobalTheory.T.doubledFlatSection_eq_translate_standardSection D ψ A B χ omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam a p f hf Φ hΦ
  have hIw := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  have hmem := GlobalTheory.SwSecMem.swSec_mem_degPS GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ omh hW ν 𝓨 hν f hf a hK
  have hχ := GlobalTheory.T.isHeckeChar_restrictionEta_inv D χ B.rank hW.hecT hW.resT
  have hP' := GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ
  have hG' := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D A μ hμ κ hκ
  obtain ⟨hκc, hκc'⟩ := GlobalTheory.T.continuous_standardUnitaryChart_and_symm D A μ hμ κ hκ
  have hr : 0 < absA D (aP A p) := hom_pos _ _
  have hfs : ∀ z, fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z = sect omS (hgtStd A a κ p) Φ z := fun z => by
    funext g; simp only [fam, sect, h0]
  have hback : ∀ g : G D A.rank, κ (κ.symm g * (p : GA D (dblSp A))⁻¹ * p) = g := fun g => by simp
  have hone : ∀ z : ℂ, npow (absA D (aP A p)) (z - sZero A B) * npow (absA D (aP A p)) (sZero A B - z) = 1 := fun z => by
    rw [← npow_add hr]; simp
  have hsect : ∀ z g, sect omS (hgtStd A a κ p) Φ z g = npow (absA D (aP A p)) (z - sZero A B) *
      flat A a (swSec A B omh ν 𝓨 f) (sZero A B) z (κ.symm g * (p : GA D (dblSp A))⁻¹) := fun z g => by
    rw [hflat, hback, ← mul_assoc, hone, one_mul]
  have hL : ∀ z, LeftInv (P D A.rank ⊓ GF D A.rank) (sect omS (hgtStd A a κ p) Φ z) := fun z q hq g => by
    rw [hsect, hsect, map_mul, mul_assoc (κ.symm q)]
    congr 1
    exact GlobalTheory.Eis.leftInv_of_mem hχ.1 (GlobalTheory.Eis.flat_mem hIw hmem z) _
      ⟨(hP' _).2 (by simpa using hq.1), (hG' _).2 (by simpa using hq.2)⟩ _
  have h3 : ∀ (z : ℂ) (g : GA D (dblSp A)), GlobalTheory.Eis.eisSer A (flat A a (swSec A B omh ν 𝓨 f) (sZero A B)) g z =
      npow (absA D (aP A p)) (sZero A B - z) * eisS (fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z) (κ (g * p)) :=
    fun z g => by
      rw [hfs]
      exact ((GlobalTheory.T.cosetSum_along_mulEquiv_subgroups _ _ κ (siegel A) (GQ (dblSp A)) (P D A.rank) (GF D A.rank) hP' hG' _ _ _ _ (fun g => hflat z g) (hL z)).2 g).2
  refine ⟨?_, ⟨hU, hR, hs, hd, fun g => ?_, ?_, fun z hz γ hγ g => ?_, fun z hz g => ?_⟩, fun z _ g => h3 z g⟩
  · have e : (fun g => (omS g Φ).1 0) = fun g => swSec A B omh ν 𝓨 f (κ.symm g * (p : GA D (dblSp A))⁻¹) := by
      funext g
      have := hsect (sZero A B) g
      simpa [sect, h0, flatH_self] using this
    rw [e]
    exact (hmem.2.1 : Continuous _).comp (hκc'.mul continuous_const)
  · refine DifferentiableOn.mul ?_ (hhol _)
    simp only [npow_eq_exp hr]
    fun_prop
  · refine ContinuousOn.mul ?_ (hc.comp (f := fun y : ℂ × G D A.rank => (y.1, κ.symm y.2 * (p : GA D (dblSp A))⁻¹))
      (continuous_fst.prodMk ((hκc'.comp continuous_snd).mul continuous_const)).continuousOn fun y hy => ⟨hy.1, trivial⟩)
    simp only [npow_eq_exp hr]
    fun_prop
  · rw [map_mul, mul_assoc (κ.symm γ), hi z hz _ ((hG' _).2 (by simpa using hγ))]
  · rw [he z hz, h3, hback]
    linear_combination (d.eval z * eisS (fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z) g) * hone z

theorem mem_section_space : K0 := fun D ψ A B χ om hW ν 𝓨 hν a _ f hf hK =>
  GlobalTheory.SwSecMem.swSec_mem_degPS GlobalTheory.weilRepresentationUnitaryPair D ψ A B χ om hW ν 𝓨 hν f hf a hK

theorem continuation_chart_defined : KillingPolyConst := by
  intro D A μ hμ κ hκ a ha p hp
  have hI := GlobalTheory.Eis.isIwasawa_Khat (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha)
  have hIw := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  obtain ⟨-, hκc'⟩ := GlobalTheory.T.continuous_standardUnitaryChart_and_symm D A μ hμ κ hκ
  haveI := t2Space_adeleRing' (F := D.host.F)
  have h1 : Continuous (hgt A a) := hIw.continuous_hgtH continuous_absE (isCompact_Khat A a)
  refine ⟨⟨(h1.comp (hκc'.mul continuous_const)).mul continuous_const, fun g => mul_pos (hgtH_pos _) (hom_pos _ _),
    fun q hq α hα g => ?_⟩, ?_⟩
  · have hq' : κ.symm q ∈ siegel A := (GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ (κ.symm q)).2 (by simpa using hq)
    have hdet : aP A ⟨κ.symm q, hq'⟩ = Matrix.GeneralLinearGroup.det α :=
      GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq D A μ hμ κ hκ ⟨κ.symm q, hq'⟩ α (by simpa using hα)
    have e : hgt A a (κ.symm q * (κ.symm g * (p : GA D (dblSp A))⁻¹)) =
        absA D (aP A ⟨κ.symm q, hq'⟩) * hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹) := hI.iwAbs_left ⟨κ.symm q, hq'⟩ _
    simp only [hgtStd]
    rw [map_mul, mul_assoc (κ.symm q), e, hdet, mul_assoc]
  · haveI : Submodule.IsFullLattice D.host.E (stdLattice D.host.E (A.rank + A.rank)) := isLattice_stdLattice
    refine ⟨levelOpen D.sp.cm.sig (Jst D A.rank) (stdLattice D.host.E (A.rank + A.rank)), isOpen_levelOpen _ _ _,
      fun k hk hf g => ?_⟩
    have hkK : k ∈ K D A.rank := mem_levelAll.2 ⟨mem_levelOpen.1 hk, fun w => by
      rw [mem_finPts_iff_forall.1 hf w]; exact one_mem _⟩
    have hk' : (p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
      rw [hp]; simpa [mul_assoc] using hkK
    have e : hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹ * ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹)) =
        hgt A a (κ.symm g * (p : GA D (dblSp A))⁻¹) := hI.iwAbs_right _ hk'
    simp only [hgtStd]
    rw [← e]; simp [mul_assoc]

theorem simple_pole_rescaling : SimplePoleRescaling := by
  intro h h' s₀ c r σ hr hc hp e
  have ha : AnalyticOnNhd ℂ (fun s => npow r (s₀ - s)) (rightOf (s₀.re - 1)) := by
    intro s _
    rw [funext fun s => npow_eq_exp hr (s₀ - s)]
    fun_prop
  have hg := holValueAt_self ha (s₀ := s₀) (by linarith)
  have h1 : npow r (s₀ - s₀) = 1 := by simp
  have hm := (hp.mul_hol (by simpa using hc) hg).2
  simp only [h1, mul_one] at hm
  exact CoeffAt.congr (by simpa using hm) ⟨σ, fun s hs => by rw [e s hs, mul_comm]⟩

theorem continuous_invariant_coefficients : ContinuousInvariantCoefficients := by
  intro D n H φ s₀ U d E σ hC ε hε k
  have hm : ∀ x : ℝ, circleMap s₀ ε x ∈ Metric.closedBall s₀ ε := fun x => circleMap_mem_closedBall s₀ hε.1.le x
  have hne : ∀ x : ℝ, d.eval (circleMap s₀ ε x) ≠ 0 := fun x => hε.2.2 _ (hm x) (circleMap_ne_center hε.1.ne')
  refine ⟨continuous_const.mul ?_, fun γ hγ g => ?_⟩
  · have hE : Continuous fun y : G D n × ℝ => E (circleMap s₀ ε y.2) y.1 :=
      hC.cont.comp_continuous (f := fun y : G D n × ℝ => (circleMap s₀ ε y.2, y.1))
        (((continuous_circleMap s₀ ε).comp continuous_snd).prodMk continuous_fst) fun y => ⟨hε.2.1 (hm y.2), trivial⟩
    have hc : Continuous fun y : G D n × ℝ => circleMap s₀ ε y.2 := (continuous_circleMap s₀ ε).comp continuous_snd
    simp only [circleIntegral, deriv_circleMap]
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun (g : G D n) (x : ℝ) => (circleMap 0 ε x * Complex.I) •
        ((circleMap s₀ ε x - s₀) ^ (k - 1) * (E (circleMap s₀ ε x) g / d.eval (circleMap s₀ ε x)))) ?_ _ _
    exact (((continuous_circleMap 0 ε).comp continuous_snd).mul continuous_const).smul
      (((hc.sub continuous_const).pow _).mul (hE.div (d.continuous.comp hc) fun y => hne y.2))
  · simp only [cf, circleIntegral, hC.inv _ (hε.2.1 (hm _)) γ hγ g]

theorem theta_kernel_identity (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (A W : HSp D) (χ : (AE D)ˣ →* Circle)
    (omh : GA D (dblSp A) × GA D W →* Module.End ℂ (WO (dblSp A) W → ℂ)) (hW : IsWeilDatumO ψ (dblSp A) W 1 χ omh)
    (ν : Measure (WO A W)) (𝓨 : Set (WO A W)) (hν : IsCovolOne (ratL W A) ν 𝓨) (κ : GA D (dblSp A) ≃* G D A.rank)
    (omS : G D A.rank →* Module.End ℂ (schwartzA θ W.rank A.rank)) (hT : IsTransport ψ θ A W ν 𝓨 omh κ omS)
    (p : GA D (dblSp A)) (Ψ : schwartzA θ W.rank A.rank) :
    ∃ f, IsThetaFunO ψ (dblSp A) W f ∧ ∀ g h, theta omS Ψ (κ (g * p)) h = thetaKO omh g h f := by
  obtain ⟨f, hf, e⟩ := (GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hW.std θ hθ A W ν 𝓨 hν).2.1 Ψ.1 Ψ.2
  refine ⟨omh (p, 1) f, hW.om_pres _ f hf, fun g h => ?_⟩
  rw [theta, hT (g * p) f hf Ψ e.symm, ← GlobalTheory.T.thetaKernel_eq_tsum_schrodingerFunction D ψ A W χ omh hW ν 𝓨 hν f hf (g * p) h]
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

end PositivityTheory.Rg.Rsw.Kplug

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Development
section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.ThetaContinuation
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Eis
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Kplug

theorem dblInt_eq_fd {D : D7} (A : HSp D) {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ) (m : Measure (GA D A))
    [m.IsHaarMeasure] {E : GA D (dblSp A) → ℂ} {f₁ f₂ : GA D A → ℂ} (hE : Continuous E)
    (hEi : LeftInv (GQ (dblSp A)) E) (h₁ : Continuous f₁) (h₁i : LeftInv (GQ A) f₁) (h₂ : Continuous f₂)
    (h₂i : LeftInv (GQ A) f₂) {X K : Set (GA D A)} (hX : IsFundamentalDomain (GQ A) X m) (hK : IsCompact K)
    (hXK : X ⊆ K) :
    dblInt A μ m E f₁ f₂ = ∫ g in X ×ˢ X, dblIntegrand A μ E f₁ f₂ g ∂m.prod m := by
  have hi := leftInv_dblIntegrand hμ hEi h₁i h₂i
  have hc := continuous_dblIntegrand hμ hE h₁ h₂
  have hint : IntegrableOn (dblIntegrand A μ E f₁ f₂) (X ×ˢ X) (m.prod m) :=
    (hc.continuousOn.integrableOn_compact (hK.prod hK)).mono_set (Set.prod_mono hXK hXK)
  exact (((dblConv_iff hi hc.measurable hX).2 hint).dblInt_eq hX).2

theorem theta_continuation : K4 := by
  intro D ψ θ A cA a hA W χ omh hW ν 𝓨 hν μ hμ κ hκ omS hT p m hm u hu hui hKi F hF hFi hX
  obtain ⟨-, X, K, hXm, hXf, hKc, hXK⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hA.sig hA.pos m hm
  have hχ := (GlobalTheory.T.isHeckeChar_restrictionEta_inv D χ W.rank hW.hecT hW.resT).1
  obtain ⟨hκc, -⟩ := GlobalTheory.T.continuous_standardUnitaryChart_and_symm D A μ hμ κ hκ
  have hG' := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D A μ hμ κ hκ
  have hcu : Continuous fun g => conj (u g) := Complex.continuous_conj.comp hu
  have hcui : LeftInv (GQ A) fun g => conj (u g) := fun γ hγ g => by simp only [hui γ hγ g]
  set w : GA D A × GA D A → ℂ := dblIntegrand A χ⁻¹ (fun _ => 1) (fun g => conj (u g)) (fun g => conj (u g)) with hw_def
  have hw : Continuous w := continuous_dblIntegrand hχ continuous_const hcu hcu
  have hsplit : ∀ (E : GA D (dblSp A) → ℂ) x,
      dblIntegrand A χ⁻¹ E (fun g => conj (u g)) (fun g => conj (u g)) x = E (io A x) * w x := fun E x => by
    simp only [hw_def, dblIntegrand]; ring
  classical
  let c : GA D A × GA D A → G D A.rank := fun x => if x ∈ K ×ˢ K then κ (io A x * p) else 1
  have hKK : IsCompact (K ×ˢ K) := hKc.prod hKc
  have hXX : X ×ˢ X ⊆ K ×ˢ K := Set.prod_mono hXK hXK
  have hcK : ∀ x ∈ X ×ˢ X, c x = κ (io A x * p) := fun x hx => if_pos (hXX hx)
  have hc0 : Continuous fun x : GA D A × GA D A => κ (io A x * p) :=
    hκc.comp ((continuous_io A).mul continuous_const)
  have hcm : Measurable c := Measurable.ite hKK.isClosed.measurableSet hc0.measurable measurable_const
  have hcr : IsCompact (closure (Set.range c)) := by
    refine ((hKK.image hc0).union (isCompact_singleton (x := (1 : G D A.rank)))).closure_of_subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases h : x ∈ K ×ˢ K
    · exact Or.inl ⟨x, h, (if_pos h).symm⟩
    · exact Or.inr (if_neg h)
  have : IsFiniteMeasure ((m.prod m).restrict (X ×ˢ X)) :=
    isFiniteMeasure_restrict.2 ((measure_mono hXX).trans_lt hKK.measure_lt_top).ne
  have hwi : Integrable w ((m.prod m).restrict (X ×ˢ X)) :=
    (hw.continuousOn.integrableOn_compact hKK).mono_set hXX
  have hXXm : MeasurableSet (X ×ˢ X) := hXm.prod hXm
  have hE : Continuous fun g : GA D (dblSp A) => F (κ (g * p)) :=
    hF.comp (hκc.comp (continuous_id.mul continuous_const))
  have hEi : LeftInv (GQ (dblSp A)) fun g => F (κ (g * p)) := fun γ hγ g => by
    simp only [mul_assoc, map_mul]
    exact hFi _ ((hG' γ).1 hγ) _
  have key := hX (GA D A × GA D A) ((m.prod m).restrict (X ×ˢ X)) c hcm hcr w hwi ?_
  · rw [dblInt_eq_fd A hχ m hE hEi hcu hcui hcu hcui hXf hKc hXK, ← key]
    refine setIntegral_congr_fun hXXm fun x hx => ?_
    simp only [hsplit, hcK x hx]
  · intro Ψ h
    obtain ⟨f, hf, he⟩ := theta_kernel_identity D ψ θ hA.inf A W χ omh hW ν 𝓨 hν κ omS hT p Ψ
    have hk := hKi f hf h
    have hkc : Continuous fun g => thetaKO omh g h f := (hW.om_cont f hf 0).comp (Continuous.prodMk_left h)
    have hki : LeftInv (GQ (dblSp A)) fun g => thetaKO omh g h f := fun γ hγ g =>
      GlobalTheory.Core.Rk.Aniso.thetaKernel_rationalSource_invariant hW hf hγ g h
    rw [dblInt_eq_fd A hχ m hkc hki hcu hcui hcu hcui hXf hKc hXK] at hk
    rw [← hk]
    refine setIntegral_congr_fun hXXm fun x hx => ?_
    simp only [hsplit, hcK x hx, he]

end PositivityTheory.Rg.Rsw.Kplug

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Assembly
noncomputable section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PositivityTheory.Rg.Rsw.Kplug

set_option maxHeartbeats 1000000 in
theorem residue_vanishes_of_siegel_eisenstein : K0 → K1 → K2 → SimplePoleRescaling → ContinuousInvariantCoefficients → KillingPolyConst → ContinuationThroughChart → K4 →
    GlobalTheory.Published.SiegelEisensteinContinuation → PositivityTheory.Rg.Rsw.ResCore → ResidueVanishing := by
  intro k0 k1 k2 k2b k2c k3a k3b k4 hP hC D ψ θ A cA a hDef _ B W t hd _ _ hW0 _ hA h2 hlt χ omB omW hWB hWW ν 𝓕 hν m hm u hu hinv hK φ hφ hKφ
  have hrk := hd.rank_add
  have hIw := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a hDef.maj
  have hχ := GlobalTheory.T.isHeckeChar_restrictionEta_inv D χ W.rank hWW.hecT hWW.resT
  obtain ⟨hEC, hReg⟩ := hP D A (by omega) a hDef.maj hIw χ⁻¹ W.rank hχ.1 hχ.2 _ _
    (k0 D ψ A B χ omB hWB ν 𝓕 hν a hDef.maj φ hφ hKφ)
  obtain ⟨U, d, E, ε, hU, hR, hs, hd0, hhol, hc, hi, he, hrad⟩ :=
    k1 D A _ hEC hReg (fun g => hEC.1.analyticOnNhd_flat g) (sZero A B)
  obtain ⟨m0, hm0, hp0⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_standardUnitaryChart_doubledSpace D A m0 hm0
  obtain ⟨p, hp⟩ := hp0 A a hDef.maj κ hκ
  obtain ⟨lam, hlam, hψ', -⟩ := GlobalTheory.T.shiftedAdditiveCharacter_archimedeanParameters D ψ hWB.std θ hDef.inf m0 hm0
  obtain ⟨oB, hTB⟩ := GlobalTheory.T.exists_weilDatum_transport_schwartzBruhat_standard D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf κ
  obtain ⟨νW, 𝓨, hνW⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank A.rank
  obtain ⟨oW, hTW⟩ := GlobalTheory.T.exists_weilDatum_transport_schwartzBruhat_standard D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf κ
  have hSB : IsWeilSch (shift ψ lam) χ⁻¹ θ B ν oB :=
    ⟨GlobalTheory.T.transportedSchrodinger_standardLeviAction D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam,
     GlobalTheory.T.transportedSchrodinger_siegelUnipotentAction D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam,
     GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam⟩
  have hSW : IsWeilSch (shift ψ lam) χ⁻¹ θ W νW oW :=
    ⟨GlobalTheory.T.transportedSchrodinger_standardLeviAction D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf m0 hm0 κ hκ oW hTW lam hlam,
     GlobalTheory.T.transportedSchrodinger_siegelUnipotentAction D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf m0 hm0 κ hκ oW hTW lam hlam,
     GlobalTheory.T.weyl_formula_standardUnitaryGroup_weilDatum D ψ A W χ omW hWW νW 𝓨 hνW θ hDef.inf m0 hm0 κ hκ oW hTW lam hlam⟩
  let Φ : schwartzA θ B.rank A.rank :=
    ⟨sch ψ A B ν 𝓕 (omB ((p : GA D (dblSp A))⁻¹, 1) φ),
      (GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hWB.std θ hDef.inf A B ν 𝓕 hν).1 _ (hWB.om_pres _ φ hφ)⟩
  obtain ⟨-, hCont, hser⟩ := k3b D ψ A B χ omB hWB ν 𝓕 hν θ hDef.inf m0 hm0 κ hκ oB hTB lam hlam a hDef.maj p hp φ hφ hKφ Φ rfl
    U d E hU hR hs hd0 hhol hc hi he
  obtain ⟨hH, hL⟩ := k3a D A m0 hm0 κ hκ a hDef.maj p hp
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    have hBr : B.rank = W.rank + 2 * t := by omega
    simp only [sZero]; rw [hBr, hA]; push_cast; ring
  obtain ⟨hcc, hcl⟩ := k2c D _ _ _ _ _ _ _ _ hCont ε hrad 1
  have hCont' := hCont
  have hrad' := hrad
  rw [hs0] at hCont' hrad'
  obtain ⟨hv, hkill⟩ := hC D A.rank t B W ⟨hd⟩ hA.symm h2 hlt hW0 (shift ψ lam) hψ' χ⁻¹ hχ.1 hχ.2 θ hDef.inf ν νW
    ⟨𝓕, hν⟩ ⟨𝓨, hνW⟩ oB oW hSB hSW _ hH hL Φ U d _ _ hCont' ε hrad'
  rw [← hs0] at hv hkill
  refine ⟨fun g => cf d (fun z g => npow (absA D (aP A p)) (z - sZero A B) * E z (κ.symm g * ((p : GA D (dblSp A))⁻¹)))
    (sZero A B) ε 1 (κ (g * p)), ⟨hEC.1, fun g => ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := k2 _ _ U d (sZero A B) ε _ hU hR (hCont.hol (κ (g * p))) hd0 hrad
      (fun z hz => hCont.eq z hz (κ (g * p))) (fun k hk => congrFun (hv k hk) (κ (g * p)))
    exact k2b _ _ _ _ _ _ (hom_pos _ _) h1 h2 (fun s hs => hser s hs g)
  · exact k4 D ψ θ A cA a hDef W χ omW hWW νW 𝓨 hνW m0 hm0 κ hκ oW hTW p m hm u hu hinv hK _ hcc hcl
      (fun X _ νX _ c hc hcp w hw h0 => hkill X νX c w hc hcp hw h0)

end PositivityTheory.Rg.Rsw.Kplug

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.ContinuationPoleOrder
noncomputable section

open Filter Topology Set Metric GlobalTheory.Cont

namespace PositivityTheory.Rg.Rsw.Kplug

theorem k2b2_tendsto {s₀ : ℂ} : ∀ (k : ℕ) {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}, HasFPowerSeriesAt g p s₀ →
    (∀ i < k, p.coeff i = 0) → Tendsto (fun s => g s / (s - s₀) ^ k) (𝓝[≠] s₀) (𝓝 (p.coeff k)) := by
  intro k g p hp hk
  have hG := hp.has_fpower_series_iterate_dslope_fslope k
  have hval : ∀ j, (Function.swap dslope s₀)^[j] g s₀ = p.coeff j := fun j => by
    rw [← (hp.has_fpower_series_iterate_dslope_fslope j).coeff_zero 1]
    have := FormalMultilinearSeries.coeff_iterate_fslope (p := p) j 0
    rw [zero_add] at this
    exact this
  have hz : ∀ j < k, (Function.swap dslope s₀)^[j] g s₀ = 0 := fun j hj => by
    rw [hval j, hk j hj]
  have heq := pow_sub_smul_iterate_dslope_of_zero k hz
  have hc : Tendsto ((Function.swap dslope s₀)^[k] g) (𝓝[≠] s₀) (𝓝 (p.coeff k)) := by
    rw [← hval k]
    exact hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : (s - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
  rw [← heq s, smul_eq_mul, mul_div_cancel_left₀ _ hne]

theorem k2b2_cps (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (n : ℕ) :
    (cauchyPowerSeries f c R).coeff n =
      (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(c, R), (1 / (z - c)) ^ n • (z - c)⁻¹ • f z :=
  cauchyPowerSeries_apply f c R n 1

theorem continuation_pole_order : PositivityTheory.Rg.Rsw.Kplug.K2 := by
  intro h e U d s₀ ε σ hU hRD he hd hrad hED hres
  obtain ⟨hε, hball, hdne⟩ := hrad
  set c : ℂ := (2 * ↑Real.pi * Complex.I)⁻¹ *
    ∮ (z : ℂ) in C(s₀, ε), (z - s₀) ^ (1 - 1) * (e z / Polynomial.eval z d) with hc
  set H : ℂ → ℂ := fun z => e z / Polynomial.eval z d with hH
  have hs₀U : s₀ ∈ U := hball (mem_closedBall_self hε.le)
  have hdan : ∀ z, AnalyticAt ℂ (fun z => Polynomial.eval z d) z := fun z =>
    Differentiable.analyticAt (Polynomial.differentiable d) z
  have hean : AnalyticOnNhd ℂ e U := he.analyticOnNhd hU
  have hHmer : ∀ z ∈ U, MeromorphicAt H z := fun z hz =>
    (hean z hz).meromorphicAt.div (hdan z).meromorphicAt
  have hext : IsExtAt h s₀ H := by
    refine ⟨U, hs₀U, hRD, hHmer, ?_⟩
    obtain ⟨M, hM⟩ := ((Polynomial.finite_setOf_isRoot hd).image Complex.re).bddAbove
    refine ⟨max σ M, fun z hz => ?_⟩
    have hz' : max σ M < z.re := hz
    have hdz : Polynomial.eval z d ≠ 0 := by
      intro h0
      have : z.re ≤ M := hM ⟨z, h0, rfl⟩
      exact absurd hz' (not_lt.mpr (le_max_of_le_right this))
    simp only [hH, hED z (lt_of_le_of_lt (le_max_left _ _) hz')]
    field_simp
  have hT : Tendsto (fun s => (s - s₀) * H s) (𝓝[≠] s₀) (𝓝 c) := by
    obtain ⟨q, hdq, hndvd⟩ := d.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hd s₀
    generalize hm : Polynomial.rootMultiplicity s₀ d = m at hdq
    have hq0 : q.eval s₀ ≠ 0 := fun h0 => hndvd (Polynomial.dvd_iff_isRoot.mpr h0)
    have hdeval : ∀ z, Polynomial.eval z d = (z - s₀) ^ m * q.eval z := fun z => by
      have := congrArg (Polynomial.eval z) hdq
      simpa using this
    have hqne : ∀ z ∈ closedBall s₀ ε, q.eval z ≠ 0 := by
      intro z hz h0
      by_cases hzs : z = s₀
      · exact hq0 (hzs ▸ h0)
      · exact hdne z hz hzs (by rw [hdeval, h0, mul_zero])
    set F : ℂ → ℂ := fun z => e z / q.eval z with hF
    have hFd : DifferentiableOn ℂ F (closedBall s₀ ε) :=
      (he.mono hball).div q.differentiable.differentiableOn hqne
    set R : NNReal := ε.toNNReal with hRdef
    have hR : (R : ℝ) = ε := Real.coe_toNNReal _ hε.le
    have hRpos : 0 < R := Real.toNNReal_pos.mpr hε
    have hFps := (show DifferentiableOn ℂ F (closedBall s₀ (R : ℝ)) by rw [hR]; exact hFd).hasFPowerSeriesOnBall hRpos
    have hcf : ∀ j, j + 1 ≤ m → (cauchyPowerSeries F s₀ (R : ℝ)).coeff j =
        (2 * ↑Real.pi * Complex.I)⁻¹ *
          ∮ (z : ℂ) in C(s₀, ε), (z - s₀) ^ (m - 1 - j) * (e z / Polynomial.eval z d) := by
      intro j hj
      rw [k2b2_cps, hR, smul_eq_mul]
      congr 1
      apply circleIntegral.integral_congr hε.le
      intro z hz
      have hzs : z - s₀ ≠ 0 := sub_ne_zero.mpr (ne_of_mem_sphere hz hε.ne')
      obtain ⟨r, hr⟩ : ∃ r, m = r + j + 1 := ⟨m - 1 - j, by omega⟩
      have hr' : m - 1 - j = r := by omega
      simp only [smul_eq_mul, hdeval, hF, hr', hr]
      by_cases hqz : q.eval z = 0
      · simp [hqz]
      · generalize z - s₀ = w at hzs ⊢
        generalize e z = a
        generalize Polynomial.eval z q = b at hqz ⊢
        rw [show r + j + 1 - 1 - j = r by omega, pow_succ, pow_add, one_div, inv_pow]
        field_simp
    have hFan := hFps.hasFPowerSeriesAt
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have hc0 : c = 0 := by
        have hI : ∮ (z : ℂ) in C(s₀, ε), (z - s₀) ^ (1 - 1) * (e z / Polynomial.eval z d) =
            ∮ (z : ℂ) in C(s₀, ε), F z := by
          apply circleIntegral.integral_congr hε.le
          intro z hz
          simp [hdeval, hm0, hF]
        rw [hc, hI, Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le
          Set.countable_empty hFd.continuousOn, mul_zero]
        intro z hz
        exact hFd.differentiableAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hz.1) ball_subset_closedBall)
      rw [hc0]
      have hlim : Tendsto (fun s => (s - s₀) * F s) (𝓝 s₀) (𝓝 ((s₀ - s₀) * F s₀)) :=
        ((continuous_id.sub continuous_const).continuousAt.mul hFan.continuousAt).tendsto
      rw [sub_self, zero_mul] at hlim
      refine (hlim.mono_left nhdsWithin_le_nhds).congr' (Filter.Eventually.of_forall fun s => ?_)
      simp [hH, hF, hdeval, hm0]
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hcoef : ∀ i < n, (cauchyPowerSeries F s₀ (R : ℝ)).coeff i = 0 := by
        intro i hi
        rw [hcf i (by omega)]
        have := hres (n + 1 - i) (by omega)
        rwa [show n + 1 - i - 1 = n + 1 - 1 - i by omega] at this
      have hlim := k2b2_tendsto n hFan hcoef
      rw [hcf n (by omega), show n + 1 - 1 - n = 1 - 1 by omega] at hlim
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hw : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
      simp only [hH, hF, hdeval]
      by_cases hqs : Polynomial.eval s q = 0
      · simp [hqs]
      · rw [pow_succ]
        field_simp
  refine ⟨⟨H, hext, 0, by simp, ?_⟩, ⟨H, hext, ?_⟩⟩
  · refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp
  · have hmer : MeromorphicAt ((fun s => s - s₀) * H) s₀ :=
      (by fun_prop : MeromorphicAt (fun s => s - s₀) s₀).mul (hHmer s₀ hs₀U)
    have h0 : 0 ≤ meromorphicOrderAt ((fun s => s - s₀) * H) s₀ :=
      (tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer).mp ⟨c, hT⟩
    rw [meromorphicOrderAt_mul (by fun_prop) (hHmer s₀ hs₀U), meromorphicOrderAt_id_sub_const] at h0
    cases ho : meromorphicOrderAt H s₀ with
    | top => exact le_top
    | coe n =>
      rw [ho] at h0
      have : (0 : WithTop ℤ) ≤ ((1 + n : ℤ) : WithTop ℤ) := by exact_mod_cast h0
      have h1 : (0 : ℤ) ≤ 1 + n := by exact_mod_cast this
      exact_mod_cast (by omega : (-(1 : ℕ) : ℤ) ≤ n)

end PositivityTheory.Rg.Rsw.Kplug

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.LocalRepresentationSmoothness
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Eis
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw
open Filter Topology Set Metric

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Kplug.FormalGroupLawNegation

theorem lim_eq {f F : ℂ → ℂ} {W : Set ℂ} {c w : ℂ} (hW : IsOpen W) (hw : w ∈ W) (hF : ContinuousOn F W)
    (he : ∀ u ∈ W, u ≠ c → f u = F u) : limUnder (𝓝[≠] w) f = F w := by
  have h1 : Tendsto F (𝓝[≠] w) (𝓝 (F w)) :=
    ((hF.continuousAt (hW.mem_nhds hw)).tendsto).mono_left nhdsWithin_le_nhds
  have h2 : ∀ᶠ u in 𝓝[≠] w, u ≠ c := by
    rcases eq_or_ne w c with rfl | h
    · exact self_mem_nhdsWithin
    · exact eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds h)
  have h3 : F =ᶠ[𝓝[≠] w] f := by
    filter_upwards [h2, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hw)] with u hu hu'
    exact (he u hu' hu).symm
  exact (h1.congr' h3).limUnder_eq

variable {D : D7} (V : HSp D) (Φ : ℂ → GA D (dblSp V) → ℂ) (d : Polynomial ℂ)

def Ek (z : ℂ) (g : GA D (dblSp V)) : ℂ := limUnder (𝓝[≠] z) fun u => d.eval u * eisCont V Φ u g

def LocRep (z : ℂ) : Prop :=
  ∃ (W : Set ℂ) (F : ℂ → GA D (dblSp V) → ℂ) (c : ℂ), IsOpen W ∧ z ∈ W ∧ (∀ g, DifferentiableOn ℂ (F · g) W) ∧
    ContinuousOn (fun y : ℂ × GA D (dblSp V) => F y.1 y.2) (W ×ˢ univ) ∧
    ∀ u ∈ W, u ≠ c → ∀ g, F u g = d.eval u * eisCont V Φ u g

variable {V Φ d}

theorem LocRep.eq {z : ℂ} (h : LocRep V Φ d z) : ∃ (W : Set ℂ) (F : ℂ → GA D (dblSp V) → ℂ), IsOpen W ∧ z ∈ W ∧
    (∀ g, DifferentiableOn ℂ (F · g) W) ∧ ContinuousOn (fun y : ℂ × GA D (dblSp V) => F y.1 y.2) (W ×ˢ univ) ∧
    ∀ u ∈ W, ∀ g, Ek V Φ d u g = F u g := by
  obtain ⟨W, F, c, hW, hz, hd, hc, he⟩ := h
  exact ⟨W, F, hW, hz, hd, hc, fun u hu g => lim_eq (f := fun u => d.eval u * eisCont V Φ u g) (F := fun u => F u g)
    (c := c) hW hu (hd g).continuousOn fun u' hu' hne => (he u' hu' hne g).symm⟩

theorem LocRep.diff {z : ℂ} (h : LocRep V Φ d z) (g : GA D (dblSp V)) : DifferentiableAt ℂ (Ek V Φ d · g) z := by
  obtain ⟨W, F, hW, hz, hd, -, e⟩ := h.eq
  exact ((hd g).differentiableAt (hW.mem_nhds hz)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hW.mem_nhds hz) fun u hu => e u hu g)

theorem LocRep.cont {z : ℂ} (h : LocRep V Φ d z) (g : GA D (dblSp V)) :
    ContinuousAt (fun y : ℂ × GA D (dblSp V) => Ek V Φ d y.1 y.2) (z, g) := by
  obtain ⟨W, F, hW, hz, -, hc, e⟩ := h.eq
  have hN : W ×ˢ (univ : Set (GA D (dblSp V))) ∈ 𝓝 (z, g) := (hW.prod isOpen_univ).mem_nhds ⟨hz, trivial⟩
  exact (hc.continuousAt hN).congr (Filter.eventually_of_mem hN fun y hy => (e y.1 hy.1 y.2).symm)

end PositivityTheory.Rg.Rsw.Kplug.FormalGroupLawNegation

namespace PositivityTheory.Rg.Rsw.Kplug

open FormalGroupLawNegation

theorem local_representation_smoothness : PositivityTheory.Rg.Rsw.Kplug.K1 := by
  intro D V Φ hE hReg ha s₀
  have ha' : ∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) (rightOf ((V.rank : ℝ) / 2)) := ha
  set a : ℝ := (V.rank : ℝ) / 2 with ha_def
  choose k hk using hReg
  have hk' : ∀ s, ∃ (r : ℝ) (H : ℂ → GA D (dblSp V) → ℂ), 0 < r ∧
      (∀ s' ∈ ball s r, s' ≠ s → ∀ g, H s' g = (s' - s) ^ k s * eisCont V Φ s' g) ∧
      (∀ g, DifferentiableOn ℂ (H · g) (ball s r)) ∧
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball s r ×ˢ univ) := fun s => by
    obtain ⟨r, H, h1, h2, h3, h4, -⟩ := hk s
    exact ⟨r, H, h1, h2, h3, h4⟩
  choose r H hr hH hHd hHc using hk'
  set T : ℝ := |a - s₀.re| + 2 with hT_def
  set K : Set ℂ := (fun t : ℝ => s₀ + t) '' Icc 0 T with hK_def
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover (fun x => ball x (r x)) fun x _ => ball_mem_nhds x (hr x)
  set B : Set ℂ := ⋃ x ∈ t, ball x (r x) with hB_def
  have hB : IsOpen B := isOpen_biUnion fun x _ => isOpen_ball
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open hB hKt
  set W₀ : Set ℂ := B ∪ rightOf a with hW₀_def
  set A : Set ℂ := {z | ∀ τ : ℝ, 0 ≤ τ → z + τ ∈ W₀} with hA_def
  set U : Set ℂ := interior A with hU_def
  set d : Polynomial ℂ := ∏ x ∈ t, (Polynomial.X - Polynomial.C x) ^ k x with hd_def

  have hUW : U ⊆ W₀ := fun z hz => by simpa using interior_subset hz 0 le_rfl
  have hs₀ : s₀ ∈ U := by
    refine mem_interior.2 ⟨ball s₀ (min δ 1), fun z hz τ hτ => ?_, isOpen_ball, mem_ball_self (lt_min hδ one_pos)⟩
    have hz' : dist z s₀ < min δ 1 := hz
    rcases le_or_gt τ T with hτT | hτT
    · refine mem_union_left _ (hδK ?_)
      rw [Metric.mem_thickening_iff]
      refine ⟨s₀ + τ, ⟨τ, ⟨hτ, hτT⟩, rfl⟩, ?_⟩
      rw [dist_add_right]
      exact hz'.trans_le (min_le_left _ _)
    · refine mem_union_right _ ?_
      show a < (z + τ).re
      have h1 : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
      have h2 : ‖z - s₀‖ < 1 := by rw [← dist_eq_norm]; exact hz'.trans_le (min_le_right _ _)
      have h3 : a - s₀.re ≤ |a - s₀.re| := le_abs_self _
      have h4 := neg_abs_le (z - s₀).re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.sub_re] at h1 h4 ⊢
      linarith
  have hRD : IsRightDomain U := by
    refine ⟨⟨a, interior_maximal (fun z hz τ hτ => mem_union_right _ ?_) (isOpen_rightOf a)⟩, fun z hz τ hτ => ?_⟩
    · show a < (z + τ).re
      have : a < z.re := hz
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    · have hopen : IsOpen ((fun w : ℂ => w - τ) ⁻¹' U) := isOpen_interior.preimage (by fun_prop)
      have hsub : (fun w : ℂ => w - τ) ⁻¹' U ⊆ A := fun w hw τ' hτ' => by
        have h1 := interior_subset hw (τ + τ') (by positivity)
        have e : w - (τ : ℂ) + ((τ + τ' : ℝ) : ℂ) = w + τ' := by push_cast; ring
        rw [e] at h1
        exact h1
      refine interior_maximal hsub hopen ?_
      show z + (τ : ℂ) - τ ∈ U
      rw [add_sub_cancel_right]
      exact hz

  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero x)

  have hloc : ∀ z ∈ U, LocRep V Φ d z := by
    intro z hz
    rcases hUW hz with hzB | hzR
    · obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 hzB
      set q : Polynomial ℂ := ∏ y ∈ t.erase x, (Polynomial.X - Polynomial.C y) ^ k y with hq_def
      have hdq : d = (Polynomial.X - Polynomial.C x) ^ k x * q := (Finset.mul_prod_erase t _ hxt).symm
      refine ⟨ball x (r x), fun u g => q.eval u * H x u g, x, isOpen_ball, hzx,
        fun g => q.differentiable.differentiableOn.mul (hHd x g),
        (q.continuous.comp continuous_fst).continuousOn.mul (hHc x), fun u hu hne g => ?_⟩
      simp only
      rw [hH x u hu hne g, hdq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      ring
    · have hv := hE.1.eisValueAt ha' hzR
      obtain ⟨r', hr', hd', hc', -⟩ := (hk z).of_eisValueAt hv
      exact ⟨ball z r', fun u g => d.eval u * eisCont V Φ u g, z, isOpen_ball, mem_ball_self hr',
        fun g => d.differentiable.differentiableOn.mul (hd' g),
        (d.continuous.comp continuous_fst).continuousOn.mul hc', fun u _ _ g => rfl⟩

  have hZ : {z : ℂ | d.IsRoot z}.Finite := Polynomial.finite_setOfPred_isRoot hd0
  have hO : IsOpen (U ∩ ({z : ℂ | d.IsRoot z} \ {s₀})ᶜ) :=
    isOpen_interior.inter (hZ.subset fun x (hx : x ∈ {z : ℂ | d.IsRoot z} \ {s₀}) => hx.1).isClosed.isOpen_compl
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.1 hO s₀ ⟨hs₀, fun h => h.2 rfl⟩
  have hcb : closedBall s₀ (ε₁ / 2) ⊆ ball s₀ ε₁ := closedBall_subset_ball (half_lt_self hε₁)
  refine ⟨U, d, Ek V Φ d, ε₁ / 2, isOpen_interior, hRD, hs₀, hd0, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun g z hz => ((hloc z hz).diff g).differentiableWithinAt
  · exact fun y hy => ((hloc y.1 hy.1).cont y.2).continuousWithinAt
  · intro z _ γ hγ g
    unfold Ek
    congr 1
    funext u
    congr 1
    exact hE.1.leftInv_eisLaurent u 0 γ hγ g
  · intro z hz g
    exact lim_eq (f := fun u => d.eval u * eisCont V Φ u g) (F := fun u => d.eval u * eisSer V Φ g u) (c := z)
      (isOpen_rightOf a) hz (d.continuous.continuousOn.mul (ha' g).continuousOn) fun u hu _ => by
        show d.eval u * cont (eisSer V Φ g) u = d.eval u * eisSer V Φ g u
        rw [eqOn_cont (ha' g) hu]
  · exact ⟨half_pos hε₁, fun z hz => (hball (hcb hz)).1, fun z hz hne h0 => (hball (hcb hz)).2 ⟨h0, hne⟩⟩

end PositivityTheory.Rg.Rsw.Kplug

end
end

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace PositivityTheory.Rg.Rsw.Kplug

theorem resKilled_of_leaves : K0 → K1 → K2 → SimplePoleRescaling → ContinuousInvariantCoefficients → KillingPolyConst → ContinuationThroughChart → K4 →
    GlobalTheory.Published.SiegelEisensteinContinuation → PositivityTheory.Rg.Rsw.ResCore → ResidueVanishing :=
  residue_vanishes_of_siegel_eisenstein

theorem k0 : K0 := mem_section_space
theorem k1 : K1 := local_representation_smoothness
theorem k2 : K2 := continuation_pole_order
theorem k2b : SimplePoleRescaling := simple_pole_rescaling
theorem k2c : ContinuousInvariantCoefficients := continuous_invariant_coefficients
theorem k3a : KillingPolyConst := continuation_chart_defined
theorem k3b : ContinuationThroughChart := continuation_through_chart
theorem k4 : K4 := theta_continuation

theorem res_killed' : GlobalTheory.Published.SiegelEisensteinContinuation → PositivityTheory.Rg.Rsw.ResCore → ResidueVanishing :=
  resKilled_of_leaves k0 k1 k2 k2b k2c k3a k3b k4

end PositivityTheory.Rg.Rsw.Kplug

end
end

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Exh.Top

variable {D : D7}

theorem downNe_of_core : ResidueKilled.DM → PositivityTheory.Rg.Rsw.ResCore →
    GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D := by
  intro hDM hCore hSP D hER ψ θ A W t χA χW om cA a β Z m u par sW Φ hDef hSigW hW0 hrank hη hom hPl hm hForm hOcc hNo
  obtain ⟨H, B, o, hd, hSigH, hSigB, hHr, hHsig, sH, hsH⟩ := GlobalTheory.T.exists_sum_hyperbolicPlanes_orthogonal_wittDecomposition D W t hSigW
  obtain ⟨c, hHyp⟩ := hForm.str
  have ht : W.rank + 5 ≤ t := hHyp.2.1
  have hBr : B.rank = W.rank + 2 * t := by have := o.rank_add; omega
  have hstd : IsStdChar D ψ (-1) := hom.std
  have h1 : IsHeckeChar D (1 : (AE D)ˣ →* Circle) := ⟨continuous_const, fun _ => rfl⟩
  have hr1 : ResEta D (1 : (AE D)ˣ →* Circle) 0 := by
    have h := resEta_parity (m := 0) (resEta_mul hom.resS (resEta_inv hom.resS)) (by omega)
    rwa [show χA * χA⁻¹ = 1 from mul_inv_cancel χA] at h
  obtain ⟨omH, homH⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ A H χA 1 hstd hom.hecS h1 hom.resS
    (resEta_parity hr1 (by omega))
  obtain ⟨omB, homB⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ A B χA χW hstd hom.hecS hom.hecT hom.resS
    (resEta_parity hom.resT (by omega))
  obtain ⟨omhB, homhB⟩ :=
    GlobalTheory.Core.Rk.exists_doubled_weilDatum GlobalTheory.weilRepresentationUnitaryPair D ψ A B χA χW omB homB
  obtain ⟨omhW, homhW⟩ :=
    GlobalTheory.Core.Rk.exists_doubled_weilDatum GlobalTheory.weilRepresentationUnitaryPair D ψ A W χA χW om hom
  have hAH : A.rank ≤ H.rank := by omega
  obtain ⟨f, hf, hf0, hfvac, hfsph, hfκ, hfoff⟩ :=
    GlobalTheory.T.exists_vacuumVector_principalCongruenceSupport D ψ θ A H χA omH (fun _ => 1) sH hDef.inf hη homH hDef.one hsH hAH β Z hPl
  have hfb := GlobalTheory.T.definite_real_group_fixes_split_space_weil_vacuum D ψ θ A H t χA omH sH hDef.inf hη homH hDef.one hsH hSigH hHr hHsig f hf hfvac
  obtain ⟨sB, LB, hsB, hLB, hbF, hbS⟩ :=
    GlobalTheory.T.boxProducts_orthogonalSum_target_cartan_fock D ψ θ A B W H o (fun _ => 1) sW sH hstd hDef.inf hOcc.cart hsH
  have hFs : IsFockVec ψ θ A B (fun _ => 1) sB (o.boxT A Φ f) := hbF Φ f hOcc.fock (fockVec_of_vac_nc hf hfvac)
  have hSs : IsSphOff ψ A B (frameLat A) LB (under Z) (o.boxT A Φ f) :=
    hbS (frameLat A) (under Z) Φ f hOcc.sph hfsph
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank A.rank
  have hPair : Pair ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 :=
    { setting := ⟨by omega, by omega, by omega, hDef.inf, hDef.sig, hDef.cart, hDef.one, hsB, hDef.cA_eq⟩
      maj := hDef.maj
      maj_eq := hDef.maj_eq
      weil := homB
      covol := hν }
  have hu := hForm.mem
  have hu' := (Submodule.mem_inf.1 hu).2
  have huc : Continuous u := hu'.1
  have hul : ∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g := hu'.2.1
  have hKill := GlobalTheory.T.doubling_integrals_vanish_of_all_lifts_vanish D ψ A W χA χW om omhW hDef.sig hDef.pos hom homhW m hm u huc hul hNo
  have hφθ := GlobalTheory.Core.Rk.DeltaTheta.main D ψ A B hstd _ _ hFs.1 hFs.1
  have hφK := GlobalTheory.Core.Rk.IP.delta_isKFinVec D ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 hPair omhB homhB _ _ hFs hFs
  obtain ⟨E₁, hE₁, hE₁0⟩ := PositivityTheory.Rg.Rsw.Kplug.res_killed' (ResidueKilled.sec_of_dm hDM) hCore D ψ θ A cA a hDef hPl.two B W t hd hSigB hSigW hW0
    (by omega) hrank (by omega) (by omega) χW omhB omhW homhB homhW ν 𝓕 hν m hm u huc hul hKill _ hφθ hφK
  obtain ⟨hZF, hEC, hAn, hReg, hint⟩ :=
    GlobalTheory.Core.Rk.Exh.zeta_eq_integral_integrand_nc hDM D ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 hPair omhB homhB m hm _ hFs u hu
  obtain ⟨hcc, -⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hDef.sig hDef.pos m hm
  have hRD := (GlobalTheory.Unf.contAut_rapidDec_bounded_integrable D A hcc (fun g => conj (u g))
    ⟨fun γ hγ g => by simp only [hul γ hγ g], Complex.continuous_conj.comp huc⟩).1
  have hμ : IsHeckeChar D χW⁻¹ :=
    ⟨(hom.hecT.1.inv : Continuous fun x => (χW x)⁻¹), fun x => by rw [MonoidHom.inv_apply, hom.hecT.2 x, inv_one]⟩
  have hcoef := GlobalTheory.T.zeta_integral_eisenstein_residue D A χW⁻¹ hμ m hm _ hEC hAn hReg _ _ hRD hRD hZF
    (sZero A B) E₁ hE₁
  rw [hE₁0] at hcoef
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.levelPlaces_integral_nonzero_constant D ψ θ A cA a hDef B W H o χA χW omB om omH homB hom homH β Z hPl m hm u hu
    hForm.fix sW Φ hOcc f hf hf0 hfκ hfb hfoff ν 𝓕 hν
  have hsph : SphFun A (frameLat A) (under Z) u := sphFun_of_param_nc hForm.param
  have hUn : Unram ψ A B χW (frameLat A) LB (under Z) (o.boxT A Φ f) (o.boxT A Φ f) :=
    ⟨GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A, hLB, fun v _ h2 => hPl.two v h2, hForm.unr, hSs, hSs⟩
  have hEq : EqRight (GlobalTheory.Eis.zeta A χW⁻¹ m (flat A a (swSec A B omhB ν 𝓕 (delta A B (o.boxT A Φ f) (o.boxT A Φ f)))
      (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g)))
      (fun s => GlobalTheory.LFun.LSD D (under Z) par χW (s + 1 / 2) /
        GlobalTheory.LFun.dSfun D.host.E (under Z : Set (FinPl D)) A.rank B.rank s * C) := by
    refine ⟨A.rank + 1, fun s hs => ?_⟩
    have hs' : (A.rank : ℝ) + 1 < s.re := hs
    have h2 : (A.rank : ℝ) / 2 < s.re := by
      have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
      linarith
    obtain ⟨hI, hz⟩ := hint s h2
    rw [hz, hER ψ θ A B χA χW (fun _ => 1) sB t cA a omB ν 𝓕 hPair (frameLat A) LB (under Z) _ _ hFs.1 hFs.1 hUn
      m hm u hu u hu par hForm.param hsph s hs' hI, hC s]
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    simp only [sZero]
    rw [hBr, hrank]
    push_cast
    ring
  have hcoef' : CoeffAt (GlobalTheory.Eis.zeta A χW⁻¹ m (flat A a (swSec A B omhB ν 𝓕 (delta A B (o.boxT A Φ f) (o.boxT A Φ f)))
      (sZero A B)) (fun g => conj (u g)) (fun g => conj (u g))) ((t : ℂ) / 2) (-1) 0 := by
    rw [← hs0]
    exact hcoef
  exact GlobalTheory.T.zeta_residue_ne_zero_of_simple_pole_lift_L_function hSP D (under Z) W.rank t c par χW hHyp A.rank B.rank _ C _ hC0 hEq hcoef' rfl

end GlobalTheory.Core.Rk.Exh.Top

end
