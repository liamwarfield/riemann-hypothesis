module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenberg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelCoordinatesBijOnAndWeilLinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralFiniteCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralFiniteCombination
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal opEFJ IsQuotIntFJ)

noncomputable section
namespace GlobalTheory.PosOne.SymComb
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix
open GlobalTheory.RootEx.Unfolding (opL orbit_locallyConstant)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem isQuotIntFJ_linear {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} (hp : 1 ≤ ρ) (hpc : ρ < c)
    (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure]
    (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] {f f' : GL (n ⊕ Fin c) k → ℂ} (a : ℂ) {z z' : ℂ} :
    IsQuotIntFJ ν μX μG ρ f z → IsQuotIntFJ ν μX μG ρ f' z' →
      IsQuotIntFJ ν μX μG ρ (fun h => a * f h + f' h) (a * z + z') := by
  classical
  rintro ⟨F, hF, h1, h2⟩ ⟨F', hF', h1', h2'⟩
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨bX, lX, sX, -⟩ := GlobalTheory.SplitWeil.volGL_haar k n ν
  obtain ⟨bG, lG, sG, -⟩ := GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν
  haveI := QuotLinear.finiteOnCompacts_volN (n := n) (c := c) (p := ρ + 1) ν
  haveI : LocallyCompactSpace (N k n c (ρ + 1)) :=
    (QuotLinear.isClosed_N (k := k) (n := n) (c := c) (p := ρ + 1)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c (ρ + 1)) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure (volN ν n c (ρ + 1)) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (volN ν n c (ρ + 1)) := sigmaFinite_of_locallyFinite
  let m : Measure (n → k) := Measure.pi fun _ => ν
  let ι : GL n k × N k n c (ρ + 1) × (n → k) → GL (n ⊕ Fin c) k := fun z =>
    embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) z.2.2
  let M : Measure (GL n k × N k n c (ρ + 1) × (n → k)) := μX.prod ((volN ν n c (ρ + 1)).prod m)
  have hm : Continuous ι :=
    ((QuotLinear.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd.fst)).mul
      (ExchangeSupport.continuous_colE.comp continuous_snd.snd)
  have hint : ∀ φ ∈ SB (GL (n ⊕ Fin c) k), ∀ h, Integrable (fun z => φ (ι z * h)) M := by
    intro φ hφ h
    obtain ⟨D, hD, hD'⟩ := GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hp hpc _
      (hφ.2.isCompact.image (continuous_mul_const h⁻¹))
    refine (hφ.1.continuous.comp (hm.mul continuous_const)).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hD fun z hz => ?_
    by_contra h0
    exact hz (hD' z ⟨_, subset_tsupport _ h0, by simp [ι]⟩)
  have hprod : ∀ φ ∈ SB (GL (n ⊕ Fin c) k), ∀ h, (∫ g, (∫ u : N k n c (ρ + 1), (∫ β : n → k,
      φ (embX c g * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) β * h) ∂m) ∂(volN ν n c (ρ + 1))) ∂μX) =
      ∫ z, φ (ι z * h) ∂M := by
    intro φ hφ h
    rw [integral_prod _ (hint φ hφ h)]
    exact integral_congr_ae ((hint φ hφ h).prod_right_ae.mono fun x hx => (integral_prod _ hx).symm)
  have hs : a • F + F' ∈ SB (GL (n ⊕ Fin c) k) := add_mem (Submodule.smul_mem _ a hF) hF'
  refine ⟨a • F + F', hs, fun h => ?_, ?_⟩
  · beta_reduce
    rw [hprod _ hs, h1, h1', hprod _ hF, hprod _ hF', ← integral_const_mul,
      ← integral_add ((hint _ hF h).const_mul a) (hint _ hF' h)]
    rfl
  · have i : Integrable F μG := hF.1.continuous.integrable_of_hasCompactSupport hF.2
    have j : Integrable F' μG := hF'.1.continuous.integrable_of_hasCompactSupport hF'.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (i.const_mul a) j, integral_const_mul, h2, h2']

theorem rel_sum {G ι : Type} (Q : (G → ℂ) → ℂ → Prop) (h0 : Q (fun _ => 0) 0)
    (hl : ∀ (a : ℂ) f f' z z', Q f z → Q f' z' → Q (fun h => a * f h + f' h) (a * z + z'))
    (s : Finset ι) (a : ι → ℂ) (f : ι → G → ℂ) (z : ι → ℂ) (h : ∀ i ∈ s, Q (f i) (z i)) :
    Q (fun g => ∑ i ∈ s, a i * f i g) (∑ i ∈ s, a i * z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact hl _ _ _ _ _ (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem tensorVal_unique {n₀ n₁ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] {c ρ : ℕ} (h1 : 1 ≤ ρ) (h2 : ρ ≤ c) {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {ν : Measure k} (hν : IsSelfDual ψ ν) {A : Type} [AddCommGroup A] [Module ℂ A]
    (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (F : A)
    (Φ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (Θ : Matrix n₁ n₀ k → (n₁ → k) → ℂ) {z z' : ℂ}
    (hz : HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 Φ.1) F) Θ z)
    (hz' : HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 Φ.1) F) Θ z') : z = z' := by
  haveI := hν.1
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hk : IsOpen (((1 : kˣ →* ℂˣ).ker : Subgroup kˣ) : Set kˣ) := by simp
  obtain ⟨⟨r, hr⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) 1 hk
  have hav := (GlobalTheory.PosOne.avg_self_and_props k n₂ n₁ c ρ h1 h2 ψ hψ hψ1 ν hν 1 hk Φ).2
  let C : (n₁ → k) → SB (Matrix n₁ n₀ k) →ₗ[ℂ] ℂ := fun u =>
    (T.flip (opL hψ ν ρ (r (rowE (c + 1) ρ u) Φ))).flip F
  have hC : IsLocallyConstant C :=
    ((orbit_locallyConstant (hsm r hr) Φ).comp_continuous ExchangeSupport.continuous_rowE).comp
      fun v => (T.flip (opL hψ ν ρ v)).flip F
  have key : ∀ Ψ (Φ₀ : SB (n₁ → k)), app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 Φ.1) F =
      ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * C u Ψ ∂(Measure.pi fun _ => ν) := by
    intro Ψ Φ₀
    obtain ⟨hmem, hE, hL⟩ := hav Φ₀
    have e := hE 1
    rw [om_one, om_one] at e
    have l := hL r hr (((T Ψ).flip F).comp (opL hψ ν ρ))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe _ ⟨_, hmem⟩] at l
    rw [← e]
    exact (congrArg (fun t : A →ₗ[ℂ] ℂ => t F) (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (T Ψ) (opL hψ ν ρ ⟨_, hmem⟩))).trans l
  have hh := (GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n₁ ψ hψ hψ1 ν hν).1
  have int1 : ∀ Ψ (Φ₀ : SB (n₁ → k)),
      Integrable (fun u => GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * C u Ψ) (Measure.pi fun _ => ν) := fun Ψ Φ₀ =>
    FourierJacobi.sb_int ⟨(hh Φ₀).1.mul (hC.comp fun l => l Ψ), (hh Φ₀).2.mul_right⟩
  have int2 : ∀ (Φ₀ : SB (n₁ → k)) (u : n₁ → k),
      Integrable (fun β => Φ₀.1 β * (ψ (u ⬝ᵥ β) : ℂ)) (Measure.pi fun _ => ν) := fun Φ₀ u =>
    (Φ₀.2.1.continuous.mul ((continuous_induced_dom.comp hψ).comp
      (continuous_const.dotProduct continuous_id))).integrable_of_hasCompactSupport Φ₀.2.2.mul_right
  have val : ∀ (m : ℕ) (Ψ : Fin m → SB (Matrix n₁ n₀ k)) (Φ₀ : Fin m → SB (n₁ → k)),
      (∀ x y, Θ x y = ∑ i, (Ψ i).1 x * (Φ₀ i).1 y) → ∑ i, app (T (Ψ i)) (opEFJ ψ ν ρ (Φ₀ i).1 Φ.1) F =
      ∫ u, app (C u) (fun x => GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Θ x) u) ∂(Measure.pi fun _ => ν) := by
    intro m Ψ Φ₀ hd
    simp only [key]
    rw [← integral_finsetSum _ fun i _ => int1 _ _]
    congr 1; funext u
    have : (fun x => GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Θ x) u) =
        (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ i).1 u • Ψ i : SB (Matrix n₁ n₀ k)).1 := by
      funext x
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, hd, Finset.sum_mul, mul_assoc]
      rw [integral_finsetSum _ fun i _ => (int2 _ u).const_mul _]
      simp [integral_const_mul, mul_comm]
    rw [this, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe]
    simp
  obtain ⟨m, Ψ, Φ₀, hd, rfl⟩ := hz
  obtain ⟨m', Ψ', Φ₀', hd', rfl⟩ := hz'
  exact (val m Ψ Φ₀ hd).trans (val m' Ψ' Φ₀' hd').symm

end GlobalTheory.PosOne.SymComb

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PosOne.SymComb

section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

theorem symmetricDoubleIntegral_combination_of_pointValues : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k), IsSelfDual ψ ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ) (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A) (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))
    (e : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ) (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ)
    (v : GL (n₀ ⊕ Fin (c + 1 + 1)) k → GL (n₁ ⊕ Fin (c + 1)) k → GL (n₂ ⊕ Fin c) k → ℂ),
    (∀ a ∈ e.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    (∀ a ∈ e.support, ∀ x y, HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ x y P₂.1)) (τ y F))
      (fl ψ ν μ₁ ρ (om μ₁ a x P₁.1)) (v a x y)) →
    ∃ u : GL (n₁ ⊕ Fin (c + 1)) k → ℂ, (∀ x, IsQuotInt ν m₂ G₂ ρ (fun y => comb e fun a => v a x y) (u x)) ∧
      IsQuotIntFJ ν m₁ G₁ ρ u (comb e z) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hc ψ hψ hψ1 ν hν μ₁ μ₂ m₁ G₁ m₂ G₂ i₁ j₁ i₂ j₂ A _ _ τ _ T _ F P₁ P₂
    e z v hz hv
  classical
  haveI := hν.1
  have h1 : 1 ≤ ρ := by omega
  have h2 : ρ ≤ c := by omega
  have q0 : IsQuotInt ν m₂ G₂ ρ (fun _ => 0) 0 := ⟨0, zero_mem _, fun _ => by simp, by simp⟩
  have ql := fun (a : ℂ) f f' z z' => QuotLinear.isQuotInt_linear k n₂ c ρ h1 h2 ν m₂ G₂ f f' a z z'
  have step : ∀ a, ∃ f : GL (n₁ ⊕ Fin (c + 1)) k → ℂ, a ∈ e.support →
      (∀ x, IsQuotInt ν m₂ G₂ ρ (fun y => v a x y) (f x)) ∧ IsQuotIntFJ ν m₁ G₁ ρ f (z a) := by
    intro a
    by_cases ha : a ∈ e.support
    swap
    · exact ⟨0, fun h => absurd h ha⟩
    obtain ⟨w, hw, f, hf, hq⟩ := hz a ha
    refine ⟨f, fun _ => ⟨fun x => ?_, hq⟩⟩
    obtain ⟨m, Ψ, Φ₀, hd, hfx⟩ := hf x
    rw [← om_mul, one_mul, mul_one] at hd
    have s := rel_sum _ q0 ql Finset.univ (fun _ => 1) _ _ fun i _ => hw x (Ψ i) (Φ₀ i)
    simp only [one_mul] at s
    rw [hfx]
    convert s using 2 with y
    exact tensorVal_unique h1 h2 hψ hψ1 hν T (τ y F) ⟨_, om_mem_SB μ₂ x y P₂.2⟩ _ (hv a ha x y) ⟨m, Ψ, Φ₀, hd, rfl⟩
  choose f hf using step
  refine ⟨fun x => ∑ a ∈ e.support, e a * f a x, fun x => ?_, ?_⟩
  · exact rel_sum _ q0 ql e.support e _ _ fun a ha => (hf a ha).1 x
  · exact rel_sum (IsQuotIntFJ ν m₁ G₁ ρ) ⟨0, zero_mem _, fun _ => by simp, by simp⟩
      (fun a _ _ _ _ => isQuotIntFJ_linear h1 (by omega) ν m₁ G₁ a) e.support e f z fun a ha => (hf a ha).2

end

theorem symDbl_comb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k), IsSelfDual ψ ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ) (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A) (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))
    (e : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ) (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ)
    (v : GL (n₀ ⊕ Fin (c + 1 + 1)) k → GL (n₁ ⊕ Fin (c + 1)) k → GL (n₂ ⊕ Fin c) k → ℂ),
    (∀ a ∈ e.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    (∀ a ∈ e.support, ∀ x y, HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ x y P₂.1)) (τ y F))
      (fl ψ ν μ₁ ρ (om μ₁ a x P₁.1)) (v a x y)) →
    ∃ u : GL (n₁ ⊕ Fin (c + 1)) k → ℂ, (∀ x, IsQuotInt ν m₂ G₂ ρ (fun y => comb e fun a => v a x y) (u x)) ∧
      IsQuotIntFJ ν m₁ G₁ ρ u (comb e z) :=
  symmetricDoubleIntegral_combination_of_pointValues

end GlobalTheory.PosOne.SymComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralFiniteCombinationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricDoubleIntegral_finite_combination : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k), IsSelfDual ψ ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ) (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A) (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))
    (e : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ) (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ)
    (v : GL (n₀ ⊕ Fin (c + 1 + 1)) k → GL (n₁ ⊕ Fin (c + 1)) k → GL (n₂ ⊕ Fin c) k → ℂ),
    (∀ a ∈ e.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    (∀ a ∈ e.support, ∀ x y, HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ x y P₂.1)) (τ y F))
      (fl ψ ν μ₁ ρ (om μ₁ a x P₁.1)) (v a x y)) →
    ∃ u : GL (n₁ ⊕ Fin (c + 1)) k → ℂ, (∀ x, IsQuotInt ν m₂ G₂ ρ (fun y => comb e fun a => v a x y) (u x)) ∧
      IsQuotIntFJ ν m₁ G₁ ρ u (comb e z) := by
  first | exact @GlobalTheory.PosOne.SymComb.symDbl_comb | exact GlobalTheory.PosOne.SymComb.symDbl_comb | (intros; apply GlobalTheory.PosOne.SymComb.symDbl_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumOfVacuaIsVacuumBoth
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumOfVacuaIsVacuumBoth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastVacPf

variable {D : D7}

theorem lastBi_apply {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (u : WO A S) (v : WO S X) :
    lastBi o o'' τ Ξ Φ₂ u v = Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := rfl

theorem heis_left (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (a : WO A S) (v : WO S X) :
    heisO ψ A S a (fun u => lastBi o o'' τ Ξ Φ₂ u v) = fun u =>
      Φ₂ (o''.resT S v).1 * heisO ψ V₀ S ((o.resS S).symm (a, 0)) Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := by
  funext u
  simp only [heisO, lastBi_apply]
  have e : (o.resS S).symm (u + a, kap τ S (o''.resT S v).2) =
      (o.resS S).symm (u, kap τ S (o''.resT S v).2) + (o.resS S).symm (a, 0) := by
    rw [← map_add (f := _), Prod.mk_add_mk, add_zero]
  rw [e, GlobalTheory.LastBiTheta.sOH_resS_symm, GlobalTheory.LastBiTheta.sOH_zero_right, add_zero]
  ring

theorem heis_right (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram)
    (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (b : WO S X) (u : WO A S) :
    heisO ψ S X b (lastBi o o'' τ Ξ Φ₂ u) = o''.boxT S (heisO ψ S T (o''.resT S b).1 Φ₂) (fun w =>
      heisO ψ V₀ S ((o.resS S).symm (0, kap τ S (o''.resT S b).2)) Ξ ((o.resS S).symm (u, kap τ S w))) := by
  obtain ⟨kadd, -, -, -, ksympl, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)
  have kH : ∀ w w', symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [ksympl]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_neg]
  show heisO ψ S X b (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))) = _
  rw [o''.heisO_boxT]
  congr 1
  funext w
  have e : (o.resS S).symm (u, kap τ S (w + (o''.resT S b).2)) =
      (o.resS S).symm (u, kap τ S w) + (o.resS S).symm (0, kap τ S (o''.resT S b).2) := by
    rw [kadd, ← map_add (f := _), Prod.mk_add_mk, add_zero]
  simp only [heisO]
  rw [e, GlobalTheory.LastBiTheta.sOH_resS_symm, GlobalTheory.LastBiTheta.sOH_zero_right, zero_add, kH]

theorem slice_left {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C)
    (v : WO S A') : IsThetaFunO ψ A S fun u => C u v := {
  quasi := fun γ u => h.quasiL γ u v
  level := by
    obtain ⟨U, hU, hl⟩ := h.levL
    exact ⟨U, hU, fun a ha h0 => hl a ha h0 v⟩
  cont := h.cont.comp (continuous_id.prodMk continuous_const)
  smooth := fun n L hL h0 u => by
    have := h.smooth n L 0 hL continuous_const h0 (fun _ => Matrix.map_zero _ (map_zero (finPart D))) u v
    simpa using this }

theorem slice_right {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C)
    (u : WO A S) : IsThetaFunO ψ S A' (C u) := {
  quasi := fun γ v => h.quasiR γ u v
  level := by
    obtain ⟨U, hU, hl⟩ := h.levR
    exact ⟨U, hU, fun a ha h0 => hl a ha h0 u⟩
  cont := h.cont.comp (continuous_const.prodMk continuous_id)
  smooth := fun n L hL h0 v => by
    have := h.smooth n 0 L continuous_const hL (fun _ => Matrix.map_zero _ (map_zero (finPart D))) h0 u v
    simpa using this }

theorem isHalf_mul_left {e : AE D} {k m n : ℕ} (P : Mx D k m) {y : Mx D m n} (h : IsHalf e y) : IsHalf e (P * y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, h l j]

theorem isHalf_mul_right {e : AE D} {k m n : ℕ} {y : Mx D k m} (P : Mx D m n) (h : IsHalf e y) : IsHalf e (y * P) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem isHalf_add {e : AE D} {m n : ℕ} {y z : Mx D m n} (hy : IsHalf e y) (hz : IsHalf e z) : IsHalf e (y + z) := by
  intro i j
  rw [Matrix.add_apply, mul_add, hy i j, hz i j]

theorem isHalf_zero (e : AE D) (m n : ℕ) : IsHalf e (0 : Mx D m n) := fun i j => by
  rw [Matrix.zero_apply, mul_zero]

theorem isHalf_smul {e : AE D} {m n : ℕ} (c : AE D) {y : Mx D m n} (h : IsHalf e y) : IsHalf e (c • y) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, h i j]

theorem isHalf_adj {e : AE D} {m n : ℕ} {y : Mx D m n} (h : IsHalf e y) : IsHalf (cA D e) (adj y) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [← map_mul, h j i]

theorem isHalf_kap {e : AE D} {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) {w : WO S L''}
    (h : IsHalf e w) : IsHalf (cA D e) (kap τ S w) := by
  unfold kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  exact isHalf_smul _ (isHalf_mul_left _ (isHalf_mul_right _ (isHalf_adj (isHalf_mul_left _ h))))

theorem cA_cA (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    simp only [cA, sigR]
    simp
    congr 1
    exact star_star e

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hε, ?_⟩
  · rw [cA_cA, mul_comm, h2]
  · rw [cA_cA, add_comm, h3]

theorem isHalf_resS_symm {e : AE D} {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) {a : WO A S} {b : WO L S}
    (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e ((o.resS S).symm (a, b)) := by
  rw [OrthDec.resS_symm_apply]
  exact isHalf_add (isHalf_mul_right _ ha) (isHalf_mul_right _ hb)

theorem isHalf_resT {e : AE D} {X T L'' : HSp D} (o'' : OrthDec X T L'') (S : HSp D) {w : WO S X} (h : IsHalf e w) :
    IsHalf e (o''.resT S w).1 ∧ IsHalf e (o''.resT S w).2 := by
  rw [OrthDec.resT_apply]
  exact ⟨isHalf_mul_left _ h, isHalf_mul_left _ h⟩

theorem smul_latV_mem_latA {S : HSp D} (L : Lat S) (P : Pl D → Prop) {c : D.host.E} (hc : c ∈ D.host.AA)
    {w : Fin S.rank → AE D} (hw : w ∈ latV S L P) : ((1 : AF D.host.F) ⊗ₜ[D.host.F] c : AE D) • w ∈ latA S L P := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hv, a, ha, z, hz, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨α, hα, hv, c, hc, z, hz, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem latA_orth {S A B : HSp D} (o : OrthDec S A B) (L : Lat S) (LA : Lat A) (LB : Lat B) (x : Pl D)
    (hO : OrthAt o L LA LB x) {z : Fin S.rank → AE D} (hz : z ∈ latA S L (· = x)) :
    o.pA *ᵥ z ∈ latA A LA (· = x) ∧ o.pB *ᵥ z ∈ latA B LB (· = x) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hv, a, ha, z, hz, rfl⟩ := hy
    have h0 : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * z i) : Fin S.rank → AE D) ∈ latV S L (· = x) :=
      AddSubgroup.subset_closure ⟨α, hα, hv, 1, Set.mem_singleton _, z, hz, rfl⟩
    have e : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * z i) : Fin S.rank → AE D) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * z i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    obtain ⟨hA, hB⟩ := (hO _).1 h0
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact ⟨smul_latV_mem_latA LA _ ha hA, smul_latV_mem_latA LB _ ha hB⟩
  | zero => simp only [Matrix.mulVec_zero]; exact ⟨zero_mem _, zero_mem _⟩
  | add y y' _ _ h h' => simp only [Matrix.mulVec_add]; exact ⟨add_mem h.1 h'.1, add_mem h.2 h'.2⟩
  | neg y _ h => simp only [Matrix.mulVec_neg]; exact ⟨neg_mem h.1, neg_mem h.2⟩

theorem extLat : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (M : Lat V₀) (LA : Lat A) (LL : Lat L) (LS : Lat S)
    (x : Pl D), IsSelfDualC V₀ M → IsSelfDualC A LA → IsSelfDualC L LL → IsSelfDualC S LS → OrthAt o M LA LL x →
    ∀ (a : WO A S) (b : WO L S), a ∈ latO A S (LA : Set _) (LS : Set _) (· = x) → b ∈ latO L S (LL : Set _) (LS : Set _) (· = x) →
      (o.resS S).symm (a, b) ∈ latO V₀ S (M : Set _) (LS : Set _) (· = x) := by
  intro D V₀ A L S o M LA LL LS x hM hLA hLL hLS hO a b ha hb
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D A S LA LS hLA hLS] at ha
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D L S LL LS hLL hLS] at hb
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ S M LS hM hLS, OrthDec.resS_symm_apply]
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    exact add_mem (sum_mem fun k _ => Ideal.mul_mem_right _ _ (ha.1 i k))
      (sum_mem fun k _ => Ideal.mul_mem_right _ _ (hb.1 i k))
  · obtain ⟨hA, hB⟩ := (hO y).1 hy
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact add_mem (ha.2 _ hA) (hb.2 _ hB)

theorem resLat : ∀ (D : D7) (X T L'' S : HSp D) (o'' : OrthDec X T L'') (LX : Lat X) (LT : Lat T) (LZ : Lat L'') (LS : Lat S)
    (x : Pl D), IsSelfDualC X LX → IsSelfDualC T LT → IsSelfDualC L'' LZ → IsSelfDualC S LS → OrthAt o'' LX LT LZ x →
    ∀ w : WO S X, w ∈ latO S X (LS : Set _) (LX : Set _) (· = x) →
      (o''.resT S w).1 ∈ latO S T (LS : Set _) (LT : Set _) (· = x) ∧ (o''.resT S w).2 ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x) := by
  intro D X T L'' S o'' LX LT LZ LS x hLX hLT hLZ hLS hO w hw
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S X LS LX hLS hLX] at hw
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hLS hLT, GlobalTheory.FinPl.LatMem.mem_latO_iff D S L'' LS LZ hLS hLZ,
    OrthDec.resT_apply]
  refine ⟨⟨fun i j => ?_, fun y hy => ?_⟩, ⟨fun i j => ?_, fun y hy => ?_⟩⟩
  · show (o''.pA * (w : Matrix (Fin X.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) i j ∈ _
    rw [Matrix.mul_apply]; exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hw.1 k j)
  · rw [← Matrix.mulVec_mulVec]; exact (latA_orth o'' LX LT LZ x hO (hw.2 y hy)).1
  · show (o''.pB * (w : Matrix (Fin X.rank) (Fin S.rank) (AE D)) : Matrix (Fin L''.rank) (Fin S.rank) (AE D)) i j ∈ _
    rw [Matrix.mul_apply]; exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hw.1 k j)
  · rw [← Matrix.mulVec_mulVec]; exact (latA_orth o'' LX LT LZ x hO (hw.2 y hy)).2

theorem lastVac : ∀ D : D7, GlobalTheory.FinPl.LastVac D := by
  intro D ψ hψ V₀ A L S X T L'' o o'' τ hL hL'' hτ P M LA LS LX LT hM hLA hLS hLX hLT hP Ξ Φ₂ hΞ hΦ
  have hB := GlobalTheory.LastBiTheta.isBiTheta_lastBi D ψ hψ V₀ A L S X T L'' o o'' τ hτ Ξ Φ₂ hΞ.1 hΦ.1
  obtain ⟨kadd, -, -, -, -, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)
  have mono : ∀ {S' T' : HSp D} (LS' : Lat S') (LT' : Lat T') (x : Pl D), P x → ∀ w,
      w ∈ latO S' T' (LS' : Set _) (LT' : Set _) (· = x) → w ∈ latO S' T' (LS' : Set _) (LT' : Set _) P :=
    fun LS' LT' x hx w hw => GlobalTheory.VacLoc.latO_mono _ _ _ _ (fun v hv => hv ▸ hx) hw
  refine ⟨fun v => ⟨slice_left hB v, GlobalTheory.VacLoc.latVac_of_places ψ A S LA LS P _ (slice_left hB v) fun x hx => ?_⟩,
    fun u => ⟨slice_right hB u,
      GlobalTheory.VacLoc.latVac_of_places ψ S X LS LX P _ (slice_right hB u) fun x hx => ?_⟩⟩
  · obtain ⟨-, LL, LZ, hLL, hLZ, hOM, -, -⟩ := hP x hx
    refine ⟨slice_left hB v, fun a ha => ?_, fun e he a ha hh => ?_⟩
    · have hm := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM a 0 ha (zero_mem _))
      have e2 : (o.resS S).symm (2 • a, 0) = 2 • (o.resS S).symm (a, 0) := by
        simp only [two_nsmul]
        rw [← map_add (f := _), Prod.mk_add_mk, add_zero]
      rw [heis_left, e2, hΞ.2.1 _ hm]
      rfl
    · have hm := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM a 0 ha (zero_mem _))
      rw [heis_left, hΞ.2.2 e he _ hm (isHalf_resS_symm o S hh (isHalf_zero e _ _))]
      rfl
  · obtain ⟨-, LL, LZ, hLL, hLZ, hOM, hOX, hk⟩ := hP x hx
    refine ⟨slice_right hB u, fun b hb => ?_, fun e he b hb hh => ?_⟩
    · obtain ⟨h1, h2⟩ := resLat D X T L'' S o'' LX LT LZ LS x hLX hLT hLZ hLS hOX b hb
      have hm1 := mono LS LT x hx _ h1
      have hm2 := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM 0 _ (zero_mem _) (hk _ h2))
      have e1 : (o''.resT S (2 • b)).1 = 2 • (o''.resT S b).1 := by
        simp only [two_nsmul, map_add (f := _), Prod.fst_add]
      have e2 : (o.resS S).symm (0, kap τ S (o''.resT S (2 • b)).2) = 2 • (o.resS S).symm (0, kap τ S (o''.resT S b).2) := by
        simp only [two_nsmul]
        rw [map_add (f := _), Prod.snd_add, kadd, ← map_add (f := _), Prod.mk_add_mk, add_zero]
      rw [heis_right ψ o o'' τ hτ, e1, e2, hΦ.2.1 _ hm1, hΞ.2.1 _ hm2]
      rfl
    · obtain ⟨h1, h2⟩ := resLat D X T L'' S o'' LX LT LZ LS x hLX hLT hLZ hLS hOX b hb
      have hm1 := mono LS LT x hx _ h1
      have hm2 := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM 0 _ (zero_mem _) (hk _ h2))
      obtain ⟨he1, he2⟩ := isHalf_resT o'' S hh
      rw [heis_right ψ o o'' τ hτ, hΦ.2.2 e he _ hm1 he1,
        hΞ.2.2 (cA D e) (isSplitIdem_cA he) _ hm2 (isHalf_resS_symm o S (isHalf_zero _ _ _) (isHalf_kap τ S he2))]
      rfl

end GlobalTheory.LastVacPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumOfVacuaIsVacuumBothStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSawDatum_of_vacua_is_vacuum_both : ∀ D : D7, GlobalTheory.FinPl.LastVac D := by
  first | exact @GlobalTheory.LastVacPf.lastVac | exact GlobalTheory.LastVacPf.lastVac | (intros; apply GlobalTheory.LastVacPf.lastVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainDatumLawsUnderLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainDatumLawsUnderLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ChainTw.TwLaw
variable {D : D7}

theorem levChi_flag (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) :
    Lev.levChi V β (Lev.flagL (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B)) κ =
      Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B) κ := by
  unfold Lev.levChi levFn
  congr 3
  simp only [Lev.flagL, Lev.withP, Lev.datY, LevelP.full, LevelP.triv, if_true]
  exact (Lev.subgroupCharExtension_one_apply _ _).trans (Lev.subgroupCharExtension_one_apply _ _).symm

theorem lift_one_of_mem (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank)
    (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (κ : GA D V) (hκ : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B)) :
    Lev.IsLevelLift V β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Lev.Frm.B) 1 κ := by
  refine ⟨(Subgroup.mem_inf.1 hκ).1, hκ.2.1, ?_⟩
  have h2 := hκ.2.2
  simp only [Lev.datY, LevelP.triv, if_true] at h2
  exact Subgroup.mem_bot.1 h2

theorem lift_one_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.IsLevelLift V β L 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem levChi_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    Lev.levChi V β L 1 = 1 := by
  unfold Lev.levChi
  rw [map_one]
  have : levFn β L 1 = 1 := (levChar D.sp.cm V.gram β L).map_one
  rw [this, Units.val_one]


set_option maxHeartbeats 1000000 in
open Classical in
theorem vecLawQ (D : D7) (c : Com D) (w : Twist D) (hw : w.Is c) (k : ℕ) (hk : k < D.R.m) (s s' : PiLocalization₂ D)
    (hs : IsStage c w k s) (hs' : IsStage c w (k + 1) s') (p : Step c s s') (hp : IsStep w (k + 1) p) :
    VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) (Lev.levG s'.V s'.β s'.L)
      (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  obtain ⟨hr, hL, hfs⟩ := hs
  obtain ⟨hr', hL', hfs'⟩ := hs'
  obtain ⟨f₀, hv⟩ := hp.vec
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.ChainOnto.levRes_step D c hw.com k hk
  rw [hw.union] at hres uS uT
  have hG : ∀ PP ∈ w.Pg, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (w.chi (k + 1) PP)⁻¹ ∧
      GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (w.chi (k + 1) PP)⁻¹ := fun PP hP => by
    rw [← hw.chiPg (k + 1) PP hP]; exact hres PP (Finset.mem_union_left _ hP)
  have hQ : ∀ PP ∈ w.Q, GlobalTheory.StepLaw.ResAt (c.chS (k + 1)) PP (w.ξ PP) ∧
      GlobalTheory.StepLaw.ResAt (c.chT (k + 1)) PP (w.ξ PP) := fun PP hP => by
    have := hres PP (Finset.mem_union_right _ hP)
    rwa [hw.chiQ (k + 1) PP hP, inv_inv] at this
  rw [hL] at hv
  have ea : s.V.rank = D.R.r + k * D.R.t := hfs.rank
  have eb : s'.V.rank = D.R.r + (k + 1) * D.R.t := hfs'.rank
  have law := fun {g0 : G0 w.Pg D.R.r} {g : GA D s.V} {h : GA D s'.V} =>
    @GlobalTheory.StepVecLaw.step_law D c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) p.ω (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β f₀ p.f
      hp.weil hfs.sigOK hfs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M)
      hfs.selfDual hfs'.selfDual hfs.frame hfs'.frame D.R.r D.R.t k hr hr' ea eb w.Pg w.Q hw.disj w.chi w.ξ hv hG hQ uS uT g0 g h
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · rw [hL] at hκ ⊢
    have h1 := law (lift_one_of_mem _ _ _ _ _ _ _ _ _ _ κ hκ) (lift_one_one _ _ _)
    rw [levChi_flag, levChi_flag, levChi_one, inv_one, one_smul] at h1
    have hne : Lev.levChi s.V s.β (Lev.datY s.V.rank D.R.r D.R.t k hr w.Pg w.Q (LevelP.triv w.Pg D.R.r ℂ) w.chi w.ξ Lev.Frm.B) κ ≠ 0 := by
      unfold Lev.levChi; exact Units.ne_zero _
    exact (inv_smul_eq_iff₀ hne).1 h1
  · rw [hL'] at hκ ⊢
    have h1 := law (lift_one_one _ _ _) (lift_one_of_mem _ _ _ _ _ _ _ _ _ _ κ hκ)
    rw [levChi_flag, levChi_flag, levChi_one, inv_one, one_smul] at h1
    exact h1

theorem levelLawQ : ∀ D : D7, LevelLawQ D := by
  intro D _ c w hw k hk s s' hs hs' p hp φ
  obtain ⟨h1, h2⟩ := vecLawQ D c w hw k hk s s' hs hs' p hp
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_⟩
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil _ _ _ _ p.f hp.theta
      κ (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ (h1 κ hκ) φ
  · exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil _ _ _ _ p.f hp.theta
      1 (one_mem _) κ (Subgroup.mem_inf.1 hκ).1 _ (h2 κ hκ) φ

end GlobalTheory.ChainTw.TwLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainDatumLawsUnderLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedChain_datum_laws_under_levels : ∀ D : D7, LevelLawQ D := by
  first | exact @GlobalTheory.ChainTw.TwLaw.levelLawQ | exact GlobalTheory.ChainTw.TwLaw.levelLawQ | (intros; apply GlobalTheory.ChainTw.TwLaw.levelLawQ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearMapVaryPureTensorFactorSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearMapVaryPureTensorFactorSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.VarySplitFactor.exists_linearMap_pure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (Φ₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))), ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → x (.inl v) = Tm (onHalf φ S T BS BT e Φ₀.1) → ∃ T₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →ₗ[ℂ] (WO S T → ℂ), T₀ Φ₀ = f ∧ (∀ u, ∃ x' : Place D → WO S T → ℂ, (∀ p, p ≠ .inl v → x' p = x p) ∧ x' (.inl v) = Tm (onHalf φ S T BS BT e u.1) ∧ IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (T₀ u)) ∧ ∀ g h, gAt S (.inl v) g = g → gAt T (.inl v) h = h → ∀ a b, IsDetAt e S g a → IsDetAt e T h b → ∀ u u' : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)), u'.1 = linOm v (grpCo φ S BS g) (grpCo φ T BT h) u.1 → om (g, h) (T₀ u) = ((splitFacO χS χT a b : Circle) : ℂ) • T₀ u' := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW _hθ hB hC x f hx v φ e he BS BT Φ₀ Tm hT hxv
  classical
  have hcoord := GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  have hsplit := GlobalTheory.SplitCoordModel.bijOn_and_om_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕
    hW hB hC v e e he.1 he.2.1 (Or.inl rfl) T.rank S.rank (mapCo φ S T BS BT) hcoord.1 Tm hT
  have honHalf : ∀ Φ, onHalf φ S T BS BT e Φ = pull e (mapCo φ S T BS BT) Φ := fun Φ => rfl
  let xf : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →
      Place D → WO S T → ℂ :=
    fun u => Function.update x (.inl v) (Tm (onHalf φ S T BS BT e u.1))
  have hres : ∀ u, IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (xf u) := by
    intro u
    refine ⟨fun p => ?_, ?_⟩
    · by_cases hp : p = .inl v
      · subst hp
        simp only [xf, Function.update_self]
        rw [honHalf]
        exact hsplit.1.mapsTo u.2
      · simp only [xf, Function.update_of_ne hp]
        exact hx.1.1 p
    · apply (hx.1.2.union (Set.finite_singleton (Sum.inl v : Place D))).subset
      intro p hp
      by_cases h : p = .inl v
      · exact Or.inr h
      · left
        simpa [xf, Function.update_of_ne h] using hp
  have hEU := fun u => GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕
    hB hC (xf u) (hres u)
  let F := fun u => (hEU u).exists.choose
  have hF : ∀ u, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (xf u) (F u) :=
    fun u => (hEU u).exists.choose_spec
  have huniq : ∀ y f1 f2, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f1 →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f2 → f1 = f2 := fun y f1 f2 h1 h2 =>
    (GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC y h1.1).unique
      h1 h2
  have hlin := (GlobalTheory.PureLinear.isPure_linear_and_dRho D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC).1
  have hscale : ∀ (y z : Place D → WO S T → ℂ) (g : WO S T → ℂ) (q : Place D) (c : ℂ),
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → z p = y p) → z q = c • y q →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • g) := by
    intro y z g q c hy hz hzq
    have := hlin y y z g g q (c - 1) hy hy (fun _ _ => rfl) hz
      (by rw [hzq, sub_smul, one_smul, sub_add_cancel])
    rwa [sub_smul, one_smul, sub_add_cancel] at this
  have hOnAdd : ∀ (Φ Ψ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) → ℂ),
      onHalf φ S T BS BT e (Φ + Ψ) = onHalf φ S T BS BT e Φ + onHalf φ S T BS BT e Ψ := by
    intro Φ Ψ
    funext t
    simp only [onHalf, Pi.add_apply]
    split_ifs <;> simp
  have hOnSmul : ∀ (c : ℂ) (Φ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) → ℂ),
      onHalf φ S T BS BT e (c • Φ) = c • onHalf φ S T BS BT e Φ := by
    intro c Φ
    funext t
    simp only [onHalf, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  let T₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →ₗ[ℂ]
      (WO S T → ℂ) :=
    { toFun := F
      map_add' := by
        intro u u'
        have hz := hlin (xf u) (xf u') (xf (u + u')) (F u) (F u') (.inl v) 1 (hF u) (hF u')
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (by
            simp only [xf, Function.update_self, Submodule.coe_add]
            rw [hOnAdd, map_add (f := _), one_smul])
        rw [one_smul] at hz
        exact huniq _ _ _ (hF (u + u')) hz
      map_smul' := by
        intro c u
        have hz := hscale (xf u) (xf (c • u)) (F u) (.inl v) c (hF u)
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (by
            simp only [xf, Function.update_self, Submodule.coe_smul]
            rw [hOnSmul, map_smul])
        exact huniq _ _ _ (hF (c • u)) hz }
  have hT₀ : ∀ u, T₀ u = F u := fun u => rfl
  refine ⟨T₀, ?_, fun u => ⟨xf u, fun p hp => by simp only [xf, Function.update_of_ne hp],
    by simp only [xf, Function.update_self], hF u⟩, ?_⟩
  · rw [hT₀]
    have hxx : xf Φ₀ = x := by
      simp only [xf]
      rw [← hxv]
      exact Function.update_eq_self _ _
    exact huniq _ _ _ (hF Φ₀) (hxx ▸ hx)
  · intro g h hg hh a b ha hb u u' hu'
    have laws := GlobalTheory.PlaceComponent.gAt_laws D
    have hgp : ∀ p, p ≠ Sum.inl v → gAt S p g = 1 := fun p hp => by
      rw [← hg]; exact ((laws.1 S (.inl v) g).2.2 p hp)
    have hhp : ∀ p, p ≠ Sum.inl v → gAt T p h = 1 := fun p hp => by
      rw [← hh]; exact ((laws.1 T (.inl v) h).2.2 p hp)
    have hsupp : ∀ (V : HSp D) (k : GA D V), gAt V (.inl v) k = k → SuppAt e V k := by
      intro V k hk i j
      have hm := (laws.1 V (.inl v) k).1
      rw [hk] at hm
      have key : Formalism.L2.Theta.mt V k - 1 =
          idem D (Sum.inl v) • (Formalism.L2.Theta.mt V k - 1) := by
        conv_lhs => rw [hm]
        rw [smul_sub, sub_smul, one_smul]
        abel
      rw [he.2.1]
      have := congrFun (congrFun key i) j
      rw [Matrix.smul_apply, smul_eq_mul] at this
      exact this.symm
    have hom := GlobalTheory.PlaceTensor.PureOm.isPure_om D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hC
      (xf u) (F u) (hF u) g h
    have hact := hsplit.2 g h (hsupp S g hg) (hsupp T h hh) a b ha hb
      (grpCo φ S BS g) (grpCo φ T BT h) (hcoord.2 g h) u.1 u.2
    have hz := hscale (xf u') (fun p => om (gAt S p g, gAt T p h) (xf u p)) (F u') (.inl v)
      ((splitFacO χS χT a b : Circle) : ℂ) (hF u')
      (fun p hp => by
        simp only [xf, Function.update_of_ne hp, hgp p hp, hhp p hp]
        have h11 : ((1 : GA D S), (1 : GA D T)) = 1 := rfl
        rw [h11, map_one]; rfl)
      (by
        simp only [xf, Function.update_self, hg, hh]
        rw [honHalf, hact, honHalf, hu'])
    exact huniq _ _ _ hom hz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearMapVaryPureTensorFactorSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearMap_vary_pureTensor_factor_split_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (Φ₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))), ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → x (.inl v) = Tm (onHalf φ S T BS BT e Φ₀.1) → ∃ T₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →ₗ[ℂ] (WO S T → ℂ), T₀ Φ₀ = f ∧ (∀ u, ∃ x' : Place D → WO S T → ℂ, (∀ p, p ≠ .inl v → x' p = x p) ∧ x' (.inl v) = Tm (onHalf φ S T BS BT e u.1) ∧ IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (T₀ u)) ∧ ∀ g h, gAt S (.inl v) g = g → gAt T (.inl v) h = h → ∀ a b, IsDetAt e S g a → IsDetAt e T h b → ∀ u u' : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)), u'.1 = linOm v (grpCo φ S BS g) (grpCo φ T BT h) u.1 → om (g, h) (T₀ u) = ((splitFacO χS χT a b : Circle) : ℂ) • T₀ u' := by
  first | exact @GlobalTheory.VarySplitFactor.exists_linearMap_pure | exact GlobalTheory.VarySplitFactor.exists_linearMap_pure | (intros; apply GlobalTheory.VarySplitFactor.exists_linearMap_pure <;> assumption)
end
end
