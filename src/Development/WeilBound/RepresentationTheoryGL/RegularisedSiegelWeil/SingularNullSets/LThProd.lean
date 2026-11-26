module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChange

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThProdA
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

open PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.ThTot GlobalTheory.CompanionTheory.ThTot.OneRow

namespace PositivityTheory.Rg.Rsw.L.LThProd

variable {D : D7}

theorem oneTh (hW : L.WMaj) {p : ℕ} (μ : Measure (Mx D 1 p)) (𝓕 : Set (Mx D 1 p)) (hμ : IsCovolOne (ratMx D 1 p) μ 𝓕)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D 1) (hdet : b₀.1.det ≠ 0)
    {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hr : ResEta D χ 1) {θ : InfFam D} (hθ : IsInfFam θ)
    (η : Mx D 1 p → ℂ) (hη : η ∈ schwartzA θ 1 p) :
    ∃ Ω, IsTh ψ χ θ b₀ μ Ω ∧ Ω 1 = η := by
  obtain ⟨c, hc0, hc⟩ := exists_base b₀ hdet
  obtain ⟨ψ₀, h₀, lam, hlam0, hlam⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hne : lam * c ≠ 0 := mul_ne_zero hlam0 hc0
  obtain ⟨hψ₁, -⟩ := exists_par ψ₀ h₀ θ hθ (lam * c) hne
  have hs : ∀ t, shift ψ₀ (lam * c) t = ψ (algebraMap D.host.F (AF D.host.F) c * t) := by
    intro t
    rw [hlam]
    simp [shift, AddChar.mulShift_apply, map_mul, mul_assoc]
  obtain ⟨ω, hω⟩ := GlobalTheory.StdUnn.Inhab.weil_exists D p (V1 D) ψ₀ h₀ (lam * c) hne χ hχ hr θ hθ μ 𝓕 hμ
  let Φ : schwartzA θ (V1 D).rank p := ⟨η, hη⟩
  have hM := hW D p (V1 D) _ hψ₁ χ hχ hr θ hθ μ ⟨𝓕, hμ⟩ ω hω Φ
  have e : ∀ g h : G D p, ω (g * h) Φ = ω g (ω h Φ) := fun g h => by rw [map_mul]; rfl
  refine ⟨fun h => (ω h Φ).1,
    { mem := fun h => (ω h Φ).2
      cont := hM.1
      maj := hM.2
      levi := by
        intro g a hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e]
        exact hω.levi g a hg _ y
      unip := by
        intro g b hg h y
        show (ω (g * h) Φ).1 y = _
        rw [e, hω.unip g b hg _ y, hs, pr_eq b₀ c hc, Matrix.mul_smul, Matrix.trace_smul, halfTr_smul]
      weyl := by
        intro g hg h x
        show (ω (g * h) Φ).1 x = _
        rw [e, hω.weyl g hg _ x]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show _ * shift ψ₀ (lam * c) _ = _ * ψ _
        rw [hs, pr_eq b₀ c hc x y, Matrix.trace_smul, trA_smul] }, ?_⟩
  show (ω 1 Φ).1 = η
  rw [map_one]
  rfl

theorem hecke_mul_inv {χ ε : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hε : IsHeckeChar D ε) :
    IsHeckeChar D (χ * ε⁻¹) := by
  have e : ⇑(χ * ε⁻¹) = fun x => χ x * (ε x)⁻¹ := by
    funext x
    simp
  refine ⟨?_, fun x => ?_⟩
  · rw [e]
    exact hχ.1.mul hε.1.inv
  · rw [e]
    simp only [hχ.2 x, hε.2 x, inv_one, mul_one]

theorem resEta_mul_inv {χ ε : (AE D)ˣ →* Circle} {k : ℕ} (hχ : ResEta D χ (k + 1)) (hε : ResEta D ε 1) :
    ResEta D (χ * ε⁻¹) k := by
  refine ⟨hχ.1, fun η hη a => ?_⟩
  have h1 := hχ.2 η hη a
  have h2 := hε.2 η hη a
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, pow_succ, pow_one, mul_inv_cancel_right]

def topH {m : ℕ} (b : HermE D (m + 1)) : HermE D m :=
  ⟨b.1.submatrix Fin.castSucc Fin.castSucc, by
    funext i j
    exact congrFun (congrFun b.2 (Fin.castSucc i)) (Fin.castSucc j)⟩

def botH {m : ℕ} (b : HermE D (m + 1)) : HermE D 1 :=
  ⟨b.1.submatrix (fun _ => Fin.last m) (fun _ => Fin.last m), by
    funext i j
    exact congrFun (congrFun b.2 (Fin.last m)) (Fin.last m)⟩

theorem diag_ne {m : ℕ} {b : HermE D m} (h : IsDiagInv b) (i : Fin m) : b.1 i i ≠ 0 := by
  have e : Matrix.diagonal (Matrix.diag b.1) = b.1 := h.1.diagonal_diag
  have hd := h.2
  rw [← e, Matrix.det_diagonal] at hd
  exact (Finset.prod_ne_zero_iff.1 hd) i (Finset.mem_univ _)

theorem topH_diag {m : ℕ} {b : HermE D (m + 1)} (h : IsDiagInv b) : IsDiagInv (topH b) := by
  refine ⟨h.1.submatrix (Fin.castSucc_injective m), ?_⟩
  have e : Matrix.diagonal (Matrix.diag (topH b).1) = (topH b).1 := (h.1.submatrix (Fin.castSucc_injective m)).diagonal_diag
  rw [← e, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => diag_ne h _

theorem botH_det {m : ℕ} {b : HermE D (m + 1)} (h : IsDiagInv b) : (botH b).1.det ≠ 0 := by
  rw [Matrix.det_fin_one]
  exact diag_ne h (Fin.last m)

theorem natAdd_one {m : ℕ} (a : Fin 1) : Fin.natAdd m a = Fin.last m := by
  ext
  simp [Fin.fin_one_eq_zero a]

theorem diagonal_hermitian_is_block {m : ℕ} {b : HermE D (m + 1)} (h : IsDiagInv b) : IsBlockSL2Embedding (r := m) (s := 1) b (topH b) (botH b) := by
  refine ⟨fun i j => rfl, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · show b.1 _ _ = b.1 _ _
    rw [natAdd_one, natAdd_one]
  · refine h.1 ?_
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  · refine h.1 ?_
    intro e
    have := congrArg Fin.val e
    simp at this
    omega

end PositivityTheory.Rg.Rsw.L.LThProd

end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

open PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.ThTot

namespace PositivityTheory.Rg.Rsw.L.LThProd

variable {D : D7}

theorem rowB_eq {m p : ℕ} (y : Mx D (m + 1) p) : rowB (r := m) (s := 1) y = y.submatrix (fun _ => Fin.last m) id := by
  funext a j
  show y (Fin.natAdd m a) j = y (Fin.last m) j
  rw [natAdd_one]

theorem succ (hW : L.WMaj) {p : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D}
    (hθ : IsInfFam θ) : ∀ (k : ℕ) (b₀ : HermE D (k + 1)), IsDiagInv b₀ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ →
    ResEta D χ (k + 1) → ∀ (μ : Measure (Mx D (k + 1) p)) (𝓕 : Set (Mx D (k + 1) p)), IsCovolOne (ratMx D (k + 1) p) μ 𝓕 →
    ∀ η : Fin (k + 1) → Mx D 1 p → ℂ, (∀ i, η i ∈ schwartzA θ 1 p) →
    ∃ Ω, IsTh ψ χ θ b₀ μ Ω ∧ ∀ y, Ω 1 y = ∏ i, η i (y.submatrix (fun _ => i) id) := by
  intro k
  induction k with
  | zero =>
    intro b₀ hb χ hχ hr μ 𝓕 hμ η hη
    obtain ⟨Ω, hT, h1⟩ := oneTh hW μ 𝓕 hμ hψ b₀ hb.2 hχ hr hθ (η 0) (hη 0)
    refine ⟨Ω, hT, fun y => ?_⟩
    rw [Fin.prod_univ_one, h1]
    congr 1
    funext a j
    rw [Fin.fin_one_eq_zero a]
    rfl
  | succ k ih =>
    intro b₀ hb χ hχ hr μ 𝓕 hμ η hη
    obtain ⟨ε, hε, hεr⟩ := GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta D 1
    obtain ⟨μr, 𝓕r, hμr⟩ := GlobalTheory.MixModel.exists_isCovolOne D (k + 1) p
    obtain ⟨μs, 𝓕s, hμs⟩ := GlobalTheory.MixModel.exists_isCovolOne D 1 p
    obtain ⟨Ωr, hTr, hr1⟩ := ih (topH b₀) (topH_diag hb) (χ * ε⁻¹) (hecke_mul_inv hχ hε)
      (resEta_mul_inv hr (by simpa using hεr)) μr 𝓕r hμr (fun i => η (Fin.castSucc i)) fun i => hη _
    obtain ⟨Ωs, hTs, hs1⟩ := oneTh hW μs 𝓕s hμs hψ (botH b₀) (botH_det hb) hε (by simpa using hεr) hθ
      (η (Fin.last (k + 1))) (hη _)
    have hP := GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor D (k + 1) 1 p μr 𝓕r μs 𝓕s
      hμr hμs ψ hψ (χ * ε⁻¹) ε θ hθ (topH b₀) (botH b₀) b₀ (diagonal_hermitian_is_block hb) Ωr Ωs hTr hTs
    rw [inv_mul_cancel_right,
      ← GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas D (k + 1) 1 p μr 𝓕r μs 𝓕s μ 𝓕 hμr hμs hμ] at hP
    refine ⟨_, hP, fun y => ?_⟩
    show Ωr 1 (rowT y) * Ωs 1 (rowB y) = _
    rw [hr1, hs1, rowB_eq]
    conv_rhs => rw [Fin.prod_univ_castSucc]
    rfl

end PositivityTheory.Rg.Rsw.L.LThProd

namespace PositivityTheory.Rg.Rsw.L

theorem thProd (hW : WMaj) : ThProd := by
  intro D ρ p m ψ hψ b₀ hb χ hχ hr hρ θ hθ η hη
  obtain ⟨k, rfl⟩ : ∃ k, ρ = k + 1 := ⟨ρ - 1, by omega⟩
  exact LThProd.succ hW hψ hθ k b₀ hb χ hχ hr m.μ m.𝓕 m.hμ η hη

end PositivityTheory.Rg.Rsw.L

end
