module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsHeisenbergGroup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsHeisenbergGroup
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem rat_maps_mem_GF : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn),
    (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧
    (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.nzx 0 (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧
    ∀ z ∈ ratHerm D ρ, M.nzx z 0 ∈ GF D n := by
  intro D n ρ p hn M
  refine ⟨fun ξ => GlobalTheory.CompanionTheory.PcB.sh_rat M ξ, fun ξ => GlobalTheory.CompanionTheory.PcB.nzx_rat M 0 (zero_mem _) ξ, fun z hz => ?_⟩
  have h := GlobalTheory.CompanionTheory.PcB.nzx_rat M z hz 0
  rwa [GlobalTheory.CompanionTheory.PcB.rat_zero'] at h

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalPointsHeisenbergGroupStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_points_heisenberg_group : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn), (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧ (∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, M.nzx 0 (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n) ∧ ∀ z ∈ ratHerm D ρ, M.nzx z 0 ∈ GF D n := by
  first | exact @GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF | exact GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF | (intros; apply GlobalTheory.CompanionTheory.FJE.rat_maps_mem_GF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientHeisenbergExpansion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCoefficientEquivariance
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCoefficientEquivariance
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ZcShift


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem zc_shift : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (c : hermA D ρ) (h : G D n), zc M m ψ b₀ F (M.nzx c 0 * h) = chz ψ b₀ c * zc M m ψ b₀ F h := by
  intro D n ρ p hn M m ψ hψ b₀ F hF c h
  obtain ⟨hadd, hnorm, hrat, -⟩ := GlobalTheory.T.centre_character_properties ψ hψ b₀
  obtain ⟨hl, hFD, -⟩ := m.hz
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : DiscreteTopology (ratHerm D ρ) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  haveI : Countable (ratHerm D ρ) := countable_of_Lindelof_of_discrete
  have hnz : ∀ z z' : hermA D ρ, M.nzx z 0 * M.nzx z' 0 = M.nzx (z + z') 0 := fun z z' => by
    have := GlobalTheory.T.unipotent_heisenberg_mul M z z' 0 0
    rwa [add_zero] at this
  have hconj : conj (chz ψ b₀ c) * chz ψ b₀ c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm c]
    simp
  set u : hermA D ρ → ℂ := fun z => F (M.nzx z 0 * h) * conj (chz ψ b₀ z) with hu
  have hper : ∀ γ ∈ ratHerm D ρ, ∀ x, u (γ + x) = u x := by
    intro γ hγ x
    simp only [hu]
    rw [← hnz, mul_assoc, hF _ ((GlobalTheory.T.rational_points_heisenberg_group M).2.2 γ hγ), hadd, hrat γ hγ, one_mul]
  have hpt : ∀ z : hermA D ρ, F (M.nzx z 0 * (M.nzx c 0 * h)) * conj (chz ψ b₀ z) = chz ψ b₀ c * u (z + c) := by
    intro z
    simp only [hu]
    rw [← mul_assoc, hnz, hadd, map_mul]
    linear_combination (-(F (M.nzx (z + c) 0 * h) * conj (chz ψ b₀ z))) * hconj
  unfold zc
  simp only [hpt]
  rw [integral_const_mul]
  congr 1
  exact GlobalTheory.CompanionTheory.ConstN.setIntegral_add_right (ratHerm D ρ) m.lz hFD u hper c

end GlobalTheory.CompanionTheory.ZcShift

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCoefficientEquivarianceStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_coefficient_equivariance : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (c : hermA D ρ) (h : G D n), zc M m ψ b₀ F (M.nzx c 0 * h) = chz ψ b₀ c * zc M m ψ b₀ F h := by
  first | exact @GlobalTheory.CompanionTheory.ZcShift.zc_shift | exact GlobalTheory.CompanionTheory.ZcShift.zc_shift | (intros; apply GlobalTheory.CompanionTheory.ZcShift.zc_shift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientHeisenbergExpansion
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.PcShear

theorem jc_zero {D : D7} {ρ p : ℕ} (y : Mx D ρ p) : GlobalTheory.CompanionTheory.FJE.jc y 0 = 0 := by
  apply Subtype.ext
  have h : adj (0 : Mx D ρ p) = 0 := by
    ext i j
    simp [adj]
  show (HMul.hMul y (adj (0 : Mx D ρ p)) : Mx D ρ ρ) + (HMul.hMul (0 : Mx D ρ p) (adj y) : Mx D ρ ρ) = _
  rw [h]
  simp

theorem chz_neg {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (z : hermA D ρ) : chz ψ b₀ (-z) = conj (chz ψ b₀ z) := by
  obtain ⟨hadd, hnorm, -, -⟩ := GlobalTheory.T.centre_character_properties ψ hψ b₀
  have h0 : chz ψ b₀ (0 : hermA D ρ) = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have hne : chz ψ b₀ (0 : hermA D ρ) ≠ 0 := by
      intro h'
      have := hnorm 0
      rw [h'] at this
      simp at this
    exact (mul_eq_left₀ hne).1 h.symm
  have h1 : chz ψ b₀ z * chz ψ b₀ (-z) = 1 := by
    rw [← hadd, add_neg_cancel, h0]
  have h2 : chz ψ b₀ z * conj (chz ψ b₀ z) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    simp
  have hne : chz ψ b₀ z ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem zc_sh {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (F : G D n → ℂ) (hF : LeftInv (GF D n) F)
    (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (k : G D n) :
    zc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * k) = zc M m ψ b₀ F k := by
  unfold zc
  congr 1
  funext z
  have hc : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * M.nzx z 0 = M.nzx z 0 * M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) := by
    have := GlobalTheory.T.shift_conj_heisenberg M (GlobalTheory.CompanionTheory.FJE.rt ξ) z 0
    rwa [jc_zero, add_zero] at this
  have hr : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) ∈ GF D n := (GlobalTheory.T.rational_points_heisenberg_group M).1 ξ
  rw [← mul_assoc, ← hc, mul_assoc, hF _ hr]

theorem zc_at {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (F : G D n → ℂ)
    (hF : LeftInv (GF D n) F) (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n) (x : Mx D ρ p) :
    zc M m ψ b₀ F (M.nzx 0 x * (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h)) =
      conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) := by
  set c : hermA D ρ := -GlobalTheory.CompanionTheory.FJE.jc (GlobalTheory.CompanionTheory.FJE.rt ξ) x with hc
  have h1 : M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * M.nzx c x = M.nzx 0 x * M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) := by
    have := GlobalTheory.T.shift_conj_heisenberg M (GlobalTheory.CompanionTheory.FJE.rt ξ) c x
    rwa [hc, neg_add_cancel] at this
  have h2 : M.nzx c x = M.nzx c 0 * M.nzx 0 x := by
    rw [GlobalTheory.CompanionTheory.NzxAdd.nzx_add, add_zero, zero_add]
  have h3 : M.nzx 0 x * (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) =
      M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * (M.nzx c 0 * (M.nzx 0 x * h)) := by
    rw [← mul_assoc, ← h1, h2]
    simp only [mul_assoc]
  rw [h3, zc_sh M m ψ b₀ F hF, GlobalTheory.T.centre_coefficient_equivariance M m ψ hψ b₀ F hF, hc, chz_neg ψ hψ, GlobalTheory.T.centre_character_commutator]

theorem pc_sh : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n), pc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) = ∫ x in m.𝓕, conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) ∂m.μ := by
  intro D n ρ p hn M m ψ hψ b₀ F hF ξ h
  unfold PositivityTheory.Rg.Rsw.pc
  congr 1
  funext x
  exact zc_at M m ψ hψ b₀ F hF ξ h x

end GlobalTheory.CompanionTheory.FJE.PcShear
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientHeisenbergExpansionStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coefficient_heisenberg_expansion : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (h : G D n), pc M m ψ b₀ F (M.sh (GlobalTheory.CompanionTheory.FJE.rt ξ) * h) = ∫ x in m.𝓕, conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ)) * zc M m ψ b₀ F (M.nzx 0 x * h) ∂m.μ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.PcShear.pc_sh | exact GlobalTheory.CompanionTheory.FJE.PcShear.pc_sh | (intros; apply GlobalTheory.CompanionTheory.FJE.PcShear.pc_sh <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiExpansionBounded
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem fold_abs {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) [SFinite μ] (S : Set X) (hS : μ S = 1)
    (Z T : X × X → ℂ) (hZ : StronglyMeasurable Z) (hT : StronglyMeasurable T) (B B₂ : ℝ)
    (hB : ∀ v, ‖Z v‖ ≤ B) (hB₂ : ∀ v, ‖T v‖ ≤ B₂)
    (c a : ι → X → ℂ) (hc : ∀ i, StronglyMeasurable (c i)) (hc1 : ∀ i x, ‖c i x‖ = 1)
    (ha : ∀ y, Summable fun i => ‖a i y‖) (hTs : ∀ y x, T (y, x) = ∑' i, c i x * a i y) :
    ∫ y in S, ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y ∂μ = ∫ v in S ×ˢ S, Z v * T v ∂(μ.prod μ) := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simp [hS]⟩
  have hZs : ∀ y, StronglyMeasurable fun x => Z (y, x) := fun y => hZ.comp_measurable measurable_prodMk_left
  have inner : ∀ y, ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y = ∫ x in S, Z (y, x) * T (y, x) ∂μ := by
    intro y
    have hint : ∀ i, Integrable (fun x => c i x * Z (y, x) * a i y) (μ.restrict S) := by
      intro i
      refine Integrable.of_bound ((((hc i).mul (hZs y)).mul stronglyMeasurable_const).aestronglyMeasurable)
        (B * ‖a i y‖) (ae_of_all _ fun x => ?_)
      rw [norm_mul, norm_mul, hc1, one_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    have hsum : Summable fun i => ∫ x in S, ‖c i x * Z (y, x) * a i y‖ ∂μ := by
      have h : ∀ i, ∫ x in S, ‖c i x * Z (y, x) * a i y‖ ∂μ = (∫ x in S, ‖Z (y, x)‖ ∂μ) * ‖a i y‖ := by
        intro i
        simp only [norm_mul, hc1, one_mul]
        exact integral_mul_const _ _
      simp only [h]
      exact (ha y).mul_left _
    have h1 := integral_tsum_of_summable_integral_norm hint hsum
    calc ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y
        = ∑' i, ∫ x in S, c i x * Z (y, x) * a i y ∂μ :=
          tsum_congr fun i => (integral_mul_const _ _).symm
      _ = ∫ x in S, ∑' i, c i x * Z (y, x) * a i y ∂μ := h1
      _ = ∫ x in S, Z (y, x) * T (y, x) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          show ∑' i, c i x * Z (y, x) * a i y = Z (y, x) * T (y, x)
          rw [hTs, ← tsum_mul_left]
          exact tsum_congr fun i => by ring
  simp only [inner]
  haveI hfin : IsFiniteMeasure ((μ.prod μ).restrict (S ×ˢ S)) := by
    rw [← Measure.prod_restrict]; infer_instance
  have hi : IntegrableOn (fun v => Z v * T v) (S ×ˢ S) (μ.prod μ) := by
    refine Integrable.of_bound ((hZ.mul hT).aestronglyMeasurable) (B * B₂) (ae_of_all _ fun v => ?_)
    rw [norm_mul]
    exact mul_le_mul (hB v) (hB₂ v) (norm_nonneg _) ((norm_nonneg _).trans (hB v))
  exact (setIntegral_prod (fun v => Z v * T v) hi).symm

theorem fj_fold_mean : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (g : G D n) (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p, ∀ B : ℝ, (∀ y x, ‖zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))‖ ≤ B) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g))) → FJ M m ψ b₀ F g φ = ∫ v in m.𝓕 ×ˢ m.𝓕, zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) * conj (th ψ b₀ φ 0 v.2 v.1) ∂(m.μ.prod m.μ) := by
  intro D n ρ p hn M m ψ hψ b₀ F hF g θ hθ φ hφ B hB hZ
  obtain ⟨hH, hfd, h1⟩ := m.hμ
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : SFinite m.μ := inferInstance
  haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨by simp [h1]⟩
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  obtain ⟨-, -, hnorm, -, -, hcont⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (ρ := ρ) (p := p) ψ hψ b₀
  have hφc : Continuous φ := GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ ⟨φ, hφ⟩
  have hφi : Integrable φ m.μ := GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ m.μ ⟨φ, hφ⟩
  obtain ⟨B₂, hB₂⟩ := GlobalTheory.T.exists_bound_lattice_sum_norm_schwartzA θ hθ φ hφ
  have hD := GlobalTheory.T.stronglyMeasurable_twisted_lattice_sum ψ hψ b₀ φ hφc.stronglyMeasurable (fun y => (hB₂ y).1)
  set Z : Mx D ρ p × Mx D ρ p → ℂ := fun v => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) with hZdef
  have hpcm : StronglyMeasurable fun y => pc M m ψ b₀ F (M.sh y * g) :=
    hZ.integral_prod_right' (ν := m.μ.restrict m.𝓕)
  have hpcb : ∀ y, ‖pc M m ψ b₀ F (M.sh y * g)‖ ≤ B := by
    intro y
    have h := norm_integral_le_of_norm_le_const (μ := m.μ.restrict m.𝓕)
      (f := fun x => zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))) (C := B) (ae_of_all _ fun x => hB y x)
    show ‖∫ x in m.𝓕, zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g)) ∂m.μ‖ ≤ B
    simpa [Measure.real, h1] using h
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hpcb 0)
  have hP : Integrable (fun y => pc M m ψ b₀ F (M.sh y * g) * conj (φ y)) m.μ := by
    refine (hφi.norm.const_mul B).mono'
      (hpcm.aestronglyMeasurable.mul (Complex.continuous_conj.comp hφc).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hpcb y) (norm_nonneg _)
  have hPξ : ∀ (y : Mx D ρ p) (ξ : Matrix (Fin ρ) (Fin p) D.host.E),
      pc M m ψ b₀ F (M.sh (rt ξ + y) * g) * conj (φ (rt ξ + y)) =
        (∫ x in m.𝓕, conj (chv ψ b₀ x (rt ξ)) * Z (y, x) ∂m.μ) * conj (φ (rt ξ + y)) := by
    intro y ξ
    rw [← GlobalTheory.CompanionTheory.FJE.sh_add M (rt ξ) y, mul_assoc, GlobalTheory.T.partial_coefficient_heisenberg_expansion M m ψ hψ b₀ F hF ξ (M.sh y * g)]
  have hfold := GlobalTheory.T.integral_eq_fundamental_domain_lattice_sum m _ hP
  have hmain := fold_abs m.μ m.𝓕 h1 Z (fun v => conj (dsum ψ b₀ φ v.2 v.1)) hZ
    (Complex.continuous_conj.comp_stronglyMeasurable hD) B B₂ (fun v => hB v.1 v.2)
    (fun v => ?_)
    (fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) x => conj (chv ψ b₀ x (rt ξ)))
    (fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) y => conj (φ (rt ξ + y)))
    (fun ξ => (Complex.continuous_conj.comp
      (hcont.comp (continuous_id.prodMk continuous_const))).stronglyMeasurable)
    (fun ξ x => by rw [RCLike.norm_conj]; exact hnorm _ _)
    (fun y => by simpa only [RCLike.norm_conj] using (hB₂ y).1)
    (fun y x => by
      show conj (dsum ψ b₀ φ x y) = _
      rw [dsum, Complex.conj_tsum]
      exact tsum_congr fun ξ => map_mul _ _ _)
  · show ∫ y, pc M m ψ b₀ F (M.sh y * g) * conj (φ y) ∂m.μ = _
    rw [hfold]
    simp only [hPξ]
    rw [hmain]
    simp only [th_zero]
    rfl
  · rw [RCLike.norm_conj, dsum]
    have hs : Summable fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖chv ψ b₀ v.2 (rt ξ) * φ (rt ξ + v.1)‖ := by
      simpa only [norm_mul, hnorm, one_mul] using (hB₂ v.1).1
    refine (norm_tsum_le_tsum_norm hs).trans ?_
    simpa only [norm_mul, hnorm, one_mul] using (hB₂ v.1).2

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiExpansionBoundedStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_expansion_bounded : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (g : G D n) (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p, ∀ B : ℝ, (∀ y x, ‖zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))‖ ≤ B) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g))) → FJ M m ψ b₀ F g φ = ∫ v in m.𝓕 ×ˢ m.𝓕, zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) * conj (th ψ b₀ φ 0 v.2 v.1) ∂(m.μ.prod m.μ) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.fj_fold_mean | exact GlobalTheory.CompanionTheory.FJE.fj_fold_mean | (intros; apply GlobalTheory.CompanionTheory.FJE.fj_fold_mean <;> assumption)
end
