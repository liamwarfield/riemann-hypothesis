module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqZeroOfOrthFock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransfer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjIntertwinerPointValueSobolevContinuous
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitWeightRealCenterActionFockMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

private theorem pow_exp_I_injective (a b : ℕ)
    (h : Complex.exp Complex.I ^ a = Complex.exp Complex.I ^ b) : a = b := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  have him := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
    Complex.natCast_im, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.mul_re] at him
  have hre : ((a : ℝ) - b) = n * (2 * Real.pi) := by linarith
  by_cases h0 : n = 0
  · subst h0
    have : (a : ℝ) = b := by simpa [sub_eq_zero] using hre
    exact_mod_cast this
  · exfalso
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h0
    have hpi : Real.pi = ((((a : ℚ) - b) / (2 * n) : ℚ) : ℝ) := by
      push_cast
      field_simp
      linarith
    exact irrational_pi ⟨_, hpi.symm⟩

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_pow_eq_pow_of_eq_exp_I_or_inv : ∀ (a b : ℕ) (w : ℂ), (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) → w ^ a = w ^ b → a = b := by
  intro a b w hw hab
  rcases hw with rfl | rfl
  · exact pow_exp_I_injective a b hab
  · rw [inv_pow, inv_pow, _root_.inv_inj] at hab
    exact pow_exp_I_injective a b hab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealCentreCharacterOnDefiniteVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealCentreCharacterOnDefiniteVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

open scoped ComplexOrder

namespace GlobalTheory.CenterVac

variable {D : D7}

theorem lintegral_enorm_sq_eq_one {α : Type} [MeasurableSpace α] {μ : Measure α} {s : Set α} {f : α → ℂ}
    (h : ∫ w in s, ‖f w‖ ^ 2 ∂μ = 1) : ∫⁻ w in s, ‖f w‖ₑ ^ 2 ∂μ = 1 := by
  have hint : Integrable (fun w => ‖f w‖ ^ 2) (μ.restrict s) :=
    Integrable.of_integral_ne_zero (by rw [h]; exact one_ne_zero)
  have e := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => by positivity)
  rw [h, ENNReal.ofReal_one] at e
  rw [e]
  refine lintegral_congr fun w => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem om_vac_eq_smul {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {x : DefSp S}
    {y : DefSp T} (hx : x.Is) (hy : y.Is) {k : KerDat S T} (hk : k.Is ψ θ x y) {z : GA D S} (hz : z ∈ GinfC S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ k.om (z, 1) k.vac = c • k.vac := by
  obtain ⟨χS, χT, hom⟩ := hk.weil
  obtain ⟨hψ, hv⟩ := hk.vac
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hdet : ∀ τ, (gramAt D S τ).det ≠ 0 := fun τ h0 => by
    have := (hx.cart τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  obtain ⟨r, hr, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ S hdet z hz
  have hy1 : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  obtain ⟨a, ha⟩ : ∃ a : ℂ, k.om (z, 1) k.vac = a • k.vac :=
    ⟨_, GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ χS χT k.om η hη hom x.s y.s hx.cart hy.cart z hz 1 (one_mem _)
      (fun τ => by rcases hx.pm τ with h | h <;> rw [h] <;> simp) (fun τ => by rw [one, one_mul, mul_one]) r 1 hr hy1
      k.vac hv.theta hv.fock⟩
  refine ⟨a, ?_, ha⟩
  obtain ⟨⟨p, hp⟩, hn⟩ := hv.norm
  have n1 : nrm2 p.1 p.2 k.vac = 1 := hn p hp
  obtain ⟨hH, hF, -⟩ := hp
  have hu := hom.om_unit p.1 p.2 hH hF (z, 1) k.vac hv.theta
  have hL := lintegral_enorm_sq_eq_one (μ := p.1) (s := p.2) (f := k.vac) n1
  rw [ha] at hu
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at hu
  rw [lintegral_const_mul' _ _ (by simp), hL, mul_one] at hu
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_eq_one] at hu
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).1 hu

theorem exists_center_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ c : GA D S → ℂ, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖c z‖ = 1 ∧ k.om (z, 1) k.vac = c z • k.vac := by
  intro D ψ θ hθ S T x y hx hy k hk
  have h : ∀ z : GA D S, ∃ c : ℂ, z ∈ GinfC S → ‖c‖ = 1 ∧ k.om (z, 1) k.vac = c • k.vac := fun z => by
    by_cases hz : z ∈ GinfC S
    · obtain ⟨c, hc⟩ := om_vac_eq_smul hθ hx hy hk hz
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h' => absurd h' hz⟩
  choose c hc using h
  exact ⟨c, fun z hz _ => hc z hz⟩

end GlobalTheory.CenterVac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealCentreCharacterOnDefiniteVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realCentre_character_on_definiteVacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ c : GA D S → ℂ, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖c z‖ = 1 ∧ k.om (z, 1) k.vac = c z • k.vac := by
  first | exact @GlobalTheory.CenterVac.exists_center_char | exact GlobalTheory.CenterVac.exists_center_char | (intros; apply GlobalTheory.CenterVac.exists_center_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitWeightRealCenterActionFockMonomial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CenFockWt

theorem central_wt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ wt : (FVar D T.rank S.rank →₀ ℕ) → GA D S → ℂ, (∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖wt α z‖ = 1 ∧ ∀ c : WO S T →₀ ℂ, IsFinComb c → k.om (z, 1) (pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) = wt α z • pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) ∧ ∀ χ : GA D S → ℂ, {α | ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z}.Finite := by
  intro D ψ θ hθ S T x y hx hy k hk
  classical
  obtain ⟨χS, χT, hW⟩ := hk.weil
  have hstd : IsStdChar D ψ (-1) := hk.vac.1
  have hvth : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_realCentre_character_on_definiteVacuum D ψ θ hθ S T x y hx hy k hk
  set ζ : GA D S → D.what₂.Tau → ℂ := fun z τ =>
    if h : 0 < S.rank then compAt θ τ (Formalism.L2.Theta.mt S z) ⟨0, h⟩ ⟨0, h⟩ else 1 with hζdef
  set μ : GA D S → D.what₂.Tau → ℂ := fun z τ => if (x.s τ = 1 ↔ y.s τ = 1) then (ζ z τ)⁻¹ else ζ z τ with hμdef
  set deg : D.what₂.Tau → (FVar D T.rank S.rank →₀ ℕ) → ℕ := fun τ α => ∑ v ∈ α.support with v.1 = τ, α v with hdeg
  have hζ : ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ,
      ‖ζ z τ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ z τ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
    intro z hz hzc τ
    obtain ⟨ζ', h1, h2⟩ := GlobalTheory.T.realComponent_central_definiteUnitary_eq_unit_scalar D θ hθ S x hx z hz hzc τ
    by_cases h : 0 < S.rank
    · have e : ζ z τ = ζ' := by
        simp only [hζdef, dif_pos h, h2, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [e]; exact ⟨h1, h2⟩
    · have e : ζ z τ = 1 := by simp only [hζdef, dif_neg h]
      refine ⟨by rw [e, norm_one], ?_⟩
      ext i
      exact absurd i.2 (by omega)
  have hμ : ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ, ‖μ z τ‖ = 1 := by
    intro z hz hzc τ
    simp only [hμdef]
    split_ifs
    · rw [norm_inv, (hζ z hz hzc τ).1, inv_one]
    · exact (hζ z hz hzc τ).1
  have hT1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have comb_smul : ∀ (cc : WO S T →₀ ℂ) (a : ℂ) (g : WO S T → ℂ), comb ψ S T cc (a • g) = a • comb ψ S T cc g := by
    intro cc a g
    unfold comb
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have : heisO ψ S T u (a • g) = a • heisO ψ S T u g := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, smul_comm]
  refine ⟨fun α z => c z * ∏ τ, μ z τ ^ deg τ α, ?_, ?_⟩
  · intro α z hz hzc
    refine ⟨?_, ?_⟩
    · rw [norm_mul, (hc z hz hzc).1, one_mul, norm_prod]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [norm_pow, hμ z hz hzc τ, one_pow]
    · intro cc hcc
      set F := pureTensorO ψ θ S T x.s y.s x.B y.B with hF
      have hcomb : ∀ g, comb ψ S T cc g = ∑ i : Fin cc.support.card,
          cc (cc.support.equivFin.symm i) • heisO ψ S T (cc.support.equivFin.symm i) g := by
        intro g
        unfold comb
        rw [← Finset.sum_coe_sort]
        exact (Equiv.sum_comp cc.support.equivFin.symm (fun u => cc u • heisO ψ S T u g)).symm
      have key1 : ∀ g, IsThetaFunO ψ S T g → ∀ P, F (comb ψ S T cc g) P = comb ψ S T cc (F g P) := by
        intro g hg P
        rw [hcomb, hcomb]
        exact (GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D ψ θ S T hstd hθ x.s y.s x.B y.B g hg cc.support.card _ _
          (fun i => hcc _ (Finset.coe_mem _)) P).1.symm
      have hop := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT k.om hW hθ x.s x.s x.B (fun τ => ζ z τ • x.B τ)
        y.s y.s y.B y.B z 1
        (fun τ => by rw [(hζ z hz hzc τ).2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [hT1, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [(hζ z hz hzc τ).2, Matrix.smul_mul, Matrix.one_mul])
        (fun τ => by rw [hT1, Matrix.one_mul]) k.vac hvth (MvPolynomial.monomial α 1)
      rw [key1 k.vac hvth, GlobalTheory.T.weilOperator_sourceRealPoint_commute_heisenbergComb D ψ S T χS χT k.om hW z hz cc hcc _ hop.1, hop.2, (hc z hz hzc).2,
        GlobalTheory.FiniteFock.pureTensorO_smul,
        GlobalTheory.T.pureTensorFock_unitScaledBasis_monomial D ψ θ hstd hθ S T x y hx hy k.vac hvth (ζ z) (fun τ => (hζ z hz hzc τ).1) α,
        smul_smul, comb_smul]
  · intro χ
    by_cases hne : ∃ α₀, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → c z * ∏ τ, μ z τ ^ deg τ α₀ = χ z
    · obtain ⟨α₀, hα₀⟩ := hne
      refine (GlobalTheory.T.finite_monomials_with_prescribed_placeDegree D T.rank S.rank (fun τ => deg τ α₀)).subset fun α hα τ => ?_
      show deg τ α = deg τ α₀
      by_cases hr : 0 < S.rank ∧ 0 < T.rank
      · obtain ⟨z, hz, hzc, h1, h2⟩ := GlobalTheory.T.exists_central_realPoint_unit_scalar_single_place D θ hθ S τ (Complex.exp Complex.I) (by simpa using Complex.norm_exp_ofReal_mul_I 1)
        have e := (hα z hz hzc).trans (hα₀ z hz hzc).symm
        have hc0 : c z ≠ 0 := by
          intro h0
          have := (hc z hz hzc).1
          rw [h0, norm_zero] at this
          exact zero_ne_one this
        have e2 := mul_left_cancel₀ hc0 e
        have hζρ : ∀ ρ, ρ ≠ τ → ζ z ρ = 1 := by
          intro ρ hρ
          simp only [hζdef, dif_pos hr.1, h2 ρ hρ, Matrix.one_apply_eq]
        have hζτ : ζ z τ = Complex.exp Complex.I := by
          simp only [hζdef, dif_pos hr.1, h1, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        have hμρ : ∀ ρ, ρ ≠ τ → μ z ρ = 1 := by
          intro ρ hρ
          simp only [hμdef, hζρ ρ hρ, inv_one, ite_self]
        rw [Finset.prod_eq_single τ (fun ρ _ hρ => by rw [hμρ ρ hρ, one_pow]) (by simp),
          Finset.prod_eq_single τ (fun ρ _ hρ => by rw [hμρ ρ hρ, one_pow]) (by simp)] at e2
        exact GlobalTheory.T.eq_of_pow_eq_pow_of_eq_exp_I_or_inv _ _ (μ z τ) (by
          simp only [hμdef, hζτ]
          split_ifs
          exacts [Or.inr rfl, Or.inl rfl]) e2
      · have hE : IsEmpty (FVar D T.rank S.rank) :=
          ⟨fun v => hr ⟨by have := v.2.2.2; omega, by have := v.2.1.2; omega⟩⟩
        simp only [hdeg, Finset.eq_empty_of_isEmpty α.support, Finset.eq_empty_of_isEmpty α₀.support,
          Finset.filter_empty, Finset.sum_empty]
    · refine Set.Finite.subset Set.finite_empty fun α hα => hne ⟨α, hα⟩

end GlobalTheory.CenFockWt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitWeightRealCenterActionFockMonomialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_weight_real_center_action_fock_monomial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ wt : (FVar D T.rank S.rank →₀ ℕ) → GA D S → ℂ, (∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖wt α z‖ = 1 ∧ ∀ c : WO S T →₀ ℂ, IsFinComb c → k.om (z, 1) (pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) = wt α z • pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) ∧ ∀ χ : GA D S → ℂ, {α | ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z}.Finite := by
  first | exact @GlobalTheory.CenFockWt.central_wt | exact GlobalTheory.CenFockWt.central_wt | (intros; apply GlobalTheory.CenFockWt.central_wt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.SeeSaw.CenFockPf

variable {D : D7}

theorem thPair_smul_smul {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (a b : ℂ) (f g : Mx D m n → ℂ) :
    thPair μ 𝓕 (a • f) (b • g) = (a * star b) * thPair μ 𝓕 f g := by
  unfold thPair
  rw [← integral_const_mul]
  congr 1; funext w
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem heisO_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f - g) = heisO ψ S T u f - heisO ψ S T u g := by
  funext w; simp only [heisO, Pi.sub_apply]; ring

theorem isLatVac_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f - g) :=
  ⟨fun u hu => by rw [heisO_sub, hf.1 u hu, hg.1 u hu],
    fun e he u hu hh => by rw [heisO_sub, hf.2 e he u hu hh, hg.2 e he u hu hh]⟩

theorem comb_single_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single 0 1) f = f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem isFinComb_single_zero (S T : HSp D) : IsFinComb (Finsupp.single (0 : WO S T) (1 : ℂ)) := by
  intro u hu
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
  subst hu
  ext i j; simp

section Pair

variable {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n))

theorem thPair_sum_right {ι : Type} (s : Finset ι) (a : ι → ℂ) (g : Mx D m n → ℂ) (h : ι → Mx D m n → ℂ)
    (hi : ∀ i, Integrable (fun w => g w * star (h i w)) (μ.restrict 𝓕)) :
    thPair μ 𝓕 g (∑ i ∈ s, a i • h i) = ∑ i ∈ s, star (a i) * thPair μ 𝓕 g (h i) := by
  unfold thPair
  have e : ∀ w, g w * star ((∑ i ∈ s, a i • h i) w) = ∑ i ∈ s, star (a i) * (g w * star (h i w)) := by
    intro w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => (hi i).const_mul _]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem thPair_sub_sum_left {ι : Type} (s : Finset ι) (a : ι → ℂ) (f g : Mx D m n → ℂ) (h : ι → Mx D m n → ℂ)
    (hf : Integrable (fun w => f w * star (g w)) (μ.restrict 𝓕))
    (hi : ∀ i, Integrable (fun w => h i w * star (g w)) (μ.restrict 𝓕)) :
    thPair μ 𝓕 (f - ∑ i ∈ s, a i • h i) g = thPair μ 𝓕 f g - ∑ i ∈ s, a i * thPair μ 𝓕 (h i) g := by
  unfold thPair
  have e : ∀ w, (f - ∑ i ∈ s, a i • h i) w * star (g w) = f w * star (g w) - ∑ i ∈ s, a i * (h i w * star (g w)) := by
    intro w
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_sub hf (integrable_finsetSum _ fun i _ => (hi i).const_mul _),
    integral_finsetSum _ fun i _ => (hi i).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end Pair

theorem exists_orth_coeff {X : Type} [MeasurableSpace X] (ν : Measure X) {ι : Type} [Fintype ι] (f : X → ℂ) (h : ι → X → ℂ)
    (hf : MemLp f 2 ν) (hh : ∀ i, MemLp (h i) 2 ν) :
    ∃ c : ι → ℂ, ∀ j, ∫ w, f w * star (h j w) ∂ν = ∑ i, c i * ∫ w, h i w * star (h j w) ∂ν := by
  have ip : ∀ (a b : X → ℂ) (ha : MemLp a 2 ν) (hb : MemLp b 2 ν),
      inner ℂ (hb.toLp b) (ha.toLp a) = ∫ w, a w * star (b w) ∂ν := by
    intro a b ha hb
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with w h1 h2
    rw [h1, h2]
    simp
  let H : ι → Lp ℂ 2 ν := fun i => (hh i).toLp (h i)
  let K : Submodule ℂ (Lp ℂ 2 ν) := Submodule.span ℂ (Set.range H)
  haveI : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range H)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (K.starProjection_apply_mem (hf.toLp f))
  refine ⟨c, fun j => ?_⟩
  have h0 := (Submodule.mem_orthogonal K _).1 (K.sub_starProjection_mem_orthogonal (hf.toLp f)) (H j)
    (Submodule.subset_span ⟨j, rfl⟩)
  rw [← hc, inner_sub_right, inner_sum, sub_eq_zero] at h0
  rw [← ip f (h j) hf (hh j)]
  refine h0.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [inner_smul_right, ← ip (h i) (h j) (hh i) (hh j)]

theorem isLatVac_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {x : DefSp S} {y : DefSp T}
    {f₀ : WO S T → ℂ} (hvac : IsVacO ψ θ S T x.s y.s x.L y.L f₀) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsLatVac (heisO ψ S T) (latO S T x.L y.L fun _ => True) (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := by
  have hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T x.s y.s x.B y.B f₀ φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hvac.1 hvac.2.inf x.s x.B y.s y.B hvac.2.theta φ
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu 2)) (hvac.2.lat.1 u hu) φ
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hvac.2.inf x.s y.s x.B y.B f₀ hth u
      (GlobalTheory.VacGood.infPart_latO hu) (hvac.2.lat.2 e he u hu hh) φ

theorem thPair_eq_zero_of_eigen {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χ χ' om) (v : VolM D T.rank S.rank) (p : GA D S × GA D T) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) {a b : ℂ} (ha : om p f = a • f) (hb : om p g = b • g)
    (hb1 : ‖b‖ = 1) (hab : b ≠ a) : thPair v.μ v.𝓕 f g = 0 := by
  have h := GlobalTheory.WeilPairing.thPair_om_eq D ψ S T χ χ' om hW v p f g hf hg
  rw [ha, hb] at h
  have h' := (thPair_smul_smul v.μ v.𝓕 a b f g).symm.trans h
  have hbb : star b * b = 1 := by
    have := Complex.conj_mul' b
    rw [hb1] at this
    simpa using this
  have : (a - b) * thPair v.μ v.𝓕 f g = 0 := by
    linear_combination b * h' - a * thPair v.μ v.𝓕 f g * hbb
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hab.symm)

theorem cenFock : ∀ D : D7, CenFock D := by
  intro D ψ θ hθ S T x y hx hy k hk χ
  classical
  obtain ⟨wt, hwt, hfin⟩ := GlobalTheory.T.exists_unit_weight_real_center_action_fock_monomial D ψ θ hθ S T x y hx hy k hk
  obtain ⟨χS, χT, hW⟩ := hk.weil
  obtain ⟨v⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 T.rank S.rank
  set pt := pureTensorO ψ θ S T x.s y.s x.B y.B k.vac with hpt
  have hth : ∀ φ, IsThetaFunO ψ S T (pt φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hk.vac.1 hθ x.s x.B y.s y.B hk.vac.2.theta φ
  have heig : ∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) →
      k.om (z, 1) (pt (MvPolynomial.monomial α 1)) = wt α z • pt (MvPolynomial.monomial α 1) := by
    intro α z hz hzc
    have := (hwt α z hz hzc).2 _ (isFinComb_single_zero S T)
    rwa [comb_single_zero] at this
  have hL2 : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → MemLp g 2 (v.μ.restrict v.𝓕) := fun hg =>
    GlobalTheory.Size.memLp_theta hk.vac.1 v.covol.1 v.covol.2.1 hg
  have hint : ∀ {g g' : WO S T → ℂ}, IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      Integrable (fun w => g w * star (g' w)) (v.μ.restrict v.𝓕) := fun hg hg' =>
    GlobalTheory.Size.integrableOn_mul_conj hk.vac.1 v.covol.1 v.covol.2.1 hg hg'
  set A := (hfin χ).toFinset with hA
  have hmem : ∀ α, α ∈ A ↔ ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z := fun α => by
    rw [hA, Set.Finite.mem_toFinset]; rfl
  let mon : A → PolF D T.rank S.rank := fun α => MvPolynomial.monomial α.1 1
  refine ⟨Submodule.span ℂ (Set.range mon), FiniteDimensional.span_of_finite ℂ (Set.finite_range mon), ?_⟩
  intro f hf hlat hχ
  obtain ⟨c, hc⟩ := exists_orth_coeff (v.μ.restrict v.𝓕) f (fun α : A => pt (mon α)) (hL2 hf) (fun α => hL2 (hth _))
  refine ⟨∑ α, c α • mon α, (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨c, rfl⟩, ?_⟩
  have hg := GlobalTheory.OrientedHeis.theta_sub hf (hth (∑ α, c α • mon α))
  have hgl := isLatVac_sub ψ S T hlat (isLatVac_pureTensorO hk.vac (∑ α, c α • mon α))
  have hsum : pt (∑ α, c α • mon α) = ∑ α, c α • pt (mon α) := by simp only [map_sum, map_smul]
  have hmono : ∀ β, thPair v.μ v.𝓕 (f - pt (∑ α, c α • mon α)) (pt (MvPolynomial.monomial β 1)) = 0 := by
    intro β
    rw [hsum]
    refine (thPair_sub_sum_left v.μ v.𝓕 Finset.univ c f _ (fun α => pt (mon α)) (hint hf (hth _))
      (fun α => hint (hth _) (hth _))).trans ?_
    by_cases hβ : β ∈ A
    · exact sub_eq_zero.2 (hc ⟨β, hβ⟩)
    · rw [hmem] at hβ
      push_neg at hβ
      obtain ⟨z, hz, hzc, hne⟩ := hβ
      rw [thPair_eq_zero_of_eigen hW v (z, 1) hf (hth _) (hχ z hz hzc) (heig β z hz hzc) (hwt β z hz hzc).1 hne, zero_sub,
        neg_eq_zero]
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [thPair_eq_zero_of_eigen hW v (z, 1) (hth _) (hth _) (heig α.1 z hz hzc) (heig β z hz hzc) (hwt β z hz hzc).1
        (by rw [(hmem α.1).1 α.2 z hz hzc]; exact hne), mul_zero]
  refine sub_eq_zero.1 (GlobalTheory.FockTotal.eq_zero_of_orth_fock D ψ θ hθ S T x y hx hy k.vac hk.vac v _ hg hgl fun Q => ?_)
  have hQ : pt Q = ∑ β ∈ Q.support, AddMonoidAlgebra.coeff Q β • pt (MvPolynomial.monomial β 1) := by
    conv_lhs => rw [Q.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  show thPair v.μ v.𝓕 (f - pt (∑ α, c α • mon α)) (pt Q) = 0
  rw [hQ]
  refine (thPair_sum_right v.μ v.𝓕 Q.support (fun β => AddMonoidAlgebra.coeff Q β) _
    (fun β => pt (MvPolynomial.monomial β 1)) (fun β => hint hg (hth _))).trans ?_
  exact Finset.sum_eq_zero fun β _ => by rw [hmono, mul_zero]

end GlobalTheory.SeeSaw.CenFockPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegreeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralEigenTheta_isFockVector_bounded_degree : ∀ D : D7, CenFock D := by
  first | exact @GlobalTheory.SeeSaw.CenFockPf.cenFock | exact GlobalTheory.SeeSaw.CenFockPf.cenFock | (intros; apply GlobalTheory.SeeSaw.CenFockPf.cenFock <;> assumption)
end
