module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecomposition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeDerivWeierstrassPParameterSeriesBou

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaTwoMulAtZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaTwoMulAtZero
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.SigmaDuplication

open Filter Topology

theorem sgStar_two_mul {Λ : AddSubgroup ℂ} (hΛ : GlobalTheory.EvenTheta.IsLat Λ) {P : ℂ} (hP : P ∉ Λ) :
    sgStar Λ (2 * P) = -(wpD Λ P) * sgStar Λ P ^ 4 := by
  obtain ⟨⟨hdiff, hd0, -, -⟩, hzero, -, hwp, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have h0 : sgStar Λ 0 = 0 := (hzero 0).2 (zero_mem Λ)
  have hPL : P ∉ L.lattice := fun hm => hP ((hL P).2 hm)
  have hwpfun : wpF Λ = L.weierstrassP := funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)
  have hwpd : HasDerivAt (wpF Λ) (wpD Λ P) P := by
    rw [hwpfun, GlobalTheory.LatticeInvariants.wpD_eq hL P, ← congrFun L.deriv_weierstrassP P]
    exact ((L.differentiableOn_weierstrassP P hPL).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hPL)).hasDerivAt
  have hA : HasDerivAt (fun v => sgStar Λ (P + v)) (deriv (sgStar Λ) (P + P) * 1) P :=
    (hdiff (P + P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_add P)
  have hB : HasDerivAt (fun v => sgStar Λ (P - v)) (deriv (sgStar Λ) (P - P) * -1) P :=
    (hdiff (P - P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_sub P)
  have hS := (hdiff P).hasDerivAt.pow 2
  have hG := (hwpd.sub_const (wpF Λ P)).mul (hS.const_mul (sgStar Λ P ^ 2))
  have hev : (fun v => sgStar Λ (P + v) * sgStar Λ (P - v)) =ᶠ[𝓝 P]
      (fun v => (wpF Λ v - wpF Λ P) * (sgStar Λ P ^ 2 * sgStar Λ v ^ 2)) := by
    have hne : sgStar Λ P ≠ 0 := fun h => hP ((hzero P).1 h)
    filter_upwards [(hdiff.continuous.continuousAt (x := P)).eventually_ne hne] with v hv
    have hvΛ : v ∉ Λ := fun hm => hv ((hzero v).2 hm)
    linear_combination hwp P v hP hvΛ
  have huniq := (hA.mul hB).unique (hG.congr_of_eventuallyEq hev)
  simp only [sub_self, h0, hd0, Pi.pow_apply] at huniq
  rw [two_mul]
  linear_combination -huniq

theorem U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, P ∉ Λ →
    U1 Λ (2 * P) (sgStar Λ) 0 = -(wpD Λ P) * U1 Λ P (sgStar Λ) 0 ^ 4 := by
  intro Λ hΛ P hP
  show sgStar Λ (0 + 2 * P) * Complex.exp _ = -(wpD Λ P) * (sgStar Λ (0 + P) * Complex.exp _) ^ 4
  rw [zero_add, zero_add, sgStar_two_mul hΛ hP, mul_pow, ← Complex.exp_nat_mul, mul_assoc]
  congr 2
  simp only [map_mul, map_ofNat]
  push_cast
  ring_nf

end GlobalTheory.SigmaDuplication
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaTwoMulAtZeroStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_modifiedSigma_two_mul_at_zero : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, P ∉ Λ → U1 Λ (2 * P) (sgStar Λ) 0 = -(wpD Λ P) * U1 Λ P (sgStar Λ) 0 ^ 4 := by
  first | exact @GlobalTheory.SigmaDuplication.U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four | exact GlobalTheory.SigmaDuplication.U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four | (intros; apply GlobalTheory.SigmaDuplication.U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicUnitaryOfLocalFamilyAlmostAllTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicUnitaryOfLocalFamilyAlmostAllTrivial
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalUnitaryGlue

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem exists_on_finset (γ : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ k : HA (Af F) σ J, (∀ v ∈ S, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = γ v) ∧
      ∀ v ∉ S, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => map_one _⟩
  | insert a S ha ih =>
    obtain ⟨k, h1, h2⟩ := ih
    have s1 : mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F a) (extH σ J (sgV a) (sgV_mul a) (γ a)) = γ a :=
      mapH_extH_self σ J _ _ _ (fun y => Pi.single_eq_same a y) _
    have s2 : ∀ w, w ≠ a →
        mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (extH σ J (sgV a) (sgV_mul a) (γ a)) = 1 :=
      fun w hw => mapH_extH_zero σ J _ _ _ (fun y => Pi.single_eq_of_ne hw y) _
    refine ⟨extH σ J (sgV a) (sgV_mul a) (γ a) * k, fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [s1, h2 _ ha, mul_one]
      · rw [s2 v (fun e => ha (e ▸ hv)), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, s2 v hv.1, h2 v hv.2, one_mul]

theorem exists_of_finite (γ : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (h : {v | γ v ≠ 1}.Finite) :
    ∃ k : HA (Af F) σ J, ∀ v, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = γ v := by
  obtain ⟨k, h1, h2⟩ := exists_on_finset σ J γ h.toFinset
  refine ⟨k, fun v => ?_⟩
  by_cases hv : v ∈ h.toFinset
  · exact h1 v hv
  · rw [h2 v hv]
    simpa [eq_comm] using hv

end Gen

theorem exists_finite_adelic : ∀ (D : D7) (V : HSp D) (γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram), {v | γ v ≠ 1}.Finite → ∃ k ∈ GfC V, ∀ v : HeightOneSpectrum (𝓞 D.host.F), (finMat D.sp.cm.sig V.gram k).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) = (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1 := by
  intro D V γ h
  obtain ⟨k, hk⟩ := exists_of_finite D.sp.cm.sig V.gram γ h
  refine ⟨ofFin D.sp.cm V k, ?_, fun v => ?_⟩
  · exact congrArg (HA.mat _ _ _) (projInf_ofFin D.sp.cm V k)
  · have e : finMat D.sp.cm.sig V.gram (ofFin D.sp.cm V k) = (HA.mat _ _ _ k).1 :=
      congrArg (fun x => (HA.mat _ _ _ x).1) (projFin_ofFin D.sp.cm V k)
    rw [e, ← hk v]
    rfl

end GlobalTheory.LocalUnitaryGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicUnitaryOfLocalFamilyAlmostAllTrivialStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnitary_of_localFamily_almostAll_trivial : ∀ (D : D7) (V : HSp D) (γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram), {v | γ v ≠ 1}.Finite → ∃ k ∈ GfC V, ∀ v : HeightOneSpectrum (𝓞 D.host.F), (finMat D.sp.cm.sig V.gram k).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) = (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1 := by
  first | exact @GlobalTheory.LocalUnitaryGlue.exists_finite_adelic | exact GlobalTheory.LocalUnitaryGlue.exists_finite_adelic | (intros; apply GlobalTheory.LocalUnitaryGlue.exists_finite_adelic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelEquationTangentAtLatticeParameter
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelEquationTangentAtLatticeParameter
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar.ModelPoint

theorem wpD_sq {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    wpD Λ v ^ 2 = 4 * wpF Λ v ^ 3 - g2 Λ * wpF Λ v - g3 Λ := by
  obtain ⟨w₁, w₂, hi, hΛ⟩ := h
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  rw [GlobalTheory.LatticeInvariants.wpD_eq hL, GlobalTheory.LatticeInvariants.wpF_eq hL,
    GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL]
  exact L.derivWeierstrassP_sq v fun h => hv ((hL v).2 h)

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := dif_pos x.2

theorem lamC_neg_div_four (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) :
    lamC lam (-x / 4) = -lamC lam x / 4 := by
  lift x to Qbar using hx
  have e : (-(x : ℂ) / 4) = ((-x / 4 : Qbar) : ℂ) := by push_cast; rfl
  rw [e, lamC_coe, lamC_coe, map_div₀, map_neg, map_ofNat]

theorem lamC_eqn (lam : Qbar →+* ℂ_[p]) {x y a b : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar)
    (ha : a ∈ Qbar) (hb : b ∈ Qbar) (h : y ^ 2 = 4 * x ^ 3 - a * x - b) :
    lamC lam y ^ 2 = 4 * lamC lam x ^ 3 - lamC lam a * lamC lam x - lamC lam b := by
  lift x to Qbar using hx
  lift y to Qbar using hy
  lift a to Qbar using ha
  lift b to Qbar using hb
  have e : y ^ 2 = 4 * x ^ 3 - a * x - b := by
    apply Subtype.ext
    push_cast
    exact h
  have := congrArg lam e
  simpa only [lamC_coe, map_sub, map_mul, map_pow, map_ofNat] using this

theorem model_point : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → wpD g.abelian₂ v ∈ Qbar → g.W.toAffine.Equation (GlobalTheory.EvenTheta.xAt g v) (GlobalTheory.ThetaPar.yAt g v) ∧ 2 * GlobalTheory.ThetaPar.yAt g v + g.W.a₁ * GlobalTheory.EvenTheta.xAt g v + g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * lamC g.lam (wpD g.abelian₂ v) := by
  intro p _ g v hL h2 h3 hv hx hy
  have key := lamC_eqn g.lam hx hy h2 h3 (wpD_sq hL hv)
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt,
      lamC_neg_div_four g.lam h2, lamC_neg_div_four g.lam h3]
    linear_combination ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 / 4 * key
  · simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₃, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt]
    ring

end GlobalTheory.ThetaPar.ModelPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicModelEquationTangentAtLatticeParameterStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicModel_equation_tangent_at_latticeParameter : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → wpD g.abelian₂ v ∈ Qbar → g.W.toAffine.Equation (GlobalTheory.EvenTheta.xAt g v) (GlobalTheory.ThetaPar.yAt g v) ∧ 2 * GlobalTheory.ThetaPar.yAt g v + g.W.a₁ * GlobalTheory.EvenTheta.xAt g v + g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * lamC g.lam (wpD g.abelian₂ v) := by
  first | exact @GlobalTheory.ThetaPar.ModelPoint.model_point | exact GlobalTheory.ThetaPar.ModelPoint.model_point | (intros; apply GlobalTheory.ThetaPar.ModelPoint.model_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslatePowerSeriesPowBoundedCoeffsOfTorsi
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecompositionStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (t : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ Λ →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), N ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  first | exact @GlobalTheory.ThetaTranslDecomp.exists_decomp | exact GlobalTheory.ThetaTranslDecomp.exists_decomp | (intros; apply GlobalTheory.ThetaTranslDecomp.exists_decomp <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslatePowerSeriesPowBoundedCoeffsOfTorsi
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl
open GlobalTheory.EvenTheta

variable {p : ℕ} [Fact p.Prime]

def GoodAt (g : GL3Theta.G1 p) (k : ℕ) (F : ℂ → ℂ) : Prop :=
  AlgEnt F ∧ ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU F = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B

theorem bdd_mul {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f * h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.2

theorem bdd_add {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f + h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).1

theorem bdd_sub {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f - h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.1

theorem bdd_C (c : ℂ_[p]) : BddSer (PowerSeries.C c) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 c).1

theorem bdd_X : BddSer (PowerSeries.X : PowerSeries ℂ_[p]) :=
  ⟨1, (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1⟩

theorem bdd_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ_[p]) (h : ∀ i ∈ s, BddSer (f i)) :
    BddSer (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bdd_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lamC_one (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  have h : (1 : ℂ) ∈ Qbar := one_mem _
  rw [lamC, dite_eq_left h]
  exact map_one lam

theorem good_mul {g : GL3Theta.G1 p} {k l : ℕ} {F G : ℂ → ℂ} (hF : GoodAt g k F) (hG : GoodAt g l G) :
    GoodAt g (k + l) (fun z => F z * G z) := by
  obtain ⟨hFa, B, hB, hFe⟩ := hF
  obtain ⟨hGa, B', hB', hGe⟩ := hG
  obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 F G hFa hGa).1
  refine ⟨ha, B * B', bdd_mul hB hB', ?_⟩
  rw [he, hFe, hGe, pow_add]
  ring

theorem good_one (g : GL3Theta.G1 p) : GoodAt g 0 (fun _ => (1 : ℂ)) := by
  obtain ⟨ha, he⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
  refine ⟨ha, 1, ?_, ?_⟩
  · simpa using bdd_C (p := p) 1
  · rw [he, lamC_one, map_one, pow_zero, one_mul]

theorem good_pow {g : GL3Theta.G1 p} {k : ℕ} {F : ℂ → ℂ} (hF : GoodAt g k F) (n : ℕ) :
    GoodAt g (k * n) (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using good_one g
  | succ n ih =>
    have := good_mul ih hF
    simp only [← pow_succ] at this
    rwa [show k * n + k = k * (n + 1) by ring] at this

theorem good_congr {g : GL3Theta.G1 p} {k l : ℕ} {F : ℂ → ℂ} (h : GoodAt g k F) (e : k = l) : GoodAt g l F :=
  e ▸ h

theorem atU_mul_pow {g : GL3Theta.G1 p} {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) (m n : ℕ) :
    AlgEnt (fun z => F z ^ m * G z ^ n) ∧ g.atU (fun z => F z ^ m * G z ^ n) = g.atU F ^ m * g.atU G ^ n := by
  have hpow : ∀ {H : ℂ → ℂ}, AlgEnt H → ∀ k : ℕ, AlgEnt (fun z => H z ^ k) ∧
      g.atU (fun z => H z ^ k) = g.atU H ^ k := by
    intro H hH k
    induction k with
    | zero =>
      obtain ⟨ha, he⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
      simp only [pow_zero]
      exact ⟨ha, by rw [he, lamC_one, map_one]⟩
    | succ k ih =>
      obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 _ H ih.1 hH).1
      simp only [pow_succ]
      exact ⟨ha, by rw [he, ih.2]⟩
  obtain ⟨h1, e1⟩ := hpow hF m
  obtain ⟨h2, e2⟩ := hpow hG n
  obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 _ _ h1 h2).1
  exact ⟨ha, by rw [he, e1, e2]⟩


set_option maxHeartbeats 800000 in
theorem tau_pow_bdd : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∀ N : ℕ, 0 < N → (N : ℂ) * t ∈ g.abelian₂ →
      GlobalTheory.EvenTheta.BddSer (GlobalTheory.ThetaTransl.tau g t ^ N) := by
  intro D p _ cc δ g hg t ht N hN hNt
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  have hU0 : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂ := by
    funext z; simp [U1]
  have hsg : AlgEnt (sgStar g.abelian₂) := hU0 ▸ halg 0 ⟨1, one_pos, by simp⟩
  have htq : InRationalLattice g.abelian₂ t := ⟨N, hN, hNt⟩
  have hP := halg t htq
  have htn := ht.1
  have hwt : wpF g.abelian₂ t ∈ Qbar := (hwp t htq htn).1
  obtain ⟨hu1, hwq1, -, he0, hsgU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def
  have he : e ≠ 0 := fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0
  have gσ : GoodAt g 1 (sgStar g.abelian₂) :=
    ⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (bdd_C ε) bdd_X, by rw [hsgU]; ring⟩
  obtain ⟨hSa, hSe⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t htn hwt
  have gS : GoodAt g 2 (sqTh g.abelian₂ t) := ⟨hSa, lineSer g.wq⁻¹ (xAt g t),
    bdd_sub ⟨1, hwq1⟩ (bdd_mul (bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩
  obtain ⟨hTa, w, hw, hTe⟩ := GlobalTheory.T.sigmaStarCubeDerivWeierstrassP_parameterSeries_bounded p g hok hlat' h2 h3 hdisc hsg t htn hwt
  have gT : GoodAt g 3 (sqThD g.abelian₂ t) := ⟨hTa, w, hw, hTe⟩
  obtain ⟨I, a, b, hle, hid⟩ := GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition g.abelian₂ hlat' t N hN hNt t htn
  let φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ := Sum.elim
    (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ t z ^ (i : ℕ))
    (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ t z ^ (j : ℕ) * sqThD g.abelian₂ t z)
  let c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ := Sum.elim (fun i => a i) (fun j => b j)
  have gφ : ∀ k, GoodAt g (2 * I + 3) (φ k) := by
    rintro (i | j)
    · have hi := i.isLt
      exact good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)
    · have hj := j.isLt
      exact good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT)
        (by omega)
  obtain ⟨hEa, hEe⟩ := atU_mul_pow (g := g) hsg hP (2 * I + 3 - N) N
  have hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - N) * U1 g.abelian₂ t (sgStar g.abelian₂) z ^ N = ∑ k, c k * φ k z := by
    intro z
    rw [hid z, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
  obtain ⟨a', -, hlin⟩ := GlobalTheory.T.algebraicTaylorCombination_parameterSeries_algebraic p g _ φ c _ hEa (fun k => (gφ k).1) hEq
  choose B hB hBe using fun k => (gφ k).2
  have hS : BddSer (∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k) :=
    bdd_sum _ _ fun k _ => bdd_mul (bdd_C _) (hB k)
  rw [hEe, hsgU] at hlin
  simp only [hBe] at hlin
  have hPe : g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)) = e * tau g t := by
    rw [tau, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [he0]; exact one_ne_zero), one_mul]
  rw [hPe] at hlin
  set K := 2 * I + 3 - N with hKd
  have hK : K + N = 2 * I + 3 := Nat.sub_add_cancel hle
  have hsum : ∑ k, PowerSeries.C (lamC g.lam (a' k)) * (e ^ (2 * I + 3) * B k) =
      e ^ (2 * I + 3) * ∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e * tau g t) ^ N =
      e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * tau g t ^ N)) := by
    rw [← hK, pow_add, map_pow]; ring
  have key := hleft.symm.trans (hlin.trans hsum)
  have key2 := mul_left_cancel₀ (pow_ne_zero _ he) key
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨C0, fun n => ?_⟩
  have h1 := congrArg (PowerSeries.coeff (n + K)) key2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h1
  have h2 := hC0 (n + K)
  rw [← h1, norm_mul, norm_pow, hu1, one_pow, one_mul] at h2
  exact h2

end GlobalTheory.ThetaTransl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslatePowerSeriesPowBoundedCoeffsOfTorsiStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslatePowerSeries_pow_boundedCoeffs_of_torsion : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∀ N : ℕ, 0 < N → (N : ℂ) * t ∈ g.abelian₂ →
      GlobalTheory.EvenTheta.BddSer (GlobalTheory.ThetaTransl.tau g t ^ N) := by
  first | exact @GlobalTheory.ThetaTransl.tau_pow_bdd | exact GlobalTheory.ThetaTransl.tau_pow_bdd | (intros; apply GlobalTheory.ThetaTransl.tau_pow_bdd <;> assumption)
end
end
