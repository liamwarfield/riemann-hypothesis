module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGram
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivariance
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivariance
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinExactAt
open GlobalTheory.SplitLinAt GlobalTheory.SplitLinear

theorem linFirst (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T)
    (hW : IsWeilDatumO ψ S T χS χT om) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ) (Ψ : Matrix n n' k → ℂ)
    (f : WO S T → ℂ) (hO : Over ψ α β LS LT f₀ Ψ f) (g : GL n' k) (h : GL n k) :
    Over ψ α β LS LT f₀ (fun x => (lam p χT⁻¹ ((T.rank : ℝ) / 2) (Matrix.GeneralLinearGroup.det g) : ℂ) *
      (lam p χS (-(S.rank : ℝ) / 2) (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ ((h⁻¹ : GL n k).val * x * g.val))
      (om (α.gl g, β.gl h) f) := by
  obtain ⟨hsS, hsT, hV, hΨ, hth⟩ := hO
  have he : IsSplitIdem D p.e := p.split
  have hec : IsSplitIdem D (cA D p.e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hA : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf p.e u → u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) :=
    fun u hu hh => latHalf D k p S T LS LT u hu (Or.inl hh)
  have hle := latO_le (S := S) (T := T) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)
  have hfix : ∀ u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf p.e u ∨ IsHalf (cA D p.e) u → heisO ψ S T u f₀ = f₀ := fun u hu hh =>
    hh.elim (fun h1 => hV.2.2 p.e he u (latHalf D k p S T LS LT u hu hh) h1)
      fun h1 => hV.2.2 _ hec u (latHalf D k p S T LS LT u hu hh) h1
  refine ⟨hsS, hsT, hV, sbSubst hΨ g h _, hth.1, fun Tm hTm => ?_⟩
  have hTm' := (placeModel_congr hA hle).1 hTm
  have hSB := (sbHalf_congr hA hle).1 (sbHalf D k p S T n n' α β LS LT hsS hsT Ψ hΨ)
  rw [hth.2 Tm hTm, lawAt D ψ S T χS χT om LS LT p.e f₀ Tm hW hsS hsT he hV.1 hfix hTm' (α.gl g) (β.gl h)
    (α.gl_supp g) (β.gl_supp h) _ _ (detFrame α g) (detFrame β h) _ hSB, ← map_smul, fac_lam]
  congr 1
  funext t
  rw [Pi.smul_apply, smul_eq_mul, extFunAct D k p S T n n' α β Ψ g h t, ← extFun_smul]

theorem idl_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (a : kˣ) : idl p a = p.idele a := by
  ext
  rw [idl_val, p.idele_val]
  ring

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt

theorem algebraMap_inj (D : D7) : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective

theorem idem_calc {R : Type} [CommRing R] (E C s t : R) (he : E * E = E) (hcc : C * C = C) (hc : E * C = 0)
    (hs : E * s = s) (hcs : C * t = t) : (1 - E + s) * (1 - C + t) * (1 - (E + C)) = 1 - (E + C) := by
  have h1 : (1 - E + s) * (1 - C + t) = 1 - E - C + s + t := by
    linear_combination (1 - t - s + s * t) * hc + (E - s) * hcs + (C - C * t) * hs
  have h2 : (1 - E - C + s + t) * (1 - (E + C)) = 1 - (E + C) := by
    linear_combination he + hcc + (2 - s - t) * hc + (C - 1) * hs + (E - 1) * hcs
  rw [h1, h2]

theorem norm_idele_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (a : kˣ) (ε : AF D.host.F) (hε : p.e + cA D p.e = algebraMap (AF D.host.F) (AE D) ε) :
    Algebra.norm (AF D.host.F) (p.idele a : AE D) * (1 - ε) = 1 - ε := by
  apply algebraMap_inj D
  rw [map_mul, GlobalTheory.SplitDetCharacter.algebraMap_norm, map_sub, map_one, ← hε, p.idele_val]
  have he : p.e * p.e = p.e := p.split.1
  have hc : p.e * cA D p.e = 0 := p.split.2.1
  have hcc : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have hs : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]
  have hcs : cA D p.e * cA D (p.sec a) = cA D (p.sec a) := by rw [← map_mul, hs]
  have hx : cA D (1 - p.e + p.sec a) = 1 - cA D p.e + cA D (p.sec a) := by
    rw [map_add (f := _), map_sub, map_one]
  rw [hx]
  exact idem_calc _ _ _ _ he hcc hc hs hcs

theorem normOff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (a : kˣ) (w : Pl D), w ≠ p.v → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D w (p.idele a) = 1 := by
  intro D k _ _ _ _ p a w hw
  obtain ⟨ε, ⟨α, rfl, -, hα⟩, hsum⟩ := p.above
  have h := congrArg (fun y => evalV D.host.F w (sndA D.host.F y)) (norm_idele_mul p a _ hsum)
  simp only [map_mul, map_sub, map_one] at h
  have h0 : evalV D.host.F w (sndA D.host.F (pairA D.host.F 0 α)) = 0 := hα w hw
  rw [h0, sub_zero, mul_one] at h
  exact Units.ext h

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt

theorem norm_idele_chart {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (π : AE D →+* Fv D.host.F p.v)
    (halg : ∀ y : AF D.host.F, π (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F p.v (sndA D.host.F y))
    (πe : π p.e = 1) (πce : π (cA D p.e) = 0) (a : kˣ) :
    ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D p.v (p.idele a) : (Fv D.host.F p.v)ˣ) : Fv D.host.F p.v) = π (p.sec a) := by
  have hs : p.e * p.sec a = p.sec a := by rw [← p.sec_pr, p.pr_sec]
  have key : evalV D.host.F p.v (sndA D.host.F (Algebra.norm (AF D.host.F) (p.idele a : AE D))) = π (p.sec a) := by
    rw [← halg, GlobalTheory.SplitDetCharacter.algebraMap_norm, map_mul, p.idele_val]
    have hcs : cA D (p.sec a) = cA D p.e * cA D (p.sec a) := by rw [← map_mul, hs]
    rw [map_add (f := _), map_sub, map_one, map_add (f := _), map_sub, map_one, map_add (f := _), map_sub, map_one, πe, hcs, map_mul, πce, zero_mul]
    ring
  exact key

open GlobalTheory.SplitHecke

theorem chartAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k), ∃ φ : k ≃+* Fv D.host.F p.v, (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) ∧
      ∀ a : kˣ, ((GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D p.v (p.idele a) : (Fv D.host.F p.v)ˣ) : Fv D.host.F p.v) = φ a := by
  intro D k _ _ _ _ p
  obtain ⟨v', π, hsurj, hker, halg, hint⟩ := GlobalTheory.SplitChart.exists_chart p.e p.split
  have he : p.e * p.e = p.e := p.split.1
  have hce : p.e * cA D p.e = 0 := p.split.2.1
  have hs : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  have πe : π p.e = 1 := by
    obtain ⟨c, hc⟩ := hsurj 1
    have h0 : π (p.e * c - c) = 0 := (hker _).2 (by rw [mul_sub, ← mul_assoc, he, sub_self])
    rw [map_sub, map_mul, hc, mul_one, sub_eq_zero] at h0
    exact h0
  have πce : π (cA D p.e) = 0 := (hker _).2 hce
  have hv : v' = p.v := by
    obtain ⟨ε, ⟨α, rfl, h1, hα⟩, hsum⟩ := p.above
    by_contra hne
    have h2 := halg (pairA D.host.F 0 α)
    rw [← hsum, map_add (f := _), πe, πce, add_zero] at h2
    have h3 : evalV D.host.F v' (sndA D.host.F (pairA D.host.F 0 α)) = 0 := hα v' hne
    rw [h3] at h2
    exact one_ne_zero h2
  subst hv
  let f : k →+* Fv D.host.F p.v :=
    { toFun := fun a => π (p.sec a)
      map_one' := by rw [SplitPt.sec_one, πe]
      map_mul' := fun a b => by rw [SplitPt.sec_mul, map_mul]
      map_zero' := by rw [map_zero, map_zero]
      map_add' := fun a b => by rw [map_add (f := _), map_add (f := _)] }
  have hsurjf : Function.Surjective f := fun b => by
    obtain ⟨c, rfl⟩ := hsurj b
    refine ⟨p.pr c, ?_⟩
    show π (p.sec (p.pr c)) = π c
    rw [p.sec_pr, map_mul, πe, one_mul]
  refine ⟨RingEquiv.ofBijective f ⟨f.injective, hsurjf⟩, fun a => ?_, fun a => ?_⟩
  · show Valued.v (π (p.sec a)) ≤ 1 ↔ a ∈ 𝒪[k]
    rw [p.int_iff, ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← isInt_Ov, ← hint, hs]
  · exact norm_idele_chart p π halg πe πce a

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt

theorem absAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (q : GlobalTheory.LatPair.Unif k),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F p.v (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.normV D p.v (p.idele q.unit)) = ((resCard k : ℕ) : ℝ)⁻¹ := by
  intro D k _ _ _ _ p q
  obtain ⟨φ, hφ, hn⟩ := chartAt D k p
  have h1 := GlobalTheory.T.valued_v_map_irreducible_eq_ofAdd_neg_one D.host.F p.v k φ hφ q.1 q.2
  have h2 := GlobalTheory.T.card_residueField_of_ringEquiv_adicCompletion D.host.F p.v k φ hφ
  have h3 : (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))).log = -1 := by
    first | rfl | simp [WithZero.log] | exact WithZero.log_coe _
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, hn, GlobalTheory.LatPair.Unif.unit, Units.val_mk0, h1, resCard, h2, h3, zpow_neg_one]

open GlobalTheory.SplitLinAt GlobalTheory.SplitLinear

theorem absFin_unif {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (q : GlobalTheory.LatPair.Unif k) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (idl p q.unit) = ((resCard k : ℕ) : ℝ)⁻¹ := by
  rw [idl_eq, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, finprod_eq_single _ p.v, absAt D k p q]
  intro w hw
  rw [normOff D k p _ w hw, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  simp

theorem lam_unif {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (q : GlobalTheory.LatPair.Unif k) (χ : (AE D)ˣ →* Circle) (r : ℝ) :
    ((lam p χ r q.unit : ℂˣ) : ℂ) = (((resCard k : ℝ) ^ (-r) : ℝ) : ℂ) * (χ (p.idele q.unit) : ℂ) := by
  rw [lam_val, absFin_unif, idl_eq, Real.inv_rpow (Nat.cast_nonneg _), ← Real.rpow_neg (Nat.cast_nonneg _), mul_comm]

end GlobalTheory.LinExactAt

namespace GlobalTheory.LinExactAt
open GlobalTheory.SplitLinAt GlobalTheory.SplitLinear

theorem linExact : ∀ D : D7, GlobalTheory.FinPl.LinExact D := by
  intro D k _ _ _ _ p q ψ S T χS χT om hW
  refine ⟨lam p χT⁻¹ ((T.rank : ℝ) / 2), lam p χS (-(S.rank : ℝ) / 2),
    fun h => lamUnram D k p _ _ (unram_inv h), fun h => lamUnram D k p _ _ h, ?_, ?_,
    fun n n' _ _ _ _ α β LS LT f₀ Ψ f hO g h => linFirst D k p ψ S T χS χT om hW n n' α β LS LT f₀ Ψ f hO g h⟩
  · rw [lam_unif, MonoidHom.inv_apply, chrPow, zpow_neg, zpow_one, neg_div]
  · rw [lam_unif, chrPow, zpow_one, neg_div, neg_neg]

end GlobalTheory.LinExactAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivarianceStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearModel_splitPlace_characterEquivariance : ∀ D : D7, GlobalTheory.FinPl.LinExact D := by
  first | exact @GlobalTheory.LinExactAt.linExact | exact GlobalTheory.LinExactAt.linExact | (intros; apply GlobalTheory.LinExactAt.linExact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem continuous_comm : letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
    Continuous (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := by
  letI : Algebra (Af D.host.F) (D.host.E ⊗[D.host.F] Af D.host.F) := Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (D.host.E ⊗[D.host.F] Af D.host.F) := moduleTopology (Af D.host.F) _
  haveI : IsModuleTopology (Af D.host.F) (D.host.E ⊗[D.host.F] Af D.host.F) := ⟨rfl⟩
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  let φ : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[Af D.host.F] (D.host.E ⊗[D.host.F] Af D.host.F) :=
    { toFun := Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
      map_add' := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).map_add
      map_smul' := fun r x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a e =>
          rw [TensorProduct.smul_tmul', Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul,
            Algebra.smul_def]
          show e ⊗ₜ[D.host.F] (r • a) = ((1 : D.host.E) ⊗ₜ[D.host.F] r) * (e ⊗ₜ[D.host.F] a)
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul]
        | add x y hx hy =>
          rw [smul_add, map_add (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E),
            map_add (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E), hx, hy, smul_add] }
  haveI : ContinuousAdd (D.host.E ⊗[D.host.F] Af D.host.F) := IsModuleTopology.toContinuousAdd (Af D.host.F) _
  haveI : ContinuousSMul (Af D.host.F) (D.host.E ⊗[D.host.F] Af D.host.F) := IsModuleTopology.toContinuousSMul (Af D.host.F) _
  exact IsModuleTopology.continuous_of_linearMap φ

def finGL (V : HSp D) (h : GA D V) : GL (Fin V.rank) (EAf D) := bc (toEAf D) (matHom V h)

theorem finGL_val (V : HSp D) (h : GA D V) : (finGL V h).val = finM V rfl h := by
  rw [finM_rfl]; rfl

theorem continuous_finGL (V : HSp D) : letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
    Continuous (finGL V) := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hv : Continuous fun h : GA D V => (finGL V h).val :=
    (GlobalTheory.Mem.VolExists.continuous_finMat (σ := D.sp.cm.sig) V.gram).matrix_map continuous_comm
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  have e : (fun h : GA D V => ((finGL V h)⁻¹ : GL (Fin V.rank) (EAf D)).val) = fun h => (finGL V h⁻¹).val := by
    funext h
    simp only [finGL, map_inv]
  rw [e]
  exact hv.comp continuous_inv

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}
theorem law_left (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F)))
    (S : StepLevel D.host.F D.host.E (sigD D) V.gram T f bad) (cl : Type)
    (yc : cl → UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC V.gram (embT D))) :
    ∀ γ ∈ GQ V, ∀ g, rdS θ V rfl S yc (fun c => Ψ (yc c)) y (γ * g) = rdS θ V rfl S yc (fun c => Ψ (yc c)) y g := by
  have key := GlobalTheory.AdForm.rdS_val D θ hθ V V.rank rfl V.gram (by simp) T f bad S cl yc hb Ψ hΨ
  intro γ hγ g
  obtain ⟨γ0, h0, e⟩ := rat_mt V γ hγ
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := key y g
  obtain ⟨⟨x', hx'⟩, hu', hv'⟩ := key y (γ * g)
  let z : Frames (gramC V.gram (embT D)) :=
    ⟨fun τ => infM θ V rfl g τ * y.1 τ, fun τ => by rw [det_mul]; exact (hu τ).mul (y.2 τ)⟩
  let z' : Frames (gramC V.gram (embT D)) :=
    ⟨fun τ => infM θ V rfl (γ * g) τ * y.1 τ, fun τ => by rw [det_mul]; exact (hu' τ).mul (y.2 τ)⟩
  have e1 := hv' x' z' hx' (fun τ => rfl)
  have e2 := hv x z hx (fun τ => rfl)
  have hxx : x'.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * x.1 * (1 : S.U).1 := by
    apply Units.ext
    simp only [Units.val_mul, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
    rw [hx', finM_mul, rat_finM V γ0 γ e, hx]
  have hzz : IsTr (atInf (embT D) γ0.val) z z' := fun τ => by
    show infM θ V rfl (γ * g) τ * y.1 τ = atInf (embT D) γ0.val τ * (infM θ V rfl g τ * y.1 τ)
    rw [infM_mul, rat_infM θ hθ V γ0 γ e, Matrix.mul_assoc]
  have e3 := hΨ γ0 h0 x x' 1 hxx z' z hzz
  rw [map_one, Units.val_one, one_mul] at e3
  exact e1.trans (e3.trans e2.symm)

theorem law_level (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F)))
    (S : StepLevel D.host.F D.host.E (sigD D) V.gram T f bad) (cl : Type)
    (yc : cl → UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC V.gram (embT D))) :
    ∀ k ∈ GfC V, ∀ κ : S.U, κ.1.1 = finM V rfl k → ∀ g,
      rdS θ V rfl S yc (fun c => Ψ (yc c)) y (g * k) = (S.chi κ : ℂ) * rdS θ V rfl S yc (fun c => Ψ (yc c)) y g := by
  have key := GlobalTheory.AdForm.rdS_val D θ hθ V V.rank rfl V.gram (by simp) T f bad S cl yc hb Ψ hΨ
  intro k hk κ hκ g
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := key y g
  obtain ⟨⟨x', hx'⟩, hu', hv'⟩ := key y (g * k)
  let z : Frames (gramC V.gram (embT D)) :=
    ⟨fun τ => infM θ V rfl g τ * y.1 τ, fun τ => by rw [det_mul]; exact (hu τ).mul (y.2 τ)⟩
  have hz : IsTr (infM θ V rfl (g * k)) y z := fun τ => by
    show infM θ V rfl g τ * y.1 τ = infM θ V rfl (g * k) τ * y.1 τ
    rw [infM_mul, infM_fin θ V k hk, Matrix.mul_one]
  have e1 := hv' x' z hx' hz
  have e2 := hv x z hx (fun τ => rfl)
  have hxx : x'.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) 1 * x.1 * κ.1 := by
    apply Units.ext
    simp only [Units.val_mul, map_one, Units.val_one, Matrix.one_mul]
    rw [hx', finM_mul, hx, hκ]
  have h1 : IsTr (atInf (embT D) (1 : GL (Fin V.rank) D.host.E).val) z z := fun τ => by
    show z.1 τ = atInf (embT D) (1 : GL (Fin V.rank) D.host.E).val τ * z.1 τ
    simp [atInf]
  have e3 := hΨ 1 (Subgroup.one_mem _) x x' κ hxx z z h1
  exact e1.trans (e3.trans (congrArg _ e2.symm))

theorem law_real (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F)))
    (S : StepLevel D.host.F D.host.E (sigD D) V.gram T f bad) (cl : Type)
    (yc : cl → UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC V.gram (embT D))) :
    ∀ k ∈ GinfC V, ∀ y', IsTr (infM θ V rfl k) y y' → ∀ g,
      rdS θ V rfl S yc (fun c => Ψ (yc c)) y (g * k) = rdS θ V rfl S yc (fun c => Ψ (yc c)) y' g := by
  have key := GlobalTheory.AdForm.rdS_val D θ hθ V V.rank rfl V.gram (by simp) T f bad S cl yc hb Ψ hΨ
  intro k hk y' hy' g
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := key y' g
  obtain ⟨-, -, hv'⟩ := key y (g * k)
  let z : Frames (gramC V.gram (embT D)) :=
    ⟨fun τ => infM θ V rfl g τ * y'.1 τ, fun τ => by rw [det_mul]; exact (hu τ).mul (y'.2 τ)⟩
  have hz : IsTr (infM θ V rfl (g * k)) y z := fun τ => by
    show infM θ V rfl g τ * y'.1 τ = infM θ V rfl (g * k) τ * y.1 τ
    rw [infM_mul, Matrix.mul_assoc, ← hy' τ]
  have hx2 : x.1.1 = finM V rfl (g * k) := by rw [finM_mul, finM_inf V k hk, Matrix.mul_one, hx]
  exact (hv' x z hx2 hz).trans (hv x z hx (fun τ => rfl)).symm

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

theorem continuous_infM (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    Continuous fun g : GA D V => infM θ V rfl g τ := by
  simp_rw [infM_rfl]
  exact GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ τ)

theorem law_cont (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F)))
    (S : StepLevel D.host.F D.host.E (sigD D) V.gram T f bad) (cl : Type)
    (yc : cl → UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (lam) (hval : ∀ x, Ψ x ∈ ValC (gramC V.gram (embT D)) lam)
    (y : Frames (gramC V.gram (embT D)))
    (hW : ∃ W : Subgroup (GA D V), IsOpen (W : Set (GA D V)) ∧ ∀ k ∈ W, k ∈ GfC V → ∀ κ : S.U, κ.1.1 = finM V rfl k → S.chi κ = 1) :
    Continuous (rdS θ V rfl S yc (fun c => Ψ (yc c)) y) := by
  obtain ⟨W, hWo, hW⟩ := hW
  have key := GlobalTheory.AdForm.rdS_val D θ hθ V V.rank rfl V.gram (by simp) T f bad S cl yc hb Ψ hΨ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have hmem : ∀ h : GA D V, finGL V h ∈ UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := fun h => by
    obtain ⟨⟨x, hx⟩, -⟩ := key y h
    have e : finGL V h = x.1 := Units.ext (by rw [finGL_val, hx])
    rw [e]; exact x.2
  let fin2 : GA D V → UPts (sigD D) V.gram (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := fun h => ⟨finGL V h, hmem h⟩
  have hc2 : Continuous fin2 := (continuous_finGL V).subtype_mk _
  have hO := S.U_open
  rw [continuous_iff_continuousAt]
  intro g0
  obtain ⟨⟨x0, hx0⟩, -, -⟩ := key y g0
  obtain ⟨P, -, hP⟩ := Submodule.mem_map.1 (hval x0)
  let F : GA D V → ℂ := fun g =>
    (∏ τ, ((1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ * (infM θ V rfl g τ * y.1 τ)).det ^ shiftOf lam τ) *
    MvPolynomial.eval (fun q : D.what₂.Tau × Fin V.rank × Fin V.rank =>
      ((1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) q.1 * (infM θ V rfl g q.1 * y.1 q.1)) q.2.1 q.2.2) P
  have hM : ∀ τ, Continuous fun g : GA D V =>
      (1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ * (infM θ V rfl g τ * y.1 τ) := fun τ =>
    continuous_const.matrix_mul ((continuous_infM θ hθ V τ).matrix_mul continuous_const)
  have hFc : Continuous F := by
    have hdet : ∀ τ g, ((1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ *
        (infM θ V rfl g τ * y.1 τ)).det ≠ 0 := by
      intro τ g
      obtain ⟨-, hu, -⟩ := key y g
      rw [Pi.one_apply, one_mul, det_mul]
      exact ((hu τ).mul (y.2 τ)).ne_zero
    exact Continuous.mul
      (continuous_finsetProd _ fun τ _ => ((hM τ).matrix_det).zpow₀ _ fun g => Or.inl (hdet τ g))
      ((MvPolynomial.continuous_eval P).comp (continuous_pi fun q => (hM q.1).matrix_elem q.2.1 q.2.2))
  refine hFc.continuousAt.congr ?_
  have hN : IsOpen {g : GA D V | ((fin2 (g0⁻¹ * g) : GL (Fin V.rank) (EAf D)) ∈ S.U) ∧ pf V (g0⁻¹ * g) ∈ W} :=
    (hO.preimage (hc2.comp (continuous_const.mul continuous_id))).inter
      (hWo.preimage ((continuous_pf V).comp (continuous_const.mul continuous_id)))
  have hg0 : g0 ∈ {g : GA D V | ((fin2 (g0⁻¹ * g) : GL (Fin V.rank) (EAf D)) ∈ S.U) ∧ pf V (g0⁻¹ * g) ∈ W} := by
    refine ⟨?_, ?_⟩
    · have e : (fin2 (g0⁻¹ * g0) : GL (Fin V.rank) (EAf D)) = 1 := by
        show finGL V (g0⁻¹ * g0) = 1
        rw [inv_mul_cancel]; exact map_one _
      show (fin2 (g0⁻¹ * g0) : GL (Fin V.rank) (EAf D)) ∈ S.U
      rw [e]; exact S.U.one_mem
    · show pf V (g0⁻¹ * g0) ∈ W
      rw [inv_mul_cancel, pf_one]; exact W.one_mem
  filter_upwards [hN.mem_nhds hg0] with g hg
  obtain ⟨hU, hWg⟩ := hg
  let κ : S.U := ⟨(fin2 (g0⁻¹ * g) : GL (Fin V.rank) (EAf D)), hU⟩
  have hκ1 : S.chi κ = 1 := hW (pf V (g0⁻¹ * g)) hWg (pf_fin V _) κ (by
    show (finGL V (g0⁻¹ * g)).val = _
    rw [finGL_val, finM_pf])
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := key y g
  let z : Frames (gramC V.gram (embT D)) :=
    ⟨fun τ => infM θ V rfl g τ * y.1 τ, fun τ => by rw [det_mul]; exact (hu τ).mul (y.2 τ)⟩
  have hxx : x.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) 1 * x0.1 * κ.1 := by
    apply Units.ext
    simp only [Units.val_mul, map_one, Units.val_one, Matrix.one_mul]
    have e : g = g0 * (g0⁻¹ * g) := by rw [mul_inv_cancel_left]
    rw [hx, e, finM_mul, ← hx0]
    exact congrArg _ (finGL_val V _).symm
  have h1 : IsTr (atInf (embT D) (1 : GL (Fin V.rank) D.host.E).val) z z := fun τ => by
    show z.1 τ = atInf (embT D) (1 : GL (Fin V.rank) D.host.E).val τ * z.1 τ
    simp [atInf]
  have e3 := hΨ 1 (Subgroup.one_mem _) x0 x κ hxx z z h1
  rw [hκ1, Units.val_one, one_mul] at e3
  rw [hv x z hx (fun τ => rfl), e3, ← hP]
  rfl

end GlobalTheory.AdForm.RdLaw

noncomputable section
namespace GlobalTheory.AdForm.RdLaw

theorem rdS_laws : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E), J = V.gram.reindex (finCongr hn) (finCongr hn) → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (cl : Type) (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → ∀ lam, ∀ φ ∈ FiC S (embT D) lam yc, ∀ y : Frames (gramC J (embT D)), (∀ γ ∈ GQ V, ∀ g, rdS θ V hn S yc φ y (γ * g) = rdS θ V hn S yc φ y g) ∧ (∀ k ∈ GfC V, ∀ κ : S.U, κ.1.1 = finM V hn k → ∀ g, rdS θ V hn S yc φ y (g * k) = (S.chi κ : ℂ) * rdS θ V hn S yc φ y g) ∧ (∀ k ∈ GinfC V, ∀ y', IsTr (infM θ V hn k) y y' → ∀ g, rdS θ V hn S yc φ y (g * k) = rdS θ V hn S yc φ y' g) ∧ ((∃ W : Subgroup (GA D V), IsOpen (W : Set (GA D V)) ∧ ∀ k ∈ W, k ∈ GfC V → ∀ κ : S.U, κ.1.1 = finM V hn k → S.chi κ = 1) → Continuous (rdS θ V hn S yc φ y)) := by
  intro D θ hθ V n hn J hJ T f bad S cl yc hb lam φ hφ y
  subst hn
  simp only [finCongr_refl, reindex_refl_refl] at hJ
  subst hJ
  obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hφ
  have hA : Ψ ∈ AdFun S (embT D) := (Submodule.mem_inf.1 hΨ).1
  have hval : ∀ x, Ψ x ∈ ValC (gramC V.gram (embT D)) lam := fun x =>
    (Submodule.mem_pi.1 (Submodule.mem_inf.1 hΨ).2) x (Set.mem_univ _)
  exact ⟨law_left θ hθ V T f bad S cl yc hb Ψ hA y, law_level θ hθ V T f bad S cl yc hb Ψ hA y,
    law_real θ hθ V T f bad S cl yc hb Ψ hA y, law_cont θ hθ V T f bad S cl yc hb Ψ hA lam hval y⟩

end GlobalTheory.AdForm.RdLaw
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevDatYZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.LevYZero

open Formalism.IndefR.Lev Formalism.L2.DIV

theorem lev_datY_zero {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (r t : ℕ) (hr : r ≤ V.rank) (hn : V.rank = r) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ ξ) (hL : L = datY V.rank r t 0 hr Pg ∅ P χ ξ Frm.B) (g : GL (Fin V.rank) (Lev.EAf D))
    (hU : g ∈ UA D.sp.cm V.gram) :
    (g ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L ↔ g ∈ St β ∧ (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) ∈ P.H) ∧
      ∀ h : (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) ∈ P.H, levFn β L g = P.chi ⟨_, h⟩ := by
  subst hL
  have hP : (datY (D := D) V.rank r t 0 hr Pg ∅ P χ ξ Frm.B).P = P := by simp [datY]
  constructor
  · rw [mem_lev, mem_parLev]
    constructor
    · rintro ⟨⟨-, hS, -, -⟩, hH⟩
      refine ⟨hS, ?_⟩
      rw [hP] at hH
      exact hH
    · rintro ⟨hS, hH⟩
      refine ⟨⟨hU, hS, fun PP _ => ?_, fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩, ?_⟩
      · rw [mem_blockTri]
        intro i j hij
        exfalso
        have hi : (i : ℕ) < r := hn ▸ i.2
        have hj : (j : ℕ) < r := hn ▸ j.2
        simp [datY, blkOf, hi, hj] at hij
      · show rTup β _ g ∈ _
        rw [hP]
        exact hH
  · intro h
    unfold levFn
    change ext1 P.H P.chi (fun PP : Pg => upperLeftBlock hr (redFn β PP.1 g)) * _ * _ = _
    simp only [datY, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
    exact extendOne_of_mem _ h

end GlobalTheory.LevYZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyNhdsOneAdelicMatrixCongruentOneAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyNhdsOneAdelicMatrixCongruentOneAtPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

namespace GlobalTheory.TwU.NearOne

theorem congAt_eventually_nhds_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n N : ℕ) (P : HeightOneSpectrum (𝓞 E)), letI := Formalism.L2.Col.rlt_top (F := F) (E := E); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, GlobalTheory.TwU.CongAt P N u := by
  intro F E _ _ _ _ _ n N P
  letI : TopologicalSpace (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Formalism.L2.Col.rlt_top (F := F) (E := E)
  haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  show ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ a b, _
  refine Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => ?_
  have hop : IsOpen ((fun y : E ⊗[F] FiniteAdeleRing (𝓞 F) F =>
      Formalism.L2.Col.iA F E (((Formalism.L2.Col.qOf P : ℕ) : E) ^ N)⁻¹ * y) ⁻¹'
      (Formalism.L2.Herm.intAf F E : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) :=
    Formalism.L2.Col.rlt_isOpen_intAf.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ∈ (fun y : E ⊗[F] FiniteAdeleRing (𝓞 F) F =>
      Formalism.L2.Col.iA F E (((Formalism.L2.Col.qOf P : ℕ) : E) ^ N)⁻¹ * y) ⁻¹'
      (Formalism.L2.Herm.intAf F E : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    simp only [Set.mem_preimage, mul_zero]
    exact zero_mem _
  have hcont : Continuous fun u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      (u : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b :=
    (Units.continuous_val.matrix_elem a b).sub continuous_const
  have ht := hcont.tendsto' 1 0 (by simp)
  filter_upwards [ht (hop.mem_nhds h0)] with u hu
  refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simpa [Matrix.sub_apply] using hu

end GlobalTheory.TwU.NearOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyNhdsOneAdelicMatrixCongruentOneAtPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_nhds_one_adelicMatrixCongruentOneAtPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n N : ℕ) (P : HeightOneSpectrum (𝓞 E)), letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, GlobalTheory.TwU.CongAt P N u := by
  first | exact @GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one | exact GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one | (intros; apply GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupsCharactersFamily
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TupChars

section Loc

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cmp (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) : kˣ →* ℂˣ :=
  (Circle.toUnits.comp χ).comp (GlobalTheory.LocChar.unitsHom (ofSplit q))

theorem isComp_cmp (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) : (ofSplit q).IsComp χ (cmp q χ) := by
  intro x a ha
  have : GlobalTheory.LocChar.unitsHom (ofSplit q) x = a := Units.ext ha.symm
  simp only [cmp, MonoidHom.comp_apply, this]
  rfl

theorem cmp_apply (q : GlobalTheory.FinPl.SplitPt D k) (χ : (AE D)ˣ →* Circle) (x : kˣ) :
    ((cmp q χ x : ℂˣ) : ℂ) = (χ (GlobalTheory.LocChar.unitsHom (ofSplit q) x) : ℂ) := rfl

theorem unitsHom_int (q : GlobalTheory.FinPl.SplitPt D k) (y : kˣ) (hy : valuation k (y : k) = 1) :
    finPart D ((GlobalTheory.LocChar.unitsHom (ofSplit q) y : (AE D)ˣ) : AE D) ∈ intAE D := by
  have he1 : q.e * q.e = q.e := q.split.1
  show finPart D (q.sec y + (1 - q.e)) ∈ intAE D
  rw [(finPart D).map_add, (finPart D).map_sub, (finPart D).map_one]
  exact add_mem ((q.int_iff _).1 ((Valuation.mem_integer_iff _ _).2 hy.le))
    (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, he1])))

theorem unit_trivial (q : GlobalTheory.FinPl.SplitPt D k) {χ : (AE D)ˣ →* Circle}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ q.v) (x : kˣ) (hx : valuation k (x : k) = 1) :
    χ (GlobalTheory.LocChar.unitsHom (ofSplit q) x) = 1 := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  have he1 : q.e * q.e = q.e := q.split.1
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hes : q.e * q.sec x = q.sec x := by
    have := q.sec_pr (q.sec x)
    rw [q.pr_sec] at this
    exact this.symm
  have hz : algebraMap (AF D.host.F) (AE D) ε * (q.sec x - q.e) = q.sec x - q.e := by
    rw [← hsum]
    linear_combination (1 - cA D q.e) * hes - he1 + (q.sec x - 1) * hec
  obtain ⟨hi, hf⟩ := (GlobalTheory.VacStabFixed.supp_iff hε _).1 hz
  have hU : ((GlobalTheory.LocChar.unitsHom (ofSplit q) x : (AE D)ˣ) : AE D) = 1 + (q.sec x - q.e) := by
    show q.sec x + (1 - q.e) = _
    ring
  refine h _ ?_ (fun w hw => ?_) (unitsHom_int q x hx) ?_
  · rw [hU, (infPart D).map_add, (infPart D).map_one, hi, add_zero]
  · rw [hU, (finPart D).map_add, (finPart D).map_one, RingHom.map_add, RingHom.map_one, hf w hw, add_zero]
  · rw [← map_inv]
    exact unitsHom_int q x⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one])

theorem val_eq_one_of_sub (x : kˣ) (hx : valuation k ((x : k) - 1) < 1) : valuation k (x : k) = 1 := by
  have e : (x : k) = ((x : k) - 1) + 1 := by ring
  rw [e, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]

end Loc

section Pack

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex}

end Pack

end GlobalTheory.TupChars

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTrivialNearOneOfLocalBadPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTrivialNearOneOfLocalBadPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

noncomputable section
namespace GlobalTheory.ChiCont

theorem chi_eq_one_of_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F)))
    (S : StepLevel F E σ J T f bad) (u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (s : Finset (HeightOneSpectrum (𝓞 F)))
    (H : ∀ v ∈ s, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) →
      bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1) :
    ∀ κ : S.U, (∀ v ∈ s, bc (prV (E := E) v) κ.1 = bc (prV (E := E) v) u) →
      (∀ v ∈ bad, v ∉ s → bc (prV (E := E) v) κ.1 = 1) → S.chi κ = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    intro κ _ hb
    exact S.chi_triv κ (fun v hv => hb v hv (Finset.notMem_empty v))
  | @insert v s hvs ih =>
    intro κ hu hb
    have hκ := (S.U_eq κ.1).1 κ.2
    set x0 := Formalism.UG.P.afsplitU v (bc (prV (E := E) v) κ.1) 1 with hx0
    have hx0v : bc (prV (E := E) v) x0 = bc (prV (E := E) v) κ.1 := Formalism.UG.P.afsplit_right1 _ _ _
    have hx0w : ∀ w, w ≠ v → bc (prV (E := E) w) x0 = 1 := by
      intro w hw
      apply Units.ext
      rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
      simp
    have hx0U : x0 ∈ S.U := by
      rw [S.U_eq]
      refine ⟨Formalism.UG.P.afsplitU_mem v _ _ _ _ (Formalism.UG.P.afsplit_bc_mem _ _ v κ.1 hκ.1) (one_mem _), fun w => ?_⟩
      by_cases hw : w = v
      · subst hw
        rw [hx0v]
        exact hκ.2 w
      · rw [hx0w w hw]
        exact one_mem _
    let x : S.U := ⟨x0, hx0U⟩
    have hchix : S.chi x = 1 :=
      H v (Finset.mem_insert_self v s) x hx0w (by rw [hx0v]; exact hu v (Finset.mem_insert_self v s))
    let κ' : S.U := x⁻¹ * κ
    have hκ'w : ∀ w, w ≠ v → bc (prV (E := E) w) κ'.1 = bc (prV (E := E) w) κ.1 := by
      intro w hw
      show bc (prV (E := E) w) (x0⁻¹ * κ.1) = _
      rw [map_mul, map_inv, hx0w w hw, inv_one, one_mul]
    have hκ'v : bc (prV (E := E) v) κ'.1 = 1 := by
      show bc (prV (E := E) v) (x0⁻¹ * κ.1) = _
      rw [map_mul, map_inv, hx0v, inv_mul_cancel]
    have hchi' : S.chi κ' = 1 := by
      refine ih (fun w hw => H w (Finset.mem_insert_of_mem hw)) κ' ?_ ?_
      · intro w hw
        have hwv : w ≠ v := fun h => hvs (h ▸ hw)
        rw [hκ'w w hwv]
        exact hu w (Finset.mem_insert_of_mem hw)
      · intro w hw hws
        by_cases hwv : w = v
        · subst hwv; exact hκ'v
        · rw [hκ'w w hwv]
          exact hb w hw (by simp [hwv, hws])
    have hk : κ = x * κ' := by rw [mul_inv_cancel_left]
    rw [hk, map_mul, hchix, hchi', one_mul]

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Vs : Set (HeightOneSpectrum (𝓞 F))), Vs.Finite → (∀ v ∈ bad, v ∈ Vs) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ v ∈ Vs, ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) → bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) := by
  intro F E _ _ _ _ _ σ n J T f bad S Vs hVs hbad hloc
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  have hall : ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ v ∈ Vs,
      ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) →
        bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1 :=
    (Filter.eventually_all_finite hVs).2 hloc
  filter_upwards [hall] with u hu κ hκu
  refine chi_eq_one_of_split σ J T f bad S u hVs.toFinset
    (fun v hv => hu v (hVs.mem_toFinset.1 hv)) κ (fun v _ => by rw [hκu]) ?_
  intro v hv hvs
  exact absurd (hVs.mem_toFinset.2 (hbad v hv)) hvs

end GlobalTheory.ChiCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTrivialNearOneOfLocalBadPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_trivial_near_one_of_local_bad_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Vs : Set (HeightOneSpectrum (𝓞 F))), Vs.Finite → (∀ v ∈ bad, v ∈ Vs) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ v ∈ Vs, ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) → bc (prV (E := E) v) x.1 = bc (prV (E := E) v) u → S.chi x = 1) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) := by
  first | exact @GlobalTheory.ChiCont.main | exact GlobalTheory.ChiCont.main | (intros; apply GlobalTheory.ChiCont.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpParameterOfTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpParameterOfTransfer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (VacFin)

noncomputable section

namespace GlobalTheory.ChainTw

theorem upParQ_of_transfer : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, UpParQ D := by
  intro hRD hHowe D hND c w hw k hk s s' hs hs' p hp u B φ hu v _ hne
  obtain ⟨hr, _, hfl⟩ := hs
  obtain ⟨hr', _, hfl'⟩ := hs'
  have hlat' : ∀ (f : GA D s'.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
      GlobalTheory.LFun.IsParamFun D.sp.cm.sig s'.V.gram s'.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔
        GlobalTheory.LFun.IsParamFunV s'.V c.S f B := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hw.com (k + 1) hk _ hfl').2
  have hlat : ∀ (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
      GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔
        GlobalTheory.LFun.IsParamFunV s.V c.S f B := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hw.com k hk.le _ hfl).2
  set y := PiLocalization₂.val u v with hy
  have hy0 : y ≠ 0 := by
    intro h; apply hne; funext x; simp [Step.up, h]
  have hyB : IsParamFunV s.V c.S (fun g => conj (y g)) B := (hlat _ B).1 (hu.2 v hy0)
  have hconj : (fun x => conj (p.up φ y x)) =
      fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν := by
    funext x; simp only [Step.up]; rw [← integral_conj]; congr 1; funext g; simp [map_mul]
  have hne' : (fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν) ≠ 0 := by
    rw [← hconj]; intro h; apply hne; funext x; simpa using congrFun h x
  have hrank : s'.V.rank = s.V.rank + D.R.t := by
    have h1 : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    have h2 : s.V.rank = D.R.rankY k := hfl.rank
    rw [h1, h2, rankY_succ]
  have hYA := PiLocalization₂.val_autCusp c s u v
  have hfock := GlobalTheory.T.twistedChainStep_fockVectors_spherical_offS D hND c w hw k hk s s' ⟨hr, by assumption, hfl⟩ ⟨hr', by assumption, hfl'⟩ p hp
  unfold ParFun
  rw [hlat', hconj]
  intro w0 hw0 w' h
  have hw0' : w0 ∉ c.S := by simpa using hw0
  exact GlobalTheory.T.thetaIntegral_conjCuspForm_parameterTransfer hRD D (GlobalTheory.T.sphericalParameterTransfer_all_finitePlaces hHowe D) c.ψ c.θ s.V s'.V _ _ p.ω hw.com.inf hp.weil D.R.t hrank s.ν s.fd
    hfl.haar hfl.fund w0 (fun w'' hw'' => GlobalTheory.T.thetaChain_step_chars_unramified_off_S D c hw.com k hk w0 hw0' w'' hw'') w' h (p.pt φ)
    ((hfock.1 φ).2.2 w0 hw0') y (B w') hYA.1 hYA.2 (hyB w0 hw0 w' h) hne'

end GlobalTheory.ChainTw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpParameterOfTransferStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainThetaLiftUp_parameter_of_transfer : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, UpParQ D := by
  first | exact @GlobalTheory.ChainTw.upParQ_of_transfer | exact GlobalTheory.ChainTw.upParQ_of_transfer | (intros; apply GlobalTheory.ChainTw.upParQ_of_transfer <;> assumption)
end
end
