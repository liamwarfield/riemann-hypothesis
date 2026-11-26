module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftAdjointEqUpwardThetaIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPairThetaLowest
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIPEqStarL2
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSumOfRank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfInnerEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerNeSpherical
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenform
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationAtRealPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdjointComp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerPosOfInnerNe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacOmFin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.FactorInf

theorem fockVac_om_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) {θ : InfFam D}
    (hθ : IsInfFam θ) {γ : GA D T} (hγ : γ ∈ GfC T) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ J f) :
    IsFockVacAt (heisO ψ S T) θ τ J (om (1, γ) f) := by
  have e : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, compAt θ τ (mt T γ) * z * compAt θ τ (mt S (1 : GA D S)⁻¹) = z := fun z => by
    rw [inv_one, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hγ τ,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S (Subgroup.one_mem _) τ, Matrix.one_mul, Matrix.mul_one]
  intro z
  have h := congrArg (om (1, γ)) (hv z)
  unfold annih at h ⊢
  rw [map_add (f := _), map_smul, GlobalTheory.OrientedHeis.om_dRho hom hθ 1 γ τ z hf, GlobalTheory.OrientedHeis.om_dRho hom hθ 1 γ τ (J z) hf,
    e, e, map_zero] at h
  exact h

theorem factInf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FactInf R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ u hu γ hγ P P'
  have hW := hL.thP.ωP i t
  have hθ : IsInfFam R.θ := hL.models.inf
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP at this
    rwa [GlobalTheory.FiniteFock.pureTensorO_one] at this
  have hvac : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t) :=
    GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hL.thP.vP i t) hth
  set f₁ := R.ωP i t (1, γ) (R.vP i t) with hf₁
  have hth1 : IsThetaFunO R.ψ (Vc D i) (Wc D i) f₁ := hW.om_pres _ _ hth
  have hvac1 : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) f₁ :=
    fun τ => fockVac_om_fin hW hθ hγ τ _ hth (hvac τ)
  have hmul : R.ωP i t (1, u * γ) (R.ptP i t P) = R.ωP i t (1, u) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
      (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f₁ P) := by
    have e : ((1 : GA D (Vc D i)), u * γ) = (1, u) * (1, γ) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    congr 1
    unfold RealDat.ptP
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ hW R.θ hθ 1 (Subgroup.one_mem _) γ hγ _ _ _ _ _ P hth
  obtain ⟨c, hc⟩ := GlobalTheory.T.fockVacuum_pairing_polynomial_translates_scalar D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW hθ (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank)
    (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => isCartanInv_one_of_onb (hL.models.BV i τ))
    (GlobalTheory.AdTh.VecFock.isCartanInv_cart _) (hL.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hL.models.order i τ)) μ 𝓕 hμ u hu P P'
  have hne := (vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ).1
  rw [hmul]
  unfold RealDat.ptP
  rw [hc f₁ _ hth1 hth hvac1 hvac, hc _ _ hth hth hvac hvac]
  unfold coef
  rw [← hf₁]
  field_simp

end GlobalTheory.RawLift.FactorInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealLow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.RealLowPf

theorem realLow : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, RealLow R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hP i t
  exact GlobalTheory.T.realLowestKType_of_extremalVectorCase D G Pl0 T A Ks R F hL hP i t (GlobalTheory.T.fockCoefficient_extremal_eq_discreteSeries D G Pl0 T A Ks R F hL hP i t)

end GlobalTheory.RawLift.RealLowPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoeffVanishesOffLevelBadPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoeffVanishesOffLevelBadPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.BadSuppPf

theorem rank_le (D : D7) (i : Fin D.R.m) : (Wc D i).rank ≤ (Vc D i).rank := by
  rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]
  exact r_le_V i

theorem badSupp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ P hP e f hPf k hk hnot
  classical
  have hv := hL.thP.vP i t
  have hθ := GlobalTheory.VecTheta.isThetaFunO_thPVec hv
  obtain ⟨-, e', he', hth⟩ := hv
  obtain ⟨cV, hBV⟩ := hL.lev.βV i
  obtain ⟨cW, hBW⟩ := hL.lev.βW i
  rw [one_pow] at hBV hBW
  have hsdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βV i)
  have hsdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βW i)
  have hdat : (fun x : WO (Vc D i) (Wc D i) => if IsHalf (cA D e') x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) *
          omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
        else 0) = GlobalTheory.FinZeta.levDatum (Vc D i) (Wc D i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t) (R.xiR t) e' := by
    funext x
    simp only [GlobalTheory.FinZeta.levDatum, GlobalTheory.Survey.LevelVectorSizeBounds.omegaG_triv R i]
  rw [hdat] at hth
  obtain ⟨hkf, hk1⟩ := GlobalTheory.SuppLocal.suppF_local D (Wc D i) P e f k hPf hk
  have hZ : ∀ PP, PP ∈ R.Pg ∪ R.Q t ↔ PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ R.Q t := fun PP => Finset.mem_union
  have hsb := GlobalTheory.FinZeta.isSBHalf_levDatum D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv)
    (R.Q t) (R.xiR t) (R.Pg ∪ R.Q t) e' hsdV hsdW hBV.1 hBW.1 he'
  have horth := GlobalTheory.ThetaOrth.orth D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hF i t).datum (R.ΛV i) (R.ΛW i) hsdV hsdW
    (R.Pg ∪ R.Q t) e' he' (R.vacP i) _ (R.vP i t) hsb hth hθ μ 𝓕 hμ k hkf (fun x hx => by
      by_contra hx'
      obtain ⟨k', hk', hag⟩ := GlobalTheory.T.mem_level_of_levelDatum_ne_zero_translate D (Vc D i) (Wc D i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
        (R.xiR t) (R.Pg ∪ R.Q t) e' hsdW hBW.1 (rank_le D i) rfl he' hZ k hkf x hx hx'
      apply hnot
      have hlo := (GlobalTheory.FinZeta.LevelOff.level_offS D (Wc D i) (R.βW i) (R.ΛW i) (R.datWp i R.triv) ((R.Pg ∪ R.Q t).image (fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) hBW
        (fun PP hPP => Finset.mem_image_of_mem _ (by
          rcases hPP with h | h
          · exact Finset.mem_union_left _ h
          · exact absurd h (Finset.notMem_empty _)))).2.1 k hkf
      refine hlo.2 ⟨⟨k', hk', fun v hvS => ?_⟩, fun v hvS => ?_⟩
      · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hvS
        exact hag PP hPP
      · have hne : v ≠ P.under (𝓞 D.host.F) := fun h => hvS (h ▸ Finset.mem_image_of_mem _
          (hP.elim (fun h => Finset.mem_union_left _ h) (fun h => Finset.mem_union_right _ h)))
        rw [hk1 v hne]
        exact Subgroup.one_mem _)
  have h0 : thetaIP μ 𝓕 (R.ωP i t (1, k) (R.vP i t)) (R.vP i t) = 0 := by
    have h1 : Formalism.IndefR.Lift.pet μ 𝓕 (R.ωP i t (1, k) (R.vP i t)) (R.vP i t) = 0 := horth
    unfold Formalism.IndefR.Lift.pet at h1
    unfold thetaIP
    have h2 : (fun w => star (R.ωP i t (1, k) (R.vP i t) w) * R.vP i t w) =
        fun w => starRingEnd ℂ (R.ωP i t (1, k) (R.vP i t) w * starRingEnd ℂ (R.vP i t w)) := by
      funext w; simp [mul_comm]
    rw [h2, integral_conj, h1, map_zero]
  unfold coef
  rw [h0, zero_div]

end GlobalTheory.BadSuppPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoeffVanishesOffLevelBadPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCoeff_vanishes_offLevel_badPlaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t := by
  first | exact @GlobalTheory.BadSuppPf.badSupp | exact GlobalTheory.BadSuppPf.badSupp | (intros; apply GlobalTheory.BadSuppPf.badSupp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsFinIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PartsSpanProof

theorem exists_isFinIdem {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    ∃ v, IsFinIdem D v f := by
  rcases h with ⟨⟨⟨-, -, v, ε, hv, he⟩, -⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hv, rfl⟩, -⟩
  · exact ⟨v, ε, hv, he⟩
  · exact ⟨v, ε, hv, rfl⟩

theorem exists_lift {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X)
    (he : Function.Injective e) (L : X →ₗ[ℂ] X) (hL : ∀ x, L (e x) ∈ LinearMap.range e) :
    ∃ h : Module.End ℂ H, ∀ x, e (h x) = L (e x) := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ (L ∘ₗ e).codRestrict _ hL, fun x => ?_⟩
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e he).apply_symm_apply ⟨L (e x), hL x⟩)

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]


set_option maxHeartbeats 2000000 in
theorem partsSpan : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i S, PartsSpan R i S := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL hF i S
  have hLP := GlobalTheory.LevelProduct.levProd_of_laws D G Pl0 T A Ks R F hL hF i
  have hS := (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hC R).2.2 i
  obtain ⟨inj, hr, hip⟩ := hL.models.HW i (sg0 D A)
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hlv := fun x v => ((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v
  let ι := {x : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D (Wc D i)) //
    Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) S
      x.1 x.2.1 x.2.2}
  have keep : ∀ x : ι, ∀ U ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) x.1.2.2 U ∈ R.Wall i (sg0 D A) := by
    rintro ⟨⟨P, d, B⟩, e, f, ϖ, α, -, hP, -, -, -, -, -, hα, -, hB, hc⟩ U hU
    obtain ⟨v, hv⟩ := exists_isFinIdem hP
    exact GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall hLP v f hv α hα B hB hc U hU
  have hex : ∀ x : ι, ∃ h : Module.End ℂ (R.HW i (sg0 D A)).H, ∀ y,
      (R.HW i (sg0 D A)).e (h y) = heckeOn (R.MW i (sg0 D A)) x.1.2.2 ((R.HW i (sg0 D A)).e y) :=
    fun x => exists_lift _ inj _ fun y => hr ▸ keep x _ (hmem y)
  choose op hop using hex
  have hcomm : Formalism.L2.Col.PairComm op := fun x x' => by
    refine LinearMap.ext fun y => inj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hop, hop, hop, hop]
    exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.comm_heckeLin (J := levW R i)
      (GlobalTheory.HeckeAdjoint.realUnif D _) x.2 x'.2 (hlv y v)
  have hadj : ∀ x : ι, ∃ x', op x' = LinearMap.adjoint (op x) := by
    intro x
    obtain ⟨B', hB', -⟩ := GlobalTheory.SphericalOps.exists_dual (J := levW R i) (GlobalTheory.HeckeAdjoint.realUnif D x.1.1) x.2
    let x' : ι := ⟨(x.1.1, dualLab x.1.2.1, B'), hB'⟩
    refine ⟨x', ?_⟩
    rw [LinearMap.eq_adjoint_iff]
    intro a b
    rw [hip, hip, hop, hop]
    unfold ipAt
    congr 1
    exact GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab D (Wc D i) _ R.θ (R.MW i (sg0 D A)) (levW R i) _ S (R.νW i) (R.fdW i)
      hL.models.inf (hL.models.νW i).1.1 (hL.models.νW i).2 hS x.1.1 (dualLab x.1.2.1) B' x.1.2.2 hB'
      (by rw [dualLab_dualLab]; exact x.2) _ (hmem a) _ (hmem b) (keep x' _ (hmem a)) (keep x _ (hmem b))
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normalFamily_orthogonal_decomposition op hcomm hadj
  classical
  unfold PartsSpan
  refine eq_top_iff.2 (h2 ▸ iSup_le fun y => ?_)
  refine le_iSup_of_le (fun P d => if h : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) S P d B then y ⟨(P, d, h.choose), h.choose_spec⟩ else 0) ?_
  intro x hx
  rw [h1, Submodule.mem_iInf] at hx
  show (R.HW i (sg0 D A)).e x ∈ partFull _ _ _ _ _ _
  unfold partFull
  refine Submodule.mem_inf.2 ⟨hmem x, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  have hE : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) S P d B := ⟨B, hB⟩
  rw [dite_eq_left hE]
  have e1 := Module.End.mem_eigenspace_iff.1 (hx ⟨(P, d, hE.choose), hE.choose_spec⟩)
  have e2 := congrArg (R.HW i (sg0 D A)).e e1
  rw [hop, map_smul] at e2
  rw [← e2]
  exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.labelUnique (J := levW R i) (GlobalTheory.HeckeAdjoint.realUnif D)
    P d B _ hB hE.choose_spec _ (hlv x v)

end GlobalTheory.PartsSpanProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetHeckeSumPreservesPrincipalForms
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetHeckeSumPreservesPrincipalForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.TransSum

def conjMeet {Γ : Type*} [Group Γ] (K : Subgroup Γ) (γ : Γ) : Subgroup Γ :=
  K ⊓ K.comap (MulAut.conj γ⁻¹).toMonoidHom

theorem mem_conjMeet {Γ : Type*} [Group Γ] {K : Subgroup Γ} {γ x : Γ} :
    x ∈ conjMeet K γ ↔ x ∈ K ∧ γ⁻¹ * x * γ ∈ K := by
  simp [conjMeet, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]

theorem exists_sum_inv {Γ : Type*} [Group Γ] (K : Subgroup Γ) (γ : Γ)
    [hf : ((conjMeet K γ).subgroupOf K).FiniteIndex] :
    ∃ C : Finset Γ, C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ K, δ = k * γ) ∧
      ∀ F : Γ → ℂ, (∀ k ∈ K, ∀ g, F (g * k) = F g) → ∀ k ∈ K, ∀ g,
        ∑ δ ∈ C, F (g * k * δ) = ∑ δ ∈ C, F (g * δ) := by
  classical
  set H := (conjMeet K γ).subgroupOf K
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let r : K ⧸ H → Γ := fun q => ((Quotient.out q : K) : Γ) * γ
  have hr : Function.Injective r := by
    intro q₁ q₂ h
    have h' : (Quotient.out q₁ : K) = Quotient.out q₂ := Subtype.ext (mul_right_cancel h)
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, h']
  refine ⟨Finset.univ.image r, ?_, ?_, ?_⟩
  · exact Finset.image_nonempty.2 ⟨(QuotientGroup.mk 1 : K ⧸ H), Finset.mem_univ _⟩
  · intro δ hδ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨_, (Quotient.out q).2, rfl⟩
  · intro F hF k hk g
    rw [Finset.sum_image (fun a _ b _ h => hr h), Finset.sum_image (fun a _ b _ h => hr h)]
    let kk : K := ⟨k, hk⟩

    have key : ∀ q : K ⧸ H, F (g * k * r q) = F (g * r (kk • q)) := by
      intro q
      have hq : (QuotientGroup.mk (Quotient.out (kk • q)) : K ⧸ H) = QuotientGroup.mk (kk * Quotient.out q) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have hm := QuotientGroup.eq.1 hq
      rw [Subgroup.mem_subgroupOf, mem_conjMeet] at hm
      have e : g * k * r q = g * r (kk • q) * (γ⁻¹ * ((((Quotient.out (kk • q))⁻¹ * (kk * Quotient.out q) : K) : Γ)) * γ) := by
        simp only [r, Subgroup.coe_mul, Subgroup.coe_inv, kk]
        group
      rw [e, hF _ hm.2]

    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Fintype.sum_equiv (MulAction.toPerm kk) _ _ (fun q => rfl)

end GlobalTheory.TransSum

namespace GlobalTheory.TransSum

theorem heckeOn_doubleCoset_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (γ : GA D (Wc D i)), γ ∈ GfC (Wc D i) → ∃ C : Finset (GA D (Wc D i)), C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ levW R i, δ = k * γ) ∧ ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hP γ hγ
  have topgrp := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Wc D i).gram
  haveI : CompactSpace (levW R i) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _)
  have hU := GlobalTheory.LevelOpen.isOpen_levG (Wc D i) (R.βW i) (R.datWp i R.triv)
  have hopen : IsOpen (((conjMeet (levW R i) γ).subgroupOf (levW R i) : Subgroup (levW R i)) : Set (levW R i)) := by
    let φ : levW R i → GfC (Wc D i) := fun x =>
      ⟨γ⁻¹ * (x : GA D (Wc D i)) * γ, mul_mem (mul_mem (inv_mem hγ) (hP.1 x.2)) hγ⟩
    have hφ : Continuous φ := by
      refine Continuous.subtype_mk ?_ _
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    have e : (((conjMeet (levW R i) γ).subgroupOf (levW R i) : Subgroup (levW R i)) : Set (levW R i)) =
        φ ⁻¹' {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)} := by
      ext x
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_conjMeet, Set.mem_preimage, Set.mem_setOf_eq, φ]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [e]
    exact hU.preimage hφ
  haveI : Finite (levW R i ⧸ (conjMeet (levW R i) γ).subgroupOf (levW R i)) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : ((conjMeet (levW R i) γ).subgroupOf (levW R i)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨C, hne, hC, hsum⟩ := exists_sum_inv (levW R i) γ
  refine ⟨C, hne, hC, fun Tm hT => ?_⟩
  have hCf : ∀ a ∈ C, a ∈ GfC (Wc D i) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := hC a ha
    exact mul_mem (hP.1 hk) hγ
  unfold RealDat.Wall at hT ⊢
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  refine GlobalTheory.HeckeParts.isMultMap_heckeOn hT hCf fun v k hk g => ?_
  have h1 : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := hP.2.1 k hk
  rw [h1, one_mul, heckeLin_apply, heckeLin_apply]
  exact hsum (Tm v) (fun k' hk' g' => by rw [hT.lev v k' hk' g', hP.2.1 k' hk', one_mul]) k hk g

end GlobalTheory.TransSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetHeckeSumPreservesPrincipalFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_levW_mul_heckeOn_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (γ : GA D (Wc D i)), γ ∈ GfC (Wc D i) → ∃ C : Finset (GA D (Wc D i)), C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ levW R i, δ = k * γ) ∧ ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  first | exact @GlobalTheory.TransSum.heckeOn_doubleCoset_mem_wall | exact GlobalTheory.TransSum.heckeOn_doubleCoset_mem_wall | (intros; apply GlobalTheory.TransSum.heckeOn_doubleCoset_mem_wall <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalDoubleCosetRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalDoubleCosetRepresentatives
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.LocalRepsFin

theorem exists_isCosetRep_finIdem : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ α : GA D V, SuppF V f α → ∃ C : Finset (GA D V), (∀ γ ∈ C, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ levG V β L ∧ SuppF V f k} α C := by
  intro D V β L v f hf α hα
  obtain ⟨ε, hε, rfl⟩ := hf
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hG : ∀ g, SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) g → g ∈ GfC V := fun g hg =>
    GlobalTheory.IdemSupport.mem_GfC_of_suppF V (GlobalTheory.IdemSupport.place_comp hΦ hε).1 hg
  let S : Subgroup (GA D V) := GlobalTheory.IdemSupport.suppGroup V (algebraMap _ (Formalism.L2.Theta.AE D) ε)
  have hS : ∀ g, g ∈ S ↔ SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) g := fun _ => Iff.rfl
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨R, r1, r2⟩ := GlobalTheory.HeckeLabels.exists_reps (GlobalTheory.HeckeLabels.relIndex_conj_ne_zero (L := S)
    (GlobalTheory.ParahoricCompact.isCompact_levG V β L) (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L)
    (fun k hk hk' => ⟨hG k ((hS k).1 hk), hk'⟩) ((hS α).2 hα))
  have hK : {k | k ∈ levG V β L ∧ SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) k} =
      (levG V β L ⊓ S : Subgroup (GA D V)) :=
    Set.ext fun k => and_congr_right fun _ => (hS k).symm
  have r0 : ∀ γ ∈ R, SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) γ := fun γ hγ => by
    obtain ⟨a, ha, b, hb, rfl⟩ := r1 γ hγ
    exact (hS _).1 (mul_mem (mul_mem ha.2 ((hS α).2 hα)) hb.2)
  rw [hK]
  exact ⟨R, r0, fun γ hγ => ⟨hG γ (r0 γ hγ), r1 γ hγ⟩, r2⟩

end GlobalTheory.LocalRepsFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalDoubleCosetRepresentativesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_local_double_coset_representatives : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ α : GA D V, SuppF V f α → ∃ C : Finset (GA D V), (∀ γ ∈ C, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ levG V β L ∧ SuppF V f k} α C := by
  first | exact @GlobalTheory.LocalRepsFin.exists_isCosetRep_finIdem | exact GlobalTheory.LocalRepsFin.exists_isCosetRep_finIdem | (intros; apply GlobalTheory.LocalRepsFin.exists_isCosetRep_finIdem <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLiftTrans

theorem norm_integral_star_mul_sq_le {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ)
    (hf2 : Integrable (fun x => star (f x) * f x) μ) (hh2 : Integrable (fun x => star (h x) * h x) μ) :
    ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re :=
  GlobalTheory.T.norm_integral_star_mul_sq_le_mul μ f h hf hh hf2 hh2

theorem exists_cosetRep_levG {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D) (hf : IsFinIdem D v f) (α : GA D V) (hα : SuppF V f α) :
    ∃ C : Finset (GA D V), (∀ γ ∈ C, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ levG V β L ∧ SuppF V f k} α C :=
  GlobalTheory.T.exists_finite_local_double_coset_representatives V β L v f hf α hα

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem heckeOn_mem_wall (hLP : LevProd R i) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D) (hf : IsFinIdem D v f)
    (α : GA D (Wc D i)) (hα : SuppF (Wc D i) f α) (C : Finset (GA D (Wc D i))) (hC : ∀ γ ∈ C, SuppF (Wc D i) f γ)
    (hR : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) (T : MMap (R.MW i (sg0 D A)))
    (hT : T ∈ R.Wall i (sg0 D A)) : heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) :=
  GlobalTheory.T.local_hecke_sum_preserves_principal_level_forms hLP v f hf α hα C hC hR T hT

theorem exists_doubleCoset_sum (hLP : LevProd R i) (γ : GA D (Wc D i)) (hγ : γ ∈ GfC (Wc D i)) :
    ∃ C : Finset (GA D (Wc D i)), C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ levW R i, δ = k * γ) ∧
      ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) :=
  GlobalTheory.T.exists_finset_levW_mul_heckeOn_mem_wall hLP γ hγ

theorem wall_props {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A)) :
    IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) T :=
  (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT

theorem rinv (hLP : LevProd R i) {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A)) (v : (R.MW i (sg0 D A)).Vec)
    {k : GA D (Wc D i)} (hk : k ∈ levW R i) (g : GA D (Wc D i)) : T v (g * k) = T v g := by
  rw [(wall_props hT).lev v k hk g, hLP.2.1 k hk, one_mul]

theorem linv {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A)) (v : (R.MW i (sg0 D A)).Vec)
    {δ : GA D (Wc D i)} (hδ : δ ∈ GQ (Wc D i)) (g : GA D (Wc D i)) : T v (δ * g) = T v g :=
  ((wall_props hT).aut v).left δ hδ g

theorem cont {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A)) (v : (R.MW i (sg0 D A)).Vec) :
    Continuous (T v) := ((wall_props hT).aut v).cont

theorem heckeOn_single_apply (T : MMap (R.MW i (sg0 D A))) (γ : GA D (Wc D i)) (v : (R.MW i (sg0 D A)).Vec)
    (g : GA D (Wc D i)) : heckeOn (R.MW i (sg0 D A)) {γ} T v g = T v (g * γ) := by
  simp [heckeOn, postOn_apply, heckeLin_apply]

theorem heckeOn_apply (T : MMap (R.MW i (sg0 D A))) (C : Finset (GA D (Wc D i))) (v : (R.MW i (sg0 D A)).Vec)
    (g : GA D (Wc D i)) : heckeOn (R.MW i (sg0 D A)) C T v g = ∑ δ ∈ C, T v (g * δ) := by
  simp [heckeOn, postOn_apply, heckeLin_apply]

theorem hecke_one (T : MMap (R.MW i (sg0 D A))) : heckeOn (R.MW i (sg0 D A)) {1} T = T := by
  ext v g; simp [heckeOn, postOn_apply, heckeLin_apply]

theorem shift {F : Face D A} (hL : Laws R F) (u : GA D (Wc D i) → ℂ)
    (hu : ∀ δ ∈ GQ (Wc D i), ∀ h, u (δ * h) = u h) (y : GA D (Wc D i)) :
    ∫ h in R.fdW i, u (h * y) ∂(R.νW i) = ∫ h in R.fdW i, u h ∂(R.νW i) := by
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  haveI := (hL.models.νW i).1.1
  haveI := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D (Wc D i) (R.νW i) (hL.models.νW i).1.1
  exact GlobalTheory.DoubleCosetAdjoint.setIntegral_mul_right (R.νW i) (GQ (Wc D i)) (R.fdW i) (hL.models.νW i).2 u hu y

theorem sq_int {F : Face D A} (hL : Laws R F) {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A))
    (v : (R.MW i (sg0 D A)).Vec) : IntegrableOn (fun g => star (T v g) * T v g) (R.fdW i) (R.νW i) := by
  have hHW := hL.models.HW i (sg0 D A)
  obtain ⟨x, rfl⟩ : T ∈ LinearMap.range (R.HW i (sg0 D A)).e := by rw [hHW.2.1]; exact hT
  obtain ⟨c, hc⟩ := GlobalTheory.HeckeParts.exists_isMultIP hHW x x
  exact (hc v v).1

theorem sq_int_tr {F : Face D A} (hL : Laws R F) {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A))
    (v : (R.MW i (sg0 D A)).Vec) (δ : GA D (Wc D i)) :
    IntegrableOn (fun g => star (T v (g * δ)) * T v (g * δ)) (R.fdW i) (R.νW i) := by
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  haveI := (hL.models.νW i).1.1
  haveI := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D (Wc D i) (R.νW i) (hL.models.νW i).1.1
  exact GlobalTheory.DoubleCosetAdjoint.integrableOn_mul_right (R.νW i) (GQ (Wc D i)) (R.fdW i) (hL.models.νW i).2
    (fun g => star (T v g) * T v g) (fun δ' hδ' g => by simp only [linv hT v hδ' g]) δ (sq_int hL hT v)

theorem int_tr {F : Face D A} (hL : Laws R F) {T T' : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A))
    (hT' : T' ∈ R.Wall i (sg0 D A)) (v v' : (R.MW i (sg0 D A)).Vec) (δ : GA D (Wc D i)) :
    IntegrableOn (fun g => star (T v g) * T' v' (g * δ)) (R.fdW i) (R.νW i) := by
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  exact GlobalTheory.DoubleCosetAdjoint.integrableOn_star_mul (R.νW i) (R.fdW i) (T v) (fun g => T' v' (g * δ))
    (cont hT v) ((cont hT' v').comp (continuous_mul_const δ)) (sq_int hL hT v) (sq_int_tr hL hT' v' δ)

theorem exists_ip {F : Face D A} (hL : Laws R F) (hLP : LevProd R i) {γ : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i))
    {T T' : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A)) (hT' : T' ∈ R.Wall i (sg0 D A)) :
    ∃ c, IsMultIP (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) T (heckeOn (R.MW i (sg0 D A)) {γ} T') c := by
  have hHW := hL.models.HW i (sg0 D A)
  obtain ⟨C, hCne, hCk, hCW⟩ := exists_doubleCoset_sum hLP γ hγ
  obtain ⟨x, rfl⟩ : T ∈ LinearMap.range (R.HW i (sg0 D A)).e := by rw [hHW.2.1]; exact hT
  obtain ⟨y, hy⟩ : heckeOn (R.MW i (sg0 D A)) C T' ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hHW.2.1]; exact hCW T' hT'
  obtain ⟨c, hc⟩ := GlobalTheory.HeckeParts.exists_isMultIP hHW x y
  have hn : (C.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hCne)
  refine ⟨c / C.card, fun v v' => ⟨?_, ?_⟩⟩
  · simpa only [heckeOn_single_apply] using int_tr hL hT hT' v v' γ
  · have key : ∀ δ ∈ C, ∫ g in R.fdW i, star ((R.HW i (sg0 D A)).e x v g) * T' v' (g * δ) ∂(R.νW i) =
        ∫ g in R.fdW i, star ((R.HW i (sg0 D A)).e x v g) * T' v' (g * γ) ∂(R.νW i) := by
      intro δ hδ
      obtain ⟨k, hk, rfl⟩ := hCk δ hδ
      have hs := shift hL (fun g => star ((R.HW i (sg0 D A)).e x v (g * k⁻¹)) * T' v' (g * γ))
        (fun δ' hδ' g => by simp only [mul_assoc, linv hT v hδ', linv hT' v' hδ']) k
      simp only [mul_inv_cancel_right, rinv hLP hT v (inv_mem hk)] at hs
      simp only [← mul_assoc]
      exact hs
    have h2 := (hc v v').2
    rw [hy] at h2
    simp only [heckeOn_apply, Finset.mul_sum] at h2
    rw [integral_finsetSum _ fun δ _ => int_tr hL hT hT' v v' δ, Finset.sum_congr rfl key, Finset.sum_const,
      nsmul_eq_mul] at h2
    simp only [heckeOn_single_apply]
    rw [div_mul_eq_mul_div, eq_div_iff hn, mul_comm, h2]

set_option maxHeartbeats 1600000 in
theorem transLaws_of {F : Face D A} (hL : Laws R F) (hLP : LevProd R i) : TransLaws R i := by
  classical
  have hHW := hL.models.HW i (sg0 D A)
  have hW : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => by
    rw [← hHW.2.1]; exact LinearMap.mem_range_self _ x
  have hfin : ∀ k ∈ levW R i, k ∈ GfC (Wc D i) := fun k hk => hLP.1 hk
  have ha : ∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∃ C : Finset (GA D (Wc D i)),
      (∀ γ ∈ C, SuppF (Wc D i) f γ) ∧ IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C :=
    fun v f hf α hα => exists_cosetRep_levG _ _ _ v f hf α hα
  have h1 : ∀ x y, trPair R i 1 x y = ⟪x, y⟫_ℂ := fun x y => by
    unfold trPair; rw [hecke_one]; exact (hHW.2.2 x y).symm
  by_cases hv : ∃ v0 : (R.MW i (sg0 D A)).Vec,
      ∏ τ, ⟪((v0 τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ), (v0 τ : (R.MW i (sg0 D A)).H τ)⟫_ℂ ≠ 0
  swap
  · push_neg at hv
    have hz : ∀ T : MMap (R.MW i (sg0 D A)), T = 0 := by
      intro T; ext v g
      obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 (hv v)
      have : v τ = 0 := Subtype.ext (inner_self_eq_zero.1 hτ)
      simp [T.map_coord_zero τ this]
    have hx0 : ∀ x : (R.HW i (sg0 D A)).H, x = 0 := fun x =>
      hHW.1 (by rw [hz ((R.HW i (sg0 D A)).e x), map_zero])
    have ht0 : ∀ γ x y, trPair R i γ x y = 0 := by
      intro γ x y
      rw [hx0 x, hx0 y, ← inner_zero_left (𝕜 := ℂ) (0 : (R.HW i (sg0 D A)).H)]
      unfold trPair
      rw [map_zero, map_zero, hHW.2.2 0 0, map_zero]
    refine ⟨ha, fun v f hf α hα C hC hR y => ⟨0, by rw [hz ((R.HW i _).e 0), hz (heckeOn _ C _)], fun γ _ x => by
      simp [ht0]⟩, fun γ _ => ⟨0, by simp, fun x y => by simp [ht0]⟩, fun γ _ k _ k' _ x y => by simp [ht0],
      fun γ _ x y => by simp [ht0], h1⟩

  obtain ⟨v0, hv0⟩ := hv
  set P := ∏ τ, ⟪((v0 τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ), (v0 τ : (R.MW i (sg0 D A)).H τ)⟫_ℂ
    with hP
  set cst : ℂ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ) with hcst
  set e := (R.HW i (sg0 D A)).e with he
  have hI : ∀ x y γ, IntegrableOn (fun g => star (e x v0 g) * e y v0 (g * γ)) (R.fdW i) (R.νW i) :=
    fun x y γ => int_tr hL (hW x) (hW y) v0 v0 γ
  have htp : ∀ γ ∈ GfC (Wc D i), ∀ x y, trPair R i γ x y =
      cst * (∫ g in R.fdW i, star (e x v0 g) * e y v0 (g * γ) ∂(R.νW i)) / P := by
    intro γ hγ x y
    have h := ipM_spec _ _ _ _ _ (exists_ip hL hLP hγ (hW x) (hW y)) v0 v0
    simp only [heckeOn_single_apply] at h
    rw [eq_div_iff hv0]
    show cst * ipM _ _ _ _ _ * P = _
    rw [mul_assoc, ← h.2]
  have hb : ∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∀ C : Finset (GA D (Wc D i)),
      (∀ γ ∈ C, SuppF (Wc D i) f γ) → IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C →
      ∀ y, ∃ y', e y' = heckeOn (R.MW i (sg0 D A)) C (e y) ∧
        ∀ γ ∈ GfC (Wc D i), ∀ x, trPair R i γ x y' = ∑ δ ∈ C, trPair R i (γ * δ) x y := by
    intro v f hf α hα C hC hR y
    obtain ⟨y', hy'⟩ : heckeOn (R.MW i (sg0 D A)) C (e y) ∈ LinearMap.range e := by
      rw [he, hHW.2.1]; exact heckeOn_mem_wall hLP v f hf α hα C hC hR _ (hW y)
    refine ⟨y', hy', fun γ hγ x => ?_⟩
    have hCf : ∀ δ ∈ C, δ ∈ GfC (Wc D i) := fun δ hδ => (hR.1 δ hδ).1
    rw [htp γ hγ, Finset.sum_congr rfl fun δ hδ => htp (γ * δ) (mul_mem hγ (hCf δ hδ)) x y, ← Finset.sum_div,
      ← Finset.mul_sum, ← integral_finsetSum _ fun δ _ => hI x y (γ * δ)]
    congr 3
    funext g
    rw [hy', heckeOn_apply, Finset.mul_sum]
    simp only [mul_assoc]
  have hd : ∀ γ ∈ GfC (Wc D i), ∀ k ∈ levW R i, ∀ k' ∈ levW R i, ∀ x y,
      trPair R i (k * γ * k') x y = trPair R i γ x y := by
    intro γ hγ k hk k' hk' x y
    rw [htp _ (mul_mem (mul_mem (hfin k hk) hγ) (hfin k' hk')), htp _ hγ]
    have e1 : ∀ g, e y v0 (g * (k * γ * k')) = e y v0 (g * k * γ) := fun g => by
      rw [show g * (k * γ * k') = g * k * γ * k' by group, rinv hLP (hW y) v0 hk']
    simp only [e1]
    have hs := shift hL (fun g => star (e x v0 (g * k⁻¹)) * e y v0 (g * γ))
      (fun δ hδ g => by simp only [mul_assoc, linv (hW x) v0 hδ, linv (hW y) v0 hδ]) k
    simp only [mul_inv_cancel_right, rinv hLP (hW x) v0 (inv_mem hk)] at hs
    rw [hs]
  have hcs : (starRingEnd ℂ) cst = cst := by rw [hcst, map_prod]; simp
  have hPs : (starRingEnd ℂ) P = P := by
    rw [hP, map_prod]; exact Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _
  have hsym : ∀ γ ∈ GfC (Wc D i), ∀ x y, trPair R i γ⁻¹ x y = star (trPair R i γ y x) := by
    intro γ hγ x y
    rw [htp _ (inv_mem hγ), htp _ hγ, Complex.star_def, map_div₀, map_mul, hcs, hPs]
    congr 2
    have hs := shift hL (fun g => star (e x v0 g) * e y v0 (g * γ⁻¹))
      (fun δ hδ g => by simp only [mul_assoc, linv (hW x) v0 hδ, linv (hW y) v0 hδ]) γ
    simp only [mul_inv_cancel_right, Complex.star_def] at hs
    rw [← hs, ← integral_conj]
    congr 1; funext g
    simp only [map_mul, Complex.star_def, Complex.conj_conj]; ring
  refine ⟨ha, hb, ?_, hd, hsym, h1⟩

  intro γ hγ
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  have hn2 : ∀ z : (R.HW i (sg0 D A)).H, ‖⟪z, z⟫_ℂ‖ = ‖z‖ ^ 2 := fun z => by
    rw [inner_self_eq_norm_sq_to_K]; simp
  have hsq : ∀ x, ‖x‖ ^ 2 = ‖cst‖ * ‖∫ g in R.fdW i, star (e x v0 g) * e x v0 g ∂(R.νW i)‖ / ‖P‖ := fun x => by
    rw [← hn2, ← h1, htp 1 (one_mem _), norm_div, norm_mul]; simp only [mul_one]
  have hab : ∀ x y, ‖∫ g in R.fdW i, star (e x v0 g) * e y v0 (g * γ) ∂(R.νW i)‖ ^ 2 ≤
      ‖∫ g in R.fdW i, star (e x v0 g) * e x v0 g ∂(R.νW i)‖ * ‖∫ g in R.fdW i, star (e y v0 g) * e y v0 g ∂(R.νW i)‖ := by
    intro x y
    have hcs' := norm_integral_star_mul_sq_le ((R.νW i).restrict (R.fdW i)) (e x v0) (fun g => e y v0 (g * γ))
      (cont (hW x) v0).aestronglyMeasurable ((cont (hW y) v0).comp (continuous_mul_const γ)).aestronglyMeasurable
      (sq_int hL (hW x) v0) (sq_int_tr hL (hW y) v0 γ)
    have hsh := shift hL (fun g => star (e y v0 g) * e y v0 g)
      (fun δ hδ g => by simp only [linv (hW y) v0 hδ]) γ
    rw [hsh] at hcs'
    refine hcs'.trans ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _) (abs_nonneg _) (norm_nonneg _)
  have hbd : ∀ x y, ‖trPair R i γ x y‖ ≤ 1 * ‖x‖ * ‖y‖ := by
    intro x y
    have key : (‖cst‖ * ‖∫ g in R.fdW i, star (e x v0 g) * e y v0 (g * γ) ∂(R.νW i)‖ / ‖P‖) ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
      rw [mul_pow, hsq x, hsq y, div_pow, mul_pow]
      rw [div_mul_div_comm, ← mul_pow, mul_mul_mul_comm, ← sq]
      gcongr
      all_goals first
        | positivity
        | exact (sq _).ge
        | (rw [mul_pow]; exact mul_le_mul_of_nonneg_left (hab x y) (by positivity))
    rw [htp γ hγ, norm_div, norm_mul, one_mul]
    have h0 : 0 ≤ ‖cst‖ * ‖∫ g in R.fdW i, star (e x v0 g) * e y v0 (g * γ) ∂(R.νW i)‖ / ‖P‖ := by positivity
    nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg (norm_nonneg x) (norm_nonneg y)]

  have hadd1 : ∀ x1 x2 y : (R.HW i (sg0 D A)).H, trPair R i γ (x1 + x2) y = trPair R i γ x1 y + trPair R i γ x2 y := by
    intro x1 x2 y
    have hf : ∀ g : GA D (Wc D i), star (e (x1 + x2) v0 g) * e y v0 (g * γ) =
        star (e x1 v0 g) * e y v0 (g * γ) + star (e x2 v0 g) * e y v0 (g * γ) := fun g => by
      simp only [map_add (f := _), MultilinearMap.add_apply, Pi.add_apply, Complex.star_def, add_mul]
    rw [htp γ hγ, htp γ hγ, htp γ hγ]
    simp only [hf]
    rw [integral_add (hI x1 y γ) (hI x2 y γ)]
    ring
  have hsm1 : ∀ (c : ℂ) (x y : (R.HW i (sg0 D A)).H), trPair R i γ (c • x) y = (starRingEnd ℂ) c • trPair R i γ x y := by
    intro c x y
    have hf : ∀ g : GA D (Wc D i), star (e (c • x) v0 g) * e y v0 (g * γ) = (starRingEnd ℂ) c * (star (e x v0 g) * e y v0 (g * γ)) :=
      fun g => by
        simp only [map_smul, MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.star_def, map_mul]; ring
    rw [htp γ hγ, htp γ hγ]
    simp only [hf]
    rw [integral_const_mul (μ := (R.νW i).restrict (R.fdW i)) ((starRingEnd ℂ) c)
      (fun g => star (e x v0 g) * e y v0 (g * γ)), smul_eq_mul]
    ring
  have hadd2 : ∀ x y1 y2 : (R.HW i (sg0 D A)).H, trPair R i γ x (y1 + y2) = trPair R i γ x y1 + trPair R i γ x y2 := by
    intro x y1 y2
    have hf : ∀ g : GA D (Wc D i), star (e x v0 g) * e (y1 + y2) v0 (g * γ) =
        star (e x v0 g) * e y1 v0 (g * γ) + star (e x v0 g) * e y2 v0 (g * γ) := fun g => by
      simp only [map_add (f := _), MultilinearMap.add_apply, Pi.add_apply, mul_add]
    rw [htp γ hγ, htp γ hγ, htp γ hγ]
    simp only [hf]
    rw [integral_add (hI x y1 γ) (hI x y2 γ)]
    ring
  have hsm2 : ∀ (c : ℂ) (x y : (R.HW i (sg0 D A)).H), trPair R i γ x (c • y) = (RingHom.id ℂ) c • trPair R i γ x y := by
    intro c x y
    have hf : ∀ g : GA D (Wc D i), star (e x v0 g) * e (c • y) v0 (g * γ) = c * (star (e x v0 g) * e y v0 (g * γ)) := fun g => by
      simp only [map_smul, MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [htp γ hγ, htp γ hγ]
    simp only [hf]
    rw [integral_const_mul (μ := (R.νW i).restrict (R.fdW i)) c
      (fun g => star (e x v0 g) * e y v0 (g * γ)), smul_eq_mul, RingHom.id_apply]
    ring
  let Bs : (R.HW i (sg0 D A)).H →ₗ⋆[ℂ] (R.HW i (sg0 D A)).H →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => trPair R i γ x y) hadd1 hsm1 hadd2 hsm2
  let Bc := Bs.mkContinuous₂ 1 hbd
  have hrep : ∀ x y, trPair R i γ x y = ⟪x, ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin Bc) y⟫_ℂ := fun x y => by
    rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]; rfl
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin Bc), ?_, hrep⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  have h2 := hbd (ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin Bc) y) y
  rw [hrep, hn2, one_mul] at h2
  nlinarith [norm_nonneg (ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin Bc) y), norm_nonneg y]

theorem transLaws : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i, TransLaws R i := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F hL hFull i
  exact transLaws_of hL (GlobalTheory.T.level_subgroup_restricted_product_of_laws D G Pl0 T A Ks R F hL hFull i)

end GlobalTheory.RawLiftTrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatSpanOfLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RatSpanProof

theorem ratSpan_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RatSpan R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t
  exact GlobalTheory.HeckeClassSums.span_jV hL.models.HV hL.models.jV i t

end GlobalTheory.RatSpanProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RawLiftOntoOfUpInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory


set_option maxHeartbeats 1000000 in
theorem rawLift_onto_of_upInj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RatSpan R → (∀ i, UpInj R i A.μ0) → ThOnto R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hS hU i
  obtain ⟨th, hth⟩ := hL.exists_isRaw i A.μ0
  have hsurj := (GlobalTheory.adjoint_injective_surjective_and_positive_scalar _ _ th).1 (hU i th hth)
  rw [hS i A.μ0, Submodule.map_top]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact hL.thP.thF_mem i A.μ0 x
  · intro w hw
    rw [← (hL.models.HW i (sg0 D A)).2.1] at hw
    obtain ⟨y, rfl⟩ := hw
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, (hth x).symm⟩

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem innerPos_of_innerNe {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (h : InnerNe R i t S) : InnerPos R i t S := by
  unfold InnerPos
  intro th hth c
  have h' := h th hth c
  obtain ⟨l, hl, hx⟩ := h'
  have key := (GlobalTheory.adjoint_injective_surjective_and_positive_scalar _ _ th).2 (part R i S c) l hl hx
  obtain ⟨l', hl', hx', -⟩ := key
  exact ⟨l', hl', hx'⟩

theorem rawLift_main : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RallisConv D →
    ThOnto R ∧ ∀ i t, UpInj R i t ∧ InnerPos R i t ∅ ∧ PartsSpan R i ∅ := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL hF hR
  have lp : ∀ i, LevProd R i := GlobalTheory.LevelProduct.levProd_of_laws D G Pl0 T A Ks R F hL hF
  have tr : ∀ i, TransLaws R i := GlobalTheory.RawLiftTrans.transLaws hC D G Pl0 T A Ks R F hL hF
  have lf : ∀ i t, LevFix R i t := GlobalTheory.RawLift.LevelFix.levFix D G Pl0 T A Ks R F hL hF
  have vn : ∀ i t, VecNe R i t := vecNe D G Pl0 T A Ks R F hL hF
  have fs : ∀ i t, FinSum R i t := fun i t =>
    GlobalTheory.RawLift.finSum_of_rallis hC D G Pl0 T A Ks R F hL hF hR i t (GlobalTheory.T.downwardLift_adjoint_eq_upwardThetaIntegral hC D G Pl0 T A Ks R F hL hF i t) (lf i t)
      (GlobalTheory.RawLift.FactorInf.factInf D G Pl0 T A Ks R F hL hF i t) (GlobalTheory.RawLift.RealLowPf.realLow D G Pl0 T A Ks R F hL hF i t) (vn i t) (lp i) (tr i)
  have fm : ∀ i t, FinMult R i t := GlobalTheory.RawLift.LocalFactor.finMult D G Pl0 T A Ks R F hL hF
  have bs : ∀ i t, BadSupp R i t := GlobalTheory.T.localCoeff_vanishes_offLevel_badPlaces D G Pl0 T A Ks R F hL hF
  have ls : ∀ i t, LocSmall R i t := fun i t =>
    GlobalTheory.RawLift.Small.locSmall D G Pl0 T A Ks R F hL hF i t (bs i t) (GlobalTheory.RawLift.GoodModulus.goodMod D G Pl0 T A Ks R F hL hF i t)
      (GlobalTheory.IndexCount.indexSum_holds D G Pl0 T A Ks R F hL hF i)
  have up : ∀ i t, UpInj R i t := fun i t =>
    GlobalTheory.UpInj.upInj_holds D G Pl0 T A Ks R F hL hF i t (fs i t) (fm i t) (lf i t) (vn i t) (ls i t) (lp i) (tr i)
  refine ⟨GlobalTheory.rawLift_onto_of_upInj D G Pl0 T A Ks R F hL hF (GlobalTheory.RatSpanProof.ratSpan_of_laws D G Pl0 T A Ks R F hL hF) (fun i => up i A.μ0),
    fun i t => ⟨up i t, ?_, GlobalTheory.PartsSpanProof.partsSpan hC D G Pl0 T A Ks R F hL hF i ∅⟩⟩
  exact innerPos_of_innerNe R i t ∅
    (GlobalTheory.RawLift.innerNe_spherical D G Pl0 T A Ks R F hL hF i t (fs i t) (fm i t) (lf i t) (vn i t) (ls i t) (bs i t) (lp i) (tr i))

end GlobalTheory.RawLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftRowsInjectiveAndTypePropertiesOfNonvanishing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DownLift

theorem liftRows_injective_and_typeProperties_of_nonvanishing : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.RawLift.RallisConv D → (∀ i t, NonVan R i t) → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, TypeNZ R i t ∧ GoodMem R i t ∧ DownEig R i t ∧ UnrCorr R i t (fun _ => True) ∧ Saturated R i t := by
  intro hDec hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull hRallis hNV
  have hLaws : GlobalTheory.RawLift.Laws R F :=
    ⟨hG.core.lev, hG.core.grp, hG.core.fam, hG.core.models, hG.core.thP⟩
  have hTop5 := GlobalTheory.RawLift.rawLift_main hDec D G Pl0 T A Ks R F hLaws hFull hRallis
  have hEig : ∀ i t, DownEig R i t := GlobalTheory.DownEigen.downEig hHowe D G Pl0 T A Ks R F hG hFull
  have hGF : ∀ i t, GenFin R i t := GlobalTheory.DownLift.GenFinite.genFin hHowe D G Pl0 T A Ks R F hG hFull
  have hGI : ∀ i t, GenInf R i t := GlobalTheory.GenReal.genInf D G Pl0 T A Ks R F hG hFull
  have hGM : ∀ i t, GoodMem R i t := GlobalTheory.GoodLift.goodMem_of_given D G Pl0 T A Ks R F hG hFull
  have hNC : ∀ i t, GoodNoChi R i t := GlobalTheory.GoodTypeNoChi.goodNoChi D G Pl0 T A Ks R F hG hFull
  have hPar : ∀ i t, ParamsEx R i t := GlobalTheory.DownLift.Params.paramsEx hDec D G Pl0 T A Ks R F hG hFull
  have hIn : ∀ i t, UnrCorr R i t (fun w => Formalism.IndefR.Lev.IsConjPl w w) := GlobalTheory.DownInert.unrCorr_inert hHowe D G Pl0 T A Ks R F hG hFull
  have hSp : ∀ i t, UnrCorr R i t (fun w => ¬ Formalism.IndefR.Lev.IsConjPl w w) := GlobalTheory.SplitCorr.unrCorr_split D G Pl0 T A Ks R F hG hFull
  have hTNZ : ∀ i t, TypeNZ R i t := fun i t =>
    GlobalTheory.DownLift.typeNZ_of_nonVan_gen D G Pl0 T A Ks R F hG hFull i t (hNV i t) (hGI i t) (hGF i t) (hNC i t) (hGM i t)
  have hU : ∀ i t, UnrCorr R i t (fun _ => True) := by
    intro i t h hh s c y hy h1 h2 B B' hB hB' w hw _
    by_cases hc : Formalism.IndefR.Lev.IsConjPl w w
    · exact hIn i t h hh s c y hy h1 h2 B B' hB hB' w hw hc
    · exact hSp i t h hh s c y hy h1 h2 B B' hB hB' w hw hc
  refine ⟨GlobalTheory.LiftInjProof.liftInj_of_typeNZ D G Pl0 T A Ks R F hG hFull
      (fun i => ⟨hTNZ i A.μ0, hEig i A.μ0, hSp i A.μ0, hIn i A.μ0, hPar i A.μ0⟩), fun i t => ?_⟩
  refine ⟨hTNZ i t, hGM i t, hEig i t, hU i t, ?_⟩
  exact GlobalTheory.DownLift.Sat.saturated hDec hHowe D G Pl0 T A Ks R F hG hFull i t (hTNZ i t) (hEig i t) (hGM i t)
    ((hTop5.2 i t).1) (hU i t) (hPar i t)

end GlobalTheory.DownLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftRowsInjectiveAndTypePropertiesOfNonvanishingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftInj_and_properties_of_rallis_of_nonVan : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.RawLift.RallisConv D → (∀ i t, NonVan R i t) → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, TypeNZ R i t ∧ GoodMem R i t ∧ DownEig R i t ∧ UnrCorr R i t (fun _ => True) ∧ Saturated R i t := by
  first | exact @GlobalTheory.DownLift.liftRows_injective_and_typeProperties_of_nonvanishing | exact GlobalTheory.DownLift.liftRows_injective_and_typeProperties_of_nonvanishing | (intros; apply GlobalTheory.DownLift.liftRows_injective_and_typeProperties_of_nonvanishing <;> assumption)
end
