module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFramedPointOverMovedBaseFrame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslatesConjHalfSqNormEqCard
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslatesConjHalfSqNormEqCard
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.VacTransOrth

theorem vacuumTranslates_conjHalf_sq_norm_eq_card_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∀ (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → ∀ (μ : MeasureTheory.Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → nrm2 μ 𝓕 (∑ y ∈ Y, heisO ψ V W y f₀) = Y.card := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT Y hY hYd μ 𝓕 hμ
  obtain ⟨-, -, -, -, hSV, hSW, -, -, hψ, hf⟩ := hP
  obtain ⟨hd, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ V W ΛV ΛW hψ hSV hSW
  have hc0 : infPart D (cA D eT) = 0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum hT
  have hfin : ∀ y ∈ Y, y.map (infPart D) = 0 := fun y hy => by
    ext i j
    show infPart D (y i j) = 0
    rw [← hY y hy i j, RingHom.map_mul, hc0, zero_mul]
  have h := GlobalTheory.HeisOrtho.thetaNormSq_sum_heisenbergTranslates_distinctChars D ψ V W hψ.1 μ 𝓕 hμ f₀ hf.theta (hf.norm.2 (μ, 𝓕) hμ) (WO V W) Y id
    (fun _ => 1) (fun _ _ => norm_one) ?_
  · simpa only [one_smul, id] using h
  intro y hy y' hy' hne
  have hnot : y - y' ∉ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) :=
    fun hm => hne (hYd y hy y' hy' hm)
  have hm0 : (y - y').map (infPart D) = 0 := by
    ext i j
    have h1 : infPart D (y i j) = 0 := congrFun (congrFun (hfin y hy) i) j
    have h2 : infPart D (y' i j) = 0 := congrFun (congrFun (hfin y' hy') i) j
    show infPart D (y i j - y' i j) = 0
    rw [RingHom.map_sub, h1, h2, sub_zero]
  rw [hd _ hm0] at hnot
  push_neg at hnot
  obtain ⟨l, hl, hne'⟩ := hnot
  obtain ⟨ε, hε, hεf⟩ := hsign f₀ hf.lat l hl
  exact ⟨l, ε, by rcases hε with rfl | rfl <;> simp, hεf f₀ hf.lat, hne'⟩

end GlobalTheory.VacTransOrth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslatesConjHalfSqNormEqCardStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumTranslates_conjHalf_sq_norm_eq_card : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∀ (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → ∀ (μ : MeasureTheory.Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → nrm2 μ 𝓕 (∑ y ∈ Y, heisO ψ V W y f₀) = Y.card := by
  first | exact @GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt | exact GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt | (intros; apply GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulMemSupLatticeOfMemLocalUnitBall
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulMemSupLatticeOfMemLocalUnitBall
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BallSup

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem nrm_le_one_of_mem_locBall {f : NX.FmK S ((j : ℕ) + 1)} (hf : f ∈ locBall YS fw iC b j)
    (y : (Rl.FW j).Pt (placeC YS iC b)) :
    (Rl.FW j).nrm (placeC YS iC b) y (fw.e j (cuspOf YS fw j f)) ≤ 1 := by
  rw [fw.nrm_eq, Core.nrmM_le_one_iff]
  obtain ⟨q, hq⟩ := (fw.pt j (placeC YS iC b) y).2
  rcases q with ⟨qv, T, io, e, ho, y', hy', eta, heta, rfl⟩
  obtain ⟨k, hk⟩ := ReadExist.exists_isReading (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io e ho hy'
  obtain ⟨z, hz⟩ := PtC.exists_of_reading hk y' hy'
  have h1 := hf z
  rw [hz _ _ _ (cuspOf_mem_sec YS fw j f)] at h1
  obtain ⟨a, ha⟩ := (hk.int _).1 h1
  rw [← hq]
  change 0 ≤ nval T.V e (evI y' _)
  by_cases hx : evI y' (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)) = 0
  · rw [hx, nval_zero]; exact le_top
  · rw [nval_of_ne hx]
    exact EReal.coe_nonneg.2 (div_nonneg (Int.cast_nonneg
      ((GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff _).1 ⟨a, ha⟩)) (Nat.cast_nonneg _))

theorem one_tmul_mem_Bsup_of_mem_locBall
    (hiC : ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range)
    (f : NX.FmK S ((j : ℕ) + 1)) (hf : f ∈ locBall YS fw iC b j) :
    (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  obtain ⟨s, hs, hsM⟩ := GlobalTheory.supLattice_localisation_of_unitBall D.what₂.LL T0.Q.c.F _ _ _ (Rl.FW j)
    (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).2 (placeC YS iC b) (fw.e j (cuspOf YS fw j f))
    (nrm_le_one_of_mem_locBall YS fw iC b j hf)
  rw [e_cuspOf] at hsM
  set c : S.Ks := (YS.fi j).eK.symm (s : T0.Q.c.F) with hcdef
  have hc : (YS.fi j).e (c • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1) = s • (YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 := by
    rw [← algebraMap_smul D.what₂.LL c, LinearEquiv.map_smul, ← (YS.fi j).eK_LL c, hcdef, RingEquiv.apply_symm_apply,
      algebraMap_smul]
    exact (algebraMap_smul T0.Q.c.F s _)
  have hcM : c • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1 ∈ (S.A ((j : ℕ) + 1)).MK := by
    rw [(YS.fi j).mkK, hc]; exact hsM

  have hgen : (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f)) ∈ NX.Bsup S i ((j : ℕ) + 1) b :=
    Submodule.subset_span ⟨c • f, hcM, rfl⟩
  have heK : eKs YS c = (s : T0.Q.c.F) := by
    apply (algebraMap T0.Q.c.F D.what₂.LL).injective
    rw [eKs_LL, ← (YS.fi j).eK_LL c, hcdef, RingEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ : ∃ x : FractionRing (D.ntw.O i), x = NX.ιK S i b c := ⟨_, rfl⟩
  have hn1 : ‖iC x‖ = 1 := by
    rw [hx]
    change ‖embS S iC b c‖ = 1
    rw [← embC_eKs YS iC b, heK]
    refine le_antisymm (norm_int_le_one _ s) (not_lt.1 fun h => hs ?_)
    exact (mem_placeAt _ s).2 h
  have hne : x ≠ 0 := fun h => by
    rw [h, map_zero, norm_zero] at hn1; exact zero_ne_one hn1
  obtain ⟨u, hu⟩ := (hiC x⁻¹).1 (by rw [map_inv₀, norm_inv, hn1, inv_one])
  have key : (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) =
      u • (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f)) := by
    rw [← algebraMap_smul (FractionRing (D.ntw.O i)) u, hu]
    have h1 : (c • (1 : NX.KB S i b)) = (show NX.KB S i b from x) := by
      rw [Algebra.smul_def, mul_one, hx]; rfl
    change (1 : NX.KB S i b) ⊗ₜ[S.Ks] f =
      (show NX.KB S i b from x⁻¹) • ((1 : NX.KB S i b) ⊗ₜ[S.Ks] (c • f) : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1))
    rw [← TensorProduct.smul_tmul, h1, TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    exact (inv_mul_cancel₀ hne).symm
  rw [key]
  exact Submodule.smul_mem _ u hgen

end BallSup

theorem one_tmul_mem_Bsup : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC hiC b j f hf
  exact one_tmul_mem_Bsup_of_mem_locBall YS fw iC b j hiC f hf

end GlobalTheory.GeoTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulMemSupLatticeOfMemLocalUnitBallStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_tmul_mem_supLattice_of_mem_localUnitBall : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), ∀ f ∈ locBall YS fw iC b j, (show NX.Fm S i ((j : ℕ) + 1) b from (1 : NX.KB S i b) ⊗ₜ[S.Ks] f) ∈ NX.Bsup S i ((j : ℕ) + 1) b := by
  first | exact @GlobalTheory.GeoTie.one_tmul_mem_Bsup | exact GlobalTheory.GeoTie.one_tmul_mem_Bsup | (intros; apply GlobalTheory.GeoTie.one_tmul_mem_Bsup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeReadOfDeltaFrob
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TwInputs.HeckePinRead

theorem pull_locE {D : D7} {Ω : Type} [Field Ω] [Algebra D.host.E Ω] {A : Type} [CommGroup A] (a : Recip D Ω) (ha : a.Good)
    (φ : G D.host.E Ω →* A) (hφ : IsOpen (φ.ker : Set (G D.host.E Ω))) (P : Pl D.host.E) (e : AE D)
    (he : Formalism.L2.JoinChr.IsPlIdem D e P) (k : D.host.Eˣ)
    (hk : Valued.v ((Formalism.L2.Host.atFin P k : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ))
    (x : (AE D)ˣ) (hx : (x : AE D) = Formalism.L2.JoinChr.locE D e (k : D.host.E)) (B : ValuationSubring Ω)
    (hB : IsPlaceOver (F := D.host.E) B P) (hine : ∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) (σ : G D.host.E Ω)
    (hσ : IsFrob (F := D.host.E) B (normV P) σ) : a.pull φ x = (φ σ)⁻¹ := by
  have hκ : a.κ (x : AE D) = ((Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) : Neutral.B1.Ideles D.host.E) :
      AdeleRing (𝓞 D.host.E) D.host.E) := by
    rw [hx]; exact ha.loc P e he k
  have hsym : a.sym x = a.art (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)) := by
    rw [Recip.sym, MonoidHom.comp_apply]
    congr 1
    exact Units.ext hκ
  obtain ⟨y, hy, hyσ⟩ := (ha.artin.frob P B hB _).mpr ⟨σ, hσ, rfl⟩
  have hu : Valued.v (((Formalism.L2.Host.atFin P k * y⁻¹ : (P.adicCompletion D.host.E)ˣ)) : P.adicCompletion D.host.E) = 1 := by
    have hy' : Valued.v ((y : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) = WithZero.exp (-1 : ℤ) := hy
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hk, hy']
    exact mul_inv_cancel₀ WithZero.exp_ne_zero
  obtain ⟨τ, hτ, hτu⟩ := (ha.artin.ine P B hB _).mp ⟨_, hu, rfl⟩
  have hs : a.sym x = GlobalTheory.HeckeGal.toAb D.host.E Ω (τ * σ⁻¹) := by
    rw [hsym, show Formalism.L2.Host.atFin P k = (Formalism.L2.Host.atFin P k * y⁻¹) * y by group, map_mul, map_mul, hyσ,
      ← hτu, map_mul]
  rw [a.pull_eq hφ hs, map_mul, hine τ hτ, map_inv, one_mul]

theorem isOpen_ker_psiAt (D : D7) (i : D.ntw.Tw) (b : Bool) :
    IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
  have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
    ext g
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
  rw [e]
  exact D.ntw.delta_open i

theorem chi_locU_unif {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (P : PlE D.host)
    (hP : P ∉ D.ntw.S0 i) {e : AE D} (he : Formalism.L2.JoinChr.IsPlIdem D e P) (hee : e * e = e) (σ : G D.host.E D.nd.Om)
    (hσ : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ) :
    (((ρ.B i j b).de.chi (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif P)) : Circle) : ℂ) =
      (ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)))⁻¹ := by
  rw [hρ.delta i j b]
  have hopen := isOpen_ker_psiAt D i b
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ⁻¹ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ⁻¹)
  have hine : ∀ τ ∈ Ine (F := D.host.E) (D.nd.plOm.1 P), Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) τ = 1 := by
    intro τ hτ
    have h : D.ntw.delta i τ = 1 := by
      by_contra hne
      exact hP (D.ntw.primes_subset_exceptional i ((D.ntw.delta_ram i P _ (D.nd.plOm.2 P)).1 ⟨τ, hτ, hne⟩))
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, h]
  have hpull := pull_locE ρ.rc hρ.rc _ hopen P e he (Formalism.L2.Host.unif P) (Formalism.L2.Host.unif_spec P) _
    (Formalism.L2.JoinChr.locU_val hee _) _ (D.nd.plOm.2 P) hine σ hσ
  change ((charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
    (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) _ : Circle) : ℂ) = _
  rw [charOf, MonoidHom.comp_apply, MonoidHom.comp_apply, hpull, unitPart_of_pow hn]
  · simp
  · rw [← map_pow, ← map_inv, ← map_pow, map_pow (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)), hpow, map_one]

def frobU (D : D7) (P : PlE D.host) : G D.host.E D.nd.Om :=
  (GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)).choose

theorem frobU_spec (D : D7) (P : PlE D.host) : IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) (frobU D P) :=
  (GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)).choose_spec.2

def uD (D : D7) : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ := fun i b P =>
  Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) (frobU D P))

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}

theorem isDeltaInv_uD {D : D7} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hpin : RealPin Rl cG ρ) : IsDeltaInv ρ (uD D) := by
  intro i j b k P hk α z hα hz
  obtain ⟨-, -, hsp, hP⟩ := hk
  have hdQ : Bridge.SplitOff P (((ρ.B i j b).de.Q : Finset _) : Set (Pl D.host.E)) :=
    GlobalTheory.SplitOffS0.main hρ i _ (fun P' hP' => by
      rw [hρ.delta i j b] at hP'
      exact D.ntw.primes_subset_exceptional i (mem_half.1 hP').1) P hsp hP
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hdQ.1
  have hee : e * e = e := he.1.1
  have h1 := (hpin.delta i j b).2 P e (GlobalTheory.HeckeDetChar.isPlIdem he) (Formalism.L2.Host.unif P) _
    (Formalism.L2.JoinChr.locU_val hee (Formalism.L2.Host.unif P))
  have h2 := chi_locU_unif hρ i j b P hP (GlobalTheory.HeckeDetChar.isPlIdem he) hee (frobU D P) (frobU_spec D P)
  rw [GlobalTheory.HeckeDetChar.chi_detAt (hpin.delta i j b) (hρ.base i j b).de.unram (hρ.base i j b).de.split hdQ hα hz,
    show (((Rl.C.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) = (((ρ.B i j b).de.chi (Formalism.L2.JoinChr.locU hee (Formalism.L2.Host.unif P)) : Circle) : ℂ)
      from h1.symm, h2, inv_pow, inv_inv]
  rfl

end GlobalTheory.TwInputs.HeckePinRead

namespace GlobalTheory.TwInputs

end GlobalTheory.TwInputs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesMatchesRationalPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesMatchesRationalPoints
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.MtReadRat

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem cT_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (σA : A →+* A) (σB : B →+* B)
    (hc : ∀ x, φ (σA x) = σB (φ x)) {m : Type} [Fintype m] [DecidableEq m] (J g : Matrix m m A) :
    Formalism.UG.cT σB (g.map φ) * J.map φ * g.map φ = (Formalism.UG.cT σA g * J * g).map φ := by
  have : Formalism.UG.cT σB (g.map φ) = (Formalism.UG.cT σA g).map φ := by
    ext i j; simp [Formalism.UG.cT, hc]
  rw [this, Matrix.map_mul, Matrix.map_mul]

variable {D : D7}

theorem finHom_entry (V : HSp D) (h : GA D V) (X : GL (Fin V.rank) D.host.E) (hX : matHom V h = Formalism.UG.bc (incA D) X)
    (a b : Fin V.rank) : (finHom V h).1 a b = inclR (F := D.host.F) (Af D.host.F) (X.1 a b) := by
  have : (finHom V h).1 a b = Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V h).1 a b) := rfl
  rw [this, hX]
  simp [Formalism.UG.bc, inclR, incA]

theorem entry_of_ratF {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a b))
    (κ : GAf D.host.E V.rank) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E)
    (e : Bridge.ratF V γ' = frameEquiv P κ) (hR : Bridge.IsRatMat V γ' γE) (a c : Fin V.rank) :
    ((κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a c =
      Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  have e' : finHom V γ'.1 = finHom V (P.ψ κ) := congrArg Subtype.val e
  have h1 := hId κ a c
  have h2 : finMat D.sp.cm.sig V.gram (P.ψ κ) a c = inclR (F := D.host.F) (Af D.host.F) (γE.val a c) := by
    show (finHom V (P.ψ κ)).1 a c = _
    rw [← e']
    exact finHom_entry V γ'.1 γE hR a c
  rw [h2] at h1
  rw [← (RingEquiv.eq_symm_apply _).1 h1]
  exact GlobalTheory.Mem.R3.DatApi.swapCast_one_tmul hF _

theorem ratMatch_fwd {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast rfl a) (Fin.cast rfl b))) (γ : ReciprocityTheory.Aut.GQ D.host.E V.rank) :
    ∃ γ' : Formalism.L2.Theta.GQ V, Bridge.ratF V γ' = frameEquiv P γ := by

  have key := entry_of_ratF hF P hId
  haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
  haveI : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := Formalism.L2.DIV.af_nontrivial (maximalRealSubfield D.host.E)
  have hinjR : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom :
      D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield D.host.E) (RingHom.injective _)

  obtain ⟨γ0, hγ0, e0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  have hγent : ∀ a b, (γ.1.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a b =
      Algebra.TensorProduct.includeLeftRingHom ((γ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := fun a b => by
    rw [← e0]; exact Matrix.GeneralLinearGroup.map_apply _ _ _ _
  have hfin : ∀ a b, (finHom V (P.ψ γ.1)).1 a b = inclR (F := D.host.F) (Af D.host.F) ((γ0 : Matrix _ _ D.host.E) a b) :=
    fun a b => by
      show finMat D.sp.cm.sig V.gram (P.ψ γ.1) a b = _
      rw [hId]
      simp only [Fin.cast_eq_self]
      rw [hγent, RingEquiv.symm_apply_eq]
      exact (GlobalTheory.Mem.R3.DatApi.swapCast_one_tmul hF _).symm

  have hsnd : ∀ x : AF D.host.F ⊗[D.host.F] D.host.E,
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (sigR (AF D.host.F) D.sp.cm.sig x) =
      sigR (Af D.host.F) D.sp.cm.sig ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom x) :=
    fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  have hUA := (P.ψ γ.1).2
  change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((P.ψ γ.1).1.1) * JR (AF D.host.F) V.gram * (P.ψ γ.1).1.1 =
    JR (AF D.host.F) V.gram at hUA
  have hUf := congrArg (fun M => M.map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom) hUA
  rw [← cT_map _ _ _ hsnd] at hUf
  have hM : ((P.ψ γ.1).1.1 : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom =
      (γ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Af D.host.F)) := by
    ext a b; exact hfin a b
  have hJ : (JR (AF D.host.F) V.gram).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom =
      V.gram.map (inclR (F := D.host.F) (Af D.host.F)) := by
    ext a b; simp [JR, inclR]
  have hci : ∀ (R : Type) [CommRing R] [Algebra D.host.F R] (x : D.host.E),
      inclR (F := D.host.F) R (D.sp.cm.sig x) = sigR R D.sp.cm.sig (inclR (F := D.host.F) R x) := fun R _ _ x => by
    simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  rw [hM, hJ, cT_map _ _ _ (hci (Af D.host.F))] at hUf
  have hγ0' : γ0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := Matrix.map_injective hinjR hUf
  have hHR : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ0 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((γ0 : Matrix _ _ D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) *
      JR (AF D.host.F) V.gram * (γ0 : Matrix _ _ D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [JR, cT_map _ _ _ (hci (AF D.host.F))]
    exact congrArg (fun M => Matrix.map M (inclR (F := D.host.F) (AF D.host.F))) hγ0'
  refine ⟨⟨⟨_, hHR⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ0, hγ0', rfl⟩)⟩, Subtype.ext (Units.ext ?_)⟩
  ext a b
  refine (finHom_entry V ⟨_, hHR⟩ γ0 rfl a b).trans ?_
  exact (hfin a b).symm

theorem ratMatch_bwd {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast rfl a) (Fin.cast rfl b))) (γ' : Formalism.L2.Theta.GQ V) :
    ∃ γ : ReciprocityTheory.Aut.GQ D.host.E V.rank, Bridge.ratF V γ' = frameEquiv P γ := by

  have key := entry_of_ratF hF P hId
  haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
  haveI : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := Formalism.L2.DIV.af_nontrivial (maximalRealSubfield D.host.E)
  have hinjR : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom :
      D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield D.host.E) (RingHom.injective _)

  obtain ⟨γE, hγE, eE⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ'.2)
  have hR : Bridge.IsRatMat V γ' γE := eE.symm
  set κ := (frameEquiv P).symm (Bridge.ratF V γ') with hκ
  have he : Bridge.ratF V γ' = frameEquiv P κ := ((frameEquiv P).apply_symm_apply _).symm
  have hent := key κ γ' γE he hR
  have hmat : ((κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) =
      (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom := by
    ext a c; exact hent a c
  have hU := κ.2
  simp only [ReciprocityTheory.Aut.GA, ReciprocityTheory.Aut.UGroup, Subgroup.mem_mk, Set.mem_ofPred_eq] at hU
  have hc : ∀ x : D.host.E, (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E)
      ((IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x) =
      ReciprocityTheory.Aut.conjAL D.host.E (Algebra.TensorProduct.includeLeftRingHom x) := fun x => by
    simp [ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.map_tmul]
  have hcT : ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E)
      ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom) =
      (ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) (γE : Matrix _ _ _)).map
        Algebra.TensorProduct.includeLeftRingHom := by
    ext i j; simp only [ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply, hc]
  have h0 : γE ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank := by
    show (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) γE = 1
    apply Matrix.map_injective hinjL
    simp only
    rw [Matrix.map_mul, ← hcT, ← hmat, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hU
  refine ⟨⟨κ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γE, h0, Units.ext ?_⟩)⟩, he⟩
  rw [hmat]
  ext a c
  exact Matrix.GeneralLinearGroup.map_apply _ _ _ _

end GlobalTheory.MtReadRat

namespace GlobalTheory.MtRead
open GlobalTheory.MtReadRat Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem ratMatch_of_idFrame : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → RatMatch (frameEquiv P) ∧ ∀ (hn : V.rank = n) (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.ratF V γ' = frameEquiv P γ → Bridge.IsRatMat V γ' γE → ∀ a c, (((γ : GAf D.host.E n) : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c) = Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  intro D V n hF P ⟨hn, hId⟩
  subst hn
  refine ⟨⟨ratMatch_fwd hF P hId, ratMatch_bwd hF P hId⟩, fun hn γ γ' γE e hR a c => ?_⟩
  simpa only [Fin.cast_eq_self] using entry_of_ratF hF P hId γ.1 γ' γE e hR a c

end GlobalTheory.MtRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesMatchesRationalPointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameKeepsMatrices_matches_rationalPoints : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → RatMatch (frameEquiv P) ∧ ∀ (hn : V.rank = n) (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.ratF V γ' = frameEquiv P γ → Bridge.IsRatMat V γ' γE → ∀ a c, (((γ : GAf D.host.E n) : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c) = Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  first | exact @GlobalTheory.MtRead.ratMatch_of_idFrame | exact GlobalTheory.MtRead.ratMatch_of_idFrame | (intros; apply GlobalTheory.MtRead.ratMatch_of_idFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesSplitPlaceReductionLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesSplitPlaceReductionLocal
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtRead.Red

section General

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem ALint_eq : ReciprocityTheory.Aut.ALint L = Formalism.L2.Herm.intAf (maximalRealSubfield L) L := by
  apply le_antisymm
  · refine Subring.closure_le.2 ?_
    rintro z (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), ⟨y, rfl⟩⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  · refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, y, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨y, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩)

theorem proj_tmul_one (s : ReciprocityTheory.Aut.SplitPlace L) (y : L) :
    s.proj (y ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) = s.i y := by
  simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem proj_mem (s : ReciprocityTheory.Aut.SplitPlace L) {z : ReciprocityTheory.Aut.AL L} (hz : z ∈ ReciprocityTheory.Aut.ALint L) :
    s.proj z ∈ s.v.adicCompletionIntegers (maximalRealSubfield L) := by
  have hle : ReciprocityTheory.Aut.ALint L ≤ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.comap s.proj := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨y, rfl⟩ | ⟨c, hc, rfl⟩)
    · show s.proj _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, proj_tmul_one]
      exact s.split_le_one y
    · show s.proj _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
        map_one, one_mul]
      exact hc s.v
  exact hle hz

theorem proj_lt_one (s : ReciprocityTheory.Aut.SplitPlace L) (z : Formalism.L2.Herm.intAf (maximalRealSubfield L) L)
    (hz : z ∈ Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) :
    Valued.v (s.proj (z : ReciprocityTheory.Aut.AL L)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe, proj_tmul_one]
    exact hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    have hc : Valued.v (s.proj (c : ReciprocityTheory.Aut.AL L)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (proj_mem s ((ALint_eq (L := L)).ge c.2))
    calc Valued.v (s.proj (c : ReciprocityTheory.Aut.AL L)) * Valued.v (s.proj (x : ReciprocityTheory.Aut.AL L))
        ≤ 1 * Valued.v (s.proj (x : ReciprocityTheory.Aut.AL L)) := by gcongr
      _ < 1 := by rwa [one_mul]

theorem resS_iff (s : ReciprocityTheory.Aut.SplitPlace L) (z : Formalism.L2.Herm.intAf (maximalRealSubfield L) L) (u : 𝓞 L) :
    Valued.v (s.i (u : L) - s.proj (z : ReciprocityTheory.Aut.AL L)) < 1 ↔
      Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z = Ideal.Quotient.mk s.w.asIdeal u := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z)
  have e1 : Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal (Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) z :=
    (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := maximalRealSubfield L) s.w.asIdeal s.w.ne_bot)).apply_symm_apply _
  have e2 : Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal (Ideal.Quotient.mk s.w.asIdeal b) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) (Formalism.L2.DIV.oToS (maximalRealSubfield L) L b) :=
    Ideal.quotientMap_mk
  have hmem : z - Formalism.L2.DIV.oToS (maximalRealSubfield L) L b ∈ Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal := by
    refine Ideal.Quotient.eq.1 ?_
    exact e1.symm.trans ((congrArg (Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal) hb.symm).trans e2)
  have h1 : Valued.v (s.proj (z : ReciprocityTheory.Aut.AL L) - s.i (algebraMap (𝓞 L) L b)) < 1 := by
    have := proj_lt_one s _ hmem
    rwa [AddSubgroupClass.coe_sub, map_sub, Formalism.L2.DIV.oToS_coe, proj_tmul_one] at this
  rw [← hb, eq_comm (a := Ideal.Quotient.mk s.w.asIdeal b), Ideal.Quotient.eq]
  show _ ↔ Valued.v (s.i ((u - b : 𝓞 L) : L)) < 1
  have e : s.i ((u - b : 𝓞 L) : L) =
      (s.i (u : L) - s.proj (z : ReciprocityTheory.Aut.AL L)) + (s.proj (z : ReciprocityTheory.Aut.AL L) - s.i (algebraMap (𝓞 L) L b)) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub]
    ring
  constructor
  · intro h
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
  · intro h
    rw [← sub_eq_iff_eq_add] at e
    rw [← e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h h1)

def castE {F : Subfield L} (h : F = maximalRealSubfield L) :
    ReciprocityTheory.Aut.AL L ≃+* L ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (GlobalTheory.Mem.R3.swapCast h).symm.trans (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) L).toRingEquiv

theorem castE_rfl (x : ReciprocityTheory.Aut.AL L) : castE (L := L) rfl x = x :=
  (Algebra.TensorProduct.comm (maximalRealSubfield L) (ReciprocityTheory.Aut.AFplus L) L).apply_symm_apply x

theorem castE_mem_iff {F : Subfield L} (h : F = maximalRealSubfield L) (x : ReciprocityTheory.Aut.AL L) :
    castE h x ∈ Formalism.L2.Herm.intAf F L ↔ x ∈ ReciprocityTheory.Aut.ALint L := by
  subst h
  rw [castE_rfl, ALint_eq]

theorem resS_castE_iff {F : Subfield L} (h : F = maximalRealSubfield L) (s : ReciprocityTheory.Aut.SplitPlace L) (x : ReciprocityTheory.Aut.AL L)
    (z : Formalism.L2.Herm.intAf F L) (hz : (z : L ⊗[F] FiniteAdeleRing (𝓞 F) F) = castE h x) (u : 𝓞 L) :
    Valued.v (s.i (u : L) - s.proj x) < 1 ↔ Formalism.L2.DIV.resS F s.w z = Ideal.Quotient.mk s.w.asIdeal u := by
  subst h
  rw [castE_rfl] at hz
  rw [← hz]
  exact resS_iff s z u

end General

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}

theorem frGL_one_val (y : GL (Fin m) (Formalism.L2.Herm.intAf F E)) (a c : Fin m) :
    (frGL (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) y).val a c = (y.val a c : E ⊗[F] Formalism.L2.Herm.Af F) := by
  have h : frGL (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) y = intGL F E m y := by
    simp [frGL]
  rw [h]
  rfl

theorem mem_St_one (g : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) (h : ∀ a c, g.val a c ∈ Formalism.L2.Herm.intAf F E)
    (h' : ∀ a c, (g⁻¹).val a c ∈ Formalism.L2.Herm.intAf F E) : g ∈ St (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  have inj : Function.Injective ((Formalism.L2.Herm.intAf F E).subtype.mapMatrix (m := Fin m)) :=
    fun x y hxy => Matrix.ext fun a c => Subtype.ext (congrFun (congrFun hxy a) c)
  refine ⟨⟨Matrix.of fun a c => ⟨_, h a c⟩, Matrix.of fun a c => ⟨_, h' a c⟩, inj ?_, inj ?_⟩, ?_⟩
  · rw [map_mul, map_one]
    exact g.mul_inv
  · rw [map_mul, map_one]
    exact g.inv_mul
  · refine Units.ext (Matrix.ext fun a c => ?_)
    rw [frGL_one_val]
    rfl

end Stab

theorem red_eq_local : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → ∀ (hn : V.rank = n) (κ : GAf D.host.E n), (κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D))) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → ∀ a c : Fin V.rank, NX.locM s κ (Fin.cast hn a) (Fin.cast hn c) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) ∧ ∀ u : 𝓞 D.host.E, Valued.v (s.i (u : D.host.E) - NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔ (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ))).val a c = Ideal.Quotient.mk s.w.asIdeal u := by
  intro D V n hF P hP hn κ
  obtain ⟨hn', hP⟩ := hP
  have ent : ∀ (κ : GAf D.host.E n) a c, (Lev.finE V (P.ψ κ)).val a c =
      castE hF ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c)) := fun κ a c =>
    congrArg (Lev.swapAE D) (hP κ a c)
  have toSt : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)) := fun hκ => by
    refine mem_St_one _ (fun a c => ?_) (fun a c => ?_)
    · rw [ent]
      exact (castE_mem_iff hF _).2 (hκ _ _)
    · rw [← map_inv, ← map_inv, ent]
      exact (castE_mem_iff hF _).2 (Subgroup.inv_mem _ hκ _ _)
  refine ⟨⟨toSt, ?_⟩, fun s hκ a c => ⟨proj_mem s (hκ _ _), fun u => ?_⟩⟩
  · rintro ⟨y, hy⟩ i j
    have h1 := ent κ (Fin.cast hn.symm i) (Fin.cast hn.symm j)
    rw [← hy, frGL_one_val] at h1
    exact (castE_mem_iff hF _).1 (h1 ▸ (y.val _ _).2)
  · obtain ⟨y, hy⟩ := toSt hκ
    have h1 := ent κ a c
    rw [← hy, frGL_one_val] at h1
    rw [← hy, redFn_frGL]
    exact resS_castE_iff hF s _ (y.val a c) h1 u

end GlobalTheory.MtRead.Red

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesSplitPlaceReductionLocalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → ∀ (hn : V.rank = n) (κ : GAf D.host.E n), (κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D))) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → ∀ a c : Fin V.rank, NX.locM s κ (Fin.cast hn a) (Fin.cast hn c) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) ∧ ∀ u : 𝓞 D.host.E, Valued.v (s.i (u : D.host.E) - NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔ (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ))).val a c = Ideal.Quotient.mk s.w.asIdeal u := by
  first | exact @GlobalTheory.MtRead.Red.red_eq_local | exact GlobalTheory.MtRead.Red.red_eq_local | (intros; apply GlobalTheory.MtRead.Red.red_eq_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralConjugateFlipScalarFiniteAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralConjugateFlipScalarFiniteAdelic
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

open GlobalTheory.IdemSupport

theorem idempotentFlip_mul_conjFlip_eq_one {R : Type} [CommRing R] {e x y c : R} (he : e * e = e) (hc : c * c = c) (hec : e * c = 0)
    (hxy : x * y = 1) : (e * x + c * y + (1 - e - c)) * (c * x + e * y + (1 - c - e)) = 1 := by
  linear_combination (x*y - x - y + 1) * he + (x*y - x - y + 1) * hc + (x^2 + y^2 - 2*x - 2*y + 2) * hec + (e + c) * hxy

theorem complementIdempotent_mul_idempotentFlip {R : Type} [CommRing R] {e x y c : R} (he : e * e = e) (hc : c * c = c) (hec : e * c = 0) :
    (1 - (e + c)) * (e * x + c * y + (1 - e - c)) = 1 - (e + c) := by
  linear_combination (1 - x) * he + (1 - y) * hc + (2 - x - y) * hec

theorem orthogonal_mul_idempotentFlip_sub_one_eq_zero {R : Type} [CommRing R] {e x y c f : R} (h1 : f * e = 0) (h2 : f * c = 0) :
    f * (e * x + c * y + (1 - e - c) - 1) = 0 := by
  linear_combination (x - 1) * h1 + (y - 1) * h2

theorem natCast_mul_incA_inv {D : D7} {m : ℕ} (hm : m ≠ 0) : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
  rw [← map_natCast (incA D) m, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hm), map_one]

theorem cA_incA_natCast_inv {D : D7} (m : ℕ) : cA D (incA D ((m : D.host.E)⁻¹)) = incA D ((m : D.host.E)⁻¹) := by
  rw [cA_incA, star_inv₀, star_natCast]

theorem cA_flipElt {D : D7} (e : AE D) (m : ℕ) :
    cA D (flipElt e m) = cA D e * (m : AE D) + e * incA D ((m : D.host.E)⁻¹) + (1 - cA D e - e) := by
  unfold flipElt
  rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_sub, map_sub, map_one, map_natCast, cA_incA_natCast_inv, cA_cA]

theorem flipElt_mul_cA {D : D7} {e : AE D} (he : e * e = e) (hec : e * cA D e = 0) {m : ℕ} (hm : m ≠ 0) :
    flipElt e m * cA D (flipElt e m) = 1 := by
  rw [cA_flipElt]
  exact idempotentFlip_mul_conjFlip_eq_one he (by rw [← map_mul, he]) hec (natCast_mul_incA_inv hm)

theorem flipElt_sub_one_mul {D : D7} {e f : AE D} (m : ℕ) (h1 : f * e = 0) (h2 : f * cA D e = 0) :
    f * (flipElt e m - 1) = 0 := by
  unfold flipElt
  exact orthogonal_mul_idempotentFlip_sub_one_eq_zero h1 h2

def scalGL {R : Type} [CommRing R] (n : ℕ) (a b : R) (h : a * b = 1) : GL (Fin n) R :=
  ⟨a • (1 : Matrix (Fin n) (Fin n) R), b • (1 : Matrix (Fin n) (Fin n) R),
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, h, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, mul_comm, h, one_smul]⟩

theorem cT_scalar {R : Type} [CommRing R] (σ : R →+* R) (n : ℕ) (a : R) :
    Formalism.UG.cT σ (a • (1 : Matrix (Fin n) (Fin n) R)) = σ a • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp only [if_true, mul_one]
  · simp only [if_neg (Ne.symm hij), if_neg hij, mul_zero, map_zero]

theorem scalGL_mem_UJ {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (J : Matrix (Fin n) (Fin n) R) (a b : R)
    (h : a * b = 1) (hb : σ a = b) : scalGL n a b h ∈ Formalism.UG.UJ σ J := by
  show Formalism.UG.cT σ (a • (1 : Matrix (Fin n) (Fin n) R)) * J * (a • (1 : Matrix (Fin n) (Fin n) R)) = J
  rw [cT_scalar, hb, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, h, one_smul]

def scalU {D : D7} (V : HSp D) (a : AE D) (ha : a * cA D a = 1) : GA D V :=
  ⟨scalGL V.rank a (cA D a) ha, scalGL_mem_UJ _ _ a (cA D a) ha rfl⟩

theorem mt_scalU {D : D7} (V : HSp D) (a : AE D) (ha : a * cA D a = 1) :
    Formalism.L2.Theta.mt V (scalU V a ha) = a • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

theorem scalar_sub_one_entry {R : Type} [CommRing R] {n : ℕ} {f a : R} (h : f * (a - 1) = 0) (i j : Fin n) :
    f * (a • (1 : Matrix (Fin n) (Fin n) R) - 1) i j = 0 := by
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij, mul_one]; exact h
  · rw [if_neg hij, mul_zero, sub_zero, mul_zero]

theorem oneAt_scalU {D : D7} (V : HSp D) {a : AE D} (ha : a * cA D a = 1) (l : ℕ)
    (h : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → algebraMap (AF D.host.F) (AE D) ε * (a - 1) = 0) :
    OneAt V l (scalU V a ha) := by
  intro v ε hε hlv i j
  rw [mt_scalU]
  exact scalar_sub_one_entry (h v ε hε hlv) i j

theorem flip_central_exists : ∀ (D : D7) (V : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → m ≠ 0 → ∃ z : GA D V, z ∈ GfC V ∧ (∀ l : ℕ, (∀ PP ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → OneAt V l z) ∧ Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  intro D V T m eT hT hm
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have he : eT * eT = eT := GlobalTheory.Tow.idemSum_mul_of_subset hT hT subset_rfl
  have hec : eT * cA D eT = 0 := hT.2
  have hcc : cA D eT * cA D eT = cA D eT := by rw [← map_mul, he]
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := hT
  have hinv := flipElt_mul_cA he hec hm
  refine ⟨scalU V _ hinv, ?_, ?_, mt_scalU V _ hinv⟩
  · have hinf : infPart D eT = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsum, map_sum]
      exact Finset.sum_eq_zero fun PP hPP => (delta_of_isIdemAt hΦ (hes PP hPP)).1
    refine mem_GfC_of_suppF V (f := eT + cA D eT) ?_ ((suppF_iff V _ _).2 ?_)
    · rw [map_add (f := _), hinf, (parts_cA eT).1, hinf, map_zero, add_zero]
    · rw [mt_scalU, smul_smul]
      unfold flipElt
      rw [complementIdempotent_mul_idempotentFlip he hcc hec]
  · intro l hl
    refine oneAt_scalU V hinv l fun v ε hε hlv => ?_
    have h0 : algebraMap (AF D.host.F) (AE D) ε * eT = 0 := by
      rw [hsum, Finset.mul_sum]
      refine Finset.sum_eq_zero fun PP hPP => ?_
      have hd := delta_of_isIdemAt hΦ (hes PP hPP)
      refine hΦ.ext' (by rw [RingHom.map_mul, (place_comp hΦ hε).1, zero_mul, RingHom.map_zero]) fun Q => ?_
      rw [ev_mul, ev_zero]
      by_cases hQ : Q = PP
      · subst hQ
        by_cases hQv : Q.under (𝓞 D.host.F) = v
        · exfalso
          apply hl Q hPP
          have h1 := hlv
          rw [← hQv] at h1
          change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal at h1
          rwa [map_natCast] at h1
        · rw [(place_comp hΦ hε).2.2 Q hQv, zero_mul]
      · rw [hd.2.2 Q hQ, mul_zero]
    have h0' : algebraMap (AF D.host.F) (AE D) ε * cA D eT = 0 := by
      rw [← cA_algebraMap ε, ← map_mul, h0, map_zero]
    exact flipElt_sub_one_mul m h0 h0'

end GlobalTheory.LevelSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralConjugateFlipScalarFiniteAdelicStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_conjugateFlipScalar_finiteAdelic : ∀ (D : D7) (V : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → m ≠ 0 → ∃ z : GA D V, z ∈ GfC V ∧ (∀ l : ℕ, (∀ PP ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → OneAt V l z) ∧ Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  first | exact @GlobalTheory.LevelSeries.flip_central_exists | exact GlobalTheory.LevelSeries.flip_central_exists | (intros; apply GlobalTheory.LevelSeries.flip_central_exists <;> assumption)
end
end
