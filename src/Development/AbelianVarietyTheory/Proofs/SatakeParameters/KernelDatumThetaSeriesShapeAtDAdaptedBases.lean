module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBases
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtLinAdaptedCoefEqStandardSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesEigenframeAtRamifiedPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAllPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ShapeNormalisedThetaCombinationsDualBasesAtD
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOfMemSq
open NumberField

noncomputable section

namespace GlobalTheory.EmbSepUnram

open GlobalTheory.Proof.IdempotentLatticeSequence (primeOf mem_primeOf primeOf_isMaximal natCast_mem_primeOf norm_int_le)

variable {p : ℕ} [Fact p.Prime]

theorem norm_sub_int_le {E : Type} [Field E] (φ ψ : E →+* ℂ_[p]) (y : 𝓞 E) : ‖φ (y : E) - ψ (y : E)‖ ≤ 1 :=
  by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_int_le φ y) ?_)
  rw [norm_neg]; exact norm_int_le ψ y

theorem exists_algEquiv {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] [IsGalois ℚ E]
    (ψ₁ ψ₂ : E →+* ℂ_[p]) (h : ∀ x : K, ψ₁ (algebraMap K E x) = ψ₂ (algebraMap K E x)) :
    ∃ σ : E ≃ₐ[K] E, ∀ x, ψ₁ x = ψ₂ (σ x) := by
  let _ : Algebra E ℂ_[p] := ψ₂.toAlgebra
  have _ := IsScalarTower.of_algebraMap_eq (R := ℚ) (S := E) (A := ℂ_[p]) fun x => by
    show algebraMap ℚ ℂ_[p] x = ψ₂ (algebraMap ℚ E x)
    rw [eq_ratCast (algebraMap ℚ ℂ_[p]), eq_ratCast (algebraMap ℚ E), map_ratCast]
  let τ : E ≃ₐ[ℚ] E := (ψ₁.toRatAlgHom).restrictNormal' E
  have hτ : ∀ x, ψ₂ (τ x) = ψ₁ x := fun x => (ψ₁.toRatAlgHom).restrictNormal_commutes E x
  let σ : E ≃ₐ[K] E := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun x => ψ₂.injective (by
    change ψ₂ (τ _) = _
    rw [hτ]; exact h x)
  exact ⟨σ, fun x => (hτ x).symm⟩

theorem norm_le_of_mem_sq {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ_[p]) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : 𝓞 E, ‖φ (y : E)‖ < 1 → ‖φ (y : E)‖ ≤ r) {z : 𝓞 E} (hz : z ∈ primeOf φ ^ 2) :
    ‖φ (z : E)‖ ≤ r * r := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · change ‖φ (algebraMap (𝓞 E) E (a * b))‖ ≤ r * r
    rw [map_mul, map_mul, norm_mul]
    exact mul_le_mul (h a ha) (h b hb) (norm_nonneg _) hr
  · change ‖φ (algebraMap (𝓞 E) E (a + b))‖ ≤ r * r
    rw [map_add (f := _), map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem embSep : Formalism.L2.Th1.GD.EmbSep := by
  intro p _ K E _ _ _ _ _ _ φ ψ₁ ψ₂ ⟨π, hπ1, hπ⟩ hK hφ hne
  by_contra hc
  push Not at hc
  have h1 : ∀ y : 𝓞 E, ‖ψ₂ (y : E) - ψ₁ (y : E)‖ < 1 := fun y => by
    have a := lt_of_le_of_ne (norm_sub_int_le φ ψ₁ y) (hc y)
    have e : ψ₂ (y : E) - ψ₁ (y : E) = (φ (y : E) - ψ₁ (y : E)) + -(φ (y : E) - ψ₂ (y : E)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a ?_)
    rw [norm_neg]; exact hφ y
  have hP : ∀ z : 𝓞 E, ‖ψ₂ (z : E)‖ < 1 → z ∈ primeOf φ := fun z hz => by
    change ‖φ (z : E)‖ < 1
    rw [← sub_add_cancel (φ (z : E)) (ψ₂ (z : E))]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hφ z) hz)
  obtain ⟨σ, hσ⟩ := exists_algEquiv ψ₁ ψ₂ hK
  have : IsGalois K E := IsGalois.tower_top_of_isGalois ℚ K E
  have := primeOf_isMaximal φ
  have hP0 : primeOf φ ≠ ⊥ := fun h => by
    have := natCast_mem_primeOf φ
    rw [h, Ideal.mem_bot] at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  have : IsGaloisGroup (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) := IsGaloisGroup.of_isFractionRing (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) K E
  have hp0 : (primeOf φ).under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0

  set r := ‖φ (algebraMap K E (π : K))‖ with hr
  have hr0 : 0 < r := by
    refine lt_of_lt_of_le ?_ (hπ (p : 𝓞 E) (natCast_mem_primeOf φ))
    rw [norm_pos_iff]
    have : ((p : 𝓞 E) : E) = (p : E) := rfl
    rw [this, map_natCast]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsq : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 E)) ((primeOf φ).under (𝓞 K)) ≤ primeOf φ ^ 2 := fun hle => by
    have hπP : algebraMap (𝓞 K) (𝓞 E) π ∈ primeOf φ ^ 2 :=
      hle (Ideal.mem_map_of_mem _ (show algebraMap (𝓞 K) (𝓞 E) π ∈ primeOf φ from hπ1))
    have := norm_le_of_mem_sq φ hr0.le hπ hπP
    change r ≤ r * r at this
    nlinarith
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) ((primeOf φ).under (𝓞 K)) (primeOf φ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx ((primeOf φ).under (𝓞 K)) (primeOf φ) (E ≃ₐ[K] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx ((primeOf φ).under (𝓞 K)) (primeOf φ) hp0,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).1 hsq)] at hcard
  have hs : σ ∈ (primeOf φ).inertia (E ≃ₐ[K] E) := AddSubgroup.mem_inertia.2 fun x => hP _ (by
    change ‖ψ₂ (σ (x : E) - (x : E))‖ < 1
    rw [map_sub, ← hσ]
    exact h1 x |> fun h => by rwa [norm_sub_rev] at h)
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact hne (RingHom.ext fun x => by rw [hσ, hs]; rfl)

end GlobalTheory.EmbSepUnram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ShapeNormalisedThetaCombinationsDualBasesAtD
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d

theorem jets_comb {K : Type} [NormedField K] [IsUltrametricDist K] {X κ : Type} [Fintype κ] (r : κ → K)
    (sg : κ → MvPowerSeries X K) (hr : ∀ k, ‖r k‖ ≤ 1) (hsg : ∀ k, JetsIntegral (sg k)) :
    JetsIntegral (∑ k, MvPowerSeries.C (r k) * sg k) := by
  refine (Formalism.L2.Th1.G.jets_in_norm_holds K X _).2 ?_
  refine Formalism.L2.Th1.G.jetsIn_sum _ _ fun k _ => ?_
  exact Formalism.L2.Th1.G.jetsIn_mul (Formalism.L2.Th1.G.jetsIn_C (hr k))
    ((Formalism.L2.Th1.G.jets_in_norm_holds K X _).1 (hsg k))

theorem atLin_X {σ κ : Type} [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    TaylorLogMetric.atLin c (fun j => MvPowerSeries.X j) F = Formalism.L2.Th1.G.linSub c F := rfl

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem analytic_U (B : Base D cc δ) (t : TaylorLogMetric.VC D N N') {G : TaylorLogMetric.VC D N N' → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) :
    AnalyticOnNhd ℂ (TaylorLogMetric.U D B.tor t G) Set.univ := _root_.GlobalTheory.Proof.integralJets_normalisedThetaCombinations_away_d.analytic_U (G := G) B t hG

abbrev jetS (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hd : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) : ℂ_[p] :=
  Formalism.L2.Th1.C.jet (Formalism.L2.Th1.A.logSer (curveL p (cmL a₀ b₀ dK ha hd lam hlam) ι))
    (Formalism.L2.Th1.Top.phC p (cmL a₀ b₀ dK ha hd lam hlam) ι) 2

theorem term_shape (hIn : GlobalTheory.ThLoc.Inputs) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {X : Fields} (s : Seam D X) (hs : s.Ok)
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (hcm : CmOK a₀ b₀ c₀ D.host.d)
    (hlat : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ)
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA₁ : TaylorLogMetric.admitted D N N' L₁ L₁') {p : ℕ} [Fact p.Prime] (hpd : p = D.host.d)
    (hE : TaylorLogMetric.EqAt D p L L₁) (hE' : TaylorLogMetric.EqAt D p L' L₁')
    (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]) (hι : Formalism.L2.KerInert.IotaExt lm ι)
    (hInt : IntCurve (curveL p (cmL a₀ b₀ D.host.d ha hd lam hlam) ι))
    (t : TaylorLogMetric.VC D N N') (ht : TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D B.tor L L') t)
    (u : HH D → ℂ_[p]) (M : D.what₂.Tau × Fin N' × Fin N → (Bool × HH D) × Fin N × Fin N' → ℂ_[p])
    (hfr : ∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau N N' → ℂ) (A : J → (Bool × HH D) × Fin N × Fin N' → ℂ_[p])
      (cE sE : D.host.E ≃+* D.host.E) (δE : D.host.E) (emb : Bool × HH D → (D.host.E →+* ℂ_[p]))
      (act : 𝓞 D.host.E → (DVar X.Tau N N' → ℂ) →ₗ[ℂ] (DVar X.Tau N N' → ℂ)),
      Formalism.L2.Th1.GD.IsEigenFrame ι (cmL a₀ b₀ D.host.d ha hd lam hlam) (ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)))
        (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF (TaylorLogMetric.tor0 D cc δ) L₁ L₁') D.host.E cE sE δE emb
        act v A u ∧ ∀ i x, frameM (ι : ℂ →+* ℂ_[p]) v A i x = M (s.iT i.1, i.2) x) :
    ‖jetS a₀ b₀ D.host.d ha hd lam hlam p ι‖ ≤ ‖(D.host.d : ℂ_[p])‖ ^ (-(1 / 2 : ℝ)) ∧
    ∃ sg : MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p], JetsIntegral sg ∧
      TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (TaylorLogMetric.pSer D lm (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁'))) =
        Formalism.DworkPowerSeriesWeights.mvExp ((-jetS a₀ b₀ D.host.d ha hd lam hlam p ι) • Formalism.L2.Th1.G.betaPair (HH D) N N' u) * sg := by
  obtain ⟨M₀, hM0, hMc, hMm⟩ := (Formalism.L2.KerInert.pairing_fact D cc δ p N N' L L₁ L' L₁' hE hE').2 t ht
  obtain ⟨J, _, v, A, cE, sE, δE, emb, act, hEF, hfM⟩ := hfr
  have hLat := GlobalTheory.T.normalisedThetaFamily_normalised_all_places D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L₁ L₁' hA₁ p ι
  have hθ := hLat.mem_th.1
  have hEan : AnalyticOnNhd ℂ (B.eNat χ N N' L₁ L₁') Set.univ := by
    have h1 : AnalyticOnNhd ℂ (fun w : TaylorLogMetric.VC D N N' => (s.flatV N N').symm w) Set.univ :=
      (LinearMap.toContinuousLinearMap (s.flatV N N').symm.toLinearMap).analyticOnNhd _
    have h2 := hθ.comp h1 (fun _ _ => Set.mem_univ _)
    have e : (B.eNat χ N N' L₁ L₁') = (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) ∘ (fun w : TaylorLogMetric.VC D N N' => (s.flatV N N').symm w) := by
      funext w
      simp
    rw [e]
    exact h2
  have hGan := analytic_U B t hEan
  have hCo : TaylorLogMetric.CoefIn D (TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁')) TaylorLogMetric.Qbar :=
    hIn.algT D cc δ B χ hcc hδ hχ N N' L₁ L₁' hA₁ t ⟨M₀, hM0, hMm⟩
  have hU : (fun z => TaylorLogMetric.U D B.tor t (B.eNat χ N N' L₁ L₁') (s.flatV N N' z)) =
      Formalism.L2.Th1.H.opU (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) ((s.flatV N N').symm t)
        (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) := by
    funext z
    rw [KS.opU_pb (s.flatV N N') _ _ (KS.form_flat s (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))), LinearEquiv.apply_symm_apply]
    simp only [Formalism.L2.Th1.H.opU, formV_apply]
    rfl
  have hfr' : (fun (i : DVar X.Tau N N') x => M (s.iT i.1, i.2) x) = frameM (ι : ℂ →+* ℂ_[p]) v A := by
    funext i x
    exact (hfM i x).symm
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨hS, sg, hsg, heq⟩ := hIn.shape GlobalTheory.EmbSepUnram.embSep a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (DVar X.Tau N N')
    (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L₁ L₁') hLat.selfDual hLat.stable
    (fun z => B.eNat χ N N' L₁ L₁' (s.flatV N N' z)) hLat.mem_th p (dvd_of_eq hpd) ι hInt hLat.locNorm Unit (fun _ => 1)
    (fun _ => (s.flatV N N').symm t) M₀ (fun _ => by simp) hM0
    (fun h => by
      have := Nat.Coprime.eq_one_of_dvd hMc.symm h
      exact (Fact.out : p.Prime).one_lt.ne' this)
    (fun _ => by
      show s.flatV N N' ((M₀ : ℂ) • (s.flatV N N').symm t) ∈ TaylorLogMetric.La D B.tor L₁ L₁'
      rw [map_smul, LinearEquiv.apply_symm_apply, Nat.cast_smul_eq_nsmul]
      exact hMm)
    J v (HH D) N N' A u D.host.E cE sE δE emb act hEF
  refine ⟨hS, sg, hsg, ?_⟩
  rw [GlobalTheory.FlatTaylorBridge.bridge D X s N N' p lm ι hι _ hGan hCo _ M, hfr', hU]
  simpa [thetaLin] using heq

end GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d

namespace GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d

theorem expS_eq (D : D7) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (S : ℂ_[p]) (u : HH D → ℂ_[p]) :
    product_zeroth_first_parts.expS ℂ_[p] (-(S • ∑ t : HH D, u t • ∑ a : Fin N, ∑ b : Fin N',
      (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
        MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p]))) =
    Formalism.DworkPowerSeriesWeights.mvExp ((-S) • Formalism.L2.Th1.G.betaPair (HH D) N N' u) := by
  have e : (-(S • ∑ t : HH D, u t • ∑ a : Fin N, ∑ b : Fin N',
      (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
        MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p]))) =
      (-S) • Formalism.L2.Th1.G.betaPair (HH D) N N' u := by
    rw [neg_smul]
    congr 2
    unfold Formalism.L2.Th1.G.betaPair
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fintype.sum_prod_type, MvPowerSeries.smul_eq_C_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_assoc]
  rw [e]
  rfl

theorem norm_bound {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (h : ‖x‖ ≤ ‖(p : ℂ_[p])‖ ^ (-(1 / 2 : ℝ))) :
    ‖x‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have e : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
  have e2 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [e, norm_algebraMap', Padic.norm_p]
  rw [e2, Real.inv_rpow hp.le, Real.rpow_neg hp.le, inv_inv] at h
  exact h

theorem atLin_comb {σ ν κ : Type} [Finite σ] [Fintype ν] [Fintype κ] {p : ℕ} [Fact p.Prime] (M : σ → ν → ℂ_[p]) (r : κ → ℂ_[p])
    (G : κ → MvPowerSeries σ ℂ_[p]) :
    TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (∑ k, algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (r k) * G k) =
      ∑ k, MvPowerSeries.C (r k) * TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (G k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [atLin_X, ← Formalism.L2.Th1.G.linSubHom_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, AlgHom.commutes, Formalism.L2.Th1.G.linSubHom_apply]
  rfl

theorem jets_prod {ν : Type} {p : ℕ} [Fact p.Prime] {sg : MvPowerSeries ν ℂ_[p]} (h : JetsIntegral sg) (m : ν →₀ ℕ) :
    ‖(m.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff m sg‖ ≤ 1 := by
  have := h m
  simpa only [Formalism.DworkPowerSeriesWeights.mfact, Finsupp.prod, Nat.cast_prod] using this

theorem comb_exp {ν κ : Type} [Fintype κ] {K : Type} [CommRing K] (E : MvPowerSeries ν K) (r : κ → K)
    (T sg : κ → MvPowerSeries ν K) (h : ∀ k, T k = E * sg k) :
    ∑ k, MvPowerSeries.C (r k) * T k = E * ∑ k, MvPowerSeries.C (r k) * sg k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h k, mul_left_comm]

end GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d

theorem GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.shapeComb : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p = D.host.d → ∀ (cD : D.what₂.Tau → ℂ), IsDgen D cD → ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (κ : D.what₂.Tau → ℂ_[p]), GlobalTheory.KerStd.StdBases D lm L P → GlobalTheory.KerStd.StdBases D lm L' P' → (∀ τ, ‖κ τ‖ ≤ ‖TaylorLogMetric.lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], TaylorLogMetric.IsComb D B.tor (B.eNat χ) lm L L' F → OrbitPlaces.ShapeD D p (GlobalTheory.KerStd.stdSer D lm κ P P' F) := by
  intro hIn D cc δ hcc hδ B χ hχ X s hs N N' L L' hA p _ lm hpd cD hgen P P' κ hP hP' hκ F hF
  obtain ⟨ι, hι⟩ := hIn.lamExt p lm
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd : 0 < D.host.d := hdp.pos
  have hd8 : D.host.d % 8 = 7 := by
    have := D.host.hyp.2.2.2.1
    omega
  obtain ⟨a₀, b₀, c₀, ha, lam, hlam, hcm, hL⟩ := KS.exists_cmOK D.host.d hd hd8 hdp B.L (GlobalTheory.FourthRootStd.hst B)
  have hlat : (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ := by
    rw [hL]
    exact B.lat
  have h5 : 5 ≤ p := by omega
  have hInt := GlobalTheory.GoodModelFive.goodModel_five hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hlat p h5 ι
  obtain ⟨u, hu, hfr⟩ := GlobalTheory.T.dualLocalBases_eigenframe_at_ramifiedPrime D cc δ hcc hδ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L L' hA p lm hpd ι hι cD hgen P P' κ hP hP' hκ
  let M : D.what₂.Tau × Fin N' × Fin N → (Bool × HH D) × Fin N × Fin N' → ℂ_[p] :=
    fun k j => κ k.1 * TaylorLogMetric.chgB D lm P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))
  have hterm := fun (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA₁ : TaylorLogMetric.admitted D N N' L₁ L₁')
      (hE : TaylorLogMetric.EqAt D p L L₁) (hE' : TaylorLogMetric.EqAt D p L' L₁') (t : TaylorLogMetric.VC D N N') (ht : TaylorLogMetric.TorsPrime D p (TaylorLogMetric.La D B.tor L L') t) =>
    GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.term_shape hIn hcc hδ B χ hχ s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat hA₁ hpd hE hE' lm ι hι hInt t ht u M
      (hfr L₁ L₁' hA₁ hE hE')
  have hb := (hterm L L' hA ⟨1, Nat.coprime_one_left p, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
    ⟨1, Nat.coprime_one_left p, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩ 0
    ⟨1, one_pos, Nat.coprime_one_left p, by simpa using AddSubgroup.zero_mem _⟩).1
  have hbound : ‖GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.jetS a₀ b₀ D.host.d ha hd lam hlam p ι‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := by
    refine GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.norm_bound ?_
    have e3 : ((D.host.d : ℕ) : ℂ_[p]) = (p : ℂ_[p]) := congrArg _ hpd.symm
    rw [e3] at hb
    exact hb
  obtain ⟨m, r, t, L₁, L₁', hr, ht, hL1, rfl⟩ := hF
  have hk := fun k => (hterm (L₁ k) (L₁' k) (hL1 k).1 (hL1 k).2.1 (hL1 k).2.2 (t k) (ht k)).2
  choose sg hsg he using hk
  refine ⟨GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.jetS a₀ b₀ D.host.d ha hd lam hlam p ι, hbound, u, hu, ∑ k, MvPowerSeries.C (r k) * sg k,
    GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.jets_prod (GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.jets_comb r sg hr hsg), ?_⟩
  rw [GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.expS_eq, ← GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.comb_exp _ r _ sg he]
  exact GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.atLin_comb M r _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ShapeNormalisedThetaCombinationsDualBasesAtDStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shape_normalisedThetaCombinations_dualBases_at_d : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), p = D.host.d → ∀ (cD : D.what₂.Tau → ℂ), IsDgen D cD → ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (κ : D.what₂.Tau → ℂ_[p]), GlobalTheory.KerStd.StdBases D lm L P → GlobalTheory.KerStd.StdBases D lm L' P' → (∀ τ, ‖κ τ‖ ≤ ‖TaylorLogMetric.lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], TaylorLogMetric.IsComb D B.tor (B.eNat χ) lm L L' F → OrbitPlaces.ShapeD D p (GlobalTheory.KerStd.stdSer D lm κ P P' F) := by
  first | exact @GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.shapeComb | exact GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.shapeComb | (intros; apply GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.shapeComb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDgenEqOne
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.EigenGenerator

theorem norm_dgen_eq_one : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (p : ℕ) [Fact p.Prime] (lm : Qbar →+* ℂ_[p]), p = D.host.d → ∀ τ, ‖lamC lm (cD τ)‖ = 1 := by
  intro D cD hD p _ lm hp τ
  obtain ⟨M, hMnf, hM, hs⟩ := hD
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have hh := D.host.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hh
  have h2 : p ∉ D.host.small := hp ▸ UpperTheory.Small.d_not_mem D.host
  have hq : p ≠ D.host.q := by omega
  rw [← hsc]
  exact norm_generator_eq_one D p lm h2 hq M hM τ s hsp

end GlobalTheory.EigenGenerator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumThetaSeriesShapeAtDAdaptedBases
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.KerShapeD

theorem thetaKernelShapeAtD_ofKer_of_hyp_adapted : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.Adapted →
    ∀ ep be sg, OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hH hA ep be sg
  intro u μ w hlev hcls i hi c c'
  have hpd : D.what₂.places.resChar w = D.host.d := by
    have h := hcls
    simp only [Host.cls, primeClass] at h
    split_ifs at h with h1 h2 h3 <;> first | exact h3 | cases h
  have hAd : AdPl D w := Or.inr (Or.inr hcls)
  have hlev' : LevFree Y u μ w := hlev
  obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hA w hAd u μ hlev'
  have hStd : ∀ j, j ≤ D.R.m → ∀ cl, GlobalTheory.KerStd.StdBases D (t.ent.lam w) ((t.O u μ).lat j cl).1 (Pm j cl) :=
    fun j hj cl => GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j cl).2.1 (fun τ => hBas j hj cl τ)
      (fun τ τ' h => hConj j hj cl τ τ' h)
  have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hH u μ w hlev' i hi c c'
  have hdg : IsDgen D t.cD := by
    rw [← t.O_dgen u μ]
    exact (t.O u μ).dgen_gen
  have hnorm : ∀ τ, ‖(fun _ => (1 : ℂ_[D.what₂.places.resChar w])) τ‖ ≤ ‖TaylorLogMetric.lamC (t.ent.lam w) (t.cD τ)‖ := by
    intro τ
    rw [GlobalTheory.EigenGenerator.norm_dgen_eq_one D t.cD hdg _ (t.ent.lam w) hpd τ]
    simp
  show OrbitPlaces.ShapeD D _ (t.ent.Th u μ w i c c')
  rw [hTh i hi c c', GlobalTheory.atLin_adCoef_eq_stdSer]
  exact GlobalTheory.T.shape_normalisedThetaCombinations_dualBases_at_d hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hcomb.1 _ (t.ent.lam w) hpd
    t.cD hdg (Pm i c) (Pm (i + 1) c') _ (hStd i hi.le c) (hStd (i + 1) hi c') hnorm _ hcomb.2

end GlobalTheory.Ggeo.KerShapeD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumThetaSeriesShapeAtDAdaptedBasesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatum_thetaSeries_shape_at_d_adaptedBases : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.Adapted → ∀ ep be sg, OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  first | exact @GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted | exact GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted | (intros; apply GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted <;> assumption)
end
