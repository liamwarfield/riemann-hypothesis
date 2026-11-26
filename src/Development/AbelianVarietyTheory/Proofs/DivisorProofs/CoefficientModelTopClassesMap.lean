module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorCharacterScaledTableStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorCharacterScaledTable
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.JetCharScale

variable {K : Type} [Field K]

def scaleVar {σ : Type} (u : σ → K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K := aeval fun v => C (u v) * X v

theorem scaleVar_monomial {σ : Type} (u : σ → K) (m : σ →₀ ℕ) (c : K) :
    scaleVar u (monomial m c) = (m.prod fun v e => u v ^ e) • monomial m c := by
  rw [scaleVar, aeval_monomial, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_prod, map_pow, algebraMap_eq]
  ring

variable {ι : Type} {a b : ℕ}

theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → K) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    jetLin J (monomial m 1) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have := (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).constr_basis K (fun m =>
    (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b)) m
  rw [coe_basisMonomials] at this
  exact this

theorem subD_scale (w : ι → K) (P : Pol K ι a) :
    scaleVar (Sum.elim (fun _ => 1) fun k => w k.1) (subD K ι a b P) =
      scaleVar (Sum.elim (fun v => w v.1) fun _ => 1) (subD K ι a b P) := by
  refine AlgHom.congr_fun (φ₁ := (scaleVar _).comp (subD K ι a b)) (φ₂ := (scaleVar _).comp (subD K ι a b))
    (MvPolynomial.algHom_ext fun v => ?_) P
  simp only [AlgHom.comp_apply, subD, aeval_X]
  split_ifs with h
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, scaleVar, aeval_X, Sum.elim_inl, Sum.elim_inr, map_one]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  · simp

variable [Fintype ι]

theorem jetLin_right (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K) (c : K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) Q =
      c • jetLin J (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1) Q) := by
  refine LinearMap.congr_fun (g := c • (jetLin J ∘ₗ (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1)).toLinearMap))
    ((basisMonomials _ K).ext fun m => ?_) Q
  rw [coe_basisMonomials]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [scaleVar_monomial, map_smul, jetLin_monomial, jetLin_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp

theorem jetLin_left (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J (scaleVar (Sum.elim (fun v => w v.1) fun _ => 1) Q) = scaleVar (fun v => w v.1) (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial m c =>
    have e : (monomial m c : MvPolynomial _ K) = c • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul, map_smul, map_smul, scaleVar_monomial, map_smul, jetLin_monomial, scaleVar_monomial,
      Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    simp

theorem jetMap_scale (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K) (c : K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n P = c • scaleVar (fun v => w v.1) (jetMap J n P) := by
  simp only [jetMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [jetLin_right, subD_scale, jetLin_left]

theorem scaleVar_hom [DecidableEq ι] (w : ι → K) (d : ι → ℕ) {Q : Pol K ι b}
    (hQ : ∀ τ, IsWeightedHomogeneous (GlobalTheory.JetDeg.posW b τ) Q (d τ)) :
    scaleVar (fun v => w v.1) Q = (∏ τ, w τ ^ d τ) • Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [scaleVar_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h := hQ τ (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_eq_single τ] at h
  · rw [← h]
    simp [GlobalTheory.JetDeg.posW, Finset.prod_pow_eq_pow_sum]
  · intro x _ hx
    simp [GlobalTheory.JetDeg.posW, hx]
  · simp

theorem jetOp_scale : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) (w : ι → ℂ) (c : ℂ), Formalism.L2.Ker.JetInVV ℂ lam lam' n →
    Formalism.L2.Ker.jetOp lam lam' (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n =
      (c * ∏ τ, w τ ^ (∑ i, (lam' τ).natW i)) • Formalism.L2.Ker.jetOp lam lam' J n := by
  classical
  intro ι _ a b lam lam' n J w c hV
  refine LinearMap.ext fun P => ?_
  simp only [jetOp, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [jetMap_scale, scaleVar_hom w _ fun τ => GlobalTheory.JetDeg.VV_hom lam' τ (hV J P P.2), smul_smul, map_smul]

end GlobalTheory.JetCharScale

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetOperator_characterScaledTable : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) (w : ι → ℂ) (c : ℂ), Formalism.L2.Ker.JetInVV ℂ lam lam' n →
    Formalism.L2.Ker.jetOp lam lam' (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n =
      (c * ∏ τ, w τ ^ (∑ i, (lam' τ).natW i)) • Formalism.L2.Ker.jetOp lam lam' J n := by
  first | exact @GlobalTheory.JetCharScale.jetOp_scale | exact GlobalTheory.JetCharScale.jetOp_scale | (intros; apply GlobalTheory.JetCharScale.jetOp_scale <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCombinationJetsAlgebraicConjEqConjSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCombinationJetsAlgebraicConjEqConjSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
open GlobalTheory.ThetaConj

namespace GlobalTheory.ConjJetComb

theorem applyAt0_mono (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = ((α.prod fun _ n => n.factorial : ℕ) : ℂ) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]
  simp [Finsupp.prod]

theorem jet_of_cjF {D : D7} {N N' : ℕ} {ρ : Qbar →ₐ[ℚ] ℂ} {F F' : VC D N N' → ℂ} (h : CjF D Qbar ρ F F')
    (α : Mono D N N') :
    GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) F ∈ Qbar ∧
      Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ (GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) F) =
        GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) (fnConj D Qbar ρ F) := by
  rw [h.fnConj_eq, applyAt0_mono, applyAt0_mono]
  set n : ℕ := α.prod fun _ n => n.factorial
  have hn : (n : ℂ) ∈ Qbar := natCast_mem _ n
  refine ⟨mul_mem hn (h.2.2 α).1, ?_⟩
  rw [cj_mul ρ hn (h.2.2 α).1, (h.2.2 α).2, cj_mem ρ hn]
  have : (⟨(n : ℂ), hn⟩ : Qbar) = (n : Qbar) := rfl
  rw [this, map_natCast]

theorem conj_jet : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (a b : ℕ), Even (a * b) → ∀ (e0 : VC D a b → ℂ), oddE0 D D.host.ccK δ t0 a b e0 →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
    ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ), 0 < k → ∀ (r : Fin n → Qbar) (s : Fin n → VC D a b),
    (∀ i, k • s i ∈ La D (tor0 D D.host.ccK δ) Ls Lt) → ∀ (ρ' : Qbar →ₐ[ℚ] ℂ) (m : Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ),
      GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
              (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) ∈ Qbar ∧
      Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
                (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z)) =
        GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
          (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) := by
  intro D _ δ t0 hc ht0 N N' _ e0 he Ls Lt hL₁ hL₁' κ hκ k₀ n hk₀ r s hs ρ m
  have hG := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  have hL := GlobalTheory.MovedVacuum.sd_stdL D N
  have hL' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have hGth := he.1
  obtain ⟨b, κ₀, hb, hκ₀, rfl⟩ := he.2.2.2.1
  obtain ⟨k, hk, hC⟩ := GlobalTheory.T.exists_homLattice_commensurable_orthonormal D N N' _ b _ _ hb hL hL'
  have kB : KLat D (tor0 D D.host.ccK δ) (LaB D (tor0 D D.host.ccK δ) b) := Or.inl ⟨_, b, hb, rfl⟩
  have kL : KLat D (tor0 D D.host.ccK δ) (La D (tor0 D D.host.ccK δ) _ _) := Or.inr ⟨_, _, hL, hL', rfl⟩
  obtain ⟨-, -, c1, c2, -⟩ := GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG D.host.ccK δ N N' _ b hb
  obtain ⟨d1, d2⟩ := GlobalTheory.T.halfPeriodTheta_differentiable_and_signedTranslate_invariant D hG D.host.ccK δ hc t0 ht0
  have hth0 := GlobalTheory.T.orthoProductTheta_mem_thetaSpace_of_lattice D (tor0 D D.host.ccK δ) N N' _ b _ c1 c2 d1 d2
  have hCb : Comm D b k (Set.range b) := by simpa using (comm_range D b).mul k
  obtain ⟨m1, -⟩ := conj_iop hc ρ hb (GlobalTheory.T.pullB_th0_mem_tr D _ δ hc t0 ht0 N N' _ b hb) hk
    hCb hC (LaB_eq D _ b ▸ kB) kL (LaB_eq D _ b ▸ hth0)
  rw [← LaB_eq, ← La_eq] at m1
  have hGm := Submodule.smul_mem _ (⟨κ₀, hκ₀.1⟩ : Qbar) m1
  obtain ⟨k₁, hk₁, hC₁⟩ := GlobalTheory.T.exists_homLattice_commensurable_orthonormal D N N' _ b Ls Lt hb hL₁ hL₁'
  have hC₂ := hC₁.mul k
  rw [mul_comm k k₁] at hC₂
  obtain ⟨m2, -⟩ := conj_iop hc ρ hb hGm (Nat.mul_pos hk₁ hk) (hC.mul k₁) hC₂ kL
      (Or.inr ⟨Ls, Lt, hL₁, hL₁', rfl⟩) hGth
  have hsB : ∀ i, (k₀ * k₁) • s i ∈ LaB D (tor0 D D.host.ccK δ) b := fun i => by
    rw [mul_nsmul]
    exact nsmul_mem_LaB (isTraceCompatibleTorusEmbedding_standardTorus D hG _ δ) (GlobalTheory.T.idealPeriodLattice_of_curveDatum D hG _ δ hc).2.2.2.2 hC₁ (hs i)
  have m3 := fun i => GlobalTheory.T.torsionTranslate_mem_thetaPullbackSpan D _ δ hc N N' _ b hb _ m2 (s i) _ (Nat.mul_pos hk₀ hk₁) (hsB i)
  choose F' hF' using fun i => galRel_all hc ρ hb (m3 i) one_pos
  exact jet_of_cjF ((CjF.sum Finset.univ fun i _ => (hF' i).1.mul (r i).2).mul hκ.1) m

end GlobalTheory.ConjJetComb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCombinationJetsAlgebraicConjEqConjSeriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCombinationJets_algebraic_conj_eq_conjSeries : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (a b : ℕ), Even (a * b) → ∀ (e0 : VC D a b → ℂ), oddE0 D D.host.ccK δ t0 a b e0 →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
    ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ), 0 < k → ∀ (r : Fin n → Qbar) (s : Fin n → VC D a b),
    (∀ i, k • s i ∈ La D (tor0 D D.host.ccK δ) Ls Lt) → ∀ (ρ' : Qbar →ₐ[ℚ] ℂ) (m : Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ),
      GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
              (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) ∈ Qbar ∧
      Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
                (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z)) =
        GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
          (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) := by
  first | exact @GlobalTheory.ConjJetComb.conj_jet | exact GlobalTheory.ConjJetComb.conj_jet | (intros; apply GlobalTheory.ConjJetComb.conj_jet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorRationalFormConjEqConjTable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorRationalFormConjEqConjTable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.JetDescent

theorem coe_lift_of_mem (M : IntermediateField ℚ ℂ) (x : ℂ) (hx : x ∈ M) : Formalism.MainNotions.TaylorLogMetric.liftM M x = ⟨x, hx⟩ := by
  unfold Formalism.MainNotions.TaylorLogMetric.liftM
  exact dif_pos hx

theorem mapVV_rational_form_conj : ∀ {D : D7} {a b : ℕ} (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b) (n : D.what₂.Tau → ℕ)
    (J : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (σ : D.what₂.LL →+* ℂ) (ρ' : Qbar →ₐ[ℚ] ℂ)
    (f : VV D.what₂.LL lam →ₗ[D.what₂.LL] VV D.what₂.LL lam'), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ m, J m ∈ Qbar) →
    (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) →
    (∀ u, Formalism.L2.Ker.jetOp lam lam' J n (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam' (f u)) →
    ∀ u, GlobalTheory.CoefModel.mapVV σ lam' (f u) =
      Formalism.L2.Ker.jetOp lam lam' (fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m)) n (GlobalTheory.CoefModel.mapVV σ lam u) := by
  intro D a b lam lam' n J σ ρ' f hV hJ hσ hf u
  have halg : ∀ x : D.what₂.LL, D.what₂.embLL x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.what₂.embLL.toRatAlgHom
  let e : D.what₂.LL →+* Qbar := D.what₂.embLL.codRestrict Qbar halg
  let i : Qbar →+* ℂ := algebraMap Qbar ℂ
  let r : Qbar →+* ℂ := ρ'
  let Jq : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → Qbar := fun m => ⟨J m, hJ m⟩
  have hie : i.comp e = D.what₂.embLL := RingHom.ext fun _ => rfl
  have hre : r.comp e = σ := RingHom.ext fun x => by
    rw [← hσ x]
    unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [coe_lift_of_mem _ _ (halg x)]
    rfl
  have hJi : (fun m => i (Jq m)) = J := funext fun _ => rfl
  have hJr : (fun m => r (Jq m)) = fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m) := funext fun m => by
    unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [coe_lift_of_mem _ _ (hJ m)]
    rfl
  have h1 : Formalism.L2.Ker.jetMap J n (MvPolynomial.map D.what₂.embLL u.1) = MvPolynomial.map D.what₂.embLL (f u).1 := by
    have h := congrArg Subtype.val (hf u)
    rw [Formalism.L2.Ker.jetOp_coe lam lam' n hV] at h
    exact h
  have h2 : Formalism.L2.Ker.jetMap Jq n (MvPolynomial.map e u.1) = MvPolynomial.map e (f u).1 := by
    apply MvPolynomial.map_injective i i.injective
    rw [Formalism.L2.Ker.map_jetMap, MvPolynomial.map_map, MvPolynomial.map_map, hie, hJi]
    exact h1
  have h3 := congrArg (MvPolynomial.map r) h2
  rw [Formalism.L2.Ker.map_jetMap, MvPolynomial.map_map, MvPolynomial.map_map, hre, hJr] at h3
  apply Subtype.ext
  rw [Formalism.L2.Ker.jetOp_coe lam lam' n hV]
  exact h3.symm

end GlobalTheory.JetDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorRationalFormConjEqConjTableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetOperator_rationalForm_conj_eq_conjTable : ∀ {D : D7} {a b : ℕ} (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b) (n : D.what₂.Tau → ℕ)
    (J : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (σ : D.what₂.LL →+* ℂ) (ρ' : Qbar →ₐ[ℚ] ℂ)
    (f : VV D.what₂.LL lam →ₗ[D.what₂.LL] VV D.what₂.LL lam'), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ m, J m ∈ Qbar) →
    (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) →
    (∀ u, Formalism.L2.Ker.jetOp lam lam' J n (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam' (f u)) →
    ∀ u, GlobalTheory.CoefModel.mapVV σ lam' (f u) =
      Formalism.L2.Ker.jetOp lam lam' (fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m)) n (GlobalTheory.CoefModel.mapVV σ lam u) := by
  first | exact @GlobalTheory.JetDescent.mapVV_rational_form_conj | exact GlobalTheory.JetDescent.mapVV_rational_form_conj | (intros; apply GlobalTheory.JetDescent.mapVV_rational_form_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicNumbersExtensionCurveFieldConjLat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicNumbersExtensionCurveFieldConjLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.ConjExtend

theorem exists_extension_of_le (M : IntermediateField ℚ ℂ) (hle : M ≤ Qbar) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x ∈ M, ρ' (TaylorLogMetric.liftM Qbar x) = ρ (TaylorLogMetric.liftM M x) := by
  let _ : Algebra M Qbar := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower ℚ M Qbar := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic M Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) M
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := M) (M := ℂ)
    (E := Qbar) ρ
  refine ⟨φ, fun x hx => ?_⟩
  rw [← hφ]
  unfold TaylorLogMetric.liftM
  rw [dite_eq_left hx, dite_eq_left (hle hx)]
  rfl

theorem fld_le (D : D7) (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) (hc : Crv D D.host.ccK δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0) : GlobalTheory.KerConjMean.fld D δ t0 ≤ Qbar := by
  obtain ⟨hdata, htor⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  unfold GlobalTheory.KerConjMean.fld
  rw [IntermediateField.adjoin_le_iff]
  rintro y (⟨x, rfl⟩ | rfl | rfl | rfl)
  · exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.what₂.embLL.toRatAlgHom)
  · exact hdata.2.1
  · exact hdata.2.2
  · exact hwp

theorem exists_extension_conj : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ GlobalTheory.KerConjMean.ext D δ t0 σ, ∃ ρ' : Qbar →ₐ[ℚ] ℂ,
      (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) ∧
      lamConj Qbar ρ' (lamOf D D.host.ccK δ) = lamConj (GlobalTheory.KerConjMean.fld D δ t0) ρ (GlobalTheory.KerConjMean.lat D δ) := by
  intro D hI δ t0 hc ht σ ρ hρ
  obtain ⟨ρ', h⟩ := exists_extension_of_le _ (fld_le D hI δ t0 hc ht) ρ
  refine ⟨ρ', fun x => ?_, ?_⟩
  · unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [h _ (GlobalTheory.KerConjMean.embLL_mem D δ t0 x), ← hρ x]
    unfold TaylorLogMetric.liftM
    rw [dite_eq_left (GlobalTheory.KerConjMean.embLL_mem D δ t0 x)]
  · have h2 : g2 (lamOf D D.host.ccK δ) ∈ GlobalTheory.KerConjMean.fld D δ t0 :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
    have h3 : g3 (lamOf D D.host.ccK δ) ∈ GlobalTheory.KerConjMean.fld D δ t0 :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
    unfold lamConj
    rw [h _ h2, h _ h3]

end GlobalTheory.ConjExtend
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicNumbersExtensionCurveFieldConjLatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicNumbers_extension_curveField_conjLattice : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ GlobalTheory.KerConjMean.ext D δ t0 σ, ∃ ρ' : Qbar →ₐ[ℚ] ℂ,
      (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) ∧
      lamConj Qbar ρ' (lamOf D D.host.ccK δ) = lamConj (GlobalTheory.KerConjMean.fld D δ t0) ρ (GlobalTheory.KerConjMean.lat D δ) := by
  first | exact @GlobalTheory.ConjExtend.exists_extension_conj | exact GlobalTheory.ConjExtend.exists_extension_conj | (intros; apply GlobalTheory.ConjExtend.exists_extension_conj <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerConjTransport

theorem kkMap_top_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    {N : Std G U} (Z : Normal W N) (t : T) (j : ℕ) (d : FinDatum G t (.top t j)) (x : FinPt G (Pair.top t j).small)
    (y : FinPt G (Pair.top t j).big) (Hf : VC D (G.pS (Pair.top t j)).rank (G.pT (Pair.top t j)).rank → ℂ)
    (hJ : Formalism.L2.Ker.JetInVV ℂ (wt G (Pair.top t j).small) (wt G (Pair.top t j).big) (nuEnd G (.top t j)))
    (hper : ∀ τ : D.what₂.Tau, period Z.δ τ ≠ 0)
    (hjet : ∀ mon, jetTab W N.frC (.top t j) (Z.vec d) (x * N.u _) (y * N.u _) mon = Z.c0 (.top t j) * opp (.top t j : Pair T)
       (((mon.mapDomain (fvar G (.top t j))).prod fun v e => period Z.δ v.1 ^ e) *
         GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar G (.top t j))) 1) Hf)) :
    Z.kkMap 1 d x y = Formalism.L2.Ker.jetOp (wt G (Pair.top t j).small) (wt G (Pair.top t j).big)
      (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) Hf) (nuEnd G (.top t j)) := by
  have e1 : jetTab W N.frC (.top t j) (Z.vec d) (x * N.u _) (y * N.u _) = fun mon => (Z.c0 (.top t j) : ℂ) *
      ((mon.prod fun v e => period Z.δ v.1 ^ e) * GL3Theta.applyAt0 D (MvPolynomial.monomial mon 1) Hf) := by
    funext mon
    rw [hjet mon, show fvar G (Pair.top t j) = id from rfl, Finsupp.mapDomain_id]
    rfl
  unfold Normal.kkMap fockComp
  rw [e1, GlobalTheory.T.jetOperator_characterScaledTable _ _ _ _ _ _ hJ, smul_smul]
  have hs : Z.scal 1 (Pair.top t j) * ((Z.c0 (Pair.top t j) : ℂ) *
      ∏ τ, period Z.δ τ ^ ∑ i, (wt G (Pair.top t j).big τ).natW i) = 1 := by
    unfold Normal.scal GlobalTheory.FunObj.fockDeg
    simp only [opp, RingHom.id_apply, Pi.one_apply, one_div]
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
    simp only [← mul_pow, inv_mul_cancel₀ (hper _), one_pow, Finset.prod_const_one, mul_one]
    simp
  rw [hs, one_smul]

end GlobalTheory.KerConjTransport

end
