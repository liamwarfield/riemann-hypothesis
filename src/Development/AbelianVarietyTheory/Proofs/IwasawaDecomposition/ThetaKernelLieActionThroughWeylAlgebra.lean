module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
public import Lean

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.Lift.WeylAction

open GlobalTheory.RealWeil

section Mat

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

omit [Fintype O] in
theorem blk_apply (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) (k l : (Fin m × Fin n) × O) :
    blk b a k l = if k.2 = l.2 then b k.2 k.1.1 l.1.1 * a k.2 l.1.2 k.1.2 else 0 := rfl

theorem sum_blk {A : Type} [AddCommGroup A] [Module ℂ A] (b : O → Matrix (Fin m) (Fin m) ℂ)
    (a : O → Matrix (Fin n) (Fin n) ℂ) (τ : O) (h : ∀ τ', τ' ≠ τ → b τ' = 0 ∨ a τ' = 0)
    (y : (Fin m × Fin n) × O → (Fin m × Fin n) × O → A) :
    ∑ k, ∑ l, blk b a k l • y k l =
      ∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n, (b τ p.1 q.1 * a τ q.2 p.2) • y (p, τ) (q, τ) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single τ _ (by simp)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [blk_apply, ite_smul]
  · intro τ' _ hτ
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases h τ' hτ with e | e <;> simp [blk_apply, e]

theorem sum_left {A : Type} [AddCommGroup A] [Module ℂ A] (X : Matrix (Fin m) (Fin m) ℂ) (τ : O)
    (y : (Fin m × Fin n) × O → (Fin m × Fin n) × O → A) :
    ∑ k, ∑ l, blk (Pi.single τ X) (fun _ => 1) k l • y k l =
      ∑ i, ∑ j, X i j • ∑ a, y ((i, a), τ) ((j, a), τ) := by
  rw [sum_blk _ _ τ fun τ' h => Or.inl (Pi.single_eq_of_ne h _)]
  simp only [Fintype.sum_prod_type, Pi.single_eq_same, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem sum_right {A : Type} [AddCommGroup A] [Module ℂ A] (Y : Matrix (Fin n) (Fin n) ℂ) (τ : O)
    (y : (Fin m × Fin n) × O → (Fin m × Fin n) × O → A) :
    ∑ k, ∑ l, blk (fun _ => 1) (Pi.single τ (-Y)) k l • y k l =
      ∑ a, ∑ b, Y a b • -∑ i, y ((i, b), τ) ((i, a), τ) := by
  rw [sum_blk _ _ τ fun τ' h => Or.inr (Pi.single_eq_of_ne h _)]
  have e : ∀ (i : Fin m) (b : Fin n), ∑ q : Fin m × Fin n, ((1 : Matrix (Fin m) (Fin m) ℂ) i q.1 * (-Y) q.2 b) •
      y ((i, b), τ) (q, τ) = ∑ a, -(Y a b • y ((i, b), τ) ((i, a), τ)) := by
    intro i b
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp [Matrix.one_apply, ite_smul]
  simp only [Pi.single_eq_same]
  rw [Fintype.sum_prod_type]
  simp only [e, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans Finset.sum_comm

end Mat

variable {D : D7} {θ : InfF D}

theorem hasDerivAt_comp (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (τ' : D.what₂.Tau) (i j : Fin V.rank) :
    HasDerivAt (fun t : ℝ => compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ X t)) i j)
      ((Pi.single τ X : D.what₂.Tau → _) τ' i j) 0 := by
  by_cases h : τ' = τ
  · subst h
    have e : ∀ t : ℝ, compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ' X t)) = NormedSpace.exp (t • X) :=
      fun t => (isAtTau_oneP hθ hX t).2.1
    have := hasDerivAt_exp_entry X 0 i j
    rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at this
    simpa only [e, Pi.single_eq_same] using this
  · have e : ∀ t : ℝ, compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ X t)) = 1 :=
      fun t => (isAtTau_oneP hθ hX t).2.2 τ' h
    simp only [e, Pi.single_eq_of_ne h]
    exact hasDerivAt_const _ _

theorem oneP_inv (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : (oneP θ V τ X t)⁻¹ = oneP θ V τ (-X) t := by
  have : oneP θ V τ (-X) t = oneP θ V τ X (-t) := by
    unfold oneP
    rw [smul_neg, neg_smul]
  rw [this]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← oneP_add hθ hX, add_neg_cancel, oneP_zero hθ]

theorem neg_mem_lieAt {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : -X ∈ lieAt V τ := by
  have h : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  show (-X)ᴴ * gramAt D V τ + gramAt D V τ * (-X) = 0
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]

theorem weyl_action : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ x d : D.what₂.Tau → Fin T.rank × Fin S.rank → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), ∀ τ, IsCCR (x τ) (d τ) ∧ (∀ X ∈ lieAt T τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om ((∑ i, ∑ j, X i j • ∑ a, x τ (i, a) * d τ (j, a)) f + lam • f) g h) 0) ∧ ∀ Y ∈ lieAt S τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ Y t) h) (thKer ψ S T om ((∑ a, ∑ b, Y a b • -∑ i, x τ (i, b) * d τ (i, a)) f + lam • f) g h) 0 := by
  intro D ψ hψ S T om hw hc θ hθ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨x, d, ⟨c1, c2, c3⟩, hn⟩ := GlobalTheory.T.exists_ccr_operators_thetaFunctions D θ σ h ψ hψ S T
  have key : ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) →
      (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (Ix S T) (Ix S T) ℂ,
      (∀ k l, HasDerivAt (fun t => mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ (f : thetaSub ψ S T) p,
      HasDerivAt (fun t => om (p * γ t) f.1 0) (om p ((∑ k, ∑ l, X k l • (x k * d l)) f + lam • f).1 0) 0 := by
    intro γ h1 h2 h3 X h4
    obtain ⟨lam, hl⟩ := GlobalTheory.T.hasDerivAt_weilRep_realOneParam_adelicPoint D θ σ h ψ hψ S T om hw hc γ h1 h2 h3 X h4
    refine ⟨lam, fun f p => ?_⟩
    have e := coe_toB hψ f.1 f.2
    have h5 := hl (toB hψ f.1 f.2) (e.symm ▸ f.2) p 0
    have e2 : ((∑ k, ∑ l, X k l • (x k * d l)) f + lam • f).1 =
        ((nOp (rhoV hψ σ S T) (HM S T) X (toB hψ f.1 f.2) + lam • toB hψ f.1 f.2).1 : WO S T → ℂ) := by
      rw [Submodule.coe_add, hn X f _ e]
      rfl
    rw [e2]
    exact h5
  refine ⟨fun τ k => x (k, τ), fun τ k => d (k, τ), fun τ => ⟨⟨fun k l => c1 _ _, fun k l => c2 _ _, fun k l => ?_⟩,
    fun X hX => ?_, fun Y hY => ?_⟩⟩
  · rw [c3]
    simp
  · obtain ⟨lam, hl⟩ := key (fun t => (1, oneP θ T τ X t)) (continuous_const.prodMk (continuous_oneP hθ hX))
      (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨one_mem _, (isAtTau_oneP hθ hX t).1⟩) (blk (Pi.single τ X) fun _ => 1) (fun k l => by
        simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, blk_apply]
        split_ifs
        · exact (hasDerivAt_comp hθ hX _ _ _).mul_const _
        · exact hasDerivAt_const _ _)
    refine ⟨lam, fun f g k => ?_⟩
    have := hl f (g, k)
    rw [sum_left X τ fun k l => x k * d l] at this
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this
  · obtain ⟨lam, hl⟩ := key (fun t => (oneP θ S τ Y t, 1)) ((continuous_oneP hθ hY).prodMk continuous_const)
      (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨(isAtTau_oneP hθ hY t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-Y))) (fun k l => by
        simp only [mM_apply, oneP_inv hθ hY, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, blk_apply]
        split_ifs
        · exact (hasDerivAt_comp hθ (neg_mem_lieAt hY) _ _ _).const_mul _
        · exact hasDerivAt_const _ _)
    refine ⟨lam, fun f g k => ?_⟩
    have := hl f (g, k)
    rw [sum_right Y τ fun k l => x k * d l] at this
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this

end GlobalTheory.Mem.Lift.WeylAction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebraStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_lieAction_through_weylAlgebra : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ x d : D.what₂.Tau → Fin T.rank × Fin S.rank → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), ∀ τ, IsCCR (x τ) (d τ) ∧ (∀ X ∈ lieAt T τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om ((∑ i, ∑ j, X i j • ∑ a, x τ (i, a) * d τ (j, a)) f + lam • f) g h) 0) ∧ ∀ Y ∈ lieAt S τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ Y t) h) (thKer ψ S T om ((∑ a, ∑ b, Y a b • -∑ i, x τ (i, b) * d τ (i, a)) f + lam • f) g h) 0 := by
  first | exact @GlobalTheory.Mem.Lift.WeylAction.weyl_action | exact GlobalTheory.Mem.Lift.WeylAction.weyl_action | (intros; apply GlobalTheory.Mem.Lift.WeylAction.weyl_action <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TypePrimes

theorem nonempty_equiv_zmod (k : Type) [Ring k] {p : ℕ} (hp : p.Prime) (h : Nat.card k = p) : Nonempty (ZMod p ≃+* k) := by
  have : Finite k := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)
  have := Fintype.ofFinite k
  exact ⟨ZMod.ringEquivOfPrime k hp (by rw [← Nat.card_eq_fintype_card, h])⟩

noncomputable def transport {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (χ : MulChar k' ℂ) : MulChar k ℂ where
  toMonoidHom := χ.toMonoidHom.comp (e : k →* k')
  map_nonunit' a ha := χ.map_nonunit fun h => ha (by simpa using h.map e.symm)

theorem transport_apply {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (χ : MulChar k' ℂ) (a : k) :
    transport e χ a = χ (e a) := rfl

theorem orderOf_ofUnitHom {p : ℕ} (hp : p.Prime) (om : (ZMod p)ˣ →* ℂˣ) (h : Function.Injective om) :
    orderOf (MulChar.ofUnitHom om) = p - 1 := by
  have := Fact.mk hp
  have key : ∀ n : ℕ, MulChar.ofUnitHom om ^ n = 1 ↔ p - 1 ∣ n := by
    intro n
    rw [← ZMod.card_units p, ← Nat.card_eq_fintype_card, ← IsCyclic.exponent_eq_card,
      Monoid.exponent_dvd_iff_forall_pow_eq_one, MulChar.ext_iff]
    refine forall_congr' fun a => ?_
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, MulChar.ofUnitHom_coe, ← Units.val_pow_eq_pow_val, Units.val_eq_one,
      ← map_pow, map_eq_one_iff om h]
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((key _).2 dvd_rfl)) ((key _).1 (pow_orderOf_eq_one _))

section Orient

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem exists_oriented (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) (p : ℕ) (hv : (p : 𝓞 F) ∈ v.asIdeal)
    (hx : x * σ x = (p : E)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (h1 : ∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x))
    (h2 : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F,
      (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) ∧ (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
      Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 < 1 := by
  by_cases h : Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 < 1
  · exact ⟨sp, h1, h2, h⟩
  refine ⟨sp.trans RingEquiv.prodComm, fun y => ?_, fun a => ?_, ?_⟩
  · rw [RingEquiv.trans_apply, h1]; rfl
  · rw [RingEquiv.trans_apply, h2]; rfl
  have e1 : (sp (inclE (F := F) (v.adicCompletion F) (σ x))).2 = (sp (inclE (F := F) (v.adicCompletion F) x)).1 :=
    congrArg Prod.snd (h1 (inclE (F := F) (v.adicCompletion F) x))
  have e2 : (sp (inclE (F := F) (v.adicCompletion F) x)).1 * (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 =
      (p : v.adicCompletion F) := by
    rw [← Prod.fst_mul, ← map_mul, ← map_mul, hx, map_natCast, map_natCast, Prod.fst_natCast]
  have e3 : Valued.v (p : v.adicCompletion F) < 1 := by
    have : (p : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
    rw [this, Examples₂.adicCompl_val_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v _).2 hv
  show Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).2 < 1
  rw [e1]
  by_contra h'
  rw [← e2, map_mul] at e3
  exact absurd e3 (not_lt.2 (one_le_mul (not_lt.1 h') (not_lt.1 h)))

end Orient

section Generic

variable {X : Fields} {Pr : Primes X} {m : ℕ}

theorem g_mem_of_vG (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
  rw [← hPr.vG_norm i w hw]
  exact Ideal.absNorm_mem _

theorem mem_vG_of_g_mem (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs)
    (h : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal) : w ∈ Pr.vG i := by
  classical
  have h1 : ∃ j, w ∈ Pr.vG j := by
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h0 | h0 <;> exact ⟨_, h0⟩
  obtain ⟨j, hj⟩ := h1
  by_cases e : j = i
  · exact e ▸ hj
  exfalso
  have hne : Pr.g j ≠ Pr.g i := by
    have := hPr.g_ne
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hc : IsCoprime ((Pr.g j : ℕ) : 𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (hPr.g_prime j) (hPr.g_prime i)).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact add_mem (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr hj)) (Ideal.mul_mem_left _ _ h)

theorem mem_vGs {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) : w ∈ Pr.vGs := by
  classical
  unfold Primes.vGs
  fin_cases i
  · exact Finset.mem_union.2 (Or.inl hw)
  · exact Finset.mem_union.2 (Or.inr hw)

theorem exists_gLoc (Ch : Chars X Pr m) (hf : 0 < X.f) (hPr : Pr.Ok) (hCh : Ch.Ok) (cm : CMData X.F X.E) (σ₀ : X.K →+* ℂ)
    (hs : ∀ i, GlobalTheory.St.G.SplitsIn X.E (Pr.g i)) :
    ∃ G : GLoc X.F X.E cm.sig Pr.g, G.piG = Pr.piG ∧
      (∀ j v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ n : ℕ,
        G.psi0 j v h (n : kv X.F v) = σ₀ (Ch.psi0 w (n : 𝓞 X.E ⧸ w.1.asIdeal))) ∧
      (∀ j v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ (s : Fin m) (n : ℕ)
        (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (c : 𝓞 X.E ⧸ w.1.asIdeal) = n →
        G.chiB j v h s.1 (n : kv X.F v) = σ₀ ((Ch.chi s w c : X.Kˣ) : X.K)) ∧ CharacterCompatible G m := by
  classical
  have hnorm : ∀ i, (Pr.piG i : X.E) * cm.sig (Pr.piG i : X.E) = (Pr.g i : X.E) := fun i => by
    have := congrArg (algebraMap (𝓞 X.E) X.E) (hPr.piG_norm i)
    simp only [map_mul, map_natCast] at this
    exact this
  have hsp := fun i => (GlobalTheory.St.G.SplitPrime.split_place X.F X.E cm (Pr.g i) (hPr.g_prime i) (hs i)).2
  have hor := fun i v h => exists_oriented cm.sig v (Pr.piG i : X.E) (Pr.g i) h (hnorm i) _ (hsp i v h).2.2.choose_spec.1
    (hsp i v h).2.2.choose_spec.2
  choose sp sp1 sp2 sp3 using hor
  have ev := fun i v h => (nonempty_equiv_zmod (kv X.F v) (hPr.g_prime i) (hsp i v h).1).some
  have hw0 : ∀ i, ∃ w, w ∈ Pr.vG i := fun i => Finset.card_pos.1 (by rw [hPr.vG_card i]; exact hf)
  choose w0 hw0 using hw0
  have ew := fun i w (hw : w ∈ Pr.vG i) => (nonempty_equiv_zmod (𝓞 X.E ⧸ w.asIdeal) (hPr.g_prime i) (by
    rw [← hPr.vG_norm i w hw, Ideal.absNorm_apply, Submodule.cardQuot_apply])).some
  choose om omi hom using hCh.chi_om
  let om' : ∀ i, MulChar (ZMod (Pr.g i)) ℂ := fun i => MulChar.ofUnitHom ((Units.map (σ₀ : X.K →* ℂ)).comp (om i))
  have hin : ∀ {j v} (h : ((Pr.g j : ℕ) : 𝓞 X.F) ∈ v.asIdeal) (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → w.1 ∈ Pr.vG j := by
    rintro j v h w rfl
    refine mem_vG_of_g_mem hPr w.2 ?_
    have h' : algebraMap (𝓞 X.F) (𝓞 X.E) (Pr.g j : ℕ) ∈ w.1.asIdeal := h
    rwa [map_natCast] at h'

  have hval : ∀ j (w : {w // w ∈ Pr.vGs}) (hw : w.1 ∈ Pr.vG j) (s : Fin m) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ),
      (om' j ^ (2 * (s.1 + 1))) ((ew j w.1 hw).symm c) = σ₀ ((Ch.chi s w c : X.Kˣ) : X.K) := by
    intro j w hw s c
    have := Fact.mk (hPr.g_prime j)
    let a : (ZMod (Pr.g j))ˣ := Units.map ((ew j w.1 hw).symm : _ →* _) c
    have ha : (ew j w.1 hw).symm c = (a : ZMod (Pr.g j)) := rfl
    have hc : (c : 𝓞 X.E ⧸ w.1.asIdeal) = (((a : ZMod (Pr.g j)).val : ℕ) : 𝓞 X.E ⧸ w.1.asIdeal) := by
      rw [← map_natCast (ew j w.1 hw), ZMod.natCast_zmod_val, ← ha, RingEquiv.apply_symm_apply]
    rw [hom j w hw s a c hc, ha, MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, Units.val_pow_eq_pow_val, map_pow]
    rfl
  refine ⟨{ sp := sp, sp_sig := sp1, sp_alg := sp2, piG := Pr.piG, piG_norm := hnorm, sp_pi := sp3
            psi0 := fun i v h => ((σ₀ : X.K →* ℂ).compAddChar (Ch.psi0 ⟨w0 i, mem_vGs (hw0 i)⟩)).compAddMonoidHom
              (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).toRingHom.toAddMonoidHom)
            psi_zero_nontrivial_character := ?_
            chiB := fun i v h a => transport (ev i v h).symm (om' i ^ (2 * (a + 1))) }, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v h h1
    apply hCh.psi_zero_nontrivial_character ⟨w0 i, mem_vGs (hw0 i)⟩
    ext x
    have h2 := DFunLike.congr_fun h1 (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).symm x)
    have h3 : σ₀ (Ch.psi0 ⟨w0 i, mem_vGs (hw0 i)⟩ (((ev i v h).symm.trans (ew i (w0 i) (hw0 i)))
      (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).symm x))) = 1 := h2
    rw [RingEquiv.apply_symm_apply, map_eq_one_iff σ₀ σ₀.injective] at h3
    exact h3
  · intro j v h w hw n
    show σ₀ (Ch.psi0 ⟨w0 j, mem_vGs (hw0 j)⟩ (((ev j v h).symm.trans (ew j (w0 j) (hw0 j))) (n : kv X.F v))) = _
    rw [map_natCast]
    have := hCh.characterAgreesOnPlaces j ⟨w0 j, mem_vGs (hw0 j)⟩ w (hw0 j) (hin h w hw) (n : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at this
    rw [this]
  · intro j v h w hw s n c hc
    show transport (ev j v h).symm (om' j ^ (2 * (s.1 + 1))) (n : kv X.F v) = _
    rw [transport_apply, map_natCast, ← hval j w (hin h w hw) s c, hc,
      map_natCast (ew j w.1 (hin h w hw)).symm]
  · intro i v h a b ha hb hab
    have h1 : om' i ^ (2 * (a + 1)) = om' i ^ (2 * (b + 1)) := by
      refine MulChar.ext' fun x => ?_
      have h2 : transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (ev i v h x) =
        transport (ev i v h).symm (om' i ^ (2 * (b + 1))) (ev i v h x) := DFunLike.congr_fun hab _
      rwa [transport_apply, transport_apply, RingEquiv.symm_apply_apply] at h2
    have h3 : (⟨a, ha⟩ : Fin m) = ⟨b, hb⟩ := by
      apply hCh.chi_inj ⟨w0 i, mem_vGs (hw0 i)⟩
      refine MonoidHom.ext fun c => Units.ext (σ₀.injective ?_)
      rw [← hval i ⟨w0 i, mem_vGs (hw0 i)⟩ (hw0 i) ⟨a, ha⟩ c, ← hval i ⟨w0 i, mem_vGs (hw0 i)⟩ (hw0 i) ⟨b, hb⟩ c, h1]
    exact congrArg Fin.val h3
  · intro i v h v' h' a n _
    show transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (n : kv X.F v) =
      transport (ev i v' h').symm (om' i ^ (2 * (a + 1))) (n : kv X.F v')
    rw [transport_apply, transport_apply, map_intCast (ev i v h).symm, map_intCast (ev i v' h').symm]
  · intro i
    refine ⟨om' i, orderOf_ofUnitHom (hPr.g_prime i) _ ((Units.map_injective σ₀.injective).comp (omi i)), ?_⟩
    intro v h a n _
    show transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (n : kv X.F v) = _
    rw [transport_apply, map_intCast]

end Generic

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_gLoc_idG_chiTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X →
    ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∃ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g),
      I.IdG l Z G ∧ CharacterCompatible G B.R.m := by
  intro B X I hI _ l Z
  have hf : 0 < B.fields.f := by
    unfold Fields.f
    rw [Fintype.card_pos_iff]
    by_contra h
    have h1 := B.fields_f
    unfold Fields.f at h1
    rw [not_nonempty_iff] at h
    rw [Fintype.card_eq_zero] at h1
    unfold Ranks.f Ranks.n at h1
    have := B.R.ord_pos
    omega
  obtain ⟨G, h1, h2, h3, h4⟩ := exists_gLoc I.Ch hf l.pr hI.ch_ok B.sp.cm B.embLL (I.rec7 l Z).nd.g_split
  exact ⟨G, ⟨h1, h2, h3⟩, h4⟩

end GlobalTheory.Mem.TypePrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderTBijective
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.AtLevel

def underT {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) :
    {v : HeightOneSpectrum (𝓞 X.F) // ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal} :=
  ⟨P.1.under (𝓞 X.F), by
    show algebraMap (𝓞 X.F) (𝓞 X.E) _ ∈ P.1.asIdeal
    rw [map_natCast]
    exact T_mem_vT hPr u P⟩

theorem underT_bijective {Z : Dat} (hX : Z.X.Ok) (hPr : Z.Pr.Ok) (u : Z.Pr.Word) : Function.Bijective (underT hPr u) := by
  constructor
  · intro P Q h
    have h1 : P.1.asIdeal.under (𝓞 Z.X.F) = Q.1.asIdeal.under (𝓞 Z.X.F) :=
      congrArg (fun v => v.1.asIdeal) h
    rcases GlobalTheory.CharVal.eq_or_eq_conjP hX (GlobalTheory.CharVal.splitOver_vT hX hPr u Q.2).ne h1 with e | e
    · exact Subtype.ext e
    · refine absurd ?_ (conj_piT_notMem hPr u Q)
      have := decoFin_mem_of_mem_divs P.2
      rw [e, mem_conjP] at this
      exact this
  · rintro ⟨v, hv⟩
    have := v.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 Z.X.E) v.asIdeal
    have hT : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ Q := by
      rw [hQv.over, Ideal.under_def, Ideal.mem_comap, map_natCast] at hv
      exact hv
    have hne : Q ≠ ⊥ := fun e => by
      rw [e, Ideal.mem_bot] at hT
      exact (hPr.T_prime u).ne_zero (by exact_mod_cast hT)
    let P : HeightOneSpectrum (𝓞 Z.X.E) := ⟨Q, hQ.isPrime, hne⟩
    rw [← hPr.piT_norm u] at hT
    rcases hQ.isPrime.mem_or_mem hT with h | h
    · exact ⟨⟨P, (mem_divs (hPr.piT_ne_zero u) P).2 h⟩, Subtype.ext (HeightOneSpectrum.ext hQv.over.symm)⟩
    · exact ⟨⟨conjPrime₂ P, (mem_divs (hPr.piT_ne_zero u) _).2 ((mem_conjP P _).2 h)⟩,
        Subtype.ext (HeightOneSpectrum.ext ((GlobalTheory.CharVal.under_conjP hX P).trans hQv.over.symm))⟩

theorem seenBar_of_not {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal) (hs : ¬ seenC Pr u w) (τ : X.Tau) :
    X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal := by
  rw [← map_natCast (X.embO τ), ← hPr.piT_norm u, map_mul] at hw
  refine (w.isPrime.mem_or_mem hw).resolve_left fun h => hs fun τ' => ?_
  rw [show X.embO τ' (Pr.piT u) = X.embO τ (Pr.piT u) from RingOfIntegers.ext (hPr.piT_Kq u _ _)]
  exact h

theorem mk_surj {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) : Function.Surjective (Ideal.Quotient.mk P.asIdeal) :=
  Ideal.Quotient.mk_surjective

theorem mk_zero {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) (x : 𝓞 X.E) : x ∈ P.asIdeal ↔ Ideal.Quotient.mk P.asIdeal x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.symm


set_option maxHeartbeats 1000000 in
def atTTied {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    AtTTied (D := (I.rec7 l Z)) u where
  eV := Equiv.ofBijective (underT l.pr u)
    (underT_bijective (Z := B.dat X I.Ch) (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1.ok l.pr u)
  piU := X.piT u
  piU_K := X.piT_K u
  piU_norm := X.piT_norm u
  piU_cong := Ideal.mem_span_singleton.2 (X.piT_cong u)
  res := I.resT l u I.mu0
  res_surj v := mk_surj (X := B.fields) v.1
  res_pi v := (mk_zero (X := B.fields) v.1 _).1 (decoFin_mem_of_mem_divs (A := 𝓞 B.fields.E) v.2)
  res_conj v pb h e := by
    have h1 : pb = B.fields.conjO (X.piT u) := RingOfIntegers.ext (h.trans (B.fields_conjO_coe _).symm)
    exact conj_piT_notMem l.pr u v (h1 ▸ Ideal.Quotient.eq_zero_iff_mem.1 e)
  res_v v x := mk_zero (X := B.fields) v.1 _
  tauOf w hw v x := by
    have hval := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
    have hw' : ((B.T u : ℕ) : 𝓞 B.LL) ∈ w.asIdeal :=
      (show B.places.resChar w = B.T u from hw) ▸ resChar_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w
    exact (tauAt_mem_iff l.pr u (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1 hw' v x).symm.trans
      (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).symm
  seenP w hw τ := by
    classical
    have hval := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
    have hw' : ((B.T u : ℕ) : 𝓞 B.LL) ∈ w.asIdeal :=
      (show B.places.resChar w = B.T u from hw) ▸ resChar_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w
    have hs : (((I.rec7 l Z).fm u).seenP w = true) ↔ seenC (B.primes X) u w := decide_eq_true_iff
    by_cases h : seenC (B.primes X) u w
    · rw [if_pos (hs.2 h)]
      exact (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).2 (h τ)
    · rw [if_neg (mt hs.1 h)]
      have h2 := (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).2 (seenBar_of_not l.pr u hw' h τ)
      have h3 : ((B.fields.embO τ (B.fields.conjO (X.piT u)) : 𝓞 B.LL) : B.LL) = B.fields.emb τ (B.host.conj (X.piT u : B.host.E)) :=
        congrArg (B.fields.emb τ) (B.fields_conjO_coe _)
      exact h3 ▸ h2

theorem exists_atTTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ u : B.Word, ∃ A : AtTTied (D := (I.rec7 l Z)) u, I.IdV l u I.mu0 A.eV ∧ A.piU = X.piT u ∧ A.res = I.resT l u I.mu0 :=
  fun I _ _ l Z u => ⟨atTTied I l Z u, fun _ => rfl, rfl, by unfold atTTied; rfl⟩

end GlobalTheory.Mem.AtLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyResidueFieldUnitBallEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapToZModEq
namespace GlobalTheory.AlgebraMapToZMod

theorem algebraMap_toZMod_eq {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type} [inst_1 : Field R]
    [inst_2 : Algebra (ZMod l) R] (f : ℤ_[l] →+* R) (hf : f (l : ℤ_[l]) = 0) (x : ℤ_[l]) :
    algebraMap (ZMod l) R (PadicInt.toZMod x) = f x := by
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  have h := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  set z : ZMod l := PadicInt.toZMod x with hz
  have hc : (ZMod.cast z : ℤ_[l]) = ((z.val : ℕ) : ℤ_[l]) := (ZMod.natCast_val z).symm
  have hx : x = y * (l : ℤ_[l]) + ((z.val : ℕ) : ℤ_[l]) := by
    rw [hy, hc]; ring
  have h1 : f x = ((z.val : ℕ) : R) := by
    conv_lhs => rw [hx]
    rw [map_add (f := _), map_mul, hf, mul_zero, zero_add, map_natCast]
  have h2 : algebraMap (ZMod l) R z = ((z.val : ℕ) : R) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [h1, h2]

end GlobalTheory.AlgebraMapToZMod
end

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open IsLocalRing

theorem valuation_le_one_iff_of_lt_iff {K F : Type} [Field K] [NumberField K] [NormedField F]
    (v : HeightOneSpectrum (𝓞 K)) (a : K →+* F)
    (h : ∀ x : K, v.valuation K x < 1 ↔ ‖a x‖ < 1) (x : K) :
    v.valuation K x ≤ 1 ↔ ‖a x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h1 := h x⁻¹
  have hv : 0 < v.valuation K x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx)
  have hn : 0 < ‖a x‖ := norm_pos_iff.mpr ((map_ne_zero a).mpr hx)
  rw [map_inv₀, map_inv₀, norm_inv, inv_lt_one₀ hv, inv_lt_one₀ hn] at h1
  rw [← not_lt, ← not_lt, h1]

theorem exists_embedding_inducing_place (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
    (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 K)) (hl : ((l : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ∃ a : K →+* PadicAlgCl l, ∀ x : K, v.valuation K x < 1 ↔ ‖a x‖ < 1 := by
  classical
  let a₀ : K →+* PadicAlgCl l := (IsAlgClosed.lift (R := ℚ) (S := K) (M := PadicAlgCl l)).toRingHom
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding K l a₀
  have hlw : ((l : ℕ) : 𝓞 K) ∈ w₀.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hw₀]
    have hfin : ‖a₀ ((l : ℕ) : K)‖ < 1 := by
      rw [map_natCast]
      have h1 : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by simp
      rw [h1, PadicAlgCl.norm_extends]
      exact Padic.norm_p_lt_one
    convert hfin using 3
    first | exact map_natCast _ _ | simp
  have := v.isPrime
  have := w₀.isPrime
  haveI := Formalism.BasicNotions.Examples₂.PlOver.liesOver_of_mem v.asIdeal hl
  haveI := Formalism.BasicNotions.Examples₂.PlOver.liesOver_of_mem w₀.asIdeal hlw
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(l : ℤ)}) v.asIdeal
    w₀.asIdeal (K ≃ₐ[ℚ] K)
  let a : K →+* PadicAlgCl l := a₀.comp (σ : K →+* K)
  obtain ⟨v', hv'⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding K l a
  have hvv : v' = v := by
    apply HeightOneSpectrum.ext
    ext y
    have h2 : (σ • y) ∈ w₀.asIdeal ↔ y ∈ v.asIdeal := by
      rw [← hσ]; exact Ideal.smul_mem_pointwise_smul_iff
    rw [← h2, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hv',
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), hw₀]
    rfl
  subst hvv
  exact ⟨a, hv'⟩

theorem algebraMap_toZMod_eq {l : ℕ} [Fact l.Prime] {R : Type} [Field R] [Algebra (ZMod l) R]
    (f : ℤ_[l] →+* R) (hf : f (l : ℤ_[l]) = 0) (x : ℤ_[l]) :
    algebraMap (ZMod l) R (PadicInt.toZMod x) = f x := by
  first
  | exact @_root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq
  | exact _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq
  | (apply _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraMapToZMod.algebraMap_toZMod_eq ..)

theorem isAlgebraic_residueField {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [IsLocalRing B]
    [Algebra (ZMod l) (ResidueField B)] (c : ℤ_[l] →+* B)
    (hcl : c (l : ℤ_[l]) ∈ maximalIdeal B)
    (halg : ∀ b : B, ∃ p : ℤ_[l][X], p.IsPrimitive ∧ p.eval₂ c b = 0) :
    Algebra.IsAlgebraic (ZMod l) (ResidueField B) := by
  have hl : (residue B).comp c (l : ℤ_[l]) = 0 := (residue_eq_zero_iff _).mpr hcl
  have hcomp : (algebraMap (ZMod l) (ResidueField B)).comp PadicInt.toZMod = (residue B).comp c :=
    RingHom.ext fun x => algebraMap_toZMod_eq _ hl x
  refine ⟨fun y => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective y
  obtain ⟨p, hp, hb⟩ := halg b
  refine ⟨p.map PadicInt.toZMod, fun h => ?_, ?_⟩
  · have hdvd : Polynomial.C (l : ℤ_[l]) ∣ p := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have h1 : PadicInt.toZMod (p.coeff i) = 0 := by
        have := congrArg (fun q => q.coeff i) h
        simpa using this
      have h2 : p.coeff i ∈ RingHom.ker (PadicInt.toZMod (p := l)) := h1
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at h2
      exact Ideal.mem_span_singleton.mp h2
    have hu := hp _ hdvd
    exact PadicInt.prime_p.not_unit hu
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hb, map_zero]

theorem exists_isPrimitive_eval₂_eq_zero {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) :
    ∃ p : ℤ_[l][X], p.IsPrimitive ∧
      p.eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom) x = 0 := by
  classical
  have hmap : algebraMap ℤ_[l] (PadicAlgCl l) =
      (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom :=
    IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)
  haveI : FaithfulSMul ℤ_[l] (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [hmap]
      exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp fun a b h => Subtype.ext h)
  letI : NormalizedGCDMonoid ℤ_[l] := Classical.arbitrary _
  have hx : IsAlgebraic ℤ_[l] x :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (PadicAlgCl l)).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨p, hp0, hp⟩ := hx
  refine ⟨p.primPart, p.isPrimitive_primPart, ?_⟩
  rw [← hmap]
  exact Polynomial.aeval_primPart_eq_zero hp0 hp

def unitBall {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) : ValuationSubring ℂ :=
  (PadicAlgCl.valued l).v.valuationSubring.comap (ι.symm : ℂ →+* PadicAlgCl l)

theorem mem_unitBall_iff {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (z : ℂ) :
    z ∈ unitBall ι ↔ ‖ι.symm z‖ ≤ 1 := by
  rw [unitBall, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
    ← NNReal.coe_le_coe]
  rfl

theorem nonempty_residueField_unitBall_equiv {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) :
    Nonempty (ResidueField (unitBall ι) ≃+* Formalism.CyclotomicNorms.Fbar l) := by
  classical
  set B := unitBall ι with hB
  let inc : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom
  have hinc : ∀ x : ℤ_[l], ‖inc x‖ = ‖x‖ := fun x => by
    change ‖((x : ℚ_[l]) : PadicAlgCl l)‖ = ‖x‖
    rw [PadicAlgCl.norm_extends]; rfl
  let c : ℤ_[l] →+* B := (ι.toRingHom.comp inc).codRestrict B.toSubring fun x => by
    change ι (inc x) ∈ B
    rw [hB, mem_unitBall_iff, RingEquiv.symm_apply_apply, hinc]
    exact PadicInt.norm_le_one x
  have hcl : c (l : ℤ_[l]) ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨⟨y, hy⟩, hxy⟩ := hu.exists_right_inv
    have h1 : ι (inc (l : ℤ_[l])) * y = 1 := congrArg Subtype.val hxy
    have h2 : inc (l : ℤ_[l]) * ι.symm y = 1 := by
      apply ι.injective
      rw [map_mul, RingEquiv.apply_symm_apply, h1, map_one]
    have h3 := congrArg norm h2
    have h4 : ‖ι.symm y‖ ≤ 1 := (mem_unitBall_iff ι y).mp hy
    rw [norm_mul, hinc, norm_one] at h3
    have h5 : ‖(l : ℤ_[l])‖ < 1 := by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
    nlinarith [norm_nonneg (ι.symm y), norm_nonneg (l : ℤ_[l])]
  have halg : ∀ b : B, ∃ p : ℤ_[l][X], p.IsPrimitive ∧ p.eval₂ c b = 0 := by
    intro b
    obtain ⟨p, hp, h0⟩ := exists_isPrimitive_eval₂_eq_zero (ι.symm (b : ℂ))
    refine ⟨p, hp, Subtype.ext ?_⟩
    have h1 := Polynomial.hom_eval₂ p c B.subtype b
    have h2 := Polynomial.hom_eval₂ p inc ι.toRingHom (ι.symm (b : ℂ))
    have h3 : B.subtype.comp c = ι.toRingHom.comp inc := RingHom.ext fun _ => rfl
    have h4 : ι.toRingHom (ι.symm (b : ℂ)) = B.subtype b := ι.apply_symm_apply _
    rw [h3, ← h4, ← h2] at h1
    have h5 : p.eval₂ inc (ι.symm (b : ℂ)) = 0 := h0
    rw [h5, map_zero] at h1
    exact h1
  have hlR : ((l : ℕ) : ResidueField B) = 0 := by
    have := (residue_eq_zero_iff _).mpr hcl
    simpa using this
  haveI : CharP (ResidueField B) l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hlR
  letI : Algebra (ZMod l) (ResidueField B) := ZMod.algebra _ l
  haveI : Algebra.IsAlgebraic (ZMod l) (ResidueField B) := isAlgebraic_residueField c hcl halg
  haveI : IsAlgClosed (ResidueField B) :=
    GlobalTheory.isAlgClosed_residueField_of_valuationRing_of_isAlgClosed B ℂ
  haveI : IsAlgClosure (ZMod l) (ResidueField B) := ⟨inferInstance, inferInstance⟩
  exact ⟨(IsAlgClosure.equiv (ZMod l) (ResidueField B) (AlgebraicClosure (ZMod l))).toRingEquiv⟩

theorem val_nonneg_iff (D : D7) (lam : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val lam x ↔ (D.plEq lam).valuation D.what₂.LL x ≤ 1 := by
  haveI := D.nfLL
  by_cases hx : x = 0
  · simp [hx]
  rw [D.val_eq lam x hx]
  have h0 : (D.plEq lam).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have h1 := WithZero.log_le_log (x := (D.plEq lam).valuation D.what₂.LL x) (y := 1) h0 one_ne_zero
  rw [WithZero.log_one] at h1
  rw [← h1]
  unfold vAdd
  norm_cast
  omega

theorem nonempty_plSide : ∀ D : D7, Nonempty (PlSide D) := by
  intro D
  haveI := D.nfLL
  haveI := D.galLL
  have key : ∀ lam : D.what₂.places.Pl, ∃ ι : Qbar (D.what₂.places.resChar lam) ≃+* ℂ,
      ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val lam x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1 := by
    intro lam
    obtain ⟨a, ha⟩ := exists_embedding_inducing_place D.what₂.LL (D.what₂.places.resChar lam)
      (D.plEq lam) (Formalism.BasicNotions.Examples₂.PlOver.resChar_mem D lam)
    obtain ⟨ι, hι⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq
      (D.what₂.places.resChar lam) D.what₂.LL a D.what₂.embLL
    refine ⟨ι, fun x => ?_⟩
    have h1 : ι.symm (D.what₂.embLL x) = a x := by
      rw [← hι]; exact ι.symm_apply_apply _
    rw [h1, val_nonneg_iff, valuation_le_one_iff_of_lt_iff _ a ha]
  choose ι hι using key
  exact ⟨⟨ι, hι, fun lam => unitBall (ι lam), fun lam z => mem_unitBall_iff (ι lam) z,
    fun lam => Classical.choice (nonempty_residueField_unitBall_equiv (ι lam))⟩⟩

end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotMeasureEqSmul
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingNorm

theorem sq_eq_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) :
    ((‖x‖ ^ 2 : ℝ) : ℂ) = inner ℂ x x := by
  rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]
  rfl

variable {D : D7}

theorem quotMeasure_eq_smul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = ν 𝓕 • muQ1 V := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hp := GlobalTheory.AutomorphicL2Unitary.isVolPair_volPair hP
  have := hp.1.1
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have e := Measure.isMulLeftInvariant_eq_smul ν (volPair V).1
  set c := Measure.haarScalarFactor ν (volPair V).1
  have e1 : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = (c : ENNReal) • muQ V := by
    rw [GlobalTheory.AutomorphicL2Unitary.muQ_eq hP, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have e2 : ν 𝓕 = c * muQ V Set.univ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]
    exact congrArg (fun m : Measure (AutQ V) => m Set.univ) e1
  rw [e1, e2, muQ1, if_pos (show _ ∧ _ from hV), smul_smul, mul_assoc, ENNReal.mul_inv_cancel hV.1 hV.2, mul_one]

theorem integral_star_mul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (φ : GA D V → ℂ) (hφ : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g)
    (ψ : AutQ V → ℂ) (hψ : MemLp ψ 2 (muQ1 V)) (c : ℝ) (h : ∀ q, ‖φ q.out‖ = c * ‖ψ q‖) :
    ∫ g in 𝓕, star (φ g) * φ g ∂ν = (((ν 𝓕).toReal * (c * ‖hψ.toLp ψ‖) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ := hφ
  have e1 := GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕
    (fun q => star (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q) * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q)
  simp only [hL.descend_mk] at e1
  have e2 : ((‖hψ.toLp ψ‖ ^ 2 : ℝ) : ℂ) = ∫ q, ((‖ψ q‖ ^ 2 : ℝ) : ℂ) ∂muQ1 V := by
    rw [sq_eq_inner, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ.coeFn_toLp] with q hq
    rw [hq, sq_eq_inner]
  rw [← e1, show GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _ from quotMeasure_eq_smul V hs hν h𝓕, integral_smul_measure, mul_pow,
    Complex.ofReal_mul, Complex.ofReal_mul, e2, ← integral_const_mul, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show star (φ q.out) * φ q.out = ((c ^ 2 : ℝ) : ℂ) * ((‖ψ q‖ ^ 2 : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, ← mul_pow, ← h, Complex.ofReal_pow]
  exact Complex.conj_mul' _

end GlobalTheory.ReadingNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepPuVolAR
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe.KeepD

variable {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X)


set_option maxHeartbeats 4000000 in
theorem toTerm_eTT (u u' : D.what₂.Word) (s : TT Y u u') : (eTT Z Y u u' s).toTerm = eRT Z Y u u' s.toTerm := (by with_unfolding_all exact (Eq.refl (eRT Z Y u u' s.toTerm) :))


set_option maxHeartbeats 4000000 in
def eFib (u u' : D.what₂.Word) (t : RT Y u u') : fib Y t ≃ fib (reY Z Y) (eRT Z Y u u' t) :=
  Equiv.subtypeEquiv (eTT Z Y u u') fun s => by
    rw [toTerm_eTT]
    exact (eRT Z Y u u').injective.eq_iff.symm


set_option maxHeartbeats 4000000 in
theorem aT_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u u' : D.what₂.Word) (s : TT Y u u') (x : ColT (h.shInj u')) :
    eCure Z h h' u (aT h u u' s x) = aT h' (wd Z u) (wd Z u') (eTT Z Y u u' s) (eCure Z h h' u' x) := (by with_unfolding_all exact (
  Eq.refl (aT h u u' s x) :))


set_option maxHeartbeats 4000000 in
theorem aR_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u u' : D.what₂.Word) (t : RT Y u u') (x : ColT (h.shInj u')) :
    eCure Z h h' u (aR h u u' t x) = aR h' (wd Z u) (wd Z u') (eRT Z Y u u' t) (eCure Z h h' u' x) := by
  letI := h.fibFT t
  letI := h'.fibFT (eRT Z Y u u' t)
  unfold aR
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, map_sum]
  exact Fintype.sum_equiv (eFib Z Y u u' t) _ _ fun s => aT_keep Z Y u u' s.1 x


set_option maxHeartbeats 4000000 in
theorem pu_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u : D.what₂.Word) (x : ColT (h.shInj u)) :
    eHHre Z X (puC h u x) = puC h' (wd Z u) (eCure Z h h' u x) := (by with_unfolding_all exact (Eq.refl (puC h u x) :))


set_option maxHeartbeats 4000000 in
theorem vol_keep (u : D.what₂.Word) : Y.volN u = (reY Z Y).volN u ∧ Y.volH u = (reY Z Y).volH u := by
  constructor
  · exact (by with_unfolding_all exact (Eq.refl (Y.volN u) :))
  · exact (by with_unfolding_all exact (Eq.refl (Y.volH u) :))

end GlobalTheory.Mem.SRe.KeepD

namespace GlobalTheory.Mem.SRe


set_option maxHeartbeats 4000000 in
theorem keep_pu_vol_aR : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y)), (∀ u x, eHHre Z X (puC h u x) = puC h' (wd Z u) (eCure Z h h' u x)) ∧ (∀ u, Y.volN u = (reY Z Y).volN u ∧ Y.volH u = (reY Z Y).volH u) ∧ ∀ u u' (t : RT Y u u') x, eCure Z h h' u (aR h u u' t x) = aR h' (wd Z u) (wd Z u') (eRT Z Y u u' t) (eCure Z h h' u' x) :=
  fun _ Z _ Y _ _ => ⟨fun u x => KeepD.pu_keep Z Y u x, fun u => KeepD.vol_keep Z Y u,
    fun u u' t x => KeepD.aR_keep Z Y u u' t x⟩

end GlobalTheory.Mem.SRe
end
