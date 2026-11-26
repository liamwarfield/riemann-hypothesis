module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.RealAction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {A B : Type} [CommRing A] [CommRing B] {m n : Type} [Fintype m] [Fintype n]

theorem map_triple (φ : A →+* B) (g : Matrix m m A) (x : Matrix m n A) (h : Matrix n n A) :
    (g * x * hᵀ).map φ = g.map φ * x.map φ * (h.map φ)ᵀ := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem map_triple_zero (φ : A →+* B) (g : Matrix m m A) (x : Matrix m n A) (h : Matrix n n A)
    (hx : x.map φ = 0) : (g * x * hᵀ).map φ = 0 := by
  rw [map_triple, hx, Matrix.mul_zero, Matrix.zero_mul]

omit [Fintype m] in
theorem map_conj (s : A →+* A) (φ : A →+* ℂ) (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (g : Matrix m m A) :
    (g.map s).map φ = (g.map φ).map (starRingEnd ℂ) := by
  ext a b
  exact h _

theorem unitary_map (s : A →+* A) (φ : A →+* ℂ) (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (g J : Matrix m m A)
    (hg : (g.map s)ᵀ * J * g = J) : (g.map φ)ᴴ * J.map φ * g.map φ = J.map φ := by
  have e : (g.map φ)ᴴ = ((g.map s)ᵀ).map φ := by
    ext a b
    exact (h _).symm
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hg]

end Generic

variable {D : D7}

theorem infMat_eq (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (k : GA D V) :
    infMat D.sp.cm.sig V.gram θ k = (mt V k).map (θ.comp (infPart D)) := rfl

theorem wAt_eq (θ : InfFam D) (V W : HSp D) (τ : D.what₂.Tau) (x : WA V W) :
    wAt θ V W τ x = x.map ((θ τ).comp (infPart D)) := rfl

theorem gramAt_eq {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    gramAt D V τ = (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) := by
  ext a b
  exact (comp_incA hθ τ _).symm

theorem infMat_mem_UH {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (k : GA D V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  rw [infMat_eq, gramAt_eq hθ]
  exact unitary_map (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ) _ _ (mt_rel V k)

theorem wAt_actHom {θ : InfFam D} (hθ : IsInfFam θ) (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W)
    (τ : D.what₂.Tau) : wAt θ V W τ (actHom V W k k' x) =
      actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x) := by
  rw [infMat_eq, infMat_eq, wAt_eq, wAt_eq]
  unfold actHom actC cM
  split_ifs
  · rw [← map_conj (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ)]
    exact map_triple _ _ _ _
  · rw [← map_conj (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ)]
    exact map_triple _ _ _ _

theorem isRealW_actHom (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W) (hx : IsRealW V W x) :
    IsRealW V W (actHom V W k k' x) := by
  unfold IsRealW actHom
  split_ifs
  · exact map_triple_zero (finPart D) _ _ _ hx
  · exact map_triple_zero (finPart D) _ _ _ hx

theorem real_action : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (V : HSp D) (k : GA D V) (τ : D.what₂.Tau), infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧ ∀ (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W), (∀ τ, wAt θ V W τ (actHom V W k k' x) = actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x)) ∧ (IsRealW V W x → IsRealW V W (actHom V W k k' x)) :=
  fun _ _ hθ => ⟨fun V k τ => infMat_mem_UH hθ V k τ, fun V W k k' x =>
    ⟨fun τ => wAt_actHom hθ V W k k' x τ, isRealW_actHom V W k k' x⟩⟩

end GlobalTheory.FockCompare.RealAction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_action_at_real_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (V : HSp D) (k : GA D V) (τ : D.what₂.Tau), infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧ ∀ (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W), (∀ τ, wAt θ V W τ (actHom V W k k' x) = actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x)) ∧ (IsRealW V W x → IsRealW V W (actHom V W k k' x)) := by
  first | exact @GlobalTheory.FockCompare.RealAction.real_action | exact GlobalTheory.FockCompare.RealAction.real_action | (intros; apply GlobalTheory.FockCompare.RealAction.real_action <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CMTypePlaces

open NumberField

theorem mk_tauE_bijective (D : D7) :
    Function.Bijective fun τ : D.what₂.Tau => InfinitePlace.mk (tauE D τ) := by
  obtain ⟨hb, hm⟩ := Formalism.BasicNotions.factEmb D.R D.host
  have hsq := D.host.sqd_sq
  have hd0 : (0 : ℝ) ≤ D.host.d := Nat.cast_nonneg _
  have hmem : ∀ τ : D.what₂.Tau, tauE D τ (D.host.sqd) =
      Complex.I * (Real.sqrt D.host.d : ℂ) := fun τ => (hm _).2 (D.eTau τ).2
  have hdpos : 0 < D.host.d := lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by
    have : Real.sqrt D.host.d ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hdpos)).ne'
    exact_mod_cast this
  have hconj : (starRingEnd ℂ) (Complex.I * (Real.sqrt D.host.d : ℂ)) =
      -(Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  have hsurj : ∀ φ : D.host.E →+* ℂ, φ (D.host.sqd) =
      Complex.I * (Real.sqrt D.host.d : ℂ) → ∃ τ, tauE D τ = φ := by
    intro φ hφ
    obtain ⟨g, rfl⟩ := hb.2 φ
    refine ⟨D.eTau.symm ⟨g, (hm g).1 hφ⟩, ?_⟩
    simp only [tauE, Equiv.apply_symm_apply]
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact D.eTau.injective (Subtype.ext (hb.1 h))
    · exfalso
      have h1 := congrArg (fun φ : D.host.E →+* ℂ => φ (D.host.sqd)) h
      simp only [ComplexEmbedding.conjugate_coe_eq] at h1
      rw [hmem, hmem, hconj] at h1
      have h2 : Complex.I * (Real.sqrt D.host.d : ℂ) = 0 := by linear_combination (-1 / 2 : ℂ) * h1
      exact mul_ne_zero Complex.I_ne_zero hs h2
  · intro w
    have h1 : (w.embedding (D.host.sqd)) ^ 2 =
        (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [← map_pow, hsq, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hd0]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · obtain ⟨τ, hτ⟩ := hsurj _ h
      exact ⟨τ, by simp only [hτ, InfinitePlace.mk_embedding]⟩
    · obtain ⟨τ, hτ⟩ := hsurj (ComplexEmbedding.conjugate w.embedding) (by
        rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, hconj, neg_neg])
      exact ⟨τ, by simp only [hτ, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]⟩

theorem places_bijective : ∀ D : D7, Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) := by
  intro D
  haveI := D.host.isCMField_hostE
  exact (IsCMField.equivInfinitePlace D.host.E).bijective.comp (mk_tauE_bijective D)

end GlobalTheory.CMTypePlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_restrict_realSubfield_infinitePlace_bijective : ∀ D : D7, Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) := by
  first | exact @GlobalTheory.CMTypePlaces.places_bijective | exact GlobalTheory.CMTypePlaces.places_bijective | (intros; apply GlobalTheory.CMTypePlaces.places_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare.SymplVal

theorem trace_field {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  obtain ⟨a, ha⟩ := hf (e + σ e) (by rw [map_add (f := _), hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h2, map_add (f := _), h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

theorem trace_tensor {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e)
    (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]; ring
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, h4, ← TensorProduct.tmul_add, ← trace_field h2 σ hσ hf, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]

theorem trace_AE (D : D7) (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) z) = z + cA D z :=
  trace_tensor D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e) (fun e he => (D.sp.cm.fixed e).1 he) _ z

theorem map_sum4 {A : Type} [CommRing A] (φ : A →+* ℂ) (c : A →+* A) (hc : ∀ a, φ (c a) = starRingEnd ℂ (φ a))
    {m n : ℕ} (x y : Fin m → Fin n → A) (P Q : Fin m → Fin n → Fin m → Fin n → A) :
    φ (∑ i, ∑ j, ∑ k, ∑ l, c (x i j) * P i j k l * Q i j k l * y k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (φ (x i j)) * φ (P i j k l) * φ (Q i j k l) * φ (y k l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc]

theorem comp_hHom {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W) :
    θ τ (infPart D (hHom V W x y)) = hC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  have hi : ∀ e, ((θ τ).comp (infPart D)) (incA D e) = tauE D τ e := comp_incA hθ τ
  unfold hHom hC
  split_ifs
  · refine (map_sum4 ((θ τ).comp (infPart D)) (cA D) (comp_cA hθ τ) x y
      (fun i j k l => incA D (V.gram k i)) (fun i j k l => incA D (W.gram j l))).trans ?_
    simp only [hi]
    rfl
  · refine (map_sum4 ((θ τ).comp (infPart D)) (cA D) (comp_cA hθ τ) x y
      (fun i j k l => incA D (V.gram i k)) (fun i j k l => incA D (W.gram l j))).trans ?_
    simp only [hi]
    rfl

theorem valTau_sympl : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W),
    valTau θ τ (sympl V W x y) = symplC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  intro D θ hθ V W τ x y
  unfold valTau sympl symplC
  rw [trace_AE, RingHom.map_add (f := _), RingHom.map_add (f := _), comp_cA hθ, RingHom.map_mul, RingHom.map_mul, comp_incA hθ,
    comp_hHom hθ, Complex.add_re, Complex.conj_re, two_mul]

end GlobalTheory.FockCompare.SymplVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_val_tau_compat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W), valTau θ τ (sympl V W x y) = symplC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  first | exact @GlobalTheory.FockCompare.SymplVal.valTau_sympl | exact GlobalTheory.FockCompare.SymplVal.valTau_sympl | (intros; apply GlobalTheory.FockCompare.SymplVal.valTau_sympl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem smooth_iff_sm_and_real_lines : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V W : HSp D), (∀ f : WA V W → ℂ, (∀ (k : ℕ) (L : (Fin k → ℝ) →+ WA V W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)) ↔ Sm (iotaW σ V W) f) ∧ (∀ L : ℝ →+ WA V W, IsRealDir V W L → ∀ t : ℝ, L t = iotaW σ V W (t • piW θ V W (L 1))) ∧ ∀ u : RW V W, ∃ L : ℝ →+ WA V W, IsRealDir V W L ∧ ∀ t : ℝ, L t = iotaW σ V W (t • u) := by
  intro D θ σ h V W
  refine ⟨fun f => ⟨fun H w => ?_, fun H k L hL hL0 w => ?_⟩, fun L hL t => ?_, fun u => ?_⟩
  · let e : RW V W ≃L[ℝ] (Fin (Module.finrank ℝ (RW V W)) → ℝ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])
    have h1 := H _ ((iotaW σ V W).comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom)
      ((h.continuous_iota V W).comp e.symm.continuous) (fun t => h.real_iota V W _) w
    have h2 := h1.comp e.contDiff
    have h3 : (fun x : RW V W => f (w + iotaW σ V W x)) = fun x => f (w + iotaW σ V W (e.symm (e x))) := by
      funext x; rw [e.symm_apply_apply]
    rw [h3]
    exact h2
  · let M : (Fin k → ℝ) →L[ℝ] RW V W :=
      ((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL)
    have h2 := (H w).comp M.contDiff
    have h3 : (fun t => f (w + L t)) = fun t => f (w + iotaW σ V W (piW θ V W (L t))) := by
      funext t; rw [h.iota_pi (hL0 t)]
    rw [h3]
    exact h2
  · let M : ℝ →L[ℝ] RW V W :=
      ((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL.1)
    have h2 : M (t • (1 : ℝ)) = t • M 1 := M.map_smul t 1
    rw [smul_eq_mul, mul_one] at h2
    have h3 : piW θ V W (L t) = t • piW θ V W (L 1) := h2
    rw [← h3, h.iota_pi (hL.2 t)]
  · let M : ℝ →L[ℝ] RW V W := ContinuousLinearMap.toSpanSingleton ℝ u
    exact ⟨(iotaW σ V W).comp M.toLinearMap.toAddMonoidHom,
      ⟨(h.continuous_iota V W).comp M.continuous, fun t => h.real_iota V W _⟩, fun t => rfl⟩

end GlobalTheory.FockCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLinesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V W : HSp D), (∀ f : WA V W → ℂ, (∀ (k : ℕ) (L : (Fin k → ℝ) →+ WA V W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)) ↔ Sm (iotaW σ V W) f) ∧ (∀ L : ℝ →+ WA V W, IsRealDir V W L → ∀ t : ℝ, L t = iotaW σ V W (t • piW θ V W (L 1))) ∧ ∀ u : RW V W, ∃ L : ℝ →+ WA V W, IsRealDir V W L ∧ ∀ t : ℝ, L t = iotaW σ V W (t • u) := by
  first | exact @GlobalTheory.FockCompare.smooth_iff_sm_and_real_lines | exact GlobalTheory.FockCompare.smooth_iff_sm_and_real_lines | (intros; apply GlobalTheory.FockCompare.smooth_iff_sm_and_real_lines <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.AdelicFactorial

theorem tendsto_factorial_adicCompletion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : v.adicCompletion F)) atTop (𝓝 0) := by
  have hle : ∀ m : ℕ, ‖(m : v.adicCompletion F)‖ ≤ 1 := fun m => by
    have := FinitePlace.norm_le_one F v (m : 𝓞 F)
    simpa using this
  set M := Ideal.absNorm v.asIdeal with hM
  have hlt : ‖(M : v.adicCompletion F)‖ < 1 := by
    have := (FinitePlace.norm_lt_one_iff_mem F v (M : 𝓞 F)).2 (Ideal.absNorm_mem _)
    simpa using this
  have hM0 : 0 < M := lt_trans one_pos (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hlt
  refine ⟨M ^ k, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (pow_pos hM0 k) hn
  rw [dist_zero_right, hc, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle c)) hk

theorem tendsto_factorial_finiteAdele (F : Type) [Field F] [NumberField F] :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => fun v : HeightOneSpectrum (𝓞 F) =>
      ((n.factorial : ℕ) : v.adicCompletionIntegers F)) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun v => ?_
    rw [tendsto_subtype_rng]
    simpa using tendsto_factorial_adicCompletion F v
  have h2 := ((RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := cofinite)).continuous.tendsto _).comp h1
  exact h2

theorem exists_nat_mem_of_isOpen : ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (AF F)),
    IsOpen (U : Set (AF F)) → ∃ N : ℕ, 0 < N ∧ pairA F 0 (N : Af F) ∈ U := by
  intro F _ _ U hU
  have h : Tendsto (fun n : ℕ => pairA F 0 ((n.factorial : ℕ) : Af F)) atTop (𝓝 (0 : AF F)) :=
    (tendsto_const_nhds (x := (0 : Ainf F))).prodMk_nhds (tendsto_factorial_finiteAdele F)
  obtain ⟨n, hn⟩ := (h.eventually (hU.mem_nhds U.zero_mem)).exists
  exact ⟨n.factorial, n.factorial_pos, hn⟩

end GlobalTheory.AdelicFactorial
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_nat_mem_open_adele_subgroup : ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (AF F)), IsOpen (U : Set (AF F)) → ∃ N : ℕ, 0 < N ∧ pairA F 0 (N : Af F) ∈ U := by
  first | exact @GlobalTheory.AdelicFactorial.exists_nat_mem_of_isOpen | exact GlobalTheory.AdelicFactorial.exists_nat_mem_of_isOpen | (intros; apply GlobalTheory.AdelicFactorial.exists_nat_mem_of_isOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare.RealChart

theorem tensor_span {F E M : Type} [Field F] [Field E] [Algebra F E] [AddCommGroup M] [Module F M] (δ : E)
    (h : ∀ x : E, ∃ u v : F, x = u • (1 : E) + v • δ) (a : M ⊗[F] E) :
    ∃ a₀ a₁ : M, a = a₀ ⊗ₜ[F] (1 : E) + a₁ ⊗ₜ[F] δ := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul m x =>
    obtain ⟨u, v, rfl⟩ := h x
    exact ⟨u • m, v • m, by simp only [TensorProduct.tmul_add, TensorProduct.smul_tmul]⟩
  | add a b ha hb =>
    obtain ⟨a₀, a₁, rfl⟩ := ha
    obtain ⟨b₀, b₁, rfl⟩ := hb
    exact ⟨a₀ + b₀, a₁ + b₁, by simp only [TensorProduct.add_tmul]; abel⟩

theorem zero_tmul_add {F E M : Type} [Field F] [Field E] [Algebra F E] [CommRing M] [Algebra F M] (x y : E) :
    (0 : M) ⊗ₜ[F] x + (0 : M) ⊗ₜ[F] y = 0 := by simp

theorem tensor_prod_ext {F E R A B : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [CommRing A] [CommRing B]
    [Algebra F R] [Algebra F A] [Algebra F B] (p : R →ₐ[F] A) (q : R →ₐ[F] B) (i : A →ₗ[F] R) (j : B →ₗ[F] R)
    (h : ∀ x, i (p x) + j (q x) = x) (a : R ⊗[F] E)
    (h1 : Algebra.TensorProduct.map p (AlgHom.id F E) a = 0)
    (h2 : Algebra.TensorProduct.map q (AlgHom.id F E) a = 0) : a = 0 := by
  have key : ∀ a : R ⊗[F] E,
      a = i.rTensor E (Algebra.TensorProduct.map p (AlgHom.id F E) a) +
        j.rTensor E (Algebra.TensorProduct.map q (AlgHom.id F E) a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul m x => simp [← TensorProduct.add_tmul, h]
    | add a b ha hb =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← ha, ← hb]
  rw [key a, h1, h2]; simp

theorem adele_tensor_ext {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (a : AF F ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) a = 0)
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) a = 0) : a = 0 :=
  tensor_prod_ext (fstA F) (sndA F) (LinearMap.inl F (Ainf F) (Af F)) (LinearMap.inr F (Ainf F) (Af F))
    (fun x => Prod.ext (add_zero x.1) (zero_add x.2)) a h1 h2

theorem star_sqrtMinusD (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have := D.host.isCMField_hostE
  have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
  rw [h2, map_neg, h1]
  simp

theorem sqrt_d_pos (D : D7) : 0 < Real.sqrt D.host.d :=
  Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))

theorem sqrtMinusD_ne (D : D7) : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [h, map_zero] at h1
  have := congrArg Complex.im h1
  have h2 := sqrt_d_pos D
  simp only [Complex.zero_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.ofReal_re] at this
  linarith

theorem host_span (D : D7) (x : D.host.E) :
    ∃ u v : D.host.F, x = u • (1 : D.host.E) + v • D.host.sqrtMinusD := by
  have hδ := sqrtMinusD_ne D
  have h2 : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  obtain ⟨u, hu⟩ := (D.sp.cm.fixed ((x + star x) / 2)).1 (by
    show star ((x + star x) / 2) = _
    rw [star_div₀, star_add, star_star, h2, add_comm])
  obtain ⟨v, hv⟩ := (D.sp.cm.fixed ((x - star x) / (2 * D.host.sqrtMinusD))).1 (by
    show star ((x - star x) / (2 * D.host.sqrtMinusD)) = _
    rw [star_div₀, star_sub, star_star, star_mul', h2, star_sqrtMinusD]
    field_simp
    ring)
  refine ⟨u, v, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def]
  erw [hu, hv]
  field_simp
  ring

variable {D : D7} {θ : InfFam D}

theorem comp_tmul (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : Ainf D.host.F) (y : D.host.E) :
    θ τ (a ⊗ₜ[D.host.F] y) = θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ y := by
  rw [← (hθ τ).1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

def emb (D : D7) (e : D.host.E) : Ainf D.host.F →+ AE D where
  toFun a := pairA D.host.F a 0 ⊗ₜ[D.host.F] e
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' a b := by
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext rfl (add_zero _).symm

theorem continuous_emb (e : D.host.E) : Continuous (emb D e) := by
  have h1 : Continuous fun a : Ainf D.host.F => pairA D.host.F a 0 :=
    Continuous.prodMk continuous_id continuous_const
  have h2 : Continuous fun a : AF D.host.F => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  refine (h2.comp h1).congr fun a => ?_
  show pairA D.host.F a 0 • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) = pairA D.host.F a 0 ⊗ₜ[D.host.F] e
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem finPart_emb (e : D.host.E) (a : Ainf D.host.F) : finPart D (emb D e a) = 0 :=
  TensorProduct.zero_tmul _ e

theorem infPart_emb (e : D.host.E) (a : Ainf D.host.F) : infPart D (emb D e a) = a ⊗ₜ[D.host.F] e := rfl

def reP (ι : Type) : (ι → ℂ) →+ (ι → ℝ) where
  toFun z i := (z i).re
  map_zero' := rfl
  map_add' _ _ := rfl

def imaginary (ι : Type) (c : ℝ) : (ι → ℂ) →+ (ι → ℝ) where
  toFun z i := (z i).im / c
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [add_div]

theorem exists_chart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ → (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) → (∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0) → ∃ σ : (D.what₂.Tau → ℂ) →+ AE D, Chart θ σ := by
  intro D θ hθ ρ hρ h1 h0
  have hd := sqrt_d_pos D
  let σ : (D.what₂.Tau → ℂ) →+ AE D :=
    { toFun := fun z => emb D 1 (ρ (reP _ z)) + emb D D.host.sqrtMinusD (ρ (imaginary _ (Real.sqrt D.host.d) z))
      map_zero' := by rw [(reP _).map_zero, (imaginary _ _).map_zero, ρ.map_zero, (emb D _).map_zero, (emb D _).map_zero, add_zero]
      map_add' := fun x y => by
        rw [(reP _).map_add, (imaginary _ _).map_add, ρ.map_add, ρ.map_add, (emb D _).map_add, (emb D _).map_add,
          add_add_add_comm] }
  have hσ : ∀ z, σ z = emb D 1 (ρ (reP _ z)) + emb D D.host.sqrtMinusD (ρ (imaginary _ (Real.sqrt D.host.d) z)) :=
    fun _ => rfl
  refine ⟨σ, hθ, ?_, fun z => ?_, fun z τ => ?_, fun a hf hi => ?_⟩
  · have c1 : Continuous (reP D.what₂.Tau) :=
      continuous_pi fun τ => Complex.continuous_re.comp (continuous_apply τ)
    have c2 : Continuous (imaginary D.what₂.Tau (Real.sqrt D.host.d)) :=
      continuous_pi fun τ => (Complex.continuous_im.comp (continuous_apply τ)).div_const _
    exact ((continuous_emb _).comp (hρ.comp c1)).add ((continuous_emb _).comp (hρ.comp c2))
  · rw [hσ, RingHom.map_add (f := _), finPart_emb, finPart_emb, add_zero]
  · rw [hσ, RingHom.map_add (f := _), infPart_emb, infPart_emb, RingHom.map_add (f := _), comp_tmul hθ τ _ D.host.sqrtMinusD, h1, h1,
      tauE_sqrtMinusD]
    show ((z τ).re : ℂ) + (((z τ).im / Real.sqrt D.host.d : ℝ) : ℂ) * _ = _
    have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [Complex.ofReal_div, mul_comm Complex.I, ← mul_assoc, div_mul_cancel₀ _ h2, Complex.re_add_im]
  · obtain ⟨b₀, b₁, hb⟩ := tensor_span D.host.sqrtMinusD (host_span D) (infPart D a)
    have key : ∀ τ, θ τ (b₀ ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 ∧ θ τ (b₁ ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
      intro τ
      have e := hi τ
      rw [hb, RingHom.map_add (f := _), comp_tmul hθ τ _ D.host.sqrtMinusD, tauE_sqrtMinusD] at e
      have r0 := Complex.conj_eq_iff_im.1 (conj_tmul_one hθ τ b₀)
      have r1 := Complex.conj_eq_iff_im.1 (conj_tmul_one hθ τ b₁)
      generalize θ τ (b₀ ⊗ₜ[D.host.F] (1 : D.host.E)) = p at *
      generalize θ τ (b₁ ⊗ₜ[D.host.F] (1 : D.host.E)) = q at *
      generalize Real.sqrt D.host.d = s at *
      have e1 := congrArg Complex.re e
      have e2 := congrArg Complex.im e
      simp [r0, r1, hd.ne'] at e1 e2
      exact ⟨Complex.ext e1 r0, Complex.ext e2 r1⟩
    have z0 := h0 b₀ fun τ => (key τ).1
    have z1 := h0 b₁ fun τ => (key τ).2
    rw [z0, z1] at hb
    exact adele_tensor_ext a (hb.trans (zero_tmul_add _ _)) hf

end GlobalTheory.FockCompare.RealChart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isArchimedeanAdeleChart_of_real_chart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ → (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) → (∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0) → ∃ σ : (D.what₂.Tau → ℂ) →+ AE D, Chart θ σ := by
  first | exact @GlobalTheory.FockCompare.RealChart.exists_chart | exact GlobalTheory.FockCompare.RealChart.exists_chart | (intros; apply GlobalTheory.FockCompare.RealChart.exists_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.LiftUnitary

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {A B T : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem lift_abstract (φ : A →+* B) (p : T → A →+* ℂ) (s : (T → ℂ) → A) (c : A →+* A) (cB : B →+* B)
    (hfin : ∀ z, φ (s z) = 0) (hcomp : ∀ z τ, p τ (s z) = z τ)
    (hext : ∀ a, φ a = 0 → (∀ τ, p τ a = 0) → a = 0)
    (hc : ∀ a, φ (c a) = cB (φ a)) (hp : ∀ τ a, p τ (c a) = starRingEnd ℂ (p τ a))
    (J : Matrix n n A) (hJ : ∀ τ, (J.map (p τ)).det ≠ 0) (g : T → Matrix n n ℂ)
    (hg : ∀ τ, (g τ)ᴴ * J.map (p τ) * g τ = J.map (p τ)) :
    ∃ k : GL n A, k ∈ Formalism.UG.UJ c J ∧ Formalism.UG.bc φ k = 1 ∧ ∀ τ, (k : Matrix n n A).map (p τ) = g τ := by
  let m : (T → Matrix n n ℂ) → Matrix n n A := fun g => 1 + Matrix.of fun i j => s fun τ => (g τ - 1) i j
  have m1 : ∀ g, (m g).map φ = 1 := by
    intro g; ext i j
    simp only [m, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add (f := _), hfin, add_zero, Matrix.one_apply]
    split_ifs <;> simp
  have m2 : ∀ g τ, (m g).map (p τ) = g τ := by
    intro g τ; ext i j
    simp only [m, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add (f := _), hcomp, Matrix.sub_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have mext : ∀ x y : Matrix n n A, x.map φ = y.map φ → (∀ τ, x.map (p τ) = y.map (p τ)) → x = y := by
    intro x y h1 h2
    ext i j
    rw [← sub_eq_zero]
    refine hext _ ?_ fun τ => ?_
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun h1 i) j
    · rw [map_sub, sub_eq_zero]; exact congrFun (congrFun (h2 τ) i) j
  have hdet : ∀ τ, IsUnit (g τ).det := by
    intro τ
    rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg Matrix.det (hg τ)
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact hJ τ this.symm
  have o1 : (1 : Matrix n n A).map φ = 1 := Matrix.map_one _ (map_zero φ) (map_one φ)
  have o2 : ∀ τ, (1 : Matrix n n A).map (p τ) = 1 := fun τ => Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨m g, m fun τ => (g τ)⁻¹, ?_, ?_⟩, ?_, ?_, m2 g⟩
  · refine mext _ _ ?_ fun τ => ?_
    · rw [Matrix.map_mul, m1, m1, o1, Matrix.one_mul]
    · rw [Matrix.map_mul, m2, m2, o2, Matrix.mul_nonsing_inv _ (hdet τ)]
  · refine mext _ _ ?_ fun τ => ?_
    · rw [Matrix.map_mul, m1, m1, o1, Matrix.one_mul]
    · rw [Matrix.map_mul, m2, m2, o2, Matrix.nonsing_inv_mul _ (hdet τ)]
  · show Formalism.UG.cT c (m g) * J * m g = J
    refine mext _ _ ?_ fun τ => ?_
    · have e : (Formalism.UG.cT c (m g)).map φ = Formalism.UG.cT cB ((m g).map φ) := by
        ext i j; exact hc _
      rw [Matrix.map_mul, Matrix.map_mul, e, m1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
    · have e : (Formalism.UG.cT c (m g)).map (p τ) = ((m g).map (p τ))ᴴ := by
        ext i j; exact hp τ _
      rw [Matrix.map_mul, Matrix.map_mul, e, m2, hg]
  · apply Units.ext
    exact m1 g

end Abstract

theorem snd_sigR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (sigR (AF F) σ z) =
      sigR (Af F) σ ((Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul a x => rfl

theorem lift_unitary (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ) (V : HSp D)
    (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ∃ k ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = g τ := by
  have hJ : ∀ τ, (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
    intro τ; ext i j; exact comp_incA h.inf τ _
  obtain ⟨k, hk, hf, hi⟩ := lift_abstract (finPart D) (fun τ => (θ τ).comp (infPart D)) σ (cA D)
    (sigR (Af D.host.F) D.sp.cm.sig) h.fin h.comp h.ext (snd_sigR D.sp.cm.sig) (comp_cA h.inf)
    (V.gram.map (incA D))
    (fun τ => by
      rw [hJ]
      have e : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
      rw [e]
      exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))
    g (fun τ => by rw [hJ]; exact hg τ)
  exact ⟨⟨k, hk⟩, hf, hi⟩

end GlobalTheory.FockCompare.LiftUnitary

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_point_unitary_with_components : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) → ∃ k ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = g τ := by
  first | exact @GlobalTheory.FockCompare.LiftUnitary.lift_unitary | exact GlobalTheory.FockCompare.LiftUnitary.lift_unitary | (intros; apply GlobalTheory.FockCompare.LiftUnitary.lift_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder Topology

namespace GlobalTheory.FockCompare.ThetaCont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem infPart_eq_zero (h : Chart θ σ) (a : AE D) (ha : ∀ τ, θ τ (infPart D a) = 0) : infPart D a = 0 := by
  let e : AF D.host.F := ((1 : Ainf D.host.F), (0 : Af D.host.F))
  let E : AE D := e ⊗ₜ[D.host.F] (1 : D.host.E)
  have h1 : infPart D E = 1 := rfl
  have h2 : finPart D E = 0 := by
    show (0 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  have h3 : infPart D (E * a) = infPart D a := by rw [RingHom.map_mul, h1, one_mul]
  have h4 : E * a = 0 := h.ext _ (by rw [RingHom.map_mul, h2, zero_mul]) fun τ => by rw [h3]; exact ha τ
  rw [← h3, h4, RingHom.map_zero]

theorem continuous_conj : Continuous (cA D) := by
  let f : AE D →ₐ[AF D.host.F] AE D :=
    Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig
  exact IsModuleTopology.continuous_of_linearMap f.toLinearMap

theorem continuous_hHom (V W : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WA V W} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => hHom V W (x t) (y t) := by
  have hx' : ∀ i j, Continuous fun t => cA D (x t i j) := fun i j =>
    continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp hx))
  have hy' : ∀ i j, Continuous fun t => y t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hy)
  unfold hHom
  split_ifs <;>
    exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => (((hx' _ _).mul continuous_const).mul continuous_const).mul (hy' _ _)

theorem continuous_symplH (V W : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WA V W} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplH V W (x t) (y t) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul (continuous_hHom V W hy hx)))

theorem continuous_of_level_of_smooth (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (V W : HSp D) (f : WA V W → ℂ)
    (hU : ∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f)
    (hs : Sm (iotaW σ V W) f) : Continuous f := by
  obtain ⟨U, hUo, hU⟩ := hU
  have : IsTopologicalAddGroup (AE D) := IsTopologicalRing.isTopologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  haveI : ContinuousSub (WA V W) := IsTopologicalAddGroup.to_continuousSub
  refine continuous_iff_continuousAt.2 fun w => ?_
  let x : WA V W → RW V W := fun w' => piW θ V W (w' - w)
  let a : WA V W → WA V W := fun w' => w + iotaW σ V W (x w')
  let u : WA V W → WA V W := fun w' => w' - a w'
  have hx : Continuous x := (continuous_pi' h.inf V W).comp (continuous_id.sub continuous_const)
  have ha : Continuous a := continuous_const.add ((h.continuous_iota V W).comp hx)
  have hu : Continuous u := continuous_id.sub ha
  have huw : u w = 0 := by
    show w - (w + iotaW σ V W (piW θ V W (w - w))) = 0
    rw [sub_self, AddMonoidHom.map_zero, AddMonoidHom.map_zero, add_zero, sub_self]
  have hinf : ∀ w', (u w').map (infPart D) = 0 := by
    intro w'
    have hp : piW θ V W (u w') = 0 := by
      show piW θ V W (w' - (w + iotaW σ V W (piW θ V W (w' - w)))) = 0
      rw [← sub_sub, AddMonoidHom.map_sub, h.pi_iota, sub_self]
    ext i j
    exact infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  have hg : Continuous fun w' => ψ (-symplH V W (a w') (u w')) * f (a w') :=
    (hψ.comp (continuous_symplH V W ha hu).neg).mul ((hs w).continuous.comp hx)
  have hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U :=
    hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))
  refine hg.continuousAt.congr (hev.mono fun w' hw' => ?_)
  have e := congrFun (hU _ hw' (hinf w')) (a w')
  have e2 : a w' + u w' = w' := add_sub_cancel _ _
  show ψ (-symplH V W (a w') (u w')) * f (a w') = f w'
  rw [← e]
  show _ * (ψ (symplH V W (a w') (u w')) * f (a w' + u w')) = _
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.FockCompare.ThetaCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmoothStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_of_heisenberg_level_and_smooth : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), Continuous ψ → ∀ (V W : HSp D) (f : WA V W → ℂ), (∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f) → Sm (iotaW σ V W) f → Continuous f := by
  first | exact @GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth | exact GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth | (intros; apply GlobalTheory.FockCompare.ThetaCont.continuous_of_level_of_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmType
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmType
noncomputable section

namespace GlobalTheory.FockCompare

section General

open NumberField GlobalTheory.InfAdeleCM
open scoped TensorProduct

theorem exists_real_chart_general {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {I : Type}
    (σ : I → (F →+* ℂ)) (hb : Function.Bijective fun i => InfinitePlace.mk (σ i)) :
    ∃ ρ : (I → ℝ) →+ InfiniteAdeleRing F, Continuous ρ ∧ (∀ x i, ext (σ i) (ρ x) = (x i : ℂ)) ∧
      ∀ a : InfiniteAdeleRing F, (∀ i, ext (σ i) a = 0) → a = 0 := by
  let e : I ≃ InfinitePlace F := Equiv.ofBijective _ hb
  let r : ∀ v : InfinitePlace F, v.Completion ≃+* ℝ := fun v =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hr : ∀ v, Continuous (r v).symm := fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous
  refine ⟨{ toFun := fun x v => (r v).symm (x (e.symm v))
            map_zero' := funext fun v => map_zero (r v).symm
            map_add' := fun x y => funext fun v => map_add (r v).symm _ _ }, ?_, ?_, ?_⟩
  · exact continuous_pi fun v => (hr v).comp (continuous_apply _)
  · intro x i
    rw [ext_eq_ofReal]
    congr 1
    have h := (r (e i)).apply_symm_apply (x (e.symm (e i)))
    refine Eq.trans h ?_
    rw [e.symm_apply_apply]
  · intro a ha
    funext v
    obtain ⟨i, rfl⟩ := hb.2 v
    exact (InfinitePlace.Completion.extensionEmbedding _).injective ((ha i).trans (map_zero _).symm)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_real_chart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) → ∃ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ ∧ (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) ∧ ∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0 := by
  intro D θ hθ hb
  haveI := D.sp.cm.totReal
  obtain ⟨ρ, h1, h2, h3⟩ := exists_real_chart_general (F := D.host.F)
    (fun τ : D.what₂.Tau => (tauE D τ).comp (algebraMap D.host.F D.host.E)) hb
  have key : ∀ τ (a : Ainf D.host.F), θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) =
      GlobalTheory.InfAdeleCM.ext ((tauE D τ).comp (algebraMap D.host.F D.host.E)) a := fun τ a => by
    have := GlobalTheory.InfAdeleCM.hom_tmul (tauE D τ) (θ τ) (hθ τ).1 (hθ τ).2 a 1
    rw [RingHom.map_one, mul_one] at this
    exact this
  exact ⟨ρ, h1, fun x τ => (key τ _).trans (h2 x τ), fun a ha => h3 a fun τ => (key τ a).symm.trans (ha τ)⟩

end GlobalTheory.FockCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_chart_infiniteAdeles_cmType : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) → ∃ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ ∧ (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) ∧ ∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0 := by
  first | exact @GlobalTheory.FockCompare.exists_real_chart | exact GlobalTheory.FockCompare.exists_real_chart | (intros; apply GlobalTheory.FockCompare.exists_real_chart <;> assumption)
end
end
