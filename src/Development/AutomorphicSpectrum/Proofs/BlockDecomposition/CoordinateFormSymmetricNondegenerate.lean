module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursProductInterleave

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerate
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem traceGram_isSymm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l))).IsSymm := by
  have hσ : ∀ e, σ (σ e) = e := sig_invol hCM
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  ext k l
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have h := Algebra.trace_eq_of_algEquiv s (b l * σ (b k))
  have hs : s (b l * σ (b k)) = b k * σ (b l) := by
    show σ (b l * σ (b k)) = b k * σ (b l)
    rw [map_mul, hσ, mul_comm]
  rw [hs] at h
  exact h.symm ▸ rfl

theorem traceGram_det_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l))).det ≠ 0 := by
  have hσ : ∀ e, σ (σ e) = e := sig_invol hCM
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  intro h0
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  set y : E := ∑ l, v l • b l with hy
  have hk : ∀ k, Algebra.trace F E (b k * σ y) = 0 := by
    intro k
    have := congrFun hmul k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum, Finset.mul_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hsm : σ (v l • b l) = v l • σ (b l) := by
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def]
    rw [hsm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hz : ∀ x, Algebra.traceForm F E (σ y) x = 0 := by
    intro x
    rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Algebra.traceForm_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_comm (σ y), hk, smul_zero]
  have hσy : σ y = 0 := (traceForm_nondegenerate F E).1 _ hz
  have hy0 : y = 0 := by rw [← hσ y, hσy, map_zero]
  have := (Fintype.linearIndependent_iff.1 b.linearIndependent) v hy0
  exact funext this

theorem coordForm_isSymm_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), (coordForm σ b n).IsSymm ∧ (coordForm σ b n).det ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM d b n
  constructor
  · refine Matrix.IsSymm.fromBlocks (Matrix.isSymm_one) (by simp) ?_
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    congr 1
    funext _
    exact traceGram_isSymm hCM b
  · unfold coordForm
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => traceGram_det_ne_zero hCM b

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerateStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_form_symmetric_nondegenerate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), (coordForm σ b n).IsSymm ∧ (coordForm σ b n).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPairingInCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPairingInCoordinates
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_mul_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x y : E) :
    Algebra.trace F E (σ x * y) = Algebra.trace F E (x * σ y) := by
  have hinv : Function.Involutive σ := GlobalTheory.CompanionTheory.SiegelND.Coef.sig_invol h
  have key := Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective σ hinv.bijective) (σ x * y)
  rw [← key]
  simp [hinv x]

theorem trace_sigR_mul {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (u w : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * w) =
      ∑ k, (Algebra.TensorProduct.basis R b).repr u k *
        ∑ l, algebraMap F R (Algebra.trace F E (b k * σ (b l))) * (Algebra.TensorProduct.basis R b).repr w l := by
  set C := Algebra.TensorProduct.basis R b with hC
  have hC' : ∀ (r : R) (k : Fin d), r • C k = r ⊗ₜ[F] b k := by
    intro r k
    simp [hC, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  conv_lhs => rw [← C.sum_repr u, ← C.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hC', map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hs : sigR R σ (C.repr u k ⊗ₜ[F] b k) = C.repr u k ⊗ₜ[F] σ (b k) := by simp [sigR]
  rw [hs, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.GaussMean.OneVec.trace_tmul, trace_mul_sig h]
  ring

theorem mulVec_inl (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (v : Idx n d → R) (i : Fin n) :
    (((coordForm σ b n).map (algebraMap F R)).mulVec v) (Sum.inl i) = v (Sum.inl i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, coordForm, Matrix.one_apply]

theorem mulVec_inr (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (v : Idx n d → R) (k : Fin d)
    (q : {p : Fin n × Fin n // p.1 < p.2}) :
    (((coordForm σ b n).map (algebraMap F R)).mulVec v) (Sum.inr (k, q)) =
      ∑ l, algebraMap F R (Algebra.trace F E (b k * σ (b l))) * v (Sum.inr (l, q)) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, coordForm, Matrix.map_apply,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, map_zero, zero_mul,
    Finset.sum_const_zero, zero_add, Matrix.blockDiagonal_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single q]
  · simp
  · intro x _ hx
    simp [hx, Ne.symm hx]
  · simp

theorem pairHerm_eq_coordForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (n : ℕ) (S T : HermR R σ n),
    pairHerm R σ n S T = dotProduct (hCo R σ b S) (((coordForm σ b n).map (algebraMap F R)).mulVec (hCo R σ b T)) := by
  intro F E _ _ _ _ _ σ h R _ _ d b n S T
  rw [GlobalTheory.HermCoordEquiv.pair_eq R h S T]
  unfold GlobalTheory.HermSD.coordPair
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [mulVec_inl, Fintype.sum_prod_type, mulVec_inr]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [trace_sigR_mul h]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPairingInCoordinatesStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_pairing_in_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ) (S T : HermR R σ n), pairHerm R σ n S T = dotProduct (hCo R σ b S) (((coordForm σ b n).map (algebraMap F R)).mulVec (hCo R σ b T)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord.pairHerm_eq_coordForm | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord.pairHerm_eq_coordForm | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord.pairHerm_eq_coordForm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlotEmbeddingsExistStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorEmbeddingsExist
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def localization₂ (a b : ℕ) (w : Pl E) : (GLw a w × GLw b w) →* Hf E a b :=
  (locGL E a w).prodMap (locGL E b w)

theorem continuous_locP (w : Pl E) : Continuous (localization₂ (E := E) a b w) :=
  ((GlobalTheory.EulerTw.continuous_locGL_spl E a w).comp continuous_fst).prodMk
    ((GlobalTheory.EulerTw.continuous_locGL_spl E b w).comp continuous_snd)

theorem atW_locP (w : Pl E) (m : GLw a w × GLw b w) : atW w (localization₂ a b w m) = m :=
  Prod.ext (pLoc_locGL w m.1) (pLoc_locGL w m.2)

theorem component_localEmbedding_eq_one_of_ne {v w : Pl E} (h : v ≠ w) (m : GLw a w × GLw b w) : atW v (localization₂ a b w m) = 1 :=
  Prod.ext (pLoc_locGL_of_ne h m.1) (pLoc_locGL_of_ne h m.2)

theorem pc_thF_of_one {n : ℕ} {v : Pl E} {x : GL (Fin n) (Af E)}
    (h : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E v)) x = 1) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) = 1 := by
  refine (GlobalTheory.EulerTwU.pc_thF v x).trans ?_
  rw [h]
  exact (congrArg _ (map_one (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv v)))).trans (map_one _)

theorem component_conj_localEmbedding_eq_one_of_ne {v w : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ w) (m : GLw a w × GLw b w) :
    atW v (thP E a b (localization₂ a b w m)) = 1 := by
  exact Prod.ext (pc_thF_of_one (pLoc_locGL_of_ne h m.1)) (pc_thF_of_one (pLoc_locGL_of_ne h m.2))

def localEmb (a b : ℕ) {S : Set (Pl E)} : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b
  | .inl w => localization₂ a b w.1
  | .inr w => (thP E a b).comp (localization₂ a b w.1)

theorem continuous_factorEmb {S : Set (Pl E)} (i : Slot S) : Continuous (localEmb (E := E) a b i) := by
  rcases i with w | w
  · exact continuous_locP w.1
  · exact GlobalTheory.CompanionTheory.FinLevelTw.continuous_thP.comp (continuous_locP w.1)

theorem cp_factorEmb {S : Set (Pl E)} (i : Slot S) (m : GLw a i.pl × GLw b i.pl) : i.cp a b (localEmb a b i m) = m := by
  rcases i with w | w
  · exact atW_locP w.1 m
  · change atW w.1 (thP E a b (thP E a b (localization₂ a b w.1 m))) = m
    rw [GlobalTheory.CompanionTheory.FinLevelTw.thP_thP]
    exact atW_locP w.1 m

theorem cp_factorEmb_of_ne {S : Set (Pl E)} (hS : IsSection S) (i j : Slot S) (m : GLw a i.pl × GLw b i.pl) (hij : i ≠ j) :
    j.cp a b (localEmb a b i m) = 1 := by
  rcases i with w | w <;> rcases j with v | v
  · exact component_localEmbedding_eq_one_of_ne (fun h => hij (congrArg Sum.inl (Subtype.ext h.symm))) m
  · refine component_conj_localEmbedding_eq_one_of_ne (fun h => ?_) m
    exact GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS v.2.1 v.2.2 (h ▸ w.2)
  · refine component_conj_localEmbedding_eq_one_of_ne (fun h => ?_) m
    refine GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 ?_
    have h' : GlobalTheory.EulerTw.cPl E v.1 = w.1 := h
    rw [← h', GlobalTheory.CompanionTheory.SuppFinTw.cPl_cPl]
    exact v.2
  · change atW v.1 (thP E a b (thP E a b (localization₂ a b w.1 m))) = 1
    rw [GlobalTheory.CompanionTheory.FinLevelTw.thP_thP]
    exact component_localEmbedding_eq_one_of_ne (fun h => hij (congrArg Sum.inr (Subtype.ext h.symm))) m

theorem finGL_thF (n : ℕ) (k : GL (Fin n) (Af E)) :
    finGL E n (thF E n k) = thetaGL n (conjAd E) (finGL E n k) :=
  (GlobalTheory.ThetaPull.thetaA_finGL k).symm

end GlobalTheory.CompanionTheory.FinActS

theorem GlobalTheory.CompanionTheory.FinActS.exists_factorEmb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) {S : Set (Pl E)} (hS : IsSection S),
    ∃ e : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b,
      (∀ i, Continuous (e i)) ∧ (∀ (i : Slot S) m, i.cp a b (e i m) = m) ∧ (∀ (i j : Slot S) m, i ≠ j → j.cp a b (e i m) = 1) ∧
      (∀ (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inl w) m) = (embW a w.1 m.1, embW b w.1 m.2)) ∧
      ∀ (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inr w) m) = (embT a w.1 m.1, embT b w.1 m.2) := by
  intro E _ _ _ a b S hS
  refine ⟨localEmb a b, continuous_factorEmb, cp_factorEmb, fun i j m h => cp_factorEmb_of_ne hS i j m h, fun w m => rfl, fun w m => ?_⟩
  exact Prod.ext (finGL_thF a _) (finGL_thF b _)

end
end

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.position_embeddings_exist : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) {S : Set (Pl E)} (hS : IsSection S),
    ∃ e : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b,
      (∀ i, Continuous (e i)) ∧ (∀ (i : Slot S) m, i.cp a b (e i m) = m) ∧ (∀ (i j : Slot S) m, i ≠ j → j.cp a b (e i m) = 1) ∧
      (∀ (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inl w) m) = (embW a w.1 m.1, embW b w.1 m.2)) ∧
      ∀ (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inr w) m) = (embT a w.1 m.1, embT b w.1 m.2) := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.exists_factorEmb | exact GlobalTheory.CompanionTheory.FinActS.exists_factorEmb | (intros; apply GlobalTheory.CompanionTheory.FinActS.exists_factorEmb <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGl
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSumSubquotientProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductLanglandsSubquotientSegments
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspProdIrr
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSubquotientExtTensorRight
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdSubquot
open TensorProduct

section General
variable {G H V V' W W' : Type} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isSubquotient_extTensor_left {σ : Representation ℂ G V} {σ' : Representation ℂ G V'}
    (B : Representation ℂ H W) (h : IsSubquotient σ σ') :
    IsSubquotient (extTensor σ B) (extTensor σ' B) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap σ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_left B ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapLeft B f) :=
    LinearMap.rTensor_surjective W hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_extTensor_right {ρ : Representation ℂ H W} {ρ' : Representation ℂ H W'}
    (A : Representation ℂ G V) (h : IsSubquotient ρ ρ') :
    IsSubquotient (extTensor A ρ) (extTensor A ρ') := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_right A ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapRight A f) :=
    LinearMap.lTensor_surjective V hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_comp {L : Type} [Group L] {σ : Representation ℂ G V}
    {σ' : Representation ℂ G V'} (s : L →* G) (h : IsSubquotient σ σ') :
    IsSubquotient (σ.comp s) (σ'.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  let T : Subrepresentation (σ'.comp s) :=
    ⟨S.toSubmodule, fun x _ hv => S.apply_mem_toSubmodule (s x) hv⟩
  exact ⟨T, ⟨f.toLinearMap, fun x => f.isIntertwining' (s x)⟩, hf⟩

end General

theorem prod₂_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U U' W W' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U') (ρ : Representation ℂ (GL (Fin t) k) W) (ρ' : Representation ℂ (GL (Fin t) k) W'), IsSmooth σ' → IsSmooth ρ' → IsSubquotient σ σ' → IsSubquotient ρ ρ' → IsSubquotient (prod₂ σ ρ) (prod₂ σ' ρ') := by
  intro k _ _ _ _ r t U U' W W' _ _ _ _ _ _ _ _ σ σ' ρ ρ' hσ' hρ' hs hr
  have hext : IsSubquotient (extTensor σ ρ) (extTensor σ' ρ') :=
    (isSubquotient_extTensor_left ρ hs).trans (isSubquotient_extTensor_right σ' hr)
  have hsm : IsSmooth ((extTensor σ' ρ').comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor hσ' hρ') _
      (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
        (continuous_apply false).prodMk (continuous_apply true))
  exact GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ _ _ _ _ _ hsm
    (isSubquotient_comp _ hext)

end GlobalTheory.CompanionTheory.ProdSubquot
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.Ysupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_of_prod₂_equiv {r t : ℕ} {U W A B C D : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U} {ρ : Representation ℂ (GL (Fin t) k) W}
    {α : Representation ℂ (GL (Fin r) k) A} {β : Representation ℂ (GL (Fin t) k) B}
    {γ : Representation ℂ (GL (Fin (r + t)) k) C} {δ : Representation ℂ (GL (Fin (r + t)) k) D}
    (hα : IsSmooth α) (hβ : IsSmooth β) (h₁ : IsSubquotient σ α) (h₂ : IsSubquotient ρ β)
    (E : (prod₂ σ ρ).Equiv δ) (F : (prod₂ α β).Equiv γ) : IsSubquotient δ γ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans
    ((GlobalTheory.CompanionTheory.ProdSubquot.prod₂_isSubquotient k r t U A W B σ α ρ β hα hβ h₁ h₂).trans
      (.of_injective F.toIntertwiningMap F.toLinearEquiv.injective))

end GlobalTheory.CompanionTheory.Ysupp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductLanglandsSubquotientSegments
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.LProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLSeg_append {p q : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (Δ₁ : Fin p → Segment k)
    (Δ₂ : Fin q → Segment k) (h₁ : ∀ i, IsLSeg (Δ₁ i) (x i).rep) (h₂ : ∀ i, IsLSeg (Δ₂ i) (y i).rep)
    (i : Fin (p + q)) : IsLSeg (Fin.append Δ₁ Δ₂ i) (Fin.append x y i).rep := by
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left, Fin.append_left]; exact h₁ i
  | right i => rw [Fin.append_right, Fin.append_right]; exact h₂ i

theorem map_append {p q : ℕ} (Δ₁ : Fin p → Segment k) (Δ₂ : Fin q → Segment k) :
    Finset.univ.val.map (Fin.append Δ₁ Δ₂) = Finset.univ.val.map Δ₁ + Finset.univ.val.map Δ₂ := by
  rw [Fin.univ_val_map, Fin.univ_val_map, Fin.univ_val_map, List.ofFn_fin_append]
  rfl

theorem prod₂_isSubquotient_append {r t p q : ℕ} {U W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) U) (ρ : Representation ℂ (GL (Fin t) k) W)
    (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hd : ∑ i, (Fin.append x y i).1 = r + t) (h₁ : IsSubquotient σ (prodIrr x hx))
    (h₂ : IsSubquotient ρ (prodIrr y hy)) : IsSubquotient (prod₂ σ ρ) (prodIrr (Fin.append x y) hd) := by
  obtain ⟨F⟩ := GlobalTheory.T.product_irreducible_append_equiv k p q r t x y hx hy hd
  exact GlobalTheory.CompanionTheory.Ysupp.isSubquotient_of_prod₂_equiv (isSmooth_prodIrr _ _) (isSmooth_prodIrr _ _)
    h₁ h₂ (Representation.Equiv.refl _) F

end GlobalTheory.CompanionTheory.LProd

theorem GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL (k := k)), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  intro k _ _ _ _ _ 𝔪 𝔫 a b ha hb
  obtain ⟨p, x, hx, ⟨Δ₁, hO₁, hL₁⟩, hc₁⟩ := ha
  obtain ⟨q, y, hy, ⟨Δ₂, hO₂, hL₂⟩, hc₂⟩ := hb
  have hd : ∑ i, (Fin.append x y i).1 = a.1 + b.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hx, hy]
  refine ⟨p + q, Fin.append x y, Fin.append Δ₁ Δ₂, hd, GlobalTheory.CompanionTheory.LProd.isLSeg_append x y Δ₁ Δ₂ hL₁ hL₂, ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.LProd.map_append, hO₁.1, hO₂.1]
  · exact GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_append _ _ x y hx hy hd hc₁.isSubquotient hc₂.isSubquotient

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductLanglandsSubquotientSegmentsStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_langlands_subquotient_segments : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (a b : IrrGL (k := k)), IsL 𝔪 a.rep → IsL 𝔫 b.rep → ∃ (h : ℕ) (z : Fin h → IrrGL (k := k)) (Δ : Fin h → Segment k) (hd : ∑ i, (z i).1 = a.1 + b.1), (∀ i, IsLSeg (Δ i) (z i).rep) ∧ Finset.univ.val.map Δ = 𝔪 + 𝔫 ∧ IsSubquotient (prod₂ a.rep b.rep) (prodIrr z hd) := by
  first | exact @GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg | exact GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg | (intros; apply GlobalTheory.CompanionTheory.LProd.prod₂_isSubquotient_prodIrr_lseg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSumSubquotientProduct
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LangSumSub

theorem isL_of_exhaust {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hEx : ∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) {N : ℕ} (τ : IrrRep (GL (Fin N) k)) :
    ∃ 𝔭 : Multiset (Segment k), IsL 𝔭 τ.ρ := by
  obtain ⟨𝔭, h𝔭⟩ := hEx (IrrGL.of τ.ρ τ.smooth τ.irr)
  exact ⟨𝔭, h𝔭.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irr).symm⟩


set_option maxHeartbeats 1000000 in
theorem isSubquotient_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k)
    (hSeg : LSegJacquet k) (hFree : LOrderFree k) (hEx : ∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep)
    (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1)
    (h0 : IsL 𝔪 (x 0).rep) (h1 : IsL 𝔫 (x 1).rep) (hy : IsL (𝔪 + 𝔫) y.rep) : IsSubquotient y.rep (prodIrr x hd) := by
  obtain ⟨n, c⟩ := y
  obtain rfl : (x 0).1 + (x 1).1 = n := (Fin.sum_univ_two _).symm.trans hd
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr_rep x hd
  have hPs : IsSmooth (prodIrr x hd) := isSmooth_prodIrr x hd
  have hPf := GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd
  obtain ⟨h₁, h₂, h, Δ₁, Δ₂, Δ, hΔ₁, hΔ₂, hΔ, hI⟩ := GlobalTheory.T.ordered_forms_interleave_sum hA 𝔪 𝔫
  have w0 : Wd (x 0).rep (wtW Δ₁) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔪 (x 0).rep h0 h₁ Δ₁ hΔ₁
  have w1 : Wd (x 1).rep (wtW Δ₂) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔫 (x 1).rep h1 h₂ Δ₂ hΔ₂
  have wp : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Δ) :=
    GlobalTheory.T.word_occurs_product_interleave hA (x 0) (x 1) _ _ _ (GlobalTheory.T.ordered_word_letters_cuspidal Δ₁) (GlobalTheory.T.ordered_word_letters_cuspidal Δ₂) w0 w1 hI
  have wP : Wd (prodIrr x hd) (wtW Δ) := GlobalTheory.T.word_occurs_of_subquotient (prodIrr x hd) (prod₂ (x 0).rep (x 1).rep) hPs
    (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) _ wp
  have hτ := GlobalTheory.T.word_occurs_irreducible_subquotient hA (prodIrr x hd) hPs hPf (wtW Δ) wP
  obtain ⟨τ, hτP, hτW⟩ := hτ
  obtain ⟨𝔭, hτL⟩ := isL_of_exhaust hEx τ
  obtain ⟨h', z, hz, ⟨Γ, hΓ, hzL⟩, hcos⟩ := id hτL
  have s1 : InShW 𝔭 (wtW Δ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z hz Γ hzL (wtW Δ) (GlobalTheory.T.ordered_word_letters_cuspidal Δ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z hz) hcos.isSubquotient _ hτW)
    rwa [hΓ.1] at this
  have wΓ : Wd τ.ρ (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA hSoc hSeg 𝔭 τ.ρ hτL h' Γ hΓ
  have wΓP : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ hPs hτP _ wΓ
  have wΓ2 : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prod₂ _ _)
    (.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective) _ wΓP
  obtain ⟨h'', z', Δ', hz', hz'L, hmap, hsub⟩ := GlobalTheory.T.product_langlands_subquotient_segments hA 𝔪 𝔫 (x 0) (x 1) h0 h1
  have s2 : InShW (𝔪 + 𝔫) (wtW Γ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z' hz' Δ' hz'L (wtW Γ) (GlobalTheory.T.ordered_word_letters_cuspidal Γ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z' hz') hsub _ wΓ2)
    rwa [hmap] at this
  have he : 𝔪 + 𝔫 = 𝔭 := GlobalTheory.T.ordered_forms_mutual_shuffle_eq hA (𝔪 + 𝔫) 𝔭 h h' Δ Γ hΔ hΓ s1 s2
  obtain ⟨ψ⟩ := GlobalTheory.T.langlands_classification_order_free_equiv hFree (𝔪 + 𝔫) τ.ρ (IrrGL.rep ⟨_, c⟩) (he ▸ hτL) hy
  exact (IsSubquotient.of_surjective ψ.toIntertwiningMap ψ.toLinearEquiv.surjective).trans hτP

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k →
    (∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) →
    ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1),
      IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) :=
  fun hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy =>
    isSubquotient_prodIrr hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy

end GlobalTheory.CompanionTheory.LangSumSub

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSumSubquotientProductStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_sum_subquotient_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k → (∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) → ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1), IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.LangSumSub.main | exact GlobalTheory.CompanionTheory.LangSumSub.main | (intros; apply GlobalTheory.CompanionTheory.LangSumSub.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGl
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LanglandsMultiseg

theorem langlandsMultisegments_of_clauses (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    (hSoc : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSocleGL k)
    (hSeg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSegJacquet k)
    (hFree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k)
    (hE : GlobalTheory.Published.LanglandsExhaustionGL) : GlobalTheory.Published.LanglandsMultisegments := by
  intro k _ _ _ _ _
  exact ⟨GlobalTheory.T.langlands_injective_of_socle hA (hSoc k) (hSeg k),
    fun 𝔪 𝔫 x y hd h₀ h₁ hy =>
      GlobalTheory.T.langlands_sum_subquotient_product hA (hSoc k) (hSeg k)
        (hFree k) (hE k) 𝔪 𝔫 x y hd h₀ h₁ hy⟩

end GlobalTheory.CompanionTheory.LanglandsMultiseg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsExhaustionGlStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_multisegments_of_exhaustion_gl : (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSocleGL k) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LSegJacquet k) → (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], LOrderFree k) → GlobalTheory.Published.LanglandsExhaustionGL → GlobalTheory.Published.LanglandsMultisegments := by
  first | exact @GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses | exact GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses | (intros; apply GlobalTheory.CompanionTheory.LanglandsMultiseg.langlandsMultisegments_of_clauses <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinThetaInvariance
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinThetaInvariance
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCellsTheta

theorem thetaInv : PositivityTheory.GramSchwartzFunctions.EC.ThetaInv := by
  intro D n V ψ χ θ μ ω hS
  let S : Subgroup (G D n) :=
    { carrier := {γ | ∀ Φ : schwartzA θ V.rank n,
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω γ Φ).1 (ξ.map (incA D)) =
          ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D))}
      one_mem' := fun Φ => by simp
      mul_mem' := fun {g h} hg hh Φ => by
        rw [map_mul, Module.End.mul_apply]
        exact (hg _).trans (hh Φ)
      inv_mem' := fun {g} hg Φ => by
        have := hg (ω g⁻¹ Φ)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        exact this.symm }
  have hle : GF D n ≤ S := GlobalTheory.T.rational_group_le_of_generators_mem D n S (fun g a hg Φ => GlobalTheory.T.theta_sum_invariant_levi_element D n V ψ χ θ μ ω hS g a hg Φ)
    (fun g b hg Φ => GlobalTheory.T.theta_sum_invariant_unipotent_translate D n V ψ χ θ μ ω hS g b hg Φ)
    (fun g hg Φ => GlobalTheory.T.theta_sum_invariant_weyl_involution D n V ψ χ θ μ ω hS g hg Φ)
  intro Φ γ hγ
  exact hle hγ Φ

end GlobalTheory.CompanionTheory.EisCellsTheta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinThetaInvarianceStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_theta_invariance : PositivityTheory.GramSchwartzFunctions.EC.ThetaInv := by
  first | exact @GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv | exact GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv | (intros; apply GlobalTheory.CompanionTheory.EisCellsTheta.thetaInv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralThetaMeasureFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralThetaMeasureFormula
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

variable {D : D7}

theorem trM_actW_ratTup (V : HSp D) {r : ℕ} (h : GA D V) (X : Fin r → Fin V.rank → D.host.E) :
    trM (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram h⁻¹ (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) X)) =
      HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((trM X).map (incA D)) := by
  ext i a
  rfl

def framesEquiv (V : HSp D) {r : ℕ} (T : Matrix (Fin r) (Fin r) D.host.E) :
    framesE D.sp.cm.sig V.gram T ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = T} where
  toFun X := ⟨trM X.1, (trM_mem_framesE_iff V X.1 T).1 X.2⟩
  invFun x := ⟨fun a i => x.1 i a, (trM_mem_framesE_iff V _ T).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem glue : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → ∀ β : HermE D r, Integrable (fun X => φ (trM X)) (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) ∧ IfrB V ν φ β = ∫ X, φ (trM X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) := by
  intro D r V θ hθ ν hν 𝓕 h𝓕 φ hφ habs β
  have : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hν
  have hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND D.sp.cm.sig V.gram := isHermND_gram V
  have hν' : HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν := hν
  have h𝓕' : HeckeCharacterZeroLocus.SiegelWeilU.IsFDH D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν 𝓕 := h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring _ _ D.sp.cm.sig hcm (AF D.host.F)
  have := hB r V.rank
  have hcont : Continuous φ :=
    (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have htr : Continuous (trM : (Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) → Mx D V.rank r) :=
    continuous_pi fun i => continuous_pi fun a =>
      (show Continuous fun X : Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E => X a i from
        (continuous_apply i).comp (continuous_apply a))
  set S := framesE D.sp.cm.sig V.gram β.1 with hS
  set Φ : (Fin r → Fin V.rank → AF D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => φ (trM X) with hΦdef
  have hΦ : Measurable Φ := (hcont.comp htr).measurable
  have hν0 : ν 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  have hinvtop : (ν 𝓕)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hν0
  have hL := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have habs' : ∫⁻ g in 𝓕, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν < ⊤ := by
    have e := GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure h𝓕 (descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ))
    simp only [hL.descend_mk] at e
    rw [← e]
    exact habs
  have hle : ∀ g : GA D V, ∑' X : S, ‖Φ (GlobalTheory.CompanionTheory.SW.actW (AF D.host.F) D.sp.cm.sig V.gram g⁻¹
      (HeckeCharacterZeroLocus.SiegelWeilU.ratTup (AF D.host.F) (X : Fin r → Fin V.rank → D.host.E)))‖ₑ ≤
      GlobalTheory.SiegelFormula.absTheta V φ g := fun g => by
    have hinj : Function.Injective fun X : S => trM (X : Fin r → Fin V.rank → D.host.E) :=
      fun X Y h => (framesEquiv V β.1).injective (Subtype.ext h)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V g ξ)‖ₑ))
    simp only [hΦdef, trM_actW_ratTup, GlobalTheory.SiegelFormula.invPt]
  have hint : Integrable Φ (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 S) := by
    refine ⟨hΦ.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ ν 𝓕 hν' h𝓕' r S _ hΦ.enorm]
    exact ENNReal.mul_lt_top hinvtop.lt_top ((lintegral_mono hle).trans_lt habs')
  refine ⟨hint, ?_⟩
  rw [← PositivityTheory.PlacePermOperatorBicommutantSpan.theta_int D.host.F D.host.E D.sp.cm.sig hcm V.rank V.gram hJ ν 𝓕 hν' h𝓕' r S Φ hΦ hint]
  have hInv := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
      (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
      (fun δ hδ ξ h => ⟨(Matrix.rank_mul_eq_right_of_isUnit_det _ _
        ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hth : ∀ g : GA D V, HeckeCharacterZeroLocus.SiegelWeilU.thetaS _ _ D.sp.cm.sig V.rank V.gram Φ S g =
      ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V g x.1) := fun g => by
    refine (tsum_congr fun X => ?_).trans ((framesEquiv V β.1).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V g x.1))
    exact congrArg φ (trM_actW_ratTup V g X.1)
  rw [IfrB, average_eq, GlobalTheory.AutomorphicL2Unitary.autMeasure, Measure.real, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕,
    GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
  have e1 : ∀ g : GA D V, descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) (GlobalTheory.AutomorphicL2Unitary.mk (GQ V) g) =
      HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram Φ S g :=
    fun g => (hInv.descend_mk g).trans (hth g).symm
  simp only [e1]
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralThetaMeasureFormulaStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_integral_theta_measure_formula : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → ∀ β : HermE D r, Integrable (fun X => φ (trM X)) (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) ∧ IfrB V ν φ β = ∫ X, φ (trM X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Frame.glue | exact GlobalTheory.CompanionTheory.WeilSiegel.Frame.glue | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Frame.glue <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupportAltBis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestTContinuousHasCompactSupport
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC

variable {F : Type} [Field F] [NumberField F]

def boxW (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v) :=
  {x | (v ∈ S → x ∈ U v) ∧ (v ∉ S → x ∈ v.adicCompletionIntegers F)}

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_integer _

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
  exact isCompact_iff_compactSpace.2 inferInstance

theorem isOpen_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsOpen (U v)) :
    IsOpen (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) := by
  have h1 : IsOpen {y : Af F | ∀ v ∈ S, y v ∈ U v} := by
    have : {y : Af F | ∀ v ∈ S, y v ∈ U v} = ⋂ v ∈ S, (fun y : Af F => y v) ⁻¹' U v := by
      ext y; simp
    rw [this]
    exact isOpen_biInter_finset fun v _ => (hU v).preimage (RestrictedProduct.continuous_eval v)
  have h2 : IsOpen {y : Af F | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => isOpen_integers v)
  exact h1.inter h2

theorem isCompact_boxW (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v))
    (v : HeightOneSpectrum (𝓞 F)) : IsCompact (boxW S U v) := by
  by_cases hv : v ∈ S
  · have : boxW S U v = U v := by
      ext x; simp [boxW, hv]
    rw [this]; exact hU v
  · have : boxW S U v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext x; simp [boxW, hv]
    rw [this]; exact isCompact_integers v

theorem isCompact_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v)) :
    IsCompact (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) := by
  haveI : ∀ v, CompactSpace (boxW S U v) := fun v => isCompact_iff_compactSpace.1 (isCompact_boxW S U hU v)
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal ((S : Set _)ᶜ) :=
    Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite
  let gP : (∀ v, boxW S U v) → RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => Fv F v)
      (fun v => (v.adicCompletionIntegers F : Set (Fv F v))) (Filter.principal ((S : Set _)ᶜ)) :=
    fun x => ⟨fun v => (x v).1, Filter.eventually_principal.2 fun v hv => (x v).2.2 (by simpa using hv)⟩
  have hgP : Continuous gP :=
    RestrictedProduct.isEmbedding_coe_of_principal.continuous_iff.2
      (continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v))
  let g : (∀ v, boxW S U v) → Af F := fun x => RestrictedProduct.inclusion _ _ hle (gP x)
  have hg : Continuous g := (RestrictedProduct.continuous_inclusion hle).comp hgP
  have hr : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U = Set.range g := by
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun v => ⟨y v, fun hv => h1 v hv, fun hv => h2 v hv⟩, by ext v; rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨fun v hv => (x v).2.1 hv, fun v hv => (x v).2.2 hv⟩
  rw [hr]
  exact isCompact_range hg

theorem isClopen_boxA (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, IsCompact (U v) ∧ IsOpen (U v)) :
    IsClopen (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) :=
  ⟨(isCompact_boxA S U fun v => (hU v).1).isClosed, isOpen_boxA S U fun v => (hU v).2⟩

theorem testT_continuous_hasCompactSupport : ∀ (F : Type) [Field F] [NumberField F] (ρ : Ainf F → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)),
    Continuous ρ → HasCompactSupport ρ → (∀ v, IsCompact (U v) ∧ IsOpen (U v)) →
    Continuous (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) ∧
      HasCompactSupport (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) := by
  intro F _ _ ρ S U hρ hρc hU
  have hB := isClopen_boxA S U hU
  have hBc := isCompact_boxA S U fun v => (hU v).1
  have hfst : Continuous (fun y : AF F => fstA F y) := continuous_fst
  have hsnd : Continuous (fun y : AF F => sndA F y) := continuous_snd
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT
    refine (Complex.continuous_ofReal.comp (hρ.comp hfst)).mul ?_
    exact (IsClopen.continuous_indicator hB continuous_const).comp hsnd
  · have hK : IsCompact ((tsupport ρ) ×ˢ (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) : Set (Ainf F × Af F)) :=
      hρc.isCompact.prod hBc
    refine HasCompactSupport.intro (K := ((tsupport ρ) ×ˢ (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U) : Set (Ainf F × Af F))) hK ?_
    intro y hy
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT
    by_cases h1 : sndA F y ∈ GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.boxA S U
    · have h2 : ρ (fstA F y) = 0 := by
        by_contra h3
        exact hy ⟨subset_tsupport ρ h3, h1⟩
      simp [h2]
    · simp [Set.indicator_of_notMem h1]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_and_hasCompactSupport_testT : ∀ (F : Type) [Field F] [NumberField F] (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), Continuous ρ → HasCompactSupport ρ → (∀ v, IsCompact (U v) ∧ IsOpen (U v)) → Continuous (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) ∧ HasCompactSupport (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport <;> assumption)
end
