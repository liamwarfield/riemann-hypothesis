module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductFubiniStatement

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphTensorProductMeasure
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphTensorProductMeasure
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HermSplit

abbrev Pairs (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def pairMap (n : ℕ) : Fin n ⊕ Pairs n → Pairs (n + 1)
  | .inl j => ⟨(0, j.succ), Fin.succ_pos j⟩
  | .inr p => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_lt_succ_iff.2 p.2⟩

theorem pairMap_bijective (n : ℕ) : Function.Bijective (pairMap n) := by
  constructor
  · rintro (j | ⟨⟨i, j⟩, h⟩) (j' | ⟨⟨i', j'⟩, h'⟩) hh <;>
      simp_all [pairMap, Subtype.ext_iff, Prod.ext_iff, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
  · rintro ⟨⟨i, j⟩, h⟩
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd h (lt_irrefl _)
      | succ j => exact ⟨.inl j, rfl⟩
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (Fin.not_lt_zero _)
      | succ j => exact ⟨.inr ⟨(i, j), Fin.succ_lt_succ_iff.1 h⟩, rfl⟩

def pairEquiv (n : ℕ) : Fin n ⊕ Pairs n ≃ Pairs (n + 1) := Equiv.ofBijective _ (pairMap_bijective n)

abbrev Coords (R K : Type) (n : ℕ) := (Fin n → R) × (Pairs n → K)

def splitE (R K : Type) (n : ℕ) : Coords R K (n + 1) ≃ R × (Fin n → K) × Coords R K n where
  toFun c := (c.1 0, fun j => c.2 (pairEquiv n (.inl j)), fun i => c.1 i.succ,
    fun p => c.2 (pairEquiv n (.inr p)))
  invFun q := ((Fin.cons q.1 q.2.2.1 : Fin (n + 1) → R),
    fun p => Sum.elim q.2.1 q.2.2.2 ((pairEquiv n).symm p))
  left_inv c := by
    refine Prod.ext ?_ ?_
    · funext i
      exact Fin.cases rfl (fun j => rfl) i
    · funext p
      obtain ⟨x, rfl⟩ := (pairEquiv n).surjective p
      rcases x with j | q <;> simp
  right_inv q := by
    obtain ⟨s, r, d, u⟩ := q
    simp

theorem splitE_symm_fst_zero {R K : Type} {n : ℕ} (q : R × (Fin n → K) × Coords R K n) :
    ((splitE R K n).symm q).1 0 = q.1 := rfl

theorem splitE_symm_fst_succ {R K : Type} {n : ℕ} (q : R × (Fin n → K) × Coords R K n) (i : Fin n) :
    ((splitE R K n).symm q).1 i.succ = q.2.2.1 i := rfl

theorem splitE_symm_snd_inl {R K : Type} {n : ℕ} (q : R × (Fin n → K) × Coords R K n) (j : Fin n) :
    ((splitE R K n).symm q).2 (pairEquiv n (.inl j)) = q.2.1 j := by
  simp [splitE]

theorem splitE_symm_snd_inr {R K : Type} {n : ℕ} (q : R × (Fin n → K) × Coords R K n) (p : Pairs n) :
    ((splitE R K n).symm q).2 (pairEquiv n (.inr p)) = q.2.2.2 p := by
  simp [splitE]

def splitH (R K : Type) [TopologicalSpace R] [TopologicalSpace K] (n : ℕ) :
    Coords R K (n + 1) ≃ₜ R × (Fin n → K) × Coords R K n where
  toEquiv := splitE R K n
  continuous_toFun := by
    refine ((continuous_apply 0).comp continuous_fst).prodMk
      ((continuous_pi fun j => (continuous_apply _).comp continuous_snd).prodMk
        ((continuous_pi fun i => (continuous_apply _).comp continuous_fst).prodMk
          (continuous_pi fun p => (continuous_apply _).comp continuous_snd)))
  continuous_invFun := by
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => ?_)
    · induction i using Fin.cases with
      | zero => exact continuous_fst
      | succ i =>
        exact (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))
    · rcases hx : (pairEquiv n).symm p with j | q
      · simp only [hx, Sum.elim_inl]
        exact (continuous_apply j).comp (continuous_fst.comp continuous_snd)
      · simp only [hx, Sum.elim_inr]
        exact (continuous_apply q).comp (continuous_snd.comp (continuous_snd.comp continuous_snd))

theorem shuffle_mp {A B C D : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace D] (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D) [SFinite a]
    [SFinite b] [SFinite c] [SFinite d] :
    MeasurePreserving (fun x : (A × B) × (C × D) => (x.1.1, x.2.1, x.1.2, x.2.2))
      ((a.prod b).prod (c.prod d)) (a.prod (c.prod (b.prod d))) := by
  have h1 := measurePreserving_prodAssoc a b (c.prod d)
  have h2 := (measurePreserving_prodAssoc b c d).symm MeasurableEquiv.prodAssoc
  have h3 : MeasurePreserving (Prod.map Prod.swap id) ((b.prod c).prod d) ((c.prod b).prod d) :=
    (Measure.measurePreserving_swap).prod (MeasurePreserving.id d)
  have h4 := measurePreserving_prodAssoc c b d
  have h5 := (MeasurePreserving.id a).prod (h4.comp (h3.comp h2))
  exact h5.comp h1

theorem splitE_mp {R K : Type} [MeasurableSpace R] [MeasurableSpace K] (lam : Measure R) (κ : Measure K)
    [SigmaFinite lam] [SigmaFinite κ] (n : ℕ) :
    MeasurePreserving (splitE R K n)
      ((Measure.pi fun _ : Fin (n + 1) => lam).prod (Measure.pi fun _ : Pairs (n + 1) => κ))
      (lam.prod ((Measure.pi fun _ : Fin n => κ).prod
        ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : Pairs n => κ)))) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => lam) 0
  have h2 := measurePreserving_arrowCongr' (fun _ : Pairs (n + 1) => κ)
    (fun _ : Fin n ⊕ Pairs n => κ) (pairEquiv n).symm (MeasurableEquiv.refl K)
    (fun _ => MeasurePreserving.id κ)
  have h3 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Pairs n => K)
    (fun _ : Fin n ⊕ Pairs n => κ)
  have h4 := h1.prod (h3.comp h2)
  have h5 := (shuffle_mp lam (Measure.pi fun _ : Fin n => lam) (Measure.pi fun _ : Fin n => κ)
    (Measure.pi fun _ : Pairs n => κ)).comp h4
  convert h5 using 1
  funext c
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · funext i
    show c.1 i.succ = c.1 (Fin.succAbove 0 i)
    simp
  · rfl

section Chart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R]

def coordOf (σ : E →ₐ[F] E) (n : ℕ) (S : HermR R σ n) : Coords R (R ⊗[F] E) n :=
  ((fun i : Fin n => algebraMap F R (1 / 2) *
      Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i)),
    (fun p : Pairs n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2))

def hermMat (σ : E →ₐ[F] E) (n : ℕ) (c : Coords R (R ⊗[F] E) n) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => if h : i < j then c.2 ⟨(i, j), h⟩ else
    if h' : j < i then sigR R σ (c.2 ⟨(j, i), h'⟩) else algebraMap R (R ⊗[F] E) (c.1 i)

theorem hermMat_mem (hσ : IsCMExt F E σ) (n : ℕ) (c : Coords R (R ⊗[F] E) n) :
    hermMat R σ n c ∈ HermR R σ n := by
  intro a b
  rcases lt_trichotomy a b with h | h | h
  · simp only [hermMat, dif_pos h, dif_neg (not_lt_of_gt h)]
    exact GlobalTheory.GaussMean.OneVec.sigR_sigR R hσ _
  · subst h
    simp only [hermMat, lt_irrefl, dif_neg, not_false_eq_true]
    exact GlobalTheory.GaussMean.OneVec.sigR_algebraMap R _
  · simp [hermMat, h, not_lt_of_gt h]

def chart (hσ : IsCMExt F E σ) (n : ℕ) : HermR R σ n ≃ Coords R (R ⊗[F] E) n where
  toFun := coordOf R σ n
  invFun c := ⟨hermMat R σ n c, hermMat_mem R hσ n c⟩
  left_inv S := by
    apply Subtype.ext
    funext i j
    rcases lt_trichotomy i j with h | h | h
    · simp [hermMat, coordOf, h]
    · subst h
      simpa [hermMat, coordOf] using GlobalTheory.GaussMean.OneVec.fixed_eq R hσ (S.2 i i)
    · simpa [hermMat, coordOf, h, not_lt_of_gt h] using S.2 i j
  right_inv c := by
    refine Prod.ext ?_ ?_
    · funext i
      simpa [hermMat, coordOf] using GlobalTheory.GaussMean.OneVec.half_trace R hσ (c.1 i)
    · funext p
      simp [hermMat, coordOf, p.2]

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_algebraMapK : Continuous (algebraMap R (R ⊗[F] E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have : (algebraMap R (R ⊗[F] E) : R → R ⊗[F] E) = fun r => r • (1 : R ⊗[F] E) := by
    funext r
    exact Algebra.algebraMap_eq_smul_one r
  rw [this]
  exact (continuous_id (X := R)).smul (continuous_const (y := (1 : R ⊗[F] E)))

def chartH (hσ : IsCMExt F E σ) (htr : Continuous (Algebra.trace R (R ⊗[F] E)))
    (hsig : Continuous (sigR R σ)) (n : ℕ) : HermR R σ n ≃ₜ Coords R (R ⊗[F] E) n where
  toEquiv := chart R hσ n
  continuous_toFun := by
    have hel : ∀ i j : Fin n, Continuous fun S : HermR R σ n =>
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => hel _ _)
    exact continuous_const.mul (htr.comp (hel i i))
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
    by_cases h : i < j
    · simp only [hermMat, dif_pos h]
      exact (continuous_apply _).comp continuous_snd
    · by_cases h' : j < i
      · simp only [hermMat, dif_neg h, dif_pos h']
        exact hsig.comp ((continuous_apply _).comp continuous_snd)
      · simp only [hermMat, dif_neg h, dif_neg h']
        exact (continuous_algebraMapK R).comp ((continuous_apply i).comp continuous_fst)

theorem hermMat_zero_zero (n : ℕ) (q : R × (Fin n → R ⊗[F] E) × Coords R (R ⊗[F] E) n) :
    hermMat R σ (n + 1) ((splitE R (R ⊗[F] E) n).symm q) 0 0 = q.1 ⊗ₜ[F] (1 : E) := by
  simp [hermMat, splitE_symm_fst_zero, Algebra.TensorProduct.algebraMap_apply]

theorem hermMat_zero_succ (n : ℕ) (q : R × (Fin n → R ⊗[F] E) × Coords R (R ⊗[F] E) n) (j : Fin n) :
    hermMat R σ (n + 1) ((splitE R (R ⊗[F] E) n).symm q) 0 j.succ = q.2.1 j := by
  have h : (0 : Fin (n + 1)) < j.succ := Fin.succ_pos j
  simp only [hermMat, dif_pos h]
  exact splitE_symm_snd_inl q j

theorem hermMat_succ_succ (n : ℕ) (q : R × (Fin n → R ⊗[F] E) × Coords R (R ⊗[F] E) n) (i j : Fin n) :
    hermMat R σ (n + 1) ((splitE R (R ⊗[F] E) n).symm q) i.succ j.succ = hermMat R σ n q.2.2 i j := by
  by_cases h : i < j
  · have h1 : i.succ < j.succ := Fin.succ_lt_succ_iff.2 h
    simp only [hermMat, dif_pos h, dif_pos h1]
    exact splitE_symm_snd_inr q ⟨(i, j), h⟩
  · have h1 : ¬ i.succ < j.succ := fun hh => h (Fin.succ_lt_succ_iff.1 hh)
    by_cases h' : j < i
    · have h2 : j.succ < i.succ := Fin.succ_lt_succ_iff.2 h'
      simp only [hermMat, dif_neg h, dif_neg h1, dif_pos h', dif_pos h2]
      exact congrArg _ (splitE_symm_snd_inr q ⟨(j, i), h'⟩)
    · have h2 : ¬ j.succ < i.succ := fun hh => h' (Fin.succ_lt_succ_iff.1 hh)
      simp only [hermMat, dif_neg h, dif_neg h1, dif_neg h', dif_neg h2]
      exact congrArg _ (splitE_symm_fst_succ q i)

end Chart

theorem herm_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ n : ℕ, ∃ e : (R × (Fin n → R ⊗[F] E) × HermR R σ n) ≃ₜ HermR R σ (n + 1), (∀ p, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 = p.1 ⊗ₜ[F] (1 : E)) ∧ (∀ p j, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 (Fin.succ j) = p.2.1 j) ∧ (∀ p i j, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (Fin.succ i) (Fin.succ j) = (p.2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j) ∧ (lam.prod ((Measure.pi fun _ => coordK R b lam).prod (coordHerm R σ b lam n))).map e = coordHerm R σ b lam (n + 1) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b lam hlam n
  obtain ⟨hKring, hKlc, hKsc, hKt2, hsig, htr, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hKring
  haveI := hKlc
  haveI := hKsc
  haveI := hKt2
  haveI := hlam
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI hκ := (GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam).1
  haveI hHerm : ∀ m, BorelSpace (HermR R σ m) := fun _ => ⟨rfl⟩
  let C := fun m => chartH (F := F) (E := E) (σ := σ) R hσ htr hsig m
  haveI hsc : ∀ m, SecondCountableTopology (HermR R σ m) := fun m => (C m).secondCountableTopology
  have hC : ∀ m, coordHerm R σ b lam m = ((Measure.pi fun _ : Fin m => lam).prod
      (Measure.pi fun _ : Pairs m => coordK R b lam)).map (C m).symm := by
    intro m
    ext s hs
    rw [(C m).symm.measurableEmbedding.map_apply]
    show Measure.comap (C m) _ s = _
    rw [(C m).measurableEmbedding.comap_apply]
    congr 1
    exact (C m).toEquiv.image_eq_preimage_symm s
  let e : (R × (Fin n → R ⊗[F] E) × HermR R σ n) ≃ₜ HermR R σ (n + 1) :=
    ((Homeomorph.refl R).prodCongr ((Homeomorph.refl _).prodCongr (C n))).trans
      ((splitH R (R ⊗[F] E) n).symm.trans (C (n + 1)).symm)
  refine ⟨e, fun p => ?_, fun p j => ?_, fun p i j => ?_, ?_⟩
  · exact hermMat_zero_zero (σ := σ) R n _
  · exact hermMat_zero_succ (σ := σ) R n _ j
  · refine (hermMat_succ_succ (σ := σ) R n _ i j).trans ?_
    have h := congrArg Subtype.val ((chart R hσ n).left_inv p.2.2)
    exact congrFun (congrFun h i) j
  · have hmp := splitE_mp lam (coordK R b lam) n
    have hmp2 : MeasurePreserving (C n).symm ((Measure.pi fun _ : Fin n => lam).prod
        (Measure.pi fun _ : Pairs n => coordK R b lam)) (((Measure.pi fun _ : Fin n => lam).prod
        (Measure.pi fun _ : Pairs n => coordK R b lam)).map (C n).symm) :=
      ⟨(C n).symm.continuous.measurable, rfl⟩
    have hmp4 := ((MeasurePreserving.id lam).prod
      ((MeasurePreserving.id (Measure.pi fun _ : Fin n => coordK R b lam)).prod hmp2)).comp hmp
    rw [hC n, hC (n + 1), ← hmp4.map_eq, Measure.map_map e.continuous.measurable hmp4.measurable]
    congr 1
    funext c
    have hq : (C n) ((C n).symm ((splitE R (R ⊗[F] E) n) c).2.2) = ((splitE R (R ⊗[F] E) n) c).2.2 :=
      (C n).apply_symm_apply _
    show (C (n + 1)).symm ((splitE R (R ⊗[F] E) n).symm (((splitE R (R ⊗[F] E) n) c).1,
      ((splitE R (R ⊗[F] E) n) c).2.1, (C n) ((C n).symm ((splitE R (R ⊗[F] E) n) c).2.2))) = _
    rw [hq]
    exact congrArg _ ((splitE R (R ⊗[F] E) n).symm_apply_apply c)

end GlobalTheory.CompanionTheory.SW.HermSplit
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphTensorProductMeasureStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_homeomorph_tensor_product_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ n : ℕ, ∃ e : (R × (Fin n → R ⊗[F] E) × HermR R σ n) ≃ₜ HermR R σ (n + 1), (∀ p, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 = p.1 ⊗ₜ[F] (1 : E)) ∧ (∀ p j, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 (Fin.succ j) = p.2.1 j) ∧ (∀ p i j, (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (Fin.succ i) (Fin.succ j) = (p.2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j) ∧ (lam.prod ((Measure.pi fun _ => coordK R b lam).prod (coordHerm R σ b lam n))).map e = coordHerm R σ b lam (n + 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermSplit.herm_split | exact GlobalTheory.CompanionTheory.SW.HermSplit.herm_split | (intros; apply GlobalTheory.CompanionTheory.SW.HermSplit.herm_split <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDisintegration
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDisintegration
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem lintegral_fibS_of_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ S hS
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨hKR, hKLC, hKSC, hKT2, -, -, -, hKB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  have := hKR
  have := hKLC
  have := hKSC
  have := hKT2
  obtain ⟨-, -, hHSC, -, hHB, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  have := hHSC
  have := hHB
  have := hKB (n + 1) (M + 1)
  have k₁ := (GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁).2.1
  have k' := (GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm').2.1
  have hact' := (hact (n + 1)).1
  have := k₁ (hermScal R σ (algebraMap F R t))
  have := k' (schur R σ t a S)
  have hvec : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E),
      Measurable (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X) := by
    intro A c
    refine Measurable.of_eval (fun i => ?_)
    induction i using Fin.cases with
    | zero =>
      have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X 0) =
          fun _ => Fin.cons A (fun _ => 0) := rfl
      rw [h0]
      exact measurable_const
    | succ j =>
      refine Measurable.of_eval (fun k => ?_)
      induction k using Fin.cases with
      | zero =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ 0) = fun _ => c j := rfl
        rw [h0]
        exact measurable_const
      | succ l =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ l.succ) =
            fun X => X j l := rfl
        rw [h0]
        exact (measurable_pi_apply l).comp (measurable_pi_apply j)
  have hf : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2)) := fun A c =>
    hact'.measurable.comp ((D.hs.comp measurable_fst).prodMk ((hvec A c).comp measurable_snd))
  have hg : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        φ (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2))) := fun A c =>
    hφ.comp (hf A c)
  have hfib := Set.indicator_of_mem hS (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2)))
  have hfib' : fibS σ J t m₁ m' s B₀ a κ₁ cm S = _ := hfib
  rw [hfib', lintegral_smul_measure, lintegral_map hφ (hf _ _),
    lintegral_prod _ (hg _ _).aemeasurable, ENNReal.smul_def, smul_eq_mul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductDisintegrationStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_lintegral_eq_scale_mul_Pint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_fibS_of_mem | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_fibS_of_mem | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_fibS_of_mem <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureConsProduct
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureConsProduct
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem pi_const_smul {ι X : Type} [Fintype ι] [MeasurableSpace X] (κ : Measure X) [SigmaFinite κ] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • κ) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => κ) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.smul_apply]
  rfl

theorem subst_row_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (u : Rˣ) (w : (Fin n → R ⊗[F] E) → HermR R σ n), Measurable w → ∀ f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞, Measurable f → ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) = (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j), S'' - w r) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D u w hw f hf
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ D.hCM R d b lam D.hlam
  haveI := hK
  haveI := hH n
  have hVU : ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) : R ⊗[F] E) *
      ((u : R) ⊗ₜ[F] (algebraMap F E t)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, inv_mul_cancel₀ D.ht, map_one, Units.inv_mul]
    rfl
  have hTm : Measurable (fun (r : Fin n → R ⊗[F] E) (j : Fin n) =>
      ((u : R) ⊗ₜ[F] (algebraMap F E t)) * r j) :=
    Measurable.of_eval fun j => (measurable_pi_apply j).const_mul _
  have hDm : Measurable (fun (r : Fin n → R ⊗[F] E) (j : Fin n) =>
      (((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j) :=
    Measurable.of_eval fun j => (measurable_pi_apply j).const_mul _
  have hmap : (Measure.pi fun _ : Fin n => coordK R b lam).map
      (fun (r : Fin n → R ⊗[F] E) (j : Fin n) => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * r j) =
      ((cm u : ℝ≥0∞) ^ n) • Measure.pi fun _ : Fin n => coordK R b lam := by
    have hm : ∀ _ : Fin n, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) =
        cm u • coordK R b lam := fun _ => D.hmod u
    have hsf : ∀ _ : Fin n, SigmaFinite ((coordK R b lam).map
        (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y)) := fun i => by
      rw [hm i]; infer_instance
    have h1 := Measure.pi_map_pi (X := fun _ : Fin n => R ⊗[F] E) (Y := fun _ : Fin n => R ⊗[F] E)
      (hμ := hsf) (μ := fun _ : Fin n => coordK R b lam)
      (f := fun _ y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y)
      (fun _ => (measurable_const_mul _).aemeasurable)
    rw [h1]
    simp only [D.hmod u]
    rw [pi_const_smul, Fintype.card_fin]
  have hh : Measurable (fun r : Fin n → R ⊗[F] E => ∫⁻ S'', f (fun j =>
      ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j), S'' - w r) ∂(coordHerm R σ b lam n)) := by
    refine Measurable.lintegral_prod_right' (f := fun p : (Fin n → R ⊗[F] E) × HermR R σ n =>
      f (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * p.1 j), p.2 - w p.1)) ?_
    exact hf.comp ((hDm.comp measurable_fst).prodMk (measurable_snd.sub (hw.comp measurable_fst)))
  have hsm : ∀ g : (Fin n → R ⊗[F] E) → ℝ≥0∞, ((cm u : ℝ≥0∞) ^ n) * ∫⁻ r, g r ∂(Measure.pi fun _ : Fin n => coordK R b lam) =
      ∫⁻ r, g r ∂(((cm u : ℝ≥0∞) ^ n) • Measure.pi fun _ : Fin n => coordK R b lam) := fun g => by
    rw [lintegral_smul_measure, smul_eq_mul]
  rw [hsm, ← hmap, lintegral_map hh hTm]
  refine lintegral_congr fun c => ?_
  have hc : (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) *
      (((u : R) ⊗ₜ[F] (algebraMap F E t)) * c j))) = c := by
    funext j
    rw [← mul_assoc, hVU, one_mul]
  rw [hc]
  exact (lintegral_sub_right_eq_self (fun S' => f (c, S')) _).symm

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureConsProductStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_coordK_coordHerm_scale_shear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (u : Rˣ) (w : (Fin n → R ⊗[F] E) → HermR R σ n), Measurable w → ∀ f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞, Measurable f → ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) = (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j), S'' - w r) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.subst_row_translate | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.subst_row_translate | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.subst_row_translate <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductPushforward
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Fold

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}

def qM (t : F) (c : Fin n → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => sigR R σ (c i) * inclR R (algebraMap F E t) * c j

theorem sigR_inclT (t : F) : sigR R σ (inclR R (algebraMap F E t)) = inclR R (algebraMap F E t) := by
  simp [sigR, inclR]

theorem qM_mem (hσ : IsCMExt F E σ) (t : F) (c : Fin n → R ⊗[F] E) : qM R σ t c ∈ HermR R σ n := by
  intro i j
  have h : sigR R σ (sigR R σ (c j)) = c j := GlobalTheory.GaussMean.OneVec.sigR_sigR R hσ _
  show sigR R σ (qM R σ t c j i) = qM R σ t c i j
  simp only [qM, map_mul, sigR_inclT, h]
  ring

theorem schurM_eq (t : F) (a : R → Rˣ) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))
    (i j : Fin n) : schurM R σ t a S i j = S i.succ j.succ - qM R σ t (cvec R t a S) i j := rfl

theorem schur_split (hσ : IsCMExt F E σ) (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1))
    (S'' : HermR R σ n)
    (h : ∀ i j, (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ =
      (S'' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j) :
    schur R σ t a S = S'' - ⟨qM R σ t (cvec R t a (S : Matrix _ _ _)), qM_mem R σ hσ t _⟩ := by
  have hm : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) =
      (S'' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - qM R σ t (cvec R t a (S : Matrix _ _ _)) := by
    funext i j
    rw [schurM_eq, h]
    rfl
  have hmem : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
    rw [hm]
    exact sub_mem S''.2 (qM_mem R σ hσ t _)
  apply Subtype.ext
  rw [schur_coe R σ t a S hmem, hm]
  rfl

theorem corner_half_trace_of_cm_pure_tensor (hσ : IsCMExt F E σ) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) (x : R)
    (h : S 0 0 = x ⊗ₜ[F] (1 : E)) : s0 R S = x := by
  have := GlobalTheory.GaussMean.OneVec.half_trace (F := F) (E := E) (σ := σ) R hσ x
  rw [Algebra.TensorProduct.algebraMap_apply] at this
  simpa [s0, h] using this

end Alg

theorem fold : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ S, ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) ∂(coordHerm R σ b lam (n + 1)) = Mid σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hσ := D.hCM
  have hlam := D.hlam
  haveI := hlam
  obtain ⟨hKring, hKlc, hKsc, hKt2, hsig, htr, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hKring
  haveI := hKlc
  haveI := hKsc
  haveI := hKt2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hκh, -, hνh⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam
  haveI := hκh
  haveI hHb : ∀ m, BorelSpace (HermR R σ m) := fun _ => ⟨rfl⟩
  haveI hHlc : ∀ m, LocallyCompactSpace (HermR R σ m) := fun m =>
    (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).1
  haveI hHsc : ∀ m, SecondCountableTopology (HermR R σ m) := fun m =>
    (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).2.1
  haveI : (coordHerm R σ b lam n).IsAddHaarMeasure := hνh n
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordHerm R σ b lam n) := inferInstance
  obtain ⟨e, he00, he0j, heij, hemap⟩ := GlobalTheory.T.coordinate_homeomorph_tensor_product_measure F E σ hσ R d b lam hlam n
  obtain ⟨hs0c, hacS, hcvc, hschc, hBopen⟩ :=
    GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  have hGon0 := GlobalTheory.T.gram_fiber_cons_lintegral_eq_scale_mul_Pint F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hmeas := GlobalTheory.T.measurable_Pint' F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hsubst := GlobalTheory.T.lintegral_coordK_coordHerm_scale_shear F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  have hUnt : IsOpen (Unt σ R n) :=
    (GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ hσ M n J D.hJ R D.hR d b lam hlam m' D.hm').1
  have hGoff0 : ∀ S, S ∉ Bset R σ t a B₀ →
      ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = 0 := by
    intro S hS
    have h0 : fibS σ J t m₁ m' s B₀ a κ₁ cm S = 0 := by
      unfold fibS
      exact Set.indicator_of_notMem hS _
    rw [h0, lintegral_zero_measure]
  obtain ⟨G, hG⟩ : ∃ G : HermR R σ (n + 1) → ℝ≥0∞,
      G = fun S => ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) := ⟨_, rfl⟩
  have hGoff : ∀ S, S ∉ Bset R σ t a B₀ → G S = 0 := by
    intro S hS
    rw [hG]
    exact hGoff0 S hS
  have hGon : ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), G S =
      (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) *
      (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n *
      Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R)
        (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
    intro S hS
    rw [hG]
    exact hGon0 S hS
  show ∫⁻ S, (fun S => ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S)) S ∂(coordHerm R σ b lam (n + 1)) = _
  rw [← hG]
  clear hGon0 hGoff0 hG
  have hGm : Measurable G := by
    refine measurable_of_restrict_of_restrict_compl hBopen.measurableSet ?_ ?_
    · have hsub : (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ⊆
          {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := fun S h => h.1
      have hk := continuousOn_iff_continuous_restrict.1 (hacS.mono hsub)
      have hc := continuousOn_iff_continuous_restrict.1 (hcvc.mono hsub)
      have hw := continuousOn_iff_continuous_restrict.1 (hschc.mono hsub)
      have hP := hmeas.comp (((Units.continuous_val.comp hk).prodMk (hc.prodMk hw)).measurable)
      have hE : (Bset R σ t a B₀ : Set (HermR R σ (n + 1))).domRestrict G = _ :=
        funext fun S => hGon S S.2
      rw [hE]
      exact (((ENNReal.continuous_coe.comp (D.hκc.comp hk)).measurable).mul
        (((ENNReal.continuous_coe.comp (D.hcmc.comp hk)).measurable).pow_const n)).mul hP
    · have hE : (Bset R σ t a B₀ : Set (HermR R σ (n + 1)))ᶜ.domRestrict G = fun _ => 0 :=
        funext fun S => hGoff S S.2
      rw [hE]
      exact measurable_const
  have hL : ∫⁻ S, G S ∂(coordHerm R σ b lam (n + 1)) =
      ∫⁻ x, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := by
    have hGe : Measurable (fun p => G (e p)) := hGm.comp e.continuous.measurable
    rw [← hemap, lintegral_map hGm e.continuous.measurable, lintegral_prod _ hGe.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact lintegral_prod _ (hGe.comp measurable_prodMk_left).aemeasurable
  have hs0 : ∀ p, s0 R (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = p.1 :=
    fun p => corner_half_trace_of_cm_pure_tensor R σ hσ _ _ (he00 p)
  have hoff : ∀ x, x ∉ B₀ → ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = 0 := by
    intro x hx
    have h0 : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) = 0 := by
      intro r S''
      refine hGoff _ fun h => hx ?_
      have h1 := h.1
      rwa [hs0] at h1
    simp [h0]
  have hon : ∀ x ∈ B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E,
        ∫⁻ S' in Unt σ R n, Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) := by
    intro x hx
    obtain ⟨u, hu⟩ : ∃ u : Rˣ, u = a x := ⟨_, rfl⟩
    rw [← hu]
    obtain ⟨cr, hcrdef⟩ : ∃ cr : (Fin n → R ⊗[F] E) → Fin n → R ⊗[F] E,
        cr = fun r j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j) := ⟨_, rfl⟩
    have hcr : Continuous cr := by
      rw [hcrdef]
      exact continuous_pi fun j => continuous_const.mul (continuous_apply j)
    let w : (Fin n → R ⊗[F] E) → HermR R σ n := fun r => ⟨qM R σ t (cr r), qM_mem R σ hσ t _⟩
    have hw : Measurable w := by
      have hwc : Continuous w := by
        refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
        exact ((hsig.comp ((continuous_apply i).comp hcr)).mul continuous_const).mul
          ((continuous_apply j).comp hcr)
      exact hwc.measurable
    let f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞ := fun z =>
      (Unt σ R n).indicator (fun S' => Pint σ J t m₁ m' s φ (u : R) z.1 S') z.2
    have hf : Measurable f := by
      have h1 : Measurable fun z : (Fin n → R ⊗[F] E) × HermR R σ n =>
          Pint σ J t m₁ m' s φ (u : R) z.1 z.2 :=
        hmeas.comp (measurable_const.prodMk measurable_id)
      exact h1.indicator (measurable_snd hUnt.measurableSet)
    have hpt : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) =
        ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r) := by
      intro r S''
      have h0 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x := hs0 _
      have h1 : cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = cr r := by
        funext j
        rw [hcrdef]
        show ((((a (s0 R _))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * _ = _
        rw [h0, he0j, ← hu]
      have h2 : schur R σ t a (e (x, r, S'')) = S'' - w r := by
        rw [schur_split R σ hσ t a (e (x, r, S'')) S'' (heij (x, r, S''))]
        have h3 : (⟨qM R σ t (cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))),
            qM_mem R σ hσ t _⟩ : HermR R σ n) = w r := Subtype.ext (congrArg (qM R σ t) h1)
        rw [h3]
      by_cases hU : S'' - w r ∈ Unt σ R n
      · have hB : e (x, r, S'') ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) :=
          ⟨by show s0 R _ ∈ B₀; rw [h0]; exact hx, by rw [h2]; exact hU⟩
        rw [hGon _ hB, h0, h1, h2, ← hu]
        simp only [f, Set.indicator_of_mem hU]
      · have hB : e (x, r, S'') ∉ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
          intro h
          have h3 := h.2
          rw [h2] at h3
          exact hU h3
        rw [hGoff _ hB]
        simp only [f, Set.indicator_of_notMem hU, mul_zero]
    have hC : ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hS : ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) =
        (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
      rw [hcrdef]
      exact hsubst u w hw f hf
    calc ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam)
        = ∫⁻ r, ∫⁻ S'', ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [hpt]
      _ = ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [lintegral_const_mul' _ _ hC]
      _ = (κ₁ u : ℝ≥0∞) * ((cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam)) := mul_assoc _ _ _
      _ = (κ₁ u : ℝ≥0∞) * ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by rw [hS]
      _ = _ := by
          congr 1
          refine lintegral_congr fun c => ?_
          exact lintegral_indicator hUnt.measurableSet (fun S' => Pint σ J t m₁ m' s φ (u : R) c S')
  rw [hL]
  unfold Mid
  calc _ = ∫⁻ x, B₀.indicator (fun x => ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam)) x ∂lam := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ B₀
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, hoff x hx]
    _ = ∫⁻ x in B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := lintegral_indicator D.hB₀.measurableSet _
    _ = _ := setLIntegral_congr_fun D.hB₀.measurableSet hon

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Fold
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductPushforwardStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_iterated_lintegral_eq_Mid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ S, ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) ∂(coordHerm R σ b lam (n + 1)) = Mid σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.Fold.fold | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.Fold.fold | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.Fold.fold <;> assumption)
end
