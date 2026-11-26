module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedDisintegrationComposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCellOpenIndependent

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorph
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorph
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split

abbrev UT (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

instance isEmpty_UT_one : IsEmpty (UT 1) :=
  ⟨fun p => absurd p.2 (by rw [Subsingleton.elim p.1.1 p.1.2]; exact lt_irrefl _)⟩

def utEquiv (n : ℕ) : Fin n ⊕ UT n ≃ UT (n + 1) :=
  Equiv.ofBijective
    (Sum.elim (fun j => ⟨(0, j.succ), Fin.succ_pos _⟩)
      (fun p => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_lt_succ_iff.2 p.2⟩))
    (by
      constructor
      · rintro (j | ⟨⟨a, b⟩, h⟩) (j' | ⟨⟨a', b'⟩, h'⟩) hh
        · simpa using hh
        · simp at hh
        · simp at hh
        · simp at hh
          simp [hh.1, hh.2]
      · rintro ⟨⟨a, b⟩, h⟩
        induction a using Fin.cases with
        | zero =>
          induction b using Fin.cases with
          | zero => exact absurd h (lt_irrefl _)
          | succ j => exact ⟨Sum.inl j, rfl⟩
        | succ i =>
          induction b using Fin.cases with
          | zero => exact absurd h (by simp)
          | succ j => exact ⟨Sum.inr ⟨(i, j), Fin.succ_lt_succ_iff.1 h⟩, rfl⟩)

theorem pi_split {ι κ τ B : Type} [Fintype ι] [Fintype κ] [Fintype τ] [MeasurableSpace B]
    (φ : κ ⊕ τ ≃ ι) (ν : Measure B) [SigmaFinite ν] :
    MeasurePreserving (fun x : ι → B => ((fun j => x (φ (Sum.inl j)), fun p => x (φ (Sum.inr p))) :
        (κ → B) × (τ → B)))
      (Measure.pi fun _ : ι => ν)
      ((Measure.pi fun _ : κ => ν).prod (Measure.pi fun _ : τ => ν)) := by
  classical
  have h1 := (measurePreserving_piCongrLeft (α := fun _ : ι => B) (fun _ : ι => ν) φ).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : κ ⊕ τ => ν)
  convert h2.comp h1 using 1
  rfl

def blockT {A B : Type} (n : ℕ) (x : (Fin (n + 1) → A) × (UT (n + 1) → B)) :
    ((Fin 1 → A) × (UT 1 → B)) × ((Fin 1 → Fin n → B) × ((Fin n → A) × (UT n → B))) :=
  ((fun _ => x.1 0, fun p => isEmptyElim p),
    (fun _ j => x.2 (utEquiv n (Sum.inl j)),
      (fun i => x.1 i.succ, fun p => x.2 (utEquiv n (Sum.inr p)))))

theorem scalar_mp {A B : Type} [MeasurableSpace A] [MeasurableSpace B] (lam : Measure A) (κ : Measure B)
    [SigmaFinite lam] :
    MeasurePreserving (fun r : A => (((fun _ => r), fun p => isEmptyElim p) : (Fin 1 → A) × (UT 1 → B)))
      lam ((Measure.pi fun _ : Fin 1 => lam).prod (Measure.pi fun _ : UT 1 => κ)) := by
  have h1 := (measurePreserving_funUnique lam (Fin 1)).symm
  have h2 : MeasurePreserving (fun f : Fin 1 → A => ((f, fun p => isEmptyElim p) : (Fin 1 → A) × (UT 1 → B)))
      (Measure.pi fun _ : Fin 1 => lam)
      ((Measure.pi fun _ : Fin 1 => lam).prod (Measure.pi fun _ : UT 1 => κ)) := by
    have hd : Measure.pi (fun _ : UT 1 => κ) = Measure.dirac (fun p => isEmptyElim p) :=
      Measure.pi_of_empty _ _
    rw [hd, Measure.prod_dirac]
    exact ⟨by fun_prop, rfl⟩
  exact h2.comp h1

theorem blockT_mp {A B : Type} [MeasurableSpace A] [MeasurableSpace B] (lam : Measure A) (κ : Measure B)
    [SigmaFinite lam] [SigmaFinite κ] (n : ℕ) :
    MeasurePreserving (blockT (A := A) (B := B) n)
      ((Measure.pi fun _ : Fin (n + 1) => lam).prod (Measure.pi fun _ : UT (n + 1) => κ))
      (((Measure.pi fun _ : Fin 1 => lam).prod (Measure.pi fun _ : UT 1 => κ)).prod
        ((Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => κ).prod
          ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : UT n => κ)))) := by
  set Au := Measure.pi fun _ : Fin n => lam
  set Bw := Measure.pi fun _ : Fin n => κ
  set Cv := Measure.pi fun _ : UT n => κ
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => lam) 0
  have h2 := pi_split (utEquiv n) κ
  have h12 := h1.prod h2
  have m1 := measurePreserving_prodAssoc lam Au (Bw.prod Cv)
  have m2 := (MeasurePreserving.id lam).prod ((measurePreserving_prodAssoc Au Bw Cv).symm)
  have m3 := (MeasurePreserving.id lam).prod
    ((Measure.measurePreserving_swap (μ := Au) (ν := Bw)).prod (MeasurePreserving.id Cv))
  have m4 := (MeasurePreserving.id lam).prod (measurePreserving_prodAssoc Bw Au Cv)
  have g1 := scalar_mp (B := B) lam κ
  have g2 := (measurePreserving_funUnique Bw (Fin 1)).symm
  have m5 := g1.prod (g2.prod (MeasurePreserving.id (Au.prod Cv)))
  have all := m5.comp (m4.comp (m3.comp (m2.comp (m1.comp h12))))
  suffices hf : blockT (A := A) (B := B) n = _ by
    rw [hf]; exact all
  clear all m5 m4 m3 m2 m1 h12 h1 h2 g1 g2
  funext x
  obtain ⟨u, v⟩ := x
  simp [blockT, MeasurableEquiv.piFinSuccAbove, Prod.map]
  refine ⟨rfl, ?_, rfl⟩
  funext i
  rw [uniqueElim_const]
  rfl

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

def corner (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ (n + 1)) : HermR R σ 1 :=
  ⟨fun _ _ => (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0, fun _ _ => S.2 0 0⟩

def firstRow (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ (n + 1)) : Fin 1 → Fin n → R ⊗[F] E :=
  fun _ j => (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ

def lowerBlock (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ (n + 1)) : HermR R σ n :=
  ⟨fun i j => (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ,
    fun a b => S.2 a.succ b.succ⟩

def glue (σ : E →ₐ[F] E) {n : ℕ} (t : HermR R σ 1) (w : Fin 1 → Fin n → R ⊗[F] E) (L : HermR R σ n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E) := fun a b =>
  Fin.cases (Fin.cases ((t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) (fun j => w 0 j) b)
    (fun i => Fin.cases (sigR R σ (w 0 i)) (fun j => (L : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j) b) a

theorem glue_mem {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) {n : ℕ} (t : HermR R σ 1)
    (w : Fin 1 → Fin n → R ⊗[F] E) (L : HermR R σ n) : glue R σ t w L ∈ HermR R σ (n + 1) := by
  intro a b
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => exact t.2 0 0
    | succ j => exact HypStage.sigR_sigR R σ hinv _
  | succ i =>
    induction b using Fin.cases with
    | zero => rfl
    | succ j => exact L.2 i j

variable [TopologicalSpace R]

theorem continuous_entry (σ : E →ₐ[F] E) {m : ℕ} (a b : Fin m) :
    Continuous fun S : HermR R σ m => (S : Matrix (Fin m) (Fin m) (R ⊗[F] E)) a b :=
  (continuous_subtype_val (p := fun S => S ∈ HermR R σ m)).matrix_elem a b

def blockHomeo {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (hsig : Continuous (sigR R σ)) (n : ℕ) :
    HermR R σ (n + 1) ≃ₜ (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n) where
  toFun S := (corner R σ S, firstRow R σ S, lowerBlock R σ S)
  invFun x := ⟨glue R σ x.1 x.2.1 x.2.2, glue_mem R hinv x.1 x.2.1 x.2.2⟩
  left_inv S := by
    apply Subtype.ext
    funext a b
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ j => rfl
    | succ i =>
      induction b using Fin.cases with
      | zero => exact S.2 _ _
      | succ j => rfl
  right_inv x := by
    obtain ⟨t, w, L⟩ := x
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · apply Subtype.ext
      funext a b
      obtain rfl : a = 0 := Subsingleton.elim _ _
      obtain rfl : b = 0 := Subsingleton.elim _ _
      rfl
    · funext a j
      obtain rfl : a = 0 := Subsingleton.elim _ _
      rfl
    · apply Subtype.ext
      rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
    · exact continuous_induced_rng.2 (continuous_matrix fun _ _ => continuous_entry R σ _ _)
    · exact continuous_pi fun _ => continuous_pi fun _ => continuous_entry R σ _ _
    · exact continuous_induced_rng.2 (continuous_matrix fun _ _ => continuous_entry R σ _ _)
  continuous_invFun := by
    have ht : Continuous fun x : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n =>
        (x.1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
      (continuous_entry R σ 0 0).comp continuous_fst
    have hw : ∀ j : Fin n, Continuous fun x : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n =>
        x.2.1 0 j := fun j =>
      (continuous_apply_apply _ _).comp (continuous_fst.comp continuous_snd)
    have hL : ∀ i j : Fin n, Continuous fun x : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n =>
        (x.2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j := fun i j =>
      (continuous_entry R σ i j).comp (continuous_snd.comp continuous_snd)
    refine Continuous.subtype_mk (continuous_matrix fun a b => ?_) _
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact ht
      | succ j => exact hw j
    | succ i =>
      induction b using Fin.cases with
      | zero => exact hsig.comp (hw i)
      | succ j => exact hL i j

end Herm

theorem coordHerm_equiv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R] {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (m : ℕ) :
    ∃ h : HermR R σ m ≃ᵐ (Fin m → R) × (UT m → R ⊗[F] E),
      (∀ S, h S = HaarCoord.hermCoord R σ m S) ∧
      MeasurePreserving h (coordHerm R σ b lam m)
        ((Measure.pi fun _ : Fin m => lam).prod (Measure.pi fun _ : UT m => coordK R b lam)) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hcm
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : BorelSpace (HermR R σ m) := ⟨rfl⟩
  have hh := HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ m t5 t6
  let ge := (hh.homeomorph _).toMeasurableEquiv
  refine ⟨ge, fun _ => rfl, ge.measurable, ?_⟩
  have hc : coordHerm R σ b lam m =
      Measure.map ge.symm ((Measure.pi fun _ : Fin m => lam).prod
        (Measure.pi fun _ : UT m => coordK R b lam)) :=
    (MeasurableEquiv.map_symm ge).symm
  rw [hc, Measure.map_map ge.measurable ge.symm.measurable]
  simp

theorem hermSplit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∃ e : HermR R σ (n + 1) ≃ₜ (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n), (∀ S, ((e S).1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 ∧ (∀ j : Fin n, (e S).2.1 0 j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) ∧ ∀ i j : Fin n, ((e S).2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) ∧ MeasurePreserving e (coordHerm R σ b lam (n + 1)) ((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) := by
  intro F E _ _ _ _ _ σ hcm M J hJ R _ _ _ _ _ hloc n d b lam hlam
  obtain ⟨l1, l2, l3, l4, -⟩ := hloc
  haveI := l1
  haveI := l2
  haveI := l3
  haveI := l4
  obtain ⟨t1, t2, t3, t4, t5, t6, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  obtain ⟨hinv, -⟩ := HaarCoord.conj_facts hcm
  obtain ⟨hK, -, hH⟩ := coord_measures_haar F E σ hcm R d b lam hlam
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hcm R 1
  obtain ⟨c1, c2, c3, c4, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hcm R n
  haveI : (coordHerm R σ b lam 1).IsAddHaarMeasure := hH 1
  haveI : (coordHerm R σ b lam n).IsAddHaarMeasure := hH n
  haveI : SigmaFinite (coordW R b lam 1 n) := by
    unfold coordW
    infer_instance
  haveI : SigmaFinite (coordHerm R σ b lam 1) := inferInstance
  haveI : SigmaFinite (coordHerm R σ b lam n) := inferInstance
  refine ⟨blockHomeo R hinv t5 n, fun S => ⟨rfl, fun j => rfl, fun i j => rfl⟩, ?_⟩
  obtain ⟨h1, hh1, mp1⟩ := coordHerm_equiv σ hcm R b lam 1
  obtain ⟨hn, hhn, mpn⟩ := coordHerm_equiv σ hcm R b lam n
  obtain ⟨hN, hhN, mpN⟩ := coordHerm_equiv σ hcm R b lam (n + 1)
  let G := h1.prodCongr ((MeasurableEquiv.refl (Fin 1 → Fin n → R ⊗[F] E)).prodCongr hn)
  have mG : MeasurePreserving G ((coordHerm R σ b lam 1).prod
      ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) _ :=
    mp1.prod ((MeasurePreserving.id (coordW R b lam 1 n)).prod mpn)
  have mT := blockT_mp lam (coordK R b lam) n
  have key : G ∘ (blockHomeo R hinv t5 n) = blockT n ∘ hN := by
    funext S
    have e1 : (G ∘ (blockHomeo R hinv t5 n)) S =
        (h1 (corner R σ S), firstRow R σ S, hn (lowerBlock R σ S)) := rfl
    rw [e1, hh1, hhn, Function.comp_apply, hhN]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext i
      rfl
    · funext p
      exact isEmptyElim p
    · funext a j
      rfl
    · funext i
      rfl
    · funext p
      rfl
  refine (mG.comp_left_iff).1 ?_
  rw [key]
  exact mT.comp mpN

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorphStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_block_decomposition_homeomorph : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∃ e : HermR R σ (n + 1) ≃ₜ (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n), (∀ S, ((e S).1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 ∧ (∀ j : Fin n, (e S).2.1 0 j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) ∧ ∀ i j : Fin n, ((e S).2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) ∧ MeasurePreserving e (coordHerm R σ b lam (n + 1)) ((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartGramFirstEntry
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartGramFirstEntry
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.ChartGram

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem sigR_halfR (σ : E →ₐ[F] E) : sigR R σ (halfR (F := F) (E := E) R) = halfR (F := F) (E := E) R := by
  unfold halfR
  rw [sigR_inclR, AlgHom.commutes]

theorem halfR_add_halfR (h2 : (2 : F) ≠ 0) :
    halfR (F := F) (E := E) R + halfR (F := F) (E := E) R = 1 := by
  have h : (1 / 2 : F) + 1 / 2 = 1 := by field_simp; norm_num
  unfold halfR
  rw [← map_add (f := _), ← map_add (f := _), h, map_one, map_one]

theorem vH_zero {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : vH a s Y 0 = a := rfl
theorem vH_one {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : vH a s Y 1 = s := rfl
theorem tailH_vH {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : tailH (vH a s Y) = Y := rfl

theorem hR_hypOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin (M + 2) → R ⊗[F] E) :
    hR R σ (hypOne J) x y =
      sigR R σ (x 0) * y 1 + sigR R σ (x 1) * y 0 + hR R σ J (tailH x) (tailH y) := by
  unfold hR hform JR tailH
  simp only [Fin.sum_univ_succ, Matrix.map_apply, Fin.succ_zero_eq_one, hypOne_zero_zero, hypOne_zero_one,
    hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one,
    hypOne_rest_rest, map_zero, map_one, mul_zero, zero_mul, mul_one, Finset.sum_const_zero, add_zero, zero_add]
  ring

theorem sigR_hR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  unfold hR hform JR
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, sigR_sigR R σ hσ, Matrix.map_apply, sigR_inclR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

theorem hR_comb_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : R ⊗[F] E)
    (x u w : Fin M → R ⊗[F] E) :
    hR R σ J x (fun i => c * u i + w i) = c * hR R σ J x u + hR R σ J x w := by
  unfold hR hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_comb_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : R ⊗[F] E)
    (u w y : Fin M → R ⊗[F] E) :
    hR R σ J (fun i => c * u i + w i) y = sigR R σ c * hR R σ J u y + hR R σ J w y := by
  unfold hR hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, map_add (f := _), map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sigR_tHalf (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin (M + 2) → R ⊗[F] E) :
    sigR R σ (tHalf R σ J x) = tHalf R σ J x := by
  unfold tHalf
  rw [map_mul, sigR_halfR, hR_hypOne, map_add (f := _), map_add (f := _), map_mul, map_mul, sigR_sigR R σ hσ, sigR_sigR R σ hσ,
    sigR_hR R σ hσ J hJ]
  ring

theorem hR_cvec_right (h2 : (2 : F) ≠ 0) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x v : Fin (M + 2) → R ⊗[F] E) (hu : IsUnit (x 0)) :
    hR R σ (hypOne J) x (cvec R σ J x v) = v 1 + tHalf R σ J x * v 0 := by
  have e1 : Ring.inverse (sigR R σ (x 0)) * sigR R σ (x 0) = 1 :=
    Ring.inverse_mul_cancel _ (hu.map (sigR R σ))
  have e3 : tHalf R σ J x + tHalf R σ J x = hR R σ (hypOne J) x x := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  have e4 := hR_hypOne R σ J x x
  have ht : tailH (cvec R σ J x v) = fun i => v 0 * tailH x i + tailH v i := rfl
  rw [hR_hypOne, ht, hR_comb_right]
  simp only [cvec, vH_zero, vH_one]
  linear_combination (v 1 - tHalf R σ J x * v 0 - hR R σ J (tailH x) (tailH v)) * e1 - v 0 * e3 - v 0 * e4

theorem hR_cvec_cvec (h2 : (2 : F) ≠ 0) (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (x v w : Fin (M + 2) → R ⊗[F] E) (hu : IsUnit (x 0)) :
    hR R σ (hypOne J) (cvec R σ J x v) (cvec R σ J x w) = hR R σ (hypOne J) v w := by
  have e1 : Ring.inverse (sigR R σ (x 0)) * sigR R σ (x 0) = 1 :=
    Ring.inverse_mul_cancel _ (hu.map (sigR R σ))
  have e2 : sigR R σ (Ring.inverse (sigR R σ (x 0))) * x 0 = 1 := by
    have := congrArg (sigR R σ) e1
    rwa [map_mul, sigR_sigR R σ hσ, map_one] at this
  have e3 : tHalf R σ J x + tHalf R σ J x = hR R σ (hypOne J) x x := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  have e4 := hR_hypOne R σ J x x
  have htv : tailH (cvec R σ J x v) = fun i => v 0 * tailH x i + tailH v i := rfl
  have htw : tailH (cvec R σ J x w) = fun i => w 0 * tailH x i + tailH w i := rfl
  rw [hR_hypOne, hR_hypOne R σ J v w, htv, htw, hR_comb_left, hR_comb_right, hR_comb_right]
  simp only [cvec, vH_zero, vH_one, map_add (f := _), map_sub, map_mul, sigR_tHalf R σ hσ J hJ,
    sigR_hR R σ hσ J hJ]
  linear_combination
    (sigR R σ (v 0) * (w 1 - tHalf R σ J x * w 0 - hR R σ J (tailH x) (tailH w))) * e1 +
    (w 0 * (sigR R σ (v 1) - tHalf R σ J x * sigR R σ (v 0) - hR R σ J (tailH v) (tailH x))) * e2 -
    sigR R σ (v 0) * w 0 * e3 - sigR R σ (v 0) * w 0 * e4

end Alg

theorem gramR_chartS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) → gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 0 = hR R σ (hypOne J) (x 0) (x 0) ∧ (∀ j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 j.succ = s 0 j) ∧ ∀ i j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) i.succ j.succ = gramR R σ J Y i j + (sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j - hR R σ (hypOne J) (x 0) (x 0) * (sigR R σ (a 0 i) * a 0 j)) := by
  intro F E _ _ _ _ _ σ hc M J hJ R _ _ n x a s Y hu
  have hσ := sig_invol σ hc
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have e3 : tHalf R σ J (x 0) + tHalf R σ J (x 0) = hR R σ (hypOne J) (x 0) (x 0) := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  refine ⟨rfl, fun j => ?_, fun i j => ?_⟩
  · change hR R σ (hypOne J) (x 0) (cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))) = s 0 j
    rw [hR_cvec_right R h2 σ J _ _ hu, vH_zero, vH_one]
    ring
  · change hR R σ (hypOne J) (cvec R σ J (x 0) (vH (a 0 i) (s 0 i - tHalf R σ J (x 0) * a 0 i) (Y i)))
      (cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))) = hR R σ J (Y i) (Y j) + _
    rw [hR_cvec_cvec R h2 σ hσ J hJ.1 _ _ _ hu, hR_hypOne]
    simp only [vH_zero, vH_one, tailH_vH, map_sub, map_mul, sigR_tHalf R σ hσ J hJ.1]
    linear_combination (-(sigR R σ (a 0 i) * a 0 j)) * e3

end GlobalTheory.CompanionTheory.WeilSiegel.ChartGram
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartGramFirstEntryStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_gram_first_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) → gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 0 = hR R σ (hypOne J) (x 0) (x 0) ∧ (∀ j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 j.succ = s 0 j) ∧ ∀ i j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) i.succ j.succ = gramR R σ J Y i j + (sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j - hR R σ (hypOne J) (x 0) (x 0) * (sigR R σ (a 0 i) * a 0 j)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.ChartGram.gramR_chartS | exact GlobalTheory.CompanionTheory.WeilSiegel.ChartGram.gramR_chartS | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.ChartGram.gramR_chartS <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuous
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def aPart {K : Type} [CommRing K] {M n : ℕ} (X : Fin (n + 1) → Fin (M + 2) → K) : Fin 1 → Fin n → K :=
  fun _ j => X j.succ 0 * Ring.inverse (X 0 0)

def sPart (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) :
    Fin 1 → Fin n → R ⊗[F] E :=
  fun _ j => sigR R σ (X 0 0) * (X j.succ 1 - aPart X 0 j * X 0 1) + tHalf R σ J (X 0) * aPart X 0 j +
    hR R σ J (tailH (X 0)) (yPart X j) + tHalf R σ J (X 0) * aPart X 0 j

def thetaS (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) :
    (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
      (Fin n → Fin M → R ⊗[F] E) :=
  (fun _ => X 0, aPart X, sPart R σ J X, yPart X)

variable (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E)
  (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E)

theorem chartS_zero : chartS R σ J x a s Y 0 = x 0 := rfl

theorem chartS_succ_zero (j : Fin n) : chartS R σ J x a s Y j.succ 0 = x 0 0 * a 0 j := rfl

theorem chartS_succ_one (j : Fin n) : chartS R σ J x a s Y j.succ 1 = a 0 j * x 0 1 +
    Ring.inverse (sigR R σ (x 0 0)) * (s 0 j - tHalf R σ J (x 0) * a 0 j - tHalf R σ J (x 0) * a 0 j -
      hR R σ J (tailH (x 0)) (Y j)) := rfl

theorem chartS_succ_rest (j : Fin n) (i : Fin M) :
    chartS R σ J x a s Y j.succ i.succ.succ = a 0 j * x 0 i.succ.succ + Y j i := rfl

variable {R σ J x a s Y}

theorem aPart_chartS (hx : IsUnit (x 0 0)) : aPart (chartS R σ J x a s Y) = a := by
  funext u j
  have hu : u = 0 := Subsingleton.elim _ _
  subst hu
  show chartS R σ J x a s Y j.succ 0 * Ring.inverse (chartS R σ J x a s Y 0 0) = a 0 j
  rw [chartS_succ_zero, chartS_zero, mul_comm (x 0 0), mul_assoc, Ring.mul_inverse_cancel _ hx, mul_one]

theorem yPart_chartS (hx : IsUnit (x 0 0)) : yPart (chartS R σ J x a s Y) = Y := by
  funext j i
  show chartS R σ J x a s Y j.succ i.succ.succ -
    chartS R σ J x a s Y j.succ 0 * Ring.inverse (chartS R σ J x a s Y 0 0) * chartS R σ J x a s Y 0 i.succ.succ = Y j i
  rw [chartS_succ_rest, chartS_succ_zero, chartS_zero, mul_comm (x 0 0), mul_assoc (a 0 j),
    Ring.mul_inverse_cancel _ hx, mul_one]
  ring

theorem sPart_chartS (hx : IsUnit (x 0 0)) : sPart R σ J (chartS R σ J x a s Y) = s := by
  funext u j
  have hu : u = 0 := Subsingleton.elim _ _
  subst hu
  have hs : IsUnit (sigR R σ (x 0 0)) := hx.map _
  have ha := aPart_chartS (R := R) (σ := σ) (J := J) (a := a) (s := s) (Y := Y) hx
  have hy := yPart_chartS (R := R) (σ := σ) (J := J) (a := a) (s := s) (Y := Y) hx
  show sigR R σ (chartS R σ J x a s Y 0 0) * (chartS R σ J x a s Y j.succ 1 -
      aPart (chartS R σ J x a s Y) 0 j * chartS R σ J x a s Y 0 1) +
      tHalf R σ J (chartS R σ J x a s Y 0) * aPart (chartS R σ J x a s Y) 0 j +
      hR R σ J (tailH (chartS R σ J x a s Y 0)) (yPart (chartS R σ J x a s Y) j) +
      tHalf R σ J (chartS R σ J x a s Y 0) * aPart (chartS R σ J x a s Y) 0 j = s 0 j
  rw [ha, hy, chartS_succ_one, chartS_zero, add_sub_cancel_left, ← mul_assoc, Ring.mul_inverse_cancel _ hs, one_mul]
  ring

theorem thetaS_chartS (hx : IsUnit (x 0 0)) : thetaS R σ J (chartS R σ J x a s Y) = (x, a, s, Y) := by
  have h0 : (fun _ : Fin 1 => chartS R σ J x a s Y 0) = x := by
    funext u
    have hu : u = 0 := Subsingleton.elim _ _
    subst hu
    rfl
  simp only [thetaS, h0, aPart_chartS hx, sPart_chartS hx, yPart_chartS hx]

end Alg

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
  {σ : E →ₐ[F] E} {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem continuous_hR [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ)) {A : Type} [TopologicalSpace A]
    {m : ℕ} (J : Matrix (Fin m) (Fin m) E) {u v : A → Fin m → R ⊗[F] E} (hu : Continuous u) (hv : Continuous v) :
    Continuous fun p => hR R σ J (u p) (v p) := by
  unfold hR hform
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((hsig.comp ((continuous_apply i).comp hu)).mul continuous_const).mul ((continuous_apply j).comp hv)

theorem continuousOn_hR [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ)) {A : Type}
    [TopologicalSpace A] {m : ℕ} (J : Matrix (Fin m) (Fin m) E) {S : Set A} {u v : A → Fin m → R ⊗[F] E}
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) : ContinuousOn (fun p => hR R σ J (u p) (v p)) S := by
  unfold hR hform
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  exact ((hsig.comp_continuousOn ((continuous_apply i).comp_continuousOn hu)).mul continuousOn_const).mul
    ((continuous_apply j).comp_continuousOn hv)

theorem continuous_tHalf [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ)) {A : Type}
    [TopologicalSpace A] {u : A → Fin (M + 2) → R ⊗[F] E} (hu : Continuous u) :
    Continuous fun p => tHalf R σ J (u p) :=
  continuous_const.mul (continuous_hR hsig _ hu hu)

theorem continuous_tailH {K A : Type} [TopologicalSpace K] [TopologicalSpace A] {u : A → Fin (M + 2) → K}
    (hu : Continuous u) : Continuous fun p => tailH (u p) :=
  continuous_pi fun i => (continuous_apply i.succ.succ).comp hu

theorem continuousOn_vH {K A : Type} [TopologicalSpace K] [TopologicalSpace A] {S : Set A} {a s : A → K}
    {Y : A → Fin M → K} (ha : ContinuousOn a S) (hs : ContinuousOn s S) (hY : ContinuousOn Y S) :
    ContinuousOn (fun p => vH (a p) (s p) (Y p)) S := by
  refine continuousOn_pi.2 fun i => ?_
  refine Fin.cases ha (fun i => ?_) i
  refine Fin.cases hs (fun i => ?_) i
  exact (continuous_apply i).comp_continuousOn hY

theorem continuousOn_cvec [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ))
    (hinv : ContinuousOn (Ring.inverse : R ⊗[F] E → R ⊗[F] E) {r | IsUnit r}) {A : Type} [TopologicalSpace A]
    {S : Set A} {u v : A → Fin (M + 2) → R ⊗[F] E} (hu : Continuous u) (hv : Continuous v)
    (hunit : ∀ p ∈ S, IsUnit (u p 0)) : ContinuousOn (fun p => cvec R σ J (u p) (v p)) S := by
  have c {w : A → Fin (M + 2) → R ⊗[F] E} (hw : Continuous w) (i : Fin (M + 2)) : Continuous fun p => w p i :=
    (continuous_apply i).comp hw
  have hI : ContinuousOn (fun p => Ring.inverse (sigR R σ (u p 0))) S :=
    hinv.comp (hsig.comp (c hu 0)).continuousOn fun p hp => (hunit p hp).map _
  refine continuousOn_vH ((c hu 0).mul (c hv 0)).continuousOn ?_ ?_
  · refine ((c hv 0).mul (c hu 1)).continuousOn.add (hI.mul (Continuous.continuousOn ?_))
    exact ((c hv 1).sub ((continuous_tHalf hsig hu).mul (c hv 0))).sub
      (continuous_hR hsig J (continuous_tailH hu) (continuous_tailH hv))
  · exact (continuous_pi fun i : Fin M => ((c hv 0).mul (c hu i.succ.succ)).add (c hv i.succ.succ)).continuousOn

theorem continuous_vH {K A : Type} [TopologicalSpace K] [TopologicalSpace A] {a s : A → K}
    {Y : A → Fin M → K} (ha : Continuous a) (hs : Continuous s) (hY : Continuous Y) :
    Continuous (fun p => vH (a p) (s p) (Y p)) :=
  continuousOn_univ.1 (continuousOn_vH ha.continuousOn hs.continuousOn hY.continuousOn)

theorem continuousOn_chartS [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ))
    (hinv : ContinuousOn (Ring.inverse : R ⊗[F] E → R ⊗[F] E) {r | IsUnit r}) :
    ContinuousOn (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2) {p | IsUnit (p.1 0 0)} := by
  have hx : Continuous fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
      (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.1 0 := by fun_prop
  refine continuousOn_pi.2 fun j => ?_
  cases j using Fin.cases with
  | zero => exact hx.continuousOn
  | succ j =>
    have ha : Continuous fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.2.1 0 j := by fun_prop
    have hs : Continuous fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.2.2.1 0 j := by fun_prop
    have hY : Continuous fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
        (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => p.2.2.2 j := by fun_prop
    exact continuousOn_cvec hsig hinv hx
      (continuous_vH ha (hs.sub ((continuous_tHalf hsig hx).mul ha)) hY) fun p hp => hp

theorem continuousOn_thetaS [IsTopologicalRing (R ⊗[F] E)] (hsig : Continuous (sigR R σ))
    (hinv : ContinuousOn (Ring.inverse : R ⊗[F] E → R ⊗[F] E) {r | IsUnit r}) :
    ContinuousOn (thetaS R σ J : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → _) {X | IsUnit (X 0 0)} := by
  have c (j : Fin (n + 1)) (i : Fin (M + 2)) :
      Continuous fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => X j i := by fun_prop
  have hI : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => Ring.inverse (X 0 0))
      {X | IsUnit (X 0 0)} := hinv.comp (c 0 0).continuousOn fun X hX => hX
  have h0 : Continuous fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => X 0 := continuous_apply 0
  have hA (j : Fin n) : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => aPart X 0 j)
      {X | IsUnit (X 0 0)} := (c j.succ 0).continuousOn.mul hI
  have hY (j : Fin n) : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => yPart X j)
      {X | IsUnit (X 0 0)} := continuousOn_pi.2 fun i =>
    (c j.succ i.succ.succ).continuousOn.sub (((c j.succ 0).continuousOn.mul hI).mul (c 0 i.succ.succ).continuousOn)
  have ht : Continuous fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => tHalf R σ J (X 0) :=
    continuous_tHalf hsig h0
  have hh (j : Fin n) : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E =>
      hR R σ J (tailH (X 0)) (yPart X j)) {X | IsUnit (X 0 0)} :=
    continuousOn_hR hsig J (continuous_tailH h0).continuousOn (hY j)
  have h1 : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => (fun _ : Fin 1 => X 0))
      {X | IsUnit (X 0 0)} := (continuous_pi fun _ => h0).continuousOn
  have h2 : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => aPart X)
      {X | IsUnit (X 0 0)} := continuousOn_pi.2 fun u => continuousOn_pi.2 fun j => by
    have hu : u = 0 := Subsingleton.elim _ _
    subst hu
    exact hA j
  have h3 : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => sPart R σ J X)
      {X | IsUnit (X 0 0)} := by
    refine continuousOn_pi.2 fun _ => continuousOn_pi.2 fun j => ?_
    have hs : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E =>
        sigR R σ (X 0 0) * (X j.succ 1 - aPart X 0 j * X 0 1) + tHalf R σ J (X 0) * aPart X 0 j +
          hR R σ J (tailH (X 0)) (yPart X j) + tHalf R σ J (X 0) * aPart X 0 j) {X | IsUnit (X 0 0)} :=
      (((((hsig.comp (c 0 0)).continuousOn).mul ((c j.succ 1).continuousOn.sub
        ((hA j).mul (c 0 1).continuousOn))).add (ht.continuousOn.mul (hA j))).add (hh j)).add
          (ht.continuousOn.mul (hA j))
    exact hs
  have h4 : ContinuousOn (fun X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E => yPart X)
      {X | IsUnit (X 0 0)} := continuousOn_pi.2 hY
  exact h1.prodMk (h2.prodMk (h3.prodMk h4))

end Top

theorem test_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ), Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → Continuous (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ HasCompactSupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ ∀ p ∈ tsupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)), IsUnit (p.1 0 0) ∧ LinearIndependent (R ⊗[F] E) p.2.2.2 := by
  intro F E _ _ _ _ _ σ hCM M J _ R _ _ _ _ _ hLoc n φ hφ hφc hφs
  have hKu := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hCM R hLoc
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hLoc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨i1, -, -, i4, hsig, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := i1
  haveI := i4
  have hinv := GlobalTheory.CompanionTheory.SW.KUnits.continuousOn_ringInverse hKu
  set ψ := fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
    (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2) with hψ
  have hCu : tsupport φ ⊆ {X | IsUnit (X 0 0)} := fun X hX => (hφs hX).1
  let T := thetaS R σ J '' tsupport φ
  have hTc : IsCompact T := hφc.isCompact.image_of_continuousOn ((continuousOn_thetaS hsig hinv).mono hCu)
  have hTcl : IsClosed T := hTc.isClosed
  have hsupp : Function.support ψ ⊆ T := by
    rintro ⟨x, a, s, Y⟩ hp
    have hC : chartS R σ J x a s Y ∈ tsupport φ := subset_tsupport φ hp
    have hx : IsUnit (x 0 0) := hCu hC
    exact ⟨_, hC, thetaS_chartS hx⟩
  have hts : tsupport ψ ⊆ T := closure_minimal hsupp hTcl
  refine ⟨?_, hTc.of_isClosed_subset (isClosed_tsupport ψ) hts, ?_⟩
  · refine continuous_iff_continuousAt.2 fun p => ?_
    by_cases hp : p ∈ T
    · obtain ⟨X, hX, rfl⟩ := hp
      have hU : IsOpen {q : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
          (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) | IsUnit (q.1 0 0)} := by
        have h1 : IsOpen {r : R ⊗[F] E | IsUnit r} := by
          have h2 : {r : R ⊗[F] E | IsUnit r} = Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) :=
            Set.ext fun r => Iff.rfl
          rw [h2]
          exact hKu.isOpen_range
        exact h1.preimage (by fun_prop)
      have hmem : thetaS R σ J X ∈ {q : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
          (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) | IsUnit (q.1 0 0)} := hCu hX
      exact hφ.continuousAt.comp ((continuousOn_chartS hsig hinv).continuousAt (hU.mem_nhds hmem))
    · have : ψ =ᶠ[𝓝 p] fun _ => 0 := by
        filter_upwards [hTcl.isOpen_compl.mem_nhds hp] with q hq
        by_contra h
        exact hq (hsupp h)
      exact continuousAt_const.congr this.symm
  · intro p hp
    obtain ⟨X, hX, rfl⟩ := hts hp
    exact hφs hX

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuousStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_compact_support_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ), Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → Continuous (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ HasCompactSupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ ∀ p ∈ tsupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)), IsUnit (p.1 0 0) ∧ LinearIndependent (R ⊗[F] E) p.2.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFibreFreeExtension
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero

theorem stages_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → (∀ X, 0 ≤ φ X) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m 0) = ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (φ (chartS R σ J x a 0 Y)) ∂(m' 0) ∂(coordW R b lam 1 n) ∂(m₁ 0) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hLoc n d b lam hlam m m₁ m' hm hm₁ hm' φ hφc hφs hφt hφ0
  have hLoc' := hLoc
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hLoc'
  obtain ⟨_, _, _, _, hsigc, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hbor 1 (M + 2)
  haveI := hbor n M
  haveI := hbor 1 n
  haveI := hbor (n + 1) (M + 2)
  obtain ⟨_, _, _, _, hl1⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R 1
  obtain ⟨_, _, _, _, hl3⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R n
  obtain ⟨_, _, _, _, hlN⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R (n + 1)
  have hJ' : IsHermND σ (hypOne J) := isHermND_hypOne σ hJ
  obtain ⟨G₁, hG₁c, hG₁⟩ := hl1 (M + 2) (hypOne J) hJ'
  obtain ⟨G₃, hG₃c, hG₃⟩ := hl3 M J hJ
  obtain ⟨G, hGc, hG⟩ := hlN (M + 2) (hypOne J) hJ'
  obtain ⟨e, he, hep⟩ := GlobalTheory.T.hermitian_block_decomposition_homeomorph F E σ hσ M J hJ R hLoc n d b lam hlam
  obtain ⟨hψc, hψs, hψt⟩ := GlobalTheory.T.chart_compact_support_continuous F E σ hσ M J hJ R hLoc n φ hφc hφs hφt
  obtain ⟨-, hcellF, -, -, -⟩ := GlobalTheory.T.free_cell_open_independent F E σ hσ M J hJ R hLoc n
  obtain ⟨-, hWh, hHh⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam
  haveI := hWh 1 (M + 2)
  haveI := hWh n M
  haveI := hWh 1 n
  haveI := hHh 1
  haveI := hHh n
  have hU1 : IsOpen {X : Fin 1 → Fin (M + 2) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ hσ R hLoc 1 (M + 2)
  have hU3 : IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ hσ R hLoc n M
  have hWo : IsOpen {X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ hσ R hLoc (n + 1) (M + 2)
  have li1 : ∀ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, IsUnit (x 0 0) → LinearIndependent (R ⊗[F] E) x := by
    intro x hx
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congrFun hg 0
    simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hx.mul_left_eq_zero.1 h0
  let Q : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) → HermR R σ n :=
    fun p => qH R σ (sig_invol σ hσ) p.1 p.2.1 p.2.2
  have hQc : Continuous Q := by
    refine Topology.IsEmbedding.subtypeVal.continuous_iff.2 (continuous_matrix fun i j => ?_)
    have ca : ∀ i, Continuous fun p : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        p.2.2 0 i := fun i =>
      (continuous_apply i).comp ((continuous_apply 0).comp (continuous_snd.comp continuous_snd))
    have cs : ∀ i, Continuous fun p : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        p.2.1 0 i := fun i =>
      (continuous_apply i).comp ((continuous_apply 0).comp (continuous_fst.comp continuous_snd))
    have ct : Continuous fun p : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        (p.1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
      (continuous_fst.subtype_val).matrix_elem 0 0
    exact ((((hsigc.comp (ca i)).mul (cs j)).add ((hsigc.comp (cs i)).mul (ca j))).sub
      (ct.mul ((hsigc.comp (ca i)).mul (ca j))))
  let ψ : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) ×
      (Fin n → Fin M → R ⊗[F] E) → ℝ := fun p => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)
  obtain ⟨hLc, hL⟩ := GlobalTheory.T.staged_disintegration_composition (Fin 1 → Fin (M + 2) → R ⊗[F] E) (Fin n → Fin M → R ⊗[F] E)
    (HermR R σ 1) (HermR R σ n) (Fin 1 → Fin n → R ⊗[F] E) (Fin 1 → Fin n → R ⊗[F] E)
    (Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) (Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (coordW R b lam 1 (M + 2)) (coordW R b lam n M) (coordHerm R σ b lam 1) (coordHerm R σ b lam n)
    (coordW R b lam 1 n) (coordW R b lam 1 n)
    (gramR R σ (hypOne J)) Subtype.val G₁ {X | LinearIndependent (R ⊗[F] E) X} m₁
    (gramR R σ J) Subtype.val G₃ {X | LinearIndependent (R ⊗[F] E) X} m' Q hU1 hU3 hG₁c hG₃c
    Subtype.val_injective Subtype.val_injective hG₁ hG₃ hm₁ hm' hQc ψ hψc hψs
    (fun p hp => ⟨li1 _ (hψt p hp).1, (hψt p hp).2⟩) (fun p => hφ0 _)
  have key : ∀ (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E)
      (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) →
      e (G (chartS R σ J x a s Y)) = (G₁ x, s, G₃ Y + Q (G₁ x, s, a)) := by
    intro x a s Y hx
    obtain ⟨g1, g2, g3⟩ := GlobalTheory.T.chart_gram_first_entry F E σ hσ M J hJ R n x a s Y hx
    obtain ⟨e1, e2, e3⟩ := he (G (chartS R σ J x a s Y))
    rw [← hG] at e1 e2 e3
    have ht : ((G₁ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = hR R σ (hypOne J) (x 0) (x 0) := by
      rw [← hG₁]; rfl
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · refine Subtype.ext (Matrix.ext fun i j => ?_)
      obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact e1.trans (g1.trans ht.symm)
    · funext i j
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact (e2 j).trans (g2 j)
    · refine Subtype.ext (Matrix.ext fun i j => ?_)
      refine (e3 i j).trans ((g3 i j).trans ?_)
      show _ = ((G₃ Y : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j +
        (sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j -
          ((G₁ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 * (sigR R σ (a 0 i) * a 0 j))
      rw [← hG₃, ht]
  have hφm : Measurable fun X => ENNReal.ofReal (φ X) :=
    ENNReal.measurable_ofReal.comp hφc.measurable
  have hφz : ∀ X, X ∉ freeCell (R ⊗[F] E) M n → φ X = 0 := fun X hX =>
    image_eq_zero_of_notMem_tsupport fun h => hX (hφt h)
  have hmF : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 2)) (gramR R σ (hypOne J))
      Subtype.val {X | LinearIndependent (R ⊗[F] E) X} (coordHerm R σ b lam (n + 1)) Set.univ m := hm
  obtain ⟨hint, hcont⟩ := hmF.2.2 φ hφc hφs (hφt.trans fun X hX => hcellF X hX)
  have hD : ∀ B, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m B) = ENNReal.ofReal (∫ X, φ X ∂(m B)) := fun B =>
    (ofReal_integral_eq_lintegral_ofReal (hint B trivial) (Filter.Eventually.of_forall hφ0)).symm
  have hDc : Continuous fun z : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n =>
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (e.symm z)) := by
    simp only [hD]
    exact ENNReal.continuous_ofReal.comp ((continuousOn_univ.1 hcont).comp e.symm.continuous)
  have hcmp : ∀ S : Set (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n), IsCompact S →
      ∫⁻ z in S, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (e.symm z))
        ∂((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) =
      ∫⁻ z in S, (∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y))
          ∂(m' (z.2.2 - Q (z.1, z.2.1, a))) ∂(coordW R b lam 1 n) ∂(m₁ z.1))
        ∂((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) := by
    intro S hS
    have hSm : MeasurableSet S := hS.measurableSet
    have hfm : Measurable (S.indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator hSm
    have h1 := hL _ hfm
    have h2 : ∀ L : HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞,
        (fun z => S.indicator (fun _ => (1 : ℝ≥0∞)) z * L z) = S.indicator L := by
      intro L
      funext z
      by_cases hz : z ∈ S <;> simp [hz]
    rw [h2, lintegral_indicator hSm] at h1
    rw [← h1, ← hep.setLIntegral_comp_preimage_emb e.measurableEmbedding _ S]
    simp only [Homeomorph.symm_apply_apply]
    have hGm := e.continuous.measurable hSm
    rw [← GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage Subtype.val_injective hGc hG hWo subset_rfl hm _ hφm
      (fun X hX => ?_) _ hGm]
    · have hgm : Measurable ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) :=
        hφm.indicator (hGc.measurable hGm)
      have hg0 : ∀ X, X ∉ freeCell (R ⊗[F] E) M n →
          ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) X = 0 := by
        intro X hX
        exact Set.indicator_apply_eq_zero.2 fun _ => by rw [hφz X hX, ENNReal.ofReal_zero]
      have h3 : ∫⁻ v in {X | LinearIndependent (R ⊗[F] E) X},
            ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) v ∂(coordW R b lam (n + 1) (M + 2)) =
          ∫⁻ v, ((G ⁻¹' (e ⁻¹' S)).indicator fun X => ENNReal.ofReal (φ X)) v
            ∂(coordW R b lam (n + 1) (M + 2)) := by
        rw [← lintegral_indicator hWo.measurableSet]
        refine lintegral_congr fun v => ?_
        by_cases hv : v ∈ {X | LinearIndependent (R ⊗[F] E) X}
        · rw [Set.indicator_of_mem hv]
        · rw [Set.indicator_of_notMem hv]
          exact (hg0 v fun hc => hv (hcellF v hc)).symm
      rw [h3, GlobalTheory.T.chart_integral_formula_hyperbolic F E σ hσ M J hJ R hLoc n d b lam hlam _ hgm
        (fun X hX => hg0 X fun hc => hX hc.1)]
      refine lintegral_congr fun x => lintegral_congr fun a => lintegral_congr fun s =>
        lintegral_congr fun Y => ?_
      by_cases hx : IsUnit (x 0 0)
      · have hk := key x a s Y hx
        by_cases hz : (G₁ x, s, G₃ Y + Q (G₁ x, s, a)) ∈ S
        · have hm1 : chartS R σ J x a s Y ∈ G ⁻¹' (e ⁻¹' S) := by
            simpa only [Set.mem_preimage, hk] using hz
          rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hz]
          simp [ψ]
        · have hm1 : chartS R σ J x a s Y ∉ G ⁻¹' (e ⁻¹' S) := by
            simpa only [Set.mem_preimage, hk] using hz
          rw [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hz]
          simp
      · have hp : ψ (x, a, s, Y) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hx (hψt _ h).1
        have hp' : φ (chartS R σ J x a s Y) = 0 := hp
        rw [hp, ENNReal.ofReal_zero, zero_mul]
        exact Set.indicator_apply_eq_zero.2 fun _ => by rw [hp', ENNReal.ofReal_zero]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hX (hcellF X (hφt h)), ENNReal.ofReal_zero]
  have hfin := GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts _ ((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n)))
    Set.univ isOpen_univ _ _ hDc.continuousOn hLc.continuousOn (fun S hS _ => hcmp S hS) 0 trivial
  have he0 : e 0 = 0 := by
    obtain ⟨e1, e2, e3⟩ := he 0
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · refine Subtype.ext (Matrix.ext fun i j => ?_)
      obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact e1
    · funext i j
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact e2 j
    · exact Subtype.ext (Matrix.ext fun i j => e3 i j)
  have hes : e.symm 0 = 0 := by rw [← he0, e.symm_apply_apply]
  have hQ0 : ∀ a, Q (0, 0, a) = 0 := by
    intro a
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    show sigR R σ (a 0 i) * 0 + sigR R σ 0 * a 0 j - 0 * (sigR R σ (a 0 i) * a 0 j) = 0
    simp
  simp only [hes, Prod.fst_zero, Prod.snd_zero, hQ0, sub_zero] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFibreFreeExtensionStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_fibre_free_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → (∀ X, 0 ≤ φ X) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m 0) = ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (φ (chartS R σ J x a 0 Y)) ∂(m' 0) ∂(coordW R b lam 1 n) ∂(m₁ 0) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StagesZero.stages_zero <;> assumption)
end
