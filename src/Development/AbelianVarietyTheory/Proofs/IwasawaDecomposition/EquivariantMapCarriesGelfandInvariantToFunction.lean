module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwise

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieWordCommutesOneParameterDerivative
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieWordCommutesOneParameterDerivative
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmVecDeriv

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem contDiff_snoc {k : ℕ} :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using contDiff_snd
  · simp only [Fin.snoc_castSucc]
    fun_prop

theorem snoc_mem {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hXs : ∀ i, Xs i ∈ lieG G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (i : Fin (k + 1)) :
    (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i ∈ lieG G := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hX
  · simpa using hXs j

theorem rep_snoc (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hXs : ∀ i, Xs i ∈ lieG G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (t : Fin k → ℝ) (s : ℝ) (u : H) :
    π (List.ofFn fun i => NormedSpace.exp ((Fin.snoc t s : Fin (k + 1) → ℝ) i •
        (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i)).prod u =
      π (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod (π (NormedSpace.exp (s • X)) u) := by
  rw [← rep_mul hπ (expProd_mem_UH hG hXs t) (exp_mem_UH hG hX s)]
  simp [List.ofFn_succ', -List.ofFn_succ]

theorem contDiff_word (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ Y ∈ l, Y ∈ lieG G) (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (hXs : ∀ i, Xs i ∈ lieG G) :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod
      (word π l (π (NormedSpace.exp (p.2 • X)) w)) := by
  induction l generalizing k with
  | nil =>
    have h1 := (hw (k + 1) (Fin.snoc Xs X) (snoc_mem hXs hX)).comp contDiff_snoc
    convert h1 using 2 with p
    exact (rep_snoc hG hπ hXs hX p.1 p.2 w).symm
  | cons Y l ih =>
    have hl' : ∀ Z ∈ l, Z ∈ lieG G := fun Z hZ => hl Z (by simp [hZ])
    have hY := hl Y (by simp)
    have h1 := ih hl' (k + 1) (Fin.snoc Xs Y) (snoc_mem hXs hY)
    have hs : ContDiff ℝ ∞ fun q : ((Fin k → ℝ) × ℝ) × ℝ =>
        (((Fin.snoc q.1.1 q.2 : Fin (k + 1) → ℝ), q.1.2) : (Fin (k + 1) → ℝ) × ℝ) :=
      (contDiff_snoc.comp (contDiff_fst.fst.prodMk contDiff_snd)).prodMk contDiff_fst.snd
    have h2 : ContDiff ℝ ∞ (Function.uncurry fun (p : (Fin k → ℝ) × ℝ) (r : ℝ) =>
        π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod (π (NormedSpace.exp (r • Y))
          (word π l (π (NormedSpace.exp (p.2 • X)) w)))) := by
      convert h1.comp hs using 1
      funext q
      exact (rep_snoc hG hπ hXs hY q.1.1 q.2 _).symm
    have h3 := (ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (g := fun _ : (Fin k → ℝ) × ℝ => (0 : ℝ)) h2
      contDiff_const (le_of_eq rfl)).clm_apply (contDiff_const (c := (1 : ℝ)))
    convert h3 using 2 with p
    have hu := word_mem hG hπ hl' (rep_mem hG hπ hw (exp_mem_UH hG hX p.2))
    have h4 := (((π _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dRep hu hY) :
      HasDerivAt (fun r : ℝ => π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod
        (π (NormedSpace.exp (r • Y)) (word π l (π (NormedSpace.exp (p.2 • X)) w)))) _ 0)
    exact h4.deriv.symm

theorem contDiff_word_curve (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ Y ∈ l, Y ∈ lieG G) :
    ContDiff ℝ ∞ fun s : ℝ => word π l (π (NormedSpace.exp (s • X)) w) := by
  have h1 := (contDiff_word hG hπ hw hX hl 0 Fin.elim0 (fun i => i.elim0)).comp
    ((contDiff_const (c := (0 : Fin 0 → ℝ))).prodMk (contDiff_id (E := ℝ)))
  simpa [Function.comp_def, rep_one hπ] using h1

theorem hasDerivAt_word : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), ∀ X ∈ lieG G, HasDerivAt (fun t : ℝ => word (trRep σ P) l ((trRep σ P) (NormedSpace.exp (t • X)) w)) (word (trRep σ P) l (dRep (trRep σ P) X w)) 0 := by
  intro n ε H _ _ _ σ P G hP h hσ l hl w hw X hX
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have h1 := ((contDiff_word_curve hG hπ hw hX hl).differentiable (by simp) 0).hasDerivAt
  convert h1 using 1
  refine ext_inner_smooth hP h hσ fun u hu => ?_
  obtain ⟨u', -, h2⟩ := word_adjoint hG hπ hl hu
  have h3 := (hasDerivAt_const (0 : ℝ) u).inner ℂ h1
  have h4 := (hasDerivAt_const (0 : ℝ) u').inner ℂ (hasDerivAt_dRep hw hX)
  simp only [h2 _ (rep_mem hG hπ hw (exp_mem_UH hG hX _)), inner_zero_left, add_zero] at h3 h4
  rw [h2 _ (dRep_mem hG hπ hw hX)]
  exact h4.unique h3

end GlobalTheory.SmVecDeriv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieWordCommutesOneParameterDerivativeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieWord_commutes_oneParameter_derivative : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), ∀ X ∈ lieG G, HasDerivAt (fun t : ℝ => word (trRep σ P) l ((trRep σ P) (NormedSpace.exp (t • X)) w)) (word (trRep σ P) l (dRep (trRep σ P) X w)) 0 := by
  first | exact @GlobalTheory.SmVecDeriv.hasDerivAt_word | exact GlobalTheory.SmVecDeriv.hasDerivAt_word | (intros; apply GlobalTheory.SmVecDeriv.hasDerivAt_word <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultGelf

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}

theorem mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {w : M.H τ} :
    w ∈ M.sm τ ↔ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := by rw [sm_eq]

theorem isURep (M : DSModel V S) (τ : D.what₂.Tau) : IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (trRep (M.σ τ) (M.fr τ)) :=
  isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1

theorem rder_apply (hT : IsMultMap θ M J χ T) [inst : DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieG (gramAt D V τ)) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X u) :
    Rder θ V τ X (T (Function.update v τ u)) = T (Function.update v τ w) := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  letI : DecidableEq D.what₂.Tau := fun a b => Classical.propDecidable (a = b)
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hT.cont τ v x
  obtain ⟨m, ls, a, hls, ha⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (mem_sm M τ).1 u.2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => T (@Function.update _ _ (fun a b => Classical.propDecidable (a = b)) v τ u)
      (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := hT.equiv τ _ (exp_mem_UH hG hX t)
      (@Function.update _ _ (fun a b => Classical.propDecidable (a = b)) v τ u) ⟨_, (mem_sm M τ).2 (hmem t)⟩
      (by rw [Function.update_self]; rfl)
    rw [Function.update_idem] at h2
    have h3 := hℓT ⟨_, (mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  have h4 : HasDerivAt (fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ)
      (∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (dRep (trRep (M.σ τ) (M.fr τ)) X u)⟫_ℂ) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
      (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
    simpa using h5
  unfold Rder
  rw [h1, h4.deriv, ← hℓT w, hw, ha _ (dRep_mem hG (isURep M τ) hu hX)]

theorem rderC_apply (hT : IsMultMap θ M J χ T) [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (T (Function.update v τ u)) = T (Function.update v τ w) := by
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  have hp := parts_mem hG (gram_herm (M.fr_gram τ)) Z
  have hu := (mem_sm M τ).1 u.2
  have h1 := rder_apply hT τ v hp.1 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ rfl
  have h2 := rder_apply hT τ v hp.2 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ rfl
  have h3 : w = ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ +
      Complex.I • ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ := Subtype.ext hw
  rw [h3, T.map_update_add, T.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (hT : IsMultMap θ M J χ T) [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (T (Function.update v τ u)) =
        T (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (isURep M τ) Z ((mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply hT τ v Z w _ rfl

theorem gelf_apply : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ T : MMap M, IsMultMap θ M J χ T → ∀ [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ), (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ) → gelf θ V τ k (T v) = T (Function.update v τ w) := by
  intro D θ V S M J χ _ T hT _ τ k v w hw
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply hT τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : w = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [hw, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  rw [h1]
  refine Eq.trans ?_ (map_sum (T.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

end GlobalTheory.MultGelf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_map_carries_gelfandInvariant_to_function : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ T : MMap M, IsMultMap θ M J χ T → ∀ [DecidableEq D.what₂.Tau] (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ), (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ) → gelf θ V τ k (T v) = T (Function.update v τ w) := by
  first | exact @GlobalTheory.MultGelf.gelf_apply | exact GlobalTheory.MultGelf.gelf_apply | (intros; apply GlobalTheory.MultGelf.gelf_apply <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RetieVolTieGAndCdScaleTie
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Vol GlobalTheory.Mem.Per

namespace GlobalTheory.Mem

theorem retie_volTieG_and_cdScaleTie :
    ∀ D : D7, Formalism.L2.Theta.VolTieG (retie D) ∧ cdScaleTie (retie D) := by
  intro D
  refine ⟨GlobalTheory.T.volumesAgreeAdelic_of_trueVolume (retie D) (fun _ => rfl), ?_⟩
  rw [cdScaleTie_iff]
  exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicitySpaceDefiniteContinuousInvariantEqui
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicitySpaceDefiniteContinuousInvariantEqui
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open Classical in
theorem mult_equiv_update {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T T' _ _ h h' =>
    funext z
    simp only [MultilinearMap.add_apply, Pi.add_apply, h, h', rTr]
  | smul r T _ h =>
    funext z
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h, rTr]

theorem multT_cont_left_equiv :
    ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ), AllPlus M → (∀ τ, M.sm τ = ⊤) → Function.Injective (inclT M) → IsTensAct M π → ∀ L ∈ MultT θ M J χ, ∀ x, Continuous (L x) ∧ (∀ γ ∈ GQ V, ∀ h, L x (γ * h) = L x h) ∧ ∀ τ u, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x) := by
  classical
  intro D θ V S M π J χ hp hsm hinj hπ L hL x
  rw [mem_multT] at hL
  have hv : ∀ v, L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm L v := fun v => rfl
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    obtain ⟨a, b, -⟩ := mult_value_left_cont_level θ M J χ _ hL v
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_smul, hv]; exact b.const_smul r
    · rw [map_smul, hv]; simp only [Pi.smul_apply, a γ hγ h]
    · let w : M.sm τ := ⟨M.rep τ (unfr M τ u) (v τ), Submodule.eq_top_iff'.1 (hsm τ) _⟩
      have e : π τ u (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ w) := by
        apply hinj
        rw [hπ]
        unfold inclT actT
        simp only [PiTensorProduct.map_tprod]
        congr 1
        funext ρ
        by_cases hρ : ρ = τ
        · subst hρ
          simp [w]
        · simp [Function.update_of_ne hρ]
      rw [map_smul, map_smul, map_smul, e, hv, hv,
        mult_equiv_update θ M J χ _ hL τ _ (hp.unfr_mem τ u) v w rfl]
      rfl
  | add x y hx hy =>
    obtain ⟨a, b, c⟩ := hx
    obtain ⟨a', b', c'⟩ := hy
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_add (f := _)]; exact a.add a'
    · simp only [map_add (f := _), Pi.add_apply, b γ hγ h, b' γ hγ h]
    · rw [map_add (f := _), map_add (f := _), map_add (f := _), c, c']; rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicitySpaceDefiniteContinuousInvariantEquiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_definite_continuous_invariant_equivariant : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ), AllPlus M → (∀ τ, M.sm τ = ⊤) → Function.Injective (inclT M) → IsTensAct M π → ∀ L ∈ MultT θ M J χ, ∀ x, Continuous (L x) ∧ (∀ γ ∈ GQ V, ∀ h, L x (γ * h) = L x h) ∧ ∀ τ u, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x) := by
  first | exact @GlobalTheory.multT_cont_left_equiv | exact GlobalTheory.multT_cont_left_equiv | (intros; apply GlobalTheory.multT_cont_left_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSumUnitarySubstitutionsEqRowLie
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSumUnitarySubstitutionsEqRowLie
noncomputable section

open MvPolynomial GlobalTheory.DefLift

namespace GlobalTheory.DefLift

section RowLie

variable {ι : Type} {m n : ℕ}


open Classical in
def rowSubst (n : ℕ) (τ : ι) (g : Matrix (Fin m) (Fin m) ℂ) : Pol ι m n →ₐ[ℂ] Pol ι m n :=
  subst (fun _ => 1) (fun ρ => if ρ = τ then g else 1)

theorem rowSubst_X_self (τ : ι) (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) (c : Fin n) :
    rowSubst n τ g (X (τ, j, c)) = ∑ i, g i j • X (τ, i, c) := by
  simp [rowSubst, subst, Matrix.one_apply]

theorem rowSubst_X_ne {τ ρ : ι} (h : ρ ≠ τ) (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) (c : Fin n) :
    rowSubst n τ g (X (ρ, j, c)) = X (ρ, j, c) := by
  simp [rowSubst, subst, Matrix.one_apply, h]

theorem rowSubst_one (τ : ι) (P : Pol ι m n) : rowSubst n τ 1 P = P := by
  have : rowSubst n τ (1 : Matrix (Fin m) (Fin m) ℂ) = AlgHom.id ℂ _ := by
    refine MvPolynomial.algHom_ext fun ⟨ρ, j, c⟩ => ?_
    by_cases h : ρ = τ
    · subst h
      simp [rowSubst_X_self, Matrix.one_apply]
    · simp [rowSubst_X_ne h]
  rw [this]; rfl

theorem rowLie_mul (τ : ι) (k l : Fin m) (P Q : Pol ι m n) :
    rowLie n τ k l (P * Q) = rowLie n τ k l P * Q + P * rowLie n τ k l Q := by
  simp only [rowLie_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem rowLie_X_self (τ : ι) (k l j : Fin m) (c : Fin n) :
    rowLie n τ k l (X (τ, j, c)) = if j = l then X (τ, k, c) else 0 := by
  classical
  rw [rowLie_apply]
  by_cases h : j = l
  · subst h
    simp [pderiv_X, Pi.single_apply]
  · simp [pderiv_X, Pi.single_apply, h]

theorem rowLie_X_ne {τ ρ : ι} (h : ρ ≠ τ) (k l j : Fin m) (c : Fin n) :
    rowLie n τ k l (X (ρ, j, c)) = 0 := by
  classical
  simp [rowLie_apply, pderiv_X, Pi.single_apply, h]

theorem exists_poly_rowSubst_coef (τ : ι) (k l : Fin m) (f : Pol ι m n) (φ : Module.Dual ℂ (Pol ι m n)) :
    ∃ Q : MvPolynomial (Fin m × Fin m) ℂ,
      (∀ g : Matrix (Fin m) (Fin m) ℂ, φ (rowSubst n τ g f) = eval (fun x => g x.1 x.2) Q) ∧
      φ (rowLie n τ k l f) = eval (fun x => (1 : Matrix (Fin m) (Fin m) ℂ) x.1 x.2) (pderiv (k, l) Q) := by
  induction f using MvPolynomial.induction_on generalizing φ with
  | C a => exact ⟨C (φ (C a)), fun g => by simp [rowSubst, subst], by simp [rowLie_apply]⟩
  | add p q hp hq =>
    obtain ⟨P, hP, hP'⟩ := hp φ
    obtain ⟨Q, hQ, hQ'⟩ := hq φ
    exact ⟨P + Q, fun g => by simp only [map_add (f := _), hP, hQ], by simp only [map_add (f := _), hP', hQ']⟩
  | mul_X p v hp =>
    obtain ⟨ρ, j, c⟩ := v
    by_cases h : ρ = τ
    · subst h
      choose P hP hP' using fun b : Fin m => hp (φ ∘ₗ LinearMap.mulRight ℂ (X (ρ, b, c)))
      refine ⟨∑ b, X (b, j) * P b, fun g => ?_, ?_⟩
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, rowSubst_X_self, Finset.mul_sum, map_sum, map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [mul_smul_comm, map_smul, map_mul (eval _), eval_X, ← hP b g]
        rfl
      · have h1 : ∀ b, eval (fun x => (1 : Matrix (Fin m) (Fin m) ℂ) x.1 x.2) (P b) = φ (p * X (ρ, b, c)) := by
          intro b
          rw [← hP b 1, rowSubst_one]; rfl
        set_option synthInstance.maxHeartbeats 100000 in
          rw [rowLie_mul, rowLie_X_self, map_add (f := _), map_sum, map_sum]
        simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, eval_X, ← hP', h1, Finset.sum_add_distrib,
          pderiv_X]
        congr 1
        · simp [Matrix.one_apply]
        · by_cases hj : j = l
          · subst hj
            simp [Pi.single_apply, apply_ite]
          · simp [Pi.single_apply, hj]
    · obtain ⟨P, hP, hP'⟩ := hp (φ ∘ₗ LinearMap.mulRight ℂ (X (ρ, j, c)))
      refine ⟨P, fun g => ?_, ?_⟩
      · rw [map_mul, rowSubst_X_ne h, ← hP g]; rfl
      · rw [rowLie_mul, rowLie_X_ne h, mul_zero, add_zero, ← hP']; rfl

theorem rowLie_mem_span_rowSub {J : Type} [Fintype J] (f : J → Pol ι m n) (τ : ι) (k l : Fin m) :
    (fun j => rowLie n τ k l (f j)) ∈
      Submodule.span ℂ (Set.range fun (u : Matrix.unitaryGroup (Fin m) ℂ) (j : J) => rowSub n τ u (f j)) := by
  classical
  by_contra hn
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hs : ∀ x : J → Pol ι m n, φ x = ∑ j, (φ ∘ₗ LinearMap.single ℂ (fun _ : J => Pol ι m n) j) (x j) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; rfl
  choose Q hQ hQ' using fun j =>
    exists_poly_rowSubst_coef τ k l (f j) (φ ∘ₗ LinearMap.single ℂ (fun _ : J => Pol ι m n) j)
  have h0 : ∑ j, Q j = 0 := by
    refine GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup m _ fun u hu => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [← hQ]
    have hm : φ (fun j => rowSub n τ ⟨u, hu⟩ (f j)) ∈ (⊥ : Submodule ℂ ℂ) :=
      hφ0 ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩)
    rw [Submodule.mem_bot, hs] at hm
    exact hm
  apply hφ
  rw [hs]
  simp only [hQ']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_sum, h0, map_zero, map_zero]

end RowLie

theorem exists_sum_rowSub_eq_rowLie (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin m) :
    ∃ (s : Finset (Matrix.unitaryGroup (Fin m) ℂ)) (c : Matrix.unitaryGroup (Fin m) ℂ → ℂ),
      ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ u ∈ s, c u • rowSub n τ u P = rowLie n τ k l P := by
  obtain ⟨S, hS⟩ : (restrictTotalDegree (ι × Fin m × Fin n) ℂ d).FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1
    (rowLie_mem_span_rowSub (fun j : S => (j : Pol ι m n)) τ k l)
  refine ⟨c.support, c, fun P hP => ?_⟩
  have hP' : P ∈ Submodule.span ℂ (S : Set (Pol ι m n)) := hS ▸ (mem_restrictTotalDegree _ _ _).2 hP
  have key : Set.EqOn (∑ u ∈ c.support, c u • rowSub n τ u : Pol ι m n →ₗ[ℂ] Pol ι m n) (rowLie n τ k l)
      (S : Set (Pol ι m n)) := by
    intro x hx
    have := congrFun hc ⟨x, hx⟩
    simpa [Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply] using this
  have := LinearMap.eqOn_span key hP'
  simpa [LinearMap.sum_apply] using this

end GlobalTheory.DefLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSumUnitarySubstitutionsEqRowLieStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_unitarySubstitutions_eq_rowLie : ∀ (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin m), ∃ (s : Finset (Matrix.unitaryGroup (Fin m) ℂ)) (c : Matrix.unitaryGroup (Fin m) ℂ → ℂ), ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ u ∈ s, c u • rowSub n τ u P = rowLie n τ k l P := by
  first | exact @GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie | exact GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie | (intros; apply GlobalTheory.DefLift.exists_sum_rowSub_eq_rowLie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActEEqOfConjRelated
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BesselCoeffIndep

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [Countable Γ]

theorem haar_eq_of_covolume_one (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {𝓕 𝓕' : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) (h' : IsFundamentalDomain Γ 𝓕' μ') (h1 : μ 𝓕 = 1) (h1' : μ' 𝓕' = 1) :
    μ' = μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ'
  have e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  have h2 : IsFundamentalDomain Γ 𝓕 μ' := h.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h3 : μ' 𝓕 = 1 := (h2.measure_eq h').trans h1'
  rw [e, Measure.smul_apply, h1, smul_eq_mul, mul_one] at h3
  rw [e, h3, one_smul]

theorem setIntegral_mul_right (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (g : G) :
    ∫ x in 𝓕, f (x * g) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (f := (· * g)) ⟨(measurable_mul_const g).aemeasurable, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id fun γ x => mul_assoc _ _ _
  have h1 : μ.map (· * g) 𝓕 = μ 𝓕 :=
    ((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)
  rw [e, Measure.smul_apply, smul_eq_mul] at h1
  have h2 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)
  rw [h2, one_smul] at e
  have hp : MeasurePreserving (· * g) μ μ := ⟨measurable_mul_const g, e⟩
  rw [← hp.setIntegral_preimage_emb (MeasurableEquiv.mulRight g).measurableEmbedding f 𝓕]
  exact h.setIntegral_eq h' (f := fun x => f (x * g)) fun γ x => by
    show f ((γ : G) * x * g) = _
    rw [mul_assoc, hf _ γ.2]

end General

section Character

open GlobalTheory.BesselCompare (hA_add hA_smul hA_sum hA_vec hA_coeff hD_swap_zero co co_surj)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hA_act_e (d : BesselDatum A B ι) {n : GA D B} (hn : n ∈ d.NSet) {l i : Fin d.ρ} (h : l ≤ i) :
    hA B (actV B n (d.e l)) (vecA B (d.f i)) = if l = i then 1 else 0 := by
  obtain ⟨c, hc, e⟩ := hn.1 l
  rw [e, hA_add, hA_coeff B d.e d.f d.ef, hc i h, add_zero, hA_vec, d.ef]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem actE_eq_of_conj_related (d : BesselDatum A B ι) {n : GA D B} (hn : n ∈ d.NSet) (i : Fin d.ρ) :
    B.hD (d.aux i.succ) (d.f i) = 0 ∧ ∃ c : Fin d.ρ → AE D, (∀ l, i < l → c l = 0) ∧
      actV B n (d.aux i.succ) = vecA B (d.aux i.succ) + ∑ l, c l • vecA B (d.e l) := by
  unfold BesselDatum.aux
  by_cases hi : i.1 + 1 = d.ρ
  · have : i.succ = Fin.last d.ρ := Fin.ext hi
    rw [this, Fin.snoc_last]
    obtain ⟨c, e⟩ := hn.2 d.z fun j => hD_swap_zero (d.ez j)
    exact ⟨hD_swap_zero (d.fz i), c, fun l hl => absurd (show i.1 < l.1 from hl) (by have := l.2; omega), e⟩
  · have hlt : i.1 + 1 < d.ρ := by have := i.2; omega
    have : i.succ = Fin.castSucc (⟨i.1 + 1, hlt⟩ : Fin d.ρ) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc]
    obtain ⟨c, hc, e⟩ := hn.1 ⟨i.1 + 1, hlt⟩
    refine ⟨?_, c, fun l hl => hc l (show i.1 + 1 ≤ l.1 from hl), e⟩
    rw [d.ef, if_neg (fun h => by have : i.1 + 1 = i.1 := congrArg Fin.val h; omega)]

theorem simpleSum_mul (d : BesselDatum A B ι) {n n' : GA D B} (hn : n ∈ d.NSet) (hn' : n' ∈ d.NSet) :
    d.simpleSum (n * n') = d.simpleSum n + d.simpleSum n' := by
  unfold BesselDatum.simpleSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h0, c, hc, e⟩ := actE_eq_of_conj_related d hn' i
  have e1 : actV B (n * n') (d.aux i.succ) = actV B n (d.aux i.succ) + ∑ l, c l • actV B n (d.e l) := by
    have : actV B (n * n') (d.aux i.succ) = (mt B n).mulVec (actV B n' (d.aux i.succ)) := mulVec_mul _ _ _
    rw [this, e, Matrix.mulVec_add, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rfl
  rw [e1, e, hA_add, hA_add, hA_coeff B d.e d.f d.ef, hA_vec, h0, RingHom.map_zero, zero_add, hA_sum,
    Finset.sum_eq_single i]
  · rw [hA_smul, hA_act_e d hn le_rfl, if_pos rfl, mul_one]
  · intro l _ hl
    rw [hA_smul]
    rcases lt_or_ge i l with h | h
    · rw [hc l h, zero_mul]
    · rw [hA_act_e d hn h, if_neg hl, mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem psiN_mul (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) {n n' : GA D B} (hn : n ∈ d.NSet)
    (hn' : n' ∈ d.NSet) : d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n' := by
  unfold BesselDatum.psiN
  rw [simpleSum_mul d hn hn', mul_add, LinearMap.map_add (f := _), AddChar.map_add_eq_mul]

theorem psiN_rat (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) {n : GA D B}
    (hn : n ∈ GQ B) : d.psiN ψ n = 1 := by
  obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hn)
  have h1 : mt B n = (g : Matrix _ _ D.host.E).map (incA D) := (congrArg Units.val hg).symm
  have h2 : ∀ v, ∃ w, actV B n v = vecA B w := fun v => by
    obtain ⟨w, hw⟩ := co_surj B ((g : Matrix _ _ D.host.E).mulVec (co B v))
    refine ⟨w, funext fun k => ?_⟩
    have : vecA B w k = incA D (co B w k) := rfl
    rw [this, hw, RingHom.map_mulVec, actV, h1]
    rfl
  choose w hw using h2
  have h3 : ∀ e : D.host.E, Algebra.trace (AF D.host.F) (AE D) (incA D e) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := fun e => by
    show Algebra.trace (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) (1 ⊗ₜ e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  unfold BesselDatum.psiN BesselDatum.simpleSum
  simp only [hw, hA_vec]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum (incA D), ← RingHom.map_mul, h3, hψ.2.2.1]

end Character

theorem coeff_indep_and_equivariant : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ F : GA D B → ℂ, (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → (∀ ν' 𝓝', d.IsUnitPair ν' 𝓝' → d.coeff ψ ν' 𝓝' F = d.coeff ψ ν 𝓝 F) ∧ ∀ n ∈ d.N, ∀ g, d.coeff ψ ν 𝓝 F (n * g) = d.psiN ψ n * d.coeff ψ ν 𝓝 F g := by
  intro D A B ι d ψ hψ F hF ν 𝓝 ⟨hν, h𝓝, h1⟩
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hcl := (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).2
  have : LocallyCompactSpace d.N := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology d.N := TopologicalSpace.Subtype.secondCountableTopology _
  have : BorelSpace d.N := Subtype.borelSpace _
  have : Countable d.NQ :=
    Function.Injective.countable (f := fun γ : d.NQ => (⟨γ.1.1, γ.2⟩ : GQ B)) fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun t : GQ B => (t : GA D B)) hab))
  have hS : ∀ n ∈ d.N, n ∈ d.NSet := fun n hn => (GlobalTheory.BesselClosed.N_eq_and_isClosed D A B ι d).1 ▸ SetLike.mem_coe.2 hn
  have hmul : ∀ n ∈ d.N, ∀ n' ∈ d.N, d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n' := fun n hn n' hn' =>
    psiN_mul d ψ (hS n hn) (hS n' hn')
  have hrat : ∀ n ∈ d.N, n ∈ GQ B → d.psiN ψ n = 1 := fun n _ hn' => psiN_rat d ψ hψ.1 hn'
  have hinv : ∀ g, ∀ γ ∈ d.NQ, ∀ x : d.N,
      F (((γ * x : d.N) : GA D B) * g) * star (d.psiN ψ ((γ * x : d.N) : GA D B)) =
        F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B)) := fun g γ hγ x => by
    rw [Subgroup.coe_mul, mul_assoc, hF (γ : GA D B) hγ, hmul _ γ.2 _ x.2, hrat _ γ.2 hγ, one_mul]
  refine ⟨fun ν' 𝓝' ⟨hν', h𝓝', h1'⟩ => ?_, fun n hn g => ?_⟩
  · obtain rfl := haar_eq_of_covolume_one d.NQ ν ν' h𝓝 h𝓝' h1 h1'
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup d.NQ
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup d.NQ ν'
    funext g
    exact h𝓝'.setIntegral_eq h𝓝 (f := fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B)))
      fun γ x => hinv g γ γ.2 x
  · have key := setIntegral_mul_right d.NQ ν h𝓝 (by rw [h1]; exact ENNReal.one_ne_top)
      (fun x : d.N => F ((x : GA D B) * g) * star (d.psiN ψ (x : GA D B))) (hinv g) ⟨n, hn⟩
    unfold BesselDatum.coeff
    rw [← key, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hu : d.psiN ψ n * star (d.psiN ψ n) = 1 := by
      have : ‖d.psiN ψ n‖ = 1 := hψ.1.2.1 _
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]; simp
    simp only [Subgroup.coe_mul]
    rw [hmul _ x.2 _ hn, star_mul', mul_assoc (x : GA D B)]
    linear_combination (-(F (x * (n * g)) * star (d.psiN ψ x))) * hu

end GlobalTheory.Mem.BesselCoeffIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBesselExchangeGroupIffRootExchange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBesselExchangeGroupIffRootExchange
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.ExStruct

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hA_half {ε : AE D} {y : Fin B.rank → AE D} (hy : ε • y = y) (x) : hA B x y = cA D ε * hA B x y := by
  rw [← hA_smul_right, hy]

theorem eps_hA {ε : AE D} (h0 : ε * cA D ε = 0) {y : Fin B.rank → AE D} (hy : ε • y = y) (x) :
    ε * hA B x y = 0 := by
  rw [hA_half hy, ← mul_assoc, h0, zero_mul]

theorem hA_smul_zero {ε : AE D} (h0 : ε * cA D ε = 0) {y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') (x) : hA B x y' • y = 0 := by
  rw [← hy, smul_smul, mul_comm, eps_hA h0 hy', zero_smul]

theorem hA_halves {ε : AE D} (h0 : ε * cA D ε = 0) {y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') : hA B y y' = 0 := by
  rw [← hy, hA_smul, eps_hA h0 hy']

theorem isK_mul {ε : AE D} (h0 : ε * cA D ε = 0) {v y y' : Fin B.rank → AE D} (hy : ε • y = y)
    (hy' : ε • y' = y') (hv' : hA B y' v = 0) (hv : hA B v y = 0) {k k' : GA D B} (hk : IsK B v y k)
    (hk' : IsK B v y' k') : IsK B v (y + y') (k * k') := by
  intro x
  rw [mulVec_mul, hk', hk]
  simp only [hA_add, hA_sub, hA_smul, hA_add_right, hv, hv', hA_halves h0 hy' hy, mul_zero, add_zero, sub_zero,
    add_smul, smul_add, mul_comm (hA B x y'), mul_smul, hA_smul_zero h0 hy hy', smul_zero, zero_smul]
  abel

theorem isK_eps {ε : AE D} (h0 : ε * cA D ε = 0) {v y : Fin B.rank → AE D} (hy : ε • y = y) {k : GA D B}
    (hk : IsK B v y k) (x) : ε • ((mt B k).mulVec x - x) = -(hA B x v • y) := by
  rw [hk, add_sub_assoc, add_sub_cancel_left, smul_sub, smul_smul, eps_hA h0 hy, zero_smul, zero_sub, smul_comm, hy]

theorem isK_supp {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) {v y : Fin B.rank → AE D} (hy : ε • y = y)
    {k : GA D B} (hk : IsK B v y k) : SuppAt ε B k := by
  rw [suppAt_iff_vec]
  intro x
  have hc : cA D ε • y = 0 := by rw [← hy, smul_smul, mul_comm, h0, zero_smul]
  rw [add_smul, isK_eps h0 hy hk, hk, add_sub_assoc, add_sub_cancel_left, smul_sub, smul_smul, ← hA_half hy,
    smul_comm, hc, smul_zero]
  abel

theorem eq_one_of_half {ε : AE D} {u : GA D B} (hu : SuppAt ε B u) (h : ∀ x, ε • ((mt B u).mulVec x - x) = 0) :
    u = 1 := by
  refine mt_ext fun x => ?_
  rw [mt_one, Matrix.one_mulVec, ← sub_eq_zero, ← suppAt_iff_vec.1 hu x, add_smul, h, zero_add]
  refine hA_nondeg fun y => ?_
  have e : (mt B u).mulVec (ε • y) = ε • y := by
    have := h y
    rwa [smul_sub, sub_eq_zero, ← Matrix.mulVec_smul] at this
  rw [hA_smul, ← hA_smul_right, hA_sub]
  conv_lhs => rw [← e]
  rw [hA_mt, e, sub_self]

theorem iA_eq (t : Fin A.rank → AE D) : iA ι t = ∑ l, t l • vecA B (ι (A.frame l)) := by
  rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]

theorem dual_iA (d : BesselDatum A B ι) (i) (t) : hA B (vecA B (dual d i)) (iA ι t) = 0 :=
  hA_vec_iA (dual_perp d i) t

theorem iA_dual (d : BesselDatum A B ι) (i) (t) : hA B (iA ι t) (vecA B (dual d i)) = 0 := by
  rw [← hA_herm, dual_iA, map_zero]

theorem vec_dual (d : BesselDatum A B ι) (i) (x : A.V) : hA B (vecA B (ι x)) (vecA B (dual d i)) = 0 := by
  rw [← hA_herm, hA_vec, dual_perp, map_zero, map_zero]

theorem mem_exSet (d : BesselDatum A B ι) {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) (i) {t} (ht : ε • t = t)
    {k : GA D B} (hk : IsK B (vecA B (dual d i)) (iA ι t) k) :
    SuppAt ε B k ∧
    (∀ x : A.V, ε • (actV B k (ι x) - vecA B (ι x)) = 0) ∧
    (∀ l, ε • (actV B k (d.f l) - vecA B (d.f l)) = 0) ∧
    (∀ l, l ≠ i → ε • (actV B k (d.aux l) - vecA B (d.aux l)) = 0) ∧
      ε • (actV B k (d.aux i) - vecA B (d.aux i)) = -iA ι t := by
  have hy : ε • iA ι t = iA ι t := by rw [← iA_smul, ht]
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d
  unfold actV
  refine ⟨isK_supp h1 h0 hy hk, fun x => ?_, fun l => ?_, fun l hl => ?_, ?_⟩
  · rw [isK_eps h0 hy hk, vec_dual, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p2, map_zero, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p1, if_neg hl, map_zero, zero_smul, neg_zero]
  · rw [isK_eps h0 hy hk, hA_vec, p1, if_pos rfl, map_one, one_smul]

theorem exists_k (d : BesselDatum A B ι) {ε : AE D} (h0 : ε * cA D ε = 0) (i) {t} (ht : ε • t = t) :
    ∃ k : GA D B, IsK B (vecA B (dual d i)) (iA ι t) k := by
  obtain ⟨K, -, hK⟩ := GlobalTheory.T.exists_continuous_unitaryRootExchangeMap D B ε h0 (vecA B (dual d i))
  exact ⟨_, hK ⟨iA ι t, by rw [← iA_smul, ht], dual_iA d i t⟩⟩

theorem isK_one (v : Fin B.rank → AE D) : IsK B v 0 1 := fun x => by
  rw [mt_one, Matrix.one_mulVec, hA_zero_right, zero_smul, smul_zero, add_zero, sub_zero]

theorem isK_unique {v y : Fin B.rank → AE D} {k k' : GA D B} (h : IsK B v y k) (h' : IsK B v y k') : k = k' :=
  mt_ext fun x => (h x).trans (h' x).symm

def kGrp (d : BesselDatum A B ι) {ε : AE D} (h0 : ε * cA D ε = 0) (i : Fin (d.ρ + 1)) : Subgroup (GA D B) where
  carrier := {g | ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g}
  one_mem' := ⟨0, smul_zero _, by rw [iA, Matrix.mulVec_zero]; exact isK_one _⟩
  mul_mem' := by
    rintro g g' ⟨t, ht, hg⟩ ⟨t', ht', hg'⟩
    refine ⟨t + t', by rw [smul_add, ht, ht'], ?_⟩
    rw [iA_add]
    exact isK_mul h0 (by rw [← iA_smul, ht]) (by rw [← iA_smul, ht']) (iA_dual d i _) (dual_iA d i _) hg hg'
  inv_mem' := by
    rintro g ⟨t, ht, hg⟩
    have ht' : ε • (-t) = -t := by rw [smul_neg, ht]
    obtain ⟨k, hk⟩ := exists_k d h0 i ht'
    have := isK_mul h0 (by rw [← iA_smul, ht]) (by rw [← iA_smul, ht']) (iA_dual d i _) (dual_iA d i _) hg hk
    rw [iA_neg, add_neg_cancel] at this
    rw [inv_eq_of_mul_eq_one_right (isK_unique this (isK_one _))]
    exact ⟨-t, ht', hk⟩

theorem mulVec_comb (L : Matrix (Fin B.rank) (Fin B.rank) (AE D)) {a : ℕ} (u : Fin a → Fin B.rank → AE D)
    (hu : ∀ i, L.mulVec (u i) = 0) (r : Fin a → AE D) : L.mulVec (∑ i, r i • u i) = 0 := by
  refine Finset.sum_induction _ (fun x => L.mulVec x = 0) (fun x y hx hy => ?_) (Matrix.mulVec_zero _) fun i _ => ?_
  · rw [Matrix.mulVec_add, hx, hy, add_zero]
  · rw [Matrix.mulVec_smul, hu, smul_zero]

theorem mulVec_zero_of (d : BesselDatum A B ι) (L : Matrix (Fin B.rank) (Fin B.rank) (AE D))
    (a1 : ∀ x, L.mulVec (vecA B (ι x)) = 0) (a2 : ∀ l, L.mulVec (vecA B (d.f l)) = 0)
    (a3 : ∀ l, L.mulVec (vecA B (d.aux l)) = 0) (x) : L.mulVec x = 0 := by
  obtain ⟨t, e⟩ := (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).2.2 x
  rw [e, iA_eq, Matrix.mulVec_add, Matrix.mulVec_add, mulVec_comb L _ (fun l => a1 (A.frame l)),
    mulVec_comb L _ a3, mulVec_comb L _ a2, add_zero, add_zero]

theorem eq_of_half {ε : AE D} {g k : GA D B} (g1 : SuppAt ε B g) (k1 : SuppAt ε B k)
    (h : ∀ x, ε • ((mt B g).mulVec x - x) = ε • ((mt B k).mulVec x - x)) : k = g := by
  refine inv_mul_eq_one.1 (eq_one_of_half (suppAt_mul (suppAt_inv k1) g1) fun x => ?_)
  have e : ε • (mt B g).mulVec x = ε • (mt B k).mulVec x := by
    have := h x
    rwa [smul_sub, smul_sub, sub_left_inj] at this
  have := congrArg (mt B k⁻¹).mulVec e
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_inv_cancel, ← mulVec_mul] at this
  rw [smul_sub, this, sub_self]

set_option maxHeartbeats 800000 in
theorem exSet_sub (d : BesselDatum A B ι) {ε : AE D} (h1 : ε * ε = ε) (h0 : ε * cA D ε = 0) (i) {g : GA D B}
    (hg : g ∈ d.ExSet ε i) : g ∈ kGrp d h0 i := by
  obtain ⟨g1, g2, g3, g4, y, g5⟩ := hg
  have ht : ε • (-(ε • y)) = -(ε • y) := by rw [smul_neg, smul_smul, h1]
  obtain ⟨k, hk⟩ := exists_k d h0 i ht
  obtain ⟨k1, k2, k3, k4, k5⟩ := mem_exSet d h1 h0 i ht hk
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin B.rank) (Fin B.rank) (AE D),
      ∀ x, L.mulVec x = ε • ((mt B g).mulVec x - x) - ε • ((mt B k).mulVec x - x) :=
    ⟨ε • (mt B g - mt B k), fun x => by
      rw [← smul_sub, sub_sub_sub_cancel_right, ← Matrix.sub_mulVec, ← Matrix.smul_mulVec]⟩
  have a1 : ∀ x, L.mulVec (vecA B (ι x)) = 0 := fun x => by
    rw [hL]; exact sub_eq_zero.2 ((g2 x).trans (k2 x).symm)
  have a2 : ∀ l, L.mulVec (vecA B (d.f l)) = 0 := fun l => by
    rw [hL]; exact sub_eq_zero.2 ((g3 l).trans (k3 l).symm)
  have a3 : ∀ l, L.mulVec (vecA B (d.aux l)) = 0 := fun l => by
    rw [hL]
    by_cases hl : l = i
    · subst hl
      refine sub_eq_zero.2 (g5.trans (Eq.symm (k5.trans ?_)))
      rw [iA_neg, neg_neg, iA_smul]; rfl
    · exact sub_eq_zero.2 ((g4 l hl).trans (k4 l hl).symm)
  have a4 : ∀ x, L.mulVec x = 0 := mulVec_zero_of d L a1 a2 a3
  rw [← eq_of_half g1 k1 fun x => sub_eq_zero.1 ((hL x).symm.trans (a4 x))]
  exact ⟨_, ht, hk⟩

theorem mem_Ex_iff : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ε : AE D), IsSplitIdem D ε → ∀ (i : Fin (d.ρ + 1)) (g : GA D B), g ∈ d.Ex ε i ↔ ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g := by
  intro D A B ι d ε he i g
  have h1 : ε * ε = ε := he.1
  have h0 : ε * cA D ε = 0 := he.2.1
  refine ⟨fun hg => (Subgroup.closure_le (kGrp d h0 i)).2 (fun _ h => exSet_sub d h1 h0 i h) hg, ?_⟩
  rintro ⟨t, ht, hk⟩
  obtain ⟨k1, k2, k3, k4, k5⟩ := mem_exSet d h1 h0 i ht hk
  refine Subgroup.subset_closure ⟨k1, k2, k3, k4, -t, k5.trans ?_⟩
  show _ = ε • iA ι (-t)
  rw [← iA_smul, smul_neg, ht, iA_neg]

end GlobalTheory.RootExch.ExStruct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBesselExchangeGroupIffRootExchangeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_besselExchangeGroup_iff_rootExchange : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ε : AE D), IsSplitIdem D ε → ∀ (i : Fin (d.ρ + 1)) (g : GA D B), g ∈ d.Ex ε i ↔ ∃ t, ε • t = t ∧ IsK B (vecA B (dual d i)) (iA ι t) g := by
  first | exact @GlobalTheory.RootExch.ExStruct.mem_Ex_iff | exact GlobalTheory.RootExch.ExStruct.mem_Ex_iff | (intros; apply GlobalTheory.RootExch.ExStruct.mem_Ex_iff <;> assumption)
end
end
