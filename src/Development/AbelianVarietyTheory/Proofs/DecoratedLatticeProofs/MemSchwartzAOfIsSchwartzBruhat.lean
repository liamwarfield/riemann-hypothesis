module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}

theorem exists_finSection (D : D7) :
    ∃ s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D, Continuous s ∧ (∀ a, finPart D (s a) = a) ∧
      ∀ a, infPart D (s a) = 0 := by
  obtain ⟨e, he, -, hec⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inr _ _), hec.comp (continuous_const.prodMk continuous_id),
    fun a => ?_, fun a => ?_⟩
  · have := (he (e.symm (0, a))).2
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  · have := (he (e.symm (0, a))).1
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm

theorem isOpen_intAE (D : D7) : IsOpen (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
  have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
  rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
  have hs : (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) = {z | ∃ y ∈ intAE D, z = 1 • y} := by
    ext z
    constructor
    · intro h
      exact ⟨z, h, (one_nsmul z).symm⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hs]
  exact this

theorem isCompact_intAE (D : D7) : IsCompact (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨C, hC, hCd⟩ := GlobalTheory.SmoothForms.Cover.exists_compact_denom D 1 one_pos
  exact hC.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (isOpen_intAE D)) fun y hy => hCd y (by simpa using hy)

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}

def chartM (σ : (D.what₂.Tau → ℂ) →+ AE D) (m n : ℕ) : (D.what₂.Tau → Fin m → Fin n → ℂ) →+ Mx D m n where
  toFun c := Matrix.of fun i j => σ fun τ => c τ i j
  map_zero' := by
    funext i j
    show σ (fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ i j) = 0
    exact σ.map_zero
  map_add' c c' := by
    funext i j
    show σ (fun τ => (c + c') τ i j) = σ (fun τ => c τ i j) + σ (fun τ => c' τ i j)
    exact σ.map_add _ _

theorem continuous_chartM {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : Continuous σ) (m n : ℕ) :
    Continuous (chartM σ m n) :=
  continuous_pi fun i => continuous_pi fun j => hσ.comp (continuous_pi fun τ =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ)))

theorem compAt_chartM {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n : ℕ}
    (c : D.what₂.Tau → Fin m → Fin n → ℂ) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    compAt θ τ (chartM σ m n c) i j = c τ i j :=
  hσ.comp (fun τ => c τ i j) τ

theorem finPart_chartM {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n : ℕ}
    (c : D.what₂.Tau → Fin m → Fin n → ℂ) : (chartM σ m n c).map (finPart D) = 0 := by
  funext i j
  exact hσ.fin _

theorem decomp {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D} (hsf : ∀ a, finPart D (s a) = a) (hsi : ∀ a, infPart D (s a) = 0)
    {m n : ℕ} (y : Mx D m n) :
    y = s.mapMatrix (y.map (finPart D)) + chartM σ m n (fun τ i j => compAt θ τ y i j) := by
  funext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · show finPart D (y i j - (s (finPart D (y i j)) + σ fun τ => compAt θ τ y i j)) = 0
    rw [RingHom.map_sub, RingHom.map_add (f := _), hsf, hσ.fin, add_zero, sub_self]
  · show θ τ (infPart D (y i j - (s (finPart D (y i j)) + σ fun τ => compAt θ τ y i j))) = 0
    rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_add (f := _), hsi, hσ.comp, RingHom.map_zero, zero_add]
    exact sub_self _

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}


open Classical in
theorem coset_mem_SB {m n : ℕ} (W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)))
    (hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))))
    (hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))))
    (q : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) :
    (fun a : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E =>
      if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = q then (1 : ℂ) else 0) ∈
      GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hmk : IsLocallyConstant
      (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => (a : _ ⧸ W)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W},
      hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩
  refine ⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩
  have hcl : IsClosed (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    AddSubgroup.isClosed_of_isOpen _ hWo
  let K : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    (fun b : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => q.out + b) '' (W : Set _)
  have hKc : IsCompact K := hWc.image (continuous_const.add continuous_id)
  have hKcl : IsClosed K := (Homeomorph.addLeft q.out).isClosedMap _ hcl
  refine HasCompactSupport.intro' hKc hKcl fun x hx => ?_
  show (if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from x) : _ ⧸ W) = q then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro hq
  apply hx
  have h1 : (QuotientAddGroup.mk q.out : _ ⧸ W) = QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from x) := by
    rw [hq, QuotientAddGroup.out_eq']
  exact ⟨-q.out + (show Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) from x), QuotientAddGroup.eq.1 h1,
    add_neg_cancel_left _ _⟩

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor


open Classical in
theorem mem_schwartzA_of_isSchwartzBruhat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  intro D θ hθ m n φ hφ
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, hsc, hsf, hsi⟩ := exists_finSection D
  obtain ⟨U, hUo, hU⟩ := hφ.level
  obtain ⟨K, hK, hKs⟩ := hφ.supp
  let S : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) →+ Mx D m n := s.mapMatrix
  have hSc : Continuous S := continuous_id.matrix_map hsc
  have hSi : ∀ a, (S a).map (infPart D) = 0 := fun a => by
    funext i j
    exact hsi (a i j)
  let W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | S a ∈ U ∧ ∀ i j, a i j ∈ intAE D}
      add_mem' := fun {a b} ha hb => ⟨by rw [S.map_add]; exact U.add_mem ha.1 hb.1,
        fun i j => (intAE D).add_mem (ha.2 i j) (hb.2 i j)⟩
      zero_mem' := ⟨by rw [S.map_zero]; exact U.zero_mem, fun _ _ => (intAE D).zero_mem⟩
      neg_mem' := fun {a} ha => ⟨by rw [S.map_neg]; exact U.neg_mem ha.1, fun i j => (intAE D).neg_mem (ha.2 i j)⟩ }
  have hWe : (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      S ⁻¹' U ∩ ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact (hUo.preimage hSc).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i)))
  have hcl : IsClosed (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    AddSubgroup.isClosed_of_isOpen _ hWo
  have hbig : IsCompact {a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) | ∀ i j, a i j ∈ intAE D} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_intAE D
  have hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    hbig.of_isClosed_subset hcl fun a ha => ha.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => {b | -a + b ∈ W})
    (fun a => hWo.preimage (continuous_const.add continuous_id))
    (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)
  let T : Finset (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) := t.image QuotientAddGroup.mk
  let k := Module.finrank ℝ (D.what₂.Tau → Fin m → Fin n → ℂ)
  let eZ : (D.what₂.Tau → Fin m → Fin n → ℂ) ≃L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let L : (Fin k → ℝ) →+ Mx D m n := (chartM σ m n).comp eZ.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom
  have hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L :=
    ⟨(continuous_chartM hσ.cont m n).comp eZ.symm.continuous, fun t => finPart_chartM hσ _⟩
  have hLi : Function.Injective L := by
    intro t t' h
    apply eZ.symm.injective
    funext τ i j
    have e := congrArg (fun y => compAt θ τ y i j) h
    simp only [L, AddMonoidHom.coe_comp, Function.comp_apply] at e
    rw [compAt_chartM hσ, compAt_chartM hσ] at e
    exact e
  choose g hg using fun q : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W =>
    hφ.schwartz k L hL hLi (S q.out)
  let f : (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) →
      SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ :=
    fun q => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eZ (g q)
  have hf : ∀ q c, f q c = φ (S q.out + chartM σ m n c) := fun q c => by
    show g q (eZ c) = _
    rw [hg q (eZ c)]
    congr 2
    show chartM σ m n (eZ.symm (eZ c)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  let gf : (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) →
      (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun q a =>
    if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = q then (1 : ℂ) else 0
  have key : φ = ∑ q ∈ T, fun x : Mx D m n =>
      f q (fun τ i j => compAt θ τ x i j) * gf q (fun i j => finPart D (x i j)) := by
    funext y
    rw [Finset.sum_apply]
    let a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) := fun i j => finPart D (y i j)
    let c : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ y i j
    have hdec : y = S a + chartM σ m n c := decomp hσ hsf hsi y
    show φ y = ∑ q ∈ T, f q c * (if (QuotientAddGroup.mk a : _ ⧸ W) = q then (1 : ℂ) else 0)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hT
    · rw [hf]
      have hmem : -(QuotientAddGroup.mk a : _ ⧸ W).out + a ∈ W := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
      have e := hU (S (-(QuotientAddGroup.mk a : _ ⧸ W).out + a)) hmem.1 (hSi _)
        (S (QuotientAddGroup.mk a : _ ⧸ W).out + chartM σ m n c)
      rw [← e]
      conv_lhs => rw [hdec]
      congr 1
      rw [S.map_add, S.map_neg]
      abel
    · by_contra hne
      obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (ht (hKs y hne))
      have hba : (QuotientAddGroup.mk b : _ ⧸ W) = QuotientAddGroup.mk a := QuotientAddGroup.eq.2 hab
      exact hT (Finset.mem_image.2 ⟨b, hb, hba⟩)
  rw [key]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨f q, gf q, coset_mem_SB W hWo hWc q, rfl⟩

end GlobalTheory.SchwartzBruhatTensor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.SeeSaw GlobalTheory.ChiGrid GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiTransfer

variable {D : D7}

def sumDec (A B : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A B) A B where
  iA := (fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin B.rank) (Fin A.rank) D.host.E)).submatrix
    finSumFinEquiv.symm id
  iB := (fromRows (0 : Matrix (Fin A.rank) (Fin B.rank) D.host.E) (1 : Matrix (Fin B.rank) (Fin B.rank) D.host.E)).submatrix
    finSumFinEquiv.symm id
  isoA := by
    rw [GlobalTheory.Doubling.gram_hsum, conjTranspose_submatrix]
    unfold GlobalTheory.Doubling.blkMat
    simp [submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  isoB := by
    rw [GlobalTheory.Doubling.gram_hsum, conjTranspose_submatrix]
    unfold GlobalTheory.Doubling.blkMat
    simp [submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  orth := by
    rw [GlobalTheory.Doubling.gram_hsum, conjTranspose_submatrix]
    unfold GlobalTheory.Doubling.blkMat
    simp [submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  rank_add := rfl

theorem finPart_conj (z : AE D) : finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem infPart_conj (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fin_dagger (S T : HSp D) {x : WO S T} (hx : x.map (finPart D) = 0) : (dagger S T x).map (finPart D) = 0 := by
  refine map_mul_eq_zero_right _ _ (map_mul_eq_zero_left _ ?_ _)
  funext i j
  have := congrFun (congrFun hx j) i
  change finPart D (x j i) = 0 at this
  change finPart D (cA D (x j i)) = 0
  rw [finPart_conj, this, map_zero]

theorem inf_dagger (S T : HSp D) {x : WO S T} (hx : x.map (infPart D) = 0) : (dagger S T x).map (infPart D) = 0 := by
  refine map_mul_eq_zero_right _ _ (map_mul_eq_zero_left _ ?_ _)
  funext i j
  have := congrFun (congrFun hx j) i
  change infPart D (x j i) = 0 at this
  change infPart D (cA D (x j i)) = 0
  rw [infPart_conj, this, map_zero]

def daggerHom (S T : HSp D) : WO S T →+ WO T S where
  toFun := dagger S T
  map_zero' := by simp [dagger]
  map_add' x y := by simp only [dagger, adj_add, Matrix.add_mul, Matrix.mul_add]

theorem dagger_zero (S T : HSp D) : dagger S T 0 = 0 := (daggerHom S T).map_zero

theorem continuous_dagger (S T : HSp D) : Continuous (dagger S T) :=
  continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)

theorem dagger_rat (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    dagger S T (rat γ) = rat (S.gram⁻¹ * (γᴴ * T.gram)) := by
  rw [rat_mul, rat_mul]; rfl

theorem giA_negSp (S : HSp D) : giA (negSp S) = -giA S := by
  have : (negSp S).gram⁻¹ = -S.gram⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [negSp_gram, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_nonsing_inv _ (gram_isUnit_det S)]
  rw [giA, this, rat_neg]; rfl

theorem symplOH_dagger (S T : HSp D) (x y : WO T S) :
    symplOH S T (dagger T S x) (dagger T S y) = symplOH (negSp T) S x y := by
  have h1 : hO S T (dagger T S x) (dagger T S y) = hO T S y x := by
    simp only [hO_eq_trace, dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel, gA_giA_cancel]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : hO (negSp T) S x y = -hO T S x y := by
    rw [hO_eq_trace, hO_eq_trace, giA_negSp, Matrix.neg_mul, trace_neg]
  rw [symplOH_eq, h1, ← symplOH_eq, symplOH_skew, symplOH_eq, symplOH_eq, h2, map_neg]

variable {W A A' : HSp D} (d : OrthDec W A (negSp A')) (S : HSp D)

def fstH : WO W S →+ WO A S := (AddMonoidHom.fst _ _).comp (d.resS S).toAddMonoidHom

def sndH : WO W S →+ WO S A' := (daggerHom A' S).comp ((AddMonoidHom.snd _ _).comp (d.resS S).toAddMonoidHom)

def inlH : WO A S →+ WO W S := (d.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

def inrH : WO S A' →+ WO W S :=
  (d.resS S).symm.toAddMonoidHom.comp ((AddMonoidHom.inr _ _).comp (daggerHom S A'))

theorem fstH_apply (x : WO W S) : fstH d S x = (d.resS S x).1 := rfl
theorem sndH_apply (x : WO W S) : sndH d S x = dagger A' S (d.resS S x).2 := rfl
theorem inlH_apply (u : WO A S) : inlH d S u = (d.resS S).symm (u, 0) := rfl
theorem inrH_apply (v : WO S A') : inrH d S v = (d.resS S).symm (0, dagger S A' v) := rfl

theorem fst_inl (u : WO A S) : fstH d S (inlH d S u) = u := by
  rw [fstH_apply, inlH_apply, AddEquiv.apply_symm_apply]
theorem fst_inr (v : WO S A') : fstH d S (inrH d S v) = 0 := by
  rw [fstH_apply, inrH_apply, AddEquiv.apply_symm_apply]
theorem snd_inl (u : WO A S) : sndH d S (inlH d S u) = 0 := by
  rw [sndH_apply, inlH_apply, AddEquiv.apply_symm_apply]; exact dagger_zero A' S
theorem snd_inr (v : WO S A') : sndH d S (inrH d S v) = v := by
  rw [sndH_apply, inrH_apply, AddEquiv.apply_symm_apply]; exact dagger_dagger S A' v

theorem continuous_fstH : Continuous (fstH d S) := continuous_fst.comp (d.continuous_resS S)
theorem continuous_sndH : Continuous (sndH d S) :=
  (continuous_dagger A' S).comp (continuous_snd.comp (d.continuous_resS S))
theorem continuous_inlH : Continuous (inlH d S) :=
  (d.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)
theorem continuous_inrH : Continuous (inrH d S) :=
  (d.continuous_resS_symm S).comp (continuous_const.prodMk (continuous_dagger S A'))

theorem symplOH_split (x y : WO W S) :
    symplOH W S x y = symplOH A S (fstH d S x) (fstH d S y) + symplOH S A' (sndH d S x) (sndH d S y) := by
  rw [d.symplOH_resS, sndH_apply, sndH_apply, symplOH_dagger]; rfl

theorem map_resS_symm {B : Type} [CommRing B] (φ : AE D →+* B) {u : WO A S} {v : WO (negSp A') S}
    (hu : u.map φ = 0) (hv : v.map φ = 0) : ((d.resS S).symm (u, v)).map φ = 0 := by
  rw [d.resS_symm_apply, Matrix.map_add _ (map_add φ), map_mul_eq_zero_left φ hu, map_mul_eq_zero_left φ hv, add_zero]

theorem map_inlH {B : Type} [CommRing B] (φ : AE D →+* B) {u : WO A S} (hu : u.map φ = 0) : (inlH d S u).map φ = 0 :=
  map_resS_symm d S φ hu (Matrix.map_zero _ φ.map_zero)

theorem fin_inrH {v : WO S A'} (hv : v.map (finPart D) = 0) : (inrH d S v).map (finPart D) = 0 :=
  map_resS_symm d S _ (Matrix.map_zero _ (finPart D).map_zero) (fin_dagger S A' hv)

theorem inf_inrH {v : WO S A'} (hv : v.map (infPart D) = 0) : (inrH d S v).map (infPart D) = 0 :=
  map_resS_symm d S _ (Matrix.map_zero _ (infPart D).map_zero) (inf_dagger S A' hv)

def join (C : WO A S → WO S A' → ℂ) : WO W S → ℂ := fun x => C (d.resS S x).1 (dagger A' S (d.resS S x).2)

theorem join_apply (C : WO A S → WO S A' → ℂ) (x : WO W S) : join d S C x = C (fstH d S x) (sndH d S x) := rfl

theorem join_symm (C : WO A S → WO S A' → ℂ) (u : WO A S) (y : WO (negSp A') S) :
    join d S C ((d.resS S).symm (u, y)) = C u (dagger A' S y) := by
  rw [join, AddEquiv.apply_symm_apply]

theorem join_inl_inr (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    join d S C (inlH d S u + inrH d S v) = C u v := by
  rw [join_apply, map_add (f := _), map_add (f := _), fst_inl, fst_inr, snd_inl, snd_inr, add_zero, zero_add]

variable {S} {ψ : AddChar (AF D.host.F) ℂ} {C : WO A S → WO S A' → ℂ}

theorem isThetaFunO_join (h : IsBiTheta ψ A S A' C) : IsThetaFunO ψ W S (join d S C) := {
  quasi γ w := by
    have e₁ : fstH d S (ratW S W γ) = ratW S A (γ * d.iA) := (rat_mul γ d.iA).symm
    have e₂ : sndH d S (ratW S W γ) = ratW A' S (A'.gram⁻¹ * ((γ * d.iB)ᴴ * S.gram)) := by
      rw [ratW_eq A' S, ← dagger_rat A' S, rat_mul]; rfl
    rw [join_apply, join_apply, map_add (f := _), map_add (f := _), symplOH_split d, e₁, e₂, h.quasiL, h.quasiR, neg_add,
      AddChar.map_add_eq_mul, mul_assoc]
  level := by
    obtain ⟨U₁, hU₁, k₁⟩ := h.levL
    obtain ⟨U₂, hU₂, k₂⟩ := h.levR
    refine ⟨U₁.comap (fstH d S) ⊓ U₂.comap (sndH d S),
      (hU₁.preimage (continuous_fstH d S)).inter (hU₂.preimage (continuous_sndH d S)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_mul_eq_zero_left _ h0 _) (sndH d S w + sndH d S u)) (fstH d S w)
    have e₂ := congrFun (k₂ _ hu.2 (inf_dagger A' S (map_mul_eq_zero_left _ h0 _)) (fstH d S w)) (sndH d S w)
    simp only [heisO] at e₁ e₂ ⊢
    rw [join_apply, join_apply, ← e₂, ← e₁, symplOH_split d, AddChar.map_add_eq_mul, map_add (f := _), map_add (f := _)]
    ring
  cont := h.cont.comp ((continuous_fstH d S).prodMk (continuous_sndH d S))
  smooth k L hL h0 w := by
    simp only [join_apply, map_add (f := _)]
    exact h.smooth k ((fstH d S).comp L) ((sndH d S).comp L) ((continuous_fstH d S).comp hL)
      ((continuous_sndH d S).comp hL) (fun t => map_mul_eq_zero_left _ (h0 t) _)
      (fun t => fin_dagger A' S (map_mul_eq_zero_left _ (h0 t) _)) _ _ }

theorem cont_of_join (h : IsThetaFunO ψ W S (join d S C)) : Continuous fun p : WO A S × WO S A' => C p.1 p.2 := by
    have := h.cont.comp (((continuous_inlH d S).comp continuous_fst).add ((continuous_inrH d S).comp continuous_snd))
    exact this.congr fun p => join_inl_inr d S C p.1 p.2

theorem smooth_of_join (h : IsThetaFunO ψ W S (join d S C)) : IsBiSmooth C := fun n L L' hL hL' h0 h0' u v => by
    have := h.smooth n ((inlH d S).comp L + (inrH d S).comp L')
      (((continuous_inlH d S).comp hL).add ((continuous_inrH d S).comp hL')) (fun t => by
        change (inlH d S (L t) + inrH d S (L' t)).map _ = 0
        rw [Matrix.map_add (finPart D) (fun _ _ => map_add (finPart D) _ _), map_inlH d S _ (h0 t), fin_inrH d S (h0' t), add_zero])
      (inlH d S u + inrH d S v)
    convert this using 2 with t
    rw [← join_inl_inr d S C, map_add (f := inlH d S), map_add (f := inrH d S), add_add_add_comm]; rfl

theorem quasiL_of_join (h : IsThetaFunO ψ W S (join d S C)) (γ) (u : WO A S) (v : WO S A') :
    C (ratW S A γ + u) v = ψ (-(symplOH A S (ratW S A γ) u)) * C u v := by
    have e : inlH d S (ratW S A γ) = ratW S W (γ * d.qA) := by
      rw [inlH_apply, d.resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq S W, rat_mul]; rfl
    have := h.quasi (γ * d.qA) (inlH d S u + inrH d S v)
    rw [← e, ← add_assoc, ← map_add (f := inlH d S), join_inl_inr, join_inl_inr, symplOH_split d, map_add (f := fstH d S), fst_inl, fst_inl, fst_inr,
      snd_inl, symplOH_zero_left, add_zero, add_zero] at this
    exact this

theorem quasiR_of_join (h : IsThetaFunO ψ W S (join d S C)) (γ) (u : WO A S) (v : WO S A') :
    C u (ratW A' S γ + v) = ψ (-(symplOH S A' (ratW A' S γ) v)) * C u v := by
    have e : inrH d S (ratW A' S γ) = ratW S W (S.gram⁻¹ * (γᴴ * A'.gram) * d.qB) := by
      rw [inrH_apply, d.resS_symm_apply, Matrix.zero_mul, zero_add, ratW_eq S W, rat_mul, ← dagger_rat S A']; rfl
    have := h.quasi (S.gram⁻¹ * (γᴴ * A'.gram) * d.qB) (inlH d S u + inrH d S v)
    rw [← e, add_left_comm, ← map_add (f := inrH d S), join_inl_inr, join_inl_inr, symplOH_split d, map_add (f := sndH d S), fst_inr, snd_inr,
      snd_inl, snd_inr, symplOH_zero_left, zero_add, zero_add] at this
    exact this

theorem levL_of_join (h : IsThetaFunO ψ W S (join d S C)) : ∃ U : AddSubgroup (WO A S), IsOpen (U : Set (WO A S)) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ v, heisO ψ A S a (fun u => C u v) = fun u => C u v := by
    obtain ⟨U, hU, k⟩ := h.level
    refine ⟨U.comap (inlH d S), hU.preimage (continuous_inlH d S), fun a ha h0 v => funext fun u => ?_⟩
    have := congrFun (k _ ha (map_inlH d S _ h0)) (inlH d S u + inrH d S v)
    simp only [heisO] at this ⊢
    rw [add_right_comm, ← map_add (f := inlH d S), join_inl_inr, join_inl_inr, symplOH_split d, map_add (f := fstH d S), fst_inl, fst_inl, fst_inr,
      snd_inl d S a, symplOH_zero_right, add_zero, add_zero] at this
    exact this

theorem levR_of_join (h : IsThetaFunO ψ W S (join d S C)) : ∃ U : AddSubgroup (WO S A'), IsOpen (U : Set (WO S A')) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ u, heisO ψ S A' a (C u) = C u := by
    obtain ⟨U, hU, k⟩ := h.level
    refine ⟨U.comap (inrH d S), hU.preimage (continuous_inrH d S), fun a ha h0 u => funext fun v => ?_⟩
    have := congrFun (k _ ha (inf_inrH d S h0))
      (inlH d S u + inrH d S v)
    simp only [heisO] at this ⊢
    rw [add_assoc, ← map_add (f := inrH d S), join_inl_inr, join_inl_inr, symplOH_split d, map_add (f := sndH d S), fst_inr d S a, snd_inl,
      snd_inr, snd_inr, symplOH_zero_right, zero_add, zero_add] at this
    exact this

theorem isBiTheta_of_join (h : IsThetaFunO ψ W S (join d S C)) : IsBiTheta ψ A S A' C :=
  ⟨cont_of_join d h, smooth_of_join d h, quasiL_of_join d h, quasiR_of_join d h, levL_of_join d h, levR_of_join d h⟩

theorem isBiTheta_iff_join : IsBiTheta ψ A S A' C ↔ IsThetaFunO ψ W S (join d S C) :=
  ⟨isThetaFunO_join d, isBiTheta_of_join d⟩

end GlobalTheory.BiTransfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTrans
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTrans
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Unf.MajLoc

theorem exists_compact_sub {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] (K Q : Set G)
    (hK : IsCompact K) (hQ : IsCompact Q) : ∃ K' : Set G, IsCompact K' ∧ ∀ k ∈ K, ∀ x ∈ Q, k - x ∈ K' :=
  ⟨_, (hK.prod hQ).image continuous_sub, fun k hk x hx => ⟨(k, x), ⟨hk, hx⟩, rfl⟩⟩

theorem summable_of_tsum_ne_top {α β : Type*} (f : β → ℝ) (hf : ∀ y, 0 ≤ f y) (h : (∑' y, ENNReal.ofReal (f y)) ≠ ⊤)
    (e : α → β) (he : Function.Injective e) : Summable fun a => f (e a) :=
  ((ENNReal.summable_toReal h).congr fun y => ENNReal.toReal_ofReal (hf y)).comp_injective he

theorem inv_pow_le {a c R : ℝ} (N : ℕ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hR : 0 ≤ R) (h : c ≤ a + R) :
    ((1 + a) ^ N)⁻¹ ≤ (1 + R) ^ N * ((1 + c) ^ N)⁻¹ := by
  have hle : 1 + c ≤ (1 + R) * (1 + a) := by nlinarith [mul_nonneg ha hR]
  have hA : 0 < (1 + a) ^ N := by positivity
  have hB : 0 < (1 + c) ^ N := by positivity
  rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB, one_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hle N

theorem realSize_neg {D : D7} (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : realSize θ (-x) = realSize θ x := by
  unfold realSize
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : compAt θ τ (-x) i j = -compAt θ τ x i j := by
    show θ τ (infPart D (-x i j)) = -θ τ (infPart D (x i j))
    rw [RingHom.map_neg (infPart D), RingHom.map_neg (θ τ)]
  rw [this, norm_neg]

theorem maj_add_le {D : D7} (θ : InfFam D) {m n : ℕ} (K K' : Set (Mx D m n)) (N : ℕ) (x y : Mx D m n) (R : ℝ)
    (hR : 0 ≤ R) (hx : realSize θ x ≤ R) (hK : ∀ k ∈ K, k - x ∈ K') :
    maj θ K N (x + y) ≤ (1 + R) ^ N * maj θ K' N y := by
  by_cases hb : InBox K (x + y)
  · have hb' : InBox K' y := by
      obtain ⟨k, hk, hkx⟩ := hb
      refine ⟨k - x, hK k hk, ?_⟩
      have : y - (k - x) = x + y - k := by abel
      rw [this]; exact hkx
    unfold maj
    rw [if_pos hb, if_pos hb']
    have hadd := GlobalTheory.MajSum.realSize_add_le θ (x + y) (-x)
    have e2 : x + y + -x = y := by abel
    rw [e2, realSize_neg] at hadd
    exact inv_pow_le N (realSize_nonneg θ _) (realSize_nonneg θ _) hR (by linarith)
  · have e0 : maj θ K N (x + y) = 0 := by
      unfold maj
      rw [if_neg hb]
    rw [e0]
    exact mul_nonneg (by positivity) (maj_nonneg θ _ N _)

theorem summable_bound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K Q : Set (Mx D m n),
    IsCompact K → IsCompact Q → ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧
      ∀ x ∈ Q, ∀ ξ, GlobalTheory.Unf.maj θ K N (x + rat ξ) ≤ b ξ := by
  intro D θ hθ m n
  obtain ⟨N, hN⟩ := GlobalTheory.MajSum.tsum_maj_ne_top D θ hθ m n
  refine ⟨N, fun K Q hK hQ => ?_⟩
  have hcont : Continuous (realSize θ : Mx D m n → ℝ) := GlobalTheory.Unf.MajMeas.continuous_realSize hθ
  obtain ⟨K', hK', hKK⟩ := @exists_compact_sub (Mx D m n) _ _ (lattice_Mx D m n).1 K Q hK hQ
  obtain ⟨R, hR⟩ := (hQ.image hcont).bddAbove
  have hs : Summable fun ξ : Matrix (Fin m) (Fin n) D.host.E => maj θ K' N (rat ξ) :=
    summable_of_tsum_ne_top (fun y : ratMx D m n => maj θ K' N y) (fun y => maj_nonneg θ K' N y) (hN K' hK')
      (fun ξ => ⟨rat ξ, rat_mem ξ⟩) fun a b h => rat_injective (congrArg Subtype.val h)
  exact ⟨fun ξ => (1 + max R 0) ^ N * maj θ K' N (rat ξ), hs.mul_left _, fun x hx ξ =>
    maj_add_le θ K K' N x (rat ξ) (max R 0) (le_max_right _ _) ((hR ⟨x, hx, rfl⟩).trans (le_max_left _ _))
      fun k hk => hKK k hk x hx⟩

end GlobalTheory.Unf.MajLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTransStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ m n : ℕ, ∃ N : ℕ, ∀ K Q : Set (Mx D m n), IsCompact K → IsCompact Q → ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ, GlobalTheory.Unf.maj θ K N (x + rat ξ) ≤ b ξ := by
  first | exact @GlobalTheory.Unf.MajLoc.summable_bound | exact GlobalTheory.Unf.MajLoc.summable_bound | (intros; apply GlobalTheory.Unf.MajLoc.summable_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.CentralUnit

variable {D : D7}

theorem exists_unit {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃ a : AE D, finPart D a = 1 ∧ (∀ ρ, θ ρ (infPart D a) = if ρ = τ then ζ else 1) ∧ cA D a * a = 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  let v : D.what₂.Tau → ℂ := fun ρ => if ρ = τ then ζ - 1 else 0
  let a : AE D := 1 + σ v
  have a1 : finPart D a = 1 := by
    simp only [a]; rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero]
  have a2 : ∀ ρ, θ ρ (infPart D a) = if ρ = τ then ζ else 1 := by
    intro ρ
    simp only [a]; rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one]
    simp only [v]
    split_ifs <;> ring
  refine ⟨a, a1, a2, sub_eq_zero.1 (hσ.ext _ ?_ fun ρ => ?_)⟩
  · have e : finPart D (cA D a) = sigR (Af D.host.F) D.sp.cm.sig (finPart D a) :=
      GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig a
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_one, e, a1, RingHom.map_one, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, RingHom.map_one, RingHom.map_one,
      GlobalTheory.FockCompare.comp_cA hθ, a2]
    split_ifs
    · rw [Complex.conj_mul', hζ, Complex.ofReal_one, one_pow, sub_self]
    · rw [RingHom.map_one, one_mul, sub_self]

theorem scalar_mem (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    Formalism.UG.cT (cA D) (Matrix.diagonal fun _ : Fin S.rank => a) * JR (AF D.host.F) S.gram *
      (Matrix.diagonal fun _ : Fin S.rank => a) = JR (AF D.host.F) S.gram := by
  rw [Formalism.UG.cT, Matrix.diagonal_map (RingHom.map_zero _), Matrix.diagonal_transpose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  linear_combination (JR (AF D.host.F) S.gram i j) * ha

noncomputable def scalarElt (S : HSp D) {a : AE D} (ha : cA D a * a = 1) : GA D S :=
  ⟨⟨Matrix.diagonal fun _ => a, Matrix.diagonal fun _ => cA D a,
    by rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal, ha, Matrix.diagonal_one]⟩, scalar_mem S ha⟩

theorem mt_scalarElt (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    Formalism.L2.Theta.mt S (scalarElt S ha) = Matrix.diagonal fun _ => a := rfl

theorem scalarElt_mem_GinfC (S : HSp D) {a : AE D} (ha : cA D a * a = 1) (h1 : finPart D a = 1) :
    scalarElt S ha ∈ GinfC S := by
  rw [GinfC, MonoidHom.mem_ker]
  refine Units.ext ?_
  ext i j
  change ((Matrix.diagonal fun _ : Fin S.rank => a).map (finPart D)) i j =
    (1 : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j
  rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs
  · exact h1
  · exact RingHom.map_zero _

theorem scalarElt_mem_center (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    scalarElt S ha ∈ Subgroup.center (GA D S) := by
  refine Subgroup.mem_center_iff.2 fun k => Subtype.ext (Units.ext ?_)
  ext i j
  change (k.1.val * Matrix.diagonal fun _ : Fin S.rank => a) i j = ((Matrix.diagonal fun _ : Fin S.rank => a) * k.1.val) i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem compAt_scalarElt (θ : InfFam D) (τ : D.what₂.Tau) (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    compAt θ τ (Formalism.L2.Theta.mt S (scalarElt S ha)) = θ τ (infPart D a) • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  rw [mt_scalarElt]
  ext i j
  rw [compAt, Matrix.map_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem exists_central_of_norm_one : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (τ : D.what₂.Tau) (ζ : ℂ), ‖ζ‖ = 1 → ∃ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∧ ∀ ρ : D.what₂.Tau, ρ ≠ τ → compAt θ ρ (Formalism.L2.Theta.mt S z) = 1 := by
  intro D θ hθ S τ ζ hζ
  obtain ⟨a, a1, a2, ac⟩ := exists_unit hθ τ hζ
  refine ⟨scalarElt S ac, scalarElt_mem_GinfC S ac a1, scalarElt_mem_center S ac, ?_, fun ρ hρ => ?_⟩
  · rw [compAt_scalarElt, a2, if_pos rfl]
  · rw [compAt_scalarElt, a2, if_neg hρ, one_smul]

end GlobalTheory.CentralUnit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_realPoint_unit_scalar_single_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (τ : D.what₂.Tau) (ζ : ℂ), ‖ζ‖ = 1 → ∃ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∧ ∀ ρ : D.what₂.Tau, ρ ≠ τ → compAt θ ρ (Formalism.L2.Theta.mt S z) = 1 := by
  first | exact @GlobalTheory.CentralUnit.exists_central_of_norm_one | exact GlobalTheory.CentralUnit.exists_central_of_norm_one | (intros; apply GlobalTheory.CentralUnit.exists_central_of_norm_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamUnitaryHolds
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RamUnit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def pet (vS : Vol S) (ψ ψ' : Form k n (GA D S → ℂ)) (P : Pair k n) : ℂ :=
  ∫ g in vS.𝓕, ψ P g * star (ψ' P g) ∂vS.μ

theorem rep_apply (β : Frame p S n) (g : GL n k) (f : GA D S → ℂ) (x : GA D S) :
    β.rep g f x = f (x * β.gl g) := rfl

theorem pet_const (vS : Vol S) (β : Frame p S n) {ψ ψ' : Form k n (GA D S → ℂ)} (hψ : ψ ∈ EqForm β.rep)
    (hψ' : ψ' ∈ EqForm β.rep) (hl : ∀ P, ∀ γ ∈ GQ S, ∀ g, ψ P (γ * g) = ψ P g)
    (hl' : ∀ P, ∀ γ ∈ GQ S, ∀ g, ψ' P (γ * g) = ψ' P g) (P Q : Pair k n) : pet vS ψ ψ' P = pet vS ψ ψ' Q := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
  unfold pet
  rw [hψ g P, hψ' g P]
  simp only [rep_apply]
  exact (GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S vS.μ vS.𝓕 vS.haar vS.fund (fun x => ψ P x * star (ψ' P x))
    (fun γ hγ x => by simp only [hl P γ hγ, hl' P γ hγ]) (β.gl g)).symm

theorem sum_pet_FFStar (vS : Vol S) (hS : CoCpt S) (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    (hχ : ∀ a, (starRingEnd ℂ) (χ a) = χ (-a))
    {φ ψ : Form k n (GA D S → ℂ)} (hφ : ∀ P, IsContAut S (φ P)) (hψ : ∀ P, IsContAut S (ψ P))
    (L : Submodule 𝒪[k] (n → k)) :
    ∑ P ∈ withLat L, pet vS (FFStar q χ φ) ψ P = ∑ P₁ ∈ withKer L, pet vS φ (FF q χ ψ) P₁ := by
  have hint : ∀ P₁ P, IntegrableOn (fun g => φ P₁ g * star (ψ P g)) vS.𝓕 vS.μ := fun P₁ P =>
    (GlobalTheory.CocompactParam.continuous_integral_param D S hS vS Unit (fun g _ => φ P₁ g * star (ψ P g))
      (((hφ P₁).2.mul (hψ P).2.star).comp continuous_fst)
      (fun γ hγ g _ => by simp only [(hφ P₁).1 γ hγ, (hψ P).1 γ hγ])).1 ()
  have e1 : ∀ P ∈ withLat L, pet vS (FFStar q χ φ) ψ P =
      ∑ P₁ ∈ withKer L, χ (-cross q P₁ P) * ∫ g in vS.𝓕, φ P₁ g * star (ψ P g) ∂vS.μ := by
    intro P hP
    rw [mem_withLat] at hP
    unfold pet
    rw [FFStar_apply, hP]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ (fun P₁ _ => (hint P₁ P).const_mul _)]
    exact Finset.sum_congr rfl fun P₁ _ => integral_const_mul _ _
  have e2 : ∀ P₁ ∈ withKer L, pet vS φ (FF q χ ψ) P₁ =
      ∑ P ∈ withLat L, χ (-cross q P₁ P) * ∫ g in vS.𝓕, φ P₁ g * star (ψ P g) ∂vS.μ := by
    intro P₁ hP₁
    rw [mem_withKer] at hP₁
    unfold pet
    rw [FF_apply, hP₁]
    have : ∀ g, φ P₁ g * star ((∑ P ∈ withLat L, χ (cross q P₁ P) • ψ P) g) =
        ∑ P ∈ withLat L, χ (-cross q P₁ P) * (φ P₁ g * star (ψ P g)) := fun g => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, Finset.mul_sum, star_mul']
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [← hχ]
      change φ P₁ g * ((starRingEnd ℂ) (χ (cross q P₁ P)) * star (ψ P g)) = _
      ring
    simp only [this]
    rw [integral_finsetSum _ (fun P _ => (hint P₁ P).const_mul _)]
    exact Finset.sum_congr rfl fun P _ => integral_const_mul _ _
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]

end GlobalTheory.FinPl.RamUnit

namespace GlobalTheory.FinPl.RamUnit

theorem ramUnitary_holds : ∀ D : D7, GlobalTheory.FinPl.RamUnitary D := by
  intro D k _ _ _ _ p n _ _ q χ hχ ε S hS vS β P φ₀ φ₀' hφ₀ hφ₀'
  obtain ⟨φ, hφ, rfl⟩ := hφ₀
  obtain ⟨φ', hφ', rfl⟩ := hφ₀'
  have hB := GlobalTheory.FinPl.ramBijective_holds D k p n q χ hχ (resChar χ hχ q) rfl ε S β P
  obtain ⟨hA, eA⟩ := hB.2.1 φ hφ
  obtain ⟨hA', eA'⟩ := hB.2.1 φ' hφ'
  rw [eA, eA']
  have hO : OperatorIdentities k n (GA D S → ℂ) q (resChar χ hχ q) :=
    ((GlobalTheory.PairOp.pairOperatorStatement k q χ hχ n).1 (GA D S → ℂ)).2
  set X := FFStar q (resChar χ hχ q) φ with hX
  set X' := FFStar q (resChar χ hχ q) φ' with hX'
  have cX : ∀ Q, IsContAut S (X Q) := fun Q => by
    have := hA.2.2 (ε⁻¹ • Q)
    rwa [dia_apply, smul_inv_smul] at this
  have cX' : ∀ Q, IsContAut S (X' Q) := fun Q => by
    have := hA'.2.2 (ε⁻¹ • Q)
    rwa [dia_apply, smul_inv_smul] at this
  have eFF : FF q (resChar χ hχ q) X' = ((resCard k : ℂ) ^ Fintype.card n) • φ' := hO.FF_FFStar_ram φ' hφ'.2.1
  have c2 : ∀ Q, IsContAut S ((FF q (resChar χ hχ q) X') Q) := fun Q => by
    rw [eFF]
    exact ⟨fun γ hγ g => by simp only [Pi.smul_apply, smul_eq_mul, (hφ'.2.2 Q).1 γ hγ],
      continuous_const.mul (hφ'.2.2 Q).2⟩
  have hsum := sum_pet_FFStar vS hS q (resChar χ hχ q) (conj_resChar hχ q) hφ.2.2 cX' P.lat
  have k1 : ∀ Q ∈ withLat P.lat, pet vS X X' Q = pet vS X X' (ε • P) := fun Q _ =>
    pet_const vS β (FFStar_mem_EqForm q _ hφ.1) (FFStar_mem_EqForm q _ hφ'.1) (fun Q => (cX Q).1)
      (fun Q => (cX' Q).1) Q (ε • P)
  have k2 : ∀ Q ∈ withKer P.lat, pet vS φ (FF q (resChar χ hχ q) X') Q = pet vS φ (FF q (resChar χ hχ q) X') P :=
    fun Q _ => pet_const vS β hφ.1 (FF_mem_EqForm q _ (FFStar_mem_EqForm q _ hφ'.1)) (fun Q => (hφ.2.2 Q).1)
      (fun Q => (c2 Q).1) Q P
  have hcard : (withLat P.lat).card = (withKer P.lat).card := by
    classical
    have e : Red P.lat ≃ₗ[𝓀[k]] Module.Dual 𝓀[k] (Red P.lat) :=
      (Module.Free.chooseBasis 𝓀[k] (Red P.lat)).toDualEquiv
    have e' : {x : Red P.lat // x ≠ 0} ≃ {f : Module.Dual 𝓀[k] (Red P.lat) // f ≠ 0} :=
      e.toEquiv.subtypeEquiv (fun x => by simp)
    refine Finset.card_eq_of_equiv ?_
    exact (Equiv.subtypeEquivRight (fun P => mem_withLat)).trans
      ((latEquiv P.lat).symm.trans (e'.symm.trans ((kerEquiv P.lat q).trans
        (Equiv.subtypeEquivRight (fun P => mem_withKer.symm)))))
  rw [Finset.sum_congr rfl k1, Finset.sum_congr rfl k2, Finset.sum_const, Finset.sum_const,
    ← hcard] at hsum
  have hN : (withLat P.lat).card ≠ 0 := (Finset.card_pos.2 ⟨P, mem_withLat.2 rfl⟩).ne'
  have hpe : pet vS X X' (ε • P) = pet vS φ (FF q (resChar χ hχ q) X') P := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hsum
    exact smul_right_injective ℂ (Nat.cast_ne_zero.2 hN) hsum
  change pet vS X X' (ε • P) = _
  rw [hpe, eFF]
  unfold pet
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_pow, Complex.star_def, Complex.conj_natCast]
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

end GlobalTheory.FinPl.RamUnit
end
end
