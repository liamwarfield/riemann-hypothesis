module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import GroundTheory.AutomorphicForms.GeometricLemma
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermBlockMatrix
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermBlockMatrix
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SizeCells

theorem exists_perm_cell_sizes : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (b : SizeMatrix m m'), ∃ w : Equiv.Perm (Fin N), ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = b.1 i j := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' b
  obtain ⟨f⟩ := b.nonempty_rows
  obtain ⟨g⟩ := b.nonempty_cols
  let A : (Σ i, Σ j, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight f).trans e
  let B : (Σ j, Σ i, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight g).trans e'
  let S : (Σ i, Σ j, Fin (b.1 i j)) ≃ (Σ j, Σ i, Fin (b.1 i j)) :=
    { toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      invFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let w : Equiv.Perm (Fin N) := (B.symm.trans S.symm).trans A
  have hA : ∀ p, blk e (A p) = p.1 := by
    intro p
    simp [A, blk]
  have hB : ∀ p, blk e' (B p) = p.1 := by
    intro p
    simp [B, blk]
  have hw : ∀ p, w.symm (A p) = B (S p) := by
    intro p
    simp [w]
  refine ⟨w, fun i j => ?_⟩
  have himg : (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j) =
      Finset.univ.image (fun t : Fin (b.1 i j) => A ⟨i, j, t⟩) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨⟨i', j', t⟩, rfl⟩ := A.surjective x
      rw [hA] at h1
      rw [hw, hB] at h2
      dsimp only [S, Equiv.coe_fn_mk] at h1 h2
      subst h1
      subst h2
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨hA _, ?_⟩
      rw [hw, hB]
      rfl
  rw [himg, Finset.card_image_of_injective _ (fun s t h => by simpa using A.injective h)]
  simp

end GlobalTheory.CompanionTheory.SizeCells
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermBlockMatrixStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_block_matrix : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (b : SizeMatrix m m'), ∃ w : Equiv.Perm (Fin N), ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = b.1 i j := by
  first | exact @GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes | exact GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes | (intros; apply GlobalTheory.CompanionTheory.SizeCells.exists_perm_cell_sizes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationTransportEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationTransportEquiv
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.FiltTransfer

theorem subQuot_of_filtration : ∀ {G H : Type} [Group G] [Group H] (ψ : H →* G) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ H V) (ρ' : Representation ℂ G V'), ρ.Equiv (ρ'.comp ψ) → ∀ (K : ℕ) (X : Fin K → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (τ : ∀ j, Representation ℂ G (X j)) (Vf : ℕ → Submodule ℂ V'), Vf 0 = ⊥ → Vf K = ⊤ → Monotone Vf → ∀ (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ' g)), (∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap (ρ'.subrepresentation (Vf (j + 1)) (hV (j + 1))) (τ j), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : V') ∈ Vf j) → ∃ S : Fin (K + 1) → Subrepresentation ρ, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last K) = ⊤ ∧ ∀ t : Fin K, Nonempty ((GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)).Equiv ((τ t).comp ψ)) := by
  intro G H _ _ ψ V V' _ _ _ _ ρ ρ' e K X _ _ τ Vf h0 hK hm hV hΨ
  have he : ∀ (h : H) (v : V), e (ρ h v) = ρ' (ψ h) (e v) := fun h v =>
    e.toIntertwiningMap.isIntertwining _ _ h v
  let S : ℕ → Subrepresentation ρ := fun i =>
    ⟨(Vf i).comap e.toLinearMap, fun h v hv => by
      have hv' : e v ∈ Vf i := hv
      show e (ρ h v) ∈ Vf i
      rw [he]
      exact hV i (ψ h) hv'⟩
  have memS : ∀ (i : ℕ) (v : V), v ∈ (S i).toSubmodule ↔ e v ∈ Vf i := fun _ _ => Iff.rfl
  refine ⟨fun t => S t, ?_, ?_, ?_, ?_⟩
  · intro a b hab v hv
    exact hm (Fin.le_def.1 hab) hv
  · apply Subrepresentation.toSubmodule_injective
    ext v
    show e v ∈ Vf 0 ↔ v = 0
    rw [h0]
    simp
  · apply Subrepresentation.toSubmodule_injective
    ext v
    show e v ∈ Vf K ↔ True
    rw [hK]
    simp
  · intro t
    obtain ⟨Ψ, hs, hk⟩ := hΨ t
    let f : (S (t + 1)).toSubmodule →ₗ[ℂ] X t :=
      Ψ.toLinearMap ∘ₗ
        (e.toLinearMap.restrict (p := (S (t + 1)).toSubmodule) (q := Vf (t + 1)) fun _ hv => hv)
    have hf : ∀ x, f x = Ψ ⟨e x, x.2⟩ := fun _ => rfl
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨w, rfl⟩ := hs y
      refine ⟨⟨e.symm w, ?_⟩, ?_⟩
      · show e (e.symm w) ∈ Vf (t + 1)
        simp
      · rw [hf]
        congr 1
        apply Subtype.ext
        simp
    have hker : (S t).toSubmodule.comap (S (t + 1)).toSubmodule.subtype = LinearMap.ker f := by
      ext x
      rw [LinearMap.mem_ker, hf, hk]
      rfl
    let E := (Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hsurj)
    refine ⟨Representation.Equiv.mk E ?_⟩
    intro g
    have hE : ∀ x, E (Submodule.Quotient.mk x) = f x := fun x => rfl
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hstep : f ⟨ρ g x, (S (t + 1)).apply_mem_toSubmodule g x.2⟩ =
        τ t (ψ g) (f x) := by
      rw [hf, hf, ← Ψ.isIntertwining _ _ (ψ g)]
      congr 1
      exact Subtype.ext (he g x)
    exact hstep

end GlobalTheory.CompanionTheory.FiltTransfer
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationTransportEquivStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_transport_equiv : ∀ {G H : Type} [Group G] [Group H] (ψ : H →* G) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ H V) (ρ' : Representation ℂ G V'), ρ.Equiv (ρ'.comp ψ) → ∀ (K : ℕ) (X : Fin K → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (τ : ∀ j, Representation ℂ G (X j)) (Vf : ℕ → Submodule ℂ V'), Vf 0 = ⊥ → Vf K = ⊤ → Monotone Vf → ∀ (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ' g)), (∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap (ρ'.subrepresentation (Vf (j + 1)) (hV (j + 1))) (τ j), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : V') ∈ Vf j) → ∃ S : Fin (K + 1) → Subrepresentation ρ, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last K) = ⊤ ∧ ∀ t : Fin K, Nonempty ((GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)).Equiv ((τ t).comp ψ)) := by
  first | exact @GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration | exact GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration | (intros; apply GlobalTheory.CompanionTheory.FiltTransfer.subQuot_of_filtration <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BernsteinZelevinskyGeometricLemma
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BernsteinZelevinskyGeometricLemma
set_option maxSynthPendingDepth 1

open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

noncomputable section

namespace GlobalTheory.CompanionTheory.GeomLemmaUniform

section Filtration

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic Matrix GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.GLnLocal ValuativeRel Topology Set DoubleCoset Filter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ}

theorem filtration_of_cellEnumeration {k : ℕ} (w : Fin k → Equiv.Perm (Fin n))
    (hcov : ∀ g : Matrix.GeneralLinearGroup (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (Matrix.GeneralLinearGroup (Fin n) F)) (blockUpper F n γ))
    (hanti : Antitone fun j => cellHeight β γ (permGL F (w j)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
    (hσ : IsSmooth σ) :
    ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)),
      V 0 = ⊥ ∧ V k = ⊤ ∧ Monotone V ∧
      ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m),
        ∀ j : Fin k, ∃ Ψ : Representation.IntertwiningMap
            ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1)))
            (twist ((invSqrtModular F n γ).comp leviIncl)
              (indRep (cellLeviSub F β γ (w j)) (cellInducing β γ (w j) σ))),
          Function.Surjective Ψ ∧
            ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  set C : Fin k → Set (Matrix.GeneralLinearGroup (Fin n) F) := fun l =>
    doubleCoset (permGL F (w l)) (blockUpper F n β : Set (Matrix.GeneralLinearGroup (Fin n) F))
      (blockUpper F n γ)
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro g hgi hgj
    obtain ⟨l, -, hl⟩ := hcov g
    exact hij ((hl i hgi).trans (hl j hgj).symm)
  have hcov' : ∀ g, ∃ l, g ∈ C l := fun g => (hcov g).exists
  have hcl := closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨fun i => jacquetFiltration γ (σ := σ) (cellUnion C i), ?_, ?_, ?_, ?_⟩
  · show jacquetFiltration γ (cellUnion C 0) = ⊥
    rw [cellUnion_zero, jacquetFiltration_empty]
  · show jacquetFiltration γ (cellUnion C k) = ⊤
    rw [cellUnion_of_cover hcov', jacquetFiltration_univ]
  · exact fun i i' h => jacquetFiltration_mono γ (cellUnion_mono h)
  refine ⟨fun i m => jacquetFiltration_le_comap γ (cellUnion_mul_mem w i).1 m, fun j => ?_⟩
  have hYo : IsOpen (cellUnion C ((j : ℕ) + 1)) := isOpen_cellUnion hdisj hcov' hcl _
  have hCY : closure (C j) ∩ cellUnion C ((j : ℕ) + 1) = C j :=
    closure_inter_cellUnion_succ hdisj hcl j
  have hYQ := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).1
  have hYP := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).2
  have hdiff : cellUnion C ((j : ℕ) + 1) \ C j = cellUnion C j := by
    rw [cellUnion_succ j, union_sdiff_right, (disjoint_cellUnion hdisj j).symm.sdiff_eq_left]
  refine ⟨⟨gradedJacquetMap γ (w j) σ hYo hCY hYQ, fun m => ?_⟩, ?_, fun x => ?_⟩
  · refine LinearMap.ext fun x => ?_
    exact gradedJacquetMap_jacquetRep σ hYo hCY hYQ m x
  · exact gradedJacquetMap_surjective σ hYo hCY hYQ (cellJacquetMap_surjective hYo hCY hYP hYQ hσ)
  · have := gradedJacquetMap_eq_zero_iff σ hYo hCY hYQ
      (fun f hf h0 => exists_sub_mem_ker_of_cellJacquet_eq_zero σ hσ hYo hCY hYQ hf h0) x
    rw [hdiff] at this
    exact this

theorem normalized_piece {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (levi F n β) W) (w : Equiv.Perm (Fin n))
    {A : Type} [AddCommGroup A] [Module ℂ A] {ρ : Representation ℂ (levi F n γ) A}
    (Ψ₀ : Representation.IntertwiningMap ρ
      (twist ((invSqrtModular F n γ).comp leviIncl)
        (indRep (cellLeviSub F β γ w) (cellInducing β γ w σ))))
    (hsurj : Function.Surjective Ψ₀) :
    ∃ Ψ : Representation.IntertwiningMap ρ (indRep (cellLeviSub F β γ w) (normInducing σ γ w)),
      Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ Ψ₀ x = 0 := by
  refine ⟨(indCongrHom σ w).comp ((indTwistHom σ w).comp Ψ₀), ?_, fun x => ?_⟩
  · exact (indCongrHom_surjective σ w).comp ((indTwistHom_surjective σ w).comp hsurj)
  · constructor
    · intro h
      apply indTwistHom_injective σ w
      apply indCongrHom_injective σ w
      rw [map_zero, map_zero]
      exact h
    · intro h
      show (indCongrHom σ w) ((indTwistHom σ w) (Ψ₀ x)) = 0
      rw [h, map_zero, map_zero]

end Filtration

theorem geometricLemma_uniform : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (β γ : Fin n → ℕ), ∃ (K : ℕ) (w : Fin K → Equiv.Perm (Fin n)), (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W), GroundTheory.Automorphic.IsSmooth σ → ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)), V 0 = ⊥ ∧ V K = ⊤ ∧ Monotone V ∧ ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m), ∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1))) (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  intro F _ _ _ _ n β γ
  obtain ⟨k, w, hcov, hanti⟩ := GroundTheory.Automorphic.Parabolic.exists_cellEnumeration (F := F) β γ
  refine ⟨k, w, hcov, fun W _ _ σ hσ => ?_⟩
  obtain ⟨V, h0, hk, hmono, hV, hΨ⟩ := filtration_of_cellEnumeration (γ := γ) w hcov hanti σ hσ
  refine ⟨V, h0, hk, hmono, hV, fun j => ?_⟩
  obtain ⟨Ψ₀, hsurj, hker⟩ := hΨ j
  obtain ⟨Ψ, hΨs, hΨk⟩ := normalized_piece σ (w j) Ψ₀ hsurj
  exact ⟨Ψ, hΨs, fun x => (hΨk x).trans (hker x)⟩

end GlobalTheory.CompanionTheory.GeomLemmaUniform
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BernsteinZelevinskyGeometricLemmaStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bernstein_zelevinsky_geometric_lemma : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (β γ : Fin n → ℕ), ∃ (K : ℕ) (w : Fin K → Equiv.Perm (Fin n)), (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W), GroundTheory.Automorphic.IsSmooth σ → ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)), V 0 = ⊥ ∧ V K = ⊤ ∧ Monotone V ∧ ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m), ∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1))) (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  first | exact @GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform | exact GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform | (intros; apply GlobalTheory.CompanionTheory.GeomLemmaUniform.geometricLemma_uniform <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspaces
open NumberField Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open GlobalTheory.CuspRep PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.IsotropicDegreeBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjE_conjE (a : E) : conjE E (conjE E a) = a :=
  IsCMField.complexConj_apply_apply E a

theorem mem_perpD_iff (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) (y : Fin n → E) :
    y ∈ perpD (conjE E) d W ↔ ∀ x ∈ W, (conjE E ∘ x) ⬝ᵥ ((d⁻¹).val *ᵥ y) = 0 := by
  have key : y ∈ perpD (conjE E) d W ↔ (d⁻¹).val *ᵥ y ∈ perp (conjE E) W := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : (d⁻¹).val *ᵥ (Matrix.toLin' d.val z) = z := by
        rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      rw [this]
      exact hz
    · intro h
      refine ⟨_, h, ?_⟩
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
  rw [key]
  exact Iff.rfl

theorem gram_nrm (d : GL (Fin n) E) :
    ((nrm d).val.map (conjE E))ᵀ * (d⁻¹).val * (nrm d).val = (d⁻¹).val := by
  set D := d.val with hD
  set Di := (d⁻¹).val with hDi
  have hval : (nrm d).val = D * (Di.map (conjE E))ᵀ := by
    simp only [nrm, Units.val_mul]
    rfl
  have hinv : Di * D = 1 := by
    rw [hDi, hD, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc : (Di.map (conjE E)) * (D.map (conjE E)) = 1 := by
    rw [← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcc : (Di.map (conjE E)).map (conjE E) = Di := by
    ext i j
    simp [conjE_conjE]
  have hm : ((nrm d).val.map (conjE E))ᵀ = Di * (D.map (conjE E))ᵀ := by
    rw [hval, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose, hcc]
  rw [hm, hval]
  calc Di * (D.map (conjE E))ᵀ * Di * (D * (Di.map (conjE E))ᵀ)
      = Di * (D.map (conjE E))ᵀ * (Di * D) * (Di.map (conjE E))ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = Di * ((Di.map (conjE E)) * (D.map (conjE E)))ᵀ := by
        rw [hinv, Matrix.transpose_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = Di := by rw [hc, Matrix.transpose_one, Matrix.mul_one]

theorem pairing_nrm (d : GL (Fin n) E) (u v : Fin n → E) :
    (conjE E ∘ ((nrm d).val *ᵥ u)) ⬝ᵥ ((d⁻¹).val *ᵥ ((nrm d).val *ᵥ v)) =
      (conjE E ∘ u) ⬝ᵥ ((d⁻¹).val *ᵥ v) := by
  have h1 : conjE E ∘ ((nrm d).val *ᵥ u) = ((nrm d).val.map (conjE E)) *ᵥ (conjE E ∘ u) := by
    funext i
    exact RingHom.map_mulVec (conjE E) (nrm d).val u i
  rw [h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    gram_nrm]

theorem img_nrm_inf (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) (hW : img (nrm d) W = W) :
    img (nrm d) (W ⊓ perpD (conjE E) d W) = W ⊓ perpD (conjE E) d W := by
  have hinj : Function.Injective (Matrix.toLin' (nrm d).val) := by
    intro a b hab
    have h := congrArg (fun z => ((nrm d)⁻¹).val *ᵥ z) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h
  have hle : img (nrm d) (W ⊓ perpD (conjE E) d W) ≤ W ⊓ perpD (conjE E) d W := by
    rintro _ ⟨y, ⟨hyW, hyP⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have : Matrix.toLin' (nrm d).val y ∈ img (nrm d) W := ⟨y, hyW, rfl⟩
      rwa [hW] at this
    · rw [SetLike.mem_coe, mem_perpD_iff]
      intro x hx
      rw [← hW] at hx
      obtain ⟨x', hx', rfl⟩ := hx
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, pairing_nrm]
      exact (mem_perpD_iff d W y).1 hyP x' hx'
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

theorem inf_le_perpD_inf (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) :
    W ⊓ perpD (conjE E) d W ≤ perpD (conjE E) d (W ⊓ perpD (conjE E) d W) := by
  intro y hy
  rw [mem_perpD_iff]
  exact fun x hx => (mem_perpD_iff d W y).1 hy.2 x hx.1

theorem prof_gap {τ : ℝ} (hτ : 0 ≤ τ) {a b m : ℕ} (hab : a < b) (hbm : b ≤ m) :
    prof m τ a + 2 * τ ≤ prof m τ b := by
  have h1 : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have h2 : (b : ℝ) ≤ m := by exact_mod_cast hbm
  have h3 : (2 : ℝ) ≤ ((b : ℝ) - a) * (2 * m + 1 - a - b) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ 2 * m - 1 - a - b)]
  have h4 := mul_nonneg hτ (sub_nonneg.2 h3)
  simp only [prof]
  nlinarith

theorem onlyIsotropic_of : OnlyStable → DegPairing → SizeBasic → OnlyIsotropic := by
  intro h1 h2 h3 E _ _ _ n
  obtain ⟨C₁, hC₁⟩ := h1 E n
  obtain ⟨C₂, hC₂⟩ := h2 E n
  refine ⟨max 0 (max C₁ C₂), fun τ x d hτ => ?_⟩
  have hs0 : 0 ≤ logSize (twConj (thetaA E n) x (ratGL E n d)) := (h3 E n).2.1 _
  have hs1 : 0 ≤ 1 + logSize (twConj (thetaA E n) x (ratGL E n d)) := by linarith
  have l₁ : C₁ ≤ max 0 (max C₁ C₂) := (le_max_left _ _).trans (le_max_right _ _)
  have l₂ : C₂ ≤ max 0 (max C₁ C₂) := (le_max_right _ _).trans (le_max_right _ _)
  have hτ₁ := le_trans (mul_le_mul_of_nonneg_right l₁ hs1) hτ
  have hτ₂ := le_trans (mul_le_mul_of_nonneg_right l₂ hs1) hτ
  have hτ₀ : 0 ≤ τ := le_trans (mul_nonneg (le_max_left _ _) hs1) hτ
  refine ⟨fun hx W _ _ => hx.1 W, fun h => (hC₁ τ x d hτ₁).2 fun W hW => ?_⟩
  have hb := h _ (img_nrm_inf d W hW) (inf_le_perpD_inf d W)
  by_cases heq : W ⊓ perpD (conjE E) d W = W
  · exact h W hW (inf_eq_left.1 heq)
  · have hlt : W ⊓ perpD (conjE E) d W < W := lt_of_le_of_ne inf_le_left heq
    have hr := Submodule.finrank_lt_finrank_of_lt hlt
    have hn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
    have hg := prof_gap hτ₀ hr hn
    have hp := (hC₂ x d).1 W hW
    linarith

end GlobalTheory.CompanionTheory.IsotropicDegreeBound
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspacesStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.only_isotropic_subspaces : OnlyStable → DegPairing → SizeBasic → OnlyIsotropic := by
  first | exact @GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of | exact GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of | (intros; apply GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsometryFlagOfEquiv
noncomputable section

open Matrix Module PositivityTheory.Rg.BcB

namespace GlobalTheory.CompanionTheory.IwaDecomp

section Isometry

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

def isoOfFinrank (h : finrank ℂ F = finrank ℂ G) : F ≃ₗᵢ[ℂ] G :=
  (stdOrthonormalBasis ℂ F).equiv (stdOrthonormalBasis ℂ G) (finCongr h)

theorem exists_extend (h : finrank ℂ F = finrank ℂ G) (S : Submodule ℂ F) (φ : S →ₗᵢ[ℂ] G) :
    ∃ ψ : F →ₗᵢ[ℂ] G, ∀ s : S, ψ s = φ s := by
  let e := isoOfFinrank h
  let L : S →ₗᵢ[ℂ] F := e.symm.toLinearIsometry.comp φ
  refine ⟨e.toLinearIsometry.comp L.extend, fun s => ?_⟩
  simp [L, LinearIsometry.extend_apply]

theorem finrank_map_isometry (K : E →ₗᵢ[ℂ] E) (A : Submodule ℂ E) :
    finrank ℂ (A.map K.toLinearMap) = finrank ℂ A :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective K.toLinearMap K.injective A)).symm

theorem exists_isometry_flag {A₁ A₂ B₁ B₂ : Submodule ℂ E} (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (h₁ : finrank ℂ A₁ = finrank ℂ B₁) (h₂ : finrank ℂ A₂ = finrank ℂ B₂) :
    ∃ K : E →ₗᵢ[ℂ] E, A₁.map K.toLinearMap = B₁ ∧ A₂.map K.toLinearMap = B₂ := by
  let φ : A₁ ≃ₗᵢ[ℂ] B₁ := isoOfFinrank h₁
  let S : Submodule ℂ A₂ := A₁.comap A₂.subtype
  let ι : S →ₗᵢ[ℂ] A₁ :=
    ⟨LinearMap.codRestrict A₁ (A₂.subtype ∘ₗ S.subtype) (fun x => x.2), fun x => rfl⟩
  let j : B₁ →ₗᵢ[ℂ] B₂ := ⟨Submodule.inclusion hB, fun x => rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_extend h₂ S (j.comp (φ.toLinearIsometry.comp ι))
  let L : A₂ →ₗᵢ[ℂ] E := B₂.subtypeₗᵢ.comp ψ
  have hK : ∀ a : A₂, L.extend a = ψ a := fun a => by
    simpa [L] using LinearIsometry.extend_apply L a
  refine ⟨L.extend, ?_, ?_⟩
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₁)
    rintro _ ⟨a, ha, rfl⟩
    have h := hK ⟨a, hA ha⟩
    have h2 := hψ ⟨⟨a, hA ha⟩, ha⟩
    change L.extend a ∈ B₁
    rw [show L.extend a = ((ψ ⟨a, hA ha⟩ : B₂) : E) from h, show ψ ⟨a, hA ha⟩ = _ from h2]
    exact (φ (ι ⟨⟨a, hA ha⟩, ha⟩)).2
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ((finrank_map_isometry _ _).trans h₂)
    rintro _ ⟨a, ha, rfl⟩
    change L.extend a ∈ B₂
    rw [show L.extend a = ((ψ ⟨a, ha⟩ : B₂) : E) from hK ⟨a, ha⟩]
    exact (ψ ⟨a, ha⟩).2

theorem exists_isometry_flag_of_equiv {V : Type*} [AddCommGroup V] [Module ℂ V] (e : V ≃ₗ[ℂ] E)
    {A₁ A₂ B₁ B₂ : Submodule ℂ V} (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂)
    (h₁ : finrank ℂ A₁ = finrank ℂ B₁) (h₂ : finrank ℂ A₂ = finrank ℂ B₂) :
    ∃ K : E →ₗᵢ[ℂ] E, (A₁.map (e : V →ₗ[ℂ] E)).map K.toLinearMap = B₁.map (e : V →ₗ[ℂ] E) ∧
      (A₂.map (e : V →ₗ[ℂ] E)).map K.toLinearMap = B₂.map (e : V →ₗ[ℂ] E) := by
  have hT : ∀ W : Submodule ℂ V, finrank ℂ (W.map (e : V →ₗ[ℂ] E)) = finrank ℂ W :=
    fun W => LinearEquiv.finrank_map_eq e W
  exact exists_isometry_flag (Submodule.map_mono hA) (Submodule.map_mono hB)
    (by rw [hT, hT, h₁]) (by rw [hT, hT, h₂])

end Isometry

variable {n : ℕ}

theorem img_one (W : Submodule ℂ (Fin n → ℂ)) : img (1 : GL (Fin n) ℂ) W = W := by
  simp [img]

theorem img_mul (a b : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : img (a * b) W = img a (img b W) := by
  simp only [img, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem img_mono (a : GL (Fin n) ℂ) {W W' : Submodule ℂ (Fin n → ℂ)} (h : W ≤ W') : img a W ≤ img a W' :=
  Submodule.map_mono h

def linEquiv (g : GL (Fin n) ℂ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.toLin'OfInv (M := (g⁻¹ : GL (Fin n) ℂ).val) (M' := g.val) (by simp) (by simp)

theorem img_eq_map_linEquiv (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    img g W = W.map (linEquiv g : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
  rfl

theorem finrank_img (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : finrank ℂ (img g W) = finrank ℂ W := by
  rw [img_eq_map_linEquiv]
  exact LinearEquiv.finrank_map_eq (linEquiv g) W

theorem thetaR_eq_self_iff (k : GL (Fin n) ℂ) :
    thetaR (starRingEnd ℂ) n k = k ↔ k.val.conjTranspose = (k⁻¹ : GL (Fin n) ℂ).val := by
  have h : (thetaR (starRingEnd ℂ) n k).val = (k⁻¹ : GL (Fin n) ℂ).val.conjTranspose := by
    rw [thetaR_val]; ext i j; simp [Matrix.conjTranspose_apply]
  constructor
  · intro e
    have h' := congrArg Units.val e
    rw [h] at h'
    rw [← h', Matrix.conjTranspose_conjTranspose]
  · intro e
    refine Units.ext ?_
    rw [h, ← e, Matrix.conjTranspose_conjTranspose]

abbrev eu (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm

theorem unitary_of_isometry (K : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧
      ∀ W : Submodule ℂ (Fin n → ℂ), (img k W).map (eu n : (Fin n → ℂ) →ₗ[ℂ] _) =
        (W.map (eu n : (Fin n → ℂ) →ₗ[ℂ] _)).map K.toLinearMap := by
  let f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    ((eu n).symm : _ →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ K.toLinearMap ∘ₗ (eu n : (Fin n → ℂ) →ₗ[ℂ] _)
  let M : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' f
  have hM : Matrix.toLin' M = f := Matrix.toLin'_toMatrix' f
  have key : ∀ x y : Fin n → ℂ, f y ⬝ᵥ star (f x) = y ⬝ᵥ star x := fun x y => by
    have := K.inner_map_map (eu n x) (eu n y)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at this
    exact this
  have hc : ∀ i l, M l i = f (Pi.single i 1) l := fun i l => by
    rw [← hM, Matrix.toLin'_apply, Matrix.mulVec_single_one]
    rfl
  have h1 : M.conjTranspose * M = 1 := by
    ext i j
    have h := key (Pi.single i 1) (Pi.single j 1)
    have e : (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ star (Pi.single i 1 : Fin n → ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      rw [single_one_dotProduct]
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [← e, ← h]
    simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, hc, Pi.star_apply, mul_comm]
  have h2 : M * M.conjTranspose = 1 := mul_eq_one_comm.1 h1
  let k : GL (Fin n) ℂ := ⟨M, M.conjTranspose, h2, h1⟩
  refine ⟨k, (thetaR_eq_self_iff k).2 rfl, fun W => ?_⟩
  have : (k.val : Matrix (Fin n) (Fin n) ℂ) = M := rfl
  change Submodule.map _ (Submodule.map (Matrix.toLin' M) W) = _
  rw [hM, ← Submodule.map_comp, ← Submodule.map_comp]
  refine congrArg (fun t => Submodule.map t W) (LinearMap.ext fun x => ?_)
  simp [f]

theorem img_mul_inv_eq {g k : GL (Fin n) ℂ} {W : Submodule ℂ (Fin n → ℂ)} (h : img k (img g⁻¹ W) = W) :
    img (g * k⁻¹) W = W := by
  conv_lhs => rw [← h]
  rw [← img_mul, ← img_mul, show g * k⁻¹ * k * g⁻¹ = 1 by group, img_one]

theorem exists_flag_unitary (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (h : W₁ ≤ W₂) (g : GL (Fin n) ℂ) :
    ∃ k : GL (Fin n) ℂ, thetaR (starRingEnd ℂ) n k = k ∧ img k (img g⁻¹ W₁) = W₁ ∧ img k (img g⁻¹ W₂) = W₂ := by
  obtain ⟨K, hK₁, hK₂⟩ := exists_isometry_flag_of_equiv (eu n) (img_mono g⁻¹ h) h
    (finrank_img g⁻¹ W₁) (finrank_img g⁻¹ W₂)
  obtain ⟨k, hk, hkK⟩ := unitary_of_isometry K
  have hinj : Function.Injective (eu n : (Fin n → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := (eu n).injective
  have inj := Submodule.map_injective_of_injective hinj
  exact ⟨k, hk, inj ((hkK _).trans hK₁), inj ((hkK _).trans hK₂)⟩

theorem exists_eq_mul_unitary (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (h : W₁ ≤ W₂) (g : GL (Fin n) ℂ) :
    ∃ q k : GL (Fin n) ℂ, g = q * k ∧ thetaR (starRingEnd ℂ) n k = k ∧ img q W₁ = W₁ ∧ img q W₂ = W₂ := by
  obtain ⟨k, hk, h₁, h₂⟩ := exists_flag_unitary W₁ W₂ h g
  exact ⟨g * k⁻¹, k, by group, hk, img_mul_inv_eq h₁, img_mul_inv_eq h₂⟩

theorem iwaFlag : PositivityTheory.Rg.BcB.D4.IwaFlag := fun _ W₁ W₂ h g => by
  obtain ⟨q, k, e, hk, h₁, h₂⟩ := exists_eq_mul_unitary W₁ W₂ h g
  exact ⟨q, ⟨h₁, h₂⟩, k, hk, e⟩

end GlobalTheory.CompanionTheory.IwaDecomp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFacts
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.RadicalForm

variable {K : Type} [Field K] {n : ℕ}

noncomputable def cols (S : Submodule K (Fin n → K)) : Fin (Module.finrank K S) → (Fin n → K) :=
  fun j => (Module.finBasis K S j : Fin n → K)

theorem cols_li (S : Submodule K (Fin n → K)) : LinearIndependent K (cols S) :=
  (Module.finBasis K S).linearIndependent.map' S.subtype S.ker_subtype

theorem cols_span (S : Submodule K (Fin n → K)) : Submodule.span K (Set.range (cols S)) = S := by
  have h : Set.range (cols S) = S.subtype '' Set.range (Module.finBasis K S) := by
    rw [← Set.range_comp]; rfl
  rw [h, Submodule.span_image, (Module.finBasis K S).span_eq, Submodule.map_top,
    Submodule.range_subtype]

def form (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) : K :=
  (fun i => σ (u i)) ⬝ᵥ (D *ᵥ v)

theorem form_add_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (u u' v : Fin n → K) :
    form σ D (u + u') v = form σ D u v + form σ D u' v := by
  simp [form, dotProduct, add_mul, Finset.sum_add_distrib]

theorem form_smul_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (c : K) (u v : Fin n → K) :
    form σ D (c • u) v = σ c * form σ D u v := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

theorem form_zero_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    form σ D 0 v = 0 := by
  simp [form, dotProduct]

theorem mem_perpD (σ : K →+* K) (d : GL (Fin n) K) (W : Submodule K (Fin n → K)) (v : Fin n → K) :
    v ∈ perpD σ d W ↔ ∀ x ∈ W, form σ (d⁻¹).val x v = 0 := by
  have h1 : d.val * (d⁻¹).val = 1 := Units.mul_inv d
  have h2 : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  constructor
  · rintro ⟨y, hy, rfl⟩ x hx
    have hy' : ∀ x ∈ W, ∑ i, σ (x i) * y i = 0 := hy
    have h3 : (d⁻¹).val *ᵥ (Matrix.toLin' d.val y) = y := by
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    simp only [form, h3]
    exact hy' x hx
  · intro h
    refine ⟨(d⁻¹).val *ᵥ v, fun x hx => h x hx, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem form_swap (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (D γ : Matrix (Fin n) (Fin n) K)
    (hγ : D * γ = (D.map σ)ᵀ) (u v : Fin n → K) :
    form σ D u (γ *ᵥ v) = σ (form σ D v u) := by
  simp only [form, Matrix.mulVec_mulVec, hγ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, map_sum, map_mul, hσ, transpose_apply, map_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem entry {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : K →+* K)
    (D : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) κ K) (N : Matrix (Fin n) κ' K) (i j) :
    ((M.map σ)ᵀ * D * N) i j = form σ D (fun k => M k i) (fun k => N k j) := by
  rw [Matrix.mul_assoc]; rfl

theorem entry_mulVec {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : K →+* K)
    (D : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) κ K) (N : Matrix (Fin n) κ' K)
    (c : κ' → K) (i) :
    (((M.map σ)ᵀ * D * N) *ᵥ c) i = form σ D (fun k => M k i) (N *ᵥ c) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; rfl

theorem exists_adapted (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (d : GL (Fin n) K)
    (γ : Matrix (Fin n) (Fin n) K) (hγ : (d⁻¹).val * γ = ((d⁻¹).val.map σ)ᵀ)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) = W) :
    ∃ (a b : ℕ) (B : Matrix (Fin n) (Fin a) K) (A : Matrix (Fin n) (Fin b) K),
      LinearIndependent K (fromCols B A)ᵀ ∧
      Submodule.span K (Set.range Bᵀ) = W ⊓ perpD σ d W ∧
      Submodule.span K (Set.range (fromCols B A)ᵀ) = W ∧
      ((fromCols B A).map σ)ᵀ * (d⁻¹).val * B = 0 ∧ (B.map σ)ᵀ * (d⁻¹).val * fromCols B A = 0 ∧
      ((A.map σ)ᵀ * (d⁻¹).val * A).det ≠ 0 := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (W ⊓ perpD σ d W)
  have hC : (W ⊓ perpD σ d W) ⊔ (Q ⊓ W) = W := by
    rw [← sup_inf_assoc_of_le Q (inf_le_left : W ⊓ perpD σ d W ≤ W), hQ.sup_eq_top, top_inf_eq]
  have hdis : Disjoint (W ⊓ perpD σ d W) (Q ⊓ W) := hQ.disjoint.mono_right inf_le_left
  obtain ⟨a, u, hu, hus⟩ : ∃ (a : ℕ) (u : Fin a → Fin n → K), LinearIndependent K u ∧
      Submodule.span K (Set.range u) = W ⊓ perpD σ d W := ⟨_, _, cols_li _, cols_span _⟩
  obtain ⟨b, v, hv, hvs⟩ : ∃ (b : ℕ) (v : Fin b → Fin n → K), LinearIndependent K v ∧
      Submodule.span K (Set.range v) = Q ⊓ W := ⟨_, _, cols_li _, cols_span _⟩
  have hum : ∀ j, u j ∈ W ⊓ perpD σ d W := fun j => hus ▸ Submodule.subset_span ⟨j, rfl⟩
  have hvm : ∀ j, v j ∈ Q ⊓ W := fun j => hvs ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin a) K, Bᵀ = u := ⟨(Matrix.of u)ᵀ, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin b) K, Aᵀ = v := ⟨(Matrix.of v)ᵀ, rfl⟩
  have hT : ((fromCols B A)ᵀ : _ → _ → K) = Sum.elim u v := by
    subst hB hA
    funext s k
    rcases s with j | j <;> rfl
  have hspan : Submodule.span K (Set.range (fromCols B A)ᵀ) = W := by
    rw [hT, Set.Sum.elim_range, Submodule.span_union, hus, hvs, hC]
  have hli : LinearIndependent K (fromCols B A)ᵀ := by
    rw [hT]
    exact hu.sum_type hv (by rw [hus, hvs]; exact hdis)
  have hFW : ∀ s, (fun k => fromCols B A k s) ∈ W := fun s => by
    have : (fun k => fromCols B A k s) ∈ Submodule.span K (Set.range (fromCols B A)ᵀ) :=
      Submodule.subset_span ⟨s, rfl⟩
    rwa [hspan] at this
  have hr : ∀ w ∈ W ⊓ perpD σ d W, ∀ x ∈ W, form σ (d⁻¹).val x w = 0 := fun w hw x hx =>
    (mem_perpD σ d W w).1 hw.2 x hx
  have hl : ∀ w ∈ W ⊓ perpD σ d W, ∀ x ∈ W, form σ (d⁻¹).val w x = 0 := fun w hw x hx => by
    rw [← hW] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [Matrix.toLin'_apply, form_swap σ hσ _ γ hγ, hr w hw x' hx', map_zero]
  have hBc : ∀ j, (fun k => B k j) = u j := fun j => congrFun hB j
  have hAc : ∀ j, (fun k => A k j) = v j := fun j => congrFun hA j
  refine ⟨_, _, B, A, hli, by rw [hB]; exact hus, hspan, ?_, ?_, ?_⟩
  · ext i j
    rw [entry, hBc]
    exact hr _ (hum j) _ (hFW i)
  · ext i j
    rw [entry, hBc]
    exact hl _ (hum i) _ (hFW j)
  · intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hAv : A *ᵥ c = ∑ j, c j • v j := by
      rw [Matrix.mulVec_eq_sum, hA]
      exact Finset.sum_congr rfl fun j _ => op_smul_eq_smul _ _
    have hyC : A *ᵥ c ∈ Q ⊓ W := by
      rw [hAv]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvm j)
    have hyW : A *ᵥ c ∈ W := hyC.2
    have hcol : ∀ s, form σ (d⁻¹).val (fun k => fromCols B A k s) (A *ᵥ c) = 0 := by
      rintro (j | j)
      · have h := hl _ (hum j) _ hyW
        rw [← hBc j] at h
        exact h
      · have := congrFun hc j
        rw [entry_mulVec] at this
        exact this
    have hperp : A *ᵥ c ∈ perpD σ d W := by
      rw [mem_perpD]
      intro x hx
      rw [← hspan] at hx
      induction hx using Submodule.span_induction with
      | mem x h =>
        obtain ⟨s, rfl⟩ := h
        exact hcol s
      | zero => exact form_zero_left _ _ _
      | add x y _ _ hx hy => rw [form_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [form_smul_left, hx, mul_zero]
    have hy0 : A *ᵥ c = 0 := by
      have := hdis.le_bot (show A *ᵥ c ∈ _ from ⟨⟨hyW, hperp⟩, hyC⟩)
      simpa using this
    apply hc0
    have hsum : ∑ j, c j • v j = 0 := by rw [← hAv, hy0]
    funext j
    exact Fintype.linearIndependent_iff.1 hv c hsum j

theorem radical : Radical := by
  intro E _ _ _ n d W hW
  have hσ : ∀ x, conjE E (conjE E x) = x := fun x => NumberField.IsCMField.complexConj_apply_apply E x
  refine exists_adapted (conjE E) hσ d (nrm d).val ?_ W hW
  have h2 : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  rw [nrm, Units.val_mul, ← mul_assoc, h2, one_mul, thetaR_val]

end GlobalTheory.CompanionTheory.RadicalForm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFactsStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radical_subspace_facts : Radical := by
  first | exact @GlobalTheory.CompanionTheory.RadicalForm.radical | exact GlobalTheory.CompanionTheory.RadicalForm.radical | (intros; apply GlobalTheory.CompanionTheory.RadicalForm.radical <;> assumption)
end
end
