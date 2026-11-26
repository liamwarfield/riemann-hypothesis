module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealCompression
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEq
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvAtParabNeZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg

section Quot

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y]
  [Module ℂ Y]

end Quot

section Main

variable {k : Type} [Field k] [TopologicalSpace k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem isGeneric_of_surjective {τ : Representation ℂ (GL (Fin N) k) W} {π : Representation ℂ (GL (Fin N) k) V}
    (q : τ.IntertwiningMap π) (hq : Function.Surjective q) (h : IsGeneric π) : IsGeneric τ := by
  obtain ⟨ψ, h1, h2, h3⟩ := h
  refine ⟨ψ, h1, h2, nontrivial_twJacquet_of_surjective q.toLinearMap hq
    (fun u v => Submodule.subset_span ⟨u, q v, ?_⟩) h3⟩
  rw [map_sub, map_smul]
  exact congrArg (· - _) (q.isIntertwining _ _ _ v)

end Main

end GlobalTheory.CompanionTheory.BZSeg

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactors
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactors
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd.ProdDrop

section Blocks

variable (k : Type) [Field k] {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r)
  (ho : StrictMono o) (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (hd' : ∑ a, d (o a) = N)

include ho hz

theorem mem_parab_drop (g : GL (Fin N) k) :
    g ∈ parab k (stdBlocks d hd) ↔ g ∈ parab k (stdBlocks (fun a => d (o a)) hd') := by
  have hE := GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty d hd o ho hz hd'
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro h a b i j hab
    rw [hE, hE]
    exact h _ _ i j (ho hab)
  · intro h a b i j hab
    obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
    obtain ⟨b, rfl⟩ := hz b (Nat.pos_iff_ne_zero.1 (Fin.pos j))
    have := h a b i j (ho.lt_iff_lt.1 hab)
    rwa [hE, hE] at this

theorem dropHom_leviProj (p : parab k (stdBlocks d hd)) (q : parab k (stdBlocks (fun a => d (o a)) hd'))
    (h : (p : GL (Fin N) k) = q) :
    dropHom d o (leviProj k (stdBlocks d hd) p) = leviProj k (stdBlocks (fun a => d (o a)) hd') q := by
  have hE := GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty d hd o ho hz hd'
  funext a
  ext i j
  show (leviProj k (stdBlocks d hd) p (o a) : Matrix _ _ k) i j = _
  rw [leviProj_apply, leviProj_apply, hE, hE, h]

theorem modExp_drop (a : Fin r') :
    modExp (fun j => Fin (d j)) (o a) = modExp (fun b => Fin (d (o b))) a := by
  have h0 : ∀ j, j ∉ Set.range o → d j = 0 := fun j hj => by_contra fun h => hj (hz j h)
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter]
  congr 1
  · refine (Fintype.sum_of_injective o ho.injective _ _ (fun j hj => ?_) fun b => ?_).symm
    · simp [h0 j hj]
    · simp [ho.lt_iff_lt]
  · refine (Fintype.sum_of_injective o ho.injective _ _ (fun j hj => ?_) fun b => ?_).symm
    · simp [h0 j hj]
    · simp [ho.lt_iff_lt]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r)
  (ho : StrictMono o) (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (hd' : ∑ a, d (o a) = N)


include ho hz in
theorem deltaHalf_drop (g : Levi k fun j => Fin (d j)) :
    deltaHalf k (fun j => Fin (d j)) g = deltaHalf k (fun a => Fin (d (o a))) (dropHom d o g) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine (Fintype.prod_of_injective o ho.injective _ _ (fun j hj => ?_) fun a => ?_).symm
  · have hj0 : d j = 0 := by_contra fun h => hj (hz j h)
    have : IsEmpty (Fin (d j)) := by rw [hj0]; infer_instance
    have h1 : Matrix.GeneralLinearGroup.det (g j) = 1 := Units.ext (by simp [Matrix.det_isEmpty])
    rw [h1, map_one]
  · rw [modExp_drop d o ho hz]
    rfl


include ho hz in
theorem parInd_comp_dropHom_equiv {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun a => Fin (d (o a))) W) :
    Nonempty ((parInd (stdBlocks d hd) (τ.comp (dropHom d o) : Representation ℂ (Levi k fun j => Fin (d j)) W)).Equiv
      (parInd (stdBlocks (fun a => d (o a)) hd') τ)) := by
  have key : ∀ (p : parab k (stdBlocks d hd)) (q : parab k (stdBlocks (fun a => d (o a)) hd')),
      (p : GL (Fin N) k) = q →
      GlobalTheory.SmGL.twist (τ.comp (dropHom d o) : Representation ℂ (Levi k fun j => Fin (d j)) W) (deltaHalf k _)
          (leviProj k (stdBlocks d hd) p) =
        GlobalTheory.SmGL.twist τ (deltaHalf k _) (leviProj k (stdBlocks (fun a => d (o a)) hd') q) := fun p q h => by
    refine LinearMap.ext fun v => ?_
    rw [twist_apply, twist_apply, deltaHalf_drop d o ho hz, dropHom_leviProj k d hd o ho hz hd' p q h]
    show _ • τ (dropHom d o _) v = _
    rw [dropHom_leviProj k d hd o ho hz hd' p q h]
  refine Placing.smInd_equiv 1
    (fun q => ⟨⟨q.1, (mem_parab_drop k d hd o ho hz hd' q.1).2 q.2⟩, by simp, key _ _ rfl⟩)
    (fun p => ⟨⟨p.1, (mem_parab_drop k d hd o ho hz hd' p.1).1 p.2⟩, by simp, (key _ _ rfl).symm⟩)

end Local


set_option maxHeartbeats 1000000 in
theorem prodIrr_drop : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr (fun a => y (o a)) hd')) := by
  intro k _ _ _ _ r r' N y hd o ho hz hd'
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv y o ho hz
  obtain ⟨χ⟩ := parInd_comp_dropHom_equiv (k := k) (fun j => (y j).1) hd o ho hz hd'
    (piTensor fun a => (y (o a)).rep)
  have e1 := parIndEquiv (stdBlocks (fun j => (y j).1) hd) φ
  have e2 := e1.trans χ
  unfold prodIrr multiProd
  exact ⟨e2⟩

end GlobalTheory.CompanionTheory.FineProd.ProdDrop

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedProductDropZeroFactorsStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_product_drop_zero_factors : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr (fun a => y (o a)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop | exact GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop | (intros; apply GlobalTheory.CompanionTheory.FineProd.ProdDrop.prodIrr_drop <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCommonOrderedForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOrderedForm
open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegOrder

variable {T : Type u}

theorem exists_last_start (s : T → T) (hs : ∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t)
    (m : Multiset (ASeg T)) (hm : m ≠ 0) :
    ∃ a ∈ m, ∀ b ∈ m, ¬ ∃ j : ℕ, 0 < j ∧ b.start = s^[j] a.start := by
  have irr : ∀ a : ASeg T, ¬ ∃ j : ℕ, 0 < j ∧ a.start = s^[j] a.start := by
    rintro a ⟨j, hj, h⟩
    exact hs a.start j hj h.symm
  induction m using Multiset.induction_on with
  | empty => exact absurd rfl hm
  | cons x m ih =>
    by_cases hm' : m = 0
    · subst hm'
      refine ⟨x, Multiset.mem_cons_self x 0, ?_⟩
      intro b hb
      have hbx : b = x := by simpa using hb
      subst hbx
      exact irr b
    · obtain ⟨a, ham, hmax⟩ := ih hm'
      by_cases hax : ∃ j : ℕ, 0 < j ∧ x.start = s^[j] a.start
      · obtain ⟨j, hj, hxa⟩ := hax
        refine ⟨x, Multiset.mem_cons_self x m, ?_⟩
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hbm
        · exact irr b
        · rintro ⟨i, hi, hbx⟩
          refine hmax b hbm ⟨i + j, by omega, ?_⟩
          rw [hbx, hxa, Function.iterate_add_apply]
      · refine ⟨a, Multiset.mem_cons_of_mem ham, ?_⟩
        intro b hb
        rcases Multiset.mem_cons.mp hb with rfl | hbm
        · exact hax
        · exact hmax b hbm

theorem exists_ordered_form : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m : Multiset (ASeg T), ∃ L : List (ASeg T), (L : Multiset (ASeg T)) = m ∧ AOrdered s L := by
  classical
  intro T s _ hs m
  induction hn : Multiset.card m generalizing m with
  | zero =>
    refine ⟨[], ?_, List.Pairwise.nil⟩
    simpa using (Multiset.card_eq_zero.mp hn).symm
  | succ n ih =>
    have hm : m ≠ 0 := by
      rintro rfl
      simp at hn
    obtain ⟨a, ham, hmax⟩ := exists_last_start s hs m hm
    have hcard : Multiset.card (m.erase a) = n := by
      rw [Multiset.card_erase_of_mem ham, hn]
      rfl
    obtain ⟨L, hL, hord⟩ := ih (m.erase a) hcard
    refine ⟨a :: L, ?_, ?_⟩
    · rw [← Multiset.cons_coe, hL]
      exact Multiset.cons_erase ham
    · refine List.pairwise_cons.mpr ⟨?_, hord⟩
      intro b hb hprec
      have hbm : b ∈ m := by
        have : b ∈ (L : Multiset (ASeg T)) := by simpa using hb
        rw [hL] at this
        exact Multiset.mem_of_mem_erase this
      exact hmax b hbm hprec.2

end GlobalTheory.CompanionTheory.SegOrder
end

open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegOrder

variable {T : Type u}

theorem interleave_left_nil (b : List T) : Interleave b [] b := by
  induction b with
  | nil => exact Interleave.nil
  | cons a b ih => exact Interleave.left ih

theorem interleave_right_nil (b : List T) : Interleave [] b b := by
  induction b with
  | nil => exact Interleave.nil
  | cons a b ih => exact Interleave.right ih

theorem Interleave.append_left {u v w : List T} (h : Interleave u v w) (b : List T) :
    Interleave (u ++ b) v (w ++ b) := by
  induction h with
  | nil => exact interleave_left_nil b
  | left _ ih => exact Interleave.left ih
  | right _ ih => exact Interleave.right ih

theorem Interleave.append_right {u v w : List T} (h : Interleave u v w) (b : List T) :
    Interleave u (v ++ b) (w ++ b) := by
  induction h with
  | nil => exact interleave_right_nil b
  | left _ ih => exact Interleave.left ih
  | right _ ih => exact Interleave.right ih

theorem wt_cons (s : T → T) (a : ASeg T) (L : List (ASeg T)) :
    wt s (a :: L) = wt s L ++ ASeg.dec s a := by
  simp [wt]

theorem exists_sublists_interleave (s : T → T) (L : List (ASeg T)) :
    ∀ m n : Multiset (ASeg T), (L : Multiset (ASeg T)) = m + n →
      ∃ L₁ L₂ : List (ASeg T), L₁.Sublist L ∧ L₂.Sublist L ∧
        (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
        Interleave (wt s L₁) (wt s L₂) (wt s L) := by
  classical
  induction L with
  | nil =>
    intro m n h
    have h0 : m = 0 ∧ n = 0 := add_eq_zero.1 (by simpa using h.symm)
    refine ⟨[], [], List.Sublist.refl _, List.Sublist.refl _, ?_, ?_, Zc.Comb.Interleave.nil⟩
    · simp [h0.1]
    · simp [h0.2]
  | cons a L ih =>
    intro m n h
    have ha : a ∈ m + n := by
      rw [← h]
      simp
    rcases Multiset.mem_add.1 ha with ha | ha
    · have hL : (L : Multiset (Zc.Comb.ASeg T)) = m.erase a + n := by
        apply (Multiset.cons_inj_right a).1
        rw [Multiset.cons_coe, h, ← Multiset.cons_add, Multiset.cons_erase ha]
      obtain ⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩ := ih (m.erase a) n hL
      refine ⟨a :: L₁, L₂, List.Sublist.cons₂ a h₁, List.Sublist.cons a h₂, ?_, e₂, ?_⟩
      · rw [← Multiset.cons_coe, e₁, Multiset.cons_erase ha]
      · rw [GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]
        exact GlobalTheory.CompanionTheory.SegOrder.Interleave.append_left hI _
    · have hL : (L : Multiset (Zc.Comb.ASeg T)) = m + n.erase a := by
        apply (Multiset.cons_inj_right a).1
        rw [Multiset.cons_coe, h, ← Multiset.add_cons, Multiset.cons_erase ha]
      obtain ⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩ := ih m (n.erase a) hL
      refine ⟨L₁, a :: L₂, List.Sublist.cons a h₁, List.Sublist.cons₂ a h₂, e₁, ?_, ?_⟩
      · rw [← Multiset.cons_coe, e₂, Multiset.cons_erase ha]
      · rw [GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]
        exact GlobalTheory.CompanionTheory.SegOrder.Interleave.append_right hI _

theorem exists_common_ordered_form : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m n : Multiset (ASeg T), ∃ L₁ L₂ L : List (ASeg T),
      (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
      (L : Multiset (ASeg T)) = m + n ∧ AOrdered s L₁ ∧ AOrdered s L₂ ∧ AOrdered s L ∧
      Interleave (wt s L₁) (wt s L₂) (wt s L) := by
  intro T s hinj hs m n
  obtain ⟨L, hL, hord⟩ := exists_ordered_form s hinj hs (m + n)
  obtain ⟨L₁, L₂, h₁, h₂, c₁, c₂, hi⟩ := exists_sublists_interleave s L m n hL
  exact ⟨L₁, L₂, L, c₁, c₂, hL, List.Pairwise.sublist h₁ hord, List.Pairwise.sublist h₂ hord,
    hord, hi⟩

end GlobalTheory.CompanionTheory.SegOrder
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSum
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcMerge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def fromA (a : Comb.ASeg (CuspT k)) : Segment k := Segment.ofFirst a.start.1 a.start.2 a.len a.len_pos

theorem toA_fromA (a : Comb.ASeg (CuspT k)) : toA (fromA a) = a := rfl

theorem fromA_toA (Δ : Segment k) : fromA (toA Δ) = Δ := Segment.ext_first rfl rfl

theorem carrier_subset_of_image {Δ Δ' : Segment k} (h : (toA Δ).carrier sNu ⊆ (toA Δ').carrier sNu) :
    Δ.carrier ⊆ Δ'.carrier := by
  rw [← ZcWords.image_carrier, ← ZcWords.image_carrier]
  exact Set.image_mono h

theorem aPrecedes_of_precedes {Δ Δ' : Segment k} (h : Δ.Precedes Δ') : Comb.APrecedes sNu (toA Δ) (toA Δ') := by
  obtain ⟨⟨⟨Γ, hΓ⟩, h1, h2⟩, j, hj, hs⟩ := h
  refine ⟨⟨⟨toA Γ, ?_⟩, fun e => h1 (carrier_subset_of_image e), fun e => h2 (carrier_subset_of_image e)⟩, j, hj,
    Subtype.ext ?_⟩
  · apply Set.image_injective.2 (Subtype.val_injective (p := fun x : IrrGL (k := k) => x.IsCusp))
    rw [Set.image_union, ZcWords.image_carrier, ZcWords.image_carrier, ZcWords.image_carrier, hΓ]
  · exact hs.trans (ZcWords.val_sNu_iterate (toA Δ).start j).symm

theorem map_toA_map_fromA (L : List (Comb.ASeg (CuspT k))) : (L.map fromA).map toA = L := by
  rw [List.map_map]
  exact List.map_id'' toA_fromA L

theorem isOrderedForm_get {L : List (Comb.ASeg (CuspT k))} {𝔪 : Multiset (Segment k)}
    (hL : (L : Multiset (Comb.ASeg (CuspT k))) = 𝔪.map toA) (hO : Comb.AOrdered sNu L) :
    IsOrderedForm (L.map fromA).get 𝔪 := by
  constructor
  · rw [Fin.univ_val_map, List.ofFn_get, ← Multiset.map_coe, hL, Multiset.map_map]
    exact (Multiset.map_congr rfl fun Δ _ => fromA_toA Δ).trans (Multiset.map_id' 𝔪)
  · intro i j hij hp
    rw [Comb.AOrdered, ← map_toA_map_fromA L, List.pairwise_map] at hO
    exact List.pairwise_iff_get.1 hO i j hij (aPrecedes_of_precedes hp)

theorem wtW_get (L : List (Comb.ASeg (CuspT k))) :
    wtW (L.map fromA).get = (Comb.wt sNu L).map Subtype.val := by
  rw [ZcWords.wtW_eq, List.ofFn_get, map_toA_map_fromA]

theorem exists_common_orderedForm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)),
    ∃ (h₁ h₂ h : ℕ) (Δ₁ : Fin h₁ → Segment k) (Δ₂ : Fin h₂ → Segment k) (Δ : Fin h → Segment k),
      IsOrderedForm Δ₁ 𝔪 ∧ IsOrderedForm Δ₂ 𝔫 ∧ IsOrderedForm Δ (𝔪 + 𝔫) ∧
        Zc.Comb.Interleave (wtW Δ₁) (wtW Δ₂) (wtW Δ) := by
  intro k _ _ _ _ _ 𝔪 𝔫
  obtain ⟨L₁, L₂, L, h1, h2, h3, o1, o2, o3, hI⟩ := GlobalTheory.CompanionTheory.SegOrder.exists_common_ordered_form (sNu (k := k)) ZcWords.sNu_injective
    ZcWords.sNu_aperiodic (𝔪.map toA) (𝔫.map toA)
  refine ⟨_, _, _, (L₁.map fromA).get, (L₂.map fromA).get, (L.map fromA).get, isOrderedForm_get h1 o1,
    isOrderedForm_get h2 o2, isOrderedForm_get (by rw [h3, Multiset.map_add (f := _)]) o3, ?_⟩
  rw [wtW_get, wtW_get, wtW_get]
  exact ZcWords.interleave_map _ hI

end GlobalTheory.CompanionTheory.ZcMerge

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSumStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordered_forms_interleave_sum : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)), ∃ (h₁ h₂ h : ℕ) (Δ₁ : Fin h₁ → Segment k) (Δ₂ : Fin h₂ → Segment k) (Δ : Fin h → Segment k), IsOrderedForm Δ₁ 𝔪 ∧ IsOrderedForm Δ₂ 𝔫 ∧ IsOrderedForm Δ (𝔪 + 𝔫) ∧ Zc.Comb.Interleave (wtW Δ₁) (wtW Δ₂) (wtW Δ) := by
  first | exact @GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm | exact GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm | (intros; apply GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterConjIsOpen
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.TopGroup

theorem inter_conj_isOpen :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G),
      IsOpen (J : Set G) → ∀ g : G,
        IsOpen ((J ⊓ J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro G _ _ _ J hJ g
  have hpre : ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
      = (fun x : G => g⁻¹ * x * g) ⁻¹' (J : Set G) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩
  have hcont : Continuous (fun x : G => g⁻¹ * x * g) := by fun_prop
  have h2 : IsOpen ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [hpre]; exact hJ.preimage hcont
  rw [Subgroup.coe_inf]
  exact hJ.inter h2

end GlobalTheory.CompanionTheory.TopGroup
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactSubgroupSmallAnnihilator
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZOnto.PerpSmall

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (m : ℕ) (s : kˣ) : AddSubgroup (Fin m → k) where
  carrier := {l | ∀ j, l j ∈ cball s}
  add_mem' ha hb j := add_mem_cball (ha j) (hb j)
  zero_mem' _ := by simp [cball]
  neg_mem' ha j := neg_mem_cball (ha j)

theorem mem_box {m : ℕ} {s : kˣ} {l : Fin m → k} : l ∈ box m s ↔ ∀ j, l j ∈ cball s := by
  exact Iff.rfl

theorem coe_box (m : ℕ) (s : kˣ) :
    (box m s : Set (Fin m → k)) = Set.univ.pi fun _ => cball s := by
  ext l
  simp only [SetLike.mem_coe, mem_box, Set.mem_univ_pi]

theorem isCompact_box (m : ℕ) (s : kˣ) : IsCompact (box m s : Set (Fin m → k)) := by
  rw [coe_box]
  exact isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s

theorem box_mem_nhds (m : ℕ) (s : kˣ) : (box m s : Set (Fin m → k)) ∈ 𝓝 (0 : Fin m → k) := by
  rw [coe_box]
  exact set_pi_mem_nhds Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.cball_mem_nhds s

theorem exists_box_subset {m : ℕ} {Ω : Set (Fin m → k)} (hΩ : Ω ∈ 𝓝 (0 : Fin m → k)) :
    ∃ r : kˣ, (box m r : Set (Fin m → k)) ⊆ Ω := by
  rw [nhds_pi, Filter.mem_pi'] at hΩ
  obtain ⟨I, t, ht, hsub⟩ := hΩ
  choose s hs using fun i => GlobalTheory.SplitWeil.exists_cball_subset (by simpa using ht i)
  by_cases hm : Nonempty (Fin m)
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ValuativeRel.valuation k (s i : k))
      Finset.univ_nonempty
    refine ⟨s i₀, fun l hl => hsub fun i _ => hs i ?_⟩
    exact le_trans (show ValuativeRel.valuation k (l i) ≤ _ from (mem_box.1 hl) i) (hi₀ i (Finset.mem_univ _))
  · exact ⟨1, fun l _ => hsub fun i _ => (hm ⟨i⟩).elim⟩

theorem dotProduct_mem_cball {m : ℕ} {r s : kˣ} {b l : Fin m → k} (hb : b ∈ box m (r * s⁻¹))
    (hl : l ∈ box m s) : b ⬝ᵥ l ∈ cball r := by
  unfold dotProduct
  refine Finset.sum_induction _ (· ∈ cball r) (fun a b ha hb => add_mem_cball ha hb) ?_ ?_
  · simp only [GlobalTheory.SplitWeil.cball, Set.mem_ofPred_eq]
    show ValuativeRel.valuation k 0 ≤ _
    simp
  · intro j _
    have h1 := (mem_box.1 hb) j
    have h2 := (mem_box.1 hl) j
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_ofPred_eq]
    show ValuativeRel.valuation k (b j * l j) ≤ ValuativeRel.valuation k (r : k)
    rw [map_mul]
    calc ValuativeRel.valuation k (b j) * ValuativeRel.valuation k (l j)
        ≤ ValuativeRel.valuation k ((r * s⁻¹ : kˣ) : k) * ValuativeRel.valuation k (s : k) := mul_le_mul' h1 h2
      _ = ValuativeRel.valuation k (r : k) := by
        rw [← map_mul]
        congr 1
        simp

end GlobalTheory.CompanionTheory.BZOnto.PerpSmall
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnLeviCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnLeviCompact
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.HalfModCompact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nabs_le_of_isCompact {C : Set k} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ u : kˣ, (u : k) ∈ C → nabs k u ≤ B := by
  classical
  have hopen : ∀ y : kˣ, IsOpen {x : k | valuation k x ≤ valuation k (y : k)} := by
    intro y
    have hy : valuation k (y : k) ≠ 0 := by simp
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨Units.mk0 (valuation k (y : k)) hy, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_ofPred_eq] at hz hx ⊢
    calc valuation k (x + z) ≤ max (valuation k x) (valuation k z) := Valuation.map_add _ _ _
      _ ≤ valuation k (y : k) := max_le hx (le_of_lt (by simpa using hz))
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun y : kˣ => {x : k | valuation k x ≤ valuation k (y : k)})
    hopen (by
      intro x _
      rw [Set.mem_iUnion]
      by_cases hx : x = 0
      · exact ⟨1, by simp [hx]⟩
      · exact ⟨Units.mk0 x hx, by simp⟩)
  obtain ⟨y, -, hy⟩ := Finset.exists_max_image (insert 1 t) (fun y : kˣ => valuation k (y : k))
    (Finset.insert_nonempty _ _)
  refine ⟨nabs k y, fun u hu => nabs_le_of_valuation_le ?_⟩
  obtain ⟨z, hz, hzu⟩ := Set.mem_iUnion₂.1 (ht hu)
  exact le_trans hzu (hy z (Finset.mem_insert_of_mem hz))

theorem nabs_pow_eq (y : kˣ) (n : ℕ) : nabs k (y ^ n) = nabs k y ^ n := by
  unfold nabs
  rw [map_pow, NNReal.coe_pow]

theorem nabs_inv_eq (y : kˣ) : nabs k y⁻¹ = (nabs k y)⁻¹ := by
  unfold nabs
  rw [map_inv, NNReal.coe_inv]

theorem nabs_eq_one_of_pow_le (y : kˣ) (B : ℝ) (h₁ : ∀ n : ℕ, nabs k (y ^ n) ≤ B)
    (h₂ : ∀ n : ℕ, nabs k (y⁻¹ ^ n) ≤ B) : nabs k y = 1 := by
  have hpos : 0 < nabs k y := (nabs_properties k).2.1 y
  rcases lt_trichotomy (nabs k y) 1 with hlt | heq | hgt
  · exfalso
    have hinv : 1 < (nabs k y)⁻¹ := (one_lt_inv₀ hpos).2 hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hinv
    have h3 := h₂ n
    rw [nabs_pow_eq, nabs_inv_eq] at h3
    linarith
  · exact heq
  · exfalso
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hgt
    have h3 := h₁ n
    rw [nabs_pow_eq] at h3
    linarith

def blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) (g : GL (Fin N) k) : k :=
  Matrix.det (Matrix.of fun i j : Fin (d a) =>
    (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩))

theorem continuous_blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) :
    Continuous (blockDet (k := k) d hd a) := by
  unfold blockDet
  first
    | fun_prop
    | exact Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
        (Units.continuous_val.matrix_elem _ _))

theorem blockDet_leviEmb {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h)
    (x : Levi k (Bl d)) :
    blockDet d hd a (leviEmb k (stdBlocks d hd) x) =
      ((Matrix.GeneralLinearGroup.det (x a) : kˣ) : k) := by
  unfold blockDet
  have hm : (Matrix.of fun i j : Fin (d a) =>
      ((leviEmb k (stdBlocks d hd) x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩)) =
      ((x a : GL (Bl d a) k) : Matrix (Bl d a) (Bl d a) k) := by
    ext i j
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  rw [hm, Matrix.GeneralLinearGroup.val_det_apply]

theorem nabs_det_eq_one_of_mem_KM {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    {J : Subgroup (GL (Fin N) k)} (hJ : IsCompact (J : Set (GL (Fin N) k)))
    {x : Levi k (Bl d)} (hx : x ∈ KM k N J d hd) (a : Fin h) :
    nabs k (Matrix.GeneralLinearGroup.det (x a)) = 1 := by
  have hmem : ∀ z ∈ KM k N J d hd, blockDet d hd a (leviEmb k (stdBlocks d hd) z) ∈
      blockDet (k := k) d hd a '' (J : Set (GL (Fin N) k)) :=
    fun z hz => ⟨_, hz, rfl⟩
  obtain ⟨B, hB⟩ := exists_nabs_le_of_isCompact (hJ.image (continuous_blockDet d hd a))
  apply nabs_eq_one_of_pow_le _ B
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem hx n)
    have e : (x ^ n) a = x a ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow] at h1
    exact h1
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem ((KM k N J d hd).inv_mem hx) n)
    have e : (x⁻¹ ^ n) a = (x a)⁻¹ ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow, map_inv] at h1
    exact h1

theorem deltaHalf_eq_one_of_mem_KM :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)),
      IsCompact (J : Set (GL (Fin N) k)) → ∀ x ∈ KM k N J d hd, deltaHalf k (Bl d) x = 1 := by
  intro k _ _ _ _ N h d hd J hJ x hx
  unfold deltaHalf
  rw [MonoidHom.finsetProd_apply]
  apply Finset.prod_eq_one
  intro a _
  rw [MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
  unfold detChar
  rw [MonoidHom.comp_apply]
  apply Units.ext
  simp [absPow, nabs_det_eq_one_of_mem_KM d hd hJ hx a]

end GlobalTheory.CompanionTheory.HalfModCompact
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnLeviCompactStatement
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_trivial_on_levi_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsCompact (J : Set (GL (Fin N) k)) → ∀ x ∈ KM k N J d hd, deltaHalf k (Bl d) x = 1 := by
  first | exact @GlobalTheory.CompanionTheory.HalfModCompact.deltaHalf_eq_one_of_mem_KM | exact GlobalTheory.CompanionTheory.HalfModCompact.deltaHalf_eq_one_of_mem_KM | (intros; apply GlobalTheory.CompanionTheory.HalfModCompact.deltaHalf_eq_one_of_mem_KM <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleContragredientSocle
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleOfIsAtom
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.MaschkeForms

open Representation

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_of_isAtom {π : Representation ℂ G V} {U : Subrepresentation π}
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by
  have hne : U.toSubmodule ≠ ⊥ := fun h => hU.1 (Subrepresentation.toSubmodule_injective h)
  have hnt : Nontrivial (Subrepresentation U.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h' : (⊥ : Submodule ℂ U.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [← U.toSubmodule.map_subtype_top, ← h', Submodule.map_bot]
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation π := ⟨S.toSubmodule.map U.toSubmodule.subtype, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, S.apply_mem_toSubmodule g hx, rfl⟩⟩
  have hT : T ≤ U := U.toSubmodule.map_subtype_le S.toSubmodule
  have hinj := Submodule.map_injective_of_injective U.toSubmodule.injective_subtype
  rcases hU.le_iff.mp hT with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans (Submodule.map_bot _).symm
  · right
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans U.toSubmodule.map_subtype_top.symm

end GlobalTheory.MaschkeForms
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleContragredientSocle
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.SocleContra

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

variable [TopologicalSpace G] [IsTopologicalGroup G]

def pullForm (f : π.IntertwiningMap σ) : (contra σ).IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun l => ⟨l.1 ∘ₗ f.toLinearMap, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds l.2 (by
          show σ.dual 1 l.1 = l.1
          rw [map_one]
          rfl)) fun g hg => LinearMap.ext fun v => by
          have h : σ.dual g l.1 = l.1 := hg
          have h2 := LinearMap.congr_fun h (f v)
          have h3 : σ.dual g l.1 (f v) = l.1 (σ g⁻¹ (f v)) := rfl
          rw [h3, ← f.isIntertwining] at h2
          exact h2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun v => by
    show l.1 (σ g⁻¹ (f v)) = l.1 (f (π g⁻¹ v))
    rw [f.isIntertwining])

theorem pullForm_injective (f : π.IntertwiningMap σ) (hf : Function.Surjective f) :
    Function.Injective (pullForm f) := fun a b h => Subtype.ext (LinearMap.ext fun y => by
  obtain ⟨v, rfl⟩ := hf y
  exact LinearMap.congr_fun (congrArg Subtype.val h) v)

theorem mem_range_pullForm (f : π.IntertwiningMap σ) (hf : Function.Surjective f) (l : smoothPart π.dual)
    (hl : ∀ v, f v = 0 → l.1 v = 0) : l ∈ (pullForm f).range := by
  let q : (V ⧸ LinearMap.ker f.toLinearMap) →ₗ[ℂ] ℂ := (LinearMap.ker f.toLinearMap).liftQ l.1 (fun v hv => hl v hv)
  let l' : Module.Dual ℂ W := q ∘ₗ (f.toLinearMap.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hl' : ∀ v, l' (f v) = l.1 v := fun v => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hf).symm (f v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show q ((f.toLinearMap.quotKerEquivOfSurjective hf).symm (f v)) = _
    rw [this]
    rfl
  have hs : l' ∈ smoothPart σ.dual := mem_smoothPart_of_nhds (Filter.mem_of_superset
    (IsOpen.mem_nhds l.2 (by
      show π.dual 1 l.1 = l.1
      rw [map_one]
      rfl)) fun g hg => LinearMap.ext fun w => by
      obtain ⟨v, rfl⟩ := hf w
      have h : π.dual g l.1 = l.1 := hg
      have h2 := LinearMap.congr_fun h v
      have h3 : π.dual g l.1 v = l.1 (π g⁻¹ v) := rfl
      rw [h3] at h2
      show l' (σ g⁻¹ (f v)) = l' (f v)
      rw [← f.isIntertwining, hl', hl', h2])
  exact ⟨⟨l', hs⟩, Subtype.ext (LinearMap.ext fun v => hl' v)⟩

theorem isSmooth_subContra (S : Subrepresentation (contra π)) : IsSmooth S.toRepresentation := fun l => by
  have : {g : G | S.toRepresentation g l = l} = {g : G | contra π g l.1 = l.1} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact isSmooth_contra π l.1

def evalForms (hπ : IsSmooth π) (S : Subrepresentation (contra π)) : π.IntertwiningMap (contra S.toRepresentation) where
  toLinearMap :=
    { toFun := fun v => ⟨{ toFun := fun l => l.1.1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg =>
          LinearMap.ext fun l => by
            have h : π g v = v := hg
            show ((contra π g⁻¹ l.1 : smoothPart π.dual) : Module.Dual ℂ V) v = l.1.1 v
            rw [contra_apply, inv_inv, h])⟩
      map_add' := fun a b => Subtype.ext (LinearMap.ext fun l => map_add l.1.1 a b)
      map_smul' := fun c a => Subtype.ext (LinearMap.ext fun l => map_smul l.1.1 c a) }
  isIntertwining' g := LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun l => by
    show l.1.1 (π g v) = ((contra π g⁻¹ l.1 : smoothPart π.dual) : Module.Dual ℂ V) v
    rw [contra_apply, inv_inv])

end General

theorem isSocle_contra_of_isCosocle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → IsCosocle σ π → IsSocle (contra σ) (contra π) := by
  intro k _ _ _ _ hA N V W _ _ _ _ σ π hπ _ hc
  obtain ⟨hi, f, hf, hu⟩ := hc
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis (k := k) N
  have hσ : IsSmooth σ := (IsSubquotient.of_surjective f hf).isSmooth hπ
  have hci : (contra σ).IsIrreducible := GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ hσ hi) hi
  refine ⟨hci, pullForm f, pullForm_injective f hf, fun S hS => ?_⟩
  have hSi := GlobalTheory.MaschkeForms.isIrreducible_of_isAtom hS
  have hcS : (contra S.toRepresentation).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ (isSmooth_subContra S) hSi) hSi
  let e := evalForms hπ S
  have hr : e.range ≠ ⊥ := fun h0 => hS.1 (eq_bot_iff.2 fun l hl => by
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have hv : e v ∈ (⊥ : Subrepresentation (contra S.toRepresentation)) := h0 ▸ ⟨v, rfl⟩
    have hv0 : e v = 0 := hv
    exact LinearMap.congr_fun (congrArg Subtype.val hv0) ⟨l, hl⟩)
  have he : Function.Surjective e := fun y => by
    have : y ∈ e.range := by
      have ht : e.range = ⊤ := (eq_bot_or_eq_top _).resolve_left hr
      rw [ht]
      trivial
    exact this
  have hk : e.ker = f.ker := hu _ (isCoatom_ker hcS e he)
  have hle : S ≤ (pullForm f).range := fun l hl => mem_range_pullForm f hf l fun v hv => by
    have hv' : v ∈ e.ker := hk ▸ hv
    have hv0 : e v = 0 := hv'
    exact LinearMap.congr_fun (congrArg Subtype.val hv0) ⟨l, hl⟩
  exact ((isAtom_range hci _ (pullForm_injective f hf)).le_iff.1 hle).resolve_left hS.1

end GlobalTheory.CompanionTheory.SocleContra

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleContragredientSocleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosocle_contragredient_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → IsCosocle σ π → IsSocle (contra σ) (contra π) := by
  first | exact @GlobalTheory.CompanionTheory.SocleContra.isSocle_contra_of_isCosocle | exact GlobalTheory.CompanionTheory.SocleContra.isSocle_contra_of_isCosocle | (intros; apply GlobalTheory.CompanionTheory.SocleContra.isSocle_contra_of_isCosocle <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutePolynomialOfMemCentralizer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutePolynomialOfMemCentralizer
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.CommMem

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_sq_eq_one : (thetaA E n) ^ 2 = 1 := by
  ext g : 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (thetaR (conjAd E) n (thetaR (conjAd E) n g)).val i j = g.val i j
  rw [thetaR_val]
  have h : (thetaR (conjAd E) n g)⁻¹ = thetaR (conjAd E) n g⁻¹ := (map_inv _ _).symm
  rw [h, thetaR_val, inv_inv]
  simp [GlobalTheory.CompanionTheory.OnlyStab.conjAd_invol]

theorem twNorm_ratGL (d : GL (Fin n) E) :
    twNorm (thetaA E n) 2 (ratGL E n d) = ratGL E n (nrm d) := by
  rw [nrm, map_mul, ← GlobalTheory.CompanionTheory.RatDisc.thetaA_ratGL]
  simp [twNorm]

theorem rm_algebraMap (a : E) :
    rm (algebraMap E (Matrix (Fin n) (Fin n) E) a) =
      algebraMap (Ad E) (Matrix (Fin n) (Fin n) (Ad E)) (algebraMap E (Ad E) a) := by
  ext i j
  by_cases h : i = j <;> simp [rm, Matrix.algebraMap_matrix_apply, h]

theorem comm_rm_aeval (x : Matrix (Fin n) (Fin n) (Ad E)) (γ : Matrix (Fin n) (Fin n) E)
    (hx : x * rm γ = rm γ * x) (f : E[X]) : x * rm (aeval γ f) = rm (aeval γ f) * x := by
  induction f using Polynomial.induction_on with
  | C a =>
    rw [aeval_C, rm_algebraMap]
    exact (Algebra.commutes _ x).symm
  | add p q hp hq =>
    rw [map_add (f := _), rm_add, mul_add, add_mul, hp, hq]
  | monomial m a h =>
    have e : aeval γ (C a * X ^ (m + 1)) = aeval γ (C a * X ^ m) * γ := by
      simp only [map_mul, map_pow, aeval_X, pow_succ, mul_assoc]
    rw [e, rm_mul, ← mul_assoc, h, mul_assoc, hx, mul_assoc]

theorem adCent_comm_rm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (t : GA E n), t ∈ adCent d → ∀ e : Matrix (Fin n) (Fin n) E, IsPol (nrm d).val e → t.val * rm e = rm e * t.val := by
  intro E _ _ _ n d t ht e he
  obtain ⟨f, rfl⟩ := he
  refine comm_rm_aeval _ _ ?_ f
  have h := twCent_commute_twNorm (thetaA E n) thetaA_sq_eq_one (ratGL E n d) ht
  rw [twNorm_ratGL] at h
  exact congrArg Units.val h

end GlobalTheory.CompanionTheory.TorusCh.CommMem

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutePolynomialOfMemCentralizerStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_polynomial_of_mem_centralizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (t : GA E n), t ∈ adCent d → ∀ e : Matrix (Fin n) (Fin n) E, IsPol (nrm d).val e → t.val * rm e = rm e * t.val := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm | exact GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm | (intros; apply GlobalTheory.CompanionTheory.TorusCh.CommMem.adCent_comm_rm <;> assumption)
end
end
