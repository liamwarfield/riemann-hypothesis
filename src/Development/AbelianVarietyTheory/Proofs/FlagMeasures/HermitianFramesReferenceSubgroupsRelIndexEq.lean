module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConst
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeTraceInitialSpanVolumeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeTraceInitialSpanVolumeEq
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TraceVol

def dfam {E V ι : Type} [CommRing E] [AddCommGroup V] [Module E V] (t : E) (g g' : ι → V) : ι ⊕ ι → V :=
  Sum.elim g fun b => t • (g' b - g b)

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

end

private theorem unitriangular_sum_castLE_eq {E V : Type} [CommRing E] [AddCommGroup V] [Module E V]
    {m J : ℕ} (hJ : J ≤ m) (b : Fin m → V) (s : Fin m → Fin m → E)
    (hs : ∀ i j, j < i → s i j = 0) (j : Fin J) :
    ∑ i, s i (Fin.castLE hJ j) • b i =
      ∑ i : Fin J, s (Fin.castLE hJ i) (Fin.castLE hJ j) • b (Fin.castLE hJ i) := by
  rw [show (∑ i : Fin J, s (Fin.castLE hJ i) (Fin.castLE hJ j) • b (Fin.castLE hJ i)) =
      ∑ i ∈ Finset.univ.map (Fin.castLEEmb hJ), s i (Fin.castLE hJ j) • b i from
    by rw [Finset.sum_map]; rfl]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  have hiJ : ¬ (i : ℕ) < J := fun h => hi (Finset.mem_map.2 ⟨⟨i, h⟩, Finset.mem_univ _, rfl⟩)
  rw [hs i _ (by rw [Fin.lt_def]; simp; omega), zero_smul]

private theorem span_image_frameScaledDifferenceFamily_eq_lemma_3 {E V : Type} [CommRing E] [AddCommGroup V]
    [Module E V] (O : Subring E) {m J : ℕ} (hJ : J ≤ m) (f f' : Fin m → V)
    (s s' : Matrix (Fin m) (Fin m) E) (hs : ∀ i j, j < i → s i j = 0)
    (hs' : ∀ i j, j < i → s' i j = 0) (θ : E) :
    Submodule.span O (_root_.GlobalTheory.HL.TraceVol.dfam θ (fun j => ∑ i, s i j • f i)
        (fun j => ∑ i, s' i j • f' i) ''
        {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J}) =
      Submodule.span O (Set.range fun j => ∑ i, Matrix.fromBlocks (s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))
        (-(θ • s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))) 0
        (θ • s'.submatrix (Fin.castLE hJ) (Fin.castLE hJ)) i j •
          Sum.elim (fun i => f (Fin.castLE hJ i)) (fun i => f' (Fin.castLE hJ i)) i) := by
  have hpt : ∀ a : Fin J ⊕ Fin J, (∑ i, Matrix.fromBlocks (s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))
        (-(θ • s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))) 0
        (θ • s'.submatrix (Fin.castLE hJ) (Fin.castLE hJ)) i a •
          Sum.elim (fun i => f (Fin.castLE hJ i)) (fun i => f' (Fin.castLE hJ i)) i) =
      _root_.GlobalTheory.HL.TraceVol.dfam θ (fun j => ∑ i, s i j • f i) (fun j => ∑ i, s' i j • f' i)
        (Sum.map (Fin.castLE hJ) (Fin.castLE hJ) a) := by
    intro a
    rcases a with j | j
    · rw [Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.submatrix_apply,
        Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
        _root_.GlobalTheory.HL.TraceVol.dfam, Sum.map_inl]
      rw [unitriangular_sum_castLE_eq hJ f s hs j]
    · rw [Fintype.sum_sum_type]
      simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.submatrix_apply,
        Sum.elim_inl, Sum.elim_inr, _root_.GlobalTheory.HL.TraceVol.dfam, Sum.map_inr]
      rw [unitriangular_sum_castLE_eq hJ f s hs j, unitriangular_sum_castLE_eq hJ f' s' hs' j]
      simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.submatrix_apply, neg_smul, smul_sub,
        Finset.smul_sum, smul_smul, smul_eq_mul, Finset.sum_neg_distrib]
      abel
  have hset : _root_.GlobalTheory.HL.TraceVol.dfam θ (fun j => ∑ i, s i j • f i)
        (fun j => ∑ i, s' i j • f' i) ''
        {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J} =
      Set.range fun a : Fin J ⊕ Fin J => _root_.GlobalTheory.HL.TraceVol.dfam θ (fun j => ∑ i, s i j • f i)
        (fun j => ∑ i, s' i j • f' i) (Sum.map (Fin.castLE hJ) (Fin.castLE hJ) a) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases a with i | i
      · exact ⟨Sum.inl ⟨i, ha⟩, rfl⟩
      · exact ⟨Sum.inr ⟨i, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      rcases a with i | i
      · exact ⟨Sum.inl (Fin.castLE hJ i), by simp, rfl⟩
      · exact ⟨Sum.inr (Fin.castLE hJ i), by simp, rfl⟩
  rw [hset]
  congr 2
  funext a
  exact (hpt a).symm

private theorem dfam_mem_lower_span {E V : Type} [CommRing E] [AddCommGroup V]
    [Module E V] {m : ℕ} (f f' g g' : Fin m → V) (t : E)
    (hg : ∀ j, g j - f j ∈ Submodule.span E (f '' {i | i < j}))
    (hg' : ∀ j, g' j - f' j ∈ Submodule.span E (f' '' {i | i < j})) (J : ℕ) (a : Fin m ⊕ Fin m)
    (ha : Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J) :
    _root_.GlobalTheory.HL.TraceVol.dfam t g g' a ∈
      Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J}) := by
  have hf : ∀ j : Fin m, (j : ℕ) < J → g j ∈ Submodule.span E (f '' {i | (i : ℕ) < J}) := by
    intro j hj
    have h1 : f j ∈ Submodule.span E (f '' {i | (i : ℕ) < J}) :=
      Submodule.subset_span ⟨j, hj, rfl⟩
    have hs : {i : Fin m | i < j} ⊆ {i : Fin m | (i : ℕ) < J} :=
      fun _ hi => lt_trans (Fin.lt_def.1 hi) hj
    have h2 : g j - f j ∈ Submodule.span E (f '' {i | (i : ℕ) < J}) :=
      Submodule.span_mono (Set.image_mono hs) (hg j)
    simpa using Submodule.add_mem _ h2 h1
  have hf' : ∀ j : Fin m, (j : ℕ) < J → g' j ∈ Submodule.span E (f' '' {i | (i : ℕ) < J}) := by
    intro j hj
    have h1 : f' j ∈ Submodule.span E (f' '' {i | (i : ℕ) < J}) :=
      Submodule.subset_span ⟨j, hj, rfl⟩
    have hs : {i : Fin m | i < j} ⊆ {i : Fin m | (i : ℕ) < J} :=
      fun _ hi => lt_trans (Fin.lt_def.1 hi) hj
    have h2 : g' j - f' j ∈ Submodule.span E (f' '' {i | (i : ℕ) < J}) :=
      Submodule.span_mono (Set.image_mono hs) (hg' j)
    simpa using Submodule.add_mem _ h2 h1
  rcases a with j | j
  · exact Submodule.mem_sup_left (hf j ha)
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_right (hf' j ha))
      (Submodule.mem_sup_left (hf j ha)))

private theorem coeff_eq_zero_of_mem_span_lower_indices {E V : Type} [CommRing E] [AddCommGroup V] [Module E V]
    {m : ℕ} (f f' : Fin m → V) (hB : LinearIndependent E (Sum.elim f f')) (J : Fin m) (α β : E)
    (h : α • f J + β • f' J ∈ Submodule.span E (f '' {i | i < J}) ⊔ Submodule.span E (f' '' {i | i < J})) :
    α = 0 ∧ β = 0 := by
  have hsup : Submodule.span E (f '' {i | i < J}) ⊔ Submodule.span E (f' '' {i | i < J}) =
      Submodule.span E (Sum.elim f f' '' (Sum.inl '' {i | i < J} ∪ Sum.inr '' {i | i < J})) := by
    rw [Set.image_union, Submodule.span_union, Set.image_image, Set.image_image]
    rfl
  have hpair : α • f J + β • f' J ∈
      Submodule.span E (Sum.elim f f' '' {Sum.inl J, Sum.inr J}) := by
    rw [Set.image_pair]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hdisj := hB.disjoint_span_image (s := {Sum.inl J, Sum.inr J})
    (t := Sum.inl '' {i | i < J} ∪ Sum.inr '' {i | i < J}) (by
      rw [Set.disjoint_left]
      intro a ha hb
      rcases ha with rfl | rfl <;> rcases hb with ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;>
        simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Set.mem_setOf_eq] at h hi <;>
        subst h <;> exact lt_irrefl _ hi)
  rw [hsup] at h
  have h0 : α • f J + β • f' J = 0 := (Submodule.disjoint_def.1 hdisj) _ hpair h
  have hli := hB.comp (fun b : Bool => if b then Sum.inl J else Sum.inr J) (by
    intro a b hab; cases a <;> cases b <;> simp_all)
  rw [Fintype.linearIndependent_iff] at hli
  have := hli (fun b => if b then α else β) (by simpa [add_comm] using h0)
  exact ⟨this true, this false⟩

private theorem mem_span_dfam_inf_iff {E V : Type} [CommRing E]
    [AddCommGroup V] [Module E V] (O : Subring E) {m : ℕ} (f f' g g' : Fin m → V)
    (hB : LinearIndependent E (Sum.elim f f')) (t : E) (ht : IsUnit t)
    (hg : ∀ j, g j - f j ∈ Submodule.span E (f '' {i | i < j}))
    (hg' : ∀ j, g' j - f' j ∈ Submodule.span E (f' '' {i | i < j})) (J : ℕ) (x : V) :
    (x ∈ Submodule.span O (Set.range (_root_.GlobalTheory.HL.TraceVol.dfam t g g')) ∧
      x ∈ Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J})) ↔
      x ∈ Submodule.span O (_root_.GlobalTheory.HL.TraceVol.dfam t g g' ''
        {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J}) := by
  have hle : ∀ J : ℕ, Submodule.span O (_root_.GlobalTheory.HL.TraceVol.dfam t g g' ''
      {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J}) ≤
      (Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔
        Submodule.span E (f' '' {i | (i : ℕ) < J})).restrictScalars O := by
    intro J
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact dfam_mem_lower_span f f' g g' t hg hg' J a ha
  refine ⟨fun ⟨hx, hY⟩ => ?_, fun hx => ⟨Submodule.span_mono (Set.image_subset_range _ _) hx, hle J hx⟩⟩
  suffices H : ∀ d J, m ≤ J + d → ∀ x, x ∈ Submodule.span O (Set.range (_root_.GlobalTheory.HL.TraceVol.dfam t g g')) →
      x ∈ Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J}) →
      x ∈ Submodule.span O (_root_.GlobalTheory.HL.TraceVol.dfam t g g' ''
        {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J}) from
    H m J (by omega) x hx hY
  intro d
  induction d with
  | zero =>
    intro J hJ x hx _
    have huniv : {a : Fin m ⊕ Fin m | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J} =
        Set.univ := Set.eq_univ_of_forall fun a => by
      rcases a with i | i <;> exact lt_of_lt_of_le i.isLt (by omega)
    rwa [huniv, Set.image_univ]
  | succ d ih =>
    intro J hJ x hx hY
    by_cases hJm : m ≤ J + d
    · exact ih J hJm x hx hY
    have hJlt : J < m := by omega
    set j0 : Fin m := ⟨J, hJlt⟩ with hj0
    have hYmono : Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J}) ≤
        Submodule.span E (f '' {i | (i : ℕ) < J + 1}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J + 1}) :=
      sup_le_sup (Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < J) => by
        show (i : ℕ) < J + 1; omega))
        (Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < J) => by
        show (i : ℕ) < J + 1; omega))
    have hx1 := ih (J + 1) (by omega) x hx (hYmono hY)
    have hset : _root_.GlobalTheory.HL.TraceVol.dfam t g g' ''
        {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J + 1} =
        {_root_.GlobalTheory.HL.TraceVol.dfam t g g' (Sum.inl j0), _root_.GlobalTheory.HL.TraceVol.dfam t g g' (Sum.inr j0)} ∪
        _root_.GlobalTheory.HL.TraceVol.dfam t g g' ''
          {a | Sum.elim (fun i : Fin m => (i : ℕ)) (fun i : Fin m => (i : ℕ)) a < J} := by
      rw [← Set.image_pair, ← Set.image_union]
      congr 1
      ext a
      rcases a with i | i <;>
        simp only [Set.mem_setOf_eq, Sum.elim_inl, Sum.elim_inr, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_or, or_false,
          Fin.ext_iff, hj0] <;> omega
    rw [hset, Submodule.span_union, Submodule.mem_sup] at hx1
    obtain ⟨z, hz, y, hy, rfl⟩ := hx1
    rw [Submodule.mem_span_pair] at hz
    obtain ⟨a, b, rfl⟩ := hz
    have hyY := hle J hy
    have hzY : a • _root_.GlobalTheory.HL.TraceVol.dfam t g g' (Sum.inl j0) +
        b • _root_.GlobalTheory.HL.TraceVol.dfam t g g' (Sum.inr j0) ∈
        Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J}) := by
      have := Submodule.sub_mem _ hY hyY
      simpa using this
    have hsets : ∀ h : Fin m → V, h '' {i | i < j0} = h '' {i | (i : ℕ) < J} := fun h => by
      congr 1
    have hrest : ((a : E) - b * t) • (g j0 - f j0) + ((b : E) * t) • (g' j0 - f' j0) ∈
        Submodule.span E (f '' {i | (i : ℕ) < J}) ⊔ Submodule.span E (f' '' {i | (i : ℕ) < J}) :=
      Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (by rw [← hsets]; exact hg j0)))
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (by rw [← hsets]; exact hg' j0)))
    have hmain : ((a : E) - b * t) • f j0 + ((b : E) * t) • f' j0 ∈
        Submodule.span (E) (f '' {i | i < j0}) ⊔ Submodule.span E (f' '' {i | i < j0}) := by
      rw [hsets, hsets]
      have := Submodule.sub_mem _ hzY hrest
      convert this using 1
      simp only [_root_.GlobalTheory.HL.TraceVol.dfam, Sum.elim_inl, Sum.elim_inr, Subring.smul_def, smul_sub,
        sub_smul, smul_smul]
      module
    obtain ⟨h1, h2⟩ := coeff_eq_zero_of_mem_span_lower_indices f f' hB j0 _ _ hmain
    have hb : b = 0 := Subtype.ext (by simpa using (ht.mul_left_eq_zero).1 h2)
    have ha : a = 0 := Subtype.ext (by simpa [hb] using h1)
    simpa [ha, hb] using hy

private theorem unitriangular_sum_sub_mem_span_lower {E V : Type} [CommRing E] [AddCommGroup V] [Module E V]
    {m : ℕ} (b : Fin m → V) (s : Fin m → Fin m → E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) (j : Fin m) :
    ∑ i, s i j • b i - b j ∈ Submodule.span E (b '' {i | i < j}) := by
  have key : ∀ i, s i j • b i = (if i < j then s i j • b i else 0) + (if i = j then b i else 0) := by
    intro i
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne]
    · simp [hs.2]
    · simp [hs.1 i j h, not_lt.2 h.le, h.ne']
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, add_sub_cancel_right]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, h, rfl⟩)
  · exact Submodule.zero_mem _

private theorem termFrameLattice_inf_initialSpan_eq_lemma {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k)
    (d : S.Datum) (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) (J : ℕ)
    (hJ : J ≤ r + 1) :
    ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) ∧
      ((∀ i j, j < i → s' i j = 0) ∧ ∀ i, s' i i = 1) ∧
      S.M d Λ ⊓ (S.spanTo S.f J ⊔
          S.spanTo S.f' J).restrictScalars L.O =
        Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks (s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))
          (-(algebraMap F E S.th⁻¹ • s.submatrix (Fin.castLE hJ) (Fin.castLE hJ))) 0
          (algebraMap F E S.th⁻¹ • s'.submatrix (Fin.castLE hJ) (Fin.castLE hJ)) i j •
            Sum.elim (fun i => S.f (Fin.castLE hJ i)) (fun i => S.f' (Fin.castLE hJ i)) i) := by
  obtain ⟨-, hW, -⟩ := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  unfold _root_.GlobalTheory.HL.Frames.IsTermW at hW
  obtain ⟨-, -, hp, hq, -⟩ := hW
  obtain ⟨hB, -, -, -, -, hth, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, hN⟩ := _root_.GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨-, hN'⟩ := _root_.GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨⟨s, hs, hsf⟩, -⟩ := hN _ hp
  obtain ⟨⟨s', hs', hsf'⟩, -⟩ := hN' _ hq
  refine ⟨s, s', hs, hs', ?_⟩
  have hθ : IsUnit (algebraMap F E S.th⁻¹) := (isUnit_iff_ne_zero.2 (inv_ne_zero hth)).map _
  have hM : S.M d Λ = Submodule.span L.O (Set.range
      (_root_.GlobalTheory.HL.TraceVol.dfam (algebraMap F E S.th⁻¹)
        (fun j => ∑ i, s i j • S.f i) (fun j => ∑ i, s' i j • S.f' i))) := by
    unfold _root_.GlobalTheory.HL.Frames.M _root_.GlobalTheory.HL.Frames.Mof
      _root_.GlobalTheory.HL.Frames.fr _root_.GlobalTheory.HL.Frames.fr' _root_.GlobalTheory.HL.TraceVol.dfam
    rw [Set.Sum.elim_range]
    congr 3
    · funext j; exact hsf j
    · funext j; rw [hsf j, hsf' j]
  rw [← span_image_frameScaledDifferenceFamily_eq_lemma_3 L.O hJ S.f S.f' s s' hs.1 hs'.1]
  ext x
  rw [Submodule.mem_inf, hM, Submodule.restrictScalars_mem]
  exact mem_span_dfam_inf_iff L.O S.f S.f' _ _ hB _ hθ
    (unitriangular_sum_sub_mem_span_lower S.f s hs) (unitriangular_sum_sub_mem_span_lower S.f' s' hs') J x

private theorem det_fromBlocks_unitriangular_eq_pow {E : Type} [CommRing E] {m : ℕ} (θ : E)
    (s s' : Matrix (Fin m) (Fin m) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1)
    (hs' : (∀ i j, j < i → s' i j = 0) ∧ ∀ i, s' i i = 1) :
    (Matrix.fromBlocks s (-(θ • s)) 0 (θ • s')).det = θ ^ m := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_of_upperTriangular (fun i j h => hs.1 i j h),
    Matrix.det_of_upperTriangular (fun i j h => hs'.1 i j h)]
  simp [hs.2, hs'.2]

private theorem linearIndependent_comb_of_isUnit_det {E V ι : Type} [CommRing E] [AddCommGroup V] [Module E V]
    [Fintype ι] [DecidableEq ι] (b : ι → V) (hb : LinearIndependent E b) (M : Matrix ι ι E)
    (hM : IsUnit M.det) : LinearIndependent E (fun j => ∑ i, M i j • b i) := by
  rw [Fintype.linearIndependent_iff] at hb ⊢
  intro c hc
  have h1 : ∀ i, M.mulVec c i = 0 := by
    refine hb _ ?_
    rw [← hc]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have h2 : M.mulVec c = 0 := funext h1
  have : c = M⁻¹.mulVec (M.mulVec c) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]
  intro i
  rw [this, h2, Matrix.mulVec_zero]
  rfl

private theorem sum_smul_sum_smul_eq_sum_mul_smul' {E V ι : Type} [CommRing E] [AddCommGroup V] [Module E V] [Fintype ι]
    (b : ι → V) (M N : Matrix ι ι E) (j : ι) :
    ∑ i, N i j • ∑ l, M l i • b l = ∑ l, (M * N) l j • b l := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]

private theorem relIndex_symm_of_blockFrameMatrix_lemma_2 {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (ϖ : (ValuativeRel.valuation F).integer)
    (hϖ : Irreducible ϖ) {N m : ℕ} (B : Fin m ⊕ Fin m → (Fin N → E))
    (hB : LinearIndependent E B) (θ : E) (hθ : IsUnit θ) (s s' u u' : Matrix (Fin m) (Fin m) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1)
    (hs' : (∀ i j, j < i → s' i j = 0) ∧ ∀ i, s' i i = 1)
    (hu : (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1)
    (hu' : (∀ i j, j < i → u' i j = 0) ∧ ∀ i, u' i i = 1) :
    (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks s (-(θ • s)) 0 (θ • s') i j • B i)).toAddSubgroup.relIndex
        (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks u (-(θ • u)) 0 (θ • u') i j • B i)).toAddSubgroup =
      (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks u (-(θ • u)) 0 (θ • u') i j • B i)).toAddSubgroup.relIndex
        (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks s (-(θ • s)) 0 (θ • s') i j • B i)).toAddSubgroup ∧
    (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks s (-(θ • s)) 0 (θ • s') i j • B i)).toAddSubgroup.relIndex
        (Submodule.span L.O (Set.range fun j => ∑ i, Matrix.fromBlocks u (-(θ • u)) 0 (θ • u') i j • B i)).toAddSubgroup ≠ 0 := by
  set T1 := Matrix.fromBlocks s (-(θ • s)) 0 (θ • s') with hT1
  set T2 := Matrix.fromBlocks u (-(θ • u)) 0 (θ • u') with hT2
  have hd1 : T1.det = θ ^ m := det_fromBlocks_unitriangular_eq_pow θ s s' hs hs'
  have hd2 : T2.det = θ ^ m := det_fromBlocks_unitriangular_eq_pow θ u u' hu hu'
  have hU1 : IsUnit T1.det := hd1 ▸ hθ.pow m
  let e : Fin (m + m) ≃ Fin m ⊕ Fin m := finSumFinEquiv.symm
  let A := T1⁻¹ * T2
  have hA : T1 * A = T2 := by rw [← mul_assoc, Matrix.mul_nonsing_inv T1 hU1, one_mul]
  have hdetA : A.det = 1 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hd1, hd2]
    exact Ring.inverse_mul_cancel _ (hθ.pow m)
  let b : Fin (m + m) → (Fin N → E) := fun j => ∑ i, T1 i (e j) • B i
  have hb : LinearIndependent E b :=
    (linearIndependent_comb_of_isUnit_det B hB T1 hU1).comp e e.injective
  let A' : Matrix (Fin (m + m)) (Fin (m + m)) E := Matrix.reindex e.symm e.symm A
  have hdetA' : A'.det = 1 := by rw [Matrix.det_reindex_self, hdetA]
  have hrange1 : Set.range b = Set.range fun j => ∑ i, T1 i j • B i := by
    have : b = (fun j => ∑ i, T1 i j • B i) ∘ e := rfl
    rw [this, Set.range_comp, e.range_eq_univ, Set.image_univ]
  have hrange2 : (Set.range fun j => ∑ i, A' i j • b i) = Set.range fun j => ∑ i, T2 i j • B i := by
    have : (fun j => ∑ i, A' i j • b i) = (fun j => ∑ i, T2 i j • B i) ∘ e := by
      funext j
      simp only [Function.comp_apply, A', b, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm]
      rw [Equiv.sum_comp e (fun i => A i (e j) • ∑ l, T1 l i • B l), sum_smul_sum_smul_eq_sum_mul_smul', hA]
    rw [this, Set.range_comp, e.range_eq_univ, Set.image_univ]
  have hcj : A'.det * L.cj A'.det = algebraMap F E 1 := by simp [hdetA']
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.HL.FrameIndex.relIndex_span_matrix L ϖ hϖ b hb A' 1 one_ne_zero hcj
    (Submodule.span L.O (Set.range b)) (Submodule.span L.O (Set.range fun j => ∑ i, A' i j • b i))
    rfl rfl
  rw [hrange1, hrange2] at h1 h2 h3
  have hv : _root_.GlobalTheory.HL.vE L ϖ (algebraMap F E 1) = 0 := by
    simpa using _root_.GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ 0 1
  rw [hv, zpow_zero, one_mul] at h3
  exact ⟨by exact_mod_cast h3.symm, h2⟩

theorem _root_.GlobalTheory.HL.TraceVol.trace_volume : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ d' Λ', S.IsTerm d' Λ' → ∀ (J : ℕ) (Yy : Submodule L.O S.V), J ≤ r + 1 → Yy = (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O → (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup = (S.M d' Λ' ⊓ Yy).toAddSubgroup.relIndex (S.M d Λ ⊓ Yy).toAddSubgroup ∧ (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT d' Λ' hT' J Yy hJ hYy
  subst hYy
  obtain ⟨s, s', hs, hs', h1⟩ := termFrameLattice_inf_initialSpan_eq_lemma L r k S d Λ hT J hJ
  obtain ⟨u, u', hu, hu', h2⟩ := termFrameLattice_inf_initialSpan_eq_lemma L r k S d' Λ' hT' J hJ
  obtain ⟨hB, -, -, -, -, hth, -⟩ := _root_.GlobalTheory.FrameBasic.main L r k S
  have hθ : IsUnit (algebraMap F E S.th⁻¹) := (isUnit_iff_ne_zero.2 (inv_ne_zero hth)).map _
  have hBJ : LinearIndependent E (Sum.elim (fun i : Fin J => S.f (Fin.castLE hJ i))
      (fun i => S.f' (Fin.castLE hJ i))) := by
    have := hB.comp (Sum.map (Fin.castLE hJ) (Fin.castLE hJ))
      (Sum.map_injective.2 ⟨Fin.castLE_injective hJ, Fin.castLE_injective hJ⟩)
    rwa [Sum.elim_comp_map] at this
  have htri : ∀ t : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → t i j = 0) ∧ ∀ i, t i i = 1) →
      ((∀ i j, j < i → t.submatrix (Fin.castLE hJ) (Fin.castLE hJ) i j = 0) ∧
        ∀ i, t.submatrix (Fin.castLE hJ) (Fin.castLE hJ) i i = 1) := fun t ht =>
    ⟨fun i j hij => ht.1 _ _ ((Fin.castLE_lt_castLE_iff hJ).2 hij), fun i => ht.2 _⟩
  rw [h1, h2]
  exact relIndex_symm_of_blockFrameMatrix_lemma_2 L S.ϖ S.ϖ_irr _ hBJ _ hθ _ _ _ _
    (htri s hs) (htri s' hs') (htri u hu) (htri u' hu')

end GlobalTheory.HL.TraceVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeTraceInitialSpanVolumeEqStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameLattice_trace_initialSpan_volume_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ d' Λ', S.IsTerm d' Λ' → ∀ (J : ℕ) (Yy : Submodule L.O S.V), J ≤ r + 1 → Yy = (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O → (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup = (S.M d' Λ' ⊓ Yy).toAddSubgroup.relIndex (S.M d Λ ⊓ Yy).toAddSubgroup ∧ (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup ≠ 0 := by
  first | exact @GlobalTheory.HL.TraceVol.trace_volume | exact GlobalTheory.HL.TraceVol.trace_volume | (intros; apply GlobalTheory.HL.TraceVol.trace_volume <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeTraceOrthogonalVolumeRat
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeTraceOrthogonalVolumeRat
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.VolPerp

open GlobalTheory.HL.DualInter

theorem relIndex_split {G : Type} [AddCommGroup G] {M A : AddSubgroup G} (Z : AddSubgroup G)
    (h : M ≤ A) : M.relIndex A = (M ⊓ Z).relIndex (A ⊓ Z) * (M ⊔ Z).relIndex (A ⊔ Z) := by
  have h1 : (M ⊔ Z) ⊓ A = M ⊔ (Z ⊓ A) := sup_inf_assoc_of_le Z h
  have h2 : M ≤ (M ⊔ Z) ⊓ A := le_inf le_sup_left h
  rw [← AddSubgroup.relIndex_mul_relIndex M _ A h2 inf_le_right]
  congr 1
  · rw [h1, AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right M, inf_comm Z A,
      ← inf_assoc, inf_eq_left.2 h]
  · rw [AddSubgroup.inf_relIndex_right, ← AddSubgroup.relIndex_sup_right A (M ⊔ Z),
      ← sup_assoc, sup_eq_left.2 h]

theorem relIndex_split' {G : Type} [AddCommGroup G] (A B Z : AddSubgroup G) :
    B.relIndex A = (B ⊓ Z).relIndex (A ⊓ Z) *
      (((A ⊓ B) ⊔ Z).relIndex ((A ⊔ Z) ⊓ (B ⊔ Z)) * (B ⊔ Z).relIndex (A ⊔ Z)) := by
  rw [← AddSubgroup.inf_relIndex_left, relIndex_split Z inf_le_left]
  congr 1
  · rw [inf_inf_distrib_right, AddSubgroup.inf_relIndex_left]
  · rw [← AddSubgroup.inf_relIndex_left (A ⊔ Z) (B ⊔ Z), AddSubgroup.relIndex_mul_relIndex _ _ _
      (le_inf (sup_le_sup_right inf_le_left _) (sup_le_sup_right inf_le_right _)) inf_le_left]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem expand {m : ℕ} {b c : Fin m → Fin n → E}
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0) {v : Fin n → E}
    (hv : v ∈ Submodule.span E (Set.range b)) : v = ∑ j, hf L Hm v (c j) • b j := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
  simp [sum_l, smul_l, hbc]

theorem inter_eq {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {b c : Fin m → Fin n → E} (hb : ∀ i, b i ∈ Λ) (hc : ∀ i, c i ∈ Λ)
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0) :
    Λ ⊓ (Submodule.span E (Set.range b)).restrictScalars L.O
      = Submodule.span L.O (Set.range b) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro v ⟨hv, hvY⟩
    rw [expand hbc hvY]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem (Submodule.span L.O (Set.range b))
      ⟨_, (hΛ.2 _).2 (hc j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    exact ⟨hb j, Submodule.subset_span ⟨j, rfl⟩⟩

theorem map_eq (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {b c : Fin m → Fin n → E} (hb : ∀ i, b i ∈ Λ) (hc : ∀ i, c i ∈ Λ)
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0)
    (φ : (Fin n → E) →ₗ[E] (Fin m → E)) (w : Fin m → Fin m → E)
    (hφ : ∀ v, φ v = ∑ j, hf L Hm v (b j) • w j) :
    Λ.toAddSubgroup.map φ.toAddMonoidHom = (Submodule.span L.O (Set.range w)).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change φ v ∈ Submodule.span L.O (Set.range w)
    rw [hφ]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem (Submodule.span L.O (Set.range w))
      ⟨_, (hΛ.2 _).2 (hb j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
  · intro hx
    have : Submodule.span L.O (Set.range w) ≤ Λ.map (φ.restrictScalars L.O) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine ⟨c j, hc j, ?_⟩
      have : ∀ i, hf L Hm (c j) (b i) = if i = j then 1 else 0 := fun i => by
        rw [← cj_hf h, hbc]; split_ifs <;> simp
      simp [hφ, this]
    exact this hx

theorem key (h : IsHermND L Hm) {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    (hΛ' : IsSD L Hm Λ') {m : ℕ} (y : Fin m → Fin n → E) (hy : LinearIndependent E y)
    {Y Z : Submodule L.O (Fin n → E)}
    (hY : Y = (Submodule.span E (Set.range y)).restrictScalars L.O)
    (hZ : Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O) :
    (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧
    (Λ.toAddSubgroup ⊔ Z.toAddSubgroup).relIndex (Λ'.toAddSubgroup ⊔ Z.toAddSubgroup) *
      (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup =
    (Λ'.toAddSubgroup ⊔ Z.toAddSubgroup).relIndex (Λ.toAddSubgroup ⊔ Z.toAddSubgroup) *
      (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have := L.free
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
  obtain ⟨b, c, hb, hc, hs, hbc⟩ := exists_dual_family h hΛ m y hy
  obtain ⟨b', c', hb', hc', hs', hbc'⟩ := exists_dual_family h hΛ' m y hy
  have hQ : Λ ⊓ Y = Submodule.span L.O (Set.range b) := by
    rw [hY, ← hs]; exact inter_eq hΛ hb hc hbc
  have hQ' : Λ' ⊓ Y = Submodule.span L.O (Set.range b') := by
    rw [hY, ← hs']; exact inter_eq hΛ' hb' hc' hbc'
  let A : Matrix (Fin m) (Fin m) E := fun i j => hf L Hm (b' j) (c i)
  let B : Matrix (Fin m) (Fin m) E := fun i j => hf L Hm (b j) (c' i)
  have hA : ∀ j, b' j = ∑ i, A i j • b i := fun j =>
    expand hbc (by rw [hs, ← hs']; exact Submodule.subset_span ⟨j, rfl⟩)
  have hBA : B * A = 1 := by
    ext k j
    have := hbc' j k
    rw [hA j, sum_l] at this
    simp only [smul_l] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← if_congr eq_comm rfl rfl, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hu : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hBA
  obtain ⟨d, hd⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (hu.mul (hu.map L.cj)).ne_zero (by rw [← hd, map_zero])
  have hli : LinearIndependent E b := by
    refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
    have := congrArg (fun v => hf L Hm v (c k)) hg
    simp only [sum_l, smul_l, hbc] at this
    simpa [hf] using this
  obtain ⟨-, p2, p3⟩ := GlobalTheory.T.relIndex_span_lattice_matrix_det_norm L ϖ hϖ b hli A d hd0 hd.symm (Λ ⊓ Y) (Λ' ⊓ Y) hQ
    (by rw [hQ']; congr 2; exact funext hA)
  have hdet : (cT L A).det = L.cj A.det := by
    have : cT L A = ((L.cj : E →+* E).mapMatrix A).transpose := rfl
    rw [this, Matrix.det_transpose, ← RingHom.map_det]; rfl
  obtain ⟨-, -, r3⟩ := GlobalTheory.T.relIndex_span_lattice_matrix_det_norm L ϖ hϖ (Pi.basisFun E (Fin m))
    (Pi.basisFun E (Fin m)).linearIndependent (cT L A) d hd0
    (by rw [hdet, L.cj_cj, mul_comm, hd]) _ _ rfl rfl
  let φ : (Fin n → E) →ₗ[E] (Fin m → E) := LinearMap.pi fun j => hfL L Hm (b' j)
  have hφ : ∀ v k, φ v k = hf L Hm v (b' k) := fun v k => rfl
  have m1 := map_eq h hΛ' hb' hc' hbc' φ (Pi.basisFun E (Fin m))
    (fun v => by ext k; simp [hφ, Pi.single_apply])
  have m2 := map_eq h hΛ hb hc hbc φ (fun j => ∑ i, cT L A i j • Pi.basisFun E (Fin m) i)
    (fun v => by
      ext k
      rw [hφ, hA k]
      simp [sum_r, smul_r, cT, Pi.single_apply, mul_comm])
  rw [← m1, ← m2, AddSubgroup.relIndex_map_map, AddSubgroup.relIndex_map_map] at r3
  have hker : φ.toAddMonoidHom.ker = Z.toAddSubgroup := by
    ext x
    rw [hZ, ← hs']
    constructor
    · intro hx v hv
      rw [← cj_hf h, hf_eq_zero_of_span (S := Set.range b') ?_ v hv, map_zero]
      rintro _ ⟨j, rfl⟩
      have : hf L Hm x (b' j) = 0 := congrFun hx j
      rw [← cj_hf h, this, map_zero]
    · intro hx
      funext j
      exact hx _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [hker] at r3
  refine ⟨p2, ?_⟩
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [p3, r3]
  ring

theorem relIndex_symm (h : IsHermND L Hm) {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    (hΛ' : IsSD L Hm Λ') : Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup ≠ 0 ∧
    Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup = Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup := by
  have hY : (⊤ : Submodule L.O (Fin n → E))
      = (Submodule.span E (Set.range (Pi.basisFun E (Fin n)))).restrictScalars L.O := by
    rw [Module.Basis.span_eq]; rfl
  have hZ : (⊥ : Submodule L.O (Fin n → E))
      = (perp L Hm (Submodule.span E (Set.range (Pi.basisFun E (Fin n))))).restrictScalars L.O := by
    rw [Module.Basis.span_eq, eq_comm, eq_bot_iff]
    intro x hx
    refine eq_zero_of_hf h fun v => ?_
    rw [← cj_hf h, hx v trivial, map_zero]
  obtain ⟨k1, k2⟩ := key h hΛ hΛ' _ (Pi.basisFun E (Fin n)).linearIndependent hY hZ
  simp only [inf_top_eq, Submodule.bot_toAddSubgroup, sup_bot_eq] at k1 k2
  exact ⟨k1, Nat.mul_self_inj.1 k2⟩

theorem vol_perp : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Y Z : Submodule L.O (Fin n → E), Y = (Submodule.span E (Set.range y)).restrictScalars L.O → Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O → (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup * (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup = (Λ' ⊓ Z).toAddSubgroup.relIndex (Λ ⊓ Z).toAddSubgroup * (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup := by
  intro F _ _ _ _ _ E _ _ _ L n Hm h Λ Λ' hΛ hΛ' m y hy Y Z hY hZ
  obtain ⟨k1, k2⟩ := key h hΛ hΛ' y hy hY hZ
  obtain ⟨a1, a2⟩ := relIndex_symm h hΛ hΛ'
  have s1 := relIndex_split' Λ.toAddSubgroup Λ'.toAddSubgroup Z.toAddSubgroup
  have s2 := relIndex_split' Λ'.toAddSubgroup Λ.toAddSubgroup Z.toAddSubgroup
  rw [inf_comm Λ'.toAddSubgroup Λ.toAddSubgroup, inf_comm (Λ'.toAddSubgroup ⊔ _)] at s2
  have e1 : (Λ ⊓ Z).toAddSubgroup = Λ.toAddSubgroup ⊓ Z.toAddSubgroup := rfl
  have e2 : (Λ' ⊓ Z).toAddSubgroup = Λ'.toAddSubgroup ⊓ Z.toAddSubgroup := rfl
  rw [e1, e2]
  have b1 := a2 ▸ a1
  rw [s1] at b1
  rw [s1, s2] at a2
  rw [s2] at a1
  simp only [ne_eq, mul_eq_zero, not_or] at a1 b1
  refine ⟨a1.1, k1, ?_⟩
  rw [mul_left_comm, mul_left_comm _ (AddSubgroup.relIndex (_ ⊓ _ ⊔ _) _)] at a2
  have a3 := mul_left_cancel₀ a1.2.1 a2
  refine mul_right_cancel₀ b1.2.2 ?_
  rw [mul_assoc, mul_comm (AddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup _), ← k2, ← mul_assoc, a3]
  ring

end GlobalTheory.HL.VolPerp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeTraceOrthogonalVolumeRatStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualHermitianLattice_trace_orthogonal_volume_ratio : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Y Z : Submodule L.O (Fin n → E), Y = (Submodule.span E (Set.range y)).restrictScalars L.O → Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O → (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup * (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup = (Λ' ⊓ Z).toAddSubgroup.relIndex (Λ ⊓ Z).toAddSubgroup * (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup := by
  first | exact @GlobalTheory.HL.VolPerp.vol_perp | exact GlobalTheory.HL.VolPerp.vol_perp | (intros; apply GlobalTheory.HL.VolPerp.vol_perp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConst
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FamilyVol

theorem relIndex_symm_of_sub {G : Type*} [AddGroup G] {A A' B B' : AddSubgroup G} {β : ℕ} (hβ : β ≠ 0)
    (hA : B ≤ A) (hA' : B' ≤ A') (h : B.relIndex A = β) (h' : B'.relIndex A' = β)
    (hB : B.relIndex B' = B'.relIndex B) (hB0 : B.relIndex B' ≠ 0) :
    A.relIndex A' = A'.relIndex A := by
  have e1 : (B ⊓ B').relIndex A = B'.relIndex B * β := by
    rw [← h, ← AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B A inf_le_left hA,
      AddSubgroup.inf_relIndex_left]
  have e2 : (B ⊓ B').relIndex A' = B.relIndex B' * β := by
    rw [← h', ← AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B' A' inf_le_right hA',
      AddSubgroup.inf_relIndex_right]
  have hle : B ⊓ B' ≤ A ⊓ A' := inf_le_inf hA hA'
  have e3 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') (A ⊓ A') A hle inf_le_left
  have e4 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') (A ⊓ A') A' hle inf_le_right
  rw [AddSubgroup.inf_relIndex_left] at e3
  rw [AddSubgroup.inf_relIndex_right] at e4
  have hne : (B ⊓ B').relIndex (A ⊓ A') ≠ 0 := by
    intro h0
    rw [h0, zero_mul, e2] at e4
    exact mul_ne_zero hB0 hβ e4.symm
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
  rw [e3, e4, e1, e2, hB]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem resQ_ne_zero (ϖ : 𝒪[F]) (h : Irreducible ϖ) : resQ ϖ ≠ 0 := by
  have e : Ideal.span {ϖ} = IsLocalRing.maximalIdeal 𝒪[F] := h.maximalIdeal_eq.symm
  unfold resQ
  rw [e]
  have : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

variable [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem exists_basis (S : Frames L r k) (J : ℕ) :
    ∃ (m : ℕ) (y : Fin m → S.V), LinearIndependent E y ∧
      Submodule.span E (Set.range y) = S.spanTo S.f J ⊔ S.spanTo S.f' J := by
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  let I := {i : Fin (r + 1) // (i : ℕ) < J}
  let φ : I ⊕ I → Fin (r + 1) ⊕ Fin (r + 1) := Sum.map Subtype.val Subtype.val
  have hφ : Function.Injective φ := Subtype.val_injective.sumMap Subtype.val_injective
  let e := (Fintype.equivFin (I ⊕ I)).symm
  refine ⟨_, (Sum.elim S.f S.f' ∘ φ) ∘ e, (hli.comp φ hφ).comp e e.injective, ?_⟩
  rw [e.surjective.range_comp, Frames.spanTo, Frames.spanTo, ← Submodule.span_union]
  congr 1
  ext v
  constructor
  · rintro ⟨i | i, rfl⟩
    · exact Or.inl ⟨i.1, i.2, rfl⟩
    · exact Or.inr ⟨i.1, i.2, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
    · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩

theorem spanTo_mono (S : Frames L r k) (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) :
    S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem relIndex_trace (S : Frames L r k) (J : ℕ) (hJ : J ≤ r + 1) (d : S.Datum) (Λ : Submodule L.O S.V)
    (hT : S.IsTerm d Λ) (hl : ∀ y ∈ S.sat Λ, S.levC d Λ y ≤ J) :
    (S.M d Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup = S.be d Λ := by
  have hM : S.M d Λ ≤ S.sat Λ := (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1
  have hlev := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.2.2
  set Y := (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O with hY
  have h1 : (S.sat Λ).toAddSubgroup = (Λ ⊓ Y).toAddSubgroup ⊔ (S.M d Λ).toAddSubgroup := by
    apply le_antisymm
    · intro y hy
      obtain ⟨y₁, hy₁, hm⟩ := (hlev y hy J).1 (hl y hy)
      have hy₁Λ : y₁ ∈ Λ := by
        have := Λ.sub_mem hy.1 (hM hm).1
        simpa using this
      have : y = y₁ + (y - y₁) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup (S := (Λ ⊓ Y).toAddSubgroup) ⟨hy₁Λ, hy₁⟩ hm
    · refine sup_le ?_ hM
      intro y hy
      exact ⟨hy.1, sup_le_sup (spanTo_mono S S.f hJ) (spanTo_mono S S.f' hJ) hy.2⟩
  have h2 : (S.M d Λ ⊓ Y).toAddSubgroup = (S.M d Λ).toAddSubgroup ⊓ (Λ ⊓ Y).toAddSubgroup := by
    ext y
    exact ⟨fun h => ⟨h.1, (hM h.1).1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [h2, AddSubgroup.inf_relIndex_right, Frames.be, h1, AddSubgroup.relIndex_sup_right]

theorem family_vol : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → ∀ Yy : Submodule L.O S.V, (Yy = (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O ∨ Yy = (perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))).restrictScalars L.O) → (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup = (Λ' ⊓ Yy).toAddSubgroup.relIndex (Λ ⊓ Yy).toAddSubgroup ∧ (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup ≠ 0 ∧ (S.M d Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup.relIndex (Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup = β := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF Λ' hT' hF' Yy hYy
  have hJ : (j : ℕ) + 1 ≤ r + 1 := by have := j.2; omega
  have b1 := relIndex_trace S (j + 1) hJ d Λ hT hF.2.2.1
  have b2 := relIndex_trace S (j + 1) hJ d Λ' hT' hF'.2.2.1
  have hβ : β ≠ 0 := by
    obtain ⟨i, -, hi⟩ := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.1
    rw [← hF.2.1, hi]
    exact pow_ne_zero _ (resQ_ne_zero _ S.ϖ_irr)
  rw [hF.2.1] at b1
  rw [hF'.2.1] at b2
  obtain ⟨hS, -, hM, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨hS', -, hM', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ' hT'
  obtain ⟨v1, v2⟩ := GlobalTheory.T.frameLattice_trace_initialSpan_volume_eq L r k S d Λ hT d Λ' hT' (j + 1) _ hJ rfl
  have hY := relIndex_symm_of_sub hβ
    (Submodule.toAddSubgroup_mono (inf_le_inf_right _ (hM.trans inf_le_left)))
    (Submodule.toAddSubgroup_mono (inf_le_inf_right _ (hM'.trans inf_le_left))) b1 b2 v1 v2
  obtain ⟨m, y, hy, hsp⟩ := exists_basis S (j + 1)
  obtain ⟨p1, p2, p3⟩ := GlobalTheory.T.selfDualHermitianLattice_trace_orthogonal_volume_ratio L S.Hm S.herm Λ Λ' hS hS' m y hy _ _ rfl rfl
  rw [hsp] at p1 p2 p3
  rcases hYy with rfl | rfl
  · exact ⟨hY, p2, b1⟩
  · refine ⟨?_, p1, b1⟩
    rw [← hY] at p3
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero p2) p3

end GlobalTheory.HL.FamilyVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConstStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFamily_trace_volume_const : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → ∀ Yy : Submodule L.O S.V, (Yy = (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O ∨ Yy = (perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))).restrictScalars L.O) → (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup = (Λ' ⊓ Yy).toAddSubgroup.relIndex (Λ ⊓ Yy).toAddSubgroup ∧ (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup ≠ 0 ∧ (S.M d Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup.relIndex (Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup = β := by
  first | exact @GlobalTheory.HL.FamilyVol.family_vol | exact GlobalTheory.HL.FamilyVol.family_vol | (intros; apply GlobalTheory.HL.FamilyVol.family_vol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesReferenceSubgroupsRelIndexEq
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.RefVol

theorem relIndex_inf_of_le {G : Type*} [AddGroup G] (P A K : AddSubgroup G) (h : K ≤ P) :
    (P ⊓ A).relIndex K = A.relIndex K := by
  rw [← AddSubgroup.inf_relIndex_right (P ⊓ A) K, ← AddSubgroup.inf_relIndex_right A K]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf]
  exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨h hx.2, hx.1⟩, hx.2⟩⟩

theorem relIndex_prod {G H : Type*} [AddGroup G] [AddGroup H] (A A' : AddSubgroup G)
    (B B' : AddSubgroup H) :
    (A.prod B).relIndex (A'.prod B') = A.relIndex A' * B.relIndex B' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective _ (f := (AddSubgroup.prodEquiv A' B').toAddMonoidHom)
      (AddSubgroup.prodEquiv A' B').surjective]
  congr 1

theorem relIndex_inf_comap {G H : Type*} [AddGroup G] [AddGroup H] (φ : G →+ H) (P : AddSubgroup G)
    (A B : AddSubgroup H) :
    (P ⊓ A.comap φ).relIndex (P ⊓ B.comap φ) = (A ⊓ P.map φ).relIndex (B ⊓ P.map φ) := by
  rw [relIndex_inf_of_le _ _ _ inf_le_left, AddSubgroup.relIndex_comap, inf_comm A,
    relIndex_inf_of_le _ _ _ inf_le_right]
  congr 1
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨h2, x, h1, rfl⟩
  · rintro ⟨h2, x, h1, rfl⟩
    exact ⟨x, ⟨h1, h2⟩, rfl⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

noncomputable def sumDiv : S.V × S.V →+ S.V :=
  (algebraMap F E S.th⁻¹ • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom.comp
    (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

theorem sumDiv_apply (p : S.V × S.V) : sumDiv S p = algebraMap F E S.th⁻¹ • (p.1 + p.2) := rfl

theorem th_mul : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ (th_ne S), map_one]

theorem refB_eq (J : ℕ) (Λ : Submodule L.O S.V) :
    S.refB J Λ = ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
      Λ.toAddSubgroup.comap (sumDiv S) := by
  unfold Frames.refB
  congr 1
  ext p
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, sumDiv_apply]
  constructor
  · rintro ⟨y, hy, h⟩
    have h' : algebraMap F E S.th • y = p.1 + p.2 := h
    rw [← h', smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    change algebraMap F E S.th • (algebraMap F E S.th⁻¹ • (p.1 + p.2)) = p.1 + p.2
    rw [smul_smul, th_mul, one_smul]

theorem map_sumDiv (X X' : Submodule E S.V) :
    (X.toAddSubgroup.prod X'.toAddSubgroup).map (sumDiv S) = (X ⊔ X').toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup, sumDiv_apply]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.add_mem_sup h1 h2)
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    refine ⟨(algebraMap F E S.th • a, algebraMap F E S.th • b),
      ⟨X.smul_mem _ ha, X'.smul_mem _ hb⟩, ?_⟩
    rw [← smul_add, smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]

theorem refB_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refB J Λ).relIndex (S.refB J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup := by
  rw [refB_eq, refB_eq, relIndex_inf_comap, map_sumDiv]
  rfl

theorem refA_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refA J Λ).relIndex (S.refA J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup *
      (Λ ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup := by
  unfold Frames.refA
  rw [relIndex_prod, relIndex_prod, AddSubgroup.relIndex_self, mul_one, refB_relIndex]
  rfl

end GlobalTheory.RefVol

theorem GlobalTheory.RefVol.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ h1 h2 Λ' h3 h4
  have a := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inl rfl)
  have b := GlobalTheory.T.hermitianFamily_trace_volume_const L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inr rfl)
  rw [GlobalTheory.RefVol.refA_relIndex, GlobalTheory.RefVol.refA_relIndex]
  exact ⟨by rw [a.1, b.1], mul_ne_zero a.2.1 b.2.1⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesReferenceSubgroupsRelIndexEqStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_reference_subgroups_relIndex_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  first | exact @GlobalTheory.RefVol.main | exact GlobalTheory.RefVol.main | (intros; apply GlobalTheory.RefVol.main <;> assumption)
end
