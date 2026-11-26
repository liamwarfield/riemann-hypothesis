module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemGoodPart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCellFiniteUnionLocalDoubleCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCellFiniteUnionLocalDoubleCosets
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.MirPatch.Decomp

open GlobalTheory.JSW GlobalTheory.SmGL Topology

theorem exists_distinct {ι X : Type} [Finite ι] (C : ι → Set X)
    (hC : ∀ i j x, x ∈ C i → x ∈ C j → C i = C j) :
    ∃ (N : ℕ) (f : Fin N → ι), (∀ i j x, x ∈ C (f i) → x ∈ C (f j) → i = j) ∧
      ∀ x, (∃ i, x ∈ C i) ↔ ∃ j, x ∈ C (f j) := by
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range C)
  have hf : ∀ j, C (e.symm j).2.choose = (e.symm j).1 := fun j => (e.symm j).2.choose_spec
  refine ⟨N, fun j => (e.symm j).2.choose, fun i j x hi hj => ?_, fun x => ⟨fun ⟨i, hi⟩ => ?_, fun ⟨j, hj⟩ => ⟨_, hj⟩⟩⟩
  · have h := hC _ _ x hi hj
    rw [hf, hf] at h
    exact e.symm.injective (Subtype.ext h)
  · refine ⟨e ⟨C i, i, rfl⟩, ?_⟩
    simp only
    rw [hf, Equiv.symm_apply_apply]
    exact hi

theorem exists_finite_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K A : Set G} (hK : IsCompact K) (hA : A ⊆ K) (V : Subgroup G) (hV : IsOpen (V : Set G)) :
    ∃ (ι : Type) (_ : Finite ι) (k : ι → G), (∀ i, k i ∈ A) ∧ ∀ a ∈ A, ∃ i, (k i)⁻¹ * a ∈ V := by
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hK (V := (V : Set G))
    (by rw [hV.interior_eq]; exact ⟨1, V.one_mem⟩)
  let ι := {g : G // g ∈ t ∧ ∃ a ∈ A, g * a ∈ V}
  haveI : Finite ι := Finite.of_injective (fun x : ι => (⟨x.1, x.2.1⟩ : t))
    (fun x y h => Subtype.ext (congrArg (fun z : t => (z : G)) h))
  refine ⟨ι, inferInstance, fun x => x.2.2.choose, fun x => x.2.2.choose_spec.1, fun a ha => ?_⟩
  obtain ⟨g, hg, hga⟩ := Set.mem_iUnion₂.1 (ht (hA ha))
  have hga' : g * a ∈ V := hga
  refine ⟨⟨g, hg, a, ha, hga'⟩, ?_⟩
  have hb := (⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose_spec.2
  have e : ((⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose)⁻¹ * a =
      (g * (⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose)⁻¹ * (g * a) := by group
  rw [e]
  exact mul_mem (inv_mem hb) hga'

theorem cell_eq_of_mem {F : Type} [NormedField F] {n : ℕ} {z g : GL (Fin n) F} {U : Subgroup (GL (Fin n) F)}
    (h : g ∈ Cut.cell z (U : Set (GL (Fin n) F))) :
    Cut.cell z (U : Set (GL (Fin n) F)) = Cut.cell g (U : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨u', hu', k', hk', rfl⟩
    exact ⟨u' * u⁻¹, mul_mem hu' (inv_mem hu), k⁻¹ * k', mul_mem (inv_mem hk) hk', by group⟩
  · rintro ⟨u', hu', k', hk', rfl⟩
    exact ⟨u' * u, mul_mem hu' hu, k * k', mul_mem hk hk', by group⟩

variable {E : Type} [Field E] [NumberField E]

theorem map_comp_eq {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := rfl

theorem af_eq {x y : Af E} (h : ∀ w, pLoc E w x = pLoc E w y) : x = y := FiniteAdeleRing.ext _ h


open Classical in
theorem pLoc_list_prod {n : ℕ} (u : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (l : List (HeightOneSpectrum (𝓞 E))) (hl : l.Nodup) (v : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (pLoc E v) (l.map fun w => locGL E n w (u w)).prod = if v ∈ l then u v else 1 := by
  classical
  induction l with
  | nil => simp
  | cons w l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih (List.nodup_cons.1 hl).2]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 hl).1, if_pos (by simp), mul_one]
    · rw [pLoc_locGL_of_ne h, one_mul]
      simp only [List.mem_cons, h, false_or]

theorem loc_mem_unipB {a : ℕ} {u : GA E a} (hu : u ∈ NA (E := E) (a := a)) (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) u ∈ unipB (w.adicCompletion E) (Fin a) :=
  (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j h => by
    show pLoc E w (pFin E _) = 0
    rw [hu.1 i j h, map_zero, map_zero], fun i => by
    show pLoc E w (pFin E _) = 1
    rw [hu.2 i, map_one, map_one]⟩

variable [_root_.NumberField.IsTotallyComplex E]

theorem finGL_mem_NA {a : ℕ} {v : GL (Fin a) (Af E)}
    (hv : ∀ w, GeneralLinearGroup.map (pLoc E w) v ∈ unipB (w.adicCompletion E) (Fin a)) : finGL E a v ∈ NA (E := E) (a := a) := by
  have e1 : ∀ i j, pInf E ((finGL E a v : Matrix (Fin a) (Fin a) (Ad E)) i j) =
      ((1 : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j := fun i j =>
    congrArg (fun g : GL (Fin a) (Cinf E) => (g : Matrix (Fin a) (Fin a) (Cinf E)) i j) (pInf_finGL (E := E) v)
  have e2 : ∀ i j, pFin E ((finGL E a v : Matrix (Fin a) (Fin a) (Ad E)) i j) = (v : Matrix (Fin a) (Fin a) (Af E)) i j :=
    fun i j => congrArg (fun g : GL (Fin a) (Af E) => (g : Matrix (Fin a) (Fin a) (Af E)) i j) (pFin_finGL (E := E) v)
  refine ⟨fun i j h => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
  · rw [e1, Units.val_one, Matrix.one_apply_ne (ne_of_gt h), map_zero]
  · rw [e2, map_zero]
    exact af_eq fun w => by rw [map_zero]; exact ((GlobalTheory.SmGL.mem_unipB _).1 (hv w)).1 i j h
  · rw [e1, Units.val_one, Matrix.one_apply_eq, map_one]
  · rw [e2, map_one]
    exact af_eq fun w => by rw [map_one]; exact ((GlobalTheory.SmGL.mem_unipB _).1 (hv w)).2 i

theorem mem_cell_iff {a : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a)
    {p : GA E a} (hp : p ∈ supS (E := E) (a := a) S) :
    p ∈ cell K q ↔ ∃ k ∈ K,
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) q * k) ∈
        unipB (w.adicCompletion E) (Fin a)) ∧
      ∀ w ∈ S, ∃ u ∈ unipB (w.adicCompletion E) (Fin a), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p =
        u * GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) q * k) := by
  constructor
  · rintro ⟨u, hu, k, hk, y, rfl⟩
    have hf : GeneralLinearGroup.map (pFin E) (u * q * finGL E a k * infGL E a y) =
        GeneralLinearGroup.map (pFin E) u * (GeneralLinearGroup.map (pFin E) q * k) := by
      rw [map_mul, map_mul, map_mul, pFin_finGL, pFin_infGL, mul_one, mul_assoc]
    refine ⟨k, hk, fun w hw => ?_, fun w _ => ⟨_, loc_mem_unipB hu w, ?_⟩⟩
    · have h1 := hp w hw
      rw [map_comp_eq, hf, map_mul] at h1
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem (loc_mem_unipB hu w)
    · rw [map_comp_eq, hf, map_mul, map_comp_eq]
  · rintro ⟨k, hk, hout, hin⟩
    set v := GeneralLinearGroup.map (pFin E) p * (GeneralLinearGroup.map (pFin E) q * k)⁻¹ with hv
    have hvN : ∀ w, GeneralLinearGroup.map (pLoc E w) v ∈ unipB (w.adicCompletion E) (Fin a) := by
      intro w
      rw [hv, map_mul, map_inv]
      by_cases hw : w ∈ S
      · obtain ⟨u, hu, he⟩ := hin w hw
        rw [← map_comp_eq, he, mul_inv_cancel_right]
        exact hu
      · rw [← map_comp_eq, hp w hw, one_mul]
        exact inv_mem (hout w hw)
    refine ⟨finGL E a v, finGL_mem_NA hvN, k, hk,
      (GeneralLinearGroup.map (pInf E) q)⁻¹ * GeneralLinearGroup.map (pInf E) p, ga_ext ?_ ?_⟩
    · simp only [map_mul, pInf_finGL, pInf_infGL, one_mul, mul_one, mul_inv_cancel_left]
    · simp only [map_mul, pFin_finGL, pFin_infGL, mul_one, hv]
      group

end GlobalTheory.JSW.MirPatch.Decomp

namespace GlobalTheory.JSW.MirPatch

open GlobalTheory.JSW GlobalTheory.SmGL Decomp

theorem cell_decomp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  intro E _ _ _ m S K hKo hKc q
  classical
  choose U hUo hUc hUK using fun w => LocEx.exists_compact_open (a := m + 1) w K hKo
  set qf := GeneralLinearGroup.map (pFin E) q with hqf
  let A : Set (GL (Fin (m + 1)) (Af E)) := {k | k ∈ K ∧ ∀ w ∉ S,
    GeneralLinearGroup.map (pLoc E w) (qf * k) ∈ unipB (w.adicCompletion E) (Fin (m + 1))}
  let V : Subgroup (GL (Fin (m + 1)) (Af E)) :=
    { carrier := {v | ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) v ∈ U w}
      mul_mem' := fun ha hb w hw => by rw [map_mul]; exact mul_mem (ha w hw) (hb w hw)
      one_mem' := fun w _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun ha w hw => by rw [map_inv]; exact inv_mem (ha w hw) }
  have hVo : IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) := by
    have e : (V : Set (GL (Fin (m + 1)) (Af E))) =
        ⋂ w ∈ S, GeneralLinearGroup.map (pLoc E w) ⁻¹' (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) := by
      ext v; simp [V]
    rw [e]
    exact isOpen_biInter_finset fun w _ => (hUo w).preimage (LocEx.continuous_map_pLoc w)
  obtain ⟨ι, _, k, hkA, hcov⟩ := exists_finite_reps (A := A) hKc (fun x hx => hx.1) V hVo
  let C : ι → Set (∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)) := fun i =>
    {x | ∀ w ∈ S, x w ∈ Cut.cell (GeneralLinearGroup.map (pLoc E w) (qf * k i))
      (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}
  have hC : ∀ i j x, x ∈ C i → x ∈ C j → C i = C j := by
    intro i j x hi hj
    ext y
    exact forall₂_congr fun w hw => by rw [cell_eq_of_mem (hi w hw), cell_eq_of_mem (hj w hw)]
  obtain ⟨N, f, huniq, hiff⟩ := exists_distinct C hC
  refine ⟨U, N, fun j w => GeneralLinearGroup.map (pLoc E w) (qf * k (f j)), fun w _ => ⟨hUc w, hUo w, hUK w⟩,
    fun p _ i j hi hj => huniq i j (fun w => GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p) hi hj,
    fun p hp => ?_⟩
  rw [mem_cell_iff S K q hp.1]
  refine Iff.trans ?_ (hiff (fun w => GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p))
  constructor
  · rintro ⟨k', hk', hout, hin⟩
    obtain ⟨i, hi⟩ := hcov k' ⟨hk', hout⟩
    refine ⟨i, fun w hw => ?_⟩
    obtain ⟨u, hu, he⟩ := hin w hw
    refine ⟨u, hu, GeneralLinearGroup.map (pLoc E w) ((k i)⁻¹ * k'), hi w hw, ?_⟩
    show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = _
    rw [he, mul_assoc u, ← map_mul, mul_assoc, mul_inv_cancel_left]
  · rintro ⟨i, hi⟩
    choose! uu huu cc hcc heq using hi
    let g : GL (Fin (m + 1)) (Af E) := (S.toList.map fun w => locGL E (m + 1) w (cc w)).prod
    have hgK : g ∈ K := by
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact hUK w _ (hcc w (Finset.mem_toList.1 hw))
    have hg : ∀ v, GeneralLinearGroup.map (pLoc E v) g = if v ∈ S then cc v else 1 := fun v => by
      rw [pLoc_list_prod cc _ S.nodup_toList v]
      simp only [Finset.mem_toList]
    refine ⟨k i * g, mul_mem (hkA i).1 hgK, fun w hw => ?_, fun w hw => ⟨uu w, huu w hw, ?_⟩⟩
    · rw [← mul_assoc, map_mul, hg w, if_neg hw, mul_one]
      exact (hkA i).2 w hw
    · refine (heq w hw).trans ?_
      rw [← mul_assoc qf, map_mul (GeneralLinearGroup.map (pLoc E w)) (qf * k i) g, hg w, if_pos hw, mul_assoc]

end GlobalTheory.JSW.MirPatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCellFiniteUnionLocalDoubleCosetsStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  first | (exact @GlobalTheory.JSW.MirPatch.cell_decomp) | (exact GlobalTheory.JSW.MirPatch.cell_decomp) | (intros; apply GlobalTheory.JSW.MirPatch.cell_decomp  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegersApproximatingRootOfUnityTwists
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationPowPrimePowSubGe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationPowPrimePowSubGe
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PowLim

theorem pow_prime_step {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ}
    (hp : p.Prime) (hvp : v (p : C) = 1) {a b : C} (ha : 0 ≤ v a) (hb : 0 ≤ v b) {t ε : ℝ}
    (hεt : ε ≤ t) (hε1 : ε ≤ 1) (ht : (t : WithTop ℝ) ≤ v (a - b)) :
    ((t + ε : ℝ) : WithTop ℝ) ≤ v (a ^ p - b ^ p) := by
  let R : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : 0 ≤ v a := ha
        have hb' : 0 ≤ v b := hb
        show 0 ≤ v (a * b)
        rw [v.map_mul]
        exact add_nonneg ha' hb'
      one_mem' := by
        show 0 ≤ v 1
        rw [v.map_one]
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (v.map_add _ _)
      zero_mem' := by
        show 0 ≤ v 0
        rw [v.map_zero]; exact le_top
      neg_mem' := fun {a} ha => by
        show 0 ≤ v (-a)
        rw [v.map_neg]; exact ha }
  have haR : a ∈ R := ha
  have hbR : b ∈ R := hb
  have hdR : a - b ∈ R := R.sub_mem haR hbR
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨a - b, hdR⟩ : R) ⟨b, hbR⟩
  have hr' := congrArg (fun z : R => (z : C)) hr
  simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast,
    sub_add_cancel] at hr'
  obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have e : a ^ p - b ^ p = (a - b) * (a - b) * (a - b) ^ k + (p : C) * (a - b) * (b * r) := by
    rw [hr']
    have : (a - b) ^ p = (a - b) * (a - b) * (a - b) ^ k := by rw [hk]; ring
    rw [this]; ring
  have h1 : (0 : WithTop ℝ) ≤ v ((a - b) ^ k) := R.pow_mem hdR k
  have h2 : (0 : WithTop ℝ) ≤ v (b * (r : C)) := R.mul_mem hbR r.2
  have hε : (ε : WithTop ℝ) ≤ v (a - b) := le_trans (WithTop.coe_le_coe.2 hεt) ht
  have hε1' : (ε : WithTop ℝ) ≤ 1 := by exact_mod_cast hε1
  rw [e]
  refine le_trans (le_min ?_ ?_) (v.map_add _ _)
  · rw [v.map_mul, v.map_mul, WithTop.coe_add]
    exact le_trans (add_le_add ht hε) (le_add_of_nonneg_right h1)
  · rw [v.map_mul, v.map_mul, WithTop.coe_add, hvp, add_comm (t : WithTop ℝ)]
    exact le_trans (add_le_add hε1' ht) (le_add_of_nonneg_right h2)

theorem pow_prime_pow_close : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ x y : C, IsIntV v x → IsIntV v y → 0 < v (x - y) → ∀ r : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
  intro C _ v p hp hvp x y hx hy hxy r
  have hx' : 0 ≤ v x := hx
  have hy' : 0 ≤ v y := hy
  obtain ⟨ε, hε0, hε1, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ (ε : WithTop ℝ) ≤ v (x - y) := by
    generalize v (x - y) = w at hxy
    induction w using WithTop.recTopCoe with
    | top => exact ⟨1, one_pos, le_rfl, le_top⟩
    | coe s =>
      have hs : 0 < s := by exact_mod_cast hxy
      exact ⟨min s 1, lt_min hs one_pos, min_le_right _ _, WithTop.coe_le_coe.2 (min_le_left _ _)⟩
  have hpow : ∀ (z : C) (n : ℕ), 0 ≤ v z → 0 ≤ v (z ^ n) := by
    intro z n hz
    rw [v.map_pow]
    exact nsmul_nonneg hz n
  have key : ∀ N : ℕ, ((((N : ℝ) + 1) * ε : ℝ) : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
    intro N
    induction N with
    | zero => simpa using hε
    | succ N ih =>
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have := pow_prime_step v hp hvp (hpow x (p ^ N) hx') (hpow y (p ^ N) hy')
        (t := ((N : ℝ) + 1) * ε) (ε := ε) (by nlinarith) hε1 ih
      rw [← pow_mul, ← pow_mul, ← pow_succ] at this
      refine le_trans (WithTop.coe_le_coe.2 (le_of_eq ?_)) this
      push_cast; ring
  obtain ⟨M, hM⟩ := exists_nat_gt (r / ε)
  refine ⟨M, fun N hN => le_trans (WithTop.coe_le_coe.2 ?_) (key N)⟩
  have h1 : (M : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_lt_iff₀ hε0] at hM
  nlinarith

end GlobalTheory.PowLim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationPowPrimePowSubGeStatement
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_pow_primePow_sub_ge : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ x y : C, IsIntV v x → IsIntV v y → 0 < v (x - y) → ∀ r : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
  first | exact @GlobalTheory.PowLim.pow_prime_pow_close | exact GlobalTheory.PowLim.pow_prime_pow_close | (intros; apply GlobalTheory.PowLim.pow_prime_pow_close <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegersApproximatingRootOfUnityTwists
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

theorem v_pow_sub_pow_lt_one {C : Type} [Field C] (v : Valuation C NNReal) {x y : C} (hx : v x ≤ 1) (hy : v y ≤ 1)
    (hxy : v (x - y) < 1) (n : ℕ) : v (x ^ n - y ^ n) < 1 := by
  rw [← geom_sum₂_mul x y n, map_mul]
  have hs : v (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one₀ (pow_le_one₀ zero_le hx) zero_le (pow_le_one₀ zero_le hy)
  calc v (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * v (x - y) ≤ 1 * v (x - y) :=
        mul_le_mul_of_nonneg_right hs zero_le
    _ = v (x - y) := one_mul _
    _ < 1 := hxy

private lemma exists_mem_sub_one_mem_of_maximal_ne {R : Type} [CommRing R] {P Q : Ideal R} (hP : P.IsMaximal)
    (hQ : Q.IsMaximal) (h : P ≠ Q) : ∃ a ∈ P, a - 1 ∈ Q := by
  have htop : P ⊔ Q = ⊤ := Ideal.IsMaximal.coprime_of_ne hP hQ h
  have h1 : (1 : R) ∈ P ⊔ Q := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  refine ⟨a, ha, ?_⟩
  have hb' : a - 1 = -b := by rw [← hab]; ring
  rw [hb']
  exact Q.neg_mem hb

theorem exists_sub_one_mem_and_mem {R ι : Type} [CommRing R] [Finite ι] (P : ι → Ideal R) (hP : ∀ i, (P i).IsMaximal)
    (t : ι) : ∃ e : R, e - 1 ∈ P t ∧ ∀ i, P i ≠ P t → e ∈ P i := by
  classical
  haveI := Fintype.ofFinite ι
  have hc : ∀ i, ∃ a : R, (P i ≠ P t → a ∈ P i) ∧ a - 1 ∈ P t := by
    intro i
    by_cases hi : P i = P t
    · exact ⟨1, fun h => absurd hi h, by simp⟩
    · obtain ⟨a, ha, ha1⟩ := exists_mem_sub_one_mem_of_maximal_ne (hP i) (hP t) hi
      exact ⟨a, fun _ => ha, ha1⟩
  choose a ha using hc
  refine ⟨∏ i, a i, ?_, ?_⟩
  · refine Ideal.Quotient.eq.1 ?_
    rw [map_prod, map_one]
    exact Finset.prod_eq_one fun i _ => by
      rw [← map_one (Ideal.Quotient.mk (P t))]
      exact Ideal.Quotient.eq.2 (ha i).2
  · intro i hi
    rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
    exact Ideal.mul_mem_right _ _ ((ha i).1 hi)

private lemma pow_pow_mul_eq_self_of_pow_sub_one_eq_one {C : Type} [Field C] {z : C} {h : ℕ} (p : ℕ) (hp : 0 < p)
    (hz : z ^ (p ^ h - 1) = 1) (M : ℕ) : z ^ p ^ (h * M) = z := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih]
    have hph : p ^ h = p ^ h - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)).symm
    rw [hph, pow_succ, hz, one_mul]

theorem exists_approx_root_twists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ (τ : E →+* ℂ) (h : ℕ), 0 < h → ∀ (lab : ZMod h → (E →+* ℂ)), (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) → ∀ z : X.C, z ^ (p ^ h - 1) = 1 → (∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1) → ∀ r : ℝ, ∃ a : 𝓞 E, (∀ s, (r : WithTop ℝ) ≤ vX_vp X (embX io X (lab s) a - z ^ p ^ s.val)) ∧ ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a) := by
  intro E _ _ _ H l c p _ T io X τ h hh lab hlab z hz ha₀ r
  classical
  obtain ⟨a₀, ha₀⟩ := ha₀
  have hp : p.Prime := Fact.out
  haveI : NeZero h := ⟨hh.ne'⟩
  obtain ⟨e, he1, he⟩ := exists_sub_one_mem_and_mem (fun σ : E →+* ℂ => primeBelow io X σ)
    (fun σ => (primeBelow_isMaximal_card E H l c p T io X σ).1) τ
  have hv1 : ∀ σ a, X.v (embX io X σ a) ≤ 1 := fun σ a => v_embX_le_one io X σ a
  have hvz : X.v z ≤ 1 := by
    have hn : p ^ h - 1 ≠ 0 := by
      have : 2 ≤ p ^ h := le_trans hp.two_le (Nat.le_self_pow hh.ne' p)
      omega
    have h1 : X.v z ^ (p ^ h - 1) ≤ 1 := by rw [← map_pow, hz, map_one]
    exact (pow_le_one_iff_of_nonneg zero_le hn).1 h1
  have hvzs : ∀ n : ℕ, X.v (z ^ n) ≤ 1 := fun n => by rw [map_pow]; exact pow_le_one₀ zero_le hvz
  have he1' : X.v (embX io X τ e - 1) < 1 := by
    have : X.v (embX io X τ (e - 1)) < 1 := he1
    rwa [map_sub, map_one] at this
  have hτb : X.v (embX io X τ (e * a₀) - z) < 1 := by
    have hsplit : embX io X τ (e * a₀) - z =
        (embX io X τ e - 1) * embX io X τ a₀ + (embX io X τ a₀ - z) := by rw [map_mul]; ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ ha₀
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le he1' (hv1 τ a₀)
  have hlabb : ∀ s : ZMod h, X.v (embX io X (lab s) (e * a₀) - z ^ p ^ s.val) < 1 := by
    intro s
    have hsplit : embX io X (lab s) (e * a₀) - z ^ p ^ s.val =
        (embX io X (lab s) (e * a₀) - embX io X τ (e * a₀) ^ p ^ s.val) +
          (embX io X τ (e * a₀) ^ p ^ s.val - z ^ p ^ s.val) := by ring
    rw [hsplit]
    exact Valuation.map_add_lt _ (hlab s (e * a₀))
      (v_pow_sub_pow_lt_one X.v (hv1 τ _) hvz hτb _)
  have hoth : ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → X.v (embX io X σ (e * a₀)) < 1 := by
    intro σ hσ
    have hmem : X.v (embX io X σ e) < 1 := he σ hσ
    rw [map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hmem (hv1 σ a₀)
  have hs : ∀ s : ZMod h, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤
      vX_vp X (embX io X (lab s) (e * a₀) ^ p ^ N - (z ^ p ^ s.val) ^ p ^ N) := by
    intro s
    exact GlobalTheory.T.exists_valuation_pow_primePow_sub_ge X.C (vX_vp X) p hp (vX_vp_p X) _ _ ((isIntV_iff X _).2 (hv1 _ _))
      ((isIntV_iff X _).2 (hvzs _)) ((vX_vp_pos_iff X _).2 (hlabb s)) r
  have hσ : ∀ σ : E →+* ℂ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → primeBelow io X σ ≠ primeBelow io X τ →
      (r : WithTop ℝ) ≤ vX_vp X (embX io X σ (e * a₀) ^ p ^ N) := by
    intro σ
    by_cases hne : primeBelow io X σ = primeBelow io X τ
    · exact ⟨0, fun _ _ h' => absurd hne h'⟩
    · have hlt : X.v (embX io X σ (e * a₀) - 0) < 1 := by rw [sub_zero]; exact hoth σ hne
      obtain ⟨N₀, hN₀⟩ := GlobalTheory.T.exists_valuation_pow_primePow_sub_ge X.C (vX_vp X) p hp (vX_vp_p X) _ 0 ((isIntV_iff X _).2 (hv1 _ _))
        ((isIntV_iff X _).2 (by simp)) ((vX_vp_pos_iff X _).2 hlt) r
      refine ⟨N₀, fun N hN _ => ?_⟩
      have := hN₀ N hN
      rwa [zero_pow (pow_ne_zero _ hp.ne_zero), sub_zero] at this
  choose Ns hNs using hs
  choose Nσ hNσ using hσ
  set M := (∑ s, Ns s) + ∑ σ, Nσ σ with hM
  have hMN : M ≤ h * M := Nat.le_mul_of_pos_left M hh
  refine ⟨(e * a₀) ^ p ^ (h * M), fun s => ?_, fun σ hne => ?_⟩
  · have hzN : (z ^ p ^ s.val) ^ p ^ (h * M) = z ^ p ^ s.val := by
      rw [← pow_mul, mul_comm, pow_mul, pow_pow_mul_eq_self_of_pow_sub_one_eq_one p hp.pos hz M]
    have hle : Ns s ≤ h * M :=
      le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s))
        (Nat.le_add_right _ _)) hMN
    have := hNs s (h * M) hle
    rwa [hzN, ← map_pow] at this
  · have hle : Nσ σ ≤ h * M :=
      le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ))
        (Nat.le_add_left _ _)) hMN
    have := hNσ σ (h * M) hle hne
    rwa [← map_pow] at this

end GlobalTheory.PrimePart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegersApproximatingRootOfUnityTwistsStatement
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integers_approximating_root_of_unity_twists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ (τ : E →+* ℂ) (h : ℕ), 0 < h → ∀ (lab : ZMod h → (E →+* ℂ)), (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) → ∀ z : X.C, z ^ (p ^ h - 1) = 1 → (∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1) → ∀ r : ℝ, ∃ a : 𝓞 E, (∀ s, (r : WithTop ℝ) ≤ vX_vp X (embX io X (lab s) a - z ^ p ^ s.val)) ∧ ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a) := by
  first | exact @GlobalTheory.PrimePart.exists_approx_root_twists | exact GlobalTheory.PrimePart.exists_approx_root_twists | (intros; apply GlobalTheory.PrimePart.exists_approx_root_twists <;> assumption)
end
end
