module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameReducesToBasisModPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InModIffForallPlaceMemSpanModulo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarCharacterEqProdAdditiveCharactersRoot

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeeperLevelIffMatricesModPlaceSymmetric
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPositionColumnCondIffCongruenceConj
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPositionColumnCondIffCongruenceConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc.Dual

open GlobalTheory.SeeConjRead (flagV)

section Comb

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {ρ k n : ℕ}

theorem fl_e (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (a : Fin ρ) (h : i.1 = a.1) :
    flagV ρ k n e f b z i = e a := by
  have := a.2
  unfold flagV
  rw [dite_eq_left (by omega)]
  exact congrArg e (Fin.ext h)

theorem fl_b (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (a : Fin k) (h : i.1 = ρ + a.1) :
    flagV ρ k n e f b z i = b a := by
  have := a.2
  unfold flagV
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  exact congrArg b (Fin.ext (by simp only; omega))

theorem symmetricFlagBasisVectors_apply_centre (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (h : i.1 = ρ + k) :
    flagV ρ k n e f b z i = z := by
  unfold flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h]

theorem fl_f (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) (a : Fin ρ) (h : i.1 + a.1 = 2 * ρ + k) :
    flagV ρ k n e f b z i = f a := by
  have := a.2
  unfold flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  exact congrArg f (Fin.ext (by simp only; omega))

theorem img_e (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ ρ) :
    e '' {a | a.1 < m} = flagV ρ k n e f b z '' {j | j.1 < m} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have := a.2
    exact ⟨⟨a.1, by omega⟩, ha, fl_e e f b z _ a rfl⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : j.1 < m := hj
    exact ⟨⟨j.1, by omega⟩, hj, (fl_e e f b z _ _ rfl).symm⟩

theorem range_eq_img (e : Fin ρ → M) : Set.range e = e '' {a | a.1 < ρ} := by
  rw [show {a : Fin ρ | a.1 < ρ} = Set.univ from Set.eq_univ_of_forall fun a => a.2, Set.image_univ]

theorem img_b (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ k) :
    Set.range e ∪ b '' {a | a.1 < m} = flagV ρ k n e f b z '' {j | j.1 < ρ + m} := by
  ext x
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, ha, rfl⟩)
    · have := a.2
      exact ⟨⟨a.1, by omega⟩, show a.1 < ρ + m by omega, fl_e e f b z _ a rfl⟩
    · have ha' : a.1 < m := ha
      exact ⟨⟨ρ + a.1, by omega⟩, show ρ + a.1 < ρ + m by omega, fl_b e f b z _ a rfl⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : j.1 < ρ + m := hj
    by_cases h : j.1 < ρ
    · exact Or.inl ⟨⟨j.1, h⟩, (fl_e e f b z _ _ rfl).symm⟩
    · exact Or.inr ⟨⟨j.1 - ρ, by omega⟩, show j.1 - ρ < m by omega,
        (fl_b e f b z _ _ (show j.1 = ρ + (j.1 - ρ) by omega)).symm⟩

theorem img_f (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ ρ) :
    f '' {a | a.1 < m} = flagV ρ k n e f b z '' {j | 2 * ρ + k < j.1 + m} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a.1 < m := ha
    exact ⟨⟨2 * ρ + k - a.1, by omega⟩, show 2 * ρ + k < 2 * ρ + k - a.1 + m by omega,
      fl_f e f b z _ a (show 2 * ρ + k - a.1 + a.1 = _ by omega)⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : 2 * ρ + k < j.1 + m := hj
    have := j.2
    exact ⟨⟨2 * ρ + k - j.1, by omega⟩, show 2 * ρ + k - j.1 < m by omega,
      (fl_f e f b z _ _ (show j.1 + (2 * ρ + k - j.1) = _ by omega)).symm⟩

theorem img_rev (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) {m : ℕ} (hm : m ≤ k) :
    Set.range f ∪ b '' {a | a.1 < m} =
      flagV ρ k n e f (fun i => b (Fin.rev i)) z '' {j | ρ + k ≤ j.1 + m ∧ j.1 ≠ ρ + k} := by
  ext x
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, ha, rfl⟩)
    · have := a.2
      exact ⟨⟨2 * ρ + k - a.1, by omega⟩, show ρ + k ≤ 2 * ρ + k - a.1 + m ∧ 2 * ρ + k - a.1 ≠ ρ + k by omega,
        fl_f e f _ z _ a (show 2 * ρ + k - a.1 + a.1 = _ by omega)⟩
    · have ha' : a.1 < m := ha
      refine ⟨⟨ρ + k - 1 - a.1, by omega⟩, show ρ + k ≤ ρ + k - 1 - a.1 + m ∧ ρ + k - 1 - a.1 ≠ ρ + k by omega, ?_⟩
      rw [fl_b e f _ z _ (Fin.rev a) (by rw [Fin.val_rev]; simp only; omega), Fin.rev_rev]
  · rintro ⟨j, hj, rfl⟩
    have hj' : ρ + k ≤ j.1 + m ∧ j.1 ≠ ρ + k := hj
    have := j.2
    by_cases h : j.1 < ρ + k
    · refine Or.inr ⟨Fin.rev ⟨j.1 - ρ, by omega⟩, ?_,
        (fl_b e f (fun i => b (Fin.rev i)) z j ⟨j.1 - ρ, by omega⟩ (show j.1 = ρ + (j.1 - ρ) by omega)).symm⟩
      show (Fin.rev _).1 < m
      rw [Fin.val_rev]; simp only; omega
    · exact Or.inl ⟨⟨2 * ρ + k - j.1, by omega⟩,
        (fl_f e f _ z _ _ (show j.1 + (2 * ρ + k - j.1) = _ by omega)).symm⟩

theorem comb (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (z : M) (b ε εd : Fin k → M) (W W' : Submodule R M)
    (T T' : M → M) (hneg : T' (-z) = -T' z) (P : Fin n → Fin n → Prop)
    (hcol : ∀ i S, T (flagV ρ k n e f ε z i) ∈ Submodule.span R (flagV ρ k n e f ε z '' S) ⊔ W ↔ ∀ j ∉ S, P j i)
    (hrow : ∀ j S, T' (flagV ρ k n f e εd (-z) j) ∈ Submodule.span R (flagV ρ k n f e εd (-z) '' S) ⊔ W' ↔
      ∀ i ∉ S, P j i)
    (hcase : (ε = b ∧ ∀ i, T' (b i) ∈ W') ∨ (εd = (fun i => b (Fin.rev i)) ∧ ∀ i, T (b i) ∈ W)) :
    (∀ i, T (flagV ρ k n e f ε z i) ∈ Submodule.span R (flagV ρ k n e f ε z '' {j | symAllowed ρ k i j}) ⊔ W) ↔
      ((∀ a : Fin ρ, T (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W) ∧
        T z ∈ Submodule.span R (Set.range e) ⊔ W ∧
        ∀ i : Fin k, T (b i) ∈ Submodule.span R (Set.range e ∪ b '' {j | j.1 < i.1}) ⊔ W) ∧
      ((∀ a : Fin ρ, T' (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W') ∧
        T' z ∈ Submodule.span R (Set.range e) ⊔ W' ∧
        ∀ i : Fin k, T' (b i) ∈ Submodule.span R (Set.range e ∪ b '' {j | j.1 < i.1}) ⊔ W') := by
  have c1 : ∀ (a : Fin ρ) (i : Fin n), i.1 = a.1 →
      (T (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W ↔ ∀ j : Fin n, ¬ j.1 < a.1 → P j i) := fun a i h => by
    rw [img_e hn e f ε z a.2.le, ← fl_e e f ε z i a h]; exact hcol _ _
  have c2 : ∀ i : Fin n, i.1 = ρ + k →
      (T z ∈ Submodule.span R (Set.range e) ⊔ W ↔ ∀ j : Fin n, ¬ j.1 < ρ → P j i) := fun i h => by
    have := hcol i {j | j.1 < ρ}
    rw [symmetricFlagBasisVectors_apply_centre e f ε z i h, ← img_e hn e f ε z le_rfl, ← range_eq_img] at this
    exact this
  have c3 : ∀ (a : Fin k) (i : Fin n), i.1 = ρ + a.1 →
      (T (ε a) ∈ Submodule.span R (Set.range e ∪ ε '' {c | c.1 < a.1}) ⊔ W ↔
        ∀ j : Fin n, ¬ j.1 < ρ + a.1 → P j i) := fun a i h => by
    rw [img_b hn e f ε z a.2.le, ← fl_b e f ε z i a h]; exact hcol _ _
  have r1 : ∀ (a : Fin ρ) (j : Fin n), j.1 + a.1 = 2 * ρ + k →
      (T' (e a) ∈ Submodule.span R (e '' {c | c.1 < a.1}) ⊔ W' ↔
        ∀ i : Fin n, ¬ 2 * ρ + k < i.1 + a.1 → P j i) := fun a j h => by
    rw [img_f hn f e εd (-z) a.2.le, ← fl_f f e εd (-z) j a h]; exact hrow _ _
  have r2 : ∀ j : Fin n, j.1 = ρ + k →
      (T' z ∈ Submodule.span R (Set.range e) ⊔ W' ↔ ∀ i : Fin n, ¬ 2 * ρ + k < i.1 + ρ → P j i) := fun j h => by
    have := hrow j {i | 2 * ρ + k < i.1 + ρ}
    rw [symmetricFlagBasisVectors_apply_centre f e εd (-z) j h, ← img_f hn f e εd (-z) le_rfl, ← range_eq_img, hneg, neg_mem_iff] at this
    exact this
  have r3 : εd = (fun i => b (Fin.rev i)) → ∀ (a : Fin k) (j : Fin n), j.1 + a.1 + 1 = ρ + k →
      (T' (b a) ∈ Submodule.span R (Set.range e ∪ b '' {c | c.1 < a.1}) ⊔ W' ↔
        ∀ i : Fin n, ¬ (ρ + k ≤ i.1 + a.1 ∧ i.1 ≠ ρ + k) → P j i) := fun hd a j h => by
    have := hrow j {i | ρ + k ≤ i.1 + a.1 ∧ i.1 ≠ ρ + k}
    have ha := a.2
    rw [hd, fl_b f e _ (-z) j (Fin.rev a) (by rw [Fin.val_rev]; omega), ← img_rev hn f e b (-z) a.2.le,
      Fin.rev_rev] at this
    exact this
  simp only [hcol, Set.mem_setOf_eq, symAllowed]
  constructor
  · intro H
    refine ⟨⟨fun a => ?_, ?_, fun a => ?_⟩, fun a => ?_, ?_, fun a => ?_⟩
    · have := a.2
      exact (c1 a ⟨a.1, by omega⟩ rfl).2 fun j hj => H _ _ (by simp only; omega)
    · exact (c2 ⟨ρ + k, by omega⟩ rfl).2 fun j hj => H _ _ (by dsimp only; omega)
    · have := a.2
      rcases hcase with ⟨rfl, -⟩ | ⟨-, h⟩
      · exact (c3 a ⟨ρ + a.1, by omega⟩ rfl).2 fun j hj => H _ _ (by simp only; omega)
      · exact Submodule.mem_sup_right (h a)
    · have := a.2
      exact (r1 a ⟨2 * ρ + k - a.1, by omega⟩ (by simp only; omega)).2 fun j hj => H _ _ (by simp only; omega)
    · exact (r2 ⟨ρ + k, by omega⟩ rfl).2 fun j hj => H _ _ (by simp only; omega)
    · have := a.2
      rcases hcase with ⟨-, h⟩ | ⟨h, -⟩
      · exact Submodule.mem_sup_right (h a)
      · exact (r3 h a ⟨ρ + k - 1 - a.1, by omega⟩ (by simp only; omega)).2 fun j hj => H _ _ (by simp only; omega)
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ i j hij
    have hi := i.2
    have hj := j.2
    by_cases a1 : i.1 < ρ
    · exact (c1 ⟨i.1, a1⟩ i rfl).1 (h1 _) j (by simp only; omega)
    by_cases a2 : i.1 = ρ + k
    · exact (c2 i a2).1 h2 j (by omega)
    by_cases a3 : ρ + k < j.1
    · exact (r1 ⟨2 * ρ + k - j.1, by omega⟩ j (by simp only; omega)).1 (h4 _) i (by simp only; omega)
    by_cases a4 : j.1 = ρ + k
    · exact (r2 j a4).1 h5 i (by omega)
    rcases hcase with ⟨rfl, -⟩ | ⟨h, -⟩
    · exact (c3 ⟨i.1 - ρ, by omega⟩ i (by simp only; omega)).1 (h3 _) j (by simp only; omega)
    · exact (r3 h ⟨ρ + k - 1 - j.1, by omega⟩ j (by simp only; omega)).1 (h6 _) i (by simp only; omega)

end Comb

open Formalism.L2.SG.Pf.unitaryCongruence GlobalTheory.Mem.SymChar GlobalTheory.Mem.SymFrame GlobalTheory.DimPartsCompare

variable {D : D7} (X : HidaSetting D)

theorem sig_mem (w : HeightOneSpectrum (𝓞 D.host.E)) {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hc : c ∈ wInt X w) : sigA X.B.I c ∈ wInt X (cPl w) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, ⟨b, hb, hab⟩, rfl⟩ := hc
    rw [sigA_inclE]
    refine Submodule.subset_span ⟨RingOfIntegers.mapRingEquiv X.ιE.symm (GlobalTheory.SumWCompare.cj _ b),
      ⟨GlobalTheory.SumWCompare.cj _ b, by rw [mem_cPl, GlobalTheory.SumWCompare.cj_cj]; exact hb, X.ιE.apply_symm_apply _⟩, ?_⟩
    congr 1
    apply X.ιE.injective
    rw [X.ιE_conj, hab, ← star_conj, ← GlobalTheory.SumWCompare.cj_coe]
    exact (X.ιE.apply_symm_apply _).symm
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    show sigA X.B.I ((r : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * a) ∈ _
    rw [map_mul]
    exact (wInt X (cPl w)).smul_mem ⟨_, sigA_mem X.B.I r.2⟩ ha

theorem mul_mem_wInt (w : HeightOneSpectrum (𝓞 D.host.E)) {t c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (ht : t ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (hc : c ∈ wInt X w) : t * c ∈ wInt X w :=
  (wInt X w).smul_mem ⟨t, ht⟩ hc

theorem coords (w : HeightOneSpectrum (𝓞 D.host.E)) {n : ℕ} (u v : Fin n → VA X.B.I)
    (hu : ∀ i, u i ∈ X.B.I.Lf) (hv : ∀ i, v i ∈ X.B.I.Lf)
    (hd : ∀ j i, hA X.B.I (v j) (u i) - (if i = j then 1 else 0) ∈ wInt X w)
    {y : VA X.B.I} (hy : GroupLoc.ModW X w (Set.range u) y) (S : Set (Fin n)) :
    GroupLoc.ModW X w (u '' S) y ↔ ∀ j ∉ S, hA X.B.I (v j) y ∈ wInt X w := by
  constructor
  · intro h j hj
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 h
    rw [hA_add_right]
    refine add_mem ?_ (hA_mem_wInt X w (hv j) ht)
    clear h hy
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨i, hi, rfl⟩ := hs
      have := hd j i
      rwa [ite_eq_right (fun (e : i = j) => hj (e ▸ hi)), sub_zero] at this
    | zero => rw [hA_zero_right']; exact zero_mem _
    | add a b _ _ ha hb => rw [hA_add_right]; exact add_mem ha hb
    | smul r a _ ha =>
      show hA X.B.I (v j) ((r : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • a) ∈ _
      rw [hA_smul_right]
      exact mul_mem_wInt X w r.2 ha
  · intro h
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hs
    refine add_mem (sum_mem fun j _ => ?_) (Submodule.mem_sup_right ht)
    by_cases hj : j ∈ S
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩))
    refine Submodule.mem_sup_right (smul_mem_wLf_of_mem_wInt X w (c := c j) ?_ (hu j))
    have h1 := h j hj
    rw [hA_add_right, hA_sum_right'] at h1
    have h2 := sub_mem h1 (hA_mem_wInt X w (hv j) ht)
    rw [add_sub_cancel_right] at h2
    have h3 : ∑ i, ((c i : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
        (hA X.B.I (v j) (u i) - (if i = j then 1 else 0))) ∈ wInt X w :=
      sum_mem fun i _ => mul_mem_wInt X w (c i).2 (hd j i)
    have h4 : ∀ i, hA X.B.I (v j) (c i • u i) =
        (c i : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I (v j) (u i) := fun i => hA_smul_right _ _ _ _
    simp only [h4] at h2
    have h5 := sub_mem h2 h3
    simpa [mul_sub, Finset.sum_sub_distrib] using h5

theorem pres_w (w : HeightOneSpectrum (𝓞 D.host.E)) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (S : Set (VA X.B.I))
    (hS : ∀ s ∈ S, GroupLoc.ModW X w S ((X.B.I.fmat x - 1) *ᵥ s)) {y : VA X.B.I} (hy : GroupLoc.ModW X w S y) :
    GroupLoc.ModW X w S (X.B.I.fmat x *ᵥ y) := by
  have h : Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S ⊔ wLf X w ≤
      (Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S ⊔ wLf X w).comap (mvO X.B.I (X.B.I.fmat x)) := by
    refine sup_le (Submodule.span_le.2 fun s hs => ?_)
      (fun s hs => Submodule.mem_sup_right (fmat_mulVec_mem_wLf X w hx hs))
    show GroupLoc.ModW X w S (X.B.I.fmat x *ᵥ s)
    have e : X.B.I.fmat x *ᵥ s = s + (X.B.I.fmat x - 1) *ᵥ s := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span hs)) (hS s hs)
  exact h hy

theorem modW_mono {w : HeightOneSpectrum (𝓞 D.host.E)} {S T : Set (VA X.B.I)} (h : S ⊆ T) {y : VA X.B.I}
    (hy : GroupLoc.ModW X w S y) : GroupLoc.ModW X w T y :=
  (sup_le_sup_right (Submodule.span_mono h) _ : Submodule.span _ S ⊔ wLf X w ≤ _) hy

theorem condAt_inv (w : HeightOneSpectrum (𝓞 D.host.E)) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (h : CondAt X w x) :
    CondAt X w x⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := h
  have key : ∀ (S : Set (VA X.B.I)) (y : VA X.B.I), (∀ s ∈ S, GroupLoc.ModW X w S ((X.B.I.fmat x⁻¹ - 1) *ᵥ s)) →
      GroupLoc.ModW X w S ((X.B.I.fmat x - 1) *ᵥ y) → GroupLoc.ModW X w S ((X.B.I.fmat x⁻¹ - 1) *ᵥ y) := fun S y hS hy => by
    rw [inv_id]
    exact neg_mem (pres_w X w (K_inv _ hx) S hS hy)
  have e1 : ∀ m : ℕ, ∀ a : Fin D.R.rS, a.1 < m →
      GroupLoc.ModW X w (X.e0 '' {b | b.1 < a.1}) ((X.B.I.fmat x⁻¹ - 1) *ᵥ X.e0 a) := by
    intro m
    induction m with
    | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro a ha
      refine key _ _ ?_ (h1 a)
      rintro _ ⟨b, hb, rfl⟩
      have hb' : b.1 < a.1 := hb
      exact modW_mono X (Set.image_mono (lt_sub hb'.le)) (ih b (by omega))
  have e3 : ∀ m : ℕ, ∀ i : Fin D.R.k, i.1 < m →
      GroupLoc.ModW X w (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ((X.B.I.fmat x⁻¹ - 1) *ᵥ X.bw i) := by
    intro m
    induction m with
    | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      refine key _ _ ?_ (h3 i)
      rintro _ (⟨b, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact modW_mono X ((Set.image_subset_range _ _).trans Set.subset_union_left) (e1 _ b (Nat.lt_succ_self _))
      · have hj' : j.1 < i.1 := hj
        exact modW_mono X (Set.union_subset_union_right _ (Set.image_mono (lt_sub hj'.le))) (ih j (by omega))
  refine ⟨fun a => e1 _ a (Nat.lt_succ_self _), key _ _ ?_ h2, fun i => e3 _ i (Nat.lt_succ_self _)⟩
  rintro _ ⟨b, rfl⟩
  exact modW_mono X (Set.image_subset_range _ _) (e1 _ b (Nat.lt_succ_self _))

theorem rank_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  have := D.R.rS_two
  unfold Ranks.r
  omega

theorem span_frame (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (u : Fin D.R.r → VA X.B.I)
    (he : ∀ a, GroupLoc.ModW X w (Set.range u) (X.e0 a)) (hf : ∀ a, GroupLoc.ModW X w (Set.range u) (X.f0 a))
    (hz : GroupLoc.ModW X w (Set.range u) X.z0) (hb : ∀ a, GroupLoc.ModW X w (Set.range u) (X.bw a))
    (hb' : ∀ a, GroupLoc.ModW X w (Set.range u) (X.bwd a)) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    GroupLoc.ModW X w (Set.range u) y := by
  have h := X.latticeSpan y hy
  refine (sup_le (Submodule.span_le.2 ?_) (le_trans ?_ le_sup_right) :
    _ ≤ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (Set.range u) ⊔ wLf X w) h
  · rintro _ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨a, rfl⟩) | ⟨a, rfl⟩)
    exacts [he a, hf a, hz, hb a, hb' a]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact smul_mem_wLf_of_mem_wInt X w (wInt_of_zmod X k hg ⟨1, one_mem _, (mul_one _).symm⟩) hx

theorem flagV_mem {e f : Fin D.R.rS → VA X.B.I} {b : Fin D.R.k → VA X.B.I} {z : VA X.B.I}
    (he : ∀ a, e a ∈ X.B.I.Lf) (hf : ∀ a, f a ∈ X.B.I.Lf) (hb : ∀ a, b a ∈ X.B.I.Lf) (hz : z ∈ X.B.I.Lf)
    (i : Fin D.R.r) : flagV D.R.rS D.R.k D.R.r e f b z i ∈ X.B.I.Lf := by
  unfold flagV
  split_ifs
  exacts [he _, hb _, hz, hf _, zero_mem _]

theorem modW_range {w : HeightOneSpectrum (𝓞 D.host.E)} {u : Fin D.R.r → VA X.B.I} {y : VA X.B.I} (i : Fin D.R.r)
    (h : u i = y) : GroupLoc.ModW X w (Set.range u) y :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨i, h⟩)

theorem one_sub_ew (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (h : EwAt X w) : 1 - X.ew ∈ wInt X w := by
  have h1 := hA_mem_wInt X w X.vectorsInLattice.2.1 (h _ X.vectorsInLattice.2.1)
  rw [hA_smul_right] at h1
  have h2 := mul_mem_wInt X w (sub_mem (one_mem _) X.ew_int) (wInt_of_zmod X k hg X.formsAtZero.1)
  have h3 := sub_mem h2 h1
  rwa [mul_add, add_sub_cancel_left, mul_one] at h3


open Classical in
def epsD (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.k → VA X.B.I :=
  if EwAt X w then X.bwd else fun i => X.bw (Fin.rev i)

def dualVec (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.r → VA X.B.I :=
  flagV D.R.rS D.R.k D.R.r X.f0 X.e0 (epsD X w) (-X.z0)

theorem hA_neg_left (x y : VA X.B.I) : hA X.B.I (-x) y = -hA X.B.I x y := by
  rw [← neg_one_smul (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) x, hA_smul_left, map_neg, map_one, neg_one_mul]

theorem hA_adj (x : X.B.I.Gf) (a b : VA X.B.I) :
    hA X.B.I b ((X.B.I.fmat x⁻¹ - 1) *ᵥ a) = sigA X.B.I (hA X.B.I a ((X.B.I.fmat x - 1) *ᵥ b)) := by
  have h : hA X.B.I (X.B.I.fmat x *ᵥ b) (X.B.I.fmat x *ᵥ (X.B.I.fmat x⁻¹ *ᵥ a)) =
      hA X.B.I b (X.B.I.fmat x⁻¹ *ᵥ a) := by
    have hx : Formalism.UG.cT (sigA X.B.I) (X.B.I.fmat x) *
        X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) * X.B.I.fmat x =
        X.B.I.J.map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) := x.2
    have hd : ∀ (J : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) (u v : VA X.B.I),
        Formalism.UG.hform (sigA X.B.I) J u v = (sigA X.B.I ∘ u) ⬝ᵥ (J *ᵥ v) := fun J u v => by
      simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
    have hσ : sigA X.B.I ∘ (X.B.I.fmat x *ᵥ b) = (X.B.I.fmat x).map (sigA X.B.I) *ᵥ (sigA X.B.I ∘ b) :=
      funext fun i => RingHom.map_mulVec (sigA X.B.I) (X.B.I.fmat x) b i
    unfold hA
    rw [hd, hd, hσ, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← Formalism.UG.cT, hx]
  have e : X.B.I.fmat x * X.B.I.fmat x⁻¹ = 1 := by rw [← fmat_mul, mul_inv_cancel, fmat_one]
  rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] at h
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right, map_sub]
  rw [← h, ← hA_symm, ← hA_symm]

theorem colCond_iff_condAt : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k ↔ GlobalTheory.Mem.GroupLoc.CondAt X (D.naut.plGw kv.1 kv.2) k ∧ GlobalTheory.Mem.GroupLoc.CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k) := by
  intro D X hI hι hgs x hx kv
  have hg := hgs kv
  have hn := rank_eq D
  have hA_e0 := hA_e0_symVec D X kv hg
  have hA_z0 := ZPair.hA_z0_symVec D X kv hg
  have hA_bw := Resid.hA_bw_symVec_not_ewAt D X kv hg
  have hsig := sigA_ew_sub_one_mem_wInt D X hI hι kv hg
  generalize D.naut.plGw kv.1 kv.2 = w at *
  have hg' : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (cPl w).asIdeal := by rw [mem_cPl, map_natCast]; exact hg
  obtain ⟨ief, iz, ib⟩ := X.vectorsInLattice
  have hse := sigA_mem X.B.I X.ew_int

  have p1 : EwAt X w → sigA X.B.I X.ew ∈ wInt X w := fun h => by
    have := mul_mem_wInt X w hse (one_sub_ew X w kv.1 hg h)
    rwa [mul_sub, mul_one, mul_comm, X.ew_orth, sub_zero] at this
  have p2 : ¬ EwAt X w → X.ew ∈ wInt X w := fun h => by
    have := neg_mem (mul_mem_wInt X w X.ew_int (hsig h))
    rwa [mul_sub, mul_one, X.ew_orth, zero_sub, neg_neg] at this
  have q1 : EwAt X w → ∀ i, X.bwd i ∈ wLf X w := fun h i => by
    rw [X.bwd_w]; exact smul_mem_wLf_of_mem_wInt X w (p1 h) (ib i).2
  have q2 : EwAt X w → ∀ i, X.bw i ∈ wLf X (cPl w) := fun h i => by
    have := sig_mem X w (p1 h)
    rw [sigA_sigA] at this
    rw [X.bw_w]; exact smul_mem_wLf_of_mem_wInt X _ this (ib i).1
  have q3 : ¬ EwAt X w → ∀ i, X.bw i ∈ wLf X w := fun h i => by
    rw [X.bw_w]; exact smul_mem_wLf_of_mem_wInt X w (p2 h) (ib i).1
  have q4 : ¬ EwAt X w → ∀ i, X.bwd i ∈ wLf X (cPl w) := fun h i => by
    rw [X.bwd_w]; exact smul_mem_wLf_of_mem_wInt X _ (sig_mem X w (p2 h)) (ib i).2
  have hu : ∀ i, symVec X w i ∈ X.B.I.Lf :=
    flagV_mem X (fun a => (ief a).1) (fun a => (ief a).2)
      (fun a => by unfold epsW; split_ifs; exacts [(ib _).1, (ib _).2]) iz
  have hv : ∀ i, dualVec X w i ∈ X.B.I.Lf :=
    flagV_mem X (fun a => (ief a).2) (fun a => (ief a).1)
      (fun a => by unfold epsD; split_ifs; exacts [(ib _).2, (ib _).1]) (neg_mem iz)

  have hd : ∀ j i, hA X.B.I (dualVec X w j) (symVec X w i) - (if i = j then 1 else 0) ∈ wInt X w := by
    intro j i
    have hj := j.2
    unfold dualVec
    by_cases a1 : j.1 < D.R.rS
    · rw [fl_e _ _ _ _ j ⟨j.1, a1⟩ rfl]
      exact hA_symVec_sub_ite_mem_wInt D X w kv.1 hg ⟨j.1, a1⟩ i
    by_cases a2 : j.1 < D.R.rS + D.R.k
    · rw [fl_b _ _ _ _ j ⟨j.1 - D.R.rS, by omega⟩ (by simp only; omega)]
      unfold epsD
      by_cases h : EwAt X w
      · rw [ite_eq_left h]
        have := Resid.hA_bwd_symVec D X w kv.1 hg h (one_sub_ew X w kv.1 hg h) ⟨j.1 - D.R.rS, by omega⟩ i
        rwa [show Resid.posB D ⟨j.1 - D.R.rS, by omega⟩ = j from Fin.ext (by simp only [Resid.posB]; omega)] at this
      · rw [ite_eq_right h]
        have := hA_bw h (hsig h) (Fin.rev ⟨j.1 - D.R.rS, by omega⟩) i
        rwa [show D.R.rS + D.R.k - 1 - (Fin.rev (⟨j.1 - D.R.rS, by omega⟩ : Fin D.R.k)).1 = j.1 by
          rw [Fin.val_rev]; simp only; omega, if_congr Fin.val_inj rfl rfl] at this
    by_cases a3 : j.1 = D.R.rS + D.R.k
    · rw [symmetricFlagBasisVectors_apply_centre _ _ _ _ j a3, hA_neg_left]
      have := neg_mem (hA_z0 i)
      rw [← a3, if_congr Fin.val_inj rfl rfl] at this
      convert this using 1
      split_ifs <;> ring
    · rw [fl_f _ _ _ _ j ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩ (by simp only; omega)]
      have := hA_e0 ⟨2 * D.R.rS + D.R.k - j.1, by omega⟩ i
      rwa [show 2 * D.R.rS + D.R.k - (⟨2 * D.R.rS + D.R.k - j.1, by omega⟩ : Fin D.R.rS).1 = j.1 by
          simp only; omega, if_congr Fin.val_inj rfl rfl] at this
  have hd' : ∀ i j, hA X.B.I (symVec X w i) (dualVec X w j) - (if j = i then 1 else 0) ∈ wInt X (cPl w) := by
    intro i j
    have := sig_mem X w (hd j i)
    rwa [map_sub, ← hA_symm, apply_ite (sigA X.B.I), map_one, map_zero, if_congr eq_comm rfl rfl] at this

  have su : ∀ y ∈ X.B.I.Lf, GroupLoc.ModW X w (Set.range (symVec X w)) y := fun y hy => by
    refine span_frame X w kv.1 hg _ (fun a => ?_) (fun a => ?_) ?_ (fun a => ?_) (fun a => ?_) hy
    · have := a.2
      exact modW_range X ⟨a.1, by omega⟩ (fl_e _ _ _ _ _ a rfl)
    · have := a.2
      exact modW_range X ⟨2 * D.R.rS + D.R.k - a.1, by omega⟩ (fl_f _ _ _ _ _ a (by simp only; omega))
    · exact modW_range X ⟨D.R.rS + D.R.k, by omega⟩ (symmetricFlagBasisVectors_apply_centre _ _ _ _ _ rfl)
    · have := a.2
      by_cases h : EwAt X w
      · exact modW_range X ⟨D.R.rS + a.1, by omega⟩ ((fl_b _ _ _ _ _ a rfl).trans (by rw [epsW, ite_eq_left h]))
      · exact Submodule.mem_sup_right (q3 h a)
    · have := a.rev.2
      by_cases h : EwAt X w
      · exact Submodule.mem_sup_right (q1 h a)
      · exact modW_range X ⟨D.R.rS + a.rev.1, by omega⟩ ((fl_b _ _ _ _ _ a.rev rfl).trans
          (by rw [epsW, ite_eq_right h]; exact congrArg X.bwd (Fin.rev_rev a)))
  have sv : ∀ y ∈ X.B.I.Lf, GroupLoc.ModW X (cPl w) (Set.range (dualVec X w)) y := fun y hy => by
    refine span_frame X _ kv.1 hg' _ (fun a => ?_) (fun a => ?_) ?_ (fun a => ?_) (fun a => ?_) hy
    · have := a.2
      exact modW_range X ⟨2 * D.R.rS + D.R.k - a.1, by omega⟩ (fl_f _ _ _ _ _ a (by simp only; omega))
    · have := a.2
      exact modW_range X ⟨a.1, by omega⟩ (fl_e _ _ _ _ _ a rfl)
    · exact neg_mem_iff.1 (modW_range X ⟨D.R.rS + D.R.k, by omega⟩ (symmetricFlagBasisVectors_apply_centre _ _ _ _ _ rfl))
    · have := a.rev.2
      by_cases h : EwAt X w
      · exact Submodule.mem_sup_right (q2 h a)
      · exact modW_range X ⟨D.R.rS + a.rev.1, by omega⟩ ((fl_b _ _ _ _ _ a.rev rfl).trans
          (by rw [epsD, ite_eq_right h]; exact congrArg X.bw (Fin.rev_rev a)))
    · have := a.2
      by_cases h : EwAt X w
      · exact modW_range X ⟨D.R.rS + a.1, by omega⟩ ((fl_b _ _ _ _ _ a rfl).trans (by rw [epsD, ite_eq_left h]))
      · exact Submodule.mem_sup_right (q4 h a)
  have sub_w : ∀ (w' : HeightOneSpectrum (𝓞 D.host.E)) (y : X.B.I.Gf), y ∈ X.B.I.Kset → ∀ s ∈ wLf X w',
      (X.B.I.fmat y - 1) *ᵥ s ∈ wLf X w' := fun w' y hy s hs => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (fmat_mulVec_mem_wLf X w' hy hs) hs
  have main := comb (R := Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hn X.e0 X.f0 X.z0 X.bw (epsW X w) (epsD X w) (wLf X w)
    (wLf X (cPl w)) (fun y => (X.B.I.fmat x - 1) *ᵥ y) (fun y => (X.B.I.fmat x⁻¹ - 1) *ᵥ y)
    (Matrix.mulVec_neg _ _)
    (fun j i => hA X.B.I (dualVec X w j) ((X.B.I.fmat x - 1) *ᵥ symVec X w i) ∈ wInt X w)
    (fun i S => coords X w _ _ hu hv hd (su _ (K_sub_mv _ hx (hu i))) S)
    (fun j S => (coords X (cPl w) _ _ hv hu hd' (sv _ (K_sub_mv _ (K_inv _ hx) (hv j))) S).trans
      (forall₂_congr fun i _ => by
        rw [hA_adj]
        refine ⟨fun h => ?_, sig_mem X w⟩
        have := sig_mem X _ h
        rwa [sigA_sigA, cPl_cPl] at this))
    (by
      by_cases h : EwAt X w
      · exact Or.inl ⟨by rw [epsW, ite_eq_left h], fun i => sub_w _ _ (K_inv _ hx) _ (q2 h i)⟩
      · exact Or.inr ⟨by rw [epsD, ite_eq_right h], fun i => sub_w _ _ hx _ (q3 h i)⟩)
  refine Iff.trans main (and_congr Iff.rfl ⟨fun h => ?_, fun h => condAt_inv X _ hx h⟩)
  have := condAt_inv X (cPl w) (K_inv _ hx) h
  rwa [inv_inv] at this

end GlobalTheory.Mem.GroupLoc.Dual

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPositionColumnCondIffCongruenceConjStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionColumnCond_iff_congruence_conj : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k ↔ GlobalTheory.Mem.GroupLoc.CondAt X (D.naut.plGw kv.1 kv.2) k ∧ GlobalTheory.Mem.GroupLoc.CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k) := by
  first | exact @GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt | exact GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt | (intros; apply GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameMatrixMemUnipotentIffColumnSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameMatrixMemUnipotentIffColumnSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GroupLoc.Coords

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA PIW.AdelClassFin

variable {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p m : ℕ}

theorem rep_of_int (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hu : ∀ j, u j ∈ I.Lf) {v : Fin I.n → I.E ⊗[I.F] Af I.F}
    {c : Fin m → ℤ} (h : v - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w) :
    RepV w p u v (fun j => (c j : ZMod p)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2 : ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j -
      ∑ j, ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    rw [← sub_smul]
    refine Wq_smul ?_ (hu j)
    have hk : c j - ((((c j : ZMod p)).val : ℕ) : ℤ) = (c j / p) * p := by
      rw [ZMod.val_intCast, Int.emod_def]; ring
    have e : (c j : I.E ⊗[I.F] Af I.F) - ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) =
        ((c j / p : ℤ) : I.E ⊗[I.F] Af I.F) * (p : I.E ⊗[I.F] Af I.F) := by
      have := congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) hk
      simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul] using this
    rw [e]
    exact Wq_mul (natCast_Wq hp hcard) (intCast_int _)
  have := add_mem h h2
  show v - _ ∈ _
  convert this using 1
  abel

theorem int_comb (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hu : ∀ j, u j ∈ I.Lf) (S : Set (Fin m))
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ Submodule.span (IntAf I.F I.E) (u '' S) ⊔ Lq I w) :
    ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧ y - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
  classical
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
  have key : ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧
      y1 - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
    clear hy
    induction hy1 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun e : j = i => hj (by rw [e]; exact hi)) _, ?_⟩
      rw [Fintype.sum_eq_single i (fun j hj => by simp [hj])]
      simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc0, hc⟩ := hx
      obtain ⟨d, hd0, hd⟩ := hz
      refine ⟨c + d, fun j hj => by simp [hc0 j hj, hd0 j hj], ?_⟩
      have := add_mem hc hd
      convert this using 1
      simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
      abel
    | smul s x _ hx =>
      obtain ⟨c, hc0, hc⟩ := hx
      obtain ⟨_, t, -, ht⟩ := congW_exists (w := w) hp hcard s.2
      refine ⟨fun j => t * c j, fun j hj => by simp [hc0 j hj], ?_⟩
      have h1 := (Lq I w).smul_mem s hc
      have h2 : ((s : I.E ⊗[I.F] Af I.F) - (t : I.E ⊗[I.F] Af I.F)) •
          ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
        refine Wq_smul ht (sum_mem fun j _ => ?_)
        rw [Int.cast_smul_eq_zsmul]
        exact zsmul_mem (hu j) _
      have := add_mem h1 h2
      convert this using 1
      show (s : I.E ⊗[I.F] Af I.F) • x - _ = (s : I.E ⊗[I.F] Af I.F) • (x - _) + _
      simp only [Int.cast_mul, mul_smul, ← Finset.smul_sum, smul_sub, sub_smul]
      abel
  obtain ⟨c, hc0, hc⟩ := key
  refine ⟨c, hc0, ?_⟩
  have := add_mem hc hy2
  convert this using 1
  abel

theorem cols_iff (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) (P : GL (Fin m) (ZMod p))
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F}
    (hP : ∀ j, RepV w p (fun k => iv I (b k)) (u j) (fun k => (P : Matrix (Fin m) (Fin m) (ZMod p)) k j))
    (A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (N : Matrix (Fin m) (Fin m) (ZMod p))
    (i : Fin m) (hN : RepV w p u (A *ᵥ u i) (fun j => N j i)) (S : Set (Fin m)) :
    (∀ j, j ∉ S → N j i = (1 : Matrix (Fin m) (Fin m) (ZMod p)) j i) ↔
      (A - 1) *ᵥ u i ∈ Submodule.span (IntAf I.F I.E) (u '' S) ⊔ Lq I w := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hu : ∀ j, u j ∈ I.Lf := fun j => by
    have h1 : u j - _ ∈ I.Lf := lamAf_mono I (wLat0_le I w) (hP j)
    have h2 : ∑ k, ((((P : Matrix (Fin m) (Fin m) (ZMod p)) k j).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ I.Lf :=
      sum_mem fun k _ => by
        rw [Nat.cast_smul_eq_nsmul]
        exact nsmul_mem (DictLat.iv_mem I (hb.1 k)) _
    simpa using add_mem h1 h2
  have e1 : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j = u i := by
    rw [Fintype.sum_eq_single i (fun j hj => by simp [Matrix.one_apply_ne hj])]
    simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · intro h
    have h1 : ∑ j, (((N j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j - u i ∈
        Submodule.span (IntAf I.F I.E) (u '' S) := by
      rw [← e1, ← Finset.sum_sub_distrib]
      refine sum_mem fun j _ => ?_
      by_cases hj : j ∈ S
      · rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        have hm : u j ∈ Submodule.span (IntAf I.F I.E) (u '' S) := Submodule.subset_span ⟨j, hj, rfl⟩
        exact sub_mem (nsmul_mem hm _) (nsmul_mem hm _)
      · rw [h j hj, sub_self]; exact zero_mem _
    have := Submodule.add_mem_sup h1 hN
    convert this using 1
    abel
  · intro h j hj
    obtain ⟨c, hc0, hc⟩ := int_comb hp hcard hu S h
    have h2 : A *ᵥ u i - ∑ l, (((c + Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l ∈ Lq I w := by
      convert hc using 1
      simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
      rw [Fintype.sum_eq_single i (f := fun l => (((Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l)
        (fun l hl => by simp [hl])]
      simp only [Pi.single_eq_same, Int.cast_one, one_smul]
      abel
    have h3 := rep_unique hp hcard hm hb (rep_comp hp hcard hb.1 hN hP)
      (rep_comp hp hcard hb.1 (rep_of_int hp hcard hu h2) hP)
    have h4 := congrArg (fun v => ((P⁻¹ : GL (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ v) h3
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h4
    have h5 := congrFun h4 j
    simp only [Pi.add_apply, hc0 j hj, zero_add] at h5
    rw [h5]
    by_cases e : j = i
    · subst e; simp
    · simp [e]

theorem mem_unipSym_iff {κ : Type} [CommRing κ] {r ρ k : ℕ} (N : GL (Fin r) κ) :
    N ∈ unipSym κ r ρ k ↔ ∀ i j : Fin r, j ∉ {j | symAllowed ρ k i j} →
      (N : Matrix (Fin r) (Fin r) κ) j i = (1 : Matrix (Fin r) (Fin r) κ) j i := by
  constructor
  · rintro ⟨h1, h2⟩ i j hj
    rcases lt_trichotomy j i with h | h | h
    · obtain ⟨a, b, c⟩ : ρ ≤ j.1 ∧ j.1 < ρ + k ∧ i.1 = ρ + k := by
        by_contra hh
        exact hj ⟨h, hh⟩
      rw [h2 j i a b c, Matrix.one_apply_ne h.ne]
    · subst h
      rw [unip_diag h1, Matrix.one_apply_eq]
    · rw [unip_lower h1 h, Matrix.one_apply_ne h.ne']
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · have hij' : j.val < i.val := hij
      rw [h j i (fun hh => by have := hh.1; omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
    · rw [h i i (fun hh => lt_irrefl _ hh.1), Matrix.one_apply_eq]
    · rw [h j i (fun hh => hh.2 ⟨ha, hb, hc⟩), Matrix.one_apply_ne (fun e => by rw [e] at hb; omega)]

end GlobalTheory.Mem.GroupLoc.Coords

namespace GlobalTheory.Mem.GroupLoc


open Formalism.L2.SG.Pf.RowDictPf in
theorem mem_unipSym_iff_colCond : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (N : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → (N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k ↔ GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k) := by
  intro D X h hι hg k _ kv N hN
  choose b hb using fun kv => Formalism.L2.SG.Pf.AllRowsRhoX.exists_b X kv
  obtain ⟨P, hP⟩ := GlobalTheory.T.symmetricFrame_reduces_to_basis_mod_place D X h hι b (fun kv => by
    unfold IsRedBasis
    rw [wLat_eq X]
    exact hb kv) hg 1
  rw [Coords.mem_unipSym_iff]
  unfold ColCond ModW
  refine forall_congr' fun i => ?_
  have hP' := hP kv
  have hN' := hN i
  unfold wLf at hP' hN' ⊢
  rw [wLat_eq X] at hP' hN' ⊢
  exact Coords.cols_iff (w := wB X (D.naut.plGw kv.1 kv.2)) (D.host.g_prime kv.1)
    (by rw [card_wB, card_res_host]) X.n_eq.symm (hb kv) (P kv) hP' (X.B.I.fmat k) _ i hN' _

end GlobalTheory.Mem.GroupLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameMatrixMemUnipotentIffColumnSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricFrame_matrix_mem_unipotent_iff_column_span : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (N : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → (N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k ↔ GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k) := by
  first | exact @GlobalTheory.Mem.GroupLoc.mem_unipSym_iff_colCond | exact GlobalTheory.Mem.GroupLoc.mem_unipSym_iff_colCond | (intros; apply GlobalTheory.Mem.GroupLoc.mem_unipSym_iff_colCond <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeeperLevelIffMatricesModPlaceSymmetric
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GroupLoc

theorem membership_iff_unipSym : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (k ∈ X.K2 ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) := by
  intro D X h hE hg k hk Ns hNs
  have hK2 : k ∈ X.K2 ↔ K2cong X.B.I X.B.g X.e0 X.z0 X.bw k := ⟨fun hm => hm.2, fun hm => ⟨hk, hm⟩⟩
  have hLf : ∀ y ∈ X.B.I.Lf, (X.B.I.fmat k - 1) *ᵥ y ∈ X.B.I.Lf := by
    intro y hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem ((hk y).1 hy) hy
  have hS1 : ∀ a : Fin D.R.rS, X.e0 '' {b | b.1 < a.1} ⊆ X.B.I.Lf := by
    rintro a _ ⟨b, -, rfl⟩; exact (X.vectorsInLattice.1 b).1
  have hS2 : Set.range X.e0 ⊆ X.B.I.Lf := by
    rintro _ ⟨b, rfl⟩; exact (X.vectorsInLattice.1 b).1
  have hS3 : ∀ i : Fin D.R.k, Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1} ⊆ X.B.I.Lf := by
    rintro i _ (⟨b, rfl⟩ | ⟨j, -, rfl⟩)
    · exact (X.vectorsInLattice.1 b).1
    · exact (X.vectorsInLattice.2.2 j).1
  have hK : K2cong X.B.I X.B.g X.e0 X.z0 X.bw k ↔
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → CondAt X w k := by
    have e1 := fun a => GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ (hS1 a) _ (hLf _ (X.vectorsInLattice.1 a).1)
    have e2 := GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ hS2 _ (hLf _ X.vectorsInLattice.2.1)
    have e3 := fun i => GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ (hS3 i) _ (hLf _ (X.vectorsInLattice.2.2 i).1)
    constructor
    · rintro ⟨h1, h2, h3⟩ w hw
      exact ⟨fun a => (e1 a).1 (h1 a) w hw, e2.1 h2 w hw, fun i => (e3 i).1 (h3 i) w hw⟩
    · intro H
      exact ⟨fun a => (e1 a).2 fun w hw => (H w hw).1 a, e2.2 fun w hw => (H w hw).2.1,
        fun i => (e3 i).2 fun w hw => (H w hw).2.2 i⟩
  have hgE : ((X.B.g : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    rw [X.g_eq, Nat.cast_mul]
  have hgw : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
    rintro ⟨kk, v⟩
    rw [hgE]
    fin_cases kk
    · exact Ideal.mul_mem_right _ _ (hg ⟨0, v⟩)
    · exact Ideal.mul_mem_left _ _ (hg ⟨1, v⟩)
  have hP : (∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → CondAt X w k) ↔
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), CondAt X (D.naut.plGw kv.1 kv.2) k ∧
        CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k := by
    constructor
    · intro H kv
      refine ⟨H _ (hgw kv), H _ ?_⟩
      rw [GlobalTheory.DimPartsCompare.mem_cPl, map_natCast]
      exact hgw kv
    · intro H w hw
      rw [hgE] at hw
      rcases w.isPrime.mem_or_mem hw with h0 | h1
      · obtain ⟨v, rfl | rfl⟩ := GlobalTheory.DimPartsCompare.cover 0 w h0
        · exact (H ⟨0, v⟩).1
        · exact (H ⟨0, v⟩).2
      · obtain ⟨v, rfl | rfl⟩ := GlobalTheory.DimPartsCompare.cover 1 w h1
        · exact (H ⟨1, v⟩).1
        · exact (H ⟨1, v⟩).2
  rw [hK2, hK, hP]
  exact forall_congr' fun kv => (GlobalTheory.T.symmetricPositionColumnCond_iff_congruence_conj D X h hE hg k hk kv).symm.trans (GlobalTheory.T.symmetricFrame_matrix_mem_unipotent_iff_column_span D X h hE hg k hk kv (Ns kv) (hNs kv)).symm

end GlobalTheory.Mem.GroupLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeeperLevelIffMatricesModPlaceSymmetricStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_deeperLevel_iff_matrices_mod_place_symmetric : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (k ∈ X.K2 ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) := by
  first | exact @GlobalTheory.Mem.GroupLoc.membership_iff_unipSym | exact GlobalTheory.Mem.GroupLoc.membership_iff_unipSym | (intros; apply GlobalTheory.Mem.GroupLoc.membership_iff_unipSym <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjLevelConjCharacterSymmetricLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.SymFrame.conj_symLevel : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) → (∀ kv, R.C.P.Div kv.1 (plg kv).1) → (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) → ∀ (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi R.Pg ψ0 → ∀ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π → ∀ (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), IsRedHom X red → FixRed X red b → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ c : G0g D.nd, ∀ k ∈ X.B.I.Kset, (k ∈ X.K2 ↔ reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧ ∀ hk : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H, (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hk⟩ : ℂˣ) : ℂ) = star (X.chi2 k) := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R X h eR plg iso hpin hIs hplg hDiv heG ψ0 hψ0 π hπ red b hred hfix hw
  classical
  obtain ⟨P, hP⟩ := GlobalTheory.T.symmetricFrame_reduces_to_basis_mod_place D X h hpin b (fun kv => (hfix kv).1) hw π
  obtain ⟨ψ', a, hψ'1, hchi⟩ := GlobalTheory.T.star_character_eq_prod_additive_characters_root_alt D X h hpin hw
  have hsc : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ d : Fin D.R.r → (ZMod (D.host.g kv.1))ˣ,
      ∀ u : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), u ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k →
        ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * u.val i j else 0) =
          (ψ0 (plg kv)).compAddMonoidHom (iso kv).toAddMonoidHom
            (edgeSum (symEdge D.R.rS D.R.k) ((GlobalTheory.SeeConjRead.diagGL d)⁻¹ * u * GlobalTheory.SeeConjRead.diagGL d)) := by
    intro kv
    have := Fact.mk (D.host.g_prime kv.1)
    refine GlobalTheory.SeeConjScale.scale_conj (Field.toIsField _) D.R.rS D.R.k (ψ' kv) _ (hψ'1 kv) ?_ (a kv)
    intro h1
    apply hψ0 _ (plg kv).2
    ext y
    have := DFunLike.congr_fun h1 ((iso kv).symm y)
    simpa using this
  choose d hd using hsc
  let c : G0g D.nd := fun kv => P kv * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j))
  refine ⟨c, fun k hk => ?_⟩
  let Ns : G0g D.nd := fun kv => Units.map (Matrix.reindexAlgEquiv (ZMod (D.host.g kv.1)) (ZMod (D.host.g kv.1)) π.symm).toMonoidHom
    ((P kv)⁻¹ * red k kv * P kv)
  have hNs : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) = (((((P kv)⁻¹ * red k kv * P kv) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).submatrix π π := by
    intro kv
    ext i j
    simp [Ns, Matrix.reindex_apply]
  have hMat : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2)
      (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
    intro kv
    rw [hNs kv]
    exact GlobalTheory.Mem.SymFrame.isMatIn_perm _ k _ π (GlobalTheory.T.matrixModPlace_basisChange_eq_conj D X red b hfix kv (hw kv) (P kv) _ (hP kv) k hk)
  have hval : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), reord π (R.eG (eR.symm (c⁻¹ * red k * c))) (plg kv) =
      Formalism.UG.bc ((iso kv : ZMod (D.host.g kv.1) ≃+* kP (plg kv).1) : ZMod (D.host.g kv.1) →+* kP (plg kv).1)
        ((GlobalTheory.SeeConjRead.diagGL (d kv))⁻¹ * Ns kv * GlobalTheory.SeeConjRead.diagGL (d kv)) := by
    intro kv
    have e1 : (c⁻¹ * red k * c) kv = (GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)))⁻¹ *
        ((P kv)⁻¹ * red k kv * P kv) * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)) := by
      simp only [c, Pi.mul_apply, Pi.inv_apply, mul_inv_rev, mul_assoc]
    have e2 := heG (eR.symm (c⁻¹ * red k * c)) kv
    rw [MulEquiv.apply_symm_apply, e1] at e2
    apply Units.ext
    ext i j
    have e3 : ((reord π (R.eG (eR.symm (c⁻¹ * red k * c))) (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) i j =
        ((R.eG (eR.symm (c⁻¹ * red k * c)) (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) (π i) (π j) := by
      simp [reord, Matrix.reindex_apply]
    rw [e3, e2]
    show (iso kv) ((((GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)))⁻¹ *
        ((P kv)⁻¹ * red k kv * P kv) * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) (π i) (π j)) =
      (iso kv) (((((GlobalTheory.SeeConjRead.diagGL (d kv))⁻¹ * Ns kv * GlobalTheory.SeeConjRead.diagGL (d kv)) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j)
    rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, GlobalTheory.SeeConjRead.diagGL_conj_apply, hNs kv]
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have hmemiff : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H ↔
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k := by
    show _ ∈ Subgroup.pi Set.univ _ ↔ _
    rw [Subgroup.mem_pi]
    constructor
    · intro H kv
      have h1 := H (plg kv) (Set.mem_univ _)
      rw [hval kv, GlobalTheory.Mem.SymFrame.mem_unipSym_bc] at h1
      exact (GlobalTheory.SeeConjRead.unipSym_conj_iff _ _ _ _).2 h1
    · intro H PP _
      obtain ⟨kv, rfl⟩ := plg.surjective PP
      rw [hval kv, GlobalTheory.Mem.SymFrame.mem_unipSym_bc]
      exact (GlobalTheory.SeeConjRead.unipSym_conj_iff _ _ _ _).1 (H kv)
  have hK2 := GlobalTheory.T.mem_deeperLevel_iff_matrices_mod_place_symmetric D X h hpin hw k hk Ns hMat
  refine ⟨hK2.trans hmemiff.symm, fun hx => ?_⟩
  have hU := hmemiff.1 hx
  have hk2 : k ∈ X.K2 := hK2.2 hU
  rw [hchi k hk2 Ns hMat hU]
  have hchiv : (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hx⟩ : ℂˣ) : ℂ) =
      ∏ PP : R.Pg, ψ0 PP.1 (edgeSum (symEdge D.R.rS D.R.k) (reord π (R.eG (eR.symm (c⁻¹ * red k * c))) PP)) := by
    have hp {α β ι : Type} [Monoid α] [CommMonoid β] (s : Finset ι)
        (f : ι → α →* β) (x : α) : (s.prod f) x = s.prod (fun i => f i x) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => simp [hi, ih]
    unfold PsharpSym LevelP.ofLocal at hx ⊢
    dsimp only at hx ⊢
    rw [hp, Units.coe_prod]
    rfl
  rw [hchiv]
  refine (Fintype.prod_equiv plg _ _ (fun _ => rfl)).symm.trans (Finset.prod_congr rfl fun kv _ => ?_)
  rw [hval kv, GlobalTheory.Mem.SymFrame.edgeSum_bc, hd kv _ (hU kv)]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjLevelConjCharacterSymmetricLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_level_conjCharacter_symmetricLevel : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) → (∀ kv, R.C.P.Div kv.1 (plg kv).1) → (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) → ∀ (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi R.Pg ψ0 → ∀ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π → ∀ (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), IsRedHom X red → FixRed X red b → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ c : G0g D.nd, ∀ k ∈ X.B.I.Kset, (k ∈ X.K2 ↔ reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧ ∀ hk : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H, (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hk⟩ : ℂˣ) : ℂ) = star (X.chi2 k) := by
  first | exact @GlobalTheory.Mem.SymFrame.conj_symLevel | exact GlobalTheory.Mem.SymFrame.conj_symLevel | (intros; apply GlobalTheory.Mem.SymFrame.conj_symLevel <;> assumption)
end
