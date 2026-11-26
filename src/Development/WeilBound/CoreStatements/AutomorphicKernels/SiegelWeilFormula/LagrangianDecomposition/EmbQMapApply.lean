module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartFacts

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartB
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartA
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem frQ_mul_frame {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    frQ c w * (incM F c.1)ᵀ = w := by
  change (w * (incM F (c⁻¹).1)ᵀ) * (incM F c.1)ᵀ = w
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, incM_mul_inv, Matrix.transpose_one, Matrix.mul_one]

theorem frQ_of {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (Q : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    frQ c (Q * (incM F c.1)ᵀ) = Q := by
  change (Q * (incM F c.1)ᵀ) * (incM F (c⁻¹).1)ᵀ = Q
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, incM_inv_mul, Matrix.transpose_one, Matrix.mul_one]

theorem frQ_injective {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) {w w' : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)}
    (e : frQ c w = frQ c w') : w = w' := by
  rw [← frQ_mul_frame c w, ← frQ_mul_frame c w', e]

theorem split_frame {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (Q : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    Q * (incM F c.1)ᵀ = Q.toCols₁ * (incM F c.1.toCols₁)ᵀ + Q.toCols₂ * (incM F c.1.toCols₂)ᵀ := by
  have e1 : incM F c.1 = Matrix.fromCols (incM F c.1.toCols₁) (incM F c.1.toCols₂) := by
    ext i j
    rcases j with j | j <;> rfl
  conv_lhs => rw [← Matrix.fromCols_toCols Q, e1, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows]

theorem adapted_e {m k : ℕ} {bs : Module.Basis (Fin 2) F E} {A : Spc F E m} {Y : Spc F E k} {c : GL (Fin k ⊕ Fin k) E}
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin k × Fin 2)}
    (hd : IsAdapted bs A Y c dd) (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) :
    dd.e w = (crdB bs (frQ c w).toCols₂, fun k => Bf σ A.J (frQ c w).toCols₁ (Ek bs k)) := by
  conv_lhs => rw [← frQ_mul_frame c w, split_frame]
  exact hd _ _

def embQ {R : Type*} [Zero R] {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) R) :
    Matrix (Fin m) (Fin N ⊕ Fin N) R :=
  (Matrix.fromCols Q (0 : Matrix (Fin m) (Fin 1 ⊕ Fin 1) R)).submatrix id (eB h)

theorem embQ_toCols₁ {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    (embQ h Q).toCols₁ = ext0 h Q.toCols₁ := by
  ext a i
  rcases idx_cases h (Sum.inl i) with ⟨u, hu⟩ | hu | hu
  · rcases u with u | u
    · simp only [Sum.map_inl, Sum.inl.injEq] at hu
      subst hu
      simp only [Matrix.toCols₁, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq]
      rw [show (Sum.inl (em0 h u) : Fin N ⊕ Fin N) = Sum.map (em0 h) (em0 h) (Sum.inl u) from rfl, eB_map]
      simp [ext0, em0]
    · simp at hu
  · simp only [Sum.inl.injEq] at hu
    subst hu
    simp only [Matrix.toCols₁, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq, block_index_inl_last]
    simp [ext0, i0]
  · simp at hu

theorem embQ_toCols₂ {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    (embQ h Q).toCols₂ = ext0 h Q.toCols₂ := by
  ext a i
  rcases idx_cases h (Sum.inr i) with ⟨u, hu⟩ | hu | hu
  · rcases u with u | u
    · simp at hu
    · simp only [Sum.map_inr, Sum.inr.injEq] at hu
      subst hu
      simp only [Matrix.toCols₂, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq]
      rw [show (Sum.inr (em0 h u) : Fin N ⊕ Fin N) = Sum.map (em0 h) (em0 h) (Sum.inr u) from rfl, eB_map]
      simp [ext0, em0]
  · simp at hu
  · simp only [Sum.inr.injEq] at hu
    subst hu
    simp only [Matrix.toCols₂, Matrix.of_apply, embQ, Matrix.submatrix_apply, id_eq, block_index_inr_last]
    simp [ext0, i0]

theorem emb_eq {m n N : ℕ} (h : n + 1 = N) (b : GL (Fin n ⊕ Fin n) E) (bd : GL (Fin N ⊕ Fin N) E)
    (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : emb h b bd w = embQ h (frQ b w) * (incM F bd.1)ᵀ := by
  rw [split_frame, embQ_toCols₁, embQ_toCols₂, emb]
  rfl

theorem frQ_emb {m n N : ℕ} (h : n + 1 = N) (b : GL (Fin n ⊕ Fin n) E) (bd : GL (Fin N ⊕ Fin N) E)
    (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : frQ bd (emb h b bd w) = embQ h (frQ b w) := by
  rw [emb_eq, frQ_of]

theorem embQ_mul_blk {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E))
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) : embQ h Q * (blk h M 1)ᵀ = embQ h (Q * Mᵀ) := by
  rw [blk_transpose]
  simp only [embQ, blk]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

theorem frQ_mul_mat {m k : ℕ} {Y : Spc F E k} (c : GL (Fin k ⊕ Fin k) E) (x : G2 σ Y)
    (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) : frQ c (w * (x.1.1)ᵀ) = frQ c w * (inFrame c x)ᵀ := by
  have e : x.1.1 = incM F c.1 * inFrame c x * incM F (c⁻¹).1 := by
    rw [inFrame_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      incM_mul_inv, Matrix.mul_one]
  rw [frQ, frQ, e]
  simp only [Matrix.transpose_mul, ← Matrix.mul_assoc]
  change w * (incM F (c⁻¹).1)ᵀ * (inFrame c x)ᵀ * (incM F c.1)ᵀ * (incM F (c⁻¹).1)ᵀ =
    w * (incM F (c⁻¹).1)ᵀ * (inFrame c x)ᵀ
  rw [Matrix.mul_assoc _ (incM F c.1)ᵀ, ← Matrix.transpose_mul, incM_inv_mul, Matrix.transpose_one, Matrix.mul_one]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_mul_single' {m k : ℕ} (A : Matrix (Fin k) (Fin m) (AE F E)) (a : Fin m) (c : Fin k) (z : AE F E) :
    (A * Matrix.single a c z).trace = A c a * z := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem map_single' {m k : ℕ} (a : Fin m) (c : Fin k) (z : AE F E) :
    (Matrix.single a c z).map (cA σ) = Matrix.single a c (cA σ z) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem Bf_Ek {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (q : Fin m × Fin k × Fin 2) : Bf σ J X (Ek bs q) =
      Algebra.trace (AF F) (AE F E) ((∑ p, X p q.2.1 * incM F J p q.1) * cA σ ((1 : AF F) ⊗ₜ[F] bs q.2.2)) := by
  unfold Bf Ek
  rw [map_single', trace_mul_single']
  simp [Matrix.mul_apply, Matrix.transpose_apply]

theorem Bf_col {m k k' : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (X' : Mx F E m k') (a : Fin m) (c : Fin k) (c' : Fin k') (t : Fin 2) (hX : ∀ p, X p c = X' p c') :
    Bf σ J X (Ek bs (a, c, t)) = Bf σ J X' (Ek bs (a, c', t)) := by
  simp only [Bf_Ek, hX]

theorem Bf_zero_col {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (a : Fin m) (c : Fin k) (t : Fin 2) (hX : ∀ p, X p c = 0) : Bf σ J X (Ek bs (a, c, t)) = 0 := by
  rw [Bf_Ek]
  simp [hX]

theorem crdB_col {m k k' : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m k) (X' : Mx F E m k') (a : Fin m)
    (c : Fin k) (c' : Fin k') (t : Fin 2) (hX : X a c = X' a c') : crdB bs X (a, c, t) = crdB bs X' (a, c', t) := by
  simp only [crdB, hX]

theorem crdB_zero_col {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m k) (a : Fin m) (c : Fin k) (t : Fin 2)
    (hX : X a c = 0) : crdB bs X (a, c, t) = 0 := by
  simp [crdB, hX]

theorem extend_zero_embedded_column {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) (p : Fin m) (j : Fin n) : ext0 h X p (em0 h j) = X p j := by
  simp [ext0, em0]

theorem extend_zero_last_column {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) (p : Fin m) : ext0 h X p (i0 h) = 0 := by
  simp [ext0, i0]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem embQ_mul_left {m n N : ℕ} (h : n + 1 = N) (L : Matrix (Fin m) (Fin m) (AE F E))
    (Q : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : L * embQ h Q = embQ h (L * Q) := by
  ext a c
  simp only [embQ, Matrix.mul_apply, Matrix.submatrix_apply, id]
  rcases eB h c with x | x <;> simp [Matrix.mul_apply]

theorem embQ_map_apply {R : Type*} [Zero R] {m n N : ℕ} (h : n + 1 = N) (Q : Matrix (Fin m) (Fin n ⊕ Fin n) R)
    (a : Fin m) (v : Fin n ⊕ Fin n) : embQ h Q a (Sum.map (em0 h) (em0 h) v) = Q a v := by
  simp [embQ, eB_map]

theorem frQ_left {m k : ℕ} (c : GL (Fin k ⊕ Fin k) E) (L : Matrix (Fin m) (Fin m) (AE F E))
    (w : Matrix (Fin m) (Fin k ⊕ Fin k) (AE F E)) : frQ c (L * w) = L * frQ c w := by
  rw [frQ, frQ, Matrix.mul_assoc]

theorem chartFacts : ChartFacts := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' h0 h'
  have rdE : ∀ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w = ((dd0.e w).1 ∘ eK d.m h, (dd0.e w).2 ∘ eK d.m h) :=
    fun w => by rw [GlobalTheory.TowU.reindexD_e, Equiv.symm_symm]
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  refine ⟨fun w' => ?_, fun u v => ⟨_, LinearEquiv.apply_symm_apply _ _⟩, fun g w H1 H2 => ?_, fun g w' => ?_,
    fun u w' => ?_⟩
  ·
    rw [rdE, adapted_e h0, frQ_emb, embQ_toCols₁, embQ_toCols₂, adapted_e h']
    refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact crdB_col _ _ _ a _ c t (extend_zero_embedded_column h _ a c)
      · exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact Bf_col _ _ _ _ a _ c t (fun p => extend_zero_embedded_column h _ p c)
      · exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
  ·
    set Q := frQ d.b w with hQdef
    set Q' := Q.submatrix id (Sum.map (em0 h) (em0 h)) with hQ'def
    have hw := adapted_e h0 w
    have hz : dd0.e (embQ h Q' * (incM F d.b.1)ᵀ) = 0 := by
      rw [adapted_e h0, frQ_of, embQ_toCols₁, embQ_toCols₂]
      refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H1 (a, c', t)
          rw [rdE, hw] at e3
          refine (crdB_col _ _ _ a _ _ t ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H2 (a, c', t)
          rw [rdE, hw] at e3
          refine (Bf_col _ _ _ _ a _ _ t fun p => ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
    have hQ' : embQ h Q' = 0 := by
      have := (LinearEquiv.map_eq_zero_iff dd0.e).1 hz
      rw [← frQ_of d.b (embQ h Q'), this, frQ, Matrix.zero_mul]
    have hQv : ∀ a v', Q a (Sum.map (em0 h) (em0 h) v') = 0 := fun a v' => by
      have := congrFun (congrFun hQ' a) (Sum.map (em0 h) (em0 h) v')
      rwa [embQ_map_apply] at this
    apply frQ_injective d.b
    show frQ d.b (w * ((j g).1.1)ᵀ) = frQ d.b w
    rw [frQ_mul_mat, hfr, ← hQdef]
    ext a u
    rw [Matrix.mul_apply]
    have hterm : ∀ v, Q a v * (blk h (inFrame b g) 1)ᵀ v u = Q a v * (1 : Matrix (Fin d.n ⊕ Fin d.n) _ (AE F E)) u v := by
      intro v
      rcases idx_cases h v with ⟨v', rfl⟩ | hv | hv
      · rw [hQv, zero_mul, zero_mul]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inl rfl) u).2]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inr rfl) u).2]
    rw [Finset.sum_congr rfl fun v _ => hterm v]
    simp [Matrix.one_apply]
  ·
    apply frQ_injective d.b
    show frQ d.b (emb h b d.b w' * ((j g).1.1)ᵀ) = frQ d.b (emb h b d.b (w' * (g.1.1)ᵀ))
    rw [frQ_mul_mat, frQ_emb, frQ_emb, frQ_mul_mat, hfr, embQ_mul_blk]
  ·
    rw [emb_eq, emb_eq, frQ_left, ← embQ_mul_left, Matrix.mul_assoc]

end PositivityTheory.SiegelWeilFormula.Ald

end
