module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinObject
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickPrincipalObjectsIsoUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepPrincipalSiegelAdjointOrderAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusIdempotentImageSiegel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinTrickFamilySiegelKernelKilled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinOrderSpanningFamilyPosDefMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinOrderSpanningFamilyPosDefMatrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam.SpanFam

def colL (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 (quat d)ᵀ 0 ((d : ℤ) • 1)

def colR (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 0 (quat d) 1

theorem colL_mul_transpose {d : ℕ} (hd : 0 < d) : colL d * (colL d)ᵀ = (d : ℤ) • form d := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [colL, form, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul]
  congr 1
  · rw [transpose_transpose, quat_transpose_mul, h1]; simp [sub_smul, smul_smul]
  · simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, transpose_zero, transpose_smul, transpose_one]
  · simp
  · simp [smul_smul]

theorem colR_mul_transpose {d : ℕ} (hd : 0 < d) : colR d * (colR d)ᵀ = form d := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [colR, form, fromBlocks_transpose, fromBlocks_multiply]
  congr 1
  · simp
  · simp
  · simp
  · rw [quat_mul_transpose, h1]; simp [sub_smul]

def col (d : ℕ) (q : Fin 4 ⊕ Fin 4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  Sum.elim (fun _ => colL d) (fun _ => colR d) q

def famM (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  col d t.2 * single t.1 t.2 1

theorem famM_apply (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) (p q : Fin 4 ⊕ Fin 4) :
    famM d t p q = if q = t.2 then col d t.2 p t.1 else 0 := by
  unfold famM
  split_ifs with h
  · subst h; simp
  · exact mul_single_apply_of_ne _ _ _ _ _ h _

theorem famM_mem (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : famM d t ∈ ord d := by
  intro i j
  rw [famM_apply]
  obtain ⟨k, q⟩ := t
  split_ifs with h
  · simp only at h
    subst h
    rcases k with k | k
    · simp only [col, colL, Sum.elim_inl, fromBlocks_apply₂₁, Matrix.zero_apply]; exact dvd_zero _
    · simp only [col, colL, Sum.elim_inl, fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
  · exact dvd_zero _

theorem famM_form_transpose {d : ℕ} (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) :
    famM d t * form d * (famM d t)ᵀ = col d t.2 * single t.1 t.1 (form d t.2 t.2) * (col d t.2)ᵀ := by
  calc famM d t * form d * (famM d t)ᵀ
      = col d t.2 * (single t.1 t.2 1 * form d * single t.2 t.1 1) * (col d t.2)ᵀ := by
        simp only [famM, transpose_mul, transpose_single, Matrix.mul_assoc]
    _ = _ := by rw [single_mul_mul_single, _root_.one_mul, _root_.mul_one]

theorem sum_single_diag' (c : ℤ) : ∑ k : Fin 4 ⊕ Fin 4, single k k c = c • (1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) := by
  ext a b
  rw [Matrix.sum_apply]
  by_cases h : a = b
  · subst h; simp [single_apply]
  · rw [Finset.sum_eq_zero (fun k _ => by rw [single_apply]; exact if_neg (fun hk => h (hk.1.symm.trans hk.2)))]
    simp [Matrix.one_apply, h]

theorem sum_famM {d : ℕ} (hd : 0 < d) :
    ∑ t, famM d t * form d * (famM d t)ᵀ = ((8 * d : ℕ) : ℤ) • form d := by
  simp_rw [famM_form_transpose]
  rw [Fintype.sum_prod_type_right]
  have hq : ∀ q : Fin 4 ⊕ Fin 4, ∑ k : Fin 4 ⊕ Fin 4, col d q * single k k (form d q q) * (col d q)ᵀ
      = form d q q • (col d q * (col d q)ᵀ) := by
    intro q
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_single_diag', Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
  simp_rw [hq]
  rw [Fintype.sum_sum_type]
  simp only [col, Sum.elim_inl, Sum.elim_inr, colL_mul_transpose hd, colR_mul_transpose hd, smul_smul]
  have e1 : ∀ j : Fin 4, form d (Sum.inl j) (Sum.inl j) = 1 := fun j => by simp [form]
  have e2 : ∀ j : Fin 4, form d (Sum.inr j) (Sum.inr j) = d := fun j => by
    simp only [form, fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one]
  simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← add_smul, smul_smul]
  rw [_root_.one_mul, ← add_nsmul, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
  congr 1

def fam (d : ℕ) (t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4)) : ord d := ⟨famM d t, famM_mem d t⟩

def coef (d : ℕ) (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : (Fin 4 ⊕ Fin 4) → (Fin 4 ⊕ Fin 4) → ℤ
  | Sum.inr m, Sum.inl j => N (Sum.inr m) (Sum.inl j) / d
  | Sum.inl m, Sum.inl j => N (Sum.inl m) (Sum.inl j) - ∑ s, quat d s m * (N (Sum.inr s) (Sum.inl j) / d)
  | Sum.inl m, Sum.inr j => N (Sum.inl m) (Sum.inr j)
  | Sum.inr m, Sum.inr j => N (Sum.inr m) (Sum.inr j) - ∑ s, quat d m s * N (Sum.inl s) (Sum.inr j)

theorem sum_coef_famM {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ} (hN : N ∈ ord d) (p q : Fin 4 ⊕ Fin 4) :
    ∑ t : (Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4), coef d N t.1 t.2 * famM d t p q = N p q := by
  simp only [famM_apply, mul_ite, mul_zero]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hdiv : ∀ m j, (d : ℤ) * (N (Sum.inr m) (Sum.inl j) / d) = N (Sum.inr m) (Sum.inl j) :=
    fun m j => Int.mul_ediv_cancel' (hN m j)
  rcases q with j | j <;> rcases p with m | m <;>
    simp [Fintype.sum_sum_type, col, colL, colR, coef, Matrix.one_apply, Matrix.smul_one_eq_diagonal, Matrix.diagonal_apply, hdiv, mul_comm]
  all_goals done

end GlobalTheory.ZarhinFam.SpanFam

namespace GlobalTheory.ZarhinFam.SpanFam

theorem span_fam_eq_top {d : ℕ} : Submodule.span ℤ (Set.range (fam d)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  rintro ⟨N, hN⟩
  have hx : (⟨N, hN⟩ : ord d) = ∑ t, coef d N t.1 t.2 • fam d t := by
    apply Subtype.ext
    ext p q
    change N p q = ((∑ t, coef d N t.1 t.2 • fam d t : ord d) : Matrix _ _ ℤ) p q
    rw [← sum_coef_famM hN p q]
    simp only [fam, AddSubmonoidClass.coe_finsetSum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [AddSubgroupClass.coe_zsmul, Matrix.smul_apply, smul_eq_mul]
  rw [hx]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem sum_fam_mul_bar {d : ℕ} (hd : 0 < d) :
    ∑ t, fam d t * bar d (fam d t) = ((8 * d : ℕ) : ord d) := by
  apply Subtype.ext
  have h : ∑ t, famM d t * form d * (famM d t)ᵀ * formInv d = ((8 * d : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) := by
    rw [← Finset.sum_mul, sum_famM hd, Matrix.smul_mul, form_mul_formInv hd]
  simp only [fam, bar_coe, Subring.coe_mul, Matrix.mul_assoc] at h ⊢
  simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, bar_coe, Matrix.mul_assoc]
  rw [h]
  simp only [Subring.coe_natCast]
  rw [Nat.cast_smul_eq_nsmul ℤ, nsmul_one]

end GlobalTheory.ZarhinFam.SpanFam

namespace GlobalTheory.ZarhinFam

theorem exists_spanning_family_posDef :
    ∀ (d : ℕ), 0 < d → ∃ (r : ℕ) (eO : Fin r → GlobalTheory.ZarhinFam.ord d) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * GlobalTheory.ZarhinFam.bar d (eO i)) = (d₀ : GlobalTheory.ZarhinFam.ord d) := by
  intro d hd
  let e := Fintype.equivFin ((Fin 4 ⊕ Fin 4) × (Fin 4 ⊕ Fin 4))
  refine ⟨_, fun i => SpanFam.fam d (e.symm i), 1, 8 * d, ?_, ?_, by omega, ?_⟩
  · have hc : (fun i => SpanFam.fam d (e.symm i)) = SpanFam.fam d ∘ e.symm := rfl
    rw [hc, e.symm.surjective.range_comp]
    exact SpanFam.span_fam_eq_top
  · rw [transpose_one, Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one]
    exact Matrix.PosDef.one.add Matrix.PosDef.one
  · simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← SpanFam.sum_fam_mul_bar hd]
    exact Equiv.sum_comp e.symm (fun t => SpanFam.fam d t * bar d (SpanFam.fam d t))

end GlobalTheory.ZarhinFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinOrderSpanningFamilyPosDefMatrixStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhin_order_spanning_family_posDef_matrix : ∀ (d : ℕ), 0 < d → ∃ (r : ℕ) (eO : Fin r → GlobalTheory.ZarhinFam.ord d) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * GlobalTheory.ZarhinFam.bar d (eO i)) = (d₀ : GlobalTheory.ZarhinFam.ord d) := by
  first | (exact @GlobalTheory.ZarhinFam.exists_spanning_family_posDef) | (exact GlobalTheory.ZarhinFam.exists_spanning_family_posDef) | (intros; apply GlobalTheory.ZarhinFam.exists_spanning_family_posDef  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinTrickFamilySiegelKernelKilled
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (O : Type) (_ : Ring O) (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), (∀ a b, bar (a + b) = bar a + bar b) ∧ Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) ∧ e * e = e ∧ (∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P bar act ∧ ZRel e jl o κ c z act) ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : O → (z₁.A ⟶ z₁.A)) (act₂ : O → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P bar act₁ → Adj z₂.A z₂.P bar act₂ → ZRel e jl o κ c z₁ act₁ → ZRel e jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  intro h M d hh hM hMo hd hcop
  obtain ⟨r, eO, W, d₀, hspan, hW, hd₀, hid⟩ := GlobalTheory.T.exists_zarhin_order_spanning_family_posDef_matrix d hd
  obtain ⟨jl, n, o, κ, hex⟩ := GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy h M d hh hM hMo hd hcop
  exact ⟨GlobalTheory.ZarhinFam.ord d, inferInstance, GlobalTheory.ZarhinFam.bar d, r, eO, W, d₀, GlobalTheory.ZarhinFam.idem d, jl, n, o, κ,
    GlobalTheory.ZarhinFam.bar_add d, hspan, hW, hd₀, hid, GlobalTheory.ZarhinFam.idem_mul_self d, hex,
    fun S t c z₁ z₂ act₁ act₂ => GlobalTheory.T.zarhinTrick_principal_objects_iso_unique h M d hh hM hMo hd hcop jl n o κ S t c z₁ z₂ act₁ act₂⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinTrickFamilySiegelKernelKilledStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhinTrick_family_siegel_kernelKilled : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (O : Type) (_ : Ring O) (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), (∀ a b, bar (a + b) = bar a + bar b) ∧ Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) ∧ e * e = e ∧ (∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P bar act ∧ ZRel e jl o κ c z act) ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : O → (z₁.A ⟶ z₁.A)) (act₂ : O → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P bar act₁ → Adj z₂.A z₂.P bar act₂ → ZRel e jl o κ c z₁ act₁ → ZRel e jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  first | (exact @GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy) | (exact GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy) | (intros; apply GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyIdempotentImageOpenLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackOfIdempotentImagesAndActionPullbac
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackOfIdempotentImagesAndActionPullbac
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.UPel.HT

theorem siegPB_of_zRel_actPB : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O)
    (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B)
    (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A))
    (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)),
    ActPB w₂ act₂ w₁ act₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ → SiegPB c₂ c₁ y := by
  intro h h' M B _ ζ O _ e jl n o κ S₁ S₂ s₁ s₂ y c₁ w₁ act₁ c₂ w₂ act₂ hA hZ₁ hZ₂
  obtain ⟨ψ, ψ₂, hψ, sψ, lψ, vψ, aψ⟩ := hA
  obtain ⟨inc₁, pr₁, mi₁, mp₁, ip₁, pi₁, L₁, V₁, -⟩ := hZ₁
  obtain ⟨inc₂, pr₂, mi₂, mp₂, ip₂, pi₂, L₂, V₂, -⟩ := hZ₂
  have ip₁' : inc₁.left ≫ pr₁.left = 𝟙 _ := by rw [← Over.comp_left, ip₁]; rfl
  have ip₂' : inc₂.left ≫ pr₂.left = 𝟙 _ := by rw [← Over.comp_left, ip₂]; rfl
  have pi₁' : pr₁.left ≫ inc₁.left = (act₁ e).left := by rw [← Over.comp_left, pi₁]
  have pi₂' : pr₂.left ≫ inc₂.left = (act₂ e).left := by rw [← Over.comp_left, pi₂]
  have K0 : inc₂.left ≫ (act₂ e).left = inc₂.left := by
    rw [← pi₂', ← Category.assoc, ip₂', Category.id_comp]
  obtain ⟨φ, hφ⟩ : ∃ φ : c₂.A.left ⟶ c₁.A.left, φ = inc₂.left ≫ ψ ≫ pr₁.left := ⟨_, rfl⟩
  have K1 : φ ≫ inc₁.left = inc₂.left ≫ ψ := by
    rw [hφ, Category.assoc, Category.assoc, pi₁', ← aψ e, ← Category.assoc, K0]
  have K2 : pr₂.left ≫ φ = ψ ≫ pr₁.left := by
    have : (act₁ e).left ≫ pr₁.left = pr₁.left := by
      rw [← pi₁', Category.assoc, ip₁', Category.comp_id]
    rw [hφ, ← Category.assoc, ← Category.assoc, pi₂', aψ e, Category.assoc, this]
  have hw : φ ≫ c₁.A.hom = c₂.A.hom ≫ y := by
    rw [hφ, Category.assoc, Category.assoc, Over.w pr₁, hψ.1.w, ← Category.assoc, Over.w inc₂]
  have hpb : IsPullback φ c₂.A.hom c₁.A.hom y := by
    let lft : ∀ s : PullbackCone c₁.A.hom y, s.pt ⟶ c₂.A.left := fun s =>
      hψ.1.lift (s.fst ≫ inc₁.left) s.snd (by rw [Category.assoc, Over.w inc₁]; exact s.condition) ≫ pr₂.left
    refine IsPullback.of_isLimit (c := PullbackCone.mk φ c₂.A.hom hw)
      (PullbackCone.IsLimit.mk hw lft (fun s => ?_) (fun s => ?_) (fun s m hm1 hm2 => ?_))
    · simp only [lft]
      rw [Category.assoc, K2, ← Category.assoc, hψ.1.lift_fst, Category.assoc, ip₁', Category.comp_id]
    · simp only [lft]
      rw [Category.assoc, Over.w pr₂, hψ.1.lift_snd]
    · have e₁ : m ≫ inc₂.left = hψ.1.lift (s.fst ≫ inc₁.left) s.snd
          (by rw [Category.assoc, Over.w inc₁]; exact s.condition) := by
        apply hψ.1.hom_ext
        · rw [hψ.1.lift_fst, Category.assoc, ← K1, ← Category.assoc, hm1]
        · rw [hψ.1.lift_snd, Category.assoc, Over.w inc₂, hm2]
      calc m = m ≫ inc₂.left ≫ pr₂.left := by rw [ip₂', Category.comp_id]
        _ = lft s := by rw [← Category.assoc, e₁]
  have hmul : ∀ (T : Over S₂) (x x' : T ⟶ c₂.A) (x₀ x₀' : Over.mk (T.hom ≫ y) ⟶ c₁.A),
      x₀.left = x.left ≫ φ → x₀'.left = x'.left ≫ φ → (x₀ * x₀').left = (x * x').left ≫ φ := by
    intro T x x' x₀ x₀' hx hx'
    haveI := mi₂
    haveI := mp₁
    have wx : ∀ z : T ⟶ c₂.A, ((z ≫ inc₂).left ≫ ψ) ≫ w₁.A.hom = (Over.mk (T.hom ≫ y)).hom := fun z => by
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w (z ≫ inc₂)]; rfl
    let X₀ : Over.mk (T.hom ≫ y) ⟶ w₁.A := Over.homMk ((x ≫ inc₂).left ≫ ψ) (wx x)
    let X₀' : Over.mk (T.hom ≫ y) ⟶ w₁.A := Over.homMk ((x' ≫ inc₂).left ≫ ψ) (wx x')
    have m := hψ.2 T (x ≫ inc₂) (x' ≫ inc₂) X₀ X₀' rfl rfl
    rw [← mul_comp] at m
    have e₀ : X₀ ≫ pr₁ = x₀ := by
      ext1
      rw [Over.comp_left, hx, hφ]
      show ((x ≫ inc₂).left ≫ ψ) ≫ pr₁.left = _
      rw [Over.comp_left]; simp only [Category.assoc]
    have e₀' : X₀' ≫ pr₁ = x₀' := by
      ext1
      rw [Over.comp_left, hx', hφ]
      show ((x' ≫ inc₂).left ≫ ψ) ≫ pr₁.left = _
      rw [Over.comp_left]; simp only [Category.assoc]
    rw [← e₀, ← e₀', ← mul_comp, Over.comp_left, m, hφ, Over.comp_left, Category.assoc, Category.assoc]
  have sq := ActUnr.sqMap_fst hw
  have sq' := ActUnr.sqMap_snd hw
  refine ⟨φ, ActUnr.sqMap hw, ⟨hpb, hmul⟩, ⟨sq, sq'⟩, ?_, fun a => ?_⟩
  · have f₁ : (inc₁ ⊗ₘ inc₁).left ≫ (fst w₁.A w₁.A).left = (fst c₁.A c₁.A).left ≫ inc₁.left := by
      rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    have g₁ : (inc₁ ⊗ₘ inc₁).left ≫ (snd w₁.A w₁.A).left = (snd c₁.A c₁.A).left ≫ inc₁.left := by
      rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    have f₂ : (inc₂ ⊗ₘ inc₂).left ≫ (fst w₂.A w₂.A).left = (fst c₂.A c₂.A).left ≫ inc₂.left := by
      rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    have g₂ : (inc₂ ⊗ₘ inc₂).left ≫ (snd w₂.A w₂.A).left = (snd c₂.A c₂.A).left ≫ inc₂.left := by
      rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    have E : (inc₂ ⊗ₘ inc₂).left ≫ ψ₂ = ActUnr.sqMap hw ≫ (inc₁ ⊗ₘ inc₁).left := by
      apply ActUnr.left_hom_ext
      · rw [Category.assoc, sψ.1, ← Category.assoc, f₂]
        simp only [Category.assoc]
        rw [f₁]
        rw [← Category.assoc (ActUnr.sqMap hw), sq, Category.assoc, K1]
      · rw [Category.assoc, sψ.2, ← Category.assoc, g₂]
        simp only [Category.assoc]
        rw [g₁]
        rw [← Category.assoc (ActUnr.sqMap hw), sq', Category.assoc, K1]
    have l₂ := GlobalTheory.TChart.AbLevel.lbIso_comp w₁.isLB w₂.isLB c₂.isLB lψ L₂
    have hN := pull_isLB c₁.isLB (ActUnr.sqMap hw)
    have l₁ := GlobalTheory.TChart.AbLevel.lbIso_comp w₁.isLB c₁.isLB hN L₁ ((GlobalTheory.CechPic.cls_eq_iff hN hN).1 rfl)
    rw [E] at l₂
    exact LBIso.trans c₂.isLB (pull_isLB w₁.isLB _) hN l₂ (LBIso.symm l₁)
  · calc (c₂.lev a).left ≫ φ = (c₂.lev a ≫ inc₂).left ≫ ψ ≫ pr₁.left := by
          rw [hφ, Over.comp_left, Category.assoc]
      _ = (w₂.lev (jl a)).left ≫ ψ ≫ pr₁.left := by rw [V₂ a]
      _ = y ≫ (w₁.lev (jl a)).left ≫ pr₁.left := by rw [← Category.assoc, vψ, Category.assoc]
      _ = y ≫ (c₁.lev a).left := by rw [← V₁ a, Over.comp_left, Category.assoc, ip₁', Category.comp_id]

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackOfIdempotentImagesAndActionPullbacStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_pullback_of_idempotent_images_and_action_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ → SiegPB c₂ c₁ y := by
  first | (exact @GlobalTheory.UPel.HT.siegPB_of_zRel_actPB) | (exact GlobalTheory.UPel.HT.siegPB_of_zRel_actPB) | (intros; apply GlobalTheory.UPel.HT.siegPB_of_zRel_actPB  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackWithActionCancellation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackWithActionCancellation
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem actPB_cancel : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (S S₁ S₂ : Scheme.{0})
    (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)) (g₁ : S₁ ⟶ S)
    (y : S₂ ⟶ S₁) (w₁ : SiegPre h M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (w₂ : SiegPre h M ζ s₂)
    (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₁ act₁ z act g₁ → ActPB w₂ act₂ z act (y ≫ g₁) → ActPB w₂ act₂ w₁ act₁ y := by
  intro h M B _ ζ O _ S S₁ S₂ s s₁ s₂ z act g₁ y w₁ act₁ w₂ act₂ m₁ m₂
  obtain ⟨φ₁, φ₁₂, h1, s1, p1, l1, a1⟩ := m₁
  obtain ⟨φ₂, φ₂₂, h2, s2, p2, l2, a2⟩ := m₂
  have hw : φ₂ ≫ z.A.hom = (w₂.A.hom ≫ y) ≫ g₁ := by rw [h2.1.w, Category.assoc]
  let ψ : w₂.A.left ⟶ w₁.A.left := h1.1.lift φ₂ (w₂.A.hom ≫ y) hw
  have hψ₁ : ψ ≫ φ₁ = φ₂ := h1.1.lift_fst _ _ _
  have hψ : ψ ≫ w₁.A.hom = w₂.A.hom ≫ y := h1.1.lift_snd _ _ _
  let ψ₂ : (G2 w₂.A).left ⟶ (G2 w₁.A).left := ActUnr.sqMap hψ
  have sψ : IsSquare ψ ψ₂ := ⟨ActUnr.sqMap_fst hψ, ActUnr.sqMap_snd hψ⟩
  have e₂ : φ₂₂ = ψ₂ ≫ φ₁₂ := by
    apply ActUnr.left_hom_ext
    · rw [s2.1, Category.assoc, s1.1, ← Category.assoc, sψ.1, Category.assoc, hψ₁]
    · rw [s2.2, Category.assoc, s1.2, ← Category.assoc, sψ.2, Category.assoc, hψ₁]
  have n : IsGrpPullback w₂.A z.A (y ≫ g₁) (ψ ≫ φ₁) := by rw [hψ₁]; exact h2
  refine ⟨ψ, ψ₂, IsGrpPullback.cancel h1 n hψ, sψ, ?_, fun a => ?_, fun o => ?_⟩
  · refine LBIso.trans w₂.isLB (pull_isLB z.isLB _) (pull_isLB w₁.isLB _) p2 ?_
    refine LBIso.trans (pull_isLB z.isLB _) (pull_isLB (pull_isLB z.isLB _) _) (pull_isLB w₁.isLB _)
      (GlobalTheory.GenSpread.lbIso_pull_pull z.isLB ψ₂ e₂) ?_
    exact GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm p1) ψ₂
  · apply h1.1.hom_ext
    · rw [Category.assoc, hψ₁, l2 a, Category.assoc, Category.assoc, l1 a]
    · rw [Category.assoc, hψ, ← Category.assoc, Over.w (w₂.lev a), Category.assoc, Over.w (w₁.lev a)]
      simp
  · apply h1.1.hom_ext
    · rw [Category.assoc, hψ₁, a2 o, Category.assoc, a1 o, ← Category.assoc, hψ₁]
    · rw [Category.assoc, hψ, ← Category.assoc, Over.w (act₂ o), Category.assoc, Over.w (act₁ o), hψ]

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackWithActionCancellationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_pullback_with_action_cancellation : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (S S₁ S₂ : Scheme.{0}) (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)) (g₁ : S₁ ⟶ S) (y : S₂ ⟶ S₁) (w₁ : SiegPre h M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (w₂ : SiegPre h M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₁ act₁ z act g₁ → ActPB w₂ act₂ z act (y ≫ g₁) → ActPB w₂ act₂ w₁ act₁ y := by
  first | exact @GlobalTheory.UPel.HT.actPB_cancel | exact GlobalTheory.UPel.HT.actPB_cancel | (intros; apply GlobalTheory.UPel.HT.actPB_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelAdjointActionPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelAdjointActionPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UPel.HT

theorem siegPre_actPB_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O)
    (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s)
    (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act →
    ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧
      Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  intro h M B _ ζ O _ bar S S' s s' f z act hs hz hR hA
  obtain ⟨⟨w, φ, φ₂, hφ, hsq, hP, hlev⟩, hpr⟩ := GlobalTheory.siegPre_pullback h M B ζ S S' s s' f z hs
  have hwP : w.Principal := hpr w ⟨φ, φ₂, hφ, hsq, hP, hlev⟩ hz
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hφ (isGrpPullback_pullback z.A f)
  haveI := he
  have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  let actw : O → (w.A ⟶ w.A) := fun a => e.hom ≫ (Over.pullback f).map (act a) ≫ e.inv
  have hv : ∀ a, (actw a).left ≫ φ = φ ≫ (act a).left := fun a => by
    have hm : ((Over.pullback f).map (act a)).left ≫ pullback.fst z.A.hom f =
        pullback.fst z.A.hom f ≫ (act a).left := pullback.lift_fst _ _ _
    rw [← heφ]
    simp only [actw, Over.comp_left, Category.assoc]
    rw [reassoc_of% hie, hm]
  have hRw : IsRAct w.A actw := ActUnr.isRAct_conj e _ (ActUnr.isRAct_pullback f z.A act hR)
  have lf : ∀ {T : Scheme.{0}} {X Y : Over T} (x y : X ⟶ Y), (lift x y).left ≫ (fst Y Y).left = x.left :=
    fun x y => by rw [← Over.comp_left, lift_fst]
  have ls : ∀ {T : Scheme.{0}} {X Y : Over T} (x y : X ⟶ Y), (lift x y).left ≫ (snd Y Y).left = y.left :=
    fun x y => by rw [← Over.comp_left, lift_snd]
  have hc1 : ∀ a, (lift (fst w.A w.A ≫ actw a) (snd w.A w.A)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst z.A z.A ≫ act a) (snd z.A z.A)).left := fun a => by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, hsq.1, ← Category.assoc, lf, Category.assoc, lf, Over.comp_left _ _ _ (fst w.A w.A) (actw a),
        Over.comp_left _ _ _ (fst z.A z.A) (act a), Category.assoc, hv, ← Category.assoc, ← hsq.1, Category.assoc]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ls, Category.assoc, ls, hsq.2]
  have hc2 : ∀ a, (lift (fst w.A w.A) (snd w.A w.A ≫ actw (bar a))).left ≫ φ₂ =
      φ₂ ≫ (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar a))).left := fun a => by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, hsq.1, ← Category.assoc, lf, Category.assoc, lf, hsq.1]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ls, Category.assoc, ls, Over.comp_left _ _ _ (snd w.A w.A) (actw (bar a)),
        Over.comp_left _ _ _ (snd z.A z.A) (act (bar a)), Category.assoc, hv, ← Category.assoc, ← hsq.2, Category.assoc]
  have hadj : Adj w.A w.P bar actw := fun a => by
    have h1 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP _ (hc1 a).symm
    have h2 := GlobalTheory.GenSpread.lbIso_pull_comp (L := z.P) (M := z.P) φ₂ rfl rfl (hA a)
    have h3 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP _ (hc2 a).symm
    exact LBIso.trans (pull_isLB w.isLB _) (pull_isLB z.isLB _) (pull_isLB w.isLB _)
      (LBIso.trans (pull_isLB w.isLB _) (pull_isLB z.isLB _) (pull_isLB z.isLB _) h1 h2) h3.symm
  exact ⟨w, actw, hwP, hRw, hadj, φ, φ₂, hφ, hsq, hP, hlev, hv⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelAdjointActionPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_siegel_adjoint_action_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O) (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  first | (exact @GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (exact GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (intros; apply GlobalTheory.UPel.HT.siegPre_actPB_pullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageRelationOfPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageRelationOfPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.UPel.HT

theorem zRel_of_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → SiegPB c₂ c₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ := by
  intro h h' M B _ ζ O _ e jl n o κ S₁ S₂ s₁ s₂ y c₁ w₁ act₁ c₂ w₂ act₂ hA hS hZ
  obtain ⟨ψ, ψ₂, hψ, sqψ, hwP, hwl, hact⟩ := hA
  obtain ⟨φ, φ₂, hφ, sqφ, hcP, hcl⟩ := hS
  obtain ⟨inc₁, pr₁, mi₁, mp₁, ip₁, pi₁, hP₁, hl₁, hz₁⟩ := hZ
  haveI := mi₁
  haveI := mp₁
  have wi : (φ ≫ inc₁.left) ≫ w₁.A.hom = c₂.A.hom ≫ y := by
    rw [Category.assoc, Over.w inc₁]; exact hφ.1.w
  let inc₂ : c₂.A ⟶ w₂.A := Over.homMk (hψ.1.lift (φ ≫ inc₁.left) c₂.A.hom wi) (hψ.1.lift_snd _ _ _)
  have inc₂_l : inc₂.left ≫ ψ = φ ≫ inc₁.left := hψ.1.lift_fst _ _ _
  have wp : (ψ ≫ pr₁.left) ≫ c₁.A.hom = w₂.A.hom ≫ y := by
    rw [Category.assoc, Over.w pr₁]; exact hψ.1.w
  let pr₂ : w₂.A ⟶ c₂.A := Over.homMk (hφ.1.lift (ψ ≫ pr₁.left) w₂.A.hom wp) (hφ.1.lift_snd _ _ _)
  have pr₂_l : pr₂.left ≫ φ = ψ ≫ pr₁.left := hφ.1.lift_fst _ _ _
  have extW : ∀ {T : Over S₂} (a b : T ⟶ w₂.A), a.left ≫ ψ = b.left ≫ ψ → a = b := fun a b hab =>
    Over.OverMorphism.ext (hψ.1.hom_ext hab (by rw [Over.w, Over.w]))
  have extC : ∀ {T : Over S₂} (a b : T ⟶ c₂.A), a.left ≫ φ = b.left ≫ φ → a = b := fun a b hab =>
    Over.OverMorphism.ext (hφ.1.hom_ext hab (by rw [Over.w, Over.w]))
  have pI : ∀ (T : Over S₂) (x : T ⟶ c₂.A), pushHom hψ T (x ≫ inc₂) = pushHom hφ T x ≫ inc₁ := fun T x =>
    Over.OverMorphism.ext (by
      show (x ≫ inc₂).left ≫ ψ = (x.left ≫ φ) ≫ inc₁.left
      rw [Over.comp_left, Category.assoc, inc₂_l, Category.assoc])
  have pP : ∀ (T : Over S₂) (x : T ⟶ w₂.A), pushHom hφ T (x ≫ pr₂) = pushHom hψ T x ≫ pr₁ := fun T x =>
    Over.OverMorphism.ext (by
      show (x ≫ pr₂).left ≫ φ = (x.left ≫ ψ) ≫ pr₁.left
      rw [Over.comp_left, Category.assoc, pr₂_l, Category.assoc])
  have mI : IsMonHom inc₂ := isMonHom_of_mul _ fun T x z => extW _ _ (congrArg (fun q => q.left)
    (calc pushHom hψ T ((x * z) ≫ inc₂) = pushHom hφ T (x * z) ≫ inc₁ := pI _ _
      _ = (pushHom hφ T x * pushHom hφ T z) ≫ inc₁ := by rw [map_mul]
      _ = (pushHom hφ T x ≫ inc₁) * (pushHom hφ T z ≫ inc₁) := MonObj.mul_comp _ _ _
      _ = pushHom hψ T (x ≫ inc₂) * pushHom hψ T (z ≫ inc₂) := by rw [pI, pI]
      _ = pushHom hψ T ((x ≫ inc₂) * (z ≫ inc₂)) := (map_mul _ _ _).symm))
  have mP : IsMonHom pr₂ := isMonHom_of_mul _ fun T x z => extC _ _ (congrArg (fun q => q.left)
    (calc pushHom hφ T ((x * z) ≫ pr₂) = pushHom hψ T (x * z) ≫ pr₁ := pP _ _
      _ = (pushHom hψ T x * pushHom hψ T z) ≫ pr₁ := by rw [map_mul]
      _ = (pushHom hψ T x ≫ pr₁) * (pushHom hψ T z ≫ pr₁) := MonObj.mul_comp _ _ _
      _ = pushHom hφ T (x ≫ pr₂) * pushHom hφ T (z ≫ pr₂) := by rw [pP, pP]
      _ = pushHom hφ T ((x ≫ pr₂) * (z ≫ pr₂)) := (map_mul _ _ _).symm))
  have h1 : inc₂ ≫ pr₂ = 𝟙 c₂.A := extC _ _ (by
    rw [Over.comp_left, Over.id_left, Category.assoc, pr₂_l, ← Category.assoc, inc₂_l, Category.assoc,
      ← Over.comp_left, ip₁, Over.id_left, Category.comp_id, Category.id_comp])
  have h2 : pr₂ ≫ inc₂ = act₂ e := extW _ _ (by
    rw [Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, pr₂_l, Category.assoc, ← Over.comp_left, pi₁,
      hact])
  have eι : (inc₂ ⊗ₘ inc₂).left ≫ ψ₂ = φ₂ ≫ (inc₁ ⊗ₘ inc₁).left := by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, sqψ.1, ← Category.assoc, ← Over.comp_left, tensorHom_fst, Category.assoc, ← Over.comp_left,
        tensorHom_fst, Over.comp_left, Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, ← sqφ.1,
        Category.assoc]
    · rw [Category.assoc, sqψ.2, ← Category.assoc, ← Over.comp_left, tensorHom_snd, Category.assoc, ← Over.comp_left,
        tensorHom_snd, Over.comp_left, Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, ← sqφ.2,
        Category.assoc]
  have P1 : LBIso (c₁.P.pull φ₂) (w₁.P.pull (φ₂ ≫ (inc₁ ⊗ₘ inc₁).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c₁.P φ₂ φ₂ rfl)
      (chartPullSame w₁.P _ (fun _ => (inc₁ ⊗ₘ inc₁).left) _ φ₂ fun _ => rfl) hP₁
  have P2 : LBIso (w₂.P.pull (inc₂ ⊗ₘ inc₂).left) (w₁.P.pull (φ₂ ≫ (inc₁ ⊗ₘ inc₁).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull w₂.P (inc₂ ⊗ₘ inc₂).left (inc₂ ⊗ₘ inc₂).left rfl)
      (chartPullSame w₁.P _ (fun _ => ψ₂) _ (inc₂ ⊗ₘ inc₂).left fun _ => eι.symm) hwP
  have hP₂ : LBIso c₂.P (w₂.P.pull (inc₂ ⊗ₘ inc₂).left) :=
    LBIso.trans c₂.isLB (pull_isLB c₁.isLB _) (pull_isLB w₂.isLB _) hcP
      (LBIso.trans (pull_isLB c₁.isLB _) (pull_isLB w₁.isLB _) (pull_isLB w₂.isLB _) P1 P2.symm)
  have lv : ∀ a, c₂.lev a ≫ inc₂ = w₂.lev (jl a) := fun a => extW _ _ (by
    rw [Over.comp_left, Category.assoc, inc₂_l, ← Category.assoc, hcl, Category.assoc, ← Over.comp_left, hl₁, hwl])
  let T₀ : Over S₂ := 𝟙_ (Over S₂)
  let u : Over.mk (T₀.hom ≫ y) ⟶ 𝟙_ (Over S₁) := toUnit _
  have hu : u.left = y := by
    simp [u, T₀]
  have pL : ∀ a, pushHom hψ T₀ (w₂.lev a) = u ≫ w₁.lev a := fun a => Over.OverMorphism.ext (by
    show (w₂.lev a).left ≫ ψ = u.left ≫ (w₁.lev a).left
    rw [hu, hwl])
  have pT : ∀ (b : Fin h ⊕ Fin h → ℤ) (r : O), pushHom hψ T₀ (c₂.lev b ≫ inc₂ ≫ act₂ r) =
      u ≫ (c₁.lev b ≫ inc₁ ≫ act₁ r) := fun b r => Over.OverMorphism.ext (by
    show (c₂.lev b ≫ inc₂ ≫ act₂ r).left ≫ ψ = u.left ≫ (c₁.lev b ≫ inc₁ ≫ act₁ r).left
    simp only [Over.comp_left, Category.assoc]
    rw [hact, reassoc_of% inc₂_l, reassoc_of% (hcl b), hu])
  have lz : ∀ a, w₂.lev a = (List.ofFn fun k => c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k)).prod := fun a =>
    extW _ _ (congrArg (fun q => q.left)
      (calc pushHom hψ T₀ (w₂.lev a) = u ≫ w₁.lev a := pL a
        _ = preHom (G := w₁.A) u (List.ofFn fun k => c₁.lev (κ k a) ≫ inc₁ ≫ act₁ (o k)).prod := by
          rw [hz₁ a]; rfl
        _ = (List.ofFn fun k => u ≫ (c₁.lev (κ k a) ≫ inc₁ ≫ act₁ (o k))).prod := by
          rw [map_list_prod, List.map_ofFn]; rfl
        _ = (List.ofFn fun k => pushHom hψ T₀ (c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k))).prod := by
          simp only [pT]
        _ = pushHom hψ T₀ (List.ofFn fun k => c₂.lev (κ k a) ≫ inc₂ ≫ act₂ (o k)).prod := by
          rw [map_list_prod, List.map_ofFn]; rfl))
  exact ⟨inc₂, pr₂, mI, mP, h1, h2, hP₂, lv, lz⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageRelationOfPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_image_relation_of_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → SiegPB c₂ c₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ := by
  first | (exact @GlobalTheory.UPel.HT.zRel_of_pullback) | (exact GlobalTheory.UPel.HT.zRel_of_pullback) | (intros; apply GlobalTheory.UPel.HT.zRel_of_pullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyIdempotentImageOpenLocus
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem idemImage_locus : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (Y : Scheme.{0}) (j : Y ⟶ S') (c : SiegPre h M (zetaAway M) (j ≫ t)), IsImmersion j ∧ QuasiCompact j ∧ SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(Y, ⊤)) ∧ (∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (y : T ⟶ Y) (c' : SiegPre h M (zetaAway M) t'), y ≫ j ≫ t = t' → SiegPB c' c y → ∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act (y ≫ j) ∧ ZRel e jl o κ c' w actw) ∧ ∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) t'), g ≫ t = t' → IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), ActPB w actw z act g ∧ ZRel e jl o κ c' w actw) → ∃! y : T ⟶ Y, y ≫ j = g ∧ SiegPB c' c y := by
  intro h h' M d O _ bar e jl n o κ S' _ t z act hh hM hodd hd hcop hpr hra hadj hee
  obtain ⟨U, c, wU, actU, hker, hunit, hwp, hwr, hwa, hwpb, hrel, hrange⟩ :=
    GlobalTheory.T.exists_open_locus_idempotent_image_siegel h h' M d O bar e jl n o κ S' t z act hh hM hodd hd hcop hpr hra hadj hee
  refine ⟨U.toScheme, U.ι, c, inferInstance, inferInstance, hker, hunit, ?_, ?_⟩
  · intro T t' y c' hyt hc'
    obtain ⟨w₂, act₂, hp₂, hr₂, ha₂, hpb₂⟩ :=
      GlobalTheory.T.exists_principal_siegel_adjoint_action_pullback h' M (cycAway M) (zetaAway M) O bar U.toScheme T (U.ι ≫ t) t' y wU actU hyt hwp hwr hwa
    exact ⟨w₂, act₂, hp₂, hr₂, ha₂, hpb₂.trans hwpb,
      GlobalTheory.T.idempotent_image_relation_of_pullback h h' M (cycAway M) (zetaAway M) O e jl n o κ U.toScheme T (U.ι ≫ t) t' y c wU actU c' w₂ act₂ hpb₂ hc' hrel⟩
  · intro T t' g c' hgt hdu hc' hex
    subst hgt
    have hr : Set.range g.base ⊆ (U : Set S') := hrange T g c' hdu hc' hex
    let y : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι g (by rw [Scheme.Opens.range_ι]; exact hr)
    have hy : y ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨w', actw', hpb', hrel'⟩ := hex
    refine ⟨y, ⟨hy, ?_⟩, ?_⟩
    · have hpb'' : ActPB w' actw' z act (y ≫ U.ι) := by rw [hy]; exact hpb'
      exact GlobalTheory.T.siegel_pullback_of_idempotent_images_and_action_pullback h h' M (cycAway M) (zetaAway M) O e jl n o κ U.toScheme T (U.ι ≫ t) (g ≫ t) y c wU actU c' w' actw'
        (GlobalTheory.T.siegel_pullback_with_action_cancellation h' M (cycAway M) (zetaAway M) O S' U.toScheme T t (U.ι ≫ t) (g ≫ t) z act U.ι y wU actU w' actw' hwpb hpb'')
        hrel hrel'
    · rintro y' ⟨hy', -⟩
      exact (cancel_mono U.ι).1 (hy'.trans hy.symm)

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyIdempotentImageOpenLocusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_family_idempotent_image_open_locus : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (Y : Scheme.{0}) (j : Y ⟶ S') (c : SiegPre h M (zetaAway M) (j ≫ t)), IsImmersion j ∧ QuasiCompact j ∧ SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(Y, ⊤)) ∧ (∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (y : T ⟶ Y) (c' : SiegPre h M (zetaAway M) t'), y ≫ j ≫ t = t' → SiegPB c' c y → ∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act (y ≫ j) ∧ ZRel e jl o κ c' w actw) ∧ ∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) t'), g ≫ t = t' → IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), ActPB w actw z act g ∧ ZRel e jl o κ c' w actw) → ∃! y : T ⟶ Y, y ≫ j = g ∧ SiegPB c' c y := by
  first | (exact @GlobalTheory.UPel.HT.idemImage_locus) | (exact GlobalTheory.UPel.HT.idemImage_locus) | (intros; apply GlobalTheory.UPel.HT.idemImage_locus  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKernelBoundedRepresentableOfCoprime
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem sdRep_of_coprime : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → SDRep h M d := by
  intro h M d hh hM hodd hd hcop
  obtain ⟨O, _, bar, r, eO, W, d₀, e, jl, n, o, κ, hbar, hspan, hW, hd₀, hsum, hee, hex, huniq⟩ :=
    GlobalTheory.T.exists_zarhinTrick_family_siegel_kernelKilled h M d hh hM hodd hd hcop
  obtain ⟨H, sH, zH, actH, hpr, hra, hadj, hq, hln, hrep⟩ :=
    GlobalTheory.T.exists_rep_principalSiegel_adjoint_orderAction (8 * h) M (by omega) hM hodd O bar r eO W d₀ hbar hspan hW hd₀ hsum
  obtain ⟨Y, j, c, hj, hjq, hker, hunit, hpull, huniv⟩ :=
    GlobalTheory.T.siegel_family_idempotent_image_open_locus h (8 * h) M d O bar e jl n o κ H sH zH actH hh hM hodd hd hcop hpr hra hadj hee
  refine ⟨Y, j ≫ sH, c, hker, hunit, isQProjOver_comp_immersion j sH hj hjq hq, ?_⟩
  intro S t c' hdu hc'
  obtain ⟨z', act', hz'p, hz'r, hz'a, hz'rel⟩ := hex S t c' hdu hc'
  obtain ⟨g, ⟨hg, hgpb⟩, -⟩ := hrep S t z' act' hz'p hz'r hz'a
  obtain ⟨y, ⟨hy, hyc⟩, -⟩ := huniv S t g c' hg hdu hc' ⟨z', act', hgpb, hz'rel⟩
  refine ⟨y, ⟨by rw [← Category.assoc, hy, hg], hyc⟩, ?_⟩
  rintro f ⟨hf, hfc⟩
  obtain ⟨w, actw, hwp, hwr, hwa, hwpb, hwrel⟩ := hpull S t f c' hf hfc
  have hiso := huniq S t c' w z' actw act' hdu hc' hwp hz'p hwr hz'r hwa hz'a hwrel hz'rel
  have h2 : ActPB w actw zH actH (𝟙 S ≫ g) := hiso.trans hgpb
  rw [Category.id_comp] at h2
  have hfj : f ≫ j = g :=
    (hrep S t w actw hwp hwr hwa).unique ⟨by rw [Category.assoc]; exact hf, hwpb⟩ ⟨hg, h2⟩
  exact (huniv S t g c' hg hdu hc' ⟨z', act', hgpb, hz'rel⟩).unique ⟨hfj, hfc⟩ ⟨hy, hyc⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKernelBoundedRepresentableOfCoprimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelKernelBoundedRepresentable_of_coprime : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → SDRep h M d := by
  first | (exact @GlobalTheory.UPel.HT.sdRep_of_coprime) | (exact GlobalTheory.UPel.HT.sdRep_of_coprime) | (intros; apply GlobalTheory.UPel.HT.sdRep_of_coprime  <;> assumption)
end
