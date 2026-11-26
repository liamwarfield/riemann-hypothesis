module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelLevelLoweringQuotientFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByCharts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.IsomCalc

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
variable {L M : MLine p σ}

theorem isom_of_local {J : Type} (W : J → X.Opens) (hW : ∀ x, ∃ j, x ∈ W j) (a : J → M.B.ι)
    (b : J → L.B.ι) (ha : ∀ j, W j ≤ M.B.U (a j)) (hb : ∀ j, W j ≤ L.B.U (b j)) (u : ∀ j, Γ(X, W j)ˣ)
    (hu : ∀ (x : X) j j', x ∈ W j → x ∈ W j' → gm (𝟙 X) x (W j) (u j) =
      gm (𝟙 X) x _ (M.B.g (a j) (a j')) * (gm (𝟙 X) x _ (L.B.g (b j) (b j')))⁻¹ * gm (𝟙 X) x (W j') (u j'))
    (hφ : ∀ j (y : CxPts p σ), y ∈ ptsIn p σ (W j) →
      M.φ.φ (a j) y = L.φ.φ (b j) y + logSq y (W j) (u j)) : L.Isom M := by
  let v (c : M.B.ι × L.B.ι) (j : J) : Γ(X, M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j)ˣ :=
    res (inf_le_inf inf_le_left (ha j)) (M.B.g c.1 (a j)) *
      (res (inf_le_inf inf_le_right (hb j)) (L.B.g c.2 (b j)))⁻¹ * res inf_le_right (u j)
  have hv (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (v c j) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    simp only [v, map_mul, map_inv, gm_res (𝟙 X) x _ hx]
  have key : ∀ {G : Type} [CommGroup G] (a b c d e : G), a * b * (c * d)⁻¹ * e = a * c⁻¹ * (b * d⁻¹ * e) := by
    intro G _ a b c d e
    simp only [mul_inv]
    ac_rfl
  have hg (c : M.B.ι × L.B.ι) : ∃ s : Γ(X, M.B.U c.1 ⊓ L.B.U c.2)ˣ, ∀ j, res inf_le_left s = v c j := by
    refine glue_unit _ _ _ (fun x hx => ?_) (v c) fun j j' x hx => ?_
    · obtain ⟨j, hj⟩ := hW x
      exact Opens.mem_iSup.2 ⟨j, hx, hj⟩
    · rw [hv c j x hx.1, hv c j' x hx.2, hu x j j' hx.1.2 hx.2.2,
        ← gm_cocycle M.φ.isLB (𝟙 X) x hx.1.1.1 (ha j hx.1.2) (ha j' hx.2.2),
        ← gm_cocycle L.φ.isLB (𝟙 X) x hx.1.1.2 (hb j hx.1.2) (hb j' hx.2.2), key]
  choose s hs using hg
  have hs' (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (s c) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    rw [← hv c j x hx, ← hs, gm_res (𝟙 X) x _ hx]
  refine ⟨⟨s⟩, (isGen_iff_germ _).2 fun x c c' hc hc' => ?_, fun a₀ b₀ y h₁ h₂ => ?_⟩
  · obtain ⟨j, hj⟩ := hW x
    refine (hs' c j x ⟨hc, hj⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_div' M.B L.B (𝟙 X) x c c' hc hc') (hs' c' j x ⟨hc', hj⟩)).symm)
    rw [← gm_cocycle M.φ.isLB (𝟙 X) x hc.1 hc'.1 (ha j hj),
      ← gm_cocycle L.φ.isLB (𝟙 X) x hc.2 hc'.2 (hb j hj), key]
  · obtain ⟨j, hj⟩ := hW (under y)
    have hj' : y ∈ ptsIn p σ (W j) := mem_ptsIn.2 hj
    have hy : y ∈ ptsIn p σ (M.B.U a₀ ⊓ L.B.U b₀ ⊓ W j) := by simp [*]
    have e : logSq y _ (s (a₀, b₀)) = logSq y _ (M.B.g a₀ (a j)) + -logSq y _ (L.B.g b₀ (b j)) +
        logSq y _ (u j) := by
      rw [← logSq_res inf_le_left hy, hs (a₀, b₀) j]
      simp only [v, logSq_mul hy, logSq_inv hy, logSq_res _ hy]
    have e₁ : _ = _ - logSq y _ (M.B.g a₀ (a j)) := M.φ.trans a₀ (a j) y h₁ (ptsIn_mono (ha j) hj')
    have e₂ : _ = _ - logSq y _ (L.B.g b₀ (b j)) := L.φ.trans b₀ (b j) y h₂ (ptsIn_mono (hb j) hj')
    have e₃ := hφ j y hj'
    change _ = _ + logSq y _ (s (a₀, b₀))
    linarith

theorem isom_of_chart (a : L.B.ι → M.B.ι) (ha : ∀ j, L.B.U j ≤ M.B.U (a j))
    (hg : ∀ (x : X) j j', x ∈ L.B.U j → x ∈ L.B.U j' →
      gm (𝟙 X) x _ (L.B.g j j') = gm (𝟙 X) x _ (M.B.g (a j) (a j')))
    (hφ : ∀ j (y : CxPts p σ), y ∈ ptsIn p σ (L.B.U j) → M.φ.φ (a j) y = L.φ.φ j y) : L.Isom M :=
  isom_of_local L.B.U (exists_chart L.φ.isLB) a id ha (fun _ => le_rfl) (fun _ => 1)
    (fun x j j' h h' => by rw [map_one, map_one, ← hg x j j' h h', mul_one]; exact (mul_inv_cancel _).symm)
    fun j y h => by rw [logSq_one h, add_zero]; exact hφ j y h

theorem isom_refl (L : MLine p σ) : L.Isom L :=
  isom_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ => rfl

theorem isom_pull (h : L.Isom M) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (L.pull π hπ).Isom (M.pull π hπ) := by
  obtain ⟨w, hw, h⟩ := h
  refine isom_of_local (fun c : M.B.ι × L.B.ι => π ⁻¹ᵁ (M.B.U c.1 ⊓ L.B.U c.2))
    (fun x => ?_) (fun c _ => c.1) (fun c _ => c.2) (fun _ _ h => mem_pull.2 h.1)
    (fun _ _ h => mem_pull.2 h.2) (fun c => pullU π _ (w.s (c.1, c.2))) (fun x c c' hc hc' => ?_)
    fun c y hy => ?_
  · obtain ⟨a, ha⟩ := exists_chart M.φ.isLB (π x)
    obtain ⟨b, hb⟩ := exists_chart L.φ.isLB (π x)
    exact ⟨(a, b), ha, hb⟩
  · refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹)
      (gm_pull_g M.B π (𝟙 Y) x (fun _ => c.1) (fun _ => c'.1) (mem_pull.2 hc.1) (mem_pull.2 hc'.1))
      (gm_pull_g L.B π (𝟙 Y) x (fun _ => c.2) (fun _ => c'.2) (mem_pull.2 hc.2) (mem_pull.2 hc'.2)))).symm
    exact (gm_pull (U := M.B.U c.1 ⊓ L.B.U c.2) (𝟙 Y) π x hc (w.s (c.1, c.2))).trans
      ((gm_isGen hw (𝟙 Y ≫ π) x _ _ _ _ hc.1 hc'.1 hc.2 hc'.2).trans (congrArg (_ * ·)
        (gm_pull (U := M.B.U c'.1 ⊓ L.B.U c'.2) (𝟙 Y) π x hc' (w.s (c'.1, c'.2))).symm))
  · have hy' : PtsOver.map π hπ _ y ∈ ptsIn p σ (M.B.U c.1 ⊓ L.B.U c.2) := hy
    refine (M.φ.pull_φ π hπ _ y).trans ((h _ _ _ (mem_ptsIn_inf.1 hy').1 (mem_ptsIn_inf.1 hy').2).trans
      (congrArg₂ (· + ·) (L.φ.pull_φ π hπ (fun _ => c.2) y).symm ?_))
    exact congrArg (fun z => Real.log (‖z‖ ^ 2)) (ev_app π hπ _ _ y).symm

theorem isom_pull_tens (L M : MLine p σ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.tens M).pull π hπ).Isom ((L.pull π hπ).tens (M.pull π hπ)) :=
  isom_of_chart (fun j => (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2))
    (fun _ _ h => ⟨mem_pull.2 (mem_pull.1 h).1, mem_pull.2 (mem_pull.1 h).2⟩)
    (fun x j j' h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine ((gm_pull_g (CechPic.tens L.B M.B) π (𝟙 Y) x j j' h h').trans
        (gm_tens L.B M.B (𝟙 Y ≫ π) x _ _ e e')).trans (Eq.symm ?_)
      exact (gm_tens (L.B.pull π) (M.B.pull π) (𝟙 Y) x (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2)
        (fun _ => (j' PUnit.unit).1, fun _ => (j' PUnit.unit).2) ⟨mem_pull.2 e.1, mem_pull.2 e.2⟩
        ⟨mem_pull.2 e'.1, mem_pull.2 e'.2⟩).trans (congrArg₂ (· * ·)
          (gm_pull_g L.B π (𝟙 Y) x _ _ (mem_pull.2 e.1) (mem_pull.2 e'.1))
          (gm_pull_g M.B π (𝟙 Y) x _ _ (mem_pull.2 e.2) (mem_pull.2 e'.2))))
    fun j y _ => (congrArg₂ (· + ·) (L.φ.pull_φ π hπ _ y) (M.φ.pull_φ π hπ _ y)).trans
      ((L.tens M).φ.pull_φ π hπ j y).symm

theorem isom_pull_ofFun (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hu' : ∀ z, CInfAt (fun z => u (ptMap π hπ σ z)) z) :
    ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) hu') :=
  isom_of_chart (fun _ => PUnit.unit) (fun _ => le_top)
    (fun x j j' h h' => (gm_pull_g (LB.triv X) π (𝟙 Y) x j j' h h').trans ((map_one _).trans (map_one _).symm))
    fun j y _ => ((MLine.ofFun u hu).φ.pull_φ π hπ j y).symm

theorem isom_addFn (L : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y) :
    (L.addFn u hu).Isom (L.tens (MLine.ofFun u hu)) :=
  isom_of_chart (fun c => (c, PUnit.unit)) (fun _ _ h => ⟨h, trivial⟩)
    (fun x c c' h h' => ((gm_tens L.B (LB.triv X) (𝟙 X) x (c, PUnit.unit) (c', PUnit.unit)
      ⟨h, trivial⟩ ⟨h', trivial⟩).trans ((congrArg (_ * ·) (map_one _)).trans (mul_one _))).symm)
    fun _ _ _ => rfl

theorem isom_pull_pull (L : MLine p σ) (π : Y ⟶ X) (hπ : π ≫ p = q) {Z : Scheme.{0}} {r : Z ⟶ Sp k} (i : Z ⟶ Y)
    (hi : i ≫ q = r) (h₀ : (i ≫ π) ≫ p = r) : ((L.pull π hπ).pull i hi).Isom (L.pull (i ≫ π) h₀) :=
  isom_of_chart (fun J => fun _ => J PUnit.unit PUnit.unit)
    (fun _ _ h => mem_pull₂.2 (mem_pull.1 (mem_pull.1 h)))
    (fun x (J J' : PUnit → PUnit → L.B.ι) h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine (gm_pull_g (L.B.pull π) i (𝟙 Z) x J J' h h').trans
        ((gm_pull_g L.B π (𝟙 Z ≫ i) x (J PUnit.unit) (J' PUnit.unit) e e').trans ?_)
      rw [Category.assoc]
      exact (gm_pull_g L.B (i ≫ π) (𝟙 Z) x (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
        (mem_pull₂.2 (mem_pull.1 e)) (mem_pull₂.2 (mem_pull.1 e'))).symm)
    fun (J : PUnit → PUnit → L.B.ι) y _ => by
      refine (L.φ.pull_φ (i ≫ π) h₀ (fun _ => J PUnit.unit PUnit.unit) y).trans (Eq.trans ?_
        ((Weight.pull_φ (L.pull π hπ).φ i hi J y).trans (L.φ.pull_φ π hπ (J PUnit.unit) _)).symm)
      exact congrArg _ (Subtype.ext (by simp [PtsOver.map_val]))

end GlobalTheory.Mix.IsomCalc


open GlobalTheory.Mix.IsomCalc in
theorem GlobalTheory.Mix.isom_calculus : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q), (∀ A : MLine p σ, A.Isom A) ∧ (∀ A B : MLine p σ, A.Isom B → (A.pull π hπ).Isom (B.pull π hπ)) ∧ (∀ A B : MLine p σ, ((A.tens B).pull π hπ).Isom ((A.pull π hπ).tens (B.pull π hπ))) ∧ (∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) fun z => (hu _).pull π hπ)) ∧ (∀ (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (A.addFn u hu).Isom (A.tens (MLine.ofFun u hu))) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp k) (g : Z ⟶ Y) (hg : g ≫ q = r) (h : (g ≫ π) ≫ p = r) (A : MLine p σ), ((A.pull π hπ).pull g hg).Isom (A.pull (g ≫ π) h) :=
  fun _ _ _ _ _ _ _ π hπ => ⟨isom_refl, fun _ _ h => isom_pull h π hπ, fun A B => isom_pull_tens A B π hπ,
    fun u hu => isom_pull_ofFun u hu π hπ _, isom_addFn, fun _ _ g hg h A => isom_pull_pull A π hπ g hg h⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculusStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q), (∀ A : MLine p σ, A.Isom A) ∧ (∀ A B : MLine p σ, A.Isom B → (A.pull π hπ).Isom (B.pull π hπ)) ∧ (∀ A B : MLine p σ, ((A.tens B).pull π hπ).Isom ((A.pull π hπ).tens (B.pull π hπ))) ∧ (∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ((MLine.ofFun u hu).pull π hπ).Isom (MLine.ofFun (fun z => u (ptMap π hπ σ z)) fun z => (hu _).pull π hπ)) ∧ (∀ (A : MLine p σ) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), (A.addFn u hu).Isom (A.tens (MLine.ofFun u hu))) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp k) (g : Z ⟶ Y) (hg : g ≫ q = r) (h : (g ≫ π) ≫ p = r) (A : MLine p σ), ((A.pull π hπ).pull g hg).Isom (A.pull (g ≫ π) h) := by
  first | exact @GlobalTheory.Mix.isom_calculus | exact GlobalTheory.Mix.isom_calculus | (intros; apply GlobalTheory.Mix.isom_calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConj
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

variable {s : ℕ}

def ldTop (j : Fin s) : {a : Fin s // (a : ℕ) < j + 1} := ⟨j, Nat.lt_succ_self _⟩

@[simp] theorem ldTop_val (j : Fin s) : (ldTop j).1 = j := rfl

theorem eq_ldTop_iff {j : Fin s} (a : {a : Fin s // (a : ℕ) < j + 1}) : a = ldTop j ↔ a.1 = j :=
  ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩

theorem sum_eq_sum_lt_of_zero (m : ℕ) (f : Fin s → ℂ) (hf : ∀ l : Fin s, ¬ (l : ℕ) < m → f l = 0) :
    ∑ l, f l = ∑ b : {a : Fin s // (a : ℕ) < m}, f b := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a : Fin s => (a : ℕ) < m) f]
  have : ∑ b : {a : Fin s // ¬ (a : ℕ) < m}, f b = 0 := Finset.sum_eq_zero (fun b _ => hf b b.2)
  rw [this, add_zero]

theorem prod_lt_eq (m : ℕ) (f : Fin s → ℂ) :
    ∏ a : {a : Fin s // (a : ℕ) < m}, f a = ∏ a : Fin s, if (a : ℕ) < m then f a else 1 := by
  rw [← Finset.prod_filter]
  exact (Finset.prod_subtype _ (by simp) f).symm

theorem prod_lt_succ (j : Fin s) (f : Fin s → ℂ) :
    ∏ a : {a : Fin s // (a : ℕ) < j + 1}, f a = (∏ a : {a : Fin s // (a : ℕ) < j}, f a) * f j := by
  have hj : f j = ∏ a : Fin s, if a = j then f a else 1 := by simp
  rw [prod_lt_eq, prod_lt_eq, hj, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases h1 : (a : ℕ) < j
  · have h2 : a ≠ j := fun h => by subst h; omega
    simp [h1, h2, show (a : ℕ) < j + 1 by omega]
  · by_cases h3 : a = j
    · subst h3; simp
    · have : ¬ (a : ℕ) < j + 1 := fun h => h3 (Fin.ext (by omega))
      simp [h1, h3, this]

theorem submatrix_mul_conjTranspose_lt (g M : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0)
    {κ : Type} (ρ : κ → Fin s) (m : ℕ) :
    (M * gᴴ).submatrix ρ (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) =
      M.submatrix ρ (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) *
        gᴴ.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_eq_sum_lt_of_zero m _ fun l hl => ?_
  rw [Matrix.conjTranspose_apply, hg c.1 l (by have := c.2; rw [Fin.lt_iff_val_lt_val]; omega), star_zero, mul_zero]

theorem submatrix_mul_lt (g M : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0)
    {κ : Type} (ν : κ → Fin s) (m : ℕ) :
    (g * M).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) ν =
      g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val *
        M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) ν := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_eq_sum_lt_of_zero m _ fun l hl => ?_
  rw [hg a.1 l (by have := a.2; rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]

theorem det_submatrix_lt (g : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (m : ℕ) :
    (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < m} → Fin s) Subtype.val).det =
      ∏ a : {a : Fin s // (a : ℕ) < m}, g a a := by
  rw [Matrix.det_of_lowerTriangular]
  · rfl
  · intro a b h
    exact hg a.1 b.1 h

theorem leadMinor_conj_lower (g G : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (m : ℕ) :
    leadMinor (g * G * gᴴ) m =
      (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) * leadMinor G m * star (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) := by
  unfold leadMinor
  rw [submatrix_mul_conjTranspose_lt g _ hg, Matrix.det_mul, submatrix_mul_lt g G hg]
  erw [Matrix.det_mul]
  rw [← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, det_submatrix_lt g hg]

theorem det_updateRow_finset_sum {ι κ : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (r : ι)
    (t : Finset κ) (c : κ → ℂ) (v : κ → ι → ℂ) :
    (A.updateRow r (∑ l ∈ t, c l • v l)).det = ∑ l ∈ t, c l * (A.updateRow r (v l)).det := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero r (fun c => by simp)
  · intro a t ha ih
    rw [Finset.sum_insert ha, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, ih, Finset.sum_insert ha]

theorem submatrix_ld_eq_updateRow (X : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    X.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val =
      (X.submatrix Subtype.val Subtype.val).updateRow (ldTop j)
        (fun c : {a : Fin s // (a : ℕ) < j + 1} => X i c) := by
  ext a c
  rw [Matrix.updateRow_apply]
  by_cases h : a.1 = j
  · simp [h, (eq_ldTop_iff a).2 h]
  · have : a ≠ ldTop j := fun e => h ((eq_ldTop_iff a).1 e)
    simp [h, this]

theorem updateRow_mul_lower (g X : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (j : Fin s)
    (v : {a : Fin s // (a : ℕ) < j + 1} → ℂ) :
    ((g * X).submatrix Subtype.val Subtype.val).updateRow (ldTop j) v =
      (g.submatrix Subtype.val Subtype.val).updateRow (ldTop j) (Pi.single (ldTop j) 1) *
        (X.submatrix Subtype.val Subtype.val).updateRow (ldTop j) v := by
  ext a c
  by_cases h : a = ldTop j
  · subst h
    simp [Matrix.mul_apply, Pi.single_apply]
  · have ha : (a.1 : ℕ) < j := by
      have := a.2
      have : (a.1 : ℕ) ≠ j := fun e => h ((eq_ldTop_iff a).2 (Fin.ext e))
      omega
    rw [Matrix.updateRow_ne h, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [sum_eq_sum_lt_of_zero ((j : ℕ) + 1) _ fun l hl => by
      rw [hg a.1 l (by rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.updateRow_ne h, Matrix.submatrix_apply, Matrix.updateRow_apply]
    by_cases hb : b = ldTop j
    · subst hb
      rw [ldTop_val, hg a.1 j (by rw [Fin.lt_iff_val_lt_val]; exact ha)]
      simp
    · simp [hb]

theorem det_frameRow (g : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (j : Fin s) :
    ((g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j + 1} → Fin s) Subtype.val).updateRow
      (ldTop j) (Pi.single (ldTop j) 1)).det =
      ∏ a : {a : Fin s // (a : ℕ) < j}, g a a := by
  rw [Matrix.det_of_lowerTriangular]
  · have e : ∀ a : {a : Fin s // (a : ℕ) < j + 1},
        ((g.submatrix Subtype.val Subtype.val).updateRow (ldTop j) (Pi.single (ldTop j) 1)) a a =
          (fun b : Fin s => if b = j then 1 else g b b) a := by
      intro a
      by_cases h : a = ldTop j
      · subst h; simp
      · have : a.1 ≠ j := fun e => h ((eq_ldTop_iff a).2 e)
        simp [Matrix.updateRow_ne h, this]
    rw [Fintype.prod_congr _ _ e, prod_lt_succ j (fun b : Fin s => if b = j then 1 else g b b)]
    simp only [if_true, mul_one]
    refine Fintype.prod_congr (fun a : {a : Fin s // (a : ℕ) < j} => if (a : Fin s) = j then (1 : ℂ) else g a a)
      (fun a => g a a) fun a => ?_
    have : a.1 ≠ j := fun e => by have := a.2; rw [e] at this; omega
    simp [this]
  · intro a b hab
    have hab' : (a.1 : ℕ) < b.1 := hab
    by_cases h : a = ldTop j
    · subst h
      have := b.2
      simp at hab'
      omega
    · rw [Matrix.updateRow_ne h, Matrix.submatrix_apply]
      exact hg a.1 b.1 (Fin.lt_iff_val_lt_val.mpr hab')

end GlobalTheory.ChernCalc

namespace GlobalTheory.ChernCalc

theorem ldNum_conj_lower {s : ℕ} (g G : Matrix (Fin s) (Fin s) ℂ) (hg : ∀ i j, i < j → g i j = 0) (i j : Fin s) :
    ((g * G * gᴴ).submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det =
      (∏ a : {a : Fin s // (a : ℕ) < j}, g a a) *
        (∑ l, g i l * (G.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then l else a.1)
          Subtype.val).det) * star (∏ a : {a : Fin s // (a : ℕ) < j + 1}, g a a) := by
  rw [submatrix_mul_conjTranspose_lt g _ hg, Matrix.det_mul, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose,
    det_submatrix_lt g hg, submatrix_ld_eq_updateRow, updateRow_mul_lower g G hg]
  erw [Matrix.det_mul]
  rw [det_frameRow g hg]
  have hrow : (fun c : {a : Fin s // (a : ℕ) < j + 1} => (g * G) i c) =
      ∑ l, g i l • (fun c : {a : Fin s // (a : ℕ) < j + 1} => G l c) := by
    funext c; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [hrow, det_updateRow_finset_sum]
  simp only [submatrix_ld_eq_updateRow]

theorem ldPart_conj_lower : ∀ (s : ℕ) (G g : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ i j, i < j → g i j = 0) →
    IsUnit g.det → ldPart (g * G * gᴴ) = g * ldPart G * (Matrix.diagonal fun i => g i i)ᴴ ∧
      ∀ i, grD (g * G * gᴴ) i = ‖g i i‖ ^ 2 * grD G i := by
  intro s G g hG hg hdet
  have hgd : g.det = ∏ a, g a a := Matrix.det_of_lowerTriangular g (fun a b h => hg a b h)
  have hdiag : ∀ a, g a a ≠ 0 := by
    intro a
    have h := hdet.ne_zero
    rw [hgd] at h
    exact (Finset.prod_ne_zero_iff.mp h) a (Finset.mem_univ _)
  have hP : ∀ m : ℕ, (∏ a : {a : Fin s // (a : ℕ) < m}, g a a) ≠ 0 :=
    fun m => Finset.prod_ne_zero_iff.mpr fun a _ => hdiag a
  have hlm : ∀ m : ℕ, leadMinor G m ≠ 0 := fun m => by
    unfold leadMinor
    exact ((hG.submatrix Subtype.val_injective).det_pos).ne'
  have hsq : ∀ z w : ℂ, (z * w * star z).re = ‖z‖ ^ 2 * w.re := by
    intro z w
    rw [mul_comm z w, mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.re_mul_ofReal]
    ring
  refine ⟨?_, fun i => ?_⟩
  · ext i j
    simp only [ldPart, Matrix.of_apply]
    rw [ldNum_conj_lower g G hg, leadMinor_conj_lower g G hg, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
      Matrix.mul_apply, prod_lt_succ j (fun b => g b b)]
    simp only [Matrix.of_apply, ← mul_div_assoc, Pi.star_apply]
    rw [← Finset.sum_div, star_mul]
    have h1 := hP (j : ℕ)
    have h2 := hlm (j : ℕ)
    have h3 : star (∏ a : {a : Fin s // (a : ℕ) < j}, g a a) ≠ 0 := star_ne_zero.mpr h1
    field_simp
  · unfold grD
    rw [leadMinor_conj_lower g G hg, leadMinor_conj_lower g G hg, hsq, hsq, prod_lt_succ i (fun b => g b b),
      norm_mul, mul_pow]
    have hn : ‖∏ a : {a : Fin s // (a : ℕ) < i}, g a a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (hP _))
    rw [mul_assoc, mul_div_mul_left _ _ hn, mul_div_assoc]

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorLowerTriangularConjStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj : ∀ (s : ℕ) (G g : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ i j, i < j → g i j = 0) → IsUnit g.det → ldPart (g * G * gᴴ) = g * ldPart G * (Matrix.diagonal fun i => g i i)ᴴ ∧ ∀ i, grD (g * G * gᴴ) i = ‖g i i‖ ^ 2 * grD G i := by
  first | exact @GlobalTheory.ChernCalc.ldPart_conj_lower | exact GlobalTheory.ChernCalc.ldPart_conj_lower | (intros; apply GlobalTheory.ChernCalc.ldPart_conj_lower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyCyclotomicAwayOddLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelFamilyOfDivisorLevelSamePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelFamilyOfDivisorLevelSamePrimes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegLev

theorem sFam_down : ∀ h n N : ℕ, 3 ≤ n → Odd N → n ∣ N → (∃ a, N ∣ n ^ a) → Nonempty (SFam h N (zetaAway N)) →
    Nonempty (SFam h n (zetaAway n)) := by
  intro h n N hn hN hnN hpow ⟨F⟩
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hN)
  obtain ⟨j, hinj, hζ, hfes⟩ := GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale n N hN0 hnN
  obtain ⟨hfin, het, hsurj⟩ := hfes hpow
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_siegelLevelLoweringQuotientFamily h n N F j hn hN hnN hζ hfin het
  exact ⟨{
    X := Q.X
    s := Q.s
    smooth := Q.smooth
    qproj := Q.qproj
    univ := Q.univ
    princ := Q.princ
    rep := fun S s' c hred hdense hpr =>
      GlobalTheory.T.siegelLevelLoweringQuotient_represents_reduced h n N F j Q hn hN hnN hinj hζ hfin het hsurj S s' c hred hdense hpr
    inj := fun R _ _ x y s' c hs h₁ h₂ =>
      GlobalTheory.T.siegelQuotientFamily_local_points_eq_of_object h n N _ _ (zetaAway n) (zetaAway N) F j Q R x y s' c hs h₁ h₂ }⟩

end GlobalTheory.SiegLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelFamilyOfDivisorLevelSamePrimesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_siegelFamily_of_divisor_level_same_primes : ∀ h n N : ℕ, 3 ≤ n → Odd N → n ∣ N → (∃ a, N ∣ n ^ a) → Nonempty (SFam h N (zetaAway N)) → Nonempty (SFam h n (zetaAway n)) := by
  first | exact @GlobalTheory.SiegLev.sFam_down | exact GlobalTheory.SiegLev.sFam_down | (intros; apply GlobalTheory.SiegLev.sFam_down <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyDeeperLevelOfDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyDeeperLevelOfDvd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegLev

section
variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {c : SiegPre h n ζ s}
  {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {d d' d'' : ℕ}

theorem sRel_trans (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

theorem sRel_principal (h₁ : SRel c' c d' d f) (hc : c.Principal) : c'.Principal :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 _) d d' d' h₁).2.1 hc

theorem sRel_scale (h₁ : SRel c' c d' d f) (e : ℕ) : SRel c' c (d' * e) (d * e) f :=
  (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 _) d d' d' h₁).2.2 e

end

theorem spMap_id_eq (o : Type) [CommRing o] : spMap (RingHom.id o) = 𝟙 _ := Spec.map_id _

theorem sFam_of_dvd : ∀ (h n N : ℕ) (o : Type) [CommRing o] [IsNoetherianRing o] (b : TBase o N), 3 ≤ n → Odd N → n ∣ N →
    Nonempty (SFam h n ((b.ζ : o) ^ (N / n))) → Nonempty (SFam h N (b.ζ : o)) := by
  intro h n N o _ _ b hn hN hnN ⟨F⟩
  set ζ : o := (b.ζ : o) ^ (N / n)

  obtain ⟨c₀, h₀₁, h₀₂⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h n o o ζ ζ (RingHom.id o) F.X F.X (F.s ≫ spMap (RingHom.id o)) F.s (𝟙 _) rfl
    (by simp)).2.2 F.univ
  have r₀₁ : SRel F.univ c₀ 1 1 (𝟙 _) := (sRel_one_one_iff _ _ _).2 h₀₁
  have r₀₂ : SRel c₀ F.univ 1 1 (𝟙 _) := (sRel_one_one_iff _ _ _).2 h₀₂
  have p₀ : c₀.Principal := sRel_principal r₀₂ F.princ
  obtain ⟨S₁, π, C, hfin, het, hsurj, hlow, huniv⟩ :=
    GlobalTheory.T.exists_finite_etale_deeper_level_siegel_cover h n N o o ζ b (RingHom.id o) F.X F.s c₀ hn hN hnN rfl p₀
  have hN0 : N ≠ 0 := hN.pos.ne'
  have pC : C.Principal := sRel_principal hlow p₀
  refine ⟨{
    X := S₁
    s := π ≫ F.s
    smooth := by
      haveI := F.smooth
      have := smoothOfRelativeDimension_comp 0 (h * (h + 1) / 2) π F.s
      rwa [zero_add] at this
    qproj := GlobalTheory.T.isQProjOver_comp_of_isFinite_noetherianBase o _ _ π F.s hfin F.qproj
    univ := C
    princ := pC
    rep := ?_
    inj := ?_ }⟩
  · intro T s' c hred hdense hp
    obtain ⟨cl, hcl1, hcl2⟩ := GlobalTheory.T.exists_siegelObject_lowered_level h n N o o ζ (b.ζ : o) (RingHom.id o) T s' c hN0 b.unit hnN rfl
    have pl : cl.Principal := sRel_principal hcl2 hp
    obtain ⟨f, hf, hfp⟩ := F.rep T (s' ≫ spMap (RingHom.id o)) cl hred
      (by rw [spMap_id_eq, Category.comp_id]; exact hdense) pl
    rw [spMap_id_eq, Category.comp_id] at hf
    subst hf
    have r1 : SRel c F.univ (N / n) 1 (𝟙 _ ≫ f) := sRel_trans ((sRel_one_one_iff _ _ _).2 hfp) hcl1
    have r2 : SRel c c₀ (N / n) 1 ((𝟙 _ ≫ f) ≫ 𝟙 _) := sRel_trans r₀₁ r1
    obtain ⟨t₁, ⟨ht₁, hC⟩, -⟩ := huniv T f c (by simpa using r2)
    exact ⟨t₁, by rw [← Category.assoc, ht₁], hC⟩
  · intro R _ _ x y s' c hxy hx hy
    have rx : SRel c C 1 1 x := (sRel_one_one_iff _ _ _).2 hx
    have ry : SRel c C 1 1 y := (sRel_one_one_iff _ _ _).2 hy
    have kx : SRel c c₀ (N / n) 1 (x ≫ π) := sRel_trans hlow (by simpa using sRel_scale rx (N / n))
    have ky : SRel c c₀ (N / n) 1 (y ≫ π) := sRel_trans hlow (by simpa using sRel_scale ry (N / n))

    obtain ⟨cx, hcx⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h n o o ζ ζ (RingHom.id o) F.X (Sp R) (F.s ≫ spMap (RingHom.id o))
      ((x ≫ π) ≫ F.s) (x ≫ π) rfl (by simp)).1 c₀
    have e1 : SRel cx c₀ 1 1 (x ≫ π) := (sRel_one_one_iff _ _ _).2 hcx
    have e2 : SRel cx c 1 (N / n) (𝟙 _) := sRel_cancel (f' := 𝟙 _) kx (by simpa using e1)
    have e3 : SRel cx c₀ 1 1 (𝟙 _ ≫ y ≫ π) := sRel_trans ky e2
    have fx : SiegPB cx F.univ (x ≫ π) := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans r₀₂ e1)
    have fy : SiegPB cx F.univ (y ≫ π) := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans r₀₂ e3)
    have hπ : x ≫ π = y ≫ π := F.inj R (x ≫ π) (y ≫ π) _ cx (by simpa using hxy) fx fy

    obtain ⟨Cx, hCx⟩ := (GlobalTheory.T.siegelPre_pullback_principal_ringChange h N o o (b.ζ : o) (b.ζ : o) (RingHom.id o) S₁ (Sp R) (π ≫ F.s)
      ((x ≫ π) ≫ F.s) x rfl (by rw [spMap_id_eq]; simp)).1 C
    have g1 : SRel Cx C 1 1 x := (sRel_one_one_iff _ _ _).2 hCx
    have g2 : SRel Cx c₀ (N / n) 1 (x ≫ π) := sRel_trans hlow (by simpa using sRel_scale g1 (N / n))
    have g3 : SRel Cx c 1 1 (𝟙 _) := sRel_cancel (f' := 𝟙 _) rx (by simpa using g1)
    have g4 : SiegPB Cx C y := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_trans ry g3)
    exact (huniv (Sp R) (x ≫ π) Cx g2).unique ⟨rfl, hCx⟩ ⟨hπ.symm, g4⟩

end GlobalTheory.SiegLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyDeeperLevelOfDvdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_deeper_level_of_dvd : ∀ (h n N : ℕ) (o : Type) [CommRing o] [IsNoetherianRing o] (b : TBase o N), 3 ≤ n → Odd N → n ∣ N → Nonempty (SFam h n ((b.ζ : o) ^ (N / n))) → Nonempty (SFam h N (b.ζ : o)) := by
  first | exact @GlobalTheory.SiegLev.sFam_of_dvd | exact GlobalTheory.SiegLev.sFam_of_dvd | (intros; apply GlobalTheory.SiegLev.sFam_of_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSFamPrimePowSq
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM

namespace GlobalTheory.SiegelTor

theorem exists_sFam_primePow_sq :
    ∀ g l : ℕ, 1 ≤ g → l.Prime → Odd l →
      ∃ j : ℕ, 1 ≤ j ∧ Nonempty (SFam g ((l ^ j) ^ 2) (zetaAway ((l ^ j) ^ 2))) := by
  intro g l hg hl _hodd
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam hLaws hLaws2 GlobalTheory.Moduli.cube_of_isLB
    GlobalTheory.thetaUnifAV_closed g l hg hl _hodd

  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have hn : (l ^ max j₀ 1) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl.ne_zero)

  have key := hj₀ (max j₀ 1) (le_max_left _ _) (cycAway ((l ^ max j₀ 1) ^ 2)) (cycBase hn)
    (cycAway ((l ^ max j₀ 1) ^ 2)).subtype (arBase_cycAway _ hn)
  rwa [cycBase_ζ hn] at key

end GlobalTheory.SiegelTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyCyclotomicAwayOddLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor

theorem exists_sFam_cycAway : ∀ g n : ℕ, 1 ≤ g → 3 ≤ n → Odd n → Nonempty (SFam g n (zetaAway n)) := by
  intro g n hg hn hodd
  have hn1 : n ≠ 1 := by omega
  have hlp : n.minFac.Prime := Nat.minFac_prime hn1
  have hln : n.minFac ∣ n := Nat.minFac_dvd n
  have hlodd : Odd n.minFac := Odd.of_dvd_nat hodd hln
  obtain ⟨j, hj, ⟨F⟩⟩ := GlobalTheory.SiegelTor.exists_sFam_primePow_sq g n.minFac hg hlp hlodd
  set l := n.minFac with hl
  set k := (l ^ j) ^ 2 with hk
  have hl3 : 3 ≤ l := by
    rcases hlodd with ⟨m, hm⟩
    have := hlp.two_le
    omega
  have hk3 : 3 ≤ k := by
    have h1 : l ≤ l ^ j := Nat.le_self_pow (by omega) l
    have h2 : l ^ j ≤ (l ^ j) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hkodd : Odd k := (hlodd.pow).pow
  have hN0 : n * k ≠ 0 := by positivity
  have hNodd : Odd (n * k) := hodd.mul hkodd
  obtain ⟨i, hi, hz, -⟩ := GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale k (n * k) hN0 (dvd_mul_left k n)
  obtain ⟨F₂⟩ := GlobalTheory.SiegelFamilyNumberField.nonempty_baseChange F i hi
  rw [hz] at F₂
  haveI : IsDedekindDomain (cycAway (n * k)) := (arBase_cycAway (n * k) hN0).1
  have hup : Nonempty (SFam g (n * k) ((cycBase hN0).ζ : cycAway (n * k))) :=
    GlobalTheory.T.siegelFamily_deeper_level_of_dvd g k (n * k) (cycAway (n * k)) (cycBase hN0) hk3 hNodd (dvd_mul_left k n)
      (by rw [cycBase_ζ]; exact ⟨F₂⟩)
  rw [cycBase_ζ] at hup
  refine GlobalTheory.T.nonempty_siegelFamily_of_divisor_level_same_primes g n (n * k) hn hNodd (dvd_mul_right n k) ⟨2 * j + 1, ?_⟩ hup
  rw [pow_succ', hk, ← pow_mul, mul_comm j 2]
  exact mul_dvd_mul_left n (pow_dvd_pow_of_dvd hln _)

end GlobalTheory.SiegelTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyCyclotomicAwayOddLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelFamily_cyclotomicAway_odd_level : ∀ g n : ℕ, 1 ≤ g → 3 ≤ n → Odd n → Nonempty (SFam g n (zetaAway n)) := by
  first | exact @GlobalTheory.SiegelTor.exists_sFam_cycAway | exact GlobalTheory.SiegelTor.exists_sFam_cycAway | (intros; apply GlobalTheory.SiegelTor.exists_sFam_cycAway <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem exists_isAmpleCls : ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c := by
  intro K _ A
  obtain ⟨L, hL, hamp⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy
    (GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A.X A.ab)
  exact ⟨cls L hL, L, hL, hamp, rfl⟩

end GlobalTheory.AV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClassStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_exists_ampleClass : ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c := by
  first | exact @GlobalTheory.AV.exists_isAmpleCls | exact GlobalTheory.AV.exists_isAmpleCls | (intros; apply GlobalTheory.AV.exists_isAmpleCls <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassSymmNaturalAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassSymmNaturalAdditive
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem lam_symm_nat_add : ∀ (K : Type) [Field K] (A B : AbVar K) (c c' : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (Y Z : Over (Sp K)) (u : Z ⟶ Y) (x y : Y ⟶ A.X), AbVar.lam c x y = AbVar.lam c y x ∧ CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) ∧ AbVar.lam d (x ≫ f.hom) (y ≫ f.hom) = AbVar.lam (CechPic.pull f.hom.left d) x y ∧ AbVar.lam (c + c') x y = AbVar.lam c x y + AbVar.lam c' x y := by
  intro K _ A B c c' d f Y Z u x y
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact CechPic.lam_comm c x y
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact CechPic.pull_lam u c x y
  · rw [AbVar.lam_eq, AbVar.lam_eq]; exact (CechPic.lam_pull f.hom d x y).symm
  · simp only [AbVar.lam, map_add (f := _)]; abel

end GlobalTheory.AV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassSymmNaturalAdditiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive : ∀ (K : Type) [Field K] (A B : AbVar K) (c c' : Pic A.X.left) (d : Pic B.X.left) (f : A ⟶ B) (Y Z : Over (Sp K)) (u : Z ⟶ Y) (x y : Y ⟶ A.X), AbVar.lam c x y = AbVar.lam c y x ∧ CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) ∧ AbVar.lam d (x ≫ f.hom) (y ≫ f.hom) = AbVar.lam (CechPic.pull f.hom.left d) x y ∧ AbVar.lam (c + c') x y = AbVar.lam c x y + AbVar.lam c' x y := by
  first | (exact @GlobalTheory.AV.lam_symm_nat_add) | (exact GlobalTheory.AV.lam_symm_nat_add) | (intros; apply GlobalTheory.AV.lam_symm_nat_add  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleClsIff

theorem isAmpleCls_cls_iff : ∀ (K : Type) [Field K] (A : AbVar K) (L : LB A.X.left) (hL : L.IsLB),
    IsAmpleCls (cls L hL) ↔ IsAmpleLB L := by
  intro K _ A L hL
  have : IsProper A.X.hom := A.ab.proper
  constructor
  · rintro ⟨M, hM, hr, he⟩
    have hM' : IsAmpleLB M := (relAmple_iff_isAmpleLB_of_isAffine A.X hM).1 hr
    exact hM'.of_lbIso hL ((CechPic.cls_eq_iff hL hM).1 he.symm)
  · intro h
    exact ⟨L, hL, (relAmple_iff_isAmpleLB_of_isAffine A.X hL).2 h, rfl⟩

end GlobalTheory.AmpleClsIff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmpleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample : ∀ (K : Type) [Field K] (A : AbVar K) (L : LB A.X.left) (hL : L.IsLB), IsAmpleCls (cls L hL) ↔ IsAmpleLB L := by
  first | exact @GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff | exact GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff | (intros; apply GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomExtPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem ext_of_pt_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f g : A ⟶ B),
    (∀ x : A.Pt, x ≫ f.hom = x ≫ g.hom) → f = g := by
  intro K _ A B f g h
  have := A.ab.smooth
  have := B.ab.proper
  have : IsReduced A.X.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.X.hom
  let Ω := AlgebraicClosure K
  let q : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  have : Surjective q := ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  have : JacobsonSpace ↥(pullback A.X.hom q) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd A.X.hom q)
  have hd : Dense (closedPoints ↥(pullback A.X.hom q)) := dense_iff_closure_eq.2 closure_closedPoints
  have hD := (pullback.fst A.X.hom q).surjective.denseRange.dense_image
    (pullback.fst A.X.hom q).continuous hd
  have hdom : IsDominant (equalizer.ι f.hom.left g.hom.left) := by
    refine ⟨hD.mono ?_⟩
    rintro _ ⟨w, hw₀, rfl⟩
    have hw : IsClosed ({w} : Set ↥(pullback A.X.hom q)) := hw₀
    let y : Sp Ω ⟶ A.X.left :=
      pointOfClosedPoint (pullback.snd A.X.hom q) w hw ≫ pullback.fst A.X.hom q
    have hy : y ≫ A.X.hom = q := by
      simp only [y, Category.assoc, pullback.condition]
      rw [← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
    let x : A.Pt := Over.homMk y hy
    have hx : y ≫ f.hom.left = y ≫ g.hom.left := congrArg CommaMorphism.left (h x)
    refine ⟨equalizer.lift y hx (IsLocalRing.closedPoint Ω), ?_⟩
    change (equalizer.lift y hx ≫ equalizer.ι f.hom.left g.hom.left) (IsLocalRing.closedPoint Ω) = _
    rw [equalizer.lift_ι]
    exact congrArg (pullback.fst A.X.hom q) (pointOfClosedPoint_apply (pullback.snd A.X.hom q) w hw _)
  have : IsDominant (equalizer.ι f.hom.left g.hom.left) := hdom
  have heq : f.hom = g.hom := Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated B.X.hom
    ((Over.w f.hom).trans (Over.w g.hom).symm) (equalizer.ι _ _) (equalizer.condition _ _))
  exact Subtype.ext heq

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPoints
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem archInt_eq_zero_of_isEmpty {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (L M : HermLB q) (e : ℕ)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : L.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
  haveI := hq σ
  simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]

theorem mixArch_eq_zero_of_isEmpty {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) {e : ℕ} (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : mixArch L M hr = 0 := by
  unfold mixArch
  simp [archInt_eq_zero_of_isEmpty hq, FibreProj.pol]

theorem mixArch_resArch_eq_zero_of_noCxPts : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), (∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) → ∀ (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q), (∀ (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), mixArch L M hr = 0) ∧ ∀ (t : M.B.Sec) (z : Y), resArch L M t z = 0 := by
  intro k _ Y _ q hq e L M
  refine ⟨fun r hr => mixArch_eq_zero_of_isEmpty hq L M hr, fun t z => ?_⟩
  unfold resArch
  split_ifs with h
  · refine mixArch_eq_zero_of_isEmpty (fun σ => ?_) _ _ _
    exact (Points.PtsOver.map (cloι z) rfl _ : CxPts (cloι z ≫ q) σ → CxPts q σ).isEmpty
  · rfl

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPointsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), (∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) → ∀ (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q), (∀ (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), mixArch L M hr = 0) ∧ ∀ (t : M.B.Sec) (z : Y), resArch L M t z = 0 := by
  first | exact @GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts | exact GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts | (intros; apply GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimension
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AbFieldDim

theorem exists_smoothOfRelativeDimension : ∀ (k : Type) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A],
    IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  intro k _ A _ hA
  exact GlobalTheory.AbelianDim.exists_relDim k A hA

end GlobalTheory.AbFieldDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimensionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension : ∀ (k : Type) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A], IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  first | (exact @GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension) | (exact GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension) | (intros; apply GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension  <;> assumption)
end
end
