module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.EqPOfSplit
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.TripleSumIndep

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RightMoveTrianglesHold
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RowSwApply
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.Mu

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem yy_stab {N N' : ℕ} {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (f : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E)
    (hfE : ∀ (a : D.host.E) A, f (a • A) = a • f A)
    (hgen : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ M, A *ᵥ x ∈ M') → ∀ x ∈ M, f A *ᵥ x ∈ M')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.YYl D M M') : f A ∈ TaylorLogMetric.YYl D M M' := by
  have hH : TaylorLogMetric.homL D M M' ≤ (TaylorLogMetric.homL D M M').comap f :=
    Submodule.span_le.2 fun B hB => Submodule.subset_span (hgen B hB)
  have hY : TaylorLogMetric.YYl D M M' ≤ (TaylorLogMetric.YYl D M M').comap f := by
    refine Submodule.span_le.2 fun B hB => ?_
    obtain ⟨a, ha, A', hA', rfl⟩ := hB
    show f (a • A') ∈ TaylorLogMetric.YYl D M M'
    rw [hfE]
    exact Submodule.subset_span ⟨a, ha, f A', hH hA', rfl⟩
  exact hY hA

theorem la_stab {N N' : ℕ} (T : TaylorLogMetric.Tor D) {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (Φ : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N')
    (f : Matrix (Fin N') (Fin N) D.host.E → Matrix (Fin N') (Fin N) D.host.E)
    (hΦ : ∀ (w : ℂ) A, Φ (w • TaylorLogMetric.embV D T A) = w • TaylorLogMetric.embV D T (f A))
    (hf : ∀ A ∈ TaylorLogMetric.YYl D M M', f A ∈ TaylorLogMetric.YYl D M M') {z : TaylorLogMetric.VC D N N'} (hz : z ∈ TaylorLogMetric.La D T M M') :
    Φ z ∈ TaylorLogMetric.La D T M M' := by
  unfold TaylorLogMetric.La at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hv
    rw [hΦ]
    exact AddSubgroup.subset_closure ⟨w, hw, f A, hf A hA, rfl⟩
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

theorem mulO_apply {N N' : ℕ} (r : D.host.E) (x : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    J.mulO N N' r x τ i j = TaylorLogMetric.embT D τ r * x τ i j := rfl

theorem mulO_la {N N' : ℕ} (T : TaylorLogMetric.Tor D) (hT : ∀ τ x, T.emb τ x = TaylorLogMetric.embT D τ x)
    {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (r : 𝓞 D.host.E) {z : TaylorLogMetric.VC D N N'} (hz : z ∈ TaylorLogMetric.La D T M M') :
    J.mulO N N' (r : D.host.E) z ∈ TaylorLogMetric.La D T M M' := by
  refine la_stab T (J.mulO N N' (r : D.host.E)).toAddMonoidHom (fun A => (r : D.host.E) • A) ?_ ?_ hz
  · intro w A
    funext τ i j
    simp only [LinearMap.toAddMonoidHom_coe, mulO_apply, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, hT]
    rw [map_mul]; ring
  · intro A hA
    rw [show (r : D.host.E) • A = r • A from algebraMap_smul D.host.E r A]
    exact Submodule.smul_mem _ r hA

theorem mem_stdL {n : ℕ} {v : Fin n → D.host.E} :
    v ∈ StandardLatticesGL3.stdL D n ↔ ∀ i, v i ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp [StandardLatticesGL3.stdL, Submodule.mem_pi]

def swp (n : ℕ) (i : Fin n) : Fin n :=
  ⟨if i.val < n / 2 then i.val + n / 2 else i.val - n / 2, by have := i.isLt; split_ifs <;> omega⟩

theorem swp_val (n : ℕ) (i : Fin n) :
    (swp n i).val = if i.val < n / 2 then i.val + n / 2 else i.val - n / 2 := rfl

theorem swp_swp {n : ℕ} (h : Even n) (i : Fin n) : swp n (swp n i) = i := by
  obtain ⟨k, hk⟩ := h
  apply Fin.ext
  rw [swp_val, swp_val]
  have := i.isLt
  split_ifs <;> omega

theorem swp_lt {n : ℕ} (h : Even n) (i : Fin n) : (swp n i).val < n / 2 ↔ ¬ i.val < n / 2 := by
  obtain ⟨k, hk⟩ := h
  rw [swp_val]; have := i.isLt
  split_ifs <;> omega

def swpE {n : ℕ} (h : Even n) : Equiv.Perm (Fin n) := Function.Involutive.toPerm (swp n) (swp_swp h)

def rowP (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => if i.val < N' / 2 then z τ i j else 0
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp only [Pi.add_apply]; split_ifs <;> simp

def rowSw (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => z τ (swp N' i) j
  map_zero' := rfl
  map_add' _ _ := rfl

def colP (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => if j.val < N / 2 then z τ i j else 0
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp only [Pi.add_apply]; split_ifs <;> simp

def colSw (N N' : ℕ) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => z τ i (swp N j)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem rowP_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    rowP N N' z τ i j = if i.val < N' / 2 then z τ i j else 0 := rfl
theorem rowSw_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    rowSw N N' z τ i j = z τ (swp N' i) j := rfl
theorem colP_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    colP N N' z τ i j = if j.val < N / 2 then z τ i j else 0 := rfl
theorem colSw_apply {N N' : ℕ} (z : TaylorLogMetric.VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    colSw N N' z τ i j = z τ i (swp N j) := rfl

section Facts

variable {N N' : ℕ}

theorem rowProjection_rowProjection (x : TaylorLogMetric.VC D N N') : rowP N N' (rowP N N' x) = rowP N N' x := by
  funext τ i j; simp only [rowP_apply]; split_ifs <;> rfl
theorem colP_colP (x : TaylorLogMetric.VC D N N') : colP N N' (colP N N' x) = colP N N' x := by
  funext τ i j; simp only [colP_apply]; split_ifs <;> rfl

theorem rowProjection_orthogonal (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (rowP N N' x) (y - rowP N N' y) = 0 := by
  rw [Ker.formV_apply, Finset.sum_eq_zero, zero_div]
  intro τ _; refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp only [rowP_apply, Pi.sub_apply]; split_ifs <;> simp
theorem colP_orth (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (colP N N' x) (y - colP N N' y) = 0 := by
  rw [Ker.formV_apply, Finset.sum_eq_zero, zero_div]
  intro τ _; refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp only [colP_apply, Pi.sub_apply]; split_ifs <;> simp

theorem rowSw_sw (h : Even N') (x : TaylorLogMetric.VC D N N') : rowSw N N' (rowSw N N' x) = x := by
  funext τ i j; simp only [rowSw_apply, swp_swp h]
theorem colSw_sw (h : Even N) (x : TaylorLogMetric.VC D N N') : colSw N N' (colSw N N' x) = x := by
  funext τ i j; simp only [colSw_apply, swp_swp h]

theorem rowSw_p (h : Even N') (x : TaylorLogMetric.VC D N N') :
    rowP N N' (rowSw N N' x) = rowSw N N' x - rowSw N N' (rowP N N' x) := by
  funext τ i j
  simp only [rowP_apply, rowSw_apply, Pi.sub_apply]
  have := swp_lt h i
  split_ifs <;> simp_all
theorem colSw_p (h : Even N) (x : TaylorLogMetric.VC D N N') :
    colP N N' (colSw N N' x) = colSw N N' x - colSw N N' (colP N N' x) := by
  funext τ i j
  simp only [colP_apply, colSw_apply, Pi.sub_apply]
  have := swp_lt h j
  split_ifs <;> simp_all

theorem rowSw_form (h : Even N') (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (rowSw N N' x) (rowSw N N' y) = Ker.formV A D.what₂.Tau N N' x y := by
  rw [Ker.formV_apply, Ker.formV_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact Equiv.sum_comp (swpE h) (fun i => ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j))
theorem colSw_form (h : Even N) (A : ℝ) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (colSw N N' x) (colSw N N' y) = Ker.formV A D.what₂.Tau N N' x y := by
  rw [Ker.formV_apply, Ker.formV_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (swpE h) (fun j => x τ i j * (starRingEnd ℂ) (y τ i j))

theorem al_form (T : TaylorLogMetric.Tor D) (f : TaylorLogMetric.VC D N N' → TaylorLogMetric.VC D N N')
    (hf : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (f x) (f y) = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' x y)
    (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T (f x) = TaylorLogMetric.al D T x := by
  unfold TaylorLogMetric.al
  rw [Ker.Hf_eq, Ker.Hf_eq, hf]

theorem mulO_rowP (r : D.host.E) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' r (rowP N N' x) = rowP N N' (J.mulO N N' r x) := by
  funext τ i j; simp only [mulO_apply, rowP_apply]; split_ifs <;> simp
theorem mulO_colP (r : D.host.E) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' r (colP N N' x) = colP N N' (J.mulO N N' r x) := by
  funext τ i j; simp only [mulO_apply, colP_apply]; split_ifs <;> simp

end Facts

section Lat

variable {N N' : ℕ}

def rowPM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => if i.val < N' / 2 then A i j else 0
  map_add' A B := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c A := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def rowSwM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => A (swp N' i) j
  map_add' A B := by ext i j; simp
  map_smul' c A := by ext i j; simp

def colPM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => if j.val < N / 2 then A i j else 0
  map_add' A B := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c A := by refine Matrix.ext fun i j => ?_; simp only [of_apply, Matrix.smul_apply, RingHom.id_apply]; split_ifs <;> simp

def colSwM (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin N') (Fin N) D.host.E where
  toFun A := Matrix.of fun i j => A i (swp N j)
  map_add' A B := by ext i j; simp
  map_smul' c A := by ext i j; simp

variable (T : TaylorLogMetric.Tor D) (hT : ∀ τ x, T.emb τ x = TaylorLogMetric.embT D τ x)
include hT

theorem rowProjection_mem_lattice {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N')) : rowP N N' z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N') := by
  refine la_stab T (rowP N N') (rowPM N N') ?_ (fun A hA => yy_stab (rowPM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j
    simp only [rowP_apply, rowPM, LinearMap.coe_mk, AddHom.coe_mk, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, of_apply, hT]
    split_ifs <;> simp
  · intro a A; refine Matrix.ext fun i j => ?_
    simp only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  · intro A hA x hx
    have h := mem_stdL.1 (hA x hx)
    refine mem_stdL.2 fun i => ?_
    by_cases hi : i.val < N' / 2
    · have e : (rowPM N N' A *ᵥ x) i = (A *ᵥ x) i := by
        simp only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply, if_pos hi]
      rw [e]; exact h i
    · have e : (rowPM N N' A *ᵥ x) i = 0 := by
        simp only [rowPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply, if_neg hi, zero_mul,
          Finset.sum_const_zero]
      rw [e]; exact Submodule.zero_mem _

theorem rowSw_la {M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N')) : rowSw N N' z ∈ TaylorLogMetric.La D T M (StandardLatticesGL3.stdL D N') := by
  refine la_stab T (rowSw N N') (rowSwM N N') ?_ (fun A hA => yy_stab (rowSwM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j; rfl
  · intro a A; ext i j; rfl
  · intro A hA x hx
    have h := mem_stdL.1 (hA x hx)
    exact mem_stdL.2 fun i => h (swp N' i)

theorem colP_mem_la {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M') : colP N N' z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M' := by
  refine la_stab T (colP N N') (colPM N N') ?_ (fun A hA => yy_stab (colPM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j
    simp only [colP_apply, colPM, LinearMap.coe_mk, AddHom.coe_mk, TaylorLogMetric.embV, Pi.smul_apply, smul_eq_mul, of_apply, hT]
    split_ifs <;> simp
  · intro a A; refine Matrix.ext fun i j => ?_
    simp only [colPM, LinearMap.coe_mk, AddHom.coe_mk, of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  · intro A hA x hx
    have hx' : (fun j : Fin N => if j.val < N / 2 then x j else 0) ∈ StandardLatticesGL3.stdL D N := by
      refine mem_stdL.2 fun j => ?_
      split_ifs
      · exact mem_stdL.1 hx j
      · exact Submodule.zero_mem _
    have e : colPM N N' A *ᵥ x = A *ᵥ (fun j : Fin N => if j.val < N / 2 then x j else 0) := by
      funext i
      simp only [colPM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [e]; exact hA _ hx'

theorem colSw_la (hN : Even N) {M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {z : TaylorLogMetric.VC D N N'}
    (hz : z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M') : colSw N N' z ∈ TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) M' := by
  refine la_stab T (colSw N N') (colSwM N N') ?_ (fun A hA => yy_stab (colSwM N N') ?_ ?_ hA) hz
  · intro w A; funext τ i j; rfl
  · intro a A; ext i j; rfl
  · intro A hA x hx
    have hx' : (fun j : Fin N => x (swp N j)) ∈ StandardLatticesGL3.stdL D N := mem_stdL.2 fun j => mem_stdL.1 hx (swp N j)
    have e : colSwM N N' A *ᵥ x = A *ᵥ (fun j : Fin N => x (swp N j)) := by
      funext i
      simp only [colSwM, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, of_apply]
      have := Equiv.sum_comp (swpE hN) (fun j => A i j * x (swp N j))
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      show A i (swp N j) * x j = A i (swp N j) * x (swp N (swp N j))
      rw [swp_swp hN]
    rw [e]; exact hA _ hx'

end Lat

section Mult

variable {N N' : ℕ}

theorem mulO_mul (r r' : D.host.E) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' r (J.mulO N N' r' x) = J.mulO N N' (r * r') x := by
  funext τ i j; simp only [mulO_apply, map_mul]; ring

theorem form_mul (A : ℝ) (l s : D.host.E) (n : ℕ) (hl : star l * l = -1 + (n : D.host.E) * s)
    (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (J.mulO N N' l x) (J.mulO N N' l y)
      = -Ker.formV A D.what₂.Tau N N' x y + (n : ℂ) * Ker.formV A D.what₂.Tau N N' x (J.mulO N N' s y) := by
  rw [J.mulO_adj, mulO_mul, hl]
  have : J.mulO N N' (-1 + (n : D.host.E) * s) y = -y + n • J.mulO N N' s y := by
    funext τ i j
    simp only [mulO_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, map_add (f := _), map_neg, map_one, map_mul, map_natCast]
    simp only [nsmul_eq_mul]
    ring
  rw [this, map_add (f := _), map_neg, map_nsmul, nsmul_eq_mul]

theorem al_mul (T : TaylorLogMetric.Tor D) {La' : AddSubgroup (TaylorLogMetric.VC D N N')} (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T La')
    (l s : D.host.E) (e : ℕ) (hl : star l * l = -1 + ((4 * e : ℕ) : D.host.E) * s) {x : TaylorLogMetric.VC D N N'}
    (hx : x ∈ La') (hmx : J.mulO N N' l x ∈ La') (hsx : J.mulO N N' s x ∈ La') :
    TaylorLogMetric.al D T (J.mulO N N' l x) = TaylorLogMetric.al D T x := by
  obtain ⟨m0, h0re, h0r⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.self_int T hI hx
  obtain ⟨m1, h1re, h1r⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.self_int T hI hmx
  obtain ⟨a, b, -, hab⟩ := hI x hx _ hsx
  have hf : TaylorLogMetric.Hf D T (J.mulO N N' l x) (J.mulO N N' l x)
      = -TaylorLogMetric.Hf D T x x + ((4 * e : ℕ) : ℂ) * TaylorLogMetric.Hf D T x (J.mulO N N' s x) :=
    form_mul (TaylorLogMetric.area T.abelian₂) l s (4 * e) hl x x
  rw [hab] at hf
  have hre : (TaylorLogMetric.Hf D T (J.mulO N N' l x) (J.mulO N N' l x)).re
      = -(TaylorLogMetric.Hf D T x x).re + ((4 * e : ℕ) : ℝ) * (a / Real.sqrt D.host.d) := by
    rw [hf, Complex.add_re, Complex.neg_re,
      show ((4 * e : ℕ) : ℂ) = (((4 * e : ℕ) : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul]
    simp
  have key : (m1 : ℝ) = -m0 + 2 * e * a := by
    rw [h1re, h0re] at hre
    have hs := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
    field_simp at hre
    push_cast at hre
    linarith
  have key' : m1 = -m0 + 2 * e * a := by exact_mod_cast key
  unfold TaylorLogMetric.al
  rw [h1r, h0r]
  apply Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.neg_one_zpow_congr
  rw [key']
  exact ⟨-m0 + e * a, by ring⟩

theorem altE_mul (T : TaylorLogMetric.Tor D) {La' : AddSubgroup (TaylorLogMetric.VC D N N')} (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T La')
    (l s : D.host.E) (e : ℕ) (hl : star l * l = -1 + ((4 * e : ℕ) : D.host.E) * s) {z y : TaylorLogMetric.VC D N N'}
    (hez : e • z ∈ La') (hsy : J.mulO N N' s y ∈ La') :
    ∃ k : ℤ, altE (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (J.mulO N N' l z) (J.mulO N N' l y)
      = -altE (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') z y + 2 * k := by
  obtain ⟨a, b, -, hab⟩ := hI _ hez _ hsy
  have hb : (e : ℝ) * (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z (J.mulO N N' s y)).im = b := by
    have h1 : Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (e • z) (J.mulO N N' s y)
        = ((e : ℝ) : ℂ) * Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z (J.mulO N N' s y) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, map_smul, LinearMap.smul_apply, smul_eq_mul]; push_cast; ring
    have h2 := congrArg Complex.im hab
    rw [show TaylorLogMetric.Hf D T (e • z) (J.mulO N N' s y)
        = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (e • z) (J.mulO N N' s y) from rfl, h1,
      Complex.im_ofReal_mul] at h2
    rw [h2]; simp
  have hf := form_mul (TaylorLogMetric.area T.abelian₂) l s (4 * e) hl z y
  refine ⟨2 * b, ?_⟩
  unfold altE
  rw [hf, Complex.add_im, Complex.neg_im,
    show ((4 * e : ℕ) : ℂ) = (((4 * e : ℕ) : ℝ) : ℂ) by norm_cast, Complex.im_ofReal_mul]
  push_cast
  linarith [hb]

theorem mulO_inv (l s l' : D.host.E) (e : ℕ) (hl : star l * l = -1 + ((4 * e : ℕ) : D.host.E) * s)
    (hl' : l' = star l) (x : TaylorLogMetric.VC D N N') :
    J.mulO N N' (-l') (J.mulO N N' l x) = x + e • J.mulO N N' (-4 * s) x ∧
    J.mulO N N' l (J.mulO N N' (-l') x) = x + e • J.mulO N N' (-4 * s) x := by
  have hE : -l' * l = 1 + (e : D.host.E) * (-4 * s) := by
    rw [hl', neg_mul, hl]; push_cast; ring
  constructor
  · funext τ i j
    have := congrArg (TaylorLogMetric.embT D τ) hE
    simp only [map_mul, map_add (f := _), map_one, map_natCast, map_neg, map_ofNat] at this
    simp only [mulO_apply, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, map_mul, map_neg, map_ofNat]
    linear_combination x τ i j * this
  · funext τ i j
    have := congrArg (TaylorLogMetric.embT D τ) hE
    simp only [map_mul, map_add (f := _), map_one, map_natCast, map_neg, map_ofNat] at this
    simp only [mulO_apply, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, map_mul, map_neg, map_ofNat]
    linear_combination x τ i j * this

end Mult

end Formalism.L2.PairingIndexBounds.Eq.Mu
end
end

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.Mu

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem signData_of (T : TaylorLogMetric.Tor D) {N N' : ℕ} {Λ₁ Λ₂ Λ₃ : AddSubgroup (TaylorLogMetric.VC D N N')}
    (p σ : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N') (pp : ∀ x, p (p x) = p x)
    (porth : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (p x) (y - p y) = 0)
    (σσ : ∀ x, σ (σ x) = x) (σp : ∀ x, p (σ x) = σ x - σ (p x))
    (σH : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (σ x) (σ y) = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' x y)
    (hmp : ∀ (r : D.host.E) x, J.mulO N N' r (p x) = p (J.mulO N N' r x))
    (hΛ : ∀ Λ, Λ = Λ₁ ∨ Λ = Λ₂ ∨ Λ = Λ₃ → (∀ x ∈ Λ, p x ∈ Λ) ∧ (∀ x ∈ Λ, σ x ∈ Λ) ∧
      (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) ∧ Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T Λ)
    (e : ℕ) (e21 : ∀ x ∈ Λ₂, e • x ∈ Λ₁) (e31 : ∀ x ∈ Λ₃, e • x ∈ Λ₁) (e32 : ∀ x ∈ Λ₃, e • x ∈ Λ₂)
    (l s l' : 𝓞 D.host.E) (hl : star (l : D.host.E) * l = -1 + ((4 * e : ℕ) : D.host.E) * s)
    (hl' : (l' : D.host.E) = star (l : D.host.E)) :
    SignData (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) Λ₁ Λ₂ Λ₃ p σ
      (J.mulO N N' (l : D.host.E)).toAddMonoidHom (J.mulO N N' (-(l' : D.host.E))).toAddMonoidHom
      (J.mulO N N' (-4 * (s : D.host.E))).toAddMonoidHom e := by
  obtain ⟨p1, σ1, m1, I1⟩ := hΛ Λ₁ (Or.inl rfl)
  obtain ⟨p2, σ2, m2, I2⟩ := hΛ Λ₂ (Or.inr (Or.inl rfl))
  obtain ⟨p3, σ3, m3, I3⟩ := hΛ Λ₃ (Or.inr (Or.inr rfl))
  have mn : ∀ {Λ : AddSubgroup (TaylorLogMetric.VC D N N')}, (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) →
      ∀ x ∈ Λ, J.mulO N N' (-(l' : D.host.E)) x ∈ Λ := fun h x hx => by
    have := h (-l') x hx; simpa using this
  have mr : ∀ {Λ : AddSubgroup (TaylorLogMetric.VC D N N')}, (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) →
      ∀ x ∈ Λ, J.mulO N N' (-4 * (s : D.host.E)) x ∈ Λ := fun h x hx => by
    have := h (-(s + s + s + s)) x hx
    rwa [show ((-(s + s + s + s) : 𝓞 D.host.E) : D.host.E) = -4 * (s : D.host.E) by push_cast; ring] at this
  exact
  { pp := pp, porth := porth, p1 := p1, p2 := p2, p3 := p3
    σσ := σσ, σp := σp, σH := σH, σα := fun x => al_form T σ σH x
    σ1 := σ1, σ2 := σ2, σ3 := σ3
    mp := fun x => hmp _ x, m'p := fun x => hmp _ x
    m1 := m1 l, m2 := m2 l, m3 := m3 l
    m'1 := mn m1, m'2 := mn m2, m'3 := mn m3
    r2 := mr m2, r3 := mr m3
    inv := fun x => (mulO_inv (l : D.host.E) (s : D.host.E) (l' : D.host.E) e hl hl' x).1
    inv' := fun x => (mulO_inv (l : D.host.E) (s : D.host.E) (l' : D.host.E) e hl hl' x).2
    e21 := e21, e31 := e31, e32 := e32
    mα1 := fun x hx => al_mul T I1 (l : D.host.E) (s : D.host.E) e hl hx (m1 l x hx) (m1 s x hx)
    mα2 := fun x hx => al_mul T I2 (l : D.host.E) (s : D.host.E) e hl hx (m2 l x hx) (m2 s x hx)
    mα3 := fun x hx => al_mul T I3 (l : D.host.E) (s : D.host.E) e hl hx (m3 l x hx) (m3 s x hx)
    mH := fun z hz y hy => altE_mul T I2 (l : D.host.E) (s : D.host.E) e hl (e32 z hz) (m2 s y hy) }

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem muOneL_of (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : MuOneL B := by
  intro N N' L L₁ hN hN' hL hL₁
  have hLat := B.latAll hcc hδ h0
  have a1 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) (sd0 N')
  have a2 := admissible_of_integral_conj_le (D := D) hN hN' hL (sd0 N')
  have a3 := admissible_of_integral_conj_le (D := D) hN hN' hL₁ (sd0 N')
  have hT : TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) := by
    exact ⟨formV_herm' _ _ _ _, (hLat.1 N N' _ _ a1).1, (hLat.1 N N' _ _ a2).1,
      (hLat.1 N N' _ _ a3).1, (hLat.1 N N' _ _ a1).2, (hLat.1 N N' _ _ a2).2,
      (hLat.1 N N' _ _ a3).2, (hLat.2 N N' _ _ _ _ a1 a2).1,
      (hLat.2 N N' _ _ _ _ a1 a2).2, (hLat.2 N N' _ _ _ _ a1 a3).1,
      (hLat.2 N N' _ _ _ _ a1 a3).2, (hLat.2 N N' _ _ _ _ a2 a3).1,
      (hLat.2 N N' _ _ _ _ a2 a3).2⟩
  obtain ⟨S₂, hS₂⟩ := (repsExist _ _ _ hT.i₁₂).1
  obtain ⟨S₃, hS₃⟩ := (repsExist _ _ _ hT.i₂₃).1
  refine ⟨S₂, S₃, hS₂, hS₃, ?_⟩
  obtain ⟨e, he, e21, e31, e32⟩ := exists_e hT
  obtain ⟨l, s, -, hl⟩ := J.negOneNorm D (4 * e) (by omega)
  obtain ⟨l', hl'⟩ := J.star_int l
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), F ≠ 0 :=
    ⟨B.thZero N N', (B.thZeroMem hS N N').2, B.thZero_ne_zero hS N N'⟩
  have hemb : ∀ τ x, (B.tor).emb τ x = TaylorLogMetric.embT D τ x := fun _ _ => rfl
  refine tripleMu_eq_one hT hF (signData_of B.tor (rowP N N') (rowSw N N') rowProjection_rowProjection (rowProjection_orthogonal _) (rowSw_sw hN')
    (rowSw_p hN') (rowSw_form hN' _) mulO_rowP ?_ e e21 e31 e32 l s l' hl hl') hS₂ hS₃
  intro Λ hΛ
  rcases hΛ with rfl | rfl | rfl
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N'))⟩
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' hL (sd0 N'))⟩
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' hL₁ (sd0 N'))⟩

theorem muOneR_of (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : MuOneR B := by
  intro N N' L' L'' hN hN' hL' hL''
  have hLat := B.latAll hcc hδ h0
  have a1 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) (sd0 N')
  have a2 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) hL'
  have a3 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) hL''
  have hT : TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') := by
    exact ⟨formV_herm' _ _ _ _, (hLat.1 N N' _ _ a1).1, (hLat.1 N N' _ _ a2).1,
      (hLat.1 N N' _ _ a3).1, (hLat.1 N N' _ _ a1).2, (hLat.1 N N' _ _ a2).2,
      (hLat.1 N N' _ _ a3).2, (hLat.2 N N' _ _ _ _ a1 a2).1,
      (hLat.2 N N' _ _ _ _ a1 a2).2, (hLat.2 N N' _ _ _ _ a1 a3).1,
      (hLat.2 N N' _ _ _ _ a1 a3).2, (hLat.2 N N' _ _ _ _ a2 a3).1,
      (hLat.2 N N' _ _ _ _ a2 a3).2⟩
  obtain ⟨S₂, hS₂⟩ := (repsExist _ _ _ hT.i₁₂).1
  obtain ⟨S₃, hS₃⟩ := (repsExist _ _ _ hT.i₂₃).1
  refine ⟨S₂, S₃, hS₂, hS₃, ?_⟩
  obtain ⟨e, he, e21, e31, e32⟩ := exists_e hT
  obtain ⟨l, s, -, hl⟩ := J.negOneNorm D (4 * e) (by omega)
  obtain ⟨l', hl'⟩ := J.star_int l
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), F ≠ 0 :=
    ⟨B.thZero N N', (B.thZeroMem hS N N').2, B.thZero_ne_zero hS N N'⟩
  have hemb : ∀ τ x, (B.tor).emb τ x = TaylorLogMetric.embT D τ x := fun _ _ => rfl
  refine tripleMu_eq_one hT hF (signData_of B.tor (colP N N') (colSw N N') colP_colP (colP_orth _) (colSw_sw hN)
    (colSw_p hN) (colSw_form hN _) mulO_colP ?_ e e21 e31 e32 l s l' hl hl') hS₂ hS₃
  intro Λ hΛ
  rcases hΛ with rfl | rfl | rfl
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N'))⟩
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) hL')⟩
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) hL'')⟩

theorem left_move_triangles_hold (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : Tr0L D B.tor :=
  left_move_triangles_of_unit (B.latAll hcc hδ h0) (muOneL_of hcc hδ h0 B hS)

theorem right_move_triangles_hold (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : Tr0R D B.tor :=
  right_move_triangles_of_unit (B.latAll hcc hδ h0) (muOneR_of hcc hδ h0 B hS)

end Formalism.L2.PairingIndexBounds.Eq.Mu
end
end

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_top (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hSp : Sq.SqSplit B) : B.EqP χ :=
  Sq.eqP_of_split B hcc hδ hδ0 hS χ hχ hSp (Mu.left_move_triangles_hold hcc hδ hδ0 B hS) (Mu.right_move_triangles_hold hcc hδ hδ0 B hS)

end Formalism.L2.PairingIndexBounds.Eq
