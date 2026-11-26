module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
public import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweChar
public import Development.DiscreteGroups.GlobalIrreducibility.DzGenCpt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.CondEx
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.condEx :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ ψ : AddChar E Circle, Continuous ψ → ψ ≠ 1 → ∃ d : ℤ, HasConductor ψ (ϖ ^ d) := by
  intro E _ _ _ _ ϖ hϖ ψ hψ hψ1
  obtain ⟨c, hc⟩ := DiscreteGroups.sglob.DzType.exists_hasConductor_of_continuous_ne_one ψ hψ hψ1
  have h1 : ord E ϖ = 1 := ord_eq_one (k := E) hϖ
  have hz : ∀ d : ℤ, ord E (ϖ ^ d) = d := by
    intro d
    cases d with
    | ofNat n => simp [DiscreteGroups.sglob.DzType.ord_pow_bis, h1]
    | negSucc n =>
      rw [zpow_negSucc, DiscreteGroups.sglob.DzType.ord_inv_eq_neg_ord, DiscreteGroups.sglob.DzType.ord_pow_bis, h1, Int.negSucc_eq]
      push_cast; ring
  have hv : valuation E ((ϖ ^ ord E c : Eˣ) : E) = valuation E (c : E) :=
    le_antisymm ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))
      ((DiscreteGroups.sglob.DzType.valuation_le_iff_ord_le _ _).2 (by rw [hz]))
  refine ⟨ord E c, fun x => ?_⟩
  rw [hv]
  exact hc x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.InjMat
open ValuativeRel Matrix

namespace UpperTheory.V.Z.Tf.L4

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ} {r s t : ValueGroupWithZero E} {A B M N : Matrix (Fin n) (Fin n) E}

def Bd (s : ValueGroupWithZero E) (M : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, valuation E (M i j) ≤ s

private theorem Bd.mul (h : Bd s M) (h' : Bd t N) : Bd (s * t) (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun l _ => by rw [map_mul]; exact mul_le_mul' (h i l) (h' l j)

private theorem Bd.add (h : Bd s M) (h' : Bd s N) : Bd s (M + N) := fun i j => Valuation.map_add_le _ (h i j) (h' i j)

private theorem Bd.sub (h : Bd s M) (h' : Bd s N) : Bd s (M - N) := fun i j => Valuation.map_sub_le _ (h i j) (h' i j)

private theorem Bd.mono (h : Bd s M) (e : s ≤ t) : Bd t M := fun i j => (h i j).trans e

private theorem Bd.smul (h : Bd s M) (x : E) : Bd (valuation E x * s) (x • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_mul' le_rfl (h i j)

private theorem bd_one : Bd 1 (1 : Matrix (Fin n) (Fin n) E) := fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

private theorem solve (hr : r < 1) (hA : Bd r (A - 1)) (e : A * M = B) (hB : Bd s B) : Bd s M := by
  intro i j
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun p : Fin n × Fin n => valuation E (M p.1 p.2))
    ⟨(i, j), Finset.mem_univ _⟩
  have hM : Bd (valuation E (M p.1 p.2)) M := fun a b => hp (a, b) (Finset.mem_univ _)
  have e2 : M = B - (A - 1) * M := by rw [← e, sub_mul, one_mul, sub_sub_cancel]
  refine (hM i j).trans (not_lt.1 fun hlt => ?_)
  have h0 : 0 < valuation E (M p.1 p.2) := lt_of_le_of_lt zero_le hlt
  have h1 := congrArg (valuation E) (congrFun (congrFun e2 p.1) p.2)
  rw [Matrix.sub_apply] at h1
  refine (lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ((hB _ _).trans_lt hlt) ?_)).ne' h1
  exact ((hA.mul hM) _ _).trans_lt (mul_lt_of_lt_one_left h0 hr)

private theorem near (hr : r < 1) (hA : Bd r (A - 1)) (e : A * M = B) (hB : Bd r (B - 1)) : Bd r (M - 1) := by
  have h1 : Bd 1 M := solve hr hA e (by simpa using (hB.mono hr.le).add bd_one)
  have e2 : M - 1 = (B - 1) - (A - 1) * M := by rw [← e, sub_mul, one_mul]; abel
  rw [e2]
  exact hB.sub (by simpa using hA.mul h1)

private theorem unit_of (hr : r < 1) (hA : Bd r (A - 1)) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨x, hx, h⟩
  have h1 : Bd 0 (Matrix.of fun i (_ : Fin n) => x i) := solve hr hA (B := 0) (by
    ext i j
    exact congrFun h i) fun i j => by simp
  exact hx (funext fun i => by simpa using h1 i i)


variable (E n) in
private def Js : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => if (i : ℕ) = j + 1 then 1 else 0

private theorem Js_bd : Bd 1 (Js E n) := fun i j => by
  rw [Js, Matrix.of_apply]; split_ifs <;> simp

private theorem Js_pow (k : ℕ) (i j : Fin n) : (Js E n ^ k) i j = if (i : ℕ) = j + k then 1 else 0 := by
  induction k generalizing i with
  | zero => simp [Matrix.one_apply, Fin.ext_iff]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    have hJ : ∀ a b : Fin n, Js E n a b = if (a : ℕ) = b + 1 then 1 else 0 := fun _ _ => rfl
    simp only [ih, hJ]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j + k, by omega⟩]
      · simp; omega
      · intro b _ hb
        rw [if_neg (c := (b : ℕ) = j + k) fun e => hb (Fin.ext e), mul_zero]
      · simp
    · refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs <;> first | omega | simp

private theorem pow_near (hr : r ≤ 1) {Y : Matrix (Fin n) (Fin n) E} (hY : Bd r Y) (k : ℕ) :
    Bd 1 (Js E n ^ k) ∧ Bd r ((Js E n + Y) ^ k - Js E n ^ k) := by
  induction k with
  | zero => exact ⟨by simpa using bd_one, fun i j => by simp⟩
  | succ k ih =>
    refine ⟨by simpa [pow_succ] using ih.1.mul Js_bd, ?_⟩
    have e : (Js E n + Y) ^ (k + 1) - Js E n ^ (k + 1) =
        ((Js E n + Y) ^ k - Js E n ^ k) * (Js E n + Y) + Js E n ^ k * Y := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [e]
    exact Bd.add (by simpa using ih.2.mul (Js_bd.add (hY.mono hr))) (by simpa using ih.1.mul hY)

private theorem cyclic (hr : r < 1) {Y Z u : Matrix (Fin (n + 1)) (Fin (n + 1)) E} (hY : Bd r Y) (hZ : Bd r Z)
    (hu : ∀ j, u (Fin.last n) j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (Fin.last n) j)
    (e : (Js E _ + Y) * u = u * (Js E _ + Z)) : Bd r (u - 1) := by
  have ek : ∀ k : ℕ, (Js E _ + Y) ^ k * u = u * (Js E _ + Z) ^ k := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, e, mul_assoc, ← pow_succ']
  have hn : ∀ {W : Matrix (Fin (n + 1)) (Fin (n + 1)) E}, Bd r W →
      Bd r ((Matrix.of fun (i j : Fin (n + 1)) => ((Js E (n + 1) + W) ^ (n - (i : ℕ)) : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (Fin.last n) j) - 1) :=
    fun {W} hW i j => by
      have h1 := (pow_near hr.le hW (n - (i : ℕ))).2 (Fin.last n) j
      rw [Matrix.sub_apply, Js_pow] at h1
      rw [Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
      convert h1 using 4
      rw [Fin.ext_iff, Fin.val_last]
      have := i.2; have := j.2
      omega
  refine near hr (hn hY) ?_ (hn hZ)
  ext i j
  have h1 := congrFun (congrFun (ek (n - (i : ℕ))) (Fin.last n)) j
  rw [Matrix.mul_apply, Matrix.mul_apply] at h1
  simp only [hu] at h1
  rw [← Matrix.mul_apply (M := 1), one_mul] at h1
  exact h1

section Local

variable [TopologicalSpace E] [IsNonarchimedeanLocalField E]

private theorem sep {V : Type} [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V] (S : Set V) (hS : S.Finite)
    (ht : Submodule.span E S = ⊤) (D : V) (hD : D ∉ Submodule.span 𝒪[E] S) :
    ∃ φ : V →ₗ[E] E, (∀ x ∈ S, valuation E (φ x) ≤ 1) ∧ 1 < valuation E (φ D) := by
  haveI : (Submodule.span 𝒪[E] S).IsLattice E := Submodule.IsLattice.of_fg E (Submodule.fg_span hS)
  haveI : (Submodule.span 𝒪[E] S).IsFullLattice E := ⟨by rw [Submodule.span_span_of_tower, ht]⟩
  haveI : Module.Free 𝒪[E] (Submodule.span 𝒪[E] S) := Submodule.IsLattice.free E _
  haveI : Module.Finite 𝒪[E] (Submodule.span 𝒪[E] S) := Submodule.IsLattice.finite E _
  let b := Module.Free.chooseBasis 𝒪[E] (Submodule.span 𝒪[E] S)
  let c := b.extendOfIsFullLattice E
  have hc : ∀ i, c i = b i := fun i => by simp [c]
  by_contra h
  push Not at h
  apply hD
  have h1 : ∀ i, valuation E (c.repr D i) ≤ 1 := fun i => h (c.coord i) fun x hx => by
    have e : x = ∑ j, ((b.repr ⟨x, Submodule.subset_span hx⟩ j : 𝒪[E]) : E) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, Submodule.subset_span hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
      refine this.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [hc]
      exact (algebraMap_smul E _ _).symm
    rw [e, Module.Basis.coord_apply, c.repr_sum_self]
    exact (b.repr ⟨x, Submodule.subset_span hx⟩ i).2
  rw [← c.sum_repr D]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e : c.repr D i • c i = (⟨c.repr D i, h1 i⟩ : 𝒪[E]) • (b i : V) := by
    rw [hc]
    exact algebraMap_smul E (⟨c.repr D i, h1 i⟩ : 𝒪[E]) _
  rw [e]
  exact Submodule.smul_mem _ _ (b i).2

private theorem dual (u w D : Matrix (Fin n) (Fin n) E) (h : ¬ ∃ Y Z, Bd 1 Y ∧ Bd 1 Z ∧ D = Z + w * Y * u) :
    ∃ X, Bd 1 X ∧ Bd 1 (u * X * w) ∧ 1 < valuation E (D * X).trace := by
  let S₁ : Set (Matrix (Fin n) (Fin n) E) := Set.range fun p : Fin n × Fin n => Matrix.single p.1 p.2 1
  let S₂ : Set (Matrix (Fin n) (Fin n) E) := Set.range fun p : Fin n × Fin n => w * Matrix.single p.1 p.2 1 * u
  have hb : ∀ i j : Fin n, Bd 1 (Matrix.single i j (1 : E)) := fun i j a b => by
    rw [Matrix.single_apply]; split_ifs <;> simp
  have hz : Bd 1 (0 : Matrix (Fin n) (Fin n) E) := fun _ _ => by simp
  obtain ⟨φ, h1, h2⟩ := sep (E := E) (S₁ ∪ S₂) ((Set.finite_range _).union (Set.finite_range _)) (by
    refine eq_top_iff.2 fun M _ => ?_
    rw [Matrix.matrix_eq_sum_single M]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : E) by simp]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨(i, j), rfl⟩))) D fun hD => h (by
      clear h
      induction hD using Submodule.span_induction with
      | mem x hx =>
        rcases hx with ⟨p, rfl⟩ | ⟨p, rfl⟩
        · exact ⟨0, _, hz, hb p.1 p.2, by simp⟩
        · exact ⟨_, 0, hb p.1 p.2, hz, by simp⟩
      | zero => exact ⟨0, 0, hz, hz, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨Y, Z, a1, a2, rfl⟩ := hx
        obtain ⟨Y', Z', b1, b2, rfl⟩ := hy
        exact ⟨Y + Y', Z + Z', a1.add b1, a2.add b2, by noncomm_ring⟩
      | smul a x _ hx =>
        obtain ⟨Y, Z, a1, a2, rfl⟩ := hx
        have ha : valuation E (a : E) * 1 ≤ 1 := by rw [mul_one]; exact a.2
        refine ⟨(a : E) • Y, (a : E) • Z, (a1.smul _).mono ha, (a2.smul _).mono ha, ?_⟩
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
        rfl)
  let X : Matrix (Fin n) (Fin n) E := Matrix.of fun j i => φ (Matrix.single i j 1)
  have hX : ∀ M : Matrix (Fin n) (Fin n) E, (M * X).trace = φ M := fun M => by
    conv_rhs => rw [Matrix.matrix_eq_sum_single M]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Matrix.trace, Matrix.diag, Matrix.mul_apply, X, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : E) by simp, map_smul, smul_eq_mul]
  refine ⟨X, fun j i => h1 _ (Or.inl ⟨(i, j), rfl⟩), fun j i => ?_, by rwa [hX]⟩
  have e : (u * X * w) j i = φ (w * Matrix.single i j 1 * u) := by
    rw [← hX, mul_assoc (w * _), mul_assoc w, Matrix.trace_mul_comm w, mul_assoc (Matrix.single i j 1), Matrix.trace_single_mul, one_smul]
  rw [e]
  exact h1 _ (Or.inr ⟨(i, j), rfl⟩)

private theorem sd_eq (g : GL (Fin n) E) : GlobalTheory.Whittaker.superDiag g = (Js E n * (g : Matrix (Fin n) (Fin n) E)).trace := by
  have hJ : ∀ a b : Fin n, Js E n a b = if (a : ℕ) = b + 1 then 1 else 0 := fun _ _ => rfl
  simp only [GlobalTheory.Whittaker.superDiag, Matrix.trace, Matrix.diag, Matrix.mul_apply, hJ, Finset.sum_filter, ite_mul, one_mul, zero_mul]
  exact Finset.sum_comm

theorem not_intertwine (p : Eˣ) (hp : valuation E (p : E) < 1) (ψ : AddChar E Circle)
    (hψ : ∀ x : E, valuation E ((p : E) * p) < valuation E x → ∃ y, valuation E y ≤ valuation E x ∧ ψ y ≠ 1)
    (u : GL (Fin n) E) (hu : u ∈ GlobalTheory.SmGL.unipB E (Fin n)) (h : ¬ Bd (valuation E (p : E)) ((u : Matrix (Fin n) (Fin n) E) - 1)) :
    ∃ k : GL (Fin n) E, Bd (valuation E (p : E)) ((k : Matrix (Fin n) (Fin n) E) - 1) ∧
      Bd (valuation E (p : E)) (((u * k * u⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) ∧
      ψ (GlobalTheory.Whittaker.superDiag (u * k * u⁻¹)) ≠ ψ (GlobalTheory.Whittaker.superDiag k) := by
  rcases n with _ | n
  · exact absurd (fun i => i.elim0) h
  obtain ⟨U, hU⟩ : ∃ U, U = (u : Matrix (Fin (n + 1)) (Fin (n + 1)) E) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = ((u⁻¹ : GL (Fin (n + 1)) E) : Matrix (Fin (n + 1)) (Fin (n + 1)) E) := ⟨_, rfl⟩
  have hUW : U * W = 1 := by rw [hU, hW, Units.mul_inv]
  have hp0 : (p : E) ≠ 0 := p.ne_zero
  obtain ⟨X, h1, h2, h3⟩ := dual U W ((p : E)⁻¹ • (W * Js E _ * U - Js E _)) (by
    rintro ⟨Y, Z, a1, a2, e⟩
    refine h (cyclic (Y := (-(p : E)) • Y) (Z := (p : E) • Z) hp (by simpa using a1.smul (-(p : E))) (by simpa using a2.smul (p : E))
      (fun j => ?_) ?_)
    · rcases (Fin.le_last j).lt_or_eq with hj | rfl
      · rw [((GlobalTheory.SmGL.mem_unipB _).1 hu).1 _ _ hj, Matrix.one_apply_ne hj.ne']
      · rw [((GlobalTheory.SmGL.mem_unipB _).1 hu).2, Matrix.one_apply_eq]
    · have e2 := congrArg (fun M => U * ((p : E) • M)) e
      simp only [smul_smul, mul_inv_cancel₀ hp0, one_smul, smul_add, mul_sub, mul_add, ← mul_assoc, hUW, one_mul,
        Matrix.mul_smul] at e2
      rw [← hU, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, neg_smul, sub_eq_iff_eq_add.1 e2]
      abel)
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h3
  generalize hT : ((W * Js E _ * U - Js E _) * X).trace = T at h3
  have hv : valuation E ((p : E) * p) < valuation E (p * T) := by
    rw [show (p : E) * T = p * p * ((p : E)⁻¹ * T) by field_simp, map_mul _ (p * p : E)]
    exact lt_mul_of_one_lt_right (zero_lt_iff.2 (by simp)) h3
  obtain ⟨y, hy, hy1⟩ := hψ _ hv
  have hx0 : (p : E) * T ≠ 0 := fun e => by rw [e, map_zero] at hv; exact not_lt_zero hv
  have ht : valuation E (y / (p * T) * p) * 1 ≤ valuation E (p : E) := by
    rw [mul_one, map_mul, map_div₀]
    exact mul_le_of_le_one_left' (div_le_one_of_le₀ hy zero_le)
  have hk : Bd (valuation E (p : E)) ((1 + (y / (p * T) * p) • X) - 1) := by
    rw [add_sub_cancel_left]
    exact (h1.smul _).mono ht
  obtain ⟨k, hk'⟩ := unit_of hp hk
  have hc : ((u * k * u⁻¹ : GL (Fin (n + 1)) E) : Matrix (Fin (n + 1)) (Fin (n + 1)) E) = 1 + (y / (p * T) * p) • (U * X * W) := by
    rw [Units.val_mul, Units.val_mul, hk', ← hU, ← hW, mul_add, add_mul, mul_one, hUW, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨k, hk' ▸ hk, ?_, fun e => hy1 ?_⟩
  · rw [hc, add_sub_cancel_left]
    exact (h2.smul _).mono ht
  · have e2 : GlobalTheory.Whittaker.superDiag (u * k * u⁻¹) = GlobalTheory.Whittaker.superDiag k + y := by
      rw [sd_eq, sd_eq, hc, hk', mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_smul,
        Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
      have e3 : (Js E _ * (U * X * W)).trace = T + (Js E _ * X).trace := by
        rw [← hT, sub_mul, Matrix.trace_sub, sub_add_cancel, ← mul_assoc, Matrix.trace_mul_comm _ W]
        simp only [mul_assoc]
      rw [e3, mul_add, mul_assoc (y / (p * T)), div_mul_cancel₀ _ hx0]
      ring
    rw [e2, AddChar.map_add_eq_mul] at e
    exact mul_eq_left.1 e

end Local

end UpperTheory.V.Z.Tf.L4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.UlFact
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.ulFact :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a → ∀ x ∈ howeSet n ϖ a c,
      ∃ u ∈ unipB E (Fin n), ∃ b ∈ howeSet n ϖ a c, x = u * b ∧ ∀ i j : Fin n, i < j → (b : Matrix (Fin n) (Fin n) E) i j = 0 := by
  intro E _ _ _ _ n ϖ hϖ a c ha x hx
  have hlt : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    exact zpow_lt_one₀ (by rw [← hϖ]; exact (Valuation.pos_iff _).2 ϖ.ne_zero) uniformizer_lt_one (by omega)
  let t : Fin n → Eˣ := fun i => ϖ ^ (c * ((i : ℕ) : ℤ))
  let w : Fin n → Fin n → E := fun i j => ((t i * (t j)⁻¹ : Eˣ) : E)
  have hw0 : ∀ i j, w i j ≠ 0 := fun i j => Units.ne_zero _
  have hwi : ∀ i, w i i = 1 := fun i => by simp [w]
  have hww : ∀ i k j, w i k * w k j = w i j := fun i k j => by
    simp only [w]
    rw [← Units.val_mul]
    congr 1
    group
  have hpow : ∀ i j : Fin n, ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) = ((ϖ ^ a : Eˣ) : E) * w i j := fun i j => by
    simp only [w, t]
    rw [← Units.val_mul, ← zpow_neg, ← zpow_add, ← zpow_add]
    congr 2
    ring
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) E) i j * w i j = (1 : Matrix (Fin n) (Fin n) E) i j := fun i j => by
    by_cases h : i = j
    · subst h; rw [hwi, mul_one]
    · rw [Matrix.one_apply_ne h, zero_mul]
  have key : ∀ (i j : Fin n) (z : E), valuation E (z * w i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤
      valuation E ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) ↔
      valuation E (z - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ valuation E ((ϖ ^ a : Eˣ) : E) := fun i j z => by
    rw [hpow, ← hone i j, ← sub_mul, hone, map_mul, map_mul]
    exact mul_le_mul_iff_left₀ ((Valuation.pos_iff (valuation E)).2 (hw0 i j))
  have hg : ∀ i j, valuation E ((x : Matrix (Fin n) (Fin n) E) i j / w i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤
      valuation E ((ϖ ^ a : Eˣ) : E) := fun i j => (key i j _).1 (by rw [div_mul_cancel₀ _ (hw0 i j)]; exact hx i j)
  have h1 : ∀ i j, valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := fun i j => by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hint : ∀ i j, (x : Matrix (Fin n) (Fin n) E) i j / w i j ∈ 𝒪[E] := fun i j => by
    change valuation E _ ≤ 1
    rw [← sub_add_cancel (_ / w i j) ((1 : Matrix (Fin n) (Fin n) E) i j)]
    exact Valuation.map_add_le _ ((hg i j).trans hlt.le) (h1 i j)
  let I : Ideal 𝒪[E] :=
    { carrier := {z | valuation E (z : E) ≤ valuation E ((ϖ ^ a : Eˣ) : E)}
      add_mem' := fun {y z} h h' => by
        rw [Set.mem_setOf_eq] at h h' ⊢
        rw [Subring.coe_add]
        exact Valuation.map_add_le _ h h'
      zero_mem' := by simp
      smul_mem' := fun r z h => by
        rw [Set.mem_setOf_eq] at h ⊢
        rw [smul_eq_mul, Subring.coe_mul, map_mul]
        simpa using mul_le_mul' (show valuation E (r : E) ≤ 1 from r.2) h }
  have hI : ∀ z : 𝒪[E], z ∈ I ↔ valuation E (z : E) ≤ valuation E ((ϖ ^ a : Eˣ) : E) := fun _ => Iff.rfl
  have hIm : I ≤ IsLocalRing.maximalIdeal 𝒪[E] := IsLocalRing.le_maximalIdeal fun h => by
    have : (1 : 𝒪[E]) ∈ I := h ▸ Submodule.mem_top
    rw [hI] at this
    exact absurd (lt_of_le_of_lt this hlt) (by simp)
  let g : Matrix (Fin n) (Fin n) 𝒪[E] := fun i j => ⟨_, hint i j⟩
  have hgd : ∀ i, g i i - 1 ∈ I := fun i => by
    have := hg i i
    rwa [Matrix.one_apply_eq] at this
  have hgo : ∀ i j, i ≠ j → g i j ∈ I := fun i j h => by
    have := hg i j
    rwa [Matrix.one_apply_ne h, sub_zero] at this
  obtain ⟨X, Y, δ, e, x1, x0, -, -, hδ, y1, y0, yL⟩ := Formalism.IrreducibleCountingLemmas.Z.iwahori_factorization_exists 𝒪[E] I I hIm n g
    (fun i => by
      have := Formalism.IrreducibleCountingLemmas.Z.isUnit_sub_of_mem_maximalIdeal isUnit_one (hIm (I.neg_mem (hgd i)))
      simpa using this)
    (fun i j h => hgo i j h.ne) fun i j h => hgo i j h.ne'
  let U : Matrix (Fin n) (Fin n) E := fun i j => (X i j : E) * w i j
  let B : Matrix (Fin n) (Fin n) E := fun i j => ((δ i * Y i j : 𝒪[E]) : E) * w i j
  have hU0 : ∀ i j, j < i → U i j = 0 := fun i j h => by simp [U, x0 i j h]
  have hU1 : ∀ i, U i i = 1 := fun i => by simp [U, x1, hwi]
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hU0 i j h)]
    simp [hU1]
  let u : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero U hdet
  have hUB : U * B = (x : Matrix (Fin n) (Fin n) E) := by
    ext i j
    have h2 : (x : Matrix (Fin n) (Fin n) E) i j / w i j = ∑ k, (X i k : E) * δ k * Y k j := by
      have := congrArg (fun z : 𝒪[E] => (z : E)) (e i j)
      simpa [g] using this
    rw [← div_mul_cancel₀ ((x : Matrix (Fin n) (Fin n) E) i j) (hw0 i j), h2, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [U, B]
    rw [← hww i k j]
    push_cast
    ring
  have hb : ((u⁻¹ * x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = B := by
    rw [Units.val_mul, ← hUB]
    change (u⁻¹).val * (u.val * B) = B
    rw [← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨u, (mem_unipB E).2 ⟨hU0, hU1⟩, u⁻¹ * x, fun i j => ?_, (mul_inv_cancel_left _ _).symm, fun i j h => ?_⟩
  · rw [hb]
    refine (key i j _).2 ?_
    rcases lt_trichotomy i j with h | h | h
    · rw [y0 i j h, Matrix.one_apply_ne h.ne]
      simp
    · subst h
      rw [y1, mul_one, Matrix.one_apply_eq]
      have : δ i - 1 ∈ I := by
        simpa using I.add_mem (Ideal.mul_le_left (hδ i)) (hgd i)
      exact this
    · rw [Matrix.one_apply_ne h.ne', sub_zero]
      exact (hI _).1 (I.mul_mem_left _ (yL i j h))
  · rw [hb]
    simp [B, y0 i j h]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.IdemOp
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.idemOp :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure →
      ∀ (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ χ : G → ℂ, IsLocallyConstant χ → (∀ x, ‖χ x‖ = 1) →
      (∀ x ∈ J, ∀ y ∈ J, χ (x * y) = χ x * χ y) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π →
        ∃ (B : V →ₗ[ℂ] V) (m : ℂ), m ≠ 0 ∧ IsIntegralOp μ π ((J : Set G).indicator fun x => (χ x)⁻¹) B ∧
          (∀ v, ∀ x ∈ J, π x (B v) = χ x • B v) ∧ ∀ v, (∀ x ∈ J, π x v = χ x • v) → B v = m • v := by
  intro G _ _ _ _ _ _ μ hμ J hJo hJc χ hχ hn hm V _ _ π hπ
  classical
  set f : G → ℂ := (J : Set G).indicator fun x => (χ x)⁻¹ with hfdef
  have hne : ∀ x, χ x ≠ 0 := fun x h => by simpa [h] using hn x
  have hJcl : IsClopen (J : Set G) := ⟨hJc.isClosed, hJo⟩
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h1 := (IsLocallyConstant.iff_eventually_eq χ).1 hχ x
    by_cases hx : x ∈ (J : Set G)
    · filter_upwards [h1, hJo.mem_nhds hx] with y hy hyJ
      simp only [hfdef, Set.indicator_of_mem hx, Set.indicator_of_mem hyJ, hy]
    · filter_upwards [hJcl.isClosed.isOpen_compl.mem_nhds hx] with y hyJ
      simp only [hfdef, Set.indicator_of_notMem hx, Set.indicator_of_notMem hyJ]
  have hc : HasCompactSupport f :=
    HasCompactSupport.intro hJc fun x hx => Set.indicator_of_notMem hx _
  have hB : IsIntegralOp μ π f (GlobalTheory.OpTrace.smoothOp π μ f) := by
    intro v l
    have hi := hπ.smoothOp_integrand hf hc v
    refine ⟨?_, ?_⟩
    · have := GlobalTheory.OpTrace.integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
      simpa only [map_smul, smul_eq_mul] using this
    · rw [hπ.map_smoothOp (μ := μ) hf hc l v]
      simp only [smul_eq_mul]
  generalize GlobalTheory.OpTrace.smoothOp π μ f = B at hB
  refine ⟨B, (μ.real (J : Set G) : ℂ), ?_, hB, ?_, ?_⟩
  · have h0 : μ (J : Set G) ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
    have h1 : μ (J : Set G) ≠ ⊤ := hJc.measure_lt_top.ne
    have : μ.real (J : Set G) ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨h0, h1⟩
    exact_mod_cast this
  · intro v x hx
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    have h1 := (hB v (l ∘ₗ π x)).2
    have h2 := (hB v l).2
    rw [map_sub, map_smul, sub_eq_zero, h2, smul_eq_mul, ← integral_const_mul,
      ← integral_mul_left_eq_self (fun g => χ x * (f g * l (π g v))) x]
    refine h1.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))
    have e : χ x * f (x * g) = f g := by
      by_cases hg : g ∈ J
      · have hxg : x * g ∈ (J : Set G) := J.mul_mem hx hg
        have hg' : g ∈ (J : Set G) := hg
        simp only [hfdef, Set.indicator_of_mem hxg, Set.indicator_of_mem hg', hm x hx g hg]
        have := hne x
        have := hne g
        field_simp
      · have hxg : x * g ∉ (J : Set G) := fun h => hg ((J.mul_mem_cancel_left hx).1 h)
        have hg' : g ∉ (J : Set G) := hg
        simp only [hfdef, Set.indicator_of_notMem hxg, Set.indicator_of_notMem hg', mul_zero]
    simp only [← mul_assoc, e, map_mul, LinearMap.comp_apply, Module.End.mul_apply]
  · intro v hv
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, map_smul, sub_eq_zero, (hB v l).2]
    have e : (fun g => f g * l (π g v)) = (J : Set G).indicator fun _ => l v := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · simp only [hfdef, Set.indicator_of_mem hg, hv g hg, map_smul, smul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (hne g), one_mul]
      · simp only [hfdef, Set.indicator_of_notMem hg, zero_mul]
    rw [e, integral_indicator_const _ hJo.measurableSet]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.LowFix
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

open Topology Filter in
private theorem lowFix_emb (E : Type) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E] (n : ℕ) :
    IsEmbedding (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Matrix (Fin n) (Fin n) E => A⁻¹) ?_ ?_
  · intro A hA
    refine (continuousAt_matrix_inv A ?_).continuousWithinAt
    have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  · intro u
    exact (Matrix.coe_units_inv u).symm

open Topology Filter in
private theorem lowFix_ball (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (γ : ValueGroupWithZero E) (hγ : γ < 1) (W : Set E) (hW : W ∈ nhds (0 : E)) :
    ∃ m : ℕ, ∀ x : E, valuation E x ≤ γ ^ m → x ∈ W := by
  obtain ⟨δ, hδ⟩ := (IsValuativeTopology.mem_nhds_zero_iff W).1 hW
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hγ δ
  exact ⟨m, fun x hx => hδ (lt_of_le_of_lt hx hm)⟩

open Topology Filter in
theorem UpperTheory.V.Z.Tf.L4.lowFix :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (d : ℤ) (U : Set (GL (Fin n) E)), U ∈ nhds (1 : GL (Fin n) E) →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, ∀ b ∈ howeSet n ϖ a (2 * a - d), (∀ i j : Fin n, i < j → (b : Matrix (Fin n) (Fin n) E) i j = 0) → b ∈ U := by
  intro E _ _ _ _ n ϖ hϖ d U hU
  have hlt : valuation E (ϖ : E) < 1 := hϖ ▸ uniformizer_lt_one
  have hpos : 0 < valuation E (ϖ : E) := zero_lt_iff.2 (by simp)
  rw [(lowFix_emb E n).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  have hc : Continuous (fun A : Fin n → Fin n → E => (Matrix.of A + 1 : Matrix (Fin n) (Fin n) E)) :=
    Continuous.add (f := fun A : Fin n → Fin n → E => (Matrix.of A : Matrix (Fin n) (Fin n) E)) continuous_id continuous_const
  have h0 : (fun A : Fin n → Fin n → E => (Matrix.of A + 1 : Matrix (Fin n) (Fin n) E)) ⁻¹' T ∈ nhds (0 : Fin n → Fin n → E) := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hT
  have key : ∃ m : ℕ, ∀ A : Fin n → Fin n → E, (∀ i j, valuation E (A i j) ≤ valuation E (ϖ : E) ^ m) →
      Matrix.of A + 1 ∈ T := by
    rw [nhds_pi, Filter.mem_pi'] at h0
    obtain ⟨I, t, ht, htI⟩ := h0
    have h1 : ∀ i, ∃ s : Fin n → Set E, (∀ j, s j ∈ nhds (0 : E)) ∧ Set.pi Set.univ s ⊆ t i := by
      intro i
      have := ht i
      rw [nhds_pi, Filter.mem_pi'] at this
      obtain ⟨J, s, hs, hsJ⟩ := this
      exact ⟨s, hs, fun x hx => hsJ fun j _ => hx j (Set.mem_univ _)⟩
    choose s hs hst using h1
    have hW : (⋂ i, ⋂ j, s i j) ∈ nhds (0 : E) :=
      Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => hs i j
    obtain ⟨m, hm⟩ := lowFix_ball E _ hlt _ hW
    refine ⟨m, fun A hA => htI fun i _ => hst i fun j _ => ?_⟩
    have := hm _ (hA i j)
    simp only [Set.mem_iInter] at this
    exact this i j
  obtain ⟨m, hm⟩ := key
  refine ⟨max (m : ℤ) |d|, fun a ha b hb hlow => hTU ?_⟩
  have ham : (m : ℤ) ≤ a := le_trans (le_max_left _ _) ha
  have had : |d| ≤ a := le_trans (le_max_right _ _) ha
  have hc0 : 0 ≤ 2 * a - d := by
    have := le_abs_self d
    have := abs_nonneg d
    omega
  have := hm (fun i j => (b : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) (by
    intro i j
    rcases lt_or_ge i j with hij | hij
    · simp [hlow i j hij, Matrix.one_apply_ne hij.ne]
    · refine le_trans (hb i j) ?_
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_natCast]
      refine zpow_le_zpow_right_of_le_one₀ hpos hlt.le ?_
      have hji : ((j : ℕ) : ℤ) ≤ ((i : ℕ) : ℤ) := by exact_mod_cast hij
      have := mul_nonneg hc0 (sub_nonneg.2 hji)
      omega)
  have e : (Matrix.of (fun i j => (b : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) + 1 : Matrix (Fin n) (Fin n) E) = (b : Matrix (Fin n) (Fin n) E) := by
    ext i j
    simp
  rw [e] at this
  exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweConj
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

private noncomputable def dg {E : Type} [Field E] (n : ℕ) (β : Eˣ) : GL (Fin n) E :=
  ⟨Matrix.diagonal fun i => ((β ^ (-((i : ℕ) : ℤ)) : Eˣ) : E), Matrix.diagonal fun i => ((β ^ ((i : ℕ) : ℤ) : Eˣ) : E),
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]⟩

private theorem dg_conj {E : Type} [Field E] {n : ℕ} (β : Eˣ) (x : GL (Fin n) E) (i j : Fin n) :
    ((dg n β * x * (dg n β)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) * (x : Matrix (Fin n) (Fin n) E) i j := by
  change (Matrix.diagonal (fun i : Fin n => ((β ^ (-((i : ℕ) : ℤ)) : Eˣ) : E)) * (x : Matrix (Fin n) (Fin n) E) *
    Matrix.diagonal (fun i : Fin n => ((β ^ ((i : ℕ) : ℤ) : Eˣ) : E))) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, zpow_add, Units.val_mul]
  ring

theorem UpperTheory.V.Z.Tf.L4.howeConj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V) (ϖ β : Eˣ) (a c t : ℤ),
      valuation E (β : E) = valuation E ((ϖ ^ t : Eˣ) : E) → ∀ ψ₀ ψ : AddChar E Circle, (∀ x, ψ x = ψ₀ (β * x)) →
      howeSpace π ψ₀ (howeSet n ϖ a (c - t)) ≠ ⊥ → howeSpace π ψ (howeSet n ϖ a c) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π ϖ β a c t hβ ψ₀ ψ hψ h
  obtain ⟨w, hw, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨π (dg n β)⁻¹ w, fun x hx => ?_, fun e => h0 ?_⟩
  · have hy : dg n β * x * (dg n β)⁻¹ ∈ howeSet n ϖ a (c - t) := fun i j => by
      have e : ((dg n β * x * (dg n β)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
          ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) *
            ((x : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
        rw [dg_conj, mul_sub]
        congr 1
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      have e2 : valuation E ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) =
          valuation E ((ϖ ^ (t * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) : Eˣ) : E) := by
        rw [zpow_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val (ϖ ^ t), map_zpow₀, map_zpow₀, hβ]
      rw [e, map_mul, e2, show a + (c - t) * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) =
        t * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) + (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) by ring, zpow_add, Units.val_mul, map_mul]
      exact mul_le_mul_right (hx i j) _
    have hs : GlobalTheory.Whittaker.superDiag (dg n β * x * (dg n β)⁻¹) = β * GlobalTheory.Whittaker.superDiag x := by
      simp only [GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      rw [dg_conj, (Finset.mem_filter.1 hj).2]
      simp
    have h1 := hw _ hy
    rw [hs, ← hψ] at h1
    rw [← map_smul, ← h1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  · have := congrArg (π (dg n β)) e
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweAvg
open GlobalTheory.PRep MeasureTheory

namespace UpperTheory.ConvolutionTheory.Loc

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

private theorem cont_coeff {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (l : V →ₗ[ℂ] ℂ) (w : V) :
    Continuous fun g : G => l (ρ g w) := by
  have h : IsLocallyConstant fun g : G => ρ g w := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun g => x⁻¹ * g) ⁻¹' {g | ρ g w = w}, (hρ w).preimage (continuous_const.mul continuous_id), by simp, ?_⟩
    intro y hy
    have hy' : ρ (x⁻¹ * y) w = w := hy
    calc ρ y w = ρ x (ρ (x⁻¹ * y) w) := by
          rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
      _ = ρ x w := by rw [hy']
  exact (h.comp l).continuous

open Classical in
private theorem avg {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (C : Subgroup G) (hC : IsCompact (C : Set G))
    (θ : G → ℂ) (hθ : Continuous θ) (hmul : ∀ a ∈ C, ∀ b ∈ C, θ (a * b) = θ a * θ b) (l : V →ₗ[ℂ] ℂ) (v : V)
    (S : Set G) (hS : IsOpen S) (h1 : 1 ∈ S) (hv : ∀ c ∈ C, θ c * l (ρ c⁻¹ v) = if c ∈ S then 1 else 0) :
    ∃ l' : V →ₗ[ℂ] ℂ, (∀ c ∈ C, ∀ w, l' (ρ c w) = θ c * l' w) ∧ l' v = 1 := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
  letI : MeasurableSpace C := borel C
  haveI : BorelSpace C := ⟨rfl⟩
  let μ : Measure C := Measure.haar
  have hc : ∀ w, Continuous fun c : C => θ c * l (ρ (c : G)⁻¹ w) := fun w =>
    (hθ.comp continuous_subtype_val).mul ((cont_coeff hρ l w).comp continuous_subtype_val.inv)
  have hi : ∀ w, Integrable (fun c : C => θ c * l (ρ (c : G)⁻¹ w)) μ := fun w =>
    (hc w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L : V →ₗ[ℂ] ℂ :=
    { toFun := fun w => ∫ c : C, θ c * l (ρ (c : G)⁻¹ w) ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hi a) (hi b)]
        simp only [map_add (f := _), mul_add]
      map_smul' := fun t a => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext c
        ring }
  have hL : ∀ c ∈ C, ∀ w, L (ρ c w) = θ c * L w := by
    intro c hc w
    change ∫ x : C, θ x * l (ρ (x : G)⁻¹ (ρ c w)) ∂μ = θ c * ∫ x : C, θ x * l (ρ (x : G)⁻¹ w) ∂μ
    rw [← integral_const_mul, ← integral_mul_left_eq_self _ (⟨c, hc⟩ : C)]
    congr 1
    funext x
    simp only [Subgroup.coe_mul, Subtype.coe_mk]
    rw [hmul c hc x x.2, ← mul_apply_eq_comp, ← map_mul, mul_inv_rev, inv_mul_cancel_right, mul_assoc]
  have hT : IsOpen ((Subtype.val : C → G) ⁻¹' S) := hS.preimage continuous_subtype_val
  have hLv : L v = (μ.real ((Subtype.val : C → G) ⁻¹' S) : ℂ) := by
    change ∫ x : C, θ x * l (ρ (x : G)⁻¹ v) ∂μ = _
    have : (fun x : C => θ x * l (ρ (x : G)⁻¹ v)) = ((Subtype.val : C → G) ⁻¹' S).indicator fun _ => (1 : ℂ) := by
      funext x
      rw [hv x x.2, Set.indicator_apply]
      rfl
    rw [this, integral_indicator_const _ hT.measurableSet]
    simp
  have hne : L v ≠ 0 := by
    rw [hLv, Complex.ofReal_ne_zero, measureReal_ne_zero_iff (measure_ne_top _ _)]
    exact hT.measure_ne_zero μ ⟨1, h1⟩
  refine ⟨(L v)⁻¹ • L, fun c hc w => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, hL c hc, smul_eq_mul]
    ring
  · simp [hne]

theorem eq_zero_of_no_intertwining {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (K N : Subgroup G)
    (hK : IsCompact (K : Set G)) (hK' : IsOpen (K : Set G))
    (hN : ∀ F : Finset G, (∀ u ∈ F, u ∈ N) → ∃ C : Subgroup G, IsCompact (C : Set G) ∧ C ≤ N ∧ ∀ u ∈ F, u ∈ C)
    (χ : G → ℂ) (hχ : Continuous χ) (hmul : ∀ a ∈ N, ∀ b ∈ N, χ (a * b) = χ a * χ b)
    (hint : ∀ u ∈ N, u ∉ K → ∃ k ∈ K, u * k * u⁻¹ ∈ K ∧ χ (u * k * u⁻¹) ≠ χ k)
    (v : V) (hv : ∀ k ∈ K, ρ k v = χ k • v)
    (hker : v ∈ Submodule.span ℂ {w | ∃ u ∈ N, ∃ x, w = ρ u x - χ u • x}) : v = 0 := by
  classical
  by_contra h0
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  have hK1 : ∀ k ∈ K, χ k = l₀ (ρ k v) := fun k hk => by rw [hv k hk, map_smul, hl₀, smul_eq_mul, mul_one]
  have hKmul : ∀ a ∈ K, ∀ b ∈ K, χ (a * b) = χ a * χ b := fun a ha b hb => by
    rw [hK1 _ (K.mul_mem ha hb), map_mul, mul_apply_eq_comp, hv b hb, map_smul, map_smul, ← hK1 a ha, smul_eq_mul,
      mul_comm]
  have hinv : ∀ a ∈ K, χ a * χ a⁻¹ = 1 := fun a ha => by
    rw [← hKmul a ha _ (K.inv_mem ha), mul_inv_cancel, hK1 1 K.one_mem, map_one, one_apply_eq_self, hl₀]
  obtain ⟨l₁, hl₁, hl₁v⟩ := avg hρ K hK χ hχ hKmul l₀ v Set.univ isOpen_univ trivial (fun c hc => by
    rw [← hK1 _ (K.inv_mem hc), hinv c hc]; simp)
  have hF : ∃ F : Finset G, (∀ u ∈ F, u ∈ N) ∧
      ∀ l' : V →ₗ[ℂ] ℂ, (∀ c ∈ F, ∀ w, l' (ρ c w) = χ c * l' w) → l' v = 0 := by
    clear hl₁v hv hK1 hl₀ h0
    induction hker using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨u, hu, x, rfl⟩ := hw
      exact ⟨{u}, by simpa using hu, fun l' h => by simp [h u (by simp)]⟩
    | zero => exact ⟨∅, by simp, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨F, hF, h⟩ := ha
      obtain ⟨F', hF', h'⟩ := hb
      refine ⟨F ∪ F', fun u hu => (Finset.mem_union.1 hu).elim (hF u) (hF' u), fun l' hl => ?_⟩
      rw [map_add (f := _), h l' fun c hc => hl c (Finset.mem_union_left _ hc), h' l' fun c hc => hl c (Finset.mem_union_right _ hc),
        add_zero]
    | smul t a _ ha =>
      obtain ⟨F, hF, h⟩ := ha
      exact ⟨F, hF, fun l' hl => by rw [map_smul, h l' hl, smul_zero]⟩
  obtain ⟨F, hFN, hF⟩ := hF
  obtain ⟨C, hC, hCN, hFC⟩ := hN F hFN
  obtain ⟨l₂, hl₂, hl₂v⟩ := avg hρ C hC χ hχ (fun a ha b hb => hmul a (hCN ha) b (hCN hb)) l₁ v K hK' K.one_mem
    (fun c hc => by
      by_cases hcK : c ∈ K
      · rw [ite_eq_left (by exact hcK), hv _ (K.inv_mem hcK), map_smul, hl₁v, smul_eq_mul, mul_one, hinv c hcK]
      · rw [ite_eq_right (by exact hcK)]
        obtain ⟨k, hk, hk', hne⟩ := hint c⁻¹ (N.inv_mem (hCN hc)) (fun h => hcK (by simpa using K.inv_mem h))
        have h1 := hl₁ _ hk' (ρ c⁻¹ v)
        rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel_right, map_mul, mul_apply_eq_comp, hv k hk, map_smul,
          map_smul, smul_eq_mul] at h1
        rw [(mul_eq_mul_right_iff.1 h1).resolve_left hne.symm, mul_zero])
  exact one_ne_zero (hl₂v.symm.trans (hF l₂ fun c hc => hl₂ c (hFC c hc)))

end UpperTheory.ConvolutionTheory.Loc
end

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc UpperTheory.V.Z.Tf.L4

theorem UpperTheory.V.Z.Tf.L4.howeEx0 :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π →
      ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ (ψ : AddChar E Circle) (d : ℤ), HasConductor ψ (ϖ ^ d) → GlobalTheory.LocGL.IsGenericFor ψ π →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, howeSpace π ψ (howeSet n ϖ a (2 * a - d)) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ ψ d hψ hg
  obtain ⟨l, v, hlv, hl⟩ : ∃ (l : Module.Dual ℂ V) (v : V), l v ≠ 0 ∧
      ∀ u ∈ unipB E (Fin n), ∀ x, l (π u x) = (ψ (GlobalTheory.Whittaker.superDiag u) : ℂ) * l x := by
    have : Nontrivial (TwJacquet π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n)) := hg
    obtain ⟨w, hw⟩ := exists_ne (0 : TwJacquet π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n))
    obtain ⟨l₀, h₀⟩ := Module.Projective.exists_dual_ne_zero ℂ hw
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨l₀ ∘ₗ Submodule.mkQ _, v, h₀, fun u hu x => ?_⟩
    have h1 : π u x - (GlobalTheory.LocGL.whitChar ψ n ⟨u, hu⟩ : ℂ) • x ∈ twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n) :=
      Submodule.subset_span ⟨⟨u, hu⟩, x, rfl⟩
    have h2 : (GlobalTheory.LocGL.whitChar ψ n ⟨u, hu⟩ : ℂ) = (ψ (GlobalTheory.Whittaker.superDiag u) : ℂ) := by
      have : (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) = GlobalTheory.Whittaker.superDiag u := by
        rw [GlobalTheory.Whittaker.superDiag, Finset.sum_filter, Fintype.sum_prod_type]
        simp only [Finset.sum_filter]
      rw [← this]
      rfl
    have h3 := (Submodule.Quotient.eq _).2 h1
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [h3, h2, Submodule.Quotient.mk_smul, map_smul, smul_eq_mul]
  obtain ⟨a₀, h₀⟩ := UpperTheory.V.Z.Tf.L4.lowFix E n ϖ hϖ d {g | π g v = v} ((hs v).mem_nhds (by simp))
  refine ⟨max 1 a₀, fun a ha => ?_⟩
  have ha1 : 1 ≤ a := le_trans (le_max_left _ _) ha
  have hψ' : HasConductor ψ (ϖ ^ (2 * a - (2 * a - d))) := by rwa [sub_sub_cancel]
  obtain ⟨J, hJ, ho, hk⟩ := UpperTheory.V.Z.Tf.L4.howeGroup E n ϖ hϖ a (2 * a - d) ha1
  obtain ⟨hlc, hmul⟩ := UpperTheory.V.Z.Tf.L4.howeChar E n ϖ hϖ a (2 * a - d) ha1 ψ hψ'
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a (2 * a - d) := fun x => by rw [← hJ]; rfl
  have : LocallyCompactSpace (GL (Fin n) E) := hk.locallyCompactSpace_of_mem_nhds_of_group (ho.mem_nhds J.one_mem)
  borelize (GL (Fin n) E)
  let μ : Measure (GL (Fin n) E) := Measure.haar
  obtain ⟨B, m, -, hB, hB1, -⟩ := UpperTheory.V.Z.Tf.L4.idemOp (GL (Fin n) E) μ inferInstance J ho hk _ hlc (fun x => Circle.norm_coe _)
    (fun x hx y hy => by rw [hmul x ((hmem x).1 hx) y ((hmem y).1 hy), Circle.coe_mul]) V π hs
  refine (Submodule.ne_bot_iff _).2 ⟨B v, fun x hx => hB1 v x ((hmem x).2 hx), fun h => ?_⟩
  have h1 := (hB v l).2
  have e : (fun g => (J : Set (GL (Fin n) E)).indicator (fun x => ((ψ (GlobalTheory.Whittaker.superDiag x) : ℂ))⁻¹) g * l (π g v)) =
      (J : Set (GL (Fin n) E)).indicator fun _ => l v := by
    funext g
    by_cases hgJ : g ∈ (J : Set (GL (Fin n) E))
    · rw [Set.indicator_of_mem hgJ, Set.indicator_of_mem hgJ]
      obtain ⟨u, hu, b, hb, hub, hlow⟩ := UpperTheory.V.Z.Tf.L4.ulFact E n ϖ hϖ a (2 * a - d) ha1 g ((hmem g).1 hgJ)
      have hbv : π b v = v := h₀ a (le_trans (le_max_right _ _) ha) b hb hlow
      have huJ : u ∈ J := by
        have : u = g * b⁻¹ := by rw [hub, mul_inv_cancel_right]
        rw [this]
        exact J.mul_mem hgJ (J.inv_mem ((hmem b).2 hb))
      have hsd : GlobalTheory.Whittaker.superDiag b = 0 :=
        Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => hlow i j (by
          have := (Finset.mem_filter.1 hj).2
          rw [Fin.lt_def]
          omega)
      rw [hub, hmul u ((hmem u).1 huJ) b hb, hsd, AddChar.map_zero_eq_one, mul_one, map_mul, mul_apply_eq_comp, hbv,
        hl u hu, ← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
    · rw [Set.indicator_of_notMem hgJ, Set.indicator_of_notMem hgJ, zero_mul]
  rw [e, h, map_zero, integral_indicator_const _ ho.measurableSet] at h1
  rcases smul_eq_zero.1 h1.symm with h2 | h2
  · exact ((ENNReal.toReal_pos (ho.measure_ne_zero μ ⟨1, J.one_mem⟩) hk.measure_lt_top.ne).ne') h2
  · exact hlv h2

theorem UpperTheory.ConvolutionTheory.Loc.howeEx :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → GlobalTheory.LocGL.IsGeneric π → ∀ c : ℤ, ∃ a₀ : ℤ, ∀ a ≥ a₀,
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → howeSpace π ψ (howeSet n ϖ a c) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ ⟨ψ₀, h1, h2, h3⟩ c
  obtain ⟨d, hd⟩ := UpperTheory.V.Z.Tf.L4.condEx E ϖ hϖ ψ₀ h1 h2
  obtain ⟨a₀, h⟩ := UpperTheory.V.Z.Tf.L4.howeEx0 E n V π hs ϖ hϖ ψ₀ d hd h3
  refine ⟨a₀, fun a ha ψ hψ => ?_⟩
  obtain ⟨β, hβ, e⟩ := UpperTheory.V.Z.Tf.L4.charDual E ϖ hϖ ψ₀ ψ d _ hd hψ
  refine UpperTheory.V.Z.Tf.L4.howeConj E n V π ϖ β a c _ hβ ψ₀ ψ e ?_
  rw [show c - (d - (2 * a - c)) = 2 * a - d by ring]
  exact h a ha

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem conj_sub (ϖ : Eˣ) (c : ℤ) (g : GL (Fin n) E) (i j : Fin n) :
    ((diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹ : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
      ((ϖ ^ (c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) * ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
  rw [DiscreteGroups.sglob.DzType.diag_conj_apply, mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, ← mul_sub, mul_sub ((ϖ ^ _ : Eˣ) : E)]
  congr 1
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

private theorem conj_mem (ϖ : Eˣ) (a c : ℤ) (g : GL (Fin n) E) :
    diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹ ∈ howeSet n ϖ a c ↔
      Bd (valuation E ((ϖ ^ a : Eˣ) : E)) ((g : Matrix (Fin n) (Fin n) E) - 1) := by
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [conj_sub, add_comm a, _root_.zpow_add, Units.val_mul, map_mul, map_mul, Matrix.sub_apply]
  exact mul_le_mul_iff_right₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))

private theorem conj_sd (ϖ : Eˣ) (c : ℤ) (g : GL (Fin n) E) :
    GlobalTheory.Whittaker.superDiag (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) * g * (diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))))⁻¹) =
      ((ϖ ^ (-c) : Eˣ) : E) * GlobalTheory.Whittaker.superDiag g := by
  simp only [GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have h := (Finset.mem_filter.1 hj).2
  rw [DiscreteGroups.sglob.DzType.diag_conj_apply, mul_right_comm, ← Units.val_mul, ← _root_.zpow_sub, h]
  congr 3
  push_cast
  ring

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem whit_eq (ψ : AddChar E Circle) (u : unipB E (Fin n)) :
    ((GlobalTheory.LocGL.whitChar ψ n u : ℂˣ) : ℂ) = (ψ (GlobalTheory.Whittaker.superDiag (u : GL (Fin n) E)) : ℂ) := by
  change ((ψ _ : Circle) : ℂ) = _
  congr 2
  simp only [GlobalTheory.Whittaker.superDiag, Finset.sum_filter]
  exact Fintype.sum_prod_type _

end

theorem UpperTheory.ConvolutionTheory.Loc.howeInj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a →
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → ∀ v ∈ howeSpace π ψ (howeSet n ϖ a c),
        v ∈ twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n) → v = 0 := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ a c ha ψ hψ v hv hk
  obtain ⟨J, hJ, ho, hc⟩ := howeGroup E n ϖ hϖ a c ha
  have hmem : ∀ x, x ∈ J ↔ x ∈ howeSet n ϖ a c := fun x => by rw [← hJ]; rfl
  refine eq_zero_of_no_intertwining hs J (unipB E (Fin n)) hc ho DiscreteGroups.sglob.DzType.exists_compact_unip
    (fun x => (ψ (GlobalTheory.Whittaker.superDiag x) : ℂ)) (howeChar E n ϖ hϖ a c ha ψ hψ).1.continuous (fun x hx y hy => ?_)
    (fun u hu hn => ?_) v (fun k h => hv k ((hmem k).1 h)) (Submodule.span_mono ?_ hk)
  · have := congrArg Units.val (map_mul (GlobalTheory.LocGL.whitChar ψ n) ⟨x, hx⟩ ⟨y, hy⟩)
    rwa [Units.val_mul, whit_eq, whit_eq, whit_eq] at this
  · obtain ⟨d, hd⟩ : ∃ d, d = diagT E (Fin n) (fun i => ϖ ^ (c * (i : ℕ))) := ⟨_, rfl⟩
    have hu' : d⁻¹ * u * d ∈ unipB E (Fin n) := by
      have e : diagT E (Fin n) (fun i => (ϖ ^ (c * (i : ℕ)))⁻¹) = d⁻¹ := by rw [hd, ← map_inv]; rfl
      have := DiscreteGroups.sglob.DzType.diag_conj_mem_unipB (fun i => (ϖ ^ (c * (i : ℕ)))⁻¹) hu
      rwa [e, inv_inv] at this
    have hp : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
      exact zpow_lt_one₀ (zero_lt_iff.2 uniformizer_ne_zero) uniformizer_lt_one (by omega)
    obtain ⟨k, h1, h2, h3⟩ := not_intertwine (ϖ ^ a) hp (ψ.mulShift ((ϖ ^ (-c) : Eˣ) : E)) (fun x hx => by
      have h0 : 0 < valuation E ((ϖ ^ (-c) : Eˣ) : E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))
      have h4 : ¬ valuation E (((ϖ ^ (-c) : Eˣ) : E) * x) ≤ valuation E ((ϖ ^ (2 * a - c) : Eˣ) : E) := by
        rw [show 2 * a - c = -c + (a + a) by ring, _root_.zpow_add, _root_.zpow_add, Units.val_mul, Units.val_mul, map_mul, map_mul _ ((ϖ ^ (-c) : Eˣ) : E),
          mul_le_mul_iff_right₀ h0]
        exact not_le.2 hx
      rw [← hψ] at h4
      push Not at h4
      obtain ⟨y, h5, h6⟩ := h4
      refine ⟨((ϖ ^ (-c) : Eˣ) : E)⁻¹ * y, ?_, by rwa [AddChar.mulShift_apply, mul_inv_cancel_left₀ (Units.ne_zero _)]⟩
      rwa [map_mul, map_inv₀, inv_mul_le_iff₀ h0, ← map_mul]) (d⁻¹ * u * d) hu' fun h => hn (by
        have := (conj_mem ϖ a c _).2 h
        rw [← hd, show d * (d⁻¹ * u * d) * d⁻¹ = u by group] at this
        exact (hmem u).2 this)
    have e : u * (d * k * d⁻¹) * u⁻¹ = d * (d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹) * d⁻¹ := by group
    refine ⟨d * k * d⁻¹, (hmem _).2 (hd ▸ (conj_mem ϖ a c k).2 h1), ?_, fun h => h3 (Circle.ext ?_)⟩
    · rw [e]
      generalize d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹ = z at h2
      exact (hmem _).2 (hd ▸ (conj_mem ϖ a c z).2 h2)
    · rw [e] at h
      generalize d⁻¹ * u * d * k * (d⁻¹ * u * d)⁻¹ = z at h
      simp only [hd, conj_sd] at h
      exact h
  · rintro w ⟨u, x, rfl⟩
    exact ⟨u, u.2, x, by rw [whit_eq]⟩

theorem UpperTheory.ConvolutionTheory.Loc.howeLine :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → π.IsIrreducible → GlobalTheory.LocGL.IsGeneric π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → ∀ c : ℤ, ∃ a₀ : ℤ, ∀ a ≥ a₀,
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → Module.finrank ℂ (howeSpace π ψ (howeSet n ϖ a c)) = 1 := by
  intro E _ _ _ _ n V _ _ π hs hi hg ϖ hϖ c
  obtain ⟨a₀, h⟩ := howeEx E n V π hs ϖ hϖ hg c
  refine ⟨max 1 a₀, fun a ha ψ hψ => ?_⟩
  have h1 := PositivityTheory.rg.gu.whit.whitLeOne E n ψ V π hs hi hψ.continuous hψ.ne_one
  let f := (twKer π (unipB E (Fin n)) (GlobalTheory.LocGL.whitChar ψ n)).mkQ ∘ₗ (howeSpace π ψ (howeSet n ϖ a c)).subtype
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).2 fun v hv =>
    Subtype.ext (howeInj E n V π hs ϖ hϖ a c (le_trans (le_max_left _ _) ha) ψ hψ v.1 v.2 ((Submodule.Quotient.mk_eq_zero _).1 hv))
  have h2 : Module.rank ℂ (howeSpace π ψ (howeSet n ϖ a c)) ≤ 1 := (LinearMap.rank_le_of_injective f hf).trans h1
  have h3 := Submodule.nontrivial_iff_ne_bot.2 (h a (le_trans (le_max_right _ _) ha) ψ hψ)
  exact Module.finrank_eq_of_rank_eq (le_antisymm (by simpa using h2) (by simpa using Cardinal.one_le_iff_pos.2 rank_pos))
