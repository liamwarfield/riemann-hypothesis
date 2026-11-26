module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAtZeroReindexEqTaylorCoefficient
section -- merged from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.WordDerivativeBlocks
open scoped BigOperators

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials

variable {ι : Type} {dim : ι → ℕ} {n : ℕ}

section Operator

variable {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def wordDeriv (dir : Λ → W) (l : List Λ) (F : W → ℂ) (p : W) : ℂ :=
  iteratedFDeriv ℂ l.length F p fun j => dir (l.get j)

def applyAt (dir : Λ → W) (P : MvPolynomial Λ ℂ) (F : W → ℂ) (p : W) : ℂ :=
  ∑ μ ∈ P.support, P.coeff μ * wordDeriv dir (Finsupp.toMultiset μ).toList F p

theorem iteratedFDeriv_directions_comp_perm_of_analyticAt (dir : Λ → W) {F : W → ℂ} {p : W} (hF : AnalyticAt ℂ F p)
    {k : ℕ} (u v : Fin k → Λ) (σ : Equiv.Perm (Fin k)) (h : u = v ∘ σ) :
    iteratedFDeriv ℂ k F p (fun j => dir (u j)) = iteratedFDeriv ℂ k F p (fun j => dir (v j)) := by
  subst h
  exact (hF.contDiffAt (n := ⊤)).iteratedFDeriv_comp_perm (fun j => dir (v j)) σ

theorem wordDeriv_perm (dir : Λ → W) {F : W → ℂ} {p : W} (hF : AnalyticAt ℂ F p)
    {l l' : List Λ} (h : l.Perm l') : wordDeriv dir l F p = wordDeriv dir l' F p := by
  have key : ∀ {l l' : List Λ}, l.Perm l' →
      ∃ e : Fin l.length ≃ Fin l'.length, ∀ j, l.get j = l'.get (e j) := by
    intro l l' h
    induction h with
    | nil => exact ⟨Equiv.refl _, fun _ => rfl⟩
    | cons x _ ih =>
      obtain ⟨e, he⟩ := ih
      refine ⟨(finSuccEquiv _).trans ((Equiv.optionCongr e).trans (finSuccEquiv _).symm), ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simpa using he j
    | swap x y l =>
      refine ⟨Equiv.swap (0 : Fin (l.length + 2)) 1, ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
      · simp
      · simp
      · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
        simp
    | trans _ _ ih₁ ih₂ =>
      obtain ⟨e₁, h₁⟩ := ih₁
      obtain ⟨e₂, h₂⟩ := ih₂
      exact ⟨e₁.trans e₂, fun j => by rw [h₁, h₂]; rfl⟩
  obtain ⟨e, he⟩ := key h
  have hl := h.length_eq
  unfold wordDeriv
  have gen : ∀ (a b : ℕ) (_ : a = b) (u : Fin a → Λ) (v : Fin b → Λ) (e : Fin a ≃ Fin b),
      (∀ j, u j = v (e j)) → iteratedFDeriv ℂ a F p (fun j => dir (u j)) =
        iteratedFDeriv ℂ b F p (fun j => dir (v j)) := by
    intro a b hab u v e he
    subst hab
    exact iteratedFDeriv_directions_comp_perm_of_analyticAt dir hF u v e (funext he)
  exact gen _ _ hl _ _ e he

end Operator

section Columns

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Columns

def gDim (f r : ℕ) : ℕ := f * r

def bigR (rd : ℝ) : ℝ := rd ^ 7

def dStar (f m : ℕ) : ℕ := 2 * f * m

def omStar (f : ℕ) (rd : ℝ) : ℝ := 2 * (f : ℝ) ^ ((3 : ℝ) / 2) * rd

def thSq (f : ℕ) (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := f * R₀ ^ 2 * bigR rd ^ 3 / q

def bZero (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := q / (R₀ ^ 2 * bigR rd ^ 4)

def tZero (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := q * bZero rd q R₀

def mOne (f m : ℕ) (rd : ℝ) : ℝ := 90 * (m : ℝ) ^ 2 * (dStar f m : ℝ) ^ 2 * rd

structure Params {ι : Type} (dim : ι → ℕ) (f r : ℕ) (rd : ℝ) (D n : ℕ) where
  q : ℕ
  R₀ : ℝ
  m : ℕ
  one_le_m : 1 ≤ m
  min_dim_le : ∃ s, dim s ≤ m
  m_pow_le : m ^ 4 ≤ f
  f_sq_le : (f : ℝ) ^ 2 ≤ rd
  sixteen_le : 16 ≤ rd
  two_le_fr : 2 ≤ f * r
  three_le_q : 3 ≤ q
  one_le_D : 1 ≤ D
  one_le_n : 1 ≤ n
  R₀_pos : 0 < R₀
  R₀_sq : max (270 : ℝ) (90 * ((gDim f r : ℝ) + D)) ≤ R₀ ^ 2
  threshold_lt : (dStar f m : ℝ) ^ 2 * omStar f rd * thSq f rd q R₀ < 1
  one_le_bZero : 1 ≤ bZero rd q R₀
  mOne_le : mOne f m rd ≤ (q : ℝ) / 2
  D_le_q : D ≤ q
  tZero_ge_log : 4 * (D : ℝ) * (7 + Real.log ((q : ℝ) * D)) + (dStar f m : ℝ) + 1 ≤ tZero rd q R₀
  tZero_ge_rank : (gDim f r : ℝ) * Real.log 2 + 2 * (dStar f m : ℝ) + 3 +
    ((D : ℝ) + 1) * ((r : ℝ) * Real.log r + 3 * r + 3) ≤ tZero rd q R₀

namespace Params

variable {f r : ℕ} {rd : ℝ} {D : ℕ} (P : Params dim f r rd D n)

end Params

end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAtZeroReindexEqTaylorCoefficient
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.DerivReindex

open GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials

theorem wordDeriv_eq {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (dir : Λ → W) (l : List Λ)
    (F : W → ℂ) (p : W) {n : ℕ} (h : l.length = n) :
    iteratedFDeriv ℂ n F p (fun i => dir (l.get ⟨i, by rw [h]; exact i.2⟩)) = wordDeriv dir l F p := by
  subst h; rfl

theorem wordDeriv_comp {Λ Λ' W W' : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup W'] [NormedSpace ℂ W'] (dir : Λ → W) (dir' : Λ' → W') (g : Λ → Λ')
    (T : W →L[ℂ] W') (hT : ∀ x, T (dir x) = dir' (g x)) (l : List Λ) (F : W' → ℂ)
    (hF : ContDiff ℂ l.length F) :
    wordDeriv dir l (F ∘ T) 0 = wordDeriv dir' (l.map g) F 0 := by
  rw [← wordDeriv_eq dir' (l.map g) F 0 (n := l.length) (by simp), wordDeriv,
    T.iteratedFDeriv_comp_right hF 0 le_rfl, map_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  simp [hT]

theorem derivAt0_reindex : ∀ (D : D7) (ι : Type) [Fintype ι] (e : ι ≃ D.what₂.Tau) (a b : ℕ) (F : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ F → ∀ m : DVar ι a b →₀ ℕ, derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D F (Finsupp.equivMapDomain (e.prodCongr (Equiv.refl (Fin b × Fin a))) m) := by
  intro D ι _ e a b F hF m
  have han : AnalyticOnNhd ℂ F Set.univ := GlobalTheory.SCV.analyticOnNhd_of_differentiable hF _
  set g := e.prodCongr (Equiv.refl (Fin b × Fin a)) with hg
  let T : VCx ι a b →L[ℂ] TaylorLogMetric.VC D a b :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (e.symm τ)
  have hT : ∀ x, T (coordX x) = TaylorLogMetric.coordV D (g x) := by
    intro x
    funext τ i j
    change coordX x (e.symm τ) i j = _
    unfold coordX TaylorLogMetric.coordV
    exact @if_congr _ _ _ (_) (_) _ _ _ _ (and_congr_left' e.symm_apply_eq) rfl rfl
  have hne : (m.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h1 : derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m
      = wordDeriv coordX m.toMultiset.toList (F ∘ T) 0 :=
    wordDeriv_eq coordX m.toMultiset.toList (F ∘ T) 0 (Multiset.length_toList _)
  have h2 : TaylorLogMetric.taylor D F (Finsupp.equivMapDomain g m)
      = wordDeriv (TaylorLogMetric.coordV D) (Finsupp.equivMapDomain g m).toMultiset.toList F 0 /
        (m.prod fun _ n => (n.factorial : ℂ)) := by
    rw [TaylorLogMetric.taylor, Finsupp.prod_equivMapDomain]
    congr 1
    exact wordDeriv_eq _ _ F 0 (Multiset.length_toList _)
  rw [h1, h2, mul_div_cancel₀ _ hne, wordDeriv_comp coordX (TaylorLogMetric.coordV D) g T hT _ F han.contDiff]
  refine wordDeriv_perm _ (han 0 trivial) ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_map, Finsupp.equivMapDomain_eq_mapDomain]

end GlobalTheory.DerivReindex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAtZeroReindexEqTaylorCoefficientStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivAtZero_reindex_eq_taylor_coefficient : ∀ (D : D7) (ι : Type) [Fintype ι] (e : ι ≃ D.what₂.Tau) (a b : ℕ) (F : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ F → ∀ m : DVar ι a b →₀ ℕ, derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D F (Finsupp.equivMapDomain (e.prodCongr (Equiv.refl (Fin b × Fin a))) m) := by
  first | exact @GlobalTheory.DerivReindex.derivAt0_reindex | exact GlobalTheory.DerivReindex.derivAt0_reindex | (intros; apply GlobalTheory.DerivReindex.derivAt0_reindex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanDetSetIffAdelicLatticeValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanDetSetIffAdelicLatticeValuation
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors

namespace GlobalTheory.AdelicDetSpan

variable {E : Type} [Field E] [NumberField E]

noncomputable def comp (P : HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* P.adicCompletion E where
  toFun x := x P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (P.adicCompletion E) a) = P.valuation E a :=
  P.valuedAdicCompletion_eq_valuation' a

theorem comp_alg (P : HeightOneSpectrum (𝓞 E)) (a : E) :
    comp P (algebraMap E (FiniteAdeleRing (𝓞 E) E) a) = algebraMap E (P.adicCompletion E) a := rfl

theorem val_det_le_one {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  let N : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨M i j, h i j⟩
  have e : M = v.integer.subtype.mapMatrix N := rfl
  rw [e, ← RingHom.map_det]
  exact N.det.2

theorem exists_clear (Q : HeightOneSpectrum (𝓞 E)) (y : FiniteAdeleRing (𝓞 E) E)
    (hy : Valued.v (comp Q y) ≤ 1) :
    ∃ b : 𝓞 E, b ∉ Q.asIdeal ∧ ∀ P : HeightOneSpectrum (𝓞 E),
      P.valuation E (b : E) * Valued.v (comp P y) ≤ 1 := by
  classical
  have hloc : ∀ P : HeightOneSpectrum (𝓞 E), ∃ c : 𝓞 E, c ∉ Q.asIdeal ∧
      P.valuation E (c : E) * Valued.v (comp P y) ≤ 1 := by
    intro P
    by_cases h1 : Valued.v (comp P y) ≤ 1
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top, by simpa using h1⟩
    have hPQ : P ≠ Q := by rintro rfl; exact h1 hy
    have hnle : ¬ P.asIdeal ≤ Q.asIdeal := fun hle =>
      hPQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle))
    obtain ⟨a, haP, haQ⟩ := Set.not_subset.1 hnle
    have hlt : P.valuation E (a : E) < 1 := (P.valuation_lt_one_iff_mem (K := E) a).2 haP
    have h0 : Valued.v (comp P y) ≠ 0 := by
      intro h; rw [h] at h1; exact h1 zero_le_one
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hlt (Units.mk0 _ h0)⁻¹
    refine ⟨a ^ m, fun h => haQ (Q.isPrime.mem_of_pow_mem m h), ?_⟩
    have : ((a ^ m : 𝓞 E) : E) = (a : E) ^ m := by simp
    rw [this, map_pow]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0] at hm
    calc _ ≤ (Valued.v (comp P y))⁻¹ * Valued.v (comp P y) := mul_le_mul' hm.le le_rfl
      _ = 1 := inv_mul_cancel₀ h0
  choose c hcQ hc using hloc
  have hfin : {P : HeightOneSpectrum (𝓞 E) | ¬ Valued.v (comp P y) ≤ 1}.Finite :=
    Filter.eventually_cofinite.1 y.2
  have hle : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E), P.valuation E (a : E) ≤ 1 :=
    fun P a => P.valuation_le_one (K := E) a
  refine ⟨∏ P ∈ hfin.toFinset, c P, ?_, fun P => ?_⟩
  · rw [Q.isPrime.prod_mem_iff]
    rintro ⟨P, -, h⟩
    exact hcQ P h
  · by_cases h1 : Valued.v (comp P y) ≤ 1
    · exact mul_le_one' (hle _ _) h1
    · have hm : P ∈ hfin.toFinset := by simpa using h1
      rw [← Finset.prod_erase_mul _ _ hm]
      have : (((∏ x ∈ hfin.toFinset.erase P, c x) * c P : 𝓞 E) : E) =
        ((∏ x ∈ hfin.toFinset.erase P, c x : 𝓞 E) : E) * (c P : E) := by push_cast; rfl
      rw [this, map_mul, mul_assoc]
      exact mul_le_one' (hle _ _) (hc P)

theorem exists_approx_matrix (Q : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (g h : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) (hg : h * g = 1) :
    ∃ X : Matrix (Fin n) (Fin n) E,
      (∀ i j, Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X) i j) ≤ 1) ∧
      Valued.v (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X).det = 1 := by
  have hd : DenseRange (Pi.map fun _ : Fin n => Pi.map fun _ : Fin n =>
      (algebraMap E (Q.adicCompletion E) : E → _)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ =>
      HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) (K := E) Q
  have hc : Continuous fun X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) => h * X :=
    continuous_const.matrix_mul continuous_id
  have hb : IsOpen {z : Q.adicCompletion E | Valued.v z < 1} := by
    have h := Valued.isOpen_ball (Q.adicCompletion E) 1
    convert h using 2 with z
    simp [Valuation.restrict_lt_iff_lt_embedding]
  have hU : IsOpen {X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) |
      (∀ i j, Valued.v ((h * X - 1) i j) < 1) ∧ Valued.v ((h * X).det - 1) < 1} := by
    change IsOpen ({X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) |
      ∀ i j, Valued.v ((h * X - 1) i j) < 1} ∩
      (fun X => (h * X).det - 1) ⁻¹' {z | Valued.v z < 1})
    refine IsOpen.inter ?_ (hb.preimage (hc.matrix_det.sub continuous_const))
    have : IsOpen (⋂ i, ⋂ j, {X : Matrix (Fin n) (Fin n) (Q.adicCompletion E) |
        Valued.v ((h * X - 1) i j) < 1}) :=
      isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hb.preimage ((hc.sub continuous_const).matrix_elem i j)
    simp only [← Set.setOf_forall] at this
    exact this
  obtain ⟨X, h1, h2⟩ := hd.exists_mem_open hU ⟨g, ⟨fun i j => by rw [hg]; simp, by rw [hg]; simp⟩⟩
  refine ⟨X, fun i j => ?_, ?_⟩
  · have h3 : Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X - 1) i j) < 1 := h1 i j
    have e : (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X) i j =
        (h * (algebraMap E (Q.adicCompletion E)).mapMatrix X - 1) i j +
          (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) i j := by simp
    rw [e]
    refine Valuation.map_add_le _ h3.le ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  · have h3 : Valued.v ((h * (algebraMap E (Q.adicCompletion E)).mapMatrix X).det - 1) < 1 := h2
    have := Valuation.map_eq_of_sub_lt Valued.v (x := (1 : Q.adicCompletion E)) (by rw [map_one]; exact h3)
    rwa [map_one] at this

theorem comp_mulVec {n : ℕ} (h : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
    (X : Matrix (Fin n) (Fin n) E) (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    comp P (h.mulVec (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i) =
      ((comp P).mapMatrix h * (algebraMap E (P.adicCompletion E)).mapMatrix X) i j := by
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, comp_alg]

theorem mem_span_detSet_iff : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)), Valued.v (((g⁻¹).1.mulVec (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i) Q) ≤ 1) → ∀ x : E, x ∈ Submodule.span (𝓞 E) (detSet L) ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (g.1.det Q) := by
  intro E _ _ n g L hL x
  classical
  have hL' : ∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)),
      Valued.v (comp Q ((g⁻¹).1.mulVec
        (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i)) ≤ 1 := hL
  have hle : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E), P.valuation E (a : E) ≤ 1 :=
    fun P a => P.valuation_le_one (K := E) a
  have hhg : ∀ Q : HeightOneSpectrum (𝓞 E),
      (comp Q).mapMatrix (g⁻¹).1 * (comp Q).mapMatrix g.1 = 1 := fun Q => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hdet : ∀ (Q : HeightOneSpectrum (𝓞 E)) (X : Matrix (Fin n) (Fin n) E),
      Q.valuation E X.det = Valued.v (comp Q g.1.det) *
        Valued.v ((comp Q).mapMatrix (g⁻¹).1 *
          (algebraMap E (Q.adicCompletion E)).mapMatrix X).det := fun Q X => by
    rw [← map_mul, RingHom.map_det, ← Matrix.det_mul, ← mul_assoc, ← map_mul, Units.mul_inv,
      map_one, one_mul, ← RingHom.map_det, val_alg]
  show _ ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (comp Q g.1.det)
  constructor
  · intro hx Q
    induction hx using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨v, hv, rfl⟩ := hd
      rw [hdet]
      refine mul_le_of_le_one_right' (val_det_le_one _ _ fun i j => ?_)
      rw [← comp_mulVec]
      exact (hL' _).1 (hv j) i Q
    | zero => simp
    | add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb
    | smul a b _ hb =>
      have e : a • b = (a : E) * b := rfl
      rw [e, map_mul]
      exact (mul_le_of_le_one_left' (hle Q a)).trans hb
  · intro hx
    have hloc : ∀ Q : HeightOneSpectrum (𝓞 E), ∃ b : 𝓞 E, b ∉ Q.asIdeal ∧
        b • x ∈ Submodule.span (𝓞 E) (detSet L) := by
      intro Q
      obtain ⟨X, hX1, hX2⟩ := exists_approx_matrix Q _ _ (hhg Q)
      choose c hcQ hc using fun i j => exists_clear Q ((g⁻¹).1.mulVec
        (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i)
        (by rw [comp_mulVec]; exact hX1 i j)
      obtain ⟨b, hb⟩ : ∃ b : 𝓞 E, b = ∏ p : Fin n × Fin n, c p.1 p.2 := ⟨_, rfl⟩
      have hbQ : b ∉ Q.asIdeal := by
        rw [hb, Q.isPrime.prod_mem_iff]
        rintro ⟨p, -, h⟩
        exact hcQ _ _ h
      have hb1 : Q.valuation E (b : E) = 1 :=
        (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) Q (r := b)).2 hbQ
      have hbc : ∀ i j (P : HeightOneSpectrum (𝓞 E)),
          P.valuation E (b : E) ≤ P.valuation E (c i j : E) := by
        intro i j P
        obtain ⟨t, ht⟩ : c i j ∣ b := hb ▸ Finset.dvd_prod_of_mem
          (fun p : Fin n × Fin n => c p.1 p.2) (Finset.mem_univ (i, j))
        have : (b : E) = (c i j : E) * (t : E) := by rw [ht]; push_cast; rfl
        rw [this, map_mul]
        exact mul_le_of_le_one_right' (hle P t)
      have hd : ((b : E) • X).det ∈ detSet L := by
        refine ⟨fun j i => (b : E) * X i j, fun j => (hL' _).2 fun i P => ?_, rfl⟩
        have e : comp P ((g⁻¹).1.mulVec
            (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) ((b : E) * X k j)) i) =
            algebraMap E _ (b : E) * comp P ((g⁻¹).1.mulVec
            (fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (X k j)) i) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, comp_alg, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [e, map_mul, val_alg]
        exact (mul_le_mul' (hbc i j P) le_rfl).trans (hc i j P)
      have hdv : Q.valuation E ((b : E) • X).det = Valued.v (comp Q g.1.det) := by
        rw [Matrix.det_smul, map_mul, map_pow, hb1, one_pow, one_mul, hdet, hX2, mul_one]
      obtain ⟨d, hdd⟩ : ∃ d, d = ((b : E) • X).det := ⟨_, rfl⟩
      rw [← hdd] at hd hdv
      have hg0 : Valued.v (comp Q g.1.det) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 ((g.isUnit.map Matrix.detMonoidHom).map (comp Q)).ne_zero
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [map_zero] at hdv
        exact hg0 hdv.symm
      obtain ⟨s, hsQ, hs⟩ := exists_clear Q (algebraMap E _ (x / d)) (by
        rw [comp_alg, val_alg, map_div₀, hdv]
        exact (div_le_one₀ (zero_lt_iff.2 hg0)).2 (hx Q))
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
        ((s : E) * (x / d)) (fun P => by
          have := hs P
          rwa [comp_alg, val_alg, ← map_mul] at this)
      refine ⟨s, hsQ, ?_⟩
      have e : s • x = a • d := by
        have e1 : s • x = (s : E) * x := rfl
        have e2 : a • d = algebraMap (𝓞 E) E a * d := rfl
        rw [e1, e2, ha]
        field_simp
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hd)
    let I : Ideal (𝓞 E) := (Submodule.span (𝓞 E) (detSet L)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E x)
    have hI : I = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
      have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
      obtain ⟨b, hb, hbx⟩ := hloc ⟨M, hM.isPrime, hM0⟩
      exact hb (hIM hbx)
    have h1 : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : 𝓞 E) • x ∈ Submodule.span (𝓞 E) (detSet L) := h1
    rwa [one_smul] at h2

end GlobalTheory.AdelicDetSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanDetSetIffAdelicLatticeValuationStatement
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_detSet_iff_adelicLattice_valuation : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x : Fin n → E, x ∈ L ↔ ∀ (i : Fin n) (Q : HeightOneSpectrum (𝓞 E)), Valued.v (((g⁻¹).1.mulVec (fun j => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x j)) i) Q) ≤ 1) → ∀ x : E, x ∈ Submodule.span (𝓞 E) (detSet L) ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ Valued.v (g.1.det Q) := by
  first | exact @GlobalTheory.AdelicDetSpan.mem_span_detSet_iff | exact GlobalTheory.AdelicDetSpan.mem_span_detSet_iff | (intros; apply GlobalTheory.AdelicDetSpan.mem_span_detSet_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullback
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.BaseChange

open ReciprocityTheory.ChartRestriction.G.Pdiv

section SlopeTestRemainingChoices

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def OActN.pull {O : Type} [Ring O] {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OActN O G) :
    OActN O ((Over.pullback f).obj G) where
  act x := (Over.pullback f).map (a.act x)
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul x y := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add x y := by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _

theorem OActN.pull_left {O : Type} [Ring O] {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OActN O G) (c : O) :
    ((OActN.pull f a).act c).left ≫ PullbackComparison.pφ f G = PullbackComparison.pφ f G ≫ (a.act c).left :=
  PullbackComparison.pullback_map_left_fst' f (a.act c)

theorem lift_pφ₂ {G : Over S} [GrpObj G] [IsCommMonObj G] {T' : Over S'} {T : Over S} (τ : T'.left ⟶ T.left)
    (a b : T' ⟶ (Over.pullback f).obj G) (a₀ b₀ : T ⟶ G)
    (ha : a.left ≫ PullbackComparison.pφ f G = τ ≫ a₀.left) (hb : b.left ≫ PullbackComparison.pφ f G = τ ≫ b₀.left) :
    (lift a b).left ≫ PullbackComparison.pφ₂ f G = τ ≫ (lift a₀ b₀).left := by
  apply PullbackComparison.adelic_GL2_ext_of_local_components
  · rw [Category.assoc, PullbackComparison.pφ₂_fst, ← Category.assoc, ← Over.comp_left, lift_fst, ha, Category.assoc,
      ← Over.comp_left, lift_fst]
  · rw [Category.assoc, PullbackComparison.pφ₂_snd, ← Category.assoc, ← Over.comp_left, lift_snd, hb, Category.assoc,
      ← Over.comp_left, lift_snd]

end SlopeTestRemainingChoices

section Aux2

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def tateMoveO {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : TateIsoO D k Q act e) : TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn hp a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn hp a)
  onto := fun n hn hp x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm hp a => by rw [← map_pow, I.tower n m hn hm hp a]
  isom := fun n hn hp a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn hp a b)

theorem isTanScal_push {O : Type} [Ring O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OActN O G) (a' : OActN O G')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S')
    (e : (epsPtR x ⟶ G') ≃* (epsPtR (x ≫ f) ⟶ G)) (he : ∀ v, (e v).left = v.left ≫ φ) (b : O) (c : R')
    (v : epsPtR x ⟶ G') : IsTanScal a' x b c v ↔ IsTanScal a (x ≫ f) b c (e v) := by
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  refine and_congr ?_ ?_
  · rw [one, he]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · have E : e (v ≫ a'.act b) = e v ≫ a.act b := Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    rw [← E, he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ a'.act b)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

theorem secPull_comp {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (u : G ⟶ G) (u' : G' ⟶ G') (hu : u'.left ≫ φ = φ ≫ u.left)
    (s : 𝟙_ (Over S) ⟶ G) : GlobalTheory.ObjPull.secPull h (s ≫ u) = GlobalTheory.ObjPull.secPull h s ≫ u' := by
  apply Over.OverMorphism.ext
  refine h.1.hom_ext ?_ ?_
  · rw [GlobalTheory.ObjPull.secPull_left]
    simp only [Over.comp_left, Category.assoc]
    rw [hu, ← Category.assoc (Over.Hom.left _) φ, GlobalTheory.ObjPull.secPull_left, Category.assoc]
  · rw [Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]

end Aux2

section Ker

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem gen_ker_push {G : Over S} [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (T : Over S')
    (x : T ⟶ (Over.pullback f).obj G)
    (H : ∃ t : ((P.pull (PullbackComparison.pφ₂ f G)).pull
      (lift (snd ((Over.pullback f).obj G) T ≫ x) (fst ((Over.pullback f).obj G) T)).left).Gen, t.IsGen) :
    ∃ t : (P.pull (lift (snd G (Over.mk (T.hom ≫ f)) ≫ GlobalTheory.ObjPull.pushEquiv (PullbackComparison.isGrpPullback f G) T x)
      (fst G (Over.mk (T.hom ≫ f)))).left).Gen, t.IsGen := by
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let Z : Over S' := Over.mk ((snd G T₀).left ≫ T.hom)
  have hZ : (fst G T₀).left ≫ G.hom = Z.hom ≫ f :=
    (Over.w (fst G T₀)).trans ((Over.w (snd G T₀)).symm.trans (Category.assoc _ _ _).symm)
  let a : Z ⟶ (Over.pullback f).obj G := Over.homMk (pullback.lift (fst G T₀).left Z.hom hZ) (pullback.lift_snd _ _ _)
  let u : Z ⟶ T := Over.homMk (snd G T₀).left rfl
  have key : (lift (snd G T₀ ≫ GlobalTheory.ObjPull.pushEquiv (PullbackComparison.isGrpPullback f G) T x) (fst G T₀)).left =
      (lift a u).left ≫ ((lift (snd ((Over.pullback f).obj G) T ≫ x) (fst ((Over.pullback f).obj G) T)).left ≫
        PullbackComparison.pφ₂ f G) := by
    apply PullbackComparison.adelic_GL2_ext_of_local_components
    · have k1 := congrArg Over.Hom.left (show lift a u ≫ lift (snd ((Over.pullback f).obj G) T ≫ x)
          (fst ((Over.pullback f).obj G) T) ≫ fst ((Over.pullback f).obj G) ((Over.pullback f).obj G) = u ≫ x by simp)
      simp only [Over.comp_left] at k1
      rw [← Over.comp_left, lift_fst, Category.assoc, Category.assoc, PullbackComparison.pφ₂_fst,
        ← Category.assoc (Over.Hom.left (lift (snd ((Over.pullback f).obj G) T ≫ x) _)), ← Category.assoc, k1]
      rfl
    · have k2 := congrArg Over.Hom.left (show lift a u ≫ lift (snd ((Over.pullback f).obj G) T ≫ x)
          (fst ((Over.pullback f).obj G) T) ≫ snd ((Over.pullback f).obj G) ((Over.pullback f).obj G) = a by simp)
      simp only [Over.comp_left] at k2
      rw [← Over.comp_left, lift_snd, Category.assoc, Category.assoc, PullbackComparison.pφ₂_snd,
        ← Category.assoc (Over.Hom.left (lift (snd ((Over.pullback f).obj G) T ≫ x) _)), ← Category.assoc, k2]
      exact (pullback.lift_fst _ _ _).symm
  obtain ⟨t, ht⟩ := H
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullIn P (fun _ : PUnit => PullbackComparison.pφ₂ f G) (fun _ => 1)
    (lift (snd ((Over.pullback f).obj G) T ≫ x) (fst ((Over.pullback f).obj G) T)).left) t ht
  exact gen_chartPull (chartPullSame P _ _ (fun _ : PUnit => 1) (lift a u).left (fun _ => key)) t₁ ht₁

end Ker

theorem exists_objMap : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (f : S' ⟶ S), f ≫ s = s' →
    ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  intro p _ D R _ b N S S' s s' o f hs
  subst hs
  have h : IsGrpPullback ((Over.pullback f).obj o.A) o.A f (PullbackComparison.pφ f o.A) := PullbackComparison.isGrpPullback f o.A
  have hact := OActN.pull_left f o.act
  have hP := pull_isLB o.isLB (PullbackComparison.pφ₂ f o.A)
  have hL := pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left
  have hL' := pull_isLB hP (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 ((Over.pullback f).obj o.A))).left
  have hdiag : (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 ((Over.pullback f).obj o.A))).left ≫ PullbackComparison.pφ₂ f o.A =
      PullbackComparison.pφ f o.A ≫ (lift (𝟙 o.A) (𝟙 o.A)).left :=
    lift_pφ₂ f _ _ _ _ _ (by simp) (by simp)
  have hLi : LBIso ((o.P.pull (PullbackComparison.pφ₂ f o.A)).pull
      (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 ((Over.pullback f).obj o.A))).left)
      ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull (PullbackComparison.pφ f o.A)) :=
    LBIso.chartPull (chartPullLinComb o.P (PullbackComparison.pφ₂ f o.A) _ _ (fun _ : PUnit => 1) (PullbackComparison.pφ f o.A) (fun _ => hdiag))
      (chartPullPull _ (PullbackComparison.pφ f o.A) _ rfl) (PullbackComparison.gen_refl _ hL)
  obtain ⟨hab, hamp, -⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' o.A _ f _
    _ _ hL hL' o.ab h hLi
  have hrose : ∀ c : D.O, LBIso ((o.P.pull (PullbackComparison.pφ₂ f o.A)).pull
      (lift (fst ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A) ≫ (OActN.pull f o.act).act c)
        (snd ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A))).left)
      ((o.P.pull (PullbackComparison.pφ₂ f o.A)).pull (lift (fst ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A))
        (snd ((Over.pullback f).obj o.A) ((Over.pullback f).obj o.A) ≫
          (OActN.pull f o.act).act (D.star c).unop)).left) := fun c => by
    refine LBIso.chartPull (chartPullLinComb o.P _ _ _ (fun _ : PUnit => 1) (PullbackComparison.pφ₂ f o.A) (fun _ => ?_))
      (chartPullLinComb o.P _ _ _ (fun _ : PUnit => 1) (PullbackComparison.pφ₂ f o.A) (fun _ => ?_)) (o.rosati c)
    · refine lift_pφ₂ f _ _ _ _ _ ?_ (PullbackComparison.pφ₂_snd f o.A).symm
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← PullbackComparison.pφ₂_fst, Category.assoc]
    · refine lift_pφ₂ f _ _ _ _ _ (PullbackComparison.pφ₂_fst f o.A).symm ?_
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← PullbackComparison.pφ₂_snd, Category.assoc]
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  refine ⟨{ A := (Over.pullback f).obj o.A
            ab := hab
            act := OActN.pull f o.act
            P := o.P.pull (PullbackComparison.pφ₂ f o.A)
            isLB := hP
            rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
              (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
            rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
              (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
            symm := LBIso.chartPull (chartPullPull o.P _ _ rfl)
              (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ₂ f o.A) (fun _ => PullbackComparison.lift_swap f o.A)) o.symm
            ample := hamp o.ample
            kerP := ?_
            rosati := hrose
            lie := ?_
            lieRank := fun k _ _ x β hx i =>
              (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' o.A _ f _ (o.act.toF D) ((OActN.pull f o.act).toF D) h
                (fun c => hact _) k x (β.comp (b.t i)) D.m).2
                (o.lieRank k (x ≫ f) β ((Category.assoc _ _ _).trans hx) i)
            eta := fun y => GlobalTheory.ObjPull.secPull h (o.eta y)
            eta_add := fun y z => by rw [o.eta_add, map_mul]
            eta_lin := fun c y => by rw [o.eta_lin]; exact secPull_comp f h _ _ (hact c) _
            eta_ker := fun y => by rw [o.eta_ker y, map_one]
            geom := fun k _ _ x β hx => ?_ },
    ⟨{ φ := PullbackComparison.pφ f o.A
       φ₂ := PullbackComparison.pφ₂ f o.A
       cart := h
       sq := PullbackComparison.isSquare f o.A
       act := hact
       pol := PullbackComparison.gen_refl _ hP
       eta := fun y => GlobalTheory.ObjPull.secPull_left h _ }⟩⟩
  · obtain ⟨e, he, hk⟩ := o.kerP
    refine ⟨e, he, fun T x H => ?_⟩
    have := hk (Over.mk (T.hom ≫ f)) (GlobalTheory.ObjPull.pushEquiv h T x) (gen_ker_push f o.P T x H)
    exact (GlobalTheory.ObjPull.pushEquiv h T).injective (by rw [map_pow, this, map_one])
  · intro R' _ β x hx v hv
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
      (Category.assoc _ _ _).symm
    obtain ⟨w₀, hw₀, hv₀⟩ := o.lie R' β (x ≫ f) ((Category.assoc _ _ _).trans hx) (e v)
      ((isTanScal_push f h o.act _ hact x e he _ _ v).1 hv)
    refine ⟨fun i => e.symm (w₀ i), fun i c => (isTanScal_push f h o.act _ hact x e he _ _ _).2
      (by rw [e.apply_symm_apply]; exact hw₀ i c), e.injective ?_⟩
    rw [hv₀, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]
  · obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β ((Category.assoc _ _ _).trans hx)
    refine ⟨tateMoveO (GlobalTheory.ObjPull.pushEquiv h (Over.mk x)) (fun c g => ?_) (fun n g g' z hz => ?_) I, fun y => ?_⟩
    · apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A _ f _ _ _ hL hL' h hLi
        (Over.mk x) n g g' _ _ _ rfl rfl).2 hz
    · exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull h _ _).trans (hI y))

end GlobalTheory.UPel.HT.BaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObjectPullback : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (f : S' ⟶ S), f ≫ s = s' → ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  first | exact @GlobalTheory.UPel.HT.BaseChange.exists_objMap | exact GlobalTheory.UPel.HT.BaseChange.exists_objMap | (intros; apply GlobalTheory.UPel.HT.BaseChange.exists_objMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitIntertwinerAdelicQuaternion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitIntertwinerAdelicQuaternion
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem nrm_smul_eq_sq_mul {R : Type*} [CommRing R] {a b : R} (t : R) (x : ℍ[R, a, b]) :
    nrm (t • x) = t ^ 2 * nrm x := by
  simp [nrm]; ring

theorem nrm_sum_orthIdem_smul {R : Type*} [CommRing R] {a b : R} {ι : Type} [Fintype ι] (η : ι → R)
    (y : ι → ℍ[R, a, b]) (h1 : ∀ i, η i * η i = η i) (h2 : ∀ i j, i ≠ j → η i * η j = 0)
    (h3 : ∑ i, η i = 1) : nrm (∑ i, η i • y i) = ∑ i, η i * nrm (y i) := by
  classical
  have key : ∀ i, η i * nrm (∑ j, η j • y j) = η i * nrm (y i) := by
    intro i
    have hs : η i • (∑ j, η j • y j) = η i • y i := by
      rw [Finset.smul_sum, Finset.sum_eq_single i]
      · rw [smul_smul, h1]
      · intro j _ hj
        rw [smul_smul, h2 i j (Ne.symm hj), zero_smul]
      · simp
    have := congrArg nrm hs
    rwa [nrm_smul_eq_sq_mul, nrm_smul_eq_sq_mul, sq, h1] at this
  calc nrm (∑ i, η i • y i) = ∑ i, η i * nrm (∑ j, η j • y j) := by
        rw [← Finset.sum_mul, h3, one_mul]
    _ = _ := Finset.sum_congr rfl fun i _ => key i

def quatStdBasis {R : Type*} [CommRing R] (a b : R) : Fin 4 → ℍ[R, a, b] :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

theorem nrm_intertwiner_comb {R : Type*} [CommRing R] {a b c : R} (p q : ℍ[R, a, b]) (hp : p.re = 0) (hq : q.re = 0)
    (hpp : p * p = algebraMap R ℍ[R, a, b] c) (hqq : q * q = algebraMap R ℍ[R, a, b] c) :
    ∑ i, (![a * b, -b, -a, 1] : Fin 4 → R) i * nrm (p * quatStdBasis a b i + quatStdBasis a b i * q)
      = -8 * a * b * c := by
  have h1 := congrArg QuaternionAlgebra.re hpp
  have h2 := congrArg QuaternionAlgebra.re hqq
  simp [QuaternionAlgebra.algebraMap_eq, hp, hq] at h1 h2
  simp [Fin.sum_univ_four, quatStdBasis, nrm, hp, hq]
  linear_combination (-4 * a * b) * h1 + (-4 * a * b) * h2

theorem exists_unit_intertwiner : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ p q : DA F a b, p.re = 0 → q.re = 0 → p * p = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ y : DA F a b, IsUnit (nrm y) ∧ y * q = p * y := by
  intro F _ _ a b ha hb c hc p q hp hq hpp hqq
  have hcomb := nrm_intertwiner_comb p q hp hq hpp hqq
  have hu : IsUnit (-8 * algebraMap F (AF F) a * algebraMap F (AF F) b * algebraMap F (AF F) c) := by
    have h : IsUnit (-8 * a * b * c) := by
      refine Ne.isUnit ?_
      have : (-8 : F) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero this ha) hb) hc
    have h' := h.map (algebraMap F (AF F))
    rwa [map_mul, map_mul, map_mul, map_neg, map_ofNat] at h'
  rw [← hcomb] at hu
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination F (Fin 4) _ _ hu
  refine ⟨∑ i, η i • (p * quatStdBasis _ _ i + quatStdBasis _ _ i * q), ?_, ?_⟩
  · rw [nrm_sum_orthIdem_smul η _ h1 h2 h3]; exact h4
  · rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [add_mul, mul_add, mul_assoc _ q q, hqq, ← mul_assoc p p, hpp, add_comm, mul_assoc,
      Algebra.commutes]

end GlobalTheory.QSA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitIntertwinerAdelicQuaternionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_intertwiner_adelicQuaternion : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ p q : DA F a b, p.re = 0 → q.re = 0 → p * p = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ y : DA F a b, IsUnit (nrm y) ∧ y * q = p * y := by
  first | exact @GlobalTheory.QSA.exists_unit_intertwiner | exact GlobalTheory.QSA.exists_unit_intertwiner | (intros; apply GlobalTheory.QSA.exists_unit_intertwiner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubfunctorStalkIdealCriterion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubfunctorStalkIdealCriterion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinStalk

theorem stalk_isArtinianRing (K : Type) [Field K] (X : Scheme) (f : X ⟶ Sp K) [IsFinite f] (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have hfin : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.Finite :=
    f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  letI := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  haveI : Module.Finite K Γ(X, ⊤) := hfin
  haveI : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K Γ(X, ⊤)
  have hU := isAffineOpen_top X
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  have hl := hU.isLocalization_stalk ⟨x, trivial⟩
  exact IsArtinianRing.localization_artinian (hU.primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl _

end GlobalTheory.FinStalk

namespace GlobalTheory.FinStalk

theorem stalk_quotient_ne_top_and_isArtinianRing : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → J ≠ ⊤ ∧ IsArtinianRing (A.left.presheaf.stalk x₀ ⧸ J) := by
  intro K _ A _ H _ j hj hci hfin x₀ hx₀ J hJ
  obtain ⟨p, hp⟩ := hx₀
  have hη : (η[H] ≫ j).left = η[A].left := congrArg CommaMorphism.left (IsMonHom.one_hom j)
  obtain ⟨h₀, e⟩ : ∃ h₀ : H.left, x₀ = j.left.base h₀ :=
    ⟨η[H].left.base p, by rw [← hp, ← hη]; rfl⟩
  subst e

  have hJ1 : J ≤ RingHom.ker (j.left.stalkMap h₀).hom :=
    (hJ (H.left.presheaf.stalk h₀) (j.left.stalkMap h₀).hom).1
      ⟨H.left.fromSpecStalk h₀, (Scheme.SpecMap_stalkMap_fromSpecStalk j.left).symm⟩
  have hne : J ≠ ⊤ := fun h => RingHom.ker_ne_top _ (top_le_iff.1 (h ▸ hJ1))
  refine ⟨hne, ?_⟩
  haveI : Nontrivial (A.left.presheaf.stalk (j.left.base h₀) ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsLocalRing (A.left.presheaf.stalk (j.left.base h₀) ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk J) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := (hJ _ (Ideal.Quotient.mk J)).2 (by rw [Ideal.mk_ker])
  let R := CommRingCat.of (A.left.presheaf.stalk (j.left.base h₀) ⧸ J)
  have hpt : y.base (IsLocalRing.closedPoint R) = h₀ := by
    apply j.left.isClosedEmbedding.injective
    have : j.left.base (y.base (IsLocalRing.closedPoint R)) = (A.left.fromSpecStalk (j.left.base h₀)).base
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).base (IsLocalRing.closedPoint R)) :=
      congrArg (fun g : Sp R ⟶ A.left => g.base (IsLocalRing.closedPoint R)) hy
    rw [this]
    haveI : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := by
      change IsLocalHom (Ideal.Quotient.mk J); infer_instance
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have key : ∀ z (_ : y.base (IsLocalRing.closedPoint R) = z),
      ∃ φ : H.left.presheaf.stalk z ⟶ R, Spec.map φ ≫ H.left.fromSpecStalk z = y := by
    rintro z rfl
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk y⟩
  obtain ⟨φ, hφ⟩ := key h₀ hpt
  have hcomp : j.left.stalkMap h₀ ≫ φ = CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    apply Spec.map_injective
    rw [← cancel_mono (A.left.fromSpecStalk (j.left.base h₀)), ← hy, ← hφ, Spec.map_comp,
      Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]
  have hsurj : Function.Surjective φ.hom := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) r
    exact ⟨(j.left.stalkMap h₀).hom a, by
      rw [← CommRingCat.comp_apply, hcomp]; rfl⟩
  haveI := stalk_isArtinianRing K H.left H.hom h₀
  exact hsurj.isArtinianRing

end GlobalTheory.FinStalk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubfunctorStalkIdealCriterionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_subfunctor_stalk_ideal_criterion : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → J ≠ ⊤ ∧ IsArtinianRing (A.left.presheaf.stalk x₀ ⧸ J) := by
  first | exact @GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing | exact GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing | (intros; apply GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing <;> assumption)
end
end
