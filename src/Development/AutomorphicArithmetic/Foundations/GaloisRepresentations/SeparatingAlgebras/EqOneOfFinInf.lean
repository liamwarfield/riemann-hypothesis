module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealTiedSetDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteBasisAlgebraicForms

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EqOneOfFinInf
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem eq_one_of_fin_inf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {x : UA E a}
    (hf : x ∈ finU (E := E) (n := a)) (hi : x ∈ infU E a) : x = 1 := by
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) x.1 = 1 := hf
  have h2 : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hi
  exact Subtype.ext (ga_ext (by rw [h1]; simp) (by rw [h2]; simp))

private theorem cLoc_of_inf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    (w : HeightOneSpectrum (𝓞 E)) {x : UA E a} (hx : x ∈ infU E a) : cLoc w x = 1 := by
  have h2 : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  have e : cLoc w x = Matrix.GeneralLinearGroup.map (pLoc E w) (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by
    ext i j
    rfl
  rw [e, h2, map_one]

private theorem conj_form {G : Type} [Group G] {s j g g' γ x c : G} (hj : j * g' = g' * j) (hj2 : j * g = g * j)
    (hxg : g * x = x * g) (hxj : j * x = x * j) (h : s * j * g' = γ * (s * j * g) * x * c) :
    γ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ := by
  have h0 : γ * (s * j * g) = s * j * g' * c⁻¹ * x⁻¹ := by
    rw [h]; group
  have h1 : γ = s * j * g' * c⁻¹ * x⁻¹ * (s * j * g)⁻¹ := eq_mul_inv_of_mul_eq h0
  have hc : Commute x (g⁻¹ * j⁻¹) :=
    (Commute.inv_right (show Commute x g from hxg.symm)).mul_right (Commute.inv_right (show Commute x j from hxj.symm))
  have hq : x⁻¹ * (g⁻¹ * j⁻¹) = g⁻¹ * j⁻¹ * x⁻¹ := (hc.inv_left).eq
  have hq2 : g⁻¹ * j⁻¹ = j⁻¹ * g⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hj2]
  calc γ = s * (j * g') * c⁻¹ * (x⁻¹ * (g⁻¹ * j⁻¹)) * s⁻¹ := by rw [h1]; group
    _ = s * (g' * j) * c⁻¹ * (j⁻¹ * g⁻¹ * x⁻¹) * s⁻¹ := by rw [hj, hq, hq2]
    _ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ := by group

theorem UpperTheory.Gal.Gen.sep_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.LocComm → UpperTheory.Gal.Gen.RatFin → UpperTheory.Gal.Gen.Sep := by
  intro hLev hComm hRat E _ _ _ a w₀ hs K hK J hJ S T hT hinj
  classical
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E a
  have hI : IsCompact (infU E a : Set (UA E a)) := isCompact_iff_compactSpace.2 inferInstance
  obtain ⟨hL0, hmem0, -, -, -, -⟩ := hLev E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have hC0 : IsCompact (lev K w₀ (J 0) : Set (UA E a)) := hL0.compact

  let P : UA E a × UA E a × UA E a × UA E a × UA E a → UA E a :=
    fun q => q.1 * q.2.2.1 * q.2.2.2.1 * q.2.1⁻¹ * q.2.2.2.2 * q.1⁻¹
  let D : Set (UA E a × UA E a × UA E a × UA E a × UA E a) :=
    (S : Set (UA E a)) ×ˢ (T : Set (UA E a)) ×ˢ (T : Set (UA E a)) ×ˢ
      (lev K w₀ (J 0) : Set (UA E a)) ×ˢ (infU E a : Set (UA E a))
  have hD : IsCompact D :=
    S.finite_toSet.isCompact.prod (T.finite_toSet.isCompact.prod (T.finite_toSet.isCompact.prod (hC0.prod hI)))
  have hP : Continuous P := by
    simp only [P]
    fun_prop
  have hR : (P '' D ∩ (ratU E a : Set (UA E a))).Finite := (hRat E a).1 _ (hD.image hP)

  let Y : UA E a × UA E a → GL (Fin a) (w₀.adicCompletion E) := fun q => cLoc w₀ (q.1⁻¹ * q.2 * q.1)
  let F : Set (GL (Fin a) (w₀.adicCompletion E)) :=
    Y '' ((S : Set (UA E a)) ×ˢ ((P '' D ∩ (ratU E a : Set (UA E a))) \ {1}))
  have hF : F.Finite := (S.finite_toSet.prod (hR.subset Set.diff_subset)).image _
  have hne : ∀ y ∈ F, y ≠ 1 := by
    rintro _ ⟨⟨s, γ⟩, ⟨-, ⟨-, hγ⟩, hγ1⟩, rfl⟩ e
    refine hγ1 ((hRat E a).2 w₀ γ hγ ?_)
    simp only [Y, map_mul, map_inv] at e
    have := congrArg (fun t => cLoc w₀ s * t * (cLoc w₀ s)⁻¹) e
    simpa [mul_assoc] using this
  have ev : ∀ y ∈ F, ∀ᶠ n in Filter.atTop, y ∉ J n := by
    intro y hy
    obtain ⟨n, hn⟩ := hJ.small {y}ᶜ (isOpen_compl_singleton.mem_nhds (by simpa using (hne y hy).symm))
    filter_upwards [Filter.eventually_ge_atTop n] with m hm hym
    exact hn (hJ.anti hm hym) rfl
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 ((Set.Finite.eventually_all hF).2 ev)
  refine ⟨n₀, fun n hn y g hg g' hg' γ hγ x hx c hc h => ?_⟩
  obtain ⟨⟨s, hsS⟩, ⟨j, hjL, hjJ⟩⟩ := y
  simp only at h
  obtain ⟨hLn, -, hcl, hck, -, hmono⟩ := hLev E a w₀ hs K hK (J n) (hJ.isOpen n) (hJ.compact n)
  have hcJ : cLoc w₀ c ∈ J n := hcl c hc
  have hcC0 : c ∈ lev K w₀ (J 0) := hmono (J 0) c hc (hJ.anti (Nat.zero_le n) hcJ)
  have hjC0 : j ∈ lev K w₀ (J 0) := (hmem0 j).2 ⟨1, K.one_mem, j, hjL, hjJ, (one_mul j).symm⟩
  have hgF : g ∈ finU (E := E) (n := a) := (hT g hg).1
  have hgF' : g' ∈ finU (E := E) (n := a) := (hT g' hg').1
  have hcF : c ∈ finU (E := E) (n := a) := hLn.fin hc
  have hjF : j ∈ finU (E := E) (n := a) := (Subgroup.mem_inf.1 hjL).1
  have hg1 : cLoc w₀ g = 1 := (hT g hg).2 w₀ (not_apart_self w₀)
  have hg1' : cLoc w₀ g' = 1 := (hT g' hg').2 w₀ (not_apart_self w₀)
  have hx1 : cLoc w₀ x = 1 := cLoc_of_inf w₀ hx
  have hγeq : γ = s * g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ * s⁻¹ :=
    conj_form (hComm E a w₀ j g' hjL (hT g' hg').2) (hComm E a w₀ j g hjL (hT g hg).2)
      (fin_mul_inf hgF hx) (fin_mul_inf hjF hx) h
  have hcloc : cLoc w₀ (s⁻¹ * γ * s) = cLoc w₀ j * (cLoc w₀ c)⁻¹ * (cLoc w₀ j)⁻¹ := by
    have e : s⁻¹ * γ * s = g' * (j * c⁻¹ * j⁻¹) * g⁻¹ * x⁻¹ := by
      rw [hγeq]; group
    rw [e]
    simp only [map_mul, map_inv, hg1, hg1', hx1, inv_one, one_mul, mul_one]
  have hin : cLoc w₀ (s⁻¹ * γ * s) ∈ J n := by
    rw [hcloc]
    exact hJ.normal n _ hjJ _ (inv_mem hcJ)
  have hγ1 : γ = 1 := by
    by_contra hne'
    have hγZ : γ ∈ P '' D :=
      ⟨(s, g, g', j * c⁻¹ * j⁻¹, x⁻¹),
        ⟨hsS, hg, hg', mul_mem (mul_mem hjC0 (inv_mem hcC0)) (inv_mem hjC0), inv_mem hx⟩, hγeq.symm⟩
    exact hn₀ n hn _ ⟨(s, γ), ⟨hsS, ⟨hγZ, hγ⟩, hne'⟩, rfl⟩ hin
  subst hγ1
  have h2 : g' = g * x * c := by
    have : s * j * g' = s * j * (g * x * c) := by
      rw [h]; group
    exact mul_left_cancel this
  have hxF : x ∈ finU (E := E) (n := a) := by
    have e : x = g⁻¹ * g' * c⁻¹ := by
      rw [h2]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hgF) hgF') (inv_mem hcF)
  have hxe : x = 1 := eq_one_of_fin_inf hxF hx
  subst hxe
  have h3 : g⁻¹ * g' = c := by
    rw [h2]; group
  have hcK : c ∈ K := hck c hc (by
    rw [← h3, map_mul, map_inv, hg1, hg1', inv_one, one_mul])
  exact hinj g hg g' hg' (h3 ▸ hcK)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.WBound
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.UnitaryCoordinateAlgebraDense
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.PolyRealU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_entry (τ : E →+* ℂ) (i j : Fin n) :
    Continuous fun x : infU E n => (cEmb τ x.1).val i j := by
  have h1 : Continuous (coord (E := E) τ) := by
    unfold coord
    split_ifs
    · exact continuous_apply _
    · exact Complex.continuous_conj.comp (continuous_apply _)
  have h2 : Continuous (pInf E) := continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst
  have h3 : Continuous fun x : infU E n => (x.1.1.val : Matrix (Fin n) (Fin n) (Ad E)) i j :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem i j
  exact h1.comp (h2.comp h3)


omit [NumberField E] [IsCMField E] in
theorem coord_star' (τ : E →+* ℂ) (z : Cinf E) : coord τ (star z) = star (coord τ z) := by
  unfold coord
  split_ifs <;> rfl

theorem coord_conj (τ : E →+* ℂ) (z : Cinf E) : coord (ComplexEmbedding.conjugate τ) z = star (coord τ z) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (ComplexEmbedding.isReal_iff.2 h)
  unfold coord
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [ite_eq_left h, ite_eq_right (by rw [h]; exact hne.symm)]
    rfl
  · rw [ite_eq_left h, ite_eq_right (by rw [h]; exact hne)]
    simp

theorem entry_inv (τ : E →+* ℂ) (x : UA E n) (i j : Fin n) :
    (cEmb τ x⁻¹).val i j = star ((cEmb τ x).val j i) := by
  have hx : Formalism.UG.cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at hx
  have h1 : (x.1⁻¹).val = Formalism.UG.cT (conjAd E) x.1.val := Units.inv_eq_of_mul_eq_one_left hx
  have h2 : ∀ y, pInf E (conjAd E y) = star (pInf E y) := fun y => by
    change (infEq E).symm (infEq E _) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  change coord τ (pInf E ((x.1⁻¹).val i j)) = star (coord τ (pInf E (x.1.val j i)))
  rw [h1, ← coord_star', ← h2]
  rfl

theorem eq_of_entry {x y : infU E n} (h : ∀ τ i j, (cEmb τ x.1).val i j = (cEmb τ y.1).val i j) : x = y := by
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · ext i j w
    have h1 : coord w.embedding (pInf E (x.1.1.val i j)) = coord w.embedding (pInf E (y.1.1.val i j)) :=
      h w.embedding i j
    unfold coord at h1
    rw [InfinitePlace.mk_embedding, ite_eq_left rfl] at h1
    exact h1
  · exact (MonoidHom.mem_ker.1 x.2).trans (MonoidHom.mem_ker.1 y.2).symm

theorem coprod_adjoin {G : Type} [Mul G] (S : Set (G → ℂ))
    (hS : ∀ p ∈ S, ∃ (m : ℕ) (a b : Fin m → G → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
      ∀ x k, p (x * k) = ∑ i, a i x * b i k) :
    ∀ p ∈ Algebra.adjoin ℂ S, ∃ (m : ℕ) (a b : Fin m → G → ℂ),
      (∀ i, a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k :=
  _root_.GlobalTheory.SplittingAdditive.main S hS

theorem poly_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, Continuous p) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, star p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ (∀ x y : infU E n, x ≠ y → ∃ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, p x ≠ p y) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ (m : ℕ) (a b : Fin m → infU E n → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ b i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  intro E _ _ _ n
  have hstar : ∀ (τ : E →+* ℂ) (i j : Fin n), (fun x : infU E n => star ((cEmb τ x.1).val i j)) ∈
      Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} :=
    fun τ i j => Algebra.subset_adjoin
      ⟨ComplexEmbedding.conjugate τ, i, j, funext fun x => (coord_conj τ _).symm⟩
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun x y hxy => ?_, fun p hp => ?_, coprod_adjoin _ ?_⟩
  · induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨τ, i, j, rfl⟩ := hp
      exact continuous_entry τ i j
    | algebraMap c => exact continuous_const
    | add p q _ _ hp hq => exact hp.add hq
    | mul p q _ _ hp hq => exact hp.mul hq
  · induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨τ, i, j, rfl⟩ := hp
      exact hstar τ i j
    | algebraMap c => exact Subalgebra.algebraMap_mem _ (star c)
    | add p q _ _ hp hq => rw [star_add]; exact add_mem hp hq
    | mul p q _ _ hp hq => rw [star_mul]; exact mul_mem hq hp
  · by_contra h
    push Not at h
    exact hxy (eq_of_entry fun τ i j => h _ (Algebra.subset_adjoin ⟨τ, i, j, rfl⟩))
  · induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨τ, i, j, rfl⟩ := hp
      convert hstar τ j i using 2 with x
      exact entry_inv τ x.1 i j
    | algebraMap c => exact Subalgebra.algebraMap_mem _ c
    | add p q _ _ hp hq => exact add_mem hp hq
    | mul p q _ _ hp hq => exact mul_mem hp hq
  · rintro _ ⟨τ, i, j, rfl⟩
    refine ⟨n, fun l x => (cEmb τ x.1).val i l, fun l x => (cEmb τ x.1).val l j,
      fun l => ⟨Algebra.subset_adjoin ⟨τ, i, l, rfl⟩, Algebra.subset_adjoin ⟨τ, l, j, rfl⟩⟩, fun x k => ?_⟩
    change (cEmb τ (x.1 * k.1)).val i j = _
    rw [map_mul, Units.val_mul, Matrix.mul_apply]

end GlobalTheory.PolyRealU
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen


open MvPolynomial in
private theorem continuous_coeff_blockAct' {Y : Type} [TopologicalSpace Y] {T : Type} {k n : ℕ}
    (A : Y → T → Matrix (Fin k) (Fin k) ℂ) (hA : ∀ t a b, Continuous fun x => A x t a b)
    (F : MvPolynomial (T × Fin k × Fin n) ℂ) :
    ∀ m, Continuous fun x => (Formalism.GradedWeylDivisibility.blockAct ℂ (A x) F).coeff m := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a =>
    intro m
    have e : ∀ x, Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (A x) (C a) = (C a : MvPolynomial (T × Fin k × Fin n) ℂ) :=
      fun x => (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (A x)).commutes a
    simp only [e]
    exact continuous_const
  | add p q hp hq =>
    intro m
    simp only [map_add (f := _), AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (hp m).add (hq m)
  | mul_X p w hp =>
    intro m
    have e : ∀ x, Formalism.GradedWeylDivisibility.blockAct ℂ (A x) (X w) = ∑ b : Fin k, C (A x w.1 w.2.1 b) * X (w.1, (b, w.2.2)) :=
      fun x => aeval_X _ _
    simp only [map_mul, e, Finset.mul_sum, coeff_sum]
    refine continuous_finsetSum _ fun b _ => ?_
    simp only [mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X']
    by_cases hw : ((w.1, (b, w.2.2)) : T × Fin k × Fin n) ∈ m.support
    · simp only [hw, ite_true]
      exact (hA _ _ _).mul (hp _)
    · simp only [hw, ite_false, mul_zero]
      exact continuous_const

private theorem continuous_detTwK' {Y : Type} [TopologicalSpace Y] {T : Type} [Fintype T] {n : ℕ}
    (lam : T → DomWeight n) (g : Y → (T → GL (Fin n) ℂ))
    (hg : ∀ v a b, Continuous fun x => ((g x v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) :
    Continuous fun x => Formalism.L2.DIV.detTwK lam (g x) := by
  simp only [Formalism.L2.DIV.detTwK]
  refine continuous_finsetProd _ fun τ _ => ?_
  have e : ∀ x, detPow ℂ n (g x τ) (lam τ).detShift =
      ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift := by
    intro x
    rw [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  simp only [e]
  have hc : Continuous fun x => ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_pi fun a => continuous_pi fun b => hg τ a b
  refine hc.matrix_det.zpow₀ _ fun x => Or.inl ?_
  exact (Matrix.isUnit_iff_isUnit_det _).1 (g x τ).isUnit |>.ne_zero


private theorem continuous_rhoK_coeff' {Y : Type} [TopologicalSpace Y] {T : Type} [Fintype T] {n : ℕ}
    (lam : T → DomWeight n) {d : ℕ} (B : Module.Basis (Fin d) ℂ (Formalism.L2.DIV.VV ℂ lam)) (g : Y → (T → GL (Fin n) ℂ))
    (hg : ∀ v a b, Continuous fun x => ((g x v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) (i j : Fin d) :
    Continuous fun x => LinearMap.toMatrix B B (Formalism.L2.DIV.rhoK lam (g x)) i j := by
  classical
  obtain ⟨s, a, ha⟩ := GlobalTheory.IntStruct.exists_coord_eq_sum_coeff (Formalism.L2.DIV.VV ℂ lam) B i
  have e : ∀ x, LinearMap.toMatrix B B (Formalism.L2.DIV.rhoK lam (g x)) i j = ∑ m : s, a m *
      (Formalism.L2.DIV.detTwK lam (g x) * (Formalism.GradedWeylDivisibility.blockAct ℂ
        (fun τ => Matrix.transpose ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
        ((B j : Formalism.L2.DIV.VV ℂ lam) : Formalism.L2.DIV.Pol ℂ T n)).coeff m.1) := by
    intro x
    rw [LinearMap.toMatrix_apply, ha]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
  simp only [e]
  exact continuous_finsetSum _ fun m _ => continuous_const.mul ((continuous_detTwK' lam g hg).mul
    (continuous_coeff_blockAct' _ (fun t a b => hg t b a) _ m.1))

private theorem continuous_rep_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Wt E a) {d : ℕ}
    (B : Module.Basis (Fin d) ℂ W.Sp) (i j : Fin d) :
    Continuous fun x : infU E a => B.repr (W.rep x (B i)) j := by
  have h := continuous_rhoK_coeff' (T := InfinitePlace E) W B (fun x : infU E a => cAll x.1)
    (fun v p q => GlobalTheory.PolyRealU.continuous_entry v.embedding p q) j i
  refine h.congr fun x => ?_
  rw [LinearMap.toMatrix_apply]
  rfl

theorem UpperTheory.Gal.Gen.wBound_pf :
    UpperTheory.Gal.Gen.WBound := by
  intro E _ _ _ a W d B
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E a
  have hc : Continuous fun x : infU E a => fun (i j : Fin d) => B.repr (W.rep x (B i)) j :=
    continuous_pi fun i => continuous_pi fun j => continuous_rep_coeff W B i j
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x i j => ?_⟩
  exact ((norm_le_pi_norm (fun j => B.repr (W.rep x (B i)) j) j).trans
    (norm_le_pi_norm (fun (i j : Fin d) => B.repr (W.rep x (B i)) j) i)).trans (hC x (Set.mem_univ _))
end
