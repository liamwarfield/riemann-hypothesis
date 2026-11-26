module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDeepestFiltrationStepEqRational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses.BaseChangeSign

section Gen
variable {L : Type} [Field L] (τ : L →+* L) {n : ℕ}

theorem hform_eq_mat (J : Matrix (Fin n) (Fin n) L) {ι : Type} [Fintype ι] (f : ι → Fin n → L) (i j : ι) :
    hform τ J (f i) (f j) = (cT τ (Matrix.of fun r i => f i r) * J * Matrix.of fun r i => f i r) i j := by
  simp only [hform, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_det_change (J : Matrix (Fin n) (Fin n) L) (V : Submodule L (Fin n → L)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c b : Module.Basis ι L V) :
    (Matrix.of fun i j => hform τ J (b i).1 (b j).1).det =
      τ (c.toMatrix b).det * (Matrix.of fun i j => hform τ J (c i).1 (c j).1).det * (c.toMatrix b).det := by
  have hM : (Matrix.of fun r i => ((b i : V) : Fin n → L) r) =
      (Matrix.of fun r i => ((c i : V) : Fin n → L) r) * c.toMatrix b := by
    ext r j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    have h := c.sum_toMatrix_smul_self b j
    calc ((b j : V) : Fin n → L) r = ((∑ i, c.toMatrix b i j • c i : V) : Fin n → L) r := by rw [h]
      _ = _ := by
        simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e1 : (Matrix.of fun i j => hform τ J (b i).1 (b j).1) =
      cT τ (Matrix.of fun r i => ((b i : V) : Fin n → L) r) * J * Matrix.of fun r i => ((b i : V) : Fin n → L) r := by
    ext i j; exact hform_eq_mat τ J (fun i => ((b i : V) : Fin n → L)) i j
  have e2 : (Matrix.of fun i j => hform τ J (c i).1 (c j).1) =
      cT τ (Matrix.of fun r i => ((c i : V) : Fin n → L) r) * J * Matrix.of fun r i => ((c i : V) : Fin n → L) r := by
    ext i j; exact hform_eq_mat τ J (fun i => ((c i : V) : Fin n → L)) i j
  have hdet : ∀ P : Matrix ι ι L, (cT τ P).det = τ P.det := by
    intro P; unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl
  rw [e1, e2, hM, cT_mul]
  set Mc := Matrix.of fun r i => ((c i : V) : Fin n → L) r
  set P := c.toMatrix b
  have : cT τ P * cT τ Mc * J * (Mc * P) = cT τ P * (cT τ Mc * J * Mc) * P := by
    simp only [Matrix.mul_assoc]
  rw [this, Matrix.det_mul, Matrix.det_mul, hdet]

theorem toMatrix_det_ne {V : Submodule L (Fin n → L)} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c b : Module.Basis ι L V) : (c.toMatrix b).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (c.toMatrix_mul_toMatrix_flip b)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end Gen

section BC
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ}

theorem mem_ker_map {A : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hx : x ∈ LinearMap.ker (Matrix.toLin' A)) :
    (φ ∘ x) ∈ LinearMap.ker (Matrix.toLin' (A.map φ)) := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
  funext i
  rw [← RingHom.map_mulVec, hx]; simp

theorem finrank_ker_map (A : Matrix (Fin n) (Fin n) K) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (A.map φ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (A.map φ))
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  have h3 : (A.map φ).rank = A.rank := GlobalTheory.Core.Rk.rank_map_field φ A
  change (A.map φ).rank + _ = _ at h1
  change A.rank + _ = _ at h2
  simp only [Module.finrank_fin_fun] at h1 h2
  omega

end BC

section Val
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dite_eq_right hx', dite_eq_right hy', dite_eq_right hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]
  rw [this, toAdd_mul]; ring

theorem sign_conj_mul {τ : L →+* L} (hv : ∀ x, Valued.v (τ x) = Valued.v x) {t : L} (ht : t ≠ 0) (a : L) :
    (-1 : ℂ) ^ ordL (τ t * a * t) = (-1) ^ ordL a := by
  by_cases ha : a = 0
  · simp [ha]
  have hτ : τ t ≠ 0 := (map_ne_zero τ).2 ht
  have ho : ordL (τ t) = ordL t := by
    unfold ordL; simp only [hv]
  rw [ordL_mul (mul_ne_zero hτ ha) ht, ordL_mul hτ ha, ho,
    show ordL t + ordL a + ordL t = ordL a + 2 * ordL t by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
  norm_num

end Val

section Main
variable {K L : Type} [Field K] [Field L] (σ : K →+* K) (τ : L →+* L) (φ : K →+* L) {n : ℕ}

theorem gram_det_map (hφ : ∀ x, τ (φ x) = φ (σ x)) (H A : Matrix (Fin n) (Fin n) K) :
    ∃ t : L, t ≠ 0 ∧ (gramOn τ (H.map φ) (LinearMap.ker (Matrix.toLin' (A.map φ)))).det =
      τ t * φ (gramOn σ H (LinearMap.ker (Matrix.toLin' A))).det * t := by
  letI := φ.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 φ.injective
  set V := LinearMap.ker (Matrix.toLin' A) with hV
  set V' := LinearMap.ker (Matrix.toLin' (A.map φ)) with hV'
  have hk : Module.finrank L V' = Module.finrank K V := finrank_ker_map φ A
  rcases isEmpty_or_nonempty (Fin (Module.finrank L V')) with he | hne
  · haveI : IsEmpty (Fin (Module.finrank K V)) := hk ▸ he
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Matrix.det_isEmpty, Matrix.det_isEmpty]; simp
  let b := Module.finBasis K V
  let v : Fin (Module.finrank L V') → V' := fun i =>
    ⟨φ ∘ ((b (Fin.cast hk i) : V) : Fin n → K), mem_ker_map φ (b (Fin.cast hk i)).2⟩
  have hli : LinearIndependent L v := by
    apply LinearIndependent.of_comp V'.subtype
    have h0 : LinearIndependent K (fun i => ((b (Fin.cast hk i) : V) : Fin n → K)) :=
      (b.linearIndependent.map' V.subtype V.ker_subtype).comp _ (Fin.cast_injective hk)
    exact linearIndependent_algebraMap_comp_iff.2 h0
  let c := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _)
  have hc : ∀ i, c i = v i := fun i => by simp [c]
  refine ⟨(c.toMatrix (Module.finBasis L V')).det, toMatrix_det_ne c _, ?_⟩
  have e1 : gramOn τ (H.map φ) V' =
      Matrix.of fun i j => hform τ (H.map φ) (Module.finBasis L V' i).1 (Module.finBasis L V' j).1 := rfl
  rw [e1, gram_det_change τ (H.map φ) V' c (Module.finBasis L V')]
  have e2 : (Matrix.of fun i j => hform τ (H.map φ) (c i).1 (c j).1) =
      ((gramOn σ H V).map φ).submatrix (finCongr hk) (finCongr hk) := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.of_apply, hc, v, Matrix.submatrix_apply, Matrix.map_apply, gramOn, hform, map_sum, map_mul,
      Function.comp_apply, hφ, finCongr_apply]
    rfl
  rw [e2, Matrix.det_submatrix_equiv_self,
    show ((gramOn σ H V).map φ).det = φ (gramOn σ H V).det from (RingHom.map_det φ _).symm]

end Main

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E),
    (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E)))
      (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det =
    (-1) ^ ordL (algebraMap E (w.adicCompletion E)
      (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := by
  intro E _ _ _ hU w hw n H A
  have hc := GlobalTheory.ConjAtPlace.main E hU w
  have hφ : ∀ x : E, cj w (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom x) :=
    fun x => (hc.2.2.2.1 hw).1 x
  obtain ⟨t, ht, hdet⟩ := gram_det_map (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w)
    (algebraMap E (w.adicCompletion E)) hφ H A
  rw [hdet, sign_conj_mul hc.2.2.1 ht]

end GlobalTheory.UnitaryClasses.BaseChangeSign
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E), (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E))) (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := by
  first | exact @GlobalTheory.UnitaryClasses.BaseChangeSign.main | exact GlobalTheory.UnitaryClasses.BaseChangeSign.main | (intros; apply GlobalTheory.UnitaryClasses.BaseChangeSign.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TotPosSign

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embReal_algebraMap {w : InfinitePlace F} (hw : w.IsReal) (t : F) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (algebraMap F w.Completion t) =
      InfinitePlace.embedding_of_isReal hw t := by
  have := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv w.1).symm t)
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]
  rw [← WithAbs.equiv_symm_apply]
  simpa only [RingEquiv.apply_symm_apply] using this

theorem eta_inf_eq_one [Algebra.IsQuadraticExtension F E] {w : InfinitePlace F} (hw : w.IsReal) (t : Fˣ)
    (ht : 0 < InfinitePlace.embedding_of_isReal hw (t : F)) :
    GlobalTheory.QuadSymbol.eta F E w.Completion (GlobalTheory.QuadSymbol.infDiag F t w) = 1 := by
  rw [GlobalTheory.QuadSymbol.eta_eq_one_iff, GlobalTheory.QuadSymbol.mem_normGroup_iff]
  set g := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set a : w.Completion := algebraMap F w.Completion (t : F)
  have hga : g a = InfinitePlace.embedding_of_isReal hw (t : F) := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, embReal_algebraMap]
  refine ⟨algebraMap w.Completion (w.Completion ⊗[F] E) (g.symm (Real.sqrt (g a))), ?_⟩
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two F E,
    ← map_pow, Real.sq_sqrt (hga ▸ ht.le), RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.TotPosSign

namespace GlobalTheory.TotPosSign

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {x : L} {y : L'} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  change (fun z : WithZero (Multiplicative ℤ) =>
      if h : z = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v x) =
    (fun z : WithZero (Multiplicative ℤ) =>
      if h : z = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v y)
  rw [h]

theorem valued_eq_exp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (hx : x ≠ 0) :
    Valued.v x = WithZero.exp (-ordL x) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dite_eq_right h0, neg_neg]
  conv_lhs => rw [← WithZero.coe_unzero h0]
  rfl

theorem eta_inert [Algebra.IsQuadraticExtension F E] {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v) (x : (v.adicCompletion F)ˣ) :
    GlobalTheory.QuadSymbol.eta F E (v.adicCompletion F) x = (-1) ^ ordL (x : v.adicCompletion F) := by
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let χ : (v.adicCompletion F)ˣ →* ℤˣ :=
    MonoidHom.mk' (GlobalTheory.QuadSymbol.eta F E (v.adicCompletion F)) ((GlobalTheory.QuadSymbol.localCharacters F E).1 v)
  set π := atFin v (unif v)
  set k := ordL (x : v.adicCompletion F)
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := unif_spec v
  set u := x * π ^ (-k)
  have hu1 : IsUnitAt v u := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπ, valued_eq_exp x.ne_zero,
      ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [k]
  have hx : x = u * π ^ k := by simp [u]
  have e1 : χ u = 1 := GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hu1)
  have e2 : χ π = -1 := GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.2
    (GlobalTheory.LFun.not_mem_normGroup_of_inert h2 hv hu (unif_spec v))
  change χ x = _
  rw [hx, map_mul, map_zpow, e1, e2, one_mul]

end Loc

end GlobalTheory.TotPosSign

namespace GlobalTheory.TotPosSign

section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isSplit_under {w : Pl E} (h : IsSplitAt w) : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 ↥(maximalRealSubfield E))) := by
  obtain ⟨u, hne, hu⟩ := h
  exact GlobalTheory.LFun.isSplit_iff.2 ⟨u, w, hne, hu, rfl⟩

theorem not_isSplit_under {w : Pl E} (h : ¬ IsSplitAt w) : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 ↥(maximalRealSubfield E))) := by
  rintro hs
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
  by_cases haw : a = w
  · subst haw
    exact h ⟨b, hab.symm, hb⟩
  · exact h ⟨a, haw, ha⟩

theorem isUnram_of_unr (hU : Unr E) (v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E))) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v :=
  GlobalTheory.LFun.isUnram_iff.2 fun P _ => by
    haveI := hU P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

theorem neg_one_zpow_cast (k : ℤ) : ((((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ k := by
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, hk.neg_one_zpow]; simp
  · rw [hk.neg_one_zpow, hk.neg_one_zpow]; simp

theorem term_eq (hU : Unr E) (w : Pl E) (t : Units ↥(maximalRealSubfield E)) :
    (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) (algebraMap ↥(maximalRealSubfield E) E t))) =
      ((GlobalTheory.QuadSymbol.eta ↥(maximalRealSubfield E) E ((w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E))
        (GlobalTheory.QuadSymbol.finDiag ↥(maximalRealSubfield E) t (w.under (𝓞 ↥(maximalRealSubfield E)))) : ℤ) : ℂ) := by
  have h2 : Module.finrank ↥(maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ↥(maximalRealSubfield E) E
  split_ifs with hs
  · rw [GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (GlobalTheory.LFun.mem_normGroup_of_isSplit h2 (isSplit_under hs) _)]
    simp
  · rw [eta_inert (not_isSplit_under hs) (isUnram_of_unr hU _), neg_one_zpow_cast]
    congr 1
    refine ordL_congr ?_
    have hx : ((GlobalTheory.QuadSymbol.finDiag ↥(maximalRealSubfield E) t (w.under (𝓞 ↥(maximalRealSubfield E))) : (w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E))) =
        algebraMap ↥(maximalRealSubfield E) _ (t : ↥(maximalRealSubfield E)) := rfl
    have e := GlobalTheory.LFun.valued_complMap (F := ↥(maximalRealSubfield E)) (E := E) (w := w) rfl
      (a := algebraMap ↥(maximalRealSubfield E) ((w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E)) (t : ↥(maximalRealSubfield E))) (by simp)
    rw [GlobalTheory.LFun.isUnram_iff.1 (isUnram_of_unr hU _) w rfl, pow_one, GlobalTheory.LFun.complMap_algebraMap] at e
    rw [hx, e]

theorem bijOn_under {S : Set (Pl E)} (hS : IsSection S) :
    Set.BijOn (fun w : Pl E => w.under (𝓞 ↥(maximalRealSubfield E))) S Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, fun a ha b hb hab => ?_, fun v _ => ?_⟩
  · obtain ⟨u, -, hu⟩ := hS a
    exact (hu a ⟨ha, rfl⟩).trans (hu b ⟨hb, hab.symm⟩).symm
  · obtain ⟨w, hw⟩ := (GlobalTheory.QNorm.places_over ↥(maximalRealSubfield E) E).2.1 v
    obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
    exact ⟨u, hu, hu'.trans hw⟩

end CM

end GlobalTheory.TotPosSign

namespace GlobalTheory.UnitaryClasses


open GlobalTheory.TotPosSign in
theorem signProd_totPos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S →
    ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) →
    ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := by
  intro E _ _ _ hU S hS d hd hpos
  have hmem : d ∈ maximalRealSubfield E := (mem_maximalRealSubfield_iff d).2 fun φ => by
    obtain ⟨r, -, hr⟩ := hpos φ
    rw [hr, Complex.star_def, Complex.conj_ofReal]
  set t0 : ↥(maximalRealSubfield E) := ⟨d, hmem⟩
  have ht0 : algebraMap (↥(maximalRealSubfield E)) E t0 = d := rfl
  have ht0' : t0 ≠ 0 := fun h => hd (by rw [← ht0, h, map_zero])
  set t := Units.mk0 t0 ht0'
  have PF := GlobalTheory.QuadSymbol.productFormula (↥(maximalRealSubfield E)) E t
  have hinf : ∀ w : InfinitePlace ↥(maximalRealSubfield E),
      GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E w.Completion (GlobalTheory.QuadSymbol.infDiag _ t w) = 1 := by
    intro w
    have hw : w.IsReal := IsTotallyReal.isReal w
    refine eta_inf_eq_one hw t ?_
    letI : Algebra (↥(maximalRealSubfield E)) ℂ := w.embedding.toAlgebra
    let τ : E →ₐ[↥(maximalRealSubfield E)] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    obtain ⟨r, hr, e⟩ := hpos τ.toRingHom
    have e2 : (InfinitePlace.embedding_of_isReal hw (t : ↥(maximalRealSubfield E)) : ℂ) = r := by
      rw [InfinitePlace.embedding_of_isReal_apply, ← e]
      exact (τ.commutes t0).symm
    rw [Complex.ofReal_inj] at e2
    rw [e2]; exact hr
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E)),
      GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E (v.adicCompletion (↥(maximalRealSubfield E)))
        (GlobalTheory.QuadSymbol.finDiag (↥(maximalRealSubfield E)) t v) = 1 := by
    have h := PF.2
    unfold GlobalTheory.QuadSymbol.etaProd at h
    rwa [Finset.prod_eq_one fun w _ => hinf w, mul_one] at h
  let cz : ℤˣ →* ℂ := (Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)
  have hd' : d = algebraMap (↥(maximalRealSubfield E)) E ((t : Units ↥(maximalRealSubfield E)) : ↥(maximalRealSubfield E)) := rfl
  rw [hd', finprod_mem_eq_of_bijOn _ (bijOn_under hS) (g := fun v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E)) => cz
      (GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E (v.adicCompletion (↥(maximalRealSubfield E)))
        (GlobalTheory.QuadSymbol.finDiag (↥(maximalRealSubfield E)) t v))) fun w _ => term_eq hU w t,
    finprod_mem_univ, ← MonoidHom.map_finprod _ (GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport PF.1), hfin, map_one]

end GlobalTheory.UnitaryClasses

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOneStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finprod_nonsplit_sign_totallyPositive_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := by
  first | exact @GlobalTheory.UnitaryClasses.signProd_totPos | exact GlobalTheory.UnitaryClasses.signProd_totPos | (intros; apply GlobalTheory.UnitaryClasses.signProd_totPos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzDeterminedBySchrodingerThetaValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzDeterminedBySchrodingerThetaValues
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Classical

namespace GlobalTheory.SchrodingerUniq

section Abstract

variable {G Y : Type} [AddCommGroup G] [AddCommGroup Y] (χ : Y → G → ℂ)

theorem chi_nsmul (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ) (hzero : ∀ ξ, χ 0 ξ = 1) (y : Y) (ξ : G) :
    ∀ m : ℕ, χ (m • y) ξ = χ y ξ ^ m
  | 0 => by rw [zero_nsmul, hzero, pow_zero]
  | m + 1 => by rw [succ_nsmul, hadd, chi_nsmul hadd hzero y ξ m, pow_succ]

theorem norm_avg_le_one (f : ℕ → ℂ) (hf : ∀ m, ‖f m‖ = 1) {M : ℕ} (hM : 0 < M) :
    ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, f m‖ ≤ 1 := by
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  calc (M : ℝ)⁻¹ * ‖∑ m ∈ Finset.range M, f m‖ ≤ (M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, ‖f m‖ := by
        gcongr; exact norm_sum_le _ _
    _ = 1 := by simp only [hf, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]; field_simp

theorem norm_avg_pow_le {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {M : ℕ} (hM : 0 < M) :
    ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, z ^ m‖ ≤ 2 / (M * ‖z - 1‖) := by
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : ‖z ^ M - 1‖ ≤ 2 := by
    calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num
  rw [geom_sum_eq hz1, norm_mul, norm_div, norm_inv, Complex.norm_natCast]
  calc (M : ℝ)⁻¹ * (‖z ^ M - 1‖ / ‖z - 1‖) ≤ (M : ℝ)⁻¹ * (2 / ‖z - 1‖) := by gcongr
    _ = 2 / (M * ‖z - 1‖) := by field_simp

variable (c : G → ℂ)

def Good (a : G → ℂ) : Prop := (∀ ξ, ‖a ξ‖ ≤ 1) ∧ a 0 = 1 ∧ ∀ y, ∑' ξ, c ξ * χ y ξ * a ξ = 0

variable {χ c}

theorem good_avg (hnorm : ∀ y ξ, ‖χ y ξ‖ = 1) (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ)
    (h0 : ∀ y, χ y 0 = 1) (hc : Summable fun ξ => ‖c ξ‖) {a : G → ℂ} (ha : Good χ c a) (y' : Y) {M : ℕ}
    (hM : 0 < M) : Good χ c (fun ξ => a ξ * ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') ξ)) := by
  refine ⟨fun ξ => ?_, ?_, fun y => ?_⟩
  · rw [norm_mul]
    calc ‖a ξ‖ * ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') ξ‖ ≤ 1 * 1 :=
          mul_le_mul (ha.1 ξ) (norm_avg_le_one _ (fun m => hnorm _ _) hM) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · simp only [ha.2.1, h0, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast hM.ne')
  · have hs : ∀ m ∈ Finset.range M, Summable fun ξ => c ξ * χ y ξ * a ξ * χ (m • y') ξ := fun m _ =>
      Summable.of_norm_bounded hc fun ξ => by
        rw [norm_mul, norm_mul, norm_mul, hnorm, hnorm, mul_one, mul_one]
        exact mul_le_of_le_one_right (norm_nonneg _) (ha.1 ξ)
    calc ∑' ξ, c ξ * χ y ξ * (a ξ * ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') ξ))
        = ∑' ξ, (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, c ξ * χ y ξ * a ξ * χ (m • y') ξ := by
          congr 1; funext ξ
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
      _ = (M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, ∑' ξ, c ξ * χ y ξ * a ξ * χ (m • y') ξ := by
          rw [tsum_mul_left, Summable.tsum_finsetSum hs]
      _ = 0 := by
          rw [Finset.sum_eq_zero fun m _ => ?_, mul_zero]
          rw [← ha.2.2 (y + m • y')]
          congr 1; funext ξ; rw [hadd]; ring

theorem exists_good_small (hnorm : ∀ y ξ, ‖χ y ξ‖ = 1) (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ)
    (hzero : ∀ ξ, χ 0 ξ = 1) (h0 : ∀ y, χ y 0 = 1) (hsep : ∀ ξ, ξ ≠ 0 → ∃ y, χ y ξ ≠ 1)
    (hc : Summable fun ξ => ‖c ξ‖) (h1 : Good χ c fun _ => 1) :
    ∀ (T : Finset G), (0 : G) ∉ T → ∀ ε > 0, ∃ a, Good χ c a ∧ ∀ ξ ∈ T, ‖a ξ‖ ≤ ε := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _ ε _; exact ⟨fun _ => 1, h1, by simp⟩
  | insert ξ T hξT ih =>
    intro h0T ε hε
    have hξ0 : ξ ≠ 0 := fun e => h0T (by rw [← e]; exact Finset.mem_insert_self ξ T)
    obtain ⟨a, ha, haT⟩ := ih (fun e => h0T (Finset.mem_insert_of_mem e)) ε hε
    obtain ⟨y', hy'⟩ := hsep ξ hξ0
    have hd : 0 < ‖χ y' ξ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hy')
    obtain ⟨M, hM⟩ := exists_nat_gt (2 / (ε * ‖χ y' ξ - 1‖))
    have hM0 : 0 < M := by
      have : (0 : ℝ) < M := lt_trans (by positivity) hM
      exact_mod_cast this
    refine ⟨_, good_avg hnorm hadd h0 hc ha y' hM0, fun η hη => ?_⟩
    rw [norm_mul]
    rcases Finset.mem_insert.1 hη with rfl | hη
    · simp_rw [chi_nsmul χ hadd hzero]
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
      calc ‖a η‖ * ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ y' η ^ m‖ ≤ 1 * (2 / (M * ‖χ y' η - 1‖)) :=
            mul_le_mul (ha.1 _) (norm_avg_pow_le (hnorm _ _) hy' hM0) (norm_nonneg _) zero_le_one
        _ ≤ ε := by
            rw [one_mul, div_le_iff₀ (by positivity)]
            rw [div_lt_iff₀ (by positivity)] at hM
            have : ε * (M * ‖χ y' η - 1‖) = M * (ε * ‖χ y' η - 1‖) := by ring
            linarith
    · calc ‖a η‖ * ‖(M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, χ (m • y') η‖ ≤ ε * 1 :=
            mul_le_mul (haT η hη) (norm_avg_le_one _ (fun m => hnorm _ _) hM0) (norm_nonneg _) hε.le
        _ = ε := mul_one ε

theorem coeff_zero_eq_zero (hnorm : ∀ y ξ, ‖χ y ξ‖ = 1) (hadd : ∀ y y' ξ, χ (y + y') ξ = χ y ξ * χ y' ξ)
    (hzero : ∀ ξ, χ 0 ξ = 1) (h0 : ∀ y, χ y 0 = 1) (hsep : ∀ ξ, ξ ≠ 0 → ∃ y, χ y ξ ≠ 1)
    (hc : Summable fun ξ => ‖c ξ‖) (h : ∀ y, ∑' ξ, c ξ * χ y ξ = 0) : c 0 = 0 := by
  have h1 : Good χ c fun _ => 1 := ⟨fun _ => by simp, rfl, fun y => by simpa using h y⟩
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
  set S := ∑' ξ, ‖c ξ‖
  have hS : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.1
    ((tendsto_tsum_compl_atTop_zero fun ξ => ‖c ξ‖).eventually (gt_mem_nhds (half_pos hδ)))
  set s := insert (0 : G) s₀
  have htail := hs₀ s (Finset.subset_insert _ _)
  have hε : 0 < δ / (2 * (S + 1)) := by positivity
  obtain ⟨a, ha, haT⟩ := exists_good_small hnorm hadd hzero h0 hsep hc h1 (s.erase 0)
    (Finset.notMem_erase 0 s) _ hε
  have hsumm : Summable fun ξ => c ξ * a ξ := Summable.of_norm_bounded hc fun ξ => by
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (ha.1 ξ)
  have hsum : ∑' ξ, c ξ * a ξ = 0 := by simpa [hzero] using ha.2.2 0
  have hsplit := hsumm.sum_add_tsum_compl (s := s)
  rw [hsum, ← Finset.add_sum_erase s _ (Finset.mem_insert_self 0 s₀), ha.2.1, mul_one] at hsplit
  have hc0 : c 0 = -(∑ x ∈ s.erase 0, c x * a x + ∑' x : ↑((s : Set G)ᶜ), c x * a x) := by
    linear_combination hsplit
  have hA : ‖∑ x ∈ s.erase 0, c x * a x‖ ≤ δ / (2 * (S + 1)) * S := by
    calc ‖∑ x ∈ s.erase 0, c x * a x‖ ≤ ∑ x ∈ s.erase 0, ‖c x * a x‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ s.erase 0, δ / (2 * (S + 1)) * ‖c x‖ := Finset.sum_le_sum fun x hx => by
          rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (haT x hx) (norm_nonneg _)
      _ = δ / (2 * (S + 1)) * ∑ x ∈ s.erase 0, ‖c x‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ δ / (2 * (S + 1)) * S := by
          gcongr; exact hc.sum_le_tsum _ fun _ _ => norm_nonneg _
  have hB : ‖∑' x : ↑((s : Set G)ᶜ), c x * a x‖ ≤ ∑' x : {x // x ∉ s}, ‖c x‖ := by
    calc ‖∑' x : ↑((s : Set G)ᶜ), c x * a x‖ ≤ ∑' x : ↑((s : Set G)ᶜ), ‖c x * a x‖ :=
          norm_tsum_le_tsum_norm ((hsumm.subtype _).norm)
      _ ≤ ∑' x : ↑((s : Set G)ᶜ), ‖c x‖ := Summable.tsum_le_tsum
          (fun x => by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (ha.1 x))
          (hsumm.subtype _).norm (hc.subtype _)
      _ = ∑' x : {x // x ∉ s}, ‖c x‖ := rfl
  have hSS : δ / (2 * (S + 1)) * S ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  rw [hc0, norm_neg, zero_add]
  calc _ ≤ ‖∑ x ∈ s.erase 0, c x * a x‖ + ‖∑' x : ↑((s : Set G)ᶜ), c x * a x‖ := norm_add_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add (hA.trans hSS) (hB.trans htail.le)
    _ = δ := add_halves δ

end Abstract

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w : (κ → AF D.host.F) × (κ → AF D.host.F), GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ) =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ')) → φ = φ' := by
  intro D ψ hψ κ _ φ hφ φ' hφ' h
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  obtain ⟨a₀, ha₀⟩ := hψ.1.2.2.2
  let ι : (κ → D.host.F) → (κ → AF D.host.F) := fun ξ i => algebraMap D.host.F (AF D.host.F) (ξ i)
  have hι0 : ι 0 = 0 := by funext i; simp [ι]
  funext x
  rw [← sub_eq_zero]
  have hΦ : (fun z => (φ - φ') (z + x)) ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    GlobalTheory.SchwartzTranslate.schA_translate D.host.F x (sub_mem hφ hφ')
  have hc : Summable fun ξ => ‖(φ - φ') (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F hΦ using 1
  have sφ : Summable fun ξ => ‖φ (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F x hφ) using 1
  have sφ' : Summable fun ξ => ‖φ' (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F x hφ') using 1
  have key := coeff_zero_eq_zero (χ := fun (y : κ → AF D.host.F) (ξ : κ → D.host.F) => ψ (ι ξ ⬝ᵥ y))
    (c := fun ξ => (φ - φ') (ι ξ + x)) (fun y ξ => hn _)
    (fun y y' ξ => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
    (fun ξ => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
    (fun y => by simp only [hι0, zero_dotProduct, AddChar.map_zero_eq_one])
    (fun ξ hξ => by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have hi' : ξ i ≠ 0 := hi
      refine ⟨Pi.single i (algebraMap D.host.F (AF D.host.F) (ξ i)⁻¹ * a₀), ?_⟩
      show ψ (ι ξ ⬝ᵥ Pi.single i (algebraMap D.host.F (AF D.host.F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [dotProduct_single]
      show ψ (algebraMap D.host.F (AF D.host.F) (ξ i) * (algebraMap D.host.F (AF D.host.F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
      exact ha₀)
    hc (fun y => ?_)
  · simpa [hι0] using key
  · have h' := h (x, y)
    simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, AddChar.map_add_eq_mul] at h'
    set b := ψ (⅟(2 : AF D.host.F) * (x ⬝ᵥ y))
    have hb : b ≠ 0 := by
      intro e
      have h1 : ‖b‖ = 1 := hn _
      rw [e, norm_zero] at h1
      exact zero_ne_one h1
    have s1 : Summable fun ξ : κ → D.host.F => ψ (ι ξ ⬝ᵥ y) * b * φ (ι ξ + x) :=
      Summable.of_norm_bounded sφ fun ξ => by rw [norm_mul, norm_mul, hn, hn, one_mul, one_mul]
    have s2 : Summable fun ξ : κ → D.host.F => ψ (ι ξ ⬝ᵥ y) * b * φ' (ι ξ + x) :=
      Summable.of_norm_bounded sφ' fun ξ => by rw [norm_mul, norm_mul, hn, hn, one_mul, one_mul]
    have e : ∑' ξ : κ → D.host.F, (ψ (ι ξ ⬝ᵥ y) * b * φ (ι ξ + x) - ψ (ι ξ ⬝ᵥ y) * b * φ' (ι ξ + x)) = 0 := by
      rw [s1.tsum_sub s2, sub_eq_zero]; exact h'
    have e2 : ∑' ξ : κ → D.host.F, (φ - φ') (ι ξ + x) * ψ (ι ξ ⬝ᵥ y) =
        b⁻¹ * ∑' ξ : κ → D.host.F, (ψ (ι ξ ⬝ᵥ y) * b * φ (ι ξ + x) - ψ (ι ξ ⬝ᵥ y) * b * φ' (ι ξ + x)) := by
      rw [← tsum_mul_left]; congr 1; funext ξ; simp only [Pi.sub_apply]; field_simp
    rw [e2, e, mul_zero]

end GlobalTheory.SchrodingerUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzDeterminedBySchrodingerThetaValuesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_determined_by_schrodingerThetaValues : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w : (κ → AF D.host.F) × (κ → AF D.host.F), GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ) =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w φ')) → φ = φ' := by
  first | exact @GlobalTheory.SchrodingerUniq.main | exact GlobalTheory.SchrodingerUniq.main | (intros; apply GlobalTheory.SchrodingerUniq.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorLatticeLocal
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

open IsDedekindDomain

namespace GlobalTheory.InertIwasawaUnram

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ hσ hU n J hJ x y hx hy L hL v hv hSD g
  haveI := hL
  obtain ⟨c, hc⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hσ inferInstance
  have hram : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.ramificationIdx (𝓞 F) = 1 := fun P => by
    haveI := P.isPrime
    haveI : Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := inferInstance
    exact Ideal.ramificationIdx_eq_one _ _
  have hUn : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v := fun P _ => hram P
  have hIU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := fun P _ => hram P
  obtain ⟨w, hw⟩ := ((GlobalTheory.LFun.exists_isInertChart σ hσ v).1 hIU).resolve_left hv
  obtain ⟨q, k, hk, hg, β, hβ⟩ := GlobalTheory.InertIwasawaLoc.exists_loc hσ hc hJ hw hUn hSD
    (e := x) (p := cT (σ : E →+* E) y * J) (by rw [Matrix.mul_assoc] at hy ⊢; exact hy) hx g
  exact ⟨q, k, hk, hg, β, hβ⟩

end GlobalTheory.InertIwasawaUnram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridCharactersUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridCharactersUnramified
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GridUnr

theorem chi_eta_unramAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ i : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) ∧ GlobalTheory.WeilParts.UnramAt e Lc.eta := by
  intro D T Lc sc G μ₀ hμ t v e he hv i
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  refine ⟨GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (G.ch.chi_eq _ h1 h2) v e he fun P hP => ?_,
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hμ.eta v e he fun P _ => Lc.C.isEta.unr P⟩
  exact G.ch.unr _ h1 h2 P (by rw [hP]; exact hv)

end GlobalTheory.GridUnr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridCharactersUnramifiedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grid_characters_unramified : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ i : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) ∧ GlobalTheory.WeilParts.UnramAt e Lc.eta := by
  first | exact @GlobalTheory.GridUnr.chi_eta_unramAt | exact GlobalTheory.GridUnr.chi_eta_unramAt | (intros; apply GlobalTheory.GridUnr.chi_eta_unramAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEntriesBoundedAlmostEverywhere
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEntriesBoundedAlmostEverywhere
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.FixedBound

theorem exists_entry_absFin_bound {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (Y : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) : ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Y p.1 p.2))) ≤ K v := by
  refine ⟨fun v => max 1 (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Y p.1 p.2))),
    ?_, fun v => le_max_left _ _, fun v => le_max_right _ _⟩
  have h := Filter.eventually_all.2 fun p : Fin n × Fin d => GlobalTheory.AdelicU.eventually_absFin_le_one F (Y p.1 p.2)
  refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
  exact max_eq_left (Finset.sup_le fun p _ => hv' p)

end GlobalTheory.FixedBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEntriesBoundedAlmostEverywhereStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_entries_bounded_almost_everywhere : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (Y : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)), ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ v, (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (Y p.1 p.2))) ≤ K v := by
  first | exact @GlobalTheory.FixedBound.exists_entry_absFin_bound | exact GlobalTheory.FixedBound.exists_entry_absFin_bound | (intros; apply GlobalTheory.FixedBound.exists_entry_absFin_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGrowthOfFinite
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

theorem GlobalTheory.AutGrowth.tame_of_autForm (hP : GlobalTheory.Published.AutomorphicFormsFiniteGL) (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hφ : IsAutForm φ) : φ ∈ tame E a := by
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing E a ν
  obtain ⟨V, hVf, hVt, hV⟩ := GlobalTheory.T.exists_finiteDimensional_space_automorphic_smoothings hP E a ν φ hφ
  let V' : Submodule ℂ (GA E a → ℂ) := V.map (Sm E a).subtype
  have hc : IsClosed (V' : Set (GA E a → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hmem : ∀ n, smoothing ν (α n) φ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := hV (α n) (hα n).1 (hα n).2
    exact ⟨_, hv, rfl⟩
  have hφ' : φ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim φ.1 φ.2 g) (Eventually.of_forall hmem)
  obtain ⟨ψ, hψ, e⟩ := hφ'
  have e' : ψ = φ := Subtype.ext e
  exact hVt (e' ▸ hψ)

theorem GlobalTheory.AutGrowth.lie_growth_of_finite : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ →
    ∀ g : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖(GlobalTheory.CuspRep.lie E a X φ).1 (g * GlobalTheory.CuspRep.infGL E a y)‖ ≤
      C * GlobalTheory.CuspRep.height y ^ N := by
  intro hP E _ _ _ a X φ hφ
  exact growth_of_tame (lie_mem_tame X (GlobalTheory.AutGrowth.tame_of_autForm hP E a φ hφ))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOfSkewHermitianTwist
noncomputable section

namespace GlobalTheory.ThK.SqIntMaxCpt

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped Matrix TensorProduct

theorem exists_congr_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) : ∃ Q : GL (Fin n) ℂ, Q.1ᴴ * P * Q.1 = 1 := by
  have hd : P.det ≠ 0 := fun h => by
    obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [e] using hpos x hx
  obtain ⟨ε, Q, hQ⟩ := Frames.exists_congr_diagonal_sign hP hd
  refine ⟨Q, hQ.trans ?_⟩
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  have hx : Q.1 *ᵥ (Pi.single i 1 : Fin n → ℂ) ≠ 0 := fun h => by
    have := congrArg ((Q⁻¹).1 *ᵥ ·) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    simpa using congrFun this i
  have := hpos _ hx
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ] at this
  cases h : ε i
  · simp [h, Matrix.mulVec_single_one, dotProduct, Pi.single_apply, Matrix.diagonal_apply] at this
    linarith
  · simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.ThK.SqIntMaxCpt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLiftPreservingAppellHumbertForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLiftPreservingAppellHumbertForm
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LieGramLift

theorem exists_lift : ∀ (Q P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (u' : HolUnif P.A P.L g) (Hm' : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (f : Q.A ⟶ P.A), IsMonHom f → LBIso (lbPow (P.L.pull f.left) 1) (lbPow Q.L 1) → ∀ (n : ℕ) (v' : Fin n → (epsR ℂ ⟶ Q.A)) (Wc : Fin n → Fin Q.g → ℂ), (∀ i, IsTangent (v' i) ∧ u.IsDiff (Wc i) (v' i)) → ∀ (m : ℕ) (a : Fin m → Fin n → ℂ) (tv : Fin m → (epsR ℂ ⟶ P.A)) (Xv : Fin m → Fin g → ℂ), (∀ i, u'.IsDiff (Xv i) (tv i)) → (∀ i (q : epsR ℂ ⟶ Q.A), IsLieComb (a i) v' q → q ≫ f = tv i) → ∃ L : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x x', hermForm Hm' (L x) (L x') = hermForm Hm x x') ∧ ∀ i, L (∑ k, a i k • Wc k) = Xv i := by
  intro Q P g u Hm χ u' Hm' χ' hu hu' f hf hL n v' Wc hv m a tv Xv htv hq
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all P g u' Hm' χ' hu'
  obtain ⟨F, hF, -, hFd, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A P.A Q.isAb P.isAb Q.L P.L Q.g g u u'
    h1 h2 f hf
  refine ⟨F, fun x x' => ?_, fun i => ?_⟩
  · have := GlobalTheory.hermForm_pull_eq_of_lbIso_pow Q.A P.A Q.L P.L Q.isLB P.isLB Q.g g u u' Hm χ Hm' χ' hu hu' f F hF 1 1 hL x x'
    simpa using this
  · have hc : IsLieComb (a i) v' (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (a i) v') :=
      (ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff (a i) v' _).2 rfl
    have hd := GlobalTheory.UnifDifferential.isDiff_of_isLieComb Q.A Q.L Q.g n u Wc v' (a i) _
      (fun k => (hv k).1) (fun k => (hv k).2) hc
    have ht := GlobalTheory.HermHom.isTangent_of_isLieComb u (fun k => (hv k).1) (fun k => (hv k).2) hc
    obtain ⟨ht', hd'⟩ := hFd _ _ ht hd
    rw [hq i _ hc] at ht' hd'
    obtain ⟨w, -, hw⟩ := h1 (tv i) ht'
    exact (hw _ hd').trans (hw _ (htv i)).symm

end GlobalTheory.LieGramLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLiftPreservingAppellHumbertFormStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_lift_preserving_appellHumbert_form : ∀ (Q P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif Q.A Q.L Q.g) (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (u' : HolUnif P.A P.L g) (Hm' : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (f : Q.A ⟶ P.A), IsMonHom f → LBIso (lbPow (P.L.pull f.left) 1) (lbPow Q.L 1) → ∀ (n : ℕ) (v' : Fin n → (epsR ℂ ⟶ Q.A)) (Wc : Fin n → Fin Q.g → ℂ), (∀ i, IsTangent (v' i) ∧ u.IsDiff (Wc i) (v' i)) → ∀ (m : ℕ) (a : Fin m → Fin n → ℂ) (tv : Fin m → (epsR ℂ ⟶ P.A)) (Xv : Fin m → Fin g → ℂ), (∀ i, u'.IsDiff (Xv i) (tv i)) → (∀ i (q : epsR ℂ ⟶ Q.A), IsLieComb (a i) v' q → q ≫ f = tv i) → ∃ L : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x x', hermForm Hm' (L x) (L x') = hermForm Hm x x') ∧ ∀ i, L (∑ k, a i k • Wc k) = Xv i := by
  first | exact @GlobalTheory.LieGramLift.exists_lift | exact GlobalTheory.LieGramLift.exists_lift | (intros; apply GlobalTheory.LieGramLift.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreUniformisationAppellHumbertUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreUniformisationAppellHumbertUnit
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FibreUnifComb

theorem exists_unif_isDiff_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ₀ : c.F →+* ℂ) (U : Unf Xo c σ₀ r), 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (w : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W) (ρ : E →+* ℂ) (z : FrPt Xo c (CAt σ₀)), z.x = (U.un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt σ₀), (∀ i, IsCombAt (U.un k w).x ((U.un k w).u ρ) (C i) (z.u ρ i)) → ∃ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x) (u' : HolUnif T.pol.A T.pol.L W.g) (χ' : u'.Λ → ℂ), u'.IsAH Wu.Hm χ' ∧ ∀ i, ∃ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i ∧ u'.IsDiff (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) w' := by
  intro E _ _ _ H Dw l Xo c r σ₀ U hpq k x W Wu ρ z hz C hC
  rcases z with ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩
  dsimp only at hz ztan hC ⊢
  subst hz
  obtain ⟨Φ₀⟩ := GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo ℂ (U.un k x).x hpq
  obtain ⟨-, h₁, h₂⟩ := GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo ℂ (U.un k x).x Φ₀.T.t Φ₀.m
  obtain ⟨th, ht⟩ := h₁ (U.un k x).s
  have hne := (h₂ th _ ht).2.1 (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ _ _ (U.un k x).gen)
  let Φ : GlobalTheory.LamT.FibKey Xo ℂ (U.un k x).x := { Φ₀ with th := th, th_ne := hne }
  obtain ⟨u, χ, -, hA, -, -, -, hD⟩ := GlobalTheory.OrthoMetric.exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos
    Wu.c2 Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7
  refine ⟨Φ.T, Φ.m, u, χ, hA, fun i => ?_⟩
  have hd := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ W.g _ W.F (W.ik k) W.Pm W.per (Dw.mult ρ)
    ((U.un k x).u ρ) (fun l => Pi.single (W.e.symm ⟨ρ, l⟩) 1) (W.der ρ) (fun l => toC (C i l)) (zu ρ i)).1
    (by rw [← W.pt]; exact hC i)
  exact hD _ _ (ztan ρ i) hd

end GlobalTheory.FibreUnifComb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreUniformisationAppellHumbertUnitStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibre_uniformisation_appellHumbert_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ₀ : c.F →+* ℂ) (U : Unf Xo c σ₀ r), 1 ≤ Dw.p + Dw.q → ∀ (k : U.Comp) (w : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W) (ρ : E →+* ℂ) (z : FrPt Xo c (CAt σ₀)), z.x = (U.un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt σ₀), (∀ i, IsCombAt (U.un k w).x ((U.un k w).u ρ) (C i) (z.u ρ i)) → ∃ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x) (u' : HolUnif T.pol.A T.pol.L W.g) (χ' : u'.Λ → ℂ), u'.IsAH Wu.Hm χ' ∧ ∀ i, ∃ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i ∧ u'.IsDiff (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) w' := by
  first | exact @GlobalTheory.FibreUnifComb.exists_unif_isDiff_comb | exact GlobalTheory.FibreUnifComb.exists_unif_isDiff_comb | (intros; apply GlobalTheory.FibreUnifComb.exists_unif_isDiff_comb <;> assumption)
end
end
