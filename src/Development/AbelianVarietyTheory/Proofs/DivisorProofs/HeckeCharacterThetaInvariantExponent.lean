module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OfBeforeProjector
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.MuProps

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem atEmb_emb (w : InfinitePlace E) (z : ℂ) : atEmb w.embedding z = Pi.single w z := by
  unfold atEmb; simp [InfinitePlace.mk_embedding]

theorem chiInf_expU_single {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) (z : ℂ) :
    ((chiInf μ (expU (Pi.single v z)) : ℂˣ) : ℂ) =
      Complex.exp ((e v : ℂ) / 2 * z + (-(e v : ℂ) / 2) * starRingEnd ℂ z) := by
  rw [h.2.2.2.2, Finset.prod_eq_single v]
  · change (Complex.exp ((Pi.single v z : Cinf E) v) / ((‖Complex.exp ((Pi.single v z : Cinf E) v)‖ : ℝ) : ℂ)) ^ e v = _
    rw [Pi.single_eq_same, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub, ← Complex.exp_int_mul]
    congr 1
    have := Complex.add_conj z
    push_cast at this
    linear_combination ((e v : ℂ) / 2) * this
  · intro u _ hu
    change (Complex.exp ((Pi.single v z : Cinf E) u) / ((‖Complex.exp ((Pi.single v z : Cinf E) u)‖ : ℝ) : ℂ)) ^ e u = 1
    rw [Pi.single_eq_of_ne hu]
    simp
  · simp

theorem expo_emb {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) :
    expo μ v.embedding = (e v : ℂ) / 2 :=
  expo_eq_of_exp μ v.embedding _ (-(e v : ℂ) / 2) fun z => by
    rw [atEmb_emb]; exact chiInf_expU_single h v z

theorem expo_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) :
    expo μ (ComplexEmbedding.conjugate v.embedding) = -(e v : ℂ) / 2 :=
  expo_eq_of_exp μ _ _ ((e v : ℂ) / 2) fun z => by
    rw [atEmb_conj, atEmb_emb, chiInf_expU_single h v]
    congr 1
    simp only [Complex.conj_conj]
    ring

theorem dchi_single {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (v : InfinitePlace E) (w : ℂ) :
    dchi μ (Pi.single v w) = (w.im : ℂ) * dchi μ (Pi.single v Complex.I) := by
  have h1 := expo_emb h v
  have h2 := expo_conj h v
  simp only [expo, atEmb_conj, atEmb_emb, map_one, Complex.conj_I, Pi.single_neg, map_neg] at h1 h2
  have hd1 : dchi μ (Pi.single v 1) = 0 := by linear_combination h1 + h2
  rw [← atEmb_emb, atEmb_eq, map_add (f := _), map_smul, map_smul, atEmb_emb, atEmb_emb, hd1]
  rw [smul_zero, zero_add, Complex.real_smul]

theorem dchi_neg_star {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (z : Cinf E) :
    dchi μ (-star z) = dchi μ z := by
  conv_lhs => rw [← Finset.univ_sum_single (-star z)]
  conv_rhs => rw [← Finset.univ_sum_single z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dchi_single h v, dchi_single h v (z v), Pi.neg_apply, Pi.star_apply, Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg]

theorem finId_conjFin (u : (Af E)ˣ) :
    finId E (Units.map (conjFin (IsCMField.complexConj E).toRingEquiv).toMonoidHom u) =
      Units.map (conjAd E).toMonoidHom (finId E u) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = (infEq E) (starRingEnd (Cinf E) ((infEq E).symm ((1 : InfiniteAdeleRing E) - 0 + 0)))
    simp
  · change (1 : Af E) - 1 + conjFin (IsCMField.complexConj E).toRingEquiv (u : Af E) =
      conjFin (IsCMField.complexConj E).toRingEquiv ((1 : Af E) - 1 + (u : Af E))
    simp

theorem mu_mul_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (x : Neutral.B1.Ideles E) :
    μ.1 x * μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x) = 1 := by
  rw [← map_mul, ← GlobalTheory.GalOfCusp.ideleMap_ideleNorm, h.2.1]
  have := congrArg (fun c : HChar E => c.1 x) (GlobalTheory.GalOfCusp.compNorm_quadChar E)
  exact this

theorem thetaInv {μ : HChar E} {e : InfinitePlace E → ℤ} (h : IsMu μ e) (a : ℕ) : ThetaInv a μ := by
  refine CG.thetaInv_of (fun u => ?_) (dchi_neg_star h)
  rw [map_inv, finId_conjFin, ← GlobalTheory.PolChar.ideleConj_eq, map_inv]
  have := mu_mul_conj h (finId E u)
  exact inv_eq_of_mul_eq_one_left this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → (∀ a, ThetaInv a μ) ∧ (∀ v : InfinitePlace E, expo μ v.embedding = (e v : ℂ) / 2) ∧ ∀ v : InfinitePlace E, expo μ (ComplexEmbedding.conjugate v.embedding) = -(e v : ℂ) / 2 :=
  fun _ _ _ _ _ _ _ h => ⟨thetaInv h, expo_emb h, expo_conj h⟩

end GlobalTheory.BCT.MuProps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPtLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def fstA (E : Type) [Field E] [NumberField E] : Ad E →+* InfiniteAdeleRing E := RingHom.fst _ _

theorem fst_entry (γ : GL (Fin n) E) (i j : Fin n) :
    fstA E ((finGL E n (ratF E n γ)).val i j) = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E)) i j := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E × Af E)) i j -
      ((0 : InfiniteAdeleRing E), (1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      ((0 : InfiniteAdeleRing E), algebraMap E (Af E) (γ.val i j))).1 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem snd_entry (γ : GL (Fin n) E) (i j : Fin n) :
    pFin E ((finGL E n (ratF E n γ)).val i j) = algebraMap E (Af E) (γ.val i j) := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E × Af E)) i j -
      ((0 : InfiniteAdeleRing E), (1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      ((0 : InfiniteAdeleRing E), algebraMap E (Af E) (γ.val i j))).2 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_cT {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (M : Matrix (Fin n) (Fin n) A) : (cT σ M).map f = cT τ (M.map f) := by
  ext i j; simp [cT, h]

theorem ext_ad (M N : Matrix (Fin n) (Fin n) (Ad E)) (h1 : M.map (fstA E) = N.map (fstA E))
    (h2 : M.map (pFin E) = N.map (pFin E)) : M = N := by
  ext i j
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem mem_UA (γ : UE E n) : finGL E n (ratF E n γ.1) ∈ UA E n := by
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  show cT (conjAd E) (finGL E n (ratF E n γ.1)).val * 1 * (finGL E n (ratF E n γ.1)).val = 1
  have hf : (finGL E n (ratF E n γ.1)).val.map (fstA E) = 1 := by
    ext i j; rw [Matrix.map_apply, fst_entry]
  have hs : (finGL E n (ratF E n γ.1)).val.map (pFin E) = γ.1.val.map (algebraMap E (Af E)) := by
    ext i j; rw [Matrix.map_apply, snd_entry]; rfl
  apply ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (fstA E) (conjAd E) ((infEq E).toRingHom.comp ((starRingEnd (Cinf E)).comp (infEq E).symm.toRingHom)) (fun x => rfl), hf, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j; simp [cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (pFin E) (conjAd E) (conjFin (IsCMField.complexConj E).toRingEquiv) (fun x => rfl), hs,
      Matrix.map_one _ (map_zero _) (map_one _)]
    have : cT (conjFin (IsCMField.complexConj E).toRingEquiv) (γ.1.val.map (algebraMap E (Af E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val).map (algebraMap E (Af E)) := by
      ext i j; simp [cT, conjFin_algebraMap]
    rw [this, ← Matrix.map_one (algebraMap E (Af E)) (map_zero _) (map_one _), ← Matrix.map_mul, ← Matrix.map_mul, hγ]

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (h : g ∈ H) : toSub H g = ⟨g, h⟩ :=
  dif_pos h

theorem mem_finU (γ : UE E n) : (⟨_, mem_UA γ⟩ : UA E n) ∈ finU (E := E) (n := n) := by
  show cInf (⟨_, mem_UA γ⟩ : UA E n) = 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (infEq E).symm (fstA E ((finGL E n (ratF E n γ.1)).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j
  rw [fst_entry]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem finPt_eq (γ : UE E n) : ((finPt γ : finU (E := E) (n := n)) : UA E n) = ⟨_, mem_UA γ⟩ := by
  have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = ⟨_, mem_UA γ⟩ := toSub_of_mem _ _ (mem_UA γ)
  unfold finPt
  rw [h1, toSub_of_mem _ _ (mem_finU γ)]

end GlobalTheory.BCT.FinPtLoc

theorem GlobalTheory.BCT.locPt_finPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E),
    toSub (UL n w) (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)) = locPt w γ := by
  intro E _ _ _ _ n γ w
  rw [FinPtLoc.finPt_eq]
  unfold locPt
  congr 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
  rw [FinPtLoc.snd_entry]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPoStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_definiteUnitaryFinitePart_eq_localPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E), toSub (UL n w) (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)) = locPt w γ := by
  first | exact @GlobalTheory.BCT.locPt_finPt | exact GlobalTheory.BCT.locPt_finPt | (intros; apply GlobalTheory.BCT.locPt_finPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SepBezout

theorem valuation_le_one_eventually {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, w.valuation E x ≤ 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal (𝓞 E)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  have h1 : w.valuation E (algebraMap (𝓞 E) E b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

theorem bezout_eventually : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ u v : (w.adicCompletion E)[X],
      (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧ (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * P.map (algebraMap E (w.adicCompletion E)) + v * derivative (P.map (algebraMap E (w.adicCompletion E))) = 1 := by
  intro E _ _ P hP
  obtain ⟨u₀, v₀, h⟩ := hP
  have key : ∀ f : E[X], ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      ∀ i, (f.map (algebraMap E (w.adicCompletion E))).coeff i ∈ w.adicCompletionIntegers E := by
    intro f
    filter_upwards [(Filter.eventually_all_finset f.support).2
      (fun i _ => valuation_le_one_eventually (f.coeff i))] with w hw i
    rw [Polynomial.coeff_map]
    by_cases hi : i ∈ f.support
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have := hw i hi
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
      exact this
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero]
      exact zero_mem _
  filter_upwards [key u₀, key v₀] with w hu hv
  refine ⟨u₀.map (algebraMap E (w.adicCompletion E)), v₀.map (algebraMap E (w.adicCompletion E)), hu, hv, ?_⟩
  rw [Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add (f := _), h,
    Polynomial.map_one]

end GlobalTheory.BCT.SepBezout
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegersStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_bezout_separable_derivative_adicIntegers : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ u v : (w.adicCompletion E)[X],
      (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧ (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * P.map (algebraMap E (w.adicCompletion E)) + v * derivative (P.map (algebraMap E (w.adicCompletion E))) = 1 := by
  first | exact @GlobalTheory.BCT.SepBezout.bezout_eventually | exact GlobalTheory.BCT.SepBezout.bezout_eventually | (intros; apply GlobalTheory.BCT.SepBezout.bezout_eventually <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsCompatible
noncomputable section

namespace GlobalTheory.PhRatCommon

section Lemmas

open NumberField
open scoped TensorProduct

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AdTh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

theorem rdU_of_isBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) {m : ℕ} {f' : Rul Xo c'} {as : Fin m → c'.F}
    {fs : Fin m → Rul Xo c} (h : IsBC hle f' as fs) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (x : Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) :
    rdU (unfBC hle U σ') f' k x = ∑ j, σ' (as j) * rdU (U (σ'.comp (incF c c' hle))) (fs j) k x := by
  by_cases hx : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom
  · letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
    have e := h (CAt σ') (fun _ => rfl) ((unfBC hle U σ').un k ⟨x, hx⟩)
    have e1 : rdU (unfBC hle U σ') f' k x = toC (evR Xo c' f' ((unfBC hle U σ').un k ⟨x, hx⟩)) := dif_pos hx
    rw [e1, e]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x =
      toC (evR Xo c (fs j) ((U (σ'.comp (incF c c' hle))).un k ⟨x, hx⟩)) := dif_pos hx
    rw [e2]
    rfl
  · have e1 : rdU (unfBC hle U σ') f' k x = 0 := dif_neg hx
    rw [e1]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x = 0 := dif_neg hx
    rw [e2, mul_zero]

theorem exists_rdU_eq_sum (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f' : Rul Xo c') (hf : f' ∈ cusp Xo c' (unfBC hle U) a n) :
    ∃ (m : ℕ) (b : Fin m → c'.F) (fs : Fin m → cusp Xo c U a n), ∀ k x,
      rdU (unfBC hle U σ') f' k x = ∑ j, σ' (b j) * rdU (U (σ'.comp (incF c c' hle))) (fs j : Rul Xo c) k x := by
  obtain ⟨m, b, fs, hfs, hbc⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC E H Dw l Xo c c' hle).2 r U a n f' hf
  exact ⟨m, b, fun j => ⟨fs j, hfs j⟩, rdU_of_isBC hle U σ' hbc⟩

end Gen

theorem sum_shape {m : ℕ} {c l u x : ℂ} {a a' y p : Fin m → ℂ} (h : x = ∑ j, a j * y j) (ha : ∀ j, a' j = a j)
    (hp : ∀ j, p j = c * u * y j) : c * l * u * x = ∑ j, a' j * (l * p j) := by
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ha, hp]
  ring

end Lemmas

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.PhRatCommon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChartMetricBlockForm
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

open Filter Topology Set
open scoped ContDiff

namespace GlobalTheory.HessPull


open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.AR.Up.RGF in
theorem cHess_comp_apply (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (U : Set (V n)) (hU : IsOpen U)
    (v : V n) (hv : v ∈ U) (hF : ContDiffOn ℂ 2 F U) (hg : ContDiffAt ℝ 2 g (F v)) (j k : Fin n) :
    cHess n (g ∘ F) v j k = ∑ a, ∑ b,
      cHess d g (F v) b a * fderiv ℂ F v (bas n j) b *
        (starRingEnd ℂ) (fderiv ℂ F v (bas n k) a) := by
  have hFd : ∀ y ∈ U, HasFDerivAt F (fderiv ℂ F y) y := fun y hy =>
    (((hF.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hgev : ∀ᶠ y in 𝓝 v, ContDiffAt ℝ 2 g (F y) :=
    (hFd v hv).continuousAt.eventually (hg.eventually (by simp))
  have hwdb : ∀ k, wdb n k (g ∘ F) =ᶠ[𝓝 v]
      fun y => ∑ a, wdb d a g (F y) * (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a) := by
    intro k
    filter_upwards [hgev, hU.mem_nhds hv] with y hy hyU
    exact gc_wdb_comp n d g F _ y (hy.differentiableAt (by simp)) (hFd y hyU) k
  have hD : DifferentiableAt ℝ (fderiv ℝ g) (F v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hWg : ∀ a, DifferentiableAt ℝ (wdb d a g) (F v) := by
    intro a
    show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas d a) +
      Complex.I * fderiv ℝ g y (Complex.I • bas d a)) / 2) (F v)
    have h1 := hD.clm_apply (differentiableAt_const (bas d a))
    have h2 := hD.clm_apply (differentiableAt_const (Complex.I • bas d a))
    have h3 := (h1.add (h2.const_mul Complex.I)).mul_const ((2 : ℂ)⁻¹)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [div_eq_mul_inv]
  have hWa : ∀ a, DifferentiableAt ℝ (fun y => wdb d a g (F y)) v := fun a =>
    (hWg a).comp v ((hFd v hv).restrictScalars ℝ).differentiableAt
  have hDF : DifferentiableAt ℂ (fun y => fderiv ℂ F y) v :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt (hU.mem_nhds hv)).differentiableAt
      (by norm_num)
  have hPa : ∀ k a, DifferentiableAt ℂ (fun y => fderiv ℂ F y (bas n k) a) v := fun k a =>
    (differentiableAt_piLp 2).1 (hDF.clm_apply (differentiableAt_const _)) a
  have hCa : ∀ k a, DifferentiableAt ℝ
      (fun y => (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v := by
    intro k a
    have := Complex.conjCLE.differentiableAt.comp v ((hPa k a).restrictScalars ℝ)
    simpa [Function.comp_def] using this
  show wd n j (wdb n k (g ∘ F)) v = _
  rw [wd_congr n j _ _ v (hwdb k),
    fc_wd_sum n j Finset.univ (fun a y => wdb d a g (F y) *
      (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v (fun a _ => (hWa a).mul (hCa k a))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wd_mul' n j _ _ v (hWa a) (hCa k a), wd_conj', fc_wdb_holo n _ v (hPa k a) j, map_zero,
    mul_zero, add_zero]
  have := gc_wd_comp n d (wdb d a g) F (fderiv ℂ F v) v (hWg a) (hFd v hv) j
  rw [show (fun y => wdb d a g (F y)) = wdb d a g ∘ F from rfl, this, Finset.sum_mul]
  rfl

end GlobalTheory.HessPull

namespace GlobalTheory.HessPull

open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open GlobalTheory.ChartGlue

theorem hess_pull_factor : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k)
    (f : Y ⟶ B) (w : f ≫ q = p) (σ : k →+* ℂ) (D d : ℕ) (c : AlgChart p σ D) (c' : AlgChart q σ d)
    (y : CxPts p σ), y ∈ c.e.source → PtsOver.map f w (spMap σ) y ∈ c'.e.source →
    ∃ (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ), ∀ (A : HermLB q)
      (i : (A.pull f w).B.ι), y ∈ ptsIn p σ ((A.pull f w).B.U i) →
        ∃ K : Matrix (Fin d) (Fin d) ℂ, c.hess ((A.pull f w).φ σ) i y = P * K * Q := by
  intro k _ B Y q p f w σ D d c c' y hy hy'
  set m := PtsOver.map f w (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ f := fun _ => rfl
  set F : V D → V d := c'.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c'.e.source)
  have hU : IsOpen U := isOpen_over c.e (c'.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := mem_over c.e hy hy'
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c'
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c'.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy]
  refine ⟨Matrix.of fun j b => fderiv ℂ F (c.e y) (bas D j) b,
    Matrix.of fun a k => (starRingEnd ℂ) (fderiv ℂ F (c.e y) (bas D k) a), ?_⟩
  intro A i hi
  have him : m y ∈ ptsIn q σ (A.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
  set g : V d → ℂ := fun v => ((A.φ σ).φ (i PUnit.unit) (c'.e.symm v) : ℂ)
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((A.cInf σ).contDiffAt c' hy' him)
  have e : (fun v => (((A.pull f w).φ σ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ (A.φ σ) f w i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c'.e.left_inv hv.2]
    exact congrArg _ this
  refine ⟨cHess d g (F (c.e y)), ?_⟩
  show cHess D _ (c.e y) = _
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]
  ext j k
  rw [cHess_comp_apply D d g F U hU _ hyU hF hg j k, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.HessPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqOneOfIsUnit
open GlobalTheory.Tw Matrix

noncomputable section

namespace GlobalTheory.SplitLattice

variable {E : Type} [NormedField E] [IsUltrametricDist E]

def ball : ValuationSubring E where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
  mem_or_inv_mem' x := by
    by_cases h : ‖x‖ ≤ 1
    · exact Or.inl h
    · right
      show ‖x⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h))

theorem norm_le_one (x : (ball : ValuationSubring E)) : ‖(x : E)‖ ≤ 1 := x.2

theorem norm_eq_one_of_isUnit {x : (ball : ValuationSubring E)} (hx : IsUnit x) : ‖(x : E)‖ = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h0 : ((u : (ball : ValuationSubring E)) : E) * ((u⁻¹ : (ball : ValuationSubring E)ˣ) : E) = 1 :=
    congrArg Subtype.val u.mul_inv
  have h := congrArg norm h0
  rw [norm_mul, norm_one] at h
  have h1 := norm_le_one (u : (ball : ValuationSubring E))
  have h2 := norm_le_one ((u⁻¹ : (ball : ValuationSubring E)ˣ) : (ball : ValuationSubring E))
  nlinarith [norm_nonneg ((u : (ball : ValuationSubring E)) : E),
    norm_nonneg (((u⁻¹ : (ball : ValuationSubring E)ˣ) : (ball : ValuationSubring E)) : E)]

instance : Finite (MaximalSpectrum (ball : ValuationSubring E)) := by
  haveI : Subsingleton (MaximalSpectrum (ball : ValuationSubring E)) := ⟨fun a b => by
    have ha := IsLocalRing.eq_maximalIdeal a.isMaximal
    have hb := IsLocalRing.eq_maximalIdeal b.isMaximal
    exact MaximalSpectrum.ext (ha.trans hb.symm)⟩
  exact Finite.of_subsingleton

abbrev ι : (ball : ValuationSubring E) →+* E := (ball : ValuationSubring E).subtype

theorem exists_cyclic_basis {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (hM : ∀ i j, ‖M i j‖ ≤ 1)
    (hs : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * M.charpoly + v * Polynomial.derivative M.charpoly = 1) :
    ∃ K : Matrix (Fin n) (Fin n) (ball : ValuationSubring E), IsUnit K.det ∧
      M * K.map ι = K.map ι * GlobalTheory.Orb.companionMat n M.charpoly := by
  obtain ⟨u, v, hu, hv, huv⟩ := hs
  let M' : Matrix (Fin n) (Fin n) (ball : ValuationSubring E) := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have hM' : M'.map ι = M := by ext i j; rfl
  have lift : ∀ p : Polynomial E, (∀ i, ‖p.coeff i‖ ≤ 1) →
      ∃ q : Polynomial (ball : ValuationSubring E), q.map ι = p := by
    intro p hp
    exact (Polynomial.mem_lifts p).1 ((Polynomial.lifts_iff_coeff_lifts p).2 fun i => ⟨⟨p.coeff i, hp i⟩, rfl⟩)
  obtain ⟨u', hu'⟩ := lift u hu
  obtain ⟨v', hv'⟩ := lift v hv
  have hsep : M'.charpoly.Separable := by
    refine ⟨u', v', Polynomial.map_injective ι Subtype.val_injective ?_⟩
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      ← Matrix.charpoly_map, hM', hu', hv', Polynomial.map_one]
    exact huv
  obtain ⟨w, hw⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField _
    (Fin n) M' hsep
  let σ : Equiv.Perm (Fin n) := (Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin n))
  have hk : GlobalTheory.RegSS.krylov M' w = (GlobalTheory.ClassParam.krylov M' w).submatrix id σ := by
    ext i j
    simp [GlobalTheory.RegSS.krylov, GlobalTheory.ClassParam.krylov, σ]
  refine ⟨GlobalTheory.ClassParam.krylov M' w, ?_, ?_⟩
  · rw [hk, Matrix.det_permute'] at hw
    exact isUnit_of_mul_isUnit_right hw
  · rw [GlobalTheory.ClassParam.krylov_map, hM']
    exact GlobalTheory.Orb.mul_krylov_eq M _

theorem split_place : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (A x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖A i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * A.charpoly + v * Polynomial.derivative A.charpoly = 1) → IsUnit x → (∀ i j, ‖(x⁻¹ * A * x) i j‖ ≤ 1) → ∃ t k : Matrix (Fin n) (Fin n) E, IsUnit t ∧ t * A = A * t ∧ (∀ i j, ‖k i j‖ ≤ 1) ∧ ‖k.det‖ = 1 ∧ x = t * k := by
  intro E _ _ _ n A x hA hs hx hy
  obtain ⟨U, rfl⟩ := hx
  have hcp : ((U : Matrix (Fin n) (Fin n) E)⁻¹ * A *
      (U : Matrix (Fin n) (Fin n) E)).charpoly = A.charpoly :=
    Matrix.charpoly_units_conj' U A
  obtain ⟨KA, hKA, hA'⟩ := exists_cyclic_basis A hA hs
  obtain ⟨Ky, hKy, hy'⟩ := exists_cyclic_basis _ hy (hcp ▸ hs)
  rw [hcp] at hy'
  set C := GlobalTheory.Orb.companionMat n A.charpoly
  set a := KA.map ι with ha_def
  set b := Ky.map ι with hb_def
  have ha : IsUnit a.det := by
    rw [ha_def, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hKA.map ι
  have hb : IsUnit b.det := by
    rw [hb_def, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hKy.map ι
  have hbinv : (Ky⁻¹).map ι = b⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [hb_def, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      Matrix.mul_nonsing_inv _ hKy, map_one]
  have hk : (KA * Ky⁻¹).map ι = a * b⁻¹ := by
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hbinv]
  have hUU : (U : Matrix (Fin n) (Fin n) E) * (U : Matrix (Fin n) (Fin n) E)⁻¹ = 1 := by
    rw [← Matrix.coe_units_inv]; exact Units.mul_inv U
  have haA : a⁻¹ * A = C * a⁻¹ := by
    calc a⁻¹ * A = a⁻¹ * (A * a) * a⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]
      _ = C * a⁻¹ := by
          rw [hA', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]
  refine ⟨(U : Matrix (Fin n) (Fin n) E) * b * a⁻¹, (KA * Ky⁻¹).map ι, ?_, ?_, ?_, ?_, ?_⟩
  · exact (U.isUnit.mul ((Matrix.isUnit_iff_isUnit_det _).2 hb)).mul
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det a ha))
  · calc (U : Matrix (Fin n) (Fin n) E) * b * a⁻¹ * A = (U : Matrix (Fin n) (Fin n) E) * (b * C) * a⁻¹ := by
          rw [Matrix.mul_assoc, haA, ← Matrix.mul_assoc, Matrix.mul_assoc ((U : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E)]
      _ = (U : Matrix (Fin n) (Fin n) E) * ((U : Matrix (Fin n) (Fin n) E)⁻¹ * A * (U : Matrix (Fin n) (Fin n) E) * b) * a⁻¹ := by rw [hy']
      _ = A * ((U : Matrix (Fin n) (Fin n) E) * b * a⁻¹) := by
          simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  · intro i j
    exact norm_le_one _
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine norm_eq_one_of_isUnit ?_
    rw [Matrix.det_mul]
    exact hKA.mul (Matrix.isUnit_nonsing_inv_det Ky hKy)
  · rw [hk]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc a⁻¹ a, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hb, Matrix.mul_one]

end GlobalTheory.SplitLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitUniq

theorem splitUniq : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N g : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t : GL (Fin n) (w.adicCompletion E), t * N = N * t ∧ ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  intro E _ _ n w N g hN hs hg
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  have key : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 ↔ x ∈ w.adicCompletionIntegers E := fun x => by
    rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  have memK : ∀ h : GL (Fin n) (w.adicCompletion E), h ∈ GlobalTheory.LFun.KGL w (n := n) ↔
      (∀ i j, h.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (h⁻¹).1 i j ∈ w.adicCompletionIntegers E := fun h => by
    rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]; rfl
  obtain ⟨hN1, -⟩ := (memK N).1 hN
  obtain ⟨hg1, -⟩ := (memK _).1 hg
  obtain ⟨u, v, hu, hv, huv⟩ := hs
  have hconj : ((g⁻¹ * N * g : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))⁻¹ * N * g := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  obtain ⟨t, k, ht, htN, hk, hdet, hgtk⟩ := GlobalTheory.SplitLattice.split_place (w.adicCompletion E) n N.val g.val
    (fun i j => (key _).2 (hN1 i j)) ⟨u, v, fun i => (key _).2 (hu i), fun i => (key _).2 (hv i), huv⟩ g.isUnit
    (fun i j => (key _).2 (by rw [← hconj]; exact hg1 i j))
  set tU := ht.unit with htU
  refine ⟨tU, Units.ext htN, tU⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
  have hkv : ((tU⁻¹ * g : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = k := by
    have htt : (tU : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = t := ht.unit_spec
    rw [Units.val_mul, hgtk, ← htt, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hkI : ∀ i j, k i j ∈ w.adicCompletionIntegers E := fun i j => (key _).1 (hk i j)
  let M : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨k i j, hkI i j⟩
  have hMk : M.map (w.adicCompletionIntegers E).subtype = k := by ext i j; rfl
  have hdetM : ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) = k.det := by
    rw [← hMk]
    exact (RingHom.map_det (w.adicCompletionIntegers E).subtype M)
  have hk0 : k.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hdet; exact zero_ne_one hdet
  have hMu : IsUnit M.det := by
    have h1 : M.det * ⟨(k.det)⁻¹, (key _).1 (by rw [norm_inv, hdet, inv_one])⟩ = 1 := by
      apply Subtype.ext
      show ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) * (k.det)⁻¹ = 1
      rw [hdetM, mul_inv_cancel₀ hk0]
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hinv : k⁻¹ = M⁻¹.map (w.adicCompletionIntegers E).subtype := by
    apply Matrix.inv_eq_right_inv
    rw [← hMk, ← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)]
  refine (memK _).2 ⟨fun i j => by rw [hkv]; exact hkI i j, fun i j => ?_⟩
  rw [Matrix.coe_units_inv, hkv, hinv]
  exact (M⁻¹ i j).2

end GlobalTheory.SplitUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGLStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N g : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t : GL (Fin n) (w.adicCompletion E), t * N = N * t ∧ ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  first | exact @GlobalTheory.SplitUniq.splitUniq | exact GlobalTheory.SplitUniq.splitUniq | (intros; apply GlobalTheory.SplitUniq.splitUniq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrame
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt

namespace GlobalTheory.PetAdd

theorem cnorm_add_le {ι : Type} [Fintype ι] (u w : ι → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (u + w) ≤ Formalism.HermitianLatticesTheory.cnorm u + Formalism.HermitianLatticesTheory.cnorm w := by
  have key : ∀ t : ι → ℂ, Formalism.HermitianLatticesTheory.cnorm t = ‖(WithLp.equiv 2 (ι → ℂ)).symm t‖ := fun t => by
    rw [EuclideanSpace.norm_eq]; rfl
  rw [key, key, key]
  have e : (WithLp.equiv 2 (ι → ℂ)).symm (u + w) = (WithLp.equiv 2 (ι → ℂ)).symm u + (WithLp.equiv 2 (ι → ℂ)).symm w := by
    first | exact WithLp.equiv_symm_add 2 u w | rfl | simp
  rw [e]
  exact norm_add_le _ _

theorem IsGram.add_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    {ι : Type} [Fintype ι] [DecidableEq ι] {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) (v : InfinitePlace K) (f g : V) :
    N v.embedding (f + g) ≤ N v.embedding f + N v.embedding g := by
  rw [← (h v).2, ← (h v).2, ← (h v).2]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  have : Formalism.HermitianLatticesTheory.vecAt b v (f + g) = Formalism.HermitianLatticesTheory.vecAt b v f + Formalism.HermitianLatticesTheory.vecAt b v g := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [this, Matrix.mulVec_add]
  exact cnorm_add_le _ _

end GlobalTheory.PetAdd

namespace GlobalTheory.PetAdd

theorem normOn_add_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E), GoodOn U x V dict Z G → ∀ σ (f g : cuspOn U Z G), normOn U x V dict Z G σ (f + g) ≤ normOn U x V dict Z G σ f + normOn U x V dict Z G σ g := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G h σ f g
  letI : Module c.F (cuspOn U Z G) := Submodule.module (cuspOn U Z G)
  obtain ⟨n, ⟨p, hp⟩⟩ := h.1
  have hconj : ∀ y, normOn U x V dict Z G ((starRingEnd ℂ).comp σ) y = normOn U x V dict Z G σ y :=
    fun y => GlobalTheory.CompHt.petOn_conj U x V dict Z G σ y
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · have := IsGram.add_le hp (InfinitePlace.mk σ) f g
    rwa [e] at this
  · have := IsGram.add_le hp (InfinitePlace.mk σ) f g
    have e' : (InfinitePlace.mk σ).embedding = (starRingEnd ℂ).comp σ := by
      rw [e]; ext a; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e', hconj, hconj, hconj] at this
    exact this

end GlobalTheory.PetAdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrameStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_norm_component_add_le_of_gramFrame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E), GoodOn U x V dict Z G → ∀ σ (f g : cuspOn U Z G), normOn U x V dict Z G σ (f + g) ≤ normOn U x V dict Z G σ f + normOn U x V dict Z G σ g := by
  first | exact @GlobalTheory.PetAdd.normOn_add_le | exact GlobalTheory.PetAdd.normOn_add_le | (intros; apply GlobalTheory.PetAdd.normOn_add_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open Filter GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwOrbGood

theorem avg_const {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have h : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold GlobalTheory.BCT.avg
  rw [h, Subgroup.index_top]
  have : (∑ᶠ q : H ⧸ (⊤ : Subgroup H), (fun _ : H => c) q.out) = c := by
    rw [finsum_eq_single (fun q : H ⧸ (⊤ : Subgroup H) => (fun _ : H => c) q.out) (QuotientGroup.mk 1)
      (fun q hq => absurd (by induction q using QuotientGroup.induction_on with | H a => exact QuotientGroup.eq.2 (Subgroup.mem_top _)) hq)]
  rw [this]; simp

theorem summand_goodplace : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (KH : Subgroup H) (δ : H), δ ∈ KH → cptPart (twCent (MonoidHom.id H) δ) ≤ KH → (∀ g : H, g⁻¹ * δ * g ∈ KH → ∃ t ∈ twCent (MonoidHom.id H) δ, t⁻¹ * g ∈ KH) → ∀ x : H, GlobalTheory.TwOrbConj.summand (MonoidHom.id H) KH δ ((KH : Set H).indicator 1) x = if ∃ t ∈ twCent (MonoidHom.id H) δ, ∃ k ∈ KH, x = t * k then 1 else 0 := by
  intro H _ _ _ KH δ hδ hc hg x
  split_ifs with hx
  · obtain ⟨t, ht, k, hk, rfl⟩ := hx
    have e : t * k = t * 1 * k := by group
    rw [e, GlobalTheory.TwOrbConj.summand_rep _ _ _ _ _ ht hk]
    unfold GlobalTheory.TwOrbConj.summand
    have hmap : KH.map (MulAut.conj (1 : H)).toMonoidHom = KH := GlobalTheory.TwOrbConj.map_conj_self KH KH.one_mem
    have hcT : cptPart (twCent (MonoidHom.id H) δ) ≤ twCent (MonoidHom.id H) δ := by
      unfold GlobalTheory.BCT.cptPart
      rw [Subgroup.closure_le]
      intro y hy; exact hy.1
    have hrel : (twCent (MonoidHom.id H) δ ⊓ KH.map (MulAut.conj (1 : H)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id H) δ)) = 1 := by
      rw [hmap, Subgroup.relIndex_eq_one]
      exact le_inf hcT hc
    have hfun : (fun k : KH => (KH : Set H).indicator (1 : H → ℂ) ((1 * (k : H))⁻¹ * δ * (MonoidHom.id H) (1 * (k : H))))
        = fun _ => 1 := by
      funext k
      rw [Set.indicator_of_mem]
      · rfl
      · simp only [one_mul, MonoidHom.id_apply]
        exact KH.mul_mem (KH.mul_mem (KH.inv_mem k.2) hδ) k.2
    rw [hrel, hfun, avg_const]; simp
  · unfold GlobalTheory.TwOrbConj.summand
    have hfun : (fun k : KH => (KH : Set H).indicator (1 : H → ℂ) ((x * (k : H))⁻¹ * δ * (MonoidHom.id H) (x * (k : H))))
        = fun _ => 0 := by
      funext k
      rw [Set.indicator_of_notMem]
      intro hm
      simp only [MonoidHom.id_apply] at hm
      obtain ⟨t, ht, htk⟩ := hg (x * k) hm
      apply hx
      refine ⟨t, ht, t⁻¹ * (x * k) * (k : H)⁻¹, KH.mul_mem htk (KH.inv_mem k.2), by group⟩
    rw [hfun, avg_const]; simp

end GlobalTheory.TwOrbGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicatorStatement
open Filter GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegralSummand_goodPlace_indicator : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (KH : Subgroup H) (δ : H), δ ∈ KH → cptPart (twCent (MonoidHom.id H) δ) ≤ KH → (∀ g : H, g⁻¹ * δ * g ∈ KH → ∃ t ∈ twCent (MonoidHom.id H) δ, t⁻¹ * g ∈ KH) → ∀ x : H, GlobalTheory.TwOrbConj.summand (MonoidHom.id H) KH δ ((KH : Set H).indicator 1) x = if ∃ t ∈ twCent (MonoidHom.id H) δ, ∃ k ∈ KH, x = t * k then 1 else 0 := by
  first | exact @GlobalTheory.TwOrbGood.summand_goodplace | exact GlobalTheory.TwOrbGood.summand_goodplace | (intros; apply GlobalTheory.TwOrbGood.summand_goodplace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HomDescent

variable {S : Scheme.{0}}

theorem isPullback_whiskerLeft' (A : Over S) {Y Z : Over S} (q : Y ⟶ Z) :
    IsPullback (A ◁ q).left (snd A Y).left (snd A Z).left q.left := by
  have h1 : IsPullback (fst A Z).left (snd A Z).left A.hom Z.hom := IsPullback.of_hasPullback A.hom Z.hom
  have h2 : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback A.hom Y.hom
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerLeft_fst, Over.w q]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

theorem isPullback_whiskerRight' {A A' : Over S} (q : A ⟶ A') (Y : Over S) :
    IsPullback (q ▷ Y).left (fst A Y).left (fst A' Y).left q.left := by
  have h1 : IsPullback (snd A' Y).left (fst A' Y).left Y.hom A'.hom :=
    (IsPullback.of_hasPullback A'.hom Y.hom).flip
  have h2 : IsPullback (snd A Y).left (fst A Y).left Y.hom A.hom := (IsPullback.of_hasPullback A.hom Y.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w q]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem epi_of_isPullback {X Y P Q : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {u : P ⟶ Q} {v : P ⟶ X} {t : Q ⟶ Y} (hp : IsPullback u v t π) : Epi u := by
  have := GlobalTheory.GaloisCartDesc.epi_pullback_fst h t
  rw [← hp.isoPullback_hom_fst]
  infer_instance

theorem exists_desc : ∀ (S : Scheme.{0}) (A A' B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj B] (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ f : A ⟶ B, IsMonHom f → (∀ h ∈ H, h ≫ f = 1) → ∃ f' : A' ⟶ B, IsMonHom f' ∧ ψ ≫ f' = f := by
  intro S A A' B _ _ _ _ _ H ψ hψ hG f hf hH
  have inv : ∀ a : H, (GlobalTheory.UPel.HT.Hecke.transl a.1).left ≫ f.left = f.left := by
    intro a
    rw [← Over.comp_left]
    congr 1
    rw [GlobalTheory.UPel.HT.Hecke.transl, mul_comp, Category.id_comp, Category.assoc, hH a.1 a.2, comp_one, _root_.mul_one]
  obtain ⟨g, hg, -⟩ := hG.existsUnique_desc f.left inv
  have eψ : Epi ψ.left := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hG
  have w : g ≫ B.hom = A'.hom := by
    rw [← cancel_epi ψ.left, reassoc_of% hg, Over.w, Over.w]
  let f' : A' ⟶ B := Over.homMk g w
  have hf' : ψ ≫ f' = f := Over.OverMorphism.ext hg
  refine ⟨f', ⟨?_, ?_⟩, hf'⟩
  · rw [← IsMonHom.one_hom ψ, Category.assoc, hf', IsMonHom.one_hom]
  · have e1 : Epi (ψ ▷ A).left := epi_of_isPullback hG (isPullback_whiskerRight' ψ A)
    have e2 : Epi (A' ◁ ψ).left := epi_of_isPullback hG (isPullback_whiskerLeft' A' ψ)
    have e : Epi (ψ ⊗ₘ ψ).left := by
      rw [MonoidalCategory.tensorHom_def, Over.comp_left]; infer_instance
    apply Over.OverMorphism.ext
    rw [← cancel_epi (ψ ⊗ₘ ψ).left, ← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [← Category.assoc, ← IsMonHom.mul_hom ψ, Category.assoc, hf', IsMonHom.mul_hom, ← hf',
      ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]

end GlobalTheory.HomDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_hom_quotient_galois_group_scheme : ∀ (S : Scheme.{0}) (A A' B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj B] (H : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ f : A ⟶ B, IsMonHom f → (∀ h ∈ H, h ≫ f = 1) → ∃ f' : A' ⟶ B, IsMonHom f' ∧ ψ ≫ f' = f := by
  first | exact @GlobalTheory.HomDescent.exists_desc | exact GlobalTheory.HomDescent.exists_desc | (intros; apply GlobalTheory.HomDescent.exists_desc; all_goals assumption)
end
end
