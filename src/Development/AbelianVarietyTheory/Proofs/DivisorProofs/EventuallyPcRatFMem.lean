module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwU

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem gl_ext {k k' : GL (Fin n) (Af E)}
    (h : ∀ v : Pl E, GeneralLinearGroup.map (pLoc E v) k = GeneralLinearGroup.map (pLoc E v) k') : k = k' := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun v => congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j) (h v)

theorem cPl_cPl (v : Pl E) : cPl E (cPl E v) = v := GlobalTheory.ThetaPull.conjSrc_conjSrc v

theorem pc_thF (v : Pl E) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) = thetaGL n (RingHom.id _)
      (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv v)
        (GeneralLinearGroup.map (pLoc E (cPl E v)) x)) :=
  GlobalTheory.ThetaPull.map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl)
    (GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) x)

theorem thF_thF (x : GL (Fin n) (Af E)) : thF E n (thF E n x) = x :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun y => GlobalTheory.ThetaPull.cFin_cFin y) x

theorem pc_ratF (v : Pl E) (δ : GL (Fin n) E) :
    GeneralLinearGroup.map (pLoc E v) (ratF E n δ) = GeneralLinearGroup.map (algebraMap E (v.adicCompletion E)) δ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem continuous_pc (v : Pl E) : Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E v)) :=
  Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval v))

theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2

theorem mem_GLint {L : Type} [Field L] (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_pc_ratF_mem (g : GL (Fin n) E) : ∀ᶠ v : Pl E in cofinite,
    GeneralLinearGroup.map (pLoc E v) (ratF E n g) ∈ GlobalTheory.LFun.KGL v (n := n) := by
  have h : ∀ g : GL (Fin n) E, ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]; exact fun i j => eventually_int _
  filter_upwards [h g, h g⁻¹] with w a b
  rw [pc_ratF]
  exact mem_GLint _ _ a (by rw [← map_inv]; exact b)

end GlobalTheory.EulerTwU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK

theorem exists_at_evI_piInf_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) :
    ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) z ∧ ∀ w, piInf (τ w) z = c w := by
  classical
  have := h.1
  have := h.2.1

  have hloc : ∀ w : InfinitePlace F, ∃ (α : E) (a b : w.Completion),
      InfinitePlace.Completion.extensionEmbedding w a +
        InfinitePlace.Completion.extensionEmbedding w b * (τ w).1 α = c w := by
    intro w
    have hα : ∃ α : E, ((τ w).1 α).im ≠ 0 := by
      by_contra hn
      push Not at hn
      refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (τ w).1)))
        (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
      exact Complex.conj_eq_iff_im.2 (hn x)
    obtain ⟨α, hα⟩ := hα
    have hs := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
    obtain ⟨a, ha⟩ := hs ((c w).re - (c w).im / ((τ w).1 α).im * ((τ w).1 α).re)
    obtain ⟨b, hb⟩ := hs ((c w).im / ((τ w).1 α).im)
    refine ⟨α, a, b, ?_⟩
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w),
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w), ha, hb]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]; field_simp; ring
  choose α a b hab using hloc
  let δ : ∀ w : InfinitePlace F, w.Completion → AF F := fun w x =>
    ((Pi.single w x : ∀ v : InfinitePlace F, v.Completion), 0)
  have hδ : ∀ (u : AF F), evI F u = 0 → ∀ w x, u * δ w x = 0 := by
    intro u hu w x
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  have hp : ∀ w v x (e : E), piInf (τ w) (δ v x ⊗ₜ[F] e) =
      InfinitePlace.Completion.extensionEmbedding w ((Pi.single v x : ∀ v : InfinitePlace F, v.Completion) w)
        * (τ w).1 e := fun _ _ _ _ => rfl
  refine ⟨∑ w, (δ w (a w) ⊗ₜ[F] (1 : E) + δ w (b w) ⊗ₜ[F] α w), fun u hu => ?_, fun w => ?_⟩
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hδ u hu, hδ u hu,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.sum_eq_single w]
      · rw [map_add (f := _), hp, hp, Pi.single_eq_same, Pi.single_eq_same, map_one, mul_one, hab]
      · intro v _ hv
        rw [map_add (f := _), hp, hp, Pi.single_eq_of_ne hv.symm, Pi.single_eq_of_ne hv.symm, map_zero, zero_mul, zero_mul, add_zero]
      · simp

end GlobalTheory.ThK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtHolomorphicFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtHolomorphicFrameChange
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm

theorem chernAt_changeFrame : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H K A : V n → Matrix r r ℂ) (v : V n), MContDiffAt 2 K v → IsUnit (K v).det → (∀ i j, AnalyticAt ℂ (fun w => A w i j) v) → IsUnit (A v).det → (H =ᶠ[𝓝 v] fun w => chg (A w) (K w)) → ∀ j, chernAt H v j = chernAt K v j := by
  intro n r _ _ H K A v hK hKu hg hAu hH j
  have hconj : ∀ (M P Q : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)), Q * P = 1 →
      (Q * M * P).charpolyRev = M.charpolyRev := by
    intro M P Q hQP
    have hQP' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
      rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
    have e : (1 : Matrix r r (Polynomial (MvPolynomial (Fin n × Fin n) ℂ))) -
        (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) • (Q * M * P).map Polynomial.C =
        Q.map Polynomial.C * (1 - (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) •
          M.map Polynomial.C) * P.map Polynomial.C := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP',
        Matrix.mul_smul, Matrix.smul_mul]
    rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
      ← Matrix.det_mul, hQP', Matrix.det_one, one_mul]
  have hsum : ∀ G : V n → Matrix r r ℂ, curvPoly G v =
      ∑ a, ∑ b, (MvPolynomial.X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
        (curv G v (coordVec a) (coordVec b)).map MvPolynomial.C := by
    intro G
    ext i j
    simp [curvPoly, Matrix.sum_apply, mul_comm]
  have hA : MContDiffAt 2 A v := fun a b => (hg a b).contDiffAt.restrict_scalars ℝ
  have hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0 := by
    have hev : ∀ᶠ x in 𝓝 v, ∀ a b, AnalyticAt ℂ (fun w => A w a b) x :=
      eventually_all.2 fun a => eventually_all.2 fun b => (hg a b).eventually_analyticAt
    filter_upwards [hev] with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b).differentiableAt]
    rfl
  have hGe : H =ᶠ[𝓝 v] fun u => (A u)ᵀ * K u * (A u)ᴴᵀ := hH
  have hcurv : ∀ ξ η, curv H v ξ η = (A v)⁻¹ * curv K v ξ η * A v :=
    fun ξ η => by rw [curv_congr hGe, curv_changeFrame hK hKu hA hAu hA0]
  have key : curvPoly H v = ((A v)⁻¹).map MvPolynomial.C * curvPoly K v * (A v).map MvPolynomial.C := by
    rw [hsum, hsum]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, hcurv]
  have key2 : chernPoly H v j = chernPoly K v j := by
    rw [chernPoly, chernPoly, key, show ∀ (Q M P : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)),
      -(Q * M * P) = Q * (-M) * P from fun Q M P => by rw [Matrix.mul_neg, Matrix.neg_mul], hconj]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hAu, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [chernAt, chernAt, key2]

end GlobalTheory.CxForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtHolomorphicFrameChangeStatement
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormOfGramMatrixAt_holomorphic_frameChange : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H K A : V n → Matrix r r ℂ) (v : V n), MContDiffAt 2 K v → IsUnit (K v).det → (∀ i j, AnalyticAt ℂ (fun w => A w i j) v) → IsUnit (A v).det → (H =ᶠ[𝓝 v] fun w => chg (A w) (K w)) → ∀ j, chernAt H v j = chernAt K v j := by
  first | exact @GlobalTheory.CxForm.chernAt_changeFrame | exact GlobalTheory.CxForm.chernAt_changeFrame | (intros; apply GlobalTheory.CxForm.chernAt_changeFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMulMemHatId
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.BlockIdx

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))

theorem gen_mem_hatId {b : 𝓞 D.host.E} (hb : b ∈ 𝔪) {s : AE D} (hs : s ∈ OhE D) :
    inc D (b : D.host.E) * s ∈ hatId D 𝔪 :=
  AddSubgroup.subset_closure ⟨b, hb, s, hs, rfl⟩

theorem mul_mem_hatId {s : AE D} (hs : s ∈ OhE D) {x : AE D} (hx : x ∈ hatId D 𝔪) :
    s * x ∈ hatId D 𝔪 := by
  have h : AddSubgroup.closure {y | ∃ b ∈ 𝔪, ∃ t ∈ OhE D, y = inc D (b : D.host.E) * t} ≤
      (hatId D 𝔪).comap (AddMonoidHom.mulLeft s) := by
    rw [AddSubgroup.closure_le]
    rintro y ⟨b, hb, t, ht, rfl⟩
    show s * (inc D (b : D.host.E) * t) ∈ hatId D 𝔪
    rw [mul_left_comm]
    exact gen_mem_hatId D 𝔪 hb (mul_mem hs ht)
  exact h hx

theorem absNorm_mul_mem_hatId {w : AE D} (hw : w ∈ OhE D) :
    (Ideal.absNorm 𝔪 : AE D) * w ∈ hatId D 𝔪 := by
  have := gen_mem_hatId D 𝔪 (Ideal.absNorm_mem 𝔪) hw
  simpa using this

theorem exists_red (h𝔪 : 𝔪 ≠ ⊥) (x : AE D) (hx : x ∈ OhE D) :
    ∃ r : 𝓞 D.host.E, x - inc D (r : D.host.E) ∈ hatId D 𝔪 := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  obtain ⟨r, hr, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D _ hn x hx
  refine ⟨⟨r, (mem_integralClosure_iff ℤ _).2 hr⟩, ?_⟩
  show x - inc D r ∈ hatId D 𝔪
  rw [e, add_sub_cancel_left]
  exact absNorm_mul_mem_hatId D 𝔪 hw

theorem mem_blockJ_of_congr {a N : ℕ} {k₁ k₂ : GA D N} (h₁ : k₁ ∈ intG D N) (h₂ : k₂ ∈ intG D N)
    (h : ∀ i j, ((k₂ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      ((k₁ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪) :
    k₁⁻¹ * k₂ ∈ blockJ D 𝔪 a N := by
  apply Subgroup.subset_closure
  refine ⟨(intG D N).mul_mem ((intG D N).inv_mem h₁) h₂, fun i j hj hi => ?_⟩
  have hij : i ≠ j := fun e => by subst e; omega
  have hinv := (mem_intG k₁).1 h₁
  have e : (((k₁⁻¹ * k₂ : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      (((k₁ : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        (((k₂ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) -
          ((k₁ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) + 1 := by
    rw [Matrix.mul_sub, Units.inv_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    abel
  rw [e, Matrix.add_apply, Matrix.one_apply_ne hij, add_zero, Matrix.mul_apply]
  exact AddSubgroup.sum_mem _ fun l _ => mul_mem_hatId D 𝔪 ((hinv i l).2) (h l j)

end GlobalTheory.BotPairSmall.BlockIdx

namespace GlobalTheory.BotPairSmall


open BlockIdx in
theorem blockJ_relIndex : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (a N : ℕ),
    (GlobalTheory.BotPairSmall.blockJ D 𝔪 a N).relIndex (intG D N) ≠ 0 ∧
      (GlobalTheory.BotPairSmall.blockJ D 𝔪 a N).relIndex (intG D N) ≤ Ideal.absNorm 𝔪 ^ (N ^ 2) := by
  intro D 𝔪 h𝔪 a N
  have hent : ∀ k : intG D N, ∀ i j,
      (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D :=
    fun k i j => (((mem_intG _).1 k.2) i j).1
  choose r hr using fun (k : intG D N) i j => exists_red D 𝔪 h𝔪 _ (hent k i j)
  let H := (blockJ D 𝔪 a N).subgroupOf (intG D N)
  let f : (intG D N ⧸ H) → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) :=
    fun q i j => Ideal.Quotient.mk 𝔪 (r q.out i j)
  have hf : Function.Injective f := by
    intro q₁ q₂ e
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv]
    refine mem_blockJ_of_congr D 𝔪 q₁.out.2 q₂.out.2 fun i j => ?_
    have e' : Ideal.Quotient.mk 𝔪 (r q₁.out i j) = Ideal.Quotient.mk 𝔪 (r q₂.out i j) :=
      congrFun (congrFun e i) j
    rw [Ideal.Quotient.eq] at e'
    have := sub_mem (sub_mem (hr q₂.out i j) (gen_mem_hatId D 𝔪 e' (one_mem (OhE D)))) (hr q₁.out i j)
    convert this using 1
    push_cast
    rw [map_sub]
    ring
  have hcard : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; simpa [Ideal.absNorm_eq_zero_iff] using h𝔪)
  haveI : Finite (intG D N ⧸ H) := Finite.of_injective f hf
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  show H.index ≤ _
  rw [Subgroup.index]
  calc Nat.card (intG D N ⧸ H) ≤ Nat.card (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) := Nat.card_le_card_of_injective f hf
    _ = Ideal.absNorm 𝔪 ^ (N ^ 2) := by
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, hcard, ← pow_mul, sq]

end GlobalTheory.BotPairSmall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPowerHermitianFormDensity
open GlobalTheory.CxForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DensPow

variable {n : ℕ}

theorem ι_mul_ι_mul_ι_mul_ι_left (u w w' : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w') = (0 : Alt n) := by
  have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) w u)
  calc _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) * ExteriorAlgebra.ι ℂ w' := by
          simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ w') := by
          rw [h]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

theorem ι_mul_ι_mul_ι_mul_ι_right (u u' w : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ u' * ExteriorAlgebra.ι ℂ w) = (0 : Alt n) := by
  have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) w u')
  calc _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u') * ExteriorAlgebra.ι ℂ w := by
          simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ u' * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ w)) := by
          rw [h]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

def row (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n where
  toFun w := ∑ b, w b • sym (a, b)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum, smul_smul]

theorem coe_row (a : Fin n) (w : Fin n → ℂ) :
    (row a w : Alt n) = dz a * ExteriorAlgebra.ι ℂ (∑ b, w b • Pi.single (Sum.inr b) (1 : ℂ)) := by
  simp [row, sym, dzb, Finset.mul_sum, mul_smul_comm]

theorem row_mul_row (a : Fin n) (w : Fin n → ℂ) : row a w * row a w = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_row, dz]
  exact ι_mul_ι_mul_ι_mul_ι_left _ _ _

theorem row_mul_row_of_ne {a a' : Fin n} (w : Fin n → ℂ) : row a w * row a' w = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_row, coe_row, dz, dz]
  exact ι_mul_ι_mul_ι_mul_ι_right _ _ _

def altRows (n : ℕ) : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] Ev n where
  toMultilinearMap := (MultilinearMap.mkPiAlgebra ℂ (Fin n) (Ev n)).compLinearMap row
  map_eq_zero_of_eq' v i j hij hne := by
    change ∏ a, row a (v a) = 0
    rw [← Finset.mul_prod_erase Finset.univ (fun a => row a (v a)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (fun a => row a (v a))
        (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩), ← mul_assoc, hij, row_mul_row_of_ne, zero_mul]

theorem altRows_apply (v : Fin n → Fin n → ℂ) : altRows n v = ∏ a, row a (v a) := by
  first
  | rfl
  | simp only [altRows, AlternatingMap.coe_mk, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

theorem alt_eq_det_smul {K M N : Type} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {m : ℕ} (e : Module.Basis (Fin m) K M)
    (f : M [⋀^Fin m]→ₗ[K] N) (h : Fin m → M) : f h = e.det h • f e := by
  have key : f = (LinearMap.toSpanSingleton K N (f e)).compAlternatingMap e.det := by
    refine e.ext_alternating (fun v hv => ?_)
    have hb : Function.Bijective v := Finite.injective_iff_bijective.1 hv
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective v hb
    have hσ : (fun i => e (v i)) = (⇑e) ∘ ⇑σ := rfl
    rw [hσ, LinearMap.compAlternatingMap_apply, LinearMap.toSpanSingleton_apply,
      AlternatingMap.map_perm, AlternatingMap.map_perm, e.det_self, Units.smul_def,
      Units.smul_def, smul_one_smul]
  rw [DFunLike.congr_fun key h]
  rfl

theorem prod_row (H : Matrix (Fin n) (Fin n) ℂ) : ∏ a, row a (H a) = H.det • ∏ a, sym (a, a) := by
  have h1 : ∏ a, row a (H a) = altRows n (fun a b => H a b) := (altRows_apply _).symm
  rw [h1, alt_eq_det_smul (Pi.basisFun ℂ (Fin n)), Pi.basisFun_det, altRows_apply]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  simp [row, Pi.single_apply]

theorem add_pow_of_mul_self {R : Type*} [CommRing R] {x : R} (hx : x * x = 0) (y : R) (m : ℕ) :
    (x + y) ^ (m + 1) = y ^ (m + 1) + ((m : R) + 1) * x * y ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((m : R) + 1) * y ^ m * hx

theorem sum_pow_card {R ι : Type*} [CommRing R] [DecidableEq ι] (f : ι → R) (hf : ∀ a, f a * f a = 0) (s : Finset ι) :
    (∀ m, (∑ a ∈ s, f a) ^ (s.card + 1 + m) = 0) ∧ (∑ a ∈ s, f a) ^ s.card = (s.card.factorial : R) * ∏ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun m => by simp, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine ⟨fun m => ?_, ?_⟩
    · rw [show s.card + 1 + 1 + m = (s.card + 1 + m) + 1 by omega, add_pow_of_mul_self (hf a),
        show s.card + 1 + m + 1 = s.card + 1 + (m + 1) by omega, ih.1, ih.1]
      simp
    · rw [add_pow_of_mul_self (hf a), show s.card + 1 = s.card + 1 + 0 by rfl, ih.1, ih.2, Nat.factorial_succ]
      push_cast
      ring

theorem dens_smul (c : ℂ) (x : Alt n) : dens (c • x) = c * dens x := by
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

theorem vol_eq_smul_prod (n : ℕ) : vol n = (Complex.I / 2) ^ n • ∏ a, sym (a, a) := by
  simp only [vol, Algebra.smul_def, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    map_pow]

theorem dens_pow (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CxForm.dens (((∑ a, ∑ b, H a b • GlobalTheory.CxForm.sym (a, b) : GlobalTheory.CxForm.Ev n) ^ n : GlobalTheory.CxForm.Ev n) :
      GlobalTheory.CxForm.Alt n) = (n.factorial : ℂ) * H.det / (Complex.I / 2) ^ n := by
  have hω : (∑ a, ∑ b, H a b • sym (a, b) : Ev n) = ∑ a, row a (H a) := by simp [row]
  have hp : (∑ a, row a (H a)) ^ n = (n.factorial : Ev n) * ∏ a, row a (H a) := by
    simpa using (sum_pow_card (fun a => row a (H a)) (fun a => row_mul_row a _) Finset.univ).2
  have hP : (n.factorial : Ev n) * ∏ a, row a (H a) = ((n.factorial : ℂ) * H.det) • ∏ a, sym (a, a) := by
    rw [prod_row, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h1 := dens_vol n
  rw [vol_eq_smul_prod, Subalgebra.coe_smul, dens_smul] at h1
  rw [hω, hp, hP, Subalgebra.coe_smul, dens_smul, div_eq_mul_inv, eq_inv_of_mul_eq_one_right h1]

end GlobalTheory.CxForm.DensPow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelsDifferBySymplecticMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelsDifferBySymplecticMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

namespace GlobalTheory

theorem goodModel_coords_rat_symplectic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood ψ → M₁.IsGood ψ → ∃ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 ∧ ∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr) := by
  intro F E _ _ _ _ _ σ ψ n d X W M M₁ hM hM₁
  classical
  let ι := algebraMap F (AF F)
  have hι : Function.Injective ι := AdeleRing.algebraMap_injective (𝓞 F) F
  let sp := LinearEquiv.sumArrowLequivProdArrow (Fin n × Fin d) (Fin n × Fin d) (AF F) (AF F)
  let Φ₀ := M.co.e.trans sp.symm
  let Φ₁ := M₁.co.e.trans sp.symm
  have hΦ₀ : ∀ u, Φ₀ u = Sum.elim (M.co.e u).1 (M.co.e u).2 := fun u => rfl
  have hΦ₁ : ∀ u, Φ₁ u = Sum.elim (M₁.co.e u).1 (M₁.co.e u).2 := fun u => rfl
  let A : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) (AF F) :=
    LinearMap.toMatrix' ((Φ₀.symm.trans Φ₁ : _ ≃ₗ[AF F] _) : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) →ₗ[AF F] _)
  have hA : ∀ u, A *ᵥ Φ₀ u = Φ₁ u := by
    intro u; simp [A, LinearMap.toMatrix'_mulVec]

  have hspan : Submodule.span (AF F) (Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) = ⊤ := by
    rw [eq_top_iff]; intro U _
    rw [Matrix.matrix_eq_sum_single U]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    generalize U i j = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      have : Matrix.single i j (a ⊗ₜ[F] e : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = a • incM F (Matrix.single i j e) := by
        ext k l
        simp only [incM, Matrix.single_apply, Matrix.smul_apply, Matrix.map_apply, inclR]
        split_ifs
        · simp [TensorProduct.smul_tmul']
        · simp
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add x y hx hy => rw [Matrix.single_add]; exact Submodule.add_mem _ hx hy
  have hspan' : Submodule.span (AF F) (Φ₀.toLinearMap '' Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) = ⊤ := by
    rw [Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  have hrat0 : ∀ x : Matrix (Fin n) (Fin d) E, ∃ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, Φ₀ (incM F x) = fun i => ι (w i) := by
    intro x; obtain ⟨y, z, h⟩ := hM.rat x
    refine ⟨Sum.elim y z, ?_⟩; funext i; rw [hΦ₀, h]; cases i <;> rfl
  have hrat1 : ∀ x : Matrix (Fin n) (Fin d) E, ∃ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, Φ₁ (incM F x) = fun i => ι (w i) := by
    intro x; obtain ⟨y, z, h⟩ := hM₁.rat x
    refine ⟨Sum.elim y z, ?_⟩; funext i; rw [hΦ₁, h]; cases i <;> rfl
  let G : Set ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F) := {w | ∃ x, Φ₀ (incM F x) = fun i => ι (w i)}
  have hG : Submodule.span F G = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let c : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F := fun i => f (fun j => if i = j then 1 else 0)
    have hfc : ∀ w, f w = ∑ i, w i * c i := by
      intro w; rw [LinearMap.pi_apply_eq_sum_univ f w]; simp [c, smul_eq_mul]
    have hP : ∀ V ∈ Submodule.span (AF F) (Φ₀.toLinearMap '' Set.range (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))),
        ∑ i, V i * ι (c i) = 0 := by
      intro V hV
      induction hV using Submodule.span_induction with
      | mem V hV =>
        obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hV
        obtain ⟨w, hw⟩ := hrat0 x
        have h1 := hfk (Submodule.subset_span (show w ∈ G from ⟨x, hw⟩))
        rw [LinearMap.mem_ker, hfc] at h1
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap, hw, ← map_mul, ← map_sum, h1, map_zero]
      | zero => simp
      | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
      | smul a x _ hx => simp [mul_assoc, ← Finset.mul_sum, hx]
    have hc : ∀ i, c i = 0 := by
      intro i
      have h1 := hP (Pi.single i 1) (by rw [hspan']; trivial)
      simp [Pi.single_apply] at h1
      exact hι (by simpa using h1)
    exact hf0 (LinearMap.ext fun w => by simp [hfc, hc])

  have hrat : ∀ w : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F, ∃ q : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F,
      A *ᵥ (fun i => ι (w i)) = fun i => ι (q i) := by
    intro w
    have hw : w ∈ Submodule.span F G := hG ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx⟩ := hw
      obtain ⟨q, hq⟩ := hrat1 x
      exact ⟨q, (congrArg (A *ᵥ ·) hx).symm.trans ((hA _).trans hq)⟩
    | zero => exact ⟨0, by funext i; simp [Matrix.mulVec, dotProduct]⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx; obtain ⟨q, hq⟩ := hy
      refine ⟨p + q, ?_⟩
      have : (fun i => ι ((x + y) i)) = (fun i => ι (x i)) + (fun i => ι (y i)) := by funext i; simp
      rw [this, Matrix.mulVec_add, hp, hq]; funext i; simp
    | smul c x _ hx =>
      obtain ⟨p, hp⟩ := hx
      refine ⟨c • p, ?_⟩
      have : (fun i => ι ((c • x) i)) = ι c • (fun i => ι (x i)) := by funext i; simp
      rw [this, Matrix.mulVec_smul, hp]; funext i; simp
  choose q hq using fun j : (Fin n × Fin d) ⊕ (Fin n × Fin d) => hrat (Pi.single j 1)
  let a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F := Matrix.of fun i j => q j i
  have haA : a.map ι = A := by
    ext i j
    have h1 : A *ᵥ Pi.single j 1 = fun i => ι (q j i) := by
      rw [← hq j]; congr 1; funext k; simp [Pi.single_apply]
    have h2 := congrFun h1 i
    rw [Matrix.mulVec_single_one] at h2
    simpa [a] using h2.symm
  have hstd : ∀ w w' : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F,
      w ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ w') = (w ∘ Sum.inl) ⬝ᵥ (w' ∘ Sum.inr) - (w' ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr) := by
    intro w w'
    rw [Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, mul_comm, sub_eq_add_neg]
  have hform : ∀ u u', Φ₁ u ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ Φ₁ u') = Φ₀ u ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 *ᵥ Φ₀ u') := by
    intro u u'
    rw [hstd, hstd, hΦ₀, hΦ₀, hΦ₁, hΦ₁]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [← M.co.form, ← M₁.co.form]
  have hsympA : Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A = Matrix.fromBlocks 0 1 (-1) 0 := by
    ext i j
    have key : ∀ N : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) (AF F),
        N i j = Pi.single i 1 ⬝ᵥ (N *ᵥ Pi.single j 1) := by
      intro N; simp [Matrix.mulVec_single_one]
    rw [key (Aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * A), key (Matrix.fromBlocks 0 1 (-1) 0)]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e1 : ∀ s, A *ᵥ s = Φ₁ (Φ₀.symm s) := fun s => by rw [← hA, LinearEquiv.apply_symm_apply]
    rw [e1, e1, hform]
    simp
  refine ⟨a, ?_, ?_⟩
  · apply Matrix.map_injective hι
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.fromBlocks_map]
    rw [haA]
    simpa [Matrix.map_zero, Matrix.map_one, Matrix.map_neg] using hsympA
  · intro u
    rw [show a.map (algebraMap F (AF F)) = A from haA, ← hΦ₀, hA, hΦ₁]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelsDifferBySymplecticMatrixStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_models_differ_by_symplectic_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood ψ → M₁.IsGood ψ → ∃ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 ∧ ∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr) := by
  first | exact @GlobalTheory.goodModel_coords_rat_symplectic | exact GlobalTheory.goodModel_coords_rat_symplectic | (intros; apply GlobalTheory.goodModel_coords_rat_symplectic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LeviPlane

variable {R : Type} [CommRing R] (c : R →+* R) {n : ℕ}

def fm (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

def lev (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) : Matrix (Fin n) (Fin n) R :=
  1 + (s - 1) • Matrix.vecMulVec X (J *ᵥ fun i => c (Y i)) - (r - 1) • Matrix.vecMulVec Y (J *ᵥ fun i => c (X i))

theorem lev_mulVec (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) (w : Fin n → R) :
    lev c J X Y s r *ᵥ w = w + ((s - 1) * fm c J w Y) • X - ((r - 1) * fm c J w X) • Y := by
  ext i
  simp only [lev, fm, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, dotProduct_comm w]
  ring

theorem fm_skew (hc : ∀ x, c (c x) = x) (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, c (J j i) = -J i j)
    (p q : Fin n → R) : fm c J p q = -c (fm c J q p) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [fm, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

variable {c}

theorem fm_add_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u + u') v = fm c J u v + fm c J u' v := by
  simp [fm, add_dotProduct]

theorem fm_sub_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u - u') v = fm c J u v - fm c J u' v := by
  simp [fm, sub_dotProduct]

theorem fm_smul_left (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J (a • u) v = a * fm c J u v := by
  simp [fm, smul_dotProduct]

theorem fm_add_right (J : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) : fm c J u (v + v') = fm c J u v + fm c J u v' := by
  have : (fun i => c ((v + v') i)) = (fun i => c (v i)) + fun i => c (v' i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_add, dotProduct_add]

theorem fm_sub_right (J : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) : fm c J u (v - v') = fm c J u v - fm c J u v' := by
  have : (fun i => c ((v - v') i)) = (fun i => c (v i)) - fun i => c (v' i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_sub, dotProduct_sub]

theorem fm_smul_right (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J u (a • v) = c a * fm c J u v := by
  have : (fun i => c ((a • v) i)) = c a • fun i => c (v i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem entry (J M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Mᵀ * J * M.map c) i j = fm c J (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp only [fm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
variable {R : Type} [CommRing R] {c : R →+* R} {n : ℕ}

section Plane
variable (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
  (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1)
include hc hJ hxx hyy hxy

theorem fm_yx : fm c J Y X = -1 := by rw [fm_skew c hc J hJ, hxy, map_one]

theorem lev_mul (s r s' r' : R) : lev c J X Y s r * lev c J X Y s' r' = lev c J X Y (s * s') (r * r') := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have key : ∀ w, (lev c J X Y s r * lev c J X Y s' r') *ᵥ w = lev c J X Y (s * s') (r * r') *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_mulVec, lev_mulVec, lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, hxx, hyy, hxy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem lev_one : lev c J X Y 1 1 = 1 := by simp [lev]

theorem lev_unitary (s r : R) (hsr : s * c r = 1) :
    (lev c J X Y s r)ᵀ * J * (lev c J X Y s r).map c = J := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have hrs : r * c s = 1 := by
    have := congrArg c hsr; rw [map_mul, hc, map_one] at this; rw [mul_comm]; exact this
  have key : ∀ u v, fm c J (lev c J X Y s r *ᵥ u) (lev c J X Y s r *ᵥ v) = fm c J u v := by
    intro u v
    rw [lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, fm_add_right, fm_sub_right, fm_smul_right, hxx, hyy, hxy, hyx]
    rw [fm_skew c hc J hJ X v, fm_skew c hc J hJ Y v]
    simp only [map_mul, map_sub, map_one, map_neg]
    linear_combination (-(fm c J u Y * c (fm c J v X))) * hsr + (fm c J u X * c (fm c J v Y)) * hrs
  ext i j
  rw [entry, key]
  have h1 := entry (c := c) J 1 i j
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_one,
    Matrix.one_mulVec] at h1
  exact h1.symm

end Plane

theorem lev_X {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} (hxx : fm c J X X = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ X = s • X := by
  rw [lev_mulVec, hxx, hxy]; ext i; simp; ring

theorem lev_Y (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
    (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ Y = r • Y := by
  rw [lev_mulVec, hyy, fm_yx hc hJ hxx hyy hxy]; ext i; simp; ring

theorem lev_mul_ι {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} {k : ℕ} (ι : Matrix (Fin n) (Fin k) R)
    (hι : ∀ j, fm c J (fun i => ι i j) X = 0 ∧ fm c J (fun i => ι i j) Y = 0) (s r : R) :
    lev c J X Y s r * ι = ι := by
  ext i j
  have h := congrFun (lev_mulVec c J X Y s r (fun i => ι i j)) i
  rw [(hι j).1, (hι j).2] at h
  simp only [mul_zero, zero_smul, add_zero, sub_zero] at h
  rw [Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct] using h

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, Algebra.TensorProduct.map_tmul, h]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cAr_inclR (σ : E →ₐ[F] E) (e : E) :
    (cA σ).toRingHom (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := cA_inclR σ e

theorem fm_inc (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    fm (cA σ).toRingHom (incM F J) (incV F x) (incV F y) = inclR (F := F) (AF F) (form σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [fm, form, incV, incM, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul,
    AlgHom.coe_toRingHom, cAr_inclR, cA_inclR]

end GlobalTheory.LeviPlane
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEigenvectorUniqueUpToUnit
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.VacuumUnique

theorem vacuum_unique : ∀ {D : D7}, Inp D → ∀ {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ}, Crv D cc δ → ∀ {N N' : ℕ} {e₁ e₂ : VC D N N' → ℂ}, oddE0 D cc δ t0 N N' e₁ → oddE0 D cc δ t0 N N' e₂ → e₁ ≠ 0 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ e₂ = κ • e₁ := by
  intro D _ cc δ t0 hC N N' e₁ e₂ h₁ h₂ hne
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D N) (GlobalTheory.NormSum.VacMove.moves_one D N')
  obtain ⟨hline, -⟩ := GlobalTheory.ThetaLine.theta_line D hG1 cc δ hC N N' _ k0
  obtain ⟨c, hc⟩ := hline e₂ h₂.1 e₁ h₁.1 hne
  refine ⟨c, ?_, hc⟩
  have hn := GlobalTheory.UnitaryTheta.normSq_ne_zero D cc δ hC k0 h₁.1 hne
  have e := h₂.2.2.1.trans h₁.2.2.1.symm
  rw [hc, GlobalTheory.UnitaryTheta.normSq_smul] at e
  have h1 : ‖c‖ ^ 2 = 1 := by
    have := mul_right_cancel₀ hn (e.trans (one_mul _).symm)
    exact this
  have h0 : 0 ≤ ‖c‖ := norm_nonneg c
  nlinarith [sq_nonneg (‖c‖ - 1), sq_nonneg (‖c‖ + 1)]

end GlobalTheory.VacuumUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfHasSig
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.SigDet

theorem det_ne_zero_of_hasSig : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → M.det ≠ 0 := by
  intro n M r s h
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  set B : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm with hB
  have key : Bᵀ * M * B.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    have t1 : Bᵀ = Aᵀ.submatrix e.symm id := rfl
    have t2 : B.map star = (A.map star).submatrix id e.symm := rfl
    rw [t1, t2, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
    rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  rw [Matrix.det_neg] at hd
  simp at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

end GlobalTheory.SigDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
noncomputable section

open NumberField IsDedekindDomain Matrix GroundTheory.Automorphic UpperTheory.V.Af
open GlobalTheory.CuspRep (GA Af Ad pFin pLoc)

namespace GlobalTheory.HenQ.Basic

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem mem_KGL_iff (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K)) :
    y ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, y.val i j ∈ Formalism.UG.Ov K w) ∧ ∀ i j, (y⁻¹).val i j ∈ Formalism.UG.Ov K w := by
  rw [GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨fun i j => (z.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((z⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map (Formalism.UG.Ov K w).subtype = y.val := by ext i j; rfl
    have hN : N.map (Formalism.UG.Ov K w).subtype = (y⁻¹).val := by ext i j; rfl
    have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) => A.map (Formalism.UG.Ov K w).subtype) :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact hM

end GlobalTheory.HenQ.Basic
end
end
