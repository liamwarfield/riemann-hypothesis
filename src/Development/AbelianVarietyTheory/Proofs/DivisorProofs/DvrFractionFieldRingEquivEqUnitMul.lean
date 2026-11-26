module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesDominantWeightIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimFieldBaseChangeLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMaxPrincipleWeightedFiniteTypeInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionFieldRingEquivEqUnitMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionFieldRingEquivEqUnitMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open IsLocalRing in
theorem _root_.GlobalTheory.dvr_fractionField_ringEquiv_eq_mul :
    ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (σ : K' ≃+* K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → ∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l := by
  intro W K' _ _ _ _ _ _ σ h₁ h₂ l hl
  classical
  have inj := IsFractionRing.injective W K'
  choose f hf using h₁
  choose g hg using h₂
  let F : W →+* W :=
    { toFun := f
      map_one' := inj (by simp [← hf])
      map_mul' := fun x y => inj (by simp [← hf])
      map_zero' := inj (by simp [← hf])
      map_add' := fun x y => inj (by simp [← hf]) }
  let G : W →+* W :=
    { toFun := g
      map_one' := inj (by simp [← hg])
      map_mul' := fun x y => inj (by simp [← hg])
      map_zero' := inj (by simp [← hg])
      map_add' := fun x y => inj (by simp [← hg]) }
  let τ : W ≃+* W := RingEquiv.ofRingHom F G
    (by ext x; exact inj (by simp [F, G, ← hg, ← hf]))
    (by ext x; exact inj (by simp [F, G, ← hg, ← hf]))
  have hτ : ∀ x, τ x = f x := fun x => rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hτϖ : Associated ϖ (τ ϖ) :=
    IsDiscreteValuationRing.associated_of_irreducible W hϖ
      ((MulEquiv.irreducible_iff (f := τ.toMulEquiv)).2 hϖ)
  have assoc : ∀ x : W, x ≠ 0 → Associated x (f x) := by
    intro x hx
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [← hτ, map_mul, map_pow]
    refine Associated.mul_mul ?_ hτϖ.pow_pow
    exact (associated_one_iff_isUnit.2 u.isUnit).trans
      (associated_one_iff_isUnit.2 ((Units.map τ.toMonoidHom u).isUnit)).symm
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) l
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hl
  obtain ⟨c, hc⟩ := assoc a ha0
  obtain ⟨d, hd⟩ := assoc b hb0
  refine ⟨c * ↑d⁻¹, ?_⟩
  have hbK : algebraMap W K' b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hdK : algebraMap W K' (d : W) * algebraMap W K' (↑d⁻¹ : W) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_div₀, hf, hf, ← hc, ← hd, map_mul, map_mul, map_mul]
  rw [eq_inv_of_mul_eq_one_right hdK]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionFieldRingEquivEqUnitMulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_fractionField_ringEquiv_eq_unit_mul : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (σ : K' ≃+* K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → ∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l := by
  first | exact @GlobalTheory.dvr_fractionField_ringEquiv_eq_mul | exact GlobalTheory.dvr_fractionField_ringEquiv_eq_mul | (intros; apply GlobalTheory.dvr_fractionField_ringEquiv_eq_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdeles
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

open IsDedekindDomain

namespace GlobalTheory.AdeleDenom

variable (E : Type) [Field E] [NumberField E]

def intAfter (c : Af E) : Set (Af E) := {y | ∀ v, (c * y) v ∈ v.adicCompletionIntegers E}

theorem isOpen_intAfter (c : Af E) : IsOpen (intAfter E c) :=
  (GlobalTheory.AdLat.OpenLat.isOpen_integral E).preimage (continuous_const.mul continuous_id)

theorem nat_mul_integral (k : ℕ) {x : Af E} (hx : ∀ v, x v ∈ v.adicCompletionIntegers E) (v) :
    ((k : Af E) * x) v ∈ v.adicCompletionIntegers E := by
  have hk : ((k : Af E)) v ∈ v.adicCompletionIntegers E := by
    rw [show ((k : Af E)) v = (k : v.adicCompletion E) from rfl]
    exact natCast_mem _ k
  exact mul_mem hk (hx v)

theorem exists_nat_mul_integral (a : Af E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v, ((N : Af E) * a) v ∈ v.adicCompletionIntegers E := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E (intAfter E a)
    ((isOpen_intAfter E a).mem_nhds (by intro v; simp only [mul_zero]; exact zero_mem _))
  refine ⟨N, hN, fun v => ?_⟩
  have h1 := h 1 (fun v => one_mem _) v
  rw [nsmul_eq_mul, mul_one, mul_comm] at h1
  exact h1

theorem mem_intAfter_of_dvd {d m : ℕ} (h : d ∣ m) {y : Af E} (hy : y ∈ intAfter E (d : Af E)) :
    y ∈ intAfter E (m : Af E) := by
  obtain ⟨k, rfl⟩ := h
  intro v
  have e : (((d * k : ℕ)) : Af E) * y = (k : Af E) * ((d : Af E) * y) := by
    rw [Nat.cast_mul]; ring
  rw [e]
  exact nat_mul_integral E k hy v

theorem intAfter_mono {n m : ℕ} (h : n ≤ m) :
    intAfter E ((n.factorial : ℕ) : Af E) ⊆ intAfter E ((m.factorial : ℕ) : Af E) :=
  fun _ hy => mem_intAfter_of_dvd E (Nat.factorial_dvd_factorial h) hy

theorem exists_common_denom : ∀ (E : Type) [Field E] [NumberField E] (Kf : Set (Af E)), IsCompact Kf →
    ∃ n : ℕ, 0 < n ∧ ∀ ξ : E, algebraMap E (Af E) ξ ∈ Kf → IsIntegral ℤ ((n : E) * ξ) := by
  intro E _ _ Kf hK
  have hcov : Kf ⊆ ⋃ n : ℕ, intAfter E ((n.factorial : ℕ) : Af E) := by
    intro y _
    obtain ⟨N, hN, h⟩ := exists_nat_mul_integral E y
    exact Set.mem_iUnion.mpr ⟨N, mem_intAfter_of_dvd E (Nat.dvd_factorial hN le_rfl) h⟩
  obtain ⟨n, hn⟩ := hK.elim_directed_cover _ (fun n => isOpen_intAfter E _) hcov
    (Monotone.directed_le fun a b h => intAfter_mono E h)
  refine ⟨n.factorial, Nat.factorial_pos n, fun ξ hξ => ?_⟩
  have h := hn hξ
  have hr : ((n.factorial : ℕ) : E) * ξ ∈ (algebraMap (𝓞 E) E).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one E _ fun v => ?_
    have := h v
    rw [← map_natCast (algebraMap E (Af E)), ← map_mul] at this
    rwa [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  obtain ⟨a, ha⟩ := hr
  rw [← ha]
  exact ((RingOfIntegers.isIntegral a).map (IsScalarTower.toAlgHom ℤ (𝓞 E) E))

end GlobalTheory.AdeleDenom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdelesStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_compact_finiteAdeles : ∀ (E : Type) [Field E] [NumberField E] (Kf : Set (Af E)), IsCompact Kf → ∃ n : ℕ, 0 < n ∧ ∀ ξ : E, algebraMap E (Af E) ξ ∈ Kf → IsIntegral ℤ ((n : E) * ξ) := by
  first | exact @GlobalTheory.AdeleDenom.exists_common_denom | exact GlobalTheory.AdeleDenom.exists_common_denom | (intros; apply GlobalTheory.AdeleDenom.exists_common_denom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightLieDerivativeRealEntryPolynomialFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightLieDerivativeRealEntryPolynomialFunction
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct

namespace GlobalTheory.PolyRightDeriv

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem hasDerivAt_eval {σ : Type} (δ : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (c : ℝ → σ → ℂ)
    (h : ∀ p, HasDerivAt (fun t => c t p) (MvPolynomial.eval (c 0) (δ (MvPolynomial.X p))) 0) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (c t) P) (MvPolynomial.eval (c 0) (δ P)) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.derivation_C] using hasDerivAt_const (0 : ℝ) a
  | add P Q hP hQ => simp only [map_add (f := _)]; exact hP.add hQ
  | mul_X P p hP =>
    have := hP.mul (h p)
    simp only [map_mul, MvPolynomial.eval_X, Derivation.leibniz, smul_eq_mul, map_add (f := _)]
    exact this.congr_deriv (by ring)

theorem hasDerivAt_entry {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (A * NormedSpace.exp (t • X)) i j) ((A * X) i j) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun B => (A * B) i j
      map_add' := fun B C => by simp [mul_add]
      map_smul' := fun c B => by simp }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

theorem lieDer_polyFun (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V) :
    lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := by
  classical
  funext g
  let c : ℝ → D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ :=
    fun t => realEntries θ V (g * expInf θ V (t • atPlace V τ X))
  have hc : ∀ t p, c t p = (infMat D.sp.cm.sig V.gram (θ p.1) g *
      NormedSpace.exp (t • (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) p.2.1 p.2.2 := fun t p => by
    simp only [c, realEntries]
    rw [R.2.2.2.1, (isExpFam_expInf R (t • atPlace V τ X)).2]
    rfl
  have h0 : c 0 = realEntries θ V g := funext fun p => by
    rw [hc, zero_smul, NormedSpace.exp_zero, mul_one]; rfl
  have h := hasDerivAt_eval (matDer τ X.1) c (fun p => by
    simp only [hc]
    convert hasDerivAt_entry (infMat D.sp.cm.sig V.gram (θ p.1) g)
      (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) p.2.1 p.2.2 using 1
    rw [h0, matDer_X]
    obtain ⟨τ', i, j⟩ := p
    by_cases e : τ' = τ
    · subst e
      simp [atPlace, Matrix.mul_apply, realEntries]
    · simp [atPlace, e, Pi.single_eq_of_ne e]) P
  rw [h0] at h
  exact h.deriv

end GlobalTheory.PolyRightDeriv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightLieDerivativeRealEntryPolynomialFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightLieDerivative_realEntryPolynomialFunction : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), RealPoints θ V → ∀ (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V), lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := by
  first | exact @GlobalTheory.PolyRightDeriv.lieDer_polyFun | exact GlobalTheory.PolyRightDeriv.lieDer_polyFun | (intros; apply GlobalTheory.PolyRightDeriv.lieDer_polyFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapPhi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Dict.SameExp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_objMap_phi {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S))
    (h₁ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : ∀ a, (o₁.etaA a).left ≫ m.φ = (o₂.etaA a).left) :
    ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap.φ = m.φ := by
  refine ⟨⟨m, fun a => ?_, fun a => (h₂ a).trans (Category.id_comp _).symm⟩, rfl⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
  exact (h₁ y hy).trans (Category.id_comp _).symm

theorem phi_eq_of_eq {D : Datum H} {l : Geo.Tor.Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {S : Scheme.{0}} {s : S ⟶ Sp B} {s' : Sp ℂ ⟶ Sp B'}
    {o : Obj D l b s} {o₁ : Obj D l b' s'} {y y' : Sp ℂ ⟶ S} (h : y' = y) (m : ObjMap o₁ o y)
    (m' : ObjMap o₁ o y') : m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact objMap_unique_of_field firstFiveLaws.1.serre m' m

end GlobalTheory.Dict.SameExp


set_option maxHeartbeats 1000000 in
open GlobalTheory.Dict.SameFibre GlobalTheory.Dict.SameExp GlobalTheory.UnifPoint GlobalTheory.AnVal in
theorem GlobalTheory.Dict.anFib_ex_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → l.A = 1 → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → A'.Marked mk → ∀ z, (A'.ex z).left = (A.ex z).left := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y y' A A' hs hx hL hA mk hmk hm hm' z
  have hyy : y'.x = y.x := anFib_point_eq E H Dw l Xo c hA r g X bas idx e x L y y' A A' hs hx hL mk hmk hm hm'
  obtain ⟨Φ, k₁, -, l₁, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, -, l₂, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y' A' hs hx hL
  obtain ⟨-, pos, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let σ : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  have hy : y.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y.x_over.trans (Category.id_comp _).symm
  have hy' : y'.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y'.x_over.trans (Category.id_comp _).symm
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y.x rfl rfl hy Xo.univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y'.x rfl rfl hy' Xo.univ
  obtain ⟨u₁, χ₁, b₁, f₁, h₁⟩ := exists_holUnif n₁.toSABMap Φ.toAnFr fun z hz => by rw [m₁]; exact pos z hz
  obtain ⟨u₂, χ₂, b₂, f₂, h₂⟩ := exists_holUnif n₂.toSABMap Φ'.toAnFr fun z hz => by rw [m₂]; exact pos z hz
  obtain ⟨m, hm₀⟩ := exists_sabMap_of_isAH o₁ o₂ u₁ u₂ h₁ h₂ (fun z => by rw [b₁, b₂, l₁, l₂])
    (fun z w => by rw [m₁, m₂]) (fun a => tyAct (fun j => rowType X (idx j)) a)
    (fun a z => OrthoMetric.pt_ext n₁.cart (by
      rw [f₁, Φ.lin, Over.comp_left, Over.comp_left, Category.assoc, n₁.act, ← Category.assoc, f₁]))
    (fun a z => OrthoMetric.pt_ext n₂.cart (by
      rw [f₂, Φ'.lin, Over.comp_left, Over.comp_left, Category.assoc, n₂.act, ← Category.assoc, f₂]))
  obtain ⟨k, hk⟩ := exists_objMap_phi o₁ o₂ m
    (fun a ha => by
      have c₁ : o₁.eta a = u₁.ex _ := OrthoMetric.pt_ext n₁.cart
        ((n₁.eta a).trans ((congrArg (fun q => q.left) ((hm a ha).trans (k₁ _).symm)).trans (f₁ _).symm))
      have c₂ : o₂.eta a = u₂.ex _ := OrthoMetric.pt_ext n₂.cart
        ((n₂.eta a).trans ((congrArg (fun q => q.left) ((hm' a ha).trans (k₂ _).symm)).trans (f₂ _).symm))
      rw [c₁, c₂, hm₀])
    (fun a => by
      have c₁ := o₁.etaA_ker a
      have c₂ := o₂.etaA_ker a
      rw [hA, one_smul] at c₁ c₂
      rw [c₁, c₂, ← CM.HermWeil.ex_zero u₁, ← CM.HermWeil.ex_zero u₂, hm₀])
  obtain ⟨k', hk'⟩ := ((ObjMaps.id_comp_cancel E H Dw l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y'.x (𝟙 _) n₂).1 k
  have hφ := phi_eq_of_eq ((Category.id_comp _).trans hyy) n₁ k'
  have e₁ := congrArg (fun q => q.left) (k₁ z)
  have e₂ := congrArg (fun q => q.left) (k₂ z)
  refine e₂.symm.trans (Eq.trans ?_ e₁)
  refine (f₂ z).symm.trans (Eq.trans ?_ (f₁ z))
  rw [← hm₀ z, Category.assoc, ← hk, ← hk', hφ]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxMonomialFamilyProdMemNormBallOfExponentLt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxMonomialFamilyProdMemNormBallOfExponentLt
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.BoxProd

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem mul_mem_Bl (P : Pair p) {a b a' b' : ℤ} {R R' : ℝ} (hR : 0 ≤ R) {f g : X.functionField}
    (hf : f ∈ P.Bl a b R) (hg : g ∈ P.Bl a' b' R') : f * g ∈ P.Bl (a + a') (b + b') (R * R') := by
  obtain ⟨h1, h2⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul _ _ _ P a b a' b' f g hf.1 hg.1
  refine ⟨h1, fun σ y => ?_⟩
  rw [h2 σ y]
  exact mul_le_mul (hf.2 σ y) (hg.2 σ y) (nu_nonneg _ _ _ _ _ _) hR

theorem one_mem_Bl (P : Pair p) : (1 : X.functionField) ∈ P.Bl 0 0 1 := by
  refine ⟨fun x i j _ _ => ?_, fun σ y => ?_⟩
  · simp only [Pair.loc, zpow_zero, mul_one]
    exact ⟨1, map_one _⟩
  · have e := IntExample.ratVal_nat y 1
    simp only [Nat.cast_one] at e
    simp [Pair.nu, Pair.loc, e]

theorem prod_mem_of_le (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField)
    (a b : ℤ) (R : ℝ) (hR : 0 ≤ R) (h : ∀ c, boxFam e x c ∈ P.Bl a b R) :
    ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i ≤ m) →
      (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  intro m
  induction m with
  | zero =>
    intro u n hn
    have h0 : ∀ i, n i = 0 := fun i => Nat.le_zero.1 (hn i)
    simp only [h0, pow_zero, Finset.prod_const_one, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      Nat.cast_zero, zero_mul]
    exact one_mem_Bl P
  | succ m ih =>
    intro u n hn
    have hx : ∏ i, x i ^ n i =
        (∏ i ∈ Finset.univ.filter (fun i => 0 < n i), x i) * ∏ i, x i ^ (n i - 1) := by
      rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rcases Nat.eq_zero_or_pos (n i) with h0 | h0
      · simp [h0]
      · rw [if_pos h0, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n i)]
    have key : (∏ l, e (u l)) * ∏ i, x i ^ n i =
        boxFam e x (u 0, Finset.univ.filter (fun i => 0 < n i)) *
          ((∏ l : Fin m, e (u l.succ)) * ∏ i, x i ^ (n i - 1)) := by
      rw [Fin.prod_univ_succ, hx]
      simp only [boxFam]
      ring
    rw [key]
    have hm := mul_mem_Bl P hR (h (u 0, Finset.univ.filter (fun i => 0 < n i)))
      (ih (fun l => u l.succ) (fun i => n i - 1) (fun i => by have := hn i; omega))
    have ea : ((m + 1 : ℕ) : ℤ) * a = a + m * a := by push_cast; ring
    have eb : ((m + 1 : ℕ) : ℤ) * b = b + m * b := by push_cast; ring
    rw [ea, eb, pow_succ']
    exact hm

theorem prod_mem_Bl : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField) (a b : ℤ) (R : ℝ), 0 ≤ R → (∀ c, boxFam e x c ∈ P.Bl a b R) → ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i < m) → (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  intro k _ X _ p P D J e x a b R hR h m u n hn
  exact prod_mem_of_le P D J e x a b R hR h m u n fun i => (hn i).le

end GlobalTheory.HSNef.BoxProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxMonomialFamilyProdMemNormBallOfExponentLtStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxMonomialFamily_prod_mem_normBall_of_exponent_lt : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (D : ℕ) (J : Type) (e : J → X.functionField) (x : Fin D → X.functionField) (a b : ℤ) (R : ℝ), 0 ≤ R → (∀ c, boxFam e x c ∈ P.Bl a b R) → ∀ (m : ℕ) (u : Fin m → J) (n : Fin D → ℕ), (∀ i, n i < m) → (∏ l, e (u l)) * ∏ i, x i ^ n i ∈ P.Bl (m * a) (m * b) (R ^ m) := by
  first | exact @GlobalTheory.HSNef.BoxProd.prod_mem_Bl | exact GlobalTheory.HSNef.BoxProd.prod_mem_Bl | (intros; apply GlobalTheory.HSNef.BoxProd.prod_mem_Bl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearSymmFixesUnitSectionGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearSymmFixesUnitSectionGenericFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma unit_pullback_left_comp_fst_eq_spMap_comp_unit {W R : Type} [CommRing W] [CommRing R] (φ : W →+* R)
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] :
    (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G]).left ≫ pullback.fst G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) =
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ ≫ η[G].left := by
  simp [Functor.grpObjObj, Functor.monObjObj]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma unit_pullback_left_comp_snd_eq_id {W R : Type} [CommRing W] [CommRing R] (φ : W →+* R)
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] :
    (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G]).left ≫ pullback.snd G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) = 𝟙 _ := by
  have h := Over.w (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G])
  simpa using h


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.semilinear_symm_fixes_unit : ∀ (K W K' : Type) [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K'] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] (e : (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G ≅ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A), IsMonHom e.hom → ∀ (σ : K' ≃ₐ[K] K') (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K' ⟶ pullback G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K')) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K') ≫ η[G].left → x ≫ pullback.snd G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K')) = 𝟙 _ → x ≫ (e.hom.left ≫ pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) (𝟙 _) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫ e.inv.left) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ x := by
  intro K W K' _ _ _ _ _ A _ G _ e he σ x hx₁ hx₂

  have hxη : x = (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left := by
    apply pullback.hom_ext
    · rw [hx₁, unit_pullback_left_comp_fst_eq_spMap_comp_unit]
    · rw [hx₂, unit_pullback_left_comp_snd_eq_id]
      rfl
  have hη : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left ≫ e.hom.left =
      (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') := by
    rw [_root_.GlobalTheory.spMap_comp_spMap]
    congr 1
    ext y
    exact σ.commutes y
  have hinv : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have hmap : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left ≫
      pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) (𝟙 _)
        (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K')) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) =
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [unit_pullback_left_comp_fst_eq_spMap_comp_unit, ← Category.assoc, hσ]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, unit_pullback_left_comp_snd_eq_id]
      simp
  rw [hxη, ← Category.assoc, hη, ← Category.assoc, hmap, Category.assoc, ← hη, Category.assoc,
    hinv, Category.comp_id]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearSymmFixesUnitSectionGenericFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_symm_fixes_unit_section_genericFibre : ∀ (K W K' : Type) [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K'] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A), IsMonHom e.hom → ∀ (σ : K' ≃ₐ[K] K') (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ η[G].left → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫ e.inv.left) = spMap (σ : K' →+* K') ≫ x := by
  first | exact @GlobalTheory.semilinear_symm_fixes_unit | exact GlobalTheory.semilinear_symm_fixes_unit | (intros; apply GlobalTheory.semilinear_symm_fixes_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantLaplacianEqCasimirDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantLaplacianEqCasimirDecomposition
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

namespace GlobalTheory.LapSplit

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem Eop_conjugate (τ : E →+* ℂ) (i j : Fin a) :
    Eop (ComplexEmbedding.conjugate τ) i j =
      (1 / 2 : ℂ) • (lieS E a i j (atEmb τ 1) + Complex.I • lieS E a i j (atEmb τ Complex.I)) := by
  have h : atEmb τ (starRingEnd ℂ Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq τ (starRingEnd ℂ Complex.I)]
    conv_rhs => rw [atEmb_eq τ Complex.I]
    simp
  simp only [Eop, atEmb_conj, map_one, h, map_neg, smul_neg, sub_neg_eq_add]

theorem sum_sum_eq_zero_of_swap {A : Type} [AddCommGroup A] [Module ℂ A] (f : Fin a → Fin a → A)
    (hf : ∀ i j, f i j + f j i = 0) : ∑ i, ∑ j, f i j = 0 := by
  have h2 : (2 : ℂ) • ∑ i, ∑ j, f i j = 0 := by
    rw [two_smul]
    conv_lhs => enter [2]; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun j _ => hf i j
  have := congrArg (fun x => (1 / 2 : ℂ) • x) h2
  simpa [smul_smul] using this

theorem lap_summand (τ : E →+* ℂ) :
    ∑ i : Fin a, ∑ j : Fin a, ((lieS E a i j (atEmb τ 1)) ^ 2 + (lieS E a i j (atEmb τ Complex.I)) ^ 2) =
      (2 : ℂ) • ∑ i : Fin a, ∑ j : Fin a, (1 / 4 : ℂ) •
        ((lieS E a i j (atEmb τ 1) - lieS E a j i (atEmb τ 1)) ^ 2 +
          (lieS E a i j (atEmb τ Complex.I) + lieS E a j i (atEmb τ Complex.I)) ^ 2) +
      (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) + (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate τ)) := by
  rw [← sub_eq_zero]
  simp only [Formalism.REAL.Cas, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply sum_sum_eq_zero_of_swap
  intro i j
  simp only [Eop_conjugate]
  simp only [Eop]
  set R1 := lieS E a i j (atEmb τ 1)
  set R2 := lieS E a j i (atEmb τ 1)
  set I1 := lieS E a i j (atEmb τ Complex.I)
  set I2 := lieS E a j i (atEmb τ Complex.I)
  simp only [sq, smul_add, smul_sub, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf

end GlobalTheory.LapSplit

namespace GlobalTheory.LapSplit

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem sum_cas_conjugate :
    ∑ τ : E →+* ℂ, Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate τ)) =
      ∑ τ : E →+* ℂ, Formalism.REAL.Cas (Eop (a := a) τ) := by
  let e : (E →+* ℂ) ≃ (E →+* ℂ) :=
    ⟨ComplexEmbedding.conjugate, ComplexEmbedding.conjugate, fun σ => star_star σ, fun σ => star_star σ⟩
  exact Equiv.sum_comp e (fun τ => Formalism.REAL.Cas (Eop (a := a) τ))

end GlobalTheory.LapSplit

namespace GlobalTheory.HCAlpha

theorem lapOp_eq_casKOp_add_cas (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    lapOp E a = (2 : ℂ) • casKOp E a + ∑ τ : E →+* ℂ, (4 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) := by
  have h4 : ∀ τ : E →+* ℂ, (4 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) =
      (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) + (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) := fun τ => by
    rw [← add_smul]; norm_num
  unfold lapOp casKOp
  rw [Finset.sum_congr rfl fun τ _ => GlobalTheory.LapSplit.lap_summand (a := a) τ]
  simp only [ Finset.sum_add_distrib, h4, ← Finset.smul_sum,
    GlobalTheory.LapSplit.sum_cas_conjugate]
  abel

end GlobalTheory.HCAlpha
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantLaplacianEqCasimirDecompositionStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftInvariantLaplacian_eq_casimir_decomposition : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    lapOp E a = (2 : ℂ) • casKOp E a + ∑ τ : E →+* ℂ, (4 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) := by
  first | exact @GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas | exact GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas | (intros; apply GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameExtensionExists
section -- merged from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.MatchingNotVacuous
noncomputable section

namespace GlobalTheory.ThetaFrameCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem genFibre_tied (T : CDVR) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c) (hz : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt)
    (G : SAB H (Sp T.V)) (m : SABMap G Y.t yt) :
    ∃ (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _))
      (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) (m' : SABMap t' Y.oF.t z),
      m1.φ = m'.φ ≫ Y.m0.toSABMap.φ ∧ m2.φ ≫ m.φ = m'.φ ≫ Y.m.φ := by
  obtain ⟨PP', cub, sym, adj, prim, m2, -⟩ :=
    sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap (algebraMap T.V T.Fr)) G
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ Y.t G _ yt (spMap (algebraMap T.V T.Fr)) m m2
  have cancel : ∀ (t' : SAB H (Sp T.Fr)) (p : Sp T.Fr ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' Y.oF.t z, n.φ = m'.φ ≫ Y.m.φ := by
    intro t' p hp n; subst hp
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n
  obtain ⟨m', hm'⟩ := cancel _ _ hz.symm n
  obtain ⟨m1, h1⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ (pullback.fst _ _) z Y.m0.toSABMap m'
  exact ⟨_, m1, m2, m', h1, hn.symm.trans hm'⟩

variable {Xo}

end GlobalTheory.ThetaFrameCheck
end
end

set_option synthInstance.maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

noncomputable section

namespace GlobalTheory.FactorDepth.Extension

attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tanEquiv {V : Type} [CommRing V] {X0 : Scheme.{0}} {t : SAB H X0} {x : Sp V ⟶ X0} {G : SAB H (Sp V)}
    (m : SABMap G t x) :
    ∃ B : (epsOver V V ⟶ G.G) ≃* (tEpsG x ⟶ t.G), (∀ v, (B v).left = v.left ≫ m.φ) ∧
      (∀ v, IsTanAtG t x (B v).left ↔ IsTan v) ∧
      (∀ v (a : 𝓞 E) (r : V), (B v).left ≫ (t.act.act a).left = spMap (epsMul r) ≫ (B v).left ↔
        (v ≫ G.act.act a).left = spMap (epsMul r) ≫ v.left) ∧
      ∀ (n : ℕ) (v : Fin n → (epsOver V V ⟶ G.G)) a w,
        IsCombAtG t x (fun i => (B (v i)).left) a (B w).left ↔ IsComb v a w := by
  have h := m.cart
  have hid : spMap (algebraMap V V) = 𝟙 _ := Spec.map_id _
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv h
    (spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)))
    (spMap (algebraMap V (DualNumber V)) ≫ x) rfl
  obtain ⟨A, hA⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv h (spMap (algebraMap V V)) x
    (by rw [hid, Category.id_comp])
  have hw : ∀ v : epsOver V V ⟶ G.G, v.left ≫ G.G.hom = spMap (algebraMap V (DualNumber V)) := fun v => Over.w v
  have sc : ∀ (a : V) (u v : epsOver V V ⟶ G.G),
      (B u).left = spMap (epsMul a) ≫ (B v).left ↔ u.left = spMap (epsMul a) ≫ v.left := by
    intro a u v
    rw [hB, hB]
    refine ⟨fun e => h.1.hom_ext (by rw [e, Category.assoc]) ?_, fun e => by rw [e, Category.assoc]⟩
    rw [Category.assoc, hw, hw, GlobalTheory.Exist.FlagBaseChange.epsMul_over]
  have prod : ∀ (n : ℕ) (u : Fin n → (epsOver V V ⟶ G.G)),
      B (List.ofFn u).prod = (List.ofFn fun i => B (u i)).prod := by
    intro n u
    rw [map_list_prod, List.map_ofFn]
    rfl
  refine ⟨B, hB, fun v => ?_, fun v a r => ?_, fun n v a w => ?_⟩
  · unfold IsTanAtG IsTan
    refine (and_iff_right (Over.w (B v))).trans ?_
    rw [← map_one A, hA, hB]
    refine ⟨fun e => h.1.hom_ext (by rw [← e, Category.assoc]) ?_, fun e => by rw [← e, Category.assoc]⟩
    rw [Category.assoc, hw, GlobalTheory.Exist.FlagBaseChange.fst_over]
    exact ((Over.w (1 : ptOver V V ⟶ G.G)).trans hid).symm
  · have e : (B v).left ≫ (t.act.act a).left = (B (v ≫ G.act.act a)).left := by
      rw [hB, hB, Over.comp_left, Category.assoc, Category.assoc, m.act]
    rw [e]
    exact sc _ _ _
  · constructor
    · rintro ⟨u, hu, e⟩
      refine ⟨fun i => B.symm (u i), fun i => (sc _ _ _).1 (by rw [B.apply_symm_apply]; exact hu i), B.injective ?_⟩
      rw [prod, ← Over.OverMorphism.ext e]
      simp
    · rintro ⟨u, hu, e⟩
      exact ⟨fun i => B (u i), fun i => (sc _ _ _).2 (hu i), by rw [e, prod]⟩

end GlobalTheory.FactorDepth.Extension
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxPrincipleNear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxPrincipleNear
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem finiteType_int_of_isAffineOpen {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  obtain ⟨N, i, hi, e⟩ := hX.isProjOver
  have : LocallyOfFiniteType p := by subst e; infer_instance
  have : Module.Finite ℤ k := hX.finite
  have h1 := Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp k)) hU (by simp)
  have h2 : (algebraMap ℤ k).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
  have h3 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).FiniteType :=
    RingHom.FiniteType.of_surjective _ fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x, by simp⟩
  have h4 := h1.comp (h3.comp h2)
  rw [← RingHom.finiteType_algebraMap]
  convert h4 using 1
  exact RingHom.ext_int _ _

theorem Pair.max_principle_near : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∀ (σ : k →+* ℂ) (y₀ : CxPts p σ), ∃ (W : Set (CxPts p σ)) (ρ : ℝ), W ∈ 𝓝 y₀ ∧ 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ' : k →+* ℂ) (y : CxPts p σ'), ρ ≤ P.nu 0 1 σ' y s → P.nu N 0 σ' y f ≤ R) → ∀ y ∈ W, P.nu N 0 σ y f ≤ Real.exp (δ * N) * R := by
  intro k _ X _ p D hX P s hs hs0 δ hδ σ y₀
  set i := pick (P.L.φ σ).isLB y₀
  set j := pick (P.A.φ σ).isLB y₀
  have hyi : y₀ ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ _
  have hyj : y₀ ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ _
  have hxV : y₀.1 (IsLocalRing.closedPoint ℂ) ∈ P.L.B.U i ⊓ P.A.B.U j :=
    GlobalTheory.CxPts.mem_ptsIn.1 (GlobalTheory.CxPts.mem_ptsIn_inf.2 ⟨hyi, hyj⟩)
  obtain ⟨U, hUa, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxV
  have hUi : U ≤ P.L.B.U i := hUV.trans inf_le_left
  have hUj : U ≤ P.A.B.U j := hUV.trans inf_le_right
  have hy₀U : y₀ ∈ ptsIn p σ U := GlobalTheory.CxPts.mem_ptsIn.2 hxU
  have hgen : genericPoint X ∈ U := gen_mem hxU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : CharZero Γ(X, U) := RingHom.charZero (evHom hy₀U)
  have : Algebra.FiniteType ℤ Γ(X, U) := finiteType_int_of_isAffineOpen hX hUa
  let _ : TopologicalSpace (Γ(X, U) →+* ℂ) :=
    TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance
  have hcont : ∀ (M : HermLB p) (c : M.B.ι), U ≤ M.B.U c → ∀ σ' : k →+* ℂ,
      ContinuousOn (fun y => (M.φ σ').φ c y / 2) (ptsIn p σ' U) := by
    intro M c hc σ' y hy
    exact ((M.cInf σ' c y (ptsIn_mono hc hy)).continuousAt.div_const 2).continuousWithinAt
  obtain ⟨ψ, hψc, hψv, hsurj, hnb⟩ :=
    GlobalTheory.T.exists_continuous_read_on_affineOpen_ringHoms k X p D hX U hUa (fun σ' y => (P.L.φ σ').φ i y / 2) (hcont P.L i hUi)
  obtain ⟨ψ', hψ'c, hψ'v, -, -⟩ :=
    GlobalTheory.T.exists_continuous_read_on_affineOpen_ringHoms k X p D hX U hUa (fun σ' y => (P.A.φ σ').φ j y / 2) (hcont P.A j hUj)
  have hsreg : ∀ x ∈ U, RegAt x (P.loc 0 1 s i j) := fun x hx => hs x i j (hUi hx) (hUj hx)
  obtain ⟨s', hs'⟩ := exists_fnOf_eq hgen hsreg
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    simp [Pair.loc, hs0] at hs'
  obtain ⟨W', K, hW', hK, hKs, hmain⟩ := GlobalTheory.T.local_max_principle_weighted_finiteType_int Γ(X, U) ψ hψc s' hs'0 (evHom hy₀U) δ hδ
  have hgc : Continuous (fun x : Γ(X, U) →+* ℂ => ‖x s'‖ * Real.exp (-ψ' x)) :=
    (((continuous_apply s').comp continuous_induced_dom).norm).mul (Real.continuous_exp.comp hψ'c.neg)
  obtain ⟨ρ, hρ, hρK⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ρ ≤ ‖x s'‖ * Real.exp (-ψ' x) := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, by simp [hKe]⟩
    · obtain ⟨x₁, hx₁, hmin⟩ := hK.exists_isMinOn hKne hgc.continuousOn
      exact ⟨_, mul_pos (norm_pos_iff.2 (hKs x₁ hx₁)) (Real.exp_pos _), fun x hx => isMinOn_iff.mp hmin x hx⟩
  refine ⟨{z | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W'}, ρ, hnb σ y₀ hy₀U W' hW', hρ, ?_⟩
  intro N f R hf hR y hyW
  obtain ⟨hyU, hyW'⟩ := hyW
  have hfreg : ∀ x ∈ U, RegAt x (P.loc N 0 f i j) := fun x hx => hf x i j (hUi hx) (hUj hx)
  obtain ⟨f', hf'⟩ := exists_fnOf_eq hgen hfreg
  have hnuF : ∀ (σ' : k →+* ℂ) (z : CxPts p σ') (hz : z ∈ ptsIn p σ' U),
      P.nu N 0 σ' z f = ‖evHom hz f'‖ * Real.exp (-(N * ψ (evHom hz))) := by
    intro σ' z hz
    rw [GlobalTheory.T.hermLineBundlePairNorm_independent_of_frames k X p P N 0 f hf σ' z i j (ptsIn_mono hUi hz) (ptsIn_mono hUj hz), ← hf',
      ratVal_fnOf hz hgen, ev_eq hz, hψv σ' z hz]
    congr 2
    push_cast
    ring
  have hnuS : ∀ (σ' : k →+* ℂ) (z : CxPts p σ') (hz : z ∈ ptsIn p σ' U),
      P.nu 0 1 σ' z s = ‖evHom hz s'‖ * Real.exp (-ψ' (evHom hz)) := by
    intro σ' z hz
    rw [GlobalTheory.T.hermLineBundlePairNorm_independent_of_frames k X p P 0 1 s hs σ' z i j (ptsIn_mono hUi hz) (ptsIn_mono hUj hz), ← hs',
      ratVal_fnOf hz hgen, ev_eq hz, hψ'v σ' z hz]
    congr 2
    push_cast
    ring
  rw [hnuF σ y hyU]
  refine hmain N f' R ?_ (evHom hyU) hyW'
  intro x hx
  obtain ⟨σ', z, hz, rfl⟩ := hsurj x
  rw [← hnuF σ' z hz]
  exact hR σ' z (by rw [hnuS σ' z hz]; exact hρK _ hx)

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxPrincipleNearStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_nu_le_exp_mul_of_far_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∀ (σ : k →+* ℂ) (y₀ : CxPts p σ), ∃ (W : Set (CxPts p σ)) (ρ : ℝ), W ∈ 𝓝 y₀ ∧ 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ' : k →+* ℂ) (y : CxPts p σ'), ρ ≤ P.nu 0 1 σ' y s → P.nu N 0 σ' y f ≤ R) → ∀ y ∈ W, P.nu N 0 σ y f ≤ Real.exp (δ * N) * R := by
  first | exact @GlobalTheory.VolBr.Pair.max_principle_near | exact GlobalTheory.VolBr.Pair.max_principle_near | (intros; apply GlobalTheory.VolBr.Pair.max_principle_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartLeftInvariantLaplacianOpPowEqIterate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartLeftInvariantLaplacianOpPowEqIterate
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

namespace GlobalTheory.HCAlpha

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem vecF_eqOn_invSet (X : Lie E a) {f f' : Lie E a → ℂ} (h : Set.EqOn f f' (invSet E a)) :
    Set.EqOn (vecF E a X f) (vecF E a X f') (invSet E a) := fun y hy => by
  have e : f =ᶠ[nhds y] f' := Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) h
  simp only [vecF, e.fderiv_eq]

theorem lapF_eqOn_invSet {f f' : Lie E a → ℂ} (h : Set.EqOn f f' (invSet E a)) :
    Set.EqOn (lapF E a f) (lapF E a f') (invSet E a) := fun y hy => by
  simp only [lapF, Finset.sum_apply, Pi.add_apply]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [vecF_eqOn_invSet _ (vecF_eqOn_invSet _ h) hy, vecF_eqOn_invSet _ (vecF_eqOn_invSet _ h) hy]

theorem chart_lie_eqOn_invSet (X : Lie E a) (φ : Sm E a) (g : GA E a) :
    Set.EqOn (chart (lie E a X φ).1 g) (vecF E a X (chart φ.1 g)) (invSet E a) := fun _ hy =>
  chart_lieD φ.2 X g hy

theorem chart_lie_sq_eqOn_invSet (X : Lie E a) (φ : Sm E a) (g : GA E a) :
    Set.EqOn (chart ((lie E a X ^ 2) φ).1 g) (vecF E a X (vecF E a X (chart φ.1 g))) (invSet E a) := by
  rw [sq]
  exact (chart_lie_eqOn_invSet X (lie E a X φ) g).trans (vecF_eqOn_invSet X (chart_lie_eqOn_invSet X φ g))

theorem chart_lapOp_eqOn_invSet (φ : Sm E a) (g : GA E a) :
    Set.EqOn (chart (lapOp E a φ).1 g) (lapF E a (chart φ.1 g)) (invSet E a) := fun y hy => by
  have hy' : IsUnit (Matrix.of y) := hy
  have key : ∀ X : Lie E a, ((lie E a X ^ 2) φ).1 (g * infGL E a hy'.unit) =
      vecF E a X (vecF E a X (chart φ.1 g)) y := fun X => by
    rw [← chart_lie_sq_eqOn_invSet X φ g hy, chart, dite_eq_left hy']
  rw [chart, dite_eq_left hy']
  simp only [lapOp, lapF, LinearMap.sum_apply, LinearMap.add_apply, Submodule.coe_sum, Submodule.coe_add,
    Finset.sum_apply, Pi.add_apply]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← key, ← key]
  rfl

theorem chart_lapOp_pow (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (g : GA E a) (n : ℕ) :
    ∀ y ∈ invSet E a, chart ((lapOp E a ^ n) φ).1 g y = (lapF E a)^[n] (chart φ.1 g) y := by
  induction n with
  | zero => intro y _; rfl
  | succ n ih =>
    intro y hy
    rw [pow_succ', Function.iterate_succ_apply', Module.End.mul_apply, chart_lapOp_eqOn_invSet _ g hy]
    exact lapF_eqOn_invSet ih hy

end GlobalTheory.HCAlpha

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartLeftInvariantLaplacianOpPowEqIterateStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_leftInvariantLaplacianOp_pow_eq_iterate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (n : ℕ),
    ∀ y ∈ invSet E a, chart ((lapOp E a ^ n) φ).1 g y = (lapF E a)^[n] (chart φ.1 g) y := by
  first | exact @GlobalTheory.HCAlpha.chart_lapOp_pow | exact GlobalTheory.HCAlpha.chart_lapOp_pow | (intros; apply GlobalTheory.HCAlpha.chart_lapOp_pow <;> assumption)
end
end
