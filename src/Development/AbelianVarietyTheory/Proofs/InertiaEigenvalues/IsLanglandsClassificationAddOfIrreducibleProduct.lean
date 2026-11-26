module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationAddOfIrreducibleProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationAddOfIrreducibleProduct
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL.SumProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}

theorem sum_fst_of_lFactors {𝔪 : Multiset (Segment k)} {h : ℕ} {x : Fin h → IrrGL (k := k)} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨rfl, -⟩, hΔ⟩ := hx
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => (hΔ a).deg_eq.symm

theorem deg_of_isL {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) :
    (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  exact (sum_fst_of_lFactors hx).symm.trans hd

theorem exists_isLSeg_of_isL {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π)
    {Δ : Segment k} (hΔ : Δ ∈ 𝔪) : ∃ y : IrrGL (k := k), IsLSeg Δ y.rep := by
  obtain ⟨_, x, -, ⟨D, ⟨rfl, -⟩, hD⟩, -⟩ := h
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hΔ
  exact ⟨x a, hD a⟩

theorem exists_isL [CharZero k] (hS : StandardCosocleGL) {𝔪 : Multiset (Segment k)}
    (h : ∀ Δ ∈ 𝔪, ∃ y : IrrGL (k := k), IsLSeg Δ y.rep) (hN : (𝔪.map Segment.deg).sum = N) :
    ∃ π : IrrRep (GL (Fin N) k), IsL 𝔪 π.ρ := by
  obtain ⟨D, hD⟩ := exists_isOrderedForm 𝔪
  have hm : ∀ i, D i ∈ 𝔪 := fun i => hD.1 ▸ Multiset.mem_map_of_mem D (Finset.mem_univ i)
  choose x hx using fun i => h _ (hm i)
  have hF : LFactors 𝔪 x := ⟨D, hD, hx⟩
  have hd : ∑ a, (x a).1 = N := (sum_fst_of_lFactors hF).trans hN
  obtain ⟨π, hπ⟩ := hS k 𝔪 _ _ x hd hF
  exact ⟨π, _, x, hd, hF, hπ⟩

theorem isL_add_of_equiv_prod₂ : LanglandsMultisegments → StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (r t : ℕ) (σ : IrrRep (GL (Fin r) k)) (τ : IrrRep (GL (Fin t) k)) (π : IrrRep (GL (Fin (r + t)) k)) (𝔪 𝔫 : Multiset (Segment k)), IsL 𝔪 σ.ρ → IsL 𝔫 τ.ρ → Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → IsL (𝔪 + 𝔫) π.ρ := by
  rintro hM hS k _ _ _ _ _ r t σ τ π 𝔪 𝔫 h1 h2 ⟨e⟩
  obtain ⟨y, hy⟩ := exists_isL (N := r + t) hS (𝔪 := 𝔪 + 𝔫)
    (fun Δ hΔ => (Multiset.mem_add.1 hΔ).elim (exists_isLSeg_of_isL h1) (exists_isLSeg_of_isL h2))
    (by rw [Multiset.map_add (f := _), Multiset.sum_add, deg_of_isL h1, deg_of_isL h2])
  have hd : ∑ a, (![IrrGL.of σ.ρ σ.smooth σ.irr, IrrGL.of τ.ρ τ.smooth τ.irr] a).1 = r + t := Fin.sum_univ_two _
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr σ.ρ σ.smooth σ.irr τ.ρ τ.smooth τ.irr hd
  have ψ := IrrGL.equivOf y.ρ y.smooth y.irr
  have a1 : IsL 𝔪 (IrrGL.of σ.ρ σ.smooth σ.irr).rep := h1.of_equiv (IrrGL.equivOf _ _ _)
  have a2 : IsL 𝔫 (IrrGL.of τ.ρ τ.smooth τ.irr).rep := h2.of_equiv (IrrGL.equivOf _ _ _)
  have a3 : IsL (𝔪 + 𝔫) (IrrGL.of y.ρ y.smooth y.irr).rep := hy.of_equiv ψ
  have hs := (hM k).2 𝔪 𝔫 ![IrrGL.of σ.ρ σ.smooth σ.irr, IrrGL.of τ.ρ τ.smooth τ.irr]
    (IrrGL.of y.ρ y.smooth y.irr) hd a1 a2 a3
  have E := (e.trans φ).symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hs.trans (.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)) (IrrRep.irr _) π.irr
  exact a3.of_equiv θ.symm

end GlobalTheory.LocGL.SumProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationAddOfIrreducibleProductStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsClassification_add_of_irreducible_product : LanglandsMultisegments → StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (r t : ℕ) (σ : IrrRep (GL (Fin r) k)) (τ : IrrRep (GL (Fin t) k)) (π : IrrRep (GL (Fin (r + t)) k)) (𝔪 𝔫 : Multiset (Segment k)), IsL 𝔪 σ.ρ → IsL 𝔫 τ.ρ → Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → IsL (𝔪 + 𝔫) π.ρ := by
  first | exact @GlobalTheory.LocGL.SumProd.isL_add_of_equiv_prod₂ | exact GlobalTheory.LocGL.SumProd.isL_add_of_equiv_prod₂ | (intros; apply GlobalTheory.LocGL.SumProd.isL_add_of_equiv_prod₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwasawaDecompositionSmoothNearOne
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

open scoped Matrix.Norms.Operator

noncomputable section

namespace GlobalTheory.SmoothIwasawaNear

variable (E : Type) [Field E] [NumberField E] {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N)

def lowPart (X : Matrix (Fin N) (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E) :=
  Matrix.of fun p q => if blk e q < blk e p then X p q else 0

def skewLin : Matrix (Fin N) (Fin N) (Cinf E) →ₗ[ℝ] Matrix (Fin N) (Fin N) (Cinf E) where
  toFun X := lowPart E e X - (lowPart E e X).conjTranspose
  map_add' X Y := by
    refine Matrix.ext fun p q => ?_
    simp only [lowPart, Matrix.add_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    split_ifs <;> simp [star_add] <;> abel
  map_smul' r X := by
    refine Matrix.ext fun p q => ?_
    simp only [lowPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      RingHom.id_apply]
    split_ifs <;> simp [star_smul, smul_sub]

def skew : Matrix (Fin N) (Fin N) (Cinf E) →L[ℝ] Matrix (Fin N) (Fin N) (Cinf E) :=
  LinearMap.toContinuousLinearMap (skewLin E e)

theorem skew_apply (X : Matrix (Fin N) (Fin N) (Cinf E)) : skew E e X = lowPart E e X - (lowPart E e X).conjTranspose := rfl

theorem skew_conjTranspose (X : Matrix (Fin N) (Fin N) (Cinf E)) : (skew E e X).conjTranspose = -skew E e X := by
  rw [skew_apply, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]

theorem blockTriangular_up (X : Matrix (Fin N) (Fin N) (Cinf E)) :
    (1 + (X - skew E e X)).BlockTriangular (blk e) := by
  intro i j h
  have hij : i ≠ j := fun hh => by subst hh; exact lt_irrefl _ h
  simp [skew_apply, lowPart, Matrix.conjTranspose_apply, Matrix.one_apply_ne hij, h, not_lt_of_gt h]

def Fm (X : Matrix (Fin N) (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E) :=
  (1 + (X - skew E e X)) * NormedSpace.exp (skew E e X)

theorem contDiff_exp' {k : WithTop ℕ∞} :
    ContDiff ℝ k (NormedSpace.exp : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E)) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem contDiff_Fm {k : WithTop ℕ∞} : ContDiff ℝ k (Fm E e) :=
  (contDiff_const.add (contDiff_id.sub (skew E e).contDiff)).mul ((contDiff_exp' E).comp (skew E e).contDiff)

theorem Fm_zero : Fm E e 0 = 1 := by simp [Fm, NormedSpace.exp_zero]

theorem hasFDerivAt_Fm : HasFDerivAt (Fm E e)
    ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin N) (Fin N) (Cinf E)) : _ →L[ℝ] _)) 0 := by
  have h1 : HasFDerivAt (fun X : Matrix (Fin N) (Fin N) (Cinf E) => 1 + (X - skew E e X))
      (ContinuousLinearMap.id ℝ _ - skew E e) 0 :=
    ((hasFDerivAt_id 0).sub (skew E e).hasFDerivAt).const_add 1
  have h0 := hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) (Cinf E))
  rw [← map_zero (skew E e)] at h0
  have h2 := h0.comp (0 : Matrix (Fin N) (Fin N) (Cinf E)) (skew E e).hasFDerivAt
  have h3 := h1.mul' h2
  refine h3.congr_fderiv (ContinuousLinearMap.ext fun X => ?_)
  have hs0 : skew E e 0 = 0 := map_zero _
  show (1 + (0 - skew E e 0)) * skew E e X + (X - skew E e X) * NormedSpace.exp (skew E e 0) = X
  rw [hs0, NormedSpace.exp_zero, sub_zero, add_zero, one_mul, mul_one]
  abel

theorem exists_local_iwasawa : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (e : (Σ i, Fin (n i)) ≃ Fin N), ∃ (p : Lie E N → parab (Cinf E) e) (k : Lie E N → Kinf E N), ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => toL (p y).1.val) (oneL E N) ∧ ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => toL (k y).1) (oneL E N) ∧ p (oneL E N) = 1 ∧ k (oneL E N) = 1 ∧ ∀ᶠ y in nhds (oneL E N), Matrix.of y = (p y).1.val * (k y).1 := by
  intro E _ _ _ c N n e
  classical
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fm E e) 0 := (contDiff_Fm E e).contDiffAt
  have hF' := hasFDerivAt_Fm E e
  set G := hF.localInverse hF' hn with hGdef
  have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Fm E e 0) := hF.to_localInverse hF' hn
  have hG1 : G (Fm E e 0) = 0 := hF.localInverse_apply_image hF' hn
  have hinv : ∀ᶠ X in nhds (Fm E e 0), Fm E e (G X) = X :=
    (hF.hasStrictFDerivAt' hF' hn).eventually_right_inverse
  rw [Fm_zero] at hG hG1 hinv
  let T : Lie E N ≃L[ℝ] Matrix (Fin N) (Fin N) (Cinf E) := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  let φ : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E) := fun X => 1 + (G X - skew E e (G X))
  let ψ : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E) :=
    fun X => NormedSpace.exp (skew E e (G X))
  have hφ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ 1 :=
    contDiffAt_const.add (hG.sub ((skew E e).contDiff.contDiffAt.comp _ hG))
  have hψ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ 1 :=
    (contDiff_exp' E).contDiffAt.comp _ ((skew E e).contDiff.contDiffAt.comp _ hG)
  have hφ1 : φ 1 = 1 := by simp [φ, hG1]
  have hψ1 : ψ 1 = 1 := by simp [ψ, hG1, NormedSpace.exp_zero]
  have hunit : ∀ᶠ X in nhds (1 : Matrix (Fin N) (Fin N) (Cinf E)), IsUnit (φ X) :=
    hφ.continuousAt.eventually_mem (by rw [hφ1]; exact Units.isOpen.mem_nhds isUnit_one)
  have hTt : Filter.Tendsto (fun y : Lie E N => Matrix.of y) (nhds (oneL E N)) (nhds 1) :=
    T.continuous.tendsto (oneL E N)
  have hunitV : ∀ᶠ y in nhds (oneL E N), IsUnit (φ (Matrix.of y)) := hTt.eventually hunit
  have hinvV : ∀ᶠ y in nhds (oneL E N), Fm E e (G (Matrix.of y)) = Matrix.of y := hTt.eventually hinv
  have hU : ∀ X, ψ X ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := fun X => by
    show NormedSpace.exp (skew E e (G X)) ∈ _
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      skew_conjTranspose, ← Matrix.exp_add_of_commute _ _ (Commute.refl (skew E e (G X))).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  have hφT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ (T (oneL E N)) := hφ
  have hψT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ (T (oneL E N)) := hψ
  refine ⟨fun y => if h : IsUnit (φ (Matrix.of y)) then ⟨h.unit, blockTriangular_up E e (G (Matrix.of y))⟩ else 1,
    fun y => ⟨ψ (Matrix.of y), hU _⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => T.symm (φ (T y))) (oneL E N) :=
      T.symm.contDiff.contDiffAt.comp _ (hφT.comp (oneL E N) T.contDiff.contDiffAt)
    refine hsm.congr_of_eventuallyEq ?_
    filter_upwards [hunitV] with y hy
    simp only [dif_pos hy]
    show toL (hy.unit : Matrix (Fin N) (Fin N) (Cinf E)) = _
    rw [hy.unit_spec]
    rfl
  · exact T.symm.contDiff.contDiffAt.comp _ (hψT.comp (oneL E N) T.contDiff.contDiffAt)
  · have h1 : IsUnit (φ (Matrix.of (oneL E N))) := by
      show IsUnit (φ 1)
      rw [hφ1]
      exact isUnit_one
    refine Subtype.ext (Units.ext ?_)
    simp only [dif_pos h1]
    exact (IsUnit.unit_spec _).trans hφ1
  · exact Subtype.ext hψ1
  · filter_upwards [hunitV, hinvV] with y hy hy'
    simp only [dif_pos hy]
    show Matrix.of y = (hy.unit : Matrix (Fin N) (Fin N) (Cinf E)) * ψ (Matrix.of y)
    rw [hy.unit_spec]
    exact hy'.symm

end GlobalTheory.SmoothIwasawaNear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexHeckeConjugatePlacePeterssonAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexHeckeConjugatePlacePeterssonAdjoint
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ComplexHeckeAdjoint

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

theorem levChi_one {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv), levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
  intro k _
  have h1 : ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi (rTup (R.βW i) (R.datWp i R.triv) (Lev.finE (Wc D i) k)) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h1]
  simp [LevCh.datWp, datY]

theorem conj_eq {D : D7} {P P' : PlE D.host} (h : Formalism.BasicNotions.IsConjPl D.host P P') : P' = Formalism.DivisionValues.conjPl P := by
  have hc : ∀ y : 𝓞 D.host.E, Formalism.HermitianLattices.Ext.L3.conjO D.host.E y = Formalism.DivisionValues.cO D.host.E y := fun y =>
    RingOfIntegers.ext (by simp [Formalism.DivisionValues.cO, Formalism.HermitianLattices.Ext.L3.conjO_coe])
  have hcc : ∀ y : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E y) = y := fun y =>
    RingOfIntegers.ext (by simp [Formalism.DivisionValues.cO])
  rw [GlobalTheory.ConjPlaceOff.isConjPl_iff] at h
  ext x
  show x ∈ P'.asIdeal ↔ x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro hx
    refine ⟨Formalism.DivisionValues.cO D.host.E x, (h _).2 ?_, hcc x⟩
    rwa [hc, hcc]
  · rintro ⟨y, hy, rfl⟩
    rw [← hc]
    exact (h y).1 hy


open GlobalTheory.HeckeParts in
theorem keep_adj {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    {L : LevDat D.host.E ℂ V.rank} (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P)
    (hχ : ∀ k ∈ levG V β L, levChi V β L k = 1) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {HM : HMod (MMap M)} {U : Submodule ℂ (MMap M)}
    (hU : U = Mult θ M (levS V β L) (levChi V β L)) {ip : MMap M → MMap M → ℂ} {c : ℂ}
    (hip : ∀ T T', ip T T' = c * ipM M μ 𝓕 T T') (h : HM.Is U ip) {x : GA D V} {A A' : Finset (GA D V)}
    (hA : LocRep (levG V β L) P x A) (hA' : LocRep (levG V β L) P x⁻¹ A') :
    (∀ y, ∃ y', HM.e y' = heckeOn M A (HM.e y)) ∧ (∀ y, ∃ y', HM.e y' = heckeOn M A' (HM.e y)) ∧
      ∀ y z y' z', HM.e y' = heckeOn M A (HM.e y) → HM.e z' = heckeOn M A' (HM.e z) → inner ℂ y' z = inner ℂ y z' := by
  subst hU
  have h' : HM.Is (Mult θ M (levS V β L) (levChi V β L)) fun T T' => c * ipM M μ 𝓕 T T' :=
    ⟨h.1, h.2.1, fun y z => (h.2.2 y z).trans (hip _ _)⟩
  have hmem : ∀ y, HM.e y ∈ Mult θ M (levS V β L) (levChi V β L) := fun y => h.2.1 ▸ LinearMap.mem_range_self _ y
  have keep : ∀ {w : GA D V} {C : Finset (GA D V)}, LocRep (levG V β L) P w C → ∀ y,
      heckeOn M C (HM.e y) ∈ LinearMap.range HM.e := by
    intro w C hC y
    rw [h.2.1]
    exact hC.mult hβ hP (fun k hk => levG_le_flag hk) (hmem y) (fun v => rInv_of_mem hχ (hmem y) v)
  have lift : ∀ {w : GA D V} {C : Finset (GA D V)}, LocRep (levG V β L) P w C →
      ∃ t : Module.End ℂ HM.H, ∀ y, HM.e (t y) = heckeOn M C (HM.e y) := by
    intro w C hC
    refine ⟨(LinearEquiv.ofInjective _ h.1).symm.toLinearMap ∘ₗ ((heckeOn M C ∘ₗ HM.e).codRestrict _ (keep hC)),
      fun y => ?_⟩
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ h.1).apply_symm_apply _)
  obtain ⟨t, ht⟩ := lift hA
  obtain ⟨t', ht'⟩ := lift hA'
  refine ⟨fun y => keep hA y, fun y => keep hA' y, fun y z y' z' hy hz => ?_⟩
  obtain rfl : y' = t y := h.1 (hy.trans (ht y).symm)
  obtain rfl : z' = t' z := h.1 (hz.trans (ht' z).symm)
  exact inner_hecke hχ hμ h𝓕 h' le_rfl hA.2 hA'.2 (hA.card hβ hP hA') ht ht' y z

end GlobalTheory.ComplexHeckeAdjoint

namespace GlobalTheory.CxHeckeAdj


set_option maxHeartbeats 1600000 in
theorem hecke_adjoint : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3),
    Rl.Char3 F → ∀ (i : Fin D.R.m) (k : ℕ) (P P' : PlE D.host), IsSplitPl D.host P → IsConjPl D.host P P' →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    Formalism.IndefR.Bridge.SplitOff P' (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal → 1 ≤ k → k ≤ D.R.r →
    ∃ (α α' : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i)) (R R' : Finset (Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i))),
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P k α ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R ∧
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P' k α' ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α' R' ∧
      (∀ x, ∃ x', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x)) ∧
      (∀ y, ∃ y', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y)) ∧
      ∀ x y x' y' : (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).H,
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x) →
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y) →
        ⟪x', y⟫_ℂ = ⟪x, y'⟫_ℂ := by

  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ Rl F hc i k P P' _hsp hcj hso hso' _h2 _h2' _hk1 hk
  classical
  obtain ⟨c, hβ⟩ := hc.lev.βW i
  have hrk : k ≤ (Formalism.IndefR.Links.Wc D i).rank := by
    rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]; exact hk
  have hoff : ∀ Q : Formalism.L2.DIV.Pl D.host.E, Formalism.IndefR.Bridge.SplitOff Q (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
      GlobalTheory.HeckeParts.OffLevel (Rl.datWp i Rl.triv) (1 ^ c) Q := by
    intro Q hQ
    refine ⟨hQ.1, ?_, ?_⟩
    · rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top
    · intro PP hPP
      have hPP' : PP ∈ Rl.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
      have hS : PP ∈ (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hc.fam.Sb hPP'
      refine ⟨fun h => hQ.2.1 (h ▸ hS), fun h => hQ.2.2 PP hS ?_⟩
      rw [Formalism.L2.Col.conjIdeal_asIdeal]
      refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ Q).isPrime.ne_top fun a ha => ?_
      obtain ⟨a', ha', e⟩ := h a ha
      rw [Formalism.L2.Col.mem_conjP]
      have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
      rwa [this]
  obtain ⟨α, A, A', hα, hA, hA'⟩ := GlobalTheory.HeckeParts.exists_hecke hβ (hoff P hso) hrk
  obtain ⟨α₂, B, B', hα₂, -, -⟩ := GlobalTheory.HeckeParts.exists_hecke hβ (hoff P' hso') hrk
  have hα₂' : Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) (Formalism.DivisionValues.conjPl P) k α₂ :=
    GlobalTheory.ComplexHeckeAdjoint.conj_eq hcj ▸ hα₂
  obtain ⟨e, ϖ, he, -, -, -⟩ := id hα
  obtain ⟨a, ha, b, hb, hab⟩ := GlobalTheory.SplitHeckeAdj.hecke_conj (Formalism.IndefR.Links.Wc D i) he hα hα₂'
  obtain ⟨Lp, -, -, -, hK⟩ := GlobalTheory.HeckeParts.loc_package hβ (hoff P hso) he
  have hA₂ : Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α₂ A :=
    GlobalTheory.SplitHeckeAdj.isDC_of_mem (Subgroup.inv_mem _ ((hK a).1 ha).1) (Subgroup.inv_mem _ ((hK b).1 hb).1)
      (by rw [hab]; group) hA.2

  obtain ⟨hk1, hk2, hadj⟩ := GlobalTheory.ComplexHeckeAdjoint.keep_adj hβ (hoff P hso) (GlobalTheory.ComplexHeckeAdjoint.levChi_one Rl.toRealDat i)
    (hc.models.νW i).1.1 (hc.models.νW i).2 rfl
    (fun _ _ => rfl) (hc.models.HW i (Formalism.IndefR.Links.sg0 D A3.A)) hA' hA
  exact ⟨α, α₂, A', A, hα, hA'.2, hα₂, hA₂, hk1, hk2, hadj⟩

end GlobalTheory.CxHeckeAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexHeckeConjugatePlacePeterssonAdjointStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexHecke_conjugatePlace_petersson_adjoint : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3),
    Rl.Char3 F → ∀ (i : Fin D.R.m) (k : ℕ) (P P' : PlE D.host), IsSplitPl D.host P → IsConjPl D.host P P' →
    Formalism.IndefR.Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    Formalism.IndefR.Bridge.SplitOff P' (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) →
    ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal → 1 ≤ k → k ≤ D.R.r →
    ∃ (α α' : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i)) (R R' : Finset (Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Wc D i))),
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P k α ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R ∧
      Formalism.IndefR.Links.IsHeckeAt (Formalism.IndefR.Links.Wc D i) P' k α' ∧
      Formalism.IndefR.Bridge.IsDC (Formalism.IndefR.Lev.levG (Formalism.IndefR.Links.Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α' R' ∧
      (∀ x, ∃ x', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x)) ∧
      (∀ y, ∃ y', (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
        Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y)) ∧
      ∀ x y x' y' : (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).H,
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e x) →
        (Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y' =
          Formalism.IndefR.Mult.heckeOn (Rl.MW i (Formalism.IndefR.Links.sg0 D A3.A)) R' ((Rl.HW i (Formalism.IndefR.Links.sg0 D A3.A)).e y) →
        ⟪x', y⟫_ℂ = ⟪x, y'⟫_ℂ := by
  first | exact @GlobalTheory.CxHeckeAdj.hecke_adjoint | exact GlobalTheory.CxHeckeAdj.hecke_adjoint | (intros; apply GlobalTheory.CxHeckeAdj.hecke_adjoint <;> assumption)
end
end
