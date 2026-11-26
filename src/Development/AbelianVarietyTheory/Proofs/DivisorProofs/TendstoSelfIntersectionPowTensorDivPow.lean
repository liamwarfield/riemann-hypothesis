module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairData
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.SelfInterGrowth

open MvPolynomial

theorem expand (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Φ ((X 0 + C t * X 1) ^ (D + 1)) = ∑ m ∈ Finset.range (D + 1 + 1),
      t ^ (D + 1 - m) * Φ (X 0 ^ m * X 1 ^ (D + 1 - m) * ((D + 1).choose m : MvPolynomial (Fin 2) ℝ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, ← map_pow, ← smul_eq_mul (a := t ^ _), ← map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  ring

theorem main : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (a : ℝ), L.IsSelfInter a → ∃ α : ℕ → ℝ, (∀ n, ((L.pow n).tens A).IsSelfInter (α n)) ∧ Tendsto (fun n : ℕ => α n / (n : ℝ) ^ (D + 1)) atTop (𝓝 a) := by
  intro hC k _ Y _ p D hX L A a ha
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![L, A]).1
  have hlin (n : ℕ) : (lin fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) = C (n : ℝ) * X 0 + C 1 * X 1 := by
    simp [lin, Fin.sum_univ_two]
  have hiso (n : ℕ) : (comb ![L, A] ![(n : ℤ), 1]).Isometric ((L.pow n).tens A) := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, HermLB.icls_tens, HermLB.icls_pow, Fin.sum_univ_two, natCast_zsmul]
  refine ⟨fun n => Φ (lin (fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) ^ (D + 1)), fun n => ?_, ?_⟩
  · exact (hiso n).isSelfInter hX (hΦ.1 _)
  have h0 : Φ (X 0 ^ (D + 1)) = a :=
    HermLB.IsSelfInter.unique hX ((((hC.arIso k Y p D hX).2 (Fin 2) _ Φ hΦ).1 0)) ha
  set f : ℝ → ℝ := fun t => Φ ((X 0 + C t * X 1) ^ (D + 1)) with hf
  have hfc : Continuous f := by
    have : f = fun t => ∑ m ∈ Finset.range (D + 1 + 1),
      t ^ (D + 1 - m) * Φ (X 0 ^ m * X 1 ^ (D + 1 - m) * ((D + 1).choose m : MvPolynomial (Fin 2) ℝ)) :=
      funext fun t => expand Φ D t
    rw [this]
    fun_prop
  have hf0 : f 0 = a := by simp [hf, h0]
  have hev : ∀ᶠ n : ℕ in atTop, f (1 / (n : ℝ)) = Φ (lin (fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) ^ (D + 1)) / (n : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have e : C (n : ℝ) * X 0 + C 1 * X 1 = C (n : ℝ) * (X 0 + C (1 / (n : ℝ)) * X 1 : MvPolynomial (Fin 2) ℝ) := by
      rw [mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hn']
    rw [hlin, e, mul_pow, ← map_pow, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hn')]
  have ht := (hfc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  rw [hf0] at ht
  exact ht.congr' hev

end GlobalTheory.SelfInterGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPowStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_selfIntersection_pow_tensor_div_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (a : ℝ), L.IsSelfInter a → ∃ α : ℕ → ℝ, (∀ n, ((L.pow n).tens A).IsSelfInter (α n)) ∧ Tendsto (fun n : ℕ => α n / (n : ℝ) ^ (D + 1)) atTop (𝓝 a) := by
  first | exact @GlobalTheory.SelfInterGrowth.main | exact GlobalTheory.SelfInterGrowth.main | (intros; apply GlobalTheory.SelfInterGrowth.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumParabolicQuotientFubini
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem split_quotient_finsum_regroup : ∀ (P M N V : Type) [Group P] [Group M] [Group N] [AddCommMonoid V] (lev : P →* M) (s : M →* P) (u : N →* P), (∀ m, lev (s m) = m) → (∀ x, lev (u x) = 1) → Function.Injective u → (∀ p, lev p = 1 → ∃ x, u x = p) → ∀ (UP : Subgroup P) (UM : Subgroup M), UM.map s ≤ UP → UP.map lev ≤ UM → ∀ (Φ : P → V), (∀ p, ∀ q ∈ UP, Φ (p * q) = Φ p) → {q : P ⧸ UP | Φ q.out ≠ 0}.Finite → ∑ᶠ q : P ⧸ UP, Φ q.out = ∑ᶠ c : M ⧸ UM, ∑ᶠ x : N ⧸ UP.comap u, Φ (s c.out * u x.out) := by
  intro P M N V _ _ _ _ lev s u hsec hlu _hu_inj hker UP UM hsU hlevU Φ hΦ hfin
  let F : (M ⧸ UM) × (N ⧸ UP.comap u) → P ⧸ UP :=
    fun cx => (QuotientGroup.mk (s cx.1.out * u cx.2.out) : P ⧸ UP)
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨c, x⟩ ⟨c', x'⟩ h
      simp only [F] at h
      rw [QuotientGroup.eq] at h
      have h1 : (c.out)⁻¹ * c'.out ∈ UM := by
        have := hlevU (Subgroup.mem_map_of_mem lev h)
        simpa [map_mul, map_inv, hsec, hlu] using this
      have hc : c = c' := by
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
        exact QuotientGroup.eq.mpr h1
      subst hc
      have h2 : (x.out)⁻¹ * x'.out ∈ UP.comap u := by
        rw [Subgroup.mem_comap]
        have he : (s c.out * u x.out)⁻¹ * (s c.out * u x'.out) = u ((x.out)⁻¹ * x'.out) := by
          rw [map_mul, map_inv]; group
        rw [← he]; exact h
      have hx : x = x' := by
        rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
        exact QuotientGroup.eq.mpr h2
      rw [hx]
    · intro q
      set p := q.out with hp
      set c : M ⧸ UM := (QuotientGroup.mk (lev p) : M ⧸ UM) with hc
      have hk : (c.out)⁻¹ * lev p ∈ UM := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      set k := (c.out)⁻¹ * lev p with hkdef
      have hr : lev ((s c.out)⁻¹ * p * (s k)⁻¹) = 1 := by
        simp only [map_mul, map_inv, hsec, hkdef]; group
      obtain ⟨Z, hZ⟩ := hker _ hr
      refine ⟨(c, (QuotientGroup.mk Z : N ⧸ UP.comap u)), ?_⟩
      obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul (UP.comap u) Z
      simp only [F]
      rw [hy, ← QuotientGroup.out_eq' q, ← hp, QuotientGroup.eq]
      have hyU : u (y : N) ∈ UP := y.2
      have hsk : s k ∈ UP := hsU (Subgroup.mem_map_of_mem s hk)
      have he : (s c.out * u (Z * y))⁻¹ * p = (u (y : N))⁻¹ * s k := by
        rw [map_mul, hZ]; group
      rw [he]
      exact UP.mul_mem (UP.inv_mem hyU) hsk
  let e := Equiv.ofBijective F hbij
  have hval : ∀ cx, Φ (e cx).out = Φ (s cx.1.out * u cx.2.out) := by
    intro cx
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul UP (s cx.1.out * u cx.2.out)
    show Φ (F cx).out = _
    simp only [F]; rw [hh]; exact hΦ _ _ h.2
  have hsupp : (Function.support
      (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out))).Finite := by
    have : Function.support
        (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out))
        = e ⁻¹' {q : P ⧸ UP | Φ q.out ≠ 0} := by
      ext cx; simp only [Function.mem_support, Set.mem_preimage, Set.mem_setOf_eq, hval]
    rw [this]; exact hfin.preimage e.injective.injOn
  rw [← finsum_comp_equiv e]
  rw [finsum_congr hval]
  exact finsum_curry (fun cx : (M ⧸ UM) × (N ⧸ UP.comap u) => Φ (s cx.1.out * u cx.2.out)) hsupp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodScalarOfIsAdelicScalar
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Source

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem span_jVx (hV : R.models_HV) (hj : R.models_jV) : Submodule.span ℂ (Set.range (jVx R i A.μ0)) = ⊤ := by
  have h0 : (R.HV i A.μ0).e '' Set.range (jVx R i A.μ0) = Set.range (R.B.jL i A.μ0) :=
    (Set.range_comp _ _).symm.trans (congrArg Set.range (funext (hj i A.μ0)))
  have h1 : (Submodule.span ℂ (Set.range (jVx R i A.μ0))).map (R.HV i A.μ0).e = (⊤ : Submodule ℂ _).map (R.HV i A.μ0).e :=
    ((Submodule.map_span _ _).trans (congrArg (Submodule.span ℂ) h0)).trans
      ((GlobalTheory.PresBasic.ext_span (R.B.L i A.μ0).pres).trans ((hV i A.μ0).2.1.symm.trans (LinearMap.range_eq_map _)))
  exact Submodule.map_injective_of_injective (hV i A.μ0).1 h1

end Source

section Target

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem eval_inj (hW : R.models_HW) {v₀ : (R.MW i (sg0 D A)).Vec} (hv : IsChosenExtremalVector R i (sg0 D A) v₀) {x y : (R.HW i (sg0 D A)).H}
    (h : (R.HW i (sg0 D A)).e x v₀ = (R.HW i (sg0 D A)).e y v₀) : x = y := by
  have h0 : (R.HW i (sg0 D A)).e (x - y) v₀ = 0 := by
    rw [LinearMap.map_sub]
    exact sub_eq_zero.2 h
  have h1 := (hW i (sg0 D A)).2.2 (x - y) (x - y)
  rw [ipAt, GlobalTheory.EvalAtUnitVector.ipM_self_eq_zero _ _ _ _ v₀ (IsChosenExtremalVector.norm R hv) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

theorem eC_idem (hr : R.grp_record) : GoodBasisCentralIdempotents.IsCentralIdem (RealDat.eC (A := A) (sg0 D A)) := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  have h0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : ∀ g, RealDat.eC (A := A) (sg0 D A) g = D.ntypes.e0.coeff (eR g) := fun g => by rw [h0]; exact h g
  obtain ⟨h2, h3⟩ := GlobalTheory.GoodLatCompare.isCentralIdempotent_of_goodSeriesIdempotent (D := D) (RingHom.id ℂ) (eC := fun g => D.ntypes.e0.coeff g) fun _ => rfl
  refine ⟨fun g k => ?_, fun g => ?_⟩
  · rw [h1, h1, map_mul eR, map_mul eR, map_inv eR]
    exact h2 _ _
  · rw [h1]
    refine Eq.trans (Fintype.sum_equiv eR.toEquiv _ _ fun k => ?_) (h3 (eR g))
    rw [h1, h1, map_mul eR, map_inv eR]
    rfl

theorem postOn_of_good {P : LevelP R.Pg D.R.r ℂ} {U : MMap (R.MW i (sg0 D A))} (hU : U ∈ R.Wat i (sg0 D A) P) :
    postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) U = U :=
  sub_eq_zero.1 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hU).2)

end Target

section Geometric

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

structure DictFacts : Prop where
  dom : ∀ g, (O.dict g).2 ∈ ((C.U ((i : ℕ) + 1) O.s0).X (O.dict g).1).dom
  mu : ∀ g, ‖O.mu g‖ = 1
  cc : ∀ k, ‖cc k‖ = 1
  lifts : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv)

variable {O cc} (hd : DictFacts O cc)
include hd

omit hd

variable (O cc)

variable {O cc}

include hd

omit hd

end Geometric

section Main

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

variable {T R F κ v₀ O}

variable (T R F κ v₀ O)

end Main

end GlobalTheory.LiftScalarCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycle
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecCycle

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh

theorem coheight_eq_one_of_dim_closure {X : Scheme.{0}} {n : ℕ}
    (hX : topologicalKrullDim X ≤ (n + 1 : ℕ)) {w : X} (hw : ¬ IsMax w)
    (hd : topologicalKrullDim (closure ({w} : Set X)) = n) : Order.coheight w = 1 := _root_.GlobalTheory.CompanionTheory.Ar.IntersectionMultiplicitySection.coheight_eq_one_of_dim_closure (X := X) (n := n) (w := w) hX hw hd

open scoped Pointwise

theorem mult_divOfSec_eq_length_cut {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {M : LB X} (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {w : X}
    (hw : Order.coheight w = 1) :
    (divOfSec hM s hs).mult w = ((Module.length (X.presheaf.stalk w)
      ((cut (structureModule X) hM s).presheaf.stalk w :)).toNat : ℤ) := _root_.GlobalTheory.CompanionTheory.Ar.IntersectionMultiplicitySection.mult_divOfSec_eq_length_cut (X := X) (M := M) (w := w) hM s hs hw

theorem mult_divOfSec_ne_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {M : LB X} (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {w : X}
    (hw : Order.coheight w = 1) (hws : w ∉ nonzeroLocus s) : (divOfSec hM s hs).mult w ≠ 0 := _root_.GlobalTheory.CompanionTheory.Ar.IntersectionMultiplicitySection.mult_divOfSec_ne_zero (X := X) (M := M) (w := w) hM s hs hw hws

theorem interNum_cons_eq_finsum_mult : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (s : M.Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfSec hM s hs).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ _ _ hproj n hX M hM P hP s hs
  have hf := algebraMap_eq_strHom κ X
  have := isNoetherian_of_isProjOver hproj
  have : IsProper (strHom κ (X := X)) := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hproj
  have hmono := (mono_cutHom_structureModule_iff hM s).2 hs
  have hfin : FiniteCohTwists κ (structureModule X) := hH.finiteCohTwists hf _
  rw [interNum_cons_eq_interNum_cut hM s hP hfin]
  have hsupp : suppDim (cut (structureModule X) hM s) ≤ (Fintype.card (Fin n) : ℕ) := by
    rw [Fintype.card_fin]
    exact suppDim_cut_le _ hM s (by rwa [QCoh.suppDim_structureModule])
  have hfs := (divOfSec hM s hs).finite_support_mult
  have hS : ∀ w ∈ support (cut (structureModule X) hM s),
      topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card (Fin n) : ℕ) → w ∈ hfs.toFinset := by
    intro w hw hd
    rw [Fintype.card_fin] at hd
    rw [support_cut, QCoh.support_structureModule] at hw
    have hmax : ¬ IsMax w := fun h => hw.2 ((h (genericPoint_specializes w) :
      w ⤳ genericPoint X).mem_open (nonzeroLocus s).isOpen hs)
    have hc := coheight_eq_one_of_dim_closure hX hmax hd
    simpa using mult_divOfSec_ne_zero hM s hs hc hw.2
  rw [T.intersectionNumber_sheaf_eq_sum_length_mul_cycle κ X hproj (Fin n) P hP _ hsupp hfs.toFinset hS,
    finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_]
  · refine Finset.sum_congr rfl fun w hw => ?_
    have hw' : (divOfSec hM s hs).mult w ≠ 0 := by simpa using hw
    rw [mult_divOfSec_eq_length_cut hM s hs (CartierDiv.coheight_eq_one_of_mult_ne_zero hw')]
  · intro w hw
    simpa using Function.support_mul_subset_left _ _ hw

end GlobalTheory.SecCycle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_globalSection_eq_sum_cycle : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (s : M.Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfSec hM s hs).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult | exact GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult | (intros; apply GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

section Fields

variable {T : Type} {n : ℕ}


open Classical in
def matDer (τ : T) (X : Matrix (Fin n) (Fin n) ℂ) :
    Derivation ℂ (MvPolynomial (T × Fin n × Fin n) ℂ) (MvPolynomial (T × Fin n × Fin n) ℂ) :=
  MvPolynomial.mkDerivation ℂ fun p =>
    if p.1 = τ then ∑ m, MvPolynomial.X (τ, p.2.1, m) * MvPolynomial.C (X m p.2.2) else 0

open Classical in
theorem matDer_X (τ : T) (X : Matrix (Fin n) (Fin n) ℂ) (p : T × Fin n × Fin n) :
    matDer τ X (MvPolynomial.X p) =
      if p.1 = τ then ∑ m, MvPolynomial.X (τ, p.2.1, m) * MvPolynomial.C (X m p.2.2) else 0 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem matDer_add (τ : T) (X Y : Matrix (Fin n) (Fin n) ℂ) : matDer τ (X + Y) = matDer τ X + matDer τ Y := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.add_apply, matDer_X, matDer_X, matDer_X]
  split_ifs
  · simp [mul_add, Finset.sum_add_distrib]
  · simp

theorem matDer_smul (τ : T) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : matDer τ (c • X) = c • matDer τ X := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.smul_apply, matDer_X, matDer_X]
  split_ifs
  · simp only [Matrix.smul_apply, smul_eq_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.C_mul, MvPolynomial.smul_eq_C_mul]; ring
  · simp

theorem matDer_bracket (τ : T) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⁅matDer τ X, matDer τ Y⁆ = matDer τ (X * Y - Y * X) := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.commutator_apply, matDer_X, matDer_X, matDer_X]
  split_ifs with h
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, Derivation.leibniz, MvPolynomial.derivation_C, smul_zero, zero_add, matDer_X, if_true,
      smul_eq_mul, Finset.sum_mul, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, MvPolynomial.C_mul,
      Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_zero, zero_add]
      refine congrArg₂ (· - ·) ?_ ?_ <;> rw [Finset.sum_comm] <;>
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · simp

theorem matDer_comm {τ τ' : T} (h : τ ≠ τ') (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⁅matDer τ X, matDer τ' Y⁆ = 0 := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.commutator_apply, matDer_X, matDer_X, Derivation.zero_apply]
  by_cases h1 : p.1 = τ <;> by_cases h2 : p.1 = τ' <;>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [h1, h2, h, Ne.symm h, map_sum, Derivation.leibniz, MvPolynomial.derivation_C, matDer_X]

theorem matDer_commute {τ τ' : T} (h : τ ≠ τ') (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Commute (matDer τ X : Module.End ℂ (MvPolynomial (T × Fin n × Fin n) ℂ)) (matDer τ' Y) := by
  refine LinearMap.ext fun a => ?_
  have := congrArg (fun D : Derivation ℂ _ _ => D a) (matDer_comm h X Y)
  simp only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] at this
  exact this

end Fields

section Reps

variable {D : D7}

abbrev PolyE (V : HSp D) : Type := MvPolynomial (D.what₂.Tau × Fin V.rank × Fin V.rank) ℂ

def realEntries (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) :
    D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ :=
  fun p => infMat D.sp.cm.sig V.gram (θ p.1) g p.2.1 p.2.2

def polyFun (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (P : PolyE V) : GA D V → ℂ :=
  fun g => MvPolynomial.eval (realEntries θ V g) P

theorem exists_placeRep (V : HSp D) (τ : D.what₂.Tau) : ∃ π : EnvAt V τ →ₐ[ℂ] Module.End ℂ (PolyE V),
    ∀ X : LieAt V τ, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = (matDer τ X.1 : Module.End ℂ (PolyE V)) := by
  refine GlobalTheory.EnvelopingExtension.exists_algHom_unitary _ _ _ (fun X : LieAt V τ => (matDer τ X.1 : Module.End ℂ (PolyE V)))
    (fun X Y => LinearMap.ext fun a => ?_) (fun c X => LinearMap.ext fun a => ?_) (fun X Y Z h => LinearMap.ext fun a => ?_)
  · change matDer τ (X.1 + Y.1) a = matDer τ X.1 a + matDer τ Y.1 a
    rw [matDer_add]; rfl
  · have e : ((c • X : LieAt V τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (c : ℂ) • X.1 := by
      ext i j; simp [Complex.real_smul]
    change matDer τ ((c • X : LieAt V τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) a = (c : ℂ) • matDer τ X.1 a
    rw [e, matDer_smul]; rfl
  · change matDer τ Z.1 a = matDer τ X.1 (matDer τ Y.1 a) - matDer τ Y.1 (matDer τ X.1 a)
    rw [h, ← matDer_bracket, Derivation.commutator_apply]

def placeRep (V : HSp D) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] Module.End ℂ (PolyE V) := (exists_placeRep V τ).choose

theorem placeRep_ι (V : HSp D) (τ : D.what₂.Tau) (X : LieAt V τ) :
    placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = (matDer τ X.1 : Module.End ℂ (PolyE V)) :=
  (exists_placeRep V τ).choose_spec X

theorem placeRep_tmul (V : HSp D) (τ : D.what₂.Tau) (c : ℂ) (X : LieAt V τ) :
    placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] X)) = c • (matDer τ X.1 : Module.End ℂ (PolyE V)) := by
  rw [show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul,
    placeRep_ι]

theorem placeRep_comm (V : HSp D) {τ τ' : D.what₂.Tau} (h : τ ≠ τ') (x : ℂ ⊗[ℝ] LieAt V τ) (y : ℂ ⊗[ℝ] LieAt V τ') :
    Commute (placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x)) (placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _)]; exact hx.add_left hx'
  | tmul c X =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [map_add (f := _), map_add (f := _)]; exact hy.add_right hy'
    | tmul c' Y =>
      rw [placeRep_tmul, placeRep_tmul]
      exact ((matDer_commute h X.1 Y.1).smul_left c).smul_right c'


open Classical in
def polyLie (V : HSp D) : GlobalTheory.AutFinLit.LieC V →ₗ⁅ℂ⁆ Module.End ℂ (PolyE V) :=
  DirectSum.toLieAlgebra _ (fun τ => (placeRep V τ).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)) fun τ τ' h x y => by
    change placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) * placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y) -
      placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y) * placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) = 0
    rw [(placeRep_comm V h x y).eq, sub_self]

def polyRep (V : HSp D) : GlobalTheory.AutFinLit.Env V →ₐ[ℂ] Module.End ℂ (PolyE V) :=
  UniversalEnvelopingAlgebra.lift ℂ (polyLie V)

open Classical in
theorem polyRep_ι_of (V : HSp D) (τ : D.what₂.Tau) (x : ℂ ⊗[ℝ] LieAt V τ) :
    polyRep V (UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x)) =
      placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) := by
  rw [polyRep, UniversalEnvelopingAlgebra.lift_ι_apply, polyLie]
  exact DirectSum.toModule_lof ℂ (M := fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x

end Reps

end GlobalTheory.CentralOps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIff
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
open IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IntCoefExt

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem nval_nonneg_iff {e : ℕ} (he : 0 < e) (x : K') : 0 ≤ nval V e x ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    simp [nval_zero, vV]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ he', zero_mul]
  exact_mod_cast Iff.rfl

theorem exists_nat_pos {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {ι : K →+* K'} {e : ℕ}
    (ho : OverLa la V ι e) : ∃ N : ℕ, N ≠ 0 ∧ 0 < vV V (N : K') := by
  have hN : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm la.asIdeal, hN, ?_⟩
  have h1 := ho.2 (Ideal.absNorm la.asIdeal : K)
  rw [map_natCast] at h1
  rw [h1]
  refine mul_pos (by exact_mod_cast ho.1) ?_
  have h2 : la.valuation K (Ideal.absNorm la.asIdeal : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) _).2 (Ideal.absNorm_mem la.asIdeal)
    simpa using this
  have h0 : la.valuation K (Ideal.absNorm la.asIdeal : K) ≠ 0 := by
    simpa using hN
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
  simp only [vLa]
  omega

theorem exists_overLa {K : Type} [Field K] [NumberField K] (ι : K →+* K') {N : ℕ} (hN : N ≠ 0)
    (h : 0 < vV V (N : K')) : ∃ (la : HeightOneSpectrum (𝓞 K)) (e : ℕ), OverLa la V ι e := by
  let u := (valV V (K' := K')).comap ι
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.CommonValuation.exists_centre u
  have hN' : (N : K') ≠ 0 := by
    rw [← map_natCast ι]
    exact (map_ne_zero ι).2 (Nat.cast_ne_zero.2 hN)
  have hNQ : (N : 𝓞 K) ∈ Q := by
    rw [hQm, map_natCast]
    show valV V (ι N) < 1
    rw [map_natCast, ← WithZero.exp_log (valV_ne_zero (V := V) hN'), ← WithZero.exp_zero, WithZero.exp_lt_exp]
    simp only [vV] at h
    omega
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hN (Nat.cast_eq_zero.1 ((Submodule.mem_bot _).1 hNQ))
  let la : HeightOneSpectrum (𝓞 K) := ⟨Q, hQ, h0⟩
  obtain ⟨e, he, hv⟩ := GlobalTheory.CommonValuation.exists_eq_pow la u
    (GlobalTheory.CommonValuation.le_one_of_ringOfIntegers u) (fun r => (hQm r).symm)
  refine ⟨la, e, he, fun a => ?_⟩
  have := hv a
  rw [Valuation.comap_apply] at this
  simp only [vV, vLa, this, WithZero.log_pow, nsmul_eq_mul]
  ring

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem integral_res_iff (T : CDVR) (io' : c'.F →+* T.Fr) (io : c.F →+* T.Fr)
    (h : ∀ a, io' (incF c c' hle a) = io a) (y : letI := io'.toAlgebra; FrPt Xo c' T.Fr) :
    Integral T io' y ↔ Integral T io (letI := io.toAlgebra; letI := io'.toAlgebra; y.res hle h) := by
  have e : ∀ (G : SAB H (Sp T.V)) τ v, IsEigV c' io' G τ v ↔ IsEigV c io G τ v := fun G τ v => by
    unfold IsEigV
    simp only [← embK_incF hle τ, h]
  constructor
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).1 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).2 he), h4⟩, h5⟩
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).2 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).1 he), h4⟩, h5⟩

theorem intAt_iff (f : Rul Xo c) : IntAt Xo c f ↔ ∀ (T : CDVR) (io : c.F →+* T.Fr) (N : ℕ), N ≠ 0 →
    0 < vV T.V (N : T.Fr) → T.FinRes → ∀ y : IntFr Xo c T io, 0 ≤ vV T.V (evI y f) := by
  constructor
  · intro h T io N hN hp hT y
    obtain ⟨la, e, ho⟩ := exists_overLa io hN hp
    exact (nval_nonneg_iff ho.1 _).1 (h la _ ⟨PtV.mk la ho y hT () trivial, rfl⟩)
  · rintro h la _ ⟨⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩, rfl⟩
    obtain ⟨N, hN, hp⟩ := exists_nat_pos ho
    exact (nval_nonneg_iff ho.1 _).2 (h T io N hN hp hy y)

theorem intAt_rulBC_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, (IntAt Xo c' (rulBC hle f) ↔ IntAt Xo c f) := by
  intro E _ _ _ H Dw l Xo c c' hle a n f hf
  have hval := ((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2
  rw [intAt_iff, intAt_iff]
  constructor
  · intro h T io N hN hp hT y
    letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
    haveI := c.fin
    haveI := c'.fin
    haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun x => by simp
    haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ _ _
    obtain ⟨L, _, _, g, hL, -, hg⟩ := GlobalTheory.exists_finite_separable_compositum c.F T.Fr c'.F io
    obtain ⟨T', iT, e, ψ, -, he, hv, hψ, -, hfin⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
    obtain ⟨⟨y₁, -, -, φ, hφ, hm⟩, -⟩ := GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw l Xo c T T' io y iT e he hv
    let io' : c'.F →+* T'.Fr := ψ.toRingHom.comp g
    have hio : ∀ x, io' (incF c c' hle x) = (iT.comp io) x := fun x => by
      have := DFunLike.congr_fun hg x
      exact (congrArg ψ this).trans (hψ _)
    have hp' : 0 < vV T'.V (N : T'.Fr) := by
      rw [← map_natCast iT, hv]
      exact mul_pos (by exact_mod_cast he) hp
    have e1 : evI y₁ f = iT (evI y f) := by
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      exact (pos_evR (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φ y.1 y.2.1 y₁.1 hm).trans
        (DFunLike.congr_fun hφ _)
    letI := (iT.comp io).toAlgebra
    letI := io'.toAlgebra
    let y' : IntFr Xo c' T' io' := ⟨y₁.1.ext hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      (integral_res_iff hle T' io' (iT.comp io) hio _).2 y₁.2.2⟩
    have e2 : evI y' (rulBC hle f) = evI y₁ f := hval T'.Fr hio y'.1
    have key := h T' io' N hN hp' (hfin hT) y'
    rw [e2, e1, hv] at key
    exact nonneg_of_mul_nonneg_right key (by exact_mod_cast he)
  · intro h T io' N hN hp hT y'
    let io : c.F →+* T.Fr := io'.comp (incF c c' hle)
    have hio : ∀ x, io' (incF c c' hle x) = io x := fun _ => rfl
    letI := io.toAlgebra
    letI := io'.toAlgebra
    let y : IntFr Xo c T io := ⟨y'.1.res hle hio, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      (integral_res_iff hle T io' io hio _).1 y'.2.2⟩
    have e2 : evI y' (rulBC hle f) = evI y f := hval T.Fr hio y'.1
    rw [e2]
    exact h T io N hN hp hT y

end GlobalTheory.IntCoefExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIffStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralRule_ruleBaseChangeCoeffField_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, (IntAt Xo c' (rulBC hle f) ↔ IntAt Xo c f) := by
  first | exact @GlobalTheory.IntCoefExt.intAt_rulBC_iff | exact GlobalTheory.IntCoefExt.intAt_rulBC_iff | (intros; apply GlobalTheory.IntCoefExt.intAt_rulBC_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem exists_localEqn_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), ∀ (D : X → ℚ), IsQCart D → ∀ x : X, ∃ (m : ℕ) (f : X.functionFieldˣ), 0 < m ∧ RegAt x (f : X.functionField) ∧ ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m := by
  intro X _ _ p D hD x
  obtain ⟨m, D₀, hm, hEff, rfl⟩ := hD
  obtain ⟨f, hf⟩ := D₀.exists_isEqn x
  obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
  refine ⟨m, f, hm, CartierDiv.eff_iff.1 hEff x f hf, fun z hz E hE => ?_⟩
  rw [qWeil, (hfV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), ∀ (D : X → ℚ), IsQCart D → ∀ x : X, ∃ (m : ℕ) (f : X.functionFieldˣ), 0 < m ∧ RegAt x (f : X.functionField) ∧ ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m := by
  first | exact @GlobalTheory.PairStep.exists_localEqn_of_isQCart | exact GlobalTheory.PairStep.exists_localEqn_of_isQCart | (intros; apply GlobalTheory.PairStep.exists_localEqn_of_isQCart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultiple
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PairStep

theorem eff_divOfSec_of_sec {X : Scheme.{0}} [IsIntegral X] {L : LB X} (hL : L.IsLB) (s : L.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) : (divOfSec hL s hs).Eff := by
  refine CartierDiv.eff_iff.2 fun y g hg => ?_
  obtain ⟨i, hi⟩ := exists_chart hL y
  have h1 := (presents_divOfRatSec hL (isRatSec_ratOfSec s hs)).isEqn i y hi
  have hu := h1.iff_unitAt.1 hg
  have hr : RegAt y (ratOfSec s hs i : X.functionField) := by
    rw [val_ratOfSec (gen_mem hi)]
    exact regAt_fnOf hi (gen_mem hi) _
  have := hu.regAt.mul hr
  rwa [div_mul_cancel₀ _ (Units.ne_zero _)] at this

theorem qNum_divOfSec : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (hN : N.IsLB) (l m : ℕ) (s : (lbPow N l).Sec) (hs : genericPoint X ∈ nonzeroLocus s), 0 < m → (divOfSec (isLB_lbPow hN l) s hs).Eff ∧ QNum p N ((l : ℚ) / m) (qWeil (divOfSec (isLB_lbPow hN l) s hs) m) := by
  intro X _ _ p hp N hN l m s hs hm
  have hE := eff_divOfSec_of_sec (isLB_lbPow hN l) s hs
  refine ⟨hE, m, _, hm, hE, rfl, fun C hC => ?_⟩
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  letI := algebraΓOfHom p
  have hcls : toPic (divOfSec (isLB_lbPow hN l) s hs) = cls _ (isLB_lbPow hN l) :=
    (presents_divOfRatSec (isLB_lbPow hN l) (isRatSec_ratOfSec s hs)).toPic_eq
  rw [interNumRed_one_congr (isLB_toLB _) (isLB_lbPow hN l) hcls, hC.interNumRed_lbPow hH hN l]
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultipleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDivOfGlobalSection_pow_numEquiv_multiple : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (hN : N.IsLB) (l m : ℕ) (s : (lbPow N l).Sec) (hs : genericPoint X ∈ nonzeroLocus s), 0 < m → (divOfSec (isLB_lbPow hN l) s hs).Eff ∧ QNum p N ((l : ℚ) / m) (qWeil (divOfSec (isLB_lbPow hN l) s hs) m) := by
  first | exact @GlobalTheory.PairStep.qNum_divOfSec | exact GlobalTheory.PairStep.qNum_divOfSec | (intros; apply GlobalTheory.PairStep.qNum_divOfSec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGalois
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Published.AbVarRed

def ptOverMap {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') :
    ptOver K Ω' ⟶ ptOver K Ω :=
  Over.homMk (spMap (j : Ω →+* Ω')) (by
    change spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp)

theorem epi_ptOverMap {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') :
    Epi (ptOverMap j).left := by
  change Epi (spMap (j : Ω →+* Ω'))
  letI := (j : Ω →+* Ω').toAlgebra
  haveI : Flat (spMap (j : Ω →+* Ω')) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat Ω Ω')
  haveI : Surjective (spMap (j : Ω →+* Ω')) :=
    ⟨fun p => ⟨(⊥ : PrimeSpectrum Ω'), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem ptOverMap_comp_specAut {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω']
    (j : Ω →ₐ[K] Ω') (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω') (h : ∀ x, σ' (j x) = j (σ x)) :
    ptOverMap j ≫ specAut σ = specAut σ' ≫ ptOverMap j :=
  Over.OverMorphism.ext (by
    change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (h x).symm)

theorem exists_injective_ptOver_galois : ∀ (K Ω Ω' : Type) [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') (A : Over (Sp K)) [GrpObj A], ∃ f : (ptOver K Ω ⟶ A) →* (ptOver K Ω' ⟶ A), Function.Injective f ∧ ∀ (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω'), (∀ x, σ' (j x) = j (σ x)) → ∀ x, f (specAut σ ≫ x) = specAut σ' ≫ f x := by
  intro K Ω Ω' _ _ _ _ _ j A _
  refine ⟨MonoidHom.mk' (fun x => ptOverMap j ≫ x) fun x y => MonObj.comp_mul _ x y, ?_, ?_⟩
  · intro x y e
    have := epi_ptOverMap j
    exact Over.OverMorphism.ext ((cancel_epi (ptOverMap j).left).1
      (by simpa using congrArg (fun q => q.left) (show ptOverMap j ≫ x = ptOverMap j ≫ y from e)))
  · intro σ σ' h x
    change ptOverMap j ≫ specAut σ ≫ x = specAut σ' ≫ ptOverMap j ≫ x
    rw [← Category.assoc, ptOverMap_comp_specAut j σ σ' h, Category.assoc]

end GlobalTheory.Published.AbVarRed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGaloisStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_points_larger_field_galois : ∀ (K Ω Ω' : Type) [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') (A : Over (Sp K)) [GrpObj A], ∃ f : (ptOver K Ω ⟶ A) →* (ptOver K Ω' ⟶ A), Function.Injective f ∧ ∀ (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω'), (∀ x, σ' (j x) = j (σ x)) → ∀ x, f (specAut σ ≫ x) = specAut σ' ≫ f x := by
  first | exact @GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois | exact GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois | (intros; apply GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairDataStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringEquiv_transports_varietyPair_data : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'),
  (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (R : Subring K) (φ : K →₀ ℚ), TrBasis c x →
  TrBasis c' (e ∘ x) ∧
  (IsLocModel c R ↔ IsLocModel c' (R.map e.toRingHom)) ∧
  (Klt c n R (dForm c x) φ ↔ Klt c' n (R.map e.toRingHom) (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ)) ∧
  (EffAt c n R (dForm c x) φ ↔ EffAt c' n (R.map e.toRingHom) (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ)) := by
  first | exact @GlobalTheory.FieldPair.transport_ringEquiv | exact GlobalTheory.FieldPair.transport_ringEquiv | (intros; apply GlobalTheory.FieldPair.transport_ringEquiv <;> assumption)
end
