module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAtTypeAndOrd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDetBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerFactorEqOneOfExpAt
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

def StdSupp (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : Prop :=
  (∀ i j, x.toRows₁ i j ∈ 𝒪[k]) ∧ valuation k x.toRows₁.det = 1 ∧ ∀ i j, x.toRows₂ i j ∈ cball (ϖ ^ c)

theorem StdSupp.det_ne {ϖ : kˣ} {c : ℕ} {x : Matrix (Fin n ⊕ Fin n') (Fin n) k} (h : StdSupp ϖ c x) :
    x.toRows₁.det ≠ 0 := fun h0 => by
  have := h.2.1
  rw [h0, map_zero] at this
  exact zero_ne_one this


open Classical in
def stdDatum (μ : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : ℂ :=
  if h : StdSupp ϖ c x then (((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ) else 0

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open GlobalTheory.SplitFlip (omA omB invT IsUnif mem_KO_iff isOpen_KO)
open GlobalTheory.StdLocZeta (StdSupp stdDatum)
open GlobalTheory.StdLoc (glVol blockIdx)
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.LocStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Renumber

variable {X a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b'] [MeasurableSpace X]

end Renumber

section Level

variable {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

theorem mem_image_KO {M : Matrix D D k} :
    M ∈ Units.val '' (KO k D : Set (GL D k)) ↔ (∀ i j, M i j ∈ 𝒪[k]) ∧ valuation k M.det = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨((mem_KO_iff g).1 hg).1, SplitFlip.valuation_gdet_of_mem_KO hg⟩
  · rintro ⟨hM, hd⟩
    let N : Matrix D D 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
    have e : (algebraMap 𝒪[k] k).mapMatrix N = M := rfl
    have hu : IsUnit N.det := by
      refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
      rw [RingHom.map_det, e, hd]
    obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det N).2 hu
    refine ⟨_, ⟨u, rfl⟩, ?_⟩
    change (algebraMap 𝒪[k] k).mapMatrix u.val = M
    rw [hu', e]

theorem mem_KO_iff_det {g : GL D k} : g ∈ KO k D ↔ (∀ i j, g.val i j ∈ 𝒪[k]) ∧ valuation k g.val.det = 1 := by
  rw [← mem_image_KO]
  exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨u, hu, e⟩ => Units.ext e ▸ hu⟩



variable {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (σ : A ⊕ A' ≃ D)

variable [MeasurableSpace k] [BorelSpace k]

end Level

section Pair

variable {n n' : ℕ} {D : Type} [Fintype D] [DecidableEq D]

def colDatum (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D) (X : Matrix (Fin n) D k) : ℂ :=
  stdDatum ν ϖ c (Xᵀ.submatrix σ id)

variable (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (σ : Fin n ⊕ Fin n' ≃ D)


omit [Fintype D] [DecidableEq D] in
theorem colDatum_eq {X : Matrix (Fin n) D k} {u : GL (Fin n) k} (hu : u ∈ KO k (Fin n))
    (h₁ : ∀ i j, X i (σ (.inl j)) = u.val i j) (h₂ : ∀ i j, X i (σ (.inr j)) ∈ cball (ϖ ^ c)) :
    colDatum ν ϖ c σ X = (((ν (GeneralLinearGroup.det u))⁻¹ : ℂˣ) : ℂ) := by
  have e : (Xᵀ.submatrix σ id).toRows₁ = u.valᵀ := by ext i j; exact h₁ j i
  have h : StdSupp ϖ c (Xᵀ.submatrix σ id) :=
    ⟨fun i j => by rw [e]; exact (mem_KO_iff_det.1 hu).1 j i, by rw [e, det_transpose]; exact (mem_KO_iff_det.1 hu).2,
      fun i j => h₂ j i⟩
  rw [colDatum, stdDatum, dite_eq_left h]
  congr 3
  exact Units.ext (by simp [e])

variable [MeasurableSpace k] [BorelSpace k] {m : Measure k}

variable {ν ϖ}


end Pair

section Main

variable {a a' : ℕ} {D : Type} [Fintype D] [DecidableEq D]

end Main

section Place

open IsDedekindDomain NumberField GlobalTheory.CMVal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Place

end GlobalTheory.LocStd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFunOfTransvectionConstantTermsZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFunOfTransvectionConstantTermsZero
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvCusp

section Abstract

variable {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
  {Γ : Subgroup N} [Countable Γ] {μ : Measure N} [μ.IsMulLeftInvariant] {𝓕 : Set N}

theorem fd_preimage (h : IsFundamentalDomain Γ 𝓕 μ) {z : N} (hz : ∀ n, z * n = n * z) :
    IsFundamentalDomain Γ ((fun n => z * n) ⁻¹' 𝓕) μ :=
  h.preimage_of_equiv (measurePreserving_mul_left μ z).quasiMeasurePreserving (e := id) Function.bijective_id
    fun γ n => by
      change z * ((γ : N) * n) = (γ : N) * (z * n)
      rw [← mul_assoc, hz, mul_assoc]

theorem inv_shift {B : Type} {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n)
    (γ : Γ) (n : N) : F (z * (γ • n)) = F (z * n) := by
  change F (z * ((γ : N) * n)) = _
  rw [← mul_assoc, hz, mul_assoc, hF]

theorem setIntegral_shift {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] (h : IsFundamentalDomain Γ 𝓕 μ)
    {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n) :
    ∫ n in 𝓕, F (z * n) ∂μ = ∫ n in 𝓕, F n ∂μ := by
  rw [h.setIntegral_eq (fd_preimage h hz) (f := fun n => F (z * n)) (inv_shift hz hF)]
  exact (measurePreserving_mul_left μ z).setIntegral_preimage_emb (MeasurableEquiv.mulLeft z).measurableEmbedding F 𝓕

theorem integrableOn_shift {B : Type} [NormedAddCommGroup B] (h : IsFundamentalDomain Γ 𝓕 μ)
    {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n)
    (hi : IntegrableOn F 𝓕 μ) : IntegrableOn (fun n => F (z * n)) 𝓕 μ := by
  rw [h.integrableOn_iff (fd_preimage h hz) (f := fun n => F (z * n)) (inv_shift hz hF)]
  exact ((measurePreserving_mul_left μ z).integrableOn_comp_preimage
    (MeasurableEquiv.mulLeft z).measurableEmbedding).2 hi

theorem setIntegral_eq_zero [SecondCountableTopology N] [SFinite μ] {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] (ν : Measure Z) [IsFiniteMeasure ν] (hν : ν ≠ 0) (i : Z → N) (hi : Continuous i)
    (hz : ∀ z n, i z * n = n * i z) (h : IsFundamentalDomain Γ 𝓕 μ) {F : N → ℂ} (hc : Continuous F)
    (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n) (h0 : ∀ n, ∫ z, F (i z * n) ∂ν = 0) : ∫ n in 𝓕, F n ∂μ = 0 := by
  by_cases hI : IntegrableOn F 𝓕 μ
  swap
  · exact integral_undef hI
  have hm : AEStronglyMeasurable (Function.uncurry fun (z : Z) (n : N) => F (i z * n)) (ν.prod (μ.restrict 𝓕)) :=
    (hc.comp ((hi.comp continuous_fst).mul continuous_snd)).aestronglyMeasurable
  have hp : Integrable (Function.uncurry fun (z : Z) (n : N) => F (i z * n)) (ν.prod (μ.restrict 𝓕)) := by
    refine (integrable_prod_iff hm).2 ⟨Filter.Eventually.of_forall fun z => integrableOn_shift h (hz z) hF hI, ?_⟩
    have e : (fun z : Z => ∫ n in 𝓕, ‖F (i z * n)‖ ∂μ) = fun _ => ∫ n in 𝓕, ‖F n‖ ∂μ :=
      funext fun z => setIntegral_shift h (hz z) (F := fun n => ‖F n‖) fun γ n => by rw [hF]
    exact e ▸ integrable_const _
  have key := integral_integral_swap hp
  simp only [h0, integral_zero, setIntegral_shift h (hz _) hF, integral_const, smul_eq_zero] at key
  exact key.resolve_left (by simpa [measureReal_eq_zero_iff] using hν)

end Abstract

section Mat

variable {R : Type} [CommRing R] {n r : ℕ} {m m' : Matrix (Fin n) (Fin n) R} {a : R} {C : Matrix (Fin n) (Fin r) R}
  {E : Matrix (Fin r) (Fin r) R} {P : Matrix (Fin r) (Fin n) R}

theorem mat_kill (ha : m = a • (C * E * P)) (h0 : P * C = 0) :
    m * C = 0 ∧ P * m = 0 ∧ ∀ x, P *ᵥ x = 0 → m *ᵥ x = C *ᵥ 0 := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [ha, Matrix.smul_mul, Matrix.mul_assoc, h0, Matrix.mul_zero, smul_zero]
  · rw [ha, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.zero_mul, smul_zero]
  · rw [ha, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, smul_zero, Matrix.mulVec_zero]

theorem mat_comm (ha : m - 1 = a • (C * E * P)) (h1 : (m' - 1) * C = 0) (h2 : P * (m' - 1) = 0) :
    m * m' = m' * m := by
  have e : Commute (m - 1) (m' - 1) := by
    rw [Commute, SemiconjBy, ha, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, h2, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, h1, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have := (e.add_left (Commute.one_left _)).add_right (Commute.one_right _)
  rw [sub_add_cancel, sub_add_cancel] at this
  exact this

theorem commute_closure {G : Type} [Group G] {s t : Set G} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {x y : G}
    (hx : x ∈ Subgroup.closure s) (hy : y ∈ Subgroup.closure t) : Commute x y := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h x hx y hy
    | one => exact Commute.one_right _
    | mul _ _ _ _ k k' => exact k.mul_right k'
    | inv _ _ k => exact k.inv_right
  | one => exact Commute.one_left _
  | mul _ _ _ _ k k' => exact k.mul_left k'
  | inv _ _ k => exact k.inv_left

end Mat

section Algebra

variable {D : D7} (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}

theorem vecMulVec_col (j : Fin r) :
    vecMulVec (fun i => C i j) ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (C i j)) ᵥ* V.gram) =
      C * Matrix.single j j (1 : D.host.E) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_single_apply_same, mul_one]
    rfl
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, zero_mul]
  · exact fun h => absurd (Finset.mem_univ j) h

theorem isoVec_col (hC : IsIsoFrame V C) (j : Fin r) : IsoVec V fun i => C i j := by
  refine ⟨hC.2.1.ne_zero j, ?_⟩
  have := congrFun (congrFun hC.2.2 j) j
  rw [Matrix.mul_assoc] at this
  exact this

theorem ZI_le (hC : IsIsoFrame V C) (j : Fin r) : ZI V (fun i => C i j) ≤ NI V C := by
  refine Subgroup.closure_mono ?_
  rintro g ⟨a, ha⟩
  have h0 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * C.map (incA D) = 0 := by
    rw [← Matrix.map_mul, hC.2.2, Matrix.map_zero _ (map_zero _)]
  rw [vecMulVec_col, Matrix.map_mul, Matrix.map_mul] at ha
  obtain ⟨k1, k2, k3⟩ := mat_kill ha h0
  refine ⟨k1, k2, fun x hx => ⟨0, k3 _ (funext fun i => ?_)⟩⟩
  have := RingHom.map_mulVec (incA D) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) x i
  rw [hx, Pi.zero_apply, map_zero] at this
  exact this.symm

theorem ZI_comm (j : Fin r) {z n : GA D V} (hz : z ∈ ZI V fun i => C i j) (hn : n ∈ NI V C) : Commute z n := by
  refine commute_closure ?_ hz hn
  rintro z ⟨a, ha⟩ n ⟨h1, h2, -⟩
  rw [vecMulVec_col, Matrix.map_mul, Matrix.map_mul] at ha
  exact Subtype.ext (Units.ext (mat_comm ha h1 h2))

end Algebra

theorem isCuspFun_of_zCusp : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ →
    ZCusp V φ → IsCuspFun V φ := by
  intro D θ V hθ φ hφ hZ r C hC μ 𝓕 hμ h𝓕 g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  let j : Fin r := ⟨0, hC.1⟩
  have hξ := isoVec_col V hC j
  obtain ⟨⟨ν, 𝓖, hν, h𝓖, -⟩, hm, -⟩ := GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ _ hξ
  obtain ⟨m0, m1⟩ := hm ν 𝓖 hν h𝓖
  have : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  let i : NIQ V C → GQ V := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ V => z.1) h))
  have : Countable (NIQ V C) := hi.countable
  have : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  have : IsFiniteMeasure (ν.restrict 𝓖) := isFiniteMeasure_restrict.2 m1
  refine setIntegral_eq_zero (ν.restrict 𝓖) (fun h => m0 (Measure.restrict_eq_zero.1 h))
    (Subgroup.inclusion (ZI_le V hC j)) (continuous_subtype_val.subtype_mk _)
    (fun z n => Subtype.ext (ZI_comm V j z.2 n.2)) h𝓕 (F := fun n => φ ((n : GA D V) * g))
    (hφ.cont.comp (continuous_subtype_val.mul continuous_const)) (fun γ n => ?_) fun n => ?_
  · rw [Subgroup.coe_mul, mul_assoc]
    exact hφ.left _ γ.2 _
  · simpa only [Subgroup.coe_mul, mul_assoc, Subgroup.coe_inclusion] using hZ _ hξ ν 𝓖 hν h𝓖 ((n : GA D V) * g)

end GlobalTheory.TransvCusp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFunOfTransvectionConstantTermsZeroStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ → ZCusp V φ → IsCuspFun V φ := by
  first | exact @GlobalTheory.TransvCusp.isCuspFun_of_zCusp | exact GlobalTheory.TransvCusp.isCuspFun_of_zCusp | (intros; apply GlobalTheory.TransvCusp.isCuspFun_of_zCusp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDataOfCongruentHeckeSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyEqRankPartMul
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.CharpolyFrobDense

def CoeffCont {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K] (F : Γ → K[X]) : Prop :=
  ∀ k, Continuous fun g => (F g).coeff k

theorem CoeffCont.mul {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {F F' : Γ → K[X]} (h : CoeffCont F) (h' : CoeffCont F') :
    CoeffCont (F * F') := by
  intro k
  simp only [Pi.mul_apply, coeff_mul]
  exact continuous_finsetSum _ fun x _ => (h x.1).mul (h' x.2)

theorem coeffCont_one {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K] :
    CoeffCont (1 : Γ → K[X]) := fun _ => continuous_const

theorem coeffCont_X_sub_C {Γ K : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {a : Γ → K} (ha : Continuous a) :
    CoeffCont fun g => (X - C (a g)) := by
  intro k
  rcases k with _ | _ | k
  · simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
    exact ha.neg
  · simpa using continuous_const
  · simp only [coeff_sub, coeff_X, coeff_C]
    simpa using continuous_const

theorem coeffCont_prod {Γ K ι : Type} [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (s : Finset ι) (F : ι → Γ → K[X]) (h : ∀ c ∈ s, CoeffCont (F c)) :
    CoeffCont fun g => ∏ c ∈ s, F c g := by
  have : (fun g => ∏ c ∈ s, F c g) = ∏ c ∈ s, F c := by
    funext g; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (fun G => CoeffCont G) (fun _ _ ha hb => ha.mul hb) coeffCont_one h

end GlobalTheory.CharpolyFrobDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDataOfCongruentHeckeSystem
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open Polynomial ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CharpolyFrobDense

namespace GlobalTheory.ExpFrame.CongrBlock

theorem norm_le_one_of_compact {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (t : Γ →* Kˣ) (ht : Continuous t) (g : Γ) : ‖((t g : Kˣ) : K)‖ ≤ 1 := by
  have hc : Continuous fun g => ‖((t g : Kˣ) : K)‖ := (Units.continuous_val.comp ht).norm
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  have hpow : ∀ k : ℕ, ‖((t g : Kˣ) : K)‖ ^ k ≤ M := fun k => by
    have := hM ⟨g ^ k, Set.mem_univ _, rfl⟩
    simpa [map_pow, Units.val_pow_eq_pow_val, norm_pow] using this
  by_contra h
  push_neg at h
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop M).exists
  exact absurd (hpow k) (not_le.2 hk)

theorem continuous_character_of_rankOneRep_continuous {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CommRing K] [TopologicalSpace K]
    (χ : Γ →* Kˣ) (h : Continuous (GlobalTheory.TripleGal.rk1 χ)) : Continuous fun g => ((χ g : Kˣ) : K) := by
  have h1 : Continuous fun g => ((GlobalTheory.TripleGal.rk1 χ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0 :=
    (Units.continuous_val.comp h).matrix_elem 0 0
  convert h1 using 1
  funext g
  simp [GlobalTheory.TripleGal.rk1]

theorem coeff_heckePolyOf {L : Type} [Field L] (n q : ℕ) (a : ℕ → L) (j : ℕ) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff j =
      if j ≤ n then (-1) ^ j * (q : L) ^ (j * (j - 1) / 2) * a j else 0 := by
  simp only [Formalism.L2.Col.heckePolyOf, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range, Nat.lt_succ_iff]

theorem coeff_sub_eq_reverse {K : Type} [Field K] {p q : K[X]} {n : ℕ} (hp : p.natDegree = n)
    (hq : q.natDegree = n) (k : ℕ) (hk : k ≤ n) :
    (p - q).coeff k = (p.reverse - q.reverse).coeff (n - k) := by
  simp only [coeff_sub, coeff_reverse, hp, hq, revAt_le (Nat.sub_le n k), Nat.sub_sub_self hk]

theorem norm_sysOf_sub_lt {l : ℕ} [Fact l.Prime] {Pl I : Type} (n : ℕ) (pt : Pl → Fin n → I) {θ θ0 : I → Qbar l}
    (h : ∀ i, ‖θ i - θ0 i‖ < 1) (P : Pl) (k : ℕ) : ‖sysOf n pt θ P k - sysOf n pt θ0 P k‖ < 1 := by
  unfold sysOf
  split_ifs
  · exact h _
  · simp

theorem norm_coeff_hecke_sub_lt {l : ℕ} [Fact l.Prime] (n q : ℕ) (a b : ℕ → Qbar l) (w : Qbar l) (hw : ‖w‖ ≤ 1)
    (hab : ∀ k, ‖a k - b k‖ < 1) (j : ℕ) :
    ‖(Formalism.L2.Col.heckePolyOf n q (fun k => a k * w ^ k) -
      Formalism.L2.Col.heckePolyOf n q (fun k => b k * w ^ k)).coeff j‖ < 1 := by
  rw [coeff_sub, coeff_heckePolyOf, coeff_heckePolyOf]
  split_ifs
  · have e : (-1) ^ j * (q : Qbar l) ^ (j * (j - 1) / 2) * (a j * w ^ j) -
        (-1) ^ j * (q : Qbar l) ^ (j * (j - 1) / 2) * (b j * w ^ j) =
        (-1) ^ j * ((q : Qbar l) ^ (j * (j - 1) / 2) * w ^ j) * (a j - b j) := by ring
    rw [e, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul, norm_pow, norm_pow]
    have h1 : ‖(q : Qbar l)‖ ^ (j * (j - 1) / 2) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
    have h2 : ‖w‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
    calc _ ≤ ‖a j - b j‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ h1 (pow_nonneg (norm_nonneg _) _) h2)
      _ < 1 := hab j
  · simp

theorem blockFor_of_congr : GlobalTheory.Published.ChebotarevDegreeOne → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (F : Frame l ι P.Nr) (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (mu : ι → ℕ → ℕ) (θ θ0 : F.I → PadicAlgCl l), (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → F.IsEig W.lam θ0 → Bk θ0 → (∀ i, ‖θ i - θ0 i‖ < 1) → BlockFor Ω inc P W mu := by
  intro hC E Ω _ _ _ _ _ _ l _ ι _ inc P W F Bk hG mu θ θ0 hmu hθ hθ0 hBk hcl
  obtain ⟨Pl, pt, Fn, ep, hep, h1, h2⟩ := hG
  obtain ⟨r, J, hJ, hr, hrR⟩ := h1 mu θ hmu hθ
  obtain ⟨a, ρ, χ, bot, hat, hρ, hχ, hbot, hρR⟩ := h2 θ0 hθ0 hBk
  refine ⟨ep, J, bot, hep, ⟨r, a, ρ, χ, hat, hr, hρ, hχ, ?_⟩, fun τ => ⟨fun b => hJ τ b, hbot τ⟩⟩

  set p : G E Ω → Polynomial (Qbar l) := fun σ => (r σ).val.charpoly with hp
  set q : G E Ω → Polynomial (Qbar l) := fun σ =>
    (ρ σ).val.charpoly * ∏ s, (X - C ((χ s σ : (Qbar l)ˣ) : Qbar l)) with hq
  have dp : ∀ σ, (p σ).natDegree = P.Nr := fun σ => by
    simp [hp, Matrix.charpoly_natDegree_eq_dim]
  have dq : ∀ σ, (q σ).natDegree = P.Nr := fun σ => by
    simp only [hq]
    rw [(Matrix.charpoly_monic _).natDegree_mul (monic_prod_of_monic _ _ fun s _ => monic_X_sub_C _),
      Matrix.charpoly_natDegree_eq_dim, natDegree_finsetProd_X_sub_C_eq_card, Fintype.card_fin,
      Finset.card_univ, Fintype.card_fin, hat]

  have cp : CoeffCont p := fun k =>
    (GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix P.Nr k).comp (Units.continuous_val.comp hr.1)
  have cq : CoeffCont q := by
    have c1 : CoeffCont fun σ : G E Ω => (ρ σ).val.charpoly := fun k =>
      (GlobalTheory.TypeLeaf.continuous_charpoly_coeff_of_matrix a k).comp (Units.continuous_val.comp hρ)
    have c2 := coeffCont_prod Finset.univ (fun s (σ : G E Ω) => (X - C ((χ s σ : (Qbar l)ˣ) : Qbar l)))
      (fun s _ => coeffCont_X_sub_C (continuous_character_of_rankOneRep_continuous (χ s) (hχ s).1))
    exact c1.mul c2

  set good : G E Ω → Prop := fun σ => ∀ k, ‖(p σ - q σ).coeff k‖ < 1 with hgood
  have hclosed : IsClosed {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} := by
    have : {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} =
        ⋂ k, (fun σ : G E Ω => (p (σ ^ (Fn.sgn : ℤ)) - q (σ ^ (Fn.sgn : ℤ))).coeff k) ⁻¹' Metric.ball 0 1 := by
      ext σ; simp [hgood]
    rw [this]
    refine isClosed_iInter fun k => (IsUltrametricDist.isClosed_ball (0 : Qbar l) 1).preimage ?_
    have hz := continuous_zpow (G := G E Ω) (Fn.sgn : ℤ)
    simp only [coeff_sub]
    exact ((cp k).comp hz).sub ((cq k).comp hz)

  have hS := Fn.cofin
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) hC hS
  have hsub : {σ : G E Ω | ∃ v : HeightOneSpectrum (𝓞 E),
      v ∉ {v : HeightOneSpectrum (𝓞 E) | (Ideal.absNorm v.asIdeal).Prime ∧ v ∉ Set.range Fn.lab} ∧
      v.asIdeal.inertiaDeg ℤ = 1 ∧ ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ IsFrob B (normV v) σ} ⊆
      {σ : G E Ω | good (σ ^ (Fn.sgn : ℤ))} := by
    rintro σ ⟨v, hv, hd, B, hB, hσ⟩
    have hpr : (Ideal.absNorm v.asIdeal).Prime := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    have hv' : v ∈ Set.range Fn.lab := by
      by_contra h; exact hv ⟨hpr, h⟩
    obtain ⟨P0, rfl⟩ := hv'
    have e1 := hrR P0 B σ hB hσ
    have e2 := hρR P0 B σ hB hσ
    have hw := norm_le_one_of_compact Fn.tw Fn.cont (σ ^ (Fn.sgn : ℤ))
    intro k
    by_cases hk : k ≤ P.Nr
    · rw [coeff_sub_eq_reverse (dp _) (dq _) k hk]
      simp only [hp, hq]
      rw [e1, e2]
      exact norm_coeff_hecke_sub_lt _ _ _ _ _ hw (norm_sysOf_sub_lt P.Nr pt hcl P0) _
    · push_neg at hk
      rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (by rw [dp]; exact hk),
        coeff_eq_zero_of_natDegree_lt (by rw [dq]; exact hk)]
      simp
  have hall : ∀ σ : G E Ω, good (σ ^ (Fn.sgn : ℤ)) := fun σ => by
    have h := closure_minimal hsub hclosed
    rw [hD.closure_eq] at h
    exact h (Set.mem_univ σ)
  intro σ k
  have h := hall (σ ^ (Fn.sgn : ℤ)) k
  have e : (σ ^ (Fn.sgn : ℤ)) ^ (Fn.sgn : ℤ) = σ := by
    rw [← zpow_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, zpow_one]
  rw [e] at h
  exact h

end GlobalTheory.ExpFrame.CongrBlock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDataOfCongruentHeckeSystemStatement
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockData_of_congruent_heckeSystem : GlobalTheory.Published.ChebotarevDegreeOne → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (P : Par) (W : Wts ι) (F : Frame l ι P.Nr) (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (mu : ι → ℕ → ℕ) (θ θ0 : F.I → PadicAlgCl l), (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → F.IsEig W.lam θ0 → Bk θ0 → (∀ i, ‖θ i - θ0 i‖ < 1) → BlockFor Ω inc P W mu := by
  first | exact @GlobalTheory.ExpFrame.CongrBlock.blockFor_of_congr | exact GlobalTheory.ExpFrame.CongrBlock.blockFor_of_congr | (intros; apply GlobalTheory.ExpFrame.CongrBlock.blockFor_of_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLogNcardSeminormBallOneGe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallMulLeConvexity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallMulLeConvexity
set_option autoImplicit false

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

set_option autoImplicit false in
open Filter Topology in
private lemma isBallFam_mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {r r' : ℝ} (hrr' : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.2 hrr'))
  simpa using this

set_option autoImplicit false in
open Filter Topology in
private lemma encard_mul_encard_le_isBallFam {G : Type} [AddCommGroup G] {Λ : AddSubgroup G}
    {B : ℝ → Set G} (hB : _root_.GlobalTheory.VolBr.IsBallFam Λ B) {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (hbm : b + b ≤ m) (hfa : (B a).Finite) (hfb : (B b).Finite) (hf1 : (B 1).Finite) :
    (B a).encard * (B b).encard ≤ (B 1).encard * (B (m * a + b)).encard := by
  classical
  set S := hfa.toFinset ×ˢ hfb.toFinset with hS
  let f : G × G → G := fun p ↦ m • p.1 + p.2
  have hmem : ∀ p ∈ S, f p ∈ B (m * a + b) := by
    intro p hp
    rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
    have h1 : m • p.1 ∈ B (m * a) :=
      (hB.nsmul_iff m a p.1 hm (hB.subset a hp.1)).2 hp.1
    have h2 : -p.2 ∈ B (0 + b) := by
      simpa using hB.sub_mem 0 b 0 p.2 (hB.zero_mem 0 le_rfl) hp.2
    have := hB.sub_mem _ _ _ _ h1 h2
    simpa [f, sub_neg_eq_add] using this
  have hcard : S.card ≤ hf1.toFinset.card * (S.image f).card := by
    refine Finset.card_le_mul_card_image S _ fun w hw ↦ ?_
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.1 hw
    refine Finset.card_le_card_of_injOn (fun p ↦ p₀.1 - p.1) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter] at hp
      obtain ⟨hpS, hfp⟩ := hp
      have hp₀' := hp₀
      rw [hS, Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hpS hp₀'
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      have hd : m • (p₀.1 - p.1) = p.2 - p₀.2 := by
        simp only [f] at hfp
        rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← hfp]
        abel
      have hΛ : p₀.1 - p.1 ∈ Λ := Λ.sub_mem (hB.subset a hp₀'.1) (hB.subset a hpS.1)
      have h2 : p.2 - p₀.2 ∈ B ((m : ℝ) * 1) :=
        isBallFam_mono hB (by simpa using hbm) (hB.sub_mem _ _ _ _ hpS.2 hp₀'.2)
      exact (hB.nsmul_iff m 1 _ hm hΛ).1 (hd ▸ h2)
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have h1 : p.1 = q.1 := by simpa using hpq
      have h2 : p.2 = q.2 := by
        have := hp.2.trans hq.2.symm
        simp only [f, h1] at this
        exact add_left_cancel this
      exact Prod.ext h1 h2
  have himg : ((S.image f).card : ℕ∞) ≤ (B (m * a + b)).encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    refine Set.encard_le_encard fun w hw ↦ ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
    exact hmem p hp
  rw [hfa.encard_eq_coe_toFinset_card, hfb.encard_eq_coe_toFinset_card,
    hf1.encard_eq_coe_toFinset_card, ← Nat.cast_mul, ← Finset.card_product]
  calc ((S.card : ℕ) : ℕ∞) ≤ ((hf1.toFinset.card * (S.image f).card : ℕ) : ℕ∞) := by
        exact_mod_cast hcard
    _ ≤ (hf1.toFinset.card : ℕ∞) * (B (m * a + b)).encard := by
        push_cast
        gcongr


set_option autoImplicit false in
open Filter Topology in
theorem _root_.GlobalTheory.VolBr.isBallFam_encard_mul_le : ∀ (G : Type) [AddCommGroup G]
    (Λ : AddSubgroup G) (B : ℝ → Set G), _root_.GlobalTheory.VolBr.IsBallFam Λ B → ∀ n : ℕ, 0 < n →
    (B n).Finite →
    (B n).encard * (B (n / 2)).encard ≤ (B 1).encard * (B (n ^ 2 + n / 2)).encard := by
  intro G _ Λ B hB n hn hfin
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (B 1).Finite := hfin.subset (isBallFam_mono hB hn1)
  have h2 : (B (n / 2)).Finite := hfin.subset (isBallFam_mono hB (by linarith))
  have := encard_mul_encard_le_isBallFam hB (a := n) (b := n / 2) hn (by linarith) hfin h2 h1
  rw [sq]
  exact this

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallMulLeConvexityStatement
open Filter Topology GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_seminormBall_mul_le_convexity : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ n : ℕ, 0 < n → (B n).Finite → (B n).encard * (B (n / 2)).encard ≤ (B 1).encard * (B (n ^ 2 + n / 2)).encard := by
  first | exact @GlobalTheory.VolBr.isBallFam_encard_mul_le | exact GlobalTheory.VolBr.isBallFam_encard_mul_le | (intros; apply GlobalTheory.VolBr.isBallFam_encard_mul_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLogNcardSeminormBallOneGe
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem IsBallFam.subset_of_le_radius {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (h : IsBallFam Λ B) {r r' : ℝ} (hr : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := h.sub_mem r (r' - r) x 0 hx (h.zero_mem _ (by linarith))
  simpa using this

theorem IsBallFam.ncard_sq_le_of_ceil {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (h : IsBallFam Λ B) (hfin : ∀ R, (B R).Finite) {e E : ℝ} (he : 1 ≤ e)
    (hE : (⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2 ≤ E) :
    ((B e).ncard : ℝ) ^ 2 ≤ (B 1).ncard * (B E).ncard := by
  have hn2 : 2 * e ≤ (⌈2 * e⌉₊ : ℝ) := Nat.le_ceil _
  have hnpos : 0 < ⌈2 * e⌉₊ := by
    have : (0:ℝ) < (⌈2 * e⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  have key := GlobalTheory.T.encard_seminormBall_mul_le_convexity G Λ B h _ hnpos (hfin _)
  rw [← (hfin _).cast_ncard_eq, ← (hfin _).cast_ncard_eq, ← (hfin _).cast_ncard_eq,
    ← (hfin _).cast_ncard_eq] at key
  have key' : (B (⌈2 * e⌉₊ : ℝ)).ncard * (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard ≤
      (B 1).ncard * (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard := by
    have := key
    exact_mod_cast this
  have h1 : (B e).ncard ≤ (B (⌈2 * e⌉₊ : ℝ)).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius (by linarith)) (hfin _)
  have h2 : (B e).ncard ≤ (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius (by linarith)) (hfin _)
  have h3 : (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard ≤ (B E).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius hE) (hfin _)
  have : (B e).ncard ^ 2 ≤ (B 1).ncard * (B E).ncard := by
    calc (B e).ncard ^ 2 = (B e).ncard * (B e).ncard := sq _
      _ ≤ (B (⌈2 * e⌉₊ : ℝ)).ncard * (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard := Nat.mul_le_mul h1 h2
      _ ≤ (B 1).ncard * (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard := key'
      _ ≤ _ := Nat.mul_le_mul_left _ h3
  exact_mod_cast this

theorem log_ncard_ball_one_eventually_ge : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G)
    (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) →
    ∀ α β t₀ : ℝ, (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => Real.log ((B m (Real.exp (t * m))).ncard : ℝ) /
      (m : ℝ) ^ d) atTop (𝓝 (α + β * t))) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      (α - ε) * (m : ℝ) ^ d ≤ Real.log ((B m 1).ncard : ℝ) := by
  intro G _ Λ B d _ hB hfin α β t₀ hlim ε hε
  obtain ⟨t, ht0, ht⟩ : ∃ t, t₀ ≤ t ∧ 0 ≤ t := ⟨max t₀ 0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨η, hη, hβη⟩ : ∃ η : ℝ, 0 < η ∧ β * η < ε := by
    refine ⟨ε / (2 * (|β| + 1)), by positivity, ?_⟩
    have hpos : 0 < 2 * (|β| + 1) := by positivity
    have hηe : ε / (2 * (|β| + 1)) * (2 * (|β| + 1)) = ε := div_mul_cancel₀ _ hpos.ne'
    have hη : 0 < ε / (2 * (|β| + 1)) := by positivity
    have hb : β * (ε / (2 * (|β| + 1))) ≤ |β| * (ε / (2 * (|β| + 1))) :=
      mul_le_mul_of_nonneg_right (le_abs_self β) hη.le
    nlinarith [mul_nonneg (abs_nonneg β) hη.le]
  have hw := ((hlim t ht0).const_mul 2).sub (hlim (2 * t + η) (by linarith))
  have hlt : α - ε < 2 * (α + β * t) - (α + β * (2 * t + η)) := by
    have : 2 * (α + β * t) - (α + β * (2 * t + η)) = α - β * η := by ring
    rw [this]; linarith
  have ev1 := hw.eventually (lt_mem_nhds hlt)
  have ev2 : ∀ᶠ m : ℕ in atTop, Real.log 12 ≤ η * m :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hη).eventually_ge_atTop _
  filter_upwards [ev1, ev2, eventually_ge_atTop 1] with m h1 h2 hm
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hmd : (0:ℝ) < (m:ℝ) ^ d := pow_pos hmpos d
  have he : 1 ≤ Real.exp (t * m) := Real.one_le_exp (mul_nonneg ht hmpos.le)
  have h12 : 12 ≤ Real.exp (η * m) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 12)]; exact Real.exp_le_exp.mpr h2
  have hE : (⌈2 * Real.exp (t * m)⌉₊ : ℝ) ^ 2 + (⌈2 * Real.exp (t * m)⌉₊ : ℝ) / 2 ≤
      Real.exp ((2 * t + η) * m) := by
    have hc : (⌈2 * Real.exp (t * m)⌉₊ : ℝ) ≤ 3 * Real.exp (t * m) := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.exp (t * m) by linarith); linarith
    have hc0 : (0:ℝ) ≤ ⌈2 * Real.exp (t * m)⌉₊ := Nat.cast_nonneg _
    rw [show (2 * t + η) * (m:ℝ) = t * m + t * m + η * m by ring, Real.exp_add, Real.exp_add]
    nlinarith [mul_le_mul hc hc hc0 (by linarith), mul_le_mul_of_nonneg_left h12
      (mul_nonneg (by linarith : (0:ℝ) ≤ Real.exp (t * m)) (by linarith : (0:ℝ) ≤ Real.exp (t * m)))]
  have hsq := (hB m).ncard_sq_le_of_ceil (hfin m) he hE
  have hpos : ∀ R, 0 ≤ R → (0:ℝ) < (B m R).ncard := fun R hR => by
    have := (Set.ncard_pos (hfin m R)).mpr ⟨0, (hB m).zero_mem R hR⟩
    exact_mod_cast this
  have hlog := Real.log_le_log (pow_pos (hpos _ (by linarith)) 2) hsq
  rw [Real.log_pow, Real.log_mul (hpos 1 zero_le_one).ne' (hpos _ (Real.exp_pos _).le).ne'] at hlog
  push_cast at hlog
  have hdiv : (2 * Real.log ((B m (Real.exp (t * m))).ncard) - Real.log ((B m (Real.exp ((2 * t + η) * m))).ncard))
      / (m:ℝ) ^ d ≤ Real.log ((B m 1).ncard) / (m:ℝ) ^ d :=
    div_le_div_of_nonneg_right (by linarith) hmd.le
  rw [sub_div, mul_div_assoc] at hdiv
  rw [← le_div_iff₀ hmd]
  linarith

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLogNcardSeminormBallOneGeStatement
open Filter Topology GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_log_ncard_seminormBall_one_ge : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ α β t₀ : ℝ, (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => Real.log ((B m (Real.exp (t * m))).ncard : ℝ) / (m : ℝ) ^ d) atTop (𝓝 (α + β * t))) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α - ε) * (m : ℝ) ^ d ≤ Real.log ((B m 1).ncard : ℝ) := by
  first | exact @GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge | exact GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge | (intros; apply GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfDisjointOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfDisjointOpenCover
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem coh_subsingleton_of_disjoint_cover : ∀ (X : Scheme.{0}) (M : LB X) (κ : Type) (U : κ → X.Opens), M.IsLB → ⨆ c, U c = ⊤ → (Pairwise fun a b => Disjoint (U a) (U b)) → ∀ q : ℕ, (∀ c, Subsingleton (coh (LB.toMod (M.pull (U c).ι)) q)) → Subsingleton (coh (LB.toMod M) q) := by
  intro X M κ U hM hc hd q h
  have hj : ∀ (i : κ) (r : ℤ), (U i).ι.appTop (algebraMap ℤ Γ(X, ⊤) r) =
      algebraMap ℤ Γ((U i).toScheme, ⊤) r := fun i r => by simp
  have hs : ∀ i, Subsingleton (coh ((LB.toMod M).restrict (U i).ι) q) := fun i =>
    (cohOn.mapIso ℤ ⊤ q ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app _ ≪≫
      LB.pullbackIso hM (U i).ι)).toEquiv.subsingleton_congr.2 (h i)
  exact (coh.disjointRestrictEquiv ℤ (fun i => (U i).ι) hj (by simpa using hc)
    (by simpa using hd) (LB.toMod M) q).toEquiv.subsingleton

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfDisjointOpenCoverStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_subsingleton_of_disjoint_open_cover : ∀ (X : Scheme.{0}) (M : LB X) (κ : Type) (U : κ → X.Opens), M.IsLB → ⨆ c, U c = ⊤ → (Pairwise fun a b => Disjoint (U a) (U b)) → ∀ q : ℕ, (∀ c, Subsingleton (coh (LB.toMod (M.pull (U c).ι)) q)) → Subsingleton (coh (LB.toMod M) q) := by
  first | exact @GlobalTheory.coh_subsingleton_of_disjoint_cover | exact GlobalTheory.coh_subsingleton_of_disjoint_cover | (intros; apply GlobalTheory.coh_subsingleton_of_disjoint_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameDivisorTrans
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

private theorem resG_resG_sameDiv {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem SameDiv.trans_of_isLB : ∀ (X : Scheme.{0}) (L M N : LB X) (σ : L.Sec) (τ : M.Sec) (υ : N.Sec),
    M.IsLB → SameDiv σ τ → SameDiv τ υ → SameDiv σ υ := by
  intro X L M N σ τ υ _ h₁ h₂ x
  obtain ⟨U₁, i, j, hi, hj, u₁, hx₁, e₁⟩ := h₁ x
  obtain ⟨U₂, j', k, hj', hk, u₂, hx₂, e₂⟩ := h₂ x
  have hV : U₁ ⊓ U₂ ≤ M.U j ⊓ M.U j' := le_inf (inf_le_left.trans hj) (inf_le_right.trans hj')
  have c := congrArg (resG X hV) (τ.compat j j')
  have e₁' := congrArg (resG X (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) e₁
  have e₂' := congrArg (resG X (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) e₂
  change resG X hV (resG X inf_le_left (τ.f j)) =
    resG X hV ((M.g j j' : Γ(X, M.U j ⊓ M.U j')) * resG X inf_le_right (τ.f j')) at c
  simp only [map_mul, resG_resG_sameDiv] at c e₁' e₂'
  refine ⟨U₁ ⊓ U₂, i, k, inf_le_left.trans hi, inf_le_right.trans hk,
    res inf_le_left u₁ * res hV (M.g j j') * res inf_le_right u₂, ⟨hx₁, hx₂⟩, ?_⟩
  simp only [Units.val_mul, res, Units.coe_map, MonoidHom.coe_coe]
  rw [e₁', c, e₂']
  simp only [resG, mul_assoc]

end GlobalTheory.LogPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsHaveSameZeroSchemeOfLineBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsHaveSameZeroSchemeOfLineBundleIso
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem exists_sameDiv_of_lbIso : ∀ (X : Scheme.{0}) (L M : LB X) (σ : L.Sec), L.IsLB → M.IsLB → LBIso L M →
    ∃ τ : M.Sec, SameDiv σ τ := by
  intro X L M σ hL hM h
  obtain ⟨u, hu⟩ := LBIso.symm h
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (u := u) σ hu hM hL, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
  refine ⟨M.U j ⊓ L.U i, i, j, inf_le_right, inf_le_left,
    ReciprocityTheory.ChartRestriction.G.Semi.res (ReciprocityTheory.ChartRestriction.G.DVR.divLe j i) (u.s (i, j)), ⟨hj, hi⟩, ?_⟩
  have e := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec (u := u) σ hu hM hL j i
  unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand at e
  change _ = _ * (ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_left : M.U j ⊓ L.U i ≤ M.U j)
    ((ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (u := u) σ hu hM hL).f j))
  rw [e, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

end GlobalTheory.LogPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsHaveSameZeroSchemeOfLineBundleIsoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sectionsHaveSameZeroScheme_of_lineBundleIso : ∀ (X : Scheme.{0}) (L M : LB X) (σ : L.Sec), L.IsLB → M.IsLB → LBIso L M → ∃ τ : M.Sec, SameDiv σ τ := by
  first | exact @GlobalTheory.LogPair.exists_sameDiv_of_lbIso | exact GlobalTheory.LogPair.exists_sameDiv_of_lbIso | (intros; apply GlobalTheory.LogPair.exists_sameDiv_of_lbIso <;> assumption)
end
end
