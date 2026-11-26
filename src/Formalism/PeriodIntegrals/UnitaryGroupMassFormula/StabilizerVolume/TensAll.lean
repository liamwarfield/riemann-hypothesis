module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVCos

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
noncomputable section

namespace PI.VolStabS

namespace TensAllW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice Matrix

def LIP (R : Type) [CommRing R] : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (W : Matrix m n R),
    (∀ c, W *ᵥ c = 0 → c = 0) → ∃ P : Matrix n m R, P * W = 1

theorem lip_field (K : Type) [Field K] : LIP K := by
  intro m n _ _ _ _ W hW
  have hk : LinearMap.ker (Matrix.toLin' W) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact hW c (by simpa [Matrix.toLin'_apply] using hc)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' W) hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : Matrix.toLin' (LinearMap.toMatrix' g * W) = LinearMap.id := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg]
  have h2 := congrArg LinearMap.toMatrix' h1
  rwa [LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h2

theorem lip_pi {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type) [∀ i, CommRing (K i)]
    (h : ∀ i, LIP (K i)) : LIP (∀ i, K i) := by
  intro m n _ _ _ _ W hW
  have hv : ∀ v, ∃ P : Matrix n m (K v), P * W.map (fun x => x v) = 1 := by
    intro v
    refine h v m n _ ?_
    intro c hc
    have key : W *ᵥ (fun j => Pi.single v (c j)) = 0 := by
      funext i v'
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply, Pi.zero_apply]
      by_cases hv' : v' = v
      · subst hv'
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using this
      · simp [hv']
    have h0 := hW _ key
    funext j
    have := congrFun (congrFun h0 j) v
    simpa using this
  choose P hP using hv
  let Q : Matrix n m (∀ v, K v) := fun i j v => P v i j
  refine ⟨Q, ?_⟩
  funext i j v
  have := congrFun (congrFun (hP v) i) j
  simp only [Matrix.mul_apply, Matrix.map_apply] at this
  rw [Matrix.mul_apply, Finset.sum_apply]
  show ∑ k, P v i k * W k j v = _
  rw [this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem inj_of_isUnit {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (W : Matrix m n R) (P : Matrix n m R) (hP : IsUnit (P * W).det)
    (c : n → R) (hc : W *ᵥ c = 0) : c = 0 := by
  have h1 : (P * W) *ᵥ c = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hP
  have h2 : ((u⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) *ᵥ ((P * W) *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, ← hu, Units.inv_mul, Matrix.one_mulVec]
  rw [← h2, h1, Matrix.mulVec_zero]

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def wMat (R : Type) [CommRing R] [Algebra F R] {a M : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    Matrix (Fin M × Fin d) (Fin a × Fin d) R :=
  fun p q => crd b R (((1 : R) ⊗ₜ[F] b q.2) * X q.1 p.1) p.2

theorem wMat_mulVec (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) (j : Fin M) (l : Fin d) :
    (wMat b R X *ᵥ c) (j, l) =
      crd b R (∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j) l := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, wMat, crd, Fintype.sum_prod_type, Finset.sum_mul,
    smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem wMat_mulVec_eq_zero (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) :
    wMat b R X *ᵥ c = 0 ↔ ∀ j, ∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j = 0 := by
  constructor
  · intro h j
    apply (Algebra.TensorProduct.basis R b).repr.injective
    ext l
    have := congrFun h (j, l)
    rw [wMat_mulVec] at this
    simpa [crd] using this
  · intro h
    funext p
    rw [wMat_mulVec, h p.1]
    simp [crd]

theorem linIndep_iff (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) X ↔ ∀ c, wMat b R X *ᵥ c = 0 → c = 0 := by
  set B := Algebra.TensorProduct.basis R b with hB
  have hBk : ∀ k, B k = (1 : R) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hX c hc
    rw [wMat_mulVec_eq_zero] at hc
    have h0 := hX (fun i => ∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) (by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hc j)
    funext p
    have h1 := h0 p.1
    have h2 : B.equivFun (∑ k, c (p.1, k) • B k) = fun k => c (p.1, k) := by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [hBk] at h2
    rw [h1, map_zero] at h2
    exact (congrFun h2 p.2).symm
  · intro hW g hg i
    have hc := hW (fun p => B.repr (g p.1) p.2) (by
      rw [wMat_mulVec_eq_zero]
      intro j
      have e : ∀ i, ∑ k, B.repr (g i) k • ((1 : R) ⊗ₜ[F] b k) = g i := by
        intro i
        simp only [← hBk]
        exact B.sum_repr (g i)
      simp only [e]
      have := congrFun hg j
      simpa [Finset.sum_apply, smul_eq_mul] using this)
    rw [← B.sum_repr (g i)]
    simp [fun k => congrFun hc (i, k)]

section Top

variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  [IsTopologicalRing R]

theorem continuous_wMat {a M : ℕ} :
    Continuous (fun X : Fin a → Fin M → R ⊗[F] E => wMat b R X) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  exact (continuous_crd b R p.2).comp
    (continuous_const.mul ((continuous_apply p.1).comp (continuous_apply q.1)))

include b in
theorem isOpen_linIndep (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R) {a M : ℕ} :
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  have e : {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} =
      ⋃ P : Matrix (Fin a × Fin d) (Fin M × Fin d) R,
        (fun X => (P * wMat b R X).det) ⁻¹' {r | IsUnit r} := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    rw [linIndep_iff b]
    constructor
    · intro h
      obtain ⟨P, hP⟩ := hL _ _ _ h
      exact ⟨P, by rw [hP, Matrix.det_one]; exact isUnit_one⟩
    · rintro ⟨P, hP⟩ c hc
      exact inj_of_isUnit _ P hP c hc
  rw [e]
  exact isOpen_iUnion fun P =>
    hU.preimage ((continuous_const.matrix_mul (continuous_wMat b R)).matrix_det)

end Top

end TensAllW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW TensAllW

theorem tensFacts_of {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R) :
    TensFacts F E σ M J a R :=
  ⟨inferInstance, inferInstance, inferInstance, isClosed_HermR R σ a, continuous_gramR R σ J,
    gramR_mem R σ hσ J hJ, isOpen_linIndep (Module.finBasis F E) R hU hL⟩

theorem lip_ainf (F : Type) [Field F] [NumberField F] : LIP (InfiniteAdeleRing F) := by
  classical
  exact lip_pi (fun v : InfinitePlace F => v.Completion) (fun v => lip_field _)

theorem tensAll_holds : TensAll := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  refine ⟨?_, fun v => ?_⟩
  · exact tensFacts_of σ hσ J hJ.1 a (Ainf F) (isOpen_units_Ainf F) (lip_ainf F)
  · have := secondCountable_Fv F v
    have := locallyCompact_Fv F v
    exact tensFacts_of σ hσ J hJ.1 a (Fv F v) (isOpen_units_Fv F v) (lip_field _)

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMeas
noncomputable section

namespace PI.VolStabS.TopoMeas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Filter Topology PI.VolFromSW
open scoped TensorProduct

theorem measurable_finprod {X ι : Type} [MeasurableSpace X] [Countable ι] (f : ι → X → ℂ)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x => ∏ᶠ i, f i x) := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat ι
  have hfin : ∀ n : ℕ, {i | e i < n}.Finite := fun n =>
    (Set.finite_lt_nat n).preimage he.injOn
  let s : ℕ → Finset ι := fun n => (hfin n).toFinset
  let A : ℕ → Set X := fun n => ⋂ i, ⋂ (_ : n ≤ e i), f i ⁻¹' {1}
  let h : ℕ → X → ℂ := fun n x => if x ∈ A n then ∏ i ∈ s n, f i x else 1
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hf i (measurableSet_singleton 1)
  have hh : ∀ n, Measurable (h n) := fun n =>
    Measurable.ite (hA n) (Finset.measurable_prod (s n) fun i _ => hf i) measurable_const
  refine measurable_of_tendsto_metrizable hh (tendsto_pi_nhds.2 fun x => ?_)
  have hev : ∀ᶠ n in atTop, h n x = ∏ᶠ i, f i x := by
    by_cases hs : (Function.mulSupport fun i => f i x).Finite
    · obtain ⟨N, hN⟩ : ∃ N, ∀ i ∈ hs.toFinset, e i < N :=
        ⟨hs.toFinset.sup e + 1, fun i hi => Nat.lt_succ_of_le (Finset.le_sup hi)⟩
      refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have hxA : x ∈ A n := by
        simp only [A, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
        intro i hi
        by_contra hne
        have : i ∈ hs.toFinset := by simpa using hne
        have := hN i this
        omega
      simp only [h, hxA, if_true]
      refine (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
      intro i hi
      have := hN i (by simpa using hi)
      simp only [s, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      omega
    · refine Eventually.of_forall fun n => ?_
      have hxA : x ∉ A n := by
        intro hx
        apply hs
        refine (hfin n).subset fun i hi => ?_
        simp only [A, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hx
        by_contra hlt
        exact hi (hx i (not_lt.1 hlt))
      simp only [h, hxA, if_false]
      exact (finprod_of_infinite_mulSupport hs).symm
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem continuous_projV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    {M a : ℕ} : Continuous (projV (F := F) (E := E) v (M := M) (n := a)) :=
  continuous_pi fun x => continuous_pi fun i =>
    (PI.VolStabS.PositiveNearLattice.continuous_map_tens b (evalV F v)
      (by exact RestrictedProduct.continuous_eval v)).comp
      ((continuous_apply i).comp (continuous_apply x))

theorem measurable_adm {M a : ℕ} (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : IsAdm F E Φ) :
    Measurable Φ := by
  obtain ⟨d, b, Φinf, Φf, Φv, hc, -, ⟨hSB, -, hprod⟩, hIF⟩ := hΦ
  have e1 : Φ = fun X => Φinf (projInf X) * Φf (projFin X) := funext hIF
  have e2 : Φf = fun Y => ∏ᶠ v, Φv v (projV v Y) := funext hprod
  have hf : Measurable Φf := by
    rw [e2]
    exact measurable_finprod _ fun v =>
      ((hSB v).1.continuous.comp (continuous_projV b v)).measurable
  rw [e1]
  exact ((hc.comp (PI.VolStabS.PositiveNearLattice.continuous_projInf b)).measurable).mul
    (hf.comp (PI.VolStabS.PositiveNearLattice.continuous_projFin b).measurable)

end PI.VolStabS.TopoMeas

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField MeasureTheory PI.VolFromSW

theorem measOrb_holds : MeasOrb := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet Φ hΦ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact (TopoMeas.measurable_adm Φ hΦ).comp
    (PositiveNearLattice.continuous_orbit σ J (ratTup (AF F) X0)).measurable

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.AdmCpt
noncomputable section

namespace PI.VolStabS.AdmissibleCompactSupport

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open PI.VolStabS PI.VolStabS.PositiveNearLattice Set Filter
open scoped TensorProduct RestrictedProduct

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_finBox {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hc : ∀ v, IsCompact (D v))
    (hf : ∀ᶠ v in cofinite, D v = (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsCompact {x : Af F | ∀ v, x v ∈ D v} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | D v = (v.adicCompletionIntegers F : Set (Fv F v))}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 hf
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) =>
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let K : Set (Πʳ v, [R v, A v]_[𝓟 S]) := {x | ∀ v, x v ∈ D v}
  have hK : IsCompact K := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have e : ((↑) : Πʳ v, [R v, A v]_[𝓟 S] → ∀ v, R v) '' K = Set.pi univ D := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩ v _
        exact hx v
      · intro hg
        refine ⟨⟨g, ?_⟩, fun v => hg v (mem_univ v), rfl⟩
        rw [eventually_principal]
        intro v hv
        have h := hg v (mem_univ v)
        rwa [show D v = _ from hv] at h
    rw [e]
    exact isCompact_univ_pi hc
  have e : {x : Af F | ∀ v, x v ∈ D v} = RestrictedProduct.inclusion R A hS '' K := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      rw [eventually_principal]
      intro v hv
      have h := hx v
      rwa [show D v = _ from hv] at h
    · rintro ⟨y, hy, rfl⟩ v
      exact hy v
  rw [e]
  exact hK.image (RestrictedProduct.continuous_inclusion hS)

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem crd_projV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F))
    (i : Fin a) (j : Fin M) (k : Fin d) :
    crd b (Fv F v) (projV v Y i j) k = (crd b (Af F) (Y i j) k) v := by
  simp only [projV]
  rw [crd_map]
  rfl

theorem eventually_mem_latV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) :
    ∀ᶠ v in cofinite, projV v Y ∈ latV b v := by
  have h : ∀ (i : Fin a) (j : Fin M) (k : Fin d), ∀ᶠ v in cofinite,
      (crd b (Af F) (Y i j) k) v ∈ v.adicCompletionIntegers F :=
    fun i j k => (crd b (Af F) (Y i j) k).2
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
    h i j k] with v hv
  intro i j k
  have := crd_projV b Y v i j k
  simp only [crd] at this
  rw [this]
  exact hv i j k

variable {a M : ℕ} (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ)

theorem mulSupport_finite
    (hae : ∀ᶠ v in cofinite, Φv v = (latV b v).indicator 1) (Y : Fin a → Fin M → Af F ⊗[F] E) :
    (Function.mulSupport fun v => Φv v (projV v Y)).Finite := by
  refine (Filter.eventually_cofinite.1 (hae.and (eventually_mem_latV b Y))).subset ?_
  intro v hv h
  apply hv
  simp only
  rw [h.1, Set.indicator_of_mem h.2]
  rfl

theorem factor_ne_zero (hae : ∀ᶠ v in cofinite, Φv v = (latV b v).indicator 1)
    (Y : Fin a → Fin M → Af F ⊗[F] E) (h : ∏ᶠ v, Φv v (projV v Y) ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) : Φv v (projV v Y) ≠ 0 := by
  have hfin := mulSupport_finite b Φv hae Y
  rw [finprod_eq_prod _ hfin] at h
  by_cases hv : v ∈ hfin.toFinset
  · exact Finset.prod_ne_zero_iff.1 h v hv
  · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not] at hv
    rw [hv]
    exact one_ne_zero

end PI.VolStabS.AdmissibleCompactSupport

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.VolStabS.AdmissibleCompactSupport

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVNA
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSt
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct

def TensNA : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ v : HeightOneSpectrum (𝓞 F), HasCOSub (Fin a → Fin M → Fv F v ⊗[F] E)

def DensVLC : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      DensOn (IsLCcOn {X | LinearIndependent (Fv F v ⊗[F] E) X}) μv (gramR (Fv F v) σ J)
        Subtype.val νv

theorem densV_of (hT : TensAll) (hNA : TensNA) (hLC : DensVLC) : DensV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨t1, t2, t3, t4, _t5, _t6, t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  exact (densAll_iff _ _ _ _ _).2 (densApprox_lc μv _ _ νv _ t7
    (hNA F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet v)
    (hLC F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν))

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct

theorem hasCOSub_of_lat {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : HasCOSub V := by
  intro N hN
  have hev : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ (L : Set V), c • y ∈ N := by
    apply hLc.eventually_forall_of_forall_eventually
    intro y _
    have hc : Tendsto (fun p : 𝕜 × V => p.1 • p.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y)) :=
      continuous_smul.tendsto _
    rw [zero_smul] at hc
    exact hc hN
  obtain ⟨k, hk⟩ := (hπ.eventually hev).exists
  have hpk : π ^ k ≠ 0 := pow_ne_zero k h0
  have he : ((L.map (DistribSMul.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := AddSubgroup.coe_map _ _
  refine ⟨L.map (DistribSMul.toAddMonoidHom V (π ^ k)), ?_, ?_, ?_⟩
  · rw [he]
    exact (Homeomorph.smulOfNeZero (π ^ k) hpk).isOpenMap _ hLo
  · rw [he]
    exact hLc.image (continuous_const_smul _)
  · rw [he]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy

theorem exists_pow_tendsto_zero_Fv {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  refine ⟨π, fun h => ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
      rw [hv]
      decide
    have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt

def latSub {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E) where
  carrier := latV (M := M) (n := a) b v
  add_mem' := by
    intro x y hx hy
    simp only [latV, Set.mem_setOf_eq] at hx hy ⊢
    intro i j k
    simp only [Pi.add_apply, map_add (f := _), Finsupp.add_apply]
    exact add_mem (hx i j k) (hy i j k)
  zero_mem' := by
    simp only [latV, Set.mem_setOf_eq]
    intro i j k
    simp only [Pi.zero_apply, map_zero, Finsupp.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro x hx
    simp only [latV, Set.mem_setOf_eq] at hx ⊢
    intro i j k
    simp only [Pi.neg_apply, map_neg, Finsupp.neg_apply]
    exact neg_mem (hx i j k)

theorem tensNA_holds : TensNA := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
  exact hasCOSub_of_lat (latSub (Module.finBasis F E) v a M)
    (PositiveNearLattice.isClopen_latV (Module.finBasis F E) v a M).isOpen
    (PositiveNearLattice.isCompact_latV (Module.finBasis F E) v a M) π h0 hπ

def scaledB (𝕜 : Type) {V : Type} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] (L : AddSubgroup V)
    (Λ : AddSubgroup V) : Prop :=
  ∃ c : 𝕜, c ≠ 0 ∧ Λ = L.map (DistribSMul.toAddMonoidHom V c)

theorem isCOBasis_scaled {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : IsCOBasis (scaledB 𝕜 L) := by
  intro N hN
  have hev : ∀ᶠ c in 𝓝 (0 : 𝕜), ∀ y ∈ (L : Set V), c • y ∈ N := by
    apply hLc.eventually_forall_of_forall_eventually
    intro y _
    have hc : Tendsto (fun p : 𝕜 × V => p.1 • p.2) (𝓝 ((0 : 𝕜), y)) (𝓝 ((0 : 𝕜) • y)) :=
      continuous_smul.tendsto _
    rw [zero_smul] at hc
    exact hc hN
  obtain ⟨k, hk⟩ := (hπ.eventually hev).exists
  have hpk : π ^ k ≠ 0 := pow_ne_zero k h0
  have he : ((L.map (DistribSMul.toAddMonoidHom V (π ^ k)) : AddSubgroup V) : Set V) =
      (fun x => π ^ k • x) '' (L : Set V) := AddSubgroup.coe_map _ _
  refine ⟨L.map (DistribSMul.toAddMonoidHom V (π ^ k)), ⟨π ^ k, hpk, rfl⟩, ?_, ?_, ?_⟩
  · rw [he]
    exact (Homeomorph.smulOfNeZero (π ^ k) hpk).isOpenMap _ hLo
  · rw [he]
    exact hLc.image (continuous_const_smul _)
  · rw [he]
    rintro _ ⟨y, hy, rfl⟩
    exact hk y hy

theorem isCOBasis_latSub {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (a M : ℕ) :
    IsCOBasis (scaledB (Fv F v) (latSub b v a M)) := by
  obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
  exact isCOBasis_scaled (latSub b v a M) (PositiveNearLattice.isClopen_latV b v a M).isOpen
    (PositiveNearLattice.isCompact_latV b v a M) π h0 hπ

def DensVLat : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
      DensCosB (scaledB (Fv F v) (latSub b v a M)) μv (gramR (Fv F v) σ J) Subtype.val νv
        {X | LinearIndependent (Fv F v ⊗[F] E) X}

theorem densVLC_of_lat (hT : TensAll) (hC : DensVLat) : DensVLC := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨_t1, t2, _t3, _t4, _t5, _t6, _t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  exact densLC_of_cosB _ _ (isCOBasis_latSub (Module.finBasis F E) v a M)
    (hC F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν _ (Module.finBasis F E))

theorem densV_of_lat (hT : TensAll) (hC : DensVLat) : DensV :=
  densV_of hT tensNA_holds (densVLC_of_lat hT hC)

end PI.VolStabS
end
end
