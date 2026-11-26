module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStar

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.LemForm
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.LemLz
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.LemBound
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.Lemmas
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.HkIterContOn
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.NormSqLeSum
noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.JoinReconstruction

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def sx (q : ℕ) : Set (Fin q → ℝ) := {t | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1}

def pt {q : ℕ} (y : Fin (q + 1) → V) (t : Fin q → ℝ) : V := y 0 + ∑ j, t j • (y j.succ - y 0)

theorem recon [FiniteDimensional ℝ V] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (b : Module.Basis κ ℝ V) :
    ∃ Ψ : ((ι → κ) → ℝ) →L[ℝ] (V [⋀^ι]→L[ℝ] ℝ), ∀ A : V [⋀^ι]→L[ℝ] ℝ, Ψ (fun v => A fun i => b (v i)) = A := by
  let L : (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] ((ι → κ) → ℝ) :=
    { toFun := fun A v => A fun i => b (v i)
      map_add' := fun A B => by
        ext v
        simp
      map_smul' := fun c A => by
        ext v
        simp }
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    have hm : A.toMultilinearMap = (0 : V [⋀^ι]→L[ℝ] ℝ).toMultilinearMap := by
      refine Module.Basis.ext_multilinear (fun _ => b) fun v => ?_
      have := congrFun hA v
      simpa [L] using this
    ext x
    simpa using congrFun (congrArg DFunLike.coe hm) x
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective L hL
  refine ⟨LinearMap.toContinuousLinearMap g, fun A => ?_⟩
  have := congrArg (fun f => f A) hg
  simpa [L] using this

theorem norm_sq_le_sum {κ : Type} [Fintype κ] (u : κ → ℝ) : ‖u‖ ^ 2 ≤ ∑ v, u v ^ 2 := by
  have hs : 0 ≤ ∑ v, u v ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  have h : ‖u‖ ≤ Real.sqrt (∑ v, u v ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun w => u w ^ 2) (fun w _ => sq_nonneg (u w)) (Finset.mem_univ v))
  calc ‖u‖ ^ 2 ≤ Real.sqrt (∑ v, u v ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ v, u v ^ 2 := Real.sq_sqrt hs

end PositivityTheory.KB.JoinReconstruction

end
end

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

section Mean

variable {G : Type} [Group G]

def mn (S : Subgroup G) {E : Type} [AddCommGroup E] [Module ℝ E]
    (e : Quotient (QuotientGroup.rightRel S) → E) : E :=
  ((S.index : ℝ))⁻¹ • ∑ᶠ c, e c

theorem fin_of_ne {S : Subgroup G} (h : S.index ≠ 0) : Finite (Quotient (QuotientGroup.rightRel S)) := by
  haveI : Finite (G ⧸ S) := Subgroup.index_ne_zero_iff_finite.mp h
  exact Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm

theorem mn_zero {S : Subgroup G} (h : S.index = 0) {E : Type} [AddCommGroup E] [Module ℝ E]
    (e : Quotient (QuotientGroup.rightRel S) → E) : mn S e = 0 := by
  simp [mn, h]

theorem mn_fin {S : Subgroup G} [Fintype (Quotient (QuotientGroup.rightRel S))] {E : Type} [AddCommGroup E]
    [Module ℝ E] (e : Quotient (QuotientGroup.rightRel S) → E) : mn S e = ((S.index : ℝ))⁻¹ • ∑ c, e c := by
  rw [mn, finsum_eq_sum_of_fintype]

theorem mn_map (S : Subgroup G) {E E' : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {F : Type} [FunLike F E E'] [LinearMapClass F ℝ E E'] (ℓ : F)
    (e : Quotient (QuotientGroup.rightRel S) → E) : ℓ (mn S e) = mn S fun c => ℓ (e c) := by
  by_cases h : S.index = 0
  · rw [mn_zero h, mn_zero h, map_zero]
  · haveI := fin_of_ne h
    letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mn_fin, mn_fin, map_smul, map_sum]

theorem mn_integral (S : Subgroup G) {X E : Type} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : Quotient (QuotientGroup.rightRel S) → X → E) (he : ∀ c, Integrable (e c) μ) :
    ∫ x, mn S (fun c => e c x) ∂μ = mn S fun c => ∫ x, e c x ∂μ := by
  by_cases h : S.index = 0
  · simp only [mn_zero h, integral_zero]
  · haveI := fin_of_ne h
    letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))
    simp only [mn_fin]
    rw [integral_smul, integral_finsetSum _ fun c _ => he c]

theorem mn_contOn (S : Subgroup G) {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Quotient (QuotientGroup.rightRel S) → X → E) {s : Set X} (he : ∀ c, ContinuousOn (e c) s) :
    ContinuousOn (fun x => mn S fun c => e c x) s := by
  by_cases h : S.index = 0
  · simp only [mn_zero h]
    exact continuousOn_const
  · haveI := fin_of_ne h
    letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))
    simp only [mn_fin]
    exact (continuousOn_finsetSum _ fun c _ => he c).const_smul _

theorem dC_mn (S : Subgroup G) {Y : Type} {m : ℕ} (F : Quotient (QuotientGroup.rightRel S) → (Fin (m + 1) → Y) → ℝ) :
    dC (fun y => mn S fun c => F c y) = fun y => mn S fun c => dC (F c) y := by
  funext y
  by_cases h : S.index = 0
  · simp [dC, mn_zero h]
  · haveI := fin_of_ne h
    letI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))
    simp only [dC, mn_fin, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
    ring

end Mean

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

open ComplexOrder in
theorem pos_convex : Convex ℝ (Pos L N) := by
  unfold Pos
  refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb _ w => ?_
  have e : mat (a • x + b • y) w = a • mat x w + b • mat y w := by
    ext i j
    rfl
  rw [e]
  exact ((hx w).smul ha).add ((hy w).smul hb)

def pb {q : ℕ} (g : Gp L N) (ω : Form (HS L N) q) : Form (HS L N) q :=
  fun h => (ω (actL g h)).compContinuousLinearMap (actL g)

private theorem pb_pb_apply_eq_pb_mul (k g : Gp L N) (h : HS L N) : actL (k * g) h = actL k (actL g h) := by
  apply Subtype.ext
  funext w i j
  show (Matrix.conjTranspose (((k * g) w)⁻¹).val * mat h w * (((k * g) w)⁻¹).val) i j =
    (Matrix.conjTranspose ((k w)⁻¹).val * (Matrix.conjTranspose ((g w)⁻¹).val * mat h w * ((g w)⁻¹).val) *
      ((k w)⁻¹).val) i j
  simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem fr_pb {q : ℕ} (g x : Gp L N) (ω : Form (HS L N) q) : fr (pb g ω) x = fr ω (g * x) := by
  ext v
  simp only [fr, pb, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, pb_pb_apply_eq_pb_mul]

theorem pb_contOn {q : ℕ} (g : Gp L N) {ω : Form (HS L N) q} (hω : ContinuousOn ω (Pos L N)) :
    ContinuousOn (pb g ω) (Pos L N) := by
  have hmaps : Set.MapsTo (actL g) (Pos L N) (Pos L N) := fun h hh => (g • (⟨h, hh⟩ : Pos L N)).2
  exact ((ContinuousAlternatingMap.compContinuousLinearMapCLM (actL g)).continuous.comp_continuousOn
    (hω.comp (actL g).continuous.continuousOn hmaps)).congr fun _ _ => rfl

theorem intS_eq {q : ℕ} (ω : Form (HS L N) q) (y : Fin (q + 1) → HS L N) :
    intS ω y = ∫ t in sx q, ω (pt y t) fun j => y j.succ - y 0 := rfl

theorem intS_pb {q : ℕ} (g : Gp L N) (ω : Form (HS L N) q) (y : Fin (q + 1) → HS L N) :
    intS (pb g ω) y = intS ω fun j => actL g (y j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [intS, pb, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, map_add (f := _), map_sum,
    map_smul, map_sub]

theorem intP_pb {q : ℕ} (g : Gp L N) (ω : Form (HS L N) q) (y : Fin (q + 1) → Pos L N) :
    intP (pb g ω) y = intP ω fun j => g • y j :=
  intS_pb g ω _

private theorem isClosed_sx (q : ℕ) : IsClosed (sx q) := by
  show IsClosed ({t : Fin q → ℝ | ∀ j, 0 ≤ t j} ∩ {t | ∑ j, t j ≤ 1})
  refine IsClosed.inter ?_ ?_
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const

private theorem isCompact_sx (q : ℕ) : IsCompact (sx q) := by
  refine (isCompact_Icc (a := (0 : Fin q → ℝ)) (b := 1)).of_isClosed_subset (isClosed_sx q) ?_
  intro t ht
  have ht' : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1 := ht
  exact ⟨fun j => ht'.1 j, fun j => (Finset.single_le_sum (fun i _ => ht'.1 i) (Finset.mem_univ j)).trans ht'.2⟩

private theorem pt_mem_Pos_of_mem_sx {q : ℕ} (y : Fin (q + 1) → Pos L N) {t : Fin q → ℝ} (ht : t ∈ sx q) :
    pt (fun j => (y j).1) t ∈ Pos L N := by
  have ht' : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1 := ht
  have hw : ∀ i ∈ Finset.univ, 0 ≤ (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i := by
    intro i _
    induction i using Fin.cases with
    | zero => simpa using ht'.2
    | succ j => simpa using ht'.1 j
  have h1 : ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i = 1 := by
    simp [Fin.sum_univ_succ]
  have hmem := pos_convex.sum_mem hw h1 (fun i _ => (y i).2)
  convert hmem using 1
  simp only [pt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, sub_smul, one_smul]
  abel

set_option maxHeartbeats 1000000 in
theorem intP_integ {q : ℕ} {ω : Form (HS L N) q} (hω : ContinuousOn ω (Pos L N)) (y : Fin (q + 1) → Pos L N) :
    IntegrableOn (fun t => ω (pt (fun j => (y j).1) t) fun j => (y j.succ).1 - (y 0).1) (sx q) := by
  refine ContinuousOn.integrableOn_compact (isCompact_sx q) ?_
  have hpt : Continuous fun t : Fin q → ℝ => pt (fun j => (y j).1) t := by
    show Continuous fun t : Fin q → ℝ => (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1)
    fun_prop
  have hev : Continuous fun f : HS L N [⋀^Fin q]→L[ℝ] ℝ => f fun j => (y j.succ).1 - (y 0).1 := by
    fun_prop
  exact hev.comp_continuousOn (hω.comp hpt.continuousOn fun t ht => pt_mem_Pos_of_mem_sx y ht)

theorem intP_sub {q : ℕ} {ω ω' : Form (HS L N) q} (hω : ContinuousOn ω (Pos L N))
    (hω' : ContinuousOn ω' (Pos L N)) (y : Fin (q + 1) → Pos L N) :
    intP (ω - ω') y = intP ω y - intP ω' y := by
  simp only [intP, intS_eq, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
  exact integral_sub (intP_integ hω y) (intP_integ hω' y)

set_option maxHeartbeats 1000000 in
theorem intP_inv {q : ℕ} {ω : Form (HS L N) q} {g : Gp L N} (hω : FInv ω g) (y : Fin (q + 1) → Pos L N) :
    intP ω (fun j => g • y j) = intP ω y := by
  rw [← intP_pb]
  simp only [intP, intS_eq]
  refine setIntegral_congr_fun (isClosed_sx q).measurableSet fun t ht => ?_
  exact DFunLike.congr_fun (hω _ (pt_mem_Pos_of_mem_sx y ht)) _

abbrev Sg (q : GK L N) : Subgroup (Gm L N) :=
  ((toK L N).range.map (MulAut.conj q⁻¹).toMonoidHom).comap (toK L N)

theorem hecke_eq {Y H E : Type} [Group H] [MulAction H Y] [AddCommGroup E] [Module ℝ E] (τ : GK L N →* H)
    (q : GK L N) (f : Y → E) (y : Y) :
    hecke (toK L N) τ q f y = mn (Sg q) fun c => f (τ (q * toK L N (Quotient.out c)) • y) := rfl

def Hk {k : ℕ} (q : GK L N) (ω : Form (HS L N) k) : Form (HS L N) k :=
  fun h => mn (Sg q) fun c => pb (toP L N (q * toK L N (Quotient.out c))) ω h

theorem fr_Hk {k : ℕ} (q : GK L N) (ω : Form (HS L N) k) (x : Gp L N) :
    fr (Hk q ω) x = hecke (toK L N) (toP L N) q (fr ω) x := by
  rw [hecke_eq]
  simp only [smul_eq_mul, ← fr_pb]
  exact mn_map (Sg q)
    ({ toFun := fun a : HS L N [⋀^Fin k]→L[ℝ] ℝ => a.compContinuousLinearMap (actL x)
       map_add' := fun a b => by ext; simp
       map_smul' := fun c a => by ext; simp } : (HS L N [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] (HS L N [⋀^Fin k]→L[ℝ] ℝ))
    (fun c => pb (toP L N (q * toK L N (Quotient.out c))) ω (actL x (one L N)))

theorem comp_Hk {k : ℕ} (q : GK L N) (ω : Form (HS L N) k) (u : Fin k → HS L N) :
    (fun x => fr (Hk q ω) x u) = hecke (toK L N) (toP L N) q fun x => fr ω x u := by
  funext x
  rw [fr_Hk, hecke_eq, hecke_eq]
  exact mn_map (Sg q)
    ({ toFun := fun f : HS L N [⋀^Fin k]→L[ℝ] ℝ => f u
       map_add' := fun _ _ => by simp
       map_smul' := fun _ _ => by simp } : (HS L N [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ) _

theorem comp_Hk_iter {k : ℕ} (q : GK L N) (ω : Form (HS L N) k) (u : Fin k → HS L N) (r : ℕ) :
    (fun x => fr ((Hk q)^[r] ω) x u) = (hecke (toK L N) (toP L N) q)^[r] fun x => fr ω x u := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', comp_Hk, ih]

theorem Hk_contOn {k : ℕ} (q : GK L N) {ω : Form (HS L N) k} (hω : ContinuousOn ω (Pos L N)) :
    ContinuousOn (Hk q ω) (Pos L N) :=
  mn_contOn (Sg q) _ fun c => pb_contOn _ hω

set_option maxHeartbeats 1000000 in
theorem intP_Hk {k : ℕ} (q : GK L N) {ω : Form (HS L N) k} (hω : ContinuousOn ω (Pos L N))
    (y : Fin (k + 1) → Pos L N) :
    intP (Hk q ω) y = mn (Sg q) fun c => intP (pb (toP L N (q * toK L N (Quotient.out c))) ω) y := by
  have key : ∀ (h : HS L N) (v : Fin k → HS L N),
      Hk q ω h v = mn (Sg q) fun c => pb (toP L N (q * toK L N (Quotient.out c))) ω h v := fun h v =>
    mn_map (Sg q)
      ({ toFun := fun f : HS L N [⋀^Fin k]→L[ℝ] ℝ => f v
         map_add' := fun _ _ => by simp
         map_smul' := fun _ _ => by simp } : (HS L N [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ) _
  simp only [intP, intS_eq, key]
  exact mn_integral (Sg q) _ fun c => intP_integ (pb_contOn _ hω) y

set_option maxHeartbeats 1000000 in
theorem Hk_good {k : ℕ} (q : GK L N) {ω : Form (HS L N) (k + 1)} (hω : Good ω) : Good (Hk q ω) := by
  refine ⟨Hk_contOn q hω.1, ?_⟩
  have h1 : intP (Hk q ω) = fun y => mn (Sg q) fun c => intP (pb (toP L N (q * toK L N (Quotient.out c))) ω) y :=
    funext fun y => intP_Hk q hω.1 y
  rw [h1, dC_mn]
  funext y
  have h0 : ∀ c : Quotient (QuotientGroup.rightRel (Sg q)),
      dC (intP (pb (toP L N (q * toK L N (Quotient.out c))) ω)) y = 0 := fun c => by
    have e2 : intP (pb (toP L N (q * toK L N (Quotient.out c))) ω) =
        fun z => intP ω fun j => toP L N (q * toK L N (Quotient.out c)) • z j :=
      funext fun z => intP_pb _ ω z
    rw [e2]
    exact congrFun hω.2 (fun j => toP L N (q * toK L N (Quotient.out c)) • y j)
  simp only [h0]
  simp [mn]

end PositivityTheory.KB.JoinReconstruction

end
end

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

section Lemmas

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem actL_cont (h : HS L N) : Continuous fun x : Gp L N => actL x h := by
  unfold actL actM
  refine continuous_induced_rng.2 ?_
  have hi : Continuous fun x : Gp L N => fun w => (((x w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) :=
    continuous_pi fun w => Units.continuous_coe_inv.comp (continuous_apply w)
  refine continuous_pi fun w => ?_
  have hw := (continuous_apply w).comp hi
  exact ((hw.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul hw

theorem ofS_cont : Continuous (ofS L N) := by
  unfold ofS
  refine continuous_pi fun w => ?_
  simp only [MonoidHom.coe_comp, Function.comp_def, MonoidHom.pi_apply, Pi.evalMonoidHom_apply]
  rw [Units.continuous_iff]
  have hv : Continuous fun a : Sp L N => ((a w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) :=
    continuous_subtype_val.comp (continuous_apply w)
  refine ⟨hv, ?_⟩
  have hi : ∀ A : Matrix.SpecialLinearGroup (Fin N) ℂ,
      ((SpecialLinearGroup.toGL A)⁻¹ : GL (Fin N) ℂ).val = Matrix.adjugate (A : Matrix (Fin N) (Fin N) ℂ) := by
    intro A
    rw [← map_inv]
    exact Matrix.SpecialLinearGroup.coe_inv A
  simp only [hi]
  exact hv.matrix_adjugate

theorem fr_comp_cont {q : ℕ} {ω : Form (HS L N) q} (hω : ContinuousOn ω (Pos L N)) (u : Fin q → HS L N) :
    Continuous fun x => fr ω x u := by
  unfold fr
  have hp : Continuous fun x : Gp L N => actL x ↑(one L N) := actL_cont _
  have hw : Continuous fun x : Gp L N => ω (actL x ↑(one L N)) :=
    hω.comp_continuous hp fun x => (x • one L N).2
  have hu : Continuous fun x : Gp L N => fun i => actL x (u i) :=
    continuous_pi fun i => actL_cont (u i)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  exact hw.eval hu

theorem fr_inv {q : ℕ} {ω : Form (HS L N) q} {g : Gp L N} (hω : FInv ω g) (x : Gp L N) :
    fr ω (g * x) = fr ω x := by
  unfold fr
  have hm : actL x ↑(one L N) ∈ Pos L N := (x • one L N).2
  have h1 := hω _ hm
  have hc : actL (g * x) = (actL g).comp (actL x) :=
    ContinuousLinearMap.ext fun h => actL_mul g x h
  rw [hc, ← h1]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.comp_apply,
    Function.comp_def]

theorem fr_sub {q : ℕ} (ω ω' : Form (HS L N) q) (x : Gp L N) : fr (ω - ω') x = fr ω x - fr ω' x := by
  ext v; simp [fr]

theorem finv_sub {q : ℕ} {ω ω' : Form (HS L N) q} {g : Gp L N} (hω : FInv ω g) (hω' : FInv ω' g) :
    FInv (ω - ω') g := by
  unfold FInv at hω hω' ⊢
  intro h hh
  ext v
  have a := congrArg (fun f => f v) (hω h hh)
  have b := congrArg (fun f => f v) (hω' h hh)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at a b
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Pi.sub_apply,
    ContinuousAlternatingMap.sub_apply, a, b]

theorem dC_sub {Y : Type} {m : ℕ} (F G : (Fin (m + 1) → Y) → ℝ) :
    dC (fun y => F y - G y) = fun y => dC F y - dC G y := by
  unfold dC
  funext y
  rw [← Finset.sum_sub_distrib]
  simp only [mul_sub]

theorem ev_sub {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (F F' : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ (fun y => F y - F' y) y z = ev ρ F y z - ev ρ F' y z := by
  unfold ev
  simp only [mul_sub, Finsupp.sum_sub]

theorem ev_toK {m : ℕ} (G : (Fin (m + 1) → GK L N) → ℝ) (Φ : (Fin (m + 1) → Pos L N) → ℝ)
    (hG : ∀ y, G y = Φ fun j => toP L N (y j) • one L N) (z : Chn (Gm L N) m) :
    ev (toK L N) G 1 z = ev (emb L N) Φ (one L N) z := by
  unfold ev
  refine Finsupp.sum_congr fun g _ => ?_
  rw [hG]
  congr 2
  funext j
  rw [smul_eq_mul, mul_one]
  rfl

private theorem pb_actL_compContinuousLinearMap_eq_pb_mul {k : ℕ} (ω : Form (HS L N) k) (g e : Gp L N) (h : HS L N) :
    (pb g ω (actL e h)).compContinuousLinearMap (actL e) = pb (g * e) ω h := by
  unfold pb
  have hc : actL (g * e) = (actL g).comp (actL e) :=
    ContinuousLinearMap.ext fun x => actL_mul g e x
  rw [hc]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.comp_apply,
    Function.comp_def]

private theorem pb_mul_eq_pb_of_fInv_of_mem_Pos {k : ℕ} {ω : Form (HS L N) k} {a : Gp L N} (ha : FInv ω a) (g : Gp L N)
    {h : HS L N} (hh : h ∈ Pos L N) : pb (a * g) ω h = pb g ω h := by
  have hm : actL g h ∈ Pos L N := (g • (⟨h, hh⟩ : Pos L N)).2
  have h1 : pb a ω (actL g h) = ω (actL g h) := by
    unfold pb
    exact ha _ hm
  rw [← pb_actL_compContinuousLinearMap_eq_pb_mul, h1]
  unfold pb
  rfl

private theorem mn_compContinuousLinearMap_actL {k : ℕ} (S : Subgroup (Gm L N))
    (F : Quotient (QuotientGroup.rightRel S) → (HS L N [⋀^Fin k]→L[ℝ] ℝ)) (e : Gp L N) :
    (mn S F).compContinuousLinearMap (actL e) = mn S fun c => (F c).compContinuousLinearMap (actL e) := by
  unfold mn
  by_cases hfin : Finite (Quotient (QuotientGroup.rightRel S))
  · haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel S))
    simp only [finsum_eq_sum_of_fintype]
    ext v
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  · have hinf : Infinite (Gm L N ⧸ S) := by
      rw [← not_finite_iff_infinite]
      intro hf
      exact hfin (Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm)
    have h0 : S.index = 0 := Subgroup.index_eq_zero_iff_infinite.2 hinf
    simp only [h0, Nat.cast_zero, _root_.inv_zero, zero_smul]
    ext v
    simp

theorem Hk_finv_emb {k : ℕ} (q : GK L N) {ω : Form (HS L N) k} (hω : ∀ γ, FInv ω (emb L N γ)) (γ : Gm L N) :
    FInv (Hk q ω) (emb L N γ) := by
  unfold FInv Hk
  intro h hh
  rw [mn_compContinuousLinearMap_actL]
  simp only [pb_actL_compContinuousLinearMap_eq_pb_mul]
  let σ : Quotient (QuotientGroup.rightRel (Sg q)) ≃ Quotient (QuotientGroup.rightRel (Sg q)) :=
    { toFun := Quotient.map' (fun x => x * γ) (fun a b hab => by
        rw [QuotientGroup.rightRel_apply] at hab ⊢
        simpa [_root_.mul_inv_rev, mul_assoc] using hab)
      invFun := Quotient.map' (fun x => x * γ⁻¹) (fun a b hab => by
        rw [QuotientGroup.rightRel_apply] at hab ⊢
        simpa [_root_.mul_inv_rev, mul_assoc] using hab)
      left_inv := by
        intro c
        induction c using Quotient.inductionOn' with
        | h a => simp only [Quotient.map'_mk'', mul_inv_cancel_right]
      right_inv := by
        intro c
        induction c using Quotient.inductionOn' with
        | h a => simp only [Quotient.map'_mk'', inv_mul_cancel_right] }
  have key : ∀ c, pb (toP L N (q * toK L N (σ c).out)) ω h =
      pb (toP L N (q * toK L N c.out) * emb L N γ) ω h := by
    intro c
    have e1 : σ c = Quotient.mk'' (c.out * γ) := by
      conv_lhs => rw [← Quotient.out_eq' c]
      rfl
    have e2 : (Quotient.mk'' (σ c).out : Quotient (QuotientGroup.rightRel (Sg q))) =
        Quotient.mk'' (c.out * γ) := by
      rw [Quotient.out_eq', e1]
    have hr := Quotient.exact' e2
    rw [QuotientGroup.rightRel_apply] at hr
    have hs : (σ c).out * (c.out * γ)⁻¹ ∈ Sg q := by
      have := (Sg q).inv_mem hr
      simpa [_root_.mul_inv_rev, mul_assoc] using this
    unfold Sg at hs
    obtain ⟨x, ⟨t, rfl⟩, hx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hs)
    have eq : q * toK L N (σ c).out = toK L N t * ((q * toK L N c.out) * toK L N γ) := by
      have hsplit : (σ c).out = ((σ c).out * (c.out * γ)⁻¹) * (c.out * γ) := by group
      rw [hsplit, map_mul (toK L N) _ (c.out * γ), ← hx]
      simp [MulAut.conj_apply, mul_assoc]
    have ht : FInv ω (toP L N (toK L N t)) := hω t
    rw [eq, map_mul, map_mul, pb_mul_eq_pb_of_fInv_of_mem_Pos ht _ hh]
    rfl
  unfold mn
  congr 1
  rw [← finsum_comp_equiv σ (f := fun c => pb (toP L N (q * toK L N c.out)) ω h)]
  exact finsum_congr fun c => (key c).symm

theorem Hk_finv_scal {k : ℕ} (q : GK L N) {ω : Form (HS L N) k} (hω : ∀ s, FInv ω (scal L N s))
    (s : InfinitePlace L → ℂˣ) : FInv (Hk q ω) (scal L N s) := by
  have hcomm : ∀ g : Gp L N, g * scal L N s = scal L N s * g := by
    intro g
    unfold scal
    funext w
    exact (GeneralLinearGroup.scalar_commute (s w) (g w)).symm
  unfold FInv Hk
  intro h hh
  rw [mn_compContinuousLinearMap_actL]
  simp only [pb_actL_compContinuousLinearMap_eq_pb_mul]
  unfold mn
  congr 1
  refine finsum_congr fun c => ?_
  show pb (toP L N (q * toK L N c.out) * scal L N s) ω h = pb (toP L N (q * toK L N c.out)) ω h
  rw [hcomm, pb_mul_eq_pb_of_fInv_of_mem_Pos (hω s) _ hh]

theorem Hk_iter_props {k : ℕ} (q : GK L N) {ω : Form (HS L N) (k + 1)} (hG : Good ω)
    (hγ : ∀ γ, FInv ω (emb L N γ)) (hs : ∀ s, FInv ω (scal L N s)) (r : ℕ) :
    Good ((Hk q)^[r] ω) ∧ (∀ γ, FInv ((Hk q)^[r] ω) (emb L N γ)) ∧ ∀ s, FInv ((Hk q)^[r] ω) (scal L N s) := by
  induction r with
  | zero => exact ⟨hG, hγ, hs⟩
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨Hk_good q ih.1, Hk_finv_emb q ih.2.1, Hk_finv_scal q ih.2.2⟩

private instance pointwiseGKAction (k : ℕ) : MulAction (GK L N) (Fin (k + 2) → GK L N) where
  smul g y j := g * y j
  one_smul y := by
    funext j
    simp
  mul_smul g h y := by
    funext j
    simp [mul_assoc]

private theorem continuousOn_Hk_of_continuousOn {k : ℕ} (q : GK L N) {ω : Form (HS L N) k} (hc : ContinuousOn ω (Pos L N)) :
    ContinuousOn (Hk q ω) (Pos L N) := by
  have hpb : ∀ g : Gp L N, ContinuousOn (pb g ω) (Pos L N) := by
    intro g
    have ha : ContinuousOn (fun h => ω (actL g h)) (Pos L N) :=
      hc.comp (actL g).continuous.continuousOn fun h hh => (g • (⟨h, hh⟩ : Pos L N)).2
    unfold pb
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (actL g)).continuous.comp_continuousOn ha
  unfold Hk mn
  by_cases hfin : Finite (Quotient (QuotientGroup.rightRel (Sg q)))
  · haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Sg q)))
    simp only [finsum_eq_sum_of_fintype]
    exact ContinuousOn.const_smul (continuousOn_finsetSum _ fun c _ => hpb _) ((((Sg q).index : ℕ) : ℝ)⁻¹)
  · have hinf : Infinite (Gm L N ⧸ Sg q) := by
      rw [← not_finite_iff_infinite]
      intro hf
      exact hfin (Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (Sg q)).symm)
    have h0 : (Sg q).index = 0 := Subgroup.index_eq_zero_iff_infinite.2 hinf
    simp only [h0, Nat.cast_zero, _root_.inv_zero, zero_smul]
    exact continuousOn_const

set_option synthInstance.maxHeartbeats 200000 in
theorem hecke_iter {k : ℕ} (q : GK L N) {ω : Form (HS L N) (k + 1)} (hω : ContinuousOn ω (Pos L N)) (r : ℕ)
    (y : Fin (k + 2) → GK L N) :
    (hecke (Y := Fin (k + 2) → GK L N) (E := ℝ) (toK L N) (MonoidHom.id (GK L N)) q)^[r]
        (fun y => intP ω fun j => toP L N (y j) • one L N) y =
      intP ((Hk q)^[r] ω) fun j => toP L N (y j) • one L N := by
  have step : ∀ ω' : Form (HS L N) (k + 1), ContinuousOn ω' (Pos L N) →
      hecke (Y := Fin (k + 2) → GK L N) (E := ℝ) (toK L N) (MonoidHom.id (GK L N)) q
          (fun y : Fin (k + 2) → GK L N => intP ω' fun j => toP L N (y j) • one L N) =
        fun y : Fin (k + 2) → GK L N => intP (Hk q ω') fun j => toP L N (y j) • one L N := by
    intro ω' hc
    funext y
    rw [intP_Hk q hc]
    unfold hecke mn Sg
    congr 1
    refine finsum_congr fun c => ?_
    simp only [MonoidHom.id_apply]
    rw [intP_pb]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    simp only [smul_smul, mul_assoc]
  have hcont : ∀ n, ContinuousOn ((Hk q)^[n] ω) (Pos L N) := by
    intro n
    induction n with
    | zero => exact hω
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact continuousOn_Hk_of_continuousOn q ih
  have hall : ∀ n, (hecke (Y := Fin (k + 2) → GK L N) (E := ℝ)
        (toK L N) (MonoidHom.id (GK L N)) q)^[n]
        (fun y : Fin (k + 2) → GK L N => intP ω fun j => toP L N (y j) • one L N) =
      fun y : Fin (k + 2) → GK L N => intP ((Hk q)^[n] ω) fun j => toP L N (y j) • one L N := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, step _ (hcont n)]
  exact congrFun (hall r) y

end Lemmas

end PositivityTheory.KB.JoinReconstruction

end
end

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

section Analytic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem lem_nrm (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ A : HS L N [⋀^Fin (k + 1)]→L[ℝ] ℝ,
    ‖A‖ ^ 2 ≤ K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      (A fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 := by
  obtain ⟨Ψ, hΨ⟩ := recon (ι := Fin (k + 1)) (Module.finBasis ℝ (HS L N))
  refine ⟨‖Ψ‖ ^ 2, sq_nonneg _, fun A => ?_⟩
  have h1 := Ψ.le_opNorm (fun v => A fun i => Module.finBasis ℝ (HS L N) (v i))
  rw [hΨ] at h1
  calc ‖A‖ ^ 2 ≤ (‖Ψ‖ * ‖fun v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)) =>
          A fun i => Module.finBasis ℝ (HS L N) (v i)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ‖Ψ‖ ^ 2 * ‖fun v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)) =>
          A fun i => Module.finBasis ℝ (HS L N) (v i)‖ ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sq_le_sum _) (sq_nonneg _)

theorem lem_meas {k : ℕ} (d : Dom L N) {ω₁ : Form (HS L N) (k + 1)} (h1 : ContinuousOn ω₁ (Pos L N)) :
    AEStronglyMeasurable (fun x => fr ω₁ (ofS L N x)) (d.μ.restrict d.D) := by
  obtain ⟨Ψ, hΨ⟩ := recon (ι := Fin (k + 1)) (Module.finBasis ℝ (HS L N))
  have hc : Continuous fun x => fun v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)) =>
      fr ω₁ (ofS L N x) fun i => Module.finBasis ℝ (HS L N) (v i) :=
    continuous_pi fun v => (fr_comp_cont h1 _).comp ofS_cont
  have := Ψ.continuous.comp_aestronglyMeasurable (hc.aestronglyMeasurable (μ := d.μ.restrict d.D))
  simpa only [hΨ] using this

theorem lem_gap (hGap : SGap) (hC : IsTotallyComplex L) (π : 𝓞 L) (hπ : Prime π)
    (hπ25 : 25 ≤ Ideal.absNorm (Ideal.span {π})) (h3N : 3 ≤ N) (d : Dom L N) (f : Gp L N → ℝ) (hf : Lz d f)
    (r : ℕ) : Lz d ((hecke (toK L N) (toP L N) (qel L N π hπ.ne_zero))^[r] f) ∧
      ∫ x in d.D, ((hecke (toK L N) (toP L N) (qel L N π hπ.ne_zero))^[r] f) (ofS L N x) ^ 2 ∂d.μ ≤
        ((3 / 5 : ℝ) ^ 2) ^ r * ∫ x in d.D, f (ofS L N x) ^ 2 ∂d.μ := by
  induction r with
  | zero => exact ⟨hf, by simp⟩
  | succ r ih =>
    obtain ⟨h1, h2⟩ := hGap L hC π hπ hπ25 N h3N d _ ih.1
    rw [Function.iterate_succ_apply']
    refine ⟨h1, h2.trans ((mul_le_mul_of_nonneg_left ih.2 (by norm_num)).trans (le_of_eq ?_))⟩
    ring

end Analytic

theorem lem_bound (hGap : SGap) (hLoc : SLoc) (L : Type) [Field L] [NumberField L] (hC : IsTotallyComplex L)
    (π : 𝓞 L) (hπ : Prime π) (hπ25 : 25 ≤ Ideal.absNorm (Ideal.span {π})) (N k : ℕ) (h3N : 3 ≤ N)
    (d : Dom L N) (ω₀ : Form (HS L N) (k + 1)) (hω₀G : Good ω₀) (hω₀γ : ∀ γ, FInv ω₀ (emb L N γ))
    (hω₀s : ∀ s, FInv ω₀ (scal L N s)) (hLz0 : ∀ u : Fin (k + 1) → HS L N, Lz d (fun x => fr ω₀ x u))
    (z : Chn (Gm L N) (k + 1)) (hz : IsCyc z) :
    ∃ C : ℝ, ∀ r : ℕ, |ev (toK L N) ((hecke (toK L N) (MonoidHom.id (GK L N)) (qel L N π hπ.ne_zero))^[r]
      (fun y => intP ω₀ fun j => toP L N (y j) • one L N)) 1 z| ≤ C * (3 / 5 : ℝ) ^ r := by
  obtain ⟨K, hK0, hK⟩ := lem_nrm (L := L) (N := N) k
  obtain ⟨Cz, hCz⟩ := hLoc L N k (by omega) d z hz
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      ∫ x in d.D, fr ω₀ (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ := ⟨_, rfl⟩
  refine ⟨|Cz| * √(K * S0), fun r => ?_⟩
  rw [ev_toK _ _ (hecke_iter (qel L N π hπ.ne_zero) hω₀G.1 r) z]
  obtain ⟨ωr, hωr⟩ : ∃ ωr, ωr = (Hk (qel L N π hπ.ne_zero))^[r] ω₀ := ⟨_, rfl⟩
  rw [← hωr]
  obtain ⟨hrG, hrγ, hrs⟩ := Hk_iter_props (qel L N π hπ.ne_zero) hω₀G hω₀γ hω₀s r
  rw [← hωr] at hrG hrγ hrs
  have hLzr : ∀ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      Lz d (fun x => fr ωr x fun i => Module.finBasis ℝ (HS L N) (v i)) ∧
      ∫ x in d.D, fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ ≤
        ((3 / 5 : ℝ) ^ 2) ^ r * ∫ x in d.D, fr ω₀ (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ :=
    fun v => by
      have := lem_gap hGap hC π hπ hπ25 h3N d _ (hLz0 (fun i => Module.finBasis ℝ (HS L N) (v i))) r
      rw [← comp_Hk_iter, ← hωr] at this
      exact this
  have hsumint : Integrable (fun x => K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
      fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2) (d.μ.restrict d.D) :=
    (integrable_finsetSum _ fun v _ => (hLzr v).1.2.2.2.1).const_mul _
  have hint_r : IntegrableOn (fun x => ‖fr ωr (ofS L N x)‖ ^ 2) d.D d.μ :=
    Integrable.mono' hsumint ((lem_meas d hrG.1).norm.pow 2) (Filter.Eventually.of_forall fun x => by
      show ‖‖fr ωr (ofS L N x)‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hK _)
  have hIr : ∫ x in d.D, ‖fr ωr (ofS L N x)‖ ^ 2 ∂d.μ ≤ ((3 / 5 : ℝ) ^ 2) ^ r * (K * S0) := by
    calc ∫ x in d.D, ‖fr ωr (ofS L N x)‖ ^ 2 ∂d.μ
        ≤ ∫ x in d.D, K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
            fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ :=
          integral_mono hint_r hsumint fun x => hK _
      _ = K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)),
            ∫ x in d.D, fr ωr (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ := by
          rw [integral_const_mul, integral_finsetSum _ fun v _ => (hLzr v).1.2.2.2.1]
      _ ≤ K * ∑ v : Fin (k + 1) → Fin (Module.finrank ℝ (HS L N)), ((3 / 5 : ℝ) ^ 2) ^ r *
            ∫ x in d.D, fr ω₀ (ofS L N x) (fun i => Module.finBasis ℝ (HS L N) (v i)) ^ 2 ∂d.μ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => (hLzr v).2) hK0
      _ = ((3 / 5 : ℝ) ^ 2) ^ r * (K * S0) := by rw [hS0, ← Finset.mul_sum]; ring
  have hsq : √(((3 / 5 : ℝ) ^ 2) ^ r * (K * S0)) = (3 / 5 : ℝ) ^ r * √(K * S0) := by
    rw [← pow_mul, mul_comm 2 r, pow_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  calc |ev (emb L N) (intP ωr) (one L N) z|
      ≤ Cz * √(∫ x in d.D, ‖fr ωr (ofS L N x)‖ ^ 2 ∂d.μ) := hCz _ hrG hrγ hrs hint_r
    _ ≤ |Cz| * √(((3 / 5 : ℝ) ^ 2) ^ r * (K * S0)) :=
        mul_le_mul (le_abs_self _) (Real.sqrt_le_sqrt hIr) (Real.sqrt_nonneg _) (abs_nonneg _)
    _ = |Cz| * √(K * S0) * (3 / 5 : ℝ) ^ r := by rw [hsq]; ring

end PositivityTheory.KB.JoinReconstruction

end
end

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

theorem lem_Lz {L : Type} [Field L] [NumberField L] {N k : ℕ} (d : Dom L N) {ω' ωb : Form (HS L N) (k + 1)}
    (hω'c : ContinuousOn ω' (Pos L N)) (hωbc : ContinuousOn ωb (Pos L N))
    (hγ : ∀ γ, FInv (ω' - ωb) (emb L N γ)) (hs : ∀ s, FInv (ω' - ωb) (scal L N s))
    (hωbfr : ∀ x, fr ωb x = (d.μ.real d.D)⁻¹ • ∫ y in d.D, fr ω' (ofS L N y) ∂d.μ)
    (hint' : IntegrableOn (fun x => fr ω' (ofS L N x)) d.D d.μ)
    (hsq' : IntegrableOn (fun x => ‖fr ω' (ofS L N x)‖ ^ 2) d.D d.μ) (u : Fin (k + 1) → HS L N) :
    Lz d (fun x => fr (ω' - ωb) x u) := by
  let E : (HS L N [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (k + 1) => HS L N) ℝ u).comp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
  have hE : ∀ F, E F = F u := fun F => rfl
  have hf : IntegrableOn (fun y => fr ω' (ofS L N y) u) d.D d.μ := E.integrable_comp hint'
  set c : ℝ := (d.μ.real d.D)⁻¹ * ∫ y in d.D, fr ω' (ofS L N y) u ∂d.μ with hcdef
  have hc : ∀ x, fr ωb x u = c := by
    intro x
    rw [hωbfr x, ContinuousAlternatingMap.smul_apply, smul_eq_mul, ← hE,
      ← ContinuousLinearMap.integral_comp_comm E hint']
    rfl
  have hfun : ∀ x, fr (ω' - ωb) x u = fr ω' x u - c := by
    intro x
    rw [fr_sub, ContinuousAlternatingMap.sub_apply, hc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fr_comp_cont (hω'c.sub hωbc) u
  · intro γ x
    simp only [fr_inv (hγ γ) x]
  · intro s x
    simp only [fr_inv (hs s) x]
  · simp only [hfun]
    have hg : IntegrableOn (fun x => 2 * ‖E‖ ^ 2 * ‖fr ω' (ofS L N x)‖ ^ 2 + 2 * c ^ 2) d.D d.μ :=
      (hsq'.const_mul (2 * ‖E‖ ^ 2)).add (integrableOn_const d.fin.ne)
    refine Integrable.mono' hg ?_ ?_
    · exact ((continuous_id.sub continuous_const).pow 2).comp_aestronglyMeasurable
        (E.integrable_comp hint').aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 : |E (fr ω' (ofS L N x))| ≤ ‖E‖ * ‖fr ω' (ofS L N x)‖ := by
        rw [← Real.norm_eq_abs]
        exact E.le_opNorm _
      have h2 : (fr ω' (ofS L N x) u) ^ 2 ≤ (‖E‖ * ‖fr ω' (ofS L N x)‖) ^ 2 := by
        rw [← hE, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (fr ω' (ofS L N x) u + c)]
  · simp only [hfun]
    rw [integral_sub hf (integrableOn_const d.fin.ne), setIntegral_const, smul_eq_mul]
    rcases eq_or_ne (d.μ.real d.D) 0 with h0 | h0
    · have hz : d.μ d.D = 0 := (measureReal_eq_zero_iff d.fin.ne).mp h0
      rw [setIntegral_measure_zero _ hz, h0, zero_mul, sub_zero]
    · rw [hcdef, mul_inv_cancel_left₀ h0, sub_self]

end PositivityTheory.KB.JoinReconstruction

end
end

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

theorem lem_form (hHt : SHt) (hPU : SPU) (hWhit : SWhit) (hCen : SCen) (L : Type) [Field L] [NumberField L]
    (hC : IsTotallyComplex L) (k a N : ℕ) (h1N : 1 ≤ N) (hPUa : Nonempty (PU L N fun x => ht x ^ a))
    (c : (Fin (k + 2) → Gm L N) → ℝ) (hcI : Inv (MonoidHom.id (Gm L N)) c) (hcd : dC c = 0) :
    ∃ ω' : Form (HS L N) (k + 1), Good ω' ∧ (∀ γ, FInv ω' (emb L N γ)) ∧ (∀ s, FInv ω' (scal L N s)) ∧
      (∀ z : Chn (Gm L N) (k + 1), IsCyc z →
        ev (emb L N) (intP ω') (one L N) z = ev (MonoidHom.id (Gm L N)) c 1 z) ∧
      ∃ K, ∀ x, ‖fr ω' x‖ ≤ K * ht x ^ (a * (k + 1)) := by
  obtain ⟨P⟩ := hPUa
  obtain ⟨_, hHtinv, ⟨c0, hc0, hc0le⟩, hHtK⟩ := hHt L hC N h1N
  have hht0 : ∀ x, 0 ≤ ht x := fun x => hc0.le.trans (hc0le x)
  obtain ⟨ω, hωG, hωγ, hωs, hωz, C1, hC1⟩ := hWhit L N k (fun x => ht x ^ a) P
    (fun γ x => by simp only [hHtinv]) (fun x => pow_nonneg (hht0 x) _) c hcI hcd
  obtain ⟨p, hp⟩ : ∃ p, p = a * (k + 1) := ⟨_, rfl⟩
  have hfrB : ∀ x, ‖fr ω x‖ ≤ |C1| * ht x ^ p := fun x => by
    calc ‖fr ω x‖ ≤ C1 * (ht x ^ a) ^ (k + 1) := hC1 x
      _ ≤ |C1| * (ht x ^ a) ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (pow_nonneg (hht0 x) _) _)
      _ = |C1| * ht x ^ p := by rw [hp, ← pow_mul]
  have hB : ∀ K : Set (Gp L N), IsCompact K →
      ∃ C, ∀ g ∈ K, ∀ x, |C1| * ht (x * g) ^ p ≤ C * (|C1| * ht x ^ p) := by
    intro K hK
    obtain ⟨C, hC⟩ := hHtK K hK
    refine ⟨|C| ^ p, fun g hg x => ?_⟩
    have h1 : ht (x * g) ≤ |C| * ht x :=
      (hC g hg x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hht0 x))
    calc |C1| * ht (x * g) ^ p ≤ |C1| * (|C| * ht x) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hht0 _) h1 p) (abs_nonneg _)
      _ = |C| ^ p * (|C1| * ht x ^ p) := by rw [mul_pow]; ring
  obtain ⟨ω', hω'G, hω'γ, hω's, hω'z, C2, hC2⟩ :=
    hCen L N k ω hωG hωγ hωs (fun x => |C1| * ht x ^ p) hB hfrB
  refine ⟨ω', hω'G, hω'γ, hω's, fun z hz => (hω'z z hz).trans (hωz z hz), |C2| * |C1|, fun x => ?_⟩
  rw [← hp]
  calc ‖fr ω' x‖ ≤ C2 * (|C1| * ht x ^ p) := hC2 x
    _ ≤ |C2| * (|C1| * ht x ^ p) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (abs_nonneg _) (pow_nonneg (hht0 x) _))
    _ = |C2| * |C1| * ht x ^ p := by ring

theorem key (hPrime : SPrime) (hHecke : SHecke) (hHt : SHt) (hPU : SPU) (hMom : SMom) (hWhit : SWhit)
    (hCen : SCen) (hGap : SGap) (hLoc : SLoc) (hMean : SMean) (hInv : SInv) : SSurj := by
  intro L _ _ hC k hkr n₀
  obtain ⟨π, hπ, hπ25⟩ := hPrime L
  obtain ⟨a, hPUa⟩ := hPU L hC
  obtain ⟨N₀, hN₀⟩ := hHecke L hC k hkr π hπ
  obtain ⟨N₁, hN₁⟩ := hMom L hC (2 * (a * (k + 1)))
  obtain ⟨N, hN⟩ : ∃ N, N = max (max N₀ N₁) (max n₀ 3) := ⟨_, rfl⟩
  have hN0 : N₀ ≤ N := by rw [hN]; exact (le_max_left N₀ N₁).trans (le_max_left _ _)
  have hN1 : N₁ ≤ N := by rw [hN]; exact (le_max_right N₀ N₁).trans (le_max_left _ _)
  have hn₀ : n₀ ≤ N := by rw [hN]; exact (le_max_left n₀ 3).trans (le_max_right _ _)
  have h3N : 3 ≤ N := by rw [hN]; exact (le_max_right n₀ 3).trans (le_max_right _ _)
  have h1N : 1 ≤ N := by omega
  refine ⟨N, hn₀, fun c hcI hcd => ?_⟩
  obtain ⟨d, hd⟩ := hN₁ N hN1
  obtain ⟨ω', hω'G, hω'γ, hω's, hω'z, K, hK⟩ :=
    lem_form hHt hPU hWhit hCen L hC k a N h1N (hPUa N h1N) c hcI hcd
  obtain ⟨_, _, ⟨c0, hc0, hc0le⟩, _⟩ := hHt L hC N h1N
  have hht0 : ∀ x, 0 ≤ ht x := fun x => hc0.le.trans (hc0le x)
  haveI : IsFiniteMeasure (d.μ.restrict d.D) := isFiniteMeasure_restrict.2 d.fin.ne
  have hsq' : IntegrableOn (fun x => ‖fr ω' (ofS L N x)‖ ^ 2) d.D d.μ := by
    refine Integrable.mono' (hd.const_mul (K ^ 2)) ((lem_meas d hω'G.1).norm.pow 2)
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖‖fr ω' (ofS L N x)‖ ^ 2‖ ≤ K ^ 2 * ht (ofS L N x) ^ (2 * (a * (k + 1)))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_comm 2 (a * (k + 1)), pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK _) 2
  have hint' : IntegrableOn (fun x => fr ω' (ofS L N x)) d.D d.μ := by
    refine Integrable.mono' (hsq'.add (integrable_const (1 : ℝ))) (lem_meas d hω'G.1)
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖fr ω' (ofS L N x)‖ ≤ ‖fr ω' (ofS L N x)‖ ^ 2 + 1
    nlinarith [sq_nonneg (‖fr ω' (ofS L N x)‖ - 1)]
  obtain ⟨ωb, hωbI, hωbfr⟩ := hMean L N (k + 1) h1N d ω' hω'G.1 hω'γ hω's hint'
  have hωbG : Good ωb := (hInv L N k ωb hωbI).1
  have hγ0 : ∀ γ, FInv (ω' - ωb) (emb L N γ) := fun γ => finv_sub (hω'γ γ) (hωbI _)
  have hs0 : ∀ s, FInv (ω' - ωb) (scal L N s) := fun s => finv_sub (hω's s) (hωbI _)
  have hLz0 := lem_Lz d hω'G.1 hωbG.1 hγ0 hs0 hωbfr hint' hsq'
  have e2 : intP (ω' - ωb) = fun y => intP ω' y - intP ωb y := funext (intP_sub hω'G.1 hωbG.1)
  have hG0 : Good (ω' - ωb) := by
    refine ⟨hω'G.1.sub hωbG.1, ?_⟩
    rw [e2, dC_sub, hω'G.2, hωbG.2]
    funext y
    simp
  have hFI : Inv (toK L N) (fun y : Fin (k + 2) → GK L N => intP (ω' - ωb) fun j => toP L N (y j) • one L N) :=
    fun γ y => by
      show (intP (ω' - ωb) fun j => toP L N (toK L N γ • y j) • one L N) =
        intP (ω' - ωb) fun j => toP L N (y j) • one L N
      simp only [smul_eq_mul, map_mul, mul_smul]
      exact intP_inv (hγ0 γ) _
  have hFd : dC (fun y : Fin (k + 2) → GK L N => intP (ω' - ωb) fun j => toP L N (y j) • one L N) = 0 := by
    funext y
    have h4 := congrFun hG0.2 (fun j => toP L N (y j) • one L N)
    simp only [dC, Pi.zero_apply] at h4 ⊢
    exact h4
  have hF0 := hN₀ N hN0 _ hFI hFd fun z hz =>
    lem_bound hGap hLoc L hC π hπ hπ25 N k h3N d (ω' - ωb) hG0 hγ0 hs0 hLz0 z hz
  refine ⟨ωb, hωbI, fun z hz => ?_⟩
  have h5 := hF0 z hz
  rw [ev_toK _ (intP (ω' - ωb)) (fun y => rfl) z, e2, ev_sub] at h5
  rw [← hω'z z hz]
  linarith

end PositivityTheory.KB.JoinReconstruction

end
end

namespace PositivityTheory.KB

theorem sSurj_of : SPrime → SHecke → SHt → SPU → SMom → SWhit → SCen → SGap → SLoc → SMean → SInv → SSurj :=
  JoinReconstruction.key

end PositivityTheory.KB
