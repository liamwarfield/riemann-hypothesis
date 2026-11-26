module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantTermHeisOAlong
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceTransvectionActsPositivelyInvariantFor
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceTransvectionActsPositivelyInvariantFor
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.SplitTransvection

theorem exists_invariant_sum {L V : Type} [AddCommGroup L] [TopologicalSpace L] [IsTopologicalAddGroup L]
    [CompactSpace L] [AddCommGroup V] (γ : L → V) (U : Set L) (hU : U ∈ nhds (0 : L))
    (hγ : ∀ u ∈ U, ∀ a, γ (a + u) = γ a) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (σ : ι → L), ∀ b, ∑ i, γ (b + σ i) = ∑ i, γ (σ i) := by
  let H : AddSubgroup L :=
    { carrier := {u | ∀ a, γ (a + u) = γ a}
      zero_mem' := fun a => by rw [add_zero]
      add_mem' := fun {u w} hu hw a => by rw [← add_assoc, hw, hu]
      neg_mem' := fun {u} hu a => by rw [← hu (a + -u), neg_add_cancel_right] }
  have hH : IsOpen (H : Set L) := H.isOpen_of_mem_nhds (Filter.mem_of_superset hU hγ)
  haveI : Finite (L ⧸ H) := H.quotient_finite_of_isOpen hH
  letI : Fintype (L ⧸ H) := Fintype.ofFinite _
  refine ⟨L ⧸ H, inferInstance, inferInstance, Quotient.out, fun b => ?_⟩
  refine Fintype.sum_equiv (Equiv.addLeft (b : L ⧸ H)) _ _ fun q => ?_
  have h : -(b + q.out) + ((b : L ⧸ H) + q).out ∈ H := by
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  have := h (b + q.out)
  rw [add_neg_cancel_left] at this
  exact this.symm

theorem undo_dual {E R : Type} [Field E] [CommRing R] (φ : E →+* R) {n : ℕ} {c : E} (hc : c ≠ 0)
    {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (x : Fin n → R) :
    φ c⁻¹ • ((φ c • (x ᵥ* (G⁻¹).map φ)) ᵥ* G.map φ) = x := by
  rw [Matrix.smul_vecMul, smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul, Matrix.vecMul_vecMul,
    ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hG.isUnit, Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]

theorem undo_transv {R : Type} [CommRing R] {m n : ℕ} {A B N : Matrix (Fin m) (Fin m) R} {a : R} (hAB : A * B = 1)
    (hB : B = 1 + a • N) (t : Matrix (Fin m) (Fin n) R) : A * (t + a • (N * t)) * (1 : Matrix (Fin n) (Fin n) R) = t := by
  have : t + a • (N * t) = B * t := by rw [hB, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hAB, Matrix.one_mul]

theorem smul_dual {R : Type} [CommRing R] {n : ℕ} (e c : R) (M : Matrix (Fin n) (Fin n) R) {x : Fin n → R}
    (hx : e • x = x) : e • (c • (x ᵥ* M)) = c • (x ᵥ* M) := by
  rw [smul_comm, ← Matrix.smul_vecMul, hx]

theorem exists_compact_annihilator_ultrametric_field {K R : Type} [NormedField K] [IsUltrametricDist K] [ProperSpace K] [CommRing R]
    [TopologicalSpace R] (j₀ : K → R) (hsub : ∀ x x', j₀ (x - x') = j₀ x - j₀ x') (hj : Continuous j₀) (P : R → Prop) (y : K)
    (hy : ∀ x, x ≠ 0 → ¬ P (j₀ x * j₀ (y / x))) {n : ℕ} {V : Set (Fin n → R)} (hV : V ∈ nhds (0 : Fin n → R)) :
    ∃ L : AddSubgroup (Fin n → R), IsCompact (L : Set (Fin n → R)) ∧ (∀ s ∈ L, ∀ i, ∃ x, s i = j₀ x) ∧
      ∀ η : Fin n → R, (∀ i, ∃ x, η i = j₀ x) → (∀ s ∈ L, P (η ⬝ᵥ s)) → η ∈ V := by
  let j : K →+ R := AddMonoidHom.ofMapSub j₀ hsub
  let J : (Fin n → K) →+ (Fin n → R) := j.compLeft (Fin n)
  have hJ : Continuous J := continuous_pi fun i => hj.comp (continuous_apply i)
  have hV' : J ⁻¹' V ∈ nhds (0 : Fin n → K) := hJ.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV'
  have hR : 0 < ‖y‖ / r + 1 := by positivity
  refine ⟨(IsUltrametricDist.closedBall_openAddSubgroup (Fin n → K) hR).toAddSubgroup.map J,
    (isCompact_closedBall (0 : Fin n → K) _).image hJ, ?_, fun η hη hs => ?_⟩
  · rintro _ ⟨x, -, rfl⟩ i
    exact ⟨x i, rfl⟩
  choose x hx using hη
  have hx' : η = J x := funext hx
  rw [hx']
  refine hball (mem_ball_zero_iff.2 ((pi_norm_lt_iff hr).2 fun i => ?_))
  by_contra hn
  rw [not_lt] at hn
  have hxpos : 0 < ‖x i‖ := hr.trans_le hn
  have hmem : (Pi.single i (y / x i) : Fin n → K) ∈ Metric.closedBall 0 (‖y‖ / r + 1) := by
    rw [mem_closedBall_zero_iff, Pi.norm_single, norm_div]
    have : ‖y‖ / ‖x i‖ ≤ ‖y‖ / r := div_le_div_of_nonneg_left (norm_nonneg _) hr hn
    linarith
  have h := hs _ ⟨_, hmem, rfl⟩
  have e1 : J (Pi.single i (y / x i)) = Pi.single i (j (y / x i)) := by
    funext k
    show j ((Pi.single i (y / x i) : Fin n → K) k) = _
    by_cases hk : k = i
    · subst hk; simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hk, map_zero]
  rw [e1, dotProduct_single, hx] at h
  exact hy _ (norm_pos_iff.1 hxpos) h


open GlobalTheory.IdemModTwo GlobalTheory.SplitAnnihilator in
theorem exists_compact_dual {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1)
    {e : AE D} (hε : IsSplitIdem D e) {n : ℕ} {V : Set (Fin n → AE D)} (hV : V ∈ nhds (0 : Fin n → AE D)) :
    ∃ L : AddSubgroup (Fin n → AE D), IsCompact (L : Set (Fin n → AE D)) ∧ (∀ s ∈ L, e • s = s) ∧
      ∀ η : Fin n → AE D, e • η = η → (∀ s ∈ L, ψ (Algebra.trace (AF D.host.F) (AE D) (η ⬝ᵥ s)) = 1) → η ∈ V := by
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  obtain ⟨y, hy⟩ := hψ v
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  have hj : Continuous fun x : Fv D.host.F v => fj D (singleV D.host.F v x) * e := by
    have h1 : Continuous (algebraMap (AF D.host.F) (AE D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
    have h2 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV D.host.F v)
    exact (h1.comp h2).mul continuous_const
  obtain ⟨L, h1, h2, h3⟩ := exists_compact_annihilator_ultrametric_field (K := Fv D.host.F v)
    (fun x => fj D (singleV D.host.F v x) * e)
    (fun x x' => by rw [singleV_sub, map_sub, sub_mul]) hj
    (fun a => ψ (Algebra.trace (AF D.host.F) (AE D) a) = 1) y (fun x hx h => by
      have h' := congrArg ψ (trace_split he x (y / x))
      rw [mul_div_cancel₀ _ hx] at h'
      exact hy (h'.symm.trans h)) hV
  refine ⟨L, h1, fun s hs => funext fun i => ?_, fun η hη => h3 η fun i => ?_⟩
  · obtain ⟨x, hx⟩ := h2 s hs i
    have hx' : s i = fj D (singleV D.host.F v x) * e := hx
    rw [Pi.smul_apply, smul_eq_mul, hx', mul_left_comm, he.1]
  · obtain ⟨x, hx⟩ := he.exists_scalar (η i)
    exact ⟨x, (congrFun hη i).symm.trans hx⟩

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def rowOf (S T : HSp D) (ξ : Fin T.rank → D.host.E) (t : WO S T) : Fin S.rank → AE D :=
  (fun d => incA D (((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* T.gram) d)) ᵥ*
    (t : Matrix (Fin T.rank) (Fin S.rank) (AE D))

theorem nil_mul (ξ : Fin T.rank → D.host.E) (t : WO S T) :
    HMul.hMul ((TransvGroup.nilM T ξ).map (incA D)) (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      along S T ξ (rowOf S T ξ t) := by
  rw [along, rowOf, ← Matrix.vecMulVec_mul]
  congr 1
  ext i j
  simp only [Matrix.map_apply, vecMulVec_apply, RingHom.map_mul]

theorem along_smul (ξ : Fin T.rank → D.host.E) (c : AE D) (a : Fin S.rank → AE D) :
    along S T ξ (c • a) = c • along S T ξ a := by
  ext i j
  simp only [along, vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem along_add (ξ : Fin T.rank → D.host.E) (a b : Fin S.rank → AE D) :
    along S T ξ (a + b) = along S T ξ a + along S T ξ b := by
  ext i j
  simp only [along, vecMulVec_apply, Pi.add_apply, Matrix.add_apply, mul_add]

theorem rowOf_smul (ξ : Fin T.rank → D.host.E) (c : AE D) (t : WO S T) :
    rowOf S T ξ (c • t) = c • rowOf S T ξ t := Matrix.vecMul_smul _ _ _

theorem hO_along (ξ : Fin T.rank → D.host.E) (t : WO S T) (s : Fin S.rank → AE D) :
    hO S T t (along S T ξ fun b => cA D (s b)) = (rowOf S T ξ t ᵥ* (S.gram⁻¹).map (incA D)) ⬝ᵥ s := by
  have e : ∀ x, incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = cA D (incA D x) :=
    fun x => (GlobalTheory.DualPairCheck.cA_incA x).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hO, along, rowOf, vecMulVec_apply, vecMul, dotProduct, Matrix.map_apply, RingHom.map_mul, map_sum,
    GlobalTheory.DualPairCheck.cA_cA, e, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem symplO_along (ξ : Fin T.rank → D.host.E) (t : WO S T) (s : Fin S.rank → AE D) :
    Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0 • (rowOf S T ξ t ᵥ* (S.gram⁻¹).map (incA D))) ⬝ᵥ s) =
      symplO S T t (along S T ξ fun b => cA D (s b)) := by
  rw [symplO, hO_along]
  exact congrArg _ (smul_dotProduct _ _ _)

theorem det_eq_one {ξ : Fin T.rank → D.host.E} (h : IsoVec T ξ) {z : GA D T} (hz : z ∈ ZI T ξ) :
    (Formalism.L2.Theta.mt T z).det = 1 := by
  obtain ⟨a, -, ha⟩ := TransvGroup.exists_skew h hz
  have e : a • (TransvGroup.nilM T ξ).map (incA D) = vecMulVec (a • fun i => incA D (ξ i))
      (fun d => incA D (((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* T.gram) d)) := by
    ext i j
    simp only [Matrix.map_apply, vecMulVec_apply, RingHom.map_mul, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      mul_assoc]
  have h2 := congrArg (incA D) h.2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.dotProduct_mulVec, dotProduct, map_sum, RingHom.map_zero] at h2
  simp only [RingHom.map_mul] at h2
  rw [Formalism.L2.Theta.mt, ha, e, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    dotProduct, h2, smul_zero, add_zero]


set_option maxHeartbeats 800000 in
open GlobalTheory.SplitScalar in
theorem eq_zero_of_small (hψ : IsStdChar D ψ (-1)) {ξ : Fin T.rank → D.host.E} {e : AE D} (he : IsSplitIdem D e)
    {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) {V : Set (Fin S.rank → AE D)} (hV : V ∈ nhds (0 : Fin S.rank → AE D))
    (H : ∀ m : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → m (heisO ψ S T u f) = m f) →
      ∀ t, IsHalf e t → rowOf S T ξ t ∈ V → m (heisO ψ S T t g) = 0)
    (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) (hℓ : ∀ a f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (along S T ξ a) f) = ℓ f) :
    ℓ g = 0 := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have he' := isSplitIdem_conj he
  have hcl := fun f (hf : IsThetaFunO ψ S T f) u => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  have hφ : Continuous fun η : Fin S.rank → AE D => incA D D.host.xi0⁻¹ • (η ᵥ* S.gram.map (incA D)) :=
    continuous_pi fun i => continuous_const.mul
      ((continuous_apply i).comp (continuous_id.matrix_vecMul continuous_const))
  obtain ⟨L, hLc, hLe, hLd⟩ := exists_compact_dual (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) he
    (hφ.continuousAt.preimage_mem_nhds (x := 0) (t := V) (by rwa [Matrix.zero_vecMul, smul_zero]))
  have : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  let α : L → WO S T := fun s => along S T ξ fun b => cA D (s.1 b)
  have hαh : ∀ s, IsHalf (cA D e) (α s) := fun s => by
    rw [isHalf_iff, ← along_smul]
    congr 1
    funext b
    rw [Pi.smul_apply, smul_eq_mul, ← RingHom.map_mul]
    exact congrArg (cA D) (congrFun (hLe s.1 s.2) b)
  have hαa : ∀ s s' f, heisO ψ S T (α (s + s')) f = heisO ψ S T (α s) (heisO ψ S T (α s') f) := fun s s' f => by
    rw [← heisO_add_of_orth ψ S T (half_orth he' (hαh s) (hαh s')), ← along_add]
    exact congrArg (fun x => heisO ψ S T (along S T ξ x) f) (funext fun b => (cA D).map_add (s.1 b) (s'.1 b))
  have hαc : Continuous α := continuous_matrix fun i k => continuous_const.mul
    (GlobalTheory.FockCompare.ThetaCont.continuous_conj.comp ((continuous_apply k).comp continuous_subtype_val))
  have hα0 : α 0 = 0 := by
    ext i k
    show _ * cA D 0 = 0
    rw [RingHom.map_zero, mul_zero]
  obtain ⟨U, hUo, hU⟩ := hg.level
  obtain ⟨ι, _, _, σ, hσ⟩ := exists_invariant_sum (fun s => heisO ψ S T (α s) g) (α ⁻¹' U)
    (hαc.continuousAt.preimage_mem_nhds (by rw [hα0]; exact hUo.mem_nhds U.zero_mem))
    fun u hu a => by rw [hαa, hU _ hu (half_fin he' (hαh u))]
  have theta_zero : IsThetaFunO ψ S T 0 := {
    quasi γ w := by simp only [Pi.zero_apply, mul_zero]
    level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
    cont := continuous_const
    smooth k L _ _ w := contDiff_const }
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
      IsThetaFunO ψ S T (f + g) := {
    quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
    cont := hf.cont.add hg.cont
    smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w) }
  have hth : IsThetaFunO ψ S T (∑ i, heisO ψ S T (α (σ i)) g) :=
    Finset.sum_induction _ _ (fun _ _ => theta_add) theta_zero
      fun i _ => hcl g hg _
  have h0 : ∑ i, heisO ψ S T (α (σ i)) g = 0 := by
    refine GlobalTheory.T.theta_function_zero_of_invariant_functionals D ψ hψ S T e he _ hth fun m hm t ht => ?_
    have key : ∀ s f, IsThetaFunO ψ S T f →
        m (heisO ψ S T t (heisO ψ S T (α s) f)) = ψ (symplO S T t (α s)) * m (heisO ψ S T t f) := fun s f hf => by
      rw [heisO_comm, map_smul, hm _ (hαh s) _ (hcl f hf t), smul_eq_mul]
    by_cases hb : ∀ s, ψ (symplO S T t (α s)) = 1
    · have hrow : rowOf S T ξ t ∈ V := by
        have h1 := hLd (incA D D.host.xi0 • (rowOf S T ξ t ᵥ* (S.gram⁻¹).map (incA D)))
          (smul_dual _ _ _ ((rowOf_smul ξ e t).symm.trans (congrArg _ ((isHalf_iff _ _).1 ht))))
          fun s hs => (congrArg ψ (symplO_along ξ t s)).trans (hb ⟨s, hs⟩)
        rwa [Set.mem_preimage, undo_dual (incA D) (GlobalTheory.IndefiniteRowSideFullHecke.BesselData.embedding_xi_zero_ne_zero D) (gram_det_ne S)] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [heisO_sum, map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [key _ _ hg, H m hm t ht hrow, mul_zero]
    · obtain ⟨s, hs⟩ := not_forall.1 hb
      have h1 := key s _ hth
      have h2 : heisO ψ S T (α s) (∑ i, heisO ψ S T (α (σ i)) g) = ∑ i, heisO ψ S T (α (σ i)) g := by
        rw [heisO_sum, ← hσ s]
        exact Finset.sum_congr rfl fun i _ => (hαa _ _ _).symm
      rw [h2] at h1
      exact (mul_left_eq_self₀.1 h1.symm).resolve_left hs
  have h1 := congrArg ℓ h0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero, Finset.sum_congr rfl fun i _ => hℓ _ g hg, Finset.sum_const, nsmul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)


open GlobalTheory.SplitScalar in
theorem transvection_pos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ ξ, IsoVec T ξ → ∀ e, IsSplitIdem D e → ∀ z ∈ ZI T ξ, Formalism.L2.Theta.SuppAt e T z → ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ a f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (along S T ξ a) f) = ℓ f) → ∀ f, IsThetaFunO ψ S T f → ℓ (om (1, z) f) = (r : ℂ) * ℓ f := by
  intro D ψ S T χS χT om hW ξ hξ e he z hz hsupp
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h1 : Formalism.L2.Theta.mt S 1 = 1 := rfl
  obtain ⟨r, hr, hm⟩ := hW.om_split e he 1 z (fun i j => by rw [h1, sub_self, Matrix.zero_apply, mul_zero]) hsupp 1 1
    (by rw [IsDetAt, h1, det_one, mul_one, add_sub_cancel]; rfl)
    (by rw [IsDetAt, det_eq_one hξ hz, mul_one, add_sub_cancel]; rfl)
  refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
  obtain ⟨a, -, ha⟩ := TransvGroup.exists_skew hξ (inv_mem hz)
  obtain ⟨U, hUo, hU⟩ := hf.level
  have hc : Continuous fun η : Fin S.rank → AE D => a • along S T ξ η :=
    continuous_matrix fun i k => continuous_const.mul (continuous_const.mul (continuous_apply k))
  have h0 : a • along S T ξ 0 = 0 := by
    ext i k
    show a * (_ * 0) = 0
    rw [mul_zero, mul_zero]
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := {
    quasi γ w := by
      rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    cont := hf.cont.const_smul c
    smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w) }
  have := eq_zero_of_small (ξ := ξ) hW.std he
    (GlobalTheory.OrientedHeis.theta_sub (hW.om_pres (1, z) f hf) (theta_smul r hf))
    (hc.continuousAt.preimage_mem_nhds (x := 0) (t := U) (by rw [h0]; exact hUo.mem_nhds U.zero_mem))
    (fun m hm' t ht hrow => ?_) ℓ hℓ
  · rwa [map_sub, map_smul, sub_eq_zero] at this
  have hd : IsHalf e (a • along S T ξ (rowOf S T ξ t)) := by
    rw [isHalf_iff, smul_comm, ← along_smul, ← rowOf_smul, (isHalf_iff _ _).1 ht]
  have hact : actO S T 1 z (t + a • along S T ξ (rowOf S T ξ t)) = t := by
    have e2 : Formalism.L2.Theta.mt T z * Formalism.L2.Theta.mt T z⁻¹ = 1 :=
      congrArg Units.val (show matHom T z * matHom T z⁻¹ = 1 from
        ((matHom T).map_mul z z⁻¹).symm.trans (by rw [mul_inv_cancel, MonoidHom.map_one]))
    rw [actO, inv_one, h1, ← nil_mul]
    exact undo_transv e2 ha t
  have h2 := hW.om_heis 1 z (t + a • along S T ξ (rowOf S T ξ t)) f hf
  rw [hact, heisO_add_of_orth ψ S T (half_orth he ht hd), hU _ hrow (half_fin he hd)] at h2
  rw [← heisL_apply, map_sub, map_smul, map_sub, map_smul, heisL_apply, heisL_apply, ← h2,
    hm m hm' _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf t), splitFacO, map_one, map_one, inv_one, mul_one,
    Circle.coe_one, mul_one, smul_eq_mul, sub_self]

end GlobalTheory.SplitTransvection

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceTransvectionActsPositivelyInvariantForStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceTransvection_acts_positively_invariant_forms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ ξ, IsoVec T ξ → ∀ e, IsSplitIdem D e → ∀ z ∈ ZI T ξ, Formalism.L2.Theta.SuppAt e T z → ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ a f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (along S T ξ a) f) = ℓ f) → ∀ f, IsThetaFunO ψ S T f → ℓ (om (1, z) f) = (r : ℂ) * ℓ f := by
  first | exact @GlobalTheory.SplitTransvection.transvection_pos | exact GlobalTheory.SplitTransvection.transvection_pos | (intros; apply GlobalTheory.SplitTransvection.transvection_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetIntegralMulLeft
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.AverageConst

@[to_additive setIntegral_add_left]
theorem setIntegral_mul_left {Z : Type} [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Λ : Subgroup Z) [Countable Λ] (μ : Measure Z)
    [μ.IsMulLeftInvariant] {F : Set Z} (hF : IsFundamentalDomain Λ F μ) (φ : Z → ℂ)
    (hφ : ∀ γ ∈ Λ, ∀ z, φ (γ * z) = φ z) (a : Z) : ∫ z in F, φ (a * z) ∂μ = ∫ z in F, φ z ∂μ := by
  have : SMulCommClass Z Λ Z := ⟨fun a γ z => by
    change a * ((γ : Z) * z) = (γ : Z) * (a * z)
    rw [← mul_assoc, hc a, mul_assoc]⟩
  rw [hF.setIntegral_eq (hF.smul_of_comm a) fun γ z => hφ γ γ.2 z]
  exact ((measurePreserving_mul_left μ a).setIntegral_image_emb (measurableEmbedding_mulLeft a) φ F).symm

theorem average_const {Y Z A : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (Γ : AddSubgroup Y)
    [DiscreteTopology Γ] {K : Set Y} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) [AddCommGroup A] (χ : A → Y → ℂ)
    (h1 : ∀ a, Continuous (χ a)) (h2 : ∀ a x y, χ a (x + y) = χ a x * χ a y) (h3 : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (h4 : ∀ x, χ 0 x = 1) (h5 : ∀ a x, ‖χ a x‖ = 1) (h6 : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ)
    (ν : Measure Y) [ν.IsAddHaarMeasure] {G : Set Y} (hG : IsAddFundamentalDomain Γ G ν)
    [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] (hc : ∀ a b : Z, a * b = b * a) (Λ : Subgroup Z) [Countable Λ] (μ : Measure Z)
    [μ.IsMulLeftInvariant] {F : Set Z} (hF : IsFundamentalDomain Λ F μ) (hfin : μ F ≠ ⊤)
    (k : Z → Y → ℂ) (kz : ∀ y, Continuous fun z => k z y) (ky : ∀ z, Continuous (k z)) {C : ℝ} (kb : ∀ z y, ‖k z y‖ ≤ C)
    (kΛ : ∀ γ ∈ Λ, ∀ z y, k (γ * z) y = k z y) (kΓ : ∀ γ ∈ Γ, ∀ z y, k z (γ + y) = k z y)
    (htw : ∀ a, (∀ y, χ a y = 1) ∨ ∃ (z₁ : Z) (c : ℂ), c ≠ 1 ∧
      ∀ z, ∫ y in G, χ a y * k (z₁ * z) y ∂ν = c * ∫ y in G, χ a y * k z y ∂ν) (y₀ : Y) :
    ∫ z in F, k z y₀ ∂μ = ∫ z in F, k z 0 ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (ν.restrict G) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov ν hG⟩
  have : IsFiniteMeasure (μ.restrict F) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Y → ℂ, ∀ y, Φ y = ∫ z in F, k z y ∂μ := ⟨_, fun _ => rfl⟩
  have hΦc : Continuous Φ := by
    rw [funext hΦ]
    exact continuous_of_dominated (bound := fun _ => C) (fun y => (kz y).aestronglyMeasurable)
      (fun y => .of_forall fun z => kb z y) (integrable_const _) (.of_forall ky)
  have hΦp : ∀ γ ∈ Γ, ∀ y, Φ (γ + y) = Φ y := fun γ hγ y => by simp only [hΦ, kΓ γ hγ]
  have hΦb : ∀ y, ‖Φ y‖ ≤ C * (μ.restrict F).real Set.univ := fun y => by
    rw [hΦ]; exact norm_integral_le_of_norm_le_const (.of_forall fun z => kb z y)
  have hint : ∀ a y₁, Integrable (fun y => χ a y * Φ (y₁ + y)) (ν.restrict G) := fun a y₁ =>
    Integrable.of_bound ((h1 a).mul (hΦc.comp (continuous_const.add continuous_id))).aestronglyMeasurable _
      (.of_forall fun y => by rw [norm_mul, h5, one_mul]; exact hΦb _)
  have hco : ∀ a, (∀ y, χ a y = 1) ∨ ∫ y in G, χ a y * Φ y ∂ν = 0 := fun a => (htw a).imp_right fun ⟨z₁, c, hc1, h⟩ => by
    have hm : StronglyMeasurable (Function.uncurry fun y z => χ a y * k z y) :=
      stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun z => (h1 a).mul (ky z))
        fun y => (continuous_const.mul (kz y)).stronglyMeasurable
    have e : ∫ y in G, χ a y * Φ y ∂ν = ∫ z in F, ∫ y in G, χ a y * k z y ∂ν ∂μ := by
      simp only [hΦ, ← integral_const_mul]
      exact integral_integral_swap (Integrable.of_bound hm.aestronglyMeasurable C (.of_forall fun p => by
        rw [Function.uncurry, norm_mul, h5, one_mul]; exact kb _ _))
    have e2 := setIntegral_mul_left hc Λ μ hF (fun z => ∫ y in G, χ a y * k z y ∂ν)
      (fun γ hγ z => by simp only [kΛ γ hγ]) z₁
    simp only [h, integral_const_mul] at e2
    rw [e]
    exact (mul_left_eq_self₀.1 e2).resolve_left hc1
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero Y Γ K hK hcov A χ h1 h2 h3 h4 h5 h6 ν G
    inferInstance hG (fun y => Φ (y₀ + y) - Φ (0 + y))
    ((hΦc.comp (continuous_const.add continuous_id)).sub (hΦc.comp (continuous_const.add continuous_id)))
    (fun γ hγ y => by rw [add_left_comm, hΦp γ hγ, add_left_comm, hΦp γ hγ]) fun a => by
      have e := setIntegral_add_left add_comm Γ ν hG (fun y => χ a y * Φ y)
        (fun γ hγ y => by rw [h2, (h6 γ).2 hγ, one_mul, hΦp γ hγ]) y₀
      simp only [h2, mul_assoc, integral_const_mul] at e
      simp only [mul_sub]
      rw [integral_sub (hint a _) (hint a _), sub_eq_zero]
      simp only [zero_add]
      rcases hco a with h | h
      · rwa [h, one_mul] at e
      · rw [h] at e ⊢
        exact (mul_eq_zero.1 e).resolve_left fun h0 => by simpa [h0] using h5 a y₀
  have := congrFun key 0
  simp only [add_zero, Pi.zero_apply, sub_eq_zero] at this
  rw [← hΦ, ← hΦ, this]

end GlobalTheory.AverageConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantTermHeisOAlong
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift GlobalTheory.OrientedHeis GlobalTheory.HolDict.TransvGroup

namespace GlobalTheory.TransvConst

variable {D : D7} {S T : HSp D} {ξ : Fin T.rank → D.host.E} {ψ : AddChar (AF D.host.F) ℂ}

def row (S T : HSp D) (ξ : Fin T.rank → D.host.E) (y : WO S T) : Fin S.rank → AE D :=
  fun j => ∑ c, ∑ d, incA D (star (ξ c) * T.gram c d) * y d j

theorem along_add (a b : Fin S.rank → AE D) : along S T ξ (a + b) = along S T ξ a + along S T ξ b :=
  Matrix.ext fun _ _ => mul_add _ _ _

theorem along_zero : along S T ξ 0 = 0 := Matrix.ext fun _ _ => mul_zero _

theorem row_along (h : IsoVec T ξ) (a : Fin S.rank → AE D) : row S T ξ (along S T ξ a) = 0 := by
  funext j
  have h1 : ∑ c, ∑ d, star (ξ c) * T.gram c d * ξ d = 0 := by
    rw [← h.2]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rfl
  have h2 := congrArg (fun x => incA D x * a j) h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul, map_zero, zero_mul] at h2
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_) h2
  rw [RingHom.map_mul _ _ (ξ d), mul_assoc]
  rfl

theorem hO_along (a : Fin S.rank → AE D) (y : WO S T) :
    hO S T (along S T ξ a) y = ∑ i, ∑ j, incA D (S.gram⁻¹ i j) * cA D (row S T ξ y j) * a i := by
  unfold hO row
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [RingHom.map_mul (cA D), GlobalTheory.DualPairCheck.cA_incA, star_mul', star_star, GlobalTheory.DualPairCheck.gram_star, RingHom.map_mul]
  change _ * (incA D (ξ c) * a i) = _
  ring

theorem symplO_along {y : WO S T} (h : row S T ξ y = 0) (a : Fin S.rank → AE D) : symplO S T (along S T ξ a) y = 0 := by
  simp only [symplO, hO_along, h, Pi.zero_apply, RingHom.map_zero, mul_zero, zero_mul, Finset.sum_const_zero, map_zero]

theorem symplOH_along (h : IsoVec T ξ) (a b : Fin S.rank → AE D) :
    symplOH S T (along S T ξ a) (along S T ξ b) = 0 := by
  rw [symplOH, symplO_along (row_along h b), mul_zero]

theorem actO_transv {z : GA D T} {t : AE D} (hz : (matHom T z).1 = 1 + t • (nilM T ξ).map (incA D)) (y : WO S T) :
    actO S T 1 z y = along S T ξ (t • row S T ξ y) + y := by
  have e : actO S T 1 z y = HMul.hMul (matHom T z).1 y := by
    unfold actO
    rw [inv_one]
    exact Matrix.mul_one _
  rw [e, hz, Matrix.add_mul, Matrix.one_mul, add_comm, Matrix.smul_mul]
  congr 1
  refine Matrix.ext fun i j => ?_
  change t * ∑ d, incA D (ξ i * ∑ c, star (ξ c) * T.gram c d) * y d j = incA D (ξ i) * (t * row S T ξ y j)
  rw [row, Finset.sum_comm, mul_left_comm, Finset.mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RingHom.map_mul _ (ξ i), map_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]

theorem actO_along (h : IsoVec T ξ) {z : GA D T} (hz : z ∈ ZI T ξ) (a : Fin S.rank → AE D) :
    actO S T 1 z (along S T ξ a) = along S T ξ a := by
  obtain ⟨t, -, e⟩ := exists_skew h hz
  rw [actO_transv e, row_along h, smul_zero, along_zero, zero_add]

theorem norm_ne_zero (hS : ∀ τ, (gramAt D S τ).PosDef) {m : Fin S.rank → D.host.E} (hm : m ≠ 0) :
    ∑ i, ∑ j, S.gram⁻¹ i j * star (m j) * m i ≠ 0 := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hinv : (gramAt D S τ)⁻¹ = (S.gram⁻¹).map (tauE D τ) := Matrix.inv_eq_right_inv (by
    rw [gramAt, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)])
  have hs : ∀ x, tauE D τ (star x) = star (tauE D τ x) := GlobalTheory.FockCompare.tauE_star τ
  have h := (hS τ).inv.dotProduct_mulVec_pos (x := fun i => tauE D τ (star (m i))) fun h0 => hm (funext fun i => by
    have := congrFun h0 i
    simpa using this)
  intro h0
  refine h.ne' ?_
  rw [← (tauE D τ).map_zero, ← h0, hinv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hs, Pi.star_apply, star_star, Matrix.map_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem trace_three (s : AF D.host.F) (a b c : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (incA D a * ((s ⊗ₜ[D.host.F] b : AE D) * incA D c)) =
      s * algebraMap _ _ (Algebra.trace D.host.F D.host.E (a * (b * c))) := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have h2 : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun x => rfl
  rw [h2, h2, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, GlobalTheory.LatVac.trace_tmul]

theorem cancel_two {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] (p : R) {q : F} (hq : q ≠ 0) :
    algebraMap F R (1 / 2) * (p * algebraMap F R q⁻¹ * algebraMap F R (2 • q)) = p := by
  rw [mul_left_comm, mul_assoc, ← map_mul, ← map_mul,
    show q⁻¹ * (1 / 2 * (2 • q)) = 1 by rw [nsmul_eq_mul]; push_cast; field_simp, map_one, mul_one]


set_option maxHeartbeats 800000 in
theorem exists_transv (hψ : IsStdChar D ψ (-1)) (hS : ∀ τ, (gramAt D S τ).PosDef) (h : IsoVec T ξ)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hx : row S T ξ (ratW T S x) ≠ 0) :
    ∃ e, IsSplitIdem D e ∧ ∃ z ∈ ZI T ξ, Formalism.L2.Theta.SuppAt e T z ∧ ∃ b, actO S T 1 z (ratW T S x) = along S T ξ b + ratW T S x ∧
      ψ (symplOH S T (along S T ξ b) (ratW T S x)) ≠ 1 := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨m, hm⟩ : ∃ m : Fin S.rank → D.host.E, ∀ j, row S T ξ (ratW T S x) j = incA D (m j) :=
    ⟨fun j => ∑ c, ∑ d, star (ξ c) * T.gram c d * x d j, fun j => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, RingHom.map_mul _ _ (x _ _)]
      rfl⟩
  have hm0 : m ≠ 0 := fun h0 => hx (funext fun j => by rw [hm, h0, Pi.zero_apply, RingHom.map_zero]; rfl)
  have hN := norm_ne_zero hS hm0
  have hNs : star (∑ i, ∑ j, S.gram⁻¹ i j * star (m j) * m i) = ∑ i, ∑ j, S.gram⁻¹ i j * star (m j) * m i := by
    simp only [star_sum, star_mul', star_star, gramInv_star]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hh : ∀ t : AE D, hO S T (along S T ξ (t • row S T ξ (ratW T S x))) (ratW T S x) =
      t * incA D (∑ i, ∑ j, S.gram⁻¹ i j * star (m j) * m i) := fun t => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hO_along, Pi.smul_apply, hm, GlobalTheory.DualPairCheck.cA_incA, map_sum, RingHom.map_mul, Finset.mul_sum, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  generalize ∑ i, ∑ j, S.gram⁻¹ i j * star (m j) * m i = N at hN hNs hh
  have hx0 := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  obtain ⟨q, hq⟩ := (D.sp.cm.fixed (D.host.xi0 * (D.host.xi0 * N))).1 (by
    rw [star_mul', star_mul', hx0, hNs, neg_mul, neg_mul, mul_neg, neg_neg])
  have hq0 : q ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hq
    exact mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) hN) hq.symm
  obtain ⟨v, hv⟩ := Formalism.L2.G.Triv.exists_place (F := D.host.F) 2 Nat.prime_two
  obtain ⟨e, e1, e2, e3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v (by exact_mod_cast hv)
  obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ v
  obtain ⟨s, hs1, hs2⟩ : ∃ s : AF D.host.F, pairA D.host.F 0 (singleV D.host.F v 1) * s = s ∧
      ψ (algebraMap D.host.F _ (1 / 2) * (s * algebraMap D.host.F _ (2 • q))) ≠ 1 :=
    ⟨GlobalTheory.SplitIdem.placeHom D.host.F v y * algebraMap D.host.F _ q⁻¹, (mul_assoc _ _ _).symm.trans (congrArg (· * _)
      (((GlobalTheory.SplitIdem.placeHom D.host.F v).map_mul' 1 y).symm.trans (congrArg _ (one_mul y)))),
      by rw [cancel_two _ hq0]; exact hy⟩
  obtain ⟨z, hz⟩ : ∃ z : GA D T, (matHom T z).1 = 1 + (s ⊗ₜ[D.host.F] D.host.xi0 : AE D) • (nilM T ξ).map (incA D) :=
    ⟨tv (AF D.host.F) D.sp.cm.sig (nilM_sq h) (nilM_adj T ξ) _ (skew_tmul _ _ hx0 s), rfl⟩
  refine ⟨e, ⟨e1, e2, v, _, ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ v 1,
    fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ v 1 hw⟩, e3⟩, z,
    Subgroup.subset_closure ⟨_, by rw [hz, add_sub_cancel_left]⟩, fun i j => ?_, _, actO_transv hz _, ?_⟩
  · rw [Formalism.L2.Theta.mt, hz, add_sub_cancel_left, e3, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    congr 1
    change (pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hs1]
  · rw [symplOH, symplO, hh, trace_three,
      ← hq, Algebra.trace_algebraMap, D.sp.cm.deg2]
    exact hs2

theorem heisO_at_zero (w : WO S T) (g : WO S T → ℂ) : heisO ψ S T w g 0 = g w := by
  have h : symplOH S T 0 w = 0 := by
    have := symplOH_add_left (S := S) (T := T) 0 0 w
    rw [add_zero] at this
    exact left_eq_add.1 this
  rw [heisO, h, ψ.map_zero_eq_one, one_mul, zero_add]

theorem heisO_rat {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T) :
    heisO ψ S T (ratW T S x) g w = ψ (symplO S T w (ratW T S x)) * g w := by
  rw [heisO, add_comm, hg.quasi, ← mul_assoc, ← ψ.map_add_eq_mul, symplOH, symplOH, symplO_skew w, mul_neg, neg_neg, ← add_mul,
    ← map_add, add_halves, map_one, one_mul]

theorem symplO_eq_add (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  rw [symplOH, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

def alongHom (S T : HSp D) (ξ : Fin T.rank → D.host.E) : (Fin S.rank → AE D) →+ WO S T :=
  AddMonoidHom.mk' (along S T ξ) along_add

theorem continuous_along : Continuous (along S T ξ) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact continuous_pi fun i => continuous_pi fun j => continuous_const.mul (continuous_apply j)

theorem along_injective (h : ξ ≠ 0) : Function.Injective (along S T ξ) := fun a b e => funext fun j => by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have h1 : incA D (ξ i) * a j = incA D (ξ i) * b j := congrFun (congrFun e i) j
  exact ((Ne.isUnit hi).map (incA D)).mul_left_cancel h1

theorem periodic (h : IsoVec T ξ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) {γ : Fin S.rank → AE D}
    (hγ : γ ∈ (ratL T S).comap (alongHom S T ξ)) (y : Fin S.rank → AE D) :
    g (along S T ξ (γ + y)) = g (along S T ξ y) := by
  obtain ⟨x, hx⟩ := hγ
  have hx' : ratW T S x = along S T ξ γ := hx
  have := hg.quasi x (along S T ξ y)
  rwa [hx', symplOH_along h, neg_zero, ψ.map_zero_eq_one, one_mul, ← along_add] at this

variable {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_along (hW : IsWeilDatumO ψ S T χS χT om) (h : IsoVec T ξ) {z : GA D T} (hz : z ∈ ZI T ξ) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) (a : Fin S.rank → AE D) :
    om (1, z) (heisO ψ S T (along S T ξ a) g) 0 = om (1, z) g (along S T ξ a) := by
  rw [hW.om_heis _ _ _ _ hg, actO_along h hz, heisO_at_zero]

theorem om_mul (z z' : GA D T) (g : WO S T → ℂ) : om (1, z * z') g = om (1, z) (om (1, z') g) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

theorem om_rat_along (hW : IsWeilDatumO ψ S T χS χT om) (h : IsoVec T ξ) {γ : GA D T} (hz : γ ∈ ZI T ξ) (hγ : γ ∈ GQ T)
    (z : GA D T) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (a : Fin S.rank → AE D) :
    om (1, γ * z) g (along S T ξ a) = om (1, z) g (along S T ξ a) := by
  have hg' := hW.om_pres (1, z) g hg
  rw [om_mul, ← om_along hW h hz hg', hW.om_aut 1 (one_mem _) γ hγ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hg' _),
    heisO_at_zero]

theorem exists_bound (hW : IsWeilDatumO ψ S T χS χT om) (h : IsoVec T ξ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ z : ZI T ξ, ∀ a, ‖om (1, (z : GA D T)) f (along S T ξ a)‖ ≤ C := by
  obtain ⟨θ, hθ⟩ := hW.std.2.1
  obtain ⟨⟨e, he⟩, -⟩ := transvection_group D θ T hθ ξ h
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F
  obtain ⟨C, hC⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hW f hf
    ((fun a => ((1 : GA D S), (e (Multiplicative.ofAdd a) : GA D T))) '' K)
    (hK.image (continuous_const.prodMk (continuous_subtype_val.comp (e.continuous.comp continuous_ofAdd))))
  refine ⟨C, fun z a => ?_⟩
  obtain ⟨s, rfl⟩ := e.surjective z
  obtain ⟨x, hx⟩ := hKx s.toAdd
  have e1 : e s = e (Multiplicative.ofAdd (algebraMap _ _ x)) * e (Multiplicative.ofAdd (s.toAdd - algebraMap _ _ x)) := by
    rw [← map_mul, ← ofAdd_add, add_sub_cancel, ofAdd_toAdd]
  rw [e1, Subgroup.coe_mul, om_rat_along hW h (SetLike.coe_mem _) ((he (Multiplicative.ofAdd (algebraMap _ _ x))).2 ⟨x, rfl⟩) _ hf]
  exact hC _ ⟨_, hx, rfl⟩ _

theorem exists_eigen (hW : IsWeilDatumO ψ S T χS χT om) (hS : ∀ τ, (gramAt D S τ).PosDef) (h : IsoVec T ξ)
    (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) (hℓ : ∀ a f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (along S T ξ a) f) = ℓ f)
    (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hx : row S T ξ (ratW T S x) ≠ 0) :
    ∃ z ∈ ZI T ξ, ∃ c : ℂ, c ≠ 1 ∧ ∀ g, IsThetaFunO ψ S T g →
      ℓ (heisO ψ S T (ratW T S x) (om (1, z) g)) = c * ℓ (heisO ψ S T (ratW T S x) g) := by
  obtain ⟨e, he, z, hz, hs, b, hb, hu⟩ := exists_transv hW.std hS h x hx
  obtain ⟨r, hr, H⟩ := GlobalTheory.T.splitPlaceTransvection_acts_positively_invariant_forms D ψ S T χS χT om hW ξ h e he z hz hs
  refine ⟨z, hz, ψ (symplOH S T (along S T ξ b) (ratW T S x)) * r, fun h1 => hu ?_, fun g hg => ?_⟩
  · have h2 := congrArg norm h1
    rw [norm_mul, hW.std.1.2.1, one_mul, norm_one, Complex.norm_real, Real.norm_of_nonneg hr.le] at h2
    rwa [h2, Complex.ofReal_one, mul_one] at h1
  · rw [mul_assoc, ← H ℓ hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hg _), hW.om_heis _ _ _ _ hg, hb,
      ← hℓ b _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std (hW.om_pres _ _ hg) _), heisO_heisO, map_smul, smul_eq_mul]


set_option maxHeartbeats 800000 in
theorem constantTerm_heisO_along : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ ξ, IsoVec T ξ → ∀ (μ : Measure (ZI T ξ)) (𝓕 : Set (ZI T ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ T).subgroupOf (ZI T ξ)) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∀ a, ∫ z in 𝓕, om (1, (z : GA D T)) (heisO ψ S T (along S T ξ a) f) 0 ∂μ = ∫ z in 𝓕, om (1, (z : GA D T)) f 0 ∂μ := by
  intro D ψ S T χS χT om hW hS ξ h μ 𝓕 hμ h𝓕 f hf a
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have : IsTopologicalGroup (GA D T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : Countable (GQ T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig T.gram
  have : BorelSpace (ZI T ξ) := Subtype.borelSpace (fun x => x ∈ (ZI T ξ : Set (GA D T)))
  have : Countable ((GQ T).subgroupOf (ZI T ξ)) :=
    Function.Injective.countable (f := fun γ : (GQ T).subgroupOf (ZI T ξ) => (⟨γ.1.1, γ.2⟩ : GQ T))
      fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ T => (x : GA D T)) h))
  obtain ⟨⟨ε, -⟩, -⟩ := transvection_group D θ T hθ ξ h
  have hfin := ((GlobalTheory.TransvMeasure.transvection_measure D θ T hθ ξ h).2.1 μ 𝓕 hμ h𝓕).2
  have hc : ∀ a b : ZI T ξ, a * b = b * a := fun a b => by
    obtain ⟨a, rfl⟩ := ε.surjective a
    obtain ⟨b, rfl⟩ := ε.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  have : LocallyCompactSpace (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : LocallyCompactSpace (AE D) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AE D) := e.secondCountableTopology
  have : T2Space (AE D) := e.isEmbedding.t2Space
  letI : MeasurableSpace (Fin S.rank → AE D) := borel _
  have : BorelSpace (Fin S.rank → AE D) := ⟨rfl⟩
  let Γ := (ratL T S).comap (alongHom S T ξ)
  have : DiscreteTopology (ratL T S) := (GlobalTheory.AdelicMatrixLattice.lattice D T S).2.2.2.2.1
  have : DiscreteTopology Γ := DiscreteTopology.of_continuous_injective (β := ratL T S) (f := fun γ => ⟨along S T ξ γ.1, γ.2⟩)
    ((continuous_along.comp continuous_subtype_val).subtype_mk _)
    fun a b e => Subtype.ext (along_injective h.1 (congrArg Subtype.val e))
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := D.host.F) (E := D.host.E) (AF D.host.F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F)
  choose c hcK using hx
  have hK' : IsCompact (Set.univ.pi fun _ : Fin S.rank => K) := isCompact_univ_pi fun _ => hK
  have hcov : ∀ y : Fin S.rank → AE D, ∃ γ ∈ Γ, γ + y ∈ Set.univ.pi fun _ : Fin S.rank => K := fun y =>
    ⟨fun j => incA D (c (y j)), ⟨vecMulVec ξ fun j => c (y j), Matrix.ext fun _ _ => RingHom.map_mul (incA D) _ _⟩,
      fun j _ => hcK (y j)⟩
  have : Countable Γ := GlobalTheory.countable_of_discrete_addSubgroup Γ
  obtain ⟨G, -, -, hG⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup Γ
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Fin S.rank → AE D), ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have : IsFiniteMeasure (ν.restrict G) :=
    isFiniteMeasure_restrict.2 (measure_addFundamentalDomain_lt_top_of_cocompact Γ hK' hcov ν (hG ν)).ne
  have hint : ∀ g, IsThetaFunO ψ S T g → Integrable (fun y => g (along S T ξ y)) (ν.restrict G) := fun g hg => by
    obtain ⟨B, hB⟩ := theta_bounded hψ hg
    exact Integrable.of_bound (hg.cont.comp continuous_along).aestronglyMeasurable B (.of_forall fun _ => hB _)
  let N : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := theta_add
      zero_mem' := theta_zero
      smul_mem' := fun a _ hg => theta_smul a hg }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend (p := N) (V' := ℂ)
    { toFun := fun g => ∫ y in G, g.1 (along S T ξ y) ∂ν
      map_add' := fun p q => integral_add (hint _ p.2) (hint _ q.2)
      map_smul' := fun c p => integral_smul c fun y => p.1 (along S T ξ y) }
  replace hℓ : ∀ g, IsThetaFunO ψ S T g → ℓ g = ∫ y in G, g (along S T ξ y) ∂ν := fun g hg =>
    LinearMap.congr_fun hℓ ⟨g, hg⟩
  have hinv : ∀ b g, IsThetaFunO ψ S T g → ℓ (heisO ψ S T (along S T ξ b) g) = ℓ g := fun b g hg => by
    rw [hℓ _ hg, hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg _),
      ← GlobalTheory.AverageConst.setIntegral_add_left add_comm Γ ν (hG ν) (fun y => g (along S T ξ y))
        (fun γ hγ y => periodic h hg hγ y) b]
    refine integral_congr_ae (.of_forall fun y => ?_)
    change ψ (symplOH S T (along S T ξ y) (along S T ξ b)) * g (along S T ξ y + along S T ξ b) = g (along S T ξ (b + y))
    rw [symplOH_along h, ψ.map_zero_eq_one, one_mul, ← along_add, add_comm y]
  obtain ⟨C, hC⟩ := exists_bound hW h hf
  have key := GlobalTheory.AverageConst.average_const Γ hK' hcov
    (fun (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) y => ψ (symplO S T (along S T ξ y) (ratW T S x)))
    (fun x => by
      simp only [symplO_eq_add]
      exact hψ.1.1.comp ((continuous_symplOH continuous_along continuous_const).add
        (continuous_symplOH continuous_along continuous_const)))
    (fun x y y' => by rw [← ψ.map_add_eq_mul, along_add, symplO_eq_add, symplO_eq_add, symplO_eq_add, symplOH_add_left, add_add_add_comm])
    (fun x x' y => by
      rw [← ψ.map_add_eq_mul, show ratW T S (x + x') = ratW T S x + ratW T S x' from Matrix.map_add _ (incA D).map_add _ _,
        symplO_eq_add, symplO_eq_add, symplO_eq_add, symplOH_add_right, add_add_add_comm])
    (fun y => by
      rw [symplO_along (funext fun j => by simp [row, ratW]), ψ.map_zero_eq_one])
    (fun _ _ => hψ.1.2.1 _)
    (fun y => (Iff.intro (fun H _ ⟨x, e⟩ => e ▸ H x) fun H x => H _ ⟨x, rfl⟩).trans
      (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T _))
    ν (hG ν) hc _ μ h𝓕 hfin (fun z y => om (1, (z : GA D T)) f (along S T ξ y))
    (fun y => (hW.om_cont f hf _).comp (continuous_const.prodMk continuous_subtype_val))
    (fun z => (hW.om_pres _ f hf).cont.comp continuous_along) hC
    (fun γ hγ z y => om_rat_along hW h γ.2 hγ _ hf y)
    (fun γ hγ z y => periodic h (hW.om_pres _ f hf) hγ y)
    (fun x => by
      by_cases hx : row S T ξ (ratW T S x) = 0
      · exact Or.inl fun y => by rw [symplO_along hx, ψ.map_zero_eq_one]
      obtain ⟨z₁, hz, c, hc1, H⟩ := exists_eigen hW hS h ℓ hinv x hx
      refine Or.inr ⟨⟨z₁, hz⟩, c, hc1, fun z => ?_⟩
      have h1 := hW.om_pres (1, (z : GA D T)) f hf
      have h2 := hW.om_pres (1, z₁) _ h1
      have := H _ h1
      rw [hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ h1 _), hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ h2 _)] at this
      simpa only [heisO_rat h1, heisO_rat h2, Subgroup.coe_mul, om_mul] using this) a
  simp only [along_zero] at key
  rw [← key]
  exact integral_congr_ae (.of_forall fun z => om_along hW h z.2 hf a)

end GlobalTheory.TransvConst

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantTermHeisOAlongStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_om_heisO_along_eq_integral_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ ξ, IsoVec T ξ → ∀ (μ : Measure (ZI T ξ)) (𝓕 : Set (ZI T ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ T).subgroupOf (ZI T ξ)) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∀ a, ∫ z in 𝓕, om (1, (z : GA D T)) (heisO ψ S T (along S T ξ a) f) 0 ∂μ = ∫ z in 𝓕, om (1, (z : GA D T)) f 0 ∂μ := by
  first | exact @GlobalTheory.TransvConst.constantTerm_heisO_along | exact GlobalTheory.TransvConst.constantTerm_heisO_along | (intros; apply GlobalTheory.TransvConst.constantTerm_heisO_along <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftDefiniteConstantTermEqZero
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLiftCusp

theorem exists_bound {Z H : Type} [Group Z] [TopologicalSpace Z] [MeasurableSpace Z] [Group H] [TopologicalSpace H]
    (Γ : Subgroup Z) (Δ : Subgroup H) (μ : Measure Z) [μ.IsOpenPosMeasure] (𝓕 : Set Z)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hc : IsCompact (closure 𝓕)) (C : Set H) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Δ, ∃ c ∈ C, h = γ * c) (K : Z × H → ℂ) (hK : Continuous K)
    (hinv : ∀ γ ∈ Γ, ∀ δ ∈ Δ, ∀ z h, K (γ * z, δ * h) = K (z, h)) : ∃ B : ℝ, ∀ p, ‖K p‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hc.prod hC).exists_bound_of_continuousOn hK.continuousOn
  refine ⟨B, fun ⟨z, h⟩ => ?_⟩
  obtain ⟨δ, hδ, c, hcC, rfl⟩ := hcov h
  have hae : ∀ᵐ z ∂μ, ‖K (z, δ * c)‖ ≤ B := by
    filter_upwards [h𝓕.ae_covers] with z hz
    obtain ⟨γ, hγ⟩ := hz
    have := hinv γ⁻¹ (inv_mem γ.2) δ hδ (γ * z) c
    rw [inv_mul_cancel_left] at this
    rw [this]
    exact hB _ ⟨subset_closure hγ, hcC⟩
  have hcl : IsClosed {z : Z | ‖K (z, δ * c)‖ ≤ B} :=
    isClosed_le (hK.comp (Continuous.prodMk_left _)).norm continuous_const
  exact hcl.closure_subset (μ.dense_of_ae hae z)

theorem swap_of_bound {Z H : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Z) (ν : Measure H) (A : Set Z) (B : Set H) (hA : μ A ≠ ⊤) (hB : ν B ≠ ⊤)
    (K : Z × H → ℂ) (hK : Continuous K) (c : ℝ) (hc : ∀ p, ‖K p‖ ≤ c) :
    ∫ z in A, ∫ h in B, K (z, h) ∂ν ∂μ = ∫ h in B, ∫ z in A, K (z, h) ∂μ ∂ν := by
  haveI : IsFiniteMeasure (μ.restrict A) := ⟨by rw [Measure.restrict_apply_univ]; exact hA.lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hB.lt_top⟩
  exact integral_integral_swap (f := fun z h => K (z, h))
    (Integrable.of_bound hK.aestronglyMeasurable c (Filter.Eventually.of_forall hc))

theorem continuous_family {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (H : IsWeilDatumO ψ S T χS χT om)
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ))
    (hL : ∀ x, IsThetaFunO ψ S T (L x)) :
    Continuous fun q : (GA D S × GA D T) × X => om q.1 (L q.2) 0 := by
  let b := Module.finBasis ℂ X
  have e : (fun q : (GA D S × GA D T) × X => om q.1 (L q.2) 0) =
      fun q => ∑ i, b.coord i q.2 * om q.1 (L (b i)) 0 := by
    funext q
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr q.2, map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul]
    rfl
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((b.coord i).continuous_of_finiteDimensional.comp continuous_snd).mul
      ((H.om_cont _ (hL _) 0).comp continuous_fst)

theorem zcusp_lift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (∀ x h g ξ, IsoVec T ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin S.rank → AE D, ∑ k, heisO ψ S T (along S T ξ (a k)) (om (h, g) (L x)) = 0) → ZCusp T (lift om ν 𝓕 fun h => L (F h)) := by
  intro D ψ S T χS χT om H hpos X _ _ _ L hL F hF hFinv ν 𝓕 hν h𝓕 hav ξ hξ μ 𝓖 hμ h𝓖 g
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig S.gram
  have i1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig T.gram
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable S
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable T
  have : BorelSpace (ZI T ξ) := Subtype.borelSpace _
  have : SecondCountableTopology (ZI T ξ) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨⟨μ₀, 𝓖₀, hμ₀, h𝓖₀, hc₀⟩, hfin, -⟩ := GlobalTheory.TransvMeasure.transvection_measure D θ T hθ ξ hξ
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  have hG : μ 𝓖 ≠ ⊤ := (hfin μ 𝓖 hμ h𝓖).2
  have hN : ν 𝓕 ≠ ⊤ := GlobalTheory.TransvMeasure.measure_ne_top_of_cocompact (GQ S) hC (fun x => by
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩) ν h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ]; exact hG.lt_top⟩

  have hint : ∀ f, IsThetaFunO ψ S T f →
      Integrable (fun z : ZI T ξ => om (1, (z : GA D T)) f 0) (μ.restrict 𝓖) := by
    intro f hf
    obtain ⟨hc, hi⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om H f hf
    have hK : Continuous fun p : ZI T ξ × GA D S => thetaKO om p.2 (p.1 : GA D T) f :=
      hc.comp (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
    obtain ⟨B, hB⟩ := exists_bound _ (GQ S) μ₀ 𝓖₀ h𝓖₀ hc₀ C hC hcov _ hK
      fun γ hγ δ hδ z h => hi δ hδ γ hγ h z
    exact Integrable.of_bound (hK.comp (Continuous.prodMk_left 1)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => hB (z, 1))

  have hin : ∀ h x, ∫ z in 𝓖, thetaKO om h ((z : GA D T) * g) (L x) ∂μ = 0 := by
    intro h x
    have hf : IsThetaFunO ψ S T (om (h, g) (L x)) := H.om_pres _ _ (hL x)
    have e : ∀ z : ZI T ξ, thetaKO om h ((z : GA D T) * g) (L x) = om (1, (z : GA D T)) (om (h, g) (L x)) 0 := by
      intro z
      have h1 : om (h, (z : GA D T) * g) = om (1, (z : GA D T)) * om (h, g) := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      unfold thetaKO
      rw [h1]
      rfl
    simp only [e]
    obtain ⟨n, hn, a, ha⟩ := hav x h g ξ hξ
    have h1 := integral_finsetSum (μ := μ.restrict 𝓖) Finset.univ
      (fun (k : Fin n) _ => hint _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all H.std hf (along S T ξ (a k))))
    have h2 : ∀ z : ZI T ξ,
        ∑ k, om (1, (z : GA D T)) (heisO ψ S T (along S T ξ (a k)) (om (h, g) (L x))) 0 = 0 := by
      intro z
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Finset.sum_apply, ← map_sum, ha, map_zero]
      rfl
    simp only [h2, GlobalTheory.T.integral_om_heisO_along_eq_integral_om D ψ S T χS χT om H hpos ξ hξ μ 𝓖 hμ h𝓖 _ hf, integral_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hn.ne')
  have hK : Continuous fun p : ZI T ξ × GA D S => thetaKO om p.2 ((p.1 : GA D T) * g) (L (F p.2)) :=
    (continuous_family H L hL).comp
      ((continuous_snd.prodMk ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).prodMk
        (hF.comp continuous_snd))
  obtain ⟨B, hB⟩ := exists_bound _ (GQ S) μ₀ 𝓖₀ h𝓖₀ hc₀ C hC hcov _ hK fun γ hγ δ hδ z h => by
    have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om H _ (hL (F h))).2 δ hδ γ hγ h (z * g)
    rw [← this, ← mul_assoc]
    simp only [hFinv δ hδ]
    rfl
  have key := swap_of_bound μ ν 𝓖 𝓕 hG hN _ hK B hB
  simp only [hin, integral_zero] at key
  exact key

end GlobalTheory.DefLiftCusp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftDefiniteConstantTermEqZeroStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_definite_constantTerm_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (∀ x h g ξ, IsoVec T ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin S.rank → AE D, ∑ k, heisO ψ S T (along S T ξ (a k)) (om (h, g) (L x)) = 0) → ZCusp T (lift om ν 𝓕 fun h => L (F h)) := by
  first | exact @GlobalTheory.DefLiftCusp.zcusp_lift | exact GlobalTheory.DefLiftCusp.zcusp_lift | (intros; apply GlobalTheory.DefLiftCusp.zcusp_lift <;> assumption)
end
