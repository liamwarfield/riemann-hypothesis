module

public import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.LatticeBasics.ConstIdele

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
noncomputable section

namespace GlobalTheory.ThK.Dbl.St

open PositivityTheory.ThKG.Tow

open scoped TensorProduct Matrix Pointwise RestrictedProduct
open NumberField IsDedekindDomain Topology Filter GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem isCompact_of_units {A : Type} [Monoid A] [TopologicalSpace A] [ContinuousMul A] [T2Space A]
    (H : Subgroup Aˣ) (hH : IsClosed (H : Set Aˣ)) (K : Set H) (hK : IsClosed K) (S : Set A) (hS : IsCompact S)
    (h : ∀ k ∈ K, (k.1 : A) ∈ S ∧ ((k⁻¹).1 : A) ∈ S) : IsCompact K := by
  have e : IsClosedEmbedding (fun k : H => Units.embedProduct A k.1) :=
    Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
  have hc : IsCompact (S ×ˢ (MulOpposite.op '' S)) := hS.prod (hS.image MulOpposite.continuous_op)
  exact (e.isCompact_preimage hc).of_isClosed_subset hK fun k hk => ⟨(h k hk).1, _, (h k hk).2, rfl⟩

theorem cartan_bound {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) :
    ∃ R : ℝ, ∀ A : Matrix (Fin n) (Fin n) ℂ, Aᵀ * M * A.map star = M → Commute A θ → ∀ i j, ‖A i j‖ ≤ R := by
  let Q : (Fin n → ℂ) → ℝ := fun x => ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x).re
  have hQ : Continuous Q := Complex.continuous_re.comp
    ((continuous_const.matrix_mulVec continuous_id).dotProduct (continuous_const.matrix_mulVec continuous_star))
  have hom : ∀ (t : ℝ) x, Q (t • x) = t ^ 2 * Q x := fun t x => by
    simp only [Q, star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, Complex.smul_re,
      smul_eq_mul]
    ring
  obtain ⟨c, hc, hle⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_forall_le' hQ.continuousOn (a := 0)
    fun x hx => h.2.2 x (by rintro rfl; simp at hx)
  have low : ∀ x, c * ‖x‖ ^ 2 ≤ Q x := fun x => by
    by_cases hx : x = 0
    · subst hx; simp [Q]
    · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have h1 := hle (‖x‖⁻¹ • x) (by simp [norm_smul, hn.ne'])
      have h2 : Q x = ‖x‖ ^ 2 * Q (‖x‖⁻¹ • x) := by rw [← hom, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [h2, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  refine ⟨∑ j, √(Q (Pi.single j 1) / c), fun A hA hc' i j => ?_⟩
  have inv : ∀ x, Q (A *ᵥ x) = Q x := fun x => by
    have e1 : star (A *ᵥ x) = A.map star *ᵥ star x := by
      ext k; simp [Matrix.mulVec, dotProduct]
    have e2 : θ *ᵥ A *ᵥ x = A *ᵥ θ *ᵥ x := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc'.eq]
    have e3 : (A *ᵥ θ *ᵥ x) ⬝ᵥ M *ᵥ A.map star *ᵥ star x = (θ *ᵥ x) ⬝ᵥ (Aᵀ * M * A.map star) *ᵥ star x := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (θ *ᵥ x) Aᵀ,
        Matrix.vecMul_transpose]
    simp only [Q]
    rw [e1, e2, e3, hA]
  have h1 : ‖A i j‖ ≤ ‖A *ᵥ Pi.single j 1‖ := by
    have := norm_le_pi_norm (A *ᵥ Pi.single j 1) i
    rwa [Matrix.mulVec_single_one] at this ⊢
  have h2 : ‖A *ᵥ Pi.single j 1‖ ≤ √(Q (Pi.single j 1) / c) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hc, mul_comm, ← inv]
    exact low _
  exact h1.trans (h2.trans (Finset.single_le_sum (f := fun j => √(Q (Pi.single j 1) / c))
    (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ j)))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem ae_ring : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem ae_t2 : T2Space (AE F E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact e.isEmbedding.t2Space

theorem ae_smul : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) _

attribute [local instance] ae_ring ae_t2 ae_smul

theorem evI_eq_zero {a : AF F} : evI F a = 0 ↔ a.1 = 0 := map_eq_zero_iff _ (RingEquiv.injective _)


variable (F) in
def intF : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨evI_eq_zero.2 rfl, fun v => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨evI_eq_zero.2 (by
      change a.1 + b.1 = 0
      rw [evI_eq_zero.1 ha.1, evI_eq_zero.1 hb.1, add_zero]),
    fun v => by
      rw [map_add (evFin F v)]
      exact add_mem (ha.2 v) (hb.2 v)⟩
  neg_mem' := fun {a} ha => ⟨evI_eq_zero.2 (by
      change -a.1 = 0
      rw [evI_eq_zero.1 ha.1, neg_zero]),
    fun v => by rw [map_neg]; exact neg_mem (ha.2 v)⟩

theorem isCompact_intF : IsCompact (intF F : Set (AF F)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  let s : (∀ v : Pl F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))) → Af F :=
    RestrictedProduct.structureMap (fun v : Pl F => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  haveI : ∀ v : Pl F, CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := this
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  have hc : Continuous fun x => pairA F 0 (s x) := continuous_const.prodMk hs
  convert isCompact_range hc using 1
  ext a
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ⟨_, h2 v⟩, Prod.ext (evI_eq_zero.1 h1).symm ?_⟩
    exact RestrictedProduct.ext _ _ fun v => rfl
  · rintro ⟨x, rfl⟩
    exact ⟨evI_eq_zero.2 rfl, fun v => (x v).2⟩

theorem mem_latHat (X : Spc F E n) {a : AF F} (ha : a ∈ intF F) {y : Fin n → E} (hy : y ∈ X.L) :
    a • incV F y ∈ latHat X :=
  AddSubgroup.subset_closure ⟨a, ha.1, ha.2, y, hy, rfl⟩

theorem isCompact_latHat (X : Spc F E n) (hX : X.L.FG) : IsCompact (latHat X : Set (Fin n → AE F E)) := by
  have hZ : (X.L.restrictScalars ℤ).FG := hX.restrictScalars
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have hsL : ∀ j, s j ∈ X.L := fun j => by
    have : s j ∈ X.L.restrictScalars ℤ := hs ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  haveI : CompactSpace (intF F) := isCompact_iff_compactSpace.1 isCompact_intF
  let f : (Fin m → intF F) →+ (Fin n → AE F E) :=
    AddMonoidHom.mk' (fun a => ∑ j, (a j : AF F) • incV F (s j)) fun a b => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : ((a + b) j : AF F) = a j + b j := rfl
      rw [this, add_smul]
  have hf : Continuous f := by
    change Continuous fun a : Fin m → intF F => ∑ j, (a j : AF F) • incV F (s j)
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun a : Fin m → intF F => (a j : AF F) := Continuous.subtype_val (continuous_apply j)
    exact h1.fun_smul continuous_const
  have e : latHat X = f.range := by
    refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
    · rintro _ ⟨a, ha, ha', y, hy, rfl⟩
      have hy' : y ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
      refine ⟨fun j => c j • ⟨a, ha, ha'⟩, funext fun i => ?_⟩
      change (∑ j, (c j • a) • incV F (s j)) i = a • inclR (F := F) (AF F) ((∑ j, c j • s j) i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      change (c j • a) • inclR (F := F) (AF F) (s j i) = _
      rw [Pi.smul_apply, map_zsmul, smul_assoc, smul_comm]
    · rintro _ ⟨a, rfl⟩
      change (∑ j, (a j : AF F) • incV F (s j)) ∈ latHat X
      exact sum_mem fun j _ => mem_latHat X (a j).2 (hsL j)
  rw [e, AddMonoidHom.coe_range]
  exact isCompact_range hf


variable (F) in
def eF : AF F := pairA F 0 1

theorem eF_mem : eF F ∈ intF F := ⟨evI_eq_zero.2 rfl, fun v => by
  have : evFin F v (eF F) = 1 := map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
  rw [this]; exact one_mem _⟩

theorem vec_bound (X : Spc F E n) (hX : X.L.IsFullLattice E) (x : Fin n → E) :
    ∃ C : Set (Fin n → AE F E), IsCompact C ∧ ∀ M : Matrix (Fin n) (Fin n) (AE F E),
      (∀ y ∈ latHat X, M *ᵥ y ∈ latHat X) → M *ᵥ (eF F • incV F x) ∈ C := by
  have hx : x ∈ Submodule.span E (X.L : Set (Fin n → E)) := by
    rw [hX.span_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨_, isCompact_latHat X hX.fg, fun M hM => hM _ (mem_latHat X eF_mem hy)⟩
  | zero =>
    refine ⟨{0}, isCompact_singleton, fun M _ => ?_⟩
    have : incV F (0 : Fin n → E) = 0 := funext fun i => map_zero (inclR (F := F) (AF F))
    rw [this, smul_zero, Matrix.mulVec_zero]; rfl
  | add y z _ _ hy hz =>
    obtain ⟨C, hC, h⟩ := hy
    obtain ⟨C', hC', h'⟩ := hz
    refine ⟨C + C', hC.add hC', fun M hM => ?_⟩
    have : incV F (y + z) = incV F y + incV F z := funext fun i => map_add (inclR (F := F) (AF F)) _ _
    rw [this, smul_add, Matrix.mulVec_add]
    exact Set.add_mem_add (h M hM) (h' M hM)
  | smul c y _ hy =>
    obtain ⟨C, hC, h⟩ := hy
    refine ⟨(fun z => inclR (F := F) (AF F) c • z) '' C, hC.image (continuous_const_smul _), fun M hM => ⟨_, h M hM, ?_⟩⟩
    have : eF F • incV F (c • y) = inclR (F := F) (AF F) c • eF F • incV F y :=
      funext fun i => by
        change eF F • inclR (F := F) (AF F) (c * y i) = inclR (F := F) (AF F) c * (eF F • inclR (F := F) (AF F) (y i))
        rw [map_mul, mul_smul_comm]
    rw [this]
    exact (Matrix.mulVec_smul _ _ _).symm

theorem fin_bound (X : Spc F E n) (hX : X.L.IsFullLattice E) (i j : Fin n) :
    ∃ C : Set (AE F E), IsCompact C ∧ ∀ M : Matrix (Fin n) (Fin n) (AE F E),
      (∀ y ∈ latHat X, M *ᵥ y ∈ latHat X) → eF F • M i j ∈ C := by
  obtain ⟨C, hC, h⟩ := vec_bound X hX (Pi.single j 1)
  refine ⟨(fun z => z i) '' C, hC.image (continuous_apply i), fun M hM => ⟨_, h M hM, ?_⟩⟩
  have : incV F (Pi.single j 1 : Fin n → E) = Pi.single j 1 := funext fun k => by
    by_cases hk : k = j
    · subst hk; simp [incV]
    · simp [incV, hk]
  rw [this, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  rfl

omit [NumberField E] in
theorem piInf_smul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (z : AE F E) :
    piInf τ (a • z) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * piInf τ z := by
  have : piInf τ (algebraMap (AF F) (AE F E) a) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    change InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 1 = _
    rw [map_one, mul_one]
  rw [Algebra.smul_def, map_mul, this]

omit [NumberField E] in
theorem compFin_smul (v : Pl F) {a : AF F} (ha : a.2 = 0) (z : AE F E) : compFin F E v (a • z) = 0 := by
  have : compFin F E v (algebraMap (AF F) (AE F E) a) = 0 := by
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a.2 ⊗ₜ[F] (1 : E) = 0
    rw [ha, map_zero, TensorProduct.zero_tmul]
  rw [Algebra.smul_def, map_mul, this, zero_mul]

theorem exists_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ Φ : (InfinitePlace F → ℂ) → AE F E, Continuous Φ ∧ ∀ z, z = Φ (fun w => piInf (τ w) z) + eF F • z := by
  haveI := h.1
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  let ρ : (InfinitePlace F → ℝ) → AF F := fun t =>
    pairA F (fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm (t w)) 0
  have hρ : Continuous ρ := by
    have : Continuous fun (t : InfinitePlace F → ℝ) (w : InfinitePlace F) =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm (t w) :=
      continuous_pi fun w => (IsometryEquiv.continuous _).comp (continuous_apply w)
    exact this.prodMk continuous_const
  have eρ : ∀ t w, InfinitePlace.Completion.extensionEmbedding w ((ρ t).1 w) = t w := fun t w => by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hr w)]
    exact congrArg _ ((InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).apply_symm_apply (t w))
  obtain ⟨a, ha, -⟩ := Levi.exists_inf h τ fun _ => Complex.I
  refine ⟨fun z => ρ (fun w => (z w).re) • 1 + ρ (fun w => (z w).im) • a, ?_, fun z => ?_⟩
  · have h1 : Continuous fun z : InfinitePlace F → ℂ => ρ fun w => (z w).re :=
      hρ.comp (continuous_pi fun w => Complex.continuous_re.comp (continuous_apply w))
    have h2 : Continuous fun z : InfinitePlace F → ℂ => ρ fun w => (z w).im :=
      hρ.comp (continuous_pi fun w => Complex.continuous_im.comp (continuous_apply w))
    have h3 : ∀ b : AE F E, Continuous fun x : AF F => x • b := fun b =>
      Continuous.fun_smul (f := fun x : AF F => x) (g := fun _ => b) continuous_id' continuous_const
    exact Continuous.fun_add (f := fun z : InfinitePlace F → ℂ => ρ (fun w => (z w).re) • (1 : AE F E))
      (g := fun z => ρ (fun w => (z w).im) • a) ((h3 1).comp' h1) ((h3 a).comp' h2)
  · refine Levi.ad_ext h τ (fun w => ?_) fun v => ?_
    · have e0 : (eF F).1 w = 0 := rfl
      rw [map_add (f := _), map_add (f := _), piInf_smul, piInf_smul, piInf_smul, eρ, eρ, ha, e0, map_zero, map_one, zero_mul, mul_one,
        add_zero, Complex.re_add_im]
    · have e0 : compFin F E v ((1 - eF F) • z) = 0 := compFin_smul v (sub_self (1 : Af F)) z
      rw [sub_smul, one_smul, map_sub, sub_eq_zero] at e0
      rw [map_add (f := _), map_add (f := _), compFin_smul v rfl, compFin_smul v rfl, zero_add, zero_add, e0]

end GlobalTheory.ThK.Dbl.St

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.ConstOfGood
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DeterminantProjection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem det_ne_zero_of_sig {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := fun z => by
  obtain ⟨e, A, hA⟩ := h
  let q : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr e)
  have := congrArg Matrix.det (show (Aᵀ.submatrix id q * M.submatrix q q) * (A.map star).submatrix q id = Matrix.fromBlocks 1 0 0 (-1) by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]; exact hA)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, z, mul_zero, zero_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) this.symm

omit [NumberField E] in
theorem hermND_transpose {B : Base F E} {X : Spc F E n} {r s : ℕ} (h : X.IsHerm σ B r s) : IsHermND σ X.Jᵀ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨fun i j => h.herm j i, fun z => det_ne_zero_of_sig (h.sig w) ?_⟩
  rw [Matrix.det_transpose] at z
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, z, map_zero]

omit [NumberField E] in
theorem mem_UG_of {J : Matrix (Fin n) (Fin n) E} {g : GL (Fin n) (AE F E)} :
    g ∈ UG (cA σ) (incM F J) ↔ g ∈ HR (AF F) σ Jᵀ := by
  change (g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J) ↔ (g.1.map (sigR (AF F) σ))ᵀ * (incM F J)ᵀ * g.1 = (incM F J)ᵀ
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    show (cA σ : AE F E → AE F E) = sigR (AF F) σ from funext cA_eq]

def sec {A : Type} [CommRing A] (R : Matrix (Fin n) (Fin n) A) (h : R * R = R) : A →* Matrix (Fin n) (Fin n) A where
  toFun z := 1 + (z - 1) • R
  map_one' := by simp
  map_mul' a b := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul, add_assoc, ← add_smul]
    congr 2
    ring

theorem su_mem (hS : GlobalTheory.Published.StrongApproxSU) (hc : IsCMExt F E σ) {X : Spc F E n} (hJ : IsHermND σ X.Jᵀ) (hn : 2 ≤ n)
    (L : Subgroup (UA σ X.J)) (hL : IsClosed (L : Set (UA σ X.J))) (hr : ratU σ X.J ≤ L) {v : Pl F}
    (hv : ∀ u ∈ UAt σ X (evFin F v), u ∈ L) {ε : AF F} {e : AE F E} (hε : GlobalTheory.Published.IsPlacesIdem ∅ {v} ε) (e1 : e * e = e)
    (e2 : e * sigR (AF F) σ e = 0) (e3 : e + sigR (AF F) σ e = algebraMap (AF F) (AE F E) ε) (g : UA σ X.J)
    (hg : (mat g).det = 1) : g ∈ L := by
  let ι : HA (AF F) σ X.Jᵀ → UA σ X.J := fun x => ⟨HA.mat _ _ _ x, mem_UG_of.2 (show HR (AF F) σ X.Jᵀ from x).2⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have z : ∀ t, evFin F v t = 0 → t * ε = 0 := fun t ht => by
    refine Prod.ext (funext fun w => (congrArg (t.1 w * ·) (hε.2.1 w (Finset.notMem_empty w))).trans (mul_zero _))
      (FiniteAdeleRing.ext _ fun u => ?_)
    by_cases hu : u = v
    · subst hu
      exact (congrArg (· * ε.2 u) ht).trans (zero_mul _)
    · exact (congrArg (t.2 u * ·) (hε.2.2.2 u fun x => hu (Finset.mem_singleton.1 x))).trans (mul_zero _)
  refine closure_minimal (t := ι ⁻¹' L) ?_ (hL.preimage hι) (hS F E σ hc n _ hn hJ ∅ {v} ε hε
    (GlobalTheory.Published.StrongApprox.not_isCompact_split σ hn hJ v ε (hε.2.2.1 v (Finset.mem_singleton_self v)) e e1 e2 e3)
    (⟨g.1, mem_UG_of.1 g.2⟩ : HR (AF F) σ X.Jᵀ) (GlobalTheory.Published.StrongApprox.mem_SUAdelic.2 hg))
  rintro _ ⟨γ, ⟨-, y, -, hy⟩, h, ⟨-, hh⟩, rfl⟩
  have h1 : ι γ ∈ L := hr ⟨y, hy⟩
  have h2 : ι h ∈ L := hv _ fun t ht => Matrix.ext fun i j => by
    refine (congrArg (t • ·) (hh i j).symm).trans ?_
    rw [← Algebra.smul_def, smul_smul, z t ht, zero_smul, Matrix.zero_apply]
  exact mul_mem h1 h2

theorem exists_sec (hc : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ Jᵀ) (hn : 1 ≤ n) :
    ∃ S : normOne (cA σ) →* UA σ J, Continuous S ∧ (∀ z, (mat (S z)).det = (z.1 : (AE F E)ˣ)) ∧
      (∀ z : normOne (cA σ), (∃ k : E, k ≠ 0 ∧ ((z.1 : (AE F E)ˣ) : AE F E) = inclR (F := F) (AF F) k) → S z ∈ ratU σ J) ∧
      ∀ (z : normOne (cA σ)) (t : AF F), t • (((z.1 : (AE F E)ˣ) : AE F E) - 1) = 0 → t • (mat (S z) - 1) = 0 := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hσ := GlobalTheory.UnitaryHeckeBaseChange.sig_sig hc
  obtain ⟨u, hu⟩ := exists_aniso (σ : E →+* E) hσ Jᵀ (fun i j => hJ.1 j i) hJ.2
  have ha := inv_mul_cancel₀ hu
  have hb : (σ : E →+* E) (hsq (σ : E →+* E) Jᵀ u)⁻¹ = (hsq (σ : E →+* E) Jᵀ u)⁻¹ := by
    rw [map_inv₀, sigma_hsq (σ : E →+* E) hσ _ fun i j => hJ.1 j i]
  generalize (hsq (σ : E →+* E) Jᵀ u)⁻¹ = b at ha hb
  let i : E →+* AE F E := inclR (F := F) (AF F)
  have hR := proj_idem' _ _ _ _ ha
  have hi : ∀ a, i ((σ : E →+* E) a) = sigR (AF F) σ (i a) := fun _ => rfl
  have hA : i b * hsq (sigR (AF F) σ) (Jᵀ.map i) (fun k => i (u k)) = 1 := by
    rw [← hsq_map i (σ : E →+* E) _ hi, ← map_mul, ha, map_one]
  have h1 := proj_unitary (sigR (AF F) σ) (GlobalTheory.UnitaryHeckeBaseChange.cA_cA hc) (Jᵀ.map i)
    (fun a b => (hi _).symm.trans (congrArg i (hJ.1 b a))) _ _ hA (by rw [← hi, hb])
  have h2 := det_proj' _ _ _ _ hA
  rw [← proj_map i (σ : E →+* E) (sigR (AF F) σ) hi] at h1 h2
  generalize proj (σ : E →+* E) Jᵀ u b = R at hR h1 h2
  have hR' : R.map i * R.map i = R.map i := by rw [← Matrix.map_mul, hR]
  have cS : Continuous (sec _ hR') := continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)
  refine ⟨((Units.map (sec _ hR')).comp (normOne (cA σ)).subtype).codRestrict _ fun z =>
    mem_UG_of.2 (h1 z.1 (by rw [← cA_eq, mul_comm]; exact mem_normOne.1 z.2)),
    ((Continuous.units_map _ cS).comp continuous_subtype_val).subtype_mk _, fun z => h2 _,
    fun z ⟨k, k0, hk⟩ => ⟨Units.map (sec _ hR) (Units.mk0 k k0), Units.ext (Matrix.ext fun a b => ?_)⟩, fun z t ht => ?_⟩
  · change i ((1 : Matrix _ _ E) a b + (k - 1) * R a b) =
      (1 : Matrix _ _ (AE F E)) a b + (((z.1 : (AE F E)ˣ) : AE F E) - 1) * i (R a b)
    rw [hk, map_add (f := _), map_mul, map_sub, map_one, Matrix.one_apply, Matrix.one_apply, apply_ite i, map_one, map_zero]
  · change t • (1 + (((z.1 : (AE F E)ˣ) : AE F E) - 1) • R.map i - 1) = 0
    rw [add_sub_cancel_left, ← smul_assoc, ht, zero_smul]

omit [NumberField E] in
theorem conj_mem_UAt {X : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {u : UA σ X.J} (hu : u ∈ UAt σ X ev) (g : UA σ X.J) :
    g⁻¹ * u * g ∈ UAt σ X ev := fun t ht => by
  have : mat (g⁻¹ * u * g) - 1 = mat g⁻¹ * (mat u - 1) * mat g := by
    rw [mul_sub, sub_mul, mul_one]
    exact congrArg₂ (· - ·) rfl (Units.inv_mul g.1).symm
  rw [this, ← smul_mul_assoc, ← mul_smul_comm, hu t ht, mul_zero, zero_mul]

theorem mem_of_good (hS : GlobalTheory.Published.StrongApproxSU) (hH : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (hc : IsCMExt F E σ)
    [IsGalois ℚ E] {X : Spc F E n} (hJ : IsHermND σ X.Jᵀ) (hn : 2 ≤ n) (T : Finset (Pl F)) (L : Subgroup (UA σ X.J))
    (hL : IsClosed (L : Set (UA σ X.J))) (hr : ratU σ X.J ≤ L)
    (hv : ∀ v ∉ T, SplitsFully E v → ∀ u ∈ UAt σ X (evFin F v), u ∈ L) (g : UA σ X.J) : g ∈ L := by
  obtain ⟨v, a, b, ε, e, hε, e1, e2, e3⟩ := exists_split hH hc T
  obtain ⟨S, cS, s1, s2, s3⟩ := exists_sec hc hJ (by omega)
  have hg : IsUnit (incM F X.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ (Matrix.det_transpose X.J ▸ hJ.2)).map _
  let z : normOne (cA σ) := ⟨_, det_mem_normOne ⟨fun a b => congrArg (inclR (F := F) (AF F)) (hJ.1 b a), hg⟩ g⟩
  have h1 : S z ∈ L := normOne_mem hH hc T (L.comap S) (hL.preimage cS) (fun z h => hr (s2 z h))
    (fun v a b z hz => hv v a b _ fun t ht => s3 z t (hz t ht)) z
  have h2 : g * S z⁻¹ ∈ L := su_mem hS hc hJ hn L hL hr (hv v a b) hε e1 e2 e3 _ (by
    rw [show mat (g * S z⁻¹) = mat g * mat (S z⁻¹) from rfl, Matrix.det_mul, s1]
    exact z.1.mul_inv)
  simpa using mul_mem h2 h1

theorem constOfGood_of (hS : GlobalTheory.Published.StrongApproxSU) (hH : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) : ConstOfGood := by
  intro F E _ _ _ _ _ σ B n X r s hB hX hn T f hf hr hv g
  have := hB.galois
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let L : Subgroup (UA σ X.J) :=
    { carrier := ⋂ g, {x | f (x * g) = f g}
      one_mem' := Set.mem_iInter.2 fun g => congrArg f (one_mul g)
      mul_mem' := fun {a b} ha hb => Set.mem_iInter.2 fun g =>
        (congrArg f (mul_assoc a b g)).trans ((Set.mem_iInter.1 ha _).trans (Set.mem_iInter.1 hb _))
      inv_mem' := fun {a} ha => Set.mem_iInter.2 fun g =>
        (Set.mem_iInter.1 ha _).symm.trans (congrArg f (mul_inv_cancel_left a g)) }
  have := mem_of_good hS hH hB.cm (hermND_transpose hX) hn T L
    (isClosed_iInter fun g => isClosed_eq (hf.comp (continuous_mul_const g)) continuous_const)
    (fun γ h => Set.mem_iInter.2 (hr γ h)) (fun v a b u hu => Set.mem_iInter.2 fun g =>
      (congrArg f (by group)).trans (hv v a b _ (conj_mem_UAt hu g) g)) g
  exact (congrArg f (mul_one g)).symm.trans (Set.mem_iInter.1 this 1)

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.ThConstLoc
noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Box

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

def boxL : (SB A) ⊗[ℂ] (SB B) →ₗ[ℂ] (A × B → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun a b z => a.1 z.1 * b.1 z.2) (fun _ _ _ => funext fun _ => add_mul _ _ _)
    (fun _ _ _ => funext fun _ => mul_assoc _ _ _) (fun _ _ _ => funext fun _ => mul_add _ _ _)
    fun _ _ _ => funext fun _ => mul_left_comm _ _ _)

theorem boxL_tmul (a : SB A) (b : SB B) : boxL (a ⊗ₜ[ℂ] b) = fun z => a.1 z.1 * b.1 z.2 := rfl

theorem boxL_ker : LinearMap.ker (boxL (A := A) (B := B)) = ⊥ := by
  classical
  refine LinearMap.ker_eq_bot'.2 fun x hx => ?_
  let e := Module.Basis.ofVectorSpace ℂ (SB A)
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left e x
  have h : ∀ i ∈ c.support, c i = 0 := fun i hi => Subtype.ext (funext fun y => by
    refine linearIndependent_iff'.1 e.linearIndependent c.support (fun i => (c i).1 y) (Subtype.ext (funext fun z => ?_)) i hi
    have := congrFun hx (z, y)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.sum, map_sum, boxL_tmul, Finset.sum_apply] at this
    simpa [mul_comm] using this)
  exact Finset.sum_eq_zero fun i hi => by simp [h i hi]

theorem mem_range_boxL [T2Space A] [T2Space B] {f : A × B → ℂ} (hf : f ∈ SB (A × B)) : f ∈ LinearMap.range boxL := by
  classical
  have hK : IsCompact (tsupport f) := hf.2
  have z : ∀ x y, (x, y) ∉ tsupport f → f (x, y) = 0 := fun x y h => image_eq_zero_of_notMem_tsupport h
  have hl : IsLocallyConstant fun x y => f (x, y) := (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
    have h1 := (hK.image continuous_snd).eventually_forall_of_forall_eventually (x₀ := x)
      (P := fun x' y => f (x', y) = f (x, y)) fun y _ => by
        have a := (IsLocallyConstant.iff_eventually_eq _).1 hf.1 (x, y)
        have b : ∀ᶠ w : A × B in 𝓝 (x, y), f (x, w.2) = f (x, y) :=
          (IsLocallyConstant.iff_eventually_eq _).1 (hf.1.comp_continuous (f := fun w : A × B => (x, w.2)) (by fun_prop)) (x, y)
        filter_upwards [a, b] with w h h' using h.trans h'.symm
    filter_upwards [h1] with x' h
    funext y
    by_cases hy : y ∈ Prod.snd '' tsupport f
    · exact h y hy
    · rw [z _ _ fun h => hy ⟨_, h, rfl⟩, z _ _ fun h => hy ⟨_, h, rfl⟩]
  have hfin : ((fun x y => f (x, y)) '' (Prod.fst '' tsupport f)).Finite := by
    letI : TopologicalSpace (B → ℂ) := ⊥
    haveI : DiscreteTopology (B → ℂ) := ⟨rfl⟩
    exact ((hK.image continuous_fst).image hl.continuous).finite_of_discrete
  have e : f = ∑ g ∈ hfin.toFinset, fun w : A × B =>
      Set.indicator {x | (fun y => f (x, y)) = g} (fun x => if g = 0 then (0 : ℂ) else 1) w.1 * g w.2 := funext fun w => by
    rw [Finset.sum_apply, Finset.sum_eq_single (fun y => f (w.1, y)) (fun g _ hg => by simp [hg.symm])]
    · by_cases h : (fun y => f (w.1, y)) = 0
      · simpa [h] using congrFun h w.2
      · simp [h]
    · intro h
      exact mul_eq_zero_of_right _ (z w.1 w.2 fun h' => h (hfin.mem_toFinset.2 ⟨_, ⟨_, h', rfl⟩, rfl⟩))
  rw [e]
  refine Submodule.sum_mem _ fun g hg => ?_
  obtain ⟨x, -, rfl⟩ := hfin.mem_toFinset.1 hg
  refine ⟨(⟨_, (LocallyConstant.indicator (LocallyConstant.const A _) (hl.isClopen_fiber _)).2,
    HasCompactSupport.intro (hK.image continuous_fst) fun x' hx' => ?_⟩ : SB A) ⊗ₜ
    (⟨_, hf.1.comp_continuous (f := fun y => (x, y)) (by fun_prop),
      HasCompactSupport.intro (hK.image continuous_snd) fun y hy => z _ _ fun h => hy ⟨_, h, rfl⟩⟩ : SB B), rfl⟩
  have : (fun y => f (x', y)) = 0 := funext fun y => z _ _ fun h => hx' ⟨_, h, rfl⟩
  refine Set.indicator_apply_eq_zero.2 fun h => ?_
  exact if_pos (h.symm.trans this)

theorem sb_comp {f : B → ℂ} (hf : f ∈ SB B) (e : A ≃ₜ B) : (fun x => f (e x)) ∈ SB A :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

end Box

section Mat

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n n' d : ℕ}

def lrH (g : GL (Fin n) k) (h : GL (Fin d) k) : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Y := g.1 * Y * h.1
  invFun Y := (g⁻¹).1 * Y * (h⁻¹).1
  left_inv Y := by simp [Matrix.mul_assoc]
  right_inv Y := by simp [Matrix.mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sb_right {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (h : GL (Fin d) k) :
    (fun y : Matrix (Fin n) (Fin d) k => f (y * h.1)) ∈ SB _ := by
  simpa [lrH] using sb_comp hf (lrH 1 h)

theorem sb_left {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (g : GL (Fin n) k) :
    (fun y : Matrix (Fin n) (Fin d) k => f (g.1 * y)) ∈ SB _ := by
  simpa [lrH] using sb_comp hf (lrH g 1)

def rowsH (e : Fin n ⊕ Fin n' ≃ Fin d) : Matrix (Fin d) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k × Matrix (Fin n') (Fin d) k where
  toFun Y := ((Y.submatrix e id).toRows₁, (Y.submatrix e id).toRows₂)
  invFun Z := (Matrix.fromRows Z.1 Z.2).submatrix e.symm id
  left_inv Y := by simp
  right_inv Z := by simp
  continuous_toFun := by
    refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_) <;>
      exact continuous_id.matrix_elem _ _
  continuous_invFun := continuous_matrix fun i j => by
    obtain ⟨i | i, rfl⟩ := e.surjective i <;>
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
    exacts [continuous_fst.matrix_elem _ _, continuous_snd.matrix_elem _ _]

end Mat

theorem locBil (hL : LocDist) {F : Type} [Field F] [NumberField F] (v : Pl F) {n n' d : ℕ} (e : Fin n ⊕ Fin n' ≃ Fin d)
    (ξ : (Fv F v)ˣ →* ℂˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ (unifAt v) : ℂ) ≠ t)
    (β : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n') (Fin d) (Fv F v)) →ₗ[ℂ] ℂ)
    (hβ : ∀ a b (h : GL (Fin d) (Fv F v)), β ⟨_, sb_right a.2 h⟩ ⟨_, sb_right b.2 h⟩ = ξ (Matrix.GeneralLinearGroup.det h) * β a b)
    (a b) (g : GL (Fin n) (Fv F v)) : β ⟨_, sb_left a.2 g⟩ b = ξ (Matrix.GeneralLinearGroup.det g) * β a b := by
  obtain ⟨q, hq⟩ := (boxL (A := Matrix (Fin n) (Fin d) (Fv F v)) (B := Matrix (Fin n') (Fin d) (Fv F v))).exists_leftInverse_of_injective boxL_ker
  let l := TensorProduct.lift β ∘ₗ q ∘ₗ LinearMap.funLeft ℂ ℂ (rowsH (k := Fv F v) e).symm
  have hl : ∀ x, l (fun y => boxL x (rowsH e y)) = TensorProduct.lift β x := fun x => by
    have : LinearMap.funLeft ℂ ℂ (rowsH (k := Fv F v) e).symm (fun y => boxL x (rowsH e y)) = boxL x := funext fun y => by
      simp [LinearMap.funLeft_apply]
    simp only [l, LinearMap.comp_apply, this]
    rw [← LinearMap.comp_apply q, hq, LinearMap.id_apply]
  let G : Matrix (Fin d) (Fin d) (Fv F v) := Matrix.reindex e e (Matrix.fromBlocks g.1 0 0 1)
  have hG : G.det = g.1.det := by simp [G]
  let G' := Matrix.GeneralLinearGroup.mkOfDetNeZero G (hG ▸ g.det_ne_zero)
  have key := (hL F v d d ξ hξ l (fun φ hφ h => ?_)).2 rfl (fun y => boxL (a ⊗ₜ b) (rowsH e y))
    (sb_comp (f := fun z => a.1 z.1 * b.1 z.2) ⟨(a.2.1.comp_continuous continuous_fst).mul (b.2.1.comp_continuous continuous_snd),
      HasCompactSupport.intro (a.2.2.prod b.2.2) fun z hz => ?_⟩ _) G'
  · rw [hl, show Matrix.GeneralLinearGroup.det G' = Matrix.GeneralLinearGroup.det g from Units.ext hG] at key
    rw [← TensorProduct.lift.tmul, ← hl, ← TensorProduct.lift.tmul, ← key]
    congr 1
    funext y
    have : rowsH e (G * y) = (g.1 * (rowsH e y).1, (rowsH e y).2) := by
      ext i j <;> simp [rowsH, G, Matrix.mul_apply, ← e.sum_comp, Matrix.one_apply]
    exact (congrArg (boxL (a ⊗ₜ b)) this).symm
  · obtain ⟨x, hx⟩ := mem_range_boxL (sb_comp hφ (rowsH e).symm)
    obtain rfl : φ = fun y => boxL x (rowsH e y) := funext fun y => by simp [hx]
    clear hx hφ
    induction x using TensorProduct.induction_on with
    | zero => simp [← Pi.zero_def]
    | add x y hx hy =>
      simp only [map_add (f := _), Pi.add_apply]
      rw [← Pi.add_def, ← Pi.add_def, map_add (f := _), map_add (f := _), hx, hy, mul_add]
    | tmul a b =>
      rw [hl, TensorProduct.lift.tmul, ← hβ, ← TensorProduct.lift.tmul, ← hl]
      rfl
  · by_cases h : z.1 ∈ tsupport a.1
    · rw [image_eq_zero_of_notMem_tsupport (f := b.1) fun h' => hz ⟨h, h'⟩, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]

end GlobalTheory.ThK.Dbl.TC

end
end
