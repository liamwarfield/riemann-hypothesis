module

public import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.ExistsHaarOfIsCompact
noncomputable section
namespace PositivityTheory.ThKG.Tow.Stab
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show (g.1 * g.1⁻¹ : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

def stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : Subgroup (UA σ X.J) where
  carrier := {g | (∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)) ∧
    ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X}
  one_mem' := by
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _
    · simp only [inv_one, mat_one, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_mul, Matrix.map_mul]; exact (hg1 w).mul_left (hh1 w)
    · rw [mul_inv_rev, mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact ⟨(hg2 _ (hh2 z hz).1).1, (hh2 _ (hg2 z hz).2).2⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · set A := (mat g).map (piInf (B.emb w))
      set A' := (mat g⁻¹).map (piInf (B.emb w))
      have e1 : A * A' = 1 := by
        rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      have e2 : A' * A = 1 := by
        rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have hc := hg1 w
      show A' * X.θ w = X.θ w * A'
      calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [e1, Matrix.mul_one]
        _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
        _ = A' * (A * X.θ w) * A' := by rw [hc.eq]
        _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
        _ = X.θ w * A' := by rw [e2, Matrix.one_mul]
    · rw [inv_inv]; exact ⟨(hg2 z hz).2, (hg2 z hz).1⟩

theorem isStab_stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : IsStab B (stabK (σ := σ) B X) := fun _ => Iff.rfl

theorem exists_haar_of_isCompact {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J))
    (hK : IsCompact (K : Set (UA σ J))) : ∃ μ : Measure K, μ.IsHaarMeasure := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact ⟨Measure.haarMeasure ⊤, Measure.isHaarMeasure_haarMeasure _⟩

theorem exists_haar_idele : ∃ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

theorem isClosed_stabK (B : Base F E) {n : ℕ} (X : Spc F E n)
    (hL : IsClosed ((latHat X : AddSubgroup (Fin n → AE F E)) : Set (Fin n → AE F E))) :
    IsClosed ((stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ X.J => mat g⁻¹ := hm.comp continuous_inv
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have h1 : IsClosed {g : UA σ X.J | ∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))
  have h2 : IsClosed {g : UA σ X.J | ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun z => isClosed_iInter fun _ => ?_
    exact (hL.preimage (hm.matrix_mulVec continuous_const)).inter (hL.preimage (hmi.matrix_mulVec continuous_const))
  exact h1.inter h2

end PositivityTheory.ThKG.Tow.Stab
end
end

noncomputable section

namespace PositivityTheory.ThKG.Tow.Stab

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
    ∃ R : ℝ, ∀ A : Matrix (Fin n) (Fin n) ℂ, Aᵀ * M * A.map star = M → Commute A θ → ∀ i j, ‖A i j‖ ≤ R := _root_.GlobalTheory.ThK.Dbl.St.cartan_bound (n := n) (M := M) (θ := θ) h

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
      rw [map_add]
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
    rw [hX.span_eq_top]; trivial
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
    have h3 : ∀ b : AE F E, Continuous fun x : AF F => x • b := fun b => continuous_id.smul continuous_const
    exact ((h3 1).comp h1).add ((h3 a).comp h2)
  · refine Levi.ad_ext h τ (fun w => ?_) fun v => ?_
    · have e0 : (eF F).1 w = 0 := rfl
      rw [map_add (f := _), map_add (f := _), piInf_smul, piInf_smul, piInf_smul, eρ, eρ, ha, e0, map_zero, map_one, zero_mul, mul_one,
        add_zero, Complex.re_add_im]
    · have e0 : compFin F E v ((1 - eF F) • z) = 0 := compFin_smul v (sub_self (1 : Af F)) z
      rw [sub_smul, one_smul, map_sub, sub_eq_zero] at e0
      rw [map_add (f := _), map_add (f := _), compFin_smul v rfl, compFin_smul v rfl, zero_add, zero_add, e0]

theorem exists_compact_mat {B : Base F E} {X : Spc F E n} {r s : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) :
    ∃ S : Set (Matrix (Fin n) (Fin n) (AE F E)), IsCompact S ∧ ∀ k ∈ stabK (σ := σ) B X, mat k ∈ S := by
  obtain ⟨Φ, hΦ, eΦ⟩ := exists_section hB.cm B.emb
  have hFull : X.L.IsFullLattice E := by
    let := hX.lat
    refine { span_eq_top := ?_ }
    let W := Submodule.span E (X.L : Set (Fin n → E))
    change W = ⊤
    by_contra hW
    let g : (Fin n → E) →ₗ[E] Module.Dual E W :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin X.Jᵀ)).domRestrict₂ W
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Fin n → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin n → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have hJ : X.Jᵀ.map σ = X.J := Matrix.ext hX.herm
    -- Self-duality puts every scalar multiple of an orthogonal vector in the lattice.
    have hline (a : E) : a • y ∈ X.L := (hX.dual _).2 fun x hx => by
      have hz' : z ⬝ᵥ X.Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      have horth : form σ X.J y x = 0 := by
        have he := σ.toRingHom.map_dotProduct z (X.Jᵀ *ᵥ x)
        rw [hz', map_zero] at he
        have hm : σ.toRingHom ∘ (X.Jᵀ *ᵥ x) = X.J *ᵥ (fun i => σ (x i)) := by
          funext i
          rw [Function.comp_apply, σ.toRingHom.map_mulVec]
          exact congrFun (congrArg (fun M => M *ᵥ (fun j => σ (x j))) hJ) i
        rw [hm] at he
        exact he.symm
      have : form σ X.J (a • y) x = 0 := by
        simpa only [form, smul_dotProduct, smul_eq_mul] using
          (show a * form σ X.J y x = 0 by rw [horth, mul_zero])
      rw [this]
      exact isIntegral_zero
    let i : E →ₗ[𝓞 E] X.L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict X.L hline
    let : Module.Finite (𝓞 E) X.L := Module.Finite.iff_fg.mpr hX.lat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  choose C hC h using fin_bound X hFull
  choose R hR using fun w => cartan_bound (hX.cartan w)
  have hD : IsCompact (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) :=
    (isCompact_univ_pi fun w => isCompact_closedBall _ _).image hΦ
  refine ⟨Set.univ.pi fun i => Set.univ.pi fun j => (Φ '' Set.univ.pi fun w => Metric.closedBall (0 : ℂ) (R w)) + C i j,
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => hD.add (hC i j), fun k hk i _ j _ => ?_⟩
  rw [eΦ (mat k i j)]
  refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ (h i j _ fun y hy => (hk.2 y hy).1)
  rw [mem_closedBall_zero_iff]
  refine hR w ((mat k).map (piInf (B.emb w))) ?_ (hk.1 w) i j
  rw [← Levi.iso_map_piInf (σ := σ) (fun τ z => Levi.piInf_cA hB.cm τ z)]
  have e : (mat k)ᵀ * incM F X.J * (mat k).map (cA σ) = incM F X.J := k.2
  rw [e]
  exact Matrix.ext fun i j => Levi.piInf_incl _ _

theorem isCompact_stabK {B : Base F E} {X : Spc F E n} {r s : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) :
    IsCompact ((stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
  obtain ⟨S, hS, h⟩ := exists_compact_mat hB hX
  have hc : Continuous (cA (F := F) σ) := IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have hU : IsClosed ((UG (cA σ) (incM F X.J) : Subgroup (GL (Fin n) (AE F E))) : Set (GL (Fin n) (AE F E))) :=
    isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map hc)) continuous_const
  exact isCompact_of_units _ hU _ (isClosed_stabK B X (isCompact_latHat X hX.lat.fg).isClosed) S hS
    fun k hk => ⟨h k hk, h _ (inv_mem hk)⟩

end PositivityTheory.ThKG.Tow.Stab

end
