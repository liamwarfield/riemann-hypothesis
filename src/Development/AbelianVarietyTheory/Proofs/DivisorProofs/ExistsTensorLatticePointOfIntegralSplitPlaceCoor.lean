module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleAddSecondSlotComplexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLatticePointOfIntegralSplitPlaceCoor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLatticePointOfIntegralSplitPlaceCoor
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LatFill
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_smul {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (a : AF F) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW τ (a • z) = evFin F v a * piW τ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), mul_add]
  | tmul b x =>
    rw [TensorProduct.smul_tmul']
    change splitProj τ (compFin F E v ((a • b) ⊗ₜ[F] x)) = evFin F v a * splitProj τ (compFin F E v (b ⊗ₜ[F] x))
    simp [compFin, mul_assoc]

theorem piW_inclR {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (F := F) (AF F) x) = τ x := by
  change splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x
  simp [compFin]

variable {n d : ℕ}

def fillSet (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) :
    AddSubgroup (Matrix (Fin n) (Fin d) (Fv F v)) where
  carrier := {M | ∃ γ ∈ latAtV X W v, (∀ i j, piW (t.comp σ) (γ i j) = 0) ∧ ∀ i j, piW t (γ i j) = M i j}
  zero_mem' := ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro _ _ ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩
    exact ⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1'], fun i j => by simp [h2, h2']⟩
  neg_mem' := by
    rintro _ ⟨γ, hγ, h1, h2⟩
    exact ⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩

variable {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d} {v : Pl (F := F)} {t : E →ₐ[F] Fv F v}

theorem smul_mem_fillSet {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) {M : Matrix (Fin n) (Fin d) (Fv F v)}
    (hM : M ∈ fillSet σ X W v t) : a • M ∈ fillSet σ X W v t := by
  obtain ⟨γ, hγ, h1, h2⟩ := hM
  refine ⟨GlobalTheory.LatVac.liftV v a • γ, (GlobalTheory.LatVac.latAtV_at_stable X W v).2 a ha γ hγ, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.smul_apply, piW_smul, h1, mul_zero]
  · rw [Matrix.smul_apply, piW_smul, h2, GlobalTheory.LatVac.evFin_liftV, Matrix.smul_apply, smul_eq_mul]

theorem gen_mem_fillSet (h : IsCMExt F E σ) {x : Fin n → E} (hx : x ∈ X.L) {x' : Fin d → E} (hx' : x' ∈ W.L) :
    Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j)) ∈ fillSet σ X W v t := by
  have key : ∀ e ∈ intLoc F E v, ∃ γ ∈ latAtV X W v,
      (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧
      ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j)) := by
    intro e he
    refine intLoc_induction (p := fun e => ∃ γ ∈ latAtV X W v,
      (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧
      ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j))) (fun a ha o => ?_) ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => by simp⟩ ?_ ?_ he
    · have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
      refine ⟨GlobalTheory.LatVac.liftV v a • incM F (Matrix.vecMulVec (o • x) x'),
        AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha,
          _, X.L.smul_mem o hx, x', hx', rfl⟩, fun i j => ?_, fun i j => ?_⟩
      · simp only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV,
          Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]
        rw [Algebra.smul_def, map_mul, ho]
        simp only [AlgHom.comp_apply]
        ring
      · simp only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV,
          Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]
        rw [Algebra.smul_def, map_mul, ho]
        ring
    · rintro y z ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩
      exact ⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1', add_mul],
        fun i j => by simp [h2, h2', add_mul]⟩
    · rintro y ⟨γ, hγ, h1, h2⟩
      exact ⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩
  obtain ⟨γ, hγ, h1, h2⟩ := key _ (splitIdem_mem h t)
  exact ⟨γ, hγ, fun i j => by simp [h1], fun i j => by simp [h2, Matrix.vecMulVec_apply]⟩

theorem vecMulVec_mem_fillSet (h : IsCMExt F E σ) {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc F X.L v)
    {y' : Fin d → Fv F v ⊗[F] E} (hy' : y' ∈ latLoc F W.L v) :
    Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t := by
  refine latLoc_induction (p := fun y => Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t)
    (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · refine latLoc_induction (p := fun y' => Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t y') ∈
      fillSet σ X W v t) (fun a' ha' x' hx' => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy'
    · have e : Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t fun j => a' ⊗ₜ[F] x' j) =
          (a * a') • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j)) := by
        ext i j; simp [splitVec, Matrix.vecMulVec_apply]; ring
      rw [e]
      exact smul_mem_fillSet (mul_mem ha ha') (gen_mem_fillSet h hx hx')
    · convert zero_mem (fillSet σ X W v t) using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply]
    · convert add_mem hy hz using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply, mul_add]
    · convert neg_mem hy using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply]
  · convert zero_mem (fillSet σ X W v t) using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply]
  · convert add_mem hy hz using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply, add_mul]
  · convert neg_mem hy using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply]

theorem mul_mul_transpose_eq_sum {K : Type} [Field K] (b : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin d) (Fin d) K)
    (A : Matrix (Fin n) (Fin d) K) :
    b * A * cᵀ = ∑ i, ∑ j, A i j • Matrix.vecMulVec (b *ᵥ Pi.single i 1) (c *ᵥ Pi.single j 1) := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, Matrix.col_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.LatFill

theorem GlobalTheory.LatFill.exists_latAtV_coord : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∀ A : Matrix (Fin n) (Fin d) (Fv F v), (∀ i j, A i j ∈ v.adicCompletionIntegers F) →
      ∃ γ ∈ latAtV X W v, γ.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ = A := by
  intro F E _ _ _ _ _ σ n d h X W v t b c hb hc A hA
  have single_mem : ∀ {m : ℕ} (i : Fin m) (k : Fin m),
      (Pi.single i (1 : Fv F v) : Fin m → Fv F v) k ∈ v.adicCompletionIntegers F := fun i k => by
    by_cases e : k = i
    · subst e; simp
    · simp [e]
  have hT : b.1 * A * c.1ᵀ ∈ GlobalTheory.LatFill.fillSet σ X W v t := by
    rw [GlobalTheory.LatFill.mul_mul_transpose_eq_sum]
    refine sum_mem fun i _ => sum_mem fun j _ => GlobalTheory.LatFill.smul_mem_fillSet (hA i j) ?_
    obtain ⟨y, hy, ey⟩ := (hb _).1 (single_mem i)
    obtain ⟨y', hy', ey'⟩ := (hc _).1 (single_mem j)
    rw [← ey, ← ey']
    exact GlobalTheory.LatFill.vecMulVec_mem_fillSet h hy hy'
  obtain ⟨γ, hγ, h1, h2⟩ := hT
  refine ⟨γ, hγ, Matrix.ext fun i j => h1 i j, ?_⟩
  have e : γ.map (piW t) = b.1 * A * c.1ᵀ := Matrix.ext fun i j => h2 i j
  rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.mul_one]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLatticePointOfIntegralSplitPlaceCoorStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorLattice_point_of_integral_splitPlace_coordinate : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∀ A : Matrix (Fin n) (Fin d) (Fv F v), (∀ i j, A i j ∈ v.adicCompletionIntegers F) →
      ∃ γ ∈ latAtV X W v, γ.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ = A := by
  first | exact @GlobalTheory.LatFill.exists_latAtV_coord | exact GlobalTheory.LatFill.exists_latAtV_coord | (intros; apply GlobalTheory.LatFill.exists_latAtV_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalIntegralIntegralNormCongruen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalIntegralIntegralNormCongruen
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.BCT.StTwLevel

theorem finsum_const_mul {ι : Type} (c : ℂ) (g : ι → ℂ) : ∑ᶠ i, c * g i = c * ∑ᶠ i, g i := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases h : (Function.support g).Finite
  · exact (mul_finsum _ _).symm
  · have hs : Function.support (fun i => c * g i) = Function.support g := by
      ext i; simp [hc]
    rw [finsum_of_infinite_support h, mul_zero, finsum_of_infinite_support (by rwa [hs])]

theorem avg_const_mul {H : Type} [Group H] (c : ℂ) (u : H → ℂ) : avg (fun h => c * u h) = c * avg u := by
  by_cases hc : c = 0
  · simp [hc, avg]
  have hR : rStab (fun h => c * u h) = rStab u := by
    ext k
    simp only [GlobalTheory.TwOrbConj.mem_rStab, mul_right_inj' hc]
  unfold avg
  rw [hR, finsum_const_mul]
  ring

theorem twOrb_const_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (c : ℂ)
    (f : G → ℂ) : twOrb θ K δ (fun x => c * f x) = c * twOrb θ K δ f := by
  unfold twOrb
  simp_rw [avg_const_mul]
  rw [← finsum_const_mul]
  refine finsum_congr fun q => ?_
  ring

theorem clSum_const_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G)
    (wt : G → ℂ) (c : ℂ) (f : G → ℂ) : clSum θ K S wt (fun x => c * f x) = c * clSum θ K S wt f := by
  unfold clSum
  rw [← finsum_const_mul]
  refine finsum_congr fun d => ?_
  split_ifs
  · rw [twOrb_const_mul]; ring
  · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem stTw2_const_mul (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ)
    (φ : GLw a w × GLw b w → ℂ) : stTw2 a b w Q₁ Q₂ (fun y => c * φ y) = c * stTw2 a b w Q₁ Q₂ φ := by
  unfold stTw2
  exact clSum_const_mul _ _ _ _ _ _

def lev (n : ℕ) (w : Pl E) (k : ℕ) (y : GLw n w) : ℂ :=
  if y ∈ GlobalTheory.LFun.KGL w (n := n) ∧ nrmL n w y ∈ GlobalTheory.PrincCong.congSub w n k then 1 else 0

theorem nrm_eq {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (y : GLw n w) : nrmL n w y = y * thL n w y := by
  unfold nrmL thL
  rw [if_neg hw, if_neg hw]

theorem thL_KGL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) :
    thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hw]
  rw [ht]
  obtain ⟨h, rfl⟩ := hg
  let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (GlobalTheory.PrincCong.cj_mem_Ov w)
  exact ⟨thetaGL n c' h, GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) h⟩

theorem conj_mem_congSub {w : Pl E} {n k : ℕ} {h g : GLw n w} (hh : h ∈ GlobalTheory.LFun.KGL w (n := n))
    (hg : g ∈ GlobalTheory.PrincCong.congSub w n k) : h * g * h⁻¹ ∈ GlobalTheory.PrincCong.congSub w n k := by
  obtain ⟨h', rfl⟩ := hh
  obtain ⟨g', hg', rfl⟩ := hg
  exact ⟨h' * g' * h'⁻¹, (MonoidHom.normal_ker _).conj_mem g' hg' h', by simp only [map_mul, map_inv]⟩

end GlobalTheory.BCT.StTwLevel

namespace GlobalTheory.BCT.StTwLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_le {w : Pl E} {n k : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.PrincCong.congSub w n k) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) := ((GlobalTheory.PrincCong.mem_congSub_iff w n k g).1 hg).1

theorem lev_level {w : Pl E} (hw : ¬ IsSplitAt w) (n k : ℕ) :
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.PrincCong.congSub w n k) :=
  ⟨GlobalTheory.PrincCong.isOpen_congSub w n k, fun _ hg => congSub_le hg, GlobalTheory.PrincCong.thL_mem_congSub w hw n k⟩

theorem lev_hecke {w : Pl E} (hw : ¬ IsSplitAt w) (n k : ℕ) :
    IsHecke (GlobalTheory.PrincCong.congSub w n k) (lev n w k) := by
  refine ⟨?_, fun x hx y => ⟨?_, ?_⟩⟩
  · have hc := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
    refine HasCompactSupport.intro' hc.2 (Subgroup.isClosed_of_isOpen _ hc.1) fun y hy => ?_
    unfold lev
    exact if_neg fun h => hy h.1
  · have hxK := congSub_le hx
    have hθx := GlobalTheory.PrincCong.thL_mem_congSub w hw n k x hx
    unfold lev
    refine if_congr ?_ rfl rfl
    by_cases hy : y ∈ GlobalTheory.LFun.KGL w (n := n)
    · have hxy : x * y ∈ GlobalTheory.LFun.KGL w (n := n) := mul_mem hxK hy
      have hθy := thL_KGL hw n hy
      have hm : (thL n w y)⁻¹ * thL n w x * thL n w y ∈ GlobalTheory.PrincCong.congSub w n k := by
        simpa using conj_mem_congSub (inv_mem hθy) hθx
      have e : nrmL n w (x * y) = x * nrmL n w y * ((thL n w y)⁻¹ * thL n w x * thL n w y) := by
        rw [nrm_eq hw, nrm_eq hw, map_mul]; group
      rw [e, Subgroup.mul_mem_cancel_right _ hm, Subgroup.mul_mem_cancel_left _ hx]
      exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨hxy, h.2⟩⟩
    · have hxy : x * y ∉ GlobalTheory.LFun.KGL w (n := n) := fun h => hy (by simpa using mul_mem (inv_mem hxK) h)
      exact ⟨fun h => absurd h.1 hxy, fun h => absurd h.1 hy⟩
  · have hxK := congSub_le hx
    have hθx := GlobalTheory.PrincCong.thL_mem_congSub w hw n k x hx
    unfold lev
    refine if_congr ?_ rfl rfl
    by_cases hy : y ∈ GlobalTheory.LFun.KGL w (n := n)
    · have hxy : y * x ∈ GlobalTheory.LFun.KGL w (n := n) := mul_mem hy hxK
      have hθy := thL_KGL hw n hy
      have hm : (thL n w y)⁻¹ * x * thL n w y ∈ GlobalTheory.PrincCong.congSub w n k := by
        simpa using conj_mem_congSub (inv_mem hθy) hx
      have e : nrmL n w (y * x) = nrmL n w y * ((thL n w y)⁻¹ * x * thL n w y) * thL n w x := by
        rw [nrm_eq hw, nrm_eq hw, map_mul]; group
      rw [e, Subgroup.mul_mem_cancel_right _ hθx, Subgroup.mul_mem_cancel_right _ hm]
      exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨hxy, h.2⟩⟩
    · have hxy : y * x ∉ GlobalTheory.LFun.KGL w (n := n) := fun h => hy (by simpa using mul_mem h (inv_mem hxK))
      exact ⟨fun h => absurd h.1 hxy, fun h => absurd h.1 hy⟩

theorem lev_eq {w : Pl E} (n k : ℕ) :
    (fun y : GLw n w => if y ∈ GlobalTheory.LFun.KGL w (n := n) ∧ nrmL n w y ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j,
      Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}
      then (1 : ℂ) else 0) = lev n w k := by
  funext y
  unfold lev
  exact if_congr (and_congr Iff.rfl (GlobalTheory.PrincCong.mem_congSub_iff w n k _).symm) rfl rfl

theorem stTw2_lev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (a b k : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → stTw2 a b w Q₁ Q₂ (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) = c * (stTw a w Q₁ (fun y : GLw a w => if y ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) * stTw b w Q₂ (fun y : GLw b w => if y ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  intro E _ _ _ w hw a b k Q₁ Q₂ c _ _ _ _ _
  rw [lev_eq a k, lev_eq b k]
  have e : (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then (1 : ℂ) else 0)) =
      fun y => c * GlobalTheory.BCT.tens (lev a w k) (lev b w k) y := by
    funext y
    congr 1
    have h1 := congrFun (lev_eq (w := w) a k) y.1
    have h2 := congrFun (lev_eq (w := w) b k) y.2
    rw [GlobalTheory.BCT.tens, ← h1, ← h2, ite_zero_mul_ite_zero, mul_one]
    exact if_congr and_assoc.symm rfl rfl
  rw [e, stTw2_const_mul, GlobalTheory.BCT.StTwTens.stTw2_tens E a b w Q₁ Q₂ _ _ _ _ (lev_level hw a k) (lev_level hw b k)
    (lev_hecke hw a k) (lev_hecke hw b k)]

end GlobalTheory.BCT.StTwLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalIntegralIntegralNormCongruenStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableTwistedOrbitalIntegral_integralNormCongruence_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (a b k : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → stTw2 a b w Q₁ Q₂ (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) = c * (stTw a w Q₁ (fun y : GLw a w => if y ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) * stTw b w Q₂ (fun y : GLw b w => if y ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  first | exact @GlobalTheory.BCT.StTwLevel.stTw2_lev | exact GlobalTheory.BCT.StTwLevel.stTw2_lev | (intros; apply GlobalTheory.BCT.StTwLevel.stTw2_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicCoord

section Ad

variable (F : Type) [Field F] [NumberField F]

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

variable {F} in
theorem af_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem pairA_mul_eq_zero_iff_snd (a : AF F) : pairA F 0 1 * a = 0 ↔ sndA F a = 0 := by
  constructor
  · intro h
    have := congrArg (sndA F) h
    rwa [map_mul, map_zero, sndA_pairA, one_mul] at this
  · intro h
    refine af_ext ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA, zero_mul]
    · rw [map_mul, map_zero, sndA_pairA, h, mul_zero]

theorem pairA_mul_eq_zero_iff_fst (a : AF F) : pairA F 1 0 * a = 0 ↔ fstA F a = 0 := by
  constructor
  · intro h
    have := congrArg (fstA F) h
    rwa [map_mul, map_zero, fstA_pairA, one_mul] at this
  · intro h
    refine af_ext ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA, h, mul_zero]
    · rw [map_mul, map_zero, sndA_pairA, zero_mul]

def incF : Af F →ₗ[F] AF F where
  toFun y := pairA F 0 y
  map_add' y y' := af_ext (by rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA, add_zero])
    (by rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA])
  map_smul' c y := af_ext (by rw [map_smul, fstA_pairA, fstA_pairA, RingHom.id_apply, smul_zero])
    (by rw [map_smul, sndA_pairA, sndA_pairA, RingHom.id_apply])

def incI : Ainf F →ₗ[F] AF F where
  toFun y := pairA F y 0
  map_add' y y' := af_ext (by rw [map_add (f := _), fstA_pairA, fstA_pairA, fstA_pairA])
    (by rw [map_add (f := _), sndA_pairA, sndA_pairA, sndA_pairA, add_zero])
  map_smul' c y := af_ext (by rw [map_smul, fstA_pairA, fstA_pairA, RingHom.id_apply])
    (by rw [map_smul, sndA_pairA, sndA_pairA, RingHom.id_apply, smul_zero])

theorem incF_sndA (a : AF F) : incF F (sndA F a) = pairA F 0 1 * a :=
  af_ext (by rw [map_mul, fstA_pairA, zero_mul]; rfl) (by rw [map_mul, sndA_pairA, one_mul]; rfl)

theorem incI_fstA (a : AF F) : incI F (fstA F a) = pairA F 1 0 * a :=
  af_ext (by rw [map_mul, fstA_pairA, one_mul]; rfl) (by rw [map_mul, sndA_pairA, zero_mul]; rfl)

end Ad

variable (D : D7)

def secF : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (incF D.host.F) LinearMap.id

def secI : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (incI D.host.F) LinearMap.id

theorem secF_finPart (z : AE D) : secF D (finPart D z) = pairA D.host.F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(finPart D).map_zero, (secF D).map_zero, smul_zero]
  | tmul a b =>
    have h1 : finPart D (a ⊗ₜ b) = sndA D.host.F a ⊗ₜ b := rfl
    rw [h1, secF, TensorProduct.map_tmul, LinearMap.id_apply, incF_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (finPart D), map_add (secF D), hx, hy, smul_add]

theorem secI_infPart (z : AE D) : secI D (infPart D z) = pairA D.host.F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(infPart D).map_zero, (secI D).map_zero, smul_zero]
  | tmul a b =>
    have h1 : infPart D (a ⊗ₜ b) = fstA D.host.F a ⊗ₜ b := rfl
    rw [h1, secI, TensorProduct.map_tmul, LinearMap.id_apply, incI_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (infPart D), map_add (secI D), hx, hy, smul_add]

theorem finPart_smul (z : AE D) : finPart D (pairA D.host.F 0 1 • z) = finPart D z := by
  rw [Algebra.smul_def, (finPart D).map_mul]
  have : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA D.host.F (algebraMap (AF D.host.F) (AF D.host.F) (pairA D.host.F 0 1)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, sndA_pairA]
    rfl
  rw [this, one_mul]

theorem infPart_smul (z : AE D) : infPart D (pairA D.host.F 1 0 • z) = infPart D z := by
  rw [Algebra.smul_def, (infPart D).map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA D.host.F (algebraMap (AF D.host.F) (AF D.host.F) (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, fstA_pairA]
    rfl
  rw [this, one_mul]

theorem finPart_eq_zero_iff (z : AE D) : finPart D z = 0 ↔ pairA D.host.F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secF_finPart, h, (secF D).map_zero]
  · intro h; rw [← finPart_smul, h, (finPart D).map_zero]

theorem infPart_eq_zero_iff (z : AE D) : infPart D z = 0 ↔ pairA D.host.F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secI_infPart, h, (secI D).map_zero]
  · intro h; rw [← infPart_smul, h, (infPart D).map_zero]

theorem smul_vec_fin {N : ℕ} (u : Fin N → AF D.host.F) : pairA D.host.F 0 1 • u = 0 ↔ GlobalTheory.SWQ.fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd D.host.F (u l)

theorem smul_vec_inf {N : ℕ} (u : Fin N → AF D.host.F) : pairA D.host.F 1 0 • u = 0 ↔ GlobalTheory.SWQ.inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst D.host.F (u l)

theorem smul_pair_eq_zero {N : ℕ} (c : AF D.host.F) (w : VA D.host.F N) : c • w = 0 ↔ c • w.1 = 0 ∧ c • w.2 = 0 :=
  Prod.ext_iff

theorem coord (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N) :
    Continuous e ∧ Continuous e.symm ∧
      (∀ x, x.map (finPart D) = 0 ↔ GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧
      (∀ x, x.map (infPart D) = 0 ↔ GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  haveI h0 : IsModuleTopology (AF D.host.F) (AE D) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI h1 : IsModuleTopology (AF D.host.F) (Fin n → AE D) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF D.host.F) (Matrix (Fin m) (Fin n) (AE D)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (finPart D) = 0 ↔ pairA D.host.F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPart_eq_zero_iff D (x i j)
    rw [key, ← smul_vec_fin, ← smul_vec_fin, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]
  · have key : x.map (infPart D) = 0 ↔ pairA D.host.F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPart_eq_zero_iff D (x i j)
    rw [key, ← smul_vec_inf, ← smul_vec_inf, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]

end GlobalTheory.AdelicCoord

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepPartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts : ∀ (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N), Continuous e ∧ Continuous e.symm ∧ (∀ x, x.map (finPart D) = 0 ↔ GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧ (∀ x, x.map (infPart D) = 0 ↔ GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  first | exact @GlobalTheory.AdelicCoord.coord | exact GlobalTheory.AdelicCoord.coord | (intros; apply GlobalTheory.AdelicCoord.coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompGlInvHaar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.SiegelCov

section Gen

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR

theorem chi_adele (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    (addEquivAddHaarChar (mulVecCE M hM) : ℝ) =
      (modu (Ainf F) (fstA F M.det) : ℝ) * ∏ᶠ v, ‖evalV F v (sndA F M.det)‖ := by
  classical
  let Mi : Matrix κ κ (Ainf F) := (fstA F).toRingHom.mapMatrix M
  let Mf : Matrix κ κ (Af F) := (sndA F).toRingHom.mapMatrix M
  have hi : Mi.det = fstA F M.det := (RingHom.map_det _ _).symm
  have hf : Mf.det = sndA F M.det := (RingHom.map_det _ _).symm
  have hMi : IsUnit Mi.det := hi ▸ hM.map (fstA F)
  have hMf : IsUnit Mf.det := hf ▸ hM.map (sndA F)
  let j : (κ → Ainf F) × (κ → Af F) →+ (κ → AF F) := zipHom κ (Ainf F) (Af F)
  have hj : IsOpenEmbedding j := GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs κ (Ainf F) (Af F)
  have s1 : addEquivAddHaarChar (mulVecCE M hM) =
      addEquivAddHaarChar (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) :=
    GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ j hj (mulVecCE M hM) (prodCE (mulVecCE Mi hMi) (mulVecCE Mf hMf)) fun p => by
      funext i
      show (M *ᵥ j p) i = ((Mi *ᵥ p.1) i, (Mf *ᵥ p.2) i)
      have e1 : fstA F ((M *ᵥ j p) i) = (Mi *ᵥ p.1) i := by
        rw [show (fstA F) ((M *ᵥ j p) i) = (fstA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      have e2 : sndA F ((M *ᵥ j p) i) = (Mf *ᵥ p.2) i := by
        rw [show (sndA F) ((M *ᵥ j p) i) = (sndA F).toRingHom ((M *ᵥ j p) i) from rfl, RingHom.map_mulVec]
        rfl
      rw [← e1, ← e2]
      rfl
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  haveI : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ v : InfinitePlace F, v.Completion))
  have s2 : addEquivAddHaarChar (mulVecCE Mi hMi) = modu (Ainf F) Mi.det :=
    GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced (Ainf F) inferInstance inferInstance κ Mi hMi
  rw [s1, GlobalTheory.T.addEquivAddHaarChar_prodCongr, NNReal.coe_mul, s2, chi_Af F Mf hMf, hi, hf]

theorem addEquivAddHaarChar_mulVecCE_adele (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    addEquivAddHaarChar (mulVecCE M hM) = distribHaarChar (AF F) hM.unit := by
  let N : Matrix Unit Unit (AF F) := fun _ _ => M.det
  have hdet : N.det = M.det := Matrix.det_unique N
  have hN : IsUnit N.det := hdet ▸ hM
  have htr := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (GlobalTheory.ModuNorm.evalUnitCE (AF F)) (mulVecCE N hN)
  have hext : ((GlobalTheory.ModuNorm.evalUnitCE (AF F)).symm.trans (mulVecCE N hN)).trans (GlobalTheory.ModuNorm.evalUnitCE (AF F)) =
      GlobalTheory.ModuNorm.mulUnitCE hM.unit := by
    ext x
    show (N *ᵥ fun _ => x) () = M.det * x
    simp [Matrix.mulVec, dotProduct, N]
  rw [hext] at htr
  rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar, htr]
  apply NNReal.coe_injective
  rw [chi_adele, chi_adele, hdet]

end Gen

end GlobalTheory.SiegelCov

namespace GlobalTheory.SiegelCov

section Coord

open Matrix GlobalTheory.ModuLR

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)

def vecCoord : (Fin n → AE F E) ≃ₗ[AF F] (Fin n × Fin (Module.finrank F E) → AF F) where
  toFun u p := (tensBasis F E).equivFun (u p.1) p.2
  invFun x i := (tensBasis F E).equivFun.symm fun k => x (i, k)
  left_inv u := by
    funext i
    exact (tensBasis F E).equivFun.symm_apply_apply (u i)
  right_inv x := by
    funext p
    obtain ⟨i, k⟩ := p
    show (tensBasis F E).equivFun ((tensBasis F E).equivFun.symm fun k => x (i, k)) k = x (i, k)
    rw [LinearEquiv.apply_symm_apply]
  map_add' u v := by funext p; simp
  map_smul' c u := by funext p; simp

theorem continuous_vecCoord : Continuous (vecCoord F E n) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hb : Continuous (tensBasis F E).equivFun :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.toLinearMap
  exact continuous_pi fun p => (continuous_apply p.2).comp (hb.comp (continuous_apply p.1))

theorem continuous_vecCoord_symm : Continuous (vecCoord F E n).symm := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hb : Continuous (tensBasis F E).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.symm.toLinearMap
  exact continuous_pi fun i => hb.comp (continuous_pi fun k => continuous_apply (i, k))

def vecCoordCE : (Fin n → AE F E) ≃ₜ+ (Fin n × Fin (Module.finrank F E) → AF F) :=
  { (vecCoord F E n).toAddEquiv with
    continuous_toFun := continuous_vecCoord F E n
    continuous_invFun := continuous_vecCoord_symm F E n }

end Coord

end GlobalTheory.SiegelCov


open GlobalTheory.GaugeEx in
theorem GlobalTheory.SiegelCov.integral_mulVec_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (μ : @Measure (Fin n → AE F E) (borel _)), GlobalTheory.SiegelAvg.IsHaarB μ →
    ∀ (t : GL (Fin n) (AE F E)) (f : (Fin n → AE F E) → ℂ),
      (letI : MeasurableSpace (Fin n → AE F E) := borel _; Integrable f μ) →
      (letI : MeasurableSpace (Fin n → AE F E) := borel _;
        ∫ y, f (((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ y) ∂μ) =
        (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) : ℂ) *
          (letI : MeasurableSpace (Fin n → AE F E) := borel _; ∫ y, f y ∂μ) := by
  intro F E _ _ _ _ _ n μ hμ t f _
  letI : MeasurableSpace (Fin n → AE F E) := borel _
  haveI : BorelSpace (Fin n → AE F E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalAddGroup (AE F E) := IsModuleTopology.isTopologicalAddGroup (AF F) _
  haveI : Module.Free (AF F) (AF F ⊗[F] E) := Module.Free.of_basis (GlobalTheory.ModuLR.tensBasis F E)
  haveI : Module.Finite (AF F) (AF F ⊗[F] E) := Module.Finite.of_basis (GlobalTheory.ModuLR.tensBasis F E)
  let Φ := GlobalTheory.SiegelCov.vecCoordCE F E n
  haveI : LocallyCompactSpace (Fin n → AE F E) := Φ.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fin n → AE F E) := Φ.toHomeomorph.isInducing.secondCountableTopology
  haveI : T2Space (Fin n → AE F E) := Φ.toHomeomorph.isEmbedding.t2Space
  haveI : μ.IsAddHaarMeasure := hμ
  haveI : TopologicalSpace.PseudoMetrizableSpace (Fin n → AE F E) := inferInstance
  haveI : SigmaCompactSpace (Fin n → AE F E) := inferInstance
  haveI : μ.Regular := inferInstance
  set T : Matrix (Fin n) (Fin n) (AE F E) := ((t⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) with hTdef
  have hT : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 (t⁻¹).isUnit
  set L := GlobalTheory.ModuLR.mulVecCE T hT with hL
  set Λ := LinearMap.toMatrix' ((GlobalTheory.SiegelCov.vecCoord F E n).toLinearMap ∘ₗ
    (Matrix.toLin' T).restrictScalars (AF F) ∘ₗ (GlobalTheory.SiegelCov.vecCoord F E n).symm.toLinearMap) with hΛdef
  have hdet : Λ.det = Algebra.norm (AF F) T.det := by
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  have hΛ : IsUnit Λ.det := hdet ▸ hT.map (Algebra.norm (AF F))
  have hc : GlobalTheory.ModuLR.mulVecCE Λ hΛ = (Φ.symm.trans L).trans Φ := by
    ext x
    rw [GlobalTheory.ModuLR.mulVecCE_apply, LinearMap.toMatrix'_mulVec]
    rfl
  have hχ : addEquivAddHaarChar L = distribHaarChar (AF F) hΛ.unit := by
    rw [← GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele, hc, GlobalTheory.ModuLR.addEquivAddHaarChar_transport]
  have hu : hΛ.unit = (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))⁻¹ := by
    ext
    rw [IsUnit.unit_spec, hdet, hTdef]
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have key := addEquivAddHaarChar_smul_map μ L
  set c := addEquivAddHaarChar L with hcdef
  have hc0 : c ≠ 0 := (addEquivAddHaarChar_pos L).ne'
  have hmap : μ.map L = c⁻¹ • μ := by
    calc μ.map L = (c⁻¹ * c) • μ.map L := by rw [inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ y, f (T *ᵥ y) ∂μ = ∫ y, f y ∂(μ.map L) :=
    (integral_map_equiv L.toHomeomorph.toMeasurableEquiv f).symm
  have hmodu : ((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
      (Matrix.GeneralLinearGroup.det t)) : ℝ≥0) = c⁻¹ := by
    rw [hχ, hu, map_inv, inv_inv]
    rfl
  show ∫ y, f (T *ᵥ y) ∂μ = _
  rw [hint, hmap, integral_smul_nnreal_measure, hmodu, NNReal.smul_def, Complex.real_smul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCharpolyEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCharpolyEq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionEll

theorem exists_GL_charpoly_eq : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := by
  intro E _ _ n P hP
  obtain ⟨hm, hn, -, hr⟩ := hP
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : P.coeff 0 ≠ 0 := by
    intro h
    have hroot : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots (hm.map τ).ne_zero, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h, map_zero]
    have := hr τ 0 hroot
    simp at this
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) E, N.charpoly = P := by
    subst hn
    exact ⟨_, (charpoly_leftMulMatrix (AdjoinRoot.powerBasis hm.ne_zero)).trans
      (AdjoinRoot.minpoly_powerBasis_gen_of_monic hm)⟩
  have hd : IsUnit N.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hN]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h0)
  exact ⟨((Matrix.isUnit_iff_isUnit_det N).mpr hd).unit, hN⟩

end GlobalTheory.CompanionEll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCharpolyEqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_charpoly_eq_of_mem_Ell : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := by
  first | exact @GlobalTheory.CompanionEll.exists_GL_charpoly_eq | exact GlobalTheory.CompanionEll.exists_GL_charpoly_eq | (intros; apply GlobalTheory.CompanionEll.exists_GL_charpoly_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddConjEqOneUnramifiedCm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddConjEqOneUnramifiedCm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LatVac

theorem exists_integer_add_conj_eq_one_of_isGood : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.IsGood σ → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ B hB
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
  exact GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance

end GlobalTheory.LatVac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddConjEqOneUnramifiedCmStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_add_conj_eq_one_unramified_cm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.IsGood σ → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  first | exact @GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood | exact GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood | (intros; apply GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDim
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DominantProjDegree

theorem residueDegree_ne_zero_of_map_genericPoint : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X = D → topologicalKrullDim Y = D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 := by
  intro k _ X Y _ _ p q D hp hq hX hY π hπ hη
  obtain ⟨N, i, hi, hcomp⟩ := hp
  obtain ⟨M, j, hj, hcomp'⟩ := hq
  haveI : IsProper (PSpace.str k N) := isProper_str k N
  haveI : IsProper (PSpace.str k M) := isProper_str k M
  haveI : IsProper p := by rw [← hcomp]; infer_instance
  haveI : IsProper (π ≫ p) := by rw [hπ, ← hcomp']; infer_instance
  haveI : IsProper π := IsProper.of_comp π p
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  have hsurj : Surjective π := ⟨fun x => by
    have : genericPoint X ∈ Set.range π := ⟨_, hη⟩
    exact (genericPoint_specializes x).mem_closed hcl this⟩
  exact GlobalTheory.GenFinite.residueDegree_genericPoint_ne_zero k Y X p π D inferInstance inferInstance
    hsurj hY hX

end GlobalTheory.DominantProjDegree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDimStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueDegree_genericPoint_ne_zero_projective_same_dim : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X = D → topologicalKrullDim Y = D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 := by
  first | exact @GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint | exact GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint | (intros; apply GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicRestrictionSubalgebraFrameDomainIsDom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicRestrictionSubalgebraFrameDomainIsDom
namespace GlobalTheory.FlatPair

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem holAlg_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  intro E _ _ _ r X hne
  obtain ⟨y0, hy0⟩ := hne
  haveI : Nontrivial (holAlg X) := ⟨⟨0, 1, fun h => by
    have := congrFun (congrArg Subtype.val h) ⟨y0, hy0⟩
    simp at this⟩⟩
  haveI : NoZeroDivisors (holAlg X) := ⟨fun {a b} hab => by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha, hb⟩ := hcon
    obtain ⟨F, hF, hFa⟩ := a.2
    obtain ⟨G, hG, hGb⟩ := b.2
    have ha' : ∃ y : X.dom, (a : X.dom → ℂ) y ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha (Subtype.ext (funext h))
    obtain ⟨y, hy⟩ := ha'
    have hfg : ∀ w ∈ X.dom, F w * G w = 0 := by
      intro w hw
      have := congrFun (congrArg Subtype.val hab) ⟨w, hw⟩
      rw [← hFa ⟨w, hw⟩, ← hGb ⟨w, hw⟩]
      simpa using this
    have hFy : F y.1 ≠ 0 := by rw [← hFa y]; exact hy
    have key := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hF hG hfg y.2 hFy
    apply hb
    apply Subtype.ext
    funext z
    rw [hGb z]
    simpa using key z.1 z.2⟩
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FlatPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicRestrictionSubalgebraFrameDomainIsDomStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicRestrictionSubalgebraFrameDomain_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  first | exact @GlobalTheory.FlatPair.holAlg_isDomain | exact GlobalTheory.FlatPair.holAlg_isDomain | (intros; apply GlobalTheory.FlatPair.holAlg_isDomain <;> assumption)
end
end
