module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrSubOfIsIrrSubMap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrSubOfIsIrrSubMap
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

namespace GlobalTheory.AbsIrrOfAlgClosed

theorem span_restrict_eq_top_of_isIrrSub_map {k Γ L : Type} [Field k] [Group Γ] [Field L]
    [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W)
    (habs : IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))))) :
    Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  classical
  letI : Algebra k L := f.toAlgebra
  set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ
  let r : Γ → Module.End k W := fun g => (τ g).restrict (hW g)
  have hr1 : r 1 = 1 := by
    ext v; simp [r]
  have hrm : ∀ g h, r (g * h) = r g * r h := by
    intro g h; ext v; simp [r]
  let d := Module.finrank k W
  let e : W ≃ₗ[k] (Fin d → k) := (Module.finBasis k W).equivFun
  let φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k :=
    e.conj.trans LinearMap.toMatrix'
  have hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ
      (e.symm : (Fin d → k) →ₗ[k] W)) := fun _ => rfl
  have hφ1 : φ 1 = 1 := by
    rw [hφa]
    have : (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ
        (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id := LinearMap.ext fun v => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hφm : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    rw [hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun v => by simp
  let S : Γ →* Matrix (Fin d) (Fin d) k :=
    { toFun := fun g => φ (r g)
      map_one' := by rw [hr1, hφ1]
      map_mul' := fun g h => by rw [hrm, hφm] }
  let σ : Γ →* GL (Fin d) k := MonoidHom.toHomUnits S
  have hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g) := fun g => rfl
  let Li : (Fin d → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ e.symm.toLinearMap
  have hLinj : Function.Injective Li := by
    intro x y hxy
    exact e.symm.injective (Subtype.val_injective hxy)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective Li (LinearMap.ker_eq_bot.2 hLinj)
  let B : Matrix (Fin a) (Fin d) k := LinearMap.toMatrix' Li
  let C : Matrix (Fin d) (Fin a) k := LinearMap.toMatrix' L'
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]
  have hBv : ∀ c, B.mulVec c = Li c := fun c => LinearMap.toMatrix'_mulVec Li c
  have hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k) := by
    intro g
    have hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g) := by
      have : τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) :=
        LinearMap.ext fun v => by rw [hτ, GlobalTheory.BurnsideSub.matRep_apply, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix'_toLin']
    rw [hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun c => ?_
    change τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)
    rw [e.symm_apply_apply]
    rfl
  have hspan : Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k))) =
      LinearMap.range (B.map f).mulVecLin := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨f ∘ e ⟨w, hw⟩, ?_⟩
      funext i
      have h1 : B.mulVec (e ⟨w, hw⟩) = w := by
        rw [hBv]
        change ((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w
        rw [e.symm_apply_apply]
      rw [Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]
      rfl
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [op_smul_eq_smul]
      refine Submodule.smul_mem _ _ ?_
      apply Submodule.subset_span
      refine ⟨Li (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩
      funext i
      simp [← hBv, Matrix.mulVec_single_one]
  rw [hspan] at habs
  have hirr : IsIrrSub (mapRep f σ) ⊤ := by
    refine GlobalTheory.BurnsideSub.isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f)
      (C.map f) ?_ ?_ habs
    · rw [← Matrix.map_mul, hCB]
      exact Matrix.map_one _ f.map_zero f.map_one
    · intro g
      change (ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f =
        B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f
      rw [← Matrix.map_mul, ← Matrix.map_mul, hint g]
  have h2 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) =
      fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map (algebraMap k L) := by
    funext g
    ext p q
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]
  rw [h3] at h2
  have h4 := GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2
  have h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r := by
    rw [← Set.range_comp]; rfl
  have h6 := Submodule.map_span φ.toLinearMap (Set.range r)
  change Submodule.span k (Set.range r) = ⊤
  refine Submodule.map_injective_of_injective φ.injective ?_
  rw [h6, Submodule.map_top, LinearEquiv.range]
  rw [h5] at h4
  exact h4

theorem absIrrSub_of_isIrrSub_map : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L]
    (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)), IsInv ρ W →
    IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) →
    AbsIrrSub ρ W := by
  intro k Γ L _ _ _ _ f a ρ W hinv hirr
  have hW : Stable (matRep ((Units.coeHom _).comp ρ)) W := fun g v hv => by
    have := hinv g v hv
    simpa [GlobalTheory.BurnsideSub.matRep_apply] using this
  have hne : W ≠ ⊥ := by
    intro h0
    apply hirr.1
    rw [h0]
    simp
  have hsp := span_restrict_eq_top_of_isIrrSub_map f ρ W hW hirr
  unfold AbsIrrSub
  exact GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top _ ρ W hW hne hsp

end GlobalTheory.AbsIrrOfAlgClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrSubOfIsIrrSubMapStatement
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrSub_of_isIrrSub_span_map : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)), IsInv ρ W → IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) → AbsIrrSub ρ W := by
  first | exact @GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map | exact GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map | (intros; apply GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixSystemNonzeroSolutionDescends
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixSystemNonzeroSolutionDescends
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem matrix_system_nonzero_solution_descends {k L Γ : Type} [Field k] [Field L] (f : k →+* L)
    {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k)
    (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L) :
    C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 →
      ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  intro hC hAB hQ
  letI := f.toAlgebra
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hC (Matrix.ext h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k L, φ (C i₀ j₀) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hij ((Module.forall_dual_apply_eq_zero_iff k (C i₀ j₀)).mp h)
  have key : ∀ (x : k) (y : L), φ (f x * y) = x * φ y := by
    intro x y
    have h1 : f x * y = x • y := (Algebra.smul_def x y).symm
    rw [h1, map_smul, smul_eq_mul]
  have key' : ∀ (x : k) (y : L), φ (y * f x) = φ y * x := by
    intro x y
    rw [mul_comm y, key, mul_comm]
  refine ⟨C.map φ, ?_, ?_, ?_⟩
  · intro h
    apply hφ
    have := congrFun (congrFun h i₀) j₀
    simpa using this
  · intro g
    ext i j
    have := congrArg φ (congrFun (congrFun (hAB g) i) j)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, key'] using this
  · ext i j
    have := congrArg φ (congrFun (congrFun hQ i) j)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, Matrix.zero_apply, map_zero]
      using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixSystemNonzeroSolutionDescendsStatement
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_intertwiner_of_map : ∀ {k L Γ : Type} [Field k] [Field L] (f : k →+* L) {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k) (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L), C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 → ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  first | exact @GlobalTheory.matrix_system_nonzero_solution_descends | exact GlobalTheory.matrix_system_nonzero_solution_descends | (intros; apply GlobalTheory.matrix_system_nonzero_solution_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsolutelyIrreducibleSplitRepOfConstituentMode
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsolutelyIrreducibleSplitRepOfConstituentMode
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.SplitCrit

variable {k L : Type} [Field k] [Field L]

abbrev ext (f : k →+* L) {a : ℕ} (W : Submodule k (Fin a → k)) : Submodule L (Fin a → L) :=
  Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))

theorem map_mulVec_comp (f : k →+* L) {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) (v : Fin n → k) :
    (M.map f).mulVec (f ∘ v) = f ∘ M.mulVec v := by
  funext i; exact (RingHom.map_mulVec f M v i).symm

theorem ext_le_comap (f : k →+* L) {m n : ℕ} (M : Matrix (Fin m) (Fin n) k)
    (U : Submodule k (Fin n → k)) (U' : Submodule k (Fin m → k)) (h : ∀ v ∈ U, M.mulVec v ∈ U') :
    ext f U ≤ (ext f U').comap (M.map f).mulVecLin := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
  rw [map_mulVec_comp]
  exact Submodule.subset_span ⟨_, h v hv, rfl⟩

theorem ext_ne_bot (f : k →+* L) {a : ℕ} {W : Submodule k (Fin a → k)} (hW : W ≠ ⊥) : ext f W ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro h
  have : f ∘ v ∈ ext f W := Submodule.subset_span ⟨v, hv, rfl⟩
  rw [h, Submodule.mem_bot] at this
  apply hv0; funext i
  have := congrFun this i
  simpa using this

theorem finrank_ext_le (f : k →+* L) {a : ℕ} (W : Submodule k (Fin a → k)) :
    Module.finrank L (ext f W) ≤ Module.finrank k W := by
  let e := Module.finBasis k W
  have hle : ext f W ≤ Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v = ∑ i, (e.repr ⟨v, hv⟩ i) • (e i : Fin a → k) := by
      have := congrArg Subtype.val (e.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have : f ∘ v = ∑ i, f (e.repr ⟨v, hv⟩ i) • (f ∘ (e i : Fin a → k)) := by
      conv_lhs => rw [hv']
      funext j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Finset.sum_apply, map_sum]
    show f ∘ v ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  calc Module.finrank L (ext f W)
      ≤ Module.finrank L (Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank k W)) := finrank_range_le_card _
    _ = Module.finrank k W := Fintype.card_fin _

theorem range_ne_bot {K : Type} [Field K] {m n : ℕ} {X : Matrix (Fin m) (Fin n) K} (hX : X ≠ 0) :
    LinearMap.range X.mulVecLin ≠ ⊥ := by
  intro h
  apply hX
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have : X.mulVecLin (Pi.single i 1) ∈ LinearMap.range X.mulVecLin := LinearMap.mem_range_self _ _
  rw [h, Submodule.mem_bot, Matrix.mulVecLin_apply] at this
  rw [this, Matrix.zero_mulVec]

end GlobalTheory.SplitCrit

namespace GlobalTheory.SplitCrit

theorem splitRep_of_models : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), (∀ V, IsIrrSub (mapRep f ρ) V → ∃ (b : ℕ) (σ : Γ →* GL (Fin b) k) (C : Matrix (Fin a) (Fin b) L), Function.Injective C.mulVec ∧ LinearMap.range C.mulVecLin = V ∧ ∀ g, ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * C = C * ((mapRep f σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)) → GlobalTheory.SplitCoef.SplitRep ρ := by
  intro k Γ L _ _ _ _ f a ρ hmod W hW
  obtain ⟨hW0, hWi, hWmin⟩ := hW

  have hLi : IsInv (mapRep f ρ) (ext f W) := fun g v hv =>
    ext_le_comap f (ρ g : Matrix (Fin a) (Fin a) k) W W (hWi g) hv
  obtain ⟨V, hVle, hV⟩ := GlobalTheory.SemisimpleDecomp.exists_irr_le hLi (ext_ne_bot f hW0)
  obtain ⟨b, σ, C, hCinj, hCr, hCint⟩ := hmod V hV

  obtain ⟨W', hc⟩ := Submodule.exists_isCompl W
  let φ : (Fin a → k) →ₗ[k] (Fin a → k) := W'.subtype.comp (W'.projectionOnto W hc.symm)
  have hφ : ∀ v, φ v = 0 ↔ v ∈ W := by
    intro v
    have hk := Submodule.ker_projectionOnto hc.symm
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, ZeroMemClass.coe_eq_zero]
    rw [← LinearMap.mem_ker, hk]
  let Q := LinearMap.toMatrix' φ
  have hQ : ∀ v, Q.mulVec v = 0 ↔ v ∈ W := fun v => by
    simp only [Q, LinearMap.toMatrix'_mulVec]; exact hφ v

  have hQL : ext f W ≤ LinearMap.ker (Q.map f).mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [map_mulVec_comp, (hQ v).2 hv]
    funext i; simp
  have hQC : Q.map f * C = 0 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    have : C.mulVec (Pi.single j 1) ∈ V := hCr ▸ LinearMap.mem_range_self C.mulVecLin _
    have := hQL (hVle this)
    simpa using this
  have hC0 : C ≠ 0 := by
    intro h; apply hV.1; rw [← hCr, h]
    ext x; simp
  have hint : ∀ g, ((ρ g : Matrix (Fin a) (Fin a) k)).map f * C = C * ((σ g : Matrix (Fin b) (Fin b) k)).map f :=
    fun g => hCint g
  obtain ⟨X, hX0, hXint, hQX⟩ := GlobalTheory.T.exists_ne_zero_intertwiner_of_map f (fun g => (ρ g : Matrix (Fin a) (Fin a) k))
    (fun g => (σ g : Matrix (Fin b) (Fin b) k)) Q C hC0 hint hQC

  have hXW : LinearMap.range X.mulVecLin ≤ W := by
    rintro _ ⟨w, rfl⟩
    rw [← hQ, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQX, Matrix.zero_mulVec]
  have hXi : IsInv ρ (LinearMap.range X.mulVecLin) := by
    rintro g _ ⟨w, rfl⟩
    refine ⟨(σ g : Matrix (Fin b) (Fin b) k).mulVec w, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hXint g]
  have hXeq : LinearMap.range X.mulVecLin = W :=
    (hWmin _ hXW hXi).resolve_left (range_ne_bot hX0)
  have hWb : Module.finrank k W ≤ b := by
    rw [← hXeq]
    exact (LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun k).le
  have hVb : Module.finrank L V = b := by
    rw [← hCr, LinearMap.finrank_range_of_inj hCinj, Module.finrank_fin_fun]
  have hVeq : V = ext f W :=
    Submodule.eq_of_le_of_finrank_le hVle ((finrank_ext_le f W).trans (hWb.trans hVb.ge))
  have hV' : IsIrrSub (mapRep f ρ) (ext f W) := hVeq ▸ hV
  exact GlobalTheory.T.absIrrSub_of_isIrrSub_span_map f ρ W hWi hV'

end GlobalTheory.SplitCrit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsolutelyIrreducibleSplitRepOfConstituentModeStatement
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbsolutelyIrreducibleSplitRep_of_constituent_models : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), (∀ V, IsIrrSub (mapRep f ρ) V → ∃ (b : ℕ) (σ : Γ →* GL (Fin b) k) (C : Matrix (Fin a) (Fin b) L), Function.Injective C.mulVec ∧ LinearMap.range C.mulVecLin = V ∧ ∀ g, ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * C = C * ((mapRep f σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)) → GlobalTheory.SplitCoef.SplitRep ρ := by
  first | exact @GlobalTheory.SplitCrit.splitRep_of_models | exact GlobalTheory.SplitCrit.splitRep_of_models | (intros; apply GlobalTheory.SplitCrit.splitRep_of_models <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftRepOfEntriesInImage
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftRepOfEntriesInImage
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem lift_rep_of_entries_in_image : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  intro k L Γ _ _ _ f b τ h
  choose pre hpre using h
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin b) (Fin b) k →+* Matrix (Fin b) (Fin b) L) :=
    Matrix.map_injective f.injective
  have key : ∀ g, f.mapMatrix (Matrix.of (pre g)) = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
    intro g; ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, hpre]
  let m : Γ →* Matrix (Fin b) (Fin b) k :=
    { toFun := fun g => Matrix.of (pre g)
      map_one' := hinj (by rw [key, map_one, map_one]; rfl)
      map_mul' := fun x y => hinj (by rw [map_mul, key, key, key, map_mul]; rfl) }
  refine ⟨MonoidHom.toHomUnits m, ?_⟩
  ext g i j
  simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  rw [MonoidHom.coe_toHomUnits]
  exact congrFun (congrFun (key g) i) j

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftRepOfEntriesInImageStatement
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_lift_of_entries_mem_range : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  first | exact @GlobalTheory.lift_rep_of_entries_in_image | exact GlobalTheory.lift_rep_of_entries_in_image | (intros; apply GlobalTheory.lift_rep_of_entries_in_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImageFiniteMemSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImageFiniteMemSubring
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem image_finite_mem_subring (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) → (↑T ⊆ (R : Set (Qbar l))) → ∀ x : O, iq (algebraMap O (FractionRing O) x) ∈ R := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  refine ⟨s.image (fun x => iq (algebraMap O (FractionRing O) x)), ?_⟩
  intro R hR hT x
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set O) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    exact hT (by simpa using Finset.mem_image_of_mem (fun x => iq (algebraMap O (FractionRing O) x)) hy)
  | zero => simpa using R.zero_mem
  | add a b _ _ ha hb => simpa using R.add_mem ha hb
  | smul c a _ ha =>
    rw [Algebra.smul_def, map_mul, map_mul, hiq]
    exact R.mul_mem (hR c) ha

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImageFiniteMemSubringStatement
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_image_mem_subring : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (iq : FractionRing O →+* Qbar l), (∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) → ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) → (↑T ⊆ (R : Set (Qbar l))) → ∀ x : O, iq (algebraMap O (FractionRing O) x) ∈ R := by
  first | exact @GlobalTheory.image_finite_mem_subring | exact GlobalTheory.image_finite_mem_subring | (intros; apply GlobalTheory.image_finite_mem_subring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstituentImage
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstituentImage
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.ConstituentImage

theorem exists_constituent_image : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ τ₀ : Γ →* GL (Fin a) L) (P : GL (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (P : Matrix (Fin a) (Fin a) L) = (P : Matrix (Fin a) (Fin a) L) * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) → IsSSRep τ → ∀ (Vs : Fin n → Submodule L (Fin a → L)), iSup Vs = ⊤ → (∀ j, IsIrrSub τ₀ (Vs j)) → ∀ V, IsIrrSub τ V → ∃ (j : Fin n) (M : Matrix (Fin a) (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * M = M * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) ∧ Submodule.map M.mulVecLin (Vs j) = V ∧ Disjoint (LinearMap.ker M.mulVecLin) (Vs j) := by
  intro Γ L _ _ a n τ τ₀ P hP hss Vs hVs hirr V hV
  obtain ⟨W', hW'i, hc⟩ := hss V hV.2.1
  set p : (Fin a → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ Submodule.linearProjOfIsCompl V W' hc with hpdef
  have hpV : ∀ x, p x ∈ V := fun x => (Submodule.linearProjOfIsCompl V W' hc x).2
  have hpid : ∀ x ∈ V, p x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩)
  have hp0 : ∀ x ∈ W', p x = 0 := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨x, hx⟩)
  have hcomm : ∀ g v, p ((τ g : Matrix (Fin a) (Fin a) L).mulVec v) = (τ g : Matrix (Fin a) (Fin a) L).mulVec (p v) := by
    intro g v
    set q := v - p v
    have hq : q ∈ W' := by
      rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc, map_sub]
      have := Submodule.linearProjOfIsCompl_apply_left hc ⟨p v, hpV v⟩
      rw [this, sub_eq_zero]; rfl
    have hv : v = p v + q := by simp [q]
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_add, map_add (f := _), hpid _ (hV.2.1 g _ (hpV v)), hp0 _ (hW'i g _ hq), add_zero]
  set π : Matrix (Fin a) (Fin a) L := LinearMap.toMatrix' p with hπ
  have hπv : ∀ v, π.mulVec v = p v := fun v => by simp [hπ, LinearMap.toMatrix'_mulVec]
  have hπc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * π = π * (τ g : Matrix (Fin a) (Fin a) L) := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hπv, hcomm]
  set M : Matrix (Fin a) (Fin a) L := π * (P : Matrix (Fin a) (Fin a) L) with hM
  have hMc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * M = M * (τ₀ g : Matrix (Fin a) (Fin a) L) := by
    intro g
    rw [hM, ← Matrix.mul_assoc, hπc g, Matrix.mul_assoc, hP g, Matrix.mul_assoc]
  have hMv : ∀ g v, (τ g : Matrix (Fin a) (Fin a) L).mulVec (M.mulVec v) = M.mulVec ((τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v) := by
    intro g v
    rw [Matrix.mulVec_mulVec, hMc g, ← Matrix.mulVec_mulVec]
  have hMV : ∀ v, M.mulVec v ∈ V := fun v => by
    rw [hM, ← Matrix.mulVec_mulVec, hπv]; exact hpV _

  have hex : ∃ j, Submodule.map M.mulVecLin (Vs j) ≠ ⊥ := by
    by_contra hne
    push_neg at hne
    obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.1
    have hsup : Submodule.map M.mulVecLin ⊤ = ⊥ := by
      rw [← hVs, Submodule.map_iSup]; simp [hne]
    have hmem : M.mulVec (((P⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x) ∈ Submodule.map M.mulVecLin ⊤ :=
      ⟨_, Submodule.mem_top, rfl⟩
    rw [hsup, Submodule.mem_bot, hM, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (M := (P : Matrix (Fin a) (Fin a) L)),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, hπv, hpid x hxV] at hmem
    exact hx0 hmem
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, M, hMc, ?_, ?_⟩
  · have hinv : IsInv τ (Submodule.map M.mulVecLin (Vs j)) := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨(τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v, (hirr j).2.1 g v hv, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact (hMv g v).symm
    have hle : Submodule.map M.mulVecLin (Vs j) ≤ V := by
      rintro _ ⟨v, _, rfl⟩; exact hMV v
    rcases hV.2.2 _ hle hinv with h | h
    · exact absurd h hj
    · exact h
  · have hinv : IsInv τ₀ (LinearMap.ker M.mulVecLin ⊓ Vs j) := by
      rintro g v ⟨hk, hv⟩
      refine ⟨?_, (hirr j).2.1 g v hv⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk ⊢
      rw [← hMv, hk, Matrix.mulVec_zero]
    rcases (hirr j).2.2 _ inf_le_right hinv with h | h
    · exact disjoint_iff.2 h
    · exfalso
      apply hj
      rw [eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      have hk : v ∈ LinearMap.ker M.mulVecLin := (h ▸ (inf_le_left : LinearMap.ker M.mulVecLin ⊓ Vs j ≤ _)) hv
      simpa using hk

end GlobalTheory.ConstituentImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstituentImageStatement
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_map_eq_of_irrSub : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ τ₀ : Γ →* GL (Fin a) L) (P : GL (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (P : Matrix (Fin a) (Fin a) L) = (P : Matrix (Fin a) (Fin a) L) * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) → IsSSRep τ → ∀ (Vs : Fin n → Submodule L (Fin a → L)), iSup Vs = ⊤ → (∀ j, IsIrrSub τ₀ (Vs j)) → ∀ V, IsIrrSub τ V → ∃ (j : Fin n) (M : Matrix (Fin a) (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * M = M * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) ∧ Submodule.map M.mulVecLin (Vs j) = V ∧ Disjoint (LinearMap.ker M.mulVecLin) (Vs j) := by
  first | exact @GlobalTheory.ConstituentImage.exists_constituent_image | exact GlobalTheory.ConstituentImage.exists_constituent_image | (intros; apply GlobalTheory.ConstituentImage.exists_constituent_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousRingHomFiniteDvrToPadicAlgClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousRingHomFiniteDvrToPadicAlgClosure
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

noncomputable section

namespace GlobalTheory.AdicCont

theorem norm_le_one_of_monic_root_ultra {K : Type} [NormedField K] [IsUltrametricDist K]
    (P : K[X]) (hm : P.Monic) (hc : ∀ i, ‖P.coeff i‖ ≤ 1) {y : K} (hy : P.eval y = 0) : ‖y‖ ≤ 1 := by
  by_contra h
  push_neg at h
  have hn : 0 < P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
    · exfalso
      have h1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm h0
      rw [h1, eval_one] at hy
      exact one_ne_zero hy
    · exact h0
  set n := P.natDegree with hndef
  have hsum := eval_eq_sum_range (p := P) y
  rw [Finset.sum_range_succ, ← hndef, hm.coeff_natDegree, one_mul, hy] at hsum
  have hyn : y ^ n = -∑ i ∈ Finset.range n, P.coeff i * y ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum.symm
  have hle : ‖∑ i ∈ Finset.range n, P.coeff i * y ^ i‖ ≤ ‖y‖ ^ (n - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.1 hi; omega
    calc ‖P.coeff i‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (n - 1) :=
          mul_le_mul (hc i) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = _ := one_mul _
  have h2 : ‖y‖ ^ n ≤ ‖y‖ ^ (n - 1) := by rw [← norm_pow, hyn, norm_neg]; exact hle
  have h3 : ‖y‖ ^ (n - 1) < ‖y‖ ^ n := pow_lt_pow_right₀ h (by omega)
  linarith

theorem continuous_adic (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    Continuous (fun x : O => iq (algebraMap O (FractionRing O) x)) := by
  set f : O →+* Qbar l := iq.comp (algebraMap O (FractionRing O)) with hf
  have hfz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := hiq

  have h1 : ∀ x : O, ‖f x‖ ≤ 1 := by
    intro x
    obtain ⟨p, hpm, hpx⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x
    let g : ℤ_[l] →+* Qbar l := f.comp (algebraMap ℤ_[l] O)
    refine norm_le_one_of_monic_root_ultra (p.map g) (hpm.map g) (fun i => ?_) ?_
    · rw [coeff_map]
      simp only [g, RingHom.comp_apply, hfz, PadicAlgCl.norm_extends]
      exact (p.coeff i).2
    · have := congrArg f hpx
      rw [hom_eval₂, map_zero] at this
      rw [eval_map]
      exact this

  have hlnorm : ‖f (l : O)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : O) ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hlnorm
    have : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hlu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hr : ‖f ϖ‖ < 1 := by
    have he : ϖ ^ e = ((u⁻¹ : Oˣ) : O) * (l : O) := by
      rw [hlu, ← mul_assoc, Units.inv_mul, one_mul]
    have hnorm : ‖f ϖ‖ ^ e ≤ (l : ℝ)⁻¹ := by
      rw [← norm_pow, ← map_pow, he, map_mul, norm_mul, hlnorm]
      calc ‖f ((u⁻¹ : Oˣ) : O)‖ * (l : ℝ)⁻¹ ≤ 1 * (l : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (h1 _) (by positivity)
        _ = _ := one_mul _
    have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    by_contra hge
    push_neg at hge
    have : 1 ≤ ‖f ϖ‖ ^ e := one_le_pow₀ hge
    linarith
  have hcont : ContinuousAt f 0 := by
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hr
    have hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hO).1 n
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx
    rw [dist_zero_right]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    calc ‖f a‖ * ‖f ϖ‖ ^ n ≤ 1 * ‖f ϖ‖ ^ n := mul_le_mul_of_nonneg_right (h1 a) (by positivity)
      _ < ε := by rwa [one_mul]
  exact continuous_of_continuousAt_zero f hcont

end GlobalTheory.AdicCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousRingHomFiniteDvrToPadicAlgClosureStatement
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_ringHom_finite_dvr_to_padicAlgClosure : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ iq : FractionRing O →+* Qbar l, (∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) → Continuous (fun x : O => iq (algebraMap O (FractionRing O) x)) := by
  first | exact @GlobalTheory.AdicCont.continuous_adic | exact GlobalTheory.AdicCont.continuous_adic | (intros; apply GlobalTheory.AdicCont.continuous_adic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseRestrictStableSubmoduleMatrixRe
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseRestrictStableSubmoduleMatrixRe
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.StableSubMat

theorem exists_restrict {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (V : Submodule L (Fin a → L)) (hV : IsInv τ V) :
    ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L),
      D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧
      ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) =
          D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧
        ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E =
          E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  classical
  set b := Module.finrank L V
  let f : (Fin b → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ (Module.finBasis L V).equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp (Module.finBasis L V).equivFun.symm.injective
  have hfr : LinearMap.range f = V := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨g₀, hg₀⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  set E : Matrix (Fin a) (Fin b) L := LinearMap.toMatrix' f with hE
  set D : Matrix (Fin b) (Fin a) L := LinearMap.toMatrix' g₀ with hD
  have hEf : E.mulVecLin = f := by rw [hE]; exact Matrix.toLin'_toMatrix' f
  have hDf : D.mulVecLin = g₀ := by rw [hD]; exact Matrix.toLin'_toMatrix' g₀
  have hDE : D * E = 1 := by
    rw [hD, hE, ← LinearMap.toMatrix'_comp, hg₀, LinearMap.toMatrix'_id]
  have hrange : LinearMap.range E.mulVecLin = V := by rw [hEf, hfr]

  have hED : ∀ v ∈ V, (E * D).mulVec v = v := by
    intro v hv
    rw [← hfr] at hv
    obtain ⟨w, rfl⟩ := hv
    rw [← Matrix.mulVec_mulVec]
    have h1 : D.mulVec (f w) = g₀ (f w) := by rw [← hDf]; rfl
    have h2 : ∀ u, E.mulVec u = f u := fun u => by rw [← hEf]; rfl
    rw [h1, h2, ← LinearMap.comp_apply g₀ f, hg₀, LinearMap.id_apply]
  have key : ∀ g, E * D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E =
      ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E := by
    intro g
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mul_assoc (E * D), ← Matrix.mulVec_mulVec (M := E * D)]
    apply hED
    rw [← Matrix.mulVec_mulVec]
    apply hV
    rw [← hrange]
    exact ⟨x, rfl⟩
  let σm : Γ →* Matrix (Fin b) (Fin b) L :=
    { toFun := fun g => D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E
      map_one' := by simp [hDE]
      map_mul' := by
        intro g h
        simp only [map_mul, Units.val_mul]
        have k := key h
        simp only [Matrix.mul_assoc] at k ⊢
        rw [k] }
  refine ⟨b, E, D, σm.toHomUnits, hDE, hrange, fun g => ⟨?_, ?_⟩⟩
  · rw [MonoidHom.coe_toHomUnits]; rfl
  · rw [MonoidHom.coe_toHomUnits]
    change _ = E * (D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E)
    have k := key g
    simp only [Matrix.mul_assoc] at k ⊢
    exact k.symm

end GlobalTheory.StableSubMat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseRestrictStableSubmoduleMatrixReStatement
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep : ∀ {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (V : Submodule L (Fin a → L)), IsInv τ V → ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L), D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧ ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) = D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E = E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  first | exact @GlobalTheory.StableSubMat.exists_restrict | exact GlobalTheory.StableSubMat.exists_restrict | (intros; apply GlobalTheory.StableSubMat.exists_restrict <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section
namespace GlobalTheory.OSplitCore

theorem mem_mul_of_mem {A : Type} [CommRing A] (R : Subring A) {m n q : ℕ} (X : Matrix (Fin m) (Fin n) A)
    (Y : Matrix (Fin n) (Fin q) A) (hX : ∀ i j, X i j ∈ R) (hY : ∀ i j, Y i j ∈ R) :
    ∀ i j, (X * Y) i j ∈ R := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => R.mul_mem (hX _ _) (hY _ _)

theorem coe_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) = ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f :=
  rfl

theorem mapped_props (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ}
    (U : Set Γ) (p : Γ → ℂ[X]) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O]
    (hadic : IsAdic (IsLocalRing.maximalIdeal O)) (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (r : Γ →* GL (Fin a) O) (hr : Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)))
    (hss : IsSSRep (mapRep (algebraMap O (FractionRing O)) r))
    (hp : ∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map
      (ι.toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) :
    IsSSRep (mapRep iq (mapRep (algebraMap O (FractionRing O)) r)) ∧
    Continuous (fun g => ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l))) ∧
    (∀ σ ∈ U, ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) σ : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) ∧
    ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) →
      (↑T ⊆ (R : Set (Qbar l))) → ∀ g i j,
      ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
        Matrix (Fin a) (Fin a) (Qbar l)) i j ∈ R := by
  have hcz : CharZero (FractionRing O) := ⟨fun m n h => by
    have := congrArg iq h
    simpa using this⟩
  have hcoe : ∀ g, ((mapRep iq (mapRep (algebraMap O (FractionRing O)) r) g : GL (Fin a) (Qbar l)) :
      Matrix (Fin a) (Fin a) (Qbar l)) =
      ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map (iq.comp (algebraMap O (FractionRing O))) := by
    intro g
    rw [coe_mapRep, coe_mapRep, Matrix.map_map]
    rfl
  refine ⟨GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ iq a _ hss, ?_, ?_, ?_⟩
  · simp only [hcoe]
    exact hr.matrix_map (GlobalTheory.T.continuous_ringHom_finite_dvr_to_padicAlgClosure l O hadic iq hiq)
  · intro σ hσ
    rw [hcoe, Matrix.charpoly_map, Polynomial.map_map]
    exact hp σ hσ
  · obtain ⟨T, hT⟩ := GlobalTheory.T.exists_finset_image_mem_subring l O iq hiq
    refine ⟨T, fun R hR hTR g i j => ?_⟩
    rw [hcoe]
    exact hT R hR hTR _

theorem exists_splitting_set : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (G E Ω)) (p : G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ (l' : ℕ) [Fact l'.Prime] (h : l = l') (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l'] O] [Module.Finite ℤ_[l'] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ iq : FractionRing O →+* Qbar l', (∀ z : ℤ_[l'], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l'] O z)) = algebraMap ℚ_[l'] (Qbar l') (z : ℚ_[l'])) → (∀ z ∈ S, ∃ x, qCast h ι (iq x) = z) → ∀ r : G E Ω →* GL (Fin a) O, Continuous (fun g => ((r g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) → IsSSRep (mapRep (algebraMap O (FractionRing O)) r) → (∀ σ ∈ U, ((r σ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).charpoly.map ((qCast h ι).toRingHom.comp (iq.comp (algebraMap O (FractionRing O)))) = p σ) → GlobalTheory.SplitCoef.SplitRep (mapRep (algebraMap O (FractionRing O)) r) := by
  intro l _ ι E Ω _ _ _ _ _ a U p hU
  classical
  by_cases hex : ∃ (ρ₀ : G E Ω →* GL (Fin a) (Qbar l)) (T : Finset (Qbar l)), IsSSRep ρ₀ ∧
      Continuous (fun g => ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      (∀ σ ∈ U, ((ρ₀ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) ∧
      ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) →
        (↑T ⊆ (R : Set (Qbar l))) → ∀ g i j, ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) i j ∈ R
  swap
  · refine ⟨∅, ?_⟩
    intro l' _ h O _ _ _ _ _ _ _ hadic iq hiq _ r hr hss hp
    subst h
    exfalso
    obtain ⟨h1, h2, h3, T, h4⟩ := mapped_props l ι U p O hadic iq hiq r hr hss hp
    exact hex ⟨_, T, h1, h2, h3, h4⟩
  obtain ⟨ρ₀, T, hss₀, hc₀, hp₀, hT⟩ := hex
  obtain ⟨n, Vs, hint, hirr⟩ := GlobalTheory.semisimple_matrix_rep_decomp ρ₀ hss₀
  choose b E D σ₀ hDE hran hσ₀ using fun j => GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep ρ₀ (Vs j) (hirr j).2.1
  let T' : Finset (Qbar l) := T ∪ Finset.univ.biUnion (fun j : Fin n =>
    Finset.univ.image (fun ij : Fin a × Fin (b j) => E j ij.1 ij.2) ∪
      Finset.univ.image (fun ij : Fin (b j) × Fin a => D j ij.1 ij.2))
  refine ⟨T'.image ι, ?_⟩
  intro l' _ h O _ _ _ _ _ _ _ hadic iq hiq hS r hr hss hp
  subst h
  obtain ⟨hss', hc', hp', -⟩ := mapped_props l ι U p O hadic iq hiq r hr hss hp
  have hT'R : ∀ t ∈ T', t ∈ iq.range := by
    intro t ht
    obtain ⟨x, hx⟩ := hS (ι t) (Finset.mem_image_of_mem _ ht)
    exact ⟨x, ι.injective hx⟩
  have hRz : ∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ iq.range := fun z => ⟨_, hiq z⟩
  have hTR : (↑T : Set (Qbar l)) ⊆ (iq.range : Set (Qbar l)) := fun t ht => hT'R t (Finset.mem_union_left _ ht)
  have hER : ∀ j i s, E j i s ∈ iq.range := fun j i s => hT'R _ (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun ij : Fin a × Fin (b j) => E j ij.1 ij.2) (Finset.mem_univ (i, s)))⟩))
  have hDR : ∀ j i s, D j i s ∈ iq.range := fun j i s => hT'R _ (Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (b j) × Fin a => D j ij.1 ij.2) (Finset.mem_univ (i, s)))⟩))
  have hρ₀R := hT iq.range hRz hTR
  set ρ := mapRep (algebraMap O (FractionRing O)) r with hρ
  have hcp : ∀ g, ((mapRep iq ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
    GlobalTheory.T.charpoly_eq_of_continuous_of_eq_on_dense _ _ hc' hc₀ U hU fun x hx =>
      Polynomial.map_injective _ ι.injective (by rw [hp' x hx, hp₀ x hx])
  obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix (mapRep iq ρ) ρ₀ hss' hss₀ hcp
  have hint' : ∀ g, ((mapRep iq ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) *
      (Pm : Matrix (Fin a) (Fin a) (Qbar l)) =
      (Pm : Matrix (Fin a) (Fin a) (Qbar l)) * ((ρ₀ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g
    rw [hPm g]
    simp only [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  apply GlobalTheory.T.isAbsolutelyIrreducibleSplitRep_of_constituent_models iq ρ
  intro V hV
  obtain ⟨j, M, hM, hMV, hMd⟩ := GlobalTheory.T.exists_intertwiner_map_eq_of_irrSub (mapRep iq ρ) ρ₀ Pm hint' hss' Vs
    hint.submodule_iSup_eq_top hirr V hV
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_rep_lift_of_entries_mem_range iq (σ₀ j) fun g i s => by
    have : ((σ₀ j g : GL (Fin (b j)) (Qbar l)) : Matrix (Fin (b j)) (Fin (b j)) (Qbar l)) i s ∈ iq.range := by
      rw [(hσ₀ j g).1]
      exact mem_mul_of_mem _ _ _ (mem_mul_of_mem _ _ _ (hDR j) (hρ₀R g)) (hER j) i s
    exact this
  refine ⟨b j, σ, M * E j, ?_, ?_, ?_⟩
  · intro v w hvw
    simp only [← Matrix.mulVec_mulVec] at hvw
    have hv : (E j).mulVec v ∈ Vs j := hran j ▸ ⟨v, rfl⟩
    have hw : (E j).mulVec w ∈ Vs j := hran j ▸ ⟨w, rfl⟩
    have hsub : (E j).mulVec v - (E j).mulVec w ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 hvw
    have h0 := hMd.le_bot ⟨hsub, Submodule.sub_mem _ hv hw⟩
    have hEq : (E j).mulVec v = (E j).mulVec w := sub_eq_zero.1 h0
    have := congrArg (D j).mulVec hEq
    simpa [Matrix.mulVec_mulVec, hDE j] using this
  · rw [Matrix.mulVecLin_mul, LinearMap.range_comp, hran j, hMV]
  · intro g
    rw [hσ, ← Matrix.mul_assoc, hM g, Matrix.mul_assoc, (hσ₀ j g).2, Matrix.mul_assoc]

end GlobalTheory.OSplitCore
