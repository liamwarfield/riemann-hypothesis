module

public import GroundTheory.AutomorphicForms.Reduction
public import GroundTheory.AutomorphicForms.GKModules.GKModule
public import GroundTheory.AutomorphicForms.HarishChandraRegularity

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

section Local

variable {E : Type*} [NormedField E] {n : ℕ}

def locHeight (g : GL (Fin n) E) : ℝ :=
  max 1 ((Finset.univ.sup fun p : Fin n × Fin n =>
    max ‖(g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊
      ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊ : ℝ≥0) : ℝ)

theorem one_le_locHeight (g : GL (Fin n) E) : 1 ≤ locHeight g := le_max_left _ _

theorem locHeight_pos (g : GL (Fin n) E) : 0 < locHeight g :=
  lt_of_lt_of_le one_pos (one_le_locHeight g)

theorem norm_apply_le_locHeight (g : GL (Fin n) E) (i j : Fin n) :
    ‖(g : Matrix (Fin n) (Fin n) E) i j‖ ≤ locHeight g := by
  refine le_trans ?_ (le_max_right _ _)
  have := Finset.le_sup (f := fun p : Fin n × Fin n =>
    max ‖(g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊
      ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) (Finset.mem_univ (i, j))
  exact le_trans (le_max_left _ _) (NNReal.coe_le_coe.2 this)

theorem norm_inv_apply_le_locHeight (g : GL (Fin n) E) (i j : Fin n) :
    ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ locHeight g := by
  refine le_trans ?_ (le_max_right _ _)
  have := Finset.le_sup (f := fun p : Fin n × Fin n =>
    max ‖(g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊
      ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) (Finset.mem_univ (i, j))
  exact le_trans (le_max_right _ _) (NNReal.coe_le_coe.2 this)

theorem locHeight_le {g : GL (Fin n) E} {c : ℝ} (hc : 1 ≤ c)
    (h₁ : ∀ i j, ‖(g : Matrix (Fin n) (Fin n) E) i j‖ ≤ c)
    (h₂ : ∀ i j, ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ c) :
    locHeight g ≤ c := by
  refine max_le hc ?_
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have : (Finset.univ.sup fun p : Fin n × Fin n =>
      max ‖(g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊
        ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) ≤ ⟨c, hc0⟩ :=
    Finset.sup_le fun p _ => max_le (h₁ p.1 p.2) (h₂ p.1 p.2)
  exact this

theorem locHeight_inv (g : GL (Fin n) E) : locHeight g⁻¹ = locHeight g := by
  refine le_antisymm (locHeight_le (one_le_locHeight g) (fun i j => norm_inv_apply_le_locHeight g i j)
    fun i j => ?_) (locHeight_le (one_le_locHeight _) (fun i j => ?_) fun i j => ?_)
  · rw [inv_inv]; exact norm_apply_le_locHeight g i j
  · have := norm_inv_apply_le_locHeight g⁻¹ i j
    rwa [inv_inv] at this
  · exact norm_apply_le_locHeight g⁻¹ i j

theorem locHeight_one : locHeight (1 : GL (Fin n) E) = 1 := by
  refine le_antisymm (locHeight_le le_rfl (fun i j => ?_) fun i j => ?_) (one_le_locHeight _)
  · simp only [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
  · simp only [inv_one, Units.val_one, Matrix.one_apply]; split_ifs <;> simp

theorem norm_mul_apply_le (a b : Matrix (Fin n) (Fin n) E) {A B : ℝ} (hA : ∀ i j, ‖a i j‖ ≤ A)
    (hB : ∀ i j, ‖b i j‖ ≤ B) (hA0 : 0 ≤ A) (i j : Fin n) : ‖(a * b) i j‖ ≤ n * (A * B) := by
  rw [Matrix.mul_apply]
  calc ‖∑ k, a i k * b k j‖ ≤ ∑ k, ‖a i k * b k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, A * B := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]; exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hA0
    _ = n * (A * B) := by simp

theorem locHeight_mul_le (g h : GL (Fin n) E) :
    locHeight (g * h) ≤ max 1 (n : ℝ) * locHeight g * locHeight h := by
  have hg := one_le_locHeight g
  have hh := one_le_locHeight h
  have hn : (1 : ℝ) ≤ max 1 (n : ℝ) := le_max_left _ _
  have h1 : 1 ≤ max 1 (n : ℝ) * locHeight g * locHeight h := by
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hn hg zero_le_one (le_trans zero_le_one hn)) hh zero_le_one
          (by positivity)
  have key : ∀ (a b : Matrix (Fin n) (Fin n) E) (A B : ℝ), (∀ i j, ‖a i j‖ ≤ A) →
      (∀ i j, ‖b i j‖ ≤ B) → 1 ≤ A → 1 ≤ B → ∀ i j, ‖(a * b) i j‖ ≤ max 1 (n : ℝ) * A * B := by
    intro a b A B hA hB hA1 hB1 i j
    refine le_trans (norm_mul_apply_le a b hA hB (le_trans zero_le_one hA1) i j) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  refine locHeight_le h1 (fun i j => ?_) fun i j => ?_
  · rw [Units.val_mul]
    exact key _ _ _ _ (norm_apply_le_locHeight g) (norm_apply_le_locHeight h) hg hh i j
  · rw [mul_inv_rev, Units.val_mul]
    have := key _ _ _ _ (norm_inv_apply_le_locHeight h) (norm_inv_apply_le_locHeight g) hh hg i j
    rwa [mul_right_comm] at this

theorem locHeight_mul_le_of_ultrametric [IsUltrametricDist E] (g h : GL (Fin n) E) :
    locHeight (g * h) ≤ locHeight g * locHeight h := by
  have hg := one_le_locHeight g
  have hh := one_le_locHeight h
  have key : ∀ (a b : Matrix (Fin n) (Fin n) E) (A B : ℝ), (∀ i j, ‖a i j‖ ≤ A) →
      (∀ i j, ‖b i j‖ ≤ B) → 1 ≤ A → 1 ≤ B → ∀ i j, ‖(a * b) i j‖ ≤ A * B := by
    intro a b A B hA hB hA1 hB1 i j
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (le_trans zero_le_one hA1)
  refine locHeight_le (one_le_mul_of_one_le_of_one_le hg hh) (fun i j => ?_) fun i j => ?_
  · rw [Units.val_mul]
    exact key _ _ _ _ (norm_apply_le_locHeight g) (norm_apply_le_locHeight h) hg hh i j
  · rw [mul_inv_rev, Units.val_mul, mul_comm (locHeight g)]
    exact key _ _ _ _ (norm_inv_apply_le_locHeight h) (norm_inv_apply_le_locHeight g) hh hg i j

theorem locHeight_eq_one {g : GL (Fin n) E}
    (h₁ : ∀ i j, ‖(g : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1)
    (h₂ : ∀ i j, ‖((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1) :
    locHeight g = 1 :=
  le_antisymm (locHeight_le le_rfl h₁ h₂) (one_le_locHeight g)

end Local

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

theorem locHeight_eq_one_of_mem_integralGL {v : HeightOneSpectrum (𝓞 K)}
    {g : GL (Fin n) (v.adicCompletion K)}
    (hg : g ∈ GLnLocal.integralGL (v.adicCompletion K) n) : locHeight g = 1 := by
  rw [GLnLocal.mem_integralGL_iff] at hg
  simp only [GroundTheory.Global.mem_valuationInteger_iff] at hg
  exact locHeight_eq_one (fun i j => norm_le_one_of_mem v (hg.1 i j))
    fun i j => norm_le_one_of_mem v (hg.2 i j)

theorem finite_mulSupport_locHeight_finAt (g : AdelicGLn.AdelicGL K n) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => locHeight (finAt v g)).Finite := by
  have : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, locHeight (finAt v g) = 1 :=
    (AdelicGLn.eventually_mem_integralGL K n g).mono fun v hv =>
      locHeight_eq_one_of_mem_integralGL (g := finAt v g) hv
  exact Filter.eventually_cofinite.1 this

def height (g : AdelicGLn.AdelicGL K n) : ℝ :=
  (∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult) *
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g)

theorem one_le_finprod_locHeight (g : AdelicGLn.AdelicGL K n) :
    1 ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g) :=
  finprod_induction (fun x : ℝ => 1 ≤ x) le_rfl (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy)
    fun _ => one_le_locHeight _

theorem one_le_prod_locHeight (g : AdelicGLn.AdelicGL K n) :
    1 ≤ ∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult :=
  Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy)
    le_rfl fun _ _ => one_le_pow₀ (one_le_locHeight _)

theorem one_le_height (g : AdelicGLn.AdelicGL K n) : 1 ≤ height g :=
  one_le_mul_of_one_le_of_one_le (one_le_prod_locHeight g) (one_le_finprod_locHeight g)

theorem height_pos (g : AdelicGLn.AdelicGL K n) : 0 < height g :=
  lt_of_lt_of_le one_pos (one_le_height g)

theorem height_inv (g : AdelicGLn.AdelicGL K n) : height g⁻¹ = height g := by
  simp only [height, infAt_inv, finAt_inv, locHeight_inv]

theorem height_one : height (1 : AdelicGLn.AdelicGL K n) = 1 := by
  simp [height, locHeight_one]


variable (K n) in
def heightConst : ℝ := ∏ w : InfinitePlace K, (max 1 (n : ℝ)) ^ w.mult

theorem one_le_heightConst : 1 ≤ heightConst K n :=
  Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy)
    le_rfl fun _ _ => one_le_pow₀ (le_max_left _ _)

theorem height_mul_le (g h : AdelicGLn.AdelicGL K n) :
    height (g * h) ≤ heightConst K n * height g * height h := by
  classical
  set s := ((finite_mulSupport_locHeight_finAt g).union
    (finite_mulSupport_locHeight_finAt h)).union (finite_mulSupport_locHeight_finAt (g * h))
  have hfin : ∀ x : AdelicGLn.AdelicGL K n, x = g ∨ x = h ∨ x = g * h →
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v x) =
        ∏ v ∈ s.toFinset, locHeight (finAt v x) := by
    intro x hx
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro v hv
    simp only [Set.Finite.coe_toFinset, Set.mem_union]
    rcases hx with rfl | rfl | rfl
    · exact Or.inl (Or.inl hv)
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv
  have hf : ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v (g * h)) ≤
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g)) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v h) := by
    rw [hfin _ (Or.inr (Or.inr rfl)), hfin _ (Or.inl rfl), hfin _ (Or.inr (Or.inl rfl)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => (locHeight_pos _).le) fun v _ => ?_
    rw [finAt_mul]
    exact locHeight_mul_le_of_ultrametric _ _
  have hi : (∏ w : InfinitePlace K, locHeight (infAt w (g * h)) ^ w.mult) ≤
      heightConst K n * (∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult) *
        ∏ w : InfinitePlace K, locHeight (infAt w h) ^ w.mult := by
    rw [heightConst, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun w _ => by have := locHeight_pos (infAt w (g * h)); positivity)
      fun w _ => ?_
    rw [← mul_pow, ← mul_pow, infAt_mul]
    exact pow_le_pow_left₀ (locHeight_pos _).le (locHeight_mul_le _ _) _
  unfold height
  calc (∏ w : InfinitePlace K, locHeight (infAt w (g * h)) ^ w.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v (g * h))
      ≤ (heightConst K n * (∏ w : InfinitePlace K, locHeight (infAt w g) ^ w.mult) *
          ∏ w : InfinitePlace K, locHeight (infAt w h) ^ w.mult) *
        ((∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g)) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v h)) :=
        mul_le_mul hi hf (le_trans zero_le_one (one_le_finprod_locHeight _))
          (mul_nonneg (mul_nonneg (le_trans zero_le_one one_le_heightConst)
            (le_trans zero_le_one (one_le_prod_locHeight g)))
            (le_trans zero_le_one (one_le_prod_locHeight h)))
    _ = _ := by ring

theorem locHeight_infAt_eq_one_of_mem_maxCompact {k : AdelicGLn.AdelicGL K n}
    (hk : k ∈ Reduction.maxCompact) (w : InfinitePlace K) : locHeight (infAt w k) = 1 := by
  have h1 : infAt w k ∈ archCompact w := hk.1 w
  have h2 : (infAt w k)⁻¹ ∈ archCompact w := inv_mem h1
  exact locHeight_eq_one (fun i j => norm_apply_le_one_of_mem_archCompact h1 i j)
    fun i j => norm_apply_le_one_of_mem_archCompact h2 i j

theorem locHeight_finAt_eq_one_of_mem_maxCompact {k : AdelicGLn.AdelicGL K n}
    (hk : k ∈ Reduction.maxCompact) (v : HeightOneSpectrum (𝓞 K)) : locHeight (finAt v k) = 1 :=
  locHeight_eq_one_of_mem_integralGL (hk.2 v)

theorem height_eq_one_of_mem_maxCompact {k : AdelicGLn.AdelicGL K n} (hk : k ∈ Reduction.maxCompact) :
    height k = 1 := by
  unfold height
  rw [Finset.prod_eq_one fun w _ => by
    rw [locHeight_infAt_eq_one_of_mem_maxCompact hk w, one_pow], one_mul]
  exact finprod_eq_one_of_forall_eq_one (locHeight_finAt_eq_one_of_mem_maxCompact hk)

end AutomorphicForm

end

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
open NumberField NumberField.mixedEmbedding IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

def ArchMatrix : Type _ := Matrix (Fin n) (Fin n) (mixedSpace K)

open scoped Classical in
instance : NormedRing (ArchMatrix K n) := Matrix.linftyOpNormedRing

open scoped Classical in
instance : NormedAlgebra ℝ (ArchMatrix K n) := Matrix.linftyOpNormedAlgebra

instance : FiniteDimensional ℝ (ArchMatrix K n) := by
  change FiniteDimensional ℝ (Matrix (Fin n) (Fin n) (mixedSpace K)); infer_instance

instance : CompleteSpace (ArchMatrix K n) := FiniteDimensional.completeSpace ℝ _

abbrev archGroup : Subgroup (ArchMatrix K n)ˣ := ⊤

abbrev archLie : Submodule ℝ (ArchMatrix K n) := ⊤

instance : NormedAddCommGroup (archLie K n) := Submodule.normedAddCommGroup _

instance : NormedSpace ℝ (archLie K n) := Submodule.normedSpace _

theorem isExpLieAlgebra : IsExpLieAlgebra (archGroup K n) (archLie K n) := by
  refine ⟨fun _ _ => Subgroup.mem_top _, ?_⟩
  exact ⟨(expPartialHomeomorph ℝ (ArchMatrix K n)).source,
    (expPartialHomeomorph ℝ (ArchMatrix K n)).open_source,
    zero_mem_expPartialHomeomorph_source ℝ _, Set.Subset.rfl, fun _ _ _ => Submodule.mem_top⟩

def archMatrixEquiv : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ≃+* ArchMatrix K n :=
  RingEquiv.mapMatrix (m := Fin n) (InfiniteAdeleRing.ringEquiv_mixedSpace K)

theorem archMatrixEquiv_apply (M : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) (a b : Fin n) :
    (archMatrixEquiv K n M : Matrix (Fin n) (Fin n) (mixedSpace K)) a b =
      InfiniteAdeleRing.ringEquiv_mixedSpace K (M a b) :=
  rfl

theorem continuous_archMatrixEquiv : Continuous (archMatrixEquiv K n) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) =>
    M.map (GroundTheory.Global.homeomorphMixedSpace K)
  exact continuous_id.matrix_map (GroundTheory.Global.homeomorphMixedSpace K).continuous

theorem continuous_archMatrixEquiv_symm : Continuous (archMatrixEquiv K n).symm := by
  have he : ⇑(GroundTheory.Global.homeomorphMixedSpace K).symm =
      ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
    funext x
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [RingEquiv.apply_symm_apply, ← GroundTheory.Global.homeomorphMixedSpace_apply,
      Homeomorph.apply_symm_apply]
  change Continuous fun M : Matrix (Fin n) (Fin n) (mixedSpace K) =>
    M.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
  rw [← he]
  exact continuous_id.matrix_map (GroundTheory.Global.homeomorphMixedSpace K).symm.continuous

def archEquiv : AdelicGLn.InfiniteAdelicGL K n ≃ₜ* archGroup K n :=
  (unitsCongr (archMatrixEquiv K n).toMulEquiv (continuous_archMatrixEquiv K n)
    (continuous_archMatrixEquiv_symm K n)).trans
    { toMulEquiv := Subgroup.topEquiv.symm
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }

def infEmb : archGroup K n →* AdelicGLn.AdelicGL K n :=
  (AdelicGLn.prodEquiv K n).symm.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp (archEquiv K n).symm.toMonoidHom)

def finEmb : AdelicGLn.FiniteAdelicGL K n →* AdelicGLn.AdelicGL K n :=
  (AdelicGLn.prodEquiv K n).symm.toMonoidHom.comp (MonoidHom.inr _ _)

variable {K n}

theorem continuous_infEmb : Continuous (infEmb K n) :=
  (AdelicGLn.prodEquiv K n).symm.continuous.comp
    ((continuous_id.prodMk continuous_const).comp (archEquiv K n).symm.continuous)

theorem continuous_finEmb : Continuous (finEmb K n) :=
  (AdelicGLn.prodEquiv K n).symm.continuous.comp (continuous_const.prodMk continuous_id)

theorem prodEquiv_infEmb (x : archGroup K n) :
    AdelicGLn.prodEquiv K n (infEmb K n x) = ((archEquiv K n).symm x, 1) :=
  (AdelicGLn.prodEquiv K n).apply_symm_apply _

theorem prodEquiv_finEmb (y : AdelicGLn.FiniteAdelicGL K n) :
    AdelicGLn.prodEquiv K n (finEmb K n y) = (1, y) :=
  (AdelicGLn.prodEquiv K n).apply_symm_apply _

theorem infEmb_mul_finEmb_comm (x : archGroup K n) (y : AdelicGLn.FiniteAdelicGL K n) :
    infEmb K n x * finEmb K n y = finEmb K n y * infEmb K n x := by
  apply (AdelicGLn.prodEquiv K n).injective
  simp only [map_mul, prodEquiv_infEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]

theorem infEmb_mul_finEmb (g : AdelicGLn.AdelicGL K n) :
    infEmb K n (archEquiv K n (AdelicGLn.prodEquiv K n g).1) *
      finEmb K n (AdelicGLn.prodEquiv K n g).2 = g := by
  apply (AdelicGLn.prodEquiv K n).injective
  simp only [map_mul, prodEquiv_infEmb, prodEquiv_finEmb, ContinuousMulEquiv.symm_apply_apply,
    Prod.mk_mul_mk, mul_one, one_mul]

theorem infEmb_injective : Function.Injective (infEmb K n) := by
  intro x y hxy
  have := congrArg (fun g => (AdelicGLn.prodEquiv K n g).1) hxy
  simpa [prodEquiv_infEmb] using this

theorem finEmb_injective : Function.Injective (finEmb K n) := by
  intro x y hxy
  have := congrArg (fun g => (AdelicGLn.prodEquiv K n g).2) hxy
  simpa [prodEquiv_finEmb] using this

variable (K n)

def archCompact : Subgroup (archGroup K n) := (Reduction.maxCompact (K := K) (n := n)).comap (infEmb K n)

end AutomorphicForm

end

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
namespace GroundTheory.Automorphic

open Sobolev Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_kernel_eq_conv_of_aeval_laplacian [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {ι : Type*} [Fintype ι]
    (bL : Module.Basis ι ℝ h.lieSubalgebra) (P : Polynomial ℂ) (hP : P.Monic) (hPd : 0 < P.natDegree)
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ U ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (h.laplacian bL) P f = 0 →
        ∀ g : G, (f : G → ℂ) g = ∫ y, (f : G → ℂ) (g * y) * κ y ∂μ := by
  let _ := h.chartedSpace
  set b := Module.finBasis ℝ 𝔤
  set d := Module.finrank ℝ 𝔤
  have hfc : ∀ f : h.smoothFuns (F := ℂ), ∀ g : G, Continuous fun y : G => (f : G → ℂ) (g * y) :=
    fun f g => (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous.comp
      (continuous_const.mul continuous_id)
  have hexpc : Continuous fun x : EuclideanSpace ℝ (Fin d) => h.expG (coordEquiv b x) :=
    h.continuous_expG.comp (coordEquiv b).continuous
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_expCoord μ b
  have hV : {x : EuclideanSpace ℝ (Fin d) | h.expG (coordEquiv b x) ∈ U} ∈ 𝓝 0 := by
    refine hexpc.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨ρ₀, hρ₀, hρ₀V⟩ := Metric.mem_nhds_iff.1 hV
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·
    have hsub : ∀ x y : EuclideanSpace ℝ (Fin d), x = y := by
      intro x y; ext i; exact absurd i.2 (by omega)
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens (fun _ => 1) contDiff_const (fun x _ => by
      rw [hsub x 0]; exact Metric.mem_closedBall_self hε.le)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun f _ g => ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact hρ₀V (by rw [hsub x 0]; exact Metric.mem_ball_self hρ₀)
    · have := hκ _ (hfc f g)
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [this, integral_euclideanSpace_of_eq_zero hd]
      simp
  ·
    set Q := P ^ (d + 1)
    have hQ : Q.Monic := hP.pow _
    have hQd : Q.natDegree = (d + 1) * P.natDegree := hP.natDegree_pow _
    obtain ⟨δ, hδ, A, a, hA, ha, hell, hop⟩ := h.exists_elliptic_aeval_laplacian bL b Q hQ
    set ρ := min (min δ ε) ρ₀
    have hρ : 0 < ρ := lt_min (lt_min hδ hε) hρ₀
    have hρδ : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 δ :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
    have hρε : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.closedBall 0 ε :=
      Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_right _ _)))
    have hρV : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 ρ₀ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hm1 : 1 ≤ 2 * Q.natDegree := by rw [hQd]; nlinarith
    have hnm : d < 2 * (2 * Q.natDegree) := by rw [hQd]; nlinarith
    obtain ⟨E, β, -, -, hEs, -, hβs, -, hβU, hid⟩ := exists_parametrix hd hm1 hnm Metric.isOpen_ball
      hA (fun α hα => (ha α hα).contDiffOn Metric.isOpen_ball.uniqueDiffOn) hell Metric.isOpen_ball
      (Metric.mem_ball_self hρ) hρδ
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens β hβs (hβU.trans hρε)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun f hf g => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hρ₀V (hρV (hβU hx))
    · have hQf : Polynomial.aeval (h.laplacian bL) Q f = 0 := by
        rw [show Q = P ^ d * P from pow_succ P d, map_mul, Module.End.mul_apply, hf, map_zero]
      set ψ := fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))
      have hψ : ContDiff ℝ ∞ ψ := h.contDiff_comp_coordEquiv f.2 g b
      have h1 := hid ψ hψ.contDiffOn
      have h0 : ∫ x, E x * diffOp A a ψ x = 0 := by
        rw [← integral_zero (EuclideanSpace ℝ (Fin d)) ℂ]
        congr 1
        funext x
        by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ
        · rw [hop f g x hx, hQf]; simp
        · rw [image_eq_zero_of_notMem_tsupport fun hE => hx (hρδ (hEs hE)), zero_mul]
      rw [h0, eq_comm, sub_eq_zero] at h1
      have hψ0 : ψ 0 = (f : G → ℂ) g := by simp [ψ]
      rw [← hψ0, h1]
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [hκ _ (hfc f g)]

noncomputable def convDeriv (X : 𝔤) (κ : G → ℂ) (y : G) : ℂ :=
  h.rightDeriv X (fun z => κ z⁻¹) y⁻¹

variable {h}

theorem continuous_of_isSmoothFun {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  let _ := h.chartedSpace
  exact ContMDiff.continuous hf

theorem isSmoothFun_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) :
    h.IsSmoothFun (fun z : G => κ z⁻¹) := by
  let _ := h.chartedSpace
  have := h.lieGroup ∞
  exact hκ.comp (contMDiff_inv 𝓘(ℝ, 𝔤) ∞)

theorem continuous_rightDeriv_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (X : 𝔤) :
    Continuous (h.rightDeriv X fun z : G => κ z⁻¹) :=
  continuous_of_isSmoothFun (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)

theorem continuous_convDeriv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (X : 𝔤) :
    Continuous (h.convDeriv X κ) :=
  (continuous_rightDeriv_comp_inv hκ X).comp continuous_inv

theorem rightDeriv_eq_zero_of_eventually {f : G → ℂ} {g : G} (hf : ∀ᶠ z in 𝓝 g, f z = 0)
    (X : 𝔤) : h.rightDeriv X f g = 0 := by
  have hc : Continuous fun Y : 𝔤 => g * h.expG Y := continuous_const.mul h.continuous_expG
  have h0 : (fun Y : 𝔤 => f (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have : Tendsto (fun Y : 𝔤 => g * h.expG Y) (𝓝 0) (𝓝 g) := by
      simpa using hc.tendsto (0 : 𝔤)
    exact this.eventually hf
  simp only [rightDeriv, h0.fderiv_eq, fderiv_const_apply]
  rfl

theorem rightDeriv_comp_inv_eq_zero {κ : G → ℂ} {z : G} (hz : z⁻¹ ∉ tsupport κ) (X : 𝔤) :
    h.rightDeriv X (fun w : G => κ w⁻¹) z = 0 := by
  refine rightDeriv_eq_zero_of_eventually ?_ X
  have hopen : IsOpen (tsupport κ)ᶜ := (isClosed_tsupport κ).isOpen_compl
  have ht : Tendsto (fun w : G => w⁻¹) (𝓝 z) (𝓝 z⁻¹) := continuous_inv.tendsto z
  exact (ht.eventually (hopen.mem_nhds hz)).mono fun w hw =>
    (image_eq_zero_of_notMem_tsupport hw : κ w⁻¹ = 0)

theorem support_convDeriv_subset (X : 𝔤) (κ : G → ℂ) :
    Function.support (h.convDeriv X κ) ⊆ tsupport κ := by
  intro y hy
  by_contra hyκ
  exact hy (rightDeriv_comp_inv_eq_zero (by rwa [inv_inv]) X)

theorem hasCompactSupport_convDeriv {κ : G → ℂ} (hκc : HasCompactSupport κ) (X : 𝔤) :
    HasCompactSupport (h.convDeriv X κ) :=
  hκc.mono' (support_convDeriv_subset X κ)

theorem exists_bound_rightDeriv_comp_inv {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ)
    (X : 𝔤) : ∃ M, ∀ z, ‖h.rightDeriv X (fun w : G => κ w⁻¹) z‖ ≤ M := by
  have hDcs : HasCompactSupport (h.rightDeriv X fun w : G => κ w⁻¹) := by
    refine HasCompactSupport.intro (hκc.image continuous_inv) fun z hz => ?_
    refine rightDeriv_comp_inv_eq_zero (fun hk => hz ⟨z⁻¹, hk, inv_inv z⟩) X
  exact hDcs.exists_bound_of_continuous (continuous_rightDeriv_comp_inv hκ X)

theorem rightDeriv_eq_integral_convDeriv [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {κ : G → ℂ}
    (hκ : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) (hκc : HasCompactSupport κ)
    {f : G → ℂ} (hf : h.IsSmoothFun f) (hconv : ∀ g, f g = ∫ y, f (g * y) * κ y ∂μ)
    (X : 𝔤) (g : G) :
    h.rightDeriv X f g = ∫ y, f (g * y) * h.convDeriv X κ y ∂μ := by
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hfc : Continuous f := continuous_of_isSmoothFun hf
  have hfg : Continuous fun y : G => f (g * y) := hfc.comp (continuous_const.mul continuous_id)
  have hκ'c : Continuous fun z : G => κ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)
  have hDc := continuous_rightDeriv_comp_inv hκ X

  have hshift : ∀ t : ℝ, f (g * h.expG (t • X)) =
      ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ := by
    intro t
    rw [hconv (g * h.expG (t • X))]
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp [mul_assoc, mul_inv_rev]

  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]

  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hκc).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hκ hκc X
  have hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ := by
    have : (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y := by
      funext y; simp
    rw [this]
    exact Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ))
      (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹)
    (F' := fun (t : ℝ) (y : G) => f (g * y) *
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => ‖f (g * y)‖ * M)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t =>
      (hfg.mul (hκ'c.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable) hint0
    (hfg.mul (hDc.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero,
          norm_zero])
    hbound
    (Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))
  have hd1 : HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f g) 0 :=
    h.hasDerivAt_rightDeriv hf X g
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  congr 1
  funext y
  simp [convDeriv]

end IsExpLieAlgebra

end GroundTheory.Automorphic
end
