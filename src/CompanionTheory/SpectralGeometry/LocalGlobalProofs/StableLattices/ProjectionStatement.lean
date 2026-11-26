module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanGenEigenOfFiniteDimensionalOrbit
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaAll

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProjectionStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProjectionStatement
open scoped InnerProductSpace
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted

namespace GlobalTheory.CompanionTheory.FixedProj

theorem stProj : StProj := by
  unfold StProj
  intro G H _ _ _ _ σ hiso K
  let V : Submodule ℂ H :=
    { carrier := {v | ∀ k ∈ K, σ k v = v}
      add_mem' := fun {a b} ha hb k hk => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add (f := _), ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun c v hv k hk => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        rw [map_smul, hv k hk] }
  have hmem : ∀ v, v ∈ V ↔ ∀ k ∈ K, σ k v = v := fun v => Iff.rfl
  have hVc : IsClosed (V : Set H) := by
    have hV : (V : Set H) = ⋂ k ∈ K, {v | σ k v = v} := by
      ext v
      simp only [Set.mem_iInter]
      exact hmem v
    rw [hV]
    exact isClosed_biInter fun k _ => isClosed_eq (σ k).continuous continuous_id
  haveI : CompleteSpace V := hVc.completeSpace_coe
  have hin : ∀ g v w, inner ℂ (σ g v) w = inner ℂ v (σ g⁻¹ w) := CompanionTheory.D.gk.admitted.FinOfPIAux.inner_left σ hiso
  refine ⟨V.starProjection, ?_, ?_, ?_⟩
  · unfold IsAvg
    refine ⟨?_, ?_, ?_⟩
    · intro v k hk
      exact (hmem _).1 (V.starProjection_apply_mem v) k hk
    · intro v hv
      exact Submodule.starProjection_eq_self_iff.2 ((hmem v).2 hv)
    · intro v k hk
      have horth : σ k v - v ∈ Vᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 : inner ℂ u (σ k v) = inner ℂ u v := by
          have h := hin k⁻¹ u v
          rw [inv_inv, (hmem u).1 hu k⁻¹ (K.inv_mem hk)] at h
          exact h.symm
        rw [inner_sub_right, h1, sub_self]
      have h0 := (Submodule.starProjection_apply_eq_zero_iff V).2 horth
      rw [map_sub, sub_eq_zero] at h0
      exact h0
  · intro u w
    exact Submodule.inner_starProjection_left_eq_right (K := V) u w
  · intro T hT
    have hTσ : ∀ g v, T (σ g v) = σ g (T v) := fun g v =>
      congrArg (fun S : H →L[ℂ] H => S v) (hT g)
    have hTV : ∀ v ∈ V, T v ∈ V := fun v hv k hk => by
      rw [← hTσ, (hmem v).1 hv k hk]
    have hadj : ∀ w ∈ V, ContinuousLinearMap.adjoint T w ∈ V := by
      intro w hw k hk
      apply ext_inner_right ℂ
      intro z
      rw [hin, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hTσ, ← hin,
        (hmem w).1 hw k hk]
    ext v
    have h1 : V.starProjection (T (V.starProjection v)) = T (V.starProjection v) :=
      Submodule.starProjection_eq_self_iff.2 (hTV _ (V.starProjection_apply_mem v))
    have hu : v - V.starProjection v ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal (K := V) v
    have h2 : V.starProjection (T (v - V.starProjection v)) = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff V).2
      rw [Submodule.mem_orthogonal] at hu ⊢
      intro w hw
      rw [← ContinuousLinearMap.adjoint_inner_left]
      exact hu _ (hadj w hw)
    have hv : v = V.starProjection v + (v - V.starProjection v) := by abel
    show T (V.starProjection v) = V.starProjection (T v)
    conv_rhs => rw [hv]
    simp only [map_add (f := _)]
    rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.FixedProj
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProjectionStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ProjectionStatement : StProj := by
  first | exact @GlobalTheory.CompanionTheory.FixedProj.stProj | exact GlobalTheory.CompanionTheory.FixedProj.stProj | (intros; apply GlobalTheory.CompanionTheory.FixedProj.stProj <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleOfCommutativeStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleOfCommutativeStatement
noncomputable section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

theorem finrank_sq_le_of_span {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (hρ : Function.Surjective ρ) {d l : ℕ}
    (x y : Fin d → A) (a : Fin l → A)
    (hs : Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} = ⊤) :
    Module.finrank ℂ V ^ 2 ≤
      d ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) := by
  classical
  set B := Algebra.adjoin ℂ (Set.range fun i => ρ (a i)) with hB
  have hmap : ∀ c ∈ Algebra.adjoin ℂ (Set.range a), ρ c ∈ B := by
    intro c hc
    have e : B = (Algebra.adjoin ℂ (Set.range a)).map ρ := by
      rw [hB, AlgHom.map_adjoin, ← Set.range_comp]
      rfl
    rw [e]
    exact ⟨c, hc, rfl⟩
  let G : Fin d × Fin d → (B →ₗ[ℂ] Module.End ℂ V) := fun p =>
    (LinearMap.mulLeft ℂ (ρ (x p.1))) ∘ₗ (LinearMap.mulRight ℂ (ρ (y p.2))) ∘ₗ B.val.toLinearMap
  let F : (Fin d × Fin d → B) →ₗ[ℂ] Module.End ℂ V :=
    ∑ p : Fin d × Fin d, G p ∘ₗ LinearMap.proj p
  have hFs : ∀ (p : Fin d × Fin d) (b : B), F (Pi.single p b) = ρ (x p.1) * b * ρ (y p.2) := by
    intro p b
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single p]
    · simp [G, mul_assoc]
    · intro q _ hq
      simp [Pi.single_eq_of_ne hq]
    · simp
  have hF : LinearMap.range F = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨g, rfl⟩ := hρ f
    have hg : g ∈ Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} := by
      rw [hs]; exact Submodule.mem_top
    induction hg using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, j, c, hc, rfl⟩ := hz
      exact ⟨Pi.single (i, j) ⟨ρ c, hmap c hc⟩, by simp [hFs]⟩
    | zero => simp
    | add u v _ _ hu hv => simpa using Submodule.add_mem _ hu hv
    | smul t u _ hu => simpa using Submodule.smul_mem _ t hu
  have h1 : Module.finrank ℂ (Module.End ℂ V) ≤ Module.finrank ℂ (Fin d × Fin d → B) := by
    have := LinearMap.finrank_range_le F
    rwa [hF, finrank_top] at this
  have h2 : Module.finrank ℂ (Module.End ℂ V) = Module.finrank ℂ V ^ 2 := by
    rw [Module.finrank_linearMap, sq]
  have h3 : Module.finrank ℂ (Fin d × Fin d → B) = d ^ 2 * Module.finrank ℂ B := by
    rw [Module.finrank_pi_fintype]
    simp [sq]
  rw [h2, h3] at h1
  exact h1

theorem stSimple_of_stComm : StComm → StSimple := by
  intro h d l
  obtain ⟨C, hC⟩ := h l (2 * d ^ 2)
  refine ⟨C, fun A _ _ hA V _ _ _ ρ hirr => ?_⟩
  obtain ⟨x, y, a, hcomm, hs⟩ := hA
  rcases subsingleton_or_nontrivial V with hV | hV
  · simp [Module.finrank_zero_of_subsingleton]
  have hsurj := GlobalTheory.CompanionTheory.Burnside.burnside_surj_of_irred ρ hirr
  have h1 := finrank_sq_le_of_span ρ hsurj x y a hs
  have h2 := hC V (fun i => ρ (a i)) (fun i j => (hcomm i j).map ρ)
  have hm : 0 < Module.finrank ℂ V := Module.finrank_pos
  generalize Module.finrank ℂ V = m at *
  generalize Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) = b at *
  have h3 : m * m ≤ C * m := by nlinarith
  exact Nat.le_of_mul_le_mul_right h3 hm

end GlobalTheory.CompanionTheory.RgFl

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleOfCommutativeStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_of_commutative_statement : StComm → StSimple := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm | exact GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm | (intros; apply GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FixedVectorStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FixedVectorStatement
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

theorem exists_least_norm_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C) (hconv : Convex ℝ C) :
    ∃ u ∈ C, ∀ w ∈ C, ‖u‖ ≤ ‖w‖ ∧ (‖w‖ ≤ ‖u‖ → w = u) := by
  obtain ⟨u, hu, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv (0 : E)
  have hin := (norm_eq_iInf_iff_real_inner_le_zero hconv hu).1 hmin
  refine ⟨u, hu, fun w hw => ?_⟩
  have h1 := hin w hw
  have h3 : inner ℝ (0 - u) (w - u) = ‖u‖ ^ 2 - inner ℝ w u := by
    rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm w u]
    ring
  have h2 : ‖w - u‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w u + ‖u‖ ^ 2 := norm_sub_sq_real w u
  have h4 : inner ℝ w u ≤ ‖w‖ * ‖u‖ := real_inner_le_norm w u
  have h5 : ‖u‖ ^ 2 ≤ ‖w‖ * ‖u‖ := by linarith
  constructor
  · rcases (norm_nonneg u).eq_or_lt with h0 | h0
    · rw [← h0]; exact norm_nonneg w
    · nlinarith
  · intro hle
    have h6 : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have := norm_nonneg w
      nlinarith
    have h7 : ‖w - u‖ ^ 2 ≤ 0 := by nlinarith
    have h8 : ‖w - u‖ = 0 := by
      have := norm_nonneg (w - u)
      nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h8)

theorem stFixVec : StFixVec := by
  intro G H _ _ _ _ _ _ _ σ hiso hcont
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨v, hv⟩ : ∃ v : H, ‖v‖ = 1 :=
    ⟨((‖x‖ : ℂ)⁻¹) • x, by
      have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      simp [norm_smul, this]⟩
  have hopen : IsOpen {g : G | ‖σ g v - v‖ < 1 / 2} :=
    isOpen_lt (((hcont v).sub continuous_const).norm) continuous_const
  have hone : (1 : G) ∈ {g : G | ‖σ g v - v‖ < 1 / 2} := by simp
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ (hopen.mem_nhds hone)
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  set A : Set H := Set.range (fun k : V => σ (k : G) v) with hA
  set C : Set H := closure (convexHull ℝ A) with hC
  have hvA : v ∈ A := ⟨1, by simp⟩
  have hCne : C.Nonempty := ⟨v, subset_closure (subset_convexHull ℝ A hvA)⟩
  have hCconv : Convex ℝ C := (convex_convexHull ℝ A).closure
  have hCball : C ⊆ Metric.closedBall v (1 / 2) := by
    refine closure_minimal (convexHull_min ?_ (convex_closedBall _ _)) Metric.isClosed_closedBall
    rintro _ ⟨k, rfl⟩
    have := hV k.2
    simp only [Set.mem_setOf_eq] at this
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact this.le
  have hstable : ∀ k : V, ∀ y ∈ C, σ (k : G) y ∈ C := by
    intro k y hy
    have hmaps : Set.MapsTo (σ (k : G)) (convexHull ℝ A) (convexHull ℝ A) := by
      have hconvpre : Convex ℝ ((σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A) :=
        (convex_convexHull ℝ A).linear_preimage _
      have hsub : A ⊆ (σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A := by
        rintro _ ⟨l, rfl⟩
        refine subset_convexHull ℝ A ⟨k * l, ?_⟩
        simp
      exact fun z hz => convexHull_min hsub hconvpre hz
    exact map_mem_closure (σ (k : G)).continuous hy hmaps
  obtain ⟨u, huC, hu⟩ := exists_least_norm_unique hCne isClosed_closure hCconv
  refine ⟨V.toSubgroup, u, V.isOpen, ?_, ?_⟩
  · rintro rfl
    have := hCball huC
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hv] at this
    norm_num at this
  · intro k hk
    exact (hu _ (hstable ⟨k, hk⟩ u huC)).2 (hiso k u).le

end GlobalTheory.CompanionTheory.RgFl
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FixedVectorStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FixedVectorStatement : StFixVec := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stFixVec | exact GlobalTheory.CompanionTheory.RgFl.stFixVec | (intros; apply GlobalTheory.CompanionTheory.RgFl.stFixVec <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementStar
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementStar
noncomputable section

open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgFl.StarPf

section

variable {A V : Type} [Ring A] [Algebra ℂ A]

def restrictAlg [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) : A →ₐ[ℂ] Module.End ℂ W where
  toFun h := (ρ h).restrict (hW h)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp
  commutes' c := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]

theorem restrictAlg_coe [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) (h : A) (x : W) : ((restrictAlg ρ W hW h x : W) : V) = ρ h x := rfl

theorem inf_orthogonal_invariant [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hs : StarClosed ρ) {U W : Submodule ℂ V}
    (hU : ∀ h, ∀ u ∈ U, ρ h u ∈ U) (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) :
    ∀ h, ∀ x ∈ Uᗮ ⊓ W, ρ h x ∈ Uᗮ ⊓ W := by
  intro h x hx
  obtain ⟨hxU, hxW⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨?_, hW h x hxW⟩
  rw [Submodule.mem_orthogonal] at hxU ⊢
  intro u hu
  obtain ⟨h', hh'⟩ := hs h
  rw [← inner_conj_symm, hh' x u, inner_conj_symm]
  exact hxU _ (hU h' u hu)

end

private theorem map_word_one {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (l : List A) : f (word 1 l) = word 1 (l.map f) := by
  induction l with
  | nil =>
    show f 1 = 1
    exact map_one f
  | cons a l ih =>
    show f (1 * a * word 1 l) = 1 * f a * word 1 (l.map f)
    rw [map_mul, map_mul, map_one, ih]

private theorem map_stdPoly_one {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) {M : ℕ} (b : Fin M → A) : f (stdPoly 1 b) = stdPoly 1 (fun i => f (b i)) := by
  unfold stdPoly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [map_mul, map_intCast, map_word_one, List.map_ofFn]
  rfl

theorem stStar : StStar := by
  unfold StStar
  intro C A _ _ hirr
  suffices key : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
      Module.finrank ℂ V = n → ∀ (ρ : A →ₐ[ℂ] Module.End ℂ V), StarClosed ρ →
        ∀ (b : Fin (C ^ 2 + 1) → A), ρ (stdPoly 1 b) = 0 by
    intro V _ _ _ ρ hs b
    exact key _ V rfl ρ hs b
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn ρ hs b
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have : Subsingleton V := Module.finrank_zero_iff.mp (hn.trans hn0)
    exact LinearMap.ext fun v => Subsingleton.elim _ _
  have : Nontrivial V := Module.finrank_pos_iff.mp (hn ▸ hnpos)
  have hex : ∃ d, ∃ W : Submodule ℂ V, ((∀ h, ∀ w ∈ W, ρ h w ∈ W) ∧ W ≠ ⊥) ∧ Module.finrank ℂ W = d :=
    ⟨_, ⊤, ⟨fun _ _ _ => Submodule.mem_top, bot_ne_top.symm⟩, rfl⟩
  obtain ⟨W, ⟨hWinv, hWne⟩, hWd⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule ℂ V, (∀ h, ∀ w ∈ W', ρ h w ∈ W') → W' ≠ ⊥ →
      Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' h1 h2
    rw [hWd]
    exact Nat.find_min' hex ⟨W', ⟨h1, h2⟩, rfl⟩
  have hWirr : ∀ U : Submodule ℂ W, (∀ h, ∀ u ∈ U, restrictAlg ρ W hWinv h u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hUb : U = ⊥
    · exact Or.inl hUb
    right
    have hU'inv : ∀ h, ∀ v ∈ U.map W.subtype, ρ h v ∈ U.map W.subtype := by
      intro h v hv
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
      exact Submodule.mem_map.mpr ⟨restrictAlg ρ W hWinv h u, hU h u hu, restrictAlg_coe ρ W hWinv h u⟩
    have hfr : Module.finrank ℂ (U.map W.subtype) = Module.finrank ℂ U := Submodule.finrank_map_subtype_eq W U
    have hU'ne : U.map W.subtype ≠ ⊥ := by
      intro h0
      apply hUb
      apply Submodule.finrank_eq_zero.mp
      rw [← hfr]
      exact Submodule.finrank_eq_zero.mpr h0
    have h1 := hmin _ hU'inv hU'ne
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le U) (hfr ▸ h1)
  have hdimW : Module.finrank ℂ W ≤ C := hirr W (restrictAlg ρ W hWinv) hWirr
  have hlt : Module.finrank ℂ W ^ 2 < C ^ 2 + 1 := Nat.lt_succ_of_le (Nat.pow_le_pow_left hdimW 2)
  have hPW : ∀ w ∈ W, ρ (stdPoly 1 b) w = 0 := by
    intro w hw
    rw [map_stdPoly_one ρ b]
    exact CompanionTheory.D.gk.admitted.small_irreducible_representation V W W le_rfl 1 (fun w hw => hw) (C ^ 2 + 1) hlt (fun i => ρ (b i))
      (fun i w hw => hWinv (b i) w hw) w hw
  have hperp : ∀ h, ∀ x ∈ Wᗮ, ρ h x ∈ Wᗮ := by
    intro h x hx
    have h1 := inf_orthogonal_invariant ρ hs (U := W) (W := ⊤) hWinv (fun _ _ _ => Submodule.mem_top) h x
      (Submodule.mem_inf.mpr ⟨hx, Submodule.mem_top⟩)
    exact (Submodule.mem_inf.mp h1).1
  have hs2 : StarClosed (restrictAlg ρ Wᗮ hperp) := by
    intro h
    obtain ⟨h', hh'⟩ := hs h
    refine ⟨h', fun u w => ?_⟩
    rw [Submodule.coe_inner, Submodule.coe_inner, restrictAlg_coe, restrictAlg_coe]
    exact hh' u w
  have hWpos : 0 < Module.finrank ℂ W := Nat.pos_of_ne_zero fun h0 => hWne (Submodule.finrank_eq_zero.mp h0)
  have hsum := Submodule.finrank_add_finrank_orthogonal W
  have hltp : Module.finrank ℂ Wᗮ < n := by omega
  have hrest := ih _ hltp Wᗮ rfl (restrictAlg ρ Wᗮ hperp) hs2 b
  have hPperp : ∀ x ∈ Wᗮ, ρ (stdPoly 1 b) x = 0 := by
    intro x hx
    have h0 := congrArg (fun T => ((T ⟨x, hx⟩ : Wᗮ) : V)) hrest
    simpa [restrictAlg_coe] using h0
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ W ⊔ Wᗮ := by
    have htop : W ⊔ Wᗮ = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W Wᗮ
      have h2 : W ⊓ Wᗮ = ⊥ := disjoint_iff.mp (Submodule.orthogonal_disjoint W)
      rw [h2, Submodule.finrank_eq_zero.mpr rfl] at h1
      omega
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨w, hw, x, hx, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add (f := _), hPW w hw, hPperp x hx, add_zero, LinearMap.zero_apply]

end GlobalTheory.CompanionTheory.RgFl.StarPf
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementStarStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.StatementStar : StStar := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.StarPf.stStar | exact GlobalTheory.CompanionTheory.RgFl.StarPf.stStar | (intros; apply GlobalTheory.CompanionTheory.RgFl.StarPf.stStar <;> assumption)
end
end
