module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjection
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FiniteOfTorsion
public import Development.WeilBound.CoreStatements.AmpleLineBundles.SpanLeOfMem

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndAction
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndAction
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem ip_add_left' (R : RiemLat E g Λ) (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  simp [RiemLat.ip, star_add, Matrix.mulVec_add, dotProduct_add]

theorem ip_add_right' (R : RiemLat E g Λ) (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_left' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) :
    R.ip (c • x) y = star c * R.ip x y := by
  simp [RiemLat.ip, star_smul, Matrix.mulVec_smul, dotProduct_smul]

theorem ip_smul_right' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem real_smul_eq' (r : ℝ) (x : Fin g → ℂ) : r • x = (r : ℂ) • x := by
  ext i
  simp

theorem ip_period_im (R : RiemLat E g Λ) (x y : Λ) : (R.ip (R.P x) (R.P y)).im = R.form y x :=
  R.im y x

theorem isometry_of_periods (R R' : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤)
    (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hf : ∀ x y, R'.form (γ x) (γ y) = R.form x y) (hP : ∀ x, R'.P (γ x) = φ (R.P x))
    (x y : Fin g → ℂ) : R'.ip (φ x) (φ y) = R.ip x y := by
  let D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun z w => R'.ip (φ z) (φ w) - R.ip z w
  have hl : ∀ z z' w, D (z + z') w = D z w + D z' w := fun z z' w => by
    simp only [D, map_add (f := _), ip_add_left']
    ring
  have hr : ∀ z w w', D z (w + w') = D z w + D z w' := fun z w w' => by
    simp only [D, map_add (f := _), ip_add_right']
    ring
  have hcl : ∀ (c : ℂ) z w, D (c • z) w = star c * D z w := fun c z w => by
    simp only [D, map_smul, ip_smul_left']
    ring
  have hcr : ∀ (c : ℂ) z w, D z (c • w) = c * D z w := fun c z w => by
    simp only [D, map_smul, ip_smul_right']
    ring
  have h0l : ∀ w, D 0 w = 0 := fun w => by
    simp [D, RiemLat.ip]
  have h0r : ∀ z, D z 0 = 0 := fun z => by
    simp [D, RiemLat.ip]
  have base : ∀ l l', (D (R.P l) (R.P l')).im = 0 := fun l l' => by
    simp only [D, Complex.sub_im]
    rw [← hP, ← hP, ip_period_im, ip_period_im, hf, sub_self]
  have s1 : ∀ l w, (D (R.P l) w).im = 0 := fun l w => by
    have hw : w ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨l', rfl⟩ := h
      exact base l l'
    | zero => simp [h0r]
    | add w w' _ _ h h' => simp [hr, h, h']
    | smul r w _ h =>
      rw [real_smul_eq', hcr]
      simp [h]
  have s2 : ∀ z w, (D z w).im = 0 := fun z w => by
    have hz : z ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨l, rfl⟩ := h
      exact s1 l w
    | zero => simp [h0l]
    | add z z' _ _ h h' => simp [hl, h, h']
    | smul r z _ h =>
      rw [real_smul_eq', hcl]
      simp [h]
  have s3 : (D x y).re = 0 := by
    have h := s2 x (Complex.I • y)
    rw [hcr] at h
    simpa using h
  have s4 : D x y = 0 := Complex.ext s3 (s2 x y)
  exact sub_eq_zero.mp s4

theorem commutes_of_periods (R R' : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤)
    (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hP : ∀ x, R'.P (γ x) = φ (R.P x))
    (a : 𝓞 E) (x : Fin g → ℂ) : φ (R.B a x) = R'.B a (φ x) := by
  have hx : x ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨l, rfl⟩ := h
    rw [← R.act, ← hP, ← hP, map_smul, R'.act]
  | zero => simp
  | add x x' _ _ h h' => simp [h, h']
  | smul r x _ h =>
    rw [real_smul_eq', map_smul, map_smul, h, map_smul, map_smul]

theorem isometry_and_commutes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
    (∀ x y, R'.form (γ x) (γ y) = R.form x y) → (∀ x, R'.P (γ x) = φ (R.P x)) →
    (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) ∧ ∀ a x, φ (R.B a x) = R'.B a (φ x) := by
  intro E _ _ _ g Λ _ _ R R' γ φ hf hP
  have hs := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  exact ⟨isometry_of_periods R R' hs γ φ hf hP, commutes_of_periods R R' hs γ φ hP⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndActionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_preserves_hermitian_and_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, R'.form (γ x) (γ y) = R.form x y) → (∀ x, R'.P (γ x) = φ (R.P x)) → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) ∧ ∀ a x, φ (R.B a x) = R'.B a (φ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes | exact GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderIsometry
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeIsometryTransport
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g g' : ℕ} {Λ Λ' : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] {Ψ : Type} [Fintype Ψ]
  (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))

theorem exists_equiv (h1 : φ '' Set.range R.P = Set.range R'.P) (h3 : ∀ a x, φ (R.B a x) = R'.B a (φ x)) :
    ∃ α : Λ ≃ₗ[𝓞 E] Λ', ∀ v, R'.P (α v) = φ (R.P v) := by
  have h4 : ∀ v, ∃ v', R'.P v' = φ (R.P v) := fun v => by
    have h : φ (R.P v) ∈ Set.range R'.P := h1 ▸ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact h
  choose f hf using h4
  let α : Λ →ₗ[𝓞 E] Λ' :=
    { toFun := f
      map_add' := fun v w => precomp_injective R' (by rw [map_add (f := _), hf, hf, hf, map_add (f := _), map_add (f := _)])
      map_smul' := fun a v => precomp_injective R' (by rw [RingHom.id_apply, R'.act, hf, hf, R.act, h3]) }
  refine ⟨LinearEquiv.ofBijective α ⟨fun v w h => ?_, fun v' => ?_⟩, hf⟩
  · have h' : f v = f w := h
    exact precomp_injective R (φ.injective (by rw [← hf, ← hf, h']))
  · have h : R'.P v' ∈ φ '' Set.range R.P := h1.symm ▸ ⟨v', rfl⟩
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := h
    exact ⟨v, precomp_injective R' ((hf v).trans hv)⟩

theorem proj_equiv (h3 : ∀ a x, φ (R.B a x) = R'.B a (φ x)) (s : 𝓞 E →+* ℂ) (x : Fin g → ℂ) :
    proj R'.B s (φ x) = φ (proj R.B s x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [proj_apply, map_sum, map_smul, h3]

theorem nz_map {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (h2 : ∀ x y, R'.ip (φ x) (φ y) = R.ip x y)
    (h3 : ∀ a x, φ (R.B a x) = R'.B a (φ x)) (α : Λ ≃ₗ[𝓞 E] Λ') (hα : ∀ v, R'.P (α v) = φ (R.P v))
    (I : Submodule (𝓞 E) Λ) : R'.nz σ (I.map α.toLinearMap) = R.nz σ I := by
  by_cases hI : I = ⊥
  · subst hI
    rw [Submodule.map_bot, RiemLat.nz, RiemLat.nz, dite_eq_right, dite_eq_right]
    · rintro ⟨r, v, h1, h4, h5, -⟩
      exact h5.ne_zero ⟨0, h1⟩ (h4 _)
    · rintro ⟨r, v, h1, h4, h5, -⟩
      exact h5.ne_zero ⟨0, h1⟩ (h4 _)
  have := R.free
  have := R.fin
  obtain ⟨r, v, hv⟩ := exists_family hI
  have h4 : (Submodule.span (𝓞 E) (Set.range fun a => α (v a))).toAddSubgroup.relIndex
      (I.map α.toLinearMap).toAddSubgroup =
      (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup := by
    rw [← relIndex_map α.toLinearMap α.injective, Submodule.map_span, ← Set.range_comp]
    rfl
  have hw : IsNzFamily (I.map α.toLinearMap) r fun a => α (v a) :=
    ⟨hv.1, fun a => Submodule.mem_map_of_mem (hv.2.1 a), hv.2.2.1.map' α.toLinearMap α.ker, h4 ▸ hv.2.2.2⟩
  rw [nz_eq R hσ hv, nz_eq R' hσ hw, RiemLat.nzOf, RiemLat.nzOf, h4]
  simp only [RiemLat.gram, eigComp_eq, hα, proj_equiv R R' φ h3, h2]

theorem isCusp_map (h2 : ∀ x y, R'.ip (φ x) (φ y) = R.ip x y) (α : Λ ≃ₗ[𝓞 E] Λ')
    (hα : ∀ v, R'.P (α v) = φ (R.P v)) (I : Submodule (𝓞 E) Λ) :
    R'.IsCusp (I.map α.toLinearMap) ↔ R.IsCusp I := by
  have h4 : ∀ v w, R'.form (α v) (α w) = R.form v w := fun v w => by
    apply Int.cast_injective (α := ℝ)
    rw [← imB_P, ← imB_P, imB_apply, imB_apply, hα, hα, h2]
  have h5 : ∀ v, α v ∈ I.map α.toLinearMap ↔ v ∈ I := fun v =>
    ⟨fun ⟨w, hw, h⟩ => α.injective h ▸ hw, fun h => Submodule.mem_map_of_mem h⟩
  refine and_congr (by simp) (and_congr ?_ ?_)
  · unfold IsSaturated
    rw [α.surjective.forall]
    simp only [← map_zsmul, h5]
  · unfold IsIsoSub
    rw [α.surjective.forall]
    refine forall_congr' fun v => imp_congr (h5 v) ?_
    rw [α.surjective.forall]
    simp only [h4, h5]

end

theorem riemann_lattice_isometry_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (g' : ℕ) (Λ' : Type) [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R' : RiemLat E g' Λ') (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)), IsCMFam σ → φ '' Set.range R.P = Set.range R'.P → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) → (∀ a x, φ (R.B a x) = R'.B a (φ x)) → R'.cuspW σ = R.cuspW σ ∧ R'.lam1 = R.lam1 ∧ (∀ m, R'.HasRank σ m ↔ R.HasRank σ m) ∧ ∃ α : Λ ≃ₗ[𝓞 E] Λ', (∀ v, R'.P (α v) = φ (R.P v)) ∧ ∀ I, IsIsoSub R.form I → R'.nz σ (I.map α.toLinearMap) = R.nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ g' Λ' _ _ R' φ hσ h1 h2 h3
  obtain ⟨α, hα⟩ := exists_equiv R R' φ h1 h3
  refine ⟨?_, ?_, fun m => forall_congr' fun τ => ?_, α, hα, fun I _ => nz_map R R' φ hσ h2 h3 α hα I⟩
  · unfold RiemLat.cuspW
    congr 2
    ext x
    constructor
    · rintro ⟨I', hI, rfl⟩
      obtain ⟨I, rfl⟩ : ∃ I : Submodule (𝓞 E) Λ, I.map α.toLinearMap = I' :=
        ⟨I'.comap α.toLinearMap, Submodule.map_comap_eq_of_surjective α.surjective I'⟩
      exact ⟨I, (isCusp_map R R' φ h2 α hα I).1 hI, by rw [nz_map R R' φ hσ h2 h3 α hα]⟩
    · rintro ⟨I, hI, rfl⟩
      exact ⟨_, (isCusp_map R R' φ h2 α hα I).2 hI, by rw [nz_map R R' φ hσ h2 h3 α hα]⟩
  · unfold RiemLat.lam1 RiemLat.normSq
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    rw [α.surjective.exists]
    simp only [hα, h2, ne_eq, α.map_eq_zero_iff]
  · have h4 : eigSp R'.B (σ τ) = (eigSp R.B (σ τ)).map φ.toLinearMap := by
      ext y
      obtain ⟨x, rfl⟩ := φ.surjective y
      rw [Submodule.mem_map_equiv, φ.symm_apply_apply, mem_eig, mem_eig]
      simp only [← h3, ← map_smul, φ.injective.eq_iff]
    rw [h4, LinearEquiv.finrank_map_eq]

end LevelTowerAlt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderIsometry
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (g' : ℕ) (Λ' : Type) [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R' : RiemLat E g' Λ') (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)), IsCMFam σ → φ '' Set.range R.P = Set.range R'.P → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) → (∀ a x, φ (R.B a x) = R'.B a (φ x)) → R'.cuspW σ = R.cuspW σ ∧ R'.lam1 = R.lam1 ∧ (∀ m, R'.HasRank σ m ↔ R.HasRank σ m) ∧ ∃ α : Λ ≃ₗ[𝓞 E] Λ', (∀ v, R'.P (α v) = φ (R.P v)) ∧ ∀ I, IsIsoSub R.form I → R'.nz σ (I.map α.toLinearMap) = R.nz σ I := by
  first | exact @LevelTowerAlt.riemann_lattice_isometry_transport | exact LevelTowerAlt.riemann_lattice_isometry_transport
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderIsometryStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_weight_invariant_under_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (g' : ℕ) (Λ' : Type) [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R' : RiemLat E g' Λ') (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)), IsCMFam σ → φ '' Set.range R.P = Set.range R'.P → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) → (∀ a x, φ (R.B a x) = R'.B a (φ x)) → R'.cuspW σ = R.cuspW σ ∧ R'.lam1 = R.lam1 ∧ (∀ m, R'.HasRank σ m ↔ R.HasRank σ m) ∧ ∃ α : Λ ≃ₗ[𝓞 E] Λ', (∀ v, R'.P (α v) = φ (R.P v)) ∧ ∀ I, IsIsoSub R.form I → R'.nz σ (I.map α.toLinearMap) = R.nz σ I := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_isometry | exact GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_isometry | (intros; apply GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_isometry <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeOrthogonalSum
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeOrthogonalSum
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.OrthSum

variable {K : Type} [Field K] [NumberField K]

theorem disjoint_of_orth (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier}
    (h : OrthAt E F G) : Disjoint F G := by
  rw [Submodule.disjoint_def]
  intro x hxF hxG
  by_contra hx
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hli : LinearIndependent (𝓞 K) (fun _ : Unit => x) := linearIndependent_unique_iff.mpr hx
  have hpos := gramDet_pos E.metric σ hli
  have h0 := h σ x hxF x hxG
  rw [← FibreSpace.inner_equiv E.metric σ] at h0
  have h0' : inner ℂ (fibreVec E.metric σ x) (fibreVec E.metric σ x) = 0 := h0
  have hz : GroundTheory.Heights₂.Heights.gramDet E.metric σ (fun _ : Unit => x) = 0 := by
    unfold GroundTheory.Heights₂.Heights.gramDet
    rw [Matrix.det_unique, Matrix.gram_apply, h0', Complex.zero_re]
  linarith

theorem gramDet_sumElim (E : HermitianBundle.{0} K) (σ : K →+* ℂ) {a b : ℕ}
    {s : Fin a → E.carrier} {t : Fin b → E.carrier} (hs : LinearIndependent (𝓞 K) s)
    (ht : LinearIndependent (𝓞 K) t)
    (h : ∀ i j, inner ℂ (fibreVec E.metric σ (s i)) (fibreVec E.metric σ (t j)) = 0) :
    gramDet E.metric σ (Sum.elim s t) = gramDet E.metric σ s * gramDet E.metric σ t := by
  have hconj : ∀ i j, inner ℂ (fibreVec E.metric σ (t j)) (fibreVec E.metric σ (s i)) = 0 := by
    intro i j
    rw [← inner_conj_symm, h i j, map_zero]
  have hM : (Matrix.gram ℂ fun k => fibreVec E.metric σ (Sum.elim s t k)) =
      Matrix.fromBlocks (Matrix.gram ℂ fun i => fibreVec E.metric σ (s i)) 0 0
        (Matrix.gram ℂ fun j => fibreVec E.metric σ (t j)) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, h, hconj]
  have him : ∀ {n : ℕ} (v : Fin n → FibreSpace E.metric σ), (Matrix.gram ℂ v).det.im = 0 := by
    intro n v
    have hA : (Matrix.gram ℂ v).conjTranspose = Matrix.gram ℂ v := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.gram_apply]
      exact inner_conj_symm _ _
    have hdet := Matrix.det_conjTranspose (Matrix.gram ℂ v)
    rw [hA] at hdet
    exact Complex.conj_eq_iff_im.mp hdet.symm
  unfold GroundTheory.Heights₂.Heights.gramDet
  rw [hM, Matrix.det_fromBlocks_zero₂₁, Complex.mul_re, him, him, mul_zero, sub_zero]

theorem degree_sup (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier}
    (h : OrthAt E F G) : E.degree (F ⊔ G) = E.degree F + E.degree G := by
  have hd : Disjoint F G := disjoint_of_orth E h
  obtain ⟨s, hs, hsF⟩ := CoverDenseAlt.exists_fam E F
  obtain ⟨t, ht, htG⟩ := CoverDenseAlt.exists_fam E G
  have hNs : Submodule.span (𝓞 K) (Set.range s) ≤ F := CoverDenseAlt.span_le_of_mem hsF
  have hNt : Submodule.span (𝓞 K) (Set.range t) ≤ G := CoverDenseAlt.span_le_of_mem htG
  have hst : LinearIndependent (𝓞 K) (Sum.elim s t) := hs.sum_type ht (hd.mono hNs hNt)
  have hmem : ∀ i, Sum.elim s t i ∈ F ⊔ G := by
    rintro (i | i)
    · exact Submodule.mem_sup_left (hsF i)
    · exact Submodule.mem_sup_right (htG i)
  have hcard : Fintype.card (Fin (E.rank F) ⊕ Fin (E.rank G)) = E.rank (F ⊔ G) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, CoverDenseAlt.rank_sup E hd]
  obtain ⟨hiF, hF⟩ := CoverDenseAlt.deg_eq E F hs hsF (Fintype.card_fin _)
  obtain ⟨hiG, hG⟩ := CoverDenseAlt.deg_eq E G ht htG (Fintype.card_fin _)
  obtain ⟨-, hFG⟩ := CoverDenseAlt.deg_eq E (F ⊔ G) hst hmem hcard
  have hidx : CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range (Sum.elim s t))) (F ⊔ G) =
      CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range s)) F * CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range t)) G := by
    rw [Set.Sum.elim_range, Submodule.span_union,
      ← CoverDenseAlt.idx_mul (sup_le_sup_right hNs _) (sup_le_sup_left hNt F)]
    congr 1
    · exact CoverDenseAlt.idx_sup hNs (hd.mono_right hNt)
    · rw [sup_comm F, sup_comm F G]
      exact CoverDenseAlt.idx_sup hNt hd.symm
  have hlog : ∀ σ : K →+* ℂ, Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ (Sum.elim s t)) =
      Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ s) + Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ t) := by
    intro σ
    have hgram := gramDet_sumElim E σ hs ht (fun i j => by
      have h1 := h σ _ (hsF i) _ (htG j)
      rw [← FibreSpace.inner_equiv E.metric σ] at h1
      exact h1)
    rw [hgram, Real.log_mul (gramDet_pos E.metric σ hs).ne' (gramDet_pos E.metric σ ht).ne']
  rw [hFG, hF, hG, hidx, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hiF) (Nat.cast_ne_zero.mpr hiG)]
  simp only [hlog, Finset.sum_add_distrib]
  ring

theorem degree_bot (E : HermitianBundle.{0} K) : E.degree ⊥ = 0 := by
  have hrk : Fintype.card (Fin 0) = E.rank ⊥ := by
    unfold GroundTheory.Heights₂.Heights.HermitianBundle.rank
    simp
  obtain ⟨-, hdeg⟩ := CoverDenseAlt.deg_eq E ⊥ (s := (Fin.elim0 : Fin 0 → E.carrier)) linearIndependent_empty_type
    (fun i => i.elim0) hrk
  have h1 : CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range (Fin.elim0 : Fin 0 → E.carrier))) ⊥ = 1 := by
    rw [CoverDenseAlt.idx_eq_card]
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨0⟩⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Subsingleton.elim a b]
  have hg : ∀ σ : K →+* ℂ, GroundTheory.Heights₂.Heights.gramDet E.metric σ (Fin.elim0 : Fin 0 → E.carrier) = 1 := by
    intro σ
    unfold GroundTheory.Heights₂.Heights.gramDet
    rw [Matrix.det_isEmpty, Complex.one_re]
  rw [hdeg, h1]
  simp only [hg, Real.log_one, Nat.cast_one, Finset.sum_const_zero, mul_zero, sub_zero]

theorem orth_biSup (E : HermitianBundle.{0} K) {F : Submodule (𝓞 K) E.carrier} {I : Type}
    (G : I → Submodule (𝓞 K) E.carrier) (S : Finset I) (h : ∀ b ∈ S, OrthAt E F (G b)) :
    OrthAt E F (⨆ b ∈ S, G b) := by
  classical
  intro σ x hx y hy
  obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum G y).mp hy
  rw [← FibreSpace.inner_equiv E.metric σ]
  have hfv : fibreVec E.metric σ (∑ b ∈ S, (μ b : E.carrier)) = ∑ b ∈ S, fibreVec E.metric σ (μ b) := by
    simpa using fibreVec_sum E.metric σ S (fun _ => 1) (fun b => (μ b : E.carrier))
  change inner ℂ (fibreVec E.metric σ x) (fibreVec E.metric σ (∑ b ∈ S, (μ b : E.carrier))) = 0
  rw [hfv, inner_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  have h1 := h b hb σ x hx _ (μ b).2
  rw [← FibreSpace.inner_equiv E.metric σ] at h1
  exact h1

theorem degree_rank_biSup (E : HermitianBundle.{0} K) {I : Type}
    (F : I → Submodule (𝓞 K) E.carrier) (h : ∀ a b, a ≠ b → OrthAt E (F a) (F b)) (S : Finset I) :
    E.degree (⨆ a ∈ S, F a) = ∑ a ∈ S, E.degree (F a) ∧
      E.rank (⨆ a ∈ S, F a) = ∑ a ∈ S, E.rank (F a) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · have hb : (⨆ a ∈ (∅ : Finset I), F a) = ⊥ := by simp
    rw [hb, Finset.sum_empty, Finset.sum_empty]
    refine ⟨degree_bot E, ?_⟩
    unfold GroundTheory.Heights₂.Heights.HermitianBundle.rank
    simp
  · intro a S ha ih
    rw [Finset.iSup_insert, Finset.sum_insert ha, Finset.sum_insert ha]
    have horth : OrthAt E (F a) (⨆ b ∈ S, F b) :=
      orth_biSup E F S fun b hb => h a b fun hab => ha (hab ▸ hb)
    refine ⟨?_, ?_⟩
    · rw [degree_sup E horth, ih.1]
    · rw [CoverDenseAlt.rank_sup E (disjoint_of_orth E horth), ih.2]

theorem normDegree_rank_iSup : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (I : Type) [Fintype I] (F : I → Submodule (𝓞 K) E.carrier), (∀ a b, a ≠ b → OrthAt E (F a) (F b)) → E.normDegree (⨆ a, F a) = ∑ a, E.normDegree (F a) ∧ E.rank (⨆ a, F a) = ∑ a, E.rank (F a) := by
  intro K _ _ E I _ F h
  have hU : (⨆ a, F a) = ⨆ a ∈ (Finset.univ : Finset I), F a := by simp
  obtain ⟨hd, hr⟩ := degree_rank_biSup E F h Finset.univ
  rw [hU]
  refine ⟨?_, hr⟩
  unfold GroundTheory.Heights₂.Heights.HermitianBundle.normDegree
  rw [hd, Finset.sum_div]

end GlobalTheory.CompanionTheory.Ar.OrthSum
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeOrthogonalSumStatement
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_orthogonal_sum : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (I : Type) [Fintype I] (F : I → Submodule (𝓞 K) E.carrier), (∀ a b, a ≠ b → OrthAt E (F a) (F b)) → E.normDegree (⨆ a, F a) = ∑ a, E.normDegree (F a) ∧ E.rank (⨆ a, F a) = ∑ a, E.rank (F a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup | exact GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup | (intros; apply GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup <;> assumption)
end
end
