module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixProjectionSelfDualLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixProjectionSelfDualLattices
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.LatticeProjection

theorem isLocalizedModule_subtype {O E V : Type*} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (B : Submodule O V) (hB : Submodule.span E (B : Set V) = ⊤) :
    IsLocalizedModule (nonZeroDivisors O) B.subtype := by
  refine ⟨fun s => ?_, fun v => ?_, fun {x y} h => ⟨1, by rw [Subtype.ext h]⟩⟩
  · exact (isLocalizedModule_id (nonZeroDivisors O) V E).map_units s
  · have hv : v ∈ Submodule.span E (B : Set V) := hB ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) E (B : Set V) v hv
    rw [Submodule.span_eq] at ht
    exact ⟨(⟨t • v, ht⟩, t), rfl⟩

theorem exists_linear_projection {O E V : Type*} [CommRing O] [IsDedekindDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (L₁ L₃ : Submodule O V) (h₁ : L₁.FG) (h₃ : L₃.FG)
    (hB : Submodule.span E ((L₁ ⊔ L₃ : Submodule O V) : Set V) = ⊤) :
    ∃ π : V →ₗ[E] V, ∀ v ∈ L₁ ⊔ L₃, π v ∈ L₁ ∧ v - π v ∈ L₃ := by
  set B := L₁ ⊔ L₃ with hBdef
  haveI : Module.Finite O B := Module.Finite.iff_fg.2 (h₁.sup h₃)
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O E V
  haveI : Module.FinitePresentation O B := Module.finitePresentation_of_finite O B
  haveI : Module.Flat O B := inferInstance
  haveI : Module.Projective O B := Module.Flat.projective_of_finitePresentation
  let p : (L₁ × L₃) →ₗ[O] B := LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)
  have hp : Function.Surjective p := by
    rintro ⟨v, hv⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  let f : B →ₗ[O] V := L₁.subtype ∘ₗ LinearMap.fst O L₁ L₃ ∘ₗ s
  haveI := isLocalizedModule_subtype (E := E) B hB
  have hu := (isLocalizedModule_id (nonZeroDivisors O) V E).map_units
  let g : V →ₗ[O] V := IsLocalizedModule.lift (nonZeroDivisors O) B.subtype f hu
  refine ⟨g.extendScalarsOfIsLocalization (nonZeroDivisors O) E, fun v hv => ?_⟩
  have hg : g v = ((s ⟨v, hv⟩).1 : V) := IsLocalizedModule.lift_apply (nonZeroDivisors O) B.subtype f hu ⟨v, hv⟩
  have hsum : ((s ⟨v, hv⟩).1 : V) + ((s ⟨v, hv⟩).2 : V) = v :=
    congrArg Subtype.val (LinearMap.congr_fun hs ⟨v, hv⟩)
  rw [LinearMap.extendScalarsOfIsLocalization_apply', hg]
  refine ⟨(s ⟨v, hv⟩).1.2, ?_⟩
  rw [sub_eq_of_eq_add' hsum.symm]
  exact (s ⟨v, hv⟩).2.2

theorem exists_matrix_projection : ∀ (D : D7) (n : ℕ) (L₁ L₃ : Lat D n), SD D L₁ → SD D L₃ →
    ∃ π : Matrix (Fin n) (Fin n) D.host.E, (∀ v ∈ L₁ ⊔ L₃, π.mulVec v ∈ L₁) ∧ (∀ v ∈ L₃, π.mulVec v ∈ L₃) ∧
      ∀ v ∈ L₁, v - π.mulVec v ∈ L₃ := by
  intro D n L₁ L₃ h₁ h₃
  obtain ⟨f₁, s₁, -⟩ := (sd_iff D L₁).1 h₁
  obtain ⟨f₃, -, -⟩ := (sd_iff D L₃).1 h₃
  obtain ⟨π, hπ⟩ := exists_linear_projection (E := D.host.E) L₁ L₃ f₁ f₃
    (top_le_iff.1 (s₁ ▸ Submodule.span_mono (fun x hx => Submodule.mem_sup_left hx)))
  refine ⟨LinearMap.toMatrix' π, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩ <;>
    rw [LinearMap.toMatrix'_mulVec]
  · exact (hπ v hv).1
  · simpa using L₃.sub_mem hv (hπ v (Submodule.mem_sup_right hv)).2
  · exact (hπ v (Submodule.mem_sup_left hv)).2

end GlobalTheory.LatticeProjection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixProjectionSelfDualLatticesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_projection_selfDual_lattices : ∀ (D : D7) (n : ℕ) (L₁ L₃ : Lat D n), SD D L₁ → SD D L₃ → ∃ π : Matrix (Fin n) (Fin n) D.host.E, (∀ v ∈ L₁ ⊔ L₃, π.mulVec v ∈ L₁) ∧ (∀ v ∈ L₃, π.mulVec v ∈ L₃) ∧ ∀ v ∈ L₁, v - π.mulVec v ∈ L₃ := by
  first | exact @GlobalTheory.LatticeProjection.exists_matrix_projection | exact GlobalTheory.LatticeProjection.exists_matrix_projection | (intros; apply GlobalTheory.LatticeProjection.exists_matrix_projection <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeTriplesDistributive
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.DistLa

variable {D : D7} {N N' : ℕ}

theorem La_map (T : Tor D) (f : VC D N N' →ₗ[ℂ] VC D N N')
    (g : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E)
    (hfg : ∀ A, f (embV D T A) = embV D T (g A)) {L M : Lat D N} {L' M' : Lat D N'}
    (hg : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ L, A.mulVec x ∈ L') → ∀ x ∈ M, (g A).mulVec x ∈ M')
    {z : VC D N N'} (hz : z ∈ La D T L L') : f z ∈ La D T M M' := by
  have h1 : ∀ A ∈ homL D L L', g A ∈ homL D M M' := by
    intro A hA
    have : homL D L L' ≤ (homL D M M').comap (g.restrictScalars (𝓞 D.host.E)) :=
      Submodule.span_le.2 fun B hB => Submodule.subset_span (hg B hB)
    exact this hA
  have h2 : ∀ A ∈ YYl D L L', g A ∈ YYl D M M' := by
    intro A hA
    have : YYl D L L' ≤ (YYl D M M').comap (g.restrictScalars (𝓞 D.host.E)) := by
      refine Submodule.span_le.2 ?_
      rintro B ⟨a, ha, C, hC, rfl⟩
      exact Submodule.subset_span ⟨a, ha, g C, h1 C hC, map_smul g a C⟩
    exact this hA
  have h3 : La D T L L' ≤ (La D T M M').comap f.toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    refine AddSubgroup.subset_closure ⟨w, hw, g A, h2 A hA, ?_⟩
    show f (w • embV D T A) = _
    rw [map_smul, hfg]
  exact h3 hz

def lft (P : Matrix (Fin N') (Fin N') D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ i j => ∑ k, embT D τ (P i k) * z τ k j
  map_add' x y := by
    funext τ i j; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

def rgt (P : Matrix (Fin N) (Fin N) D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ i j => ∑ k, z τ i k * embT D τ (P k j)
  map_add' x y := by
    funext τ i j; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem lft_add (P : Matrix (Fin N') (Fin N') D.host.E) (z : VC D N N') : lft P z + lft (1 - P) z = z := by
  funext τ i j
  show ∑ k, embT D τ (P i k) * z τ k j + ∑ k, embT D τ ((1 - P) i k) * z τ k j = z τ i j
  rw [← Finset.sum_add_distrib]
  simp only [← add_mul, ← map_add (f := _), Matrix.sub_apply, add_sub_cancel, Matrix.one_apply]
  simp [apply_ite]

theorem rgt_add (P : Matrix (Fin N) (Fin N) D.host.E) (z : VC D N N') : rgt P z + rgt (1 - P) z = z := by
  funext τ i j
  show ∑ k, z τ i k * embT D τ (P k j) + ∑ k, z τ i k * embT D τ ((1 - P) k j) = z τ i j
  rw [← Finset.sum_add_distrib]
  simp only [← mul_add, ← map_add (f := _), Matrix.sub_apply, add_sub_cancel, Matrix.one_apply]
  simp [apply_ite]

theorem lft_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (P : Matrix (Fin N') (Fin N') D.host.E) {L : Lat D N}
    {L' M' : Lat D N'} (hP : ∀ v ∈ L', P.mulVec v ∈ M') {z : VC D N N'} (hz : z ∈ La D (tor0 D cc δ) L L') :
    lft P z ∈ La D (tor0 D cc δ) L M' := by
  refine La_map _ (lft P)
    { toFun := fun A => P * A, map_add' := fun A B => Matrix.mul_add P A B,
      map_smul' := fun c A => Matrix.mul_smul P c A } ?_ ?_ hz
  · intro A
    funext τ i j
    show ∑ k, embT D τ (P i k) * embT D τ (A k j) = embT D τ ((P * A) i j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul]
  · intro A hA x hx
    show (P * A).mulVec x ∈ M'
    rw [← Matrix.mulVec_mulVec]
    exact hP _ (hA x hx)

theorem rgt_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (P : Matrix (Fin N) (Fin N) D.host.E) {L M : Lat D N}
    {L' : Lat D N'} (hP : ∀ v ∈ M, P.mulVec v ∈ L) {z : VC D N N'} (hz : z ∈ La D (tor0 D cc δ) L L') :
    rgt P z ∈ La D (tor0 D cc δ) M L' := by
  refine La_map _ (rgt P)
    { toFun := fun A => A * P, map_add' := fun A B => Matrix.add_mul A B P,
      map_smul' := fun c A => Matrix.smul_mul c A P } ?_ ?_ hz
  · intro A
    funext τ i j
    show ∑ k, embT D τ (A i k) * embT D τ (P k j) = embT D τ ((A * P) i j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul]
  · intro A hA x hx
    show (A * P).mulVec x ∈ L'
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hP x hx)

theorem one_sub_mulVec {n : ℕ} (P : Matrix (Fin n) (Fin n) D.host.E) (v : Fin n → D.host.E) :
    (1 - P).mulVec v = v - P.mulVec v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

theorem bet_proj {n : ℕ} {L₁ L₂ L₃ : Lat D n} (hb : Bet D L₁ L₂ L₃) {P : Matrix (Fin n) (Fin n) D.host.E}
    (h1 : ∀ v ∈ L₁ ⊔ L₃, P.mulVec v ∈ L₁) (h2 : ∀ v ∈ L₃, P.mulVec v ∈ L₃)
    (h3 : ∀ v ∈ L₁, v - P.mulVec v ∈ L₃) (v : Fin n → D.host.E) (hv : v ∈ L₂) :
    P.mulVec v ∈ L₁ ∧ P.mulVec v ∈ L₂ ∧ v - P.mulVec v ∈ L₃ := by
  obtain ⟨a, ⟨ha1, ha2⟩, b, ⟨hb2, hb3⟩, rfl⟩ := Submodule.mem_sup.1 (hb.1 hv)
  have pa := h1 a (Submodule.mem_sup_left ha1)
  have pb := h1 b (Submodule.mem_sup_right hb3)
  rw [Matrix.mulVec_add]
  refine ⟨L₁.add_mem pa pb, L₂.add_mem ?_ (hb.2 ⟨pb, h2 b hb3⟩), ?_⟩
  · have := L₂.sub_mem ha2 (hb.2 ⟨L₁.sub_mem ha1 pa, h3 a ha1⟩)
    rwa [sub_sub_cancel] at this
  · rw [add_sub_add_comm]
    exact L₃.add_mem (h3 a ha1) (L₃.sub_mem hb3 (h2 b hb3))

theorem dist_La : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), (∀ (L : Lat D N) (L₁ L₂ L₃ : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L L₁) (La D (tor0 D cc δ) L L₂) (La D (tor0 D cc δ) L L₃)) ∧ (∀ (L₁ L₂ L₃ : Lat D N) (L' : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L₁ L') (La D (tor0 D cc δ) L₂ L') (La D (tor0 D cc δ) L₃ L')) ∧ ∀ (L₀ L : Lat D N) (L₀' L' : Lat D N'), SD D L₀' → SD D L' → Dist (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) L₀ L') (La D (tor0 D cc δ) L L') := by
  intro D cc δ N N'
  refine ⟨?_, ?_, ?_⟩
  · intro L L₁ L₂ L₃ s1 s3 hb x hx y _ _
    obtain ⟨P, h1, h2, h3⟩ := GlobalTheory.T.exists_matrix_projection_selfDual_lattices D N' L₁ L₃ s1 s3
    have k := bet_proj hb h1 h2 h3
    rw [← lft_add P x]
    refine add_mem (AddSubgroup.mem_sup_left ⟨lft_mem cc δ P (fun v hv => (k v hv).1) hx,
      lft_mem cc δ P (fun v hv => (k v hv).2.1) hx⟩) (AddSubgroup.mem_sup_right
        ⟨lft_mem cc δ _ (fun v hv => ?_) hx, lft_mem cc δ _ (fun v hv => ?_) hx⟩)
    · rw [one_sub_mulVec]; exact L₂.sub_mem hv (k v hv).2.1
    · rw [one_sub_mulVec]; exact (k v hv).2.2
  · intro L₁ L₂ L₃ L' s1 s3 hb x hx y _ _
    obtain ⟨P, h1, h2, h3⟩ := GlobalTheory.T.exists_matrix_projection_selfDual_lattices D N L₁ L₃ s1 s3
    have k := bet_proj hb h1 h2 h3
    rw [← rgt_add P x, add_comm]
    refine add_mem (AddSubgroup.mem_sup_left ⟨rgt_mem cc δ _ (fun v hv => ?_) hx,
      rgt_mem cc δ _ (fun v hv => ?_) hx⟩) (AddSubgroup.mem_sup_right
        ⟨rgt_mem cc δ P (fun v hv => (k v hv).2.1) hx,
          rgt_mem cc δ P (fun v hv => hb.2 ⟨h1 v (Submodule.mem_sup_right hv), h2 v hv⟩) hx⟩)
    · rw [one_sub_mulVec]; exact hb.2 ⟨L₁.sub_mem hv (h1 v (Submodule.mem_sup_left hv)), h3 v hv⟩
    · rw [one_sub_mulVec]; exact L₂.sub_mem hv (k v hv).2.1
  · intro L₀ L L₀' L' s1 s3 x hx y hy hu
    obtain ⟨P, h1, h2, h3⟩ := GlobalTheory.T.exists_matrix_projection_selfDual_lattices D N' L₀' L' s1 s3
    have q1 : ∀ v ∈ L₀', (1 - P).mulVec v ∈ L₀' := fun v hv => by
      rw [one_sub_mulVec]; exact L₀'.sub_mem hv (h1 v (Submodule.mem_sup_left hv))
    have q2 : ∀ v ∈ L₀', (1 - P).mulVec v ∈ L' := fun v hv => by
      rw [one_sub_mulVec]; exact h3 v hv
    have q3 : ∀ v ∈ L', (1 - P).mulVec v ∈ L' := fun v hv => by
      rw [one_sub_mulVec]; exact L'.sub_mem hv (h2 v hv)
    have e : x = lft P x + lft (1 - P) (x + y) - lft (1 - P) y := by
      rw [map_add (f := _), ← add_assoc, lft_add, add_sub_cancel_right]
    have e2 : lft (1 - P) y = lft (1 - P) (x + y) - lft (1 - P) x := by
      rw [map_add (f := _), add_sub_cancel_left]
    rw [e]
    refine sub_mem (AddSubgroup.mem_sup_left (add_mem
      ⟨lft_mem cc δ P (fun v hv => h1 v (Submodule.mem_sup_right hv)) hx, lft_mem cc δ P h2 hx⟩
      ⟨lft_mem cc δ _ q1 hu, lft_mem cc δ _ q2 hu⟩)) (AddSubgroup.mem_sup_right ⟨?_, lft_mem cc δ _ q3 hy⟩)
    rw [e2]
    exact AddSubgroup.sub_mem _ (lft_mem cc δ _ q2 hu) (lft_mem cc δ _ q3 hx)

end GlobalTheory.DistLa
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeTriplesDistributiveStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLattice_triples_distributive : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), (∀ (L : Lat D N) (L₁ L₂ L₃ : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L L₁) (La D (tor0 D cc δ) L L₂) (La D (tor0 D cc δ) L L₃)) ∧ (∀ (L₁ L₂ L₃ : Lat D N) (L' : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L₁ L') (La D (tor0 D cc δ) L₂ L') (La D (tor0 D cc δ) L₃ L')) ∧ ∀ (L₀ L : Lat D N) (L₀' L' : Lat D N'), SD D L₀' → SD D L' → Dist (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) L₀ L') (La D (tor0 D cc δ) L L') := by
  first | exact @GlobalTheory.DistLa.dist_La | exact GlobalTheory.DistLa.dist_La | (intros; apply GlobalTheory.DistLa.dist_La <;> assumption)
end
